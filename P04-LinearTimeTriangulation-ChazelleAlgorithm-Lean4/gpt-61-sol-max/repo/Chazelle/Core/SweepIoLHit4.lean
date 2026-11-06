module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepIoLHit3

/-!
# The sweep RAM (WP-D), answers: the local hit, part 4 (the scan loops)

The test of one chord, the loop over the exit chords of one region, and the scan of the three
regions of the local hit.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft sideInArc)
open OracleQ (sj sk ek succP predP)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## Two list and memory facts -/

/-- A word reached through a doubly indirect pointer that robustly holds a value lies below the
bound. -/
theorem robust_addr3 {E : ℕ} {m : ℕ → ℕ} {b a o t v : ℕ}
    (h : Robust E m fun m' => m' (m' b + m' (m' a + o) + t) = v) (ha : a < E)
    (hao : m a + o < E) : b < E ∧ m b + m (m a + o) + t < E := by
  have hb : b < E := by
    by_contra hge
    have := h (Function.update (Function.update m b (b + 1)) (b + 1 + m (m a + o) + t) (v + 1))
      (fun x hx => by grind)
    grind
  refine ⟨hb, ?_⟩
  by_contra hge
  have := h (Function.update m (m b + m (m a + o) + t) (v + 1)) (fun x hx => by
    grind)
  grind

theorem take_succ_getD {l : List ℕ} {t : ℕ} (h : t < l.length) :
    l.take (t + 1) = l.take t ++ [l.getD t 0] := by
  simp_all

/-! ## Register sets and frames -/

/-- The registers written by the read of a chord. -/
def RSet (q : ℕ) : Prop :=
  q = sX ∨ q = sY ∨ q = sK ∨ q = sCh ∨ q = sLp ∨ q = sRp ∨ q = sH1

/-- The registers written by one test (read and offer). -/
def WSet (q : ℕ) : Prop := RSet q ∨ q = sFe ∨ q = sFh

theorem scanReadL_other' (m f : ℕ → ℕ) {q : ℕ} (h : ¬ RSet q) : regB m scanReadL f q = f q :=
  regB_other m scanReadL f (fun i hi => by
    simp only [scanReadL, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [dstI] <;> intro he <;> subst he <;> apply h <;> simp [RSet])

section
variable (X : ℕ → Prop)
include X
/-- **The frame of a scan step**: registers outside the oracle bands, the set `X`, the
accumulator block, `lO, lO + 1` and the allocator are unchanged; the allocator grows; memory
below it is kept. -/
def XFr (c c' : Config) : Prop :=
  (∀ r, bandOf r ∉ oracleBands → ¬ X r → (r < accA ∨ accA + 12 < r) → r ≠ lO → r ≠ lO + 1 →
    r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
  c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)

theorem XFr.refl (c : Config) : XFr X c c :=
  by core_grind


end

theorem XFr.trans {X : ℕ → Prop} {c₁ c₂ c₃ : Config} (h₁ : XFr X c₁ c₂) (h₂ : XFr X c₂ c₃) :
    XFr X c₁ c₃ :=
  by core_grind

theorem XFr.mono {X Y : ℕ → Prop} {c c' : Config} (h : XFr X c c') (hXY : ∀ r, X r → Y r) :
    XFr Y c c' :=
  by core_grind

/-! ## The environment of the scan -/

/-- **The environment of the scan**: the chain and its normal form, the tag, the position `x`
(registers `lE, lH`) and the direction code `d` (register `lD`). -/
structure SEnv (P : Polygon) (W : ℕ) (C : Chain) (N : NF) (Mod : ℕ → Chain) (R₀ : ℝ) (x : WPos)
    (d : ℕ) (c : Config) : Prop where
  hG : GoodEnv P
  hW3 : P.n + 3 ≤ W
  hctx : ChainCtx P W c lCD C
  hNF : IsNF (chainModel C) (Qof P) N
  htag : c.nreg lT ≤ 2
  hMod : Mod (c.nreg lT) = C
  hR : C.radius = R₀
  hn : c.nreg lN = 2 * C.m + 7
  hE : c.nreg lE = x.edge
  hH : c.nreg lH = x.hgt
  hD : c.nreg lD = d
  hy : |((chainModel C).pos (Qof P) x).2| < R₀

theorem SEnv.transport {C : Chain} {N : NF} {Mod : ℕ → Chain} {R₀ : ℝ} {x : WPos} {d : ℕ}
    {c c' : Config} (h : SEnv P W C N Mod R₀ x d c)
    (hr : ∀ r, r = lCD ∨ r = lT ∨ r = lN ∨ r = lE ∨ r = lH ∨ r = lD → c'.nreg r = c.nreg r)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (hA : c.nreg ALLOC ≤ c'.nreg ALLOC) :
    SEnv P W C N Mod R₀ x d c' := by
  obtain ⟨hG, hW3, hctx, hNF, htag, hMod, hR, hn, hE, hH, hD, hy⟩ := h
  have r1 := hr lCD (Or.inl rfl)
  have r2 := hr lT (Or.inr (Or.inl rfl))
  have r3 := hr lN (Or.inr (Or.inr (Or.inl rfl)))
  have r4 := hr lE (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have r5 := hr lH (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have r6 := hr lD (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  exact ⟨hG, hW3, hctx.transport r1 hm hA, hNF, by omega, by simp_all, hR,
    by omega, by omega, by omega, by omega, hy⟩

/-- The registers of the environment lie outside the scan's writes. -/
theorem SEnv.keep {C : Chain} {N : NF} {Mod : ℕ → Chain} {R₀ : ℝ} {x : WPos} {d : ℕ}
    {c c' : Config} (h : SEnv P W C N Mod R₀ x d c) (fr : XFr SSet c c') :
    SEnv P W C N Mod R₀ x d c' :=
  h.transport (fun r hr => by
    refine fr.1 r (not_oracle_sw ?_ ?_) ?_ ?_ ?_ ?_ ?_ <;>
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      omega_nf ) fr.2.2 fr.2.1

/-! ## Growth of the accumulator -/

/-- **A step of the accumulator**: from `L`, only good candidates are added, and (below the top)
the far ends of the matching chords of `ks` are offered. -/
def AccStep (P : Polygon) (C : Chain) (N : NF) (Mod : ℕ → Chain) (R₀ : ℝ) (x : WPos) (d : ℕ)
    (ks : List ℕ) (L : Set ℝ) (c : Config) : Prop :=
  ∃ L', AccOK P accA Mod R₀ ((chainModel C).pos (Qof P) x) (dirOf d) L' c ∧ L ⊆ L' ∧
    (∀ τ ∈ L', τ ∈ L ∨ (0 < τ ∧ OnCB C (rayPt ((chainModel C).pos (Qof P) x) (dirOf d) τ))) ∧
    (((chainModel C).pos (Qof P) x).2 ≤ C.top.2 → ChordsDone P C N x d ks L')

section
variable {C : Chain} {N : NF} {Mod : ℕ → Chain} {R₀ : ℝ} {x : WPos} {d : ℕ}
theorem AccStep.transport
    {ks : List ℕ} {L : Set ℝ} {c c' : Config} (h : AccStep P C N Mod R₀ x d ks L c)
    (hr : ∀ j, j ≤ 12 → c'.nreg (accA + j) = c.nreg (accA + j)) :
    AccStep P C N Mod R₀ x d ks L c' := by
  obtain ⟨L', a, s, g, dn⟩ := h
  exact ⟨L', a.transport hr, s, g, dn⟩

theorem AccStep.init
    {L : Set ℝ} {c : Config}
    (h : AccOK P accA Mod R₀ ((chainModel C).pos (Qof P) x) (dirOf d) L c) :
    AccStep P C N Mod R₀ x d [] L c :=
  ⟨L, h, le_rfl, fun _τ hτ => Or.inl hτ, fun _ _k hk => absurd hk List.not_mem_nil⟩

theorem AccStep.trans
    {ks₁ ks₂ : List ℕ} {L L' : Set ℝ} {c : Config} (h₁ : L ⊆ L')
    (g₁ : ∀ τ ∈ L', τ ∈ L ∨
      (0 < τ ∧ OnCB C (rayPt ((chainModel C).pos (Qof P) x) (dirOf d) τ)))
    (d₁ : ((chainModel C).pos (Qof P) x).2 ≤ C.top.2 → ChordsDone P C N x d ks₁ L')
    (h₂ : AccStep P C N Mod R₀ x d ks₂ L' c) : AccStep P C N Mod R₀ x d (ks₁ ++ ks₂) L c := by
  obtain ⟨L'', a, s, g, dn⟩ := h₂
  refine ⟨L'', a, h₁.trans s, fun τ hτ => ?_, fun ht k hk hca => ?_⟩
  all_goals ram_grind

/-! ## The test of a chord -/


end

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The test of a chord** read into `sLp, sRp, sH1`. -/
theorem scanTest_irs {C : Chain} {N : NF} {Mod : ℕ → Chain} {R₀ : ℝ} {x : WPos} {d : ℕ}
    (hI : IInv W c₀ c) (hK : Consts c₀) (hS : SEnv P W C N Mod R₀ x d c) {k : ℕ}
    (hk : k < N.nChords) {L : Set ℝ}
    (hacc : AccOK P accA Mod R₀ ((chainModel C).pos (Qof P) x) (dirOf d) L c)
    (hlp : c.nreg sLp = (N.chord k).lp) (hrp : c.nreg sRp = (N.chord k).rp)
    (hh1 : c.nreg sH1 = (N.chord k).h + 1) (hroom : c.nreg ALLOC + scanTestK ≤ W) :
    IRS P W c₀ scanTest c scanTestK (fun c' =>
      AccStep P C N Mod R₀ x d [k] L c' ∧ XFr (fun r => r = sFe ∨ r = sFh) c c') := by
  obtain ⟨xe, xh⟩ := x
  obtain ⟨hG, hW3, hctx, hNF, htag, hMod, hR, hn, hE, hH, hD, hy⟩ := hS
  simp only at hE hH
  subst hE hH hD
  have hk1 : c.nreg K1 = 1 := (hK.fix hI).2.1
  have hiffR : c.nreg lD ≠ 1 → ((c.nreg sRp = c.nreg lE ∧ c.nreg sH1 = c.nreg lH) ↔
      Sweep.ChordAt (N.chord k) ⟨c.nreg lE, c.nreg lH⟩ (c.nreg lD)) := by
    ram_grind
  have hiffL : c.nreg lD = 1 → ((c.nreg sLp = c.nreg lE ∧ c.nreg sH1 = c.nreg lH) ↔
      Sweep.ChordAt (N.chord k) ⟨c.nreg lE, c.nreg lH⟩ (c.nreg lD)) := by
    ram_grind
  have hfarR : c.nreg lD ≠ 1 → Sweep.farPos (N.chord k) (c.nreg lD) = ⟨c.nreg sLp, c.nreg sH1⟩ := by
    simp_all [Sweep.farPos, CRec.lpos]
  have hfarL : c.nreg lD = 1 → Sweep.farPos (N.chord k) (c.nreg lD) = ⟨c.nreg sRp, c.nreg sH1⟩ := by
    simp_all [Sweep.farPos, CRec.rpos]
  have r1 : c.nreg ALLOC + (10 + offerFK) ≤ W := by omega_nf
  have conv : ∀ c', ((∃ L', AccOK P accA Mod R₀ ((chainModel C).pos (Qof P) ⟨c.nreg lE, c.nreg lH⟩)
        (dirOf (c.nreg lD)) L' c' ∧ L ⊆ L' ∧
        (∀ τ ∈ L', τ ∈ L ∨ (0 < τ ∧ OnCB C (rayPt ((chainModel C).pos (Qof P)
          ⟨c.nreg lE, c.nreg lH⟩) (dirOf (c.nreg lD)) τ))) ∧
        (((chainModel C).pos (Qof P) ⟨c.nreg lE, c.nreg lH⟩).2 ≤ C.top.2 →
          ChordsDone P C N ⟨c.nreg lE, c.nreg lH⟩ (c.nreg lD) [k] L')) ∧
      (∀ r, bandOf r ∉ oracleBands → r ≠ sFe → r ≠ sFh → (r < accA ∨ accA + 12 < r) → r ≠ lO →
        r ≠ lO + 1 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) →
      AccStep P C N Mod R₀ ⟨c.nreg lE, c.nreg lH⟩ (c.nreg lD) [k] L c' ∧
        XFr (fun r => r = sFe ∨ r = sFh) c c' := by
    rintro c' ⟨hst, h5, h6, h7⟩
    exact ⟨hst, fun r hr hX => h5 r hr (fun e => hX (Or.inl e)) (fun e => hX (Or.inr e)), h6, h7⟩
  unfold scanTest
  by_cases h1 : c.nreg lD < c.nreg K1
  · exact (IRS.ifT h1 (eqOffer_irs (Or.inr rfl) (Or.inl rfl) hk hI hK hG hW3 hctx hNF hacc htag
      hMod hR hn rfl hy (hiffR (by omega)) (hfarR (by omega)) r1)).mono
      (by omega_nf) conv
  refine IRS.mono (K := (12 + offerFK) + 2) (IRS.ifF h1 ?_) (by omega_nf)
    (fun _ h => h)
  by_cases h2 : c.nreg K1 < c.nreg lD
  · exact (IRS.ifT h2 (eqOffer_irs (Or.inr rfl) (Or.inl rfl) hk hI hK hG hW3 hctx hNF hacc htag
      hMod hR hn rfl hy (hiffR (by omega)) (hfarR (by omega)) r1)).mono (by omega) conv
  · exact (IRS.ifF h2 (eqOffer_irs (Or.inl rfl) (Or.inr rfl) hk hI hK hG hW3 hctx hNF hacc htag
      hMod hR hn rfl hy (hiffL (by omega)) (hfarL (by omega)) r1)).mono (by omega) conv

/-! ## The body of the loop over the chords of a region -/

/-- The cost of the body. -/
def scanBodyK : ℕ := 13 + scanTestK

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **One chord of the region `r`**: read the chord at place `sT` of its list, test, offer. -/
theorem scanBody_irs {C : Chain} {N : NF} {Mod : ℕ → Chain} {R₀ : ℝ} {x : WPos} {d : ℕ}
    (hI : IInv W c₀ c) (hK : Consts c₀) (hS : SEnv P W C N Mod R₀ x d c) {r B E : ℕ}
    (hr : r < N.nRegions) (hNW : NFWithin c.nmem B E N) (hEA : E ≤ c.nreg ALLOC)
    (hC3 : c.nreg sC3 = c.nmem (B + 3))
    (hCl : c.nreg sCl = c.nmem (B + 7) + c.nmem (c.nmem (B + 5) + 5 * r + 3))
    (hT : c.nreg sT < (N.region r).chords.length) {L : Set ℝ}
    (hacc : AccOK P accA Mod R₀ ((chainModel C).pos (Qof P) x) (dirOf d) L c)
    (hroom : c.nreg ALLOC + scanBodyK ≤ W) :
    IRS P W c₀ scanBody c scanBodyK (fun c' =>
      AccStep P C N Mod R₀ x d [(N.region r).chords.getD (c.nreg sT) 0] L c' ∧
      c'.nreg sT = c.nreg sT + 1 ∧ XFr (fun q => WSet q ∨ q = sT) c c') := by
  have hN : NFAt c.nmem B N := hNW.holds
  have hrl : r < N.regions.length := hr
  have hk1 : c.nreg K1 = 1 := (hK.fix hI).2.1
  obtain ⟨k, hkdef⟩ : ∃ k, k = (N.region r).chords.getD (c.nreg sT) 0 := ⟨_, rfl⟩
  rw [← hkdef]
  have hkmem : k ∈ (N.region r).chords := by
    simp_all
  have hNF := hS.hNF
  obtain ⟨-, -, -, reg, -, -, -, hRegs, -, hhlt, -⟩ := hNF
  have hk : k < N.nChords := (((hRegs r hr).1 k).1 hkmem).1
  have hkl : k < N.chords.length := hk
  have rk : c.nmem (c.nreg sCl + c.nreg sT) = k := by
    rw [hCl, hkdef]; exact (hN.2.2.2.2.2.2.2.1 r hrl).2.2.2.2 _ hT
  obtain ⟨wh, wl, wr, -, -⟩ := hN.2.2.2.2.2.1 k hkl
  have b1 : B + 5 < E ∧ c.nmem (B + 5) + (5 * r + 4) < E := NFLoc.robust_addr2 (fun m' hm' => by
    simpa only [Nat.add_assoc] using ((hNW m' hm').2.2.2.2.2.2.2.1 r hrl).2.2.1)
  have b2 := robust_addr3 (b := B + 7) (a := B + 5) (o := 5 * r + 3) (t := c.nreg sT) (v := k)
    (fun m' hm' => by
      have := ((hNW m' hm').2.2.2.2.2.2.2.1 r hrl).2.2.2.2 _ hT
      grind) b1.1 (by omega)
  have b3 := NFLoc.robust_addr2 (b := B + 3) (o := 5 * k + 2) (fun m' hm' => by
    simpa only [Nat.add_assoc] using ((hNW m' hm').2.2.2.2.2.1 k hkl).2.2.1)
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hhk := hhlt k hk
  rw [hQn] at hhk
  have hW3 := hS.hW3
  have hAW : c.nreg ALLOC ≤ W := by omega
  have e2 : c.nmem (B + 5) + 5 * r + 3 = c.nmem (B + 5) + (5 * r + 3) := by ring
  have hb : c.nreg sCl + c.nreg sT ≤ W := by grind
  have hb2 : c.nreg sC3 + 5 * c.nmem (c.nreg sCl + c.nreg sT) + 2 ≤ W := by omega
  have hb3 : c.nmem (c.nreg sC3 + 5 * c.nmem (c.nreg sCl + c.nreg sT)) + 1 ≤ W := by
    grind
  have hok := scanReadL_ok c.nmem c.nreg hk1 hb hb2 hb3
  unfold scanBody
  refine IRS.seq (K₂ := scanTestK + 1) (IRS.block _ hI hok) ?_ |>.mono
    (by grind [scanReadL, List.length_cons, List.length_nil, scanBodyK]) (fun _ h => h)
  rintro c₁ hI₁ - - hc1
  have hm1 : c₁.nmem = c.nmem := by rw [hc1]
  have kk : ∀ q, ¬ RSet q → c₁.nreg q = c.nreg q := fun q hq => by
    rw [hc1]; exact scanReadL_other' _ _ hq
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := kk ALLOC (by omega_nf)
  obtain ⟨v1, v2, v3⟩ := scanReadL_val c.nmem c.nreg hk1
  have vLp : c₁.nreg sLp = (N.chord k).lp := by
    rw [hc1]; grind
  have vRp : c₁.nreg sRp = (N.chord k).rp := by
    rw [hc1]; grind
  have vH1 : c₁.nreg sH1 = (N.chord k).h + 1 := by
    rw [hc1]; grind
  have hS₁ : SEnv P W C N Mod R₀ x d c₁ := hS.transport (fun q hq => kk q (by
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
        omega_nf <;> omega))
    (fun a _ => by rw [hm1]) hA1.ge
  have hacc₁ := hacc.transport (c' := c₁) (fun j hj => kk _ (by
    unfold RSet sX sY sK sCh sLp sRp sH1 accA sw; omega))
  refine IRS.seq (K₂ := 1) (scanTest_irs hI₁ hK hS₁ hk hacc₁ vLp vRp vH1
    (by ram_grind)) ?_
  rintro c₂ hI₂ - - ⟨hst, fr2⟩
  have t2 : c₂.nreg sT = c.nreg sT := by
    rw [fr2.1 sT (not_oracle_sw (by omega_nf) (by omega_nf))
      (by omega_nf) (by omega_nf) (by omega_nf)
      (by omega_nf) (by grind)]
    exact kk sT (by omega_nf)
  have k12 : c₂.nreg K1 = 1 := (hK.fix hI₂).2.1
  have hok3 : okB W c₂.nmem [.addN sT sT K1] c₂.nreg :=
    ⟨⟨iscr_sw (by omega_nf) (by omega_nf), by
      omega⟩, trivial⟩
  refine (IRS.block _ hI₂ hok3).mono le_rfl ?_
  intro c₃ hc3
  have r3 : ∀ q, q ≠ sT → c₃.nreg q = c₂.nreg q := by
    intro q hq; rw [hc3]; show regB c₂.nmem [.addN sT sT K1] c₂.nreg q = _
    simp only [regB, regI]; ram_simp
  have t3 : c₃.nreg sT = c₂.nreg sT + 1 := by
    rw [hc3]; show regB c₂.nmem [.addN sT sT K1] c₂.nreg sT = _
    simp only [regB, regI, upd_same]; rw [k12]
  have hm3 : c₃.nmem = c₂.nmem := by rw [hc3]
  refine ⟨hst.transport (fun j hj => r3 _ (by omega_nf)), by rw [t3, t2], ?_,
    ?_, ?_⟩
  · intro q hq hX hqa hqo hqo1 hqA
    rw [r3 q (fun h => hX (Or.inr h)), fr2.1 q hq (fun h => hX (Or.inl (Or.inr h))) hqa hqo hqo1 hqA]
    ram_grind
  · rw [r3 ALLOC (by grind), ← hA1]; exact fr2.2.1
  · intro a ha
    rw [hm3, fr2.2.2 a (by omega), hm1]

/-! ## The head of the loop over the chords of a region -/

/-- The registers written by the head. -/
def HdSet (q : ℕ) : Prop := q = sX ∨ q = sY ∨ q = sNc ∨ q = sCl ∨ q = sT

/-- The registers written by the scan of one region. -/
def ScanW (q : ℕ) : Prop := WSet q ∨ HdSet q

theorem scanW_sset {q : ℕ} (h : ScanW q) : SSet q := by
  omega_nf

theorem scanHeadL_other (m f : ℕ → ℕ) (rr : ℕ) {q : ℕ} (h : ¬ HdSet q) :
    regB m (scanHeadL rr) f q = f q :=
  regB_other m (scanHeadL rr) f (fun i hi => by
    simp only [scanHeadL, List.mem_cons, List.not_mem_nil, or_false] at hi
    core_grind)

section
variable (m f : ℕ → ℕ) {rr : ℕ} (hrr : ¬ SSet rr) (hk2 : f K2 = 2) (hk3 : f K3 = 3)
include hrr hk2 hk3
theorem scanHeadL_val :
    regB m (scanHeadL rr) f sNc = m (f sR5 + 5 * f rr + 2) ∧
    regB m (scanHeadL rr) f sCl = m (f sR5 + 5 * f rr + 3) ∧
    regB m (scanHeadL rr) f sT = 0 := by
  have e2 : f 240615 = 2 := hk2
  have e3 : f 240616 = 3 := hk3
  unfold SSet sw at hrr
  have n1 : rr ≠ 241130 := by omega
  
  simp only [scanHeadL, regB, regI, upd, sX, sY, sR5, sNc, sCl, sT, K2, K3, sw]
  grind

theorem scanHeadL_ok (hb : f sR5 + 5 * f rr + 3 ≤ W) : okB W m (scanHeadL rr) f := by
  have e2 : f 240615 = 2 := hk2
  have e3 : f 240616 = 3 := hk3
  
  unfold SSet sw at hrr
  have n1 : rr ≠ 241130 := by omega
  
  have s : ∀ j, 700 ≤ j → j < 10000 → IScr (240000 + j) := fun j h1 h2 =>
    iscr_sw (by omega) (by omega)
  simp only [scanHeadL, okB, okI, regI, upd, sX, sY, sR5, sNc, sCl, sT, K2, K3, sw]
  ram_grind


end

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The head of the scan of region `r`**: its number of chords, the start of its chord list
(when there is one) and the place `0`. -/
theorem scanHead_irs {rr : ℕ} (hrr : ¬ SSet rr) {N : NF} (hI : IInv W c₀ c) (hK : Consts c₀)
    {B E r : ℕ} (hNW : NFWithin c.nmem B E N) (hEA : E ≤ c.nreg ALLOC) (hAW : c.nreg ALLOC ≤ W)
    (hr : r < N.nRegions) (hrv : c.nreg rr = r) (hR5 : c.nreg sR5 = c.nmem (B + 5))
    (hL7 : c.nreg sL7 = c.nmem (B + 7)) :
    IRS P W c₀ (scanHead rr) c 12 (fun c' =>
      c'.nreg sNc = (N.region r).chords.length ∧
      (0 < (N.region r).chords.length →
        c'.nreg sCl = c.nmem (B + 7) + c.nmem (c.nmem (B + 5) + 5 * r + 3)) ∧
      c'.nreg sT = 0 ∧ (∀ q, ¬ HdSet q → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  have hN : NFAt c.nmem B N := hNW.holds
  have hrl : r < N.regions.length := hr
  have hKc := hK.fix hI
  have hk2 : c.nreg K2 = 2 := hKc.2.2.2.2.2.1
  have hk3 : c.nreg K3 = 3 := hKc.2.2.2.2.2.2
  have b1 : B + 5 < E ∧ c.nmem (B + 5) + (5 * r + 4) < E := NFLoc.robust_addr2 (fun m' hm' => by
    simpa only [Nat.add_assoc] using ((hNW m' hm').2.2.2.2.2.2.2.1 r hrl).2.2.1)
  have hok := scanHeadL_ok (W := W) c.nmem c.nreg hrr hk2 hk3 (by omega)
  obtain ⟨v1, v2, v3⟩ := scanHeadL_val c.nmem c.nreg hrr hk2 hk3
  unfold scanHead
  refine IRS.seq (K₂ := 3) (IRS.block _ hI hok) ?_ |>.mono
    (by grind [scanHeadL, List.length_cons, List.length_nil]) (fun _ h => h)
  rintro c₁ hI₁ - - hc1
  have hm1 : c₁.nmem = c.nmem := by rw [hc1]
  have kk : ∀ q, ¬ HdSet q → c₁.nreg q = c.nreg q := fun q hq => by
    rw [hc1]; exact scanHeadL_other _ _ _ hq
  have w1 : c₁.nreg sNc = (N.region r).chords.length := by
    rw [hc1]; show regB c.nmem (scanHeadL rr) c.nreg sNc = _
    rw [v1, hR5, hrv]; exact (hN.2.2.2.2.2.2.2.1 r hrl).2.1
  have w2 : c₁.nreg sCl = c.nmem (c.nmem (B + 5) + 5 * r + 3) := by
    simp_all
  have w3 : c₁.nreg sT = 0 := by
    simp_all
  have k0 : c₁.nreg K0 = 0 := (hK.fix hI₁).1
  by_cases hpos : c₁.nreg K0 < c₁.nreg sNc
  · have hn0 : 0 < (N.region r).chords.length := by omega
    have b2 := robust_addr3 (b := B + 7) (a := B + 5) (o := 5 * r + 3) (t := 0)
      (v := (N.region r).chords.getD 0 0)
      (fun m' hm' => by
        have := ((hNW m' hm').2.2.2.2.2.2.2.1 r hrl).2.2.2.2 0 hn0
        omega) b1.1 (by omega)
    have e2 : c.nmem (B + 5) + 5 * r + 3 = c.nmem (B + 5) + (5 * r + 3) := by ring
    have l7 : c₁.nreg sL7 = c.nmem (B + 7) := by
      grind [HdSet, sX, sY, sNc, sCl, sT, sL7, sw]
    have hok2 : okI W c₁.nreg (.addN sCl sCl sL7) :=
      ⟨iscr_sw (by omega_nf) (by omega_nf), by
        grind⟩
    refine (IRS.ifT hpos (IRS.instr1 hI₁ hok2)).mono le_rfl ?_
    intro c' hc'
    have r' : ∀ q, q ≠ sCl → c'.nreg q = c₁.nreg q := by
      simp_all [regI]
    refine ⟨by ram_grind, fun _ => ?_,
      by ram_grind, fun q hq => ?_, by simp_all⟩
    · rw [hc']; show regI c₁.nmem (.addN sCl sCl sL7) c₁.nreg sCl = _
      simp only [regI, upd_same]; omega
    ram_grind
  · refine (IRS.ifF hpos (IRS.skip hI₁ ?_)).mono le_rfl (fun _ h => h)
    simp_all

/-! ## The loop over the chords of a region -/

/-- The cost of the scan of a region with `n` chords. -/
def scanRK (n : ℕ) : ℕ := 12 + ((scanBodyK + 2) * n + 2)

theorem XFr.of_regs {X : ℕ → Prop} {c c' : Config} (hr : ∀ q, ¬ X q → c'.nreg q = c.nreg q)
    (hX : ¬ X ALLOC) (hm : c'.nmem = c.nmem) : XFr X c c' :=
  by grind [Chazelle.Core.SweepIo.XFr]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The scan of the exit chords of the region `r`** (register `rr`). -/
theorem scanR_irs {rr : ℕ} (hrr : ¬ SSet rr) {C : Chain} {N : NF} {Mod : ℕ → Chain} {R₀ : ℝ}
    {x : WPos} {d : ℕ} (hI : IInv W c₀ c) (hK : Consts c₀) (hS : SEnv P W C N Mod R₀ x d c)
    {r B E : ℕ} (hr : r < N.nRegions) (hNW : NFWithin c.nmem B E N) (hEA : E ≤ c.nreg ALLOC)
    (hrv : c.nreg rr = r) (hR5 : c.nreg sR5 = c.nmem (B + 5)) (hL7 : c.nreg sL7 = c.nmem (B + 7))
    (hC3 : c.nreg sC3 = c.nmem (B + 3)) {L : Set ℝ}
    (hacc : AccOK P accA Mod R₀ ((chainModel C).pos (Qof P) x) (dirOf d) L c)
    (hroom : c.nreg ALLOC + scanRK (N.region r).chords.length ≤ W) :
    IRS P W c₀ (scanR rr) c (scanRK (N.region r).chords.length) (fun c' =>
      AccStep P C N Mod R₀ x d (N.region r).chords L c' ∧ XFr ScanW c c') := by
  obtain ⟨n, hn⟩ : ∃ n, n = (N.region r).chords.length := ⟨_, rfl⟩
  rw [← hn] at hroom ⊢
  have hrl : r < N.regions.length := hr
  have b1 : B + 5 < E ∧ c.nmem (B + 5) + (5 * r + 4) < E := NFLoc.robust_addr2 (fun m' hm' => by
    simpa only [Nat.add_assoc] using ((hNW m' hm').2.2.2.2.2.2.2.1 r hrl).2.2.1)
  have hAW : c.nreg ALLOC ≤ W := by omega
  unfold scanR
  refine IRS.seq (K₂ := (scanBodyK + 2) * n + 2)
    (scanHead_irs hrr hI hK hNW hEA hAW hr hrv hR5 hL7) ?_
  rintro c₁ hI₁ - - ⟨w1, w2, w3, kk, hm1⟩
  rw [← hn] at w1 w2
  have fr1 : XFr ScanW c c₁ := XFr.of_regs (fun q hq => kk q (fun h => hq (Or.inr h)))
    (by omega_nf) hm1
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC :=
    kk ALLOC (by omega_nf)
  have c31 : c₁.nreg sC3 = c.nreg sC3 :=
    kk sC3 (by omega_nf)
  have hS₁ : SEnv P W C N Mod R₀ x d c₁ := hS.keep (fr1.mono fun q h => scanW_sset h)
  have hacc₁ := hacc.transport (c' := c₁) (fun j hj => kk _ (by
    grind [HdSet, sX, sY, sNc, sCl, sT, accA, sw]))
  have hreg : ∀ c', XFr (fun q => WSet q ∨ q = sT) c₁ c' → ∀ q, q = sNc ∨ q = sCl ∨ q = sC3 →
      c'.nreg q = c₁.nreg q := by
    intro c' fr q hq
    refine fr.1 q (not_oracle_sw ?_ ?_) ?_ ?_ ?_ ?_ ?_ <;> rcases hq with rfl | rfl | rfl <;>
      omega_nf <;> omega
  have hmem : ∀ c', XFr (fun q => WSet q ∨ q = sT) c₁ c' → ∀ a, a < c.nreg ALLOC →
      c'.nmem a = c.nmem a := by
    intro c' fr a ha; rw [fr.2.2 a (by omega), hm1]
  have hsub : ∀ q, (WSet q ∨ q = sT) → ScanW q := fun q h =>
    h.elim Or.inl (fun e => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e)))))
  let I : Config → Prop := fun c' => XFr (fun q => WSet q ∨ q = sT) c₁ c' ∧ c'.nreg sT ≤ n ∧
    AccStep P C N Mod R₀ x d ((N.region r).chords.take (c'.nreg sT)) L c'
  have hW := IRS.while (P := P) (W := W) (c₀ := c₀) (a := sT) (b := sNc) (body := scanBody) I
    (fun c' => n - c'.nreg sT) scanBodyK
    (fun c' hc ht => by
      grind)
    (fun c' hI' hc ht hroom' => by
      obtain ⟨fr, hle, hst⟩ := hc
      rw [hreg c' fr sNc (Or.inl rfl), w1] at ht
      have hn0 : 0 < n := by omega
      have hn0' : 0 < (N.region r).chords.length := by omega
      have b2 := robust_addr3 (b := B + 7) (a := B + 5) (o := 5 * r + 3) (t := 0)
        (v := (N.region r).chords.getD 0 0)
        (fun m' hm' => by
          have := ((hNW m' hm').2.2.2.2.2.2.2.1 r hrl).2.2.2.2 0 hn0'
          omega) b1.1 (by omega)
      have m' := hmem c' fr
      have hS' : SEnv P W C N Mod R₀ x d c' :=
        hS₁.keep (fr.mono fun q h => scanW_sset (hsub q h))
      have hNW' : NFWithin c'.nmem B E N := hNW.transport (fun a ha => m' a (by omega))
      have hEA' : E ≤ c'.nreg ALLOC := by have := fr.2.1; omega
      have e2 : c.nmem (B + 5) + 5 * r + 3 = c.nmem (B + 5) + (5 * r + 3) := by ring
      have hC3' : c'.nreg sC3 = c'.nmem (B + 3) := by
        grind
      have hCl' : c'.nreg sCl = c'.nmem (B + 7) + c'.nmem (c'.nmem (B + 5) + 5 * r + 3) := by
        grind
      obtain ⟨L', a', s', g', d'⟩ := hst
      refine (scanBody_irs hI' hK hS' hr hNW' hEA' hC3' hCl' (by omega) a'
        hroom').mono le_rfl ?_
      rintro c'' ⟨hst2, t2, fr2⟩
      refine ⟨⟨fr.trans fr2, by omega, ?_⟩, by omega⟩
      rw [t2, take_succ_getD (l := (N.region r).chords) (by omega)]
      exact AccStep.trans s' g' d' hst2)
    hI₁ ⟨XFr.refl _ _, by omega, by rw [w3]; exact AccStep.init hacc₁⟩ (by
      rw [w3, hA1, Nat.sub_zero]; ram_grind)
  rw [w3, Nat.sub_zero] at hW
  refine hW.mono le_rfl ?_
  grind [Chazelle.Core.SweepIo.XFr.mono, Chazelle.Core.SweepIo.XFr.trans]

/-! ## The scan of the three regions -/

theorem robust_addr1 {E : ℕ} {m : ℕ → ℕ} {b v : ℕ} (h : Robust E m fun m' => m' b = v) :
    b < E := by
  by_contra hge
  have := h (Function.update m b (v + 1)) (fun x hx => by grind)
  simp_all

/-- The registers written by the initialisation of the scan. -/
def ISet (q : ℕ) : Prop := q = sX ∨ q = sR5 ∨ q = sL7 ∨ q = sC3

theorem scanInitL_other (m f : ℕ → ℕ) {q : ℕ} (h : ¬ ISet q) : regB m scanInitL f q = f q :=
  regB_other m scanInitL f (fun i hi => by
    simp only [scanInitL, List.mem_cons, List.not_mem_nil, or_false] at hi
    core_grind)

section
variable (m f : ℕ → ℕ) (hk2 : f K2 = 2) (hk3 : f K3 = 3) (hk5 : f K5 = 5)
include hk2 hk3 hk5
theorem scanInitL_val :
    regB m scanInitL f sR5 = m (f lNF + 5) ∧ regB m scanInitL f sL7 = m (f lNF + 7) ∧
    regB m scanInitL f sC3 = m (f lNF + 3) := by
  simp_all [scanInitL, regB, regI, upd, sX, sR5, sL7, sC3, lNF, K2, K3, K5, sw, Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false]

theorem scanInitL_ok
    (hb : f lNF + 7 ≤ W) : okB W m scanInitL f := by
  have e2 : f 240615 = 2 := hk2
  have e3 : f 240616 = 3 := hk3
  have e5 : f 240614 = 5 := hk5
  
  have s : ∀ j, 700 ≤ j → j < 10000 → IScr (240000 + j) := fun j h1 h2 =>
    iscr_sw (by omega) (by omega)
  simp only [scanInitL, okB, okI, regI, upd, sX, sR5, sL7, sC3, lNF, K2, K3, K5, sw]
  ram_grind


end

theorem XFr.scanKeep {c c' : Config} (fr : XFr ScanW c c') {q : ℕ}
    (hq : q = sR5 ∨ q = sL7 ∨ q = sC3 ∨ q = lR0 ∨ q = lR1 ∨ q = lR2) : c'.nreg q = c.nreg q := by
  refine fr.1 q (not_oracle_sw ?_ ?_) ?_ ?_ ?_ ?_ ?_ <;>
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    omega_nf <;> omega

/-- The cost of the scan of the three regions. -/
def lhScanK (n0 n1 n2 : ℕ) : ℕ := 6 + (scanRK n0 + (scanRK n1 + scanRK n2))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The scan of the exit chords of the three regions** `lR0, lR1, lR2`. -/
theorem lhScan_irs {C : Chain} {N : NF} {Mod : ℕ → Chain} {R₀ : ℝ} {x : WPos} {d : ℕ}
    (hI : IInv W c₀ c) (hK : Consts c₀) (hS : SEnv P W C N Mod R₀ x d c) {B E : ℕ}
    (hB : c.nreg lNF = B) (hNW : NFWithin c.nmem B E N) (hEA : E ≤ c.nreg ALLOC)
    {r0 r1 r2 : ℕ} (h0 : c.nreg lR0 = r0) (h1 : c.nreg lR1 = r1) (h2 : c.nreg lR2 = r2)
    (hr0 : r0 < N.nRegions) (hr1 : r1 < N.nRegions) (hr2 : r2 < N.nRegions) {L : Set ℝ}
    (hacc : AccOK P accA Mod R₀ ((chainModel C).pos (Qof P) x) (dirOf d) L c)
    (hroom : c.nreg ALLOC + lhScanK (N.region r0).chords.length (N.region r1).chords.length
      (N.region r2).chords.length ≤ W) :
    IRS P W c₀ lhScan c (lhScanK (N.region r0).chords.length (N.region r1).chords.length
      (N.region r2).chords.length) (fun c' =>
      AccStep P C N Mod R₀ x d
        ((N.region r0).chords ++ ((N.region r1).chords ++ (N.region r2).chords)) L c' ∧
      XFr SSet c c') := by
  have hKc := hK.fix hI
  have hB11 : B + 11 < E := robust_addr1 (fun m' hm' => (hNW m' hm').2.2.2.2.1)
  have hAW : c.nreg ALLOC ≤ W := by omega
  have hok : okB W c.nmem scanInitL c.nreg := scanInitL_ok c.nmem c.nreg hKc.2.2.2.2.2.1
    hKc.2.2.2.2.2.2 hKc.2.2.2.2.1 (by omega)
  obtain ⟨v1, v2, v3⟩ := scanInitL_val c.nmem c.nreg hKc.2.2.2.2.2.1 hKc.2.2.2.2.2.2
    hKc.2.2.2.2.1
  unfold lhScan
  refine IRS.seq (K₂ := scanRK (N.region r0).chords.length + (scanRK (N.region r1).chords.length +
    scanRK (N.region r2).chords.length)) (IRS.block _ hI hok) ?_ |>.mono
    (by grind [scanInitL, List.length_cons, List.length_nil, lhScanK]) (fun _ h => h)
  rintro c₁ hI₁ - - hc1
  have hm1 : c₁.nmem = c.nmem := by rw [hc1]
  have kk : ∀ q, ¬ ISet q → c₁.nreg q = c.nreg q := fun q hq => by
    rw [hc1]; exact scanInitL_other _ _ hq
  have fr1 : XFr SSet c c₁ := XFr.of_regs (fun q hq => kk q (fun h => hq (by
      omega_nf)))
    (by omega_nf) hm1
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := kk ALLOC (by
    omega_nf)
  have w5 : c₁.nreg sR5 = c.nmem (B + 5) := by
    simp_all
  have w7 : c₁.nreg sL7 = c.nmem (B + 7) := by
    simp_all
  have w3 : c₁.nreg sC3 = c.nmem (B + 3) := by
    simp_all
  have hS₁ := hS.keep fr1
  have hacc₁ := hacc.transport (c' := c₁) (fun j hj => kk _ (by
    grind [ISet, sX, sR5, sL7, sC3, accA, sw]))
  have nr : ∀ q, q = lR0 ∨ q = lR1 ∨ q = lR2 → ¬ SSet q := by
    omega_nf
  have g0 : c₁.nreg lR0 = r0 := by
    grind [ISet, sX, sR5, sL7, sC3, lR0, sw]
  have g1 : c₁.nreg lR1 = r1 := by
    grind [ISet, sX, sR5, sL7, sC3, lR1, sw]
  have g2 : c₁.nreg lR2 = r2 := by
    grind [ISet, sX, sR5, sL7, sC3, lR2, sw]
  -- region `r0`
  refine IRS.seq (K₂ := scanRK (N.region r1).chords.length + scanRK (N.region r2).chords.length)
    (scanR_irs (nr lR0 (Or.inl rfl)) hI₁ hK hS₁ hr0
      (hNW.transport (fun a ha => by rw [hm1])) (by omega) g0 (by rw [w5, hm1])
      (by rw [w7, hm1]) (by rw [w3, hm1]) hacc₁
      (by ram_grind)) ?_
  rintro c₂ hI₂ hA2 hA2' ⟨hst2, fr2⟩
  obtain ⟨L₁, a₁, s₁, gg₁, d₁⟩ := hst2
  have m2 : ∀ a, a < c.nreg ALLOC → c₂.nmem a = c.nmem a := fun a ha => by
    rw [fr2.2.2 a (by omega), hm1]
  have hS₂ := hS₁.keep (fr2.mono fun q h => scanW_sset h)
  refine IRS.seq (K₂ := scanRK (N.region r2).chords.length)
    (scanR_irs (nr lR1 (Or.inr (Or.inl rfl))) hI₂ hK hS₂ hr1
      (hNW.transport (fun a ha => m2 a (by omega))) (by omega)
      (by rw [fr2.scanKeep (by simp), g1])
      (by rw [fr2.scanKeep (by simp), w5, m2 _ (by omega)])
      (by rw [fr2.scanKeep (by simp), w7, m2 _ (by omega)])
      (by rw [fr2.scanKeep (by simp), w3, m2 _ (by omega)]) a₁
      (by grind [lhScanK])) ?_
  rintro c₃ hI₃ hA3 hA3' ⟨hst3, fr3⟩
  obtain ⟨L₂, a₂, s₂, gg₂, d₂⟩ := hst3
  have m3 : ∀ a, a < c.nreg ALLOC → c₃.nmem a = c.nmem a := fun a ha => by
    rw [fr3.2.2 a (by omega), m2 a ha]
  have hS₃ := hS₂.keep (fr3.mono fun q h => scanW_sset h)
  refine (scanR_irs (nr lR2 (Or.inr (Or.inr rfl))) hI₃ hK hS₃ hr2
      (hNW.transport (fun a ha => m3 a (by omega))) (by omega)
      (by rw [fr3.scanKeep (by simp), fr2.scanKeep (by simp), g2])
      (by rw [fr3.scanKeep (by simp), fr2.scanKeep (by simp), w5, m3 _ (by omega)])
      (by rw [fr3.scanKeep (by simp), fr2.scanKeep (by simp), w7, m3 _ (by omega)])
      (by rw [fr3.scanKeep (by simp), fr2.scanKeep (by simp), w3, m3 _ (by omega)]) a₂
      (by grind [lhScanK])).mono le_rfl ?_
  rintro c₄ ⟨hst4, fr4⟩
  refine ⟨AccStep.trans s₁ gg₁ d₁ (AccStep.trans s₂ gg₂ d₂ hst4), ?_⟩
  exact fr1.trans ((fr2.mono fun q h => scanW_sset h).trans
    ((fr3.mono fun q h => scanW_sset h).trans (fr4.mono fun q h => scanW_sset h)))

end

end SweepIo

end Chazelle.Core
