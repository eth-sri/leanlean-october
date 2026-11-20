module

public import Chazelle.Core.SweepIoBruteMath

/-!
# The sweep RAM (WP-D), answers: a shot from the symbolic point of the query

`symShot sh md base cnt dsc tg` shoots, in the chain model of the model descriptor whose address
is in register `md`, from the point of the symbolic point in `sO` (`sw 3231 …`), in the direction
of code `qD`, at the `cnt` arcs (four-word records) at `base` with no holes (`shotList` with the
shot block `RS`), and offers its hit (if any) to the accumulator `accA` with the chain descriptor
register `dsc` and the tag register `tg`.  Used by the brute-force shot (`BruteSpec`, tag `0`) and
by the label shots (`Lab0Spec`, tag `1`).

`symShot_irs`: at most one candidate is added, a point of the chain or of the box on the ray at a
positive parameter; if the direction is free and the exit point lies on the arcs, the first hit
of the chain is offered.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
open Chazelle.Visibility (rayPt rayPt_snd)
open Chazelle.Merge (FreeAt)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- The shot block preparation: model descriptor, arcs, origin `sO`, direction `qD`, weight bound
`sw 5`, context handle `sw 10`, no holes. -/
def sPrepL (md base cnt : ℕ) : List Instr :=
  [.copyN 241300 md, .copyN 241301 base, .copyN 241302 cnt, .copyN 241303 sO,
    .copyN 241304 (sO + 1), .copyN 241305 (sO + 2), .copyN 241306 qD, .copyN 241307 (sw 5),
    .copyN 241308 (sw 10), .constN 241309 0]

/-- Offer the hit of the shot. -/
def sOffer (dsc tg : ℕ) : Stmt := .ifLtN K0 241320 (offer accA dsc 241321 241322 tg qD) .skip

/-- **The shot from `sO`** and the offer of its hit. -/
def symShot (sh : Stmt) (md base cnt dsc tg : ℕ) : Stmt :=
  .seq (block (sPrepL md base cnt)) (.seq (ShotList.shotList sh RS) (sOffer dsc tg))

/-- The cost of the shot and its offer. -/
def symShotK (Fg K : ℕ) : ℕ := 10 + (ShotList.shotCost Fg K + (offerK + 2))

/-- A register usable as an input of `symShot`: in band `bSweep`, outside the shot block and the
accumulator. -/
def SRegOK (r : ℕ) : Prop :=
  240000 ≤ r ∧ r < 250000 ∧ (r < 241300 ∨ 241600 ≤ r) ∧ (r < 242000 ∨ 242012 < r)

theorem sPrepL_val (m f : ℕ → ℕ) {md base cnt : ℕ} (_h1 : md < 241300 ∨ 241309 < md)
    (h2 : base < 241300 ∨ 241309 < base) (h3 : cnt < 241300 ∨ 241309 < cnt) :
    regB m (sPrepL md base cnt) f 241300 = f md ∧ regB m (sPrepL md base cnt) f 241301 = f base ∧
    regB m (sPrepL md base cnt) f 241302 = f cnt ∧ regB m (sPrepL md base cnt) f 241303 = f sO ∧
    regB m (sPrepL md base cnt) f 241304 = f (sO + 1) ∧
    regB m (sPrepL md base cnt) f 241305 = f (sO + 2) ∧
    regB m (sPrepL md base cnt) f 241306 = f qD ∧ regB m (sPrepL md base cnt) f 241307 = f (sw 5) ∧
    regB m (sPrepL md base cnt) f 241308 = f (sw 10) ∧ regB m (sPrepL md base cnt) f 241309 = 0 ∧
    (∀ q, (q < 241300 ∨ 241309 < q) → regB m (sPrepL md base cnt) f q = f q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => regB_other _ _ _ (fun i hi => by
    simp only [sPrepL, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [dstI] <;>
      omega)⟩ <;>
  · simp only [sPrepL, regB, regI, upd, sO, qD, sw]
    simp (disch := omega) only [ite_eq_right, ite_true, Nat.reduceAdd]

theorem sPrepL_ok (m f : ℕ → ℕ) (md base cnt : ℕ) (hW : 0 ≤ W) : okB W m (sPrepL md base cnt) f := by
  simp only [sPrepL, okB, okI]
  exact ⟨iscr_sw (by norm_num) (by norm_num), iscr_sw (by norm_num) (by norm_num),
    iscr_sw (by norm_num) (by norm_num), iscr_sw (by norm_num) (by norm_num),
    iscr_sw (by norm_num) (by norm_num), iscr_sw (by norm_num) (by norm_num),
    iscr_sw (by norm_num) (by norm_num), iscr_sw (by norm_num) (by norm_num),
    iscr_sw (by norm_num) (by norm_num), ⟨iscr_sw (by norm_num) (by norm_num), hW⟩, trivial⟩

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **The shot from `sO`** and the offer of its hit. -/
theorem symShot_irs {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands)
    (hXl : X.CapLocal) {C : Chain} {H : Host} {Mod : ℕ → Chain} {R₀ : ℝ} {L : Set ℝ}
    {s : SymPt} {z : Point} {md base cnt dsc tg : ℕ}
    (hI : IInv W c₀ c) (hK : Consts c₀) (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    (hX : X.holds P c₀.nmem (c₀.nreg (sw 10)) (c₀.nreg ALLOC))
    (hcap : c₀.nreg (sw 5) ≤ X.cap P c₀.nmem (c₀.nreg (sw 10)))
    (hOk : Ok P (chainModel C)) (hmd : MdFacts P c (c.nreg md) H C)
    (hreg : HostRegular P.n H) (hctx : ChainCtx P W c dsc C)
    (harcs : ∀ j, j < c.nreg cnt →
      ShotList.PieceOK (chainModel C) (Qof P) P.n (ShotList.arcAt c.nmem (c.nreg base) j) ∧
      (chainModel C).arcWt ((chainModel C).key (Qof P) (ShotList.arcAt c.nmem (c.nreg base) j).1)
        ((chainModel C).key (Qof P) (ShotList.arcAt c.nmem (c.nreg base) j).2) ≤ c₀.nreg (sw 5))
    (hAB : c.nreg base + 4 * c.nreg cnt ≤ c.nreg ALLOC)
    (hs : SymPtIn c sO s) (hsl : s.Lt P.n) (hz : s.eval (Qof P) = z)
    (hzD : z ∈ C.dom) (hz1 : |z.1| < C.radius) (hz2 : |z.2| < C.radius) (hzt : z.2 ≤ C.top.2)
    (hacc : AccOK P accA Mod R₀ z (dirOf (c.nreg qD)) L c) (htag : c.nreg tg ≤ 2)
    (hMod : Mod (c.nreg tg) = C) (hR : C.radius = R₀)
    (hr : SRegOK md ∧ SRegOK base ∧ SRegOK cnt ∧ SRegOK dsc ∧ SRegOK tg)
    (hroom : c.nreg ALLOC + symShotK (F (c₀.nreg (sw 5))) (c.nreg cnt) ≤ W) :
    IRS P W c₀ (symShot sh md base cnt dsc tg) c (symShotK (F (c₀.nreg (sw 5))) (c.nreg cnt))
      (fun c' => ∃ L', AccOK P accA Mod R₀ z (dirOf (c.nreg qD)) L' c' ∧
        (L' = L ∨ ∃ τ, L' = insert τ L ∧ 0 < τ ∧ OnCB C (rayPt z (dirOf (c.nreg qD)) τ)) ∧
        (FreeAt C z (dirOf (c.nreg qD)) →
          rayPt z (dirOf (c.nreg qD)) (C.hitParam z (dirOf (c.nreg qD))) ∈
            ShotList.loSet (chainModel C) (Qof P) c.nmem (c.nreg base) (c.nreg cnt) [] →
          C.hitParam z (dirOf (c.nreg qD)) ∈ L') ∧
        (∀ r, bandOf r ∉ oracleBands → ¬ (RS ≤ r ∧ r < RS + 300) → (r < accA ∨ accA + 12 < r) →
          r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  have hK₀ := hK.fix hI
  set σ := dirOf (c.nreg qD) with hσ
  set K := c.nreg cnt with hKd
  have hσ' : σ = 1 ∨ σ = -1 := by rw [hσ]; unfold dirOf; split_ifs <;> simp
  have hP : C.P.Simple := hctx.2.2.2.2.1
  obtain ⟨rmd, rbase, rcnt, rdsc, rtg⟩ := hr
  -- 1. prepare the shot block
  refine IRS.seq (K₂ := ShotList.shotCost (F (c₀.nreg (sw 5))) K + (offerK + 2))
    (IRS.block (sPrepL md base cnt) hI (sPrepL_ok _ _ _ _ _ (Nat.zero_le _))) ?_ |>.mono
      (by simp [sPrepL, symShotK]) (fun _ h => h)
  rintro c₁ hI₁ - - hc1
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, po⟩ := sPrepL_val c.nmem c.nreg
    (md := md) (base := base) (cnt := cnt) (by unfold SRegOK at rmd; omega)
    (by unfold SRegOK at rbase; omega) (by unfold SRegOK at rcnt; omega)
  have hm1 : c₁.nmem = c.nmem := by rw [hc1]
  have q1 : ∀ q, (q < 241300 ∨ 241309 < q) → c₁.nreg q = c.nreg q := fun q hq => by
    rw [hc1]; exact po q hq
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := q1 _ (by unfold ALLOC; omega)
  have c0 : c₁.nreg RS = c.nreg md := by rw [hc1]; exact p0
  have c1' : c₁.nreg (RS + 1) = c.nreg base := by rw [hc1]; exact p1
  have c2' : c₁.nreg (RS + 2) = K := by rw [hc1]; exact p2
  have c6 : c₁.nreg (RS + 6) = c.nreg qD := by rw [hc1]; exact p6
  have c7 : c₁.nreg (RS + 7) = c₀.nreg (sw 5) := by
    rw [hc1]; show regB _ _ _ 241307 = _; rw [p7]; exact hI.hin _ (by unfold IFix sw; omega)
  have c8 : c₁.nreg (RS + 8) = c₀.nreg (sw 10) := by
    rw [hc1]; show regB _ _ _ 241308 = _; rw [p8]; exact hI.hin _ (by unfold IFix sw; omega)
  have c9 : c₁.nreg (RS + 9) = 0 := by rw [hc1]; exact p9
  have hhl : ShotList.holeList c₁ RS = [] := by
    unfold ShotList.holeList; rw [c9]; rfl
  have hori : OriginIn c₁ (RS + 3) (.sym s) :=
    SweepIo.symPtIn_copy hs (by rw [hc1]; exact p3) (by rw [hc1]; exact p4)
      (by rw [hc1]; exact p5)
  obtain ⟨hmd0, hmdC, hmdW, hmdA⟩ := hmd
  -- 2. the precondition of the shot
  have hlow : ∀ a, a < c₀.nreg ALLOC → c₁.nmem a = c₀.nmem a := hI₁.hm
  have hX1 : X.holds P c₁.nmem (c₁.nreg (RS + 8)) (c₁.nreg ALLOC) := by
    rw [c8]
    exact X.mono _ _ _ _ _ hI₁.hA (X.local_ _ _ _ _ _ (fun a ha => (hlow a ha).symm) hX)
  have hcap1 : c₁.nreg (RS + 7) ≤ X.cap P c₁.nmem (c₁.nreg (RS + 8)) := by
    rw [c7, c8, hXl P c₀.nmem c₁.nmem _ _ (fun a ha => hlow a ha) hX]; exact hcap
  have hev : Origin.eval (chainModel C) (Qof P) (Origin.sym s) = z := hz
  have pre : ShotList.ShotPre X Ok RS P W c₁ := by
    refine ⟨hG, hWh, hX1, hcap1, by rw [c0, hm1, hA1]; exact hmdW, by rw [c0, hm1]; exact hmd0,
      by rw [c1', c2', hA1]; exact hAB, by rw [c9]; omega, H, C, by rw [c0, hm1]; exact hmdC,
      fun H' hH' => ?_, hOk, hctx.2.2.2.2.2, fun j hj => ?_, fun j hj => ?_, .sym s, hori, hsl,
      Or.inr ⟨by rw [hev]; exact innerPt_box C hz1 hz2, fun x hx => by cases hx⟩,
      by rw [hev]; exact hz2, ?_⟩
    · rw [c0, hm1] at hH'
      rw [← NFLoc.hostAt_unique hmdC.1 hH']
      exact hreg
    · rw [c2'] at hj
      rw [c1', hm1, c7]
      exact harcs j hj
    · rw [c9] at hj; omega
    · rw [hhl, hev]
      intro p t hp ht0 ht1 hpt
      exact absurd hpt (walk_ne_of_dom C hP hzD hp ht0 ht1)
  -- 3. the shot
  refine IRS.seq (shot_irs hsh hBs hXl hI₁ pre (by
    rw [c7, c2', hA1]; unfold symShotK at hroom; omega)) ?_ |>.mono (by rw [c7, c2']) (fun _ h => h)
  rintro c₂ hI₂ - hAb ⟨hpost, k2, hA2, hm2⟩
  have hmdC1 : ModelDescAt c₁.nmem (c₁.nreg RS) (Qof P) (chainModel C) := by
    rw [c0, hm1]; exact hmdA
  obtain ⟨hfl, A, hlo, hhi, hyes, hno⟩ := hpost (chainModel C) (.sym s) hmdC1 hori
  rw [c6, hev] at hyes hno
  rw [c1', c2', hhl, hm1] at hlo
  rw [c1', c2', hm1] at hhi
  have hAoff : A ⊆ C.domᶜ := by
    intro w hw
    have := hhi hw
    unfold ShotList.hiSet at this
    simp only [Set.mem_iUnion] at this
    obtain ⟨j, -, hj⟩ := this
    exact Sweep.arcSet_subset_compl_dom C hP _ _ hj
  -- registers after the shot
  have keep2 : ∀ r, 240000 ≤ r → r < 250000 → ¬ (RS ≤ r ∧ r < RS + 300) →
      c₂.nreg r = c₁.nreg r :=
    fun r h1 h2 h3 => k2 r (not_oracle_sw h1 h2) (by unfold ALLOC; omega) h3
  have keepc : ∀ r, 240000 ≤ r → r < 250000 → (r < RS ∨ RS + 299 < r) →
      c₂.nreg r = c.nreg r :=
    fun r h1 h2 h3 => (keep2 r h1 h2 (by omega)).trans (q1 r (by unfold RS at h3; omega))
  have t2 : c₂.nreg tg = c.nreg tg := keepc _ rtg.1 rtg.2.1 (by unfold RS; have := rtg.2.2.1; omega)
  have d2 : c₂.nreg qD = c.nreg qD := keepc _ (by unfold qD sw; norm_num)
    (by unfold qD sw; norm_num) (by unfold qD RS sw; omega)
  have cd2 : c₂.nreg dsc = c.nreg dsc :=
    keepc _ rdsc.1 rdsc.2.1 (by unfold RS; have := rdsc.2.2.1; omega)
  have a2 : ∀ j, j ≤ 12 → c₂.nreg (accA + j) = c.nreg (accA + j) := fun j hj =>
    keepc _ (by unfold accA sw; omega) (by unfold accA sw; omega) (by unfold accA RS sw; omega)
  have hacc2 : AccOK P accA Mod R₀ z σ L c₂ := hacc.transport a2
  have hA2' : c.nreg ALLOC ≤ c₂.nreg ALLOC := hA1 ▸ hA2
  have hm2' : ∀ a, a < c.nreg ALLOC → c₂.nmem a = c.nmem a := fun a ha => by
    rw [hm2 a (by omega), hm1]
  have hctx2 : ChainCtx P W c₂ dsc C := hctx.transport cd2 hm2' hA2'
  have k0₂ : c₂.nreg K0 = 0 := (hK.fix hI₂).1
  -- the completeness of the shot
  have complete : FreeAt C z σ →
      rayPt z σ (C.hitParam z σ) ∈
        ShotList.loSet (chainModel C) (Qof P) c.nmem (c.nreg base) K [] →
      c₂.nreg 241320 = 1 ∧ ∀ t, FirstHit A z σ t → t = C.hitParam z σ := by
    intro hf hlo'
    have hTA := hlo hlo'
    refine ⟨?_, fun t ht => firstHit_exit C hσ' hzt hf hAoff ht hTA⟩
    by_contra hne
    obtain ⟨hT0, -, -⟩ := Merge.hit_of_freeAt C hzt hσ' hf
    exact hno hne _ hT0 hTA
  have frame2 : ∀ r, bandOf r ∉ oracleBands → ¬ (RS ≤ r ∧ r < RS + 300) → r ≠ ALLOC →
      c₂.nreg r = c.nreg r := fun r hr hrs hrA => by
    rw [k2 r hr hrA hrs]; exact q1 r (by unfold RS at hrs; omega)
  unfold sOffer
  by_cases hflag : c₂.nreg K0 < c₂.nreg 241320
  · rw [k0₂] at hflag
    have h1 : c₂.nreg 241320 = 1 := by have : c₂.nreg 241320 ≤ 1 := hfl; omega
    obtain ⟨t, hFH, hpp2, he2, hpos2⟩ := hyes h1
    have hroom2 : c₂.nreg ALLOC + offerK ≤ W := by
      rw [c7, c2', hA1] at hAb; unfold symShotK at hroom; omega
    refine (IRS.ifT (by rw [k0₂]; exact hflag) (offer_irs (L := L) (τ := t) (Mod := Mod) hI₂ hK hG
      (by unfold hostWords at hWh; omega)
      ⟨by unfold accA sw; norm_num, by unfold accA sw; norm_num⟩
      ⟨rdsc.1, rdsc.2.1, by norm_num, by norm_num, by norm_num, by norm_num, rtg.1, rtg.2.1,
        by unfold qD sw; norm_num, by unfold qD sw; norm_num⟩
      ⟨by unfold accA; have := rdsc.2.2.2; unfold sw; omega, by unfold accA sw; omega,
        by unfold accA sw; omega, by unfold accA; have := rtg.2.2.2; unfold sw; omega,
        by unfold qD accA sw; omega⟩
      (by rw [d2]; exact hacc2) (by rw [t2]; exact htag) (by rw [t2, hMod]; exact hctx2)
      (by rw [t2, hMod]; exact hR) (by rw [t2, hMod]; exact he2)
      (by rw [t2, hMod]; exact hpp2) (by rw [t2, hMod, d2]; exact hpos2)
      (by rw [← hR]; exact hz2) hroom2)).mono (by omega) ?_
    rintro c' ⟨hacc', k3, hA3, hm3⟩
    rw [d2] at hacc'
    refine ⟨insert t L, hacc', Or.inr ⟨t, rfl, hFH.1, ?_⟩, fun hf hlo' => ?_,
      fun r hr hrs hra hrA => ?_, hA2'.trans hA3, fun a ha => by
        rw [hm3 a (by omega)]; exact hm2' a ha⟩
    · rw [← hpos2]
      refine walk_hit_onCB C (Qof P) he2 hpp2 ?_
      rw [hpos2, rayPt_snd]; exact hzt
    · obtain ⟨-, ht⟩ := complete hf hlo'
      rw [← ht t hFH]
      exact Set.mem_insert _ _
    · rw [k3 r hr hra hrA]; exact frame2 r hr hrs hrA
  · refine (IRS.ifF hflag (IRS.skip (K := offerK) hI₂ ⟨L, hacc2, Or.inl rfl, fun hf hlo' => ?_,
      fun r hr hrs hra hrA => frame2 r hr hrs hrA, hA2', hm2'⟩)).mono (by omega) (fun _ h => h)
    rw [k0₂] at hflag
    exact absurd (complete hf hlo').1 (by omega)

end

end SweepIo

end Chazelle.Core
