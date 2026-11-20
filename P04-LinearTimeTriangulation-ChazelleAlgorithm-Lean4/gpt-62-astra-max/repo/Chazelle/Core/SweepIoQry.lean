module
public import Chazelle.Core.ModelAccess
public import Chazelle.Machine.Frames
public import Chazelle.Programs.Address
public import Chazelle.Programs.Verification

public import Chazelle.Core.SweepIoPipe2

/-!
# The sweep RAM (WP-D), answers: the per-query program

`qry_run`: the per-query program `qryP c0 c1` from the loop registers: read the query, convert
its position to the walk of `C` (`convQ_sem`), the flag (`flagS`); for a direction that is not
free the zero record; otherwise the bits, the cleared accumulator, the candidate step of the side
(an `IRS` contract `hc` with the cost `Kc`), the winner in the walk of `C` (`winVal_sem`), the
record (`recS`) and the result `(1, h, lp, rp)` in the slot (`QryPost`).
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft sideInArc)
open Chazelle.Merge (FreeAt)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- Register (in)equalities of the pipeline. -/
macro "rne" : tactic => `(tactic| (simp only [qE, qH, qD, qJ, zE, zF, zP, zPh, yE, yH, wF, wP,
  wPh, rL, rR, rho, bL, bR, cX, cT, cDd, ALLOC, accA, tAq, tH, sZ, sTq, kO, pJ, pA, pR, sSide, K0,
  K1, K2, K3, K4, K5, K6, sO, sw] at *; omega))

/-- The stage-0 registers at a configuration of the answer phase. -/
theorem st0_reg (hI : IInv W c₀ c) {j : ℕ} (hj : j < 700) : c.nreg (sw j) = c₀.nreg (sw j) :=
  hI.hin _ (by unfold IFix sw; omega)

set_option maxHeartbeats 4000000 in
/-- **The query position in the walk of `C`.** -/
theorem convQ_sem {J : Merge.Junction} {H : Host} (hI : IInv W c₀ c) (hK : Consts c₀)
    (hst : SweepEv.St0S P c₀ H J) (hP : J.P.Simple) (hWm : 2 * J.whole.m + 7 ≤ W) {i : ℕ}
    (hi : i ≤ 1) (hs : c.nreg sSide = i)
    (hcls : PosClass (sideChain J i) (Qof P) ⟨c.nreg qE, c.nreg qH⟩) :
    IRS P W c₀ convQ c 24 (fun c' => c'.nreg zE < (chainModel J.whole).W.n ∧
      (chainModel J.whole).param (Qof P) ⟨c'.nreg zE, c.nreg qH⟩ =
        (chainModel (sideChain J i)).param (Qof P) ⟨c.nreg qE, c.nreg qH⟩ ∧
      (chainModel J.whole).pos (Qof P) ⟨c'.nreg zE, c.nreg qH⟩ =
        (chainModel (sideChain J i)).pos (Qof P) ⟨c.nreg qE, c.nreg qH⟩ ∧
      (∀ r, ¬ CvSet zE r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  have hKc := hK.fix hI
  have k1 : c.nreg K1 = 1 := hKc.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h40, h45, h33, h34, h35, -⟩ := id hst
  have rr : AgreeOnBand 240000 240700 c.nreg c₀.nreg := fun x h1 h2 =>
    hI.hin _ ⟨h1, h2⟩
  have r : ∀ j, j < 700 → c.nreg (sw j) = c₀.nreg (sw j) := fun j hj => st0_reg hI hj
  have hm1 : J.left.m ≤ J.whole.m := sideChain_m_le J 0
  have hm2 : J.right.m ≤ J.whole.m := sideChain_m_le J 1
  have hpe : qE ≠ cX ∧ qE ≠ cT ∧ qE ≠ cDd := by unfold qE cX cT cDd sw; omega
  have hpo : IScr zE ∧ zE ≠ cX ∧ zE ≠ cT ∧ zE ≠ cDd :=
    ⟨guarded iscr_sw, by unfold zE cX sw; omega,
      by unfold zE cT sw; omega, by unfold zE cDd sw; omega⟩
  have v35 : c.nreg (sw 35) = 2 * J.whole.m + 7 := by rw [at_index r 35, h35]
  have hnC : ∀ C : Chain, (chainModel C).W.n = 2 * C.m + 7 := fun C => cm_n C
  rcases sideChain_cases J hi with ⟨rfl, hC⟩ | ⟨rfl, hC⟩
  · rw [hC] at hcls ⊢
    have ht : c.nreg sSide < c.nreg K1 := by rw [hs, k1]; norm_num
    have hqE : c.nreg qE < 2 * J.left.m + 6 + 1 := by
      rcases hcls with (h | h) | ⟨-, h⟩ | ⟨h, -⟩ <;> simp only at h <;> omega
    have v33 : c.nreg (sw 33) = 2 * J.left.m + 7 := by rw [at_index r 33, h33]
    have v45 : c.nreg (sw 45) = 6 + tpos J.whole (J.m₁ + 2 * J.m₂) := by
      rw [at_index r 45, show (45 : ℕ) = 45 + 0 from rfl, at_index h45 0]; rfl
    have v46 : c.nreg (sw 45 + 1) = 6 + tpos J.left J.m₁ := by
      rw [show sw 45 + 1 = sw 46 from rfl, at_index r 46, show (46 : ℕ) = 45 + 1 from rfl,
        at_index h45 1]; rfl
    have t1 := tpos_lt J.left J.m₁
    have t2 := tpos_lt J.whole (J.m₁ + 2 * J.m₂)
    refine (IRS.ifT ht (guarded (convS_irs (Or.inr rfl) (Or.inl rfl) hpe hpo hI hK))).mono (by norm_num) ?_
    rintro c' ⟨h1, h2, h3⟩
    obtain ⟨a1, a2, a3⟩ := convL_val hst hP hcls
    grind [sw]
  · rw [hC] at hcls ⊢
    have ht : ¬ c.nreg sSide < c.nreg K1 := by rw [hs, k1]; norm_num
    have hqE : c.nreg qE < 2 * J.right.m + 6 + 1 := by
      rcases hcls with (h | h) | ⟨-, h⟩ | ⟨h, -⟩ <;> simp only at h <;> omega
    have v34 : c.nreg (sw 34) = 2 * J.right.m + 7 := by rw [at_index r 34, h34]
    have v40 : c.nreg (sw 40) = 6 + tpos J.whole J.m₁ := by
      rw [at_index r 40, show (40 : ℕ) = 40 + 0 from rfl, at_index h40 0]; rfl
    have v41 : c.nreg (sw 40 + 1) = 6 + tpos J.right 0 := by
      rw [show sw 40 + 1 = sw 41 from rfl, at_index r 41, show (41 : ℕ) = 40 + 1 from rfl,
        at_index h40 1]; rfl
    have t1 := tpos_lt J.right 0
    have t2 := tpos_lt J.whole J.m₁
    refine (IRS.ifF ht (guarded (convS_irs (Or.inl rfl) (Or.inr rfl) hpe hpo hI hK))).mono (by norm_num) ?_
    rintro c' ⟨h1, h2, h3⟩
    obtain ⟨a1, a2, a3⟩ := convR_val hst hP hcls
    grind [sw]

set_option maxHeartbeats 4000000 in
/-- **The winner in the walk of `C`.** -/
theorem winVal_sem {J : Merge.Junction} {H : Host} (hI : IInv W c₀ c)
    (hst : SweepEv.St0S P c₀ H J) (hP : J.P.Simple) {z : Point} {σ T : ℝ}
    (hzR : |z.2| < J.whole.radius)
    (hbL : c.nreg bL = 1 → z.2 ≤ J.left.top.2) (hbR : c.nreg bR = 1 → z.2 ≤ J.right.top.2)
    (hpp : ProperPos (chainModel (ModB J (c.nreg bL) (c.nreg bR) (c.nreg (accA + 3)))) (Qof P)
      P.n ⟨c.nreg (accA + 1), c.nreg (accA + 2)⟩)
    (he : c.nreg (accA + 1) < (chainModel (ModB J (c.nreg bL) (c.nreg bR) (c.nreg (accA + 3)))).W.n)
    (hpos : (chainModel (ModB J (c.nreg bL) (c.nreg bR) (c.nreg (accA + 3)))).pos (Qof P)
      ⟨c.nreg (accA + 1), c.nreg (accA + 2)⟩ = rayPt z σ T) :
    winVal c < (chainModel J.whole).W.n ∧
      ProperPos (chainModel J.whole) (Qof P) P.n ⟨winVal c, c.nreg (accA + 2)⟩ ∧
      (chainModel J.whole).pos (Qof P) ⟨winVal c, c.nreg (accA + 2)⟩ = rayPt z σ T := by
  have rr : AgreeOnBand 240000 240700 c.nreg c₀.nreg := fun x h1 h2 =>
    hI.hin _ ⟨h1, h2⟩
  unfold winVal
  split_ifs with h1 h2
  · have hM : ModB J (c.nreg bL) (c.nreg bR) (c.nreg (accA + 3)) = J.left := by
      unfold ModB; simp_all
    rw [hM] at hpp he hpos
    have hcls :=
      posClass_of he hpp.1 hpp.2.1
        (by rwa [hpos, Chazelle.Visibility.rayPt_snd, FuseMath.radius_of_P J (C' := J.left) rfl])
        (Or.inl (by simp_all))
    obtain ⟨a1, a2, a3⟩ := convL_val hst hP hcls
    simp only [at_index rr (sw 45),
      at_index rr (sw 45 + 1),
      at_index rr (sw 45 + 2),
      at_index rr (sw 45 + 4),
      at_index rr (sw 33),
      at_index rr (sw 35)]
    exact ⟨a1, ⟨by rw [a2]; exact hpp.1, by rw [a2]; exact hpp.2.1, hpp.2.2⟩, by simp_all⟩
  · have hM : ModB J (c.nreg bL) (c.nreg bR) (c.nreg (accA + 3)) = J.right := by
      unfold ModB; simp_all
    rw [hM] at hpp he hpos
    have hcls :=
      posClass_of he hpp.1 hpp.2.1
        (by rwa [hpos, Chazelle.Visibility.rayPt_snd, FuseMath.radius_of_P J (C' := J.right) rfl])
        (Or.inl (by simp_all))
    obtain ⟨a1, a2, a3⟩ := convR_val hst hP hcls
    simp only [at_index rr (sw 40),
      at_index rr (sw 40 + 1),
      at_index rr (sw 40 + 2),
      at_index rr (sw 40 + 4),
      at_index rr (sw 34),
      at_index rr (sw 35)]
    exact ⟨a1, ⟨by rw [a2]; exact hpp.1, by rw [a2]; exact hpp.2.1, hpp.2.2⟩, by simp [*]⟩
  · grind [ModB]

/-- The postcondition of a query. -/
def QryPost (J : Merge.Junction) (P : Polygon) (i : ℕ) (L : List (ℕ × ℕ × ℕ)) (j : ℕ)
    (c c' : Config) : Prop :=
  (∃ r : ℕ × ℕ × ℕ × ℕ, c'.nmem (c.nreg pR) = r.1 ∧ c'.nmem (c.nreg pR + 1) = r.2.1 ∧
    c'.nmem (c.nreg pR + 2) = r.2.2.1 ∧ c'.nmem (c.nreg pR + 3) = r.2.2.2 ∧
    SeesInWhole J (Qof P) i (L.getD j (0, 0, 0)) r) ∧
  (∀ a, a < c.nreg ALLOC → (a < c.nreg pR ∨ c.nreg pR + 4 ≤ a) → c'.nmem a = c.nmem a) ∧
  (∀ r, sw 5000 ≤ r → r < sw 6000 → c'.nreg r = c.nreg r) ∧
  c.nreg ALLOC ≤ c'.nreg ALLOC

/-- A frame: registers outside the oracle bands and outside `S` (other than the allocator)
kept, the allocator not lowered, memory below it kept. -/
def PFr (S : ℕ → Prop) (c c' : Config) : Prop :=
  (∀ r, bandOf r ∉ oracleBands → ¬ S r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
    c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)

theorem PFr.trans {S S' : ℕ → Prop} {c₁ c₂ c₃ : Config} (h₁ : PFr S c₁ c₂) (h₂ : PFr S' c₂ c₃)
    (hS : ∀ r, S r → S' r) : PFr S' c₁ c₃ :=
  ⟨fun r h0 h1 h2 => (h₂.1 r h0 h1 h2).trans (h₁.1 r h0 (fun h => h1 (hS r h)) h2),
    h₁.2.1.trans h₂.2.1, fun a ha => (h₂.2.2 a (lt_of_lt_of_le ha h₁.2.1)).trans (h₁.2.2 a ha)⟩

/-- The registers a query writes (besides the slot, the oracle bands and the allocator). -/
def QW (r : ℕ) : Prop := (sw 1000 ≤ r ∧ r < sw 3400) ∨ (sw 4000 ≤ r ∧ r < sw 5000)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 40000 in
/-- **The per-query program.** -/
theorem qry_run {c0 c1 : Stmt} {X : MemCtx} {Ok : Polygon → Model → Prop}
    {Aux : Polygon → Merge.Junction → NF → Config → Prop} {J : Merge.Junction} {H : Host}
    {N₁ N₂ : NF} {E : ℕ} {L : List (ℕ × ℕ × ℕ)} {i j Kc : ℕ}
    (hB : ABase P W X Ok Aux J H N₁ N₂ E L i c₀) (hI : IInv W c₀ c)
    (hpJ : c.nreg pJ = j) (hj : j < L.length) (hpA : c.nreg pA = c₀.nreg (sw 8) + 3 * j)
    (hpR : c.nreg pR = c₀.nreg (sw 11) + 4 * j) (hslot : c.nreg pR + 4 ≤ c.nreg ALLOC)
    (hc : ∀ c', IInv W c₀ c' → QState P J i (qPt J P i L j) c' → c'.nreg qJ = j →
      (i = 1 → c'.nreg qJ < 2 * N₂.nChords →
        (c'.nreg qE, c'.nreg qH, c'.nreg qD) = (sweepEndQ N₂.chords).getD (c'.nreg qJ) (0, 0, 0)) →
      c'.nreg accA = 0 → c'.nreg ALLOC + Kc ≤ W →
      IRS P W c₀ (if i = 0 then c0 else c1) c' Kc
        (fun c'' => CandOut P J (qPt J P i L j) c' c'' ∧ CandFr c' c''))
    (hroom : c.nreg ALLOC + (87100 + Kc) ≤ W) :
    IRS P W c₀ (qryP c0 c1) c (87100 + Kc) (QryPost J P i L j c) := by
  have hA := hB.hA
  have hK := hA.hK
  have hKc := hK.fix hI
  have hQn : (Qof P).n = P.n := shear_n _ _
  set q := L.getD j (0, 0, 0) with hq_def
  have hqL : q ∈ L := by rw [hq_def, List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
  have hqOK := hB.hq q hqL
  have hqht := hB.hht q hqL
  set z := qPt J P i L j with hz_def
  have hzq : (chainModel (sideChain J i)).pos (Qof P) ⟨q.1, q.2.1⟩ = z := rfl
  obtain ⟨hcls, hzR, hzts, hzt, hzC⟩ := query_facts J hqOK
  rw [hzq] at hzR hzts hzt hzC
  have hσ := Sweep.dirOf_cases q.2.2
  have hLm := hB.hLm
  have hAc : c₀.nreg ALLOC ≤ c.nreg ALLOC := hI.hA
  obtain ⟨g1, g2, g3⟩ := hB.hLat j hj
  have hm : AgreeBelow (c₀.nreg ALLOC) c.nmem c₀.nmem := hI.hm
  -- 1. read the query
  refine (IRS.seq (K₂ := 87094 + Kc) (guarded (loadQ_irs hI hK)) ?_).mono
    (by omega) (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' ⟨l1, l2, l3, l4, l5, l6⟩
  have e1 : c₁.nreg qE = q.1 := by
    rw [l2, at_index hm _, hpA, show c₀.nreg (sw 8) + 3 * j = c₀.nreg (sw 8) + 3 * j + 0
      by ring, ← g1]; rfl
  have e2 : c₁.nreg qH = q.2.1 := by rw [l3, at_index hm _, hpA, ← g2]
  have e3 : c₁.nreg qD = q.2.2 := by rw [l4, at_index hm _, hpA, ← g3]
  have e0 : c₁.nreg qJ = j := by rw [l1, hpJ]
  have hside : ∀ c', IInv W c₀ c' → c'.nreg sSide = i := fun c' h' =>
    (at_index h'.hin _).trans hB.hside
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := at_index l5 _
  -- 2. the position in the walk of `C`
  refine (IRS.seq (K₂ := 87070 + Kc) (convQ_sem hI₁ hK hA.hst hA.hP hA.hWm hB.hi (hside c₁ hI₁)
    (by rw [e1, e2]; exact hcls)) ?_).mono (by omega) (fun _ h => h)
  rintro c₂ hI₂ hA₂ hA₂' ⟨v1, v2, v3, v4, v5⟩
  rw [e1, e2] at v2 v3
  rw [hzq] at v3
  have k2 : AgreeExcept [zE, cX, cT, cDd] c₂.nreg c₁.nreg := fun r a b d e =>
    at_index v4 r
  have e1' : c₂.nreg qE = q.1 := by rw [at_index k2 qE, e1]
  have e2' : c₂.nreg qH = q.2.1 := by rw [at_index k2 qH, e2]
  have e3' : c₂.nreg qD = q.2.2 := by rw [at_index k2 qD, e3]
  have e0' : c₂.nreg qJ = j := by rw [at_index k2 qJ, e0]
  have hA2 : c₂.nreg ALLOC = c.nreg ALLOC := by
    rw [at_index k2 ALLOC, hA1]
  -- 3. the flag
  obtain ⟨-, hq1, hqn, hp0, hp1, -, -⟩ := hqOK
  have hpp2 : ProperPos (chainModel J.whole) (Qof P) P.n ⟨c₂.nreg zE, c₂.nreg qH⟩ := by
    rw [e2']; exact ⟨by rw [v2]; exact hp0, by rw [v2]; exact hp1, by grind⟩
  refine (IRS.seq (K₂ := 52063 + Kc) (guarded (flagS_irs hI₂ hA.hP (hA.ctxW hI₂) v1 hpp2
    (by rw [e2']; exact v3) hzR hzC)) ?_).mono (by omega) (fun _ h => h)
  rintro c₃ hI₃ hA₃ hA₃' ⟨u1, u2, u3, u4, u5, u6⟩
  rw [e3'] at u2 u3
  have k3 : ∀ r, bandOf r ∉ oracleBands → r ≠ zF → r ≠ zP → r ≠ zPh → r ≠ ALLOC →
    c₃.nreg r = c₂.nreg r := u4
  have s3 : ∀ r, 240000 ≤ r → r < 250000 → r ≠ zF → r ≠ zP → r ≠ zPh →
      c₃.nreg r = c₂.nreg r := fun r h1 h2 a b d =>
    guarded (k3 r (not_oracle_sw h1 h2) a b d)
  have hKc3 := hK.fix hI₃
  -- the slot
  have hR3 : c₃.nreg pR = c.nreg pR := by
    rw [at_index s3 pR, at_index k2 pR,
      at_index l5 pR]
  have hslotA : c₀.nreg ALLOC ≤ c.nreg pR := by
    rw [hpR, hB.hres]; omega
  -- the frame so far
  have fr3 : PFr QW c c₃ := by
    refine ⟨fun r h0 h1 h2 => ?_, by omega, fun a ha => ?_⟩
    · have : ¬ (sw 3200 ≤ r ∧ r < sw 3400) := fun h => h1 (Or.inl ⟨by unfold sw at *; omega, h.2⟩)
      rw [k3 r h0 (by rne) (by rne) (by rne) h2, at_index k2 r,
        at_index l5 r]
    · frame_simp [u6, v5, l6]
  by_cases hf : c₃.nreg zF < c₃.nreg K1
  · -- not free: the zero record
    have hz0 : ¬ FreeAt J.whole z (dirOf q.2.2) := fun h => by
      have := u2.2 h; rw [hKc3.2.1] at hf; omega
    refine (IRS.ifT hf (guarded (store4_irs hI₃ hK))).mono (by omega) ?_
    rintro c' ⟨w1, w2⟩
    have k0 : c₃.nreg K0 = 0 := hKc3.1
    rw [hR3, k0] at w1
    refine ⟨⟨(0, 0, 0, 0), ?_, ?_, ?_, ?_, guarded (seesInWhole_notFree' J (Qof P) i q hzq rfl hz0 _)⟩, fun a ha hout => ?_, fun r h1 h2 => ?_, ?_⟩
    · rw [w1]; unfold mem4'; simp
    · rw [w1]; unfold mem4'; simp
    · rw [w1]; unfold mem4'; simp
    · rw [w1]; unfold mem4'; simp
    · rw [w1]; unfold mem4'
      block_post
    · rw [at_index w2 r]
      exact fr3.1 r (guarded not_oracle_sw)
        (by address_omega) (by rne)
    · rw [at_index w2 ALLOC]; exact fr3.2.1
  -- free: the candidates
  have hf1 : c₃.nreg zF = 1 := by rw [hKc3.2.1] at hf; omega
  have hfree : FreeAt J.whole z (dirOf q.2.2) := u2.1 hf1
  obtain ⟨a1, a2, a3⟩ := u3 hf1
  have q3E : c₃.nreg qE = q.1 := by rw [at_index s3 qE, e1']
  have q3H : c₃.nreg qH = q.2.1 := by rw [at_index s3 qH, e2']
  have q3D : c₃.nreg qD = q.2.2 := by rw [at_index s3 qD, e3']
  have q3J : c₃.nreg qJ = j := by rw [at_index s3 qJ, e0']
  have q3zE : c₃.nreg zE = c₂.nreg zE := at_index s3 zE
  have hvz : ((Qof P).vtx (q.2.1 - 1)).2 = z.2 := by rw [← hqht, hzq]
  refine (IRS.ifF hf (K := 52061 + Kc) ?_).mono (by omega) (fun _ h => h)
  -- 5. the bits
  refine (IRS.seq (K₂ := 35095 + Kc) (bitsQ_irs hI₃ hK hB.hi (hside c₃ hI₃) (hA.ctxL hI₃)
    (hA.ctxR hI₃) (by grind)
    (fun h0 => by
      rw [q3H, hvz]; have := hzts; subst h0; simpa [sideChain] using this)
    (fun h1 => by
      rw [q3H, hvz]; have := hzts; subst h1; simpa [sideChain] using this)
    (by omega)) ?_).mono (by omega) (fun _ h => h)
  rintro c₄ hI₄ hA₄ hA₄' ⟨⟨b1, b2⟩, ⟨b3, b4⟩, b5, b6, b7⟩
  rw [q3H, hvz] at b2 b4
  have s4 : ∀ r, 240000 ≤ r → r < 250000 → r ≠ bL → r ≠ bR → ¬ (sw 3230 ≤ r ∧ r < sw 3300) →
      c₄.nreg r = c₃.nreg r := fun r h1 h2 a b d =>
    guarded (b5 r (not_oracle_sw h1 h2) a b d)
  -- 6. clear the accumulator
  have okA : okB W c₄.nmem [.constN accA 0] c₄.nreg :=
    ⟨⟨guarded iscr_sw, Nat.zero_le _⟩, trivial⟩
  refine (IRS.seq (K₂ := 35094 + Kc) (IRS.block _ hI₄ okA) ?_).mono (by simp; omega) (fun _ h => h)
  rintro c₅ hI₅ - - hc5
  have v5 : AgreeExcept [accA] c₅.nreg c₄.nreg := fun r hr => by
    rw [hc5]; simp only [regB, regI]; exact upd_other _ _ _ hr
  have acc5 : c₅.nreg accA = 0 := by rw [hc5]; simp only [regB, regI, upd_same]
  have m5 : c₅.nmem = c₄.nmem := by rw [hc5]
  have s5 : ∀ r, 240000 ≤ r → r < 250000 → r ≠ bL → r ≠ bR → ¬ (sw 3230 ≤ r ∧ r < sw 3300) →
      r ≠ accA → c₅.nreg r = c₃.nreg r := fun r h1 h2 a b d e => by
    rw [v5 r e, s4 r h1 h2 a b d]
  have hA5 : c₅.nreg ALLOC = c₄.nreg ALLOC := at_index v5 _
  have q5E : c₅.nreg qE = q.1 := by
    rw [at_index s5 qE, q3E]
  have q5H : c₅.nreg qH = q.2.1 := by
    rw [at_index s5 qH, q3H]
  have q5D : c₅.nreg qD = q.2.2 := by
    rw [at_index s5 qD, q3D]
  have q5J : c₅.nreg qJ = j := by
    rw [at_index s5 qJ, q3J]
  have q5zE : c₅.nreg zE = c₂.nreg zE := by
    rw [at_index s5 zE, q3zE]
  have q5P : c₅.nreg zP = c₃.nreg zP := at_index s5 zP
  have q5Ph : c₅.nreg zPh = c₃.nreg zPh :=
    at_index s5 zPh
  have q5bL : c₅.nreg bL = c₄.nreg bL := at_index v5 _
  have q5bR : c₅.nreg bR = c₄.nreg bR := at_index v5 _
  have hQS : QState P J i z c₅ := by
    refine ⟨by rw [q5E, q5H, q5D]; exact hB.hq q hqL, by grind,
      by rw [q5E, q5H]; exact hzq, by rw [q5zE]; exact v1, by grind,
      by rw [q5zE, q5H, ← e2']; rw [e2']; exact v3, by rw [q5D]; exact hfree,
      by rw [q5P]; exact a1, by grind, by rw [q5P, q5Ph, q5D]; exact a3,
      by grind, by rw [q5bR]; exact ⟨b3, b4⟩⟩
  have hend5 : i = 1 → c₅.nreg qJ < 2 * N₂.nChords →
      (c₅.nreg qE, c₅.nreg qH, c₅.nreg qD) =
        (sweepEndQ N₂.chords).getD (c₅.nreg qJ) (0, 0, 0) := by
    intro hi1 hlt
    obtain ⟨L₁, hL, -⟩ := hB.hend hi1
    rw [q5E, q5H, q5D, q5J]
    rw [q5J] at hlt
    have hlen : (sweepEndQ N₂.chords).length = 2 * N₂.nChords := by
      simp [sweepEndQ, NF.nChords]
    show q = _
    rw [hq_def, hL, guarded (List.getD_append _ _ _ _)]
  -- 7. the candidate step
  have hKc5 := hK.fix hI₅
  have hdisp : IRS P W c₀ (.ifLtN sSide K1 c0 c1) c₅ (Kc + 2)
      (fun c'' => CandOut P J z c₅ c'' ∧ CandFr c₅ c'') := by
    have hcand := guarded (hc c₅ hI₅ hQS q5J hend5 acc5)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hB.hi with h0 | h0
    · rw [ite_eq_left h0] at hcand
      exact IRS.ifT (by rw [hside c₅ hI₅, hKc5.2.1, h0]; norm_num) hcand
    · rw [guarded ite_eq_right] at hcand
      exact IRS.ifF (by rw [hside c₅ hI₅, hKc5.2.1, h0]; norm_num) hcand
  refine (IRS.seq (K₂ := 35068) hdisp ?_).mono (by omega) (fun _ h => h)
  rintro c₆ hI₆ hA₆ hA₆' ⟨⟨Lc, hacc, hgood, hhit⟩, cf1, cf2, cf3⟩
  rw [q5D] at hacc hgood hhit
  obtain ⟨wf, wt, wpp, we, wpos⟩ := winner_eq hacc hgood hhit
  have s6 : ∀ r, 240000 ≤ r → r < 250000 → ¬ (sw 1000 ≤ r ∧ r < sw 3200) →
      ¬ (sw 3230 ≤ r ∧ r < sw 3400) → ¬ (sw 4000 ≤ r ∧ r < sw 5000) → c₆.nreg r = c₅.nreg r :=
    fun r h1 h2 a b d => guarded (cf1 r (not_oracle_sw h1 h2) a b d)
  have q6bL : c₆.nreg bL = c₅.nreg bL := at_index s6 bL
  have q6bR : c₆.nreg bR = c₅.nreg bR := at_index s6 bR
  rw [← q6bL, ← q6bR] at wpp we wpos
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h40, h45, h33, h34, h35, -⟩ := id hA.hst
  have rr6 : AgreeOnBand 240000 240700 c₆.nreg c₀.nreg := fun x h1 h2 =>
    hI₆.hin _ ⟨h1, h2⟩
  have hmL : J.left.m ≤ J.whole.m := sideChain_m_le J 0
  have hmR : J.right.m ≤ J.whole.m := sideChain_m_le J 1
  have hWm := hA.hWm
  -- 8. the winner in the walk of `C`
  refine (IRS.seq (K₂ := 35038) (winQ_irs hI₆ hK ⟨by rw [q6bL, q5bL]; exact b1,
      by rw [q6bR, q5bR]; exact b3⟩ (fun t0 l1 => ?_) (fun t1 r1 => ?_)) ?_).mono (by omega)
    (fun _ h => h)
  · have hM : ModB J (c₆.nreg bL) (c₆.nreg bR) (c₆.nreg (accA + 3)) = J.left := by
      unfold ModB; rw [ite_eq_left ⟨t0, l1⟩]
    rw [hM, cm_n] at we
    have t1 := tpos_lt J.left J.m₁
    have t2 := tpos_lt J.whole (J.m₁ + 2 * J.m₂)
    rw [at_index rr6 (sw 33), at_index rr6 (sw 45 + 1),
      at_index rr6 (sw 45), at_index rr6 (sw 35), h33, h35, show sw 45 = sw (45 + 0) from rfl, at_index h45 0,
      show sw (45 + 0) + 1 = sw (45 + 1) from rfl, at_index h45 1]
    simp only [cstL, List.getD_cons_zero, List.getD_cons_succ]
    refine ⟨by omega, by show 6 + tpos J.left J.m₁ < _; omega, by omega, by omega, by omega⟩
  · have hM : ModB J (c₆.nreg bL) (c₆.nreg bR) (c₆.nreg (accA + 3)) = J.right := by
      unfold ModB; rw [guarded ite_eq_right, ite_eq_left ⟨t1, r1⟩]
    rw [hM, cm_n] at we
    have t1 := tpos_lt J.right 0
    have t2 := tpos_lt J.whole J.m₁
    rw [at_index rr6 (sw 34), at_index rr6 (sw 40 + 1),
      at_index rr6 (sw 40), at_index rr6 (sw 35), h34, h35, show sw 40 = sw (40 + 0) from rfl, at_index h40 0,
      show sw (40 + 0) + 1 = sw (40 + 1) from rfl, at_index h40 1]
    simp only [cstR, List.getD_cons_zero, List.getD_cons_succ]
    refine ⟨by omega, by omega, by omega, by omega, by omega⟩
  rintro c₇ hI₇ hA₇ hA₇' ⟨y1, y2, y3, y4⟩
  obtain ⟨w1, w2, w3⟩ := winVal_sem hI₆ hA.hst hA.hP hzR
    (fun h => by rw [q6bL, q5bL] at h; exact b2.1 h) (fun h => by rw [q6bR, q5bR] at h; exact b4.1 h)
    wpp we wpos
  rw [← y1] at w1
  rw [← y1, ← y2] at w2 w3
  have s7 : ∀ r, 240000 ≤ r → r < 250000 → ¬ (sw 1000 ≤ r ∧ r < sw 3200) →
      ¬ (sw 3230 ≤ r ∧ r < sw 3400) → ¬ (sw 4000 ≤ r ∧ r < sw 5000) → r ≠ yE → r ≠ yH →
      c₇.nreg r = c₅.nreg r := fun r h1 h2 a b d e f => by
    rw [guarded (y3 r e f), s6 r h1 h2 a b d]
  have q7D : c₇.nreg qD = q.2.2 := by
    rw [at_index s7 qD, q5D]
  have q7H : c₇.nreg qH = q.2.1 := by
    frame_simp [s7, q5H]
  have q7P : c₇.nreg zP = c₃.nreg zP := by
    frame_simp [s7, q5P]
  have q7Ph : c₇.nreg zPh = c₃.nreg zPh := by
    frame_simp [s7, q5Ph]
  have hA7 : c₇.nreg ALLOC = c₆.nreg ALLOC := at_index y3 _
  -- 9. the record
  refine (IRS.seq (K₂ := 8) (guarded (recS_irs hI₇ hK hA.hP (hA.ctxW hI₇) hzt (by rw [q7D]; exact hfree)
    rfl (by rw [q7D, q7P, q7Ph]; exact a3) w1 w2 (by rw [q7D]; exact w3) hzR
    (h := q.2.1 - 1) hvz)) ?_).mono (by simp [recK]) (fun _ h => h)
  rintro c₈ hI₈ hA₈ hA₈' ⟨hRD, x1, x2, x3⟩
  rw [q7D, q7P] at hRD
  have hSee := seesInWhole_hit J P.Qof i q hzq rfl hzt ⟨hfree, rfl⟩ hRD
  have k8 : ∀ r ≥ 240000, r < 250000 → r ≠ rho → r ≠ wF → r ≠ wP → r ≠ wPh → r ≠ rL →
      r ≠ rR → c₈.nreg r = c₇.nreg r := fun r h1 h2 a b d e f g =>
    guarded (x1 r (not_oracle_sw h1 h2) a b d e f g)
  have q8H : c₈.nreg qH = q.2.1 := by
    frame_simp [k8, q7H]
  -- 10. the height code minus one
  have hKc8 := hK.fix hI₈
  have okH : okB W c₈.nmem [.subN tH qH K1] c₈.nreg := ⟨guarded iscr_sw, trivial⟩
  refine IRS.seq (K₂ := 7) (IRS.block _ hI₈ okH) ?_
  rintro c₉ hI₉ - - hc9
  have v9 : AgreeExcept [tH] c₉.nreg c₈.nreg := fun r hr => by
    simp [hc9, regB, regI]; exact upd_other _ _ _ hr
  have t9 : c₉.nreg tH = q.2.1 - 1 := by
    simp [hc9, regB, regI, upd_same, q8H, hKc8.2.1]
  have m9 : c₉.nmem = c₈.nmem := by rw [hc9]
  -- the frame up to the store
  have fr4 : PFr QW c₃ c₄ := ⟨fun r h0 h1 h2 => b5 r h0
      (by intro h; apply h1; subst h; left; rne) (by intro h; apply h1; subst h; left; rne)
      (fun h => h1 (Or.inl ⟨by unfold sw at *; omega, by unfold sw at *; omega⟩)) h2, b6, b7⟩
  have fr5 : PFr QW c₄ c₅ := ⟨fun r _ h1 _ => at_index v5 r,
      by omega, fun a _ => by rw [m5]⟩
  have fr6 : PFr QW c₅ c₆ := ⟨fun r h0 h1 h2 => cf1 r h0
      (fun h => h1 (Or.inl ⟨h.1, by unfold sw at *; omega⟩))
      (fun h => h1 (Or.inl ⟨by unfold sw at *; omega, h.2⟩)) (fun h => h1 (Or.inr h)) h2, cf2, cf3⟩
  have fr7 : PFr QW c₆ c₇ := ⟨fun r _ h1 _ => at_index y3 r,
      by omega, fun a _ => by rw [y4]⟩
  have fr8 : PFr QW c₇ c₈ := ⟨fun r h0 h1 h2 => x1 r h0
      (by intro h; apply h1; subst h; left; rne) (by intro h; apply h1; subst h; left; rne)
      (by intro h; apply h1; subst h; left; rne) (by intro h; apply h1; subst h; left; rne)
      (by intro h; apply h1; subst h; left; rne) (by intro h; apply h1; subst h; left; rne) h2,
      x2, x3⟩
  have fr9 : PFr QW c₈ c₉ := ⟨fun r _ h1 _ => at_index v9 r,
      by rw [at_index v9 ALLOC], fun a _ => by rw [m9]⟩
  have fr : PFr QW c c₉ := ((((((fr3.trans fr4 (fun _ h => h)).trans fr5 (fun _ h => h)).trans
    fr6 (fun _ h => h)).trans fr7 (fun _ h => h)).trans fr8 (fun _ h => h)).trans fr9
    (fun _ h => h))
  have hR9 : c₉.nreg pR = c.nreg pR := guarded (fr.1 pR (not_oracle_sw (by rne) (by rne)))
  -- 11. the store
  refine (guarded (store4_irs hI₉ hK)).mono le_rfl ?_
  rintro c' ⟨w1, w2⟩
  rw [hR9, (hK.fix hI₉).2.1, t9, at_index v9 rL, at_index v9 rR] at w1
  refine ⟨⟨(1, q.2.1 - 1, c₈.nreg rL, c₈.nreg rR), ?_, ?_, ?_, ?_, hSee⟩,
    fun a ha hout => ?_, fun r h1 h2 => ?_, ?_⟩
  all_goals try (solve | rw [w1]; unfold mem4'; simp)
  · rw [w1]; unfold mem4'
    simp only [upd]
    rw [guarded ite_eq_right, guarded ite_eq_right, guarded ite_eq_right, guarded ite_eq_right]
    exact fr.2.2 a ha
  · rw [at_index w2 r]
    exact fr.1 r (guarded not_oracle_sw)
      (by unfold QW; unfold sw at *; omega) (by rne)
  · rw [at_index w2 ALLOC]; exact fr.2.1

open Classical in
/-- The cost of the candidate step of a query. -/
noncomputable def candK (κ0 κ1 F : ℕ → ℕ) (c₀ : Config) (J : Merge.Junction) (P : Polygon)
    (N₁ N₂ : NF) (L : List (ℕ × ℕ × ℕ)) (i j : ℕ) : ℕ :=
  if i = 0 then κ0 (c₀.nreg (sw 6)) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1)
  else κ1 (c₀.nreg (sw 6)) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) +
    (if BruteQ J N₂ j (qPt J P i L j) then
      κ1 (c₀.nreg (sw 6)) * (N₁.arcs.length + 1) * (F (c₀.nreg (sw 5)) + 1) else 0)

theorem candK_le (κ0 κ1 F : ℕ → ℕ) (c₀ : Config) (J : Merge.Junction) (P : Polygon)
    (N₁ N₂ : NF) (L : List (ℕ × ℕ × ℕ)) {i : ℕ} (hi : i ≤ 1) (j : ℕ) :
    87100 + candK κ0 κ1 F c₀ J P N₁ N₂ L i j ≤
      qCost (fun D => κ0 D + κ1 D + 87100) F c₀ J P N₁ N₂ L i j := by
  grind [candK, qCost]

open Classical in
/-- **The per-query procedure from the candidate steps.** -/
theorem qry_of_cands (h0 : Cand0Spec) (h1 : Cand1Spec) :
    ∃ (init0 : Stmt) (Aux : Polygon → Merge.Junction → NF → Config → Prop) (κ0 : ℕ → ℕ),
      InitSpec init0 Aux κ0 ∧ QrySpec Aux := by
  obtain ⟨init0, cand0, Aux, κ0, hInit, hRob, hC0⟩ := h0
  obtain ⟨cand1, κ1, hC1⟩ := h1
  refine ⟨init0, Aux, κ0, hInit, fun sh => qryP (cand0 sh) (cand1 sh),
    fun D => κ0 D + κ1 D + 87100, ?_⟩
  intro sh Bs F X Ok hsh hBs hXl P W c₀ c J H N₁ N₂ E L i j hB hI hpJ hj hpA hpR hslot hroom
  have hle := candK_le κ0 κ1 F c₀ J P N₁ N₂ L hB.hi j
  refine (qry_run (c0 := cand0 sh) (c1 := cand1 sh) (Kc := candK κ0 κ1 F c₀ J P N₁ N₂ L i j) hB
    hI hpJ hj hpA hpR hslot ?_ (by omega)).mono hle (fun c' h => h)
  intro c' hI' hQS hqJ hend hacc hroom'
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hB.hi with h0 | h0
  · subst h0
    exact hC0 sh Bs F X Ok hsh hBs hXl P W c₀ c' J H N₁ N₂ E _ hB.hA (hB.hAux rfl) hI' hQS hacc
      hroom'
  · subst h0
    simp
    have hk : candK κ0 κ1 F c₀ J P N₁ N₂ L 1 j =
        κ1 (c₀.nreg (sw 6)) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) +
          (if BruteQ J N₂ (c'.nreg qJ) (qPt J P 1 L j) then
            κ1 (c₀.nreg (sw 6)) * (N₁.arcs.length + 1) * (F (c₀.nreg (sw 5)) + 1) else 0) := by
      simp [candK, hqJ]
    rw [hk] at hroom' ⊢
    exact hC1 sh Bs F X Ok hsh hBs hXl P W c₀ c' J H N₁ N₂ E _ hB.hA hI' hQS (hend rfl) hacc
      hroom'

end

end SweepIo

end Chazelle.Core
