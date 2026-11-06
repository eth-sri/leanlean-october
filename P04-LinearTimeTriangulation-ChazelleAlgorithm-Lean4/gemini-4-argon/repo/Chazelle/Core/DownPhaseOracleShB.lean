module

public import Chazelle.Core.DownPhaseOracleShA

/-!
# WP-M (E7-B, RAM part 9): the running best hit of the interior shooter

The interior shooter keeps the first hit found so far (`BestI`): the flag `170070` and the
boundary symbolic point of the hit in `170071 …`.  After a shot of the chain shooter at a chain
arc `A` (its answer in `140010 … 140012`), `updI` turns a hit into its boundary symbolic point
(`hsI`) and keeps the nearer of the two hits (one abscissa test in the direction of the ray,
`cmpI`): `updI_exec`, the running best then describes the first hit on the union.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace IOrc

open Machine Machine.Stmt Programs SignK WalkKey SweepPrim
open Chazelle.Visibility (rayPt)

@[expose] public section

/-! ## The programs -/

/-- Take the new hit. -/
def takeI : Stmt :=
  block [.constN 170070 1, .copyN 170071 170130, .copyN 170072 170131, .copyN 170073 170132]

/-- `170141 := 1` iff the new hit (`170130`) is nearer than the best one (`170071`) in the
direction of the ray. -/
def cmpI : Stmt :=
  .ifLtN 170008 170011 (kbit 170071 170130 170071 0 170141)
    (.ifLtN 170011 170008 (kbit 170071 170130 170071 0 170141)
      (kbit 170130 170071 170130 0 170141))

/-- **The update of the running best hit** after a shot. -/
def updI : Stmt :=
  .ifLtN 140010 170011 .skip
    (.ifLtN 170011 140010 .skip
      (.seq hsI
        (.ifLtN 170070 170011 takeI
          (.seq cmpI (.ifLtN 170012 170141 takeI .skip)))))

/-- The registers `updI` writes. -/
def Bupd (r : ℕ) : Bool :=
  decide (170070 ≤ r ∧ r < 170074) || decide (170130 ≤ r ∧ r < 170142) || Bk r

theorem wr_updI : wr Bupd updI = true := by
  have hk : ∀ a b d op, wr Bupd (kbit a b d op 170141) = true := fun a b d op =>
    SweepPrim.wr_mono (SweepPrim.wr_kbit a b d op 170141) (fun r hr => by
      simp only [SweepPrim.Bkb, Bool.or_eq_true, beq_iff_eq] at hr
      unfold Bupd; rcases hr with hr | hr
      · simp [hr]
      · subst hr; simp)
  have hs := SweepPrim.wr_mono wr_hsI (B' := Bupd) (fun r hr => by
    simp only [Bhs, Bupd, Bool.or_eq_true, decide_eq_true_eq] at hr ⊢; omega)
  simp only [updI, cmpI, takeI, wr, block, wrOK, hk, hs, Bool.and_true, Bool.true_and]
  decide

/-! ## The running best hit -/

/-- **The running best hit** describes the first hit of the ray from `z` in direction `σ` on
`S`. -/
def BestI (P : Polygon) (c : Config) (S : Set Point) (z : Point) (σ : ℝ) : Prop :=
  c.nreg 170070 ≤ 1 ∧
    (c.nreg 170070 = 1 → ∃ sb t, SymPtIn c 170071 sb ∧ BSym (Qof P) sb ∧ FirstHit S z σ t ∧
      sb.eval (Qof P) = rayPt z σ t) ∧
    (c.nreg 170070 ≠ 1 → NoHit S z σ)

theorem BestI.keep {P : Polygon} {c c' : Config} {S : Set Point} {z : Point} {σ : ℝ}
    (h : BestI P c S z σ) (hk : ∀ r, 170070 ≤ r → r < 170074 → c'.nreg r = c.nreg r) :
    BestI P c' S z σ := by
  obtain ⟨h0, h1, h2⟩ := h
  have k0 : c'.nreg 170070 = c.nreg 170070 := hk _ le_rfl (by norm_num)
  refine ⟨by rwa [k0], fun hf => ?_, fun hf => h2 (by rwa [← k0])⟩
  obtain ⟨sb, t, hs, hb, hfh, hev⟩ := h1 (by rwa [← k0])
  exact ⟨sb, t, symPtIn_of_eq hs (fun j h1 h2 => hk j (by omega) (by omega)), hb, hfh, hev⟩

/-- The empty best: no hit on the empty set. -/
theorem bestI_empty {P : Polygon} {c : Config} {z : Point} {σ : ℝ} (h : c.nreg 170070 = 0) :
    BestI P c ∅ z σ :=
  ⟨by omega, fun hf => by omega, fun _ t _ hm => hm⟩

/-! ## Execution -/

section exec

variable {P : Polygon} {W : ℕ}

/-- **Taking the new hit.** -/
theorem takeI_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) {sn : SymPt}
    (hs : SymPtIn c 170130 sn) :
    ∃ c' k, Exec P W takeI c c' k ∧ k = 4 ∧ c'.nreg 170070 = 1 ∧ SymPtIn c' 170071 sn := by
  unfold takeI
  exec_block
  · omega
  exact ⟨rfl, by config_simp, NFLoc.symPtIn_copy hs (by config_simp) (by config_simp)
    (by config_simp)⟩

/-- **The comparison of two hits on one ray.** -/
theorem cmpI_exec (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P) (hW : P.n + 3 ≤ W)
    (h11 : c.nreg 170011 = 1) {sn sb : SymPt} (hsn : SymPtIn c 170130 sn)
    (hsb : SymPtIn c 170071 sb) (hln : sn.Lt P.n) (hlb : sb.Lt P.n) {z : Point} {t₁ t₂ : ℝ}
    (hen : sn.eval (Qof P) = rayPt z (dirOf (c.nreg 170008)) t₂)
    (heb : sb.eval (Qof P) = rayPt z (dirOf (c.nreg 170008)) t₁) :
    ∃ c' k, Exec P W cmpI c c' k ∧ k ≤ 245 ∧ c'.nreg 170141 ≤ 1 ∧
      (c'.nreg 170141 = 1 ↔ t₂ < t₁) ∧ FrameB (SweepPrim.Bkb 170141) c c' := by
  unfold cmpI
  by_cases h1 : c.nreg 170008 < c.nreg 170011
  · have hd : dirOf (c.nreg 170008) = -1 := by unfold dirOf; rw [ite_eq_right (by omega)]
    obtain ⟨c', k, e, hk, F, b1, b2⟩ := kbit_exec (P := P) hG hW c hw (a := 170071) (b := 170130)
      (d := 170071) (op := 0) (dst := 170141) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hlb hln hlb hsb hsn hsb
    refine ⟨c', _, .ifLtN_true h1 e, by omega, b1, ?_, F⟩
    rw [b2, SignTest, heb, hen, hd]; simp only [Visibility.rayPt_fst]
    constructor <;> intro h <;> linarith
  · by_cases h2 : c.nreg 170011 < c.nreg 170008
    · have hd : dirOf (c.nreg 170008) = -1 := by unfold dirOf; rw [ite_eq_right (by omega)]
      obtain ⟨c', k, e, hk, F, b1, b2⟩ := kbit_exec (P := P) hG hW c hw (a := 170071) (b := 170130)
        (d := 170071) (op := 0) (dst := 170141) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hlb hln hlb hsb hsn hsb
      refine ⟨c', _, .ifLtN_false h1 (.ifLtN_true h2 e), by omega, b1, ?_, F⟩
      rw [b2, SignTest, heb, hen, hd]; simp only [Visibility.rayPt_fst]
      constructor <;> intro h <;> linarith
    · have hd : dirOf (c.nreg 170008) = 1 := by unfold dirOf; rw [ite_eq_left (by omega)]
      obtain ⟨c', k, e, hk, F, b1, b2⟩ := kbit_exec (P := P) hG hW c hw (a := 170130) (b := 170071)
        (d := 170130) (op := 0) (dst := 170141) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hln hlb hln hsn hsb hsn
      refine ⟨c', _, .ifLtN_false h1 (.ifLtN_false h2 e), by omega, b1, ?_, F⟩
      rw [b2, SignTest, heb, hen, hd]; simp only [Visibility.rayPt_fst]
      constructor <;> intro h <;> linarith

/-- **The update of the running best hit** after a shot at a chain arc `A` of the chain `C`
(the shooter's answer in `140010 … 140012`). -/
theorem updI_exec (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P) {cs L S v : ℕ}
    (hR : HRegs P W c cs L S v) {C : Chain} (hC : C.P = Qof P) (hCs : C.s = cs) (hCm : C.m = L)
    (hCS : C.sideS C.sideBeta = S) (hv : v = (C.s + C.topIdx) % (Qof P).n) {e h : ℕ}
    (he : c.nreg 140011 = e) (hh : c.nreg 140012 = h) (he2 : c.nreg 140010 = 1 → e < 2 * L + 7)
    {A Sp : Set Point} {z : Point} {σ : ℝ} (hσ : σ = dirOf (c.nreg 170008)) (hAC : A ⊆ C.set)
    (hhit : c.nreg 140010 = 1 → ∃ t, FirstHit A z σ t ∧
      ProperPos (chainModel C) (Qof P) P.n ⟨e, h⟩ ∧ (chainModel C).pos (Qof P) ⟨e, h⟩ = rayPt z σ t)
    (hno : c.nreg 140010 ≠ 1 → NoHit A z σ) (hB : BestI P c Sp z σ) :
    ∃ c' k, Exec P W updI c c' k ∧ k ≤ 600 ∧ BestI P c' (Sp ∪ A) z σ ∧ FrameB Bupd c c' := by
  have hW := hR.hW
  have hQ : (Qof P).n = P.n := qn'
  have hD : DistinctHeights (Qof P) := (goodShear_epsOf hG.2).2.1
  suffices hX : ∃ c' k, Exec P W updI c c' k ∧ k ≤ 600 ∧ BestI P c' (Sp ∪ A) z σ by
    obtain ⟨c', k, ex, hk, b⟩ := hX
    exact ⟨c', k, ex, hk, b, exec_frameB ex wr_updI⟩
  obtain ⟨hb1, hb2, hb3⟩ := hB
  -- no hit
  have nohit : c.nreg 140010 ≠ 1 → BestI P c (Sp ∪ A) z σ := fun hf => by
    have hn := hno hf
    refine ⟨hb1, fun h1 => ?_, fun h1 => noHit_union (hb3 h1) hn⟩
    obtain ⟨sb, t, hs, hbs, hfh, hev⟩ := hb2 h1
    exact ⟨sb, t, hs, hbs, firstHit_noHit hfh hn, hev⟩
  unfold updI
  by_cases f1 : c.nreg 140010 < c.nreg 170011
  · refine spec_ifLtN_true f1 (spec_skip hw ⟨by omega, nohit (by rw [hR.r11] at f1; omega)⟩)
  refine spec_ifLtN_false f1 ?_
  by_cases f2 : c.nreg 170011 < c.nreg 140010
  · refine spec_ifLtN_true f2 (spec_skip hw ⟨by omega, nohit (by rw [hR.r11] at f2; omega)⟩)
  refine spec_ifLtN_false f2 ?_
  have hf : c.nreg 140010 = 1 := by rw [hR.r11] at f1 f2; omega
  replace he2 := he2 hf
  obtain ⟨t₂, hA, hp, hpos⟩ := hhit hf
  -- the symbolic point of the hit
  obtain ⟨c₁, k₁, e₁, hk₁, s₁, F₁⟩ := hsI_exec (P := P) c hw hR he hh he2
  have hv' : v = (C.s + C.topIdx) % C.P.n := by rwa [hC]
  have hsym := hitSym_ch (C := C) hv' (e := e) (h := h) (by rwa [hCm])
  rw [hCs, hCm, show sSV C.sideBeta C.topIdx L = S by rw [← hCS]; unfold sSV Chain.sideS; rw [hCm],
    hC, hQ] at hsym
  have hmem : (chainModel C).pos C.P ⟨e, h⟩ ∈ C.set := by
    rw [hC, hpos]; exact hAC hA.2.1
  have hDC : DistinctHeights C.P := by rwa [hC]
  have hpC : ProperPos (chainModel C) C.P C.P.n ⟨e, h⟩ := by
    rwa [hC, hQ]
  obtain ⟨hbsym, hev⟩ := hitSym_spec C hDC hpC (by rwa [hCm]) hmem
  rw [hsym, hC] at hbsym hev
  rw [hpos] at hev
  set sn := hitSymV P.n cs L S v e h
  have hlt : sn.Lt P.n := by have := hbsym.lt; rwa [hQ] at this
  have w₁ := e₁.wb_right
  have f₁ : ∀ r, Bhs r = false → c₁.nreg r = c.nreg r := F₁.1
  refine spec_seq ⟨c₁, k₁, e₁, ?_⟩
  have b70 : c₁.nreg 170070 = c.nreg 170070 := f₁ _ (by decide)
  have b11 : c₁.nreg 170011 = 1 := by rw [f₁ _ (by decide)]; exact hR.r11
  by_cases g : c₁.nreg 170070 < c₁.nreg 170011
  · -- no best yet: take the new hit
    have hb0 : c.nreg 170070 ≠ 1 := by rw [b70, b11] at g; omega
    refine spec_ifLtN_true g ?_
    obtain ⟨c₂, k₂, e₂, hk₂, a70, s₂⟩ := takeI_exec (P := P) c₁ w₁ (by omega) s₁
    refine ⟨c₂, k₂, e₂, by omega, by omega, fun _ => ⟨sn, t₂, s₂, hbsym, ?_, hev⟩,
      fun h => absurd a70 h⟩
    exact noHit_firstHit (hb3 hb0) hA
  refine spec_ifLtN_false g ?_
  have hb1' : c.nreg 170070 = 1 := by rw [b70, b11] at g; omega
  obtain ⟨sb, t₁, hsb, hbsb, hfh, hevb⟩ := hb2 hb1'
  have hsb₁ : SymPtIn c₁ 170071 sb := symPtIn_of_eq hsb (fun j h1 h2 => f₁ j (by
    unfold Bhs; simp only [decide_eq_false_iff_not]; omega))
  have hltb : sb.Lt P.n := by have := hbsb.lt; rwa [hQ] at this
  have d8 : c₁.nreg 170008 = c.nreg 170008 := f₁ _ (by decide)
  obtain ⟨c₂, k₂, e₂, hk₂, b41, i41, F₂⟩ := cmpI_exec (P := P) c₁ w₁ hG (by omega) b11 s₁ hsb₁
    hlt hltb (z := z) (t₁ := t₁) (t₂ := t₂) (by rwa [d8, ← hσ])
    (by rwa [d8, ← hσ])
  have f₂ : ∀ r, 10500 ≤ r → r ≠ 170141 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    F₂.1 r (by simp only [SweepPrim.Bkb, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      beq_eq_false_iff_ne]; exact ⟨by omega, h2⟩)
  have w₂ := e₂.wb_right
  refine spec_seq ⟨c₂, k₂, e₂, ?_⟩
  have c12 : c₂.nreg 170012 = 0 := by
    rw [f₂ _ (by norm_num) (by norm_num), f₁ _ (by decide)]; exact hR.r12
  by_cases g2 : c₂.nreg 170012 < c₂.nreg 170141
  · have ht : t₂ < t₁ := i41.1 (by rw [c12] at g2; omega)
    refine spec_ifLtN_true g2 ?_
    have s₂ : SymPtIn c₂ 170130 sn := symPtIn_of_eq s₁ (fun j h1 h2 => f₂ j (by omega) (by omega))
    obtain ⟨c₃, k₃, e₃, hk₃, a70, s₃⟩ := takeI_exec (P := P) c₂ w₂ (by omega) s₂
    refine ⟨c₃, k₃, e₃, by omega, by omega, fun _ => ⟨sn, t₂, s₃, hbsym, ?_, hev⟩,
      fun h => absurd a70 h⟩
    rw [Set.union_comm]
    exact firstHit_min hA hfh ht.le
  · have ht : ¬ t₂ < t₁ := fun h => g2 (by rw [c12, i41.2 h]; omega)
    refine spec_ifLtN_false g2 (spec_skip w₂ ?_)
    have k70 : ∀ r, 170070 ≤ r → r < 170074 → c₂.nreg r = c.nreg r := fun r h1 h2 => by
      have hb : Bhs r = false := by unfold Bhs; simp only [decide_eq_false_iff_not]; omega
      rw [f₂ r (by omega) (by omega), f₁ r hb]
    refine ⟨by omega, ?_⟩
    have hB' : BestI P c (Sp ∪ A) z σ := ⟨hb1, fun _ => ⟨sb, t₁, hsb, hbsb,
      firstHit_min hfh hA (not_lt.1 ht), hevb⟩,
      fun h => absurd hb1' h⟩
    exact hB'.keep k70

end exec

end

end IOrc

end Chazelle.Core
