module

public import RequestProject.LocalDirichletFlattenedEquation
public import RequestProject.LpBoundedMultiplier
public import RequestProject.SmoothCompactExtension
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PolyaNeumann

open Set Metric Filter Complex MeasureTheory
open scoped Topology ContDiff

/-! ### Directional derivative algebra & iterated coordinate derivatives -/

theorem isCompact_smoothDirichletClosedHalfBox (A b : ℝ) :
    IsCompact (smoothDirichletClosedHalfBox A b) :=
  Metric.isCompact_of_isClosed_isBounded
    ((isClosed_le Complex.continuous_re.abs continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const)))
    ((isBounded_closedBall (x := (0 : ℂ)) (r := A + b)).subset fun z hz => by
      rw [mem_closedBall, dist_zero_right]
      exact (Complex.norm_le_abs_re_add_abs_im z).trans
        (add_le_add hz.1 (by rw [abs_of_nonneg hz.2.1]; exact hz.2.2)))

theorem dirichlet_normal_dirD_add {a b : ℂ → ℂ} {z : ℂ}
    (ha : DifferentiableAt ℝ a z) (hb : DifferentiableAt ℝ b z) (v : ℂ) :
    dirD (fun w => a w + b w) v z = dirD a v z + dirD b v z := by
  change fderiv ℝ (fun w => a w + b w) z v = _; rw [fderiv_fun_add ha hb]; rfl

private theorem dirichlet_normal_dirD_sub {a b : ℂ → ℂ} {z : ℂ}
    (ha : DifferentiableAt ℝ a z) (hb : DifferentiableAt ℝ b z) (v : ℂ) :
    dirD (fun w => a w - b w) v z = dirD a v z - dirD b v z := by
  change fderiv ℝ (fun w => a w - b w) z v = _; rw [fderiv_fun_sub ha hb]; rfl

private theorem dirichlet_normal_dirD_mul {a b : ℂ → ℂ} {z : ℂ}
    (ha : DifferentiableAt ℝ a z) (hb : DifferentiableAt ℝ b z) (v : ℂ) :
    dirD (fun w => a w * b w) v z = dirD a v z * b z + a z * dirD b v z := by
  change fderiv ℝ (fun w => a w * b w) z v = _
  rw [fderiv_fun_mul ha hb]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  change a z * dirD b v z + b z * dirD a v z = _; ring

private theorem dirichlet_dirD_contDiff {c : ℂ → ℂ}
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (w : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (dirD c w) :=
  (hc.fderiv_right (m := (⊤ : ℕ∞)) le_rfl).clm_apply contDiff_const

def dirichletCoordinateDerivative (w : ℂ) : ℕ → (ℂ → ℂ) → (ℂ → ℂ)
  | 0, u => u
  | k + 1, u => dirD (dirichletCoordinateDerivative w k u) w

@[simp] private theorem dirichletCoordinateDerivative_succ (w : ℂ) (k : ℕ) (u : ℂ → ℂ) :
    dirichletCoordinateDerivative w (k + 1) u = dirD (dirichletCoordinateDerivative w k u) w := rfl

private theorem dirichletCoordinateDerivative_iterate (w : ℂ) (k l : ℕ) (u : ℂ → ℂ) :
    dirichletCoordinateDerivative w k (dirichletCoordinateDerivative w l u) =
      dirichletCoordinateDerivative w (k + l) u := by
  induction k with
  | zero => simp [dirichletCoordinateDerivative]
  | succ k ih => simp [dirichletCoordinateDerivative_succ, ih, Nat.succ_add]

private theorem dirichletCoordinateDerivative_succ_right (w : ℂ) (k : ℕ) (u : ℂ → ℂ) :
    dirichletCoordinateDerivative w k (dirD u w) = dirichletCoordinateDerivative w (k + 1) u :=
  dirichletCoordinateDerivative_iterate w k 1 u

private theorem dirichletCoordinateDerivative_contDiff {u : ℂ → ℂ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (w : ℂ) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (dirichletCoordinateDerivative w k u) := by
  induction k with
  | zero => exact hu
  | succ _ ih => exact dirichlet_dirD_contDiff ih w

private theorem dirichletCoordinateDerivative_contDiffOn {U : Set ℂ} (hU : IsOpen U)
    {u : ℂ → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (w : ℂ) (k : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (dirichletCoordinateDerivative w k u) U := by
  induction k with
  | zero => exact hu
  | succ _ ih => exact dirichlet_contDiffOn_dirD hU ih w

private theorem dirichletCoordinateDerivative_eventuallyEq {u v : ℂ → ℂ} {z : ℂ}
    (heq : u =ᶠ[𝓝 z] v) (w : ℂ) (k : ℕ) :
    dirichletCoordinateDerivative w k u =ᶠ[𝓝 z] dirichletCoordinateDerivative w k v := by
  induction k with
  | zero => exact heq
  | succ _ ih => exact (ih.fderiv (𝕜 := ℝ)).fun_comp (fun A : ℂ →L[ℝ] ℂ => A w)

private theorem dirichletCoordinateDerivative_eqOn {U : Set ℂ} (hU : IsOpen U)
    {u v : ℂ → ℂ} (heq : EqOn u v U) (w : ℂ) (k : ℕ) :
    EqOn (dirichletCoordinateDerivative w k u) (dirichletCoordinateDerivative w k v) U := fun z hz =>
  (dirichletCoordinateDerivative_eventuallyEq
    (Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hU.mem_nhds hz, heq⟩) w k).self_of_nhds

theorem dirichlet_bootstrap_dirD_eqOn {U : Set ℂ} (hU : IsOpen U)
    {u v : ℂ → ℂ} (heq : EqOn u v U) (w : ℂ) : EqOn (dirD u w) (dirD v w) U :=
  dirichletCoordinateDerivative_eqOn hU heq w 1

private theorem dirichletBootstrap_differentiableAt {U : Set ℂ} (hU : IsOpen U)
    {v : ℂ → ℂ} (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U) {z : ℂ} (hz : z ∈ U) :
    DifferentiableAt ℝ v z :=
  (hv.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)

private theorem dirichletCoordinateDerivative_add_eqOn {U : Set ℂ} (hU : IsOpen U)
    {u v : ℂ → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U) (w : ℂ) (k : ℕ) :
    EqOn (dirichletCoordinateDerivative w k (fun z => u z + v z))
      (fun z => dirichletCoordinateDerivative w k u z +
        dirichletCoordinateDerivative w k v z) U := by
  induction k with
  | zero => intro _ _; rfl
  | succ k ih =>
    intro z hz
    rw [dirichletCoordinateDerivative_succ, dirichlet_bootstrap_dirD_eqOn hU ih w hz]
    exact dirichlet_normal_dirD_add
      (dirichletBootstrap_differentiableAt hU (dirichletCoordinateDerivative_contDiffOn hU hu w k) hz)
      (dirichletBootstrap_differentiableAt hU (dirichletCoordinateDerivative_contDiffOn hU hv w k) hz) w

private theorem dirichletCoordinateDerivative_const_mul_eqOn {U : Set ℂ} (hU : IsOpen U)
    {u : ℂ → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (c w : ℂ) (k : ℕ) :
    EqOn (dirichletCoordinateDerivative w k (fun z => c * u z))
      (fun z => c * dirichletCoordinateDerivative w k u z) U := by
  induction k with
  | zero => intro _ _; rfl
  | succ k ih =>
    intro z hz
    rw [dirichletCoordinateDerivative_succ, dirichlet_bootstrap_dirD_eqOn hU ih w hz]
    change fderiv ℝ (fun x => c * dirichletCoordinateDerivative w k u x) z w = _
    rw [fderiv_const_mul (dirichletBootstrap_differentiableAt hU
      (dirichletCoordinateDerivative_contDiffOn hU hu w k) hz) c]; rfl

private theorem dirichletCoordinateDerivative_sub_eqOn {U : Set ℂ} (hU : IsOpen U)
    {u v : ℂ → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U) (w : ℂ) (k : ℕ) :
    EqOn (dirichletCoordinateDerivative w k (fun z => u z - v z))
      (fun z => dirichletCoordinateDerivative w k u z -
        dirichletCoordinateDerivative w k v z) U := fun z hz => by
  rw [show (fun z => u z - v z) = fun z => u z + (-1 : ℂ) * v z from funext fun _ => by ring,
    dirichletCoordinateDerivative_add_eqOn hU hu (contDiffOn_const.mul hv) w k hz]
  dsimp only
  rw [dirichletCoordinateDerivative_const_mul_eqOn hU hv (-1) w k hz]
  ring

private theorem dirichletCoordinateDerivative_mul_eqOn_of_dirD_zero {U : Set ℂ}
    (hU : IsOpen U) {a u : ℂ → ℂ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a U)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (w : ℂ)
    (hzero : ∀ z ∈ U, dirD a w z = 0) (k : ℕ) :
    EqOn (dirichletCoordinateDerivative w k (fun z => a z * u z))
      (fun z => a z * dirichletCoordinateDerivative w k u z) U := by
  induction k with
  | zero => intro _ _; rfl
  | succ k ih =>
    intro z hz
    rw [dirichletCoordinateDerivative_succ, dirichlet_bootstrap_dirD_eqOn hU ih w hz,
      dirichlet_normal_dirD_mul (dirichletBootstrap_differentiableAt hU ha hz)
        (dirichletBootstrap_differentiableAt hU
          (dirichletCoordinateDerivative_contDiffOn hU hu w k) hz) w, hzero z hz]
    simp [dirichletCoordinateDerivative_succ]

private theorem dirichletCoordinateDerivative_dirD_comm_eqOn {U : Set ℂ} (hU : IsOpen U)
    {u : ℂ → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (v w : ℂ) (k : ℕ) :
    EqOn (dirichletCoordinateDerivative v k (dirD u w))
      (dirD (dirichletCoordinateDerivative v k u) w) U := by
  induction k with
  | zero => intro _ _; rfl
  | succ k ih =>
    intro z hz
    rw [dirichletCoordinateDerivative_succ, dirichlet_bootstrap_dirD_eqOn hU ih v hz]
    exact dirichlet_dirD_comm hU (dirichletCoordinateDerivative_contDiffOn hU hu v k) hz w v

private theorem dirichletCoordinateDerivative_comm_eqOn {U : Set ℂ} (hU : IsOpen U)
    {u : ℂ → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (v w : ℂ) (p q : ℕ) :
    EqOn (dirichletCoordinateDerivative v p (dirichletCoordinateDerivative w q u))
      (dirichletCoordinateDerivative w q (dirichletCoordinateDerivative v p u)) U := by
  induction q with
  | zero => intro _ _; rfl
  | succ q ih =>
    intro z hz
    rw [dirichletCoordinateDerivative_succ,
      dirichletCoordinateDerivative_dirD_comm_eqOn hU
        (dirichletCoordinateDerivative_contDiffOn hU hu w q) v w p hz,
      dirichlet_bootstrap_dirD_eqOn hU ih w hz]; rfl

def dirichletMixedDerivative (p q : ℕ) (u : ℂ → ℂ) : ℂ → ℂ :=
  dirichletCoordinateDerivative 1 p (dirichletCoordinateDerivative Complex.I q u)

theorem dirichletMixedDerivative_contDiffOn {U : Set ℂ} (hU : IsOpen U)
    {u : ℂ → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (p q : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (dirichletMixedDerivative p q u) U :=
  dirichletCoordinateDerivative_contDiffOn hU
    (dirichletCoordinateDerivative_contDiffOn hU hu Complex.I q) 1 p

theorem dirD_dirichletMixedDerivative_one (p q : ℕ) (u : ℂ → ℂ) :
    dirD (dirichletMixedDerivative p q u) 1 = dirichletMixedDerivative (p + 1) q u := rfl

theorem dirD_dirichletMixedDerivative_I_eqOn {U : Set ℂ} (hU : IsOpen U)
    {u : ℂ → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (p q : ℕ) :
    EqOn (dirD (dirichletMixedDerivative p q u) Complex.I)
      (dirichletMixedDerivative p (q + 1) u) U := fun z hz =>
  (dirichletCoordinateDerivative_dirD_comm_eqOn hU
    (dirichletCoordinateDerivative_contDiffOn hU hu Complex.I q) 1 Complex.I p hz).symm

/-! ### Iterated tangential finite differences & commutator bounds -/

private def dirichletTangentialTranslate (h : ℝ) (u : ℂ → ℂ) (z : ℂ) : ℂ := u (z + (h : ℂ))

private def dirichletTangentialDifferenceIter (h : ℝ) : ℕ → (ℂ → ℂ) → (ℂ → ℂ)
  | 0, u => u
  | k + 1, u => dirichletTangentialDifference h (dirichletTangentialDifferenceIter h k u)

@[simp] private theorem dirichletTangentialDifferenceIter_succ (h : ℝ) (k : ℕ) (u : ℂ → ℂ) :
    dirichletTangentialDifferenceIter h (k + 1) u =
      dirichletTangentialDifference h (dirichletTangentialDifferenceIter h k u) := rfl

private lemma margin_succ {A a h : ℝ} {k : ℕ} (hm : a + ((k + 1 : ℕ) : ℝ) * |h| ≤ A) :
    (a + |h|) + (k : ℝ) * |h| ≤ A := by
  rw [Nat.cast_add, Nat.cast_one] at hm; nlinarith

private theorem dirichletTangentialDifferenceIter_linear (h : ℝ) (k : ℕ) (a b : ℂ) (u v : ℂ → ℂ) :
    dirichletTangentialDifferenceIter h k (fun z => a * u z + b * v z) =
      fun z => a * dirichletTangentialDifferenceIter h k u z +
        b * dirichletTangentialDifferenceIter h k v z := by
  induction k with
  | zero => rfl
  | succ _ ih =>
    funext z
    simp only [dirichletTangentialDifferenceIter_succ, ih, dirichletTangentialDifference, div_eq_mul_inv]
    ring

private theorem dirichletTangentialDifferenceIter_add (h : ℝ) (k : ℕ) (u v : ℂ → ℂ) :
    dirichletTangentialDifferenceIter h k (fun z => u z + v z) =
      fun z => dirichletTangentialDifferenceIter h k u z + dirichletTangentialDifferenceIter h k v z := by
  simpa only [one_mul] using dirichletTangentialDifferenceIter_linear h k 1 1 u v

private theorem dirichletTangentialDifferenceIter_sub (h : ℝ) (k : ℕ) (u v : ℂ → ℂ) :
    dirichletTangentialDifferenceIter h k (fun z => u z - v z) =
      fun z => dirichletTangentialDifferenceIter h k u z - dirichletTangentialDifferenceIter h k v z := by
  simpa only [one_mul, neg_one_mul, sub_eq_add_neg] using
    dirichletTangentialDifferenceIter_linear h k 1 (-1) u v

private theorem dirichletTangentialDifferenceIter_const_mul
    (h : ℝ) (k : ℕ) (a : ℂ) (u : ℂ → ℂ) :
    dirichletTangentialDifferenceIter h k (fun z => a * u z) =
      fun z => a * dirichletTangentialDifferenceIter h k u z := by
  simpa only [zero_mul, add_zero] using dirichletTangentialDifferenceIter_linear h k a 0 u 0

private theorem dirichletTangentialDifferenceIter_congr (h : ℝ) (m : ℕ) {d c : ℂ → ℂ} (w : ℂ)
    (he : ∀ j ≤ m, d (w + (((j : ℝ) * h : ℝ) : ℂ)) = c (w + (((j : ℝ) * h : ℝ) : ℂ))) :
    dirichletTangentialDifferenceIter h m d w = dirichletTangentialDifferenceIter h m c w := by
  induction m generalizing w with
  | zero => simpa [dirichletTangentialDifferenceIter] using he 0 le_rfl
  | succ m ih =>
    change (_ - _) / (h : ℂ) = (_ - _) / (h : ℂ)
    rw [ih (w + (h : ℂ)) fun j hj => by
          rw [show w + (h : ℂ) + (((j : ℝ) * h : ℝ) : ℂ) =
            w + ((((j + 1 : ℕ) : ℝ) * h : ℝ) : ℂ) by push_cast; ring]
          exact he (j + 1) (Nat.succ_le_succ hj),
        ih w fun j hj => he j (hj.trans (Nat.le_succ _))]

private def dirichletHigherCoefficientCommutator (h : ℝ) (k : ℕ)
    (a v : ℂ → ℂ) (z : ℂ) : ℂ :=
  dirichletTangentialDifferenceIter h k (fun w => a w * v w) z -
    dirichletTangentialTranslate ((k : ℝ) * h) a z *
      dirichletTangentialDifferenceIter h k v z

private theorem dirichletTangentialDifferenceIter_mul_eq_shift_add_commutator
    (h : ℝ) (k : ℕ) (a v : ℂ → ℂ) (z : ℂ) :
    dirichletTangentialDifferenceIter h k (fun w => a w * v w) z =
      dirichletTangentialTranslate ((k : ℝ) * h) a z *
        dirichletTangentialDifferenceIter h k v z +
      dirichletHigherCoefficientCommutator h k a v z := by
  unfold dirichletHigherCoefficientCommutator; ring

private theorem dirichletTangentialDifferenceIter_contDiff {u : ℂ → ℂ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (h : ℝ) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (dirichletTangentialDifferenceIter h k u) := by
  induction k with
  | zero => exact hu
  | succ _ ih => exact ((ih.comp (contDiff_id.add contDiff_const)).sub ih).div_const (h : ℂ)

private theorem dirichletTangentialDifferenceIter_continuousOn
    {A a b h : ℝ} (k : ℕ) (hmargin : a + (k : ℝ) * |h| ≤ A)
    {u : ℂ → ℂ} (hu : ContinuousOn u (smoothDirichletClosedHalfBox A b)) :
    ContinuousOn (dirichletTangentialDifferenceIter h k u) (smoothDirichletClosedHalfBox a b) := by
  induction k generalizing a with
  | zero => exact hu.mono fun _ hz => ⟨hz.1.trans (by simpa using hmargin), hz.2⟩
  | succ _ ih => exact dirichletTangentialDifference_continuousOn le_rfl (ih (margin_succ hmargin))

private theorem dirichletTangentialDifferenceIter_contDiffOn
    {A a b h : ℝ} (k : ℕ) (hmargin : a + (k : ℝ) * |h| ≤ A)
    {u : ℂ → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (dirichletTangentialDifferenceIter h k u) (smoothDirichletHalfBox a b) := by
  induction k generalizing a with
  | zero => exact hu.mono fun _ hz => ⟨hz.1.trans_le (by simpa using hmargin), hz.2⟩
  | succ _ ih => exact dirichletTangentialDifference_contDiffOn le_rfl (ih (margin_succ hmargin))

private theorem dirichletTangentialDifferenceIter_zero_bottom
    {A a h : ℝ} (k : ℕ) (hmargin : a + (k : ℝ) * |h| ≤ A)
    {u : ℂ → ℂ} (hu : ∀ x : ℝ, |x| < A → u (x : ℂ) = 0)
    {x : ℝ} (hx : |x| < a) :
    dirichletTangentialDifferenceIter h k u (x : ℂ) = 0 := by
  induction k generalizing a x with
  | zero => exact hu x (hx.trans_le (by simpa using hmargin))
  | succ _ ih =>
    exact dirichletTangentialDifference_zero_bottom le_rfl (fun _ hy => ih (margin_succ hmargin) hy) hx

private theorem dirichletTangentialDifferenceIter_dirD
    {A a b h : ℝ} (k : ℕ) (hmargin : a + (k : ℝ) * |h| ≤ A)
    {u : ℂ → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b))
    {z : ℂ} (hz : z ∈ smoothDirichletHalfBox a b) (w : ℂ) :
    dirD (dirichletTangentialDifferenceIter h k u) w z =
      dirichletTangentialDifferenceIter h k (dirD u w) z := by
  induction k generalizing a z with
  | zero => rfl
  | succ k ih =>
    have hm := margin_succ hmargin
    have hs := dirichletTangentialDifferenceIter_contDiffOn k hm hu
    have hz' : z ∈ smoothDirichletHalfBox (a + |h|) b :=
      ⟨hz.1.trans_le (le_add_of_nonneg_right (abs_nonneg h)), hz.2⟩
    have hzh : z + (h : ℂ) ∈ smoothDirichletHalfBox (a + |h|) b :=
      ⟨by simpa only [Complex.add_re, Complex.ofReal_re] using
          (abs_add_le z.re h).trans_lt (add_lt_add_of_lt_of_le hz.1 le_rfl),
       by simpa using hz.2⟩
    rw [dirichletTangentialDifferenceIter_succ,
      dirichletTangentialDifference_dirD
        (dirichletBootstrap_differentiableAt (isOpen_smoothDirichletHalfBox _ _) hs hz')
        (dirichletBootstrap_differentiableAt (isOpen_smoothDirichletHalfBox _ _) hs hzh) w]
    change (dirD (dirichletTangentialDifferenceIter h k u) w (z + (h : ℂ)) -
      dirD (dirichletTangentialDifferenceIter h k u) w z) / (h : ℂ) = _
    rw [ih hm hzh, ih hm hz']; rfl

private theorem dirichletTangentialDifferenceIter_memLp
    {A a b h : ℝ} (k : ℕ) (hmargin : a + (k : ℝ) * |h| ≤ A)
    {u : ℂ → ℂ} (hu : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b))) :
    MemLp (dirichletTangentialDifferenceIter h k u) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  induction k generalizing a with
  | zero =>
    have ha : a ≤ A := by simpa using hmargin
    exact hu.mono_measure (Measure.restrict_mono_set volume
      (show smoothDirichletHalfBox a b ⊆ smoothDirichletHalfBox A b from
        fun _ hz => ⟨hz.1.trans_le ha, hz.2⟩))
  | succ _ ih => exact dirichletTangentialDifference_memLp le_rfl (ih (margin_succ hmargin))

private theorem dirichletTangentialDifferenceIter_gradient_memLp
    {A a b h : ℝ} (k : ℕ) (hmargin : a + (k : ℝ) * |h| ≤ A)
    {u : ℂ → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b))
    {w : ℂ} (hg : MemLp (dirD u w) 2 (volume.restrict (smoothDirichletHalfBox A b))) :
    MemLp (dirD (dirichletTangentialDifferenceIter h k u) w) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  refine (dirichletTangentialDifferenceIter_memLp k hmargin hg).ae_eq ?_
  filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet] with z hz
  exact (dirichletTangentialDifferenceIter_dirD k hmargin hu hz w).symm

private theorem norm_dirichletHigherCoefficientCommutator_le
    (h : ℝ) (k : ℕ) (a v : ℂ → ℂ) (z : ℂ) :
    ‖dirichletHigherCoefficientCommutator h k a v z‖ ≤
      ∑ j ∈ Finset.range k, (k.choose j : ℝ) *
        (‖dirichletTangentialDifferenceIter h (k - j) a (z + (((j : ℝ) * h : ℝ) : ℂ))‖ *
          ‖dirichletTangentialDifferenceIter h j v z‖) := by
  have hleib (m : ℕ) (w : ℂ) :
      dirichletTangentialDifferenceIter h m (fun x => a x * v x) w =
        ∑ j ∈ Finset.range (m + 1), (m.choose j : ℂ) *
          (dirichletTangentialTranslate ((j : ℝ) * h)
              (dirichletTangentialDifferenceIter h (m - j) a) w *
            dirichletTangentialDifferenceIter h j v w) := by
    induction m generalizing w with
    | zero => simp [dirichletTangentialDifferenceIter, dirichletTangentialTranslate]
    | succ m ih =>
      let K : ℕ → ℕ → ℂ → ℂ := fun j l x =>
        dirichletTangentialTranslate ((j : ℝ) * h)
          (dirichletTangentialDifferenceIter h l a) x * dirichletTangentialDifferenceIter h j v x
      have hK (j : ℕ) (hj : j ∈ Finset.range (m + 1)) :
          dirichletTangentialDifference h (K j (m - j)) w =
            K j (m + 1 - j) w + K (j + 1) (m - j) w := by
        have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        have hd : dirichletTangentialDifference h (dirichletTangentialDifferenceIter h (m - j) a) =
            dirichletTangentialDifferenceIter h (m + 1 - j) a := by
          rw [← dirichletTangentialDifferenceIter_succ, show m - j + 1 = m + 1 - j by omega]
        have hmul (p q : ℂ → ℂ) : dirichletTangentialDifference h (fun x => p x * q x) w =
            dirichletTangentialTranslate h p w * dirichletTangentialDifference h q w +
              dirichletTangentialDifference h p w * q w := by
          simp only [dirichletTangentialDifference, dirichletTangentialTranslate, div_eq_mul_inv]; ring
        have htr (t : ℝ) (p : ℂ → ℂ) :
            dirichletTangentialDifference h (dirichletTangentialTranslate t p) =
              dirichletTangentialTranslate t (dirichletTangentialDifference h p) := by
          funext x; simp only [dirichletTangentialDifference, dirichletTangentialTranslate]
          rw [show x + (h : ℂ) + (t : ℂ) = x + (t : ℂ) + (h : ℂ) by ring]
        have htr_succ : dirichletTangentialTranslate h (dirichletTangentialTranslate ((j : ℝ) * h)
            (dirichletTangentialDifferenceIter h (m - j) a)) =
            dirichletTangentialTranslate (((j + 1 : ℕ) : ℝ) * h)
              (dirichletTangentialDifferenceIter h (m - j) a) := by
          funext x; unfold dirichletTangentialTranslate; congr 1; push_cast; ring
        change dirichletTangentialDifference h
          (fun x => dirichletTangentialTranslate ((j : ℝ) * h)
            (dirichletTangentialDifferenceIter h (m - j) a) x *
              dirichletTangentialDifferenceIter h j v x) w = _
        rw [hmul, htr, htr_succ, hd]
        exact add_comm _ _
      have hsum_diff : dirichletTangentialDifferenceIter h (m + 1) (fun x => a x * v x) w =
          ∑ j ∈ Finset.range (m + 1), (m.choose j : ℂ) *
            dirichletTangentialDifference h (K j (m - j)) w := by
        rw [dirichletTangentialDifferenceIter_succ, funext ih]
        dsimp only [dirichletTangentialDifference]
        rw [← Finset.sum_sub_distrib, Finset.sum_div]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hsum_diff, Finset.sum_congr rfl fun j hj => congrArg ((m.choose j : ℂ) * ·) (hK j hj),
        Finset.sum_choose_succ_mul (fun j l => K j l w) m]
      simp only [mul_add, Finset.sum_add_distrib]
  have hcomm : dirichletHigherCoefficientCommutator h k a v z =
      ∑ j ∈ Finset.range k, (k.choose j : ℂ) *
        (dirichletTangentialTranslate ((j : ℝ) * h)
            (dirichletTangentialDifferenceIter h (k - j) a) z *
          dirichletTangentialDifferenceIter h j v z) := by
    unfold dirichletHigherCoefficientCommutator
    rw [hleib, Finset.sum_range_succ]
    simp only [Nat.choose_self, Nat.sub_self, dirichletTangentialDifferenceIter]; ring
  rw [hcomm]
  refine (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun j _ => ?_)
  simp only [norm_mul, Complex.norm_natCast, dirichletTangentialTranslate]

private def dirichletHigherCoefficientDifferenceFlux (f : ℝ → ℝ) (h : ℝ) (k : ℕ)
    (u : ℂ → ℂ) (i : Fin 2) (z : ℂ) : ℂ :=
  ![-dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f) (dirD u Complex.I) z,
    -dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f) (dirD u 1) z +
      dirichletHigherCoefficientCommutator h k
        (fun w => 1 + dirichletGraphSlope f w ^ 2) (dirD u Complex.I) z] i

private theorem dirichletTangentialDifferenceIter_flux_split
    {A a b h : ℝ} (k : ℕ) (hmargin : a + (k : ℝ) * |h| ≤ A)
    (f : ℝ → ℝ) {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b))
    {z : ℂ} (hz : z ∈ smoothDirichletHalfBox a b) (i : Fin 2) :
    dirichletTangentialDifferenceIter h k (dirichletFlattenedFlux f u i) z =
      dirichletShiftedFlux f ((k : ℝ) * h) (dirichletTangentialDifferenceIter h k u) i z +
        dirichletHigherCoefficientDifferenceFlux f h k u i z := by
  have hx := dirichletTangentialDifferenceIter_dirD k hmargin hu hz 1
  have hy := dirichletTangentialDifferenceIter_dirD k hmargin hu hz Complex.I
  fin_cases i
  · change dirichletTangentialDifferenceIter h k
        (fun w => dirD u 1 w - dirichletGraphSlope f w * dirD u Complex.I w) z =
      (dirD (dirichletTangentialDifferenceIter h k u) 1 z -
        dirichletGraphSlope f (z + (((k : ℝ) * h : ℝ) : ℂ)) *
          dirD (dirichletTangentialDifferenceIter h k u) Complex.I z) +
      -dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f) (dirD u Complex.I) z
    simp only [dirichletTangentialDifferenceIter_sub]
    rw [dirichletTangentialDifferenceIter_mul_eq_shift_add_commutator, hx, hy]
    simp only [dirichletTangentialTranslate]; ring
  · have hneg (w : ℂ) : -dirichletGraphSlope f w * dirD u 1 w =
        (-1 : ℂ) * (dirichletGraphSlope f w * dirD u 1 w) := by ring
    change dirichletTangentialDifferenceIter h k
        (fun w => -dirichletGraphSlope f w * dirD u 1 w +
          (1 + dirichletGraphSlope f w ^ 2) * dirD u Complex.I w) z =
      (-dirichletGraphSlope f (z + (((k : ℝ) * h : ℝ) : ℂ)) *
          dirD (dirichletTangentialDifferenceIter h k u) 1 z +
        (1 + dirichletGraphSlope f (z + (((k : ℝ) * h : ℝ) : ℂ)) ^ 2) *
          dirD (dirichletTangentialDifferenceIter h k u) Complex.I z) +
      (-dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f) (dirD u 1) z +
        dirichletHigherCoefficientCommutator h k
          (fun w => 1 + dirichletGraphSlope f w ^ 2) (dirD u Complex.I) z)
    simp only [dirichletTangentialDifferenceIter_add]
    simp_rw [hneg]
    rw [dirichletTangentialDifferenceIter_const_mul]
    change (-1 : ℂ) * dirichletTangentialDifferenceIter h k
        (fun w => dirichletGraphSlope f w * dirD u 1 w) z +
      dirichletTangentialDifferenceIter h k
        (fun w => (1 + dirichletGraphSlope f w ^ 2) * dirD u Complex.I w) z = _
    rw [dirichletTangentialDifferenceIter_mul_eq_shift_add_commutator,
      dirichletTangentialDifferenceIter_mul_eq_shift_add_commutator, hx, hy]
    simp only [dirichletTangentialTranslate]; ring

private theorem dirichletTangentialDifferenceIter_dirD_global
    {c : ℂ → ℂ} (hc : ContDiff ℝ (⊤ : ℕ∞) c) (h : ℝ) (k : ℕ) (w : ℂ) :
    dirD (dirichletTangentialDifferenceIter h k c) w =
      dirichletTangentialDifferenceIter h k (dirD c w) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext z
    have hs := dirichletTangentialDifferenceIter_contDiff hc h k
    rw [dirichletTangentialDifferenceIter_succ,
      dirichletTangentialDifference_dirD (hs.differentiable (by simp) z)
        (hs.differentiable (by simp) (z + (h : ℂ))) w, ih]; rfl

private theorem dirichletTangentialDifferenceIter_norm_le
    {A a b h M : ℝ} (k : ℕ) (hh : 0 < h) (hmargin : a + (k : ℝ) * h ≤ A)
    {c : ℂ → ℂ} (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hM : ∀ z ∈ smoothDirichletClosedHalfBox A b,
      ‖dirichletCoordinateDerivative 1 k c z‖ ≤ M)
    {z : ℂ} (hz : z ∈ smoothDirichletClosedHalfBox a b) :
    ‖dirichletTangentialDifferenceIter h k c z‖ ≤ M := by
  induction k generalizing a c z with
  | zero => exact hM z ⟨hz.1.trans (by simpa using hmargin), hz.2⟩
  | succ k ih =>
    have hm : (a + h) + (k : ℝ) * h ≤ A := by rw [Nat.cast_add, Nat.cast_one] at hmargin; nlinarith
    have hd1 {f₀ : ℂ → ℂ} (hf₀ : ContDiff ℝ (⊤ : ℕ∞) f₀)
        (hM₁ : ∀ w ∈ smoothDirichletClosedHalfBox (a + h) b, ‖dirD f₀ 1 w‖ ≤ M) :
        ‖dirichletTangentialDifference h f₀ z‖ ≤ M := by
      let v : ℝ → ℂ := fun t => f₀ (z + (t : ℂ))
      have hmap (t : ℝ) (ht : t ∈ Icc (0 : ℝ) h) :
          z + (t : ℂ) ∈ smoothDirichletClosedHalfBox (a + h) b :=
        ⟨by simpa only [Complex.add_re, Complex.ofReal_re] using
            (abs_add_le z.re t).trans (add_le_add hz.1 (by rw [abs_of_nonneg ht.1]; exact ht.2)),
         by simpa using hz.2⟩
      have hd (t : ℝ) : HasDerivAt v (dirD f₀ 1 (z + (t : ℂ))) t :=
        (hf₀.differentiable (by simp) (z + (t : ℂ))).hasFDerivAt.comp_hasDerivAt t
          (Complex.ofRealCLM.hasDerivAt.const_add z)
      have hp := (convex_Icc (0 : ℝ) h).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun t _ => (hd t).hasDerivWithinAt) (fun t ht => hM₁ _ (hmap t ht))
        ⟨le_rfl, hh.le⟩ ⟨hh.le, le_rfl⟩
      have hp' : ‖f₀ (z + (h : ℂ)) - f₀ z‖ ≤ M * h := by
        simpa only [v, Complex.ofReal_zero, add_zero, sub_zero,
          Real.norm_eq_abs, abs_of_pos hh] using hp
      rw [dirichletTangentialDifference, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
      exact (div_le_iff₀ hh).mpr hp'
    refine hd1 (dirichletTangentialDifferenceIter_contDiff hc h k) fun w hw => ?_
    rw [dirichletTangentialDifferenceIter_dirD_global hc]
    refine ih hm (dirichlet_dirD_contDiff hc 1) (fun v hv => ?_) hw
    rw [dirichletCoordinateDerivative_succ_right]; exact hM v hv

private def HasGraphCommBound (f : ℝ → ℝ) (a b h M : ℝ) (k : ℕ) : Prop :=
  ∀ (v : ℂ → ℂ) (z : ℂ), z ∈ smoothDirichletClosedHalfBox a b →
    (‖dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f) v z‖ ≤
      M * ∑ j ∈ Finset.range k, (k.choose j : ℝ) * ‖dirichletTangentialDifferenceIter h j v z‖) ∧
    (‖dirichletHigherCoefficientCommutator h k (fun w => 1 + dirichletGraphSlope f w ^ 2) v z‖ ≤
      M * ∑ j ∈ Finset.range k, (k.choose j : ℝ) * ‖dirichletTangentialDifferenceIter h j v z‖)

private theorem exists_dirichletGraphHigherCommutator_bound {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (A b : ℝ) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (a h : ℝ), 0 < h → a + (k : ℝ) * h ≤ A →
      HasGraphCommBound f a b h M k := by
  have hupto {c : ℂ → ℂ} (hc : ContDiff ℝ (⊤ : ℕ∞) c) :
      ∃ M : ℝ, 0 ≤ M ∧ ∀ l ≤ k, ∀ z ∈ smoothDirichletClosedHalfBox A b,
        ‖dirichletCoordinateDerivative 1 l c z‖ ≤ M := by
    have h1 (l : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ smoothDirichletClosedHalfBox A b,
        ‖dirichletCoordinateDerivative 1 l c z‖ ≤ B := by
      obtain ⟨B, hB⟩ := (isCompact_smoothDirichletClosedHalfBox A b).exists_bound_of_continuousOn
        (dirichletCoordinateDerivative_contDiff hc 1 l).continuous.continuousOn
      exact ⟨max 0 B, le_max_left _ _, fun z hz => (hB z hz).trans (le_max_right _ _)⟩
    choose B hB0 hB using h1
    refine ⟨∑ l ∈ Finset.range (k + 1), B l, Finset.sum_nonneg fun l _ => hB0 l,
      fun l hl z hz => (hB l z hz).trans
        (Finset.single_le_sum (fun j _ => hB0 j) (Finset.mem_range.mpr (by omega)))⟩
  have hd := dirichletGraphSlope_contDiff hf
  obtain ⟨M₀, hM₀, h₀⟩ := hupto hd
  obtain ⟨M₁, _, h₁⟩ := hupto (contDiff_const.add (hd.pow 2))
  have hcomm_bd {c : ℂ → ℂ} (hc : ContDiff ℝ (⊤ : ℕ∞) c) {M : ℝ}
      (hM : ∀ l ≤ k, ∀ w ∈ smoothDirichletClosedHalfBox A b,
        ‖dirichletCoordinateDerivative 1 l c w‖ ≤ M)
      {a h : ℝ} (hh : 0 < h) (hmargin : a + (k : ℝ) * h ≤ A) (v : ℂ → ℂ)
      {z : ℂ} (hz : z ∈ smoothDirichletClosedHalfBox a b) :
      ‖dirichletHigherCoefficientCommutator h k c v z‖ ≤
        M * ∑ j ∈ Finset.range k, (k.choose j : ℝ) * ‖dirichletTangentialDifferenceIter h j v z‖ := by
    refine (norm_dirichletHigherCoefficientCommutator_le h k c v z).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hjk : j ≤ k := (Finset.mem_range.mp hj).le
    have hm : (a + (j : ℝ) * h) + ((k - j : ℕ) : ℝ) * h ≤ A := by rw [Nat.cast_sub hjk]; nlinarith
    have hjh : 0 ≤ (j : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh.le
    have hshift : z + (((j : ℝ) * h : ℝ) : ℂ) ∈ smoothDirichletClosedHalfBox (a + (j : ℝ) * h) b :=
      ⟨by simpa only [Complex.add_re, Complex.ofReal_re] using
          (abs_add_le z.re ((j : ℝ) * h)).trans (add_le_add hz.1 (le_of_eq (abs_of_nonneg hjh))),
       by simpa using hz.2⟩
    have hcoef := dirichletTangentialDifferenceIter_norm_le (k - j) hh hm hc
      (hM (k - j) (Nat.sub_le _ _)) hshift
    calc _ ≤ (k.choose j : ℝ) * (M * ‖dirichletTangentialDifferenceIter h j v z‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)) (Nat.cast_nonneg _)
      _ = _ := by ring
  refine ⟨max M₀ M₁, hM₀.trans (le_max_left _ _), fun a h hh hmargin v z hz =>
    ⟨hcomm_bd hd (fun l hl w hw => (h₀ l hl w hw).trans (le_max_left _ _)) hh hmargin v hz,
     hcomm_bd (contDiff_const.add (hd.pow 2)) (fun l hl w hw => (h₁ l hl w hw).trans (le_max_right _ _))
       hh hmargin v hz⟩⟩

private theorem dirichletTangentialDifferenceIter_tendsto_of_contDiffOn
    {U : Set ℂ} (hU : IsOpen U) {c : ℂ → ℂ}
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) c U) (k : ℕ) {z : ℂ} (hz : z ∈ U) :
    Tendsto (fun h : ℝ => dirichletTangentialDifferenceIter h k c z)
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (dirichletCoordinateDerivative 1 k c z)) := by
  have hcenter {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (m : ℕ)
      {h M : ℝ} (hh : 0 < h) (w C : ℂ)
      (hM : ∀ t ∈ Icc (0 : ℝ) ((m : ℝ) * h),
        ‖dirichletCoordinateDerivative 1 m g (w + (t : ℂ)) - C‖ ≤ M) :
      ‖dirichletTangentialDifferenceIter h m g w - C‖ ≤ M := by
    induction m generalizing g w with
    | zero => simpa [dirichletCoordinateDerivative, dirichletTangentialDifferenceIter] using hM 0 ⟨le_rfl, by simp⟩
    | succ m ih =>
      let v : ℝ → ℂ := fun t => dirichletTangentialDifferenceIter h m g (w + (t : ℂ)) - (t : ℂ) * C
      let dv : ℝ → ℂ := fun t => dirichletTangentialDifferenceIter h m (dirD g 1) (w + (t : ℂ)) - C
      have hd (t : ℝ) : HasDerivAt v (dv t) t := by
        have hs := dirichletTangentialDifferenceIter_contDiff hg h m
        have hgr := ((hs.differentiable (by simp) (w + (t : ℂ))).hasFDerivAt.comp_hasDerivAt
          t (Complex.ofRealCLM.hasDerivAt.const_add w)).sub (Complex.ofRealCLM.hasDerivAt.mul_const C)
        simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] at hgr
        have heq := congrFun (dirichletTangentialDifferenceIter_dirD_global hg h m 1) (w + (t : ℂ))
        change HasDerivAt v (fderiv ℝ (dirichletTangentialDifferenceIter h m g) (w + (t : ℂ)) 1 - C) t at hgr
        have hgr' : fderiv ℝ (dirichletTangentialDifferenceIter h m g) (w + (t : ℂ)) 1 =
            dirichletTangentialDifferenceIter h m (dirD g 1) (w + (t : ℂ)) := heq
        rwa [hgr'] at hgr
      have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) h) : ‖dv t‖ ≤ M := by
        refine ih (dirichlet_dirD_contDiff hg 1) (w + (t : ℂ)) fun s hs => ?_
        have hsum : t + s ∈ Icc (0 : ℝ) (((m + 1 : ℕ) : ℝ) * h) := by
          rw [Nat.cast_add, Nat.cast_one]; exact ⟨add_nonneg ht.1 hs.1, by nlinarith [ht.2, hs.2]⟩
        rw [dirichletCoordinateDerivative_succ_right,
          show w + (t : ℂ) + (s : ℂ) = w + ((t + s : ℝ) : ℂ) by push_cast; ring]
        exact hM (t + s) hsum
      have hp := (convex_Icc (0 : ℝ) h).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun t _ => (hd t).hasDerivWithinAt) hbound ⟨le_rfl, hh.le⟩ ⟨hh.le, le_rfl⟩
      have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
      have heq : (v h - v 0) / (h : ℂ) = dirichletTangentialDifferenceIter h (m + 1) g w - C := by
        simp only [v, Complex.ofReal_zero, zero_mul, sub_zero, add_zero,
          dirichletTangentialDifferenceIter_succ, dirichletTangentialDifference]
        field_simp [hhC]; ring
      rw [← heq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
      exact (div_le_iff₀ hh).mpr (by simpa only [sub_zero, Real.norm_eq_abs, abs_of_pos hh] using hp)
  obtain ⟨d, hd, hdc⟩ := exists_smooth_compact_extension
    (isCompact_singleton (x := z)) hU (singleton_subset_iff.mpr hz) hc
  have heq : d =ᶠ[𝓝 z] c := hdc z (mem_singleton z)
  have hall : ∀ᶠ h : ℝ in 𝓝 (0 : ℝ), ∀ j ∈ Finset.range (k + 1),
      d (z + (((j : ℝ) * h : ℝ) : ℂ)) = c (z + (((j : ℝ) * h : ℝ) : ℂ)) := by
    refine (Filter.eventually_all_finset _).mpr fun j _ => ?_
    have hst : Continuous (fun h : ℝ => z + (((j : ℝ) * h : ℝ) : ℂ)) :=
      (continuous_const : Continuous fun _ : ℝ => z).add
        (Complex.continuous_ofReal.comp
          ((continuous_const : Continuous fun _ : ℝ => (j : ℝ)).mul continuous_id))
    have ht : Tendsto (fun h : ℝ => z + (((j : ℝ) * h : ℝ) : ℂ)) (𝓝 (0 : ℝ)) (𝓝 z) := by
      simpa only [mul_zero, Complex.ofReal_zero, add_zero] using hst.tendsto (0 : ℝ)
    exact ht.eventually heq
  have hlim_d : Tendsto (fun h : ℝ => dirichletTangentialDifferenceIter h k d z)
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (dirichletCoordinateDerivative 1 k d z)) := by
    refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp
      ((dirichletCoordinateDerivative_contDiff hd.1 1 k).continuous.continuousAt (x := z))
      (ε / 2) (by positivity)
    have hk : 0 < (k : ℝ) + 1 := by positivity
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (div_pos hδ hk)).filter_mono nhdsWithin_le_nhds] with h hh hs
    have hhpos : 0 < h := hh
    have hkh : ((k : ℝ) + 1) * h < δ := by simpa only [mul_comm] using (lt_div_iff₀ hk).mp hs
    rw [dist_eq_norm]
    refine (hcenter (M := ε / 2) hd.1 k hhpos z _ fun t ht => ?_).trans_lt (by linarith)
    have hd_lt : dist (z + (t : ℂ)) z < δ := by
      simpa only [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ht.1] using (by nlinarith [ht.2] : t < δ)
    exact (by simpa only [dist_eq_norm] using hclose hd_lt : _ < ε / 2).le
  rw [← (dirichletCoordinateDerivative_eventuallyEq heq 1 k).self_of_nhds]
  exact hlim_d.congr' ((hall.mono fun h hh =>
    dirichletTangentialDifferenceIter_congr h k z fun j hj =>
      hh j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))).filter_mono nhdsWithin_le_nhds)

/-! ### Higher tangential difference energy bootstrap -/

private def dirichletGradientSq (v : ℂ → ℂ) (z : ℂ) : ℝ :=
  ‖dirD v 1 z‖ ^ 2 + ‖dirD v Complex.I z‖ ^ 2

private theorem dirichletGradientSq_integrable {μ : Measure ℂ} {v : ℂ → ℂ}
    (hg : ∀ i : Fin 2, MemLp (dirD v (coordDir i)) 2 μ) :
    Integrable (dirichletGradientSq v) μ := by
  have hx : MemLp (dirD v 1) 2 μ := by simpa only [coordDir, Matrix.cons_val_zero] using hg 0
  have hy : MemLp (dirD v Complex.I) 2 μ := by
    simpa only [coordDir, Matrix.cons_val_one, Matrix.cons_val_zero] using hg 1
  exact (hx.integrable_norm_pow (by norm_num)).add (hy.integrable_norm_pow (by norm_num))

private theorem dirichletHigherCoefficientDifferenceFlux_memLp
    {A a b h M : ℝ} (k : ℕ) (hmargin : a + (k : ℝ) * |h| ≤ A)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {u : ℂ → ℂ} (hM : 0 ≤ M)
    (hbound : HasGraphCommBound f a b h M k)
    (hg : ∀ i : Fin 2, MemLp (dirD u (coordDir i)) 2 (volume.restrict (smoothDirichletHalfBox A b)))
    (i : Fin 2) :
    MemLp (dirichletHigherCoefficientDifferenceFlux f h k u i) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  let V := smoothDirichletHalfBox a b
  let μ := volume.restrict V
  have hmeas_iter {v : ℂ → ℂ} (hv : Measurable v) (m : ℕ) :
      Measurable (dirichletTangentialDifferenceIter h m v) := by
    induction m with
    | zero => exact hv
    | succ _ ih => exact ((ih.comp (measurable_id.add_const (h : ℂ))).sub ih).div_const (h : ℂ)
  have hmeas_comm {a₀ v : ℂ → ℂ} (ha₀ : Measurable a₀) (hv : Measurable v) :
      Measurable (dirichletHigherCoefficientCommutator h k a₀ v) :=
    (hmeas_iter (ha₀.mul hv) k).sub
      ((ha₀.comp (measurable_id.add_const (((k : ℝ) * h : ℝ) : ℂ))).mul (hmeas_iter hv k))
  have hd_m := (dirichletGraphSlope_contDiff hf).continuous.measurable
  have hux : MemLp (dirD u 1) 2 (volume.restrict (smoothDirichletHalfBox A b)) := by
    simpa only [coordDir, Matrix.cons_val_zero] using hg 0
  have huy : MemLp (dirD u Complex.I) 2 (volume.restrict (smoothDirichletHalfBox A b)) := by
    simpa only [coordDir, Matrix.cons_val_one, Matrix.cons_val_zero] using hg 1
  let vx : ℕ → ℂ → ℝ := fun j z => ‖dirichletTangentialDifferenceIter h j (dirD u 1) z‖
  let vy : ℕ → ℂ → ℝ := fun j z => ‖dirichletTangentialDifferenceIter h j (dirD u Complex.I) z‖
  let B : ℂ → ℝ := fun z => M * ∑ j ∈ Finset.range k, (k.choose j : ℝ) * (vx j z + vy j z)
  have hBm : MemLp B 2 μ := by
    apply MemLp.const_mul _ M
    apply memLp_finset_sum
    intro j hj
    have hm : a + (j : ℝ) * |h| ≤ A :=
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (by exact_mod_cast (Finset.mem_range.mp hj).le) (abs_nonneg h))).trans hmargin
    exact ((dirichletTangentialDifferenceIter_memLp j hm hux).norm.add
      (dirichletTangentialDifferenceIter_memLp j hm huy).norm).const_mul (k.choose j : ℝ)
  have hfl_m : Measurable (dirichletHigherCoefficientDifferenceFlux f h k u i) := by
    fin_cases i
    · exact (hmeas_comm hd_m (measurable_fderiv_apply_const ℝ u Complex.I)).neg
    · exact (hmeas_comm hd_m (measurable_fderiv_apply_const ℝ u 1)).neg.add
        (hmeas_comm ((measurable_const : Measurable fun _ : ℂ => (1 : ℂ)).add (hd_m.pow_const 2))
          (measurable_fderiv_apply_const ℝ u Complex.I))
  refine hBm.mono' hfl_m.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet] with z hz
  have hz' : z ∈ smoothDirichletClosedHalfBox a b := ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩
  let Sx := ∑ j ∈ Finset.range k, (k.choose j : ℝ) * vx j z
  let Sy := ∑ j ∈ Finset.range k, (k.choose j : ℝ) * vy j z
  have hSx : 0 ≤ Sx := Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hBS : B z = M * (Sx + Sy) := by simp only [B, Sx, Sy, mul_add, Finset.sum_add_distrib]
  have hcx := (hbound (dirD u 1) z hz').1
  have hcy := (hbound (dirD u Complex.I) z hz').1
  have hsy := (hbound (dirD u Complex.I) z hz').2
  fin_cases i
  · change ‖-dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f) (dirD u Complex.I) z‖ ≤ B z
    rw [norm_neg, hBS]; nlinarith [hcy, mul_nonneg hM hSx]
  · change ‖-dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f) (dirD u 1) z +
      dirichletHigherCoefficientCommutator h k (fun w => 1 + dirichletGraphSlope f w ^ 2) (dirD u Complex.I) z‖ ≤ B z
    exact (norm_add_le _ _).trans (by rw [norm_neg, hBS]; nlinarith [hcx, hsy])

private theorem dirichletHigherCoefficientDifferenceFlux_energy_le
    {A a b h M E : ℝ} (k : ℕ) (hmargin : a + (k : ℝ) * |h| ≤ A)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {u : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b)) (hM : 0 ≤ M)
    (hbound : HasGraphCommBound f a b h M k)
    (hg : ∀ i : Fin 2, MemLp (dirD u (coordDir i)) 2 (volume.restrict (smoothDirichletHalfBox A b)))
    (henergy : ∀ j ∈ Finset.range k,
      (∫ z in smoothDirichletHalfBox a b,
        dirichletGradientSq (dirichletTangentialDifferenceIter h j u) z) ≤ E) :
    (∫ z in smoothDirichletHalfBox a b,
      ‖dirichletHigherCoefficientDifferenceFlux f h k u 0 z‖ ^ 2 +
        ‖dirichletHigherCoefficientDifferenceFlux f h k u 1 z‖ ^ 2) ≤
      (3 * M ^ 2 * ∑ j ∈ Finset.range k, (k.choose j : ℝ) ^ 2) * ((k : ℝ) * E) := by
  let V := smoothDirichletHalfBox a b
  let D := 3 * M ^ 2 * ∑ j ∈ Finset.range k, (k.choose j : ℝ) ^ 2
  have hD : 0 ≤ D := mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hCm (i : Fin 2) := dirichletHigherCoefficientDifferenceFlux_memLp k hmargin hf hM hbound hg i
  have hCi := ((hCm 0).integrable_norm_pow (by norm_num)).add ((hCm 1).integrable_norm_pow (by norm_num))
  have hgi (j : ℕ) (hj : j ∈ Finset.range k) :
      IntegrableOn (dirichletGradientSq (dirichletTangentialDifferenceIter h j u)) V := by
    have hm : a + (j : ℝ) * |h| ≤ A :=
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (by exact_mod_cast (Finset.mem_range.mp hj).le) (abs_nonneg h))).trans hmargin
    exact dirichletGradientSq_integrable
      fun i => dirichletTangentialDifferenceIter_gradient_memLp j hm hs (hg i)
  have hbnd : (∫ z in V, ‖dirichletHigherCoefficientDifferenceFlux f h k u 0 z‖ ^ 2 +
      ‖dirichletHigherCoefficientDifferenceFlux f h k u 1 z‖ ^ 2) ≤
      ∫ z in V, D * ∑ j ∈ Finset.range k,
        dirichletGradientSq (dirichletTangentialDifferenceIter h j u) z := by
    refine integral_mono_ae hCi ((integrable_finset_sum _ hgi).const_mul D) ?_
    filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet] with z hz
    let vx : ℕ → ℝ := fun j => ‖dirD (dirichletTangentialDifferenceIter h j u) 1 z‖
    let vy : ℕ → ℝ := fun j => ‖dirD (dirichletTangentialDifferenceIter h j u) Complex.I z‖
    let Sx := ∑ j ∈ Finset.range k, (k.choose j : ℝ) * vx j
    let Sy := ∑ j ∈ Finset.range k, (k.choose j : ℝ) * vy j
    let P := ∑ j ∈ Finset.range k, (k.choose j : ℝ) ^ 2
    have hSx : 0 ≤ Sx := Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
    have hSy : 0 ≤ Sy := Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
    have hdir (j : ℕ) (hj : j ∈ Finset.range k) (w : ℂ) :
        dirichletTangentialDifferenceIter h j (dirD u w) z =
          dirD (dirichletTangentialDifferenceIter h j u) w z := by
      have hm : a + (j : ℝ) * |h| ≤ A :=
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right
          (by exact_mod_cast (Finset.mem_range.mp hj).le) (abs_nonneg h))).trans hmargin
      exact (dirichletTangentialDifferenceIter_dirD j hm hs hz w).symm
    have hcl : z ∈ smoothDirichletClosedHalfBox a b := ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩
    have hcx : ‖dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f) (dirD u 1) z‖ ≤ M * Sx :=
      ((hbound (dirD u 1) z hcl).1).trans_eq
        (congrArg (M * ·) (Finset.sum_congr rfl fun j hj => by rw [hdir j hj]))
    have hcy : ‖dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f) (dirD u Complex.I) z‖ ≤ M * Sy :=
      ((hbound (dirD u Complex.I) z hcl).1).trans_eq
        (congrArg (M * ·) (Finset.sum_congr rfl fun j hj => by rw [hdir j hj]))
    have hsy : ‖dirichletHigherCoefficientCommutator h k
        (fun w => 1 + dirichletGraphSlope f w ^ 2) (dirD u Complex.I) z‖ ≤ M * Sy :=
      ((hbound (dirD u Complex.I) z hcl).2).trans_eq
        (congrArg (M * ·) (Finset.sum_congr rfl fun j hj => by rw [hdir j hj]))
    have h0 : ‖dirichletHigherCoefficientDifferenceFlux f h k u 0 z‖ ≤ M * Sy := by
      simpa only [dirichletHigherCoefficientDifferenceFlux, Matrix.cons_val_zero, norm_neg] using hcy
    have h1 : ‖dirichletHigherCoefficientDifferenceFlux f h k u 1 z‖ ≤ M * (Sx + Sy) := by
      change ‖-_ + _‖ ≤ _; exact (norm_add_le _ _).trans (by rw [norm_neg]; nlinarith [hcx, hsy])
    have hsum : Sx ^ 2 + Sy ^ 2 ≤ P *
        ∑ j ∈ Finset.range k, dirichletGradientSq (dirichletTangentialDifferenceIter h j u) z := by
      simpa only [dirichletGradientSq, Finset.sum_add_distrib, vx, vy, mul_add] using
        add_le_add (Finset.sum_mul_sq_le_sq_mul_sq (Finset.range k) (fun j => (k.choose j : ℝ)) vx)
          (Finset.sum_mul_sq_le_sq_mul_sq (Finset.range k) (fun j => (k.choose j : ℝ)) vy)
    have hc0 := pow_le_pow_left₀ (norm_nonneg _) h0 2
    have hc1 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have hmab := mul_le_mul_of_nonneg_left
      (by nlinarith [sq_nonneg (Sx - Sy), sq_nonneg Sx] : Sy ^ 2 + (Sx + Sy) ^ 2 ≤ 3 * (Sx ^ 2 + Sy ^ 2))
      (sq_nonneg M)
    refine (by nlinarith : _ ≤ 3 * M ^ 2 * (Sx ^ 2 + Sy ^ 2)).trans ?_
    simpa only [D, P, mul_assoc] using mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 3 * M ^ 2)
  rw [integral_const_mul, integral_finset_sum _ hgi] at hbnd
  exact hbnd.trans (mul_le_mul_of_nonneg_left
    (by simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
      Finset.sum_le_sum fun j hj => henergy j hj) hD)

private theorem exists_dirichlet_halfBox_higher_difference_gradient_energy
    {A b : ℝ} (hA : 0 < A) (hb : 0 < b) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {K : NNReal} (hLip : LipschitzWith K f)
    {u G : ℂ → ℂ} (hc : ContinuousOn u (smoothDirichletClosedHalfBox A b))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b))
    (hz : ∀ x : ℝ, |x| < A → u (x : ℂ) = 0)
    (hm : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b)))
    (hg : ∀ i : Fin 2, MemLp (dirD u (coordDir i)) 2 (volume.restrict (smoothDirichletHalfBox A b)))
    (hstrong : ∀ z ∈ smoothDirichletHalfBox A b, dirichletFlattenedDivergence f u z = -G z)
    (hGs : ContDiff ℝ (⊤ : ℕ∞) G) (n : ℕ) :
    ∃ ρ ε E : ℝ, 0 < ρ ∧ ρ < A / 2 ∧ ρ < b ∧ 0 < ε ∧ 0 ≤ E ∧
      ∀ h ∈ Ioo 0 ε, ∀ j ≤ n,
        (∫ z in smoothDirichletHalfBox ρ ρ,
          dirichletGradientSq (dirichletTangentialDifferenceIter h j u) z) ≤ E := by
  let U := smoothDirichletHalfBox A b
  induction n with
  | zero =>
    let ρ := min A b / 4
    have hρ : 0 < ρ := div_pos (lt_min hA hb) (by norm_num)
    have hρA : ρ < A / 2 := by dsimp [ρ]; linarith [min_le_left A b]
    have hρb : ρ < b := by dsimp [ρ]; linarith [min_le_right A b]
    let E := ∫ z in U, dirichletGradientSq u z
    have hsub : smoothDirichletHalfBox ρ ρ ⊆ U := fun z hz' =>
      ⟨hz'.1.trans (by linarith), hz'.2.1, hz'.2.2.trans hρb⟩
    refine ⟨ρ, 1, E, hρ, hρA, hρb, by norm_num,
      integral_nonneg fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _), fun _ _ j hj => ?_⟩
    obtain rfl : j = 0 := Nat.eq_zero_of_le_zero hj
    exact setIntegral_mono_set (dirichletGradientSq_integrable hg)
      (Eventually.of_forall fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _)) hsub.eventuallyLE
  | succ n ih =>
    obtain ⟨ρ, ε₀, E₀, hρ, hρA, hρb, hε₀, hE₀, hprev⟩ := ih
    let k := n + 1
    let W := smoothDirichletHalfBox ρ ρ
    let V := smoothDirichletHalfBox (ρ / 2) ρ
    let ε := min ε₀ (ρ / (4 * ((k : ℝ) + 1)))
    have hε : 0 < ε := lt_min hε₀ (div_pos hρ (by positivity))
    have hVW : V ⊆ W := fun z hz' => ⟨hz'.1.trans (by linarith), hz'.2⟩
    have hsteps (h : ℝ) (hh : h ∈ Ioo 0 ε) :
        h ∈ Ioo 0 ε₀ ∧ ρ / 2 + (k : ℝ) * |h| ≤ ρ ∧ ρ + (k : ℝ) * |h| ≤ A ∧ ρ / 2 + h < ρ := by
      have hh₀ := hh.2.trans_le (min_le_left _ _)
      have hhs := (lt_div_iff₀ (by positivity : 0 < 4 * ((k : ℝ) + 1))).mp (hh.2.trans_le (min_le_right _ _))
      have hkh₀ : 0 ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh.1.le
      rw [abs_of_pos hh.1]
      exact ⟨⟨hh.1, hh₀⟩, by nlinarith, by nlinarith, by nlinarith⟩
    have hmargin (h : ℝ) (hh : h ∈ Ioo 0 ε) : ρ / 2 + (k : ℝ) * |h| ≤ A :=
      ((hsteps h hh).2.1).trans (by linarith)
    have hposMargin (h : ℝ) (hh : h ∈ Ioo 0 ε) : ρ / 2 + (k : ℝ) * h ≤ ρ := by
      have hm' := (hsteps h hh).2.1; rwa [abs_of_pos hh.1] at hm'
    have hW_sub_b : W ⊆ smoothDirichletHalfBox ρ b :=
      fun _ hz' => ⟨hz'.1, hz'.2.1, hz'.2.2.trans hρb⟩
    have hV_sub_b : V ⊆ smoothDirichletHalfBox (ρ / 2) b :=
      fun _ hz' => ⟨hz'.1, hz'.2.1, hz'.2.2.trans hρb⟩
    have hA_sub_b : smoothDirichletHalfBox A ρ ⊆ smoothDirichletHalfBox A b :=
      fun _ hz' => ⟨hz'.1, hz'.2.1, hz'.2.2.trans hρb⟩
    have hsmallgrad (h : ℝ) (hh : h ∈ Ioo 0 ε) (j : ℕ) (hj : j ≤ k) (i : Fin 2) :
        MemLp (dirD (dirichletTangentialDifferenceIter h j u) (coordDir i)) 2 (volume.restrict W) := by
      have hmj : ρ + (j : ℝ) * |h| ≤ A :=
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right (by exact_mod_cast hj)
          (abs_nonneg h))).trans (hsteps h hh).2.2.1
      exact (dirichletTangentialDifferenceIter_gradient_memLp j hmj hs (hg i)).mono_measure
        (Measure.restrict_mono_set volume hW_sub_b)
    let v : ℝ → ℂ → ℂ := fun h => dirichletTangentialDifferenceIter h k u
    let Q : ℝ → ℂ → ℂ := fun h => dirichletTangentialDifferenceIter h k G
    let C : ℝ → Fin 2 → ℂ → ℂ := fun h => dirichletHigherCoefficientDifferenceFlux f h k u
    have hvenergy (h : ℝ) (hh : h ∈ Ioo 0 ε) : (∫ z in V, ‖v h z‖ ^ 2) ≤ E₀ := by
      have hnmargin : ρ + (n : ℝ) * |h| ≤ A :=
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ n)
          (abs_nonneg h))).trans (hsteps h hh).2.2.1
      have hnm : MemLp (dirichletTangentialDifferenceIter h n u) 2 (volume.restrict W) :=
        (dirichletTangentialDifferenceIter_memLp n hnmargin hm).mono_measure
          (Measure.restrict_mono_set volume hW_sub_b)
      have hns : ContDiffOn ℝ (⊤ : ℕ∞) (dirichletTangentialDifferenceIter h n u) W :=
        (dirichletTangentialDifferenceIter_contDiffOn n hnmargin hs).mono hW_sub_b
      have hnx : MemLp (dirD (dirichletTangentialDifferenceIter h n u) 1) 2 (volume.restrict W) := by
        simpa only [coordDir, Matrix.cons_val_zero] using hsmallgrad h hh n (Nat.le_succ n) 0
      have hv' := dirichlet_halfBox_tangential_difference_energy_le
        (by linarith : 0 < ρ / 2) hρ hh.1 (hsteps h hh).2.2.2 hns hnm hnx
      have hnorm : (∫ z in W, ‖dirD (dirichletTangentialDifferenceIter h n u) 1 z‖ ^ 2) ≤
          ∫ z in W, dirichletGradientSq (dirichletTangentialDifferenceIter h n u) z :=
        integral_mono_ae (hnx.integrable_norm_pow (by norm_num))
          (dirichletGradientSq_integrable (hsmallgrad h hh n (Nat.le_succ n)))
          (Eventually.of_forall fun _ => le_add_of_nonneg_right (sq_nonneg _))
      exact hv'.trans (hnorm.trans (hprev h (hsteps h hh).1 n le_rfl))
    obtain ⟨MQ₀, hMQ₀⟩ := (isCompact_smoothDirichletClosedHalfBox ρ ρ).exists_bound_of_continuousOn
      (dirichletCoordinateDerivative_contDiff hGs 1 k).continuous.continuousOn
    let MQ := max MQ₀ 0
    have : IsFiniteMeasure (volume.restrict V) := ⟨by
      simpa only [Measure.restrict_apply_univ] using
        (dirichlet_halfBox_isBounded (a := ρ / 2) (b := ρ)).measure_lt_top⟩
    let EQ := ∫ _ : ℂ, MQ ^ 2 ∂volume.restrict V
    have hEQ : 0 ≤ EQ := integral_nonneg fun _ => sq_nonneg _
    have hQdata (h : ℝ) (hh : h ∈ Ioo 0 ε) :
        MemLp (Q h) 2 (volume.restrict V) ∧ (∫ z in V, ‖Q h z‖ ^ 2) ≤ EQ := by
      have hQb (z : ℂ) (hz' : z ∈ V) : ‖Q h z‖ ≤ MQ :=
        dirichletTangentialDifferenceIter_norm_le k hh.1 (hposMargin h hh) hGs
          (fun w hw => (hMQ₀ w hw).trans (le_max_left _ _)) ⟨hz'.1.le, hz'.2.1.le, hz'.2.2.le⟩
      have hQm : MemLp (Q h) 2 (volume.restrict V) :=
        MemLp.of_bound (dirichletTangentialDifferenceIter_contDiff hGs h k).continuous.aestronglyMeasurable
          MQ ((ae_restrict_mem (isOpen_smoothDirichletHalfBox _ _).measurableSet).mono hQb)
      exact ⟨hQm, integral_mono_ae (hQm.integrable_norm_pow (by norm_num)) (integrable_const _)
        ((ae_restrict_mem (isOpen_smoothDirichletHalfBox _ _).measurableSet).mono fun z hz' =>
          pow_le_pow_left₀ (norm_nonneg _) (hQb z hz') 2)⟩
    obtain ⟨MC, hMC, hCbound⟩ := exists_dirichletGraphHigherCommutator_bound hf ρ ρ k
    let EC := (3 * MC ^ 2 * ∑ j ∈ Finset.range k, (k.choose j : ℝ) ^ 2) * ((k : ℝ) * E₀)
    have hEC : 0 ≤ EC := mul_nonneg (mul_nonneg (by positivity)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (mul_nonneg (Nat.cast_nonneg _) hE₀)
    have hug (i : Fin 2) : MemLp (dirD u (coordDir i)) 2 (volume.restrict (smoothDirichletHalfBox A ρ)) :=
      (hg i).mono_measure (Measure.restrict_mono_set volume hA_sub_b)
    have hus : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A ρ) := hs.mono hA_sub_b
    have hCm (h : ℝ) (hh : h ∈ Ioo 0 ε) (i : Fin 2) : MemLp (C h i) 2 (volume.restrict V) :=
      dirichletHigherCoefficientDifferenceFlux_memLp k (hmargin h hh) hf hMC
        (hCbound (ρ / 2) h hh.1 (hposMargin h hh)) hug i
    have hCenergy (h : ℝ) (hh : h ∈ Ioo 0 ε) :
        (∫ z in V, ‖C h 0 z‖ ^ 2 + ‖C h 1 z‖ ^ 2) ≤ EC :=
      dirichletHigherCoefficientDifferenceFlux_energy_le k (hmargin h hh) hf hus hMC
        (hCbound (ρ / 2) h hh.1 (hposMargin h hh)) hug fun j hj =>
          (setIntegral_mono_set
            (dirichletGradientSq_integrable (hsmallgrad h hh j
              ((Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans (Nat.le_succ n))))
            (Eventually.of_forall fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
            hVW.eventuallyLE).trans
            (hprev h (hsteps h hh).1 j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
    have hweak (h : ℝ) (hh : h ∈ Ioo 0 ε) (φ : ℂ → ℂ) (hφ : TestFunction V φ) :
        (∫ z in V, ∑ i : Fin 2,
          (dirichletShiftedFlux f ((k : ℝ) * h) (v h) i z + C h i z) * dirD φ (coordDir i) z) =
          ∫ z in V, Q h z * φ z := by
      let H : Fin 2 → ℂ → ℂ := fun i => dirichletTangentialDifferenceIter h k (dirichletFlattenedFlux f u i)
      have hU_A := isOpen_smoothDirichletHalfBox A ρ
      have hV_o := isOpen_smoothDirichletHalfBox (ρ / 2) ρ
      have hflux (i : Fin 2) := dirichletFlattenedFlux_contDiffOn hU_A hf hus i
      have hH (i : Fin 2) : ContDiffOn ℝ (⊤ : ℕ∞) (H i) V :=
        dirichletTangentialDifferenceIter_contDiffOn k (hmargin h hh) (hflux i)
      have hdiv (z : ℂ) (hz' : z ∈ V) :
          (∑ i : Fin 2, dirD (H i) (coordDir i) z) = -Q h z := by
        have hd (i : Fin 2) : dirD (H i) (coordDir i) z =
            dirichletTangentialDifferenceIter h k (dirD (dirichletFlattenedFlux f u i) (coordDir i)) z :=
          dirichletTangentialDifferenceIter_dirD k (hmargin h hh) (hflux i) hz' _
        simp_rw [hd]; rw [Fin.sum_univ_two]
        simp only [coordDir, Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [← congrFun (dirichletTangentialDifferenceIter_add h k
          (dirD (dirichletFlattenedFlux f u 0) 1) (dirD (dirichletFlattenedFlux f u 1) Complex.I)) z]
        change dirichletTangentialDifferenceIter h k (dirichletFlattenedDivergence f u) z = _
        rw [dirichletTangentialDifferenceIter_congr (c := fun w => -G w) h k z fun j hj =>
          hstrong (z + (((j : ℝ) * h : ℝ) : ℂ))
          ⟨by simpa only [Complex.add_re, Complex.ofReal_re] using
              (abs_add_le z.re ((j : ℝ) * h)).trans_lt
                ((add_lt_add_of_lt_of_le hz'.1
                  (by rw [abs_mul, Nat.abs_cast]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (abs_nonneg h))).trans_le
                  (hmargin h hh)),
           by simpa using hz'.2.1,
           by simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using hz'.2.2.trans hρb⟩]
        simpa only [Q, neg_one_mul] using congrFun (dirichletTangentialDifferenceIter_const_mul h k (-1 : ℂ) G) z
      have hI (i : Fin 2) := dirichlet_local_smooth_mul_test_integrable hV_o (hH i) (hφ.dirD (coordDir i))
      have hDI (i : Fin 2) := dirichlet_local_smooth_mul_test_integrable hV_o
        (dirichlet_contDiffOn_dirD hV_o (hH i) (coordDir i)) hφ
      have heq_ibp : (∫ z in V, ∑ i : Fin 2, H i z * dirD φ (coordDir i) z) =
          -(∫ z in V, (∑ i : Fin 2, dirD (H i) (coordDir i) z) * φ z) := by
        rw [integral_finset_sum _ fun i _ => hI i,
          Finset.sum_congr rfl fun i _ => dirichlet_local_smooth_field_test_eq_neg_dirD hV_o (hH i) hφ i,
          Finset.sum_neg_distrib, ← integral_finset_sum _ fun i _ => hDI i]
        congr 1; refine integral_congr_ae (Eventually.of_forall fun _ => (Finset.sum_mul _ _ _).symm)
      have hleft : (∫ z in V, ∑ i : Fin 2,
          (dirichletShiftedFlux f ((k : ℝ) * h) (v h) i z + C h i z) * dirD φ (coordDir i) z) =
          ∫ z in V, ∑ i : Fin 2, H i z * dirD φ (coordDir i) z :=
        setIntegral_congr_fun hV_o.measurableSet fun z hz' =>
          Finset.sum_congr rfl fun i _ => by rw [← dirichletTangentialDifferenceIter_flux_split k (hmargin h hh) f hus hz' i]
      rw [hleft, heq_ibp, ← integral_neg]
      refine setIntegral_congr_fun hV_o.measurableSet fun z hz' => ?_
      change -((∑ i : Fin 2, dirD (H i) (coordDir i) z) * φ z) = Q h z * φ z
      rw [hdiv z hz']; ring
    obtain ⟨r₀, hr₀, hra₀, hrρ₀, η, Bη, hBη, hηsupp, hη, hηgrad, hηone⟩ :=
      exists_dirichlet_boundary_energy_cutoff (by linarith : 0 < ρ / 2) hρ
    let Mf := 2 * (1 + (K : ℝ) ^ 2)
    have hMf : 0 < Mf := by dsimp [Mf]; positivity
    let E₁ := 2 * Mf * (EQ + (4 * Mf + 2 * Bη ^ 2) * EC + (32 * Bη ^ 2 * Mf ^ 3 + 2) * E₀)
    have hE₁ : 0 ≤ E₁ := by dsimp [E₁]; positivity
    let r := r₀ / 2
    have hr : 0 < r := by dsimp [r]; linarith
    have hrρ : r < ρ := by dsimp [r]; linarith
    have hnew (h : ℝ) (hh : h ∈ Ioo 0 ε) :
        (∫ z in smoothDirichletHalfBox r r, dirichletGradientSq (v h) z) ≤ E₁ := by
      have hvc : ContinuousOn (v h) (smoothDirichletClosedHalfBox (ρ / 2) ρ) :=
        (dirichletTangentialDifferenceIter_continuousOn k (hmargin h hh) hc).mono
          fun _ hz' => ⟨hz'.1, hz'.2.1, hz'.2.2.trans hρb.le⟩
      have hvs : ContDiffOn ℝ (⊤ : ℕ∞) (v h) V :=
        (dirichletTangentialDifferenceIter_contDiffOn k (hmargin h hh) hs).mono
          fun _ hz' => ⟨hz'.1, hz'.2.1, hz'.2.2.trans hρb⟩
      have hvz (x : ℝ) (hx : |x| < ρ / 2) : v h (x : ℂ) = 0 :=
        dirichletTangentialDifferenceIter_zero_bottom k (hmargin h hh) hz hx
      have hvm : MemLp (v h) 2 (volume.restrict V) :=
        (dirichletTangentialDifferenceIter_memLp k (hmargin h hh) hm).mono_measure
          (Measure.restrict_mono_set volume hV_sub_b)
      have hvg (i : Fin 2) : MemLp (dirD (v h) (coordDir i)) 2 (volume.restrict V) :=
        (hsmallgrad h hh k le_rfl i).mono_measure (Measure.restrict_mono_set volume hVW)
      have henergy := dirichlet_localized_boundary_energy_bound hρ hMf hBη η
        hηsupp hη hηgrad hvc hvs hvz hvm hvg
        (fun i => dirichletShiftedFlux_memLp hf hLip ((k : ℝ) * h) hvg i)
        (hCm h hh) (hQdata h hh).1
        (fun z _ => dirichletShiftedFlux_coercive hLip ((k : ℝ) * h) (v h) z)
        (fun z _ => dirichletShiftedFlux_norm_sum_bound hLip ((k : ℝ) * h) (v h) z)
        (hweak h hh)
      have hbnd := henergy.trans (add_le_add
        (add_le_add (hQdata h hh).2 (mul_le_mul_of_nonneg_left (hCenergy h hh) (by positivity)))
        (mul_le_mul_of_nonneg_left (hvenergy h hh) (by positivity)))
      have hJbound : (∫ z in V, ‖η z‖ ^ 2 * dirichletGradientSq (v h) z) ≤ E₁ := by
        have hd_le := (div_le_iff₀ (by positivity : 0 < 2 * Mf)).mp hbnd
        calc (∫ z in V, ‖η z‖ ^ 2 * dirichletGradientSq (v h) z)
            ≤ (EQ + (4 * Mf + 2 * Bη ^ 2) * EC + (32 * Bη ^ 2 * Mf ^ 3 + 2) * E₀) * (2 * Mf) := hd_le
          _ = E₁ := by dsimp only [E₁]; ring
      have hηx := dirichlet_localized_memLp η
        (by simpa only [coordDir, Matrix.cons_val_zero] using hvg 0 : MemLp (dirD (v h) 1) 2 _)
      have hηy := dirichlet_localized_memLp η
        (by simpa only [coordDir, Matrix.cons_val_one, Matrix.cons_val_zero] using hvg 1 :
          MemLp (dirD (v h) Complex.I) 2 _)
      have hJi : IntegrableOn (fun z => ‖η z‖ ^ 2 * dirichletGradientSq (v h) z) V :=
        ((hηx.integrable_norm_pow (by norm_num)).add (hηy.integrable_norm_pow (by norm_num))).congr
          (Eventually.of_forall fun z => by
            change ‖η z * dirD (v h) 1 z‖ ^ 2 + ‖η z * dirD (v h) Complex.I z‖ ^ 2 = _
            simp only [dirichletGradientSq, norm_mul, mul_pow]; ring)
      have hW_eq : (∫ z in smoothDirichletHalfBox r r, dirichletGradientSq (v h) z) =
          ∫ z in smoothDirichletHalfBox r r, ‖η z‖ ^ 2 * dirichletGradientSq (v h) z :=
        setIntegral_congr_fun (isOpen_smoothDirichletHalfBox _ _).measurableSet fun z hzW => by
          change dirichletGradientSq (v h) z = ‖η z‖ ^ 2 * dirichletGradientSq (v h) z
          rw [hηone z hzW, norm_one, one_pow, one_mul]
      have hWsub : smoothDirichletHalfBox r r ⊆ V := fun z hzW =>
        ⟨hzW.1.trans (by dsimp [r]; linarith), hzW.2.1, hzW.2.2.trans (by dsimp [r]; linarith)⟩
      rw [hW_eq]
      exact (setIntegral_mono_set hJi
        (Eventually.of_forall fun _ => mul_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
        hWsub.eventuallyLE).trans hJbound
    have hrW : smoothDirichletHalfBox r r ⊆ W := fun z hz' => ⟨hz'.1.trans hrρ, hz'.2.1, hz'.2.2.trans hrρ⟩
    refine ⟨r, ε, max E₀ E₁, hr, by linarith, hrρ.trans hρb, hε, hE₀.trans (le_max_left _ _),
      fun h hh j hj => ?_⟩
    rcases Nat.eq_or_lt_of_le hj with rfl | hjk
    · exact (hnew h hh).trans (le_max_right _ _)
    · have hjn : j ≤ n := Nat.le_of_lt_succ hjk
      exact (setIntegral_mono_set
        (dirichletGradientSq_integrable (hsmallgrad h hh j (hjn.trans (Nat.le_succ n))))
        (Eventually.of_forall fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
        hrW.eventuallyLE).trans ((hprev h (hsteps h hh).1 j hjn).trans (le_max_left _ _))

/-! ### Normal equation recovery & mixed-order `L²` bootstrap -/

private def dirichletGraphCurvature (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  ((deriv (deriv f) z.re : ℝ) : ℂ)

private def dirichletNormalCoefficientInverse (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  Complex.ofReal ((1 + (deriv f z.re) ^ 2 : ℝ)⁻¹)

private def dirichletNormalRecoveryExpression (f : ℝ → ℝ) (q : ℕ) (u G : ℂ → ℂ) (z : ℂ) : ℂ :=
  ((-1 : ℂ) * dirichletCoordinateDerivative Complex.I q G z +
    dirichletGraphCurvature f z * dirichletCoordinateDerivative Complex.I (q + 1) u z) +
    ((2 : ℂ) * dirichletGraphSlope f z) * dirichletMixedDerivative 1 (q + 1) u z -
    dirichletMixedDerivative 2 q u z

private theorem dirichletBootstrap_realCoefficient_dirD_I {r : ℝ → ℝ}
    (hr : ContDiff ℝ (⊤ : ℕ∞) r) (z : ℂ) :
    dirD (fun w : ℂ => (r w.re : ℂ)) Complex.I z = 0 := by
  have hd := (hr.differentiable (by simp)) z.re
  have hs := Complex.ofRealCLM.hasFDerivAt.comp z
    (hd.hasDerivAt.comp_hasFDerivAt z Complex.reCLM.hasFDerivAt)
  change fderiv ℝ (Complex.ofRealCLM ∘ r ∘ Complex.re) z Complex.I = 0
  rw [hs.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    Complex.reCLM_apply, Complex.I_re, smul_zero, map_zero]

private theorem dirichlet_normal_higher_derivative_recovery {U : Set ℂ} (hU : IsOpen U)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {u G : ℂ → ℂ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U)
    (hstrong : ∀ z ∈ U, dirichletFlattenedDivergence f u z = -G z) (q : ℕ) :
    EqOn (dirichletCoordinateDerivative Complex.I (q + 2) u)
      (fun z => dirichletNormalCoefficientInverse f z *
        dirichletNormalRecoveryExpression f q u G z) U := by
  have hcurv_cd : ContDiff ℝ (⊤ : ℕ∞) (dirichletGraphCurvature f) :=
    Complex.ofRealCLM.contDiff.comp
      (((contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hf).2).2).comp Complex.reCLM.contDiff)
  have hinv_r : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (1 + (deriv f x) ^ 2)⁻¹) :=
    (contDiff_const.add ((contDiff_infty_iff_deriv.mp hf).2.pow 2)).inv fun _ => by positivity
  have hinv_cd : ContDiff ℝ (⊤ : ℕ∞) (dirichletNormalCoefficientInverse f) :=
    Complex.ofRealCLM.contDiff.comp (hinv_r.comp Complex.reCLM.contDiff)
  have hbase : EqOn (dirichletCoordinateDerivative Complex.I 2 u)
      (fun z => dirichletNormalCoefficientInverse f z *
        dirichletNormalRecoveryExpression f 0 u G z) U := fun z hz => by
    let d := dirichletGraphSlope f
    let x := dirD u 1
    let y := dirD u Complex.I
    have hd : DifferentiableAt ℝ d z := (dirichletGraphSlope_contDiff hf).differentiable (by simp) z
    have hx : DifferentiableAt ℝ x z :=
      dirichletBootstrap_differentiableAt hU (dirichlet_contDiffOn_dirD hU hu 1) hz
    have hy : DifferentiableAt ℝ y z :=
      dirichletBootstrap_differentiableAt hU (dirichlet_contDiffOn_dirD hU hu Complex.I) hz
    have hdx : dirD d 1 z = dirichletGraphCurvature f z := by
      have hdf := ((contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp)) z.re
      have hs := Complex.ofRealCLM.hasFDerivAt.comp z
        (hdf.hasDerivAt.comp_hasFDerivAt z Complex.reCLM.hasFDerivAt)
      change fderiv ℝ (Complex.ofRealCLM ∘ (deriv f ∘ Complex.re)) z 1 = _
      rw [hs.fderiv]
      simp [dirichletGraphCurvature]
    have hdy : dirD d Complex.I z = 0 := dirD_dirichletGraphSlope_I hf z
    have haI : dirD (fun w => (1 : ℂ) + d w ^ 2) Complex.I z = 0 := by
      rw [show (fun w => (1 : ℂ) + d w ^ 2) = fun w => 1 + d w * d w from funext fun w => by rw [pow_two],
        dirichlet_normal_dirD_add (a := fun _ => (1 : ℂ)) (b := fun w => d w * d w)
          (differentiableAt_const 1) (hd.mul hd),
        dirichlet_normal_dirD_mul (a := d) (b := d) hd hd, hdy]
      simp [dirD]
    have hflux₀ : dirD (dirichletFlattenedFlux f u 0) 1 z =
        dirD x 1 z - (dirichletGraphCurvature f z * y z + d z * dirD y 1 z) := by
      change dirD (fun w => x w - d w * y w) 1 z = _
      rw [dirichlet_normal_dirD_sub (a := x) (b := fun w => d w * y w) hx (hd.mul hy),
        dirichlet_normal_dirD_mul (a := d) (b := y) hd hy, hdx]
    have hflux₁ : dirD (dirichletFlattenedFlux f u 1) Complex.I z =
        -d z * dirD x Complex.I z + (1 + d z ^ 2) * dirD y Complex.I z := by
      rw [show dirichletFlattenedFlux f u 1 = fun w => (1 + d w ^ 2) * y w - d w * x w from
        funext fun w => by change -d w * x w + (1 + d w ^ 2) * y w = _; ring,
        dirichlet_normal_dirD_sub (a := fun w => (1 + d w ^ 2) * y w) (b := fun w => d w * x w)
          (((differentiableAt_const (1 : ℂ)).add (hd.pow 2)).mul hy) (hd.mul hx),
        dirichlet_normal_dirD_mul (a := fun w => 1 + d w ^ 2) (b := y)
          ((differentiableAt_const 1).add (hd.pow 2)) hy,
        dirichlet_normal_dirD_mul (a := d) (b := x) hd hx, haI, hdy]
      ring
    have hexp : dirichletFlattenedDivergence f u z =
        dirD (dirD u 1) 1 z - dirichletGraphCurvature f z * dirD u Complex.I z -
          2 * d z * dirD (dirD u 1) Complex.I z + (1 + d z ^ 2) * dirD (dirD u Complex.I) Complex.I z := by
      rw [dirichletFlattenedDivergence, hflux₀, hflux₁]
      change dirD (dirD u 1) 1 z - (dirichletGraphCurvature f z * dirD u Complex.I z +
        d z * dirD (dirD u Complex.I) 1 z) + (-d z * dirD (dirD u 1) Complex.I z +
          (1 + d z ^ 2) * dirD (dirD u Complex.I) Complex.I z) = _
      rw [dirichlet_dirD_comm hU hu hz Complex.I 1]; ring
    rw [hstrong z hz] at hexp
    have hinv_mul : dirichletNormalCoefficientInverse f z * (1 + d z ^ 2) = 1 := by
      have hpos : (1 + (deriv f z.re) ^ 2 : ℝ) ≠ 0 := by positivity
      rw [show (1 + d z ^ 2 : ℂ) = ((1 + (deriv f z.re) ^ 2 : ℝ) : ℂ) by simp [d, dirichletGraphSlope],
        dirichletNormalCoefficientInverse, ← Complex.ofReal_mul, inv_mul_cancel₀ hpos, Complex.ofReal_one]
    have hnum : dirichletNormalRecoveryExpression f 0 u G z =
        (1 + d z ^ 2) * dirD (dirD u Complex.I) Complex.I z := by
      simp only [dirichletNormalRecoveryExpression, dirichletMixedDerivative, dirichletCoordinateDerivative]
      rw [dirichlet_dirD_comm hU hu hz Complex.I 1]
      dsimp only [d]; linear_combination hexp
    change dirD (dirD u Complex.I) Complex.I z =
      dirichletNormalCoefficientInverse f z * dirichletNormalRecoveryExpression f 0 u G z
    rw [hnum, ← mul_assoc, hinv_mul, one_mul]
  let t₀ : ℂ → ℂ := fun z => (-1 : ℂ) * G z
  let t₁ : ℂ → ℂ := fun z => dirichletGraphCurvature f z * dirichletCoordinateDerivative Complex.I 1 u z
  let t₂ : ℂ → ℂ := fun z => ((2 : ℂ) * dirichletGraphSlope f z) * dirichletMixedDerivative 1 1 u z
  let t₃ := dirichletMixedDerivative 2 0 u
  have h₀ : ContDiffOn ℝ (⊤ : ℕ∞) t₀ U := contDiffOn_const.mul hG
  have h₁ : ContDiffOn ℝ (⊤ : ℕ∞) t₁ U :=
    hcurv_cd.contDiffOn.mul (dirichletCoordinateDerivative_contDiffOn hU hu Complex.I 1)
  have h₂ : ContDiffOn ℝ (⊤ : ℕ∞) t₂ U :=
    (contDiff_const.mul (dirichletGraphSlope_contDiff hf)).contDiffOn.mul
      (dirichletMixedDerivative_contDiffOn hU hu 1 1)
  have h₃ : ContDiffOn ℝ (⊤ : ℕ∞) t₃ U := dirichletMixedDerivative_contDiffOn hU hu 2 0
  have hexpr_cd : ContDiffOn ℝ (⊤ : ℕ∞) (dirichletNormalRecoveryExpression f 0 u G) U :=
    ((h₀.add h₁).add h₂).sub h₃
  have hhq := dirichletCoordinateDerivative_eqOn hU hbase Complex.I q
  have hmul := dirichletCoordinateDerivative_mul_eqOn_of_dirD_zero hU
    hinv_cd.contDiffOn hexpr_cd Complex.I (fun z _ => dirichletBootstrap_realCoefficient_dirD_I hinv_r z) q
  intro z hz
  rw [← dirichletCoordinateDerivative_iterate Complex.I q 2 u]
  refine (hhq hz).trans ((hmul hz).trans (congrArg (dirichletNormalCoefficientInverse f z * ·) ?_))
  change dirichletCoordinateDerivative Complex.I q (fun w => (t₀ w + t₁ w) + t₂ w - t₃ w) z = _
  rw [dirichletCoordinateDerivative_sub_eqOn hU ((h₀.add h₁).add h₂) h₃ Complex.I q hz]
  change dirichletCoordinateDerivative Complex.I q (fun w => (t₀ w + t₁ w) + t₂ w) z -
    dirichletCoordinateDerivative Complex.I q t₃ z = _
  rw [dirichletCoordinateDerivative_add_eqOn hU (h₀.add h₁) h₂ Complex.I q hz]
  change (dirichletCoordinateDerivative Complex.I q (fun w => t₀ w + t₁ w) z +
    dirichletCoordinateDerivative Complex.I q t₂ z) -
    dirichletCoordinateDerivative Complex.I q t₃ z = _
  rw [dirichletCoordinateDerivative_add_eqOn hU h₀ h₁ Complex.I q hz]
  have ht₀ := dirichletCoordinateDerivative_const_mul_eqOn hU hG (-1) Complex.I q hz
  have ht₁ := dirichletCoordinateDerivative_mul_eqOn_of_dirD_zero hU hcurv_cd.contDiffOn
    (dirichletCoordinateDerivative_contDiffOn hU hu Complex.I 1) Complex.I
    (fun w _ => dirichletBootstrap_realCoefficient_dirD_I
      ((contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hf).2).2) w) q hz
  have ht₂ := dirichletCoordinateDerivative_mul_eqOn_of_dirD_zero hU
    (contDiff_const.mul (dirichletGraphSlope_contDiff hf)).contDiffOn
    (dirichletMixedDerivative_contDiffOn hU hu 1 1) Complex.I
    (fun w _ => by
      change fderiv ℝ (fun x => (2 : ℂ) * dirichletGraphSlope f x) w Complex.I = 0
      rw [fderiv_const_mul ((dirichletGraphSlope_contDiff hf).differentiable (by simp) w) (2 : ℂ)]
      change (2 : ℂ) * dirD (dirichletGraphSlope f) Complex.I w = 0
      rw [dirD_dirichletGraphSlope_I hf w, mul_zero]) q hz
  change (dirichletCoordinateDerivative Complex.I q t₀ z +
      dirichletCoordinateDerivative Complex.I q t₁ z) +
    dirichletCoordinateDerivative Complex.I q t₂ z -
    dirichletCoordinateDerivative Complex.I q t₃ z = _
  change dirichletCoordinateDerivative Complex.I q t₀ z = _ at ht₀
  change dirichletCoordinateDerivative Complex.I q t₁ z = _ at ht₁
  change dirichletCoordinateDerivative Complex.I q t₂ z = _ at ht₂
  rw [ht₀, ht₁, ht₂, dirichletCoordinateDerivative_iterate Complex.I q 1 u]
  have hmix (p r : ℕ) : dirichletCoordinateDerivative Complex.I q (dirichletMixedDerivative p r u) z =
      dirichletMixedDerivative p (q + r) u z := by
    have hc := dirichletCoordinateDerivative_comm_eqOn hU
      (dirichletCoordinateDerivative_contDiffOn hU hu Complex.I r) 1 Complex.I p q hz
    simpa only [dirichletMixedDerivative, dirichletCoordinateDerivative_iterate] using hc.symm
  change -1 * dirichletCoordinateDerivative Complex.I q G z +
    dirichletGraphCurvature f z * dirichletCoordinateDerivative Complex.I (q + 1) u z +
    2 * dirichletGraphSlope f z * dirichletCoordinateDerivative Complex.I q (dirichletMixedDerivative 1 1 u) z -
    dirichletCoordinateDerivative Complex.I q (dirichletMixedDerivative 2 0 u) z = _
  rw [hmix 1 1, hmix 2 0]
  simp only [Nat.add_zero, dirichletNormalRecoveryExpression]

private theorem dirichletBootstrap_tangential_mul_memLp {a b : ℝ} {c v : ℂ → ℂ}
    (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b)) (p : ℕ)
    (hLp : ∀ j ≤ p, MemLp (dirichletCoordinateDerivative 1 j v) 2
      (volume.restrict (smoothDirichletHalfBox a b))) :
    MemLp (dirichletCoordinateDerivative 1 p (fun z => c z * v z)) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  induction p generalizing c v with
  | zero =>
    obtain ⟨M, hM⟩ := (isCompact_smoothDirichletClosedHalfBox a b).exists_bound_of_continuousOn
      hc.continuous.continuousOn
    refine (hLp 0 le_rfl).of_le_mul (c := M)
      (hc.continuous.aestronglyMeasurable.mul (hLp 0 le_rfl).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet] with z hz
    change ‖c z * v z‖ ≤ M * ‖v z‖; rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hM z ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩) (norm_nonneg _)
  | succ p ih =>
    let U := smoothDirichletHalfBox a b
    have hU : IsOpen U := isOpen_smoothDirichletHalfBox a b
    have hdv := dirichlet_contDiffOn_dirD hU hv 1
    have hdc := dirichlet_dirD_contDiff hc 1
    have h₀ := ih hdc hv fun j _ => hLp j (by omega)
    have h₁ := ih hc hdv fun j _ => by
      rw [dirichletCoordinateDerivative_succ_right]; exact hLp (j + 1) (by omega)
    have hsplit : EqOn (dirD (fun z => c z * v z) 1) (fun z => dirD c 1 z * v z + c z * dirD v 1 z) U :=
      fun z hz => dirichlet_normal_dirD_mul (hc.differentiable (by simp) z)
        (dirichletBootstrap_differentiableAt hU hv hz) 1
    have hiter := dirichletCoordinateDerivative_eqOn hU hsplit 1 p
    have hadd := dirichletCoordinateDerivative_add_eqOn hU (hdc.contDiffOn.mul hv) (hc.contDiffOn.mul hdv) 1 p
    refine (h₀.add h₁).ae_eq ?_
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    rw [← dirichletCoordinateDerivative_succ_right]
    exact ((hiter hz).trans (hadd hz)).symm

theorem exists_dirichlet_halfBox_mixed_derivative_memLp
    {A b : ℝ} (hA : 0 < A) (hb : 0 < b) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {K : NNReal} (hLip : LipschitzWith K f)
    {u G : ℂ → ℂ} (hc : ContinuousOn u (smoothDirichletClosedHalfBox A b))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b))
    (hz : ∀ x : ℝ, |x| < A → u (x : ℂ) = 0)
    (hm : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b)))
    (hg : ∀ i : Fin 2, MemLp (dirD u (coordDir i)) 2 (volume.restrict (smoothDirichletHalfBox A b)))
    (hstrong : ∀ z ∈ smoothDirichletHalfBox A b, dirichletFlattenedDivergence f u z = -G z)
    (hGs : ContDiff ℝ (⊤ : ℕ∞) G) (N : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < A / 2 ∧ ρ < b ∧
      ∀ p q : ℕ, p + q ≤ N → MemLp (dirichletMixedDerivative p q u) 2
        (volume.restrict (smoothDirichletHalfBox ρ ρ)) := by
  obtain ⟨ρ, ε₀, E, hρ, hρA, hρb, hε₀, _, henergy⟩ :=
    exists_dirichlet_halfBox_higher_difference_gradient_energy hA hb hf hLip hc hs hz hm hg hstrong hGs N
  let W := smoothDirichletHalfBox ρ ρ
  let hW : IsOpen W := isOpen_smoothDirichletHalfBox ρ ρ
  let μ := volume.restrict W
  have hWU : W ⊆ smoothDirichletHalfBox A b :=
    fun z hz' => ⟨hz'.1.trans (by linarith), hz'.2.1, hz'.2.2.trans hρb⟩
  let ε := min ε₀ ((A - ρ) / ((N : ℝ) + 1))
  have hε : 0 < ε := lt_min hε₀ (div_pos (by linarith) (by positivity))
  have hgrad_lim (j : ℕ) (hj : j ≤ N) (i : Fin 2) :
      MemLp (dirichletCoordinateDerivative 1 j (dirD u (coordDir i))) 2 μ := by
    let F : ℝ → ℂ → ℂ := fun h => dirD (dirichletTangentialDifferenceIter h j u) (coordDir i)
    let g := dirichletCoordinateDerivative 1 j (dirD u (coordDir i))
    have hstep (h : ℝ) (hh : h ∈ Ioo 0 ε) : h ∈ Ioo 0 ε₀ ∧ ρ + (j : ℝ) * |h| ≤ A := by
      have hh₀ := hh.2.trans_le (min_le_left _ _)
      have hh' := (lt_div_iff₀ (by positivity : 0 < (N : ℝ) + 1)).mp (hh.2.trans_le (min_le_right _ _))
      have hjh : (j : ℝ) * h ≤ (N : ℝ) * h := mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hh.1.le
      rw [abs_of_pos hh.1]; exact ⟨⟨hh.1, hh₀⟩, by nlinarith⟩
    have hmem (h : ℝ) (hh : h ∈ Ioo 0 ε) (l : Fin 2) :
        MemLp (dirD (dirichletTangentialDifferenceIter h j u) (coordDir l)) 2 μ :=
      (dirichletTangentialDifferenceIter_gradient_memLp j (hstep h hh).2 hs (hg l)).mono_measure
        (Measure.restrict_mono_set volume
          (show W ⊆ smoothDirichletHalfBox ρ b from
            fun _ hz' => ⟨hz'.1, hz'.2.1, hz'.2.2.trans hρb⟩))
    have he (h : ℝ) (hh : h ∈ Ioo 0 ε) : (∫ z, ‖F h z‖ ^ 2 ∂μ) ≤ E := by
      have hle (z : ℂ) : ‖F h z‖ ^ 2 ≤
          dirichletGradientSq (dirichletTangentialDifferenceIter h j u) z := by
        fin_cases i
        · exact le_add_of_nonneg_right (sq_nonneg _)
        · exact le_add_of_nonneg_left (sq_nonneg _)
      exact (integral_mono_ae ((hmem h hh i).integrable_norm_pow (by norm_num))
        (dirichletGradientSq_integrable (hmem h hh)) (Eventually.of_forall hle)).trans
        (henergy h (hstep h hh).1 j hj)
    have hbound : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), eLpNorm (F h) 2 μ ≤ ENNReal.ofReal (Real.sqrt E) := by
      filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds] with h hh hhε
      apply (ENNReal.toReal_le_toReal (hmem h ⟨hh, hhε⟩ i).eLpNorm_ne_top (by simp)).mp
      rw [dirichlet_eLpNorm_toReal_eq_sqrt_energy (hmem h ⟨hh, hhε⟩ i),
        ENNReal.toReal_ofReal (Real.sqrt_nonneg E)]
      exact Real.sqrt_le_sqrt (he h ⟨hh, hhε⟩)
    have hU_o := isOpen_smoothDirichletHalfBox A b
    have hgmeas : AEStronglyMeasurable g μ :=
      ((dirichletCoordinateDerivative_contDiffOn hU_o
        (dirichlet_contDiffOn_dirD hU_o hs (coordDir i)) 1 j).continuousOn.aestronglyMeasurable
          hU_o.measurableSet).mono_measure (Measure.restrict_mono_set volume hWU)
    have hlim : ∀ᵐ z ∂μ, Tendsto (fun h : ℝ => F h z) (𝓝[>] (0 : ℝ)) (𝓝 (g z)) := by
      filter_upwards [ae_restrict_mem hW.measurableSet] with z hzW
      refine (dirichletTangentialDifferenceIter_tendsto_of_contDiffOn hU_o
        (dirichlet_contDiffOn_dirD hU_o hs (coordDir i)) j (hWU hzW)).congr' ?_
      filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds] with h hh hhε
      exact (dirichletTangentialDifferenceIter_dirD j (hstep h ⟨hh, hhε⟩).2 hs
        ⟨hzW.1, hzW.2.1, hzW.2.2.trans hρb⟩ (coordDir i)).symm
    exact lt_of_le_of_lt
      (Lp.eLpNorm_le_of_ae_tendsto hbound
        (fun h => (measurable_fderiv_apply_const ℝ (dirichletTangentialDifferenceIter h j u)
          (coordDir i)).aestronglyMeasurable) hgmeas hlim) (by simp)
  have htangent (j : ℕ) (hj : j ≤ N) :
      MemLp (dirichletCoordinateDerivative 1 j u) 2 μ ∧
        MemLp (dirD (dirichletCoordinateDerivative 1 j u) Complex.I) 2 μ := by
    refine ⟨?_, ?_⟩
    · cases j with
      | zero => exact hm.mono_measure (Measure.restrict_mono_set volume hWU)
      | succ j =>
        simpa only [coordDir, Matrix.cons_val_zero, dirichletCoordinateDerivative_succ_right] using
          hgrad_lim j (by omega) 0
    · have hdy : MemLp (dirichletCoordinateDerivative 1 j (dirD u Complex.I)) 2 μ := by
        simpa only [coordDir, Matrix.cons_val_one, Matrix.cons_val_zero] using hgrad_lim j hj 1
      refine hdy.ae_eq ?_
      filter_upwards [ae_restrict_mem hW.measurableSet] with z hzW
      exact dirichletCoordinateDerivative_dirD_comm_eqOn (isOpen_smoothDirichletHalfBox A b)
        hs 1 Complex.I j (hWU hzW)
  have hsW := hs.mono hWU
  have hstrongW (z : ℂ) (hz' : z ∈ W) : dirichletFlattenedDivergence f u z = -G z :=
    hstrong z (hWU hz')
  have hcurv_cd : ContDiff ℝ (⊤ : ℕ∞) (dirichletGraphCurvature f) :=
    Complex.ofRealCLM.contDiff.comp
      (((contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hf).2).2).comp Complex.reCLM.contDiff)
  have hinv_cd : ContDiff ℝ (⊤ : ℕ∞) (dirichletNormalCoefficientInverse f) :=
    Complex.ofRealCLM.contDiff.comp
      (((contDiff_const.add ((contDiff_infty_iff_deriv.mp hf).2.pow 2)).inv fun _ => by positivity).comp
        Complex.reCLM.contDiff)
  have : IsFiniteMeasure μ := ⟨by
    simpa only [μ, Measure.restrict_apply_univ] using
      (dirichlet_halfBox_isBounded (a := ρ) (b := ρ)).measure_lt_top⟩
  have hnormal : ∀ q p : ℕ, p + q ≤ N → MemLp (dirichletMixedDerivative p q u) 2 μ := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro p hp
      cases q with
      | zero => exact (htangent p (by omega)).1
      | succ q =>
        cases q with
        | zero =>
          refine (htangent p (by omega)).2.ae_eq ?_
          filter_upwards [ae_restrict_mem hW.measurableSet] with z hz'
          exact (dirichletCoordinateDerivative_comm_eqOn hW hsW 1 Complex.I p 1 hz').symm
        | succ q =>
          have hlow₀ (j : ℕ) (hj : j + q ≤ N) := ih q (by omega) j hj
          have hlow₁ (j : ℕ) (hj : j + (q + 1) ≤ N) := ih (q + 1) (by omega) j hj
          have hexp_cd : ContDiffOn ℝ (⊤ : ℕ∞) (dirichletNormalRecoveryExpression f q u G) W :=
            (((contDiffOn_const.mul (dirichletCoordinateDerivative_contDiffOn hW hGs.contDiffOn Complex.I q)).add
              (hcurv_cd.contDiffOn.mul (dirichletCoordinateDerivative_contDiffOn hW hsW Complex.I (q + 1)))).add
              ((contDiff_const.mul (dirichletGraphSlope_contDiff hf)).contDiffOn.mul
                (dirichletMixedDerivative_contDiffOn hW hsW 1 (q + 1)))).sub
              (dirichletMixedDerivative_contDiffOn hW hsW 2 q)
          have hexp_mem (j : ℕ) (hj : j ≤ p) :
              MemLp (dirichletCoordinateDerivative 1 j (dirichletNormalRecoveryExpression f q u G)) 2 μ := by
            let t₀ : ℂ → ℂ := fun z => (-1 : ℂ) * dirichletCoordinateDerivative Complex.I q G z
            let t₁ : ℂ → ℂ := fun z => dirichletGraphCurvature f z *
              dirichletCoordinateDerivative Complex.I (q + 1) u z
            let t₂ : ℂ → ℂ := fun z => ((2 : ℂ) * dirichletGraphSlope f z) *
              dirichletMixedDerivative 1 (q + 1) u z
            let t₃ := dirichletMixedDerivative 2 q u
            have ht₀_cd : ContDiffOn ℝ (⊤ : ℕ∞) t₀ W :=
              contDiffOn_const.mul (dirichletCoordinateDerivative_contDiffOn hW hGs.contDiffOn Complex.I q)
            have ht₁_cd : ContDiffOn ℝ (⊤ : ℕ∞) t₁ W :=
              hcurv_cd.contDiffOn.mul (dirichletCoordinateDerivative_contDiffOn hW hsW Complex.I (q + 1))
            have ht₂_cd : ContDiffOn ℝ (⊤ : ℕ∞) t₂ W :=
              (contDiff_const.mul (dirichletGraphSlope_contDiff hf)).contDiffOn.mul
                (dirichletMixedDerivative_contDiffOn hW hsW 1 (q + 1))
            have ht₃_cd : ContDiffOn ℝ (⊤ : ℕ∞) t₃ W := dirichletMixedDerivative_contDiffOn hW hsW 2 q
            have hforc : MemLp (dirichletMixedDerivative j q G) 2 μ := by
              have hcd := dirichletCoordinateDerivative_contDiff
                (dirichletCoordinateDerivative_contDiff hGs Complex.I q) 1 j
              obtain ⟨M, hM⟩ := (isCompact_smoothDirichletClosedHalfBox ρ ρ).exists_bound_of_continuousOn
                hcd.continuous.continuousOn
              exact MemLp.of_bound hcd.continuous.aestronglyMeasurable M
                ((ae_restrict_mem hW.measurableSet).mono fun z hz' => hM z ⟨hz'.1.le, hz'.2.1.le, hz'.2.2.le⟩)
            have hm₀ : MemLp (dirichletCoordinateDerivative 1 j t₀) 2 μ := by
              refine (hforc.const_mul (-1 : ℂ)).ae_eq ?_
              filter_upwards [ae_restrict_mem hW.measurableSet] with z hz'
              exact (dirichletCoordinateDerivative_const_mul_eqOn hW
                (dirichletCoordinateDerivative_contDiffOn hW hGs.contDiffOn Complex.I q) (-1) 1 j hz').symm
            have hm₁ : MemLp (dirichletCoordinateDerivative 1 j t₁) 2 μ :=
              dirichletBootstrap_tangential_mul_memLp hcurv_cd
                (dirichletCoordinateDerivative_contDiffOn hW hsW Complex.I (q + 1)) j
                fun l _ => hlow₁ l (by omega)
            have hm₂ : MemLp (dirichletCoordinateDerivative 1 j t₂) 2 μ :=
              dirichletBootstrap_tangential_mul_memLp (contDiff_const.mul (dirichletGraphSlope_contDiff hf))
                (dirichletMixedDerivative_contDiffOn hW hsW 1 (q + 1)) j fun l _ => by
                  rw [dirichletMixedDerivative, dirichletCoordinateDerivative_iterate 1 l 1]
                  exact hlow₁ (l + 1) (by omega)
            have hm₃ : MemLp (dirichletCoordinateDerivative 1 j t₃) 2 μ := by
              rw [show t₃ = dirichletMixedDerivative 2 q u from rfl,
                dirichletMixedDerivative, dirichletCoordinateDerivative_iterate 1 j 2]
              exact hlow₀ (j + 2) (by omega)
            have hadd_lp {v₁ v₂ : ℂ → ℂ} (hv₁ : ContDiffOn ℝ (⊤ : ℕ∞) v₁ W) (hv₂ : ContDiffOn ℝ (⊤ : ℕ∞) v₂ W)
                (hm_1 : MemLp (dirichletCoordinateDerivative 1 j v₁) 2 μ)
                (hm_2 : MemLp (dirichletCoordinateDerivative 1 j v₂) 2 μ) :
                MemLp (dirichletCoordinateDerivative 1 j (fun z => v₁ z + v₂ z)) 2 μ :=
              (hm_1.add hm_2).ae_eq ((ae_restrict_mem hW.measurableSet).mono fun z hz' =>
                (dirichletCoordinateDerivative_add_eqOn hW hv₁ hv₂ 1 j hz').symm)
            exact ((hadd_lp (ht₀_cd.add ht₁_cd) ht₂_cd (hadd_lp ht₀_cd ht₁_cd hm₀ hm₁) hm₂).sub hm₃).ae_eq
              ((ae_restrict_mem hW.measurableSet).mono fun z hz' =>
                (dirichletCoordinateDerivative_sub_eqOn hW ((ht₀_cd.add ht₁_cd).add ht₂_cd) ht₃_cd 1 j hz').symm)
          have hm_prod := dirichletBootstrap_tangential_mul_memLp hinv_cd hexp_cd p hexp_mem
          have hrec := dirichletCoordinateDerivative_eqOn hW
            (dirichlet_normal_higher_derivative_recovery hW hf hsW hGs.contDiffOn hstrongW q) 1 p
          refine hm_prod.ae_eq ?_
          filter_upwards [ae_restrict_mem hW.measurableSet] with z hz'
          exact (hrec hz').symm
  exact ⟨ρ, hρ, hρA, hρb, fun p q hpq => hnormal q p hpq⟩

end PolyaNeumann
end
