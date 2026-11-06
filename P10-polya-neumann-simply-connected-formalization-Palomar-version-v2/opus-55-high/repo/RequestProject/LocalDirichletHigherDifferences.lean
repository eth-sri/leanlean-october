module

public import RequestProject.LocalDirichletFlattenedEquation
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Data.Nat.Choose.Sum
public import RequestProject.SmoothCompactExtension

/-!
# Genuine iterated tangential differences in the flattened Dirichlet problem

The quotients here are the actual translated quotients of the original
function.  In particular, their continuity and bottom-edge zero values come
from the original function, without a boundary trace assertion about a
derivative.  The coefficient commutators are exact discrete product formulas.
Bounds for smooth coefficients use their genuine directional derivatives on
a larger compact rectangle and an explicit translation margin.

This is a foundation for the higher difference energy induction; it does not
assert that the complete boundary regularity bootstrap has been performed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric MeasureTheory Filter
open scoped Topology

/-- Actual horizontal translation, with the physical real increment. -/
def dirichletTangentialTranslate (h : ℝ) (u : ℂ → ℂ) (z : ℂ) : ℂ :=
  u (z + (h : ℂ))

/-- Iteration of the genuine quotient already used by the first energy
estimate.  The zeroth quotient is the original function, including its
constant mode and its actual boundary values. -/
def dirichletTangentialDifferenceIter (h : ℝ) : ℕ → (ℂ → ℂ) → (ℂ → ℂ)
  | 0, u => u
  | k + 1, u => dirichletTangentialDifference h
      (dirichletTangentialDifferenceIter h k u)

variable (h : ℝ) (k : ℕ) (a : ℂ) (u : ℂ → ℂ) (c : ℂ → ℂ)

@[simp] theorem dirichletTangentialDifferenceIter_zero :
    dirichletTangentialDifferenceIter h 0 u = u := rfl

@[simp] theorem dirichletTangentialDifferenceIter_succ :
    dirichletTangentialDifferenceIter h (k + 1) u =
      dirichletTangentialDifference h (dirichletTangentialDifferenceIter h k u) := rfl

theorem dirichletTangentialDifference_add (u v : ℂ → ℂ) :
    dirichletTangentialDifference h (fun z => u z + v z) =
      fun z => dirichletTangentialDifference h u z +
        dirichletTangentialDifference h v z := by
  funext z
  simp only [dirichletTangentialDifference]
  ring

theorem dirichletTangentialDifference_sub (u v : ℂ → ℂ) :
    dirichletTangentialDifference h (fun z => u z - v z) =
      fun z => dirichletTangentialDifference h u z -
        dirichletTangentialDifference h v z := by
  funext z
  simp only [dirichletTangentialDifference]
  ring

theorem dirichletTangentialDifference_const_mul :
    dirichletTangentialDifference h (fun z => a * u z) =
      fun z => a * dirichletTangentialDifference h u z := by
  funext z
  simp only [dirichletTangentialDifference]
  ring

/-- The discrete product rule, with the shift on the first factor.  It
remains true for zero step because the actual quotient is then zero. -/
theorem dirichletTangentialDifference_mul (h : ℝ) (a v : ℂ → ℂ) :
    dirichletTangentialDifference h (fun z => a z * v z) =
      fun z => dirichletTangentialTranslate h a z *
          dirichletTangentialDifference h v z +
        dirichletTangentialDifference h a z * v z := by
  funext z
  simp only [dirichletTangentialDifference, dirichletTangentialTranslate]
  ring

theorem dirichletTangentialDifference_translate (h t : ℝ) (u : ℂ → ℂ) :
    dirichletTangentialDifference h (dirichletTangentialTranslate t u) =
      dirichletTangentialTranslate t (dirichletTangentialDifference h u) := by
  funext z
  simp only [dirichletTangentialDifference, dirichletTangentialTranslate]
  ring

theorem dirichletTangentialDifferenceIter_add (u v : ℂ → ℂ) :
    dirichletTangentialDifferenceIter h k (fun z => u z + v z) =
      fun z => dirichletTangentialDifferenceIter h k u z +
        dirichletTangentialDifferenceIter h k v z := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [ih, dirichletTangentialDifference_add]

theorem dirichletTangentialDifferenceIter_sub (u v : ℂ → ℂ) :
    dirichletTangentialDifferenceIter h k (fun z => u z - v z) =
      fun z => dirichletTangentialDifferenceIter h k u z -
        dirichletTangentialDifferenceIter h k v z := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [ih, dirichletTangentialDifference_sub]

theorem dirichletTangentialDifferenceIter_const_mul
    :
    dirichletTangentialDifferenceIter h k (fun z => a * u z) =
      fun z => a * dirichletTangentialDifferenceIter h k u z := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [ih, dirichletTangentialDifference_const_mul]

/-- The actual commutator after k quotients.  This is constructed from
the two actual products, rather than an assumed differentiated equation. -/
def dirichletHigherCoefficientCommutator (h : ℝ) (k : ℕ)
    (a v : ℂ → ℂ) (z : ℂ) : ℂ :=
  dirichletTangentialDifferenceIter h k (fun w => a w * v w) z -
    dirichletTangentialTranslate ((k : ℝ) * h) a z *
      dirichletTangentialDifferenceIter h k v z

@[simp] theorem dirichletHigherCoefficientCommutator_zero
    (h : ℝ) (a v : ℂ → ℂ) (z : ℂ) :
    dirichletHigherCoefficientCommutator h 0 a v z = 0 := by
  simp [dirichletHigherCoefficientCommutator, dirichletTangentialTranslate]

theorem dirichletTangentialDifferenceIter_mul_eq_shift_add_commutator
    (a v : ℂ → ℂ) (z : ℂ) :
    dirichletTangentialDifferenceIter h k (fun w => a w * v w) z =
      dirichletTangentialTranslate (k * h) a z *
        dirichletTangentialDifferenceIter h k v z +
      dirichletHigherCoefficientCommutator h k a v z := by
  unfold dirichletHigherCoefficientCommutator
  ring

theorem dirichletTangentialDifferenceIter_contDiff {u : ℂ → ℂ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (h : ℝ) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (dirichletTangentialDifferenceIter h k u) := by
  induction k with
  | zero => assumption
  | succ k ih =>
      exact ((ih.comp (contDiff_id.add contDiff_const)).sub ih).div_const h

/-- No derivative is assumed continuous on the bottom: each finite
quotient inherits the original function's continuity by translation. -/
theorem dirichletTangentialDifferenceIter_continuousOn
    {A a b h : ℝ} (k : ℕ) (hmargin : a + k * |h| ≤ A)
    {u : ℂ → ℂ} (hu : ContinuousOn u (smoothDirichletClosedHalfBox A b)) :
    ContinuousOn (dirichletTangentialDifferenceIter h k u)
      (smoothDirichletClosedHalfBox a b) := by
  induction k generalizing a with
  | zero =>
      exact hu.mono (fun z hz => ⟨hz.1.trans (by simp_all), hz.2⟩)
  | succ k ih =>
      exact dirichletTangentialDifference_continuousOn (le_refl (a + |h|))
        (ih (by
        grind))

theorem dirichletTangentialDifferenceIter_contDiffOn
    {A a b h : ℝ} (k : ℕ) (hmargin : a + k * |h| ≤ A)
    {u : ℂ → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (dirichletTangentialDifferenceIter h k u)
      (smoothDirichletHalfBox a b) := by
  induction k generalizing a with
  | zero =>
      exact hu.mono (fun z hz => ⟨hz.1.trans_le (by simp_all), hz.2⟩)
  | succ k ih =>
      exact dirichletTangentialDifference_contDiffOn (le_refl (a + |h|))
        (ih (by
        grind))

theorem dirichletTangentialDifferenceIter_zero_bottom
    {A a h : ℝ} (k : ℕ) (hmargin : a + k * |h| ≤ A)
    {u : ℂ → ℂ} (hu : ∀ x : ℝ, |x| < A → u x = 0)
    {x : ℝ} (hx : |x| < a) :
    dirichletTangentialDifferenceIter h k u x = 0 := by
  induction k generalizing a x with
  | zero =>
      exact hu x (hx.trans_le (by simp_all))
  | succ k ih =>
      exact dirichletTangentialDifference_zero_bottom (le_refl (a + |h|))
        (fun y hy => ih (by
        grind) hy) hx

/-- Actual first derivatives commute with every finite quotient in the
interior.  This statement uses only smoothness on the larger open box. -/
theorem dirichletTangentialDifferenceIter_dirD
    {A a b h : ℝ} (k : ℕ) (hmargin : a + k * |h| ≤ A)
    {u : ℂ → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b))
    {z : ℂ} (hz : z ∈ smoothDirichletHalfBox a b) (w : ℂ) :
    dirD (dirichletTangentialDifferenceIter h k u) w z =
      dirichletTangentialDifferenceIter h k (dirD u w) z := by
  induction k generalizing a z with
  | zero => rfl
  | succ k ih =>
      have hm : (a + |h|) + k * |h| ≤ A := by
        grind
      have hs := dirichletTangentialDifferenceIter_contDiffOn k hm hu
      have hz' : z ∈ smoothDirichletHalfBox (a + |h|) b :=
        ⟨hz.1.trans_le (le_add_of_nonneg_right (abs_nonneg h)), hz.2⟩
      have hzh : z + h ∈ smoothDirichletHalfBox (a + |h|) b := by
        have hx := (abs_add_le z.re h).trans_lt
          (add_lt_add_of_lt_of_le hz.1 le_rfl)
        simp_all [smoothDirichletHalfBox]
      rw [dirichletTangentialDifferenceIter_succ,
        dirichletTangentialDifference_dirD
          ((hs.contDiffAt ((isOpen_smoothDirichletHalfBox _ _).mem_nhds hz')).differentiableAt
            (by simp))
          ((hs.contDiffAt ((isOpen_smoothDirichletHalfBox _ _).mem_nhds hzh)).differentiableAt
            (by simp)) w]
      change (dirD (dirichletTangentialDifferenceIter h k u) w (z + h) -
          dirD (dirichletTangentialDifferenceIter h k u) w z) / h = _
      rw [ih hm hzh, ih hm hz']
      rfl

/-- Each fixed finite quotient is truly in L².  The norm is allowed to
depend on that nonzero fixed step; the later energy estimate removes that
dependence. -/
theorem dirichletTangentialDifferenceIter_memLp
    {A a b h : ℝ} (k : ℕ) (hmargin : a + k * |h| ≤ A)
    {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b))) :
    MemLp (dirichletTangentialDifferenceIter h k u) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  induction k generalizing a with
  | zero =>
      apply hu.mono_measure
      exact Measure.restrict_mono_set volume
        (fun z hz => ⟨hz.1.trans_le (by simp_all), hz.2⟩)
  | succ k ih =>
      exact dirichletTangentialDifference_memLp (le_refl (a + |h|)) (ih (by
        grind))

theorem dirichletTangentialDifferenceIter_gradient_memLp
    {A a b h : ℝ} (k : ℕ) (hmargin : a + k * |h| ≤ A)
    {u : ℂ → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b))
    {w : ℂ} (hg : MemLp (dirD u w) 2
      (volume.restrict (smoothDirichletHalfBox A b))) :
    MemLp (dirD (dirichletTangentialDifferenceIter h k u) w) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  apply (dirichletTangentialDifferenceIter_memLp k hmargin hg).ae_eq
  filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
    with z hz
  exact (dirichletTangentialDifferenceIter_dirD k hmargin hu hz w).symm

theorem dirichletTangentialTranslate_succ (j : ℕ) (a : ℂ → ℂ) :
    dirichletTangentialTranslate h (dirichletTangentialTranslate (j * h) a) =
      dirichletTangentialTranslate ((j + 1 : ℕ) * h) a := by
  funext z
  unfold dirichletTangentialTranslate
  push_cast
  ring

theorem dirichletTangentialDifference_sum {ι : Type*}
    (s : Finset ι) (h : ℝ) (v : ι → ℂ → ℂ) :
    dirichletTangentialDifference h (fun z => ∑ j ∈ s, v j z) =
      fun z => ∑ j ∈ s, dirichletTangentialDifference h (v j) z := by
  funext z
  simp [dirichletTangentialDifference, ← Finset.sum_sub_distrib, Finset.sum_div]

/-- Full discrete Leibniz formula.  The jth difference of v is at the
original point; only the smooth coefficient is shifted by j h. -/
theorem dirichletTangentialDifferenceIter_mul
    (a v : ℂ → ℂ) (z : ℂ) :
    dirichletTangentialDifferenceIter h k (fun w => a w * v w) z =
      ∑ j ∈ Finset.range (k + 1), k.choose j *
        (dirichletTangentialTranslate (j * h)
            (dirichletTangentialDifferenceIter h (k - j) a) z *
          dirichletTangentialDifferenceIter h j v z) := by
  induction k generalizing z with
  | zero => simp [dirichletTangentialTranslate]
  | succ k ih =>
      let K : ℕ → ℕ → ℂ → ℂ := fun j l w =>
        dirichletTangentialTranslate (j * h)
          (dirichletTangentialDifferenceIter h l a) w *
          dirichletTangentialDifferenceIter h j v w
      have heq : dirichletTangentialDifferenceIter h k (fun w => a w * v w) =
          fun w => ∑ j ∈ Finset.range (k + 1), k.choose j * K j (k - j) w :=
        funext ih
      have hK (j : ℕ) (hj : j ∈ Finset.range (k + 1)) :
          dirichletTangentialDifference h (K j (k - j)) z =
            K j (k + 1 - j) z + K (j + 1) (k - j) z := by
        have hjk  := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        have hnat : k - j + 1 = k + 1 - j := by omega
        have hd : dirichletTangentialDifference h
            (dirichletTangentialDifferenceIter h (k - j) a) =
            dirichletTangentialDifferenceIter h (k + 1 - j) a := by
          rw [← dirichletTangentialDifferenceIter_succ, hnat]
        rw [dirichletTangentialDifference_mul,
          dirichletTangentialDifference_translate,
          dirichletTangentialTranslate_succ, hd]
        exact add_comm _ _
      calc
        _ = ∑ j ∈ Finset.range (k + 1), k.choose j *
            dirichletTangentialDifference h (K j (k - j)) z := by
          simp [heq, dirichletTangentialDifference_sum, dirichletTangentialDifference_const_mul]
        _ = ∑ j ∈ Finset.range (k + 1), k.choose j *
            (K j (k + 1 - j) z + K (j + 1) (k - j) z) := Finset.sum_congr rfl (fun j hj => congrArg (fun t => (k.choose j : ℂ) * t)
            (hK j hj))
        _ = ∑ j ∈ Finset.range (k + 2), (k + 1).choose j *
            K j (k + 1 - j) z := by
          simp [Finset.sum_choose_succ_mul (fun j l => K j l z) k, mul_add, Finset.sum_add_distrib]
        _ = _ := rfl

/-- The full commutator contains only gradient differences strictly
below k; no translated gradient estimate is hidden in its formula. -/
theorem dirichletHigherCoefficientCommutator_eq_sum
    (a v : ℂ → ℂ) (z : ℂ) :
    dirichletHigherCoefficientCommutator h k a v z =
      ∑ j ∈ Finset.range k, k.choose j *
        (dirichletTangentialTranslate (j * h)
            (dirichletTangentialDifferenceIter h (k - j) a) z *
          dirichletTangentialDifferenceIter h j v z) := by
  unfold dirichletHigherCoefficientCommutator
  simp [dirichletTangentialDifferenceIter_mul, Finset.sum_range_succ]

theorem norm_dirichletHigherCoefficientCommutator_le
    (a v : ℂ → ℂ) (z : ℂ) :
    ‖dirichletHigherCoefficientCommutator h k a v z‖ ≤
      ∑ j ∈ Finset.range k, k.choose j *
        (‖dirichletTangentialDifferenceIter h (k - j) a
              (z + (j * h : ℝ))‖ *
          ‖dirichletTangentialDifferenceIter h j v z‖) := by
  rw [dirichletHigherCoefficientCommutator_eq_sum]
  calc
    _ ≤ ∑ j ∈ Finset.range k, ‖k.choose j *
        (dirichletTangentialTranslate (j * h)
          (dirichletTangentialDifferenceIter h (k - j) a) z *
            dirichletTangentialDifferenceIter h j v z)‖ := norm_sum_le _ _
    _ = _ := by
      simp [dirichletTangentialTranslate]

/-- The actual kth coefficient error in both rows of the graph matrix. -/
def dirichletHigherCoefficientDifferenceFlux (f : ℝ → ℝ) (h : ℝ) (k : ℕ)
    (u : ℂ → ℂ) (i : Fin 2) (z : ℂ) : ℂ :=
  ![-dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f)
      (dirD u Complex.I) z,
    -dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f)
      (dirD u 1) z +
      dirichletHigherCoefficientCommutator h k
        (fun w => 1 + dirichletGraphSlope f w ^ 2) (dirD u Complex.I) z] i

/-- The exact kth flux decomposition on the interior smaller half box.
The coefficients in the principal part are evaluated at z+k h.  The
commutator uses only lower actual quotients of coefficient and gradient. -/
theorem dirichletTangentialDifferenceIter_flux_split
    {A a b h : ℝ} (k : ℕ) (hmargin : a + k * |h| ≤ A)
    (f : ℝ → ℝ) {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b))
    {z : ℂ} (hz : z ∈ smoothDirichletHalfBox a b) (i : Fin 2) :
    dirichletTangentialDifferenceIter h k (dirichletFlattenedFlux f u i) z =
      dirichletShiftedFlux f (k * h)
        (dirichletTangentialDifferenceIter h k u) i z +
      dirichletHigherCoefficientDifferenceFlux f h k u i z := by
  have hx := dirichletTangentialDifferenceIter_dirD k hmargin hu hz 1
  have hy := dirichletTangentialDifferenceIter_dirD k hmargin hu hz Complex.I
  fin_cases i
  · change dirichletTangentialDifferenceIter h k
        (fun w => dirD u 1 w - dirichletGraphSlope f w * dirD u Complex.I w) z =
      (dirD (dirichletTangentialDifferenceIter h k u) 1 z -
        dirichletGraphSlope f (z + (k * h : ℝ)) *
          dirD (dirichletTangentialDifferenceIter h k u) Complex.I z) +
      -dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f)
        (dirD u Complex.I) z
    simp only [dirichletTangentialDifferenceIter_sub]
    rw [dirichletTangentialDifferenceIter_mul_eq_shift_add_commutator]
    rw [hx, hy]
    simp only [dirichletTangentialTranslate]
    ring
  · have hneg (w : ℂ) : -dirichletGraphSlope f w * dirD u 1 w =
        -1 * (dirichletGraphSlope f w * dirD u 1 w) := by ring
    change dirichletTangentialDifferenceIter h k
        (fun w => -dirichletGraphSlope f w * dirD u 1 w +
          (1 + dirichletGraphSlope f w ^ 2) * dirD u Complex.I w) z =
      (-dirichletGraphSlope f (z + (k * h : ℝ)) *
          dirD (dirichletTangentialDifferenceIter h k u) 1 z +
        (1 + dirichletGraphSlope f (z + (k * h : ℝ)) ^ 2) *
          dirD (dirichletTangentialDifferenceIter h k u) Complex.I z) +
      (-dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f)
          (dirD u 1) z +
        dirichletHigherCoefficientCommutator h k
          (fun w => 1 + dirichletGraphSlope f w ^ 2) (dirD u Complex.I) z)
    simp only [dirichletTangentialDifferenceIter_add]
    simp_rw [hneg]
    rw [dirichletTangentialDifferenceIter_const_mul]
    change -1 * dirichletTangentialDifferenceIter h k
        (fun w => dirichletGraphSlope f w * dirD u 1 w) z +
      dirichletTangentialDifferenceIter h k
        (fun w => (1 + dirichletGraphSlope f w ^ 2) * dirD u Complex.I w) z = _
    rw [dirichletTangentialDifferenceIter_mul_eq_shift_add_commutator,
      dirichletTangentialDifferenceIter_mul_eq_shift_add_commutator]
    rw [hx, hy]
    simp only [dirichletTangentialTranslate]
    ring

/-- The genuine iterated horizontal derivative, used only for smooth
coefficients and forcing in the uniform quotient bounds below. -/
def dirichletTangentialDerivative : ℕ → (ℂ → ℂ) → (ℂ → ℂ)
  | 0, c => c
  | k + 1, c => dirD (dirichletTangentialDerivative k c) 1

@[simp] theorem dirichletTangentialDerivative_zero :
    dirichletTangentialDerivative 0 c = c := rfl

@[simp] theorem dirichletTangentialDerivative_succ :
    dirichletTangentialDerivative (k + 1) c =
      dirD (dirichletTangentialDerivative k c) 1 := rfl

theorem dirichlet_dirD_contDiff {c : ℂ → ℂ}
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (w : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (dirD c w) :=
  (hc.fderiv_right  le_rfl).clm_apply contDiff_const

theorem dirichletTangentialDerivative_contDiff {c : ℂ → ℂ}
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (dirichletTangentialDerivative k c) := by
  induction k with
  | zero => assumption
  | succ k ih => exact dirichlet_dirD_contDiff ih 1

theorem dirichletTangentialDerivative_succ_right :
    dirichletTangentialDerivative k (dirD c 1) =
      dirichletTangentialDerivative (k + 1) c := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp_all

theorem dirichletTangentialDifferenceIter_dirD_global
    {c : ℂ → ℂ} (hc : ContDiff ℝ (⊤ : ℕ∞) c) (h : ℝ) (k : ℕ) (w : ℂ) :
    dirD (dirichletTangentialDifferenceIter h k c) w =
      dirichletTangentialDifferenceIter h k (dirD c w) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      funext z
      have hs := dirichletTangentialDifferenceIter_contDiff hc h k
      simp [dirichletTangentialDifference_dirD           (hs.differentiable (by simp) z)           (hs.differentiable (by simp) (z + h)) w, ih]

/-- The closed half rectangle is actually compact, also when its side
lengths make it empty. -/
theorem isCompact_smoothDirichletClosedHalfBox (A b : ℝ) :
    IsCompact (smoothDirichletClosedHalfBox A b) := Metric.isCompact_of_isClosed_isBounded ((isClosed_le Complex.continuous_re.abs continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const))) (by
    apply (isBounded_closedBall  ).subset
    intro z hz
    rw [mem_closedBall, dist_zero_right]
    calc
      ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ A + b := add_le_add hz.1 (by rw [abs_of_nonneg hz.2.1]; exact hz.2.2))

/-- One true quotient is bounded by its horizontal derivative on the
larger closed box.  Only the smooth coefficient has boundary derivatives. -/
theorem dirichletTangentialDifference_norm_le
    {A a b h M : ℝ} (hh : 0 < h) (hmargin : a + h ≤ A)
    {c : ℂ → ℂ} (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hM : ∀ z ∈ smoothDirichletClosedHalfBox A b, ‖dirD c 1 z‖ ≤ M)
    {z : ℂ} (hz : z ∈ smoothDirichletClosedHalfBox a b) :
    ‖dirichletTangentialDifference h c z‖ ≤ M := by
  let v : ℝ → ℂ := fun t => c (z + t)
  let dv  := fun t => dirD c 1 (z + t)
  have hmap (t : ℝ) (ht : t ∈ Icc 0 h) :
      z + t ∈ smoothDirichletClosedHalfBox A b := by
    have hx : |z.re + t| ≤ A := by
      calc
        |z.re + t| ≤ |z.re| + |t| := abs_add_le _ _
        _ ≤ a + h := add_le_add hz.1 (by grind)
        _ ≤ A := hmargin
    simp_all [smoothDirichletClosedHalfBox]
  have hd (t : ℝ) : HasDerivAt v (dv t) t := (hc.differentiable (by simp) (z + t)).hasFDerivAt.comp_hasDerivAt t ((Complex.ofRealCLM.hasDerivAt).const_add z)
  have hp := (convex_Icc 0 h).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hd t).hasDerivWithinAt) (fun t ht => hM _ (hmap t ht))
    (⟨le_rfl, hh.le⟩)
    (⟨hh.le, le_rfl⟩)
  rw [dirichletTangentialDifference, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hh]
  exact (div_le_iff₀ hh).mpr (by
    simp_all [v, abs_of_pos hh])

/-- At every fixed order the quotient bound depends on the actual kth
horizontal derivative, and not on h.  The margin counts every translation. -/
theorem dirichletTangentialDifferenceIter_norm_le
    {A a b h M : ℝ} (k : ℕ) (hh : 0 < h)
    (hmargin : a + k * h ≤ A) {c : ℂ → ℂ}
    (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hM : ∀ z ∈ smoothDirichletClosedHalfBox A b,
      ‖dirichletTangentialDerivative k c z‖ ≤ M)
    {z : ℂ} (hz : z ∈ smoothDirichletClosedHalfBox a b) :
    ‖dirichletTangentialDifferenceIter h k c z‖ ≤ M := by
  induction k generalizing a c z with
  | zero =>
      exact hM z ⟨hz.1.trans (by nlinarith), hz.2⟩
  | succ k ih =>
      apply dirichletTangentialDifference_norm_le hh (le_refl (a + h))
        (dirichletTangentialDifferenceIter_contDiff hc h k) _ hz
      intro w hw
      rw [dirichletTangentialDifferenceIter_dirD_global hc]
      apply ih (by
        grind) (dirichlet_dirD_contDiff hc 1) _ hw
      simp_all [dirichletTangentialDerivative_succ_right]

/-- Smooth coefficients or a genuine smooth forcing have uniform kth
quotient bounds on every fixed smaller half box with the stated margin. -/
theorem exists_dirichletTangentialDifferenceIter_bound
    {c : ℂ → ℂ} (hc : ContDiff ℝ (⊤ : ℕ∞) c) (A b : ℝ) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (a h : ℝ), 0 < h → a + k * h ≤ A →
      ∀ z ∈ smoothDirichletClosedHalfBox a b,
        ‖dirichletTangentialDifferenceIter h k c z‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_smoothDirichletClosedHalfBox A b).exists_bound_of_continuousOn
    (dirichletTangentialDerivative_contDiff hc k).continuous.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun a h hh hmargin z hz => ?_⟩
  apply dirichletTangentialDifferenceIter_norm_le k hh hmargin hc _ hz
  simp_all

/-- A finite number of genuine derivative bounds can be made simultaneous.
No bound on a derivative of the Dirichlet solution is requested here. -/
theorem exists_dirichletTangentialDerivative_upto_bound
    {c : ℂ → ℂ} (hc : ContDiff ℝ (⊤ : ℕ∞) c) (A b : ℝ) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ l : ℕ, l ≤ k →
      ∀ z ∈ smoothDirichletClosedHalfBox A b,
        ‖dirichletTangentialDerivative l c z‖ ≤ M := by
  induction k with
  | zero =>
      obtain ⟨M, hM⟩ := (isCompact_smoothDirichletClosedHalfBox A b).exists_bound_of_continuousOn
        hc.continuous.continuousOn
      refine ⟨max M 0, le_max_right _ _, fun l hl z hz => ?_⟩
      simp_all
  | succ k ih =>
      obtain ⟨M₀, hM₀, h₀⟩ := ih
      obtain ⟨M₁, h₁⟩ := (isCompact_smoothDirichletClosedHalfBox A b).exists_bound_of_continuousOn
        (dirichletTangentialDerivative_contDiff hc (k + 1)).continuous.continuousOn
      refine ⟨max M₀ M₁, hM₀.trans (le_max_left _ _), fun l hl z hz => ?_⟩
      grind

/-- Uniform pointwise coefficient commutator control by lower differences
of the actual input, all at the original point z. -/
theorem norm_dirichletHigherCoefficientCommutator_le_of_derivative_bounds
    {A a b h M : ℝ} (k : ℕ) (hh : 0 < h) (hmargin : a + k * h ≤ A)
    {c : ℂ → ℂ} (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hM : ∀ l : ℕ, l ≤ k → ∀ w ∈ smoothDirichletClosedHalfBox A b,
      ‖dirichletTangentialDerivative l c w‖ ≤ M)
    (v : ℂ → ℂ) {z : ℂ} (hz : z ∈ smoothDirichletClosedHalfBox a b) :
    ‖dirichletHigherCoefficientCommutator h k c v z‖ ≤
      M * ∑ j ∈ Finset.range k, k.choose j *
        ‖dirichletTangentialDifferenceIter h j v z‖ := by
  refine (norm_dirichletHigherCoefficientCommutator_le h k c v z).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hnat : ((k - j : ℕ) : ℝ) = k - j := Nat.cast_sub (Finset.mem_range.mp hj).le
  have hm : (a + j * h) + (k - j : ℕ) * h ≤ A := by
    nlinarith
  calc
    _ ≤ k.choose j * (M * ‖dirichletTangentialDifferenceIter h j v z‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (dirichletTangentialDifferenceIter_norm_le (k - j) hh hm hc
    (hM (k - j) (Nat.sub_le _ _)) (by
    have hx := (abs_add_le z.re (j * h)).trans
      (add_le_add hz.1 (le_of_eq (abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hh.le))))
    simp_all [smoothDirichletClosedHalfBox])) (norm_nonneg _)) (Nat.cast_nonneg _)
    _ = _ := by ring

/-- The two genuine graph coefficients admit the simultaneous commutator
bound needed by the localized higher energy induction. -/
theorem exists_dirichletGraphHigherCommutator_bound {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (A b : ℝ) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (a h : ℝ), 0 < h → a + k * h ≤ A →
      ∀ (v : ℂ → ℂ) (z : ℂ), z ∈ smoothDirichletClosedHalfBox a b →
        (‖dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f) v z‖ ≤
          M * ∑ j ∈ Finset.range k, k.choose j *
            ‖dirichletTangentialDifferenceIter h j v z‖) ∧
        (‖dirichletHigherCoefficientCommutator h k
            (fun w => 1 + dirichletGraphSlope f w ^ 2) v z‖ ≤
          M * ∑ j ∈ Finset.range k, k.choose j *
            ‖dirichletTangentialDifferenceIter h j v z‖) := by
  have hd := dirichletGraphSlope_contDiff hf
  obtain ⟨M₀, hM₀, h₀⟩ := exists_dirichletTangentialDerivative_upto_bound hd A b k
  obtain ⟨M₁, _, h₁⟩ := exists_dirichletTangentialDerivative_upto_bound
    (contDiff_const.add (hd.pow 2)) A b k
  refine ⟨max M₀ M₁, hM₀.trans (le_max_left _ _), fun a h hh hmargin v z hz => ?_⟩
  constructor
  · apply norm_dirichletHigherCoefficientCommutator_le_of_derivative_bounds
      k hh hmargin hd _ v hz
    simp_all
  · apply norm_dirichletHigherCoefficientCommutator_le_of_derivative_bounds
      k hh hmargin (contDiff_const.add (hd.pow 2)) _ v hz
    continuity

/-- Centered higher mean-value bound.  The kth quotient stays within
the same norm ball as the actual kth derivative on its entire stencil.
This is the genuine finite-difference ingredient in the later Fatou limit. -/
theorem dirichletTangentialDifferenceIter_centered_norm_le
    {c : ℂ → ℂ} (hc : ContDiff ℝ (⊤ : ℕ∞) c) (k : ℕ)
    {h M : ℝ} (hh : 0 < h) (z C : ℂ)
    (hM : ∀ t ∈ Icc 0 (k * h),
      ‖dirichletTangentialDerivative k c (z + t) - C‖ ≤ M) :
    ‖dirichletTangentialDifferenceIter h k c z - C‖ ≤ M := by
  induction k generalizing c z with
  | zero =>
      simp_all
  | succ k ih =>
      let v : ℝ → ℂ := fun t =>
        dirichletTangentialDifferenceIter h k c (z + t) - t * C
      let dv  := fun t =>
        dirichletTangentialDifferenceIter h k (dirD c 1) (z + t) - C
      have hd (t : ℝ) : HasDerivAt v (dv t) t := by
        have hg := (((dirichletTangentialDifferenceIter_contDiff hc h k).differentiable (by simp) (z + t)).hasFDerivAt.comp_hasDerivAt
          t ((Complex.ofRealCLM.hasDerivAt).const_add z)).sub ((Complex.ofRealCLM.hasDerivAt).mul_const C)
        have hgrad : fderiv ℝ (dirichletTangentialDifferenceIter h k c)
            (z + t) 1 =
              dirichletTangentialDifferenceIter h k (dirD c 1) (z + t) := congrFun (dirichletTangentialDifferenceIter_dirD_global hc h k 1)
          (z + t)
        continuity
      have hbound (t : ℝ) (ht : t ∈ Icc 0 h) : ‖dv t‖ ≤ M := by
        apply ih (dirichlet_dirD_contDiff hc 1) (z + t)
        intro s hs
        have heq : z + t + s = z + (t + s : ℝ) := by
          push_cast
          ring
        rw [dirichletTangentialDerivative_succ_right]
        grind
      have hp' : ‖(v h - v 0) / h‖ ≤ M := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
        apply (div_le_iff₀ hh).mpr
        simpa only [sub_zero, Real.norm_eq_abs, abs_of_pos hh] using ((convex_Icc 0 h).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun t _ => (hd t).hasDerivWithinAt) hbound
        (⟨le_rfl, hh.le⟩)
        (⟨hh.le, le_rfl⟩))
      have hhC : (h : ℂ) ≠ 0 := by continuity
      have heq : (v h - v 0) / h =
          dirichletTangentialDifferenceIter h (k + 1) c z - C := by
        simp only [v, Complex.ofReal_zero, dirichletTangentialDifferenceIter_succ, dirichletTangentialDifference]
        grind
      simp_all

/-- Positive-step higher quotients genuinely converge to the actual
iterated directional derivative at every smooth point. -/
theorem dirichletTangentialDifferenceIter_tendsto
    {c : ℂ → ℂ} (hc : ContDiff ℝ (⊤ : ℕ∞) c) (k : ℕ) (z : ℂ) :
    Tendsto (fun h  => dirichletTangentialDifferenceIter h k c z)
      (𝓝[Ioi 0] 0) (𝓝 (dirichletTangentialDerivative k c z)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp (dirichletTangentialDerivative_contDiff hc k).continuous.continuousAt (ε / 2) (by positivity)
  have hk : 0 < (k : ℝ) + 1 := by positivity
  filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds (div_pos hδ hk)).filter_mono nhdsWithin_le_nhds] with h hh hs
  have hb := dirichletTangentialDifferenceIter_centered_norm_le hc k hh z
    (dirichletTangentialDerivative k c z) (by
    intro t ht
    have hkh : (k + 1) * h < δ := by
      simpa only [mul_comm] using (lt_div_iff₀ hk).mp hs
    have htδ : t < δ := by grind
    exact (show ‖dirichletTangentialDerivative k c (z + t) -
        dirichletTangentialDerivative k c z‖ < ε / 2 by
      simpa only [dist_eq_norm] using hclose (by
      simp_all [abs_of_nonneg ht.1])).le)
  rw [dist_eq_norm]
  linarith

/-- Exact finite-stencil locality.  No value or derivative outside the
stencil can change an actual iterated quotient. -/
theorem dirichletTangentialDifferenceIter_eq_of_stencil
    (c d : ℂ → ℂ) (z : ℂ)
    (heq : ∀ j : ℕ, j ≤ k →
      c (z + (j * h : ℝ)) = d (z + (j * h : ℝ))) :
    dirichletTangentialDifferenceIter h k c z =
      dirichletTangentialDifferenceIter h k d z := by
  induction k generalizing z with
  | zero => simp_all
  | succ k ih =>
      have h0 : ∀ j : ℕ, j ≤ k →
          c (z + (j * h : ℝ)) =
            d (z + (j * h : ℝ)) :=
        fun j hj => heq j (hj.trans (Nat.le_succ _))
      have h1 : ∀ j : ℕ, j ≤ k →
          c (z + h + (j * h : ℝ)) =
            d (z + h + (j * h : ℝ)) := by
        intro j hj
        have harg : z + h + (j * h : ℝ) =
            z + ((j + 1 : ℕ) * h : ℝ) := by
          push_cast
          ring
        rw [harg]
        exact heq (j + 1) (Nat.succ_le_succ hj)
      change (dirichletTangentialDifferenceIter h k c (z + h) -
          dirichletTangentialDifferenceIter h k c z) / h =
        (dirichletTangentialDifferenceIter h k d (z + h) -
          dirichletTangentialDifferenceIter h k d z) / h
      simp_all

theorem dirichletTangentialDerivative_eventuallyEq {c d : ℂ → ℂ} {z : ℂ}
    (heq : c =ᶠ[𝓝 z] d) (k : ℕ) :
    dirichletTangentialDerivative k c =ᶠ[𝓝 z] dirichletTangentialDerivative k d := by
  induction k with
  | zero => assumption
  | succ k ih =>
      exact (ih.fderiv ).fun_comp (fun A  => A 1)

/-- The limit used by Fatou needs smoothness only in the actual open
interior.  A genuine local compact extension transfers its finite stencil
and its derivative germ; no boundary extension of a derivative is used. -/
theorem dirichletTangentialDifferenceIter_tendsto_of_contDiffOn
    {U : Set ℂ} (hU : IsOpen U) {c : ℂ → ℂ}
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) c U) (k : ℕ) {z : ℂ} (hz : z ∈ U) :
    Tendsto (fun h  => dirichletTangentialDifferenceIter h k c z)
      (𝓝[Ioi 0] 0) (𝓝 (dirichletTangentialDerivative k c z)) := by
  obtain ⟨d, hd, hdc⟩ := exists_smooth_compact_extension
    (isCompact_singleton ) hU (singleton_subset_iff.mpr hz) hc
  have heq  := hdc z (mem_singleton z)
  have hall : ∀ᶠ h : ℝ in 𝓝 0, ∀ j ∈ Finset.range (k + 1),
      d (z + (j * h : ℝ)) = c (z + (j * h : ℝ)) := by
    apply (Filter.eventually_all_finset _).mpr
    intro j _
    have ht : Tendsto (fun h  => z + (j * h : ℝ))
        (𝓝 0) (𝓝 z) := by
      have hstencil : Continuous (fun h  => z + (j * h : ℝ)) :=
        continuous_const.add
          (Complex.continuous_ofReal.comp
            (continuous_const.mul continuous_id))
      simpa only [mul_zero, Complex.ofReal_zero, add_zero] using hstencil.tendsto 0
    exact ht.eventually heq
  have hdiff : (fun h  => dirichletTangentialDifferenceIter h k d z) =ᶠ[𝓝 0]
      fun h => dirichletTangentialDifferenceIter h k c z := by
    filter_upwards [hall] with h hh
    apply dirichletTangentialDifferenceIter_eq_of_stencil h k d c z
    simp_all
  have hlim := (dirichletTangentialDifferenceIter_tendsto hd.1 k z).congr'
    (hdiff.filter_mono nhdsWithin_le_nhds)
  simp_all [(dirichletTangentialDerivative_eventuallyEq heq k).self_of_nhds]

end PolyaNeumann

end
