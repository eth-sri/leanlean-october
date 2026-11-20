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

open scoped ContDiff

namespace PolyaNeumann

open Set Metric MeasureTheory Filter
open scoped Topology

/-- Actual horizontal translation, with the physical real increment. -/
def dirichletTangentialTranslate (h : ℝ) (u : ℂ → ℂ) (z : ℂ) : ℂ :=
  u (z + (h : ℂ))

/-- Translation minus identity, divided by the step, is complex linear, including at step zero. -/
def tangentialQuotient (h : ℝ) : Module.End ℂ (ℂ → ℂ) where
  toFun := dirichletTangentialDifference h
  map_add' u v := by funext z; simp [dirichletTangentialDifference]; ring
  map_smul' c u := by funext z; simp [dirichletTangentialDifference]; ring

/-- The `k`-fold composite as an endomorphism of fields on the plane. -/
def dirichletTangentialDifferenceIter (h : ℝ) : ℕ → Module.End ℂ (ℂ → ℂ)
  | 0 => LinearMap.id
  | k + 1 => (tangentialQuotient h).comp (dirichletTangentialDifferenceIter h k)

section

variable (h : ℝ) (k : ℕ) (u : ℂ → ℂ)

@[simp] theorem dirichletTangentialDifferenceIter_zero :
    dirichletTangentialDifferenceIter h 0 u = u := rfl

@[simp] theorem dirichletTangentialDifferenceIter_succ :
    dirichletTangentialDifferenceIter h (k + 1) u =
      dirichletTangentialDifference h (dirichletTangentialDifferenceIter h k u) := rfl

end

section

variable (h : ℝ) (k : ℕ) (a v : ℂ → ℂ) (z : ℂ)

/-- The discrete product rule, with the shift on the first factor.  It
remains true for zero step because the actual quotient is then zero. -/
theorem dirichletTangentialDifference_mul :
    dirichletTangentialDifference h (fun z => a z * v z) =
      fun z => dirichletTangentialTranslate h a z *
          dirichletTangentialDifference h v z +
        dirichletTangentialDifference h a z * v z := by
  funext z
  simp [dirichletTangentialDifference, dirichletTangentialTranslate, div_eq_mul_inv]
  ring

theorem dirichletTangentialDifference_translate (t : ℝ) (u : ℂ → ℂ) :
    dirichletTangentialDifference h (dirichletTangentialTranslate t u) =
      dirichletTangentialTranslate t (dirichletTangentialDifference h u) := by
  funext z
  simp [dirichletTangentialDifference, dirichletTangentialTranslate] <;> ring

include a h k v z in
/-- The actual commutator after k quotients.  This is constructed from
the two actual products, rather than an assumed differentiated equation. -/
def dirichletHigherCoefficientCommutator : ℂ :=
  dirichletTangentialDifferenceIter h k (fun w => a w * v w) z -
    dirichletTangentialTranslate ((k : ℝ) * h) a z *
      dirichletTangentialDifferenceIter h k v z

theorem dirichletTangentialDifferenceIter_mul_eq_shift_add_commutator :
    dirichletTangentialDifferenceIter h k (a * v) z =
      dirichletTangentialTranslate ((k : ℝ) * h) a z *
        dirichletTangentialDifferenceIter h k v z +
      dirichletHigherCoefficientCommutator h k a v z := by
  unfold dirichletHigherCoefficientCommutator; change _ = _ + ((dirichletTangentialDifferenceIter h k) (a * v) z - _)
  ring

theorem dirichletTangentialDifferenceIter_contDiff {u : ℂ → ℂ}
    (hu : ContDiff ℝ ∞ u) (h : ℝ) (k : ℕ) :
    ContDiff ℝ ∞ (dirichletTangentialDifferenceIter h k u) := by
  induction k with
  | zero => exact hu
  | succ k ih =>
      exact ((ih.comp (contDiff_id.add contDiff_const)).sub ih).div_const (h : ℂ)

end

private lemma step_margin {a A h : ℝ} {k : ℕ} (hm : a + (↑(k+1) : ℝ) * |h| ≤ A) :
    (a + |h|) + k * |h| ≤ A := by push_cast at hm; linarith

/-- Transfer a local field property along an entire finite-difference stencil. -/
private lemma quotientIter_induction {h A : ℝ} {u : ℂ → ℂ} (P : ℝ → (ℂ → ℂ) → Prop)
    (mono : ∀ {a}, a ≤ A → P a u) (step : ∀ {a v}, P (a + |h|) v → P a (dirichletTangentialDifference h v))
    {a : ℝ} (k : ℕ) (hm : a + k * |h| ≤ A) : P a (dirichletTangentialDifferenceIter h k u) := by
  induction k generalizing a with
  | zero => exact mono (by simpa using hm)
  | succ k ih => exact step (ih (step_margin hm))

/-- No derivative is assumed continuous on the bottom: each finite
quotient inherits the original function's continuity by translation. -/
theorem dirichletTangentialDifferenceIter_continuousOn
    {A a b h : ℝ} (k : ℕ) (hmargin : a + (k : ℝ) * |h| ≤ A)
    {u : ℂ → ℂ} (hu : ContinuousOn u (smoothDirichletClosedHalfBox A b)) :
    ContinuousOn (dirichletTangentialDifferenceIter h k u)
      (smoothDirichletClosedHalfBox a b) := by
  exact quotientIter_induction (fun a v => ContinuousOn v (smoothDirichletClosedHalfBox a b))
    (fun h => hu.mono fun _ hz => ⟨hz.1.trans h, hz.2⟩)
    (dirichletTangentialDifference_continuousOn le_rfl) k hmargin

theorem dirichletTangentialDifferenceIter_contDiffOn
    {A a b h : ℝ} (k : ℕ) (hmargin : a + (k : ℝ) * |h| ≤ A)
    {u : ℂ → ℂ} (hu : ContDiffOn ℝ ∞ u (smoothDirichletHalfBox A b)) :
    ContDiffOn ℝ ∞ (dirichletTangentialDifferenceIter h k u)
      (smoothDirichletHalfBox a b) := by
  exact quotientIter_induction (fun a v => ContDiffOn ℝ ∞ v (smoothDirichletHalfBox a b))
    (fun h => hu.mono (halfBox_mono h le_rfl)) (dirichletTangentialDifference_contDiffOn le_rfl) k hmargin

theorem dirichletTangentialDifferenceIter_zero_bottom
    {A a h : ℝ} (k : ℕ) (hmargin : a + (k : ℝ) * |h| ≤ A)
    {u : ℂ → ℂ} (hu : ∀ x : ℝ, |x| < A → u (x : ℂ) = 0)
    {x : ℝ} (hx : |x| < a) :
    dirichletTangentialDifferenceIter h k u (x : ℂ) = 0 := by
  exact quotientIter_induction (fun a v => ∀ x : ℝ, |x| < a → v (x : ℂ) = 0)
    (fun h x hx => hu x (hx.trans_le h)) (fun hv _ => dirichletTangentialDifference_zero_bottom le_rfl hv) k hmargin x hx

/-- Actual first derivatives commute with every finite quotient in the
interior.  This statement uses only smoothness on the larger open box. -/
theorem dirichletTangentialDifferenceIter_dirD
    {A a b h : ℝ} (k : ℕ) (hmargin : a + (k : ℝ) * |h| ≤ A)
    {u : ℂ → ℂ} (hu : ContDiffOn ℝ ∞ u (smoothDirichletHalfBox A b))
    {z : ℂ} (hz : z ∈ smoothDirichletHalfBox a b) (w : ℂ) :
    dirD (dirichletTangentialDifferenceIter h k u) w z =
      dirichletTangentialDifferenceIter h k (dirD u w) z := by
  induction k generalizing a z with
  | zero => rfl
  | succ k ih =>
      have hm := step_margin hmargin
      have hs := dirichletTangentialDifferenceIter_contDiffOn k hm hu
      have hz' : z ∈ smoothDirichletHalfBox (a + |h|) b :=
        ⟨hz.1.trans_le (le_add_of_nonneg_right (abs_nonneg h)), hz.2⟩
      have hzh := halfBox_add_mem (t := h) le_rfl hz
      rw [dirichletTangentialDifferenceIter_succ,
        dirichletTangentialDifference_dirD
          ((hs.contDiffAt ((isOpen_smoothDirichletHalfBox _ _).mem_nhds hz')).differentiableAt
            (by simp))
          ((hs.contDiffAt ((isOpen_smoothDirichletHalfBox _ _).mem_nhds hzh)).differentiableAt
            (by simp)) w]
      change (dirD (dirichletTangentialDifferenceIter h k u) w (z + (h : ℂ)) -
          dirD (dirichletTangentialDifferenceIter h k u) w z) / (h : ℂ) = _
      rw [ih hm hzh, ih hm hz']
      rfl

/-- Each fixed finite quotient is truly in L².  The norm is allowed to
depend on that nonzero fixed step; the later energy estimate removes that
dependence. -/
theorem dirichletTangentialDifferenceIter_memLp
    {A a b h : ℝ} (k : ℕ) (hmargin : a + (k : ℝ) * |h| ≤ A)
    {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b))) :
    MemLp (dirichletTangentialDifferenceIter h k u) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  exact quotientIter_induction (fun a v => MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (fun h => hu.mono_measure (Measure.restrict_mono_set _ (halfBox_mono h le_rfl)))
    (dirichletTangentialDifference_memLp le_rfl) k hmargin

section

variable (f : ℝ → ℝ) (h : ℝ) (j k : ℕ) (a u v : ℂ → ℂ) (i : Fin 2) (z : ℂ)

theorem dirichletTangentialDifferenceIter_gradient_memLp
    {A a b h : ℝ} (k : ℕ) (hmargin : a + (k : ℝ) * |h| ≤ A)
    {u : ℂ → ℂ} (hu : ContDiffOn ℝ ∞ u (smoothDirichletHalfBox A b))
    {w : ℂ} (hg : MemLp (dirD u w) 2
      (volume.restrict (smoothDirichletHalfBox A b))) :
    MemLp (dirD (dirichletTangentialDifferenceIter h k u) w) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  
  apply (dirichletTangentialDifferenceIter_memLp k hmargin hg).ae_eq
  filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
    with z hz
  exact (dirichletTangentialDifferenceIter_dirD k hmargin hu hz w).symm

theorem dirichletTangentialTranslate_succ :
    dirichletTangentialTranslate h (dirichletTangentialTranslate ((j : ℝ) * h) a) =
      dirichletTangentialTranslate (((j + 1 : ℕ) : ℝ) * h) a := by
  funext z
  unfold dirichletTangentialTranslate
  congr 1
  push_cast
  ring

/-- Full discrete Leibniz formula.  The jth difference of v is at the
original point; only the smooth coefficient is shifted by j h. -/
theorem dirichletTangentialDifferenceIter_mul :
    dirichletTangentialDifferenceIter h k (fun w => a w * v w) z =
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) *
        (dirichletTangentialTranslate ((j : ℝ) * h)
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
          fun w => ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) * K j (k - j) w :=
        funext ih
      have hK (j : ℕ) (hj : j ∈ Finset.range (k + 1)) :
          dirichletTangentialDifference h (K j (k - j)) z =
            K j (k + 1 - j) z + K (j + 1) (k - j) z := by
        have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
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
        _ = ∑ j ∈ Finset.range (k + 1), (k.choose j) *
            dirichletTangentialDifference h (K j (k - j)) z := by
          change tangentialQuotient h (dirichletTangentialDifferenceIter h k _ ) z = _
          rw [heq]
          have he : (fun w => ∑ j ∈ Finset.range (k+1), (k.choose j : ℂ) * K j (k-j) w) =
              ∑ j ∈ Finset.range (k+1), (k.choose j : ℂ) • K j (k-j) := by ext w; simp [Finset.sum_apply]
          rw [he, map_sum]; simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]; rfl
        _ = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) *
            (K j (k + 1 - j) z + K (j + 1) (k - j) z) := Finset.sum_congr rfl (fun j hj => congrArg (fun t => (k.choose j : ℂ) * t)
            (hK j hj))
        _ = ∑ j ∈ Finset.range (k + 2), ((k + 1).choose j) *
            K j (k + 1 - j) z := by
          rw [Finset.sum_choose_succ_mul (fun j l => K j l z) k]
          simp [mul_add, Finset.sum_add_distrib]
        _ = _ := rfl

/-- The full commutator contains only gradient differences strictly
below k; no translated gradient estimate is hidden in its formula. -/
theorem dirichletHigherCoefficientCommutator_eq_sum :
    dirichletHigherCoefficientCommutator h k a v z =
      ∑ j ∈ Finset.range k, (k.choose j : ℂ) *
        (dirichletTangentialTranslate ((j : ℝ) * h)
            (dirichletTangentialDifferenceIter h (k - j) a) z *
          dirichletTangentialDifferenceIter h j v z) := by
  simp [dirichletHigherCoefficientCommutator, dirichletTangentialDifferenceIter_mul, Finset.sum_range_succ, Nat.choose_self, Nat.sub_self, dirichletTangentialDifferenceIter_zero]

theorem norm_dirichletHigherCoefficientCommutator_le :
    ‖dirichletHigherCoefficientCommutator h k a v z‖ ≤
      ∑ j ∈ Finset.range k, (k.choose j : ℝ) *
        (‖dirichletTangentialDifferenceIter h (k - j) a
              (z + (((j : ℝ) * h : ℝ) : ℂ))‖ *
          ‖dirichletTangentialDifferenceIter h j v z‖) := by
  rw [dirichletHigherCoefficientCommutator_eq_sum]
  calc
    _ ≤ _ := norm_sum_le _ _
    _ = _ := by
      simp [norm_mul, Complex.norm_natCast, dirichletTangentialTranslate]

include f h i k u z in
/-- The actual kth coefficient error in both rows of the graph matrix. -/
def dirichletHigherCoefficientDifferenceFlux : ℂ :=
  ![-dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f)
      (dirD u Complex.I) z,
    -dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f)
      (dirD u 1) z +
      dirichletHigherCoefficientCommutator h k
        (fun w => 1 + dirichletGraphSlope f w ^ 2) (dirD u Complex.I) z] i

end

/-- The exact kth flux decomposition on the interior smaller half box.
The coefficients in the principal part are evaluated at z+k h.  The
commutator uses only lower actual quotients of coefficient and gradient. -/
theorem dirichletTangentialDifferenceIter_flux_split
    {A a b h : ℝ} (k : ℕ) (hmargin : a + (k : ℝ) * |h| ≤ A)
    (f : ℝ → ℝ) {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ ∞ u (smoothDirichletHalfBox A b))
    {z : ℂ} (hz : z ∈ smoothDirichletHalfBox a b) (i : Fin 2) :
    dirichletTangentialDifferenceIter h k (dirichletFlattenedFlux f u i) z =
      dirichletShiftedFlux f ((k : ℝ) * h)
        (dirichletTangentialDifferenceIter h k u) i z +
      dirichletHigherCoefficientDifferenceFlux f h k u i z := by
  have hx := dirichletTangentialDifferenceIter_dirD k hmargin hu hz 1
  have hy := dirichletTangentialDifferenceIter_dirD k hmargin hu hz Complex.I
  let X := dirD u 1
  let Y := dirD u Complex.I
  let S := dirichletGraphSlope f
  let T := fun w => 1 + S w ^ 2
  let D := dirichletTangentialDifferenceIter h k
  fin_cases i
  · change D (X - S * Y) z = _
    rw [map_sub, Pi.sub_apply]; dsimp only [D]; rw [dirichletTangentialDifferenceIter_mul_eq_shift_add_commutator]
    simp [dirichletShiftedFlux, dirichletHigherCoefficientDifferenceFlux, dirichletTangentialTranslate, X, Y, S, D, hx, hy]; ring
  · change D ((fun w => -S w * X w) + T * Y) z = _
    have he : (fun w => -S w * X w) = -(S * X) := funext fun _ => neg_mul ..
    rw [he, map_add, map_neg, Pi.add_apply, Pi.neg_apply]
    simp [D, X, Y, S, T, dirichletShiftedFlux, dirichletHigherCoefficientDifferenceFlux,
      dirichletTangentialDifferenceIter_mul_eq_shift_add_commutator, hx, hy, dirichletTangentialTranslate]; ring

/-- Iteration of the actual real directional derivative. -/
def dirichletCoordinateDerivative (w : ℂ) : ℕ → (ℂ → ℂ) → (ℂ → ℂ)
  | 0, u => u
  | k + 1, u => dirD (dirichletCoordinateDerivative w k u) w

@[simp] theorem dirichletCoordinateDerivative_succ (w : ℂ) (k : ℕ) (u : ℂ → ℂ) :
    dirichletCoordinateDerivative w (k + 1) u =
      dirD (dirichletCoordinateDerivative w k u) w := rfl

section

variable (w : ℂ) (k l : ℕ) (u : ℂ → ℂ)

theorem dirichletCoordinateDerivative_iterate :
    dirichletCoordinateDerivative w k (dirichletCoordinateDerivative w l u) =
      dirichletCoordinateDerivative w (k + l) u := by
  induction k with
  | zero => simp [dirichletCoordinateDerivative]
  | succ k ih =>
      simp [dirichletCoordinateDerivative_succ, ih, Nat.succ_add]

abbrev dirichletTangentialDerivative := dirichletCoordinateDerivative 1

lemma dirichletTangentialDerivative_succ_right :
    dirichletTangentialDerivative k (dirD u 1) = dirichletTangentialDerivative (k+1) u :=
  dirichletCoordinateDerivative_iterate 1 k 1 u

end

attribute [simp] dirichletCoordinateDerivative.eq_1

theorem dirichlet_dirD_contDiff {c : ℂ → ℂ}
    (hc : ContDiff ℝ ∞ c) (w : ℂ) :
    ContDiff ℝ ∞ (dirD c w) :=
  (hc.fderiv_right  le_rfl).clm_apply contDiff_const

theorem dirichletCoordinateDerivative_contDiff {u : ℂ → ℂ}
    (hu : ContDiff ℝ ∞ u) (w : ℂ) (k : ℕ) :
    ContDiff ℝ ∞ (dirichletCoordinateDerivative w k u) := by
  induction k with
  | zero => exact hu
  | succ k ih => exact dirichlet_dirD_contDiff ih w

theorem dirichletTangentialDifferenceIter_dirD_global
    {c : ℂ → ℂ} (hc : ContDiff ℝ ∞ c) (h : ℝ) (k : ℕ) (w : ℂ) :
    dirD (dirichletTangentialDifferenceIter h k c) w =
      dirichletTangentialDifferenceIter h k (dirD c w) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      funext z
      have hs := dirichletTangentialDifferenceIter_contDiff hc h k
      rw [dirichletTangentialDifferenceIter_succ,
        dirichletTangentialDifference_dirD
          (hs.differentiable (by simp) z)
          (hs.differentiable (by simp) (z + h)) w,
        ih]
      rfl

/-- The closed half rectangle is actually compact, also when its side
lengths make it empty. -/
theorem isCompact_smoothDirichletClosedHalfBox (A b : ℝ) :
    IsCompact (smoothDirichletClosedHalfBox A b) := by
  have hs : IsClosed (smoothDirichletClosedHalfBox A b) :=
    (isClosed_le Complex.continuous_re.abs continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const))
  
  apply Metric.isCompact_of_isClosed_isBounded hs
  apply (isBounded_closedBall  (r := A + b)).subset
  intro z hz
  rw [mem_closedBall, dist_zero_right]
  calc
    _ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ _ := add_le_add hz.1 (by rw [abs_of_nonneg hz.2.1]; exact hz.2.2)

/-- One true quotient is bounded by its horizontal derivative on the
larger closed box.  Only the smooth coefficient has boundary derivatives. -/
theorem dirichletTangentialDifference_norm_le
    {A a b h M : ℝ} (hh : 0 < h) (hmargin : a + h ≤ A)
    {c : ℂ → ℂ} (hc : ContDiff ℝ ∞ c)
    (hM : ∀ z ∈ smoothDirichletClosedHalfBox A b, ‖dirD c 1 z‖ ≤ M)
    {z : ℂ} (hz : z ∈ smoothDirichletClosedHalfBox a b) :
    ‖dirichletTangentialDifference h c z‖ ≤ M := by
  let v : ℝ → ℂ := fun t => c (z + t)
  let dv  := fun t => dirD c 1 (z + t)
  have hmap (t : ℝ) (ht : t ∈ Icc 0 h) :
      z + t ∈ smoothDirichletClosedHalfBox A b := by
    have hx  := by
      calc
        _ ≤ _ := abs_add_le _ _
        _ ≤ a + h := add_le_add hz.1 (by rw [abs_of_nonneg ht.1]; exact ht.2)
        _ ≤ A := hmargin
    simpa [smoothDirichletClosedHalfBox] using (show |z.re + t| ≤ A ∧ 0 ≤ z.im ∧ z.im ≤ b from ⟨hx, hz.2⟩)
  have hd (t : ℝ) : HasDerivAt v (dv t) t := by
    
    exact (hc.differentiable (by simp) (z + t)).hasFDerivAt.comp_hasDerivAt t ((Complex.ofRealCLM.hasDerivAt).const_add z)
  have hp := (convex_Icc 0 h).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hd t).hasDerivWithinAt) (fun t ht => hM _ (hmap t ht))
    (show (0 : ℝ) ∈ Icc (0 : ℝ) h from ⟨le_rfl, hh.le⟩)
    (show h ∈ Icc (0 : ℝ) h from ⟨hh.le, le_rfl⟩)
  have hp' : ‖c (z + (h : ℂ)) - c z‖ ≤ M * h := by
    simpa only [v, Complex.ofReal_zero, add_zero, sub_zero,
      Real.norm_eq_abs, abs_of_pos hh] using hp
  rw [dirichletTangentialDifference, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hh]
  exact (div_le_iff₀ hh).mpr hp'

/-- At every fixed order the quotient bound depends on the actual kth
horizontal derivative, and not on h.  The margin counts every translation. -/
theorem dirichletTangentialDifferenceIter_norm_le
    {A a b h M : ℝ} (k : ℕ) (hh : 0 < h)
    (hmargin : a + (k : ℝ) * h ≤ A) {c : ℂ → ℂ}
    (hc : ContDiff ℝ ∞ c)
    (hM : ∀ z ∈ smoothDirichletClosedHalfBox A b,
      ‖dirichletTangentialDerivative k c z‖ ≤ M)
    {z : ℂ} (hz : z ∈ smoothDirichletClosedHalfBox a b) :
    ‖dirichletTangentialDifferenceIter h k c z‖ ≤ M := by
  induction k generalizing a c z with
  | zero =>
      
      refine hM z ⟨hz.1.trans ?_, hz.2⟩
      simpa using hmargin
  | succ k ih =>
      
      apply dirichletTangentialDifference_norm_le hh (le_refl (a + h))
        (dirichletTangentialDifferenceIter_contDiff hc h k) _ hz
      intro w hw
      rw [dirichletTangentialDifferenceIter_dirD_global hc]
      apply ih (by
        rw [Nat.cast_add, Nat.cast_one] at hmargin
        nlinarith) (dirichlet_dirD_contDiff hc 1) _ hw
      intro v hv
      rw [dirichletTangentialDerivative_succ_right]
      exact hM v hv

/-- Smooth coefficients or a genuine smooth forcing have uniform kth
quotient bounds on every fixed smaller half box with the stated margin. -/
theorem exists_dirichletTangentialDifferenceIter_bound
    {c : ℂ → ℂ} (hc : ContDiff ℝ ∞ c) (A b : ℝ) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (a h : ℝ), 0 < h → a + (k : ℝ) * h ≤ A →
      ∀ z ∈ smoothDirichletClosedHalfBox a b,
        ‖dirichletTangentialDifferenceIter h k c z‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_smoothDirichletClosedHalfBox A b).exists_bound_of_continuousOn
    (dirichletCoordinateDerivative_contDiff hc 1 k).continuous.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun a h hh hmargin z hz => ?_⟩
  grind [dirichletTangentialDifferenceIter_norm_le]

/-- A finite number of genuine derivative bounds can be made simultaneous.
No bound on a derivative of the Dirichlet solution is requested here. -/
theorem exists_dirichletTangentialDerivative_upto_bound
    {c : ℂ → ℂ} (hc : ContDiff ℝ ∞ c) (A b : ℝ) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ l : ℕ, l ≤ k →
      ∀ z ∈ smoothDirichletClosedHalfBox A b,
        ‖dirichletTangentialDerivative l c z‖ ≤ M := by
  induction k with
  | zero =>
      obtain ⟨M, hM⟩ := (isCompact_smoothDirichletClosedHalfBox A b).exists_bound_of_continuousOn
        hc.continuous.continuousOn
      refine ⟨max M 0, le_max_right _ _, fun l hl z hz => ?_⟩
      have hl0 : l = 0 := Nat.eq_zero_of_le_zero hl
      simp [*]
  | succ k ih =>
      obtain ⟨M₀, hM₀, h₀⟩ := ih
      obtain ⟨M₁, h₁⟩ := (isCompact_smoothDirichletClosedHalfBox A b).exists_bound_of_continuousOn
        (dirichletCoordinateDerivative_contDiff hc 1 (k + 1)).continuous.continuousOn
      refine ⟨max M₀ M₁, hM₀.trans (le_max_left _ _), fun l hl z hz => ?_⟩
      rcases Nat.eq_or_lt_of_le hl with h | h
      · grind
      · grind

/-- Uniform pointwise coefficient commutator control by lower differences
of the actual input, all at the original point z. -/
theorem norm_dirichletHigherCoefficientCommutator_le_of_derivative_bounds
    {A a b h M : ℝ} (k : ℕ) (hh : 0 < h) (hmargin : a + (k : ℝ) * h ≤ A)
    {c : ℂ → ℂ} (hc : ContDiff ℝ ∞ c)
    (hM : ∀ l : ℕ, l ≤ k → ∀ w ∈ smoothDirichletClosedHalfBox A b,
      ‖dirichletTangentialDerivative l c w‖ ≤ M)
    (v : ℂ → ℂ) {z : ℂ} (hz : z ∈ smoothDirichletClosedHalfBox a b) :
    ‖dirichletHigherCoefficientCommutator h k c v z‖ ≤
      M * ∑ j ∈ Finset.range k, (k.choose j : ℝ) *
        ‖dirichletTangentialDifferenceIter h j v z‖ := by
  refine (norm_dirichletHigherCoefficientCommutator_le h k c v z).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hjk  := (Finset.mem_range.mp hj).le
  have hnat : ((k - j : ℕ) : ℝ) = (k : ℝ) - (j : ℝ) := Nat.cast_sub hjk
  
  have hshift : z + ((j * h : ℝ) : ℂ) ∈
      smoothDirichletClosedHalfBox (a + j * h) b := by
    
    have hx := (abs_add_le z.re (j * h)).trans
      (add_le_add hz.1 (le_of_eq (abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hh.le))))
    simpa [smoothDirichletClosedHalfBox] using (show |z.re + (j : ℝ) * h| ≤ a + (j : ℝ) * h ∧
        0 ≤ z.im ∧ z.im ≤ b from ⟨hx, hz.2⟩)
  have hcoef := dirichletTangentialDifferenceIter_norm_le (k - j) hh (by
    nlinarith) hc
    (hM (k - j) (Nat.sub_le _ _)) hshift
  calc
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)) (Nat.cast_nonneg _)
    _ = _ := by ring

/-- The two genuine graph coefficients admit the simultaneous commutator
bound needed by the localized higher energy induction. -/
theorem exists_dirichletGraphHigherCommutator_bound {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (A b : ℝ) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (a h : ℝ), 0 < h → a + (k : ℝ) * h ≤ A →
      ∀ (v : ℂ → ℂ) (z : ℂ), z ∈ smoothDirichletClosedHalfBox a b →
        (‖dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f) v z‖ ≤
          M * ∑ j ∈ Finset.range k, (k.choose j : ℝ) *
            ‖dirichletTangentialDifferenceIter h j v z‖) ∧
        (‖dirichletHigherCoefficientCommutator h k
            (fun w => 1 + dirichletGraphSlope f w ^ 2) v z‖ ≤
          M * ∑ j ∈ Finset.range k, (k.choose j : ℝ) *
            ‖dirichletTangentialDifferenceIter h j v z‖) := by
  have hd := dirichletGraphSlope_contDiff hf
  obtain ⟨M₀, hM₀, h₀⟩ := exists_dirichletTangentialDerivative_upto_bound hd A b k
  obtain ⟨M₁, _, h₁⟩ := exists_dirichletTangentialDerivative_upto_bound
    (contDiff_const.add (hd.pow 2)) A b k
  refine ⟨max M₀ M₁, (by grind), fun a h hh hmargin v z hz => ?_⟩
  constructor
  · grind [norm_dirichletHigherCoefficientCommutator_le_of_derivative_bounds]
  · apply norm_dirichletHigherCoefficientCommutator_le_of_derivative_bounds
      k hh hmargin ((by fun_prop)) _ v hz
    exact fun l hl w hw => (h₁ l hl w hw).trans (le_max_right _ _)

/-- Centered higher mean-value bound.  The kth quotient stays within
the same norm ball as the actual kth derivative on its entire stencil.
This is the genuine finite-difference ingredient in the later Fatou limit. -/
theorem dirichletTangentialDifferenceIter_centered_norm_le
    {c : ℂ → ℂ} (hc : ContDiff ℝ ∞ c) (k : ℕ)
    {h M : ℝ} (hh : 0 < h) (z C : ℂ)
    (hM : ∀ t ∈ Icc (0 : ℝ) ((k : ℝ) * h),
      ‖dirichletTangentialDerivative k c (z + (t : ℂ)) - C‖ ≤ M) :
    ‖dirichletTangentialDifferenceIter h k c z - C‖ ≤ M := by
  induction k generalizing c z with
  | zero =>
      aesop
  | succ k ih =>
      let v : ℝ → ℂ := fun t =>
        dirichletTangentialDifferenceIter h k c (z + t) - t * C
      let dv  := fun t =>
        dirichletTangentialDifferenceIter h k (dirD c 1) (z + t) - C
      have hd (t : ℝ) : HasDerivAt v (dv t) t := by
        
        
        have hg := (((dirichletTangentialDifferenceIter_contDiff hc h k).differentiable (by simp) (z + t)).hasFDerivAt.comp_hasDerivAt
          t ((Complex.ofRealCLM.hasDerivAt).const_add z)).sub (Complex.ofRealCLM.hasDerivAt.mul_const C)
        have heq := congrFun (dirichletTangentialDifferenceIter_dirD_global hc h k 1)
          (z + t)
        have hgrad : fderiv ℝ (dirichletTangentialDifferenceIter h k c)
            (z + (t : ℂ)) 1 =
              dirichletTangentialDifferenceIter h k (dirD c 1) (z + (t : ℂ)) := heq
        simp at hg
        
        rw [hgrad] at hg
        exact hg
      have hbound (t : ℝ) (ht : t ∈ Icc 0 h) : ‖dv t‖ ≤ M := by
        apply ih (dirichlet_dirD_contDiff hc 1) (z + t)
        intro s hs
        
        have heq : z + (t : ℂ) + (s : ℂ) = z + ((t + s : ℝ) : ℂ) := by
          push_cast
          ring
        rw [dirichletTangentialDerivative_succ_right, heq]
        apply hM (t + s)
        rw [Nat.cast_add, Nat.cast_one]
        constructor
        · exact add_nonneg ht.1 hs.1
        · nlinarith [ht.2, hs.2]
      have hp := (convex_Icc 0 h).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun t _ => (hd t).hasDerivWithinAt) hbound
        (show (0 : ℝ) ∈ Icc (0 : ℝ) h from ⟨le_rfl, hh.le⟩)
        (show h ∈ Icc (0 : ℝ) h from ⟨hh.le, le_rfl⟩)
      have hp' : ‖(v h - v 0) / h‖ ≤ M := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
        apply (div_le_iff₀ hh).mpr
        simpa [sub_zero, Real.norm_eq_abs, abs_of_pos hh] using hp
      have hhC : h ≠ 0 := by exact_mod_cast hh.ne'
      have heq : (v h - v 0) / (h : ℂ) =
          dirichletTangentialDifferenceIter h (k + 1) c z - C := by
        simp only [v, Complex.ofReal_zero, zero_mul, sub_zero, add_zero,
          dirichletTangentialDifferenceIter_succ, dirichletTangentialDifference]
        field_simp [hhC]
        ring
      rw [heq] at hp'
      exact hp'

/-- Positive-step higher quotients genuinely converge to the actual
iterated directional derivative at every smooth point. -/
theorem dirichletTangentialDifferenceIter_tendsto
    {c : ℂ → ℂ} (hc : ContDiff ℝ ∞ c) (k : ℕ) (z : ℂ) :
    Tendsto (fun h : ℝ => dirichletTangentialDifferenceIter h k c z)
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (dirichletTangentialDerivative k c z)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hct : ContinuousAt (dirichletTangentialDerivative k c) z :=
    (dirichletCoordinateDerivative_contDiff hc 1 k).continuous.continuousAt
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hct (ε / 2) (by positivity)
  have hk : 0 < (k : ℝ) + 1 := by positivity
  
  filter_upwards [self_mem_nhdsWithin, ((eventually_lt_nhds (div_pos hδ hk)).filter_mono nhdsWithin_le_nhds)] with h hh hs
  have hhpos  := hh
  have hbound : ∀ t ∈ Icc 0 (k * h),
      ‖dirichletTangentialDerivative k c (z + t) -
        dirichletTangentialDerivative k c z‖ ≤ ε / 2 := by
    intro t ht
    have hkh : ((k : ℝ) + 1) * h < δ := by
      simpa only [mul_comm] using (lt_div_iff₀ hk).mp hs
    have htδ : t < δ := by nlinarith [ht.2]
    have hd : dist (z + (t : ℂ)) z < δ := by
      simpa only [dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg ht.1] using htδ
    exact (show ‖dirichletTangentialDerivative k c (z + t) -
        dirichletTangentialDerivative k c z‖ < ε / 2 by
      simpa [dist_eq_norm] using hclose hd).le
  have hb := dirichletTangentialDifferenceIter_centered_norm_le hc k hhpos z
    (dirichletTangentialDerivative k c z) hbound
  rw [dist_eq_norm]
  linarith

/-- Exact finite-stencil locality.  No value or derivative outside the
stencil can change an actual iterated quotient. -/
theorem dirichletTangentialDifferenceIter_eq_of_stencil
    (h : ℝ) (k : ℕ) (c d : ℂ → ℂ) (z : ℂ)
    (heq : ∀ j : ℕ, j ≤ k →
      c (z + (((j : ℝ) * h : ℝ) : ℂ)) = d (z + (((j : ℝ) * h : ℝ) : ℂ))) :
    dirichletTangentialDifferenceIter h k c z =
      dirichletTangentialDifferenceIter h k d z := by
  induction k generalizing z with
  | zero => simpa using heq 0 le_rfl
  | succ k ih =>
      
      have h1 : ∀ j : ℕ, j ≤ k →
          c (z + h + ((j * h : ℝ) : ℂ)) =
            d (z + h + ((j * h : ℝ) : ℂ)) := by
        intro j hj
        have harg : z + (h : ℂ) + (((j : ℝ) * h : ℝ) : ℂ) =
            z + ((((j + 1 : ℕ) : ℝ) * h : ℝ) : ℂ) := by
          push_cast
          ring
        rw [harg]
        bound
      change (dirichletTangentialDifferenceIter h k c (z + (h : ℂ)) -
          dirichletTangentialDifferenceIter h k c z) / (h : ℂ) =
        (dirichletTangentialDifferenceIter h k d (z + (h : ℂ)) -
          dirichletTangentialDifferenceIter h k d z) / (h : ℂ)
      rw [ih (z + h) h1, ih z (fun j hj => heq j (hj.trans (Nat.le_succ _)))]

theorem dirichletTangentialDerivative_eventuallyEq {c d : ℂ → ℂ} {z : ℂ}
    (heq : c =ᶠ[𝓝 z] d) (k : ℕ) :
    dirichletTangentialDerivative k c =ᶠ[𝓝 z] dirichletTangentialDerivative k d := by
  induction k with
  | zero => exact heq
  | succ k ih =>
      exact ih.fderiv.fun_comp (fun A : ℂ →L[ℝ] ℂ => A 1)

/-- The limit used by Fatou needs smoothness only in the actual open
interior.  A genuine local compact extension transfers its finite stencil
and its derivative germ; no boundary extension of a derivative is used. -/
theorem dirichletTangentialDifferenceIter_tendsto_of_contDiffOn
    {U : Set ℂ} (hU : IsOpen U) {c : ℂ → ℂ}
    (hc : ContDiffOn ℝ ∞ c U) (k : ℕ) {z : ℂ} (hz : z ∈ U) :
    Tendsto (fun h : ℝ => dirichletTangentialDifferenceIter h k c z)
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (dirichletTangentialDerivative k c z)) := by
  obtain ⟨d, hd, hdc⟩ := exists_smooth_compact_extension
    (isCompact_singleton (x := z)) hU (singleton_subset_iff.mpr hz) hc
  have heq  := hdc z (mem_singleton z)
  have hall : ∀ᶠ h : ℝ in 𝓝 0, ∀ j ∈ Finset.range (k + 1),
      d (z + ((j * h : ℝ) : ℂ)) = c (z + ((j * h : ℝ) : ℂ)) := by
    apply (Filter.eventually_all_finset _).mpr
    intro j _
    have ht : Tendsto (fun h : ℝ => z + ((j * h : ℝ) : ℂ))
        (𝓝 0) (𝓝 z) := by
      have hstencil : Continuous (fun h : ℝ => z + (((j : ℝ) * h : ℝ) : ℂ)) :=
        (by fun_prop)
      simpa using hstencil.tendsto 0
    exact ht.eventually heq
  have hdiff : (fun h : ℝ => dirichletTangentialDifferenceIter h k d z) =ᶠ[𝓝 0]
      fun h => dirichletTangentialDifferenceIter h k c z := by
    filter_upwards [hall] with h hh
    grind [dirichletTangentialDifferenceIter_eq_of_stencil]
  have hlim := (dirichletTangentialDifferenceIter_tendsto hd.1 k z).congr'
    (hdiff.filter_mono nhdsWithin_le_nhds)
  rw [(dirichletTangentialDerivative_eventuallyEq heq k).self_of_nhds] at hlim
  exact hlim

end PolyaNeumann

end
