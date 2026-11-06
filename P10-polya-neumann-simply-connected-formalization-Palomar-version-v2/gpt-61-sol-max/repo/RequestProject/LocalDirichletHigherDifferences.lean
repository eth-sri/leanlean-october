module

public import RequestProject.PlanarTypes

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

open scoped ContDiff

noncomputable section

namespace PolyaNeumann

open Set Metric MeasureTheory Filter
open scoped Topology

/-- Actual horizontal translation, with the physical real increment. -/
def dirichletTangentialTranslate (h : ℝ) (u : PlaneMap) z  :=
  u (z + (h : ℂ))

/-- Iteration of the genuine quotient already used by the first energy
estimate.  The zeroth quotient is the original function, including its
constant mode and its actual boundary values. -/
@[simp] def dirichletTangentialDifferenceIter (h : ℝ) : ℕ → (PlaneMap) → (PlaneMap)
  | 0, u => u
  | k + 1, u => dirichletTangentialDifference h
      (dirichletTangentialDifferenceIter h k u)

section
variable (h : ℝ)
include h



theorem dirichletTangentialDifference_add u v :
    dirichletTangentialDifference h (fun z => u z + v z) =
      fun z => dirichletTangentialDifference h u z +
        dirichletTangentialDifference h v z := by
  grind only [dirichletTangentialDifference]

theorem dirichletTangentialDifference_sub u v :
    dirichletTangentialDifference h (fun z => u z - v z) =
      fun z => dirichletTangentialDifference h u z -
        dirichletTangentialDifference h v z := by
  grind only [dirichletTangentialDifference]

theorem dirichletTangentialDifference_const_mul a u :
    dirichletTangentialDifference h (fun z => a * u z) =
      fun z => a * dirichletTangentialDifference h u z := by
  grind only [dirichletTangentialDifference]

/-- The discrete product rule, with the shift on the first factor.  It
remains true for zero step because the actual quotient is then zero. -/
theorem dirichletTangentialDifference_mul a v :
    dirichletTangentialDifference h (fun z => a z * v z) =
      fun z => dirichletTangentialTranslate h a z *
          dirichletTangentialDifference h v z +
        dirichletTangentialDifference h a z * v z := by
  grind only [dirichletTangentialDifference, dirichletTangentialTranslate]

end


theorem dirichletTangentialDifference_translate h t u :
    dirichletTangentialDifference h (dirichletTangentialTranslate t u) =
      dirichletTangentialTranslate t (dirichletTangentialDifference h u) := by
  grind only [dirichletTangentialDifference, dirichletTangentialTranslate]

section
variable (h : ℝ) (k : ℕ)
include h k

theorem dirichletTangentialDifferenceIter_add u v :
    dirichletTangentialDifferenceIter h k (fun z => u z + v z) =
      fun z => dirichletTangentialDifferenceIter h k u z +
        dirichletTangentialDifferenceIter h k v z := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp_all [dirichletTangentialDifference_add]

theorem dirichletTangentialDifferenceIter_sub u v :
    dirichletTangentialDifferenceIter h k (fun z => u z - v z) =
      fun z => dirichletTangentialDifferenceIter h k u z -
        dirichletTangentialDifferenceIter h k v z := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp_all [dirichletTangentialDifference_sub]

theorem dirichletTangentialDifferenceIter_const_mul a u :
    dirichletTangentialDifferenceIter h k (fun z => a * u z) =
      fun z => a * dirichletTangentialDifferenceIter h k u z := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp_all [dirichletTangentialDifference_const_mul]

end


/-- The actual commutator after k quotients.  This is constructed from
the two actual products, rather than an assumed differentiated equation. -/
def dirichletHigherCoefficientCommutator h k
    a v z  :=
  dirichletTangentialDifferenceIter h k (fun w => a w * v w) z -
    dirichletTangentialTranslate ((k : ℝ) * h) a z *
      dirichletTangentialDifferenceIter h k v z



theorem dirichletTangentialDifferenceIter_mul_eq_shift_add_commutator
    h k a v z :
    dirichletTangentialDifferenceIter h k (fun w => a w * v w) z =
      dirichletTangentialTranslate ((k : ℝ) * h) a z *
        dirichletTangentialDifferenceIter h k v z +
      dirichletHigherCoefficientCommutator h k a v z := by
  unfold dirichletHigherCoefficientCommutator
  ring

theorem dirichletTangentialDifferenceIter_contDiff 
    (hu : RealSmooth u) h k :
    RealSmooth (dirichletTangentialDifferenceIter h k u) := (Nat.recAux hu (fun k ih => ContDiff.div_const (ContDiff.sub (ContDiff.comp ih (ContDiff.add contDiff_id contDiff_const)) ih) ↑h) k)

section
variable {A a b h : ℝ} (k : ℕ) (hmargin : a + (k : ℝ) * |h| ≤ A) {u : PlaneMap}

include A a b h k hmargin u in
/-- No derivative is assumed continuous on the bottom: each finite
quotient inherits the original function's continuity by translation. -/
theorem dirichletTangentialDifferenceIter_continuousOn (hu : ContinuousOn u (smoothDirichletClosedHalfBox A b)) :
    ContinuousOn (dirichletTangentialDifferenceIter h k u)
      (smoothDirichletClosedHalfBox a b) := by
  induction k generalizing a with
  | zero =>
      have ha : a ≤ A := by simpa using hmargin
      exact hu.mono (fun z hz => ⟨hz.1.trans ha, hz.2⟩)
  | succ k ih =>
      have hm : (a + |h|) + (k : ℝ) * |h| ≤ A := by
        grind
      exact dirichletTangentialDifference_continuousOn (le_refl (a + |h|))
        (ih hm)

section
variable (hu : RealSmoothOn u (smoothDirichletHalfBox A b))

include A a b h k hmargin u in
include hu in
theorem dirichletTangentialDifferenceIter_contDiffOn :
    RealSmoothOn (dirichletTangentialDifferenceIter h k u)
      (smoothDirichletHalfBox a b) := by
  induction k generalizing a with
  | zero =>
      have ha : a ≤ A := by simpa using hmargin
      exact hu.mono (fun z hz => ⟨hz.1.trans_le ha, hz.2⟩)
  | succ k ih =>
      have hm : (a + |h|) + (k : ℝ) * |h| ≤ A := by
        grind
      exact dirichletTangentialDifference_contDiffOn (le_refl (a + |h|))
        (ih hm)

theorem dirichletTangentialDifferenceIter_zero_bottom
     (k : ℕ) (hmargin : a + (k : ℝ) * |h| ≤ A)
     (hu : ∀ x : ℝ, |x| < A → u (x : ℂ) = 0)
     (hx : |x| < a) :
    dirichletTangentialDifferenceIter h k u (x : ℂ) = 0 := by
  induction k generalizing a x with
  | zero =>
      have ha : a ≤ A := by simpa using hmargin
      exact hu x (hx.trans_le ha)
  | succ k ih =>
      have hm : (a + |h|) + (k : ℝ) * |h| ≤ A := by
        grind
      exact dirichletTangentialDifference_zero_bottom (le_refl (a + |h|))
        (fun y hy => ih hm hy) hx

section
include A a b h k hmargin u

include hu in
/-- Actual first derivatives commute with every finite quotient in the
interior.  This statement uses only smoothness on the larger open box. -/
theorem dirichletTangentialDifferenceIter_dirD
     (hz : z ∈ smoothDirichletHalfBox a b) w :
    dirD (dirichletTangentialDifferenceIter h k u) w z =
      dirichletTangentialDifferenceIter h k (dirD u w) z := by
  induction k generalizing a z with
  | zero => rfl
  | succ k ih =>
      have hm : (a + |h|) + (k : ℝ) * |h| ≤ A := by
        grind
      have hs := dirichletTangentialDifferenceIter_contDiffOn k hm hu
      have hz' : z ∈ smoothDirichletHalfBox (a + |h|) b :=
        ⟨hz.1.trans_le (le_add_of_nonneg_right (abs_nonneg h)), hz.2⟩
      have hzh : z + (h : ℂ) ∈ smoothDirichletHalfBox (a + |h|) b := by
        have hx := (abs_add_le z.re h).trans_lt
          ((add_lt_add_of_lt_of_le hz.1 le_rfl))
        simp_all [smoothDirichletHalfBox, PolyaNeumann.smoothDirichletHalfBox]
      rw [dirichletTangentialDifferenceIter.eq_2,
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
    (hu : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b))) :
    MemLp (dirichletTangentialDifferenceIter h k u) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  induction k generalizing a with
  | zero =>
      have ha : a ≤ A := by simpa using hmargin
      apply hu.mono_measure
      exact Measure.restrict_mono_set volume
        ((fun z hz => ⟨hz.1.trans_le ha, hz.2⟩))
  | succ k ih =>
      have hm : (a + |h|) + (k : ℝ) * |h| ≤ A := by
        grind
      exact dirichletTangentialDifference_memLp (le_refl (a + |h|)) (ih hm)

include hu in
theorem dirichletTangentialDifferenceIter_gradient_memLp
     (hg : MemLp (dirD u w) 2
      (volume.restrict (smoothDirichletHalfBox A b))) :
    MemLp (dirD (dirichletTangentialDifferenceIter h k u) w) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  have hm := dirichletTangentialDifferenceIter_memLp k hmargin hg
  apply hm.ae_eq
  filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
    with z hz
  grind only [dirichletTangentialDifferenceIter_dirD]

end


end


end


theorem dirichletTangentialTranslate_succ h (j : ℕ) a :
    dirichletTangentialTranslate h (dirichletTangentialTranslate ((j : ℝ) * h) a) =
      dirichletTangentialTranslate (((j + 1 : ℕ) : ℝ) * h) a := by
  funext z
  unfold dirichletTangentialTranslate
  congr 1
  push_cast
  ring

theorem dirichletTangentialDifference_sum {ι : Type*}
    s h (v : ι → PlaneMap) :
    dirichletTangentialDifference h (fun z => ∑ j ∈ s, v j z) =
      fun z => ∑ j ∈ s, dirichletTangentialDifference h (v j) z := by
  funext z
  simp  [dirichletTangentialDifference]
  rw [← Finset.sum_sub_distrib, Finset.sum_div]

section
variable (h : ℝ) (k : ℕ) (a v : PlaneMap) (z : ℂ)
include h k a v z

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
      let K : ℕ → ℕ → PlaneMap := fun j l w =>
        dirichletTangentialTranslate (j * h)
          (dirichletTangentialDifferenceIter h l a) w *
          dirichletTangentialDifferenceIter h j v w
      have heq : dirichletTangentialDifferenceIter h k (fun w => a w * v w) =
          fun w => ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) * K j (k - j) w :=
        funext ih
      have hK (j : ℕ) (hj : j ∈ Finset.range (k + 1)) :
          dirichletTangentialDifference h (K j (k - j)) z =
            K j (k + 1 - j) z + K (j + 1) (k - j) z := by
        have hjk  := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        have hnat : k - j + 1 = k + 1 - j := by omega
        have hd : dirichletTangentialDifference h
            (dirichletTangentialDifferenceIter h (k - j) a) =
            dirichletTangentialDifferenceIter h (k + 1 - j) a := by
          rw [← dirichletTangentialDifferenceIter.eq_2, Nat.succ_eq_add_one, hnat]
        change dirichletTangentialDifference h
          (fun w => dirichletTangentialTranslate (j * h)
            (dirichletTangentialDifferenceIter h (k - j) a) w *
              dirichletTangentialDifferenceIter h j v w) z = _
        rw [dirichletTangentialDifference_mul,
          dirichletTangentialDifference_translate,
          dirichletTangentialTranslate_succ, hd]
        change K (j + 1) (k - j) z + K j (k + 1 - j) z = _
        exact add_comm _ _
      calc
        _ = ∑ j ∈ Finset.range (k + 1), (k.choose j) *
            dirichletTangentialDifference h (K j (k - j)) z := by
          rw [dirichletTangentialDifferenceIter.eq_2, heq,
            dirichletTangentialDifference_sum]
          simp  [dirichletTangentialDifference_const_mul]
        _ = ∑ j ∈ Finset.range (k + 1), (k.choose j) *
            (K j (k + 1 - j) z + K (j + 1) (k - j) z) := by
          simp_all only 
        _ = ∑ j ∈ Finset.range (k + 2), ((k + 1).choose j) *
            K j (k + 1 - j) z := by
          rw [Finset.sum_choose_succ_mul (fun j l => K j l z) k]
          simp  [mul_add, Finset.sum_add_distrib]
        _ = _ := rfl

/-- The full commutator contains only gradient differences strictly
below k; no translated gradient estimate is hidden in its formula. -/
theorem dirichletHigherCoefficientCommutator_eq_sum :
    dirichletHigherCoefficientCommutator h k a v z =
      ∑ j ∈ Finset.range k, (k.choose j : ℂ) *
        (dirichletTangentialTranslate ((j : ℝ) * h)
            (dirichletTangentialDifferenceIter h (k - j) a) z *
          dirichletTangentialDifferenceIter h j v z) := by
  unfold dirichletHigherCoefficientCommutator
  rw [dirichletTangentialDifferenceIter_mul, Finset.sum_range_succ]
  simp_all

theorem norm_dirichletHigherCoefficientCommutator_le :
    ‖dirichletHigherCoefficientCommutator h k a v z‖ ≤
      ∑ j ∈ Finset.range k, (k.choose j : ℝ) *
        (‖dirichletTangentialDifferenceIter h (k - j) a
              (z + (((j : ℝ) * h : ℝ) : ℂ))‖ *
          ‖dirichletTangentialDifferenceIter h j v z‖) := by
  rw [dirichletHigherCoefficientCommutator_eq_sum]
  calc
    _ ≤ ∑ j ∈ Finset.range k, ‖(k.choose j) *
        (dirichletTangentialTranslate (j * h)
          (dirichletTangentialDifferenceIter h (k - j) a) z *
            dirichletTangentialDifferenceIter h j v z)‖ := norm_sum_le _ _
    _ = _ := by
      simp_all [dirichletTangentialTranslate]

end


/-- The actual kth coefficient error in both rows of the graph matrix. -/
def dirichletHigherCoefficientDifferenceFlux f h k
    u i z  :=
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
     (k : ℕ) (hmargin : a + (k : ℝ) * |h| ≤ A)
    f 
    (hu : RealSmoothOn u (smoothDirichletHalfBox A b))
     (hz : z ∈ smoothDirichletHalfBox a b) i :
    dirichletTangentialDifferenceIter h k (dirichletFlattenedFlux f u i) z =
      dirichletShiftedFlux f ((k : ℝ) * h)
        (dirichletTangentialDifferenceIter h k u) i z +
      dirichletHigherCoefficientDifferenceFlux f h k u i z := by
  have hx := dirichletTangentialDifferenceIter_dirD k hmargin hu hz 1
  have hy := dirichletTangentialDifferenceIter_dirD k hmargin hu hz Complex.I
  fin_cases i
  · change dirichletTangentialDifferenceIter h k
        (fun w => dirD u 1 w - dirichletGraphSlope f w * dirD u Complex.I w) z =
      (dirD (dirichletTangentialDifferenceIter h k u) 1 z -
        dirichletGraphSlope f (z + (((k : ℝ) * h : ℝ))) *
          dirD (dirichletTangentialDifferenceIter h k u) Complex.I z) +
      -dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f)
        (dirD u Complex.I) z
    simp only [dirichletTangentialDifferenceIter_sub]
    rw [dirichletTangentialDifferenceIter_mul_eq_shift_add_commutator]
    grind only [dirichletTangentialTranslate]
  · have hneg (w : ℂ) : -dirichletGraphSlope f w * dirD u 1 w =
        (-1 : ℂ) * (dirichletGraphSlope f w * dirD u 1 w) := by ring
    change dirichletTangentialDifferenceIter h k
        (fun w => -dirichletGraphSlope f w * dirD u 1 w +
          (1 + dirichletGraphSlope f w ^ 2) * dirD u Complex.I w) z =
      (-dirichletGraphSlope f (z + (((k : ℝ) * h : ℝ))) *
          dirD (dirichletTangentialDifferenceIter h k u) 1 z +
        (1 + dirichletGraphSlope f (z + (((k : ℝ) * h : ℝ))) ^ 2) *
          dirD (dirichletTangentialDifferenceIter h k u) Complex.I z) +
      (-dirichletHigherCoefficientCommutator h k (dirichletGraphSlope f)
          (dirD u 1) z +
        dirichletHigherCoefficientCommutator h k
          (fun w => 1 + dirichletGraphSlope f w ^ 2) (dirD u Complex.I) z)
    simp only [dirichletTangentialDifferenceIter_add]
    simp_rw [hneg]
    rw [dirichletTangentialDifferenceIter_const_mul]
    change (-1) * dirichletTangentialDifferenceIter h k
        (fun w => dirichletGraphSlope f w * dirD u 1 w) z +
      dirichletTangentialDifferenceIter h k
        (fun w => (1 + dirichletGraphSlope f w ^ 2) * dirD u Complex.I w) z = _
    rw [dirichletTangentialDifferenceIter_mul_eq_shift_add_commutator,
      dirichletTangentialDifferenceIter_mul_eq_shift_add_commutator]
    grind only [dirichletTangentialTranslate]

/-- The genuine iterated horizontal derivative, used only for smooth
coefficients and forcing in the uniform quotient bounds below. -/
@[simp] def dirichletTangentialDerivative : ℕ → (PlaneMap) → (PlaneMap)
  | 0, c => c
  | k + 1, c => dirD (dirichletTangentialDerivative k c) 1



section
variable {c : PlaneMap} (hc : RealSmooth c)

include c hc in
theorem dirichlet_dirD_contDiff w :
    RealSmooth (dirD c w) :=
  (hc.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

include c hc in
theorem dirichletTangentialDerivative_contDiff k :
    RealSmooth (dirichletTangentialDerivative k c) := (Nat.recAux hc (fun k ih => dirichlet_dirD_contDiff ih 1) k)

theorem dirichletTangentialDerivative_succ_right k c :
    dirichletTangentialDerivative k (dirD c 1) =
      dirichletTangentialDerivative (k + 1) c := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp_all

include c hc in
theorem dirichletTangentialDifferenceIter_dirD_global h k w :
    dirD (dirichletTangentialDifferenceIter h k c) w =
      dirichletTangentialDifferenceIter h k (dirD c w) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      funext z
      have hs := dirichletTangentialDifferenceIter_contDiff hc h k
      rw [dirichletTangentialDifferenceIter.eq_2,
        dirichletTangentialDifference_dirD
          (hs.differentiable (by simp) z)
          (hs.differentiable (by simp) (z + h)) w,
        ih]
      rfl

/-- The closed half rectangle is actually compact, also when its side
lengths make it empty. -/
theorem isCompact_smoothDirichletClosedHalfBox A b :
    IsCompact (smoothDirichletClosedHalfBox A b) := by
  have hs : IsClosed (smoothDirichletClosedHalfBox A b) :=
    (isClosed_le Complex.continuous_re.abs continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const))
  have hb : Bornology.IsBounded (smoothDirichletClosedHalfBox A b) := by
    apply (isBounded_closedBall (x := 0) (r := A + b)).subset
    intro z hz
    rw [mem_closedBall, dist_zero_right]
    calc
      ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ A + b := add_le_add hz.1 (by rw [abs_of_nonneg hz.2.1]; exact hz.2.2)
  exact Metric.isCompact_of_isClosed_isBounded hs hb

/-- One true quotient is bounded by its horizontal derivative on the
larger closed box.  Only the smooth coefficient has boundary derivatives. -/
theorem dirichletTangentialDifference_norm_le
     (hh : 0 < h) (hmargin : a + h ≤ A)
     (hc : RealSmooth c)
    (hM : ∀ z ∈ smoothDirichletClosedHalfBox A b, ‖dirD c 1 z‖ ≤ M)
     (hz : z ∈ smoothDirichletClosedHalfBox a b) :
    ‖dirichletTangentialDifference h c z‖ ≤ M := by
  let v : ComplexCurve := fun t => c (z + t)
  let dv  := fun t => dirD c 1 (z + t)
  have hmap (t : ℝ) (ht : t ∈ Icc (0 : ℝ) h) :
      z + (t : ℂ) ∈ smoothDirichletClosedHalfBox A b := by
    have hx : |z.re + t| ≤ A := by
      calc
        |z.re + t| ≤ |z.re| + |t| := abs_add_le _ _
        _ ≤ a + h := add_le_add hz.1 (by rw [abs_of_nonneg ht.1]; exact ht.2)
        _ ≤ A := hmargin
    simp_all [smoothDirichletClosedHalfBox]
  have hd (t : ℝ) : HasDerivAt v (dv t) t := by
    have ht : HasDerivAt (fun s : ℝ => z + (s : ℂ)) (1 : ℂ) t :=
      (Complex.ofRealCLM.hasDerivAt).const_add z
    exact (hc.differentiable (by simp) (z + t)).hasFDerivAt.comp_hasDerivAt t ht
  have hp := (convex_Icc 0 h).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hd t).hasDerivWithinAt) (fun t ht => hM _ (hmap t ht))
    ((⟨le_rfl, hh.le⟩))
    ((⟨hh.le, le_rfl⟩))
  have hp' : ‖c (z + (h : ℂ)) - c z‖ ≤ M * h := by
    simpa  [v, abs_of_pos hh] using hp
  rw [dirichletTangentialDifference, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hh]
  exact (div_le_iff₀ hh).mpr hp'

section
variable {A a b h M : ℝ} (k : ℕ) (hh : 0 < h) (hmargin : a + (k : ℝ) * h ≤ A)

include A a b h M k hh hmargin in
/-- At every fixed order the quotient bound depends on the actual kth
horizontal derivative, and not on h.  The margin counts every translation. -/
theorem dirichletTangentialDifferenceIter_norm_le 
    (hc : RealSmooth c)
    (hM : ∀ z ∈ smoothDirichletClosedHalfBox A b,
      ‖dirichletTangentialDerivative k c z‖ ≤ M)
     (hz : z ∈ smoothDirichletClosedHalfBox a b) :
    ‖dirichletTangentialDifferenceIter h k c z‖ ≤ M := by
  induction k generalizing a c z with
  | zero =>
      have ha : a ≤ A := by simpa using hmargin
      exact hM z ⟨hz.1.trans ha, hz.2⟩
  | succ k ih =>
      have hm : (a + h) + (k : ℝ) * h ≤ A := by
        grind
      apply dirichletTangentialDifference_norm_le hh (le_refl (a + h))
        (dirichletTangentialDifferenceIter_contDiff hc h k) _ hz
      intro w hw
      rw [dirichletTangentialDifferenceIter_dirD_global hc]
      apply ih hm (dirichlet_dirD_contDiff hc 1) _ hw
      simp_all [dirichletTangentialDerivative_succ_right]

include c hc in
/-- Smooth coefficients or a genuine smooth forcing have uniform kth
quotient bounds on every fixed smaller half box with the stated margin. -/
theorem exists_dirichletTangentialDifferenceIter_bound A b (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (a h : ℝ), 0 < h → a + (k : ℝ) * h ≤ A →
      ∀ z ∈ smoothDirichletClosedHalfBox a b,
        ‖dirichletTangentialDifferenceIter h k c z‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_smoothDirichletClosedHalfBox A b).exists_bound_of_continuousOn
    (dirichletTangentialDerivative_contDiff hc k).continuous.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun a h hh hmargin z hz => ?_⟩
  grind [dirichletTangentialDifferenceIter_norm_le, PolyaNeumann.dirichletTangentialDifferenceIter]

include c hc in
/-- A finite number of genuine derivative bounds can be made simultaneous.
No bound on a derivative of the Dirichlet solution is requested here. -/
theorem exists_dirichletTangentialDerivative_upto_bound A b k :
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

include A a b h M k hh hmargin in
/-- Uniform pointwise coefficient commutator control by lower differences
of the actual input, all at the original point z. -/
theorem norm_dirichletHigherCoefficientCommutator_le_of_derivative_bounds
     (hc : RealSmooth c)
    (hM : ∀ l : ℕ, l ≤ k → ∀ w ∈ smoothDirichletClosedHalfBox A b,
      ‖dirichletTangentialDerivative l c w‖ ≤ M)
    v  (hz : z ∈ smoothDirichletClosedHalfBox a b) :
    ‖dirichletHigherCoefficientCommutator h k c v z‖ ≤
      M * ∑ j ∈ Finset.range k, (k.choose j : ℝ) *
        ‖dirichletTangentialDifferenceIter h j v z‖ := by
  refine (norm_dirichletHigherCoefficientCommutator_le h k c v z).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hjk  := (Finset.mem_range.mp hj).le
  have hnat : ((k - j : ℕ) : ℝ) = (k : ℝ) - (j : ℝ) := Nat.cast_sub hjk
  have hm : (a + (j : ℝ) * h) + ((k - j : ℕ) : ℝ) * h ≤ A := by
    rw [hnat]
    nlinarith
  have hshift : z + (((j : ℝ) * h : ℝ) : ℂ) ∈
      smoothDirichletClosedHalfBox (a + (j : ℝ) * h) b := by
    have hjh : 0 ≤ (j : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh.le
    have hx := (abs_add_le z.re (j * h)).trans
      (add_le_add hz.1 (le_of_eq (abs_of_nonneg hjh)))
    simp_all [smoothDirichletClosedHalfBox, PolyaNeumann.smoothDirichletClosedHalfBox]
  have hcoef := dirichletTangentialDifferenceIter_norm_le (k - j) hh hm hc
    (hM (k - j) (Nat.sub_le _ _)) hshift
  calc
    _ ≤ (k.choose j) * (M * ‖dirichletTangentialDifferenceIter h j v z‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)) (Nat.cast_nonneg _)
    _ = _ := by ring

end


/-- The two genuine graph coefficients admit the simultaneous commutator
bound needed by the localized higher energy induction. -/
theorem exists_dirichletGraphHigherCommutator_bound 
    (hf : RealSmooth f) A b (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (a h : ℝ), 0 < h → a + (k : ℝ) * h ≤ A →
      ∀ (v : PlaneMap) (z : ℂ), z ∈ smoothDirichletClosedHalfBox a b →
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
  refine ⟨max M₀ M₁, hM₀.trans (le_max_left _ _), fun a h hh hmargin v z hz => ?_⟩
  constructor
  · grind [norm_dirichletHigherCoefficientCommutator_le_of_derivative_bounds, PolyaNeumann.dirichletGraphSlope, PolyaNeumann.dirichletTangentialDifferenceIter]
  · apply norm_dirichletHigherCoefficientCommutator_le_of_derivative_bounds
      k hh hmargin (contDiff_const.add (hd.pow 2)) _ v hz
    measurability

include c hc in
/-- Centered higher mean-value bound.  The kth quotient stays within
the same norm ball as the actual kth derivative on its entire stencil.
This is the genuine finite-difference ingredient in the later Fatou limit. -/
theorem dirichletTangentialDifferenceIter_centered_norm_le (k : ℕ)
     (hh : 0 < h) z C
    (hM : ∀ t ∈ Icc (0 : ℝ) ((k : ℝ) * h),
      ‖dirichletTangentialDerivative k c (z + (t : ℂ)) - C‖ ≤ M) :
    ‖dirichletTangentialDifferenceIter h k c z - C‖ ≤ M := by
  induction k generalizing c z with
  | zero =>
      simp_all
  | succ k ih =>
      let v : ComplexCurve := fun t =>
        dirichletTangentialDifferenceIter h k c (z + t) - t * C
      let dv : ComplexCurve := fun t =>
        dirichletTangentialDifferenceIter h k (dirD c 1) (z + t) - C
      have hd (t : ℝ) : HasDerivAt v (dv t) t := by
        have ht : HasDerivAt (fun s : ℝ => z + (s : ℂ)) (1 : ℂ) t :=
          (Complex.ofRealCLM.hasDerivAt).const_add z
        have hs := dirichletTangentialDifferenceIter_contDiff hc h k
        have hg := ((hs.differentiable (by simp) (z + t)).hasFDerivAt.comp_hasDerivAt
          t ht).sub ((Complex.ofRealCLM.hasDerivAt).mul_const C)
        have heq := congrFun (dirichletTangentialDifferenceIter_dirD_global hc h k 1)
          (z + t)
        have hgrad : fderiv ℝ (dirichletTangentialDifferenceIter h k c)
            (z + (t : ℂ)) 1 =
              dirichletTangentialDifferenceIter h k (dirD c 1) (z + (t : ℂ)) := heq
        simp   at hg
        change HasDerivAt
          (fun s : ℝ => dirichletTangentialDifferenceIter h k c (z + s) -
            s * C)
          (fderiv ℝ (dirichletTangentialDifferenceIter h k c) (z + t) 1 - C) t at hg
        rw [hgrad] at hg
        exact hg
      have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) h) : ‖dv t‖ ≤ M := by
        apply ih (dirichlet_dirD_contDiff hc 1) (z + t)
        intro s hs
        have hsum : t + s ∈ Icc (0 : ℝ) (((k + 1 : ℕ) : ℝ) * h) := by
          grind
        have heq : z + (t : ℂ) + (s : ℂ) = z + ((t + s : ℝ) : ℂ) := by
          push_cast
          ring
        simp_all only [dirichletTangentialDerivative_succ_right, PolyaNeumann.dirichletTangentialDerivative]
      have hp := (convex_Icc 0 h).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun t _ => (hd t).hasDerivWithinAt) hbound
        ((⟨le_rfl, hh.le⟩))
        ((⟨hh.le, le_rfl⟩))
      have hp' : ‖(v h - v 0) / (h : ℂ)‖ ≤ M := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
        apply (div_le_iff₀ hh).mpr
        simpa only [sub_zero, Real.norm_eq_abs, abs_of_pos hh] using hp
      have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
      have heq : (v h - v 0) / (h : ℂ) =
          dirichletTangentialDifferenceIter h (k + 1) c z - C := by
        simp only [v, Complex.ofReal_zero, zero_mul, sub_zero, add_zero,
          dirichletTangentialDifferenceIter.eq_2, dirichletTangentialDifference]
        field_simp [hhC]
        ring
      rw [heq] at hp'
      exact hp'

include c hc in
/-- Positive-step higher quotients genuinely converge to the actual
iterated directional derivative at every smooth point. -/
theorem dirichletTangentialDifferenceIter_tendsto k z :
    Tendsto (fun h : ℝ => dirichletTangentialDifferenceIter h k c z)
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (dirichletTangentialDerivative k c z)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hct : ContinuousAt (dirichletTangentialDerivative k c) z :=
    (dirichletTangentialDerivative_contDiff hc k).continuous.continuousAt
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hct (ε / 2) (by positivity)
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have hsmall : ∀ᶠ h : ℝ in 𝓝[Ioi (0 : ℝ)] 0, h < δ / ((k : ℝ) + 1) :=
    (eventually_lt_nhds (div_pos hδ hk)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hs
  have hhpos  := hh
  have hbound : ∀ t ∈ Icc (0 : ℝ) ((k : ℝ) * h),
      ‖dirichletTangentialDerivative k c (z + (t : ℂ)) -
        dirichletTangentialDerivative k c z‖ ≤ ε / 2 := by
    intro t ht
    have hkh : ((k : ℝ) + 1) * h < δ := by
      simpa  [mul_comm] using (lt_div_iff₀ hk).mp hs
    have htδ : t < δ := by nlinarith [ht.2]
    have hd : dist (z + (t : ℂ)) z < δ := by
      simpa  [abs_of_nonneg ht.1] using htδ
    exact (show ‖dirichletTangentialDerivative k c (z + t) -
        dirichletTangentialDerivative k c z‖ < ε / 2 by
      simpa  [dist_eq_norm] using hclose hd).le
  have hb := dirichletTangentialDifferenceIter_centered_norm_le hc k hhpos z
    (dirichletTangentialDerivative k c z) hbound
  rw [dist_eq_norm]
  exact hb.trans_lt (by linarith)

end


/-- Exact finite-stencil locality.  No value or derivative outside the
stencil can change an actual iterated quotient. -/
theorem dirichletTangentialDifferenceIter_eq_of_stencil
    h k c d z
    (heq : ∀ j : ℕ, j ≤ k →
      c (z + (((j : ℝ) * h : ℝ) : ℂ)) = d (z + (((j : ℝ) * h : ℝ) : ℂ))) :
    dirichletTangentialDifferenceIter h k c z =
      dirichletTangentialDifferenceIter h k d z := by
  induction k generalizing z with
  | zero => simpa using heq 0 le_rfl
  | succ k ih =>
      have h0 : ∀ j : ℕ, j ≤ k →
          c (z + (((j : ℝ) * h : ℝ) : ℂ)) =
            d (z + (((j : ℝ) * h : ℝ) : ℂ)) :=
        fun j hj => heq j (hj.trans (Nat.le_succ _))
      have h1 : ∀ j : ℕ, j ≤ k →
          c (z + (h : ℂ) + (((j : ℝ) * h : ℝ) : ℂ)) =
            d (z + (h : ℂ) + (((j : ℝ) * h : ℝ) : ℂ)) := by
        intro j hj
        have harg : z + (h : ℂ) + (((j : ℝ) * h : ℝ) : ℂ) =
            z + ((((j + 1 : ℕ) : ℝ) * h : ℝ) : ℂ) := by
          push_cast
          ring
        rw [harg]
        exact heq (j + 1) (Nat.succ_le_succ hj)
      change (dirichletTangentialDifferenceIter h k c (z + h) -
          dirichletTangentialDifferenceIter h k c z) / h =
        (dirichletTangentialDifferenceIter h k d (z + h) -
          dirichletTangentialDifferenceIter h k d z) / h
      rw [ih (z + h) h1, ih z h0]

theorem dirichletTangentialDerivative_eventuallyEq  
    (heq : c =ᶠ[𝓝 z] d) k :
    dirichletTangentialDerivative k c =ᶠ[𝓝 z] dirichletTangentialDerivative k d := (Nat.recAux heq (fun k ih => EventuallyEq.fun_comp (EventuallyEq.fderiv ih) fun A => A 1) k)

/-- The limit used by Fatou needs smoothness only in the actual open
interior.  A genuine local compact extension transfers its finite stencil
and its derivative germ; no boundary extension of a derivative is used. -/
theorem dirichletTangentialDifferenceIter_tendsto_of_contDiffOn
     (hU : IsOpen U) 
    (hc : RealSmoothOn c U) k  (hz : z ∈ U) :
    Tendsto (fun h : ℝ => dirichletTangentialDifferenceIter h k c z)
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (dirichletTangentialDerivative k c z)) := by
  obtain ⟨d, hd, hdc⟩ := exists_smooth_compact_extension
    (isCompact_singleton (x := z)) hU (singleton_subset_iff.mpr hz) hc
  have heq  := hdc z (mem_singleton z)
  have hall : ∀ᶠ h : ℝ in 𝓝 (0 : ℝ), ∀ j ∈ Finset.range (k + 1),
      d (z + (((j : ℝ) * h : ℝ) : ℂ)) = c (z + (((j : ℝ) * h : ℝ) : ℂ)) := by
    apply (Filter.eventually_all_finset _).mpr
    intro j _
    have ht : Tendsto (fun h : ℝ => z + (((j : ℝ) * h : ℝ) : ℂ))
        (𝓝 (0 : ℝ)) (𝓝 z) := by
      have hstencil : Continuous (fun h : ℝ => z + (((j : ℝ) * h : ℝ) : ℂ)) :=
        (continuous_const).add
          (Complex.continuous_ofReal.comp
            ((continuous_const).mul continuous_id))
      simpa   using hstencil.tendsto 0
    exact ht.eventually heq
  have hdiff : (fun h : ℝ => dirichletTangentialDifferenceIter h k d z) =ᶠ[𝓝 (0 : ℝ)]
      fun h => dirichletTangentialDifferenceIter h k c z := by
    filter_upwards [hall] with h hh
    simp_all [dirichletTangentialDifferenceIter_eq_of_stencil]
  have hlim := (dirichletTangentialDifferenceIter_tendsto hd.1 k z).congr'
    (hdiff.filter_mono nhdsWithin_le_nhds)
  rw [(dirichletTangentialDerivative_eventuallyEq heq k).self_of_nhds] at hlim
  exact hlim

end PolyaNeumann

end
