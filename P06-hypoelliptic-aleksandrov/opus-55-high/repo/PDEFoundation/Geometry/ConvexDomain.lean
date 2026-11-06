module

public import PDEFoundation.Geometry.Affine
public import PDEFoundation.Geometry.Domain
public import PDEFoundation.Geometry.EuclideanBall
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Bounded open convex domains

The shared domain class for mean-zero Poincaré and Sobolev--Poincaré
estimates. It contains explicit round balls and axis-aligned cubes.
-/

@[expose] public section

open scoped Pointwise

namespace PDE

variable {d : ℕ} {U : Set (Vec d)}

theorem Bornology.IsBounded.isBoundedDomain  (hU : Bornology.IsBounded U) :
    IsBoundedDomain U := by
  classical
  by_cases hd : d = 0
  · refine ⟨1, zero_lt_one, ?_⟩
    simp_all
  · have : NeZero d := ⟨hd⟩
    have hcoord :
        ∀ i : Fin d, Bornology.IsBounded (Function.eval i '' U) :=
      fun i => hU.image_eval i
    have hcoordBound :
        ∀ i : Fin d, ∃ R : ℝ, 0 < R ∧
          ∀ y ∈ Function.eval i '' U, ‖y‖ ≤ R := by
      intro i
      rcases isBounded_iff_forall_norm_le.1 (hcoord i) with
        ⟨R, hR⟩
      refine
        ⟨max R 1, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
      simp_all
    choose R hRpos hR using hcoordBound
    let Rmax : ℝ := Finset.univ.sup' Finset.univ_nonempty R
    have hRmaxPos : 0 < Rmax := by
      aesop
    refine ⟨Rmax, hRmaxPos, ?_⟩
    aesop

theorem IsBoundedDomain.isBounded  (hU : IsBoundedDomain U) :
    Bornology.IsBounded U := by
  rcases hU with ⟨R, hRpos, hR⟩
  refine isBounded_iff_forall_norm_le.2 ⟨R, ?_⟩
  intro x hx
  refine (pi_norm_le_iff_of_nonneg hRpos.le).2 ?_
  simp_all

/-- Bounded open convex sets in the native ambient space.

This is definitionally compatible with LIH's existing predicate and therefore
does not encode nonemptiness. Results involving an integral mean add a
nonemptiness or positive-volume hypothesis at their theorem boundary. -/
def IsOpenBoundedConvexDomain {d : ℕ}
    (U : Set (Vec d)) : Prop :=
  IsOpen U ∧ IsBoundedDomain U ∧ Convex ℝ U

namespace IsOpenBoundedConvexDomain

variable {d : ℕ} {U : Set (Vec d)}

theorem isOpen 
    (hU : IsOpenBoundedConvexDomain U) :
    IsOpen U :=
  hU.1

theorem isBoundedDomain 
    (hU : IsOpenBoundedConvexDomain U) :
    IsBoundedDomain U :=
  hU.2.1

theorem convex 
    (hU : IsOpenBoundedConvexDomain U) :
    Convex ℝ U :=
  hU.2.2

theorem measurableSet 
    (hU : IsOpenBoundedConvexDomain U) :
    MeasurableSet U :=
  hU.isOpen.measurableSet

theorem isSobolevRegularDomain 
    (hU : IsOpenBoundedConvexDomain U) :
    IsSobolevRegularDomain U :=
  ⟨hU.measurableSet, hU.isBoundedDomain⟩

theorem translateSet 
    (hU : IsOpenBoundedConvexDomain U) (z : Vec d) :
    IsOpenBoundedConvexDomain (PDE.translateSet z U) := by
  refine ⟨?_, ?_, ?_⟩
  · have hopen :
        IsOpen ((fun x : Vec d => x - z) ⁻¹' U) :=
      hU.isOpen.preimage (continuous_id.sub continuous_const)
    simpa [preimage_subRight_eq_translateSet] using hopen
  · rcases hU.isBoundedDomain with ⟨R, hRpos, hR⟩
    refine ⟨R + ‖z‖ + 1, ?_, ?_⟩
    · positivity
    · intro x hx i
      have hxpre :
          x - z ∈ U :=
        (mem_translateSet_iff_sub_mem).1 hx
      have hcoord : |(x - z) i| ≤ R :=
        hR (x - z) hxpre i
      have hzcoord : |z i| ≤ ‖z‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm z i
      have hxi : x i = (x - z) i + z i := by
        simp
      grind
  · have hconv :
        Convex ℝ ((fun x : Vec d => x + -z) ⁻¹' U) := by
      simpa using hU.convex.translate_preimage_left _
    simpa [preimage_addNeg_eq_translateSet] using hconv

/-- Positive scalar dilation preserves bounded open convex domains. -/
theorem smul_of_pos 
    (hU : IsOpenBoundedConvexDomain U) {r : ℝ} (hr : 0 < r) :
    IsOpenBoundedConvexDomain (r • U) := by
  refine ⟨hU.isOpen.smul₀ hr.ne', ?_, hU.convex.smul r⟩
  rcases hU.isBoundedDomain with ⟨R, hRpos, hR⟩
  refine ⟨r * R, mul_pos hr hRpos, ?_⟩
  intro x hx i
  rcases Set.mem_smul_set.mp hx with ⟨y, hy, rfl⟩
  simpa only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hr] using
    mul_le_mul_of_nonneg_left (hR y hy i) hr.le

end IsOpenBoundedConvexDomain

theorem isOpenBoundedConvexDomain_euclideanBall {d : ℕ}
    (x : Vec d) {R : ℝ} (hR : 0 < R) :
    IsOpenBoundedConvexDomain (euclideanBall x R) := by
  refine ⟨isOpen_euclideanBall x R, ?_, convex_euclideanBall x R⟩
  exact Bornology.IsBounded.isBoundedDomain <|
    Metric.isBounded_ball.subset
      (euclideanBall_subset_supBall hR)

end PDE
