module

public import PDEFoundation.Ambient.EuclideanNorm
public import PDEFoundation.Geometry.Affine
public import Mathlib.Basic.Real.Pointwise
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import PDEFoundation.Geometry.EuclideanBall.Topology
public import PDEFoundation.Geometry.EuclideanBall.Basic
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public noncomputable section

namespace PDE
open scoped Pointwise

/-- Coordinatewise boundedness, compatible with the existing LIH API. -/
def IsBoundedDomain {d : ℕ} (U : Set (Vec d)) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∀ x ∈ U, ∀ i, |x i| ≤ R

/-- The minimal measurable bounded domain class used by Sobolev integration. -/
def IsSobolevRegularDomain {d : ℕ} (U : Set (Vec d)) : Prop :=
  MeasurableSet U ∧ IsBoundedDomain U

/-- Every pair of points in `U` is at Euclidean distance at most `D`. -/
def HasEuclideanDiameterLE {d : ℕ}
    (U : Set (Vec d)) (D : ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ U → ∀ ⦃y⦄, y ∈ U →
    vecEuclideanNorm (x - y) ≤ D

namespace IsSobolevRegularDomain

theorem measurableSet {d : ℕ} {U : Set (Vec d)}
    (hU : IsSobolevRegularDomain U) :
    MeasurableSet U :=
  hU.1

theorem isBoundedDomain {d : ℕ} {U : Set (Vec d)}
    (hU : IsSobolevRegularDomain U) :
    IsBoundedDomain U :=
  hU.2

end IsSobolevRegularDomain

namespace HasEuclideanDiameterLE




end HasEuclideanDiameterLE


theorem Bornology.IsBounded.isBoundedDomain {d : ℕ}
    {U : Set (Vec d)} (hU : Bornology.IsBounded U) :
    IsBoundedDomain U := by
  classical
  by_cases hd : d = 0
  · refine ⟨1, zero_lt_one, ?_⟩
    subst hd
    intro x hx i
    exact Fin.elim0 i
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
      intro y hy
      exact (hR y hy).trans (le_max_left _ _)
    choose R hRpos hR using hcoordBound
    let Rmax : ℝ := Finset.univ.sup' Finset.univ_nonempty R
    have hRmaxPos : 0 < Rmax := by
      let i₀ : Fin d := 0
      have hi₀ : i₀ ∈ (Finset.univ : Finset (Fin d)) := by
        simp
      have hle : R i₀ ≤ Rmax := by
        exact Finset.le_sup' (f := R) hi₀
      exact lt_of_lt_of_le (hRpos i₀) hle
    refine ⟨Rmax, hRmaxPos, ?_⟩
    intro x hx i
    have hRi : R i ≤ Rmax := by
      exact Finset.le_sup' (f := R) (Finset.mem_univ i)
    simpa [Real.norm_eq_abs] using! (hR i (x i) ⟨x, hx, rfl⟩).trans hRi

theorem IsBoundedDomain.isBounded {d : ℕ}
    {U : Set (Vec d)} (hU : IsBoundedDomain U) :
    Bornology.IsBounded U := by
  rcases hU with ⟨R, hRpos, hR⟩
  refine isBounded_iff_forall_norm_le.2 ⟨R, ?_⟩
  intro x hx
  refine (pi_norm_le_iff_of_nonneg hRpos.le).2 ?_
  intro i
  simpa [Real.norm_eq_abs] using hR x hx i

/-- Bounded open convex sets in the native ambient space.

This is definitionally compatible with LIH's existing predicate and therefore
does not encode nonemptiness. Results involving an integral mean add a
nonemptiness or positive-volume hypothesis at their theorem boundary. -/
def IsOpenBoundedConvexDomain {d : ℕ}
    (U : Set (Vec d)) : Prop :=
  IsOpen U ∧ IsBoundedDomain U ∧ Convex ℝ U

namespace IsOpenBoundedConvexDomain

theorem isOpen {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) :
    IsOpen U :=
  hU.1

theorem isBoundedDomain {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) :
    IsBoundedDomain U :=
  hU.2.1

theorem convex {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) :
    Convex ℝ U :=
  hU.2.2

theorem measurableSet {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) :
    MeasurableSet U :=
  hU.isOpen.measurableSet

theorem isSobolevRegularDomain {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) :
    IsSobolevRegularDomain U :=
  ⟨hU.measurableSet, hU.isBoundedDomain⟩

theorem translateSet {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (z : Vec d) :
    IsOpenBoundedConvexDomain (PDE.translateSet z U) := by
  refine ⟨?_, ?_, ?_⟩
  · have hopen :
        IsOpen ((fun x => x - z) ⁻¹' U) :=
      hU.isOpen.preimage (continuous_id.sub continuous_const)
    simpa [preimage_subRight_eq_translateSet] using hopen
  · rcases hU.isBoundedDomain with ⟨R, hRpos, hR⟩
    refine ⟨R + ‖z‖ + 1, ?_, ?_⟩
    · linarith [norm_nonneg z]
    · intro x hx i
      have hcoord :=
        hR (x - z) ((mem_translateSet_iff_sub_mem).1 hx) i
      have hzcoord : |z i| ≤ ‖z‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm z i
      have hxi : x i = (x - z) i + z i := by
        simp
      calc
        |x i| = |(x - z) i + z i| := by
          rw [hxi]
        _ ≤ |(x - z) i| + |z i| := abs_add_le _ _
        _ ≤ R + ‖z‖ := add_le_add hcoord hzcoord
        _ ≤ R + ‖z‖ + 1 := by
          linarith
  · have hconv :
        Convex ℝ ((fun x => x + -z) ⁻¹' U) := by
      simpa using hU.convex.translate_preimage_left (-z)
    simpa [preimage_addNeg_eq_translateSet] using hconv

/-- Positive scalar dilation preserves bounded open convex domains. -/
theorem smul_of_pos {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {r : ℝ} (hr : 0 < r) :
    IsOpenBoundedConvexDomain (r • U) := by
  refine ⟨hU.isOpen.smul₀ hr.ne', ?_, hU.convex.smul r⟩
  rcases hU.isBoundedDomain with ⟨R, hRpos, hR⟩
  refine ⟨r * R, mul_pos hr hRpos, ?_⟩
  intro x hx i
  rcases Set.mem_smul_set.mp hx with ⟨y, hy, rfl⟩
  simpa [abs_mul, abs_of_pos hr] using
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

