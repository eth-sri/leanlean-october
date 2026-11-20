module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import GS.Core
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.GroupTheory.GroupAction.Quotient
public import GS.CompactFibres
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Basic

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section

/-!
# A horizontal complement for the orbit differential

All finite-dimensional choices in this file are constructed from complements
of submodules. The horizontal restriction is injective and has a continuous
linear left inverse defined on the full ambient matrix space. No hypothesis
excluding overlap is used.
-/

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GS.OverlapGeometry

section Linear
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

def horizontalComplement (D : E →L[ℝ] F) : Submodule ℝ E :=
  Classical.choose (LinearMap.ker D.toLinearMap).exists_isCompl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem horizontalComplement_isCompl (D : E →L[ℝ] F) :
    IsCompl (horizontalComplement D) (LinearMap.ker D.toLinearMap) :=
  (Classical.choose_spec (LinearMap.ker D.toLinearMap).exists_isCompl).symm

def complementKernelEquiv (D : E →L[ℝ] F) :
    (horizontalComplement D × (LinearMap.ker D.toLinearMap)) ≃L[ℝ] E :=
  (Submodule.prodEquivOfIsCompl _ _ (horizontalComplement_isCompl D)).toContinuousLinearEquiv

def horizontalRestriction (D : E →L[ℝ] F) : horizontalComplement D →L[ℝ] F :=
  D.comp (horizontalComplement D).subtypeL

theorem horizontalRestriction_injective (D : E →L[ℝ] F) :
    Function.Injective (horizontalRestriction D) := by
  intro x y h
  exact (D.toLinearMap.kerComplementEquivRange (horizontalComplement_isCompl D)).injective (Subtype.ext h)

theorem horizontalRestriction_range (D : E →L[ℝ] F) : (horizontalRestriction D).range = D.range := by
  change LinearMap.range (D.toLinearMap.comp (horizontalComplement D).subtype) = _
  rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.range_eq_map]
  exact le_antisymm (Submodule.map_mono le_top)
    (D.toLinearMap.map_le_map_iff.mpr (by rw [(horizontalComplement_isCompl D).sup_eq_top]))

end Linear

end GS.OverlapGeometry

end

section

/-!
# An atlas from ambient smooth slices

This file constructs manifold charts on the inherited topology of a subset of
a real normed space. The input consists of concrete ambient coordinate maps and
parametrizations, with their local inverse identities and open domains. No
manifold or quotient topology on the subset is assumed.

The application to a matrix orbit must independently construct the slice data,
including the relative openness of each slice image.
-/

open Set Filter
open scoped Topology Manifold

namespace GS.OverlapGeometry

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A slice is a parametrized patch with a smooth ambient left inverse.
Its source is the image of its parameter domain in the inherited topology. -/
structure SmoothSlice (S : Set F) where
  target : Set E
  coordinates : F → E
  parametrization : E → S
  open_target : IsOpen target
  open_source : IsOpen (parametrization '' target)
  parametrization_smooth : ContDiff ℝ ⊤ (fun x => (parametrization x).val)
  coordinates_smooth_at : ∀ x ∈ target, ContDiffAt ℝ ⊤ coordinates (parametrization x).val
  right_inverse : ∀ x ∈ target, coordinates (parametrization x).val = x

namespace SmoothSlice

variable {S : Set F} (s : SmoothSlice (E := E) S)

abbrev source := s.parametrization '' s.target

theorem coordinates_smooth (y : S) (hy : y ∈ s.source) : ContDiffAt ℝ ⊤ s.coordinates y.val := by
  obtain ⟨x,hx,rfl⟩ := hy
  exact s.coordinates_smooth_at x hx

theorem left_inverse (y : S) (hy : y ∈ s.source) : s.parametrization (s.coordinates y.val) = y := by
  obtain ⟨x,hx,rfl⟩ := hy
  rw [s.right_inverse x hx]

/-- The local homeomorphism associated with a slice. -/
def chart : OpenPartialHomeomorph S E where
  toFun := fun y => s.coordinates y.val
  invFun := s.parametrization
  source := s.source
  target := s.target
  map_source' _ := by rintro ⟨x,hx,rfl⟩; rwa [s.right_inverse x hx]
  map_target' x hx := ⟨x,hx,rfl⟩
  left_inv' := s.left_inverse
  right_inv' := s.right_inverse
  open_source := s.open_source
  open_target := s.open_target
  continuousOn_toFun := by
    intro y hy
    exact ((s.coordinates_smooth y hy).continuousAt.comp
      continuous_subtype_val.continuousAt).continuousWithinAt
  continuousOn_invFun := by
    exact s.parametrization_smooth.continuous.subtype_mk
      (fun x => (s.parametrization x).property) |>.continuousOn

/-- The transition is the composition of the ambient coordinate map of the
second slice with the smooth parametrization of the first slice. -/
theorem transition_smooth (s t : SmoothSlice (E := E) S) :
    ContDiffOn ℝ ⊤ (s.chart.symm.trans t.chart)
      (s.chart.symm.trans t.chart).source := by
  intro x hx
  change x ∈ s.target ∧ s.parametrization x ∈ t.source at hx
  exact ((t.coordinates_smooth (s.parametrization x) hx.2).comp x
    s.parametrization_smooth.contDiffAt).contDiffWithinAt

end SmoothSlice

/-- The atlas obtained from one concrete slice around each point. -/
def sliceChartedSpace {S : Set F} (s : S → SmoothSlice (E := E) S)
    (covers : ∀ x : S, x ∈ (s x).source) : ChartedSpace E S where
  atlas := Set.range (fun x => (s x).chart)
  chartAt x := (s x).chart
  mem_chart_source x := covers x
  chart_mem_atlas x := ⟨x, rfl⟩

/-- Smoothness of the atlas constructed from slices. In particular, this
construction does not assume an existing manifold structure on the subset. -/
theorem slice_isManifold {S : Set F} (s : S → SmoothSlice (E := E) S)
    (covers : ∀ x : S, x ∈ (s x).source) :
    letI := sliceChartedSpace s covers
    IsManifold (𝓘(ℝ, E)) ⊤ S := by
  letI := sliceChartedSpace s covers
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨x,rfl⟩ ⟨y,rfl⟩
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ] using (s x).transition_smooth (s y)

/-- The inclusion of the subset with its constructed atlas is genuinely
manifold-smooth. -/
theorem slice_val_contMDiff {S : Set F} (s : S → SmoothSlice (E := E) S)
    (covers : ∀ x : S, x ∈ (s x).source) :
    letI := sliceChartedSpace s covers
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ⊤ (fun x : S => x.val) := by
  letI := sliceChartedSpace s covers
  intro x
  rw [contMDiffAt_iff]
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  change ContDiffWithinAt ℝ ⊤ (fun y : E => ((s x).parametrization y).val)
    (Set.range (id : E → E)) ((s x).coordinates x.val)
  exact (s x).parametrization_smooth.contDiffAt.contDiffWithinAt

/-- The actual manifold derivative of the inclusion is the derivative of the
preferred inverse chart. -/
theorem slice_val_mfderiv_eq {S : Set F} (s : S → SmoothSlice (E := E) S)
    (covers : ∀ x : S, x ∈ (s x).source) (x : S) :
    letI := sliceChartedSpace s covers
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) (fun y : S => y.val) x =
      fderiv ℝ (fun y => ((s x).parametrization y).val) ((s x).coordinates x.val) := by
  letI := sliceChartedSpace s covers
  have hd : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) (fun y : S => y.val) x :=
    (slice_val_contMDiff s covers x).mdifferentiableAt (by simp)
  unfold mfderiv
  aesop

end GS.OverlapGeometry

end

section

/-!
# Manifold-valued sources for the ambient slice criterion

The source may be any charted manifold, in particular an actual tangent
bundle. Smoothness into the slice manifold is equivalent to smoothness of
the ambient realization. The subset keeps its inherited topology.
-/

open scoped Topology Manifold

namespace GS.OverlapGeometry

variable {E F G H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]

theorem slice_contMDiff_of_ambient {S : Set F}
    (s : S → SmoothSlice (E := E) S) (covers : ∀ x : S, x ∈ (s x).source)
    (I : ModelWithCorners ℝ G H) (f : M → S)
    (hf : ContMDiff I (𝓘(ℝ, F)) ⊤ (fun x => (f x).val)) :
    letI := sliceChartedSpace s covers
    ContMDiff I (𝓘(ℝ, E)) ⊤ f := by
  letI := sliceChartedSpace s covers
  have hc : Continuous f := hf.continuous.subtype_mk (fun x => (f x).property)
  intro x
  rw [contMDiffAt_iff_target]
  refine ⟨hc.continuousAt, ?_⟩
  change ContMDiffAt I (𝓘(ℝ, E)) ⊤
    (fun y => (s (f x)).coordinates (f y).val) x
  exact ContDiffAt.comp_contMDiffAt
    (I := I) (f := fun y : M => (f y).val) (g := (s (f x)).coordinates)
    ((s (f x)).coordinates_smooth (f x) (covers (f x))) (hf x)

end GS.OverlapGeometry

end
