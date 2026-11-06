module

public import GS.GlobalGeometry.SharedAlgebra
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Abel
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Analysis.InnerProductSpace.ProdL2

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS InnerProductSpace Filter Set
open scoped BigOperators Topology ComplexOrder Manifold ContDiff

namespace GS.OverlapGeometry

theorem isOpen_slice_image_of_productChart
    {H K M X : Type*} [TopologicalSpace H] [TopologicalSpace K]
    [TopologicalSpace M] [TopologicalSpace X]
    (e : OpenPartialHomeomorph (H × K) M) (q : M → X) (p : H → X)
    (hq : IsOpenMap q)
    (heq : ∀ z ∈ e.source, q (e z) = p z.1)
    (U : Set H) (hU : IsOpen U)
    (hcover : ∀ h ∈ U, ∃ k : K, (h, k) ∈ e.source) :
    IsOpen (p '' U) := by
  let V : Set (H × K) := e.source ∩ Prod.fst ⁻¹' U
  have hopen : IsOpen (q '' (e '' V)) :=
    hq _ (e.isOpen_image_of_subset_source (e.open_source.inter (hU.preimage continuous_fst)) inter_subset_left)
  have himage : q '' (e '' V) = p '' U := by
    ext x; refine ⟨?_, ?_⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩; exact ⟨z.1, hz.2, (heq z hz.1).symm⟩
    · rintro ⟨h, hh, rfl⟩; obtain ⟨k, hk⟩ := hcover h hh
      exact ⟨e (h, k), ⟨(h, k), ⟨hk, hh⟩, rfl⟩, heq (h, k) hk⟩
  rwa [himage] at hopen

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

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem horizontalRestriction_injective (D : E →L[ℝ] F) :
    Function.Injective (horizontalRestriction D) := by
  intro x y h
  apply Subtype.ext; apply sub_eq_zero.mp
  apply Submodule.disjoint_def.mp (horizontalComplement_isCompl D).disjoint
    ((x : E) - (y : E)) ((horizontalComplement D).sub_mem x.property y.property)
  change D ((x : E) - (y : E)) = 0
  change D (x : E) = D (y : E) at h
  rw [map_sub, h, sub_self]

def horizontalRangeComplement (D : E →L[ℝ] F) : Submodule ℝ F :=
  Classical.choose (LinearMap.range (horizontalRestriction D).toLinearMap).exists_isCompl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem horizontalRangeComplement_isCompl (D : E →L[ℝ] F) :
    IsCompl (LinearMap.range (horizontalRestriction D).toLinearMap) (horizontalRangeComplement D) :=
  Classical.choose_spec (LinearMap.range (horizontalRestriction D).toLinearMap).exists_isCompl

def horizontalLeftInverse (D : E →L[ℝ] F) : F →L[ℝ] horizontalComplement D :=
  (LinearMap.linearProjOfIsCompl (horizontalRangeComplement D)
    (horizontalRestriction D).toLinearMap (horizontalRestriction_injective D)
    (horizontalRangeComplement_isCompl D)).toContinuousLinearMap

@[simp] theorem horizontalLeftInverse_apply (D : E →L[ℝ] F)
    (x : horizontalComplement D) : horizontalLeftInverse D (D x) = x :=
  LinearMap.linearProjOfIsCompl_apply_left _ _ _ _ x

theorem horizontalLeftInverse_comp (D : E →L[ℝ] F) :
    (horizontalLeftInverse D).comp (horizontalRestriction D) =
      ContinuousLinearMap.id ℝ (horizontalComplement D) :=
  ContinuousLinearMap.ext (horizontalLeftInverse_apply D)

end Linear

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

structure SmoothSlice (S : Set F) where
  source : Set S
  target : Set E
  coordinates : F → E
  parametrization : E → S
  open_source : IsOpen source
  open_target : IsOpen target
  coordinates_smooth : ∀ y ∈ source, ContDiffAt ℝ ⊤ coordinates y.val
  parametrization_smooth : ContDiff ℝ ⊤ (fun x => (parametrization x).val)
  maps_source : ∀ y ∈ source, coordinates y.val ∈ target
  maps_target : ∀ x ∈ target, parametrization x ∈ source
  left_inverse : ∀ y ∈ source, parametrization (coordinates y.val) = y
  right_inverse : ∀ x ∈ target, coordinates (parametrization x).val = x

namespace SmoothSlice

variable {S : Set F} (s : SmoothSlice (E := E) S)

def chart : OpenPartialHomeomorph S E where
  toFun y := s.coordinates y.val
  invFun := s.parametrization
  source := s.source
  target := s.target
  map_source' := s.maps_source
  map_target' := s.maps_target
  left_inv' := s.left_inverse
  right_inv' := s.right_inverse
  open_source := s.open_source
  open_target := s.open_target
  continuousOn_toFun y hy :=
    ((s.coordinates_smooth y hy).continuousAt.comp continuous_subtype_val.continuousAt).continuousWithinAt
  continuousOn_invFun :=
    (s.parametrization_smooth.continuous.subtype_mk fun x => (s.parametrization x).property).continuousOn

theorem transition_smooth (s t : SmoothSlice (E := E) S) :
    ContDiffOn ℝ ⊤ (s.chart.symm.trans t.chart)
      (s.chart.symm.trans t.chart).source := fun x hx =>
  ((t.coordinates_smooth (s.parametrization x) hx.2).comp x s.parametrization_smooth.contDiffAt).contDiffWithinAt

theorem parametrization_fderiv_injective (x : E) (hx : x ∈ s.target) :
    Function.Injective (fderiv ℝ (fun y => (s.parametrization y).val) x) := by
  have hp := (s.parametrization_smooth.differentiable (by simp) x).hasFDerivAt
  have hc := ((s.coordinates_smooth _ (s.maps_target x hx)).differentiableAt (by simp)).hasFDerivAt
  have he : (fun y => s.coordinates (s.parametrization y).val) =ᶠ[𝓝 x] (id : E → E) := by
    filter_upwards [s.open_target.mem_nhds hx] with y hy; exact s.right_inverse y hy
  have hd := ((hc.comp x hp).congr_of_eventuallyEq he.symm).unique (hasFDerivAt_id x)
  intro v w hvw
  have hvw' := congrArg (fderiv ℝ s.coordinates (s.parametrization x).val) hvw
  change ((fderiv ℝ s.coordinates (s.parametrization x).val).comp
    (fderiv ℝ (fun y => (s.parametrization y).val) x)) v =
    ((fderiv ℝ s.coordinates (s.parametrization x).val).comp
      (fderiv ℝ (fun y => (s.parametrization y).val) x)) w at hvw'
  simpa only [hd, ContinuousLinearMap.id_apply] using hvw'

end SmoothSlice

def sliceChartedSpace {S : Set F} (s : S → SmoothSlice (E := E) S)
    (covers : ∀ x : S, x ∈ (s x).source) : ChartedSpace E S where
  atlas := Set.range (fun x => (s x).chart)
  chartAt x := (s x).chart
  mem_chart_source x := covers x
  chart_mem_atlas x := ⟨x, rfl⟩

theorem slice_isManifold {S : Set F} (s : S → SmoothSlice (E := E) S)
    (covers : ∀ x : S, x ∈ (s x).source) :
    letI := sliceChartedSpace s covers
    IsManifold (𝓘(ℝ, E)) ⊤ S := by
  letI := sliceChartedSpace s covers
  apply isManifold_of_contDiffOn
  rintro e e' ⟨x, rfl⟩ ⟨y, rfl⟩
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ] using (s x).transition_smooth (s y)

theorem slice_val_contMDiff {S : Set F} (s : S → SmoothSlice (E := E) S)
    (covers : ∀ x : S, x ∈ (s x).source) :
    letI := sliceChartedSpace s covers
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ⊤ (fun x : S => x.val) := by
  letI := sliceChartedSpace s covers
  intro x
  rw [contMDiffAt_iff]
  exact ⟨continuous_subtype_val.continuousAt, (s x).parametrization_smooth.contDiffAt.contDiffWithinAt⟩

theorem slice_val_mfderiv_eq {S : Set F} (s : S → SmoothSlice (E := E) S)
    (covers : ∀ x : S, x ∈ (s x).source) (x : S) :
    letI := sliceChartedSpace s covers
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) (fun y : S => y.val) x =
      fderiv ℝ (fun y => ((s x).parametrization y).val) ((s x).coordinates x.val) := by
  letI := sliceChartedSpace s covers
  have hd : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) (fun y : S => y.val) x :=
    (slice_val_contMDiff s covers x).mdifferentiableAt (by simp)
  unfold mfderiv; rw [if_pos hd]
  change fderivWithin ℝ (fun y => ((s x).parametrization y).val)
    (Set.range (id : E → E)) ((s x).coordinates x.val) = _
  simp only [Set.range_id, fderivWithin_univ]

theorem slice_val_mfderiv_injective {S : Set F} (s : S → SmoothSlice (E := E) S)
    (covers : ∀ x : S, x ∈ (s x).source) (x : S) :
    letI := sliceChartedSpace s covers
    Function.Injective (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) (fun y : S => y.val) x) := by
  let := sliceChartedSpace s covers
  rw [slice_val_mfderiv_eq s covers x]
  exact (s x).parametrization_fderiv_injective _ ((s x).maps_source x (covers x))

variable {G H M : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]

theorem slice_contMDiff_of_ambient {S : Set F}
    (s : S → SmoothSlice (E := E) S) (covers : ∀ x : S, x ∈ (s x).source)
    (I : ModelWithCorners ℝ G H) (f : M → S)
    (hf : ContMDiff I (𝓘(ℝ, F)) ⊤ (fun x => (f x).val)) :
    letI := sliceChartedSpace s covers
    ContMDiff I (𝓘(ℝ, E)) ⊤ f := by
  let := sliceChartedSpace s covers
  have hc : Continuous f := hf.continuous.subtype_mk fun x => (f x).property
  intro x
  rw [contMDiffAt_iff_target]
  exact ⟨hc.continuousAt, ContDiffAt.comp_contMDiffAt
    (I := I) (f := fun y : M => (f y).val) (g := (s (f x)).coordinates)
    ((s (f x)).coordinates_smooth (f x) (covers (f x))) (hf x)⟩

theorem slice_contMDiff_iff_ambient {S : Set F}
    (s : S → SmoothSlice (E := E) S) (covers : ∀ x : S, x ∈ (s x).source)
    (I : ModelWithCorners ℝ G H) (f : M → S) :
    letI := sliceChartedSpace s covers
    ContMDiff I (𝓘(ℝ, E)) ⊤ f ↔
      ContMDiff I (𝓘(ℝ, F)) ⊤ (fun x => (f x).val) := by
  let := sliceChartedSpace s covers
  exact ⟨fun hf => (slice_val_contMDiff s covers).comp hf,
    slice_contMDiff_of_ambient s covers I f⟩

theorem slice_contMDiff_iff_contDiff {S : Set F}
    (s : S → SmoothSlice (E := E) S) (covers : ∀ x : S, x ∈ (s x).source)
    (f : G → S) :
    letI := sliceChartedSpace s covers
    ContMDiff (𝓘(ℝ, G)) (𝓘(ℝ, E)) ⊤ f ↔
      ContDiff ℝ ⊤ (fun x => (f x).val) :=
  (slice_contMDiff_iff_ambient s covers (𝓘(ℝ, G)) f).trans contMDiff_iff_contDiff

end GS.OverlapGeometry

namespace GS.Extensions

variable {E F H M V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {S : Set F}
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def smoothSliceOfParametrization (p : E → S) (c : F → E) (U : Set E)
    (hp : ContDiff ℝ ⊤ (fun x => (p x).val))
    (hU : IsOpen U) (himage : IsOpen (p '' U))
    (hc : ∀ x ∈ U, ContDiffAt ℝ ⊤ c (p x).val)
    (hi : ∀ x ∈ U, c (p x).val = x) :
    GS.OverlapGeometry.SmoothSlice (E := E) S where
  source := p '' U
  target := U
  coordinates := c
  parametrization := p
  open_source := himage
  open_target := hU
  coordinates_smooth := by rintro _ ⟨x, hx, rfl⟩; exact hc x hx
  parametrization_smooth := hp
  maps_source := by rintro _ ⟨x, hx, rfl⟩; rw [hi x hx]; exact hx
  maps_target x hx := ⟨x, hx, rfl⟩
  left_inverse := by rintro _ ⟨x, hx, rfl⟩; rw [hi x hx]
  right_inverse := hi

def translateSmoothSlice (s : GS.OverlapGeometry.SmoothSlice (E := E) S)
    (f g : F → F) (T U : S → S)
    (hT : ∀ x, (T x).val = f x.val) (hU : ∀ x, (U x).val = g x.val)
    (hTU : ∀ x, T (U x) = x) (hUT : ∀ x, U (T x) = x)
    (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) (hUc : Continuous U) :
    GS.OverlapGeometry.SmoothSlice (E := E) S where
  source := U ⁻¹' s.source
  target := s.target
  coordinates A := s.coordinates (g A)
  parametrization h := T (s.parametrization h)
  open_source := s.open_source.preimage hUc
  open_target := s.open_target
  coordinates_smooth X hX := by
    have hc := s.coordinates_smooth (U X) hX; rw [hU] at hc
    exact hc.comp X.val hg.contDiffAt
  parametrization_smooth := by simpa only [hT, Function.comp_def] using hf.comp s.parametrization_smooth
  maps_source X hX := by simpa only [hU] using s.maps_source (U X) hX
  maps_target h hh := by change U (T (s.parametrization h)) ∈ s.source; rw [hUT]; exact s.maps_target h hh
  left_inverse X hX := by simpa only [hU, hTU] using congrArg T (s.left_inverse (U X) hX)
  right_inverse h hh := by rw [← hU, hUT]; exact s.right_inverse h hh

variable (I : ModelWithCorners ℝ E H)

theorem mfderiv_retraction_precompose_linear
    (R : E → M) (L : V →L[ℝ] E)
    (hR : MDifferentiableAt (𝓘(ℝ, E)) I R 0)
    (hD : mfderiv (𝓘(ℝ, E)) I R 0 = ContinuousLinearMap.id ℝ E)
    (v : V) :
    mfderiv (𝓘(ℝ, V)) I (R ∘ L) 0 v = L v := by
  have h := mfderiv_comp_apply_of_eq (0 : V) hR L.mdifferentiableAt (map_zero L) v
  simpa only [TangentSpace, ContinuousLinearMap.mfderiv_eq, hD, ContinuousLinearMap.id_apply] using h

theorem mfderiv_partial_right (F : M × V → M) (x : M)
    (hF : MDifferentiableAt (I.prod (𝓘(ℝ, V))) I F (x, 0)) (v : V) :
    mfderiv (𝓘(ℝ, V)) I (fun w : V => F (x, w)) 0 v =
      mfderiv (I.prod (𝓘(ℝ, V))) I F (x, 0) (0, v) := by
  have he : MDifferentiableAt (𝓘(ℝ, V)) (I.prod (𝓘(ℝ, V))) (fun w : V => (x, w)) 0 :=
    mdifferentiableAt_const.prodMk mdifferentiableAt_id
  simpa only [TangentSpace, mfderiv_prod_right, ContinuousLinearMap.inr_apply, Function.comp_def] using
    mfderiv_comp_apply_of_eq (0 : V) hF he rfl v

theorem contMDiff_vertical_input [IsManifold I ⊤ M] :
    ContMDiff (I.prod (𝓘(ℝ, V))) (I.prod (𝓘(ℝ, V))).tangent ⊤
      (fun p : M × V =>
        (⟨(p.1, 0), (0, p.2)⟩ : TangentBundle (I.prod (𝓘(ℝ, V))) (M × V))) := by
  have hzero : ContMDiff (I.prod (𝓘(ℝ, V))) I.tangent ⊤
      (fun p : M × V => (⟨p.1, 0⟩ : TangentBundle I M)) :=
    (Bundle.contMDiff_zeroSection ℝ (TangentSpace I)).comp contMDiff_fst
  have hvector : ContMDiff (I.prod (𝓘(ℝ, V))) (𝓘(ℝ, V)).tangent ⊤
      (fun p : M × V => (⟨0, p.2⟩ : TangentBundle (𝓘(ℝ, V)) V)) := by
    have hp : ContMDiff (M' := ModelProd V V)
        (I.prod (𝓘(ℝ, V))) ((𝓘(ℝ, V)).prod (𝓘(ℝ, V))) ⊤
        (fun p : M × V => ((0, p.2) : ModelProd V V)) := by
      rw [← modelWithCornersSelf_prod]
      exact contMDiff_const.prodMk_space contMDiff_snd
    exact (contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := 𝓘(ℝ, V))).comp hp
  exact (contMDiff_equivTangentBundleProd_symm
    (I := I) (I' := 𝓘(ℝ, V)) (M := M) (M' := V)).comp (hzero.prodMk hvector)

end GS.Extensions

open GS.OverlapGeometry
namespace GS.SharedGeometry
section
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ}

/-- A valid complete-block layout and arbitrary within-layer sharing labels.
Unused labels are allowed; different layers have independent patterns. -/
structure Pattern (𝕂 : Type) (n : ℕ) where
  size : ℕ
  positive : 0 < size
  divides : size ∣ n
  label : ℕ → ℕ

namespace Pattern

def block (s : Pattern 𝕂 n) (i : Fin n) : ℕ := i.val / s.size

/-- Actual entry equalities define a subgroup of the already constructed
block unitary group. -/
def subgroup (s : Pattern 𝕂 n) : Subgroup (BlockK 𝕂 s.block) where
  carrier := {A | KTiedEntries s.size s.label A.val}
  one_mem' := TiedEntries_one s.size s.label
  mul_mem' := by
    intro A B hA hB
    exact TiedEntries_mul s.positive s.divides A.property.1 B.property.1 hA hB
  inv_mem' := by
    intro A hA
    exact TiedEntries_conjTranspose hA

theorem subgroup_isClosed (s : Pattern 𝕂 n) :
    IsClosed (s.subgroup : Set (BlockK 𝕂 s.block)) :=
  (isClosed_tiedEntries s.size s.label).preimage continuous_subtype_val

end Pattern

abbrev Factor (s : Pattern 𝕂 n) := ↥s.subgroup
abbrev Generator (s : Pattern 𝕂 n) := ↥(ksharedSkewSpace (𝕂 := 𝕂) (n := n) s.size s.label)

variable {s right left : Pattern 𝕂 n}

def fmat (A : Factor s) : KMat 𝕂 n := A.val.val

@[simp] theorem fmat_one : fmat (1 : Factor s) = 1 := rfl

theorem fmat_shared (A : Factor s) : KSharedFactor s.size s.label (fmat A) :=
  ⟨A.val.property.1, A.val.property.2, A.property⟩

theorem fmat_unitary (A : Factor s) : KUnitary (fmat A) := A.val.property.2

theorem fmat_injective : Function.Injective (fmat : Factor s → KMat 𝕂 n) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

theorem continuous_fmat : Continuous (fmat : Factor s → KMat 𝕂 n) :=
  continuous_subtype_val.comp continuous_subtype_val

def ofMatrix (A : KMat 𝕂 n) (hA : KSharedFactor s.size s.label A) : Factor s :=
  ⟨⟨A, hA.1, hA.2.1⟩, hA.2.2⟩

@[simp] theorem fmat_ofMatrix (A : KMat 𝕂 n) (hA : KSharedFactor s.size s.label A) :
    fmat (ofMatrix A hA) = A := rfl

instance factorCompactSpace (s : Pattern 𝕂 n) : CompactSpace (Factor s) :=
  isCompact_iff_compactSpace.mp s.subgroup_isClosed.isCompact

/-- The two layers can use unrelated sharing maps and block sizes. -/
abbrev Factors (right left : Pattern 𝕂 n) := Factor left × Factor right
set_option hygiene false in
scoped notation "FG" => Factors right left



/-- A total continuous linear extension of the shared chart coordinates. -/
def modelProjection (s : Pattern 𝕂 n) : KMat 𝕂 n →L[ℝ] Generator s :=
  ({ toFun := fun A => ⟨kfrobProjection (ksharedSkewSpace s.size s.label) A,
        kfrobProjection_mem _ _⟩
     map_add' := by
       intro A B
       apply Subtype.ext
       exact map_add _ A B
     map_smul' := by
       intro a A
       apply Subtype.ext
       exact map_smul _ a A } : KMat 𝕂 n →ₗ[ℝ] Generator s).toContinuousLinearMap


theorem modelProjection_val_of_mem (s : Pattern 𝕂 n) (A : KMat 𝕂 n)
    (hA : A ∈ ksharedSkewSpace s.size s.label) : (modelProjection s A).val = A :=
  kfrobProjection_of_mem _ _ hA

@[simp] theorem modelProjection_inclusion (C : Generator s) :
    modelProjection s C.val = C := by
  apply Subtype.ext
  exact modelProjection_val_of_mem s C.val C.property

/-- Open neighbourhood of Q inside the inherited shared-factor topology. -/
def factorSource (Q : Factor s) : Set (Factor s) :=
  {U | kadmissible ((fmat Q)ᴴ * fmat U)}

def factorCoordinates (Q : Factor s) (A : KMat 𝕂 n) : Generator s :=
  modelProjection s (kcayley ((fmat Q)ᴴ * A))

/-- All shared skew coordinates reconstruct valid shared unitary factors. -/
def reconstruct (Q : Factor s) (C : Generator s) : Factor s :=
  Q * ofMatrix (kcayley C.val) (cayley_shared s.positive s.divides C.property)

@[simp] theorem reconstruct_matrix (Q : Factor s) (C : Generator s) :
    fmat (reconstruct Q C) = fmat Q * kcayley C.val := rfl

theorem factorSource_open (Q : Factor s) : IsOpen (factorSource Q) :=
  admissible_open.preimage
    (kcontinuous_matrix_product continuous_const continuous_fmat)

@[simp] theorem base_mem_factorSource (Q : Factor s) : Q ∈ factorSource Q := by
  change kadmissible ((fmat Q)ᴴ * fmat Q)
  rw [(fmat_unitary Q).1]
  exact admissible_one

theorem centered_reconstruct (Q : Factor s) (C : Generator s) :
    (fmat Q)ᴴ * fmat (reconstruct Q C) = kcayley C.val := by
  rw [reconstruct_matrix, ← Matrix.mul_assoc, (fmat_unitary Q).1,
    Matrix.one_mul]

theorem reconstruct_mem_source (Q : Factor s) (C : Generator s) :
    reconstruct Q C ∈ factorSource Q := by
  change kadmissible ((fmat Q)ᴴ * fmat (reconstruct Q C))
  rw [centered_reconstruct]
  exact admissible_cayley C.val (admissible_of_isSkew C.val C.property.2.1)

theorem centered_cayley_shared (Q U : Factor s) (hU : U ∈ factorSource Q) :
    kcayley ((fmat Q)ᴴ * fmat U) ∈ ksharedSkewSpace s.size s.label :=
  cayley_sharedSkew s.positive s.divides
    (shared_factor_mul s.positive s.divides
      (shared_factor_conjTranspose (fmat_shared Q)) (fmat_shared U)) hU

theorem factorCoordinates_val (Q U : Factor s) (hU : U ∈ factorSource Q) :
    (factorCoordinates Q (fmat U)).val =
      kcayley ((fmat Q)ᴴ * fmat U) :=
  modelProjection_val_of_mem s _ (centered_cayley_shared Q U hU)

@[simp] theorem factorCoordinates_reconstruct (Q : Factor s) (C : Generator s) :
    factorCoordinates Q (fmat (reconstruct Q C)) = C := by
  unfold factorCoordinates
  rw [centered_reconstruct,
    cayley_involutive C.val (admissible_of_isSkew C.val C.property.2.1)]
  exact modelProjection_inclusion C

theorem reconstruct_factorCoordinates (Q U : Factor s) (hU : U ∈ factorSource Q) :
    reconstruct Q (factorCoordinates Q (fmat U)) = U := by
  apply fmat_injective
  rw [reconstruct_matrix, factorCoordinates_val Q U hU, cayley_involutive _ hU,
    ← Matrix.mul_assoc, (fmat_unitary Q).2, Matrix.one_mul]

@[simp] theorem reconstruct_zero (Q : Factor s) : reconstruct Q 0 = Q := by
  apply fmat_injective
  simp only [reconstruct_matrix, Submodule.coe_zero, cayley_zero, Matrix.mul_one]


theorem factorCoordinates_smooth_at (Q : Factor s) (A : KMat 𝕂 n)
    (hA : kadmissible ((fmat Q)ᴴ * A)) :
    ContDiffAt ℝ ⊤ (factorCoordinates Q) A :=
  (modelProjection s).contDiff.contDiffAt.comp A
    (smooth_cayley_comp_at (ksmooth_mul_at contDiffAt_const contDiffAt_id) hA)

theorem reconstruct_matrix_smooth (Q : Factor s) :
    ContDiff ℝ ⊤ (fun C : Generator s => fmat (reconstruct Q C)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro C
  exact ksmooth_mul_at contDiffAt_const
    (smooth_cayley_comp_at
      (ksharedSkewSpace (𝕂 := 𝕂) (n := n) s.size s.label).subtypeL.contDiff.contDiffAt
      (admissible_of_isSkew C.val C.property.2.1))

theorem continuous_reconstruct (Q : Factor s) : Continuous (reconstruct Q) :=
  ((reconstruct_matrix_smooth Q).continuous.subtype_mk _).subtype_mk _

/-- A total extension on each side, with an open source and full linear target. -/
def factorPartialChart (Q : Factor s) : OpenPartialHomeomorph (Factor s) (Generator s) where
  toFun U := factorCoordinates Q (fmat U)
  invFun := reconstruct Q
  source := factorSource Q
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' C _ := reconstruct_mem_source Q C
  left_inv' U hU := reconstruct_factorCoordinates Q U hU
  right_inv' C _ := factorCoordinates_reconstruct Q C
  open_source := factorSource_open Q
  open_target := isOpen_univ
  continuousOn_toFun := by
    intro U hU
    exact ((factorCoordinates_smooth_at Q (fmat U) hU).continuousAt.comp
      continuous_fmat.continuousAt).continuousWithinAt
  continuousOn_invFun := (continuous_reconstruct Q).continuousOn













/-- Actual two-layer family with full within-layer unitary block sharing. -/


instance factorsMulAction (right left : Pattern 𝕂 n) :
    MulAction (FG) (KMat 𝕂 n) where
  smul g X := fmat g.1 * X * (fmat g.2)ᴴ
  one_smul X := by
    change (1 : KMat 𝕂 n) * X * (1 : KMat 𝕂 n)ᴴ = X
    simp
  mul_smul g h X := by
    change (fmat g.1 * fmat h.1) * X *
      (fmat g.2 * fmat h.2)ᴴ =
      fmat g.1 * (fmat h.1 * X * (fmat h.2)ᴴ) *
        (fmat g.2)ᴴ
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

@[simp] theorem action_apply (g : FG) (X : KMat 𝕂 n) :
    g • X = fmat g.1 * X * (fmat g.2)ᴴ := rfl

instance factorsContinuousSMul (right left : Pattern 𝕂 n) :
    ContinuousSMul (FG) (KMat 𝕂 n) where
  continuous_smul := by
    change Continuous (fun p : FG × KMat 𝕂 n =>
      fmat p.1.1 * p.2 * (fmat p.1.2)ᴴ)
    exact kcontinuous_matrix_product
      (kcontinuous_matrix_product
        (continuous_fmat.comp (continuous_fst.comp continuous_fst)) continuous_snd)
      (kcontinuous_matrix_conjTranspose
        (continuous_fmat.comp (continuous_snd.comp continuous_fst)))

def orbitMap (right left : Pattern 𝕂 n) (P : KMat 𝕂 n) : FG → KMat 𝕂 n :=
  fun g => g • P

abbrev MatrixOrbit (right left : Pattern 𝕂 n) (P : KMat 𝕂 n) :=
  ↥(MulAction.orbit (FG) P)

abbrev PointStabilizer (right left : Pattern 𝕂 n) (P : KMat 𝕂 n) :=
  MulAction.stabilizer (FG) P


theorem continuous_orbitMap (P : KMat 𝕂 n) : Continuous (orbitMap right left P) :=
  continuous_id.smul continuous_const

theorem orbit_iff_inShared (P X : KMat 𝕂 n) :
    X ∈ MulAction.orbit (FG) P ↔
      KInSharedA2 right.size left.size right.label left.label P X := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨fmat g.1, (fmat g.2)ᴴ, fmat_shared g.1,
      shared_factor_conjTranspose (fmat_shared g.2), hg.symm⟩
  · rintro ⟨L, R, hL, hR, hX⟩
    refine ⟨(ofMatrix L hL, ofMatrix Rᴴ (shared_factor_conjTranspose hR)), ?_⟩
    simpa only [action_apply, fmat_ofMatrix, Matrix.conjTranspose_conjTranspose,
      kproduct2] using hX.symm

theorem orbit_set_eq_inShared (P : KMat 𝕂 n) :
    MulAction.orbit (FG) P =
      {X | KInSharedA2 right.size left.size right.label left.label P X} := by
  ext X
  exact orbit_iff_inShared P X

def orbitMapToOrbit (right left : Pattern 𝕂 n) (P : KMat 𝕂 n) :
    FG → MatrixOrbit right left P :=
  fun g => ⟨g • P, ⟨g, rfl⟩⟩
set_option hygiene false in
scoped notation "oMap" => orbitMapToOrbit right left P

theorem continuous_orbitMapToOrbit (P : KMat 𝕂 n) :
    Continuous (oMap) :=
  (continuous_orbitMap P).subtype_mk _

theorem surjective_orbitMapToOrbit (P : KMat 𝕂 n) :
    Function.Surjective (oMap) := by
  rintro ⟨X, g, hg⟩
  exact ⟨g, Subtype.ext hg⟩



theorem action_cFrobInner (g : FG) (X Y : KMat 𝕂 n) :
    kfrobInner (g • X) (g • Y) = kfrobInner X Y :=
  by change kfrobInner (fmat g.1 * X * (fmat g.2)ᴴ) (fmat g.1 * Y * (fmat g.2)ᴴ) = _; rw [kfrobInner_right_unitary _ ((shared_factor_conjTranspose (fmat_shared g.2)).2.1), kfrobInner_left_unitary _ (fmat_unitary g.1)]

/-- The same ambient linear isometry as for independent factors, restricted
to the actual shared subgroup. -/
def actionLinearEquiv (g : FG) : KMat 𝕂 n ≃ₗ[ℝ] KMat 𝕂 n :=
  { toFun := fun X => g • X, invFun := fun X => g⁻¹ • X, left_inv := fun X => inv_smul_smul g X, right_inv := fun X => smul_inv_smul g X, map_add' := fun X Y => by simp [Matrix.mul_add, Matrix.add_mul], map_smul' := fun a X => by simp [Matrix.mul_smul, Matrix.smul_mul] }


theorem orbit_fibre_iff (P : KMat 𝕂 n) (g h : FG) :
    orbitMap right left P g = orbitMap right left P h ↔
      g⁻¹ * h ∈ PointStabilizer right left P := by
  change g • P = h • P ↔ (g⁻¹ * h) • P = P
  constructor
  · intro he
    rw [mul_smul, ← he, inv_smul_smul]
  · intro he
    have he' := congrArg (fun X : KMat 𝕂 n => g • X) he
    have hh : h • P = g • P := by
      simpa only [mul_smul, smul_inv_smul] using he'
    exact hh.symm



theorem closed_of_orbit_preimage_closed (P : KMat 𝕂 n)
    (s : Set (MatrixOrbit right left P))
    (hs : IsClosed (oMap ⁻¹' s)) : IsClosed s := by
  have he : s = oMap '' (oMap ⁻¹' s) := by
    ext x
    constructor
    · intro hx
      obtain ⟨g, rfl⟩ := surjective_orbitMapToOrbit P x
      exact ⟨g, hx, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact hg
  rw [he]
  exact (hs.isCompact.image (continuous_orbitMapToOrbit P)).isClosed

theorem orbit_saturation (P : KMat 𝕂 n) (s : Set (FG)) :
    oMap ⁻¹' (oMap '' s) =
      ⋃ h : PointStabilizer right left P,
        (fun g : FG => g * h.val) ⁻¹' s := by
  ext g
  constructor
  · rintro ⟨h, hh, he⟩
    have hf : orbitMap right left P g = orbitMap right left P h :=
      (congrArg Subtype.val he).symm
    let k : PointStabilizer right left P := ⟨g⁻¹ * h, (orbit_fibre_iff P g h).mp hf⟩
    apply Set.mem_iUnion.mpr
    refine ⟨k, ?_⟩
    change g * (g⁻¹ * h) ∈ s
    simpa only [mul_inv_cancel_left] using hh
  · intro hg
    obtain ⟨h, hh⟩ := Set.mem_iUnion.mp hg
    refine ⟨g * h.val, hh, ?_⟩
    apply Subtype.ext
    change (g * h.val) • P = g • P
    rw [mul_smul, show h.val • P = P from h.property]

/-- Images of factor neighbourhoods are orbit neighbourhoods.  No continuous
or smooth section of the orbit map is asserted by this openness result. -/
theorem orbitMapToOrbit_isOpenMap (P : KMat 𝕂 n) :
    IsOpenMap (oMap) := by
  intro s hs
  have ho : IsOpen (oMap ⁻¹'
      (oMap '' s)) := by
    rw [orbit_saturation]
    exact isOpen_iUnion (fun h => hs.preimage (continuous_id.mul continuous_const))
  have hc := closed_of_orbit_preimage_closed P
    (oMap '' s)ᶜ (by simpa using ho.isClosed_compl)
  simpa using hc.isOpen_compl



abbrev PairGenerator (right left : Pattern 𝕂 n) := Generator left × Generator right
set_option hygiene false in
scoped notation "PG" => PairGenerator right left

/-- Spatial left and right generators; the plus sign absorbs the sign of
transposition in the group action. -/
def pointMap (right left : Pattern 𝕂 n) (X : KMat 𝕂 n) :
    PG →ₗ[ℝ] KMat 𝕂 n where
  toFun v := v.1.val * X + X * v.2.val
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add,
      Matrix.add_mul, Matrix.mul_add]
    abel
  map_smul' a v := by
    change (a • v.1.val) * X + X * (a • v.2.val) =
      a • (v.1.val * X + X * v.2.val)
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_add]

def pointDirections (right left : Pattern 𝕂 n) (X : KMat 𝕂 n) : Submodule ℝ (KMat 𝕂 n) :=
  LinearMap.range (pointMap right left X)
set_option hygiene false in
scoped notation "pDir" => pointDirections right left

theorem mem_pointDirections_iff (X Y : KMat 𝕂 n) :
    Y ∈ pDir X ↔
      ∃ A ∈ ksharedSkewSpace left.size left.label,
        ∃ B ∈ ksharedSkewSpace right.size right.label, Y = A * X + X * B := by
  constructor
  · rintro ⟨⟨A, B⟩, h⟩
    exact ⟨A.val, A.property, B.val, B.property, h.symm⟩
  · rintro ⟨A, hA, B, hB, h⟩
    exact ⟨(⟨A, hA⟩, ⟨B, hB⟩), h.symm⟩

/-- Changing from body generators to spatial generators preserves all ties. -/
theorem sharedDirection_iff_pointDirections (P L R Y : KMat 𝕂 n)
    (hL : KSharedFactor left.size left.label L)
    (hR : KSharedFactor right.size right.label R) :
    KSharedDirection right.size left.size right.label left.label P L R Y ↔
      Y ∈ pDir (kproduct2 L P R) := by
  rw [mem_pointDirections_iff]
  constructor
  · rintro ⟨C, hC, Ω, hΩ, hY⟩
    refine ⟨L * C * Lᴴ, sharedSkew_conjugate left.positive left.divides hL hC,
      Rᴴ * Ω * R, sharedSkew_conjugate_conjTranspose right.positive right.divides hR hΩ, ?_⟩
    have hl : (L * C * Lᴴ) * (L * P * R) = L * C * P * R := by
      calc
        _ = L * C * (Lᴴ * L) * P * R := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hL.2.1.1]; simp only [Matrix.mul_one]
    have hr : (L * P * R) * (Rᴴ * Ω * R) = L * P * Ω * R := by
      calc
        _ = L * P * (R * Rᴴ) * Ω * R := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hR.2.1.2]; simp only [Matrix.mul_one]
    simpa only [kproduct2, hl, hr] using hY
  · rintro ⟨A, hA, B, hB, hY⟩
    refine ⟨Lᴴ * A * L,
      sharedSkew_conjugate_conjTranspose left.positive left.divides hL hA,
      R * B * Rᴴ, sharedSkew_conjugate right.positive right.divides hR hB, ?_⟩
    have hl : L * (Lᴴ * A * L) * P * R = A * (L * P * R) := by
      calc
        _ = (L * Lᴴ) * A * (L * P * R) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hL.2.1.2]; simp only [Matrix.one_mul]
    have hr : L * P * (R * B * Rᴴ) * R = (L * P * R) * B := by
      calc
        _ = (L * P * R) * B * (Rᴴ * R) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hR.2.1.1, Matrix.mul_one]
    simpa only [kproduct2, hl, hr] using hY

/-- The direction spaces transform under the actual shared group action. -/
theorem action_mem_pointDirections (g : FG) (X Y : KMat 𝕂 n)
    (hY : Y ∈ pDir X) :
    g • Y ∈ pDir (g • X) := by
  obtain ⟨A, hA, B, hB, hY⟩ := (mem_pointDirections_iff X Y).mp hY
  let L := fmat g.1
  let R := fmat g.2
  have hL := fmat_shared g.1
  have hR := fmat_shared g.2
  apply (mem_pointDirections_iff (g • X) (g • Y)).mpr
  refine ⟨L * A * Lᴴ, sharedSkew_conjugate left.positive left.divides hL hA,
    R * B * Rᴴ, sharedSkew_conjugate right.positive right.divides hR hB, ?_⟩
  have hl : (L * A * Lᴴ) * (L * X * Rᴴ) = L * (A * X) * Rᴴ := by
    calc
      _ = L * A * (Lᴴ * L) * X * Rᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hL.2.1.1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hr : (L * X * Rᴴ) * (R * B * Rᴴ) = L * (X * B) * Rᴴ := by
    calc
      _ = L * X * (Rᴴ * R) * B * Rᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hR.2.1.1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  change L * Y * Rᴴ = (L * A * Lᴴ) * (L * X * Rᴴ) +
    (L * X * Rᴴ) * (R * B * Rᴴ)
  rw [hY, hl, hr, Matrix.mul_add, Matrix.add_mul]



/-- Total reconstruction in the genuine shared product group. -/
def factorLift (g : FG) (v : PG) :
    FG := (reconstruct g.1 v.1, reconstruct g.2 v.2)

@[simp] theorem factorLift_zero (g : FG) : factorLift g 0 = g := by
  exact Prod.ext (reconstruct_zero g.1) (reconstruct_zero g.2)

theorem continuous_factorLift (g : FG) : Continuous (factorLift g) :=
  ((continuous_reconstruct g.1).comp continuous_fst).prodMk
    ((continuous_reconstruct g.2).comp continuous_snd)

/-- Matrix formula on the whole shared coordinate model. -/
def orbitParam (g : FG) (P : KMat 𝕂 n) (v : PG) :
    KMat 𝕂 n := factorLift g v • P

@[simp] theorem orbitParam_zero (g : FG) (P : KMat 𝕂 n) :
    orbitParam g P 0 = g • P := by simp only [orbitParam, factorLift_zero]

theorem orbitParam_smooth (g : FG) (P : KMat 𝕂 n) :
    ContDiff ℝ ⊤ (orbitParam g P) := by
  apply contDiff_iff_contDiffAt.mpr
  intro v
  change ContDiffAt ℝ ⊤ (fun w : PG =>
    fmat (reconstruct g.1 w.1) * P *
      (fmat (reconstruct g.2 w.2))ᴴ) v
  exact ksmooth_mul_at
    (ksmooth_mul_at ((reconstruct_matrix_smooth g.1).contDiffAt.comp v contDiffAt_fst)
      contDiffAt_const)
    (ksmooth_conjTranspose_at ((reconstruct_matrix_smooth g.2).contDiffAt.comp v contDiffAt_snd))

/-- Reuse the checked ambient Cayley derivative without changing its proof. -/
theorem reconstruct_line_hasDerivAt_zero {s : Pattern 𝕂 n} (Q : Factor s)
    (v : Generator s) :
    HasDerivAt (fun t : ℝ => fmat (reconstruct Q (t • v)))
      ((-2 : ℝ) • (fmat Q * v.val)) 0 :=
  chartInv_line_hasDerivAt_zero Q.val
    ⟨v.val, v.property.1, v.property.2.1⟩

/-- True Frechet derivative at the centre, not a definition of a differential. -/
theorem orbitParam_fderiv_zero (g : FG) (P : KMat 𝕂 n)
    (v : PG) :
    fderiv ℝ (orbitParam g P) 0 v =
      ktangentParam (fmat g.1) P (fmat g.2)ᴴ
        ((-2 : ℝ) • v.1.val) ((2 : ℝ) • v.2.val) := by
  have hdL := reconstruct_line_hasDerivAt_zero g.1 v.1
  have hdR := khasDerivAt_matrix_conjTranspose (reconstruct_line_hasDerivAt_zero g.2 v.2)
  have ht : ((-2 : ℝ) • (fmat g.2 * v.2.val))ᴴ =
      (2 : ℝ) • (v.2.val * (fmat g.2)ᴴ) := by
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_mul, v.2.property.2.1,
      Matrix.neg_mul, smul_neg, ← neg_smul]
    norm_num
  rw [ht] at hdR
  have hactual := khasDerivAt_product2 P hdL hdR
  have hi := ((orbitParam_smooth g P).differentiable (by simp) 0).hasFDerivAt
  have hcomputed := hi.comp_hasDerivAt_of_eq 0
    ((hasDerivAt_id (0 : ℝ)).smul_const v) (by simp)
  have ha : HasDerivAt (fun t : ℝ => orbitParam g P (t • v))
      (ktangentParam (fmat g.1) P (fmat g.2)ᴴ
        ((-2 : ℝ) • v.1.val) ((2 : ℝ) • v.2.val)) 0 := by
    simpa only [orbitParam, factorLift, action_apply, kproduct2, zero_smul,
      reconstruct_zero, ktangentParam, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_assoc, Prod.smul_fst, Prod.smul_snd] using hactual
  simpa only [one_smul] using hcomputed.unique ha

/-- The actual coordinate differential has the full tied generator range. -/
theorem orbitParam_fderiv_zero_range (g : FG) (P Y : KMat 𝕂 n) :
    (∃ v : PG, fderiv ℝ (orbitParam g P) 0 v = Y) ↔
      Y ∈ pDir (g • P) := by
  change (∃ v : PG, fderiv ℝ (orbitParam g P) 0 v = Y) ↔
    Y ∈ pDir (kproduct2 (fmat g.1) P (fmat g.2)ᴴ)
  rw [← sharedDirection_iff_pointDirections P (fmat g.1)
    (fmat g.2)ᴴ Y (fmat_shared g.1)
    (shared_factor_conjTranspose (fmat_shared g.2))]
  constructor
  · rintro ⟨v, rfl⟩
    rw [orbitParam_fderiv_zero]
    let C : Generator left := (-2 : ℝ) • v.1
    let Ω : Generator right := (2 : ℝ) • v.2
    exact ⟨C.val, C.property, Ω.val, Ω.property, rfl⟩
  · rintro ⟨C, hC, Ω, hΩ, hY⟩
    let c : Generator left := ⟨C, hC⟩
    let w : Generator right := ⟨Ω, hΩ⟩
    refine ⟨((-1 / 2 : ℝ) • c, (1 / 2 : ℝ) • w), ?_⟩
    rw [orbitParam_fderiv_zero, hY]
    change ktangentParam (fmat g.1) P (fmat g.2)ᴴ
      ((-2 : ℝ) • ((-1 / 2 : ℝ) • C)) ((2 : ℝ) • ((1 / 2 : ℝ) • Ω)) = _
    norm_num [smul_smul, ktangentParam]

theorem orbitParam_kernel_iff_intertwine (P : KMat 𝕂 n) (v : PG) :
    fderiv ℝ (orbitParam (1 : FG) P) 0 v = 0 ↔
      v.1.val * P = P * v.2.val := by
  rw [orbitParam_fderiv_zero]
  change ktangentParam (1 : KMat 𝕂 n) P (1 : KMat 𝕂 n)ᴴ
    ((-2 : ℝ) • v.1.val) ((2 : ℝ) • v.2.val) = 0 ↔ _
  simp only [ktangentParam, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul]
  constructor
  · intro h
    have hz : (-2 : ℝ) • (v.1.val * P - P * v.2.val) = 0 := by
      simpa only [smul_sub, sub_eq_add_neg, smul_add, smul_neg,
        neg_smul, neg_add_rev, neg_neg] using h
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (by norm_num))
  · intro h
    rw [h, ← add_smul]
    norm_num

/-- Both implications hold for the entire Cayley parameter domain.  Thus the
continuous shared stabilizer is handled by its true linear kernel in this chart. -/
theorem factorLift_stabilizes_iff_kernel (P : KMat 𝕂 n) (v : PG) :
    factorLift (1 : FG) v • P = P ↔
      fderiv ℝ (orbitParam (1 : FG) P) 0 v = 0 := by
  rw [orbitParam_kernel_iff_intertwine]
  have hA := admissible_of_isSkew v.1.val v.1.property.2.1
  have hB := admissible_of_isSkew v.2.val v.2.property.2.1
  have ho := cayley_unitary v.2.val v.2.property.2.1 hB
  simp only [factorLift, action_apply, reconstruct_matrix, Prod.fst_one, Prod.snd_one, fmat_one,
    Matrix.one_mul]
  change kcayley v.1.val * P * (kcayley v.2.val)ᴴ = P ↔ _
  constructor
  · intro h
    have he := congrArg (fun Y : KMat 𝕂 n => Y * kcayley v.2.val) h
    have hi : kcayley v.1.val * P = P * kcayley v.2.val := by
      simpa only [Matrix.mul_assoc, ho.1, Matrix.mul_one] using he
    have hc := cayley_intertwine
      (kcayley v.1.val) (kcayley v.2.val) P
      (admissible_cayley v.1.val hA) (admissible_cayley v.2.val hB) hi
    simpa only [cayley_involutive v.1.val hA, cayley_involutive v.2.val hB] using hc
  · intro h
    rw [cayley_intertwine v.1.val v.2.val P hA hB h,
      Matrix.mul_assoc, ho.2, Matrix.mul_one]



def pairSource (g : FG) : Set (FG) :=
  factorSource g.1 ×ˢ factorSource g.2

def pairCoordinates (g h : FG) : PG :=
  (factorCoordinates g.1 (fmat h.1),
    factorCoordinates g.2 (fmat h.2))

theorem pairSource_open (g : FG) : IsOpen (pairSource g) :=
  (factorSource_open g.1).prod (factorSource_open g.2)

@[simp] theorem self_mem_pairSource (g : FG) : g ∈ pairSource g :=
  ⟨base_mem_factorSource g.1, base_mem_factorSource g.2⟩

theorem factorLift_pairCoordinates (g h : FG)
    (hh : h ∈ pairSource g) : factorLift g (pairCoordinates g h) = h :=
  Prod.ext (reconstruct_factorCoordinates g.1 h.1 hh.1) (reconstruct_factorCoordinates g.2 h.2 hh.2)


theorem reconstruct_isOpenMap (Q : Factor s) : IsOpenMap (reconstruct Q) := by
  intro U hU
  exact (factorPartialChart Q).isOpen_image_symm_of_subset_target hU
    (by change U ⊆ Set.univ; exact Set.subset_univ U)

/-- Positively dimensional stabilizers do not affect openness of reconstruction. -/
theorem factorLift_isOpenMap (g : FG) : IsOpenMap (factorLift g) :=
  (reconstruct_isOpenMap g.1).prodMap (reconstruct_isOpenMap g.2)

theorem factorLift_orbit_isOpenMap (g : FG) (P : KMat 𝕂 n) :
    IsOpenMap (fun v : PG =>
      oMap (factorLift g v)) :=
  (orbitMapToOrbit_isOpenMap P).comp (factorLift_isOpenMap g)

/-- Smooth linear action of any fixed shared factor pair on ambient matrices. -/
theorem fixed_action_smooth (g : FG) :
    ContDiff ℝ ⊤ (fun A : KMat 𝕂 n => g • A) := by
  apply contDiff_iff_contDiffAt.mpr
  intro A
  exact ksmooth_mul_at (ksmooth_mul_at contDiffAt_const contDiffAt_id) contDiffAt_const

/-- A fixed representative is used only to centre a chart.  No continuity
of this choice function is asserted or used. -/
def preferredFactor (P : KMat 𝕂 n) (X : MatrixOrbit right left P) : FG :=
  Classical.choose X.property

@[simp] theorem preferredFactor_spec (P : KMat 𝕂 n) (X : MatrixOrbit right left P) :
    oMap (preferredFactor P X) = X := by
  apply Subtype.ext
  exact Classical.choose_spec X.property

/-- A total matrix-orbit parametrization; only injectivity will be local. -/
def orbitInverse (P : KMat 𝕂 n) (g : FG) (v : PG) :
    MatrixOrbit right left P := oMap (factorLift g v)

@[simp] theorem orbitInverse_val (P : KMat 𝕂 n) (g : FG)
    (v : PG) : (orbitInverse P g v).val = orbitParam g P v := rfl

/-- Fixed group translation of the total factor chart. -/
theorem factorLift_eq_mul (g : FG) (v : PG) :
    factorLift g v = g * factorLift (1 : FG) v := by
  apply Prod.ext
  · change reconstruct g.1 v.1 = g.1 * reconstruct (1 : Factor left) v.1
    simp only [reconstruct, one_mul]
  · change reconstruct g.2 v.2 = g.2 * reconstruct (1 : Factor right) v.2
    simp only [reconstruct, one_mul]

/-- This identity is global in the coordinate model. -/
theorem orbitParam_eq_translate (g : FG) (P : KMat 𝕂 n)
    (v : PG) :
    orbitParam g P v = g • orbitParam (1 : FG) P v := by
  unfold orbitParam
  rw [factorLift_eq_mul g v, mul_smul]



/-- Canonical ambient Frobenius projection at a matrix point. -/
def pointProjection (right left : Pattern 𝕂 n) (X : KMat 𝕂 n) : KMat 𝕂 n →L[ℝ] KMat 𝕂 n :=
  kfrobProjection (pDir X)
set_option hygiene false in
scoped notation "pProj" => pointProjection right left

theorem pointProjection_mem (X Z : KMat 𝕂 n) :
    pProj X Z ∈ pDir X :=
  kfrobProjection_mem _ _

theorem pointProjection_of_mem (X Y : KMat 𝕂 n)
    (hY : Y ∈ pDir X) : pProj X Y = Y :=
  kfrobProjection_of_mem _ _ hY

theorem pointProjection_normal (X Z Y : KMat 𝕂 n)
    (hY : Y ∈ pDir X) :
    kfrobInner (Z - pProj X Z) Y = 0 :=
  kfrobProjection_normal _ _ _ hY

theorem pointProjection_self_adjoint (X Z Y : KMat 𝕂 n) :
    kfrobInner (pProj X Z) Y =
      kfrobInner Z (pProj X Y) :=
  kfrobProjection_self_adjoint _ _ _

@[simp] theorem pointProjection_idempotent (X Z : KMat 𝕂 n) :
    pProj X (pProj X Z) =
      pProj X Z :=
  pointProjection_of_mem X _ (pointProjection_mem X Z)

/-- Equivariance follows from the actual action isometry and the full range,
not an entrywise overlap mask. -/
theorem pointProjection_equivariant (g : FG) (X Z : KMat 𝕂 n) :
    pProj (g • X) (g • Z) =
      g • pProj X Z := by
  apply kfrobProjection_unique_normal (pDir (g • X)) (g • Z)
  · exact action_mem_pointDirections g X _ (pointProjection_mem X Z)
  · intro Y hY
    have hback : g⁻¹ • Y ∈ pDir X := by
      simpa only [inv_smul_smul] using
        action_mem_pointDirections g⁻¹ (g • X) Y hY
    have he := action_cFrobInner g (Z - pProj X Z) (g⁻¹ • Y)
    rw [show g • (Z - pProj X Z) =
        g • Z - g • pProj X Z from
          (actionLinearEquiv g).map_sub _ _, smul_inv_smul] at he
    rw [he]
    exact pointProjection_normal X Z _ hback



/-- The actual differential of the original factor parametrization. -/
def orbitDerivative (right left : Pattern 𝕂 n) (P : KMat 𝕂 n) :
    PG →L[ℝ] KMat 𝕂 n :=
  fderiv ℝ (orbitParam (1 : FG) P) 0

abbrev OrbitKernel (right left : Pattern 𝕂 n) (P : KMat 𝕂 n) :=
  LinearMap.ker (orbitDerivative right left P).toLinearMap

abbrev HorizontalModel (right left : Pattern 𝕂 n) (P : KMat 𝕂 n) :=
  horizontalComplement (orbitDerivative right left P)
set_option hygiene false in
scoped notation "OK" => OrbitKernel right left P
set_option hygiene false in
scoped notation "HM" => HorizontalModel right left P
set_option hygiene false in
scoped notation "MO" => MatrixOrbit right left P
set_option hygiene false in
scoped notation "I_H" => 𝓘(ℝ, HorizontalModel right left P)
set_option hygiene false in
scoped notation "I_M" => 𝓘(ℝ, KMat 𝕂 n)
set_option hygiene false in
scoped notation "I_HT" => (𝓘(ℝ, HorizontalModel right left P)).tangent
set_option hygiene false in
scoped notation "I_HP" => (𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, KMat 𝕂 n))
set_option hygiene false in
scoped notation "I_HPT" => ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, KMat 𝕂 n))).tangent

def horizontalKernelEquiv (right left : Pattern 𝕂 n) (P : KMat 𝕂 n) :
    (HM × OK) ≃L[ℝ] PG :=
  complementKernelEquiv (orbitDerivative right left P)

def orbitHorizontalInverse (right left : Pattern 𝕂 n) (P : KMat 𝕂 n) :
    KMat 𝕂 n →L[ℝ] HM :=
  horizontalLeftInverse (orbitDerivative right left P)




def blockProductCoordinates (s : Pattern 𝕂 n) (x : Generator s × Generator s) :
    Generator s :=
  factorCoordinates (1 : Factor s)
    (fmat (reconstruct (1 : Factor s) x.1) * fmat (reconstruct (1 : Factor s) x.2))

theorem blockProductCoordinates_smooth_zero (s : Pattern 𝕂 n) :
    ContDiffAt ℝ ⊤ (blockProductCoordinates s) 0 := by
  have hm := ksmooth_mul_at
    ((reconstruct_matrix_smooth (1 : Factor s)).contDiffAt.comp 0 contDiffAt_fst)
    ((reconstruct_matrix_smooth (1 : Factor s)).contDiffAt.comp 0 contDiffAt_snd)
  have hc : ContDiffAt ℝ ⊤ (factorCoordinates (1 : Factor s))
      ((fun x : Generator s × Generator s => fmat (reconstruct (1 : Factor s) x.1) *
        fmat (reconstruct (1 : Factor s) x.2)) 0) := by
    simpa using factorCoordinates_smooth_at (1 : Factor s) (1 : KMat 𝕂 n) (by
      change kadmissible ((1 : KMat 𝕂 n)ᴴ * 1); simpa using admissible_one (n := n))
  exact hc.comp 0 hm

@[simp] theorem blockProductCoordinates_fst_zero (s : Pattern 𝕂 n) (x : Generator s) :
    blockProductCoordinates s (x, 0) = x := by
  simp only [blockProductCoordinates, reconstruct_zero, fmat_one, Matrix.mul_one, factorCoordinates_reconstruct]

@[simp] theorem blockProductCoordinates_snd_zero (s : Pattern 𝕂 n) (y : Generator s) :
    blockProductCoordinates s (0, y) = y := by
  simp only [blockProductCoordinates, reconstruct_zero, fmat_one, Matrix.one_mul, factorCoordinates_reconstruct]

def factorProductCoordinates (right left : Pattern 𝕂 n) (x : PG × PG) : PG :=
  (blockProductCoordinates left (x.1.1, x.2.1),
    blockProductCoordinates right (x.1.2, x.2.2))

theorem factorProductCoordinates_eq (x y : PG) :
    factorProductCoordinates right left (x, y) =
      pairCoordinates (1 : FG) (factorLift (1 : FG) x * factorLift (1 : FG) y) := rfl

def reorderLeft (right left : Pattern 𝕂 n) :
    (PG × PG) →L[ℝ] (Generator left × Generator left) :=
  ((ContinuousLinearMap.fst ℝ (Generator left) (Generator right)).comp
    (ContinuousLinearMap.fst ℝ _ _)).prod
  ((ContinuousLinearMap.fst ℝ (Generator left) (Generator right)).comp
    (ContinuousLinearMap.snd ℝ _ _))

def reorderRight (right left : Pattern 𝕂 n) :
    (PG × PG) →L[ℝ] (Generator right × Generator right) :=
  ((ContinuousLinearMap.snd ℝ (Generator left) (Generator right)).comp
    (ContinuousLinearMap.fst ℝ _ _)).prod
  ((ContinuousLinearMap.snd ℝ (Generator left) (Generator right)).comp
    (ContinuousLinearMap.snd ℝ _ _))

theorem factorProductCoordinates_smooth_zero (right left : Pattern 𝕂 n) :
    ContDiffAt ℝ ⊤ (factorProductCoordinates right left) 0 := by
  have hl0 : ContDiffAt ℝ ⊤ (blockProductCoordinates left) (reorderLeft right left 0) :=
    by simpa using blockProductCoordinates_smooth_zero left
  have hr0 : ContDiffAt ℝ ⊤ (blockProductCoordinates right) (reorderRight right left 0) :=
    by simpa using blockProductCoordinates_smooth_zero right
  exact (hl0.comp 0 (reorderLeft right left).contDiff.contDiffAt).prodMk
    (hr0.comp 0 (reorderRight right left).contDiff.contDiffAt)

attribute [local irreducible] ksharedSkewSpace orbitDerivative GS.OverlapGeometry.horizontalComplement

def sliceProduct (right left : Pattern 𝕂 n) (P : KMat 𝕂 n) (x : HM × OK) : PG :=
  factorProductCoordinates right left (x.1.val, x.2.val)

def sliceInclusion (right left : Pattern 𝕂 n) (P : KMat 𝕂 n) :
    (HM × OK) →L[ℝ] (PG × PG) :=
  ((HM).subtypeL.comp (ContinuousLinearMap.fst ℝ _ _)).prod
    ((OK).subtypeL.comp (ContinuousLinearMap.snd ℝ _ _))

set_option synthInstance.maxHeartbeats 100000 in
theorem sliceProduct_smooth_zero (right left : Pattern 𝕂 n) (P : KMat 𝕂 n) :
    ContDiffAt ℝ ⊤ (sliceProduct right left P) 0 := by
  have hf : ContDiffAt ℝ ⊤ (factorProductCoordinates right left) (sliceInclusion right left P 0) :=
    by simpa only [map_zero] using factorProductCoordinates_smooth_zero right left
  exact ContDiffAt.comp (f := fun x : HM × OK => sliceInclusion right left P x)
    (g := factorProductCoordinates right left) 0 hf
    (@ContinuousLinearMap.contDiff ℝ (HM × OK) (PG × PG) _ _ _ _ _ ⊤ (sliceInclusion right left P)).contDiffAt

set_option maxHeartbeats 600000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem sliceProduct_hasFDerivAt_zero (right left : Pattern 𝕂 n) (P : KMat 𝕂 n) :
    HasFDerivAt (sliceProduct right left P)
      (horizontalKernelEquiv right left P : _ →L[ℝ] _) 0 := by
  have hd := ((sliceProduct_smooth_zero right left P).differentiableAt (by simp)).hasFDerivAt
  have hinl : HasFDerivAt (ContinuousLinearMap.inl ℝ HM OK) (ContinuousLinearMap.inl ℝ HM OK) 0 :=
    @ContinuousLinearMap.hasFDerivAt ℝ _ HM _ _ _ (HM × OK) _ _ _ (ContinuousLinearMap.inl ℝ HM OK) 0
  have hinr : HasFDerivAt (ContinuousLinearMap.inr ℝ HM OK) (ContinuousLinearMap.inr ℝ HM OK) 0 :=
    @ContinuousLinearMap.hasFDerivAt ℝ _ OK _ _ _ (HM × OK) _ _ _ (ContinuousLinearMap.inr ℝ HM OK) 0
  have hd_inl : HasFDerivAt (fun h : HM => sliceProduct right left P (ContinuousLinearMap.inl ℝ HM OK h))
      ((fderiv ℝ (sliceProduct right left P) 0).comp (ContinuousLinearMap.inl ℝ HM OK)) 0 :=
    HasFDerivAt.comp (𝕜 := ℝ) (f := fun h : HM => ContinuousLinearMap.inl ℝ HM OK h)
      (g := sliceProduct right left P) 0 hd hinl
  have hd_inr : HasFDerivAt (fun k : OK => sliceProduct right left P (ContinuousLinearMap.inr ℝ HM OK k))
      ((fderiv ℝ (sliceProduct right left P) 0).comp (ContinuousLinearMap.inr ℝ HM OK)) 0 :=
    HasFDerivAt.comp (𝕜 := ℝ) (f := fun k : OK => ContinuousLinearMap.inr ℝ HM OK k)
      (g := sliceProduct right left P) 0 hd hinr
  have h1 : (fderiv ℝ (sliceProduct right left P) 0).comp (ContinuousLinearMap.inl ℝ HM OK) = (HM).subtypeL := by
    refine (hd_inl.congr_of_eventuallyEq (Eventually.of_forall fun h => ?_)).unique
      (@ContinuousLinearMap.hasFDerivAt ℝ _ HM _ _ _ PG _ _ _ (HM).subtypeL 0)
    exact (Prod.ext (blockProductCoordinates_fst_zero left h.val.1) (blockProductCoordinates_fst_zero right h.val.2)).symm
  have h2 : (fderiv ℝ (sliceProduct right left P) 0).comp (ContinuousLinearMap.inr ℝ HM OK) = (OK).subtypeL := by
    refine (hd_inr.congr_of_eventuallyEq (Eventually.of_forall fun k => ?_)).unique
      (@ContinuousLinearMap.hasFDerivAt ℝ _ OK _ _ _ PG _ _ _ (OK).subtypeL 0)
    exact (Prod.ext (blockProductCoordinates_snd_zero left k.val.1) (blockProductCoordinates_snd_zero right k.val.2)).symm
  convert hd using 1
  refine ContinuousLinearMap.ext fun ⟨h, k⟩ => ?_
  have hk := congrArg (fun L : HM →L[ℝ] PG => L h) h1
  have hr := congrArg (fun L : OK →L[ℝ] PG => L k) h2
  have hsum : ((h, k) : HM × OK) = ContinuousLinearMap.inl ℝ HM OK h + ContinuousLinearMap.inr ℝ HM OK k := by
    apply Prod.ext <;> simp
  conv_rhs => rw [hsum, map_add]
  exact (congrArg₂ (· + ·) hk hr).symm

def sliceProductChart (right left : Pattern 𝕂 n) (P : KMat 𝕂 n) :
    OpenPartialHomeomorph (HM × OK)
      (PG) :=
  (sliceProduct_smooth_zero right left P).toOpenPartialHomeomorph _
    (sliceProduct_hasFDerivAt_zero right left P) (by simp)


theorem sliceProductChart_zero_mem_source (right left : Pattern 𝕂 n)
    (P : KMat 𝕂 n) : (0 : HM × OK)
      ∈ (sliceProductChart right left P).source :=
  (sliceProduct_smooth_zero right left P).mem_toOpenPartialHomeomorph_source _ (by simp)


end

section
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ} (right left : Pattern 𝕂 n) (P : KMat 𝕂 n)
local instance projectedSliceNormedSpace : NormedSpace ℝ (HM) :=
  Submodule.normedSpace _

def horizontalValue (h : HM) : KMat 𝕂 n :=
  orbitParam (1 : FG) P h.val
set_option hygiene false in
scoped notation "hVal" => horizontalValue right left P

def horizontalPoint (h : HM) :
    MO :=
  orbitInverse P (1 : FG) h.val

@[simp] theorem horizontalPoint_val (h : HM) :
    (horizontalPoint right left P h).val = hVal h :=
  orbitInverse_val P 1 h.val

theorem horizontalValue_smooth : ContDiff ℝ ⊤ (hVal) :=
  (orbitParam_smooth 1 P).comp
    (horizontalComplement (orbitDerivative right left P)).subtypeL.contDiff

@[simp] theorem horizontalValue_zero :
    hVal 0 = P := by
  simp [horizontalValue, orbitParam_zero, one_smul]

def horizontalProjected (h : HM) : HM :=
  orbitHorizontalInverse right left P (hVal h - P)

theorem horizontalProjected_smooth : ContDiff ℝ ⊤ (horizontalProjected right left P) :=
  (orbitHorizontalInverse right left P).contDiff.comp
    ((horizontalValue_smooth right left P).sub contDiff_const)

@[simp] theorem horizontalProjected_zero : horizontalProjected right left P 0 = 0 := by
  simp [horizontalProjected]

theorem horizontalValue_hasFDerivAt_zero :
    HasFDerivAt (hVal)
      (horizontalRestriction (orbitDerivative right left P)) 0 := by
  have hh := ((orbitParam_smooth (1 : FG) P).differentiable
    (by simp) 0).hasFDerivAt
  unfold horizontalValue
  simpa only [Function.comp_def, horizontalValue, horizontalRestriction, orbitDerivative, map_zero] using
    HasFDerivAt.comp (f := fun h : HM => h.val)
      (g := orbitParam (1 : FG) P) 0 hh
      (horizontalComplement (orbitDerivative right left P)).subtypeL.hasFDerivAt

theorem horizontalProjected_hasFDerivAt_zero :
    HasFDerivAt (horizontalProjected right left P)
      (ContinuousLinearMap.id ℝ (HM)) 0 := by
  have hh := (orbitHorizontalInverse right left P).hasFDerivAt.comp 0
    ((horizontalValue_hasFDerivAt_zero right left P).sub_const P)
  unfold horizontalProjected
  simpa only [Function.comp_def, horizontalProjected, orbitHorizontalInverse, horizontalLeftInverse_comp] using hh

def projectedSliceEquiv : OpenPartialHomeomorph (HM)
    (HM) :=
  (horizontalProjected_smooth right left P).contDiffAt.toOpenPartialHomeomorph
    (horizontalProjected right left P)
    (f' := ContinuousLinearEquiv.refl ℝ (HM))
    (horizontalProjected_hasFDerivAt_zero right left P) (by simp)

@[simp] theorem projectedSliceEquiv_apply (h : HM) :
    projectedSliceEquiv right left P h = horizontalProjected right left P h := rfl

theorem projectedSliceEquiv_zero_source : 0 ∈ (projectedSliceEquiv right left P).source :=
  (horizontalProjected_smooth right left P).contDiffAt.mem_toOpenPartialHomeomorph_source
    (f' := ContinuousLinearEquiv.refl ℝ (HM))
    (horizontalProjected_hasFDerivAt_zero right left P) (by simp)

theorem projectedSliceEquiv_zero_target : 0 ∈ (projectedSliceEquiv right left P).target := by
  simpa only [projectedSliceEquiv_apply, horizontalProjected_zero] using
    (projectedSliceEquiv right left P).map_source (projectedSliceEquiv_zero_source right left P)

theorem projectedSliceEquiv_inverse_smooth_zero :
    ContDiffAt ℝ ⊤ (projectedSliceEquiv right left P).symm 0 := by
  have hh := (horizontalProjected_smooth right left P).contDiffAt.to_localInverse
    (f' := ContinuousLinearEquiv.refl ℝ (HM))
    (horizontalProjected_hasFDerivAt_zero right left P) (by simp)
  simpa only [horizontalProjected_zero, ContDiffAt.localInverse, HasStrictFDerivAt.localInverse, ContDiffAt.toOpenPartialHomeomorph, projectedSliceEquiv] using hh

/-- Concrete IFT data, without any assertion that its image is open in the orbit. -/
structure ProjectedSliceData where
  domain : Set (HM)
  coordinates : KMat 𝕂 n → HM
  open_domain : IsOpen domain
  zero_mem : 0 ∈ domain
  left_inverse : ∀ h ∈ domain, coordinates (hVal h) = h
  coordinates_smooth : ∀ h ∈ domain,
    ContDiffAt ℝ ⊤ coordinates (hVal h)

theorem exists_projectedSliceData : Nonempty (ProjectedSliceData right left P) := by
  let e := projectedSliceEquiv right left P
  have hs : ∀ᶠ y in 𝓝 (0 : HM), ContDiffAt ℝ ⊤ e.symm y :=
    (projectedSliceEquiv_inverse_smooth_zero right left P).eventually (by simp)
  obtain ⟨W, hWsub, hWopen, hWzero⟩ := mem_nhds_iff.mp
    (inter_mem (e.open_target.mem_nhds (projectedSliceEquiv_zero_target right left P)) hs)
  let V := e.source ∩ horizontalProjected right left P ⁻¹' W
  let c : KMat 𝕂 n → HM := fun A =>
    e.symm (orbitHorizontalInverse right left P (A - P))
  refine ⟨⟨V, c, e.open_source.inter
    (hWopen.preimage (horizontalProjected_smooth right left P).continuous),
    ⟨projectedSliceEquiv_zero_source right left P, ?_⟩, ?_, ?_⟩⟩
  · simpa only [Set.mem_preimage, horizontalProjected_zero] using hWzero
  · intro h hh
    exact e.left_inv hh.1
  · intro h hh
    have hi : ContDiffAt ℝ ⊤ e.symm (horizontalProjected right left P h) :=
      (hWsub hh.2).2
    exact hi.comp (hVal h)
      ((orbitHorizontalInverse right left P).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt

def projectedSliceData : ProjectedSliceData right left P :=
  Classical.choice (exists_projectedSliceData right left P)
set_option hygiene false in
scoped notation "pData" => projectedSliceData right left P



attribute [local irreducible] ksharedSkewSpace orbitDerivative GS.OverlapGeometry.horizontalComplement

def productFactors (z : HM × OK) :
    FG :=
  factorLift 1 z.1.val * factorLift 1 z.2.val

theorem productFactors_continuous : Continuous (productFactors right left P) :=
  ((continuous_factorLift 1).comp (continuous_subtype_val.comp continuous_fst)).mul
    ((continuous_factorLift 1).comp (continuous_subtype_val.comp continuous_snd))

def goodProductDomain : Set (HM × OK) :=
  productFactors right left P ⁻¹' pairSource (1 : FG)

theorem goodProductDomain_open : IsOpen (goodProductDomain right left P) :=
  (pairSource_open 1).preimage (productFactors_continuous right left P)

def goodProductChart :
    OpenPartialHomeomorph (HM × OK)
      (PG) :=
  (sliceProductChart right left P).restrOpen (goodProductDomain right left P)
    (goodProductDomain_open right left P)

theorem goodProductChart_zero_source :
    (0 : HM × OK) ∈
      (goodProductChart right left P).source := by
  refine ⟨sliceProductChart_zero_mem_source right left P, ?_⟩
  change factorLift (1 : FG) 0 * factorLift 1 0 ∈ pairSource 1
  simpa using self_mem_pairSource (1 : FG)

theorem goodProductChart_orbit (z : HM × OK)
    (hz : z ∈ (goodProductChart right left P).source) :
    oMap
      (factorLift 1 (goodProductChart right left P z)) = horizontalPoint right left P z.1 := by
  apply Subtype.ext
  change factorLift 1 (sliceProduct right left P z) • P = _
  have hz' : factorLift (1 : FG) z.1.val * factorLift 1 z.2.val ∈
      pairSource 1 := hz.2
  have hk : (fderiv ℝ (orbitParam (1 : FG) P) 0) z.2.val = 0 := by
    simpa only [orbitDerivative] using
      (show orbitDerivative right left P z.2.val = 0 from z.2.property)
  rw [sliceProduct, factorProductCoordinates_eq,
    factorLift_pairCoordinates 1 _ hz', mul_smul,
    (factorLift_stabilizes_iff_kernel P z.2.val).mpr hk]
  rfl

/-- The horizontal parameter neighbourhood where the product decomposition
and the ambient inverse are simultaneously valid. -/
def horizontalChartDomain : Set (HM) :=
  (pData).domain ∩
    (fun h => (h, (0 : OK))) ⁻¹' (goodProductChart right left P).source

theorem horizontalChartDomain_open : IsOpen (horizontalChartDomain right left P) :=
  (pData).open_domain.inter
    ((goodProductChart right left P).open_source.preimage
      (continuous_id.prodMk continuous_const))

theorem horizontalChartDomain_zero : (0 : HM) ∈
    horizontalChartDomain right left P :=
  ⟨(pData).zero_mem, goodProductChart_zero_source right left P⟩

/-- Relative openness is proved by the group orbit map and the product IFT,
not assumed as part of a putative manifold structure. -/
theorem horizontalChartImage_open :
    IsOpen (horizontalPoint right left P '' horizontalChartDomain right left P) := by
  apply isOpen_slice_image_of_productChart (goodProductChart right left P)
    (fun x => oMap (factorLift 1 x))
    (horizontalPoint right left P) (factorLift_orbit_isOpenMap 1 P)
    (goodProductChart_orbit right left P) _ (horizontalChartDomain_open right left P)
  intro h hh
  exact ⟨0, hh.2⟩

/-- A concrete ambient smooth slice at the carrier matrix. -/
def baseOrbitSlice :
    SmoothSlice (E := HM)
      (MulAction.orbit (FG) P) :=
  GS.Extensions.smoothSliceOfParametrization
    (horizontalPoint right left P) (pData).coordinates
    (horizontalChartDomain right left P) (horizontalValue_smooth right left P)
    (horizontalChartDomain_open right left P) (horizontalChartImage_open right left P)
    (fun h hh => (pData).coordinates_smooth h hh.1)
    (fun h hh => (pData).left_inverse h hh.1)

/-- Translation of points of the orbit in its inherited topology. -/
def orbitTranslate (g : FG) (X : MO) :
    MO :=
  ⟨g • X.val, by
    obtain ⟨h, hh⟩ := X.property
    exact ⟨g * h, by simpa only [mul_smul, hh]⟩⟩

@[simp] theorem orbitTranslate_val (g : FG)
    (X : MO) :
    (orbitTranslate right left P g X).val = g • X.val := rfl

theorem orbitTranslate_continuous (g : FG) :
    Continuous (orbitTranslate right left P g) :=
  (continuous_subtype_val.const_smul g).subtype_mk _

@[simp] theorem orbitTranslate_inv (g : FG)
    (X : MO) :
    orbitTranslate right left P g⁻¹ (orbitTranslate right left P g X) = X := by
  apply Subtype.ext
  exact inv_smul_smul g X.val

@[simp] theorem orbitTranslate_inv' (g : FG)
    (X : MO) :
    orbitTranslate right left P g (orbitTranslate right left P g⁻¹ X) = X := by
  apply Subtype.ext
  exact smul_inv_smul g X.val

/-- Translate the constructed slice from the carrier matrix to an
arbitrary point, without changing the common horizontal model. -/
def translatedOrbitSlice (g : FG) :
    SmoothSlice (E := HM)
      (MulAction.orbit (FG) P) :=
  GS.Extensions.translateSmoothSlice (baseOrbitSlice right left P)
    (fun A => g • A) (fun A => g⁻¹ • A)
    (orbitTranslate right left P g) (orbitTranslate right left P g⁻¹)
    (orbitTranslate_val right left P g) (orbitTranslate_val right left P g⁻¹)
    (orbitTranslate_inv' right left P g) (orbitTranslate_inv right left P g)
    (fixed_action_smooth g) (fixed_action_smooth g⁻¹)
    (orbitTranslate_continuous right left P g⁻¹)
set_option hygiene false in
scoped notation "tSlice" => translatedOrbitSlice right left P

theorem translatedOrbitSlice_centre_mem (g : FG) :
    oMap g ∈ (tSlice g).source := by
  have he : orbitTranslate right left P g⁻¹
      (oMap g) = horizontalPoint right left P 0 := by
    apply Subtype.ext
    change g⁻¹ • (g • P) = (horizontalPoint right left P 0).val
    rw [inv_smul_smul, horizontalPoint_val, horizontalValue_zero]
  change orbitTranslate right left P g⁻¹ _ ∈
    horizontalPoint right left P '' horizontalChartDomain right left P
  rw [he]
  exact ⟨0, horizontalChartDomain_zero right left P, rfl⟩

theorem translatedOrbitSlice_centre_coordinates (g : FG) :
    (tSlice g).coordinates
      (oMap g).val = 0 := by
  change (pData).coordinates (g⁻¹ • (g • P)) = 0
  rw [inv_smul_smul]
  simpa only [horizontalValue_zero] using
    (pData).left_inverse 0 (pData).zero_mem

def preferredOrbitSlice (X : MO) :
    SmoothSlice (E := HM)
      (MulAction.orbit (FG) P) :=
  tSlice (preferredFactor P X)
set_option hygiene false in
scoped notation "pSlice" => preferredOrbitSlice right left P

theorem preferredOrbitSlice_covers (X : MO) :
    X ∈ (pSlice X).source := by
  have hh := translatedOrbitSlice_centre_mem right left P (preferredFactor P X)
  simpa only [preferredFactor_spec, preferredOrbitSlice] using hh

theorem preferredOrbitSlice_coordinates_zero (X : MO) :
    (pSlice X).coordinates X.val = 0 := by
  have hh := translatedOrbitSlice_centre_coordinates right left P (preferredFactor P X)
  simpa only [preferredFactor_spec, preferredOrbitSlice] using hh

/-- The shared orbit atlas in its original matrix-subtype topology.  This
is an explicit structure, not a global instance changing older geometries. -/
def sharedOrbitChartedSpace :
    ChartedSpace (HM) (MO) :=
  sliceChartedSpace (pSlice) (preferredOrbitSlice_covers right left P)

theorem sharedOrbitIsManifold :
    letI := sharedOrbitChartedSpace right left P
    IsManifold I_H ⊤ (MO) :=
  slice_isManifold (pSlice) (preferredOrbitSlice_covers right left P)

theorem sharedOrbit_val_contMDiff :
    letI := sharedOrbitChartedSpace right left P
    ContMDiff I_H I_M ⊤
      (fun X : MO => X.val) :=
  slice_val_contMDiff (pSlice) (preferredOrbitSlice_covers right left P)

theorem sharedOrbit_val_mfderiv_eq (X : MO) :
    letI := sharedOrbitChartedSpace right left P
    mfderiv I_H I_M
      (fun Y : MO => Y.val) X =
        fderiv ℝ (fun h : HM =>
          preferredFactor P X • hVal h) 0 := by
  letI := sharedOrbitChartedSpace right left P
  have hh := slice_val_mfderiv_eq (pSlice)
    (preferredOrbitSlice_covers right left P) X
  rw [preferredOrbitSlice_coordinates_zero] at hh
  simpa only [preferredOrbitSlice, translatedOrbitSlice, baseOrbitSlice,
    GS.Extensions.translateSmoothSlice, GS.Extensions.smoothSliceOfParametrization,
    orbitTranslate_val, horizontalPoint_val] using hh

theorem sharedOrbit_val_mfderiv_injective (X : MO) :
    letI := sharedOrbitChartedSpace right left P
    Function.Injective (mfderiv I_H I_M
      (fun Y : MO => Y.val) X) :=
  slice_val_mfderiv_injective (pSlice)
    (preferredOrbitSlice_covers right left P) X


end

section
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ} {right left : Pattern 𝕂 n}
local instance horizontalDifferentialNormedSpace (P : KMat 𝕂 n) :
    NormedSpace ℝ (HM) := Submodule.normedSpace _

theorem orbitParam_fderiv_zero_of_kernel (g : FG) (P : KMat 𝕂 n)
    (v : PG)
    (hv : fderiv ℝ (orbitParam (1 : FG) P) 0 v = 0) :
    fderiv ℝ (orbitParam g P) 0 v = 0 := by
  have hi := (orbitParam_kernel_iff_intertwine P v).mp hv
  rw [orbitParam_fderiv_zero]
  simp only [ktangentParam, Matrix.smul_mul, Matrix.mul_smul]
  have he : (fmat g.1) * v.1.val * P * (fmat g.2)ᴴ =
      (fmat g.1) * P * v.2.val * (fmat g.2)ᴴ := by
    simpa only [Matrix.mul_assoc] using congrArg
      (fun A : KMat 𝕂 n => (fmat g.1) * A * (fmat g.2)ᴴ) hi
  rw [he]
  rw [← add_smul]
  norm_num

theorem horizontalOrbit_hasFDerivAt_zero (P : KMat 𝕂 n)
    (g : FG) :
    HasFDerivAt (fun h : HM => orbitParam g P h.val)
      ((fderiv ℝ (orbitParam g P) 0).comp
        (HM).subtypeL) 0 := by
  have hh := ((orbitParam_smooth g P).differentiable (by simp) 0).hasFDerivAt
  simpa only [map_zero, Function.comp_def] using
    HasFDerivAt.comp (f := fun h : HM => h.val)
      (g := orbitParam g P) 0 hh
      (HM).subtypeL.hasFDerivAt

theorem horizontalOrbit_fderiv_zero (P : KMat 𝕂 n)
    (g : FG) (h : HM) :
    fderiv ℝ (fun h : HM => orbitParam g P h.val) 0 h =
      fderiv ℝ (orbitParam g P) 0 h.val := by
  rw [(horizontalOrbit_hasFDerivAt_zero P g).fderiv]
  rfl

theorem horizontalOrbit_fderiv_zero_range (P : KMat 𝕂 n)
    (g : FG) (Z : KMat 𝕂 n) :
    (∃ h : HM,
      fderiv ℝ (fun h : HM => orbitParam g P h.val) 0 h = Z) ↔
      Z ∈ pDir (g • P) := by
  rw [← orbitParam_fderiv_zero_range g P Z]
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨h.val, (horizontalOrbit_fderiv_zero P g h).symm.trans hh⟩
  · rintro ⟨v, hv⟩
    let z := (horizontalKernelEquiv right left P).symm v
    have hz : (z.1.val : PG) + z.2.val = v :=
      (horizontalKernelEquiv right left P).apply_symm_apply v
    have hk : fderiv ℝ (orbitParam g P) 0 z.2.val = 0 :=
      orbitParam_fderiv_zero_of_kernel g P z.2.val z.2.property
    refine ⟨z.1, ?_⟩
    rw [horizontalOrbit_fderiv_zero, ← hv, ← hz, map_add, hk, add_zero]


end

section
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ} (right left : Pattern 𝕂 n) (P : KMat 𝕂 n)
local instance tangentBridgeNormedSpace : NormedSpace ℝ (HM) :=
  Submodule.normedSpace _
local instance tangentBridgeChartedSpace : ChartedSpace (HM)
    (MO) := sharedOrbitChartedSpace right left P

/-- Full image of the actual mathlib manifold differential. -/
theorem orbit_tangent_image_iff (X : MO) (Z : KMat 𝕂 n) :
    (∃ v : TangentSpace I_H X,
      mfderiv I_H I_M
        (fun Y : MO => Y.val) X v = Z) ↔
      Z ∈ pDir X.val := by
  rw [sharedOrbit_val_mfderiv_eq right left P X]
  have he : (fun h : HM =>
      preferredFactor P X • hVal h) =
      (fun h : HM => orbitParam (preferredFactor P X) P h.val) := by
    funext h
    exact (orbitParam_eq_translate (preferredFactor P X) P h.val).symm
  rw [he]
  have hg : preferredFactor P X • P = X.val :=
    congrArg Subtype.val (preferredFactor_spec P X)
  have hh := horizontalOrbit_fderiv_zero_range P (preferredFactor P X) Z
  rw [hg] at hh
  constructor
  · rintro ⟨v, hv⟩
    exact hh.mp ⟨v, hv⟩
  · intro hZ
    obtain ⟨v, hv⟩ := hh.mpr hZ
    exact ⟨v, hv⟩

/-- The fixed points of the canonical projector are exactly the true tangents. -/
theorem pointProjection_fixed_iff_tangent_image
    (X : MO) (Z : KMat 𝕂 n) :
    pProj X.val Z = Z ↔
      ∃ v : TangentSpace I_H X,
        mfderiv I_H I_M
          (fun Y : MO => Y.val) X v = Z := by
  rw [orbit_tangent_image_iff]
  constructor
  · intro h
    rw [← h]
    exact pointProjection_mem X.val Z
  · exact pointProjection_of_mem X.val Z

/-- The projected ambient matrix has one and only one actual tangent lift. -/
theorem pointProjection_unique_tangent_lift
    (X : MO) (Z : KMat 𝕂 n) :
    ∃! v : TangentSpace I_H X,
      mfderiv I_H I_M
        (fun Y : MO => Y.val) X v =
          pProj X.val Z := by
  obtain ⟨v, hv⟩ := (orbit_tangent_image_iff right left P X _).mpr
    (pointProjection_mem X.val Z)
  refine ⟨v, hv, ?_⟩
  intro w hw
  exact sharedOrbit_val_mfderiv_injective right left P X (hw.trans hv.symm)

/-- The intrinsic and ambient smooth-map interfaces agree. -/
theorem sharedOrbit_contMDiff_iff_contDiff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → MO) :
    ContMDiff (𝓘(ℝ, E)) I_H ⊤ f ↔
      ContDiff ℝ ⊤ (fun x => (f x).val) :=
  GS.OverlapGeometry.slice_contMDiff_iff_contDiff (pSlice)
    (preferredOrbitSlice_covers right left P) f

/-- The same criterion permits a manifold source, including its tangent bundle. -/
theorem sharedOrbit_contMDiff_iff_ambient {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) (f : M → MO) :
    ContMDiff I I_H ⊤ f ↔
      ContMDiff I I_M ⊤ (fun x => (f x).val) :=
  GS.OverlapGeometry.slice_contMDiff_iff_ambient (pSlice)
    (preferredOrbitSlice_covers right left P) I f




local instance metricIsManifold : IsManifold I_H ⊤
    (MO) := sharedOrbitIsManifold right left P

attribute [local irreducible] ksharedSkewSpace orbitDerivative GS.OverlapGeometry.horizontalComplement

def inclusionDifferential (X : MO) :
    TangentSpace I_H X →L[ℝ] KMat 𝕂 n :=
  mfderiv I_H I_M (fun Y : MO => Y.val) X
set_option hygiene false in
scoped notation "iDiff" => inclusionDifferential right left P

theorem inclusionDifferential_injective (X : MO) :
    Function.Injective (iDiff X) :=
  sharedOrbit_val_mfderiv_injective right left P X

def tangentPairing (X : MO) (v w : TangentSpace I_H X) : ℝ :=
  kfrobInner (iDiff X v) (iDiff X w)
set_option hygiene false in
scoped notation "tPair" => tangentPairing right left P

def tangentAmbient (p : TangentBundle I_H (MO)) : KMat 𝕂 n :=
  iDiff p.proj p.2

theorem tangentAmbient_contMDiff :
    ContMDiff I_HT I_M ⊤ (tangentAmbient right left P) :=
  (contMDiff_snd_tangentBundle_modelSpace (KMat 𝕂 n) I_M).comp
    ((sharedOrbit_val_contMDiff right left P).contMDiff_tangentMap (by simp))

def localFactors (g : FG) (A : KMat 𝕂 n) : FG :=
  factorLift g ((tSlice g).coordinates A).val
set_option hygiene false in
scoped notation "lFac" => localFactors right left P

theorem localFactors_orbit (g : FG) (A : KMat 𝕂 n) :
    oMap (lFac g A) = (tSlice g).parametrization ((tSlice g).coordinates A) :=
  Subtype.ext (orbitParam_eq_translate g P _)

theorem localFactors_right_inverse (g : FG)
    (X : MO) (hX : X ∈ (tSlice g).source) :
    oMap (lFac g X.val) = X := by
  rw [localFactors_orbit]; exact (tSlice g).left_inverse X hX

theorem localFactors_left_matrix_smooth_at (g : FG)
    (X : MO) (hX : X ∈ (tSlice g).source) :
    ContDiffAt ℝ ⊤ (fun A : KMat 𝕂 n => fmat (lFac g A).1) X.val :=
  (reconstruct_matrix_smooth g.1).contDiffAt.comp X.val
    (contDiffAt_fst.comp X.val ((HM).subtypeL.contDiff.contDiffAt.comp X.val
      ((tSlice g).coordinates_smooth X hX)))

theorem localFactors_right_matrix_smooth_at (g : FG)
    (X : MO) (hX : X ∈ (tSlice g).source) :
    ContDiffAt ℝ ⊤ (fun A : KMat 𝕂 n => fmat (lFac g A).2) X.val :=
  (reconstruct_matrix_smooth g.2).contDiffAt.comp X.val
    (contDiffAt_snd.comp X.val ((HM).subtypeL.contDiff.contDiffAt.comp X.val
      ((tSlice g).coordinates_smooth X hX)))

theorem pointProjection_factor_formula (g : FG) (Z : KMat 𝕂 n) :
    pProj (g • P) Z =
      fmat g.1 * pProj P ((fmat g.1)ᴴ * Z * fmat g.2) * (fmat g.2)ᴴ := by
  have h := pointProjection_equivariant g P (g⁻¹ • Z)
  rw [smul_inv_smul] at h
  have hi : g⁻¹ • Z = (fmat g.1)ᴴ * Z * fmat g.2 := by
    change (fmat g.1)ᴴ * Z * ((fmat g.2)ᴴ)ᴴ = _; rw [Matrix.conjTranspose_conjTranspose]
  simpa only [hi, action_apply] using h

def localProjectionFormula (g : FG) (p : KMat 𝕂 n × KMat 𝕂 n) : KMat 𝕂 n :=
  let q := lFac g p.1
  fmat q.1 * pProj P ((fmat q.1)ᴴ * p.2 * fmat q.2) * (fmat q.2)ᴴ

theorem localProjectionFormula_eq (g : FG)
    (X : MO) (hX : X ∈ (tSlice g).source) (Z : KMat 𝕂 n) :
    localProjectionFormula right left P g (X.val, Z) = pProj X.val Z := by
  have he : lFac g X.val • P = X.val :=
    congrArg Subtype.val (localFactors_right_inverse right left P g X hX)
  have h := pointProjection_factor_formula right left P (lFac g X.val) Z
  rw [he] at h; exact h.symm

theorem localProjectionFormula_smooth_at (g : FG)
    (X : MO) (hX : X ∈ (tSlice g).source) (Z : KMat 𝕂 n) :
    ContDiffAt ℝ ⊤ (localProjectionFormula right left P g) (X.val, Z) := by
  have hL := (localFactors_left_matrix_smooth_at right left P g X hX).comp (X.val, Z) contDiffAt_fst
  have hR := (localFactors_right_matrix_smooth_at right left P g X hX).comp (X.val, Z) contDiffAt_fst
  have hcore := ksmooth_mul_at (ksmooth_mul_at (ksmooth_conjTranspose_at hL) contDiffAt_snd) hR
  exact ksmooth_mul_at (ksmooth_mul_at hL ((pProj P).contDiff.contDiffAt.comp (X.val, Z) hcore))
    (ksmooth_conjTranspose_at hR)

theorem pointProjection_contMDiff :
    ContMDiff (I_HP) I_M ⊤ (fun p : MO × KMat 𝕂 n => pProj p.1.val p.2) := by
  intro p
  let g := preferredFactor P p.1
  have h₀ : p.1 ∈ (tSlice g).source := by
    simpa only [g, preferredFactor_spec] using translatedOrbitSlice_centre_mem right left P g
  have hinc : ContMDiff (I_HP) (𝓘(ℝ, KMat 𝕂 n × KMat 𝕂 n)) ⊤ (fun q : MO × KMat 𝕂 n => (q.1.val, q.2)) :=
    ((sharedOrbit_val_contMDiff right left P).comp contMDiff_fst).prodMk_space contMDiff_snd
  refine (ContDiffAt.comp_contMDiffAt (f := fun q : MO × KMat 𝕂 n => (q.1.val, q.2))
    (g := localProjectionFormula right left P g)
    (localProjectionFormula_smooth_at right left P g p.1 h₀ p.2) (hinc p)).congr_of_eventuallyEq ?_
  filter_upwards [(continuous_fst.continuousAt).eventually ((tSlice g).open_source.mem_nhds h₀)] with q hq
  exact (localProjectionFormula_eq right left P g q.1 hq q.2).symm

def tangentProjection (X : MO) (Z : KMat 𝕂 n) : TangentSpace I_H X :=
  Classical.choose (pointProjection_unique_tangent_lift right left P X Z)
set_option hygiene false in
scoped notation "tProj" => tangentProjection right left P

@[simp] theorem inclusion_tangentProjection (X : MO) (Z : KMat 𝕂 n) :
    iDiff X (tProj X Z) = pProj X.val Z :=
  (Classical.choose_spec (pointProjection_unique_tangent_lift right left P X Z)).1

theorem tangentProjection_pairing (X : MO) (Z : KMat 𝕂 n) (v : TangentSpace I_H X) :
    tPair X (tProj X Z) v = kfrobInner Z (iDiff X v) := by
  have hfix : pProj X.val (iDiff X v) = iDiff X v :=
    (pointProjection_fixed_iff_tangent_image right left P X _).mpr ⟨v, rfl⟩
  unfold tangentPairing
  rw [inclusion_tangentProjection, pointProjection_self_adjoint, hfix]

theorem tangentProjection_add (X : MO) (Z W : KMat 𝕂 n) :
    tProj X (Z + W) = tProj X Z + tProj X W :=
  inclusionDifferential_injective right left P X (by simp [map_add])

theorem tangentProjection_smul (X : MO) (a : ℝ) (Z : KMat 𝕂 n) :
    tProj X (a • Z) = a • tProj X Z :=
  inclusionDifferential_injective right left P X (by simp [map_smul])

theorem restricted_loss_mfderiv (f : KMat 𝕂 n → ℝ) (X : MO)
    (hf : DifferentiableAt ℝ f X.val) :
    mfderiv I_H (𝓘(ℝ, ℝ)) (fun Y : MO => f Y.val) X =
      (fderiv ℝ f X.val).comp (iDiff X) := by
  have hi : MDifferentiableAt I_H I_M (fun Y : MO => Y.val) X :=
    ((sharedOrbit_val_contMDiff right left P) X).mdifferentiableAt (by simp)
  have hh := mfderiv_comp X hf.mdifferentiableAt hi
  rw [mfderiv_eq_fderiv] at hh
  convert hh using 1 <;> rfl

def intrinsicGradient (f : KMat 𝕂 n → ℝ) (X : MO) : TangentSpace I_H X :=
  tProj X (kambientGradient f X.val)

theorem intrinsicGradient_characterization (f : KMat 𝕂 n → ℝ)
    (X : MO) (hf : DifferentiableAt ℝ f X.val) (v : TangentSpace I_H X) :
    tPair X (intrinsicGradient right left P f X) v =
      mfderiv I_H (𝓘(ℝ, ℝ)) (fun Y : MO => f Y.val) X v := by
  rw [restricted_loss_mfderiv right left P f X hf]
  change tPair X (intrinsicGradient right left P f X) v = fderiv ℝ f X.val (iDiff X v)
  rw [kambientGradient_represents]
  exact tangentProjection_pairing right left P X _ v

end

section
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ} {right left : Pattern 𝕂 n}

def generatorInner (v w : PG) : ℝ :=
  kfrobInner v.1.val w.1.val + kfrobInner v.2.val w.2.val

def generatorEnergy (v : PG) : ℝ := generatorInner v v

theorem generatorInner_add_left (u v w : PG) :
    generatorInner (u + v) w = generatorInner u w + generatorInner v w := by
  simp only [generatorInner, Prod.fst_add, Prod.snd_add, Submodule.coe_add, kfrobInner_add_left]; ring

theorem generatorInner_sub_left (u v w : PG) :
    generatorInner (u - v) w = generatorInner u w - generatorInner v w := by
  change kfrobInner (u.1.val - v.1.val) w.1.val + kfrobInner (u.2.val - v.2.val) w.2.val = _
  rw [kfrobInner_sub_left, kfrobInner_sub_left]; unfold generatorInner; ring

theorem generatorInner_smul_left (a : ℝ) (v w : PG) :
    generatorInner (a • v) w = a * generatorInner v w := by
  change kfrobInner (a • v.1.val) w.1.val + kfrobInner (a • v.2.val) w.2.val = _
  rw [kfrobInner_smul_left, kfrobInner_smul_left]; unfold generatorInner; ring

@[simp] theorem generatorEnergy_eq_zero_iff (v : PG) :
    generatorEnergy v = 0 ↔ v = 0 := by
  refine ⟨fun h => ?_, fun h => by subst h; simp [generatorEnergy, generatorInner]⟩
  change kfrobInner v.1.val v.1.val + kfrobInner v.2.val v.2.val = 0 at h
  have h1 := kfrobSq_nonneg v.1.val; have h2 := kfrobSq_nonneg v.2.val
  exact Prod.ext (Subtype.ext ((kfrobSq_eq_zero_iff _).mp (by linarith)))
    (Subtype.ext ((kfrobSq_eq_zero_iff _).mp (by linarith)))

abbrev GeneratorHilbert (n : ℕ) := WithLp 2 (KFrobCoordinates n × KFrobCoordinates n)

def generatorEncoding (right left : Pattern 𝕂 n) : PG →ₗ[ℝ] GeneratorHilbert n :=
  let L := (encodeKFrob.comp (ksharedSkewSpace left.size left.label).subtype).comp
    (LinearMap.fst ℝ (Generator left) (Generator right))
  let R := (encodeKFrob.comp (ksharedSkewSpace right.size right.label).subtype).comp
    (LinearMap.snd ℝ (Generator left) (Generator right))
  (WithLp.linearEquiv 2 ℝ (KFrobCoordinates n × KFrobCoordinates n)).symm.toLinearMap.comp (L.prod R)

theorem generatorEncoding_inner (v w : PG) :
    ⟪generatorEncoding right left v, generatorEncoding right left w⟫_ℝ = generatorInner v w := rfl

def IsHorizontal (X : KMat 𝕂 n) (v : PG) : Prop :=
  ∀ k : PG, pointMap right left X k = 0 → generatorInner v k = 0

theorem horizontal_lift_unique (X : KMat 𝕂 n) (v w : PG)
    (hv : IsHorizontal X v) (hw : IsHorizontal X w)
    (h : pointMap right left X v = pointMap right left X w) : v = w := by
  have hk : pointMap right left X (v - w) = 0 := by rw [map_sub, h, sub_self]
  apply sub_eq_zero.mp; apply (generatorEnergy_eq_zero_iff (v - w)).mp
  change generatorInner (v - w) (v - w) = 0
  rw [generatorInner_sub_left, hv _ hk, hw _ hk, sub_self]

theorem exists_horizontal_lift (X Z : KMat 𝕂 n) :
    ∃ v : PG, pointMap right left X v = pProj X Z ∧ IsHorizontal X v := by
  obtain ⟨v, hv⟩ := pointProjection_mem (right := right) (left := left) X Z
  let K : Submodule ℝ (GeneratorHilbert n) := (pointMap right left X).ker.map (generatorEncoding right left)
  obtain ⟨kp, hkp_ker, hkp_enc⟩ := (K.orthogonalProjection (generatorEncoding right left v)).property
  refine ⟨v - kp, by rw [map_sub, hkp_ker, sub_zero, hv], fun k hk => ?_⟩
  have h := Submodule.orthogonalProjectionFn_inner_eq_zero (K := K)
    (generatorEncoding right left v) (generatorEncoding right left k) ⟨k, hk, rfl⟩
  rw [Submodule.starProjection_apply] at h
  rw [← generatorEncoding_inner, map_sub, hkp_enc]
  exact h

def minimumNormLift (right left : Pattern 𝕂 n) (X : KMat 𝕂 n) :
    KMat 𝕂 n →L[ℝ] PG :=
  let sel (Z : KMat 𝕂 n) := Classical.choose (exists_horizontal_lift (right := right) (left := left) X Z)
  have hsyn (Z) : pointMap right left X (sel Z) = pProj X Z :=
    (Classical.choose_spec (exists_horizontal_lift (right := right) (left := left) X Z)).1
  have hhor (Z) : IsHorizontal X (sel Z) :=
    (Classical.choose_spec (exists_horizontal_lift (right := right) (left := left) X Z)).2
  ({ toFun := sel
     map_add' := fun Z W => horizontal_lift_unique X _ _ (hhor (Z + W))
       (fun k hk => by rw [generatorInner_add_left, hhor Z k hk, hhor W k hk, add_zero])
       (by simp only [map_add, hsyn])
     map_smul' := fun a Z => horizontal_lift_unique X _ _ (hhor (a • Z))
       (fun k hk => by rw [generatorInner_smul_left, hhor Z k hk, mul_zero])
       (by simp only [map_smul, hsyn, RingHom.id_apply])
   } : KMat 𝕂 n →ₗ[ℝ] PG).toContinuousLinearMap
set_option hygiene false in
scoped notation "mLift" => minimumNormLift right left

theorem minimumNormLift_synthesis (X Z : KMat 𝕂 n) :
    pointMap right left X (mLift X Z) = pProj X Z :=
  (Classical.choose_spec (exists_horizontal_lift (right := right) (left := left) X Z)).1

theorem minimumNormLift_horizontal (X Z : KMat 𝕂 n) :
    IsHorizontal X (mLift X Z) :=
  (Classical.choose_spec (exists_horizontal_lift (right := right) (left := left) X Z)).2

theorem minimumNormLift_unique (X Z : KMat 𝕂 n) (v : PG)
    (hv : pointMap right left X v = pProj X Z)
    (hh : IsHorizontal X v) : v = mLift X Z :=
  horizontal_lift_unique X v _ hh (minimumNormLift_horizontal X Z)
    (hv.trans (minimumNormLift_synthesis X Z).symm)

@[simp] theorem minimumNormLift_projected (X Z : KMat 𝕂 n) :
    mLift X (pProj X Z) = mLift X Z :=
  minimumNormLift_unique X Z _
    (by rw [minimumNormLift_synthesis, pointProjection_idempotent])
    (minimumNormLift_horizontal X _)

def generatorAction (g : FG) : PG →ₗ[ℝ] PG where
  toFun v :=
    (⟨fmat g.1 * v.1.val * (fmat g.1)ᴴ,
      sharedSkew_conjugate left.positive left.divides (fmat_shared g.1) v.1.property⟩,
     ⟨fmat g.2 * v.2.val * (fmat g.2)ᴴ,
      sharedSkew_conjugate right.positive right.divides (fmat_shared g.2) v.2.property⟩)
  map_add' v w := by
    apply Prod.ext <;> apply Subtype.ext <;>
      simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' a v := by
    apply Prod.ext <;> apply Subtype.ext
    · change fmat g.1 * (a • v.1.val) * (fmat g.1)ᴴ = a • (fmat g.1 * v.1.val * (fmat g.1)ᴴ)
      rw [Matrix.mul_smul, Matrix.smul_mul]
    · change fmat g.2 * (a • v.2.val) * (fmat g.2)ᴴ = a • (fmat g.2 * v.2.val * (fmat g.2)ᴴ)
      rw [Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem generatorAction_left (g : FG) (v : PG) :
    (generatorAction g v).1.val = fmat g.1 * v.1.val * (fmat g.1)ᴴ := rfl

@[simp] theorem generatorAction_right (g : FG) (v : PG) :
    (generatorAction g v).2.val = fmat g.2 * v.2.val * (fmat g.2)ᴴ := rfl

private theorem conjugate_cancel (A C : KMat 𝕂 n) (hA : KUnitary A) :
    Aᴴ * (A * C * Aᴴ) * A = C := by
  calc _ = (Aᴴ * A) * C * (Aᴴ * A) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hA.1]; simp

@[simp] theorem generatorAction_inverse (g : FG) (v : PG) :
    generatorAction g⁻¹ (generatorAction g v) = v := by
  apply Prod.ext <;> apply Subtype.ext
  · change (fmat g.1)ᴴ * (fmat g.1 * v.1.val * (fmat g.1)ᴴ) * ((fmat g.1)ᴴ)ᴴ = v.1.val
    rw [Matrix.conjTranspose_conjTranspose]; exact conjugate_cancel _ _ (fmat_unitary g.1)
  · change (fmat g.2)ᴴ * (fmat g.2 * v.2.val * (fmat g.2)ᴴ) * ((fmat g.2)ᴴ)ᴴ = v.2.val
    rw [Matrix.conjTranspose_conjTranspose]; exact conjugate_cancel _ _ (fmat_unitary g.2)

@[simp] theorem generatorAction_inverse_right (g : FG) (v : PG) :
    generatorAction g (generatorAction g⁻¹ v) = v := by
  simpa only [inv_inv] using generatorAction_inverse g⁻¹ v

theorem pointMap_generatorAction (g : FG) (X : KMat 𝕂 n) (v : PG) :
    pointMap right left (g • X) (generatorAction g v) = g • pointMap right left X v := by
  let L := fmat g.1; let R := fmat g.2
  have hl : (L * v.1.val * Lᴴ) * (L * X * Rᴴ) = L * (v.1.val * X) * Rᴴ := by
    calc _ = L * v.1.val * (Lᴴ * L) * X * Rᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [(fmat_unitary g.1).1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hr : (L * X * Rᴴ) * (R * v.2.val * Rᴴ) = L * (X * v.2.val) * Rᴴ := by
    calc _ = L * X * (Rᴴ * R) * v.2.val * Rᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [(fmat_unitary g.2).1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  change (L * v.1.val * Lᴴ) * (L * X * Rᴴ) + (L * X * Rᴴ) * (R * v.2.val * Rᴴ) =
    L * (v.1.val * X + X * v.2.val) * Rᴴ
  rw [hl, hr, Matrix.mul_add, Matrix.add_mul]

theorem generatorInner_action (g : FG) (v w : PG) :
    generatorInner (generatorAction g v) (generatorAction g w) = generatorInner v w := by
  unfold generatorInner; simp only [generatorAction_left, generatorAction_right]
  rw [kfrobInner_right_unitary _ (fmat_unitary g.1).conjTranspose,
    kfrobInner_right_unitary _ (fmat_unitary g.2).conjTranspose,
    kfrobInner_left_unitary _ (fmat_unitary g.1),
    kfrobInner_left_unitary _ (fmat_unitary g.2)]

theorem generatorAction_horizontal (g : FG) (X : KMat 𝕂 n)
    (v : PG) (hv : IsHorizontal X v) :
    IsHorizontal (g • X) (generatorAction g v) := by
  intro k hk
  have hb : pointMap right left X (generatorAction g⁻¹ k) = 0 := by
    have he := pointMap_generatorAction g⁻¹ (g • X) k
    rw [inv_smul_smul, hk] at he
    simpa only [action_apply, Matrix.mul_zero, Matrix.zero_mul] using he
  calc generatorInner (generatorAction g v) k =
        generatorInner (generatorAction g v) (generatorAction g (generatorAction g⁻¹ k)) := by
          rw [generatorAction_inverse_right]
    _ = 0 := (generatorInner_action g v _).trans (hv _ hb)

theorem minimumNormLift_equivariant (g : FG) (X Z : KMat 𝕂 n) :
    mLift (g • X) (g • Z) = generatorAction g (mLift X Z) :=
  (minimumNormLift_unique _ _ _
    (by rw [pointMap_generatorAction, minimumNormLift_synthesis, pointProjection_equivariant])
    (generatorAction_horizontal g X _ (minimumNormLift_horizontal X Z))).symm

theorem minimumNormLift_factor_formula (g : FG) (P Z : KMat 𝕂 n) :
    mLift (g • P) Z = generatorAction g (mLift P (g⁻¹ • Z)) := by
  simpa only [smul_inv_smul] using minimumNormLift_equivariant g P (g⁻¹ • Z)

end

section
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ} (right left : Pattern 𝕂 n) (P : KMat 𝕂 n)
local instance smoothLiftNormedSpace : NormedSpace ℝ (HM) := Submodule.normedSpace _
local instance smoothLiftChartedSpace : ChartedSpace (HM) (MO) := sharedOrbitChartedSpace right left P

def transportedMinimumNormLift (p : KMat 𝕂 n × (KMat 𝕂 n × KMat 𝕂 n)) : PG :=
  let v := mLift P (p.1ᴴ * p.2.2 * p.2.1)
  (modelProjection left (p.1 * v.1.val * p.1ᴴ),
   modelProjection right (p.2.1 * v.2.val * p.2.1ᴴ))

theorem transportedMinimumNormLift_smooth :
    ContDiff ℝ ⊤ (transportedMinimumNormLift right left P) := by
  refine contDiff_iff_contDiffAt.mpr fun p => ?_
  have hL : ContDiffAt ℝ ⊤ (fun q : KMat 𝕂 n × (KMat 𝕂 n × KMat 𝕂 n) => q.1) p := contDiffAt_fst
  have hR : ContDiffAt ℝ ⊤ (fun q : KMat 𝕂 n × (KMat 𝕂 n × KMat 𝕂 n) => q.2.1) p := contDiffAt_snd.fst
  have hZ : ContDiffAt ℝ ⊤ (fun q : KMat 𝕂 n × (KMat 𝕂 n × KMat 𝕂 n) => q.2.2) p := contDiffAt_snd.snd
  have hv := (mLift P).contDiff.contDiffAt.comp p
    (ksmooth_mul_at (ksmooth_mul_at (ksmooth_conjTranspose_at hL) hZ) hR)
  have hvL := (ksharedSkewSpace (𝕂 := 𝕂) (n := n) left.size left.label).subtypeL.contDiff.contDiffAt.comp p hv.fst
  have hvR := (ksharedSkewSpace (𝕂 := 𝕂) (n := n) right.size right.label).subtypeL.contDiff.contDiffAt.comp p hv.snd
  exact ((modelProjection left).contDiff.contDiffAt.comp p
    (ksmooth_mul_at (ksmooth_mul_at hL hvL) (ksmooth_conjTranspose_at hL))).prodMk
    ((modelProjection right).contDiff.contDiffAt.comp p
      (ksmooth_mul_at (ksmooth_mul_at hR hvR) (ksmooth_conjTranspose_at hR)))

theorem transportedMinimumNormLift_on_factors (g : FG) (Z : KMat 𝕂 n) :
    transportedMinimumNormLift right left P (fmat g.1, (fmat g.2, Z)) =
      mLift (g • P) Z := by
  rw [minimumNormLift_factor_formula]
  have he : g⁻¹ • Z = (fmat g.1)ᴴ * Z * fmat g.2 := by
    change (fmat g.1)ᴴ * Z * ((fmat g.2)ᴴ)ᴴ = _; rw [Matrix.conjTranspose_conjTranspose]
  rw [he]
  exact Prod.ext (modelProjection_inclusion (generatorAction g (mLift P ((fmat g.1)ᴴ * Z * fmat g.2))).1)
    (modelProjection_inclusion (generatorAction g (mLift P ((fmat g.1)ᴴ * Z * fmat g.2))).2)

def localMinimumNormLift (g : FG) (p : KMat 𝕂 n × KMat 𝕂 n) : PG :=
  let q := lFac g p.1
  transportedMinimumNormLift right left P (fmat q.1, (fmat q.2, p.2))

theorem localMinimumNormLift_eq (g : FG)
    (X : MO) (hX : X ∈ (tSlice g).source) (Z : KMat 𝕂 n) :
    localMinimumNormLift right left P g (X.val, Z) = mLift X.val Z := by
  have he : lFac g X.val • P = X.val :=
    congrArg Subtype.val (localFactors_right_inverse right left P g X hX)
  change transportedMinimumNormLift right left P _ = _
  rw [transportedMinimumNormLift_on_factors, he]

theorem localMinimumNormLift_smooth_at (g : FG)
    (X : MO) (hX : X ∈ (tSlice g).source) (Z : KMat 𝕂 n) :
    ContDiffAt ℝ ⊤ (localMinimumNormLift right left P g) (X.val, Z) := by
  have hL := (localFactors_left_matrix_smooth_at right left P g X hX).comp (X.val, Z) contDiffAt_fst
  have hR := (localFactors_right_matrix_smooth_at right left P g X hX).comp (X.val, Z) contDiffAt_fst
  exact (transportedMinimumNormLift_smooth right left P).contDiffAt.comp
    (X.val, Z) (hL.prodMk (hR.prodMk contDiffAt_snd))

theorem minimumNormLift_contMDiff :
    ContMDiff (I_HP) (𝓘(ℝ, PG)) ⊤ (fun p : MO × KMat 𝕂 n => mLift p.1.val p.2) := by
  intro p
  let g := preferredFactor P p.1
  have h₀ : p.1 ∈ (tSlice g).source := by
    simpa only [g, preferredFactor_spec] using translatedOrbitSlice_centre_mem right left P g
  have hinc : ContMDiff (I_HP) (𝓘(ℝ, KMat 𝕂 n × KMat 𝕂 n)) ⊤ (fun q : MO × KMat 𝕂 n => (q.1.val, q.2)) :=
    ((sharedOrbit_val_contMDiff right left P).comp contMDiff_fst).prodMk_space contMDiff_snd
  refine (ContDiffAt.comp_contMDiffAt (f := fun q : MO × KMat 𝕂 n => (q.1.val, q.2))
    (g := localMinimumNormLift right left P g)
    (localMinimumNormLift_smooth_at right left P g p.1 h₀ p.2) (hinc p)).congr_of_eventuallyEq ?_
  filter_upwards [(continuous_fst.continuousAt).eventually ((tSlice g).open_source.mem_nhds h₀)] with q hq
  exact (localMinimumNormLift_eq right left P g q.1 hq q.2).symm

end

section
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ} {right left : Pattern 𝕂 n}

theorem unitCayley_shared (s : Pattern 𝕂 n) (C : Generator s) :
    KSharedFactor s.size s.label (kunitCayley C.val) :=
  cayley_shared s.positive s.divides
    ((ksharedSkewSpace s.size s.label).smul_mem (-1 / 2 : ℝ) C.property)

def generatorCayleyValue (right left : Pattern 𝕂 n)
    (p : KMat 𝕂 n × (PG × ℝ)) : KMat 𝕂 n :=
  kunitCayley (p.2.2 • p.2.1.1.val) * p.1 * kunitCayley (p.2.2 • p.2.1.2.val)

theorem generatorCayleyValue_smooth (right left : Pattern 𝕂 n) :
    ContDiff ℝ ⊤ (generatorCayleyValue right left) := by
  let E := KMat 𝕂 n × (PG × ℝ)
  have hL : ContDiff ℝ ⊤ (fun p : E => p.2.2 • p.2.1.1.val) :=
    contDiff_snd.snd.smul
      ((ksharedSkewSpace (𝕂 := 𝕂) (n := n) left.size left.label).subtypeL.contDiff.comp contDiff_snd.fst.fst)
  have hR : ContDiff ℝ ⊤ (fun p : E => p.2.2 • p.2.1.2.val) :=
    contDiff_snd.snd.smul
      ((ksharedSkewSpace (𝕂 := 𝕂) (n := n) right.size right.label).subtypeL.contDiff.comp contDiff_snd.fst.snd)
  have hcL := unitCayley_smooth_comp _ hL (fun p => kisSkew_smul p.2.2 p.2.1.1.property.2.1)
  have hcR := unitCayley_smooth_comp _ hR (fun p => kisSkew_smul p.2.2 p.2.1.2.property.2.1)
  exact ksmooth_matrix_product (ksmooth_matrix_product hcL contDiff_fst) hcR

def generatorCayleyAction (v : PG) (t : ℝ) : FG :=
  (ofMatrix (kunitCayley (t • v.1.val)) (unitCayley_shared left (t • v.1)),
   ofMatrix ((kunitCayley (t • v.2.val))ᴴ)
     (shared_factor_conjTranspose (unitCayley_shared right (t • v.2))))

theorem generatorCayleyAction_value (X : KMat 𝕂 n) (v : PG) (t : ℝ) :
    generatorCayleyAction v t • X = generatorCayleyValue right left (X, (v, t)) := by
  change kunitCayley (t • v.1.val) * X * ((kunitCayley (t • v.2.val))ᴴ)ᴴ = _
  rw [Matrix.conjTranspose_conjTranspose]; rfl

def sharedCayleyValue (right left : Pattern 𝕂 n) (X Z : KMat 𝕂 n) (t : ℝ) : KMat 𝕂 n :=
  generatorCayleyValue right left (X, (mLift X Z, t))
set_option hygiene false in
scoped notation "sCayley" => sharedCayleyValue right left

@[simp] theorem sharedCayleyValue_projected (X Z : KMat 𝕂 n) (t : ℝ) :
    sCayley X (pProj X Z) t = sCayley X Z t := by
  simp only [sharedCayleyValue, minimumNormLift_projected]

theorem sharedCayleyValue_smul (X Z : KMat 𝕂 n) (a t : ℝ) :
    sCayley X (a • Z) t = sCayley X Z (t * a) := by
  unfold sharedCayleyValue; rw [map_smul]
  change kunitCayley (t • (a • (mLift X Z).1.val)) * X * kunitCayley (t • (a • (mLift X Z).2.val)) =
    kunitCayley ((t * a) • (mLift X Z).1.val) * X * kunitCayley ((t * a) • (mLift X Z).2.val)
  simp only [smul_smul]

theorem sharedCayleyValue_mem_orbit (P : KMat 𝕂 n) (X : MO)
    (Z : KMat 𝕂 n) (t : ℝ) :
    sCayley X.val Z t ∈ MulAction.orbit (FG) P := by
  obtain ⟨g, hg⟩ := X.property
  refine ⟨generatorCayleyAction (mLift X.val Z) t * g, ?_⟩
  change g • P = X.val at hg
  change (generatorCayleyAction (mLift X.val Z) t * g) • P = _
  rw [mul_smul, hg, generatorCayleyAction_value]; rfl

theorem sharedCayleyValue_derivative (X Z : KMat 𝕂 n) :
    HasDerivAt (sCayley X Z) (pProj X Z) 0 := by
  let v := mLift X Z
  have hL := unitCayley_line_derivative v.1.val v.1.property.2.1
  have hR := unitCayley_line_derivative v.2.val v.2.property.2.1
  have hd := khasDerivAt_matrix_mul (khasDerivAt_matrix_mul hL (hasDerivAt_const (0 : ℝ) X)) hR
  have hv : v.1.val * X + X * v.2.val = pProj X Z := minimumNormLift_synthesis X Z
  unfold sharedCayleyValue generatorCayleyValue
  simpa only [zero_smul, unitCayley_zero, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, add_zero, hv] using hd

theorem sharedCayleyValue_fixed_smooth (X : KMat 𝕂 n) :
    ContDiff ℝ ⊤ (fun p : KMat 𝕂 n × ℝ => sCayley X p.1 p.2) :=
  (generatorCayleyValue_smooth right left).comp
    (contDiff_const.prodMk (((mLift X).contDiff.comp contDiff_fst).prodMk contDiff_snd))

section OrbitSmoothness
variable (right left : Pattern 𝕂 n) (P : KMat 𝕂 n)
local instance cayleyStepChartedSpace : ChartedSpace (HM) (MO) := sharedOrbitChartedSpace right left P

theorem sharedCayleyValue_contMDiff :
    ContMDiff ((I_HP).prod (𝓘(ℝ, ℝ))) I_M ⊤ (fun p : (MO × KMat 𝕂 n) × ℝ =>
        sCayley p.1.1.val p.1.2 p.2) := by
  have hb : ContMDiff ((I_HP).prod (𝓘(ℝ, ℝ))) I_M ⊤ (fun p : (MO × KMat 𝕂 n) × ℝ => p.1.1.val) :=
    (sharedOrbit_val_contMDiff right left P).comp (contMDiff_fst.comp contMDiff_fst)
  have hl : ContMDiff ((I_HP).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, PG)) ⊤ (fun p : (MO × KMat 𝕂 n) × ℝ => mLift p.1.1.val p.1.2) :=
    (minimumNormLift_contMDiff right left P).comp contMDiff_fst
  exact (generatorCayleyValue_smooth right left).comp_contMDiff (hb.prodMk_space (hl.prodMk_space contMDiff_snd))

end OrbitSmoothness

end

section
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ} (right left : Pattern 𝕂 n) (P : KMat 𝕂 n)
local instance retractionNormedSpace : NormedSpace ℝ (HM) := Submodule.normedSpace _
local instance retractionChartedSpace : ChartedSpace (HM) (MO) := sharedOrbitChartedSpace right left P
local instance retractionIsManifold : IsManifold I_H ⊤ (MO) := sharedOrbitIsManifold right left P

attribute [local irreducible] ksharedSkewSpace orbitDerivative GS.OverlapGeometry.horizontalComplement

def cayleyFibreRetraction (X : MO) (v : TangentSpace I_H X) : MO :=
  ⟨sCayley X.val (iDiff X v) 1, sharedCayleyValue_mem_orbit P X (iDiff X v) 1⟩
set_option hygiene false in
scoped notation "cRet" => cayleyFibreRetraction right left P

@[simp] theorem cayleyFibreRetraction_zero (X : MO) : cRet X 0 = X :=
  Subtype.ext (by simp [cayleyFibreRetraction, sharedCayleyValue, generatorCayleyValue])

theorem cayleyFibreRetraction_contMDiff (X : MO) :
    ContMDiff I_H I_H ⊤ (fun v : HM => cRet X v) := by
  let D : HM →L[ℝ] KMat 𝕂 n := iDiff X
  exact (sharedOrbit_contMDiff_iff_contDiff right left P _).mpr <|
    (sharedCayleyValue_fixed_smooth (right := right) (left := left) X.val).comp
      (f := fun v : HM => (D v, (1 : ℝ))) (D.contDiff.prodMk contDiff_const)

theorem cayleyFibreRetraction_mfderiv_zero (X : MO) :
    mfderiv (M := HM) (M' := MO) I_H I_H (fun v : HM => cRet X v) (0 : HM) =
      ContinuousLinearMap.id ℝ (HM) := by
  ext (v : HM)
  have hd : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa only [one_smul, id_eq] using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hf := (cayleyFibreRetraction_contMDiff right left P X).mdifferentiable (by simp)
  have hi := (sharedOrbit_val_contMDiff right left P).mdifferentiable (by simp)
  have hline_val : (fun t : ℝ => (cRet X (t • v)).val) = sCayley X.val (iDiff X v) := by
    funext t; change sCayley X.val (iDiff X (t • v)) 1 = _
    rw [map_smul, sharedCayleyValue_smul, one_mul]
  have h0v : (0 : ℝ) • v = (0 : HM) := zero_smul ℝ v
  have hγ0 : cRet X ((0 : ℝ) • v) = X := by rw [h0v, cayleyFibreRetraction_zero]
  have hγ_mdiff : MDifferentiableAt (𝓘(ℝ, ℝ)) I_H (fun t : ℝ => cRet X (t • v)) 0 :=
    (h0v.symm ▸ hf 0).comp 0 hd.differentiableAt.mdifferentiableAt
  have h1 := mfderiv_comp_apply_of_eq (0 : ℝ) (hi X) hγ_mdiff hγ0 (1 : ℝ)
  have h2 : @Eq HM (mfderiv (𝓘(ℝ, ℝ)) I_H (fun t : ℝ => cRet X (t • v)) 0 (1 : ℝ))
      (mfderiv (M := HM) (M' := MO) I_H I_H (fun w : HM => cRet X w) (0 : HM)
        (mfderiv (𝓘(ℝ, ℝ)) I_H (fun t : ℝ => t • v) 0 (1 : ℝ))) :=
    mfderiv_comp_apply_of_eq (0 : ℝ) (hf 0) hd.differentiableAt.mdifferentiableAt h0v (1 : ℝ)
  have hlineD : @Eq HM (mfderiv (𝓘(ℝ, ℝ)) I_H (fun t : ℝ => t • v) 0 (1 : ℝ)) v := by
    rw [mfderiv_eq_fderiv]; exact hd.deriv
  have hright : @Eq HM
      (mfderiv (M := HM) (M' := MO) I_H I_H (fun w : HM => cRet X w) (0 : HM)
        (mfderiv (𝓘(ℝ, ℝ)) I_H (fun t : ℝ => t • v) 0 (1 : ℝ)))
      (mfderiv (M := HM) (M' := MO) I_H I_H (fun w : HM => cRet X w) (0 : HM) v) :=
    congrArg (α := HM) (β := HM) (fun w => mfderiv (M := HM) (M' := MO) I_H I_H (fun u : HM => cRet X u) (0 : HM) w) hlineD
  have hmatD : mfderiv (𝓘(ℝ, ℝ)) I_M (fun t : ℝ => (cRet X (t • v)).val) 0 (1 : ℝ) = iDiff X v := by
    rw [mfderiv_eq_fderiv, hline_val]
    have hfix : pProj X.val (iDiff X v) = iDiff X v :=
      (pointProjection_fixed_iff_tangent_image right left P X _).mpr ⟨v, rfl⟩
    exact (hfix ▸ sharedCayleyValue_derivative X.val (iDiff X v)).deriv
  have hv : @Eq HM (mfderiv (𝓘(ℝ, ℝ)) I_H (fun t : ℝ => cRet X (t • v)) 0 (1 : ℝ)) v :=
    inclusionDifferential_injective right left P X (h1.symm.trans hmatD)
  exact hright.symm.trans (h2.symm.trans hv)

def cayleyRetraction (p : TangentBundle I_H (MO)) : MO := cRet p.proj p.2

@[simp] theorem cayleyRetraction_val (p : TangentBundle I_H (MO)) :
    (cayleyRetraction right left P p).val =
      sCayley p.proj.val (tangentAmbient right left P p) 1 := rfl

set_option maxHeartbeats 800000 in
theorem cayleyRetraction_contMDiff :
    ContMDiff I_HT I_H ⊤ (cayleyRetraction right left P) := by
  have hargs : ContMDiff I_HT ((I_HP).prod (𝓘(ℝ, ℝ))) ⊤
      (fun p : TangentBundle I_H (MO) => ((p.proj, tangentAmbient right left P p), (1 : ℝ))) :=
    ((Bundle.contMDiff_proj (TangentSpace I_H)).prodMk
      (tangentAmbient_contMDiff right left P)).prodMk contMDiff_const
  apply (sharedOrbit_contMDiff_iff_ambient right left P I_HT (cayleyRetraction right left P)).mpr
  simpa only [cayleyRetraction_val, Function.comp_def] using
    (sharedCayleyValue_contMDiff right left P).comp hargs

@[simp] theorem cayleyRetraction_zero_section (X : MO) :
    cayleyRetraction right left P ⟨X, 0⟩ = X := cayleyFibreRetraction_zero right left P X

theorem cayleyRetraction_fibre_mfderiv_zero (X : MO) :
    mfderiv I_H I_H (fun v : HM => cayleyRetraction right left P ⟨X, v⟩) (0 : HM) =
      ContinuousLinearMap.id ℝ (HM) :=
  cayleyFibreRetraction_mfderiv_zero right left P X

def tangentProjectionCLM (X : MO) : KMat 𝕂 n →L[ℝ] HM :=
  ({ toFun := tProj X
     map_add' := tangentProjection_add right left P X
     map_smul' := tangentProjection_smul right left P X
   } : KMat 𝕂 n →ₗ[ℝ] HM).toContinuousLinearMap

def ambientRetraction (p : MO × KMat 𝕂 n) : MO := cRet p.1 (tProj p.1 p.2)
set_option hygiene false in
scoped notation "aRet" => ambientRetraction right left P

@[simp] theorem ambientRetraction_val (X : MO) (Z : KMat 𝕂 n) :
    (aRet (X, Z)).val = sCayley X.val Z 1 := by
  change sCayley X.val (iDiff X (tProj X Z)) 1 = _
  rw [inclusion_tangentProjection, sharedCayleyValue_projected]

@[simp] theorem ambientRetraction_zero (X : MO) : aRet (X, 0) = X :=
  Subtype.ext (by simp [ambientRetraction_val, sharedCayleyValue, generatorCayleyValue])

set_option maxHeartbeats 800000 in
theorem ambientRetraction_contMDiff : ContMDiff (I_HP) I_H ⊤ (aRet) := by
  apply (sharedOrbit_contMDiff_iff_ambient right left P (I_HP) (aRet)).mpr
  have hb : ContMDiff (I_HP) I_M ⊤ (fun p : MO × KMat 𝕂 n => p.1.val) :=
    (sharedOrbit_val_contMDiff right left P).comp contMDiff_fst
  have h := (generatorCayleyValue_smooth right left).comp_contMDiff
    (hb.prodMk_space ((minimumNormLift_contMDiff right left P).prodMk_space (contMDiff_const (c := (1 : ℝ)))))
  have he : (fun p : MO × KMat 𝕂 n => (aRet p).val) = (fun p : MO × KMat 𝕂 n => sCayley p.1.val p.2 1) :=
    funext fun ⟨X, Z⟩ => ambientRetraction_val right left P X Z
  rwa [he]

def projectionVerticalInput (p : MO × KMat 𝕂 n) :
    TangentBundle (I_HP) (MO × KMat 𝕂 n) := ⟨(p.1, 0), (0, p.2)⟩

def tangentProjectionBundle (p : MO × KMat 𝕂 n) :
    TangentBundle I_H (MO) := ⟨p.1, tProj p.1 p.2⟩

set_option maxHeartbeats 800000 in
theorem tangentProjectionBundle_contMDiff :
    ContMDiff (I_HP) I_HT ⊤ (tangentProjectionBundle right left P) := by
  have he : tangentProjectionBundle right left P =
      tangentMap (I_HP) I_H (aRet) ∘ projectionVerticalInput right left P := by
    funext ⟨X, Z⟩
    have h1 := GS.Extensions.mfderiv_partial_right I_H (aRet) X
      ((ambientRetraction_contMDiff right left P).mdifferentiable (by simp) (X, 0)) Z
    have h2 := GS.Extensions.mfderiv_retraction_precompose_linear I_H (cRet X)
      (tangentProjectionCLM right left P X)
      ((cayleyFibreRetraction_contMDiff right left P X).mdifferentiable (by simp) 0)
      (cayleyFibreRetraction_mfderiv_zero right left P X) Z
    simp only [Function.comp_apply, tangentProjectionBundle, projectionVerticalInput, tangentMap, h1.symm.trans h2]
    congr 1; exact (ambientRetraction_zero right left P X).symm
  rw [he]
  exact ((ambientRetraction_contMDiff right left P).contMDiff_tangentMap (by simp)).comp
    (GS.Extensions.contMDiff_vertical_input (M := MO) (V := KMat 𝕂 n) I_H)

theorem intrinsicGradientSection_smooth (f : KMat 𝕂 n → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContMDiff I_H I_HT ∞ (fun X : MO => (⟨X, intrinsicGradient right left P f X⟩ : TangentBundle I_H MO)) := by
  have hg : ContDiff ℝ ∞ (kambientGradient f) := kambientGradient_contDiff_of_loss f hf (by simp)
  have hpair : ContMDiff I_H (I_HP) ∞ (fun X : MO => (X, kambientGradient f X.val)) :=
    contMDiff_id.prodMk (hg.comp_contMDiff ((sharedOrbit_val_contMDiff right left P).of_le le_top))
  exact ((tangentProjectionBundle_contMDiff right left P).of_le le_top).comp hpair

end

end GS.SharedGeometry
