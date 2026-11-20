module

public import GS.Shared.Directions
public import Mathlib.Topology.Constructions.SumProd
public import GS.Shared.OrbitAtlas
public import GS.Shared.Frobenius
public import GS.OriginalLocalModel
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Analysis.LocallyConvex.Bounded
public import GS.OverlapGeometry.SliceAtlas
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import GS.Extensions.TangentSections
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false
set_option maxHeartbeats 800000
open Matrix ContinuousLinearMap Function Filter
open scoped Topology Manifold InnerProduct ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GS.Shared.RankLift
variable {G F : Type*} [NormedAddCommGroup G] [NormedAddCommGroup F]
  [InnerProductSpace ℝ G] [InnerProductSpace ℝ F] [FiniteDimensional ℝ G] [FiniteDimensional ℝ F]

private theorem contDiff_real_adjoint : ContDiff ℝ ⊤ (fun A : G →L[ℝ] F => A.adjoint) :=
  (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := G) (F := F)).toContinuousLinearEquiv.contDiff

def frameEquiv (T : G →L[ℝ] F) : T.kerᗮ ≃L[ℝ] T.range :=
  (T.toLinearMap.kerComplementEquivRange T.ker.isCompl_orthogonal.symm).toContinuousLinearEquiv

def lift (T : G →L[ℝ] F) : F →L[ℝ] G :=
  T.kerᗮ.subtypeL ∘L (frameEquiv T).symm.toContinuousLinearMap ∘L T.range.orthogonalProjectionOnto

@[simp] theorem lift_apply (T : G →L[ℝ] F) (z : F) :
    T (lift T z) = T.range.starProjection z :=
  congrArg Subtype.val ((frameEquiv T).apply_symm_apply (T.range.orthogonalProjectionOnto z))

private theorem lift_unique (T : G →L[ℝ] F) (z : F) (y : G)
    (h : T.adjoint (z - T y) = 0) (hy : y ∈ T.kerᗮ) : lift T z = y := by
  refine congrArg Subtype.val ((frameEquiv T).injective (Subtype.ext ?_) :
    (frameEquiv T).symm _ = ⟨y,hy⟩)
  change T (lift T z) = T y
  rw [lift_apply, T.range.eq_starProjection_of_mem_orthogonal (v := T y) ⟨y,rfl⟩
    (by rwa [T.orthogonal_range] : z - T y ∈ T.rangeᗮ)]

private theorem gram_invertible {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (K : H →L[ℝ] F) (hK : Injective K) : (K.adjoint ∘L K).IsInvertible := by
  exact ⟨(LinearEquiv.ofInjectiveEndo (K.adjoint ∘L K).toLinearMap
    (K.adjoint_comp_self_injective_iff.mpr hK)).toContinuousLinearEquiv, rfl⟩

/-- The least-norm lift is smooth in constant-rank families. At a base point
we use its range as a frame for the ranges of the nearby Gram operators. -/
theorem lift_contMDiff {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X] {I : ModelWithCorners ℝ E H}
    {T : X → G →L[ℝ] F} (hT : ContMDiff I 𝓘(ℝ,G →L[ℝ] F) ⊤ T)
    (hr : ∀ x y, Module.finrank ℝ (T x).range = Module.finrank ℝ (T y).range) :
    ContMDiff I 𝓘(ℝ,F →L[ℝ] G) ⊤ (fun x => lift (T x)) := by
  intro x
  let U := (T x).range
  let B (y : X) : U →L[ℝ] G := (T y).adjoint ∘L U.subtypeL
  let C y := T y ∘L B y
  let A y := (C y).adjoint ∘L C y
  have hc : Injective (C x) := by
    apply LinearMap.ker_eq_bot.mp
    change (Submodule.comap U.subtype ((T x) ∘L (T x).adjoint).ker) = ⊥
    rw [(T x).ker_self_comp_adjoint, ← (T x).orthogonal_range, ← Submodule.disjoint_iff_comap_eq_bot]
    exact U.orthogonal_disjoint
  have ha := gram_invertible (C x) hc
  have hA : ContMDiff I 𝓘(ℝ,U →L[ℝ] U) ⊤ A := by
    unfold A C B
    repeat' first | exact hT | exact contMDiff_const | apply ContMDiff.clm_comp |
      apply contDiff_real_adjoint.comp_contMDiff
  have hi := ha.contDiffAt_map_inverse.comp_contMDiffAt (f := A) (hA x)
  let f y := B y ∘L (A y).inverse ∘L (C y).adjoint
  have hf : ContMDiffAt I 𝓘(ℝ,F →L[ℝ] G) ⊤ f x := by
    unfold f C B
    repeat' first | exact hT x | exact hi | exact contMDiffAt_const | apply ContMDiffAt.clm_comp |
      apply contDiff_real_adjoint.contDiffAt.comp_contMDiffAt
  apply hf.congr_of_eventuallyEq
  filter_upwards [(hA.continuous.continuousAt (x := x)).eventually ha.eventually_nhds] with y hy
  have hc' : Injective (C y) := by
    exact Injective.of_comp (f := (C y).adjoint) (g := C y) (show (A y).IsInvertible from hy).bijective.1
  have hR : (C y).range = (T y).range := Submodule.eq_of_le_of_finrank_eq
    (LinearMap.range_comp_le_range ..)
    ((LinearEquiv.ofInjective (C y).toLinearMap hc').finrank_eq.symm.trans (hr x y))
  ext z
  refine lift_unique _ _ _ ?_ ?_
  · change z - T y (f y z) ∈ (T y).adjoint.ker
    rw [← (T y).orthogonal_range, ← hR, (C y).orthogonal_range, LinearMap.mem_ker, map_sub]
    exact sub_eq_zero.mpr ((show (A y).IsInvertible from hy).self_apply_inverse _).symm
  · rw [(T y).orthogonal_ker]
    aesop

end GS.Shared.RankLift

namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

variable (right left : Pattern 𝕜 n)

/-- Canonical ambient Frobenius projection at a matrix point. -/
def pointProjection (X : M 𝕜 n) : M 𝕜 n →L[ℝ] M 𝕜 n :=
  frobProjection (pointDirections right left X)

abbrev LiftSpace := EuclideanSpace ℝ (Fin (Module.finrank ℝ (PairGenerator right left)))

def liftEquiv : PairGenerator right left ≃L[ℝ] LiftSpace right left :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

def liftSynthesis (X : M 𝕜 n) : LiftSpace right left →L[ℝ] FrobCoordinates 𝕜 n :=
  (frobEquiv 𝕜 n).toContinuousLinearMap ∘L (orbitDerivative right left X) ∘L
    (liftEquiv right left).symm.toContinuousLinearMap

private theorem orbitDerivative_smooth : ContDiff ℝ ⊤ (orbitDerivative right left) := by
  apply contDiff_clm_apply_iff.mpr
  intro y
  simp only [orbitDerivative_apply]
  fun_prop

local notation "Gens" => PairGenerator right left
local notation "A" => M 𝕜 n
local notation "S" => liftSynthesis right left

private theorem synthesis_range (X : A) : (S X).range = encodedSubspace (pointDirections right left X) := by
  change LinearMap.range ((frobEquiv 𝕜 n).toLinearEquiv.toLinearMap.comp
    ((orbitDerivative right left X).toLinearMap.comp (liftEquiv right left).symm.toLinearEquiv.toLinearMap)) = _
  rw [LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]
  rfl

private theorem synthesis_rank (P : A) (X : MatrixOrbit right left P) :
    Module.finrank ℝ (S X.val).range = Module.finrank ℝ (S P).range := by
  obtain ⟨g,hg⟩ := X.property
  rw [← hg, synthesis_range, synthesis_range]
  unfold encodedSubspace
  rw [LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq, ← action_pointDirections,
    LinearEquiv.finrank_map_eq]

def gramLift (X : A) : A →L[ℝ] Gens :=
  (liftEquiv right left).symm.toContinuousLinearMap ∘L RankLift.lift (S X) ∘L
    (frobEquiv 𝕜 n).toContinuousLinearMap

theorem gramLift_synthesis (X Z : A) :
    orbitDerivative right left X (gramLift right left X Z) = pointProjection right left X Z := by
  apply (frobEquiv 𝕜 n).injective
  change S X (RankLift.lift (S X) (frobEquiv 𝕜 n Z)) = _
  rw [RankLift.lift_apply]
  exact (congrArg (fun T : Submodule ℝ (FrobCoordinates 𝕜 n) => T.starProjection (𝕜 := ℝ)
    (frobEquiv 𝕜 n Z)) (synthesis_range right left X)).trans
    ((frobEquiv 𝕜 n).apply_symm_apply _).symm

variable (P : M 𝕜 n)
local notation "E" => HorizontalModel right left P
local notation "O" => MatrixOrbit right left P
local notation "I" => 𝓘(ℝ, E)
local notation "J" => 𝓘(ℝ, A)
local instance : NormedSpace ℝ E := Submodule.normedSpace _
local instance : ChartedSpace E O := sharedOrbitChartedSpace right left P
local instance : IsManifold I ⊤ O := sharedOrbitIsManifold right left P

/-- Full image of the actual mathlib manifold differential. -/
theorem orbit_tangent_image_iff (X : O) (Z : A) :
    (∃ v, inclusionDifferential right left P X v = Z) ↔
      Z ∈ pointDirections right left X.val := by
  rw [inclusionDifferential_eq]
  change Z ∈ LinearMap.range ((actionLinearEquiv (preferredFactor P X)).toLinearMap.comp
    (GS.OverlapGeometry.horizontalRestriction (orbitDerivative right left P)).toLinearMap) ↔ _
  rw [LinearMap.range_comp, GS.OverlapGeometry.horizontalRestriction_range,
    show (orbitDerivative right left P).range = pointDirections right left P from rfl,
    action_pointDirections, preferredFactor_spec]

private theorem derivative_contMDiff : ContMDiff I 𝓘(ℝ,Gens →L[ℝ] A) ⊤
    (fun X : O => orbitDerivative right left X.val) :=
  (orbitDerivative_smooth right left).comp_contMDiff (sharedOrbit_val_contMDiff right left P)

private theorem gramLift_contMDiff : ContMDiff ((I).prod J) 𝓘(ℝ,Gens) ⊤
    (fun p : O × A => gramLift right left p.1.val p.2) := by
  have hS : ContMDiff I 𝓘(ℝ,LiftSpace right left →L[ℝ] FrobCoordinates 𝕜 n) ⊤ (fun X : O => S X.val) :=
    contMDiff_const.clm_comp ((derivative_contMDiff right left P).clm_comp contMDiff_const)
  have h := RankLift.lift_contMDiff hS
    (fun x y => (synthesis_rank right left P x).trans (synthesis_rank right left P y).symm)
  exact (liftEquiv right left).symm.contDiff.comp_contMDiff <| (h.comp contMDiff_fst).clm_apply
    ((frobEquiv 𝕜 n).contDiff.comp_contMDiff contMDiff_snd)

theorem pointProjection_contMDiff : ContMDiff ((I).prod J) J ⊤
    (fun p : O × A => pointProjection right left p.1.val p.2) :=
  (((derivative_contMDiff right left P).comp contMDiff_fst).clm_apply
    (gramLift_contMDiff right left P)).congr fun p => (gramLift_synthesis right left p.1.val p.2).symm

/-- Reuse the orbit slice Cayley update, lifting its input through the orbit differential. -/
def ambientCayley (p : O × A) : O :=
  factorLift 1 (gramLift right left p.1.val p.2) • p.1

@[simp] theorem ambientCayley_zero (X : O) : ambientCayley right left P (X, 0) = X := by
  simp [ambientCayley]

theorem ambientCayley_contMDiff : ContMDiff ((I).prod J) I ⊤ (ambientCayley right left P) := by
  apply GS.OverlapGeometry.slice_contMDiff_of_ambient (preferredOrbitSlice right left P)
    (preferredOrbitSlice_covers right left P)
  let f (p : A × Gens) := orbitParam 1 p.1 p.2
  change ContMDiff ((I).prod J) J ⊤ (f ∘ fun p : O × A => (p.1.val, gramLift right left p.1.val p.2))
  exact (orbitParam_smooth (1 : Factors right left)).comp_contMDiff (g := f)
    (((sharedOrbit_val_contMDiff right left P).comp contMDiff_fst).prodMk_space
      (gramLift_contMDiff right left P))

theorem ambientCayley_fderiv (X : O) (Z : A) :
    fderiv ℝ (fun W => (ambientCayley right left P (X, W)).val) 0 Z =
      pointProjection right left X.val Z := by
  let L := gramLift right left X.val
  have h : HasFDerivAt (orbitParam 1 X.val) (orbitDerivative right left X.val) (L 0) := by
    simpa only [map_zero] using orbitParam_hasFDerivAt_zero (right := right) (left := left) X.val
  exact (DFunLike.congr_fun (h.comp 0 L.hasFDerivAt).fderiv Z).trans (gramLift_synthesis right left X.val Z)

local notation "U" => ambientCayley right left P

private theorem ambientCayley_mdifferentiable (X : O) : MDifferentiableAt ((I).prod J) I U (X,0) :=
  (ambientCayley_contMDiff right left P).mdifferentiable (by simp) _

/-- The vertical differential of the Cayley update lifts ambient vectors to tangent vectors. -/
def liftBundle (p : O × A) : TangentBundle I O :=
  ⟨p.1, mfderiv ((I).prod J) I U (p.1,0) (0,p.2)⟩

theorem liftBundle_contMDiff : ContMDiff ((I).prod J) (I).tangent ⊤ (liftBundle right left P) := by
  apply (((ambientCayley_contMDiff right left P).contMDiff_tangentMap (by simp)).comp
    (GS.Extensions.contMDiff_vertical_input (V := A) I)).congr
  intro p
  simp only [Function.comp_apply, tangentMap, liftBundle]
  congr 1
  exact (ambientCayley_zero right left P p.1).symm

theorem inclusion_liftBundle (X : O) (Z : A) :
    inclusionDifferential right left P X (liftBundle right left P (X, Z)).2 =
      pointProjection right left X.val Z := by
  have hU := ambientCayley_mdifferentiable right left P X
  have h := (sharedOrbit_val_contMDiff right left P).mdifferentiable (by simp) X
  change mfderiv I J Subtype.val X (mfderiv ((I).prod J) I U (X,0) (0,Z)) = _
  rw [← mfderiv_comp_apply_of_eq (X,0) h hU (ambientCayley_zero right left P X),
    ← GS.Extensions.mfderiv_fibre I _ X (h.comp_of_eq _ hU (ambientCayley_zero right left P X)),
    mfderiv_eq_fderiv]
  exact ambientCayley_fderiv right left P X Z

/-- The whole tangent bundle retraction evaluates the same ambient extension. -/
def cayleyBundle (p : TangentBundle I O) : O :=
  ambientCayley right left P (p.proj, inclusionDifferential right left P p.proj p.2)

theorem cayleyBundle_contMDiff : ContMDiff (I).tangent I ⊤ (cayleyBundle right left P) :=
  (ambientCayley_contMDiff right left P).comp ((Bundle.contMDiff_proj (TangentSpace I)).prodMk
    ((contMDiff_snd_tangentBundle_modelSpace A J).comp
      ((sharedOrbit_val_contMDiff right left P).contMDiff_tangentMap (by simp))))

theorem cayleyBundle_zero (X : O) : cayleyBundle right left P ⟨X, 0⟩ = X := by
  simp [cayleyBundle]

theorem cayleyBundle_fibre (X : O) :
    mfderiv I I (fun v : E => cayleyBundle right left P ⟨X,v⟩) 0 = ContinuousLinearMap.id ℝ E := by
  let L := inclusionDifferential right left P X
  have h := ambientCayley_mdifferentiable right left P X
  have hL := (L.mdifferentiableAt (x := (0 : E)))
  ext v : 1
  change mfderiv I I (U ∘ fun z : E => (X,L z)) 0 v = v
  rw [mfderiv_comp_apply_of_eq 0 h (mdifferentiableAt_const.prodMk hL) (by simp),
    mfderiv_prodMk mdifferentiableAt_const hL, mfderiv_const, L.mfderiv_eq]
  change (liftBundle right left P (X,L v)).2 = v
  apply inclusionDifferential_injective right left P X
  exact (inclusion_liftBundle right left P X _).trans
    (frobProjection_of_mem _ _ ((orbit_tangent_image_iff right left P X _).mp ⟨v,rfl⟩))

def liftedGradient (f : A → ℝ) (X : O) : E :=
  (liftBundle right left P (X, ambientGradient f X.val)).2

theorem liftedGradient_smooth (f : A → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContMDiff I (I).tangent ∞ (fun X : O => (⟨X,liftedGradient right left P f X⟩ : TangentBundle I O)) :=
  ((liftBundle_contMDiff right left P).of_le le_top).comp
    (contMDiff_id.prodMk ((ambientGradient_contDiff_of_loss f hf (by simp)).comp_contMDiff
      ((sharedOrbit_val_contMDiff right left P).of_le le_top)))

theorem liftedGradient_characterization (f : A → ℝ) (X : O) (hf : DifferentiableAt ℝ f X.val)
    (v : E) : frobInner (inclusionDifferential right left P X (liftedGradient right left P f X))
      (inclusionDifferential right left P X v) = mfderiv I 𝓘(ℝ, ℝ) (fun Y : O => f Y.val) X v := by
  have h := mfderiv_comp_apply X hf.mdifferentiableAt
    ((sharedOrbit_val_contMDiff right left P).mdifferentiable (by simp) X) v
  rw [mfderiv_eq_fderiv] at h
  rw [liftedGradient, inclusion_liftBundle, pointProjection,
    frobProjection_inner _ _ _ ((orbit_tangent_image_iff right left P X _).mp ⟨v,rfl⟩),
    ← ambientGradient_represents]
  exact h.symm

end GS.Shared
