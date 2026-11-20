module

public import GS.Isometric.Pseudo
public import GS.Isometric.OrbitAtlas
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

@[expose] public section

/-! Split the generator map analytically over the orbit. An arbitrary fixed
Euclidean basis on the generator space suffices: the *image* projection in
the splitting formula is the Frobenius one. Apply unit-speed Cayley in both
factors to the resulting generators. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open Matrix Function
open scoped Manifold
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace GS.Isometric
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (r l : Layer 𝕜 n) (P : Square 𝕜 n)
local notation "A" => Square 𝕜 n
local notation "G" => PairGenerator r l
local notation "H" => HorizontalModel r l P
local notation "M" => MatrixOrbit r l P
local notation "I" => 𝓘(ℝ,H)
local notation "J" => 𝓘(ℝ,A)
local instance : NormedSpace ℝ H := Submodule.normedSpace _
local instance : ChartedSpace H M := sharedOrbitChartedSpace r l P

def euclid : G ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ G)) := .ofFinrankEq (by simp)
def du (X : A) := ((euclid r l).arrowCongr encode) ((pointMap r l X).toContinuousLinearMap)
lemma du_range (X : A) : (du r l X).range = (pointDirections r l X).map encode.toLinearMap := by
  ext z; constructor
  · rintro ⟨v,rfl⟩; exact ⟨_,⟨_,rfl⟩,rfl⟩
  · rintro ⟨_,⟨v,rfl⟩,rfl⟩; exact ⟨euclid r l v,by simp [du]⟩

abbrev pointProjection (X : A) := projection (pointDirections r l X)

def velocityLift (X : A) : A →L[ℝ] G := (euclid r l).symm.toContinuousLinearMap ∘L Pseudo.lift (du r l X) ∘L encode.toContinuousLinearMap
lemma velocityLift_spec (X Z : A) : pointMap r l X (velocityLift r l X Z) = pointProjection r l X Z := by
  apply encode.injective; rw [pointProjection,encode_projection]
  exact (Pseudo.lift_spec (du r l X) (encode Z)).trans (congrArg (fun S : Submodule ℝ (Coordinates 𝕜 n) => S.starProjection (encode Z)) (du_range r l X))

lemma map_smooth : ContDiff ℝ ⊤ (fun X : A => (pointMap r l X).toContinuousLinearMap) :=
  contDiff_clm_apply_iff.2 fun v => (smooth_matrix_product contDiff_const contDiff_id).sub (smooth_matrix_product contDiff_id contDiff_const)
lemma velocityLift_smooth : ContMDiff ((I).prod J) 𝓘(ℝ,G) ⊤ (fun x : M × A => velocityLift r l x.1.val x.2) := by
  suffices h : ContMDiff I 𝓘(ℝ,A →L[ℝ] G) ⊤ (fun x : M => velocityLift r l x.val) from (h.comp contMDiff_fst).clm_apply contMDiff_snd
  apply ParamAt.out (orbitPatch r l P); intro x
  let a := orbitPatch r l P
  have dim (y : M) : Module.finrank ℝ (du r l y.val).range = Module.finrank ℝ H := by
    rw [du_range,encode.toLinearEquiv.finrank_map_eq,← patch_range r l P,LinearMap.finrank_range_of_inj (a y).regular.injective]
  have d : ContDiff ℝ ⊤ (du r l) := contDiff_const.clm_comp ((map_smooth r l).clm_comp contDiff_const)
  exact contDiff_const.clm_comp ((Pseudo.smooth (d.comp (a x).smooth) (fun z => dim ((a x).param z))).clm_comp contDiff_const)

lemma projection_joint : ContMDiff ((I).prod J) J ⊤ (fun x : M × A => pointProjection r l x.1.val x.2) := by
  simp_rw [← velocityLift_spec]
  exact (((map_smooth r l).comp_contMDiff (ParamAt.inclusion (orbitPatch r l P))).comp contMDiff_fst).clm_apply (velocityLift_smooth r l P)

def step (p : M × A) : M := frames (velocityLift r l p.1.val p.2) • p.1
lemma step_zero (x : M) : step r l P (x,0) = x := by simp only [step,map_zero,frames_zero,one_smul]
lemma step_smooth : ContMDiff ((I).prod J) I ⊤ (step r l P) := by
  apply ParamAt.into (orbitPatch r l P)
  exact (move_smooth (r := r) (l := l)).comp_contMDiff (f := fun p : M × A => (p.1.val,velocityLift r l p.1.val p.2)) (((ParamAt.inclusion (orbitPatch r l P)).comp contMDiff_fst).prodMk_space (velocityLift_smooth r l P))
lemma step_line (x : M) (Z : A) : HasDerivAt (fun t : ℝ => (step r l P (x,t • Z)).val) (pointProjection r l x.val Z) 0 := by
  simpa only [step,MulAction.orbit.coe_smul,map_smul,velocityLift_spec] using move_line x.val (velocityLift r l x.val Z)
end GS.Isometric
