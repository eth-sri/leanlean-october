module

public import GS.Isometric.SplitStep
public import GS.Extensions.AmbientStep
public import GS.Isometric.Blocks

@[expose] public section

/-! The same embedded geometry for the unitary groups of every pair of real matrix star subalgebras. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix
open scoped Manifold ContDiff
namespace GSPalomar
/-- A finite-dimensional atlas on the given matrix subtype, an injective
inclusion differential with exactly the prescribed tangent image, a jointly
smooth orthogonal projector, a smooth whole-tangent-bundle retraction, and
smooth gradient sections for every smooth ambient loss. The topology of the
subtype is fixed before the atlas is chosen. -/
def EmbeddedGeometry {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (pairing : A → A → ℝ) (S : Set A) (D : A → A → Prop) : Prop :=
  ∃ E : Type, ∃ normE : NormedAddCommGroup E, letI := normE
  ∃ spaceE : NormedSpace ℝ E, letI := spaceE
  FiniteDimensional ℝ E ∧
  ∃ cs : ChartedSpace E S, letI := cs
  ∃ hm : IsManifold (𝓘(ℝ, E)) ⊤ S, letI := hm
  ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, A)) ⊤ (fun X : S => X.val) ∧
  (∀ X : S, Function.Injective (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, A))
    (fun Y : S => Y.val) X)) ∧
  (∀ (X : S) (Z : A), D X.val Z ↔ ∃ v : E,
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, A)) (fun Y : S => Y.val) X v = Z) ∧
  (∃ π : S × A → A,
    ContMDiff ((𝓘(ℝ, E)).prod (𝓘(ℝ, A))) (𝓘(ℝ, A)) ⊤ π ∧
    ∀ (X : S) (Z : A), D X.val (π (X, Z)) ∧
      ∀ Y : A, D X.val Y → pairing (Z - π (X, Z)) Y = 0) ∧
  (∃ R : TangentBundle (𝓘(ℝ, E)) S → S,
    ContMDiff (𝓘(ℝ, E)).tangent (𝓘(ℝ, E)) ⊤ R ∧
    (∀ X : S, R ⟨X, 0⟩ = X) ∧
    ∀ X : S, mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E))
      (fun v : E => R ⟨X, v⟩) 0 = ContinuousLinearMap.id ℝ E) ∧
  (∀ f : A → ℝ, ContDiff ℝ ∞ f → ∃ g : S → E,
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)).tangent ∞
      (fun X : S => (⟨X, g X⟩ : TangentBundle (𝓘(ℝ, E)) S)) ∧
    ∀ (X : S) (v : E),
      pairing (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, A)) (fun Y : S => Y.val) X (g X))
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, A)) (fun Y : S => Y.val) X v) =
      mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) (fun Y : S => f Y.val) X v)
end GSPalomar
namespace GS.Isometric
variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
set_option maxHeartbeats 1600000

section
open GS.Extensions.AmbientStep
variable (r l : Layer 𝕜 n) (P : Square 𝕜 n)
local notation "A" => Square 𝕜 n
local notation "E" => HorizontalModel r l P
local notation "M" => MatrixOrbit r l P
local notation "I" => 𝓘(ℝ,E)
local notation "J" => 𝓘(ℝ,A)
local instance : NormedSpace ℝ E := Submodule.normedSpace _
local instance : ChartedSpace E M := sharedOrbitChartedSpace r l P
local instance : IsManifold I ⊤ M := ParamAt.manifold (orbitPatch r l P)

theorem embedded :
    GSPalomar.EmbeddedGeometry pairing {X | InOrbit r l P X}
      (fun X Z => Z ∈ pointDirections r l X) := by
  rw [← orbit_set_eq_inShared]
  let i : M → A := Subtype.val
  let F := step r l P
  let D (x : M) := mfderiv J I (fun z : A => F (x,z)) 0
  have hi := ParamAt.inclusion (orbitPatch r l P)
  have hF := step_smooth r l P
  have h₀ := step_zero r l P
  have df := ParamAt.differential (orbitPatch r l P)
  have dinj (x : M) : Function.Injective (mfderiv I J i x) := df x ▸ (orbitPatch r l P x).regular.injective
  have image (x : M) : (mfderiv I J i x).range = pointDirections r l x.val := (df x) ▸ patch_range r l P x
  have d (x : M) (z : A) : mfderiv I J i x (D x z) = pointProjection r l x.val z :=
    differential hi hF h₀ (step_line r l P x z)
  have fix (x : M) (v : E) : pointProjection r l x.val (mfderiv I J i x v) = mfderiv I J i x v := projection_of_mem _ _ (image x ▸ (LinearMap.mem_range_self _ v))
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hi, dinj, fun x Z => by change Z ∈ pointDirections r l x.val ↔ _; rw [← image x]; rfl, ?_, ?_, ?_⟩
  · exact ⟨_, projection_joint r l P, fun X Z =>
      ⟨projection_mem _ _,projection_normal _ _⟩⟩
  · exact retraction hi hF h₀ dinj fun x v => (d x _).trans (fix x v)
  · intro f hf
    refine ⟨fun x => D x (ambientGradient f x.val), liftSmooth hF h₀
      ((ambientGradient_contDiff_of_loss f hf (by simp)).comp_contMDiff (hi.of_le le_top)), ?_⟩
    intro x v
    change pairing (mfderiv I J i x _) (mfderiv I J i x v) = _
    rw [d, projection_self_adjoint,fix x v,← ambientGradient_represents]
    simpa only [mfderiv_eq_fderiv] using! (mfderiv_comp_apply_of_eq x (hf.differentiable (by simp) (i x)).mdifferentiableAt
      (hi.mdifferentiable (by simp) x) rfl v).symm

end

lemma blockFactor_iff (b τ hb hd) (A : Square 𝕜 n) : SharedFactor (blocks 𝕜 b τ hb hd) A ↔ BlockFactor b τ A := by
  change (_ ∧ _) ∧ _ ↔ _ ∧ _ ∧ _; tauto

lemma blockGenerator_iff (b τ hb hd) (A : Square 𝕜 n) : A ∈ skewSpace (blocks 𝕜 b τ hb hd) ↔ DiagonalBlocks b A ∧ Skew A ∧ Tied b τ A := by
  change (_ ∧ _) ∧ _ ↔ _ ∧ _ ∧ _; tauto

lemma pairing_entries (A B : Square 𝕜 n) : pairing A B =
    ∑ i, ∑ j, (RCLike.re (A i j) * RCLike.re (B i j) + RCLike.im (A i j) * RCLike.im (B i j)) := by
  simp only [pairing_trace, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    map_sum, RCLike.star_def, RCLike.mul_re, RCLike.conj_re, RCLike.conj_im, neg_mul, sub_neg_eq_add]
  exact Finset.sum_comm

theorem block_geometry (b₁ b₂ : ℕ) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hd₁ : b₁ ∣ n) (hd₂ : b₂ ∣ n)
    (τ₁ τ₂ : ℕ → ℕ) (P : Square 𝕜 n) :
    GSPalomar.EmbeddedGeometry (fun A B : Square 𝕜 n => ∑ i, ∑ j,
      (RCLike.re (A i j) * RCLike.re (B i j) + RCLike.im (A i j) * RCLike.im (B i j)))
      {X | Shared₂ b₁ b₂ τ₁ τ₂ P X}
      (BlockDirections b₁ b₂ τ₁ τ₂) := by
  have h := embedded (blocks 𝕜 b₁ τ₁ hb₁ hd₁) (blocks 𝕜 b₂ τ₂ hb₂ hd₂) P
  simpa only [Shared₂, InOrbit, blockFactor_iff, BlockDirections, mem_pointDirections_iff,
    blockGenerator_iff, show pairing (𝕜 := 𝕜) (n := n) = _ from funext fun A => funext (pairing_entries A)] using! h
end GS.Isometric
