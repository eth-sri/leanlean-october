module

public import GSChecked

public import GS.Shared.Geodesic

@[expose] public section

/-! # Proofs of the Palomar statement of record

Every declaration below is proved by the full library. Challenge is never
imported here. The existing project README and coverage documents describe
the paper correspondence and the additional results.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
open Matrix
open scoped BigOperators Manifold ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GSPalomar

/-- Every orthogonal matrix in the two-layer class admits orthogonal layers. -/
theorem two_factor (n : ℕ) (s₁ s₂ : GS.BlockSpec n)
    (σ : Equiv.Perm (Fin n)) (A : GS.Mat n) :
    GS.InA2 s₁.size s₂.size (GS.permMatrix σ) A ∧ GS.Orthogonal A ↔
      GS.InA2Orth s₁.size s₂.size (GS.permMatrix σ) A :=
  GS.Shared.twoFactor s₁.size s₂.size σ A

/-- The same equality holds for three layers and arbitrary fixed permutations. -/
theorem three_factor (n : ℕ) (s₁ s₂ s₃ : GS.BlockSpec n)
    (σ₁ σ₂ : Equiv.Perm (Fin n)) (A : GS.Mat n) :
    GS.InA3 s₁.size s₂.size s₃.size (GS.permMatrix σ₁) (GS.permMatrix σ₂) A ∧
      GS.Orthogonal A ↔
    GS.InA3Orth s₁.size s₂.size s₃.size (GS.permMatrix σ₁) (GS.permMatrix σ₂) A :=
  GS.Shared.threeFactor s₁.size s₂.size s₃.size σ₁ σ₂ A

open GS GS.UnitaryGeometry

/-- Unrestricted two-layer unitary matrices admit unitary layers. -/
theorem unitary_two_factor {n : ℕ} (b₁ b₂ : ℕ)
    (σ : Equiv.Perm (Fin n)) (A : CMat n) :
    CInA2 b₁ b₂ (cPermMatrix σ) A ∧ Unitary A ↔
      CInA2Unitary b₁ b₂ (cPermMatrix σ) A := GS.Shared.twoFactor b₁ b₂ σ A

/-- Unrestricted three-layer unitary matrices admit unitary layers. -/
theorem unitary_three_factor {n : ℕ} (b₁ b₂ b₃ : ℕ)
    (σ₁ σ₂ : Equiv.Perm (Fin n)) (A : CMat n) :
    CInA3 b₁ b₂ b₃ (cPermMatrix σ₁) (cPermMatrix σ₂) A ∧ Unitary A ↔
      CInA3Unitary b₁ b₂ b₃ (cPermMatrix σ₁) (cPermMatrix σ₂) A := GS.Shared.threeFactor b₁ b₂ b₃ σ₁ σ₂ A

/-- The scalar (p,2,p) family fills the orthogonal group (including p=0). -/
theorem real_cs_exhaustion {p : ℕ} {A : Mat (2*p)} :
    InA3Orth p 2 p (permMatrix (scalarShuffle 2 p))
      (permMatrix (scalarShuffle 2 p))ᵀ A ↔ Orthogonal A := GS.Shared.cs_exhaustion

/-- Complex cosine-sine decomposition gives the entire unitary group. -/
theorem unitary_cs_exhaustion {p : ℕ} {A : CMat (2*p)} :
    CInA3Unitary p 2 p (cPermMatrix (scalarShuffle 2 p))
      (cPermMatrix (scalarShuffle 2 p))ᴴ A ↔ Unitary A := GS.Shared.cs_exhaustion

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

/-- Exact real tangent directions in the unitary case; phases are retained. -/
def ComplexDirections {n : ℕ} (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (X Z : CMat n) : Prop :=
  ∃ C Ω : CMat n,
    (CBlockDiagonal b₂ C ∧ Cᴴ = -C ∧ GS.UnitarySharing.TiedEntries b₂ τ₂ C) ∧
    (CBlockDiagonal b₁ Ω ∧ Ωᴴ = -Ω ∧ GS.UnitarySharing.TiedEntries b₁ τ₁ Ω) ∧
    Z = C * X + X * Ω

open GS.Shared in
private theorem shared_geometry {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (right left : Pattern 𝕜 n) (P : M 𝕜 n) :
    EmbeddedGeometry GS.Shared.frobInner
      {X | InSharedA2Unitary right.size left.size right.label left.label P X}
      (SharedDirections right.size left.size right.label left.label) := by
  rw [← orbit_set_eq_inShared (right := right) (left := left) P]
  let E := HorizontalModel right left P
  letI : ChartedSpace E (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P
  letI : IsManifold (𝓘(ℝ, E)) ⊤ (MatrixOrbit right left P) := sharedOrbitIsManifold right left P
  have hdir X Z := (mem_pointDirections_iff (right := right) (left := left) X Z).symm
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    sharedOrbit_val_contMDiff right left P, inclusionDifferential_injective right left P,
    ?_, ?_, ?_, ?_⟩
  · intro X Z
    exact (hdir X.val Z).trans (orbit_tangent_image_iff right left P X Z).symm
  · exact ⟨fun p => pointProjection right left p.1.val p.2, pointProjection_contMDiff right left P,
      fun X Z => ⟨(hdir _ _).mpr (frobProjection_mem (pointDirections right left X.val) Z),
        fun Y hY => frobProjection_normal (pointDirections right left X.val) Z Y ((hdir _ _).mp hY)⟩⟩
  · exact ⟨cayleyBundle right left P, cayleyBundle_contMDiff right left P,
      cayleyBundle_zero right left P, cayleyBundle_fibre right left P⟩
  · exact fun f hf => ⟨liftedGradient right left P f,
      liftedGradient_smooth right left P f hf, fun X v =>
        liftedGradient_characterization right left P f X ((hf.differentiable (by simp)) X) v⟩

/-- Smooth geometry of the actual orthogonal image, including arbitrary overlap,
complete within-layer sharing, and arbitrary fixed carriers. -/
theorem orthogonal_shared_geometry {n : ℕ} (b₁ b₂ : ℕ)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hd₁ : b₁ ∣ n) (hd₂ : b₂ ∣ n)
    (τ₁ τ₂ : ℕ → ℕ) (P : Mat n) :
    EmbeddedGeometry (fun A B : Mat n => ∑ i, ∑ j, A i j * B i j)
      {X | GS.GlobalGeometry.InSharedA2Orth b₁ b₂ τ₁ τ₂ P X}
      (RealDirections b₁ b₂ τ₁ τ₂) := by
  have hp : GS.Shared.frobInner = fun A B : Mat n => ∑ i, ∑ j, A i j * B i j :=
    funext fun A => funext fun B => GS.Shared.frobInner_eq_sum A B
  rw [← hp]
  exact shared_geometry (𝕜 := ℝ) ⟨b₁, hd₁, τ₁⟩ ⟨b₂, hd₂, τ₂⟩ P

/-- The same real differential geometry for shared unitary layers, with the
full continuous stabilizer allowed. No special-unitary restriction is imposed. -/
theorem unitary_shared_geometry {n : ℕ} (b₁ b₂ : ℕ)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hd₁ : b₁ ∣ n) (hd₂ : b₂ ∣ n)
    (τ₁ τ₂ : ℕ → ℕ) (P : CMat n) :
    EmbeddedGeometry (fun A B : CMat n =>
      ∑ i, ∑ j, ((A i j).re * (B i j).re + (A i j).im * (B i j).im))
      {X | GS.UnitarySharing.InSharedA2Unitary b₁ b₂ τ₁ τ₂ P X}
      (ComplexDirections b₁ b₂ τ₁ τ₂) := by
  have hp : GS.Shared.frobInner = fun A B : CMat n =>
      ∑ i, ∑ j, ((A i j).re * (B i j).re + (A i j).im * (B i j).im) := by
    funext A B
    rw [GS.Shared.frobInner_eq_sum]
    change ∑ i, ∑ j, (star (A i j) * B i j).re = _
    simp [Complex.mul_re]
  rw [← hp]
  exact shared_geometry (𝕜 := ℂ) ⟨b₁, hd₁, τ₁⟩ ⟨b₂, hd₂, τ₂⟩ P

end GSPalomar
