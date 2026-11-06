module

public import GS.Shared.Factorization
public import GS.Specifications
public import GS.UnitaryCS.ColumnGram
public import GS.GlobalGeometry.SharedDescent
public import GS.Results.OriginalCellRank
public import GS.UnitaryCS.Bridge
public import GS.Shared.GradientSection
public import GS.UnitarySharing.Orbit
public import GS.UnitaryTopology.MatrixNonmanifold


@[expose] public section

/-! # Proofs of the Palomar statement of record

Every declaration below is proved by the full library. Challenge is never
imported here. The existing project README and coverage documents describe
the paper correspondence and the additional results.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators Manifold ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GSPalomar

/-- Every orthogonal matrix in the two-layer class admits orthogonal layers. -/
theorem two_factor (n : ℕ) (s₁ s₂ : GS.BlockSpec n)
    (σ : Equiv.Perm (Fin n)) (A : GS.Mat n) :
    GS.InA2 s₁.size s₂.size (GS.permMatrix σ) A ∧ GS.Orthogonal A ↔
      GS.InA2Orth s₁.size s₂.size (GS.permMatrix σ) A :=
  GS.Shared.twoFactor (𝕜 := ℝ) _ _ σ A

/-- The same equality holds for three layers and arbitrary fixed permutations. -/
theorem three_factor (n : ℕ) (s₁ s₂ s₃ : GS.BlockSpec n)
    (σ₁ σ₂ : Equiv.Perm (Fin n)) (A : GS.Mat n) :
    GS.InA3 s₁.size s₂.size s₃.size (GS.permMatrix σ₁) (GS.permMatrix σ₂) A ∧
      GS.Orthogonal A ↔
    GS.InA3Orth s₁.size s₂.size s₃.size (GS.permMatrix σ₁) (GS.permMatrix σ₂) A :=
  GS.Shared.threeFactor (𝕜 := ℝ) _ _ _ σ₁ σ₂ A

/-- Four 2-by-2-block layers need not admit an orthogonal-layer realization. -/
theorem four_factor_counterexample :
    ∃ A : GS.Mat 6,
      GS.InA4 2 2 2 2 GS.M4.P GS.M4.P GS.M4.P A ∧ GS.Orthogonal A ∧
      ¬ GS.InA4Orth 2 2 2 2 GS.M4.P GS.M4.P GS.M4.P A :=
  ⟨GS.M4.Q, GS.M4.counterexample⟩

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

/-- Allowing complex unitary layers does not remove the four-layer obstruction. -/
theorem unitary_four_factor_counterexample :
    ∃ A : CMat 6, let P : CMat 6 := fun i j => (GS.M4.P i j : ℂ)
      CInA4 2 2 2 2 P P P A ∧ Unitary A ∧ ¬CInA4Unitary 2 2 2 2 P P P A := ⟨GS.UnitaryFour.Q, GS.UnitaryFour.counterexample⟩

/-- The scalar (p,2,p) family fills the orthogonal group (including p=0). -/
theorem real_cs_exhaustion {p : ℕ} {A : Mat (2*p)} :
    InA3Orth p 2 p (permMatrix (scalarShuffle 2 p))
      (permMatrix (scalarShuffle 2 p))ᵀ A ↔ Orthogonal A := GS.UnitaryCS.scalar_two_iff (𝕜 := ℝ)

/-- Complex cosine-sine decomposition gives the entire unitary group. -/
theorem unitary_cs_exhaustion {p : ℕ} {A : CMat (2*p)} :
    CInA3Unitary p 2 p (cPermMatrix (scalarShuffle 2 p))
      (cPermMatrix (scalarShuffle 2 p))ᴴ A ↔ Unitary A := GS.UnitaryCS.scalar_two_iff

/-- A rank-one determinantal singularity survives any Euclidean factor. -/
theorem rank_one_cone_singularity (d e : ℕ) (hd : 2 ≤ d) :
    ¬ EuclideanAtSubset
      {p : (Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ | p.2.rank ≤ 1} (0, 0) := GS.Results.cone_rankOne_not_euclidean d e hd

/-- Every all-nonzero orthogonal base gives a genuine topological singularity. -/
theorem real_three_factor_singularity {q : ℕ} (hq : 3 ≤ q)
    (Q : Mat q) (hQ : Orthogonal Q) (hne : ∀ i j, Q i j ≠ 0) :
    ¬ EuclideanAtSubset (localFamily q) (basePoint Q) := GS.Results.gs_not_euclidean_at hq Q hQ hne

/-- There is a singular point for every q≥3, with no conditional base assumption. -/
theorem real_singular_point (q : ℕ) (hq : 3 ≤ q) :
    ∃ A : Mat (q*2), A ∈ localFamily q ∧ ¬ EuclideanAtSubset (localFamily q) A := GS.Results.exists_nonEuclidean_point q hq

/-- The unitary topological result is restricted to odd q. -/
theorem unitary_singular_point (q : ℕ) (hq : 3 ≤ q) (hodd : Odd q) :
    let P := cPermMatrix (scalarShuffle q 2)
    let S : Set (CMat (q*2)) := {A | CInA3Unitary 2 q 2 P Pᴴ A}
    ∃ A : CMat (q*2), A ∈ S ∧ ¬ EuclideanAtSubset S A := GS.UnitaryTopology.exists_unitary_nonEuclidean_point q hq hodd

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

/-- Exact real tangent directions with the prescribed layer supports and ties. -/
def RealDirections {n : ℕ} (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (X Z : Mat n) : Prop :=
  ∃ C Ω : Mat n,
    (BlockDiagonal b₂ C ∧ Cᵀ = -C ∧ GS.GlobalGeometry.TiedEntries b₂ τ₂ C) ∧
    (BlockDiagonal b₁ Ω ∧ Ωᵀ = -Ω ∧ GS.GlobalGeometry.TiedEntries b₁ τ₁ Ω) ∧
    Z = C * X + X * Ω

/-- Exact real tangent directions in the unitary case; phases are retained. -/
def ComplexDirections {n : ℕ} (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (X Z : CMat n) : Prop :=
  ∃ C Ω : CMat n,
    (CBlockDiagonal b₂ C ∧ Cᴴ = -C ∧ GS.UnitarySharing.TiedEntries b₂ τ₂ C) ∧
    (CBlockDiagonal b₁ Ω ∧ Ωᴴ = -Ω ∧ GS.UnitarySharing.TiedEntries b₁ τ₁ Ω) ∧
    Z = C * X + X * Ω

theorem shared_geometry {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (right left : GS.Shared.Pattern 𝕜 n)
    (P : Matrix (Fin n) (Fin n) 𝕜) :
    EmbeddedGeometry GS.Shared.frob
      {X | GS.Shared.InShared right.size left.size right.label left.label P X}
      (fun X Z => Z ∈ GS.Shared.pointDirections right left X) := by
  open GS.Shared in
  rw [← orbit_set_eq_inShared (right := right) (left := left) P]
  letI : NormedSpace ℝ (HorizontalModel right left P) := Submodule.normedSpace _
  letI := sharedOrbitChartedSpace right left P
  exact ⟨_, _, _, inferInstance, _, sharedOrbitIsManifold right left P,
    sharedOrbit_val_contMDiff right left P, sharedOrbit_val_mfderiv_injective right left P,
    fun X Z => (orbit_tangent_image_iff right left P X Z).symm,
    ⟨_, pointProjection_contMDiff right left P, fun X Z =>
      ⟨pointProjection_mem X.val Z, pointProjection_normal X.val Z⟩⟩,
    ⟨_, cayleyRetraction_contMDiff right left P, cayleyRetraction_zero_section right left P,
      cayleyRetraction_fibre_mfderiv_zero right left P⟩,
    fun f hf => ⟨_, intrinsicGradientSection_smooth right left P f hf, fun X v =>
      intrinsicGradient_characterization right left P f X ((hf.differentiable (by simp)) X) v⟩⟩

/-- Smooth geometry of the actual orthogonal image, including arbitrary overlap,
complete within-layer sharing, and arbitrary fixed carriers. -/
theorem orthogonal_shared_geometry {n : ℕ} (b₁ b₂ : ℕ)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hd₁ : b₁ ∣ n) (hd₂ : b₂ ∣ n)
    (τ₁ τ₂ : ℕ → ℕ) (P : Mat n) :
    EmbeddedGeometry (fun A B : Mat n => ∑ i, ∑ j, A i j * B i j)
      {X | GS.GlobalGeometry.InSharedA2Orth b₁ b₂ τ₁ τ₂ P X}
      (RealDirections b₁ b₂ τ₁ τ₂) := by
  convert shared_geometry (𝕜 := ℝ) ⟨b₁, hb₁, hd₁, τ₁⟩ ⟨b₂, hb₂, hd₂, τ₂⟩ P using 1
  · ext A B
    simp [GS.Shared.frob, Matrix.trace, Matrix.mul_apply]
    exact Finset.sum_comm
  · ext X
    simp [GS.Shared.InShared, GS.GlobalGeometry.InSharedA2Orth, GS.Shared.SharedFactor,
      GS.GlobalGeometry.SharedOrthogonalFactor, GS.Shared.Uni, Orthogonal, GS.product2,
      BlockDiagonal, Supported, GS.Shared.Supp, GS.Shared.Tied, GS.GlobalGeometry.TiedEntries]
  · ext X Z
    simp [GS.Shared.mem_pointDirections_iff, RealDirections, GS.Shared.sharedSkewSpace,
      BlockDiagonal, Supported, GS.Shared.Supp, GS.Shared.Tied, GS.GlobalGeometry.TiedEntries]

/-- The same real differential geometry for shared unitary layers, with the
full continuous stabilizer allowed. No special-unitary restriction is imposed. -/
theorem unitary_shared_geometry {n : ℕ} (b₁ b₂ : ℕ)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hd₁ : b₁ ∣ n) (hd₂ : b₂ ∣ n)
    (τ₁ τ₂ : ℕ → ℕ) (P : CMat n) :
    EmbeddedGeometry (fun A B : CMat n =>
      ∑ i, ∑ j, ((A i j).re * (B i j).re + (A i j).im * (B i j).im))
      {X | GS.UnitarySharing.InSharedA2Unitary b₁ b₂ τ₁ τ₂ P X}
      (ComplexDirections b₁ b₂ τ₁ τ₂) := by
  convert shared_geometry (𝕜 := ℂ) ⟨b₁, hb₁, hd₁, τ₁⟩ ⟨b₂, hb₂, hd₂, τ₂⟩ P using 1
  · ext A B
    simp [GS.Shared.frob, Matrix.trace, Matrix.mul_apply]
    exact Finset.sum_comm
  · ext X
    simp [GS.Shared.InShared, GS.UnitarySharing.InSharedA2Unitary, GS.Shared.SharedFactor,
      GS.UnitarySharing.SharedUnitaryFactor, GS.Shared.Uni, GS.Unitary, GS.UnitaryGeometry.product2,
      CSupported, GS.Shared.Supp, GS.Shared.Tied, GS.UnitarySharing.TiedEntries]
  · ext X Z
    simp [GS.Shared.mem_pointDirections_iff, ComplexDirections, GS.Shared.sharedSkewSpace,
      CBlockDiagonal, CSupported, GS.Shared.Supp, GS.Shared.Tied, GS.UnitarySharing.TiedEntries]

/-- Exact cell-rank criterion, including singular matrices and empty cells. -/
theorem two_factor_rank_criterion {n : ℕ} (b₁ b₂ : ℕ)
    (σ : Equiv.Perm (Fin n)) (A : GS.Mat n) :
    GS.InA2 b₁ b₂ (GS.permMatrix σ) A ↔
      ∀ a b : ℕ,
        (Matrix.of fun i j : Fin n =>
          if a = i.val / b₂ ∧ b = j.val / b₁ then A i j else 0).rank ≤
        Fintype.card {t : Fin n // a = (σ t).val / b₂ ∧ b = t.val / b₁} :=
  (GS.Results.OriginalCellRank.inA2_iff_coordinate b₁ b₂ σ A).trans (GS.Results.OriginalCellRank.coordinate_iff_block_rank _ _ _ _ A)

/-- With no off-diagonal overlap, the explicit shared block exponentials stay
in the actual image and have normal ambient acceleration and constant speed.
The normality test ranges over the entire tangent image given above. -/
theorem orthogonal_shared_block_geodesic {n : ℕ} (b₁ b₂ : ℕ)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hd₁ : b₁ ∣ n) (hd₂ : b₂ ∣ n)
    (τ₁ τ₂ : ℕ → ℕ) (σ : Equiv.Perm (Fin n))
    (hno : Function.Injective (fun i : Fin n => (i.val / b₁, (σ i).val / b₂)))
    (L R C Ω : Mat n)
    (hL : GS.GlobalGeometry.SharedOrthogonalFactor b₂ τ₂ L)
    (hR : GS.GlobalGeometry.SharedOrthogonalFactor b₁ τ₁ R)
    (hC : BlockDiagonal b₂ C ∧ Cᵀ = -C ∧ GS.GlobalGeometry.TiedEntries b₂ τ₂ C)
    (hΩ : BlockDiagonal b₁ Ω ∧ Ωᵀ = -Ω ∧ GS.GlobalGeometry.TiedEntries b₁ τ₁ Ω) :
    let γ : ℝ → Mat n := fun t =>
      L * NormedSpace.exp (t • C) * permMatrix σ * (NormedSpace.exp (t • Ω) * R)
    ∀ t : ℝ,
      GS.GlobalGeometry.InSharedA2Orth b₁ b₂ τ₁ τ₂ (permMatrix σ) (γ t) ∧
      HasDerivAt γ (deriv γ t) t ∧
      HasDerivAt (deriv γ) (deriv (deriv γ) t) t ∧
      (∀ Z : Mat n, RealDirections b₁ b₂ τ₁ τ₂ (γ t) Z →
        (∑ i, ∑ j, deriv (deriv γ) t i j * Z i j) = 0) ∧
      (∑ i, ∑ j, (deriv γ t i j)^2) =
        (∑ i, ∑ j, (C i j)^2) + (∑ i, ∑ j, (Ω i j)^2) := by
  intro γ t
  have hab := GS.ManifoldCompletion.noOverlap_offDiagonalDisjoint
    (block₁ := fun i : Fin n => i.val / b₁) (block₂ := fun i : Fin n => i.val / b₂) σ hno
  have hP := perm_orthogonal σ
  have hγ : γ = GS.Continuation.gsExpCurve L (permMatrix σ) R C Ω := by
    funext s
    simp only [GS.Continuation.gsExpCurve, GS.Continuation.gsExpLeft, GS.Continuation.gsExpRight,
      GS.Continuation.expLine, GS.matrixExp_eq_exp, GS.product2, Matrix.mul_assoc, γ]
  rw [hγ, funext fun s => (GS.Continuation.gsExpCurve_hasDerivAt L _ R C Ω hP s).deriv,
    funext fun s => (GS.Continuation.gsExpVelocity_hasDerivAt L _ R C Ω hP s).deriv]
  have hL' := GS.GlobalGeometry.gsExpLeft_shared b₂ τ₂ hb₂ hd₂ L C hL hC t
  have hR' := GS.GlobalGeometry.gsExpRight_shared b₁ τ₁ hb₁ hd₁ R Ω hR hΩ t
  refine ⟨⟨_, _, hL', hR', rfl⟩, GS.Continuation.gsExpCurve_hasDerivAt L _ R C Ω hP t,
    GS.Continuation.gsExpVelocity_hasDerivAt L _ R C Ω hP t, fun Z ⟨A, B, hA, hB, hZ⟩ =>
      GS.Continuation.gsExpCurve_acceleration_normal _ _ σ L R C Ω hab hL.2.1 hR.2.1 hC.1 hΩ.1
        hC.2.1 hΩ.2.1 t Z ⟨_, _, (hL'.1.transpose.mul hA.1).mul hL'.1, ?_,
          (hR'.1.mul hB.1).mul hR'.1.transpose, ?_, ?_⟩, ?_⟩
  · simp [IsSkew, Matrix.mul_assoc, hA.2.1]
  · simp [IsSkew, Matrix.mul_assoc, hB.2.1]
  · simp only [hZ, GS.tangentParam, GS.Continuation.gsExpCurve, GS.product2, Matrix.mul_assoc,
      hR'.2.1.1, Matrix.mul_one]
    simp only [← Matrix.mul_assoc, hL'.2.1.2, Matrix.one_mul]
  simpa only [GS.frobSq, GS.frobInner, sq] using GS.Continuation.gsExpCurve_constant_speed _ _ σ
    L R C Ω hab hL.2.1 hR.2.1 hC.1 hΩ.1 hC.2.1 hΩ.2.1 t

end GSPalomar
