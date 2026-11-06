import Mathlib.Tactic

import GSChecked
import GS.MatrixGeometry.GradientSection
import GS.MatrixCS.Bridge
open GS.MatrixBase


/-! # Proofs of the Palomar statement of record

Every declaration below is proved by the full library. Challenge is never
imported here. The existing project README and coverage documents describe
the paper correspondence and the additional results.
-/

set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped Manifold ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GSPalomar

/-- Every orthogonal matrix in the two-layer class admits orthogonal layers. -/
theorem two_factor (n : ℕ) (s₁ s₂ : GS.BlockSpec n)
    (σ : Equiv.Perm (Fin n)) (A : GS.Mat n) :
    GS.InA2 s₁.size s₂.size (GS.permMatrix σ) A ∧ GS.Orthogonal A ↔
      GS.InA2Orth s₁.size s₂.size (GS.permMatrix σ) A :=
  GS.MatrixFactor.twoFactorUnitarization s₁.size s₂.size σ A

/-- The same equality holds for three layers and arbitrary fixed permutations. -/
theorem three_factor (n : ℕ) (s₁ s₂ s₃ : GS.BlockSpec n)
    (σ₁ σ₂ : Equiv.Perm (Fin n)) (A : GS.Mat n) :
    GS.InA3 s₁.size s₂.size s₃.size (GS.permMatrix σ₁) (GS.permMatrix σ₂) A ∧
      GS.Orthogonal A ↔
    GS.InA3Orth s₁.size s₂.size s₃.size (GS.permMatrix σ₁) (GS.permMatrix σ₂) A :=
  GS.MatrixFactor.threeFactorUnitarization s₁.size s₂.size s₃.size σ₁ σ₂ A

/-- Four 2-by-2-block layers need not admit an orthogonal-layer realization. -/
theorem four_factor_counterexample :
    ∃ A : GS.Mat 6,
      GS.InA4 2 2 2 2 GS.M4.P GS.M4.P GS.M4.P A ∧ GS.Orthogonal A ∧
      ¬ GS.InA4Orth 2 2 2 2 GS.M4.P GS.M4.P GS.M4.P A :=
  ⟨GS.M4.Q, GS.M4.Q_mem_A4, GS.M4.Q_orthogonal, GS.M4.Q_not_mem_A4Orth⟩

open GS GS.UnitaryGeometry

/-- Unrestricted two-layer unitary matrices admit unitary layers. -/
theorem unitary_two_factor {n : ℕ} (b₁ b₂ : ℕ)
    (σ : Equiv.Perm (Fin n)) (A : CMat n) :
    CInA2 b₁ b₂ (cPermMatrix σ) A ∧ GS.Unitary A ↔
      CInA2Unitary b₁ b₂ (cPermMatrix σ) A := GS.MatrixFactor.twoFactorUnitarization b₁ b₂ σ A

/-- Unrestricted three-layer unitary matrices admit unitary layers. -/
theorem unitary_three_factor {n : ℕ} (b₁ b₂ b₃ : ℕ)
    (σ₁ σ₂ : Equiv.Perm (Fin n)) (A : CMat n) :
    CInA3 b₁ b₂ b₃ (cPermMatrix σ₁) (cPermMatrix σ₂) A ∧ GS.Unitary A ↔
      CInA3Unitary b₁ b₂ b₃ (cPermMatrix σ₁) (cPermMatrix σ₂) A := GS.MatrixFactor.threeFactorUnitarization b₁ b₂ b₃ σ₁ σ₂ A

/-- Allowing complex unitary layers does not remove the four-layer obstruction. -/
theorem unitary_four_factor_counterexample :
    ∃ A : CMat 6, let P : CMat 6 := fun i j => (GS.M4.P i j : ℂ)
      CInA4 2 2 2 2 P P P A ∧ GS.Unitary A ∧ ¬CInA4Unitary 2 2 2 2 P P P A := ⟨GS.UnitaryFour.Q, GS.UnitaryFour.Q_mem_A4, GS.UnitaryFour.Q_unitary, GS.UnitaryFour.Q_not_mem_A4Unitary⟩

/-- The scalar (p,2,p) family fills the orthogonal group (including p=0). -/
theorem real_cs_exhaustion {p : ℕ} {A : Mat (2*p)} :
    InA3Orth p 2 p (permMatrix (scalarShuffle 2 p))
      (permMatrix (scalarShuffle 2 p))ᵀ A ↔ Orthogonal A := GS.MatrixCS.scalar_exhaustion

/-- Complex cosine-sine decomposition gives the entire unitary group. -/
theorem unitary_cs_exhaustion {p : ℕ} {A : CMat (2*p)} :
    CInA3Unitary p 2 p (cPermMatrix (scalarShuffle 2 p))
      (cPermMatrix (scalarShuffle 2 p))ᴴ A ↔ GS.Unitary A := GS.MatrixCS.scalar_exhaustion

/-- A rank-one determinantal singularity survives any Euclidean factor. -/
theorem rank_one_cone_singularity (d e : ℕ) (hd : 2 ≤ d) :
    ¬ EuclideanAtSubset
      {p : (Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ | p.2.rank ≤ 1} (0, 0) := by
  intro hE
  let S : Set ((Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ) := {p | p.2.rank ≤ 1}
  have hz : ((0,0) : (Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ) ∈ S := by aesop
  have hsub := (GS.NonmanifoldFinal.euclideanAtSubset_iff S (0,0) hz).mp hE
  exact GS.NonmanifoldTopology.cone_not_euclidean
    (ι := Fin e) (κ := Fin d) (by simpa using hd)
    ((GS.NonmanifoldFinal.euclideanAt_homeomorph
      GS.NonmanifoldFinal.flattenConeProduct GS.NonmanifoldObstruction.productZero).mpr hsub)

/-- Every all-nonzero orthogonal base gives a genuine topological singularity. -/
theorem real_three_factor_singularity {q : ℕ} (hq : 3 ≤ q)
    (Q : Mat q) (hQ : Orthogonal Q) (hne : ∀ i j, Q i j ≠ 0) :
    ¬ EuclideanAtSubset (localFamily q) (basePoint Q) := by
  intro he
  obtain ⟨g⟩ := GS.NonmanifoldCompletion.original_pointed_neighbourhood_model (by omega) Q hQ hne
  have hf := (GS.NonmanifoldFinal.euclideanAtSubset_iff (localFamily q)
    (basePoint Q) (GS.NonmanifoldCompletion.familyBase Q hQ).property).mp he
  have hm := (GS.NonmanifoldFinal.euclideanAt_pointedOpenModel
    (GS.NonmanifoldObstruction.pointedOpenModel g)).mp hf
  apply GS.NonmanifoldTopology.cone_not_euclidean
    (ι := GS.NonmanifoldFinal.FreeIndex q) (κ := GS.Nonmanifold.UpperIndex q)
    (by grind [GS.Nonmanifold.three_le_card_upperIndex])
  simpa only [GS.NonmanifoldFinal.modelFreeCoordinates_zero] using
    (GS.NonmanifoldFinal.euclideanAt_homeomorph (GS.NonmanifoldFinal.modelFreeCoordinates q)
      (GS.Nonmanifold.modelCoordinatesZero q)).mp hm

/-- There is a singular point for every q≥3, with no conditional base assumption. -/
theorem real_singular_point (q : ℕ) (hq : 3 ≤ q) :
    ∃ A : Mat (q*2), A ∈ localFamily q ∧ ¬ EuclideanAtSubset (localFamily q) A := by
  have hQ := GS.Results.reflectionBase_orthogonal q (by omega)
  exact ⟨basePoint (GS.Results.reflectionBase q),
    GS.NonmanifoldCompletion.basePoint_mem_localFamily _ hQ,
    real_three_factor_singularity hq _ hQ (GS.Results.reflectionBase_entries_ne_zero q hq)⟩

open GS.UnitaryTopology GS.UnitaryLocalModel GS.UnitaryManifold
  GS.NonmanifoldFinal GS.NonmanifoldClosure in
/-- The unitary topological result is restricted to odd q. -/
theorem unitary_singular_point (q : ℕ) (hq : 3 ≤ q) (hodd : Odd q) :
    let P := cPermMatrix (scalarShuffle q 2)
    let S : Set (CMat (q*2)) := {A | CInA3Unitary 2 q 2 P Pᴴ A}
    ∃ A : CMat (q*2), A ∈ S ∧ ¬ EuclideanAtSubset S A := by
  let Q := fullUnitary (ofRealMatrix (GS.Results.reflectionBase q))
    (ofRealMatrix_unitary (GS.Results.reflectionBase_orthogonal q (by omega)))
  let o : Fin q := ⟨0,by omega⟩
  have hQ : AnchorNonzero Q.val Q.val o := by
    have h (i j : Fin q) : Q.val i j ≠ 0 := by
      change (GS.Results.reflectionBase q i j : ℂ) ≠ 0
      exact_mod_cast GS.Results.reflectionBase_entries_ne_zero q hq i j
    exact ⟨fun i => ⟨h i o,h i o⟩,fun j => ⟨h o j,h o j⟩⟩
  refine ⟨scalarBlockBase Q.val,(unitaryFamilyBase Q o).property,?_⟩
  obtain ⟨g⟩ := unitary_matrix_pointed_neighbourhood_model Q o hQ
  intro he
  have hsub := (euclideanAtSubset_iff (GS.UnitaryNonmanifold.localFamily q)
    (scalarBlockBase Q.val) (unitaryFamilyBase Q o).property).mp he
  let a := identityOuter q o
  obtain ⟨n,⟨c⟩⟩ := pointedModel_of_finiteDimensional_chart
    ((blockUTuplePartialChart a.1).prod (blockUTuplePartialChart a.2)) a
    ⟨fun _ _ => base_mem_chartSource _,fun _ _ => base_mem_chartSource _⟩
  have hmodel := (euclideanAt_pointedOpenModel (GS.NonmanifoldObstruction.pointedOpenModel g)).mp hsub
  have hprod := (euclideanAt_pointedOpenModel
    (pointedOpenModel_prodRight c (coneCoordinatesZero ((q-1)^2)))).mp hmodel
  have hflat := euclideanAt_of_homeomorph (euclideanConeCoordinates n ((q-1)^2))
    (0,coneCoordinatesZero ((q-1)^2)) hprod
  apply rankThreeProduct_not_euclidean_of_four_dvd (n+(q-1)^2) ((q-1)^2) ?_ ?_
    (by aesop)
  · have : 0<q-1 := by omega
    positivity
  · obtain ⟨k,hk⟩ := hodd
    refine ⟨k^2,?_⟩
    have he : q-1=2*k := by omega
    rw [he]
    ring

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

open GS.MatrixGeometry in
theorem realDirections_eq_generic {n : ℕ} (right left : Pattern ℝ n) :
    RealDirections right.size left.size right.label left.label = Directions right left := rfl

open GS.MatrixGeometry GS.MatrixBase in
/-- The real differential geometry is shared by both RCLike scalar fields. -/
theorem matrix_shared_geometry {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (right left : Pattern 𝕜 n) (P : KMat 𝕜 n) :
    EmbeddedGeometry (GS.MatrixBase.cFrobInner (𝕜 := 𝕜))
      {X | InSharedA2Unitary right.size left.size right.label left.label P X}
      (Directions right left) := by
  rw [← orbit_set_eq_inShared   P]
  let E := HorizontalModel right left P
  letI : NormedSpace ℝ E := Submodule.normedSpace _
  letI := sharedOrbitChartedSpace right left P
  letI := sharedOrbitIsManifold right left P
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    sharedOrbit_val_contMDiff right left P,
    sharedOrbit_val_mfderiv_injective right left P, ?_, ?_, ?_, ?_⟩
  · intro X Z
    exact (directions_iff X.val Z).trans (orbit_tangent_image_iff right left P X Z).symm
  · refine ⟨fun p => pointProjection right left p.1.val p.2, ?_, ?_⟩
    · apply transported_contMDiff right left P (fun X Z => pointProjection right left X Z)
        (fun p => p.1 * pointProjection right left P (p.1ᴴ * p.2.2 * p.2.1) * p.2.1ᴴ)
      · fun_prop
      · intro g Z
        have h := pointProjection_equivariant g P (g⁻¹ • Z)
        rw [smul_inv_smul] at h
        have hi : g⁻¹ • Z = (Factor.matrix g.1)ᴴ * Z * Factor.matrix g.2 := by simp_all
        simpa only [hi,action_apply] using h.symm
    · intro X Z
      exact ⟨(directions_iff _ _).mpr (pointProjection_mem X.val Z),
        fun Y hY => pointProjection_normal X.val Z Y ((directions_iff _ _).mp hY)⟩
  · refine ⟨cayleyRetraction right left P, ?_,
      cayleyFibreRetraction_zero right left P, cayleyFibreRetraction_mfderiv_zero right left P⟩    
    apply (sharedOrbit_contMDiff_iff_ambient right left P
      (𝓘(ℝ, HorizontalModel right left P)).tangent (cayleyRetraction right left P)).mpr
    have hp := Bundle.contMDiff_proj (F := HorizontalModel right left P) (IB := 𝓘(ℝ,HorizontalModel right left P)) (n := ⊤) (TangentSpace (𝓘(ℝ, HorizontalModel right left P)) (M := MatrixOrbit right left P))
    have hv := (contMDiff_snd_tangentBundle_modelSpace (KMat 𝕜 n) (𝓘(ℝ, KMat 𝕜 n))).comp
      ((sharedOrbit_val_contMDiff right left P).contMDiff_tangentMap (m := ⊤) (by simp))
    have hl := (minimumNormLift_contMDiff right left P).comp (hp.prodMk hv)
    exact (generatorCayleyValue_smooth right left).comp_contMDiff
      (((sharedOrbit_val_contMDiff right left P).comp hp).prodMk_space
        (hl.prodMk_space (contMDiff_const (c := (1 : ℝ)))))
  · intro f hf
    refine ⟨intrinsicGradient right left P f, ?_, ?_⟩
    · have hg : ContDiff ℝ ∞ (ambientGradient f) := by
        
        have hdec : ContDiff ℝ ∞ (fun x : CFrobCoordinates 𝕜 n => (decodeCFrob x : KMat 𝕜 n)) := (decodeCFrob : CFrobCoordinates 𝕜 n →ₗ[ℝ] KMat 𝕜 n).toContinuousLinearMap.contDiff (n := ∞)
        have hdual : ContDiff ℝ ∞ (fun D => (InnerProductSpace.toDual ℝ (CFrobCoordinates 𝕜 n)).symm D) :=
          (InnerProductSpace.toDual ℝ (CFrobCoordinates 𝕜 n)).symm.toContinuousLinearEquiv.contDiff
        fun_prop [ambientGradient,dualMatrix]
      have hpair :=
        contMDiff_id.prodMk
          (hg.comp_contMDiff ((sharedOrbit_val_contMDiff right left P).of_le le_top))
      exact ((tangentProjectionBundle_contMDiff right left P).of_le le_top).comp hpair
    · intro X v
      have hchain := congrArg (fun L => L v) (mfderiv_comp X
        (((hf.differentiable (by simp)) X).mdifferentiableAt)
        (((sharedOrbit_val_contMDiff right left P) X).mdifferentiableAt (by simp)))
      simp only [Function.comp_def,mfderiv_eq_fderiv,ContinuousLinearMap.comp_apply] at hchain
      rw [hchain]
      change GS.MatrixBase.cFrobInner
        (inclusionDifferential right left P X (intrinsicGradient right left P f X))
        (inclusionDifferential right left P X v) =
        fderiv ℝ f X.val (inclusionDifferential right left P X v)
      rw [GS.MatrixBase.functional_eq_cFrobInner]
      rw [intrinsicGradient,inclusion_tangentProjection,
        pointProjection,cFrobProjection_self_adjoint]
      congr 1
      exact (pointProjection_fixed_iff_tangent_image right left P X _).mpr ⟨v,rfl⟩
/-- Smooth geometry of the actual orthogonal image, including arbitrary overlap,
complete within-layer sharing, and arbitrary fixed carriers. -/
theorem orthogonal_shared_geometry {n : ℕ} (b₁ b₂ : ℕ)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hd₁ : b₁ ∣ n) (hd₂ : b₂ ∣ n)
    (τ₁ τ₂ : ℕ → ℕ) (P : Mat n) :
    EmbeddedGeometry (fun A B : Mat n => ∑ i, ∑ j, A i j * B i j)
      {X | GS.GlobalGeometry.InSharedA2Orth b₁ b₂ τ₁ τ₂ P X}
      (RealDirections b₁ b₂ τ₁ τ₂)   := by
  let right : GS.MatrixGeometry.Pattern ℝ n := ⟨b₁, hb₁, hd₁, τ₁⟩
  let left : GS.MatrixGeometry.Pattern ℝ n := ⟨b₂, hb₂, hd₂, τ₂⟩
  convert matrix_shared_geometry right left P using 1
  · rfl
  · rfl
  · exact realDirections_eq_generic right left

/-- The same real differential geometry for shared unitary layers, with the
full continuous stabilizer allowed. No special-unitary restriction is imposed. -/
theorem unitary_shared_geometry {n : ℕ} (b₁ b₂ : ℕ)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hd₁ : b₁ ∣ n) (hd₂ : b₂ ∣ n)
    (τ₁ τ₂ : ℕ → ℕ) (P : CMat n) :
    EmbeddedGeometry (fun A B : CMat n =>
      ∑ i, ∑ j, ((A i j).re * (B i j).re + (A i j).im * (B i j).im))
      {X | GS.UnitarySharing.InSharedA2Unitary b₁ b₂ τ₁ τ₂ P X}
      (ComplexDirections b₁ b₂ τ₁ τ₂)   :=
by
  convert matrix_shared_geometry
    (⟨b₁,hb₁,hd₁,τ₁⟩ : GS.MatrixGeometry.Pattern ℂ n)
    (⟨b₂,hb₂,hd₂,τ₂⟩ : GS.MatrixGeometry.Pattern ℂ n) P using 1
  · ext <;> simp_all [GS.MatrixBase.cFrobInner,RCLike.mul_re,RCLike.star_def]
  · rfl
  · rfl

/-- Exact cell-rank criterion, including singular matrices and empty cells. -/
theorem two_factor_rank_criterion {n : ℕ} (b₁ b₂ : ℕ)
    (σ : Equiv.Perm (Fin n)) (A : GS.Mat n) :
    GS.InA2 b₁ b₂ (GS.permMatrix σ) A ↔
      ∀ a b : ℕ,
        (Matrix.of fun i j : Fin n =>
          if a = i.val / b₂ ∧ b = j.val / b₁ then A i j else 0).rank ≤
        Fintype.card {t : Fin n // a = (σ t).val / b₂ ∧ b = t.val / b₁} :=
by
  refine Iff.trans ?_ (GS.Results.OriginalCellRank.coordinate_iff_block_rank _ _ _ _ A)
  constructor
  · rintro ⟨B₁, B₂, hb₁, hb₂, hA⟩
    refine ⟨B₂ * permMatrix σ, B₁, ?_, ?_, hA⟩
    · aesop
    · aesop
  · rintro ⟨L, R, hL, hR, hA⟩
    refine ⟨R, L * (permMatrix σ)ᵀ, ?_, ?_, ?_⟩
    · tauto
    · intro i j h
      rw [perm_transpose, mul_perm_apply]
      apply hL i (σ.symm j)
      simpa only [Equiv.apply_symm_apply] using h
    · simpa only [GS.product2, Matrix.mul_assoc, (perm_orthogonal σ).1,
        Matrix.one_mul] using hA

open GS.Continuation GS.GlobalGeometry

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
        (∑ i, ∑ j, (C i j)^2) + (∑ i, ∑ j, (Ω i j)^2) :=
by
  let right : GS.MatrixGeometry.Pattern ℝ n := ⟨b₁, hb₁, hd₁, τ₁⟩
  let left : GS.MatrixGeometry.Pattern ℝ n := ⟨b₂, hb₂, hd₂, τ₂⟩
  let γ : ℝ → Mat n := fun t =>
    L * NormedSpace.exp (t • C) * permMatrix σ * (NormedSpace.exp (t • Ω) * R)
  let v := gsExpVelocity L (permMatrix σ) R C Ω
  let a := gsExpAcceleration L (permMatrix σ) R C Ω
  have hv (t : ℝ) :=
    gsExpCurve_hasDerivAt L (permMatrix σ) R C Ω (perm_orthogonal σ) t
  have heV : deriv γ = v := funext fun t => (hv t).deriv
  have ha (t : ℝ) :=
    gsExpVelocity_hasDerivAt L (permMatrix σ) R C Ω (perm_orthogonal σ) t
  have heA : deriv (deriv γ) = a := by rw [heV]; exact funext fun t => (ha t).deriv
  have hab := GS.ManifoldCompletion.noOverlap_offDiagonalDisjoint (block₁ := right.block) (block₂ := left.block) σ hno
  change ∀ t, GS.GlobalGeometry.InSharedA2Orth b₁ b₂ τ₁ τ₂ (permMatrix σ) (γ t) ∧ _
  intro t
  have hLt := GS.MatrixGeometry.shared_factor_mul hb₂ hd₂ hL (expLine_shared hb₂ hd₂ hC t)
  have hRt := GS.MatrixGeometry.shared_factor_mul hb₁ hd₁ (expLine_shared hb₁ hd₁ hΩ t) hR
  refine ⟨⟨gsExpLeft L C t, gsExpRight R Ω t, hLt, hRt, rfl⟩,
    ?_, ?_, ?_, ?_⟩
  · aesop
  · aesop
  · intro Z hZ
    have hz : GS.MatrixGeometry.Directions right left (γ t) Z := by aesop
    obtain ⟨A, hA, B, hB, hZ⟩ :=
      (GS.MatrixGeometry.sharedDirection_iff_pointDirections (right := right) (left := left)
        (permMatrix σ) (gsExpLeft L C t) (gsExpRight R Ω t) Z hLt hRt).mpr
        ((GS.MatrixGeometry.directions_iff _ _).mp hz)
    rw [heA]
    rw [hZ]
    change cFrobInner (gsExpAcceleration L (permMatrix σ) R C Ω t)
      (GS.tangentParam (gsExpLeft L C t) (permMatrix σ) (gsExpRight R Ω t) A B) = 0
    rw [GS.tangentParam_factored _ _ _ _ _ (perm_orthogonal σ)]
    simp only [gsExpAcceleration, GS.Extensions.lift]
    rw [cFrobInner_right_unitary (ι := Fin n) (permMatrix σ * gsExpRight R Ω t)
      ((perm_orthogonal σ).mul hRt.2.1), cFrobInner_left_unitary (κ := Fin n) (gsExpLeft L C t) hLt.2.1]
    change Supported left.block C ∧ IsSkew C ∧ _ at hC
    change Supported left.block A ∧ IsSkew A ∧ _ at hA
    have hK := (supported_perm_conjugate_iff right.block σ Ω).mpr hΩ.1
    have hE := (supported_perm_conjugate_iff right.block σ B).mpr hB.1
    have hKs := conjugate_skew (permMatrix σ) Ω hΩ.2.1
    have hEs := conjugate_skew (permMatrix σ) B hB.2.1
    have hm : cFrobInner (C * (permMatrix σ * Ω * (permMatrix σ)ᵀ))
        (A + permMatrix σ * B * (permMatrix σ)ᵀ) = 0 := by
      grind [Matrix.conjTranspose_eq_transpose_of_trivial, GS.Supported.mul, GS.Supported.transpose, GS.Extensions.OffDiagonalDisjoint.symm,
        GS.Extensions.frobInner_disjoint_supported_skew, GS.Extensions.frobInner_mul_right, GS.MatrixBase.cFrobInner_add_right,
        GS.MatrixBase.cFrobInner_comm, GS.MatrixBase.cFrobInner_mul_left]
    let K := permMatrix σ * Ω * (permMatrix σ)ᵀ
    let E := permMatrix σ * B * (permMatrix σ)ᵀ
    have hs := cFrobInner_conjTranspose (C*C+K*K) (A+E)
    change Kᵀ = -K at hKs
    change Eᵀ = -E at hEs
    simp only [GS.IsSkew] at hC hA
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_add,
      Matrix.transpose_mul,hC.2.1,hA.2.1,hKs,hEs,Matrix.neg_mul,Matrix.mul_neg,neg_neg] at hs
    
    grind [GS.Extensions.accelerationCore,cFrobInner_add_left,cFrobInner_add_right,
      cFrobInner_comm,cFrobInner_neg_left,cFrobInner_real_smul_left]

  · rw [heV]
    simp only [sq]
    change cFrobSq (gsExpVelocity L (permMatrix σ) R C Ω t) = cFrobSq C + cFrobSq Ω
    have hcross := GS.Extensions.frobInner_disjoint_supported_skew hab _ _ hC.1
      ((supported_perm_conjugate_iff right.block σ Ω).mpr hΩ.1)
      (conjugate_skew _ _ hΩ.2.1)
    unfold gsExpVelocity GS.Extensions.lift cFrobSq
    rw [cFrobInner_right_unitary (ι := Fin n) (permMatrix σ * gsExpRight R Ω t)
      ((perm_orthogonal σ).mul hRt.2.1),
      cFrobInner_left_unitary (κ := Fin n) (gsExpLeft L C t) hLt.2.1]
    have hnorm : cFrobSq (permMatrix σ * Ω * (permMatrix σ)ᵀ) = cFrobSq Ω := by
      unfold cFrobSq
      rw [cFrobInner_right_unitary (ι := Fin n) (permMatrix σ)ᵀ (perm_orthogonal σ).transpose,
        cFrobInner_left_unitary (κ := Fin n) (permMatrix σ) (perm_orthogonal σ)]
    grind [cFrobInner_add_left,cFrobInner_add_right,cFrobInner_comm]

end GSPalomar
