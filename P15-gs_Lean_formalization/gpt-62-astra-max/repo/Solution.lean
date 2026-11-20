module

public import GSChecked
public import GS.Isometric.Geodesic
public import GS.Isometric.ShuffledCS

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
  GS.Isometric.two s₁.size s₂.size σ A

/-- The same equality holds for three layers and arbitrary fixed permutations. -/
theorem three_factor (n : ℕ) (s₁ s₂ s₃ : GS.BlockSpec n)
    (σ₁ σ₂ : Equiv.Perm (Fin n)) (A : GS.Mat n) :
    GS.InA3 s₁.size s₂.size s₃.size (GS.permMatrix σ₁) (GS.permMatrix σ₂) A ∧
      GS.Orthogonal A ↔
    GS.InA3Orth s₁.size s₂.size s₃.size (GS.permMatrix σ₁) (GS.permMatrix σ₂) A :=
  GS.Isometric.three s₁.size s₂.size s₃.size σ₁ σ₂ A

open GS GS.UnitaryGeometry

/-- Four 2-by-2-block layers need not admit an orthogonal-layer realization. -/
theorem four_factor_counterexample :
    ∃ A : GS.Mat 6,
      GS.InA4 2 2 2 2 GS.M4.P GS.M4.P GS.M4.P A ∧ GS.Orthogonal A ∧
      ¬ GS.InA4Orth 2 2 2 2 GS.M4.P GS.M4.P GS.M4.P A :=
  ⟨_, by simpa only [M4.wiring_real] using! M4.counterexample ℝ⟩

open GS GS.UnitaryGeometry

/-- Unrestricted two-layer unitary matrices admit unitary layers. -/
theorem unitary_two_factor {n : ℕ} (b₁ b₂ : ℕ)
    (σ : Equiv.Perm (Fin n)) (A : CMat n) :
    CInA2 b₁ b₂ (cPermMatrix σ) A ∧ Unitary A ↔
      CInA2Unitary b₁ b₂ (cPermMatrix σ) A := GS.Isometric.two b₁ b₂ σ A

/-- Unrestricted three-layer unitary matrices admit unitary layers. -/
theorem unitary_three_factor {n : ℕ} (b₁ b₂ b₃ : ℕ)
    (σ₁ σ₂ : Equiv.Perm (Fin n)) (A : CMat n) :
    CInA3 b₁ b₂ b₃ (cPermMatrix σ₁) (cPermMatrix σ₂) A ∧ Unitary A ↔
      CInA3Unitary b₁ b₂ b₃ (cPermMatrix σ₁) (cPermMatrix σ₂) A := GS.Isometric.three b₁ b₂ b₃ σ₁ σ₂ A

/-- Allowing complex unitary layers does not remove the four-layer obstruction. -/
theorem unitary_four_factor_counterexample :
    ∃ A : CMat 6, let P : CMat 6 := fun i j => (GS.M4.P i j : ℂ)
      CInA4 2 2 2 2 P P P A ∧ Unitary A ∧ ¬CInA4Unitary 2 2 2 2 P P P A := ⟨_, M4.counterexample ℂ⟩

/-- The scalar (p,2,p) family fills the orthogonal group (including p=0). -/
theorem real_cs_exhaustion {p : ℕ} {A : Mat (2*p)} :
    InA3Orth p 2 p (permMatrix (scalarShuffle 2 p))
      (permMatrix (scalarShuffle 2 p))ᵀ A ↔ Orthogonal A := GS.Isometric.exhaustion

/-- Complex cosine-sine decomposition gives the entire unitary group. -/
theorem unitary_cs_exhaustion {p : ℕ} {A : CMat (2*p)} :
    CInA3Unitary p 2 p (cPermMatrix (scalarShuffle 2 p))
      (cPermMatrix (scalarShuffle 2 p))ᴴ A ↔ Unitary A := GS.Isometric.exhaustion

/-- A rank-one determinantal singularity survives any Euclidean factor. -/
theorem rank_one_cone_singularity (d e : ℕ) (hd : 2 ≤ d) :
    ¬ EuclideanAtSubset
      {p : (Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ | p.2.rank ≤ 1} (0, 0) := GS.Results.cone_rankOne_not_euclidean d e hd

/-- Every all-nonzero orthogonal base gives a genuine topological singularity. -/
theorem real_three_factor_singularity {q : ℕ} (hq : 3 ≤ q)
    (Q : Mat q) (hQ : Orthogonal Q) (hne : ∀ i j, Q i j ≠ 0) :
    ¬ EuclideanAtSubset (localFamily q) (basePoint Q) := (GS.Results.gs_singularity hq Q hQ hne).2

/-- There is a singular point for every q≥3, with no conditional base assumption. -/
theorem real_singular_point (q : ℕ) (hq : 3 ≤ q) :
    ∃ A : Mat (q*2), A ∈ localFamily q ∧ ¬ EuclideanAtSubset (localFamily q) A := GS.Results.exists_nonEuclidean_point q hq

/-- The unitary topological result is restricted to odd q. -/
theorem unitary_singular_point (q : ℕ) (hq : 3 ≤ q) (hodd : Odd q) :
    let P := cPermMatrix (scalarShuffle q 2)
    let S : Set (CMat (q*2)) := {A | CInA3Unitary 2 q 2 P Pᴴ A}
    ∃ A : CMat (q*2), A ∈ S ∧ ¬ EuclideanAtSubset S A := GS.UnitaryTopology.exists_unitary_nonEuclidean_point q hq hodd

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

/-- Smooth geometry of the actual orthogonal image, including arbitrary overlap,
complete within-layer sharing, and arbitrary fixed carriers. -/
theorem orthogonal_shared_geometry {n : ℕ} (b₁ b₂ : ℕ)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hd₁ : b₁ ∣ n) (hd₂ : b₂ ∣ n)
    (τ₁ τ₂ : ℕ → ℕ) (P : Mat n) :
    EmbeddedGeometry (fun A B : Mat n => ∑ i, ∑ j, A i j * B i j)
      {X | GS.GlobalGeometry.InSharedA2Orth b₁ b₂ τ₁ τ₂ P X}
      (RealDirections b₁ b₂ τ₁ τ₂) := by
  simpa only [RCLike.re_to_real, RCLike.im_to_real, zero_mul, add_zero] using! GS.Isometric.block_geometry b₁ b₂ hb₁ hb₂ hd₁ hd₂ τ₁ τ₂ P

/-- The same real differential geometry for shared unitary layers, with the
full continuous stabilizer allowed. No special-unitary restriction is imposed. -/
theorem unitary_shared_geometry {n : ℕ} (b₁ b₂ : ℕ)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hd₁ : b₁ ∣ n) (hd₂ : b₂ ∣ n)
    (τ₁ τ₂ : ℕ → ℕ) (P : CMat n) :
    EmbeddedGeometry (fun A B : CMat n =>
      ∑ i, ∑ j, ((A i j).re * (B i j).re + (A i j).im * (B i j).im))
      {X | GS.UnitarySharing.InSharedA2Unitary b₁ b₂ τ₁ τ₂ P X}
      (ComplexDirections b₁ b₂ τ₁ τ₂) :=
  GS.Isometric.block_geometry b₁ b₂ hb₁ hb₂ hd₁ hd₂ τ₁ τ₂ P

open GS.Isometric

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
  let right := blocks ℝ b₁ τ₁ hb₁ hd₁
  let left := blocks ℝ b₂ τ₂ hb₂ hd₂
  have eL : SharedFactor left L := (blockFactor_iff ..).2 hL
  have eR : SharedFactor right R := (blockFactor_iff ..).2 hR
  have eC : C ∈ skewSpace left := (blockGenerator_iff ..).2 hC
  have eΩ : Ω ∈ skewSpace right := (blockGenerator_iff ..).2 hΩ
  have h := Geodesic.certificate σ (r := right) (l := left) (a := fun i => i.val / b₂) (b := fun i => i.val / b₁) hno (fun _ h => h.1) (fun _ h => h.1) eL eR eC eΩ
  simp only [pairing_entries,RCLike.re_to_real,RCLike.im_to_real,mul_zero,add_zero] at h
  intro γ t
  obtain ⟨⟨A,B,a,b,eq⟩,hv,ha,hn,he⟩ := h t
  refine ⟨⟨A,B,(blockFactor_iff ..).1 a,(blockFactor_iff ..).1 b,eq⟩,hv,ha,?_,by simpa [sq] using! he⟩
  rintro Z ⟨D,E,d,e,hZ⟩; exact hn Z ((mem_pointDirections_iff ..).2
    ⟨D,E,(blockGenerator_iff ..).2 d,(blockGenerator_iff ..).2 e,hZ⟩)

end GSPalomar
