import GS.MatrixGeometry.Base

import GS.MatrixGeometry.Orbit



/-!
# Factor-independent infinitesimal directions for shared layers

The point map (A,B) |-> A X + X B is defined directly from X.  Conjugation
closure of the tied generator spaces identifies its range with the old
factor-coordinate formula for every valid factorization.  Thus the range
and the set of realized tied-factor velocities do not depend on that choice.

`pointDirections` is deliberately not called a tangent bundle.  The full
shared-orbit atlas and identification with its manifold differential are
constructed in the later atlas and tangent-bridge modules.
-/

noncomputable section
open Matrix GS.MatrixBase
namespace GS.MatrixGeometry
variable {𝕜 : Type} [RCLike 𝕜]
variable  {right left : Pattern 𝕜 n}

abbrev PairGenerator (right left : Pattern 𝕜 n) := Generator left × Generator right

/-- Spatial left and right generators; the plus sign absorbs the sign of
transposition in the group action. -/
def pointMap (right left : Pattern 𝕜 n) (X : KMat 𝕜 n) :
    PairGenerator right left →ₗ[ℝ] KMat 𝕜 n where
  toFun v := v.1.val * X + X * v.2.val
  map_add' v w := by grind [Submodule.coe_add,Prod.fst_add,Prod.snd_add,Matrix.add_mul,Matrix.mul_add]
  map_smul' a v := by simp_all

def pointDirections (right left : Pattern 𝕜 n) (X : KMat 𝕜 n) : Submodule ℝ (KMat 𝕜 n) :=
  LinearMap.range (pointMap right left X)

theorem mem_pointDirections_iff (X Y : KMat 𝕜 n) :
    Y ∈ pointDirections right left X ↔
      ∃ A ∈ sharedSkewSpace left.size left.label,
        ∃ B ∈ sharedSkewSpace right.size right.label, Y = A * X + X * B := by
  constructor
  · rintro ⟨⟨A, B⟩, h⟩
    exact ⟨A.val, A.property, B.val, B.property, h.symm⟩
  · rintro ⟨A, hA, B, hB, h⟩
    exact ⟨(⟨A, hA⟩, ⟨B, hB⟩), h.symm⟩

/-- Complete synthesis: equalities between repeated entries do not remove
nonoverlap residuals from a coupled least-squares problem. -/
def SharedDirection (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P L R Y : KMat 𝕜 n) : Prop :=
  ∃ C ∈ sharedSkewSpace b₂ τ₂, ∃ Ω ∈ sharedSkewSpace b₁ τ₁,
    Y = L * C * P * R + L * P * Ω * R

/-- The spatial-generator form of the tangent directions. -/
def Directions (right left : Pattern 𝕜 n) (X Z : KMat 𝕜 n) : Prop :=
  ∃ C Ω : KMat 𝕜 n,
    C ∈ sharedSkewSpace left.size left.label ∧
    Ω ∈ sharedSkewSpace right.size right.label ∧ Z = C * X + X * Ω

theorem directions_iff (X Z : KMat 𝕜 n) :
    Directions right left X Z ↔ Z ∈ pointDirections right left X := by
  simp only [Directions, mem_pointDirections_iff]
  aesop

/-- Changing from body generators to spatial generators preserves all ties. -/
theorem sharedDirection_iff_pointDirections (P L R Y : KMat 𝕜 n)
    (hL : SharedUnitaryFactor left.size left.label L)
    (hR : SharedUnitaryFactor right.size right.label R) :
    SharedDirection right.size left.size right.label left.label P L R Y ↔
      Y ∈ pointDirections right left (GS.MatrixBase.product2 L P R) := by
  rw [mem_pointDirections_iff]
  constructor
  · rintro ⟨C, hC, Ω, hΩ, hY⟩
    refine ⟨L * C * Lᴴ, sharedSkew_conjugate left.positive left.divides hL hC,
      Rᴴ * Ω * R, sharedSkew_conjugate_conjTranspose right.positive right.divides hR hΩ, ?_⟩
    simpa only [GS.MatrixBase.product2, Matrix.mul_assoc, ← Matrix.mul_assoc Lᴴ L,
      ← Matrix.mul_assoc R Rᴴ, hL.2.1.1, hR.2.1.2, Matrix.one_mul, Matrix.mul_one] using hY
  · rintro ⟨A, hA, B, hB, hY⟩
    refine ⟨Lᴴ * A * L,
      sharedSkew_conjugate_conjTranspose left.positive left.divides hL hA,
      R * B * Rᴴ, sharedSkew_conjugate right.positive right.divides hR hB, ?_⟩
    simpa only [GS.MatrixBase.product2, Matrix.mul_assoc, ← Matrix.mul_assoc L Lᴴ,
      ← Matrix.mul_assoc Rᴴ R, hL.2.1.2, hR.2.1.1, Matrix.one_mul, Matrix.mul_one] using hY

section
variable (g : Factors right left)

/-- Conjugation acts separately on the two full shared generator matrices. -/
def generatorAction  :
    PairGenerator right left →ₗ[ℝ] PairGenerator right left where
  toFun v :=
    (⟨Factor.matrix g.1 * v.1.val * (Factor.matrix g.1)ᴴ,
      sharedSkew_conjugate left.positive left.divides (Factor.matrix_shared g.1) v.1.property⟩,
     ⟨Factor.matrix g.2 * v.2.val * (Factor.matrix g.2)ᴴ,
      sharedSkew_conjugate right.positive right.divides (Factor.matrix_shared g.2) v.2.property⟩)
  map_add' v w := by simp_all [Submodule.coe_add,Prod.fst_add,Prod.snd_add,Matrix.add_mul,Matrix.mul_add]
  map_smul' a v := by aesop

@[simp] theorem generatorAction_left  (v : PairGenerator right left) :
    (generatorAction g v).1.val = Factor.matrix g.1 * v.1.val * (Factor.matrix g.1)ᴴ := rfl

@[simp] theorem generatorAction_right  (v : PairGenerator right left) :
    (generatorAction g v).2.val = Factor.matrix g.2 * v.2.val * (Factor.matrix g.2)ᴴ := rfl

/-- Intertwining of the actual point-based synthesis maps. -/
theorem pointMap_generatorAction  (X : KMat 𝕜 n)
    (v : PairGenerator right left) :
    pointMap right left (g • X) (generatorAction g v) =
      g • pointMap right left X v := by
  let L := Factor.matrix g.1
  let R := Factor.matrix g.2
  change (L * v.1.val * Lᴴ) * (L * X * Rᴴ) +
    (L * X * Rᴴ) * (R * v.2.val * Rᴴ) = L * (v.1.val * X + X * v.2.val) * Rᴴ
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Lᴴ L, (Factor.matrix_unitary g.1).1,
    ← Matrix.mul_assoc Rᴴ R, (Factor.matrix_unitary g.2).1]
  simp only [Matrix.one_mul]

end

/-- Synthesis intertwining transports the exact image of the tangent map. -/
theorem action_mem_pointDirections (g : Factors right left) (X Y : KMat 𝕜 n)
    (hY : Y ∈ pointDirections right left X) :
    g • Y ∈ pointDirections right left (g • X) := by
  obtain ⟨v,rfl⟩ := hY
  exact ⟨generatorAction g v,pointMap_generatorAction g X v⟩

end GS.MatrixGeometry
