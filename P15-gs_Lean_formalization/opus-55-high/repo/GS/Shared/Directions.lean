module

public import GS.Shared.Orbit

@[expose] public section


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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix
namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {right left : Pattern 𝕜 n}

section
variable (right left : Pattern 𝕜 n)
abbrev PairGenerator := Generator left × Generator right

/-- Spatial left and right generators; the plus sign absorbs the sign of
transposition in the group action. -/
def pointMap (X : 𝕄) :
    PairGenerator right left →ₗ[ℝ] 𝕄 where
  toFun v := v.1.val * X + X * v.2.val
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add,
      Matrix.add_mul, Matrix.mul_add]
    abel
  map_smul' a v := by
    simp

def pointDirections (X : 𝕄) : Submodule ℝ (𝕄) :=
  LinearMap.range (pointMap right left X)

end

theorem mem_pointDirections_iff (X Y : 𝕄) :
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
def SharedDirection (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P L R Y : 𝕄) : Prop :=
  ∃ C ∈ sharedSkewSpace b₂ τ₂, ∃ Ω ∈ sharedSkewSpace b₁ τ₁,
    Y = L * C * P * R + L * P * Ω * R

/-- Changing from body generators to spatial generators preserves all ties. -/
theorem sharedDirection_iff_pointDirections (P L R Y : 𝕄)
    (hL : SharedFactor left.size left.label L)
    (hR : SharedFactor right.size right.label R) :
    SharedDirection right.size left.size right.label left.label P L R Y ↔
      Y ∈ pointDirections right left (L * P * R) := by
  rw [mem_pointDirections_iff]
  constructor
  · rintro ⟨C, hC, Ω, hΩ, hY⟩
    refine ⟨L * C * Lᴴ, sharedSkew_conjugate left.positive left.divides hL hC,
      Rᴴ * Ω * R, sharedSkew_conjugate_conjTranspose right.positive right.divides hR hΩ, ?_⟩
    have hl : (L * C * Lᴴ) * (L * P * R) = L * C * P * R := by
      calc
        _ = L * C * (Lᴴ * L) * P * R := by grind
        _ = _ := by rw [hL.2.1.1]; simp
    have hr : (L * P * R) * (Rᴴ * Ω * R) = L * P * Ω * R := by
      calc
        _ = L * P * (R * Rᴴ) * Ω * R := by grind
        _ = _ := by rw [hR.2.1.2]; simp
    grind
  · rintro ⟨A, hA, B, hB, hY⟩
    refine ⟨Lᴴ * A * L,
      sharedSkew_conjugate_conjTranspose left.positive left.divides hL hA,
      R * B * Rᴴ, sharedSkew_conjugate right.positive right.divides hR hB, ?_⟩
    have hl : L * (Lᴴ * A * L) * P * R = A * (L * P * R) := by
      calc
        _ = (L * Lᴴ) * A * (L * P * R) := by grind
        _ = _ := by rw [hL.2.1.2]; simp
    have hr : L * P * (R * B * Rᴴ) * R = (L * P * R) * B := by
      calc
        _ = (L * P * R) * B * (Rᴴ * R) := by grind
        _ = _ := by rw [hR.2.1.1, Matrix.mul_one]
    aesop

/-- The direction spaces transform under the actual shared group action. -/
theorem action_mem_pointDirections (g : Factors right left) (X Y : 𝕄)
    (hY : Y ∈ pointDirections right left X) :
    g • Y ∈ pointDirections right left (g • X) := by
  obtain ⟨A, hA, B, hB, hY⟩ := (mem_pointDirections_iff X Y).mp hY
  let L := Factor.matrix g.1
  let R := Factor.matrix g.2
  have hL := Factor.matrix_shared g.1
  have hR := Factor.matrix_shared g.2
  apply (mem_pointDirections_iff (g • X) (g • Y)).mpr
  refine ⟨L * A * Lᴴ, sharedSkew_conjugate left.positive left.divides hL hA,
    R * B * Rᴴ, sharedSkew_conjugate right.positive right.divides hR hB, ?_⟩
  have hl : (L * A * Lᴴ) * (L * X * Rᴴ) = L * (A * X) * Rᴴ := by
    calc
      _ = L * A * (Lᴴ * L) * X * Rᴴ := by grind
      _ = _ := by rw [hL.2.1.1]; grind
  have hr : (L * X * Rᴴ) * (R * B * Rᴴ) = L * (X * B) * Rᴴ := by
    calc
      _ = L * X * (Rᴴ * R) * B * Rᴴ := by grind
      _ = _ := by rw [hR.2.1.1]; grind
  simp
  rw [hY, hl, hr, Matrix.mul_add, Matrix.add_mul]

end GS.Shared
