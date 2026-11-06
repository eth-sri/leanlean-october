import Mathlib.Tactic

import GS.UnitaryLocalModel.NormalizedFibres
import GS.UnitaryLocalModel.AxisConjugation



/-!
# Positivity of normalized Pauli middle blocks

The shared spectral diagonalization reduces positivity to the two positive
real diagonal entries. The diagonalizer is used only for existence.
-/
open scoped ComplexOrder
namespace GS.UnitaryLocalModel

variable (t a b c : ℂ)

/-- Scalar normalization acts on both eigenvalues. -/
theorem smul_middleBlock  (u : AxisVector) :
    t • middleBlock a b u = middleBlock (t*a) (t*b) u := by
  ext <;> simp_all [middleBlock] <;> ring

/-- Positive anchor ratios give the positive blocks required by outer recovery. -/
theorem middleBlock_ratio_posDef  (u : AxisVector) (hu : OnSphere u)
    (ha : ∃ r : ℝ, 0 < r ∧ a/c = r)
    (hb : ∃ s : ℝ, 0 < s ∧ b/c = s) :
    (c⁻¹ • middleBlock a b u).PosDef := by
  obtain ⟨r, hr, ha⟩ := ha
  obtain ⟨s, hs, hb⟩ := hb
  rw [smul_middleBlock]
  rw [show c⁻¹*a = (r : ℂ) by grind]
  rw [show c⁻¹*b = (s : ℂ) by grind]
  obtain ⟨S,hS,he⟩ := middleBlock_unitary_diagonalization u hu
  rw [← he]
  apply Matrix.PosDef.conjTranspose_mul_mul_same
  · apply Matrix.PosDef.diagonal
    intro i
    fin_cases i
    · simpa using hr
    · simpa using hs
  · exact Matrix.mulVec_injective_of_isUnit (_root_.Unitary.isUnit_coe (U := ⟨S,hS⟩))

end GS.UnitaryLocalModel
