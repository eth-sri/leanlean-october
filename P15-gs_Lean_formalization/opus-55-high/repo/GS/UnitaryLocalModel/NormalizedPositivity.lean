module

public import GS.UnitaryLocalModel.NormalizedFibres

@[expose] public section


/-!
# Positivity of normalized Pauli middle blocks

A positive middle block is the square of a Hermitian matrix with an explicit
inverse. This gives positivity for every sphere axis without choosing an
axis-dependent diagonalizing unitary.
-/
noncomputable section
open Matrix
open scoped ComplexOrder
namespace GS.UnitaryLocalModel

/-- The two Pauli eigenspaces multiply independently. -/
theorem middleBlock_mul (a b c d : ℂ) (u : AxisVector) (hu : OnSphere u) :
    middleBlock a b u * middleBlock c d u = middleBlock (a*c) (b*d) u := by
  have hh : pauli u * pauli u = (1 : CMat 2) := by
    rw [pauli_square, hu]
    simp
  unfold middleBlock
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, hh]
  ext i j
  simp
  ring

section
variable (r s : ℝ)
theorem middleBlock_real_hermitian (u : AxisVector) :
    (middleBlock (r : ℂ) (s : ℂ) u).IsHermitian := by
  change (middleBlock (r : ℂ) (s : ℂ) u)ᴴ = _
  simp [middleBlock, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    pauli_conjTranspose]

/-- Positive real Pauli eigenvalues imply actual matrix positive definiteness. -/
theorem middleBlock_posDef (hr : 0 < r) (hs : 0 < s)
    (u : AxisVector) (hu : OnSphere u) :
    (middleBlock (r : ℂ) (s : ℂ) u).PosDef := by
  have hp := Matrix.PosDef.one.conjTranspose_mul_mul_same (B := middleBlock (√r : ℂ) (√s : ℂ) u)
    (Function.LeftInverse.injective (g := (middleBlock (√r : ℂ)⁻¹ (√s : ℂ)⁻¹ u).mulVec) fun x => by
      rw [Matrix.mulVec_mulVec, middleBlock_mul _ _ _ _ u hu]; simp [middleBlock_equal, show (√r:ℂ) ≠ 0 by positivity, show (√s:ℂ) ≠ 0 by positivity])
  rwa [Matrix.mul_one, (middleBlock_real_hermitian _ _ u).eq, middleBlock_mul _ _ _ _ u hu, ← Complex.ofReal_mul,
    ← Complex.ofReal_mul, Real.mul_self_sqrt hr.le, Real.mul_self_sqrt hs.le] at hp

end

/-- Scalar normalization acts on both eigenvalues. -/
theorem smul_middleBlock (t a b : ℂ) (u : AxisVector) :
    t • middleBlock a b u = middleBlock (t*a) (t*b) u := by
  ext i j
  simp only [middleBlock, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

/-- Positive anchor ratios give the positive blocks required by outer recovery. -/
theorem middleBlock_ratio_posDef (a b c : ℂ) (u : AxisVector) (hu : OnSphere u)
    (ha : ∃ r : ℝ, 0 < r ∧ a/c = r)
    (hb : ∃ s : ℝ, 0 < s ∧ b/c = s) :
    (c⁻¹ • middleBlock a b u).PosDef := by
  obtain ⟨r, hr, ha⟩ := ha
  obtain ⟨s, hs, hb⟩ := hb
  rw [smul_middleBlock, show c⁻¹*a = r by grind, show c⁻¹*b = s by grind]
  exact middleBlock_posDef r s hr hs u hu

end GS.UnitaryLocalModel
