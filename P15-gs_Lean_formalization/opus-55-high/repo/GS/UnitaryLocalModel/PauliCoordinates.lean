module

public import GS.UnitaryNonmanifold.BlockInvariant
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section


/-!
# The two-sphere of unitary local axes

The real three-dimensional Pauli coordinates replace the real two-dimensional
reflection coordinates. Every point of the unit sphere gives a traceless
Hermitian involution. This algebra is used in the mathematical local model;
this module does not assert the existence of a local topological chart.
-/

noncomputable section
open Matrix

namespace GS.UnitaryLocalModel

abbrev AxisVector := Fin 3 → ℝ

section
variable (u : AxisVector)
def OnSphere : Prop := u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1

def pauli : CMat 2 :=
  !![(u 0 : ℂ), (u 1 : ℂ) - Complex.I * (u 2 : ℂ);
      (u 1 : ℂ) + Complex.I * (u 2 : ℂ), -(u 0 : ℂ)]

end

theorem continuous_pauli : Continuous pauli :=
  continuous_pi fun i => continuous_pi fun j => by fin_cases i <;> fin_cases j <;> simp [pauli] <;> fun_prop

section
variable (u : AxisVector)
theorem pauli_conjTranspose : (pauli u)ᴴ = pauli u := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli, Matrix.conjTranspose_apply] <;> ring

theorem pauli_square :
    pauli u * pauli u = ((u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 : ℝ) : ℂ) •
      (1 : CMat 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;> simp [Complex.I_sq]

theorem pauli_neg : pauli (-u) = -pauli u := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli] <;> ring

end

/-- A traceless Hermitian involution is exactly a point of the Pauli sphere. -/
theorem exists_sphere_pauli (H : CMat 2) (hH : Hᴴ = H) (ht : Matrix.trace H = 0) (hs : H * H = 1) :
    ∃ u : AxisVector, OnSphere u ∧ pauli u = H := by
  obtain ⟨u, rfl⟩ : ∃ u, pauli u = H := by
    have h1 := congrFun₂ hH 0 0
    have h2 := congrFun₂ hH 0 1
    refine ⟨![(H 0 0).re, (H 1 0).re, (H 1 0).im], ?_⟩
    simp [Matrix.trace, Fin.sum_univ_two] at ht
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pauli, Complex.ext_iff] at * <;> grind
  refine ⟨u, ?_, rfl⟩
  rw [pauli_square] at hs
  have := congrFun₂ hs 0 0
  simp at this
  exact_mod_cast this

section
variable (a b : ℂ) (u : AxisVector)
def middleBlock : CMat 2 :=
  ((a+b)/2) • (1 : CMat 2) + ((a-b)/2) • pauli u

theorem middleBlock_simultaneous_swap :
    middleBlock b a (-u) = middleBlock a b u := by
  rw [middleBlock, pauli_neg]
  ext i j
  simp [middleBlock]
  ring

end

theorem middleBlock_equal (a : ℂ) (u : AxisVector) :
    middleBlock a a u = a • (1 : CMat 2) := by
  simp [middleBlock]

end GS.UnitaryLocalModel
