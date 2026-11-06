
import GS.UnitaryNonmanifold.ScalarBridge
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith



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

variable (u : AxisVector)

def OnSphere  : Prop := u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1

def pauli  : CMat 2 :=
  !![(u 0 : ℂ), (u 1 : ℂ) - Complex.I * (u 2 : ℂ);
      (u 1 : ℂ) + Complex.I * (u 2 : ℂ), -(u 0 : ℂ)]

theorem continuous_pauli : Continuous pauli := by fun_prop [pauli]

theorem pauli_conjTranspose  : (pauli u)ᴴ = pauli u := by
  ext i j
  fin_cases i,j <;> simp [pauli, Matrix.conjTranspose_apply] <;> ring



theorem pauli_neg  : pauli (-u) = -pauli u := by
  ext i j
  fin_cases i,j <;> simp [pauli] <;> ring

variable (a b : ℂ)

variable (u : AxisVector)

variable (H : CMat 2)

/-- Every traceless Hermitian two-by-two matrix has unique real Pauli coordinates. -/
theorem exists_pauli_of_hermitian_traceless 
    (hH : Hᴴ = H) (ht : Matrix.trace H = 0) :
    ∃ u : AxisVector, pauli u = H := by
  have hh := Matrix.ext_iff.mpr hH
  simp [Matrix.conjTranspose_apply, Fin.forall_fin_two, Complex.ext_iff,
    Matrix.trace, Fin.sum_univ_two] at hh ht
  refine ⟨![(H 0 0).re, (H 1 0).re, (H 1 0).im], ?_⟩
  ext i j
  fin_cases i,j <;> apply Complex.ext <;>
    simp [pauli] <;> linarith

/-- A traceless Hermitian involution is exactly a point of the Pauli sphere. -/
theorem exists_sphere_pauli 
    (hH : Hᴴ = H) (ht : Matrix.trace H = 0) (hs : H * H = 1) :
    ∃ u : AxisVector, OnSphere u ∧ pauli u = H := by
  obtain ⟨u, rfl⟩ := exists_pauli_of_hermitian_traceless H hH ht
  refine ⟨u, ?_, rfl⟩
  have he := congrArg Complex.re (congrFun (congrFun hs 0) 0)
  change u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1
  simpa [pauli,Matrix.mul_apply,Fin.sum_univ_two,pow_two,add_assoc] using he

def middleBlock   : CMat 2 :=
  ((a+b)/2) • (1 : CMat 2) + ((a-b)/2) • pauli u

theorem middleBlock_simultaneous_swap   :
    middleBlock b a (-u) = middleBlock a b u := by ext <;> simp_all [middleBlock,pauli_neg] <;> ring

theorem middleBlock_equal   :
    middleBlock a a u = a • (1 : CMat 2) := by
  simp [middleBlock]

end GS.UnitaryLocalModel
