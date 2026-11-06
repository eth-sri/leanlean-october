import Mathlib.Analysis.CStarAlgebra.Basic

import GS.UnitaryLocalModel.NormalizationAlgebra
import GS.MatrixFactor.Factorization



/-!
# All representatives of the scalar base fibre

Every factorization of the scalar-block base point has identity anchor gauges
and both dephased central matrices equal to the reference. This is a statement
about every representative of the full fibre, not a chosen factorization.
-/

open Matrix GS.UnitaryNonmanifold
namespace GS.UnitaryLocalModel

variable (U V : CMat 2)

theorem sandwich_phase_of_scalar (a b c : ℂ)
    (hU : GS.Unitary U) (hV : GS.Unitary V) (hc : c ≠ 0)
    (he : U*diagTwo a b*V = c • (1 : CMat 2)) :
    U*diagTwo (phase (a/c)) (phase (b/c))*V = 1 := by
  have hd : diagTwo (a/c) (b/c) = c⁻¹ • diagTwo a b := by
    ext i j
    fin_cases i,j <;> simp [diagTwo,div_eq_mul_inv,mul_comm]
  have h : U*diagTwo (a/c) (b/c)*V = 1 := by aesop
  have hu := GS.MatrixFactor.middle_unitary_of_factorization
    GS.MatrixBase.Unitary.one hU hV h.symm
  have hn (k : Fin 2) : ‖![a/c,b/c] k‖=1 := by
    apply CStarRing.norm_of_mem_unitary
    have hk : star (![a/c,b/c] k)*![a/c,b/c] k=1 := by
      simpa [diagTwo,Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal] using congrFun (congrFun hu.1 k) k
    exact ⟨hk,by grind⟩
  simpa only [phase,show ‖a/c‖=1 from hn 0,show ‖b/c‖=1 from hn 1,Complex.ofReal_one,div_one] using h

variable (U V : Fin q → CMat 2) (Q A B : CMat q) (o : Fin q)


theorem base_fibre_dephased_middle (hU : ∀ i, GS.Unitary (U i)) (hV : ∀ j, GS.Unitary (V j))
    (hQc : ∀ i, Q i o ≠ 0) (hQr : ∀ j, Q o j ≠ 0)
    (he : ∀ i j, U i * diagTwo (A i j) (B i j) * V j = Q i j • (1 : CMat 2)) :
    dephase Q A o = Q ∧ dephase Q B o = Q := by
  have hl (i : Fin q) : phaseGaugeLeft U V Q A B o i = 1 :=
    sandwich_phase_of_scalar (U i) (V o) (A i o) (B i o) (Q i o)
      (hU i) (hV o) (hQc i) (he i o)
  have hr (j : Fin q) : phaseGaugeRight V Q A B o j = 1 := by
    have h := sandwich_phase_of_scalar (U o) (V j) (A o j) (B o j) (Q o j)
      (hU o) (hV j) (hQr j) (he o j)
    calc
      _ = (phaseGaugeLeft U V Q A B o o)ᴴ *
          (U o * colPhaseDiagonal Q A B o j * V j) := by
        simp only [phaseGaugeLeft,phaseGaugeRight,Matrix.conjTranspose_mul,Matrix.mul_assoc,
          ← Matrix.mul_assoc (U o)ᴴ (U o),(hU o).1,Matrix.one_mul]
      _ = 1 := by rw [hl o]; simpa only [Matrix.conjTranspose_one,Matrix.one_mul,colPhaseDiagonal,colPhase] using h
  have hd (i j : Fin q) : diagTwo (dephase Q A o i j) (dephase Q B o i j) =
      Q i j • (1 : CMat 2) := by
    have hn := phase_normalization_block U V Q A B o i j (hU i) (hV j)
    rw [hl i,hr j,Matrix.conjTranspose_one,Matrix.one_mul,Matrix.mul_one,he i j] at hn
    calc
      _ = V o * ((V o)ᴴ * diagTwo (dephase Q A o i j) (dephase Q B o i j) * V o) *
          (V o)ᴴ := by
        simp only [← Matrix.mul_assoc,(hV o).2,Matrix.one_mul]
        rw [Matrix.mul_assoc,(hV o).2,Matrix.mul_one]
      _ = _ := by
        rw [← hn,Matrix.mul_smul,Matrix.smul_mul]
        simp only [Matrix.mul_one,(hV o).2]
  constructor <;> ext i j
  · simpa [diagTwo] using congrFun (congrFun (hd i j) 0) 0
  · simpa [diagTwo] using congrFun (congrFun (hd i j) 1) 1

end GS.UnitaryLocalModel
