module

public import GS.UnitaryLocalModel.NormalizationAlgebra

@[expose] public section


/-!
# All representatives of the scalar base fibre

Every factorization of the scalar-block base point has identity anchor gauges
and both dephased central matrices equal to the reference. This is a statement
about every representative of the full fibre, not a chosen factorization.
-/

noncomputable section
open Matrix GS GS.UnitaryNonmanifold
namespace GS.UnitaryLocalModel

section
variable (U V : CMat 2) (a b c : ℂ) (hU : GS.Unitary U) (hV : GS.Unitary V) (hc : c ≠ 0)
    (he : U*diagTwo a b*V = c • (1 : CMat 2))
include hU hV hc he

theorem sandwich_scalar : U*diagTwo (a/c) (b/c)*V = 1 ∧ ‖a/c‖ = 1 ∧ ‖b/c‖ = 1 := by
  have hs : U*diagTwo (a/c) (b/c)*V = 1 := by
    rw [show diagTwo (a/c) (b/c) = c⁻¹ • diagTwo a b by
      ext i j; fin_cases i <;> fin_cases j <;> simp [diagTwo, div_eq_mul_inv, mul_comm],
      Matrix.mul_smul, Matrix.smul_mul, he, smul_smul]
    aesop
  have hd : diagTwo (a/c) (b/c) = Uᴴ * Vᴴ := by
    calc
      _ = Uᴴ*(U*diagTwo (a/c) (b/c)*V)*Vᴴ := by
        simp only [← Matrix.mul_assoc, hU.1, Matrix.one_mul]
        rw [Matrix.mul_assoc, hV.2, Matrix.mul_one]
      _ = _ := by grind
  have h := congrFun₂ (hU.conjTranspose.mul hV.conjTranspose).1
  refine ⟨hs, ?_, ?_⟩ <;> [have := h 0 0; have := h 1 1] <;>
    simp [← hd, diagTwo, Matrix.mul_apply, Fin.sum_univ_two] at this <;>
    rw [← map_div₀, Complex.conj_mul'] at this <;>
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp (by exact_mod_cast this)

theorem sandwich_phase_of_scalar :
    U*diagTwo (phase (a/c)) (phase (b/c))*V = 1 := by
  obtain ⟨hs, ha, hb⟩ := sandwich_scalar U V a b c hU hV hc he
  simpa only [phase, ha, hb, Complex.ofReal_one, div_one] using hs

theorem sandwich_entries_nonzero_of_scalar : a ≠ 0 ∧ b ≠ 0 := by
  have := sandwich_scalar U V a b c hU hV hc he
  aesop

end

variable {q : ℕ}

section
variable (U V : Fin q → CMat 2) (Q A B : CMat q)
theorem base_fibre_dephased_middle (o : Fin q) (hU : ∀ i, GS.Unitary (U i)) (hV : ∀ j, GS.Unitary (V j))
    (hQc : ∀ i, Q i o ≠ 0) (hQr : ∀ j, Q o j ≠ 0)
    (he : ∀ i j, U i * diagTwo (A i j) (B i j) * V j = Q i j • (1 : CMat 2)) :
    (AnchorNonzero Q A o ∧ AnchorNonzero Q B o) ∧ dephase Q A o = Q ∧ dephase Q B o = Q := by
  refine ⟨?_, ?_⟩
  · have hc := fun i => sandwich_entries_nonzero_of_scalar (U i) (V o)
      (A i o) (B i o) (Q i o) (hU i) (hV o) (hQc i) (he i o)
    have hr := fun j => sandwich_entries_nonzero_of_scalar (U o) (V j)
      (A o j) (B o j) (Q o j) (hU o) (hV j) (hQr j) (he o j)
    exact ⟨⟨by grind,by grind⟩, ⟨by grind,by grind⟩⟩
  have hl : ∀ i, phaseGaugeLeft U V Q A B o i = 1 := fun i =>
    sandwich_phase_of_scalar (U i) (V o) (A i o) (B i o) (Q i o) (hU i) (hV o) (hQc i) (he i o)
  have hr : ∀ j, phaseGaugeRight V Q A B o j = 1 := fun j => by
    have : phaseGaugeRight V Q A B o j = (phaseGaugeLeft U V Q A B o o)ᴴ * (U o * colPhaseDiagonal Q A B o j * V j) := by
      unfold phaseGaugeLeft phaseGaugeRight
      simp
      calc
        _ = (V o)ᴴ * (rowPhaseDiagonal Q A B o o)ᴴ * ((U o)ᴴ*U o) * colPhaseDiagonal Q A B o j * V j := by
          rw [(hU o).1,Matrix.mul_one]
        _ = _ := by grind
    rw [this, hl o]
    simpa [colPhaseDiagonal, colPhase] using sandwich_phase_of_scalar (U o) (V j) (A o j) (B o j) (Q o j) (hU o) (hV j) (hQr j) (he o j)
  have hd (i j : Fin q) : diagTwo (dephase Q A o i j) (dephase Q B o i j) =
      Q i j • (1 : CMat 2) := by
    have hn := phase_normalization_block U V Q A B o i j (hU i) (hV j)
    simp_all
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

end

end GS.UnitaryLocalModel
