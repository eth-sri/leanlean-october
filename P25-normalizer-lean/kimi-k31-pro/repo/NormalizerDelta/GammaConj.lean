module

public import NormalizerLean.NewmanRat

@[expose] public section

/-!
# §G: conjugation by diag(M, 1): X_Δ(N) ≅ X₁(M, N/M) and X_Δ(M²) ≅ X(M)

D = projSL diag(M, 1) = diag(√M, 1/√M) acts by D [[a, b], [c, d]] D⁻¹ = [[a, Mb], [c/M, d]].
For M² ∣ N and Δ = {d ≡ ±1 mod N/M} this maps Γ_Δ(N) onto ±(Γ(M) ∩ Γ₁(N/M)): for γ ∈ Γ_Δ(N) with
d ≡ ε (ε = ±1) mod N/M, ε·DγD⁻¹ ∈ Γ(M) ∩ Γ₁(N/M) (M ∣ N/M, and a ≡ d⁻¹); conversely the preimage of
ζ ∈ Γ(M) ∩ Γ₁(N/M) is [[a, b/M], [Mc, d]] ∈ Γ_Δ(N), and −1 ∈ Γ_Δ(N).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-- D = diag(M, 1) in SL₂(ℝ). -/
abbrev Dm (M : ℕ) : SLℝ := projSL !![(M : ℝ), 0; 0, 1]

theorem coe_Dm {M : ℕ} (hM : 0 < M) :
    (Dm M : Matℝ) = !![Real.sqrt M, 0; 0, (Real.sqrt M)⁻¹] := by
  have hdet : 0 < (!![(M : ℝ), 0; 0, 1] : Matℝ).det := by
    rw [det_fin_two_of]; simp; exact_mod_cast hM
  have hs : Real.sqrt M ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hM)).ne'
  rw [Dm, coe_projSL _ hdet]
  simp only [det_fin_two_of, mul_one, mul_zero, sub_zero]
  mat_smp
  field_simp
  rw [Real.sq_sqrt (Nat.cast_nonneg _)]

/-- Conjugation by D: [[a, b], [c, d]] ↦ [[a, Mb], [c/M, d]]. -/
theorem coe_conj_Dm {M : ℕ} (hM : 0 < M) {Y : SLℝ} {a b c d : ℝ}
    (hY : (Y : Matℝ) = !![a, b; c, d]) :
    ((MulAut.conj (Dm M) Y : SLℝ) : Matℝ) =
      !![a, M * b; c / M, d] := by
  have hs : Real.sqrt M ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hM)).ne'
  have hss : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt (Nat.cast_nonneg _)
  rw [MulAut.conj_apply, coe_conj, coe_Dm hM, hY, adjugate_fin_two_of]
  mat_smp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> (try rw [Real.sq_sqrt (Nat.cast_nonneg _)]) <;> ring

end

end NormalizerLean
