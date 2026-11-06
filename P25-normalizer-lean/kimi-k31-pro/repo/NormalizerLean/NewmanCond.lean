module

public import NormalizerLean.NewmanRat

@[expose] public section

/-!
# Newman's theorem, step 2: the integrality conditions ([Nw §3])

With g = κ·S, S = [[α, β/h], [hγ, δ]] and e = αδ − βγ (so κ²e = 1), conjugation by g is
Φ(M) = S M adj(S) / e.  `InL N M` says that M is an integer matrix with N ∣ M₁₀ and ε ∣ M₁₁ − M₀₀
(ε = gcd(N, 24)); it holds on Γ₀(N) (units mod divisors of 24 square to 1) and is closed under
integer combinations.  Applying Φ to E₁₂ = T − 1, NE₂₁ = U − 1, NE₂₂ = N − (TU − T − U + 1) and
(t − x)E₂₂ = γ − x − yE₁₂ − NE₂₁ (γ = [[x, y], [N, t]] ∈ Γ₀(N)) gives integer divisibilities.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-- ε = gcd(N, 24). -/
def epsPart (N : ℕ) : ℕ := Nat.gcd N 24

/-! ### Conjugation as a linear map -/

/-- S = [[α, β/h], [hγ, δ]]. -/
def Smat (h : ℕ) (α β γ δ : ℤ) : Matℝ :=
  !![(α : ℝ), (β : ℝ) / h; (h : ℝ) * γ, (δ : ℝ)]

/-- Φ(M) = S M adj(S) / e. -/
def Phi (h : ℕ) (α β γ δ : ℤ) (M : Matℝ) : Matℝ :=
  ((detS α β γ δ : ℤ) : ℝ)⁻¹ • (Smat h α β γ δ * M * (Smat h α β γ δ).adjugate)

theorem Phi_add (h : ℕ) (α β γ δ : ℤ) (M M' : Matℝ) :
    Phi h α β γ δ (M + M') = Phi h α β γ δ M + Phi h α β γ δ M' := by
  simp [Phi, Matrix.mul_add, Matrix.add_mul, smul_add]

theorem Phi_smul (h : ℕ) (α β γ δ : ℤ) (r : ℝ) (M : Matℝ) :
    Phi h α β γ δ (r • M) = r • Phi h α β γ δ M := by
  simp [Phi, smul_smul, mul_comm]

theorem Phi_sub (h : ℕ) (α β γ δ : ℤ) (M M' : Matℝ) :
    Phi h α β γ δ (M - M') = Phi h α β γ δ M - Phi h α β γ δ M' := by
  have := Phi_add h α β γ δ M ((-1 : ℝ) • M')
  rw [Phi_smul] at this
  simpa [sub_eq_add_neg] using this

theorem det_Smat {h : ℕ} (hh : h ≠ 0) (α β γ δ : ℤ) :
    (Smat h α β γ δ).det = ((detS α β γ δ : ℤ) : ℝ) := by
  have hhr : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hh
  rw [Smat, det_fin_two_of]
  push_cast
  field_simp

theorem Phi_one {h : ℕ} (hh : h ≠ 0) {α β γ δ : ℤ} (he : detS α β γ δ ≠ 0) :
    Phi h α β γ δ 1 = 1 := by
  have her : ((detS α β γ δ : ℤ) : ℝ) ≠ 0 := by exact_mod_cast he
  rw [Phi, Matrix.mul_one, Matrix.mul_adjugate, det_Smat hh, smul_smul, inv_mul_cancel₀ her,
    one_smul]

/-- Conjugation by g = κ S is Φ. -/
theorem coe_conj_eq_Phi {g : SLℝ} {κ : ℝ} {h : ℕ} {α β γ δ : ℤ}
    (hg : (g : Matℝ) = κ • Smat h α β γ δ) (hh : h ≠ 0) (Y : SLℝ) :
    ((g * Y * g⁻¹ : SLℝ) : Matℝ) =
      Phi h α β γ δ (Y : Matℝ) := by
  have hdet : κ ^ 2 * ((detS α β γ δ : ℤ) : ℝ) = 1 := by
    have := g.2
    rw [hg, det_smul, Fintype.card_fin, Smat, det_fin_two_of] at this
    have hhr : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hh
    push_cast
    field_simp at this
    linear_combination this
  have hE : ((detS α β γ δ : ℤ) : ℝ) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hdet; exact zero_ne_one hdet
  have hinv : κ ^ 2 = ((detS α β γ δ : ℤ) : ℝ)⁻¹ := by
    field_simp
    linear_combination hdet
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, hg, adjugate_smul, Fintype.card_fin]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Phi]
  congr 1

/-- The explicit images of E₁₂, E₂₁, E₂₂ under M ↦ S M adj(S). -/
theorem Phi_E12 (h : ℕ) (α β γ δ : ℤ) :
    Phi h α β γ δ !![0, 1; 0, 0] = ((detS α β γ δ : ℤ) : ℝ)⁻¹ •
      !![-(α * h * γ : ℝ), (α : ℝ) ^ 2; -((h : ℝ) ^ 2 * γ ^ 2), α * h * γ] := by
  unfold Phi Smat
  rw [adjugate_fin_two_of, mul_fin_two, mul_fin_two]
  congr 1
  mat_smp <;> ring

theorem Phi_E21 {h : ℕ} (hh : h ≠ 0) (α β γ δ : ℤ) :
    Phi h α β γ δ !![0, 0; 1, 0] = ((detS α β γ δ : ℤ) : ℝ)⁻¹ •
      !![(β : ℝ) * δ / h, -((β : ℝ) ^ 2 / (h : ℝ) ^ 2); (δ : ℝ) ^ 2, -((β : ℝ) * δ / h)] := by
  have hhr : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hh
  unfold Phi Smat
  rw [adjugate_fin_two_of, mul_fin_two, mul_fin_two]
  congr 1
  mat_smp <;> field_simp

theorem Phi_E22 {h : ℕ} (hh : h ≠ 0) (α β γ δ : ℤ) :
    Phi h α β γ δ !![0, 0; 0, 1] = ((detS α β γ δ : ℤ) : ℝ)⁻¹ •
      !![-((β : ℝ) * γ), (α : ℝ) * β / h; -((h : ℝ) * γ * δ), (α : ℝ) * δ] := by
  have hhr : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hh
  unfold Phi Smat
  rw [adjugate_fin_two_of, mul_fin_two, mul_fin_two]
  congr 1
  mat_smp <;> field_simp

end

end NormalizerLean
