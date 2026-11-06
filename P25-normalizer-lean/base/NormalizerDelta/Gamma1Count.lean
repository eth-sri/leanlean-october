module

public import NormalizerDelta.Gamma1KK

@[expose] public section

/-!
# §K: the diamonds, the quotient (ℤ/2)^{ω(N)}, and the order 2^{ω(N)} φ(N)/2

* `eq_of_isAtkinLehner_both`: an element is an Atkin–Lehner element for at most one Q ∥ N (the (0,1)
  entries give y²Q' = y'²Q, while p ∣ Q, p ∤ Q' forces p ∤ y).
* `isAtkinLehner_mul_gen`: w_{Q₁} w_{Q₂} is an Atkin–Lehner element for (Q₁/G)(Q₂/G), G = gcd(Q₁, Q₂).
* σ(g) = (p ↦ [p ∣ Q(g)]) is a homomorphism Nor(±Γ₁(N)) → (ℤ/2)^{primes of N} (N ≠ 4), trivial on
  ±Γ₁(N), onto (w_{Q_T}, Q_T = ∏_{p ∈ T} p^{v_p(N)}), with kernel the image of Γ₀(N).
* The diamonds Γ₀(N)/±Γ₁(N) have order [(ℤ/N)ˣ : {±1}] = φ(N)/2, and are normal since
  Nor(±Γ₁(N)) ≤ Nor(Γ₀(N)) (for N = 4 because ±Γ₁(4) = Γ₀(4)).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

variable {N : ℕ}

/-! ### Uniqueness of Q -/

/-! ### The general product law -/

theorem isAtkinLehner_mul_gen [NeZero N] {Q₁ Q₂ : ℕ} (hQ₁ : Q₁ ∣ N) (hQ₂ : Q₂ ∣ N)
    {g₁ g₂ : SL(2, ℝ)} (h₁ : IsAtkinLehner N Q₁ g₁) (h₂ : IsAtkinLehner N Q₂ g₂) :
    IsAtkinLehner N (Q₁ / Nat.gcd Q₁ Q₂ * (Q₂ / Nat.gcd Q₁ Q₂)) (g₁ * g₂) := by
  have hQ10 : Q₁ ≠ 0 := by rintro rfl; exact NeZero.ne N (Nat.eq_zero_of_zero_dvd hQ₁)
  have hQ20 : Q₂ ≠ 0 := by rintro rfl; exact NeZero.ne N (Nat.eq_zero_of_zero_dvd hQ₂)
  obtain ⟨G, hGdef⟩ : ∃ G, G = Nat.gcd Q₁ Q₂ := ⟨_, rfl⟩
  rw [← hGdef]
  have hG0 : 0 < G := hGdef ▸ Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hQ10)
  obtain ⟨q₁, hq₁⟩ : G ∣ Q₁ := hGdef ▸ Nat.gcd_dvd_left Q₁ Q₂
  obtain ⟨q₂, hq₂⟩ : G ∣ Q₂ := hGdef ▸ Nat.gcd_dvd_right Q₁ Q₂
  have e1 : Q₁ / G = q₁ := by rw [hq₁, Nat.mul_div_cancel_left _ hG0]
  have e2 : Q₂ / G = q₂ := by rw [hq₂, Nat.mul_div_cancel_left _ hG0]
  rw [e1, e2]
  have hq10 : q₁ ≠ 0 := by rintro rfl; simp at hq₁; exact hQ10 hq₁
  have hq20 : q₂ ≠ 0 := by rintro rfl; simp at hq₂; exact hQ20 hq₂
  have hL : G * q₁ * q₂ ∣ N := by
    have h := Nat.lcm_dvd hQ₁ hQ₂
    have : Nat.lcm Q₁ Q₂ = G * q₁ * q₂ := by
      rw [Nat.lcm, ← hGdef, hq₁, hq₂]
      rw [show G * q₁ * (G * q₂) = G * (G * q₁ * q₂) by ring, Nat.mul_div_cancel_left _ hG0]
    rwa [this] at h
  obtain ⟨L, hLN⟩ := hL
  obtain ⟨x₁, y₁, z₁, w₁, hd₁, hg₁⟩ := h₁
  obtain ⟨x₂, y₂, z₂, w₂, hd₂, hg₂⟩ := h₂
  have hGz : (G : ℤ) ≠ 0 := by exact_mod_cast hG0.ne'
  have hq1z : (q₁ : ℤ) ≠ 0 := by exact_mod_cast hq10
  have hq2z : (q₂ : ℤ) ≠ 0 := by exact_mod_cast hq20
  have r₁ : (G : ℤ) * q₁ * x₁ * w₁ - q₂ * L * y₁ * z₁ = 1 := by
    apply mul_left_cancel₀ (mul_ne_zero hGz hq1z)
    rw [hq₁, hLN] at hd₁; push_cast at hd₁; linear_combination hd₁
  have r₂ : (G : ℤ) * q₂ * x₂ * w₂ - q₁ * L * y₂ * z₂ = 1 := by
    apply mul_left_cancel₀ (mul_ne_zero hGz hq2z)
    rw [hq₂, hLN] at hd₂; push_cast at hd₂; linear_combination hd₂
  refine ⟨G * x₁ * x₂ + L * y₁ * z₂, q₁ * x₁ * y₂ + q₂ * y₁ * w₂, q₂ * z₁ * x₂ + q₁ * w₁ * z₂,
    L * z₁ * y₂ + G * w₁ * w₂, ?_, ?_⟩
  · rw [hLN]; push_cast
    linear_combination ((q₁ : ℤ) * q₂ * (G * q₂ * x₂ * w₂ - q₁ * L * y₂ * z₂)) * r₁ +
      ((q₁ : ℤ) * q₂) * r₂
  · have hsq : Real.sqrt Q₁ * Real.sqrt Q₂ = G * Real.sqrt ((q₁ * q₂ : ℕ) : ℝ) := by
      rw [← Real.sqrt_mul (Nat.cast_nonneg _), hq₁, hq₂]
      push_cast
      rw [show (G : ℝ) * q₁ * (G * q₂) = G ^ 2 * (q₁ * q₂) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (Nat.cast_nonneg _)]
    have hs1 : Real.sqrt Q₁ ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hQ10)).ne'
    have hs2 : Real.sqrt Q₂ ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hQ20)).ne'
    have hGr : (G : ℝ) ≠ 0 := by exact_mod_cast hG0.ne'
    rw [Matrix.SpecialLinearGroup.coe_mul, hg₁, hg₂, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      ← mul_inv, hsq, mul_inv, mul_comm (G : ℝ)⁻¹, mul_smul]
    congr 1
    rw [hLN, hq₁, hq₂]
    push_cast
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp <;> ring

/-! ### Exact divisors -/

/-! ### Nor(±Γ₁(N)) ≤ Nor(Γ₀(N)); the diamonds are normal -/

/-! ### The order of the diamonds -/

/-! ### σ : Nor(±Γ₁(N)) → (ℤ/2)^{primes of N} -/

section Sigma

variable [NeZero N] (hN : N ≠ 4)

theorem mul_div_gcd_dvd {Q₁ Q₂ : ℕ} (hQ₁ : Q₁ ∣ N) (hQ₂ : Q₂ ∣ N) :
    Q₁ / Nat.gcd Q₁ Q₂ * (Q₂ / Nat.gcd Q₁ Q₂) ∣ N := by
  have h1 : Q₁ / Nat.gcd Q₁ Q₂ * (Q₂ / Nat.gcd Q₁ Q₂) ∣ Q₁ / Nat.gcd Q₁ Q₂ * Q₂ :=
    mul_dvd_mul_left _ (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _))
  have h2 : Q₁ / Nat.gcd Q₁ Q₂ * Q₂ = Nat.lcm Q₁ Q₂ := by
    rw [Nat.lcm, Nat.div_mul_right_comm (Nat.gcd_dvd_left _ _)]
  rw [h2] at h1
  exact h1.trans (Nat.lcm_dvd hQ₁ hQ₂)

end Sigma

end

end NormalizerLean
