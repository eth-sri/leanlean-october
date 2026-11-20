module

public import NormalizerLean.Basic

@[expose] public section

/-! Integral lifts and arithmetic for Γ_Δ(N). -/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

variable {N : ℕ} {Δ : Subgroup (ZMod N)ˣ}

theorem GammaDelta_le_Gamma0 : GammaDelta N Δ ≤ CongruenceSubgroup.Gamma0 N := fun _ h => h.1

theorem GammaDeltaR_le_Gamma0R : GammaDeltaR N Δ ≤ Gamma0R N :=
  Subgroup.map_mono GammaDelta_le_Gamma0

/-- An integer matrix of determinant 1. -/
def mkSL (a b c d : ℤ) (h : a * d - b * c = 1) : SL(2, ℤ) := ⟨!![a, b; c, d], by
  rw [det_fin_two_of]; exact h⟩

/-! ### ε_Δ -/

theorem dvd_epsDelta_iff [NeZero N] {m : ℕ} :
    m ∣ epsDelta N Δ ↔ m ∣ N ∧ ∀ u ∈ Δ, m ∣ (u : ZMod N).val ^ 2 - 1 := by
  classical
  unfold epsDelta
  rw [Nat.dvd_gcd_iff, Finset.dvd_gcd_iff]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem epsDelta_pos [NeZero N] : 0 < epsDelta N Δ :=
  Nat.pos_of_dvd_of_pos (dvd_epsDelta_iff.1 dvd_rfl).1 (NeZero.pos N)

/-- Bézout witnesses for a lift with bottom row `(N, val u)`. -/
theorem exists_lift_unit (u : (ZMod N)ˣ) :
    ∃ x y : ℤ, x * ((u : ZMod N).val : ℤ) - y * N = 1 := by
  obtain ⟨x, y, h⟩ := (ZMod.val_coe_unit_coprime u).isCoprime
  exact ⟨x, -y, by simpa using h⟩

theorem factorization_hDelta [NeZero N] (p : ℕ) :
    (hDelta N Δ).factorization p =
      min ((epsDelta N Δ).factorization p) (N.factorization p / 2) := by
  unfold hDelta
  rw [Nat.factorization_prod (fun q hq => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hq).ne_zero),
    Finset.sum_apply']
  rw [Finset.sum_congr rfl (fun q hq => by
    rw [(Nat.prime_of_mem_primeFactors hq).factorization_pow, Finsupp.single_apply]),
    Finset.sum_ite_eq']
  split_ifs with hp
  · rfl
  · have : N.factorization p = 0 := by
      rwa [← Finsupp.notMem_support_iff, Nat.support_factorization]
    simp [this]

end

theorem hDelta_pos (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : 0 < hDelta N Δ :=
  Finset.prod_pos fun _ hp => pow_pos (Nat.pos_of_mem_primeFactors hp) _

theorem hDelta_sq_dvd (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : hDelta N Δ ^ 2 ∣ N := by
  rw [← Nat.factorization_le_iff_dvd (pow_ne_zero 2 (hDelta_pos N Δ).ne') (NeZero.ne N)]
  intro p
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, factorization_hDelta]
  omega

theorem nDelta_mul (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    nDelta N Δ * hDelta N Δ ^ 2 = N :=
  Nat.div_mul_cancel (hDelta_sq_dvd N Δ)

instance (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : NeZero (nDelta N Δ) :=
  ⟨left_ne_zero_of_mul (nDelta_mul N Δ ▸ NeZero.ne N)⟩

end NormalizerLean
