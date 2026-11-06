module

public import NormalizerDelta.Basic

@[expose] public section

/-!
# The generalized Newman bound

Γ_Δ(N) satisfies the hypotheses of the generic Newman argument; the only new ingredient is the element γ_p.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

variable {N : ℕ} {Δ : Subgroup (ZMod N)ˣ}

/-- Γ_Δ(N) satisfies the hypotheses of the generic Newman argument. -/
theorem newmanData_delta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    NewmanData N (GammaDeltaR N Δ) (epsDelta N Δ) (hDelta N Δ) where
  le := GammaDeltaR_le_Gamma0R
  T_mem := matT_mem_GammaDeltaR
  U_mem := matU_mem_GammaDeltaR
  inL := fun _ hY => inLe_of_mem_GammaDeltaR hY
  eps_dvd := epsDelta_dvd
  h_pos := by unfold hDelta; exact Finset.prod_pos (fun q hq => pow_pos (Nat.pos_of_mem_primeFactors hq) _)
  h_sq_dvd := by
    have hN := NeZero.ne N
    have hh : hDelta N Δ ≠ 0 := by
      unfold hDelta
      exact Finset.prod_ne_zero_iff.2 (fun q hq => pow_ne_zero _ (Nat.pos_of_mem_primeFactors hq).ne')
    rw [← Nat.factorization_le_iff_dvd (pow_ne_zero 2 hh) hN]
    intro p
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, factorization_hDelta]
    omega
  h_fact := factorization_hDelta
  gamma := by
    intro p hp hpN hj
    have hN := NeZero.ne N
    have hN2 : 2 ≤ N := le_trans hp.two_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hpN)
    set j := (epsDelta N Δ).factorization p
    set ν := N.factorization p
    have hε0 : epsDelta N Δ ≠ 0 := epsDelta_pos.ne'
    obtain ⟨u, hu, hnd⟩ : ∃ u ∈ Δ, ¬ p ^ (j + 1) ∣ (u : ZMod N).val ^ 2 - 1 := by
      by_contra hcon
      push Not at hcon
      have h1 : p ^ (j + 1) ∣ N := (hp.pow_dvd_iff_le_factorization hN).2 (by omega)
      have h2 : p ^ (j + 1) ∣ epsDelta N Δ := dvd_epsDelta_iff.2 ⟨h1, hcon⟩
      have := (hp.pow_dvd_iff_le_factorization hε0).1 h2
      omega
    have hpj : p ^ j ∣ (u : ZMod N).val ^ 2 - 1 :=
      (Nat.ordProj_dvd (epsDelta N Δ) p).trans (epsDelta_dvd_val hu)
    set v := (u : ZMod N).val
    have hv1 : 1 ≤ v := one_le_val_unit hN2 u
    have hcopN : Nat.Coprime v N := ZMod.val_coe_unit_coprime u
    have hb := Int.gcd_eq_gcd_ab v N
    rw [Int.gcd_natCast_natCast, hcopN] at hb
    set x := Int.gcdA v N
    set y := -Int.gcdB v N
    have hdet : x * v - y * N = 1 := by
      push_cast at hb
      simp only [y]
      linear_combination -hb
    refine ⟨x, y, v, hdet, ?_, ?_⟩
    · have hdet' : x * v - y * N = 1 := hdet
      refine ⟨ofZ (mkSL x y N v hdet'), ofZ_mem_toR (mkSL_mem_GammaDelta hdet' (dvd_refl _) hu ?_),
        coe_ofZ_mkSL hdet'⟩
      simp [v]
    · have hdet2 : (v : ℤ) * x - y * N = 1 := by linear_combination hdet
      have hpν : (p : ℤ) ^ ν ∣ (N : ℤ) := by exact_mod_cast Nat.ordProj_dvd N p
      have hpv : IsCoprime (p : ℤ) (v : ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
        exact (Nat.Coprime.coprime_dvd_right hpN hcopN).symm
      have hcast : (((v ^ 2 - 1 : ℕ)) : ℤ) = (v : ℤ) ^ 2 - 1 := by
        rw [Nat.cast_sub (Nat.one_le_pow _ _ hv1)]; push_cast; ring
      have hρ1 : (p : ℤ) ^ j ∣ 1 - (v : ℤ) ^ 2 := by
        have := Int.natCast_dvd_natCast.2 hpj
        rw [hcast] at this
        push_cast at this
        have := this.neg_right
        convert this using 1; ring
      have hρ2 : ¬ (p : ℤ) ^ (j + 1) ∣ 1 - (v : ℤ) ^ 2 := by
        intro hd
        apply hnd
        have hd' : (p : ℤ) ^ (j + 1) ∣ (((v ^ 2 - 1 : ℕ)) : ℤ) := by
          rw [hcast]; have := hd.neg_right; convert this using 1; ring
        exact_mod_cast hd'
      rcases gamma_val hp hdet2 hpν (by simp) hpv hρ1 hρ2 with h | ⟨-, hne, hval⟩
      · omega
      · refine ⟨fun h0 => hne (by linear_combination -h0), ?_⟩
        rw [show (v : ℤ) - x = -(x - v) by ring, vz_neg]
        exact hval

theorem gcd24_dvd_epsDelta [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : Nat.gcd N 24 ∣ epsDelta N Δ := by
  refine dvd_epsDelta_iff.2 ⟨Nat.gcd_dvd_left _ _, fun u _ => ?_⟩
  set k := Nat.gcd N 24
  by_cases hN : N = 1
  · subst hN; simp [k]
  have hN2 : 2 ≤ N := by have := NeZero.ne N; omega
  have h1 := one_le_val_unit hN2 u
  set a : ℤ := (((u⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ)
  set d : ℤ := ((u : ZMod N).val : ℤ)
  have had : a * d ≡ 1 [ZMOD N] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    simp [a, d]
  have hadk : a * d ≡ 1 [ZMOD k] := had.of_dvd (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left _ _))
  have hk : a ≡ d [ZMOD k] := by
    have hk : k ∣ 24 := Nat.gcd_dvd_right _ _
    have hk24 : k ≤ 24 := Nat.le_of_dvd (by norm_num) hk
    rw [← ZMod.intCast_eq_intCast_iff] at hadk ⊢
    push_cast at hadk
    generalize (a : ZMod k) = x at hadk ⊢
    generalize (d : ZMod k) = y at hadk ⊢
    revert x y
    interval_cases k <;> norm_num at hk <;> decide
  have hdd : d * d ≡ 1 [ZMOD k] := ((hk.symm.mul_right d).trans (by rw [mul_comm] at hadk ⊢; exact hadk))
  have : (k : ℤ) ∣ d ^ 2 - 1 := by
    have := (Int.ModEq.dvd hdd.symm)
    rw [pow_two]
    exact this
  have h2 : (k : ℤ) ∣ (((u : ZMod N).val ^ 2 - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ h1)]; push_cast; exact this
  exact_mod_cast h2

theorem hDelta_ne_zero [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : hDelta N Δ ≠ 0 :=
  (newmanData_delta N Δ).h_pos.ne'

end

end NormalizerLean
