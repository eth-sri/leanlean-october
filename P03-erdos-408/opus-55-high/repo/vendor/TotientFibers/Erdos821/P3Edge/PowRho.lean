module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

lemma pow_mul_rho_bound_aux (rho : ℝ) (hrho0 : 0 < rho) (hrho1 : rho < 1) (A : ℕ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ, (z : ℝ) ^ A * rho ^ z ≤ C := by
  classical
  have hlog : Real.log rho < 0 := by
    have h1 := Real.log_lt_log hrho0 hrho1
    simpa using h1
  let δ : ℝ := -Real.log rho / 2
  have hδ : 0 < δ := by
    unfold δ
    linarith
  let e1 : ℝ := Real.exp 1
  have he1 : 1 < e1 := by
    have h := Real.add_one_le_exp 1
    norm_num at h
    linarith
  have he1pos : 0 < e1 := lt_trans zero_lt_one he1
  let C0 : ℝ := (A / (e1 * δ)) ^ A
  have hC0pos : 0 < C0 := by
    unfold C0
    apply pow_pos
    apply div_pos
    · positivity
    · positivity
  have key : ∀ z : ℕ, (z : ℝ) ^ A ≤ C0 * Real.exp (δ * z) := by
    intro z
    have hy : (δ * z / (A : ℝ)) ≤ Real.exp (δ * z / A - 1) := by
      have h := Real.add_one_le_exp (δ * (z : ℝ) / A - 1)
      have heq : (δ * (z : ℝ) / (A : ℝ) - 1) + 1 = δ * z / (A : ℝ) := by ring_nf
      rw [heq] at h
      exact h
    have hexp : Real.exp (δ * (z : ℝ) / (A : ℝ) - 1) = Real.exp (δ * z / (A : ℝ)) / e1 := by
      rw [Real.exp_sub]
    rw [hexp] at hy
    have hApos : (0:ℝ) < (A : ℝ) := by positivity
    have hz_le : (z : ℝ) ≤ (A / (e1 * δ)) * Real.exp (δ * z / (A : ℝ)) := by
      have h1 : ((A : ℝ) / δ) * (δ * (z : ℝ) / (A : ℝ)) ≤ ((A : ℝ) / δ) * (Real.exp (δ * z / (A : ℝ)) / e1) := by
        apply mul_le_mul_of_nonneg_left hy
        apply div_nonneg hApos.le hδ.le
      have lhs : ((A : ℝ) / δ) * (δ * (z : ℝ) / (A : ℝ)) = (z : ℝ) := by
        field_simp
      have rhs : ((A : ℝ) / δ) * (Real.exp (δ * z / (A : ℝ)) / e1) = (A / (e1 * δ)) * Real.exp (δ * z / (A : ℝ)) := by
        field_simp
      rw [lhs, rhs] at h1
      exact h1
    have hz_nonneg : (0:ℝ) ≤ (z : ℝ) := Nat.cast_nonneg _
    have hC_nonneg : (0:ℝ) ≤ (A / (e1 * δ)) * Real.exp (δ * (z : ℝ) / (A : ℝ)) := by
      apply mul_nonneg
      · positivity
      · positivity
    have hpow := pow_le_pow_left₀ hz_nonneg hz_le A
    have hexpA : ((A / (e1 * δ)) * Real.exp (δ * (z : ℝ) / (A : ℝ))) ^ A =
        C0 * Real.exp (δ * (z : ℝ)) := by
      unfold C0
      rw [mul_pow]
      congr 1
      have h2 := Real.exp_nat_mul (δ * (z : ℝ) / (A : ℝ)) A
      have heq : (A : ℝ) * (δ * (z : ℝ) / (A : ℝ)) = δ * (z : ℝ) := by
        field_simp
      rw [heq] at h2
      exact h2.symm
    rw [hexpA] at hpow
    exact hpow
  have rho_eq : ∀ z : ℕ, rho ^ z = Real.exp (Real.log rho * (z : ℝ)) := by
    intro z
    have h1 : rho ^ ((z : ℝ)) = Real.exp (Real.log rho * (z : ℝ)) := Real.rpow_def_of_pos hrho0 _
    have h2 := Real.rpow_natCast rho z
    rw [h2] at h1
    -- h1 : rho^z (Nat pow, via rpow_natCast? Actually h2 says rpow = Nat pow, so rw h2 at h1 replaces rpow with Nat pow? Wait h1 LHS is rpow, h2 LHS is rpow, RHS Nat pow. rw h2 at h1 replaces rpow in h1 with Nat pow, giving Nat pow = exp. Good.
    exact h1
  -- Combine: z^A * rho^z ≤ C0 * exp(δz) * exp(log rho * z) = C0 * exp((δ+log rho)z) = C0 * exp(log rho/2 * z) ≤ C0
  refine ⟨C0, hC0pos, fun z => ?_⟩
  have hz := key z
  have hr := rho_eq z
  calc (z : ℝ) ^ A * rho ^ z
      = (z : ℝ) ^ A * Real.exp (Real.log rho * z) := by simp_all
    _ ≤ (C0 * Real.exp (δ * z)) * Real.exp (Real.log rho * z) := by
        apply mul_le_mul_of_nonneg_right hz (by positivity)
    _ = C0 * (Real.exp (δ * z) * Real.exp (Real.log rho * z)) := by ring_nf
    _ = C0 * Real.exp ((δ + Real.log rho) * z) := by
        rw [← Real.exp_add]
        ring
    _ ≤ C0 * 1 := by
        apply mul_le_mul_of_nonneg_left _ hC0pos.le
        -- exp((δ+log rho)z) ≤ 1 since (δ+log rho) = log rho/2 <0 and z≥0 => exponent ≤0
        have hexp_nonpos : (δ + Real.log rho) * (z : ℝ) ≤ 0 := by
          have hsum : δ + Real.log rho = Real.log rho / 2 := by
            unfold δ
            ring_nf
          rw [hsum]
          apply mul_nonpos_of_nonpos_of_nonneg
          · linarith
          · simp
        simp_all
    _ = C0 := by ring_nf

lemma pow_mul_rho_bound (rho : ℝ) (hrho0 : 0 < rho) (hrho1 : rho < 1) (Amax : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ) (_ : a ≤ Amax) (z : ℕ), (z : ℝ) ^ a * rho ^ z ≤ C := by
  classical
  -- Handle a=0 separately (1*rho^z ≤1), and a≥1 via aux with A=a (need uniform C over a≤Amax)
  -- Since Amax finite, take max over a≤Amax of individual bounds.
  -- For each a, get C_a; then take max +1 to ensure positivity and uniform.
  -- To avoid max over many, use bound with A=Amax: z^a ≤ max(1, z^Amax)? Since a≤Amax.
  -- Simpler: prove uniform bound via Amax directly: z^a ≤ 1 + z^Amax? Since for z≥1, z^a ≤ z^Amax; for z=0, 0^a ≤1? Need careful for a=0 (0^0=1).
  -- Use: z^a ≤ 1 + z^Amax for all z,a≤Amax? Check: If z=0, LHS is 0^a (0 if a>0, 1 if a=0) ≤1 ≤1+z^Amax. Good. If z≥1, z^a ≤ z^Amax (since a≤Amax and z≥1, monotonic). So z^a ≤ z^Amax ≤1+z^Amax. Good. Then z^a*rho^z ≤ (1+z^Amax)*rho^z = rho^z + z^Amax*rho^z ≤1 + C_Amax (since rho^z≤1 and second term bounded by aux). Good!
  -- Need aux bound for Amax (if Amax≥1; if Amax=0, then a=0 only, bound by 1).
  by_cases hMax : Amax = 0
  · subst hMax
    refine ⟨1, zero_lt_one, fun a ha z => ?_⟩
    have ha0 := Nat.le_zero.mp ha
    subst ha0
    simp
    -- 1*rho^z ≤1 since rho^z ≤1 (as 0<rho≤1? Actually rho<1, rho^z ≤1)
    have hrho_le : rho ^ z ≤ (1:ℝ) := pow_le_one₀ hrho0.le hrho1.le
    omega
  · -- Amax ≥1
    have hAmax_pos := Nat.one_le_iff_ne_zero.mpr hMax
    obtain ⟨Cmax, hCmax_pos, hCmax⟩ := pow_mul_rho_bound_aux rho hrho0 hrho1 Amax hAmax_pos
    refine ⟨1 + Cmax, by linarith, fun a ha z => ?_⟩
    have hz_a_le : (z : ℝ) ^ a ≤ 1 + (z : ℝ) ^ Amax := by
      by_cases hz0 : (z : ℝ) = 0
      · -- z=0: LHS is 0^a (0 or 1) ≤1 ≤1+...
        have h0a : (z : ℝ) ^ a ≤ (1:ℝ) := by
          rw [hz0]
          exact pow_le_one₀ le_rfl zero_le_one
        simp_all
      · -- z≠0, so z≥1 as Nat? Actually (z:ℝ)≠0 => z≠0 => z≥1 => (z:ℝ)≥1
        have hz_ge : (1:ℝ) ≤ (z : ℝ) := by
          have hzn : 1 ≤ z := Nat.one_le_iff_ne_zero.mpr (fun h => hz0 (by simp_all))
          exact Nat.one_le_cast.mpr hzn
        have hpow_le : (z : ℝ) ^ a ≤ (z : ℝ) ^ Amax := pow_le_pow_right₀ hz_ge ha
        linarith
    have hrho_le_one : rho ^ z ≤ (1:ℝ) := pow_le_one₀ hrho0.le hrho1.le
    calc (z : ℝ) ^ a * rho ^ z
        ≤ (1 + (z : ℝ) ^ Amax) * rho ^ z := by
          simp_all
      _ = rho ^ z + (z : ℝ) ^ Amax * rho ^ z := by ring_nf
      _ ≤ 1 + Cmax := by
          grind

lemma descFactorial_le_pow (z a : ℕ) : ((z.descFactorial a : ℕ) : ℝ) ≤ (z : ℝ) ^ a := by
  have h := Nat.descFactorial_le_pow z a
  have hcast : ((z.descFactorial a : ℕ) : ℝ) ≤ (((z ^ a : ℕ)) : ℝ) := Nat.cast_le.mpr h
  simp_all

end Erdos821.P3Edge
