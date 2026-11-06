/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import DOZZ.Upsilon.Continuation
import DOZZ.Upsilon.FullShifts
import DOZZ.Upsilon.Uniqueness
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.NumberTheory.Real.Irrational

/-!
# Zero structure of the entire Upsilon function

The first reciprocal-Gamma shift gives the zero lattice and its local orders.
-/

@[expose] public section

open Complex Filter Topology

namespace DOZZ.Proofs

variable {γ : ℝ}

private noncomputable def upsilonB (γ : ℝ) : ℂ := ((γ / 2 : ℝ) : ℂ)

private noncomputable def upsilonLeftFactor (γ : ℝ) : ℂ → ℂ :=
  (fun z : ℂ => upsilonB γ ^ ((γ : ℂ) * z - 1) *
    Complex.Gamma (1 - upsilonB γ * z)) *
  (fun z => (Complex.Gamma (upsilonB γ * z))⁻¹)

private theorem upsilonB_cast γ : upsilonB γ = (γ / 2 : ℂ) := by
  exact Complex.ofReal_div γ 2

private noncomputable def upsilonShiftN (γ : ℝ) (n : ℕ) : ℂ :=
  (n : ℂ) * upsilonB γ

private theorem upsilonShiftN_re γ (n : ℕ) :
    (upsilonShiftN γ n).re = (n : ℝ) * (γ / 2) := by
  simp [upsilonShiftN, upsilonB, Complex.mul_re]

private theorem upsilonShiftN_succ γ n :
    upsilonShiftN γ (n + 1) = upsilonShiftN γ n + upsilonB γ := by
  simp [upsilonShiftN, Nat.cast_add]
  ring




/-- The derivative at zero is the value one half-period to the right. -/
theorem IsUpsilon.deriv_zero {U} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hU : IsUpsilon γ U) : deriv U 0 = U (γ / 2) := by
  have upsilonLeftFactor_hasDerivAt_zero : HasDerivAt (upsilonLeftFactor γ) 1 0 := by
    have differentiableAt_upsilonLeftUnitFactor : DifferentiableAt ℂ (fun z => upsilonB γ ^ ((γ : ℂ) * z - 1) * Complex.Gamma (1 - upsilonB γ * z)) 0 := by
      have hpow : DifferentiableAt ℂ
          (fun z => upsilonB γ ^ ((γ : ℂ) * z - 1)) 0 := by
        apply DifferentiableAt.const_cpow
        · fun_prop
        · exact Or.inl (by apply Complex.ofReal_ne_zero.mpr; exact div_ne_zero hγ.ne' (by norm_num))
      exact hpow.mul (by exact DifferentiableAt.fun_comp' 0 (f := fun z => 1 - upsilonB γ * z) (g := Complex.Gamma) (by simpa using Complex.differentiableAt_Gamma_one) (by fun_prop))
    have reciprocalGamma_hasDerivAt_zero : HasDerivAt (fun z => (Complex.Gamma z)⁻¹) 1 0 := by
      have hGamma := Complex.tendsto_self_mul_Gamma_nhds_zero
      have hprod_ne := hGamma.eventually (isOpen_ne.mem_nhds (by norm_num : (1 : ℂ) ≠ 0))
      have hRatio :
          (fun z => (z * Complex.Gamma z)⁻¹) =ᶠ[𝓝[≠] (0 : ℂ)]
            (fun z => z⁻¹ * (Complex.Gamma z)⁻¹) := by
        filter_upwards [hprod_ne] with z hz
        have hz0 : z ≠ 0 := by
          intro h
          subst z
          simp at hz
        have hΓ := (mul_ne_zero_iff.mp hz).2
        field_simp [hz0, hΓ]
      exact (hasDerivAt_iff_tendsto_slope_zero).mpr (by simpa using (by simpa [Complex.Gamma_zero] using ((tendsto_congr' hRatio).mp (show Tendsto (fun z => (z * Complex.Gamma z)⁻¹) (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) by simpa using hGamma.inv₀ (by norm_num : (1 : ℂ) ≠ 0)))))
    simpa [upsilonLeftFactor, Complex.Gamma_zero, Complex.Gamma_one,
      Complex.cpow_neg, (show upsilonB γ ≠ 0 by apply Complex.ofReal_ne_zero.mpr; exact div_ne_zero hγ.ne' (by norm_num))] using ((differentiableAt_upsilonLeftUnitFactor).hasDerivAt.mul (show HasDerivAt (fun z => (Complex.Gamma (upsilonB γ * z))⁻¹) (upsilonB γ) 0 by simpa only [Function.comp_def, one_mul] using HasDerivAt.comp (0 : ℂ) (show HasDerivAt (fun z => (Complex.Gamma z)⁻¹) 1 (upsilonB γ * (0 : ℂ)) by simpa using reciprocalGamma_hasDerivAt_zero) (by simpa using (hasDerivAt_const_mul (upsilonB γ) : HasDerivAt (fun z => upsilonB γ * z) (upsilonB γ) 0))))
  have hLocalEq :
      (fun z => U z) =ᶠ[𝓝 (0 : ℂ)]
        (upsilonLeftFactor γ * fun z => U (z + upsilonB γ)) := by
    filter_upwards [(Complex.isOpen_re_lt (2 / γ)).mem_nhds (by dsimp; simpa using (by positivity))] with z hz
    have hFactorEq : upsilonLeftFactor γ z * U (z + upsilonB γ) = U z := by
      change ((upsilonB γ) ^ ((γ : ℂ) * z - 1) *
        Complex.Gamma (1 - upsilonB γ * z) *
        (Complex.Gamma (upsilonB γ * z))⁻¹ * U (z + upsilonB γ)) = U z
      rw [upsilonB_cast]
      simpa [mul_assoc] using (IsUpsilon.shift_b_reciprocal hγ hγ2 hU z hz)
    change U z = (upsilonLeftFactor γ * fun w : ℂ => U (w + upsilonB γ)) z
    rw [Pi.mul_apply]
    exact hFactorEq.symm
  calc
    deriv U 0 = U (upsilonB γ) := ((show HasDerivAt (upsilonLeftFactor γ * fun z => U (z + upsilonB γ)) (U (upsilonB γ)) 0 by simpa [(show upsilonLeftFactor γ 0 = 0 by simp [upsilonLeftFactor, Complex.Gamma_zero])] using ((upsilonLeftFactor_hasDerivAt_zero).mul (DifferentiableAt.fun_comp' 0 (f := fun z => z + upsilonB γ) (g := U) (hU.1 (0 + upsilonB γ)) (by fun_prop)).hasDerivAt)).congr_of_eventuallyEq hLocalEq).deriv
    _ = U (γ / 2) := by rw [upsilonB_cast]

private theorem IsUpsilon.left_product {U} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hU : IsUpsilon γ U) :
    ∀ (N : ℕ) (z : ℂ),
      (∀ j ∈ Finset.range N, (z + upsilonShiftN γ j).re < 2 / γ) →
      U z = U (z + upsilonShiftN γ N) *
        ∏ j ∈ Finset.range N, upsilonLeftFactor γ (z + upsilonShiftN γ j) := by
  intro N
  induction N with
  | zero =>
      intro z hz
      simp [upsilonShiftN]
  | succ N ih =>
      intro z hstage
      have hfirst : upsilonLeftFactor γ z * U (z + upsilonB γ) = U z := by
        change ((upsilonB γ) ^ ((γ : ℂ) * z - 1) *
          Complex.Gamma (1 - upsilonB γ * z) *
          (Complex.Gamma (upsilonB γ * z))⁻¹ * U (z + upsilonB γ)) = U z
        rw [upsilonB_cast]
        simpa [mul_assoc] using (IsUpsilon.shift_b_reciprocal hγ hγ2 hU z (by simpa [upsilonShiftN] using hstage 0 (by simp)))
      have hstage' : ∀ j ∈ Finset.range N,
          ((z + upsilonB γ) + upsilonShiftN γ j).re < 2 / γ := by
        intro j hj
        rw [(show z + upsilonB γ + upsilonShiftN γ j = z + upsilonShiftN γ (j + 1) by rw [upsilonShiftN_succ]; ring)]
        exact (hstage (j + 1) (by apply Finset.mem_range.mpr; exact Nat.succ_lt_succ (Finset.mem_range.mp hj)))
      have hprod :
          (∏ j ∈ Finset.range N,
            upsilonLeftFactor γ ((z + upsilonB γ) + upsilonShiftN γ j)) =
          ∏ j ∈ Finset.range N,
            upsilonLeftFactor γ (z + upsilonShiftN γ (j + 1)) := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [(show z + upsilonB γ + upsilonShiftN γ j = z + upsilonShiftN γ (j + 1) by rw [upsilonShiftN_succ]; ring)]
      rw [← hfirst, (ih (z + upsilonB γ) hstage'), (show z + upsilonB γ + upsilonShiftN γ N = z + upsilonShiftN γ (N + 1) by rw [upsilonShiftN_succ]; ring), hprod, Finset.prod_range_succ']
      simp only [upsilonShiftN, Nat.cast_zero, zero_mul, add_zero]
      ring




private theorem IsUpsilon.zero_left_iff {U} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hU : IsUpsilon γ U) (z : ℂ) (hz : z.re ≤ 0) :
    U z = 0 ↔ ∃ m n : ℕ, z = -((m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) : ℝ) := by
  have upsilonLeftFactor_eq_zero_iff {z : ℂ} (hz : z.re ≤ 0) : upsilonLeftFactor γ z = 0 ↔ ∃ n : ℕ, upsilonB γ * z = -(n : ℂ) := by
    have hbR : 0 < γ / 2 := by positivity
    have hGamma1 : Complex.Gamma (1 - upsilonB γ * z) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by
        rw [Complex.sub_re, Complex.one_re, (show (upsilonB γ * z).re = (γ / 2) * z.re by simp [upsilonB, Complex.mul_re])]
        have := mul_nonpos_of_nonneg_of_nonpos hbR.le hz
        linarith)
    change (upsilonB γ ^ ((γ : ℂ) * z - 1) *
        Complex.Gamma (1 - upsilonB γ * z)) *
        (Complex.Gamma (upsilonB γ * z))⁻¹ = 0 ↔ _
    rw [mul_eq_zero]
    constructor
    · rintro (hbad | hrecip)
      · exact ((mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (by apply Complex.ofReal_ne_zero.mpr; exact hbR.ne'))) hGamma1) hbad).elim
      · rw [inv_eq_zero] at hrecip
        exact (Complex.Gamma_eq_zero_iff (upsilonB γ * z)).mp hrecip
    · rintro ⟨n, harg⟩
      right
      rw [inv_eq_zero, harg, Complex.Gamma_neg_nat_eq_zero]
  have upsilon_arg_eq_lattice_iff (j : ℕ) (n : ℕ) z : upsilonB γ * (z + upsilonShiftN γ j) = -(n : ℂ) ↔ z = -((j : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) : ℝ) := by
    have hb : upsilonB γ ≠ 0 := by
      apply Complex.ofReal_ne_zero.mpr
      exact (div_pos hγ (by norm_num)).ne'
    have hshiftCast : upsilonShiftN γ j =
        (((j : ℝ) * (γ / 2) : ℝ) : ℂ) := by
      change ((j : ℝ) : ℂ) * ((γ / 2 : ℝ) : ℂ) = _
      exact (Complex.ofReal_mul _ _).symm
    constructor
    · intro harg
      have hmul : upsilonB γ * z = -(n : ℂ) - upsilonB γ * upsilonShiftN γ j := by
        calc
          upsilonB γ * z =
              upsilonB γ * (z + upsilonShiftN γ j) -
                upsilonB γ * upsilonShiftN γ j := by ring
          _ = _ := by rw [harg]
      have hsolve : z = -(n : ℂ) / upsilonB γ - upsilonShiftN γ j := by
        calc
          z = 1 * z := by simp
          _ = (upsilonB γ)⁻¹ * (upsilonB γ * z) := by
            calc
              1 * z = (upsilonB γ)⁻¹ * upsilonB γ * z := by
                rw [inv_mul_cancel₀ hb, one_mul]
              _ = (upsilonB γ)⁻¹ * (upsilonB γ * z) := by ring
          _ = (upsilonB γ)⁻¹ *
              (-(n : ℂ) - upsilonB γ * upsilonShiftN γ j) := by rw [hmul]
          _ = _ := by field_simp [hb]
      rw [neg_div, (show (n : ℂ) / upsilonB γ = (((n : ℝ) / (γ / 2) : ℝ) : ℂ) by change ((n : ℝ) : ℂ) / ((γ / 2 : ℝ) : ℂ) = _; exact (Complex.ofReal_div _ _).symm), hshiftCast, (show (n : ℝ) / (γ / 2) = (n : ℝ) * (2 / γ) by field_simp [hγ.ne'])] at hsolve
      calc
        z = -(((n : ℝ) * (2 / γ) : ℝ) : ℂ) -
            (((j : ℝ) * (γ / 2) : ℝ) : ℂ) := hsolve
        _ = -((j : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) : ℝ) := by
          push_cast
          ring
    · intro h
      rw [h, hshiftCast, upsilonB_cast]
      push_cast
      field_simp [hγ.ne']
      ring
  have exists_upsilonShiftN_between_zero_and_B : ∃ N : ℕ, 0 < (z + upsilonShiftN γ N).re ∧ (z + upsilonShiftN γ N).re ≤ γ / 2 := by
    have hb : 0 < γ / 2 := by positivity
    let y := -z.re / (γ / 2)
    let N := Nat.floor y + 1
    have hNcast : (N : ℝ) = (Nat.floor y : ℝ) + 1 := by simp [N]
    have hNle : (N : ℝ) ≤ y + 1 := by
      rw [hNcast]
      have := Nat.floor_le (show 0 ≤ y by dsimp [y]; exact div_nonneg (neg_nonneg.mpr hz) hb.le)
      linarith
    have hzy : z.re = -(y * (γ / 2)) := by
      dsimp [y]
      field_simp [ne_of_gt hb]
    refine ⟨N, ?_, ?_⟩
    · rw [Complex.add_re, upsilonShiftN_re]
      simpa using (by rw [hzy]; linarith only [(mul_lt_mul_of_pos_right (show y < (N : ℝ) by rw [hNcast]; exact Nat.lt_floor_add_one y) hb)])
    · rw [Complex.add_re, upsilonShiftN_re]
      exact (by rw [hzy]; linarith only [(mul_le_mul_of_nonneg_right hNle hb.le)])
  obtain ⟨N, hEnd0, hEndB⟩ := exists_upsilonShiftN_between_zero_and_B
  have hbpos : 0 < γ / 2 := by positivity
  have hEndQ : (z + upsilonShiftN γ N).re < Q γ := by
    have hbQ : γ / 2 < Q γ := by
      unfold Q
      have : 0 < 2 / γ := by positivity
      linarith
    exact hEndB.trans_lt hbQ
  have hStageLe : ∀ j ∈ Finset.range N,
      (z + upsilonShiftN γ j).re ≤ 0 := by
    intro j hj
    have hmul := mul_le_mul_of_nonneg_right
      (show (j : ℝ) + 1 ≤ (N : ℝ) by exact_mod_cast (Nat.succ_le_iff.mpr (Finset.mem_range.mp hj)))
      (show 0 ≤ γ / 2 by positivity)
    rw [add_mul] at hmul
    linarith [(show (z + upsilonShiftN γ j).re + γ / 2 ≤ (z + upsilonShiftN γ N).re by rw [Complex.add_re, Complex.add_re, upsilonShiftN_re, upsilonShiftN_re]; linarith), hEndB]
  have hStage : ∀ j ∈ Finset.range N,
      (z + upsilonShiftN γ j).re < 2 / γ := by
    intro j hj
    have := hStageLe j hj
    have hpos : 0 < 2 / γ := by positivity
    linarith
  have hUzero : U z = 0 ↔
      (∏ j ∈ Finset.range N,
        upsilonLeftFactor γ (z + upsilonShiftN γ j)) = 0 := by
    rw [(IsUpsilon.left_product hγ hγ2 hU N z hStage), mul_eq_zero]
    simp [(show U (z + upsilonShiftN γ N) ≠ 0 by rw [hU.2 _ hEnd0 hEndQ]; exact Complex.exp_ne_zero _)]
  constructor
  · intro hzero
    obtain ⟨j, hj, hfactor⟩ := Finset.prod_eq_zero_iff.mp (hUzero.mp hzero)
    obtain ⟨n, harg⟩ := (upsilonLeftFactor_eq_zero_iff (hStageLe j hj)).mp hfactor
    exact ⟨j, n, ((upsilon_arg_eq_lattice_iff j n z).mp harg)⟩
  · rintro ⟨m, n, hrep⟩
    let y := -z.re / (γ / 2)
    have hmle : (m : ℝ) ≤ y := by
      dsimp [y]
      apply (le_div_iff₀ hbpos).2
      rw [(show z.re = -((m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ)) by simpa using (congrArg Complex.re hrep))]
      have : 0 ≤ (n : ℝ) * (2 / γ) := by positivity
      linarith
    have hmN : m < N := by
      have hEnd0' : 0 < z.re + (N : ℝ) * (γ / 2) := by
        have hEnd0'' := hEnd0
        rw [Complex.add_re, upsilonShiftN_re] at hEnd0''
        exact hEnd0''
      rw [(show z.re = -(y * (γ / 2)) by dsimp [y]; field_simp [ne_of_gt hbpos])] at hEnd0'
      exact_mod_cast lt_of_le_of_lt hmle (lt_of_mul_lt_mul_right (show y * (γ / 2) < (N : ℝ) * (γ / 2) by linarith only [hEnd0']) hbpos.le)
    have hzj : (z + upsilonShiftN γ m).re ≤ 0 := hStageLe m (by
      apply Finset.mem_range.mpr
      exact hmN)
    exact hUzero.mpr (Finset.prod_eq_zero_iff.mpr ⟨m, Finset.mem_range.mpr hmN, ((upsilonLeftFactor_eq_zero_iff hzj).2 ⟨n, ((upsilon_arg_eq_lattice_iff m n z).2 hrep)⟩)⟩)

/-- The zeros are the two reflected negative reciprocal-Gamma lattices. -/
theorem IsUpsilon.eq_zero_iff {U} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hU : IsUpsilon γ U) z :
    U z = 0 ↔ ∃ m n : ℕ, z = -(m * (γ / 2) + n * (2 / γ) : ℝ) ∨
      z = (Q γ + m * (γ / 2) + n * (2 / γ) : ℝ) := by
  constructor
  · intro hz
    by_cases hleft : z.re ≤ 0
    · obtain ⟨m, n, hrep⟩ :=
        (IsUpsilon.zero_left_iff hγ hγ2 hU z hleft).mp hz
      exact ⟨m, n, Or.inl hrep⟩
    · have hzpos : 0 < z.re := lt_of_not_ge hleft
      by_cases hmid : z.re < Q γ
      · have hzexp := hU.2 z hzpos hmid
        exact (Complex.exp_ne_zero _ (show Complex.exp (upsilonLog γ z) = 0 by simpa [hz] using hzexp.symm)).elim
      · have hreflectRe : ((Q γ : ℂ) - z).re ≤ 0 := by
          rw [Complex.sub_re, Complex.ofReal_re]
          linarith
        obtain ⟨m, n, hrep⟩ :=
          (IsUpsilon.zero_left_iff hγ hγ2 hU ((Q γ : ℂ) - z) hreflectRe).mp (by rw [IsUpsilon.reflect hγ hγ2 hU z]; exact hz)
        have hright : z = (Q γ + m * (γ / 2) + n * (2 / γ) : ℝ) := by
          calc
            z = (Q γ : ℂ) - ((Q γ : ℂ) - z) := by ring
            _ = (Q γ : ℂ) -
                (-((m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) : ℝ)) := by rw [hrep]
            _ = (Q γ + m * (γ / 2) + n * (2 / γ) : ℝ) := by
              push_cast
              ring
        exact ⟨m, n, Or.inr hright⟩
  · rintro ⟨m, n, hrep | hrep⟩
    · have hleft : z.re ≤ 0 := by
        rw [hrep]
        simp only [Complex.neg_re, Complex.ofReal_re]
        exact neg_nonpos.mpr (by positivity)
      exact (IsUpsilon.zero_left_iff hγ hγ2 hU z hleft).2 ⟨m, n, hrep⟩
    · have hreflectRep : (Q γ : ℂ) - z =
          -((m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) : ℝ) := by
        calc
          (Q γ : ℂ) - z = (Q γ : ℂ) - (Q γ + m * (γ / 2) + n * (2 / γ) : ℝ) := by
            rw [hrep]
          _ = -((m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) : ℝ) := by
            push_cast
            ring
      exact (IsUpsilon.reflect hγ hγ2 hU z).symm.trans ((IsUpsilon.zero_left_iff hγ hγ2 hU ((Q γ : ℂ) - z) (by rw [hreflectRep]; simp only [Complex.neg_re, Complex.ofReal_re]; exact neg_nonpos.mpr (by positivity))).2 ⟨m, n, hreflectRep⟩)

end DOZZ.Proofs

end
