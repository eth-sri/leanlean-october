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

private theorem upsilonB_cast (γ : ℝ) : upsilonB γ = (γ / 2 : ℂ) := by
  exact Complex.ofReal_div γ 2

private noncomputable def upsilonShiftN (γ : ℝ) (n : ℕ) : ℂ :=
  (n : ℂ) * upsilonB γ

private theorem upsilonShiftN_re (γ : ℝ) (n : ℕ) :
    (upsilonShiftN γ n).re = (n : ℝ) * (γ / 2) := by
  simp [upsilonShiftN, upsilonB, Complex.mul_re]

private theorem upsilonShiftN_succ (γ : ℝ) (n : ℕ) :
    upsilonShiftN γ (n + 1) = upsilonShiftN γ n + upsilonB γ := by
  simp [upsilonShiftN, Nat.cast_add]
  ring

private theorem reciprocalGamma_hasDerivAt_zero :
    HasDerivAt (fun z : ℂ => (Complex.Gamma z)⁻¹) 1 0 := by
  have hGamma := Complex.tendsto_self_mul_Gamma_nhds_zero
  have hInv : Tendsto (fun z : ℂ => (z * Complex.Gamma z)⁻¹)
      (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
    simpa using hGamma.inv₀ (by norm_num : (1 : ℂ) ≠ 0)
  have hprod_ne : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z * Complex.Gamma z ≠ 0 :=
    hGamma.eventually (isOpen_ne.mem_nhds (by norm_num : (1 : ℂ) ≠ 0))
  have hRatio :
      (fun z : ℂ => (z * Complex.Gamma z)⁻¹) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun z => z⁻¹ * (Complex.Gamma z)⁻¹) := by
    filter_upwards [hprod_ne] with z hz
    have hz0 : z ≠ 0 := by
      intro h
      subst z
      simp at hz
    have hΓ : Complex.Gamma z ≠ 0 := (mul_ne_zero_iff.mp hz).2
    field_simp [hz0, hΓ]
  have hSlope : Tendsto (fun z : ℂ => z⁻¹ * (Complex.Gamma z)⁻¹)
      (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
    exact (tendsto_congr' hRatio).mp hInv
  have hDiffSlope : Tendsto
      (fun z : ℂ => z⁻¹ • ((Complex.Gamma z)⁻¹ - (Complex.Gamma 0)⁻¹))
      (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
    simpa [Complex.Gamma_zero] using hSlope
  exact (hasDerivAt_iff_tendsto_slope_zero).mpr (by simpa using hDiffSlope)

private theorem differentiableAt_upsilonLeftUnitFactor
    (hγ : 0 < γ) :
    DifferentiableAt ℂ
      (fun z : ℂ => upsilonB γ ^ ((γ : ℂ) * z - 1) *
        Complex.Gamma (1 - upsilonB γ * z)) 0 := by
  have hb : upsilonB γ ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact div_ne_zero hγ.ne' (by norm_num)
  have hpow : DifferentiableAt ℂ
      (fun z : ℂ => upsilonB γ ^ ((γ : ℂ) * z - 1)) 0 := by
    apply DifferentiableAt.const_cpow
    · fun_prop
    · exact Or.inl hb
  have hGammaOne : DifferentiableAt ℂ Complex.Gamma (1 : ℂ) := by
    exact Complex.differentiableAt_Gamma_one
  have harg : DifferentiableAt ℂ (fun z : ℂ => 1 - upsilonB γ * z) 0 := by
    fun_prop
  have hGammaComp : DifferentiableAt ℂ
      (fun z : ℂ => Complex.Gamma (1 - upsilonB γ * z)) 0 := by
    have hGammaAt : DifferentiableAt ℂ Complex.Gamma
        (1 - upsilonB γ * (0 : ℂ)) := by
      simpa using hGammaOne
    exact DifferentiableAt.fun_comp' 0
      (f := fun z : ℂ => 1 - upsilonB γ * z) (g := Complex.Gamma) hGammaAt harg
  exact hpow.mul hGammaComp

private theorem upsilonLeftFactor_hasDerivAt_zero
    (hγ : 0 < γ) : HasDerivAt (upsilonLeftFactor γ) 1 0 := by
  have hb : upsilonB γ ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact div_ne_zero hγ.ne' (by norm_num)
  have hlin : HasDerivAt (fun z : ℂ => upsilonB γ * z) (upsilonB γ) 0 := by
    simpa using (hasDerivAt_const_mul (upsilonB γ) :
      HasDerivAt (fun z : ℂ => upsilonB γ * z) (upsilonB γ) 0)
  have hrecip : HasDerivAt
      (fun z : ℂ => (Complex.Gamma (upsilonB γ * z))⁻¹) (upsilonB γ) 0 := by
    have hRecipAt : HasDerivAt (fun z : ℂ => (Complex.Gamma z)⁻¹) 1
        (upsilonB γ * (0 : ℂ)) := by
      simpa using reciprocalGamma_hasDerivAt_zero
    simpa only [Function.comp_def, one_mul] using
      HasDerivAt.comp (0 : ℂ) hRecipAt hlin
  have hOuterDiff := differentiableAt_upsilonLeftUnitFactor hγ
  have hA := hOuterDiff.hasDerivAt.mul hrecip
  simpa [upsilonLeftFactor, Complex.Gamma_zero, Complex.Gamma_one,
    Complex.cpow_neg, hb] using hA

/-- The derivative at zero is the value one half-period to the right. -/
theorem IsUpsilon.deriv_zero {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hU : IsUpsilon γ U) : deriv U 0 = U (γ / 2) := by
  have hFactor := upsilonLeftFactor_hasDerivAt_zero hγ
  have hFactor0 : upsilonLeftFactor γ 0 = 0 := by
    simp [upsilonLeftFactor, Complex.Gamma_zero]
  have hUshift : DifferentiableAt ℂ (fun z : ℂ => U (z + upsilonB γ)) 0 := by
    exact DifferentiableAt.fun_comp' 0 (f := fun z : ℂ => z + upsilonB γ)
      (g := U) (hU.1 (0 + upsilonB γ)) (by fun_prop)
  have hProd := hFactor.mul hUshift.hasDerivAt
  have hProd' : HasDerivAt
      (upsilonLeftFactor γ * fun z : ℂ => U (z + upsilonB γ))
      (U (upsilonB γ)) 0 := by
    have hFactor0 : upsilonLeftFactor γ 0 = 0 := by
      simp [upsilonLeftFactor, Complex.Gamma_zero]
    simpa [hFactor0] using hProd
  have hLocalEq :
      (fun z : ℂ => U z) =ᶠ[𝓝 (0 : ℂ)]
        (upsilonLeftFactor γ * fun z : ℂ => U (z + upsilonB γ)) := by
    have hOpen : IsOpen {z : ℂ | z.re < 2 / γ} := Complex.isOpen_re_lt (2 / γ)
    have h0 : (0 : ℂ) ∈ {z : ℂ | z.re < 2 / γ} := by
      dsimp
      have hbound : 0 < 2 / γ := by positivity
      simpa using hbound
    filter_upwards [hOpen.mem_nhds h0] with z hz
    have hShift := IsUpsilon.shift_b_reciprocal hγ hγ2 hU z hz
    have hFactorEq : upsilonLeftFactor γ z * U (z + upsilonB γ) = U z := by
      change ((upsilonB γ) ^ ((γ : ℂ) * z - 1) *
        Complex.Gamma (1 - upsilonB γ * z) *
        (Complex.Gamma (upsilonB γ * z))⁻¹ * U (z + upsilonB γ)) = U z
      rw [upsilonB_cast]
      simpa [mul_assoc] using hShift
    change U z = (upsilonLeftFactor γ * fun w : ℂ => U (w + upsilonB γ)) z
    rw [Pi.mul_apply]
    exact hFactorEq.symm
  have hUderiv := hProd'.congr_of_eventuallyEq hLocalEq
  calc
    deriv U 0 = U (upsilonB γ) := hUderiv.deriv
    _ = U (γ / 2) := by rw [upsilonB_cast]

private theorem IsUpsilon.left_product {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
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
      have hz0 : z.re < 2 / γ := by
        simpa [upsilonShiftN] using hstage 0 (by simp)
      have hShift := IsUpsilon.shift_b_reciprocal hγ hγ2 hU z hz0
      have hfirst : upsilonLeftFactor γ z * U (z + upsilonB γ) = U z := by
        change ((upsilonB γ) ^ ((γ : ℂ) * z - 1) *
          Complex.Gamma (1 - upsilonB γ * z) *
          (Complex.Gamma (upsilonB γ * z))⁻¹ * U (z + upsilonB γ)) = U z
        rw [upsilonB_cast]
        simpa [mul_assoc] using hShift
      have hstage' : ∀ j ∈ Finset.range N,
          ((z + upsilonB γ) + upsilonShiftN γ j).re < 2 / γ := by
        intro j hj
        have hj' : j + 1 ∈ Finset.range (N + 1) := by
          apply Finset.mem_range.mpr
          exact Nat.succ_lt_succ (Finset.mem_range.mp hj)
        have h := hstage (j + 1) hj'
        have harg : z + upsilonB γ + upsilonShiftN γ j =
            z + upsilonShiftN γ (j + 1) := by
          rw [upsilonShiftN_succ]
          ring
        rw [harg]
        exact h
      have htail := ih (z + upsilonB γ) hstage'
      have hend : z + upsilonB γ + upsilonShiftN γ N =
          z + upsilonShiftN γ (N + 1) := by
        rw [upsilonShiftN_succ]
        ring
      have hprod :
          (∏ j ∈ Finset.range N,
            upsilonLeftFactor γ ((z + upsilonB γ) + upsilonShiftN γ j)) =
          ∏ j ∈ Finset.range N,
            upsilonLeftFactor γ (z + upsilonShiftN γ (j + 1)) := by
        apply Finset.prod_congr rfl
        intro j hj
        have harg : z + upsilonB γ + upsilonShiftN γ j =
            z + upsilonShiftN γ (j + 1) := by
          rw [upsilonShiftN_succ]
          ring
        rw [harg]
      rw [← hfirst, htail, hend, hprod, Finset.prod_range_succ']
      simp only [upsilonShiftN, Nat.cast_zero, zero_mul, add_zero]
      ring

private theorem exists_upsilonShiftN_between_zero_and_B (hγ : 0 < γ) (z : ℂ)
    (hz : z.re ≤ 0) :
    ∃ N : ℕ, 0 < (z + upsilonShiftN γ N).re ∧
      (z + upsilonShiftN γ N).re ≤ γ / 2 := by
  have hb : 0 < γ / 2 := by positivity
  let y : ℝ := -z.re / (γ / 2)
  have hy : 0 ≤ y := by
    dsimp [y]
    exact div_nonneg (neg_nonneg.mpr hz) hb.le
  let N : ℕ := Nat.floor y + 1
  have hNcast : (N : ℝ) = (Nat.floor y : ℝ) + 1 := by simp [N]
  have hylt : y < (N : ℝ) := by
    rw [hNcast]
    exact Nat.lt_floor_add_one y
  have hNle : (N : ℝ) ≤ y + 1 := by
    rw [hNcast]
    have hfloor := Nat.floor_le hy
    linarith
  have hzy : z.re = -(y * (γ / 2)) := by
    dsimp [y]
    field_simp [ne_of_gt hb]
  have hlow : 0 < z.re + (N : ℝ) * (γ / 2) := by
    have hmul := mul_lt_mul_of_pos_right hylt hb
    rw [hzy]
    linarith only [hmul]
  have hupp : z.re + (N : ℝ) * (γ / 2) ≤ γ / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hNle hb.le
    rw [hzy]
    linarith only [hmul]
  refine ⟨N, ?_, ?_⟩
  · rw [Complex.add_re, upsilonShiftN_re]
    simpa using hlow
  · rw [Complex.add_re, upsilonShiftN_re]
    exact hupp

private theorem upsilon_arg_eq_lattice_iff (hγ : 0 < γ) (j n : ℕ) (z : ℂ) :
    upsilonB γ * (z + upsilonShiftN γ j) = -(n : ℂ) ↔
      z = -((j : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) : ℝ) := by
  have hb : upsilonB γ ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact (div_pos hγ (by norm_num)).ne'
  have hshiftCast : upsilonShiftN γ j =
      (((j : ℝ) * (γ / 2) : ℝ) : ℂ) := by
    change ((j : ℝ) : ℂ) * ((γ / 2 : ℝ) : ℂ) = _
    exact (Complex.ofReal_mul _ _).symm
  have hdivCast : (n : ℂ) / upsilonB γ =
      (((n : ℝ) / (γ / 2) : ℝ) : ℂ) := by
    change ((n : ℝ) : ℂ) / ((γ / 2 : ℝ) : ℂ) = _
    exact (Complex.ofReal_div _ _).symm
  have hreal : (n : ℝ) / (γ / 2) = (n : ℝ) * (2 / γ) := by
    field_simp [hγ.ne']
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
    rw [neg_div, hdivCast, hshiftCast, hreal] at hsolve
    calc
      z = -(((n : ℝ) * (2 / γ) : ℝ) : ℂ) -
          (((j : ℝ) * (γ / 2) : ℝ) : ℂ) := hsolve
      _ = -((j : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) : ℝ) := by
        push_cast
        ring
  · intro h
    rw [h, hshiftCast]
    rw [upsilonB_cast]
    push_cast
    field_simp [hγ.ne']
    ring

private theorem upsilonLeftFactor_eq_zero_iff (hγ : 0 < γ) {z : ℂ}
    (hz : z.re ≤ 0) :
    upsilonLeftFactor γ z = 0 ↔
      ∃ n : ℕ, upsilonB γ * z = -(n : ℂ) := by
  have hbR : 0 < γ / 2 := by positivity
  have hb : upsilonB γ ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact hbR.ne'
  have hbzre : (upsilonB γ * z).re = (γ / 2) * z.re := by
    simp [upsilonB, Complex.mul_re]
  have hGamma1 : Complex.Gamma (1 - upsilonB γ * z) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by
      rw [Complex.sub_re, Complex.one_re, hbzre]
      have hmul : (γ / 2) * z.re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hbR.le hz
      linarith)
  have hpow : upsilonB γ ^ ((γ : ℂ) * z - 1) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hb)
  have houter :
      upsilonB γ ^ ((γ : ℂ) * z - 1) * Complex.Gamma (1 - upsilonB γ * z) ≠ 0 :=
    mul_ne_zero hpow hGamma1
  change (upsilonB γ ^ ((γ : ℂ) * z - 1) *
      Complex.Gamma (1 - upsilonB γ * z)) *
      (Complex.Gamma (upsilonB γ * z))⁻¹ = 0 ↔ _
  rw [mul_eq_zero]
  constructor
  · rintro (hbad | hrecip)
    · exact (houter hbad).elim
    · rw [inv_eq_zero] at hrecip
      have hzero := (Complex.Gamma_eq_zero_iff (upsilonB γ * z)).mp hrecip
      exact hzero
  · rintro ⟨n, harg⟩
    right
    rw [inv_eq_zero, harg, Complex.Gamma_neg_nat_eq_zero]

private theorem IsUpsilon.zero_left_iff {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hU : IsUpsilon γ U) (z : ℂ) (hz : z.re ≤ 0) :
    U z = 0 ↔ ∃ m n : ℕ, z = -((m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) : ℝ) := by
  obtain ⟨N, hEnd0, hEndB⟩ := exists_upsilonShiftN_between_zero_and_B hγ z hz
  have hbpos : 0 < γ / 2 := by positivity
  have hEndQ : (z + upsilonShiftN γ N).re < Q γ := by
    have hbQ : γ / 2 < Q γ := by
      unfold Q
      have hpos : 0 < 2 / γ := by positivity
      linarith
    exact hEndB.trans_lt hbQ
  have hStageLe : ∀ j ∈ Finset.range N,
      (z + upsilonShiftN γ j).re ≤ 0 := by
    intro j hj
    have hjN : j + 1 ≤ N := Nat.succ_le_iff.mpr (Finset.mem_range.mp hj)
    have hmul := mul_le_mul_of_nonneg_right
      (show (j : ℝ) + 1 ≤ (N : ℝ) by exact_mod_cast hjN)
      (show 0 ≤ γ / 2 by positivity)
    rw [add_mul] at hmul
    have hstep : (z + upsilonShiftN γ j).re + γ / 2 ≤
        (z + upsilonShiftN γ N).re := by
      rw [Complex.add_re, Complex.add_re, upsilonShiftN_re, upsilonShiftN_re]
      linarith
    linarith [hstep, hEndB]
  have hStage : ∀ j ∈ Finset.range N,
      (z + upsilonShiftN γ j).re < 2 / γ := by
    intro j hj
    have hjle := hStageLe j hj
    have hpos : 0 < 2 / γ := by positivity
    linarith
  have hformula := IsUpsilon.left_product hγ hγ2 hU N z hStage
  have hEndNe : U (z + upsilonShiftN γ N) ≠ 0 := by
    rw [hU.2 _ hEnd0 hEndQ]
    exact Complex.exp_ne_zero _
  have hUzero : U z = 0 ↔
      (∏ j ∈ Finset.range N,
        upsilonLeftFactor γ (z + upsilonShiftN γ j)) = 0 := by
    rw [hformula, mul_eq_zero]
    simp [hEndNe]
  constructor
  · intro hzero
    have hprod := hUzero.mp hzero
    obtain ⟨j, hj, hfactor⟩ := Finset.prod_eq_zero_iff.mp hprod
    have hzj := hStageLe j hj
    obtain ⟨n, harg⟩ := (upsilonLeftFactor_eq_zero_iff hγ hzj).mp hfactor
    have hrep := (upsilon_arg_eq_lattice_iff hγ j n z).mp harg
    exact ⟨j, n, hrep⟩
  · rintro ⟨m, n, hrep⟩
    have hy : 0 ≤ -z.re / (γ / 2) := by
      exact div_nonneg (neg_nonneg.mpr hz) (by positivity)
    let y : ℝ := -z.re / (γ / 2)
    have hmle : (m : ℝ) ≤ y := by
      have hrepRe := congrArg Complex.re hrep
      have hb := hbpos
      have hrepRe' : z.re = -((m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ)) := by
        simpa using hrepRe
      dsimp [y]
      apply (le_div_iff₀ hb).2
      rw [hrepRe']
      have hn : 0 ≤ (n : ℝ) * (2 / γ) := by positivity
      linarith
    have hmN : m < N := by
      have hzy : z.re = -(y * (γ / 2)) := by
        dsimp [y]
        field_simp [ne_of_gt hbpos]
      have hEnd0' : 0 < z.re + (N : ℝ) * (γ / 2) := by
        have hEnd0'' := hEnd0
        rw [Complex.add_re, upsilonShiftN_re] at hEnd0''
        exact hEnd0''
      rw [hzy] at hEnd0'
      have hyltNmul : y * (γ / 2) < (N : ℝ) * (γ / 2) := by
        linarith only [hEnd0']
      have hyltN : y < (N : ℝ) := lt_of_mul_lt_mul_right hyltNmul hbpos.le
      exact_mod_cast lt_of_le_of_lt hmle hyltN
    have hzj : (z + upsilonShiftN γ m).re ≤ 0 := hStageLe m (by
      apply Finset.mem_range.mpr
      exact hmN)
    have harg := (upsilon_arg_eq_lattice_iff hγ m n z).2 hrep
    have hfactor := (upsilonLeftFactor_eq_zero_iff hγ hzj).2 ⟨n, harg⟩
    have hprod :
        (∏ j ∈ Finset.range N,
          upsilonLeftFactor γ (z + upsilonShiftN γ j)) = 0 :=
      Finset.prod_eq_zero_iff.mpr ⟨m, Finset.mem_range.mpr hmN, hfactor⟩
    exact hUzero.mpr hprod

/-- The zeros are the two reflected negative reciprocal-Gamma lattices. -/
theorem IsUpsilon.eq_zero_iff {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hU : IsUpsilon γ U) (z : ℂ) :
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
        have hexpZero : Complex.exp (upsilonLog γ z) = 0 := by
          simpa [hz] using hzexp.symm
        exact (Complex.exp_ne_zero _ hexpZero).elim
      · have hreflectRe : ((Q γ : ℂ) - z).re ≤ 0 := by
          rw [Complex.sub_re, Complex.ofReal_re]
          linarith
        have hreflect : U ((Q γ : ℂ) - z) = 0 := by
          rw [IsUpsilon.reflect hγ hγ2 hU z]
          exact hz
        obtain ⟨m, n, hrep⟩ :=
          (IsUpsilon.zero_left_iff hγ hγ2 hU ((Q γ : ℂ) - z) hreflectRe).mp hreflect
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
        have hn : 0 ≤ (m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) := by positivity
        exact neg_nonpos.mpr hn
      exact (IsUpsilon.zero_left_iff hγ hγ2 hU z hleft).2 ⟨m, n, hrep⟩
    · have hreflectRep : (Q γ : ℂ) - z =
          -((m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) : ℝ) := by
        calc
          (Q γ : ℂ) - z = (Q γ : ℂ) - (Q γ + m * (γ / 2) + n * (2 / γ) : ℝ) := by
            rw [hrep]
          _ = -((m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) : ℝ) := by
            push_cast
            ring
      have hreflectRe : ((Q γ : ℂ) - z).re ≤ 0 := by
        rw [hreflectRep]
        simp only [Complex.neg_re, Complex.ofReal_re]
        have hn : 0 ≤ (m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) := by positivity
        exact neg_nonpos.mpr hn
      have hleftzero := (IsUpsilon.zero_left_iff hγ hγ2 hU
        ((Q γ : ℂ) - z) hreflectRe).2
        ⟨m, n, hreflectRep⟩
      exact (IsUpsilon.reflect hγ hγ2 hU z).symm.trans hleftzero

end DOZZ.Proofs

end
