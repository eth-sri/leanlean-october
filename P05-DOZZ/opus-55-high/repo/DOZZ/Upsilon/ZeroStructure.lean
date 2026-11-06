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

private theorem upsilonB_cast (γ : ℝ) : upsilonB γ = (γ / 2 : ℂ) := Complex.ofReal_div γ 2

private noncomputable def upsilonShiftN (γ : ℝ) (n : ℕ) : ℂ :=
  (n : ℂ) * upsilonB γ
section
variable (γ : ℝ) (n : ℕ)

private theorem upsilonShiftN_re :
    (upsilonShiftN γ n).re = (n : ℝ) * (γ / 2) := by
  simp [upsilonShiftN, upsilonB, Complex.mul_re]

private theorem upsilonShiftN_succ :
    upsilonShiftN γ (n + 1) = upsilonShiftN γ n + upsilonB γ := by
  simp [upsilonShiftN, Nat.cast_add]
  ring

end

private theorem reciprocalGamma_hasDerivAt_zero :
    HasDerivAt (fun z : ℂ => (Complex.Gamma z)⁻¹) 1 0 := by
  have hGamma := Complex.tendsto_self_mul_Gamma_nhds_zero
  have hInv : Tendsto (fun z => (z * Complex.Gamma z)⁻¹)
      (𝓝[≠] 0) (𝓝 1) := by
    simpa using hGamma.inv₀ (by norm_num)
  have hprod_ne : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z * Complex.Gamma z ≠ 0 :=
    hGamma.eventually (isOpen_ne.mem_nhds (by norm_num))
  have hRatio :
      (fun z => (z * Complex.Gamma z)⁻¹) =ᶠ[𝓝[≠] 0]
        (fun z => z⁻¹ * (Complex.Gamma z)⁻¹) := by
    filter_upwards [hprod_ne] with z hz
    ring
  have hSlope : Tendsto (fun z => z⁻¹ * (Complex.Gamma z)⁻¹)
      (𝓝[≠] 0) (𝓝 1) := (tendsto_congr' hRatio).mp hInv
  have hDiffSlope : Tendsto
      (fun z => z⁻¹ • ((Complex.Gamma z)⁻¹ - (Complex.Gamma 0)⁻¹))
      (𝓝[≠] 0) (𝓝 1) := by
    simp_all
  exact (hasDerivAt_iff_tendsto_slope_zero).mpr (by simp_all)
section
variable (hγ : 0 < γ)
include hγ

private theorem differentiableAt_upsilonLeftUnitFactor
    :
    DifferentiableAt ℂ
      (fun z : ℂ => upsilonB γ ^ ((γ : ℂ) * z - 1) *
        Complex.Gamma (1 - upsilonB γ * z)) 0 := by
  have hb : upsilonB γ ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    positivity
  have hpow : DifferentiableAt ℂ
      (fun z : ℂ => upsilonB γ ^ (γ * z - 1)) 0 := by
    apply DifferentiableAt.const_cpow
    · fun_prop
    simp
  have hGammaOne : DifferentiableAt ℂ Complex.Gamma 1 := Complex.differentiableAt_Gamma_one
  have harg : DifferentiableAt ℂ (fun z : ℂ => 1 - upsilonB γ * z) 0 := by
    fun_prop
  have hGammaComp : DifferentiableAt ℂ
      (fun z => Complex.Gamma (1 - upsilonB γ * z)) 0 := by
    have hGammaAt : DifferentiableAt ℂ Complex.Gamma
        (1 - upsilonB γ * 0) := by
      simp_all
    fun_prop
  simp_all

private theorem upsilonLeftFactor_hasDerivAt_zero
    : HasDerivAt (upsilonLeftFactor γ) 1 0 := by
  have hb : upsilonB γ ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    positivity
  have hlin : HasDerivAt (fun z => upsilonB γ * z) (upsilonB γ) 0 := by
    simpa using (hasDerivAt_const_mul (upsilonB γ) :
      HasDerivAt (fun z => upsilonB γ * z) (upsilonB γ) 0)
  have hrecip : HasDerivAt
      (fun z => (Complex.Gamma (upsilonB γ * z))⁻¹) (upsilonB γ) 0 := by
    have hRecipAt : HasDerivAt (fun z => (Complex.Gamma z)⁻¹) 1
        (upsilonB γ * 0) := by
      simpa using reciprocalGamma_hasDerivAt_zero
    simpa only [Function.comp_def, one_mul] using
      HasDerivAt.comp 0 hRecipAt hlin
  simpa [upsilonLeftFactor, Complex.Gamma_zero, Complex.Gamma_one,
    Complex.cpow_neg, hb] using ((differentiableAt_upsilonLeftUnitFactor hγ).hasDerivAt.mul hrecip)

end
section
variable {U : ℂ → ℂ}
section
variable (hγ : 0 < γ) (hγ2 : γ < 2) (hU : IsUpsilon γ U)
include hγ hγ2 hU

/-- The derivative at zero is the value one half-period to the right. -/
theorem IsUpsilon.deriv_zero : deriv U 0 = U (γ / 2) := by
  have hFactor0 : upsilonLeftFactor γ 0 = 0 := by
    simp [upsilonLeftFactor, Complex.Gamma_zero]
  have hUshift : DifferentiableAt ℂ (fun z : ℂ => U (z + upsilonB γ)) 0 := by
    exact DifferentiableAt.fun_comp' 0 (f := fun z : ℂ => z + upsilonB γ)
      (g := U) (hU.1 _) (by fun_prop)
  have hProd := (upsilonLeftFactor_hasDerivAt_zero hγ).mul hUshift.hasDerivAt
  have hProd' : HasDerivAt
      (upsilonLeftFactor γ * fun z : ℂ => U (z + upsilonB γ))
      (U (upsilonB γ)) 0 := by
    simp_all
  have hLocalEq :
      (fun z : ℂ => U z) =ᶠ[𝓝 (0 : ℂ)]
        (upsilonLeftFactor γ * fun z : ℂ => U (z + upsilonB γ)) := by
    have hOpen : IsOpen {z : ℂ | z.re < 2 / γ} := Complex.isOpen_re_lt _
    have h0 : (0 : ℂ) ∈ {z : ℂ | z.re < 2 / γ} := by
      simp_all
    filter_upwards [hOpen.mem_nhds h0] with z hz
    have hShift := IsUpsilon.shift_b_reciprocal hγ hγ2 hU z hz
    have hFactorEq : upsilonLeftFactor γ z * U (z + upsilonB γ) = U z := by
      change ((upsilonB γ) ^ ((γ : ℂ) * z - 1) *
        Complex.Gamma _ *
        (Complex.Gamma _)⁻¹ * U _) = U z
      rw [upsilonB_cast]
      simp_all
    simp_all
  calc
    deriv U 0 = U (upsilonB γ) := (hProd'.congr_of_eventuallyEq hLocalEq).deriv
    _ = U _ := by norm_cast

private theorem IsUpsilon.left_product :
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
        change ((upsilonB γ) ^ (γ * z - 1) *
          Complex.Gamma _ *
          (Complex.Gamma _)⁻¹ * U _) = U z
        rw [upsilonB_cast]
        simp_all
      have hstage' : ∀ j ∈ Finset.range N,
          ((z + upsilonB γ) + upsilonShiftN γ j).re < 2 / γ := by
        intro j hj
        have hj' : j + 1 ∈ Finset.range (N + 1) := by
          simp_all
        have h := hstage _ hj'
        have harg : z + upsilonB γ + upsilonShiftN γ j =
            z + upsilonShiftN γ (j + 1) := by
          rw [upsilonShiftN_succ]
          ring
        rwa [harg]
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
      rw [← hfirst, (ih _ hstage'), hend, hprod, Finset.prod_range_succ']
      simp only [upsilonShiftN, Nat.cast_zero, zero_mul, add_zero]
      ring

end

end
section
variable (hγ : 0 < γ)
include hγ

private theorem exists_upsilonShiftN_between_zero_and_B (z : ℂ)
    (hz : z.re ≤ 0) :
    ∃ N : ℕ, 0 < (z + upsilonShiftN γ N).re ∧
      (z + upsilonShiftN γ N).re ≤ γ / 2 := by
  have hb : 0 < γ / 2 := by positivity
  let y := -z.re / (γ / 2)
  have hy : 0 ≤ y := by
    bound
  let N := Nat.floor y + 1
  have hNcast : N = (Nat.floor y : ℝ) + 1 := by aesop
  have hylt : y < (N : ℝ) := by
    rw [hNcast]
    bound
  have hNle : (N : ℝ) ≤ y + 1 := by
    have hfloor := Nat.floor_le hy
    linarith
  have hzy : z.re = -(y * (γ / 2)) := by
    grind
  have hlow : 0 < z.re + N * (γ / 2) := by
    simp_all
  have hupp : z.re + N * (γ / 2) ≤ γ / 2 := by
    nlinarith
  refine ⟨N, ?_, ?_⟩
  · rw [Complex.add_re, upsilonShiftN_re]
    assumption
  · rw [Complex.add_re, upsilonShiftN_re]
    exact hupp

private theorem upsilon_arg_eq_lattice_iff (j n : ℕ) (z : ℂ) :
    upsilonB γ * (z + upsilonShiftN γ j) = -(n : ℂ) ↔
      z = -((j : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) : ℝ) := by
  have hb : upsilonB γ ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    positivity
  have hshiftCast : upsilonShiftN γ j =
      (((j : ℝ) * (γ / 2) : ℝ) : ℂ) := by
    change ((j : ℝ) : ℂ) * ((γ / 2 : ℝ) : ℂ) = _
    simp
  have hdivCast : (n : ℂ) / upsilonB γ =
      (((n : ℝ) / (γ / 2) : ℝ) : ℂ) := by
    change ((n : ℝ) : ℂ) / ((γ / 2 : ℝ) : ℂ) = _
    simp
  have hreal : (n : ℝ) / (γ / 2) = (n : ℝ) * (2 / γ) := by
    ring
  constructor
  · intro harg
    have hmul : upsilonB γ * z = -(n : ℂ) - upsilonB γ * upsilonShiftN γ j := by
      grind
    have hsolve : z = -(n : ℂ) / upsilonB γ - upsilonShiftN γ j := by
      grind
    rw [neg_div, hdivCast, hshiftCast, hreal] at hsolve
    aesop
  · intro h
    rw [h, hshiftCast]
    rw [upsilonB_cast]
    push_cast
    field_simp [hγ.ne']
    ring

private theorem upsilonLeftFactor_eq_zero_iff {z : ℂ}
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
      nlinarith)
  have hpow : upsilonB γ ^ ((γ : ℂ) * z - 1) ≠ 0 :=
    by simp_all
  have houter :=
    mul_ne_zero hpow hGamma1
  change (upsilonB γ ^ (γ * z - 1) *
      Complex.Gamma _) *
      (Complex.Gamma _)⁻¹ = 0 ↔ _
  grind

end
section
variable {U : ℂ → ℂ}
section
variable (hγ : 0 < γ) (hγ2 : γ < 2) (hU : IsUpsilon γ U) (z : ℂ)
include hγ hγ2 hU

private theorem IsUpsilon.zero_left_iff (hz : z.re ≤ 0) :
    U z = 0 ↔ ∃ m n : ℕ, z = -((m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) : ℝ) := by
  obtain ⟨N, hEnd0, hEndB⟩ := exists_upsilonShiftN_between_zero_and_B hγ z hz
  have hbpos : 0 < γ / 2 := by positivity
  have hEndQ : (z + upsilonShiftN γ N).re < Q γ := by
    have hbQ : γ / 2 < Q γ := by
      unfold Q
      simp_all
    linarith
  have hStageLe : ∀ j ∈ Finset.range N,
      (z + upsilonShiftN γ j).re ≤ 0 := by
    intro j hj
    have hmul := mul_le_mul_of_nonneg_right
      (show j + 1 ≤ (N : ℝ) by exact_mod_cast (Nat.succ_le_iff.mpr (Finset.mem_range.mp hj)))
      (show 0 ≤ γ / 2 by positivity)
    rw [add_mul] at hmul
    have hstep : (z + upsilonShiftN γ j).re + γ / 2 ≤
        (z + upsilonShiftN γ N).re := by
      rw [Complex.add_re, Complex.add_re, upsilonShiftN_re, upsilonShiftN_re]
      linarith
    linarith
  have hStage : ∀ j ∈ Finset.range N,
      (z + upsilonShiftN γ j).re < 2 / γ := by
    intro j hj
    have hjle := hStageLe j hj
    have hpos : 0 < 2 / γ := by positivity
    linarith
  have hEndNe : U (z + upsilonShiftN γ N) ≠ 0 := by
    rw [hU.2 _ hEnd0 hEndQ]
    exact Complex.exp_ne_zero _
  have hUzero : U z = 0 ↔
      (∏ j ∈ Finset.range N,
        upsilonLeftFactor γ (z + upsilonShiftN γ j)) = 0 := by
    rw [(IsUpsilon.left_product hγ hγ2 hU N z hStage), mul_eq_zero]
    simp [hEndNe]
  constructor
  · intro hzero
    have hprod := hUzero.mp hzero
    obtain ⟨j, hj, hfactor⟩ := Finset.prod_eq_zero_iff.mp hprod
    have hzj := hStageLe j hj
    obtain ⟨n, harg⟩ := (upsilonLeftFactor_eq_zero_iff hγ hzj).mp hfactor
    exact ⟨j, n, ((upsilon_arg_eq_lattice_iff hγ j n z).mp harg)⟩
  · rintro ⟨m, n, hrep⟩
    have hy : 0 ≤ -z.re / (γ / 2) := by bound
    let y := -z.re / (γ / 2)
    have hmle : m ≤ y := by
      have hrepRe' : z.re = -(m * (γ / 2) + n * (2 / γ)) := by
        simpa using (congrArg Complex.re hrep)
      dsimp [y]
      apply (le_div_iff₀ hbpos).2
      rw [hrepRe']
      have hn : 0 ≤ n * (2 / γ) := by positivity
      linarith
    have hmN : m < N := by
      have hzy : z.re = -(y * (γ / 2)) := by
        dsimp [y]
        field_simp [ne_of_gt hbpos]
      have hEnd0' : 0 < z.re + N * (γ / 2) := by
        have hEnd0'' := hEnd0
        rwa [Complex.add_re, upsilonShiftN_re] at hEnd0''
      rw [hzy] at hEnd0'
      have hyltNmul : y * (γ / 2) < N * (γ / 2) := by
        linarith only [hEnd0']
      exact_mod_cast lt_of_le_of_lt hmle (lt_of_mul_lt_mul_right hyltNmul hbpos.le)
    have hzj := hStageLe m (by
      apply Finset.mem_range.mpr
      exact hmN)
    have hprod :
        (∏ j ∈ Finset.range N,
          upsilonLeftFactor γ (z + upsilonShiftN γ j)) = 0 :=
      Finset.prod_eq_zero_iff.mpr ⟨m, Finset.mem_range.mpr hmN, ((upsilonLeftFactor_eq_zero_iff hγ hzj).2 ⟨n, ((upsilon_arg_eq_lattice_iff hγ m n z).2 hrep)⟩)⟩
    exact hUzero.mpr hprod

/-- The zeros are the two reflected negative reciprocal-Gamma lattices. -/
theorem IsUpsilon.eq_zero_iff :
    U z = 0 ↔ ∃ m n : ℕ, z = -(m * (γ / 2) + n * (2 / γ) : ℝ) ∨
      z = (Q γ + m * (γ / 2) + n * (2 / γ) : ℝ) := by
  constructor
  · intro hz
    by_cases hleft : z.re ≤ 0
    · obtain ⟨m, n, hrep⟩ :=
        (IsUpsilon.zero_left_iff hγ hγ2 hU z hleft).mp hz
      tauto
    · have hzpos : 0 < z.re := lt_of_not_ge hleft
      by_cases hmid : z.re < Q γ
      · have hzexp := hU.2 z hzpos hmid
        simp_all
      · have hreflectRe : ((Q γ : ℂ) - z).re ≤ 0 := by
          simp_all
        have hreflect : U ((Q γ : ℂ) - z) = 0 := by
          rw [IsUpsilon.reflect hγ hγ2 hU z]
          exact hz
        obtain ⟨m, n, hrep⟩ :=
          (IsUpsilon.zero_left_iff hγ hγ2 hU ((Q γ : ℂ) - z) hreflectRe).mp hreflect
        have hright : z = (Q γ + m * (γ / 2) + n * (2 / γ) : ℝ) := by
          calc
            z = (Q γ : ℂ) - ((Q γ : ℂ) - z) := by ring
            _ = (Q γ : ℂ) -
                (-((m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) : ℝ)) := by simp_all
            _ = (Q γ + m * (γ / 2) + n * (2 / γ) : ℝ) := by
              push_cast
              ring
        exact ⟨m, n, Or.inr hright⟩
  · rintro ⟨m, n, hrep | hrep⟩
    · have hleft : z.re ≤ 0 := by
        rw [hrep]
        simp
        have hn : 0 ≤ (m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) := by positivity
        linarith
      exact (IsUpsilon.zero_left_iff hγ hγ2 hU z hleft).2 ⟨m, n, hrep⟩
    · have hreflectRep : (Q γ : ℂ) - z =
          -((m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) : ℝ) := by
        calc
          (Q γ : ℂ) - z = (Q γ : ℂ) - (Q γ + m * (γ / 2) + n * (2 / γ) : ℝ) := by
            simp_all
          _ = -((m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) : ℝ) := by
            push_cast
            ring
      have hreflectRe : ((Q γ : ℂ) - z).re ≤ 0 := by
        rw [hreflectRep]
        simp
        have hn : 0 ≤ (m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) := by positivity
        linarith
      have hleftzero := (IsUpsilon.zero_left_iff hγ hγ2 hU
        ((Q γ : ℂ) - z) hreflectRe).2
        ⟨m, n, hreflectRep⟩
      exact (IsUpsilon.reflect hγ hγ2 hU z).symm.trans hleftzero

end

end

end DOZZ.Proofs

end
