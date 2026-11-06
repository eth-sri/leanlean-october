/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.CircleTilt
public import DOZZ.FourPoint.Reflected.MassFiniteness
public import DOZZ.FourPoint.TaylorFixedDisk
public import DOZZ.FourPoint.RootedPairMoments
public import DOZZ.GMC.SharpMoments.SeibergWeight
import Mathlib.Tactic
/-! # The literal retained-region charge shift under a circle tilt -/
@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The retained Coulomb mass with an arbitrary moving charge. -/
noncomputable abbrev retainedCoulombMass (γ β α₁ α₂ α₃ : ℝ) (μ : Measure ℂ)
    (z : ℂ) (ξ : ℝ) : ℝ≥0∞ :=
  coulombMass γ (μ.restrict {x : ℂ | ‖z‖ ^ (1 - ξ) ≤ ‖x‖})
    ![β, α₁, α₂] ![z, 0, 1] α₃

/-- Restricting a measurable weight gives a measurable functional of the measure. -/
theorem retainedCoulombMass_measurable (γ β α₁ α₂ α₃ ξ : ℝ) (z : ℂ) :
    Measurable (fun μ : Measure ℂ => retainedCoulombMass γ β α₁ α₂ α₃ μ z ξ) := by
  let D : Set ℂ := {x | ‖z‖ ^ (1 - ξ) ≤ ‖x‖}
  have hD : MeasurableSet D := (isClosed_le continuous_const continuous_norm).measurableSet
  have hm := Measure.measurable_lintegral
    ((measurable_coulombWeight γ ![β, α₁, α₂] ![z, 0, 1] α₃).indicator hD)
  convert hm using 1
  funext μ
  rw [retainedCoulombMass, coulombMass_eq_lintegral_coulombWeight, lintegral_indicator hD]

/-- Outside the tilting circle, its exponential density is the exact zero-root ratio power. -/
theorem coulomb_circle_density_outside (γ a m : ℝ) (x : ℂ)
    (hx : 0 < ‖x‖) (hm : Real.exp (-m) ≤ ‖x‖) :
    Real.exp (γ * a * (Real.log (normPlus x) - Real.log (max (Real.exp (-m)) ‖x‖))) =
      (normPlus x / ‖x‖) ^ (γ * a) := by
  have hp : 0 < normPlus x := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [max_eq_right hm, Real.rpow_def_of_pos (div_pos hp hx), Real.log_div hp.ne' hx.ne']
  congr 1
  ring

/-- The density changes the first ordinary charge and retains the moving degenerate root. -/
theorem retained_coulombWeight_charge_shift (γ β a α₁ α₂ α₃ : ℝ) (z x : ℂ)
    (hx : x ≠ 0) :
    ENNReal.ofReal ((normPlus x / ‖x‖) ^ (γ * a)) *
      coulombWeight γ ![β, α₁, α₂] ![z, 0, 1] α₃ x =
        coulombWeight γ ![β, α₁ + a, α₂] ![z, 0, 1] α₃ x := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hp : 0 < normPlus x := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hd : 0 < normPlus x / ‖x‖ := div_pos hp hn
  simp only [coulombWeight, Fin.prod_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.prod_univ_zero, mul_one, sub_zero]
  rw [coulombWeight_rpow_ofReal hd, coulombWeight_rpow_ofReal hd]
  have he : γ * (α₁ + a) = γ * a + γ * α₁ := by ring
  rw [he, Real.rpow_add hd, ENNReal.ofReal_mul (Real.rpow_pos_of_pos hd _).le]
  ring

/-- Circle tilting of the literal retained mass is exactly the charge shift whenever the
retained region lies outside that circle. No atom assumptions on the underlying measure enter. -/
theorem retained_coulombMass_circle_density_shift (γ β a m α₁ α₂ α₃ ξ : ℝ)
    (μ : Measure ℂ) (z : ℂ) (hr : 0 < ‖z‖ ^ (1 - ξ))
    (hm : Real.exp (-m) ≤ ‖z‖ ^ (1 - ξ)) :
    retainedCoulombMass γ β α₁ α₂ α₃
      (μ.withDensity (fun x : ℂ => ENNReal.ofReal
        (Real.exp (γ * a * (Real.log (normPlus x) -
          Real.log (max (Real.exp (-m)) ‖x‖)))))) z ξ =
      retainedCoulombMass γ β (α₁ + a) α₂ α₃ μ z ξ := by
  let D : Set ℂ := {x | ‖z‖ ^ (1 - ξ) ≤ ‖x‖}
  have hD : MeasurableSet D := (isClosed_le continuous_const continuous_norm).measurableSet
  have hd : Measurable (fun x : ℂ => ENNReal.ofReal
      (Real.exp (γ * a * (Real.log (normPlus x) -
        Real.log (max (Real.exp (-m)) ‖x‖))))) := by
    unfold normPlus
    fun_prop
  unfold retainedCoulombMass
  rw [restrict_withDensity hD,
    coulombMass_eq_lintegral_coulombWeight,
    lintegral_withDensity_eq_lintegral_mul _ hd (measurable_coulombWeight _ _ _ _),
    coulombMass_eq_lintegral_coulombWeight]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hD] with x hx
  have hn : 0 < ‖x‖ := hr.trans_le hx
  dsimp only [Pi.mul_apply]
  rw [coulomb_circle_density_outside γ a m x hn (hm.trans hx)]
  exact retained_coulombWeight_charge_shift γ β a α₁ α₂ α₃ z x
    (norm_pos_iff.mp hn)


/-- Uniform inverse moments of the literal retained mass, at every nonnegative inverse order. -/
theorem retained_coulombMass_inverse_moment_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (β α₁ α₂ α₃ q : ℝ) (hq : 0 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (ξ : ℝ), ‖z‖ ≤ 1 → ‖z‖ ^ (1 - ξ) ≤ 1 →
      (∫⁻ ω, retainedCoulombMass γ β α₁ α₂ α₃ (M ω) z ξ ^ (-q) ∂P) ≤
        ENNReal.ofReal C := by
  let w : ℝ := (2 : ℝ) ^ (-∑ i : Fin 3, |γ * (![β, α₁, α₂] : Fin 3 → ℝ) i|) *
    (4 : ℝ) ^ (-|γ * α₃|)
  obtain ⟨C, hC, hb⟩ := gmc_inverse_moment_uniform_of_disk_lower
    P X hX γ hγ hγ₂ M hM q w hq (by dsimp only [w]; positivity)
  refine ⟨C, hC, ?_⟩
  intro z ξ hz hr
  exact hb _ fun ω => coulombMass_restrict_norm_fixed_disk_lower γ (M ω) ![β, α₁, α₂] ![z, 0, 1]
    α₃ _ hr (by simpa [Fin.forall_fin_succ] using hz)

/-- Exact Cameron-Martin identification of the inverse outer moment at arbitrary real circle time. -/
theorem retained_coulombMass_circle_tilt {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (β a m α₁ α₂ α₃ ξ q : ℝ) (hm : 0 ≤ m) (z : ℂ)
    (hr : 0 < ‖z‖ ^ (1 - ξ)) (houtside : Real.exp (-m) ≤ ‖z‖ ^ (1 - ξ)) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (a * Xc ω 0 m - m * a ^ 2 / 2)) *
      retainedCoulombMass γ β α₁ α₂ α₃ (M ω) z ξ ^ (-q) ∂P) =
      ∫⁻ ω, retainedCoulombMass γ β (α₁ + a) α₂ α₃ (M ω) z ξ ^ (-q) ∂P := by
  rw [reflected_lintegral_circleTilt P X hX γ hγ hγ₂ M hM Xc hXc a m hm
    (fun μ => retainedCoulombMass γ β α₁ α₂ α₃ μ z ξ ^ (-q))
    ((retainedCoulombMass_measurable γ β α₁ α₂ α₃ ξ z).pow_const (-q))]
  apply lintegral_congr
  intro ω
  rw [retained_coulombMass_circle_density_shift γ β a m α₁ α₂ α₃ ξ (M ω) z hr houtside]

/-- Every radial likelihood order and nonnegative outer inverse order is finite at the
actual retained source scale. Cameron-Martin handles the correlation, then the fixed disk gives
finiteness for the shifted charge. -/
theorem retained_coulombMass_radial_moment_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (β k ν h s α₁ α₂ α₃ ξ q : ℝ) (hh : 0 ≤ h) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hq : 0 ≤ q)
    (z : ℂ) (hz0 : z ≠ 0) (hz : ‖z‖ ≤ 1) :
    (∫⁻ ω, ENNReal.ofReal ((Real.exp (γ * Xc ω 0 (-Real.log ‖z‖ + h) -
        γ * ν * (-Real.log ‖z‖ + h) - k * (-Real.log ‖z‖)))^s)*
      retainedCoulombMass γ β α₁ α₂ α₃ (M ω) z ξ ^(-q) ∂P) < ⊤ := by
  let t := -Real.log ‖z‖
  let m := t+h
  let aTilt := γ*s
  let D := Real.exp (m*aTilt^2/2-s*γ*ν*m-s*k*t)
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hm : 0 ≤ m := by
    have hl := Real.log_nonpos hn.le hz
    dsimp only [m,t]
    linarith only [hl,hh]
  have hr0 : 0 < ‖z‖^(1-ξ) := Real.rpow_pos_of_pos hn _
  have hr1 : ‖z‖^(1-ξ) ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow hn.le hz (sub_nonneg.mpr hξ1.le)
  have hr : ‖z‖ ≤ ‖z‖^(1-ξ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hn hz
      (by linarith only [hξ] : 1-ξ ≤ 1)
  have hout : Real.exp (-m) ≤ ‖z‖^(1-ξ) := by
    have hsmall : -m ≤ Real.log ‖z‖ := by dsimp only [m,t]; linarith only [hh]
    have hs : Real.exp (-m) ≤ ‖z‖ := by
      simpa only [Real.exp_log hn] using Real.exp_le_exp.mpr hsmall
    exact hs.trans hr
  have he (ω : Ω) : (Real.exp (γ * Xc ω 0 (-Real.log ‖z‖ + h) -
        γ * ν * (-Real.log ‖z‖ + h) - k * (-Real.log ‖z‖)))^s =
      D*Real.exp (aTilt*Xc ω 0 m-m*aTilt^2/2) := by
    dsimp only [D,m,t,aTilt]
    rw [← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  have hshift := retained_coulombMass_circle_tilt P X hX γ hγ hγ₂ M hM Xc hc
    β aTilt m α₁ α₂ α₃ ξ q hm z hr0 hout
  obtain ⟨C, _, hb⟩ := retained_coulombMass_inverse_moment_uniform P X hX γ hγ hγ₂ M hM
    β (α₁+aTilt) α₂ α₃ q hq
  have hf  :=
    (hb z ξ hz hr1).trans_lt ENNReal.ofReal_lt_top
  have hD : 0 ≤ D := (Real.exp_pos _).le
  simp_rw [he, ENNReal.ofReal_mul hD, mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hshift]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf


/-- The actual retained source mass is positive and finite on one full-measure event. -/
theorem retained_coulombMass_positive_finite_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (β α₁ α₂ α₃ ξ : ℝ) (hβ : β < Q γ) (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hz : ‖z‖ ≤ 1)
    (hr : ‖z‖^(1-ξ) ≤ 1) :
    ∀ᵐ ω ∂P, 0 < retainedCoulombMass γ β α₁ α₂ α₃ (M ω) z ξ ∧
      retainedCoulombMass γ β α₁ α₂ α₃ (M ω) z ξ < ⊤ := by
  have hinj : Function.Injective (![z,0,1] : Fin 3 → ℂ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hcharges : ∀ i : Fin 3, (![β,α₁,α₂] : Fin 3 → ℝ) i < Q γ := by
    simpa [Fin.forall_fin_succ] using And.intro hβ (And.intro hα₁ hα₂)
  have hfull := reflected_coulombMass_ae_finite P X hX γ hγ hγ₂ M hM
    ![z,0,1] hinj ![β,α₁,α₂] α₃ hcharges hα₃
  have hmeas : AEMeasurable (fun ω => retainedCoulombMass γ β α₁ α₂ α₃ (M ω) z ξ) P :=
    (retainedCoulombMass_measurable γ β α₁ α₂ α₃ ξ z).comp_aemeasurable
      (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)
  obtain ⟨C, _, hb⟩ := retained_coulombMass_inverse_moment_uniform P X hX γ hγ hγ₂ M hM
    β α₁ α₂ α₃ 1 (by norm_num)
  have hInv : (∫⁻ ω, retainedCoulombMass γ β α₁ α₂ α₃ (M ω) z ξ ^ (-(1 : ℝ)) ∂P) < ⊤ :=
    (hb z ξ hz hr).trans_lt ENNReal.ofReal_lt_top
  filter_upwards [hfull, ae_lt_top' (hmeas.pow_const (-(1 : ℝ))) hInv.ne] with ω hf hi
  constructor
  · apply pos_iff_ne_zero.mpr
    intro he
    rw [he, ENNReal.zero_rpow_of_neg (by norm_num : -(1 : ℝ) < 0)] at hi
    exact lt_irrefl _ hi
  · have hle : retainedCoulombMass γ β α₁ α₂ α₃ (M ω) z ξ ≤
        coulombMass γ (M ω) ![β,α₁,α₂] ![z,0,1] α₃ := by
      unfold retainedCoulombMass coulombMass
      exact lintegral_mono' Measure.restrict_le_self le_rfl
    exact hle.trans_lt hf

end DOZZ.Proofs
