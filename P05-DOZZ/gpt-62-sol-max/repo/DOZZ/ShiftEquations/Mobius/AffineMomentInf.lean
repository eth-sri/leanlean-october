/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Mobius.AffineMoment
import DOZZ.GMC.EquatorGFFChaosTransportLaw
public import DOZZ.ShiftEquations.Mobius.RepinTilt
import DOZZ.ShiftEquations.Mobius.InversionMoment

/-!
# Coulomb moments under affine maps, with a charge at infinity

The affine moment identity of `AffineMoment` extended to Coulomb masses with a charge `αinf`
at infinity. Through `ψ(y) = a y + b` the background factor `|x|_+^{γ αinf}` picks up
`exp (γ αinf (d(y) + log|a|/2))`, so the defect exponent becomes `γ (∑αₖ + αinf)` and the
zero-mode exponent is `s = (∑αₖ + αinf - 2Q)/γ`. The same repinning, law transport and
Cameron–Martin tilt give `E[I_{ψz}^{-s}] = |a|^{γ (∑αₖ - αinf) s/2} E[I_z^{-s}]`; in particular
translations preserve the moments.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The zero-mode exponent `(∑αₖ + αinf - 2Q)/γ` with a charge at infinity. -/
noncomputable def infSExp {N : ℕ} (γ : ℝ) (α : Fin N → ℝ) (αinf : ℝ) : ℝ :=
  ((∑ k, α k) + αinf - 2 * Q γ) / γ

/-- The charge at infinity contributes the extra factor `|x|_+^{γ αinf}`. -/
private theorem coulombWeight_inf_eq {N : ℕ} (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ)
    (αinf : ℝ) (x : ℂ) :
    coulombWeight γ α z αinf x =
      coulombWeight γ α z 0 x * ENNReal.rpow (ENNReal.ofReal (normPlus x)) (γ * αinf) := by
  unfold coulombWeight
  simp only [ENNReal.rpow_eq_pow, mul_zero, ENNReal.rpow_zero, mul_one]

/-- A power of the background weight through the affine map picks up the defect. -/
private theorem rpow_normPlus_affine (a b : ℂ) (y : ℂ) (e : ℝ) :
    ENNReal.rpow (ENNReal.ofReal (normPlus (a * y + b))) e =
      ENNReal.ofReal (Real.exp (e * (affineDefect a b y + Real.log ‖a‖ / 2))) *
        ENNReal.rpow (ENNReal.ofReal (normPlus y)) e := by
  have hy := normPlus_pos' y
  have hψ := normPlus_pos' (a * y + b)
  have hnorm : normPlus (a * y + b) =
      Real.exp (affineDefect a b y + Real.log ‖a‖ / 2) * normPlus y := by
    have h : affineDefect a b y + Real.log ‖a‖ / 2 =
        Real.log (normPlus (a * y + b) / normPlus y) := by
      rw [Real.log_div hψ.ne' hy.ne']
      unfold affineDefect
      ring
    rw [h, Real.exp_log (by positivity)]
    field_simp
  simp [ENNReal.rpow_eq_pow, hnorm, ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul, mul_comm e]

/-- **The Coulomb weight with a charge at infinity through an affine map**, off the roots. -/
theorem coulombWeight_affine_inf {N : ℕ} (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf : ℝ)
    (a b : ℂ) (ha : a ≠ 0) {y : ℂ} (hyz : ∀ k, y ≠ z k) :
    coulombWeight γ α (fun k => a * z k + b) αinf (a * y + b) =
      ENNReal.ofReal (Real.exp (γ * ((∑ k, α k) + αinf) * affineDefect a b y -
        γ * ((∑ k, α k) - αinf) * (Real.log ‖a‖ / 2))) * coulombWeight γ α z αinf y := by
  rw [coulombWeight_inf_eq γ α _ αinf (a * y + b), coulombWeight_inf_eq γ α z αinf y,
    coulombWeight_affine γ α z a b ha hyz, rpow_normPlus_affine a b y (γ * αinf)]
  have hE : ENNReal.ofReal (Real.exp (γ * ((∑ k, α k) + αinf) * affineDefect a b y -
        γ * ((∑ k, α k) - αinf) * (Real.log ‖a‖ / 2))) =
      ENNReal.ofReal (Real.exp (γ * (∑ k, α k) * (affineDefect a b y - Real.log ‖a‖ / 2))) *
        ENNReal.ofReal (Real.exp (γ * αinf * (affineDefect a b y + Real.log ‖a‖ / 2))) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  rw [hE]
  ring

/-- The Coulomb mass of the repinned chaos is a tilted reweighting of `M`. -/
theorem lintegral_coulombWeight_repinChaos_inf {Ω : Type*} (M : Ω → Measure ℂ) (L : Ω → ℝ)
    (a b : ℂ) (ha : a ≠ 0) (γ V : ℝ) (ω : Ω) {N : ℕ} (α : Fin N → ℝ) (z : Fin N → ℂ)
    (αinf : ℝ) :
    ∫⁻ x, coulombWeight γ α z αinf x ∂repinChaos M L a b γ V ω =
      ENNReal.ofReal (Real.exp (-γ * L ω - γ ^ 2 / 2 * V)) *
        ∫⁻ x, coulombWeight γ α z αinf (affineInv a b x) *
          ENNReal.ofReal (Real.exp (γ ^ 2 * repinPotential a b x) * repinWeight a b x) ∂M ω := by
  have hc := continuous_repinPotential a b ha
  have hw := continuous_repinWeight a b ha
  unfold repinChaos
  have hcw : Measurable fun x => coulombWeight γ α z αinf (affineInv a b x) :=
    (measurable_coulombWeight γ α z αinf).comp (continuous_affineInv a b).measurable
  rw [lintegral_map (measurable_coulombWeight γ α z αinf) (continuous_affineInv a b).measurable,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hcw,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext x
  simp only [Pi.mul_apply]
  rw [Real.exp_add, mul_assoc, ENNReal.ofReal_mul (Real.exp_pos _).le]
  ring

/-- **The reweighting identity with a charge at infinity.** -/
theorem coulombWeight_repin_identity_inf {N : ℕ} (γ : ℝ) (hγ : 0 < γ) (α : Fin N → ℝ)
    (z : Fin N → ℂ) (αinf : ℝ) (a b : ℂ) (ha : a ≠ 0) {x : ℂ} (hx : ∀ k, x ≠ a * z k + b) :
    coulombWeight γ α z αinf (affineInv a b x) *
        ENNReal.ofReal (Real.exp (γ ^ 2 * (1 + infSExp γ α αinf) * repinPotential a b x) *
          repinWeight a b x) =
      ENNReal.ofReal (‖a‖ ^ (γ * ((∑ k, α k) - αinf) / 2) *
        Real.exp (γ ^ 2 * (1 + infSExp γ α αinf) * repinKappa a b)) *
        coulombWeight γ α (fun k => a * z k + b) αinf x := by
  set y := affineInv a b x with hydef
  have hxy : x = a * y + b := (affine_affineInv a b ha x).symm
  have hyz : ∀ k, y ≠ z k := fun k h => hx k (by rw [hxy, h])
  have hapos  := norm_pos_iff.mpr ha
  have hγne  := hγ.ne'
  have hexp : γ ^ 2 * (1 + infSExp γ α αinf) + 4 = γ * ((∑ k, α k) + αinf) := by
    unfold infSExp Q
    field_simp
    ring
  rw [hxy, coulombWeight_affine_inf γ α z αinf a b ha hyz, repinPotential_affine a b ha y,
    repinWeight_affine a b ha y, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    mul_comm (ENNReal.ofReal _) (coulombWeight _ _ _ _ _)]
  congr 2
  rw [Real.rpow_def_of_pos hapos, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  linear_combination (affineDefect a b y) * hexp

/-- **Coulomb moments with a charge at infinity under affine maps**:
`E[I_{ψz}^{-s}] = |a|^{γ (∑αₖ - αinf) s/2} E[I_z^{-s}]`, `s = (∑αₖ + αinf - 2Q)/γ`. -/
theorem coulombMass_affine_moment_inf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) {N : ℕ} (α : Fin N → ℝ) (z : Fin N → ℂ)
    (αinf : ℝ) (a b : ℂ) (ha : a ≠ 0) :
    ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α (fun k => a * z k + b) αinf)
        (-infSExp γ α αinf) ∂P =
      ENNReal.ofReal (‖a‖ ^ (γ * ((∑ k, α k) - αinf) * infSExp γ α αinf / 2)) *
        ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α z αinf) (-infSExp γ α αinf) ∂P := by
  obtain ⟨hMfin, Xc, hXc, hconv⟩ := id hM
  set s := infSExp γ α αinf with hs
  set S := ∑ k, α k with hS
  set L : Ω → ℝ := fun ω => Xc ω b (-Real.log ‖a‖) with hLdef
  set VL : ℝ := ∫ ω, L ω ^ 2 ∂P with hVLdef
  set κ := repinKappa a b with hκ
  have hapos  := norm_pos_iff.mpr ha
  have hV : gaussianVariance P L = VL := by simp only [gaussianVariance, gaussianCovariance, hVLdef, pow_two]
  have hVL : VL = 2 * κ := (hV.symm.trans (gaussianVariance_repinCircle P X hX Xc hXc a b ha))
  set J : Measure ℂ → ℝ≥0∞ := fun μ => ∫⁻ x, coulombWeight γ α z αinf (affineInv a b x) *
    ENNReal.ofReal (Real.exp (γ ^ 2 * repinPotential a b x) * repinWeight a b x) ∂μ with hJ
  have hcw  :=
    (measurable_coulombWeight γ α z αinf).comp (continuous_affineInv a b).measurable
  have hc := continuous_repinPotential a b ha
  have hw := continuous_repinWeight a b ha
  have hJmeas : Measurable J :=
    Measure.measurable_lintegral (hcw.mul (ENNReal.measurable_ofReal.comp (by fun_prop)))
  -- Step 1: the repinned model has the law of the original one
  have hlaw := equatorGFF_GMC_law_transport P X hX P (repinField X L a b)
    (isEquatorGFF_repinField P X Xc a b hX hXc ha) γ hγ hγ2 M hM (repinChaos M L a b γ VL)
    (isGMCOf_repinChaos P X hX γ M hMfin Xc hXc hconv a b ha)
    (fun _ μ => ENNReal.rpow (∫⁻ x, coulombWeight γ α z αinf x ∂μ) (-s))
    (by
      simp only [ENNReal.rpow_eq_pow]
      exact ((Measure.measurable_lintegral (measurable_coulombWeight γ α z αinf)).comp
        measurable_snd).pow_const _)
  -- Step 2: the repinned mass is a random multiple of `J M`
  have h2 : ∀ ω, ENNReal.rpow (∫⁻ x, coulombWeight γ α z αinf x ∂repinChaos M L a b γ VL ω) (-s) =
      ENNReal.ofReal (Real.exp (s * (γ ^ 2 / 2 * VL))) *
        (ENNReal.ofReal (Real.exp (γ * s * L ω)) * ENNReal.rpow (J (M ω)) (-s)) := by
    intro ω
    rw [lintegral_coulombWeight_repinChaos_inf M L a b ha γ VL ω α z αinf, ENNReal.rpow_eq_pow, inversionMoment_mul_rpow
          (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' ENNReal.ofReal_ne_top, ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ENNReal.rpow_eq_pow]
    congr 3
    ring
  -- The repinning circle tilt removes the Gaussian factor.
  have htilt := lintegral_repin_circle_tilt P X hX γ hγ hγ2 M hM Xc hXc a b ha (γ * s)
    (fun μ => ENNReal.rpow (J μ) (-s))
    (by simpa only [ENNReal.rpow_eq_pow] using hJmeas.pow_const (-s))
  change (∫⁻ ω, ENNReal.ofReal (Real.exp (γ * s * L ω - (γ * s) ^ 2 * gaussianVariance P L / 2)) *
      ENNReal.rpow (J (M ω)) (-s) ∂P) = _ at htilt
  rw [hV] at htilt
  -- Step 4: the tilted reweighted mass is a constant multiple of the Coulomb mass at `ψ z`
  set K : ℝ := ‖a‖ ^ (γ * (S - αinf) / 2) * Real.exp (γ ^ 2 * (1 + s) * κ) with hKdef
  have hKpos : 0 < K := by positivity
  have h4 : ∀ᵐ ω ∂P, J ((M ω).withDensity fun x => ENNReal.ofReal (Real.exp (γ * (γ * s * repinPotential a b x)))) =
      ENNReal.ofReal K * coulombMass γ (M ω) α (fun k => a * z k + b) αinf := by
    have hatoms : ∀ᵐ ω ∂P, ∀ k, M ω {a * z k + b} = 0 :=
      ae_all_iff.2 fun k => gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM _
    filter_upwards [hatoms] with ω hω
    have hD : Measurable fun x => ENNReal.ofReal (Real.exp (γ * (γ * s * repinPotential a b x))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (measurable_const.mul (measurable_const.mul (continuous_repinPotential a b ha).measurable)))
    have hI : Measurable fun x => coulombWeight γ α z αinf (affineInv a b x) *
        ENNReal.ofReal (Real.exp (γ ^ 2 * repinPotential a b x) * repinWeight a b x) :=
      hcw.mul (ENNReal.measurable_ofReal.comp (by fun_prop))
    simp only [hJ]
    rw [lintegral_withDensity_eq_lintegral_mul _ hD hI,
      coulombMass_eq_lintegral_coulombWeight, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr_ae
    have hnull  := measure_iUnion_null hω
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx
    have hxk  := fun k h => hx (Set.mem_iUnion.2 ⟨k, h⟩)
    rw [hKdef, ← coulombWeight_repin_identity_inf γ hγ α z αinf a b ha hxk]
    simp only [Pi.mul_apply]
    rw [mul_left_comm, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← mul_assoc, ← Real.exp_add]
    congr 4
    ring
  -- Step 5: collect the constants
  have hfac : ∀ ω, ENNReal.ofReal (Real.exp (γ * s * L ω)) =
      ENNReal.ofReal (Real.exp ((γ * s) ^ 2 * VL / 2)) *
        ENNReal.ofReal (Real.exp (γ * s * L ω - (γ * s) ^ 2 * VL / 2)) := by
    intro ω
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  have hmain : ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α z αinf) (-s) ∂P =
      ENNReal.ofReal (Real.exp (s * (γ ^ 2 / 2 * VL))) *
        (ENNReal.ofReal (Real.exp ((γ * s) ^ 2 * VL / 2)) *
          (ENNReal.rpow (ENNReal.ofReal K) (-s) *
            ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α (fun k => a * z k + b) αinf) (-s) ∂P)) := by
    calc ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α z αinf) (-s) ∂P
        = ∫⁻ ω, ENNReal.rpow (∫⁻ x, coulombWeight γ α z αinf x ∂repinChaos M L a b γ VL ω) (-s)
            ∂P := hlaw
      _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (s * (γ ^ 2 / 2 * VL))) *
            (ENNReal.ofReal (Real.exp (γ * s * L ω)) * ENNReal.rpow (J (M ω)) (-s)) ∂P := by
          simp_rw [h2]
      _ = ENNReal.ofReal (Real.exp (s * (γ ^ 2 / 2 * VL))) *
            (ENNReal.ofReal (Real.exp ((γ * s) ^ 2 * VL / 2)) *
              ∫⁻ ω, ENNReal.ofReal (Real.exp (γ * s * L ω - (γ * s) ^ 2 * VL / 2)) *
                ENNReal.rpow (J (M ω)) (-s) ∂P) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          simp_rw [hfac, mul_assoc]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = _ := by
          rw [htilt]
          congr 2
          have hne : (ENNReal.ofReal K).rpow (-s) ≠ ⊤ := by
            rw [ENNReal.rpow_eq_pow]
            exact ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_pos.mpr hKpos).ne'
              ENNReal.ofReal_ne_top
          rw [← lintegral_const_mul' _ _ hne]
          apply lintegral_congr_ae
          filter_upwards [h4] with ω hω
          rw [hω, ENNReal.rpow_eq_pow, ENNReal.rpow_eq_pow, ENNReal.rpow_eq_pow,
            inversionMoment_mul_rpow (ENNReal.ofReal_pos.mpr hKpos).ne' ENNReal.ofReal_ne_top]
  have hconst : ENNReal.ofReal (‖a‖ ^ (γ * (S - αinf) * s / 2)) *
      (ENNReal.ofReal (Real.exp (s * (γ ^ 2 / 2 * VL))) *
        (ENNReal.ofReal (Real.exp ((γ * s) ^ 2 * VL / 2)) *
          ENNReal.rpow (ENNReal.ofReal K) (-s))) = 1 := by
    have hlogK : Real.log K = γ * (S - αinf) / 2 * Real.log ‖a‖ + γ ^ 2 * (1 + s) * κ := by
      rw [hKdef, Real.log_mul (Real.rpow_pos_of_pos hapos _).ne' (Real.exp_pos _).ne',
        Real.log_rpow hapos, Real.log_exp]
    rw [ENNReal.rpow_eq_pow, ENNReal.ofReal_rpow_of_pos hKpos,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hapos _).le, ← ENNReal.ofReal_one]
    congr 1
    rw [Real.rpow_def_of_pos hapos, Real.rpow_def_of_pos hKpos, hlogK, ← Real.exp_add,
      ← Real.exp_add, ← Real.exp_add, Real.exp_eq_one_iff, hVL]
    ring
  calc ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α (fun k => a * z k + b) αinf) (-s) ∂P
      = (ENNReal.ofReal (‖a‖ ^ (γ * (S - αinf) * s / 2)) *
          (ENNReal.ofReal (Real.exp (s * (γ ^ 2 / 2 * VL))) *
            (ENNReal.ofReal (Real.exp ((γ * s) ^ 2 * VL / 2)) *
              ENNReal.rpow (ENNReal.ofReal K) (-s)))) *
          ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α (fun k => a * z k + b) αinf) (-s) ∂P := by
        rw [hconst, one_mul]
    _ = ENNReal.ofReal (‖a‖ ^ (γ * (S - αinf) * s / 2)) *
          ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α z αinf) (-s) ∂P := by
        rw [hmain]
        ring

end DOZZ.Proofs

end
