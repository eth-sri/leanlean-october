/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.ShiftEquations.DualFirstCase.Geometry
public import DOZZ.ShiftEquations.DualFirstCase.CoefficientIdentity
public import DOZZ.ShiftEquations.DualFirstCase.Continuation
public import DOZZ.Statements.ShiftEquations.TwoPoleWindow
import DOZZ.Brownian.Reflection.RtheorIdentification
import DOZZ.DOZZAlgebra.ReflectionShifts
import DOZZ.FourPoint.Crossing.GammaHalfCrossing
import DOZZ.FourPoint.Dual.FullFusion
import DOZZ.FourPoint.SeedOne.Assembly
import DOZZ.ShiftEquations.Shifts.Seeds.SeedTwo
import DOZZ.ShiftEquations.Gluing.ReflectedClosed
import DOZZ.ShiftEquations.Shifts.Rtheor

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
universe u
namespace DOZZ.Proofs
theorem structureConstant_dual_shift_strip_first_case_joint
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) X
    (M : Ω → Measure ℂ) γ μ η
    (hγ : 0 < γ) (hγ2 : γ < 2) (hγirr : Irrational (γ ^ 2)) (hμ : 0 < μ)
    (hη : 0 < η ∧ Q γ - 2 * η > γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (α₂ α₃ : ℝ)
    (hα₂ : Q γ - η < α₂ ∧ α₂ < Q γ)
    (hα₃ : Q γ - η < α₃ ∧ α₃ < Q γ)
    (hsmall : η ≤ γ / 4) :
    ∃ h : ℝ, 0 < h ∧ ∃ C : ℂ → ℂ,
      MeromorphicOn C (horizontalStrip h) ∧
      (∀ α : ℝ, 2 * η < α → α < Q γ →
        C (α : ℂ) = (structureConstant P M γ μ α α₂ α₃ : ℂ)) ∧
      (∀ᶠ z in codiscrete ℂ,
        C (z + γ / 2) =
          -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ) *
            C (z - γ / 2)) ∧
      ∀ᶠ z in codiscrete ℂ,
        C (z + 2 / γ) =
          -(1 / (Real.pi * dualMu γ μ)) *
            shiftCoeffA γ (2 / γ) z (α₂ : ℂ) (α₃ : ℂ) *
              C (z - 2 / γ) := by
  obtain ⟨e, he, heη, hesmall, hewindow, he₂, he₃⟩ :=
    dualFirstCase_shrink γ η α₂ α₃ hη hsmall hα₂ hα₃
  obtain ⟨B, Z, hZ, hB, H, hH, F, R, hF, hR, hFreal, hRreal, hglue, _hreflected⟩ :=
    structureConstant_reflected_shift_and_gluing_of_crossing P X M γ μ e hγ hγ2 hμ ⟨he, hewindow⟩
      hX hM α₂ α₃ he₂ he₃ fun μ' α' ε α hμ' h1 h2 h3 h4 h5 =>
        (gammaHalf_crossing P X M γ μ' α' ε α hγ hγ2 hμ' h1 h2 h3 h4 h5 hX hM).2
  have hseedTwo := dual_crossing_seed_two_of_fusion dual_full_fusion_and_asymptotic P M X
  have hOff := fun x (hα : γ / 2 < x ∧ x < Q γ) (hPole : ReflectionPoleFree γ x) Bx Zx
      (hData : IsReflectionData P γ x Bx Zx) =>
    reflection_Rtheor_off_poles_of_seedTwo P X M hseedTwo γ μ x hγ hγ2 hγirr hμ hX hM hα hPole Bx
      Zx hData
  have hχ : 0 < 2 / γ := div_pos (by norm_num) hγ
  have hχb : γ / 2 < 2 / γ := by
    apply (div_lt_div_iff₀ (by norm_num) hγ).mpr
    nlinarith only [hγ, hγ2]
  have hq : Q γ = 2 / γ + γ / 2 := rfl
  have hRD : R =ᶠ[codiscreteWithin (horizontalStrip H)] reflectionDOZZ γ μ := by
    apply dualFirstCase_continue_interval hH (lo := max (γ / 2) (2 / γ)) (hi := Q γ)
    · apply max_lt <;> rw [hq] <;> linarith only [hγ, hχ]
    · exact hR
    · exact (meromorphicOn_reflectionDOZZ γ μ hγ hγ2 hμ).mono_set (subset_univ _)
    · intro x hx hxQ
      have hxb : γ / 2 < x := lt_of_le_of_lt (le_max_left _ _) hx
      have hxc : Q γ - γ / 2 < x := by rw [hq]; linarith only [lt_of_le_of_lt (le_max_right _ _) hx]
      rw [hRreal x hxb hxQ]
      exact hOff x ⟨hxb, hxQ⟩ (dualFirstCase_poleFree hγ hxc) (B x) Z (hB x hxb hxQ)
  obtain ⟨lo, hloQ, hwindow⟩ := dualFirstCase_seed_interval γ e α₂ α₃ hγ hesmall he₂.1 he₃.1
  let a := max lo (2 / γ)
  have haQ : a < Q γ := max_lt hloQ (by rw [hq]; linarith only [hγ])
  have ha₂ : Q γ - γ / 2 < α₂ := by linarith only [he₂.1, hesmall, hγ]
  have ha₂b : γ / 2 < α₂ := by
    rw [hq] at he₂
    linarith only [he₂.1, hχb, hesmall, hγ]
  have hseed : (fun z => F (z + ((-(2 / γ) : ℝ) : ℂ))) =ᶠ[codiscreteWithin (horizontalStrip H)]
      (fun z => dualFirstCase_crossingProduct γ α₂ α₃ z * reflectionDOZZ γ μ z *
        F (((2 * Q γ - 2 / γ : ℝ) : ℂ) - z)) := by
    apply dualFirstCase_continue_interval hH haQ (dualFirstCase_meromorphic_translate hF (-(2 / γ)))
    · exact (((dualFirstCase_crossingProduct_meromorphic γ α₂ α₃).mono_set (subset_univ _)).mul
        ((meromorphicOn_reflectionDOZZ γ μ hγ hγ2 hμ).mono_set (subset_univ _))).mul
          (dualFirstCase_meromorphic_reflect hF (2 * Q γ - 2 / γ))
    · intro x hx hxQ
      have hxlo : lo < x := lt_of_le_of_lt (le_max_left _ _) hx
      obtain ⟨hs, hminus, href⟩ := hwindow x hxlo hxQ
      have hxc : Q γ - γ / 2 < x := by
        rw [hq]; linarith only [lt_of_le_of_lt (le_max_right _ _) hx]
      have hxb : γ / 2 < x := by linarith only [hminus.1, he, hχb]
      obtain ⟨B₁, Z₁, _hZ₁, hB₁, hc₁⟩ :=
        dual_crossing_seed_one P M X γ μ x α₂ α₃ hγ hγ2 hμ hxQ he₂.2 he₃.2 hs hX hM
      obtain ⟨B₂, Bx, Z₂, _hZ₂, hB₂, hBx, hc₂⟩ :=
        hseedTwo γ μ x α₂ α₃ hγ hγ2 hμ hxQ he₂.2 he₃.2 hs hX hM
      have hc₁c := congrArg (fun r : ℝ => (r : ℂ)) hc₁
      have hc₂c := congrArg (fun r : ℝ => (r : ℂ)) hc₂
      push_cast at hc₁c hc₂c
      rw [hOff α₂ ⟨ha₂b, he₂.2⟩ (dualFirstCase_poleFree hγ ha₂) B₁ Z₁ hB₁] at hc₁c
      rw [hOff α₂ ⟨ha₂b, he₂.2⟩ (dualFirstCase_poleFree hγ ha₂) B₂ Z₂ hB₂,
        hOff x ⟨hxb, hxQ⟩ (dualFirstCase_poleFree hγ hxc) Bx Z₂ hBx,
        dualFirstCase_structure_swap12 P X M γ μ (2 * Q γ - α₂ - 2 / γ) x α₃ hγ hγ2 hX hM,
        dualFirstCase_structure_swap12 P X M γ μ α₂ (2 * Q γ - x - 2 / γ) α₃ hγ hγ2 hX hM] at hc₂c
      rw [show (x : ℂ) + ((-(2 / γ) : ℝ) : ℂ) = ((x - 2 / γ : ℝ) : ℂ) by push_cast; ring,
        show ((2 * Q γ - 2 / γ : ℝ) : ℂ) - (x : ℂ) = ((2 * Q γ - x - 2 / γ : ℝ) : ℂ) by push_cast; ring,
        hFreal (x - 2 / γ) hminus.1 hminus.2,
        hFreal (2 * Q γ - x - 2 / γ) href.1 href.2,
        dualFirstCase_crossingProduct_ofReal γ x α₂ α₃ hγ.ne']
      calc
        (structureConstant P M γ μ (x - 2 / γ) α₂ α₃ : ℂ) = _ := hc₁c
        _ = (dualCrossingMultiplier γ α₃ x α₂ : ℂ) *
          (reflectionDOZZ γ μ α₂ * (structureConstant P M γ μ x (2 * Q γ - α₂ - 2 / γ) α₃ : ℂ)) := by ring
        _ = _ := by rw [hc₂c]; push_cast; ring
  have hk := four_div_sq_ne_int_of_irrational hγirr
  have hK : (Real.pi : ℂ) * dualMu γ μ ≠ 0 := by
    have heq : (Real.pi : ℂ) * dualMu γ μ = reflectionDOZZDualConst γ μ := by
      unfold dualMu reflectionDOZZDualConst
      field_simp
    rw [heq]
    exact reflectionDOZZDualConst_ne_zero hγ hγ2 hμ hk
  have hcoeff := dualFirstCase_coefficient_product_codiscrete γ (α₂ : ℂ) (α₃ : ℂ) hγ.ne'
    (dualFirstCase_fixed_factor_ne_zero hγ ha₂ he₂.2)
  have hden := reflectionDualShiftDenom_ne_zero hγ hk
  have hshiftR := reflectionDOZZ_shift_binv hγ hγ2 (fun n => by exact_mod_cast hk n) hμ
  have hglueW : ∀ᶠ z in codiscreteWithin (horizontalStrip H), F z = R z * F (2 * Q γ - z) :=
    hglue.filter_mono (codiscreteWithin_le_codiscrete_inf_principal _ |>.trans inf_le_left)
  have hplus := dualFirstCase_codiscreteWithin_translate hglueW (2 / γ)
  have hRDplus := dualFirstCase_codiscreteWithin_translate hRD (2 / γ)
  have hshiftF : ∀ᶠ z in codiscreteWithin (horizontalStrip H),
      F (z + (2 / γ : ℝ)) =
        (-(1 / (Real.pi * dualMu γ μ)) * shiftCoeffA γ (2 / γ) z α₂ α₃) * F (z - (2 / γ : ℝ)) := by
    have hfilter : codiscreteWithin (horizontalStrip H) ≤ codiscrete ℂ :=
      codiscreteWithin_le_codiscrete_inf_principal _ |>.trans inf_le_left
    filter_upwards [hseed, hplus, hRDplus, hcoeff.filter_mono hfilter,
      hden.filter_mono hfilter, hshiftR.filter_mono hfilter] with z hs hg hrd hc hd hr
    rw [hr] at hs
    rw [hrd] at hg
    have hreflect : ((2 * Q γ - 2 / γ : ℝ) : ℂ) - z = 2 * Q γ - (z + (2 / γ : ℝ)) := by push_cast; ring
    rw [hreflect] at hs
    have hconst : (((dozzBase γ μ : ℝ) : ℂ) ^ ((4 / γ ^ 2 : ℝ) : ℂ) /
      lFun ((4 / γ ^ 2 : ℝ) : ℂ)) = (Real.pi : ℂ) * dualMu γ μ := by
      unfold dualMu
      field_simp
    rw [hconst] at hs
    simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat] at hs hg ⊢
    rw [← sub_eq_add_neg] at hs
    change dualFirstCase_crossingProduct γ α₂ α₃ z * shiftCoeffA γ (2 / γ) z α₂ α₃ = reflectionDualShiftDenom γ z at hc
    exact dualFirstCase_scalar_shift
      (dualFirstCase_crossingProduct γ α₂ α₃ z) (shiftCoeffA γ (2 / γ) z α₂ α₃)
      ((Real.pi : ℂ) * dualMu γ μ) (reflectionDualShiftDenom γ z)
      (reflectionDOZZ γ μ (z + 2 / γ)) (F (2 * Q γ - (z + 2 / γ)))
      (F (z - 2 / γ)) (F (z + 2 / γ)) hd hK hc
      (by simpa only [reflectionDualShiftDenom, Complex.ofReal_div, Complex.ofReal_ofNat] using hs) hg
  have hfirstF : ∀ᶠ z in codiscrete ℂ,
      F (z + γ / 2) = -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z α₂ α₃ * F (z - γ / 2) := by
    filter_upwards [eventually_codiscrete_comp_add hglue ((γ / 2 : ℝ) : ℂ), _hreflected] with z hg hr
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at hg
    rw [hg, show 2 * (Q γ : ℂ) - (z + γ / 2) = 2 * Q γ - z - γ / 2 by ring]
    exact hr
  obtain ⟨C, hC, hCF, hCzero, hCs⟩ :=
    dualFirstCase_common_representative F
      (fun z => -(1 / (Real.pi * dualMu γ μ)) * shiftCoeffA γ (2 / γ) z α₂ α₃)
      H (2 / γ) hH hF hshiftF
  refine ⟨H / 2, half_pos hH, C, hC, ?_, ?_, ?_⟩
  · intro x hx hxQ
    have hxstrip : (x : ℂ) ∈ horizontalStrip (H / 2) := by
      simpa only [horizontalStrip, mem_ofPred_eq, Complex.ofReal_im, abs_zero] using half_pos hH
    rw [hCF hxstrip]
    exact hFreal x (by linarith only [heη, hx]) hxQ
  · have hfirstF' : ∀ᶠ z in codiscrete ℂ,
        F (z + ((γ / 2 : ℝ) : ℂ)) =
          (-(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z α₂ α₃) * F (z - ((γ / 2 : ℝ) : ℂ)) := by
      simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using hfirstF
    have ht := dualFirstCase_transfer_global_shift F C
      (fun z => -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z α₂ α₃)
      (H / 2) (γ / 2) hCF hCzero hfirstF'
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using ht
  · simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using hCs
end DOZZ.Proofs
