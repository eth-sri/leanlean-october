module
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_STATIONARY_DYADIC_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonStationarySeries
public import MathCollab.Density.Stronger.Atkinson.AtkinsonMainNormalization
public import MathCollab.Density.Stronger.Atkinson.AtkinsonMainVariation
public import MathCollab.Density.Stronger.Atkinson.AtkinsonPrefixVectors
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Set Filter
open MathCollab.Density.Stronger.Fourth
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def atkinsonNegativePhaseTerm (T : ℝ) (n : ℕ) : ℂ :=
  divisorWeight n * (-1:ℂ)^n * Complex.exp ((-atkinsonSourcePhase T n : ℂ)*I)

def atkinsonCommonMainPhase (T : ℝ) : ℂ :=
  (1+I)*zetaSquareReflectedGammaPhase T*Complex.exp ((atkinsonCentralPhase T : ℂ)*I)

theorem atkinsonStationaryLeadingTerm_eq_signed {T G : ℝ} (hT : 0 < T)
    (hG : G ≠ 0) (L : ℝ) (n : ℕ) :
    atkinsonStationaryLeadingTerm T G L n = atkinsonCommonMainPhase T *
      (atkinsonPositiveMainWeight T G L n*atkinsonPositivePhaseTerm T n -
        atkinsonNegativeMainWeight T G L n*atkinsonNegativePhaseTerm T n) := by
  have he : (2:ℂ)*(Real.sqrt Real.pi : ℂ)*(atkinsonBesselScale (1/4) n : ℂ) =
      (((n:ℝ)^(-(1/4:ℝ)) : ℝ) : ℂ) := by
    exact_mod_cast atkinsonBesselScale_quarter_normalization n
  pm_146 hpi Real.pi Real.pi_ne_zero
  unfold atkinsonStationaryLeadingTerm atkinsonStationaryLeadingIntegral
  rw [atkinsonStationaryMain_sqrt_normalized hT,atkinsonStationaryMain_neg_sqrt_normalized hT hG]
  unfold atkinsonCommonMainPhase atkinsonPositiveMainWeight atkinsonNegativeMainWeight
    atkinsonPositivePhaseTerm atkinsonNegativePhaseTerm atkinsonFourthRootCoefficient
    neumannLeadingPlus neumannLeadingMinus
  push_cast
  rw [← he]
  field_simp
  ring_nf
  simp only [I_sq]
  ring

theorem norm_atkinsonCommonMainPhase_le (T : ℝ) :
    ‖atkinsonCommonMainPhase T‖ ≤ 2 := by
  unfold atkinsonCommonMainPhase
  rw [norm_mul,norm_mul,norm_zetaSquareReflectedGammaPhase,Complex.norm_exp_ofReal_mul_I,
    mul_one,mul_one]
  apply (norm_add_le _ _).trans
  norm_num

theorem atkinsonNegativePhaseTerm_eq_conj (T : ℝ) (n : ℕ) :
    atkinsonNegativePhaseTerm T n = (starRingEnd ℂ) (atkinsonPositivePhaseTerm T n) := by
  unfold atkinsonNegativePhaseTerm atkinsonPositivePhaseTerm divisorWeight
  simp only [map_mul,map_pow,map_neg,map_one,map_natCast,← Complex.exp_conj,
    Complex.conj_ofReal,Complex.conj_I]
  congr 2
  ring

end MathCollab.Density.Stronger.Atkinson
