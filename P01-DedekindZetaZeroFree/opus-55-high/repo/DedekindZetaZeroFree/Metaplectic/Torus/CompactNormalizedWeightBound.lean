module

public import DedekindZetaZeroFree.Metaplectic.Torus.NormTwistedPeriodizationAndAveraging

@[expose] public section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.RepresentationTheory.torus_weighted_chart_quantitative_prove
open KPGlobalTorusBorelNormTwistTransport

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem delta_real_continuous : Continuous (fun t : E F ζ hζ =>
    (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ))) := by
  have hc := NNReal.continuous_coe.comp
    (Units.continuous_val.comp (KPGlobalCenterRationalCharacter.nu_continuous F ζ hζ))
  have he : (fun t : E F ζ hζ => (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ))) =
      (fun t : E F ζ hζ => (((KPGlobalCenterRationalCharacter.nu F ζ hζ t : ℝ≥0) : ℝ)) ^ (6 : ℕ)) := by
    funext t
    rw [KPGlobalCenterRationalCharacter.nu_formula, ← Real.rpow_natCast, ← Real.rpow_mul]
    · norm_num [KPGlobalTorusFunctionData.delta]
    simp
  rw [he]
  fun_prop

theorem normalized_weight_continuous (C : ModelData F ζ hζ) (s : ℂ) :
    Continuous (fun b : KPGlobalTorusPeriodizationInverse.B F ζ hζ C =>
      ‖(((((twist F ζ hζ (productModel F ζ hζ C) s).character b)⁻¹ : ℂˣ) : ℂ) *
        (KPGlobalTorusFunctionData.deltaHalf F ζ hζ b.val)⁻¹)‖) := by
  have hh : Continuous (fun b : KPGlobalTorusPeriodizationInverse.B F ζ hζ C =>
      KPGlobalTorusFunctionData.deltaHalf F ζ hζ b.val) :=
    Complex.continuous_ofReal.comp
      ((delta_real_continuous F ζ hζ).sqrt.comp continuous_subtype_val)
  have hn : ∀ b : KPGlobalTorusPeriodizationInverse.B F ζ hζ C,
      KPGlobalTorusFunctionData.deltaHalf F ζ hζ b.val ≠ 0 := by
    intro b
    unfold KPGlobalTorusFunctionData.deltaHalf
    simp
  exact ((Units.continuous_val.comp
    (Continuous.inv (twist F ζ hζ (productModel F ζ hζ C) s).character.continuous)).mul
      (hh.inv₀ hn)).norm

theorem compact_normalized_weight_bound (C : ModelData F ζ hζ) (s : ℂ)
    (L : Set (KPGlobalTorusPeriodizationInverse.B F ζ hζ C)) (hL : IsCompact L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ b ∈ L,
      ‖(((((twist F ζ hζ (productModel F ζ hζ C) s).character b)⁻¹ : ℂˣ) : ℂ) *
        (KPGlobalTorusFunctionData.deltaHalf F ζ hζ b.val)⁻¹)‖ ≤ B := by
  obtain ⟨B, hB⟩ := hL.bddAbove_image
    (normalized_weight_continuous F ζ hζ C s).continuousOn
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  intro b hb
  exact (hB (Set.mem_image_of_mem _ hb)).trans (le_max_right _ _)
