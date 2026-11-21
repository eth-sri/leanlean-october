module

public import DedekindZetaZeroFree.Analysis.Calculus.DominatedJets

public import DedekindZetaZeroFree.Metaplectic.Torus.Averaging.WeightedChartExtension
public import DedekindZetaZeroFree.Eisenstein.Induction.Borel.TwistedAveragingContinuity

@[expose] public section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory Filter
open scoped Topology ContDiff

namespace DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction
open KPGlobalTorusBorelNormTwistTransport
noncomputable section
set_option autoImplicit false

export DedekindZetaZeroFree (integral_contDiffOn_of_locally_dominated_jets)

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem functionsQ_chart_integral (C : ModelData F ζ hζ) (s : ℂ)
    (r : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C)
    (f : InducedFunctions F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s))
    (g : G F ζ hζ) (z : GroupArch F) :
    ((functionsQ F ζ hζ C s f).val (groupArchChart F ζ hζ z * g)).val.val 1 =
      ∫ x, twistedIntegrand F ζ hζ C s r
        (f.val (groupArchChart F ζ hζ z * g)) 1 x
        ∂KPGlobalTorusPeriodizationInverse.probabilityHaar F ζ hζ C := by
  exact twistedQ_formula F ζ hζ C s r
    (f.val (groupArchChart F ζ hζ z * g)) 1

theorem functionsQ_right_level (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : InducedFunctions F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s))
    (hf : f ∈ InducedLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J)
    (g : G F ζ hζ) (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J) :
    (functionsQ F ζ hζ C s f).val (g * j.val) =
      (functionsQ F ζ hζ C s f).val g := by
  change twistedQ F ζ hζ C s (f.val (g * j.val)) = twistedQ F ζ hζ C s (f.val g)
  rw [hf.2 g j]

theorem functionsQ_chart_contDiff_of_local_extension (C : ModelData F ζ hζ) (s : ℂ)
    (f : InducedFunctions F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s))
    (r : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C)
    (g : G F ζ hζ)
    (hlocal : ∀ z ∈ groupArchDomain F,
      ∃ U : Set (GroupArch F), IsOpen U ∧ z ∈ U ∧ U ⊆ groupArchDomain F ∧
        ∃ A : GroupArch F → KPGlobalTorusPeriodizationInverse.CompactIndex F ζ hζ C → ℂ,
          (∀ x, ContDiff ℝ (⊤ : ℕ∞) (fun y => A y x)) ∧
          (∀ n : ℕ, Continuous
            (fun p : GroupArch F × KPGlobalTorusPeriodizationInverse.CompactIndex F ζ hζ C =>
              iteratedFDeriv ℝ n (fun y => A y p.2) p.1)) ∧
          ∀ y ∈ U, ∀ x, A y x = twistedIntegrand F ζ hζ C s r
            (f.val (groupArchChart F ζ hζ y * g)) 1 x) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => ((functionsQ F ζ hζ C s f).val (groupArchChart F ζ hζ z * g)).val.val 1)
      (groupArchDomain F) := by
  refine contDiffOn_of_locally_contDiffOn ?_
  intro z hz
  obtain ⟨U, hU, hzU, _hUD, A, hA, hAj, hEq⟩ := hlocal z hz
  refine ⟨U, hU, hzU, ?_⟩
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => ∫ x, A y x ∂KPGlobalTorusPeriodizationInverse.probabilityHaar F ζ hζ C)
      Set.univ := by
    refine (integral_contDiffOn_of_locally_dominated_jets
      (KPGlobalTorusPeriodizationInverse.probabilityHaar F ζ hζ C) A Set.univ isOpen_univ
      (fun x => (hA x).contDiffOn) ?_ ?_).1
    · intro n y _
      simpa only [iteratedFDerivWithin_univ, Function.comp_def, id_eq] using
        ((hAj n).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable_of_compactSpace
    · intro n y _
      obtain ⟨B, hB⟩ := ((isCompact_closedBall y 1).prod (isCompact_univ : IsCompact
        (Set.univ : Set (KPGlobalTorusPeriodizationInverse.CompactIndex F ζ hζ C)))).exists_bound_of_continuousOn
          (hAj n).continuousOn
      refine ⟨Metric.closedBall y 1, (fun _ => B), Metric.closedBall_mem_nhds _ zero_lt_one,
        Set.subset_univ _, integrable_const B, Filter.Eventually.of_forall ?_⟩
      intro x v hv
      simpa only [iteratedFDerivWithin_univ] using hB (v, x) ⟨hv, Set.mem_univ x⟩
  apply (hsm.mono (Set.subset_univ _)).congr
  intro y hy
  rw [functionsQ_chart_integral F ζ hζ C s r f g y]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => (hEq y hy.2 x).symm)

theorem functionsQ_preserves_level (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : InducedFunctions F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s))
    (hf : f ∈ InducedLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J) :
    functionsQ F ζ hζ C s f ∈
      InducedLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J := by
  constructor
  · intro g
    let r := Classical.choice
      (KPGlobalTorusPeriodizationInverse.averaging_representatives_exist F ζ hζ C)
    apply functionsQ_chart_contDiff_of_local_extension F ζ hζ C s f r g
    intro z hz
    obtain ⟨U, hU, hzU, hUD, A, hA, hAj, hEq⟩ :=
      TorusChartTransport.weightedChart_local_extension F ζ hζ C s J f hf r g z hz
    refine ⟨U, hU, hzU, hUD, A, hA, hAj, ?_⟩
    intro y hy x
    rw [hEq y hy x, TorusChartTransport.weightedChartIntegrand_eq F ζ hζ C s r f g y]
  · exact functionsQ_right_level F ζ hζ C s J f hf

end
end DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction
