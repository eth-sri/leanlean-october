module

public import DedekindZetaZeroFree.Eisenstein.Induction.Borel.TwistedAveragingSmoothness
public import DedekindZetaZeroFree.Eisenstein.Induction.RationalPeriodizationJetEstimates

@[expose] public section

section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction
open KPGlobalTorusBorelNormTwistTransport
noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
open scoped Topology

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

local instance functionsQLevelFunctionsAddGroup (P : Polarization F ζ hζ) :
    AddCommGroup (InducedFunctions F ζ hζ P) :=
  @Submodule.addCommGroup ℂ (G F ζ hζ → Smooth F ζ hζ P)
    inferInstance inferInstance inferInstance (InducedFunctions F ζ hζ P)
local instance functionsQLevelAddGroup (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    AddCommGroup (InducedLevel F ζ hζ P J) :=
  @Submodule.addCommGroup ℂ (InducedFunctions F ζ hζ P)
    inferInstance inferInstance inferInstance (InducedLevel F ζ hζ P J)

theorem functionsQ_level_continuous_of_isBounded (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (hbound : Seminorm.IsBounded
      (fun i : G F ζ hζ × ℕ × KPGlobalTorusFunctionData.JetCompact (groupArchDomain F) =>
        inducedJet F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J i.1 i.2.1 i.2.2)
      (fun i : G F ζ hζ × ℕ × KPGlobalTorusFunctionData.JetCompact (groupArchDomain F) =>
        inducedJet F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J i.1 i.2.1 i.2.2)
      (levelMap F ζ hζ _ _ (functionsQ F ζ hζ C s)
        (functionsQ_preserves_level F ζ hζ C s) J)) :
    @Continuous
      (InducedLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J)
      (InducedLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J)
      (inducedLevelTopology F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J)
      (inducedLevelTopology F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J)
      (levelMap F ζ hζ _ _ (functionsQ F ζ hζ C s)
        (functionsQ_preserves_level F ζ hζ C s) J) := by
  letI := inducedLevelTopology F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J
  letI := inducedLevelTopology F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J
  have hp : WithSeminorms (fun i : G F ζ hζ × ℕ ×
      KPGlobalTorusFunctionData.JetCompact (groupArchDomain F) =>
      inducedJet F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J i.1 i.2.1 i.2.2) :=
    ⟨rfl⟩
  have hq : WithSeminorms (fun i : G F ζ hζ × ℕ ×
      KPGlobalTorusFunctionData.JetCompact (groupArchDomain F) =>
      inducedJet F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J i.1 i.2.1 i.2.2) :=
    ⟨rfl⟩
  exact WithSeminorms.continuous_of_isBounded hp hq _ hbound

theorem functionsQ_chart_integral_jets (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (r : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C)
    (f : InducedLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J)
    (g : G F ζ hζ) (n : ℕ) (z : GroupArch F) (hz : z ∈ groupArchDomain F) :
    iteratedFDerivWithin ℝ n
      (fun y => ((functionsQ F ζ hζ C s f.val).val
        (groupArchChart F ζ hζ y * g)).val.val 1) (groupArchDomain F) z =
    ∫ x, iteratedFDerivWithin ℝ n
      (fun y => TorusChartTransport.weightedChartIntegrand F ζ hζ C s r f.val g y x)
      (groupArchDomain F) z
      ∂KPGlobalTorusPeriodizationInverse.probabilityHaar F ζ hζ C := by
  obtain ⟨U, hU, hzU, hUD, A, hA, hAj, hEq⟩ :=
    TorusChartTransport.weightedChart_local_extension F ζ hζ C s J f.val f.property r g z hz
  have hj := (integral_contDiffOn_of_locally_dominated_jets
    (KPGlobalTorusPeriodizationInverse.probabilityHaar F ζ hζ C) A Set.univ isOpen_univ
    (fun x => (hA x).contDiffOn) (by
      intro m y _
      simpa only [iteratedFDerivWithin_univ, Function.comp_def, id_eq] using
        ((hAj m).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable_of_compactSpace)
    (by
      intro m y _
      obtain ⟨B, hB⟩ := ((isCompact_closedBall y 1).prod (isCompact_univ : IsCompact
        (Set.univ : Set (KPGlobalTorusPeriodizationInverse.CompactIndex F ζ hζ C)))).exists_bound_of_continuousOn
          (hAj m).continuousOn
      refine ⟨Metric.closedBall y 1, (fun _ => B), Metric.closedBall_mem_nhds _ zero_lt_one,
        Set.subset_univ _, integrable_const B, Filter.Eventually.of_forall ?_⟩
      intro x v hv
      simpa only [iteratedFDerivWithin_univ] using hB (v, x) ⟨hv, Set.mem_univ x⟩)).2 n z (Set.mem_univ z)
  have heq : (fun y => ((functionsQ F ζ hζ C s f.val).val
      (groupArchChart F ζ hζ y * g)).val.val 1) =ᶠ[nhds z]
      (fun y => ∫ x, A y x ∂KPGlobalTorusPeriodizationInverse.probabilityHaar F ζ hζ C) := by
    filter_upwards [hU.mem_nhds hzU] with y hy
    change (twistedQ F ζ hζ C s (f.val.val (groupArchChart F ζ hζ y * g))).val.val 1 = _
    rw [← TorusChartTransport.weightedChart_integral_eq F ζ hζ C s r f.val g y]
    simp_all
  have hset : groupArchDomain F =ᶠ[nhds z] (Set.univ : Set (GroupArch F)) :=
    Filter.eventually_of_mem ((groupArchDomain_open F).mem_nhds hz)
      (fun y hy => by simp [hy])
  rw [iteratedFDerivWithin_congr_set (𝕜 := ℝ)
    (f := fun y => ((functionsQ F ζ hζ C s f.val).val
      (groupArchChart F ζ hζ y * g)).val.val 1) hset n]
  refine ((heq.filter_mono (nhdsWithin_le_nhds (s := Set.univ))).iteratedFDerivWithin_eq
    (𝕜 := ℝ) heq.eq_of_nhds n).trans (hj.trans ?_)
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  have hex : (fun y => A y x) =ᶠ[nhds z]
      (fun y => TorusChartTransport.weightedChartIntegrand F ζ hζ C s r f.val g y x) :=
    Filter.eventually_of_mem (hU.mem_nhds hzU) (fun y hy => hEq y hy x)
  change iteratedFDerivWithin ℝ n (fun y => A y x) Set.univ z = _
  exact ((hex.filter_mono (nhdsWithin_le_nhds (s := Set.univ))).iteratedFDerivWithin_eq
    (𝕜 := ℝ) hex.eq_of_nhds n).trans
    (iteratedFDerivWithin_congr_set (𝕜 := ℝ)
      (f := fun y => TorusChartTransport.weightedChartIntegrand F ζ hζ C s r f.val g y x)
      hset.symm n)

theorem functionsQ_jet_le_of_integral_jets (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (r : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C)
    (g : G F ζ hζ) (n : ℕ)
    (K : KPGlobalTorusFunctionData.JetCompact (groupArchDomain F))
    (f : InducedLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J)
    (B : ℝ) (hB : 0 ≤ B)
    (hjets : ∀ z ∈ K.set,
      iteratedFDerivWithin ℝ n
        (fun y => ((functionsQ F ζ hζ C s f.val).val
          (groupArchChart F ζ hζ y * g)).val.val 1) (groupArchDomain F) z =
      ∫ x, iteratedFDerivWithin ℝ n
        (fun y => TorusChartTransport.weightedChartIntegrand F ζ hζ C s r f.val g y x)
        (groupArchDomain F) z
        ∂KPGlobalTorusPeriodizationInverse.probabilityHaar F ζ hζ C)
    (hbound : ∀ z ∈ K.set, ∀ x,
      ‖iteratedFDerivWithin ℝ n
        (fun y => TorusChartTransport.weightedChartIntegrand F ζ hζ C s r f.val g y x)
        (groupArchDomain F) z‖ ≤ B) :
    inducedJet F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J g n K
      (levelMap F ζ hζ _ _ (functionsQ F ζ hζ C s)
        (functionsQ_preserves_level F ζ hζ C s) J f) ≤ B := by
  change inducedJetBound F ζ hζ _ J g n K _ ≤ B
  unfold inducedJetBound
  by_cases hK : K.set.Nonempty
  · apply csSup_le (hK.image _)
    rintro _ ⟨z, hz, rfl⟩
    change ‖iteratedFDerivWithin ℝ n
      (fun y => ((functionsQ F ζ hζ C s f.val).val
        (groupArchChart F ζ hζ y * g)).val.val 1) (groupArchDomain F) z‖ ≤ B
    rw [hjets z hz]
    simpa using norm_integral_le_of_norm_le_const
      (μ := KPGlobalTorusPeriodizationInverse.probabilityHaar F ζ hζ C)
      (Filter.Eventually.of_forall (hbound z hz))
  · have hE : K.set = ∅ := Set.not_nonempty_iff_eq_empty.mp hK
    simpa only [hE, Set.image_empty, Real.sSup_empty] using hB

theorem functionsQ_level_continuous (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    @Continuous
      (InducedLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J)
      (InducedLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J)
      (inducedLevelTopology F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J)
      (inducedLevelTopology F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J)
      (levelMap F ζ hζ _ _ (functionsQ F ζ hζ C s)
        (functionsQ_preserves_level F ζ hζ C s) J) := by
  apply functionsQ_level_continuous_of_isBounded F ζ hζ C s J
  apply Seminorm.IsBounded.of_real
  intro i
  let r := Classical.choice
    (KPGlobalTorusPeriodizationInverse.averaging_representatives_exist F ζ hζ C)
  let h := TorusChartTransport.weightedChart_source_jet_bound F ζ hζ C s J r i.1 i.2.1 i.2.2
  let S := h.choose
  let B := h.choose_spec.choose
  have hB : 0 ≤ B := h.choose_spec.choose_spec.1
  have hb := h.choose_spec.choose_spec.2
  refine ⟨S, B, fun f => ?_⟩
  apply functionsQ_jet_le_of_integral_jets F ζ hζ C s J r i.1 i.2.1 i.2.2 f
  · exact mul_nonneg hB (apply_nonneg _ _)
  · intro z hz
    exact functionsQ_chart_integral_jets F ζ hζ C s J r f i.1 i.2.1 z (i.2.2.inside hz)
  · exact hb f

end
end DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction

end

section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport
noncomputable section
open KPGlobalTorusBorelTwistCompatibilityBorelInduction
set_option maxRecDepth 2000
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

local instance smoothTopology3 (P : Polarization F ζ hζ) :
    TopologicalSpace (Smooth F ζ hζ P) :=
  KPGlobalTorusFunctionData.torusSmoothTopology F ζ hζ P

local instance inducedTop3 (P : Polarization F ζ hζ) : TopologicalSpace (Induced F ζ hζ P) :=
  inducedTopology F ζ hζ P

local instance inducedFunctionsAddGroup3 (P : Polarization F ζ hζ) :
    AddCommGroup (InducedFunctions F ζ hζ P) := @Submodule.addCommGroup ℂ (G F ζ hζ → Smooth F ζ hζ P)
      inferInstance inferInstance inferInstance (InducedFunctions F ζ hζ P)
local instance inducedLevelAddGroup3 (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    AddCommGroup (InducedLevel F ζ hζ P J) := @Submodule.addCommGroup ℂ (InducedFunctions F ζ hζ P)
      inferInstance inferInstance inferInstance (InducedLevel F ζ hζ P J)
local instance inducedAddGroup3 (P : Polarization F ζ hζ) :
    AddCommGroup (Induced F ζ hζ P) := @Submodule.addCommGroup ℂ (InducedFunctions F ζ hζ P)
      inferInstance inferInstance inferInstance (Induced F ζ hζ P)

def borelP (C : ModelData F ζ hζ) (s : ℂ) :
    Induced F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) →L[ℂ]
      Induced F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) :=
  ⟨unionMap F ζ hζ _ _ (functionsP F ζ hζ C s)
      (functionsP_preserves_level F ζ hζ C s),
    unionMap_continuous F ζ hζ _ _ (functionsP F ζ hζ C s)
      (functionsP_preserves_level F ζ hζ C s)
      (functionsP_level_continuous F ζ hζ C s)⟩

def borelQ (C : ModelData F ζ hζ) (s : ℂ) :
    Induced F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) →L[ℂ]
      Induced F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) :=
  ⟨unionMap F ζ hζ _ _ (functionsQ F ζ hζ C s)
      (functionsQ_preserves_level F ζ hζ C s),
    unionMap_continuous F ζ hζ _ _ (functionsQ F ζ hζ C s)
      (functionsQ_preserves_level F ζ hζ C s)
      (functionsQ_level_continuous F ζ hζ C s)⟩

 theorem borelP_fiberwise (C : ModelData F ζ hζ) (s : ℂ)
    (f : Induced F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s)) (g : G F ζ hζ) :
    (borelP F ζ hζ C s f).val.val g = twistedP F ζ hζ C s (f.val.val g) := by rfl

 theorem borelQ_fiberwise (C : ModelData F ζ hζ) (s : ℂ)
    (f : Induced F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s)) (g : G F ζ hζ) :
    (borelQ F ζ hζ C s f).val.val g = twistedQ F ζ hζ C s (f.val.val g) := by rfl
