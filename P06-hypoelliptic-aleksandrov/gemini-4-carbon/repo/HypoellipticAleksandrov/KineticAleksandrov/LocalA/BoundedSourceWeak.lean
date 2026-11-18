module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceWeakMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelWeak

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Evolution Occupation
open scoped ENNReal Topology
section
open MeasureTheory Set
open scoped ENNReal ProbabilityTheory
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- The past moving cylinder in product coordinates used by the source-action measure. -/
def boundedSourcePast (Ω : Set (PDE.Vec d)) (γ : ℝ → PDE.Vec d) (T : ℝ) :
    Set (ℝ × EvolutionAmbientState d) :=
  {q | q.1 < T ∧ q.2.1 ∈ movingDomain Ω γ q.1}

/-- The source past set is Borel. -/
theorem measurableSet_boundedSourcePast (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (T : ℝ) : MeasurableSet (boundedSourcePast Ω γ T) := by
  have ht : MeasurableSet {q : ℝ × EvolutionAmbientState d | q.1 < T} :=
    measurableSet_lt measurable_fst measurable_const
  have hp : MeasurableSet {q : ℝ × EvolutionAmbientState d | q.2.1 - γ q.1 ∈ Ω} :=
    hΩ.preimage (measurable_snd.fst.sub (hγ.measurable.comp measurable_fst))
  convert ht.inter hp using 1
  ext q
  simp [boundedSourcePast, movingDomain, PDE.mem_translateSet_iff_sub_mem]

/-- An open moving domain gives an open past cylinder in product coordinates. -/
theorem isOpen_boundedSourcePast (hΩ : IsOpen Ω) (hγ : Continuous γ) (T : ℝ) :
    IsOpen (boundedSourcePast Ω γ T) := by
  have ht : IsOpen {q : ℝ × EvolutionAmbientState d | q.1 < T} :=
    isOpen_lt continuous_fst continuous_const
  have hp : IsOpen {q : ℝ × EvolutionAmbientState d | q.2.1 - γ q.1 ∈ Ω} :=
    hΩ.preimage (continuous_snd.fst.sub (hγ.comp continuous_fst))
  convert ht.inter hp using 1
  ext q
  simp [boundedSourcePast, movingDomain, PDE.mem_translateSet_iff_sub_mem]


end
variable {d : ℕ}

/-- The positive part of a compact test defines a positive source measure. -/
def sourcePositiveMeasure (Λ : ℝ × EvolutionAmbientState d → ℝ) :
    Measure (ℝ × EvolutionAmbientState d) :=
  volume.withDensity (fun q => ENNReal.ofReal (max (Λ q) 0))

/-- Integrable positive parts give finite test weights. -/
theorem sourcePositiveMeasure_isFinite (Λ : ℝ × EvolutionAmbientState d → ℝ)
    (hΛ : Continuous Λ) (hc : HasCompactSupport Λ) :
    IsFiniteMeasure (sourcePositiveMeasure Λ) := by
  have hint : Integrable (fun q => max (Λ q) 0) :=
    (hΛ.max continuous_const).integrable_of_hasCompactSupport
      (hc.comp_left (g := fun r => max r 0) (max_self 0))
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun q => le_max_right (Λ q) 0)]
  exact ENNReal.ofReal_ne_top

/-- The same test weight on physical starting points uses the coordinate equivalence. -/
def sourcePositiveStartMeasure (Λ : ℝ × EvolutionAmbientState d → ℝ) :
    Measure (KineticPoint d) :=
  (sourcePositiveMeasure Λ).map (KineticPoint.equivProd d).symm

/-- Positive compact test weights are finite also in the starting-point carrier. -/
theorem sourcePositiveStartMeasure_isFinite (Λ : ℝ × EvolutionAmbientState d → ℝ)
    (hΛ : Continuous Λ) (hc : HasCompactSupport Λ) :
    IsFiniteMeasure (sourcePositiveStartMeasure Λ) := by
  have := sourcePositiveMeasure_isFinite Λ hΛ hc
  unfold sourcePositiveStartMeasure
  infer_instance

/-- Integrals against positive test weights are the ordinary weighted integrals. -/
theorem integral_sourcePositiveMeasure (Λ : ℝ × EvolutionAmbientState d → ℝ)
    (hΛ : Measurable Λ) (f : ℝ × EvolutionAmbientState d → ℝ) :
    (∫ q, f q ∂sourcePositiveMeasure Λ) = ∫ q, max (Λ q) 0 * f q := by
  unfold sourcePositiveMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    ((hΛ.max measurable_const).ennreal_ofReal)
    (Filter.Eventually.of_forall fun q => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (le_max_right _ _), smul_eq_mul]

/-- A starting-coordinate weight integrates by the literal coordinate permutation. -/
theorem integral_sourcePositiveStartMeasure (Λ : ℝ × EvolutionAmbientState d → ℝ)
    (hΛ : Measurable Λ) (f : KineticPoint d → ℝ) (hf : Measurable f) :
    (∫ p, f p ∂sourcePositiveStartMeasure Λ) =
      ∫ q, max (Λ q) 0 * f ⟨q.1, q.2.1, q.2.2⟩ := by
  unfold sourcePositiveStartMeasure
  rw [integral_map (KineticPoint.measurable_equivProd_symm d).aemeasurable
    hf.aestronglyMeasurable]
  exact integral_sourcePositiveMeasure Λ hΛ _

/-- The finite-window source action is Borel as a function of starting point. -/
theorem measurable_duhamel_window {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (g : KineticPoint d → ℝ) (hg : Measurable g) (a T : ℝ) :
    Measurable (fun p => ∫ r in Ioo a T, duhamelIntegrand K g p r) :=
  ((measurable_duhamelIntegrand K hΩ hγ g hg).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioo a T))).measurable

/-- Compact-test source weights reproduce the weighted Duhamel window integral. -/
theorem integral_boundedSourceAction_positive_weight
    {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (Λ : ℝ × EvolutionAmbientState d → ℝ) (hΛ : Continuous Λ)
    (hc : HasCompactSupport Λ) (a T : ℝ)
    (g : KineticPoint d → ℝ) (hg : Measurable g)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ p, |g p| ≤ M) :
    (∫ q, g ⟨q.1, q.2.1, q.2.2⟩
      ∂boundedSourceActionMeasure K (sourcePositiveStartMeasure Λ) a T) =
      ∫ q, max (Λ q) 0 *
        (∫ r in Ioo a T, duhamelIntegrand K g ⟨q.1, q.2.1, q.2.2⟩ r) := by
  have := sourcePositiveStartMeasure_isFinite Λ hΛ hc
  rw [integral_boundedSourceActionMeasure K hΩ hγ _ a T g hg M hM hb]
  exact integral_sourcePositiveStartMeasure Λ hΛ.measurable _
    (measurable_duhamel_window K hΩ hγ g hg a T)

/-- A compact test's lower time bound identifies its action with the Duhamel potential. -/
theorem integral_boundedSourceAction_positive_potential
    {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (Λ : ℝ × EvolutionAmbientState d → ℝ) (hΛ : Continuous Λ)
    (hc : HasCompactSupport Λ) (a T : ℝ) (hfloor : ∀ q, Λ q ≠ 0 → a ≤ q.1)
    (g : KineticPoint d → ℝ) (hg : Measurable g)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ p, |g p| ≤ M) :
    (∫ q, g ⟨q.1, q.2.1, q.2.2⟩
      ∂boundedSourceActionMeasure K (sourcePositiveStartMeasure Λ) a T) =
      ∫ q, max (Λ q) 0 * duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩ := by
  rw [integral_boundedSourceAction_positive_weight K hΩ hγ Λ hΛ hc a T g hg M hM hb]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro q
  change max (Λ q) 0 *
    (∫ r in Ioo a T, duhamelIntegrand K g ⟨q.1, q.2.1, q.2.2⟩ r) =
      max (Λ q) 0 * duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩
  by_cases hq : Λ q = 0
  · simp [hq, max_self]
  · rw [duhamelPotential_eq_integral_window K g ⟨q.1, q.2.1, q.2.2⟩ (hfloor q hq)]

variable {d : ℕ}


/-- Positive-part weights remain continuous with compact support. -/
theorem positive_weight_compact (Λ : ℝ × EvolutionAmbientState d → ℝ)
    (hΛ : Continuous Λ) (hc : HasCompactSupport Λ) :
    Continuous (fun q => max (Λ q) 0) ∧ HasCompactSupport (fun q => max (Λ q) 0) :=
  ⟨hΛ.max continuous_const, hc.comp_left (g := fun r => max r 0) (max_self 0)⟩

/-- Positive and negative compact weights recover the signed weighted integral. -/
theorem integral_positive_negative_weight_sub
    (Λ : ℝ × EvolutionAmbientState d → ℝ) (hΛ : Continuous Λ)
    (hc : HasCompactSupport Λ) (f : ℝ × EvolutionAmbientState d → ℝ)
    (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ q, Λ q ≠ 0 → |f q| ≤ C) :
    (∫ q, max (Λ q) 0 * f q) - (∫ q, max (-Λ q) 0 * f q) = ∫ q, Λ q * f q  := by
  have integrable_compact_weight_bounded (Λ : ℝ × EvolutionAmbientState d → ℝ) (hΛ : Continuous Λ) (hc : HasCompactSupport Λ) (_hC : 0 ≤ C) (hb : ∀ q, Λ q ≠ 0 → |f q| ≤ C) :
      Integrable (fun q => Λ q * f q) := by
    have hi : Integrable (fun q => C * ‖Λ q‖) :=
      (hΛ.integrable_of_hasCompactSupport hc).norm.const_mul C
    apply hi.mono' (hΛ.measurable.mul hf).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro q
    change ‖Λ q * f q‖ ≤ C * ‖Λ q‖
    rw [norm_mul, Real.norm_eq_abs (f q)]
    by_cases hq : Λ q = 0
    · simp [hq, norm_zero, le_refl]
    · exact (mul_le_mul_of_nonneg_left (hb q hq) (norm_nonneg _)).trans_eq (mul_comm _ _)
  obtain ⟨hpcont, hpcomp⟩ := positive_weight_compact Λ hΛ hc
  obtain ⟨hncont, hncomp⟩ := positive_weight_compact (fun q => -Λ q) hΛ.neg hc.neg
  have hp :=
    integrable_compact_weight_bounded _ hpcont hpcomp hC (fun q hq => by
      apply hb q
      intro hz
      exact hq (by simp only [hz, max_self]))
  have hn :=
    integrable_compact_weight_bounded _ hncont hncomp hC (fun q hq => by
      apply hb q
      intro hz
      exact hq (by simp [hz, max_self]))
  rw [← integral_sub hp hn]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro q
  change max (Λ q) 0 * f q - max (-Λ q) 0 * f q = Λ q * f q
  rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]

section
open MeasureTheory Set
open scoped ENNReal
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- Positive test weights vanish outside every set containing their closed support. -/
theorem sourcePositiveMeasure_compl_eq_zero
    (Ψ : ℝ × EvolutionAmbientState d → ℝ) {U : Set (ℝ × EvolutionAmbientState d)}
    (hU : MeasurableSet U) (hs : tsupport Ψ ⊆ U) : sourcePositiveMeasure Ψ Uᶜ = 0 := by
  rw [sourcePositiveMeasure, withDensity_apply _ hU.compl]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem hU.compl] with q hq
  rw [(image_eq_zero_of_notMem_tsupport (fun h => hq (hs h))), max_self, ENNReal.ofReal_zero]
  rfl

/-- Negating a compact weight preserves its closed support. -/
theorem tsupport_neg_weight (Ψ : ℝ × EvolutionAmbientState d → ℝ) :
    tsupport (fun q => -Ψ q) = tsupport Ψ := by
  apply congrArg closure
  ext q
  change (-Ψ q ≠ 0) ↔ (Ψ q ≠ 0)
  exact neg_ne_zero

/-- The two positive source measures in a signed weak identity. -/
def weakSourcePositiveMeasure (K : MovingFiberKernel Ω γ)
    (Λ Ψ : ℝ × EvolutionAmbientState d → ℝ) (a T : ℝ) :
    Measure (ℝ × EvolutionAmbientState d) :=
  boundedSourceActionMeasure K (sourcePositiveStartMeasure Λ) a T + sourcePositiveMeasure Ψ



end
section
open MeasureTheory Set
open Evolution Occupation
open scoped Topology
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- Product-coordinate test sources retain their closed support under the homeomorphism. -/
theorem boundedSourceTest_support (φ : ℝ × EvolutionAmbientState d → ℝ) :
    tsupport (φ ∘ KineticPoint.equivProd d) =
      (KineticPoint.equivProd d) ⁻¹' tsupport φ := by
  change tsupport (φ ∘ KineticPoint.homeomorphProd d) = _
  rw [tsupport_comp_eq_preimage]
  rfl

/-- The smooth Duhamel theorem gives the exact product-coordinate test identity. -/
theorem duhamel_smooth_product_identity (hΩa : IsAdmissibleEvolutionDomain Ω)
    (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (T : ℝ)
    {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ T)
    (φ : ℝ × EvolutionAmbientState d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ boundedSourcePast Ω γ T)
    (hφr : ∀ q, 0 ≤ φ q ∧ φ q ≤ 1) :
    (∫ q, transportedAdjoint B b ψ (packQ d q) *
      duhamelPotential K T (φ ∘ KineticPoint.equivProd d) ⟨q.1, q.2.1, q.2.2⟩) =
      -(∫ q, ψ (packQ d q) * φ q) := by
  let g := φ ∘ KineticPoint.equivProd d
  have hgn : ∀ p, 0 ≤ g p := fun p => (hφr _).1
  have hgU : tsupport g ⊆ evolutionPastOpenCylinder Ω γ T := by
    intro p hp
    rw [boundedSourceTest_support] at hp
    exact hφU hp
  have h := duhamel_weak_identity hΩa hΩ hγ B b S K hreal hB hBs hb g hgn
    (hφ.continuous.comp (KineticPoint.homeomorphProd d).continuous) (hφc.comp_homeomorph (KineticPoint.homeomorphProd d)) (hφ) T hgU hψ hc hψs
  rw [integral_evolution_eq_prod, integral_evolution_eq_prod] at h
  simp at h
  have hleft : (∫ q, transportedAdjoint B b ψ (packQ d q) *
      duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩) =
      ∫ q, duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩ *
        transportedAdjoint B b ψ (packQ d q) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun q => mul_comm _ _
  have hright : (∫ q, φ q * ψ (packQ d q)) = ∫ q, ψ (packQ d q) * φ q := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun q => mul_comm _ _
  exact hleft.trans (h.trans (congrArg Neg.neg hright))


/-- Compact weak tests have a uniform lower time bound in product coordinates. -/
theorem exists_boundedSource_test_floor (Λ : ℝ × EvolutionAmbientState d → ℝ)
    (hc : HasCompactSupport Λ) (T : ℝ) :
    ∃ a : ℝ, a < T ∧ ∀ q, Λ q ≠ 0 → a ≤ q.1 := by
  obtain ⟨lower, hLower⟩ := (hc.image continuous_fst).bddBelow
  refine ⟨min lower (T - 1), ?_, ?_⟩
  · exact (min_le_right lower (T - 1)).trans_lt (by linarith)
  · intro q hq
    exact (min_le_left lower (T - 1)).trans (hLower ⟨q, subset_tsupport Λ hq, rfl⟩)

end
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- The bounded-source weak identity in product coordinates. -/
theorem duhamel_bounded_product_identity (hΩa : IsAdmissibleEvolutionDomain Ω)
    (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (g : KineticPoint d → ℝ) (hg : Measurable g)
    (M : ℝ) (hM : 0 ≤ M) (hgb : ∀ p, |g p| ≤ M) (T : ℝ)
    {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ T) :
    (∫ q, transportedAdjoint B b ψ (packQ d q) *
      duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩) =
      -(∫ q, ψ (packQ d q) * g ⟨q.1, q.2.1, q.2.2⟩)    := by
  let weakSourceNegativeMeasure (Λ Ψ : ℝ × EvolutionAmbientState d → ℝ) (a : ℝ) (T : ℝ) :=
    weakSourcePositiveMeasure K (fun q => -Λ q) (fun q => -Ψ q) a T
  have boundedSourceAdjoint_support (ψ : EvolutionVec d → ℝ) :
      tsupport (transportedAdjoint B b ψ) ⊆ tsupport ψ := by
    apply closure_minimal
    · intro x hx
      by_contra hnot
      exact hx (transportedAdjoint_eq_zero_of_notMem_tsupport ψ hnot)
    · exact isClosed_tsupport ψ
  have weakSourceMeasures_eq_of_smooth_identity (hΩ : IsOpen Ω) (hγ : Continuous γ) (Λ Ψ : ℝ × EvolutionAmbientState d → ℝ) (hΛ : Continuous Λ) (hΛc : HasCompactSupport Λ) (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ) (a : ℝ) (T : ℝ) (haT : a < T) (hfloor : ∀ q, Λ q ≠ 0 → a ≤ q.1) (hΛU : tsupport Λ ⊆ boundedSourcePast Ω γ T) (hΨU : tsupport Ψ ⊆ boundedSourcePast Ω γ T) (hidentity : ∀ φ : ℝ × EvolutionAmbientState d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ boundedSourcePast Ω γ T → (∀ q, 0 ≤ φ q ∧ φ q ≤ 1) →
      (∫ q, Λ q * duhamelPotential K T (φ ∘ KineticPoint.equivProd d)
        ⟨q.1, q.2.1, q.2.2⟩) = -(∫ q, Ψ q * φ q)) :
      weakSourcePositiveMeasure K Λ Ψ a T = weakSourceNegativeMeasure Λ Ψ a T := by
    have boundedSourceActionMeasure_compl_past (hΩ : MeasurableSet Ω) (hγ : Continuous γ) (ν : Measure (KineticPoint d)) [IsFiniteMeasure ν] (a : ℝ) (T : ℝ) :
        boundedSourceActionMeasure K ν a T (boundedSourcePast Ω γ T)ᶜ = 0 := by
      let ρ := ν.prod (volume.restrict (Ioo a T))
      let η := ρ.comap ((↑) : BoundedSourcePair Ω γ → KineticPoint d × ℝ)
      let κ := boundedSourcePairKernel K
      have : ProbabilityTheory.IsFiniteKernel κ := by
        dsimp only [κ, boundedSourcePairKernel]
        infer_instance
      have hU := measurableSet_boundedSourcePast hΩ hγ T
      have hr : ∀ᵐ q ∂ρ, q.2 ∈ Ioo a T :=
        (Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.preimage measurable_snd)).2
          (Filter.Eventually.of_forall fun _ => ae_restrict_mem measurableSet_Ioo)
      have hrη : ∀ᵐ q ∂η, q.1.2 ∈ Ioo a T := by
        have hmapped : ∀ᵐ q ∂Measure.map Subtype.val η, q.2 ∈ Ioo a T := by
          dsimp only [η]
          rw [map_comap_subtype_coe (measurableSet_boundedSourcePairSet hΩ hγ)]
          exact ae_restrict_of_ae hr
        exact ae_of_ae_map (p := fun q : KineticPoint d × ℝ => q.2 ∈ Ioo a T)
          measurable_subtype_coe.aemeasurable hmapped
      have houtput : ∀ᵐ q ∂η.compProd κ,
          boundedSourceOutput q ∈ boundedSourcePast Ω γ T := by
        apply (Measure.ae_compProd_iff (hU.preimage measurable_boundedSourceOutput)).2
        filter_upwards [hrη] with q hq
        have hstate : ∀ᵐ w ∂κ q,
            w ∈ evolutionStateSet Ω γ q.1.2 := by
          change ∀ᵐ w ∂K.master (boundedSourcePairQuery q),
            w ∈ evolutionStateSet Ω γ q.1.2
          rw [← K.terminal_support (boundedSourcePairQuery q)]
          exact ae_restrict_mem (measurableSet_evolutionStateSet hΩ _)
        filter_upwards [hstate] with w hw
        exact ⟨hq.2, hw.1⟩
      change (Measure.map boundedSourceOutput (η.compProd κ)) _ = 0
      rw [measure_eq_zero_iff_ae_notMem]
      simpa using
        (ae_map_iff (p := fun q => q ∈ boundedSourcePast Ω γ T)
          measurable_boundedSourceOutput.aemeasurable hU).2 houtput
    have hΛstart := sourcePositiveStartMeasure_isFinite Λ hΛ hΛc
    have hΛnstart := sourcePositiveStartMeasure_isFinite (fun q => -Λ q) hΛ.neg hΛc.neg
    have hΨfin := sourcePositiveMeasure_isFinite Ψ hΨ hΨc
    have hΨnfin := sourcePositiveMeasure_isFinite (fun q => -Ψ q) hΨ.neg hΨc.neg
    let μ := boundedSourceActionMeasure K (sourcePositiveStartMeasure Λ) a T
    let μn := boundedSourceActionMeasure K (sourcePositiveStartMeasure (fun q => -Λ q)) a T
    have hfin : IsFiniteMeasure μ := by dsimp only [μ]; infer_instance
    have hnfin : IsFiniteMeasure μn := by dsimp only [μn]; infer_instance
    change μ + sourcePositiveMeasure Ψ = μn + sourcePositiveMeasure (fun q => -Ψ q)
    have hU := measurableSet_boundedSourcePast hΩ.measurableSet hγ T
    apply measure_eq_of_smooth_integral_eq (isOpen_boundedSourcePast hΩ hγ T)
    · rw [Measure.add_apply, boundedSourceActionMeasure_compl_past hΩ.measurableSet hγ,
        sourcePositiveMeasure_compl_eq_zero Ψ hU hΨU, add_zero]
    · rw [Measure.add_apply, boundedSourceActionMeasure_compl_past hΩ.measurableSet hγ,
        sourcePositiveMeasure_compl_eq_zero (fun q => -Ψ q) hU
          (by rw [tsupport_neg_weight]; exact hΨU), add_zero]
    intro φ hφ hφc hφU hφr
    have hφb : ∀ q, |φ q| ≤ 1 := fun q => by
      rw [abs_of_nonneg (hφr q).1]
      exact (hφr q).2
    have hφm := hφ.continuous.measurable
    have hφμ := integrable_bounded_real μ φ hφm 1 hφb
    have hφμn := integrable_bounded_real μn φ hφm 1 hφb
    have hφΨ := integrable_bounded_real (sourcePositiveMeasure Ψ) φ hφm 1 hφb
    have hφΨn := integrable_bounded_real (sourcePositiveMeasure (fun q => -Ψ q)) φ hφm 1 hφb
    rw [integral_add_measure hφμ hφΨ, integral_add_measure hφμn hφΨn]
    let g := φ ∘ KineticPoint.equivProd d
    have hgm := hφm.comp (KineticPoint.measurable_equivProd d)
    have hgb : ∀ p, |g p| ≤ 1 := fun p => hφb _
    have hfloorN : ∀ q, -Λ q ≠ 0 → a ≤ q.1 := fun q hq => hfloor q (neg_ne_zero.mp hq)
    have hact := integral_boundedSourceAction_positive_potential K hΩ.measurableSet hγ
      Λ hΛ hΛc a T hfloor g hgm 1 zero_le_one hgb
    have hactn := integral_boundedSourceAction_positive_potential K hΩ.measurableSet hγ
      (fun q => -Λ q) hΛ.neg hΛc.neg a T hfloorN g hgm 1 zero_le_one hgb
    have hbase := integral_sourcePositiveMeasure Ψ hΨ.measurable φ
    have hbasen := integral_sourcePositiveMeasure (fun q => -Ψ q) hΨ.neg.measurable φ
    have hWm : Measurable (fun q : ℝ × EvolutionAmbientState d =>
        duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩) :=
      (measurable_duhamelPotential K hΩ.measurableSet hγ T g hgm).comp
        (KineticPoint.measurable_equivProd_symm d)
    have hWb : ∀ q, Λ q ≠ 0 →
        |duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩| ≤ T - a := by
      intro q hq
      have ht := (hΛU (subset_tsupport Λ hq)).1
      have hpoint : |duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩| ≤ T - q.1 := by
        simpa using (abs_duhamelPotential_le K g 1 zero_le_one hgb ⟨q.1, q.2.1, q.2.2⟩ T ht.le)
      exact hpoint.trans (sub_le_sub_left (hfloor q hq) T)
    have hsub := integral_positive_negative_weight_sub Λ hΛ hΛc _ hWm
      (T - a) (sub_nonneg.mpr haT.le) hWb
    have hsubbase := integral_positive_negative_weight_sub Ψ hΨ hΨc φ hφm
      1 zero_le_one (fun q _ => hφb q)
    change (∫ q, φ q ∂μ) = _ at hact
    change (∫ q, φ q ∂μn) = _ at hactn
    rw [hact, hactn, hbase, hbasen]
    linarith only [hsub, hsubbase, (hidentity φ hφ hφc hφU hφr)]
  let Λ : ℝ × EvolutionAmbientState d → ℝ := fun q => transportedAdjoint B b ψ (packQ d q)
  let Ψ : ℝ × EvolutionAmbientState d → ℝ := fun q => ψ (packQ d q)
  have hΛ : Continuous Λ :=
    (contDiff_transportedAdjoint hB hb hψ).continuous.comp continuous_packQ
  have hΛc : HasCompactSupport Λ :=
    hasCompactSupport_comp_packQ (hasCompactSupport_transportedAdjoint hc)
  have hΨ : Continuous Ψ := hψ.continuous.comp continuous_packQ
  have hΨc : HasCompactSupport Ψ := hasCompactSupport_comp_packQ hc
  have hpreΨ : tsupport Ψ = (packQ d) ⁻¹' tsupport ψ := by
    change tsupport (ψ ∘ (evolutionProdCLE d).symm.toHomeomorph) = _
    rw [tsupport_comp_eq_preimage]
    rfl
  have hpreΛ : tsupport Λ = (packQ d) ⁻¹' tsupport (transportedAdjoint B b ψ) := by
    change tsupport (transportedAdjoint B b ψ ∘ (evolutionProdCLE d).symm.toHomeomorph) = _
    rw [tsupport_comp_eq_preimage]
    rfl
  have hΨU : tsupport Ψ ⊆ boundedSourcePast Ω γ T := by
    rw [hpreΨ]
    intro q hq
    have hp := hψs hq
    change evolutionHomeomorph d (packQ d q) ∈ evolutionPastOpenCylinder Ω γ T at hp
    rw [duhamel_homeomorph_packQ] at hp
    exact hp
  have hΛU : tsupport Λ ⊆ boundedSourcePast Ω γ T := by
    rw [hpreΛ]
    intro q hq
    apply hΨU
    rw [hpreΨ]
    exact boundedSourceAdjoint_support ψ hq
  obtain ⟨a, haT, hfloor⟩ := exists_boundedSource_test_floor Λ hΛc T
  have hΩo := isOpen_of_isAdmissibleEvolutionDomain hΩa
  have hΛstart := sourcePositiveStartMeasure_isFinite Λ hΛ hΛc
  have hΛnstart := sourcePositiveStartMeasure_isFinite (fun q => -Λ q) hΛ.neg hΛc.neg
  have hΨfin := sourcePositiveMeasure_isFinite Ψ hΨ hΨc
  have hΨnfin := sourcePositiveMeasure_isFinite (fun q => -Ψ q) hΨ.neg hΨc.neg
  let μ := boundedSourceActionMeasure K (sourcePositiveStartMeasure Λ) a T
  let μn := boundedSourceActionMeasure K (sourcePositiveStartMeasure (fun q => -Λ q)) a T
  have hfin : IsFiniteMeasure μ := by dsimp only [μ]; infer_instance
  have hnfin : IsFiniteMeasure μn := by dsimp only [μn]; infer_instance
  let f : ℝ × EvolutionAmbientState d → ℝ := fun q => g ⟨q.1, q.2.1, q.2.2⟩
  have hf := hg.comp (KineticPoint.measurable_equivProd_symm d)
  have hfb : ∀ q, |f q| ≤ M := fun q => hgb _
  have hμ := integrable_bounded_real μ f hf M hfb
  have hμn := integrable_bounded_real μn f hf M hfb
  have hν := integrable_bounded_real (sourcePositiveMeasure Ψ) f hf M hfb
  have hνn := integrable_bounded_real (sourcePositiveMeasure (fun q => -Ψ q)) f hf M hfb
  have hint : (∫ q, f q ∂(μ + sourcePositiveMeasure Ψ)) =
      ∫ q, f q ∂(μn + sourcePositiveMeasure (fun q => -Ψ q)) :=
    congrArg (fun ν => ∫ q, f q ∂ν) (weakSourceMeasures_eq_of_smooth_identity hΩo hγ Λ Ψ hΛ hΛc hΨ hΨc a T haT hfloor hΛU hΨU (fun φ hφ hφc hφU hφr => duhamel_smooth_product_identity hΩa hΩ hγ B b S K hreal hB hBs hb T hψ hc hψs φ hφ hφc hφU hφr))
  rw [integral_add_measure hμ hν, integral_add_measure hμn hνn] at hint
  have hfloorN : ∀ q, -Λ q ≠ 0 → a ≤ q.1 := fun q hq => hfloor q (neg_ne_zero.mp hq)
  have hact := integral_boundedSourceAction_positive_potential K hΩ hγ
    Λ hΛ hΛc a T hfloor g hg M hM hgb
  have hactn := integral_boundedSourceAction_positive_potential K hΩ hγ
    (fun q => -Λ q) hΛ.neg hΛc.neg a T hfloorN g hg M hM hgb
  change (∫ q, f q ∂μ) = _ at hact
  change (∫ q, f q ∂μn) = _ at hactn
  rw [hact, hactn, (integral_sourcePositiveMeasure Ψ hΨ.measurable f), (integral_sourcePositiveMeasure (fun q => -Ψ q) hΨ.neg.measurable f)] at hint
  let W : ℝ × EvolutionAmbientState d → ℝ :=
    fun q => duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩
  have hWm :=
    (measurable_duhamelPotential K hΩ hγ T g hg).comp
      (KineticPoint.measurable_equivProd_symm d)
  have hWb : ∀ q, Λ q ≠ 0 → |W q| ≤ (T - a) * M := by
    intro q hq
    exact (abs_duhamelPotential_le K g M hM hgb ⟨q.1, q.2.1, q.2.2⟩ T ((hΛU (subset_tsupport Λ hq)).1).le).trans
      (mul_le_mul_of_nonneg_right (sub_le_sub_left (hfloor q hq) T) hM)
  have hsub := integral_positive_negative_weight_sub Λ hΛ hΛc W hWm
    ((T - a) * M) (mul_nonneg (sub_nonneg.mpr haT.le) hM) hWb
  change (∫ q, Λ q * W q) = -(∫ q, Ψ q * f q)
  linarith only [hint, hsub, (integral_positive_negative_weight_sub Ψ hΨ hΨc f hf M hM (fun q _ => hfb q))]

/-- The signed bounded Borel identity in the existing transported coordinates. -/
theorem duhamel_bounded_weak_identity (hΩa : IsAdmissibleEvolutionDomain Ω)
    (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (g : KineticPoint d → ℝ) (hg : Measurable g)
    (M : ℝ) (hM : 0 ≤ M) (hgb : ∀ p, |g p| ≤ M) (T : ℝ)
    {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ T) :
    (∫ q, transportedAdjoint B b ψ q *
      duhamelPotential K T g (evolutionHomeomorph d q)) =
      -(∫ q, ψ q * g (evolutionHomeomorph d q)) := by
  rw [integral_evolution_eq_prod, integral_evolution_eq_prod]
  simp
  exact duhamel_bounded_product_identity hΩa hΩ hγ B b S K hreal hB hBs hb
    g hg M hM hgb T hψ hc hψs

/-- Bounded Borel sources give the existing kinetic weak-solution carrier. -/
theorem duhamel_bounded_isKineticWeakTransportedSolution
    (hΩa : IsAdmissibleEvolutionDomain Ω) (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (g : KineticPoint d → ℝ) (hg : Measurable g)
    (M : ℝ) (hM : 0 ≤ M) (hgb : ∀ p, |g p| ≤ M) (T : ℝ) :
    IsKineticWeakTransportedSolution B b (evolutionPastOpenCylinder Ω γ T)
      (duhamelPotential K T g) (fun p => -g p) := by
  have hbound : Continuous (fun q =>
      |T - (evolutionHomeomorph d q).time| * M) :=
    (continuous_const.sub (continuous_time.comp
      (evolutionHomeomorph d).continuous)).abs.mul continuous_const
  have hloc := hbound.continuousOn.locallyIntegrableOn
    (μ := (volume : Measure (EvolutionVec d))) ((isOpen_duhamelCylinder (isOpen_of_isAdmissibleEvolutionDomain hΩa) hγ T).preimage (evolutionHomeomorph d).continuous).measurableSet
  have hW := hloc.mono ((measurable_duhamelPotential K hΩ hγ T g hg).comp (evolutionHomeomorph d).continuous.measurable).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (abs_nonneg _) hM)]
      exact abs_duhamelPotential_le_abs_time K g M hM hgb _ T)
  apply (isWeakTransportedSolution_comp_iff B b _ _ _).1
  refine ⟨hW, fun ψ hψ hc hs => ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · simp [neg_mul, integral_neg]
    simpa only [mul_comm] using (duhamel_bounded_weak_identity hΩa hΩ hγ B b S K hreal hB hBs hb g hg M hM hgb T hψ hc hs)
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
  · intro x hx
    rw [transportedAdjoint_eq_zero_of_notMem_tsupport ψ (fun h => hx (hs h)), mul_zero]

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

