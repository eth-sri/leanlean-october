module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DensityIntegral
public import Mathlib.MeasureTheory.Measure.Complex
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.MeasurableIntegral
public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierGreen

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Green
open MeasureTheory Set HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal NNReal ProbabilityTheory
section

open MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal NNReal ProbabilityTheory

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- The complex measure of the half-time evolution. -/
def evolvedMeasure (μ : Measure X) (κ : ProbabilityTheory.Kernel X Y) (ph : Y → ℂ) (π : Y → Z) :
    VectorMeasure Z ℂ :=
  (((μ ⊗ₘ κ).snd).withDensityᵥ ph).map π

/-- The fibre measure at `x`. -/
def fibreMeasure (κ : ProbabilityTheory.Kernel X Y) (ph : Y → ℂ) (π : Y → Z) (x : X) :
    VectorMeasure Z ℂ :=
  ((κ x).withDensityᵥ ph).map π

variable (μ : Measure X) [IsFiniteMeasure μ] (κ : ProbabilityTheory.Kernel X Y)
  [ProbabilityTheory.IsFiniteKernel κ] (ph : Y → ℂ) (π : Y → Z)

/-- Integrals against the second marginal of a kernel product. -/
lemma integral_snd_compProd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Y → E) (hf : Integrable f (μ ⊗ₘ κ).snd) :
    ∫ y, f y ∂(μ ⊗ₘ κ).snd = ∫ x, ∫ y, f y ∂κ x ∂μ := by
  have hsnd : Measurable (Prod.snd : X × Y → Y) := measurable_snd
  have hf' : Integrable (fun p => f p.2) (μ ⊗ₘ κ) := by
    rw [Measure.snd] at hf
    exact (integrable_map_measure hf.aestronglyMeasurable hsnd.aemeasurable).1 hf
  have hf'' : AEStronglyMeasurable f (Measure.map Prod.snd (μ ⊗ₘ κ)) := by
    rw [Measure.snd] at hf
    exact hf.aestronglyMeasurable
  rw [Measure.snd, integral_map hsnd.aemeasurable hf'', Measure.integral_compProd hf']


/-- Pairing of bounded Borel `h` with `η`, as an iterated kernel integral. -/
lemma evolved_integral (hph : Measurable ph) (hph1 : ∀ y, ‖ph y‖ = 1) (hπ : Measurable π)
    (h : Z → ℂ) (hh : Measurable h) (hb : ∃ C : ℝ, ∀ z, ‖h z‖ ≤ C) :
    (∫ᵛ z, h z ∂[ContinuousLinearMap.mul ℝ ℂ; evolvedMeasure μ κ ph π]) =
      ∫ x, ∫ y, h (π y) * ph y ∂κ x ∂μ := by
  set Λ : Measure Y := (μ ⊗ₘ κ).snd with hΛ
  have hi : Integrable (fun y => h (π y)) Λ := by
    obtain ⟨C, hC⟩ := hb
    exact Integrable.mono' (integrable_const C) (hh.comp hπ).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => hC (π y)))
  have hiv : (Λ.withDensityᵥ ph).Integrable (h ∘ π) := by
    simpa only [VectorMeasure.Integrable, (variation_density_one Λ ph hph hph1), Function.comp_def] using hi
  unfold evolvedMeasure
  rw [VectorMeasure.integral_map hπ hh.aestronglyMeasurable hiv,
    integral_density_one Λ ph hph hph1 _ hi]
  exact integral_snd_compProd μ κ (fun y => h (π y) * ph y)
    (hi.mul_bdd hph.aestronglyMeasurable (Filter.Eventually.of_forall (fun y => (hph1 y).le)))

/-- `‖∫ h dη‖ ≤ ∫ ‖h‖ d|η|`. -/
lemma evolved_integral_enorm_le (hph : Measurable ph) (hph1 : ∀ y, ‖ph y‖ = 1) (hπ : Measurable π)
    (h : Z → ℂ) (hh : Measurable h) (hb : ∃ C : ℝ, ∀ z, ‖h z‖ ≤ C) :
    ‖∫ x, ∫ y, h (π y) * ph y ∂κ x ∂μ‖ₑ ≤ ∫⁻ z, ‖h z‖ₑ ∂(evolvedMeasure μ κ ph π).variation := by
  rw [← evolved_integral μ κ ph π hph hph1 hπ h hh hb]
  refine VectorMeasure.enorm_integral_le_lintegral_enorm.trans ?_
  have : ‖(ContinuousLinearMap.mul ℝ ℂ : ℂ →L[ℝ] ℂ →L[ℝ] ℂ)‖ₑ ≤ 1 := by
    rw [← ofReal_norm, ENNReal.ofReal_le_one]
    exact ContinuousLinearMap.opNorm_mul_le ℝ ℂ
  calc _ ≤ 1 * ∫⁻ z, ‖h z‖ₑ ∂(evolvedMeasure μ κ ph π).variation := by gcongr
    _ = _ := one_mul _


lemma integrable_phase_finite {W : Type*} [MeasurableSpace W] (ν : Measure W) [IsFiniteMeasure ν]
    (ph : W → ℂ) (hph : Measurable ph) (hph1 : ∀ y, ‖ph y‖ = 1) : Integrable ph ν :=
  Integrable.mono' (integrable_const (1 : ℝ)) hph.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun w => (hph1 w).le))

lemma fibreMeasure_apply (hph : Measurable ph) (hph1 : ∀ y, ‖ph y‖ = 1) (hπ : Measurable π)
    (x : X) {t : Set Z} (ht : MeasurableSet t) :
    fibreMeasure κ ph π x t = ∫ y, (π ⁻¹' t).indicator ph y ∂κ x := by
  unfold fibreMeasure
  rw [VectorMeasure.map_apply _ hπ ht, withDensityᵥ_apply (integrable_phase_finite _ ph hph hph1)
    (hπ ht), integral_indicator (hπ ht)]

lemma evolvedMeasure_apply (hph : Measurable ph) (hph1 : ∀ y, ‖ph y‖ = 1) (hπ : Measurable π)
    {t : Set Z} (ht : MeasurableSet t) :
    evolvedMeasure μ κ ph π t = ∫ x, ∫ y, (π ⁻¹' t).indicator ph y ∂κ x ∂μ := by
  unfold evolvedMeasure
  rw [VectorMeasure.map_apply _ hπ ht, withDensityᵥ_apply (integrable_phase_finite _ ph hph hph1)
    (hπ ht), ← integral_indicator (hπ ht)]
  refine integral_snd_compProd μ κ _ ?_
  exact ((integrable_phase_finite _ ph hph hph1).indicator (hπ ht))

/-- **Mass of `|η|`.**  If every fibre has total variation at most `δ`, so does `η` up to `μ(X)`. -/
lemma evolved_variation_le (hph : Measurable ph) (hph1 : ∀ y, ‖ph y‖ = 1) (hπ : Measurable π)
    (δ : ℝ≥0∞) (hδ : ∀ x, (fibreMeasure κ ph π x).variation univ ≤ δ) :
    (evolvedMeasure μ κ ph π).variation univ ≤ μ univ * δ := by
  refine le_of_forall_lt (fun a ha => ?_)
  obtain ⟨P, hPs, hPd, hPm, hsum⟩ :=
    (evolvedMeasure μ κ ph π).exists_lt_sum_of_lt_variation MeasurableSet.univ ha
  have hfib : ∀ t ∈ P, Measurable (fun x => ‖fibreMeasure κ ph π x t‖ₑ) := by
    intro t ht
    have hm : StronglyMeasurable (fun q : X × Y => (π ⁻¹' t).indicator ph q.2) :=
      ((hph.indicator (hπ (hPm t ht))).comp measurable_snd).stronglyMeasurable
    have h1 : ∀ x, fibreMeasure κ ph π x t = ∫ y, (π ⁻¹' t).indicator ph y ∂κ x :=
      fun x => fibreMeasure_apply κ ph π hph hph1 hπ x (hPm t ht)
    simp_rw [h1]
    exact (hm.integral_kernel_prod_right' (κ := κ)).measurable.enorm
  have hle : ∀ t ∈ P, ‖evolvedMeasure μ κ ph π t‖ₑ ≤ ∫⁻ x, ‖fibreMeasure κ ph π x t‖ₑ ∂μ := by
    intro t ht
    rw [evolvedMeasure_apply μ κ ph π hph hph1 hπ (hPm t ht)]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr (fun x => ?_)
    rw [fibreMeasure_apply κ ph π hph hph1 hπ x (hPm t ht)]
  calc a < ∑ t ∈ P, ‖evolvedMeasure μ κ ph π t‖ₑ := hsum
    _ ≤ ∑ t ∈ P, ∫⁻ x, ‖fibreMeasure κ ph π x t‖ₑ ∂μ := Finset.sum_le_sum hle
    _ = ∫⁻ x, ∑ t ∈ P, ‖fibreMeasure κ ph π x t‖ₑ ∂μ :=
        (lintegral_finsetSum' P (fun t ht => (hfib t ht).aemeasurable)).symm
    _ ≤ ∫⁻ _x, δ ∂μ := by
        refine lintegral_mono (fun x => ?_)
        exact (VectorMeasure.le_variation (fibreMeasure κ ph π x) MeasurableSet.univ hPs hPd).trans
          (hδ x)
    _ = μ univ * δ := by rw [lintegral_const, mul_comm]


/-- The variation measure of `η` is finite. -/
lemma evolved_variation_finite (hph : Measurable ph) (hph1 : ∀ y, ‖ph y‖ = 1) :
    IsFiniteMeasure (evolvedMeasure μ κ ph π).variation := by
  have hle : (evolvedMeasure μ κ ph π).variation ≤ ((μ ⊗ₘ κ).snd).map π := by
    unfold evolvedMeasure
    refine VectorMeasure.variation_map_le.trans ?_
    rw [variation_density_one _ ph hph hph1]
  have : IsFiniteMeasure (((μ ⊗ₘ κ).snd).map π) := inferInstance
  exact isFiniteMeasure_of_le _ hle

end


/-- `L^γ` norms of a time-shifted occupation density on the slab. -/
lemma eLpNorm_slabShift_le {d : ℕ} (g : ℝ × PDE.Vec d → ℝ) (hgm : Measurable g)
    (hgn : ∀ q, 0 ≤ g q) (s T S γ Cn : ℝ) (hT : 0 ≤ T) (hs : 0 ≤ T - s) (hTS : 2 * T - s ≤ S)
    (hbound : eLpNorm g (ENNReal.ofReal γ)
      (volume.restrict (Ioo (0 : ℝ) S ×ˢ (univ : Set (PDE.Vec d)))) ≤ ENNReal.ofReal Cn) :
    eLpNorm (fun y => ENNReal.ofReal (g (slabShift d s y))) (ENNReal.ofReal γ) (slabBase d T) ≤
      ENNReal.ofReal Cn := by
  have hemb := measurableEmbedding_slabShift d s
  have h1 : eLpNorm (fun y => ENNReal.ofReal (g (slabShift d s y))) (ENNReal.ofReal γ)
      (slabBase d T) = eLpNorm g (ENNReal.ofReal γ) ((slabBase d T).map (slabShift d s)) := by
    rw [hemb.eLpNorm_map_measure]
    refine eLpNorm_congr_enorm_ae (ENNReal.measurable_ofReal.comp (hgm.comp hemb.measurable)).aestronglyMeasurable
      (hgm.comp hemb.measurable).aestronglyMeasurable (Filter.Eventually.of_forall (fun y => ?_))
    rw [Function.comp_apply, enorm_eq_self, Real.enorm_of_nonneg (hgn _)]
  rw [h1, map_slabBase_slabShift d T s hT]
  refine le_trans (eLpNorm_mono_measure _ (Measure.restrict_mono ?_ le_rfl)) hbound
  intro q hq
  simp at hq ⊢
  constructor <;> linarith [hq.1, hq.2]





lemma one_le_slabGamma0 {d : ℕ} (hd : 0 < d) : 1 ≤ slabGamma0 d := by
  unfold slabGamma0
  have : (0 : ℝ) < d := by exact_mod_cast hd
  rw [le_div_iff₀ this]
  linarith

/-- The `ofReal` arithmetic of the marginal bound. -/
lemma ofReal_marginal_bound (C a M b : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M) (T : ℝ) (hT : 0 ≤ T)
    (β : ℝ) (hb : b = (2 * T) ^ β) (ha : a = (2 : ℝ) ^ β) :
    ENNReal.ofReal (C * M * b) =
      ENNReal.ofReal (C * a) * ENNReal.ofReal M * ENNReal.ofReal (T ^ β) := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  rw [hb, ha, Real.mul_rpow h2 hT, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul
    (by positivity)]
  congr 1
  ring

/-- **Lemma 5.1, first sentence ((5.1)).**  The `(τ,w)`-marginal of the Green
measure on `T < τ < 2T` has a density with `‖g‖_{L^γ} ≤ C_γ 2^{β_γ} M T^{β_γ}`. -/
theorem slab_marginal_density {d : ℕ} (hd : 0 < d)
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ K)
    (C : ℝ → ℝ) (hocc : OccupationBoundedBy K C)
    (σ₀ : ℝ) (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)) (hΓ : IsGreenMeasure K σ₀ ⊤ μ Γ)
    {T : ℝ} (hT : 0 < T) :
    ∃ g : SlabBase d → ℝ≥0∞, Measurable g ∧
      (∀ E : Set (SlabBase d), MeasurableSet E →
        Γ {p | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} = ∫⁻ y in E, g y ∂slabBase d T) ∧
      ∀ γ : ℝ, 1 ≤ γ → γ ≤ slabGamma0 d →
        eLpNorm g (ENNReal.ofReal γ) (slabBase d T) ≤
          ENNReal.ofReal (C γ * (2 : ℝ) ^ slabBeta d γ) * μ univ *
            ENNReal.ofReal (T ^ slabBeta d γ)  := by
  have green_slab_marginal_eq (σ₀ : ℝ) (μ : Measure (EvolutionState (wholeSpace d) (fun _ => 0) σ₀)) [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)) (hΓ : IsGreenMeasure K σ₀ ⊤ μ Γ) (T : ℝ) {E : Set (SlabBase d)} (hE : MeasurableSet E) :
      Γ {p | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} =
      ∫⁻ v, (∫⁻ τ in slabTimeSet T, occupationKernel K σ₀ τ.1 v {w | (τ, w) ∈ E}
        ∂elapsedVolume ⊤) ∂μ.map (fun p => p.1.1) := by
    have measurable_slab_occupation (σ₁ s T : ℝ) {E : Set (SlabBase d)} (hE : MeasurableSet E) :
        Measurable (fun v => ∫⁻ τ in slabTimeSet T,
        occupationKernel K σ₁ (τ.1 - s) v {w | (τ, w) ∈ E} ∂elapsedVolume ⊤) := by
      have hE' : MeasurableSet {z : (PDE.Vec d × ElapsedTime ⊤) × PDE.Vec d | (z.1.2, z.2) ∈ E} :=
        hE.preimage (by fun_prop)
      have hm := measurable_occupationKernel_sectionGen K σ₁
        (f := fun x => x.2.1 - s) (u := fun x => x.1)
        (by fun_prop) (by fun_prop) hE'
      exact hm.lintegral_prod_right'
    have hSE : {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} =
        (fun p => (p.1, p.2.1)) ⁻¹' E ∩ slabSet T := by
      ext p; simp [slabSet, slabTimeSet]
    have hSEm : MeasurableSet
        {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} := by
      rw [hSE]
      exact (hE.preimage (by fun_prop)).inter (measurableSet_slabSet T)
    have hmapm : Measurable (fun p : EvolutionState (wholeSpace d) (fun _ => 0) σ₀ =>
        p.1.1) := measurable_fst.comp measurable_subtype_coe
    rw [← lintegral_indicator_one hSEm, hΓ _ (measurable_one.indicator hSEm),
      lintegral_map (measurable_slab_occupation σ₀ 0 T hE |> fun h => by simpa using h) hmapm]
    refine lintegral_congr (fun p => ?_)
    rw [← lintegral_indicator (measurableSet_slabTimeSet T)]
    refine lintegral_congr (fun τ => ?_)
    by_cases hτ : τ ∈ slabTimeSet T
    · rw [indicator_of_mem hτ]
      have hsec : MeasurableSet {w' : PDE.Vec d | (τ, w') ∈ E} := measurable_prodMk_left hE
      have hfun : (fun w =>
          {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T}.indicator
            1 (τ, w)) =
          {w : EvolutionAmbientState d | w.1 ∈ {w' : PDE.Vec d | (τ, w') ∈ E}}.indicator
            (1 : EvolutionAmbientState d → ℝ≥0∞) := by
        funext w
        by_cases h : (τ, w.1) ∈ E
        · have h1 : (τ, w) ∈ {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} :=
            ⟨h, hτ.1, hτ.2⟩
          have h2 : w ∈ {w : EvolutionAmbientState d | w.1 ∈ {w' : PDE.Vec d | (τ, w') ∈ E}} := h
          rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
          rfl
        · have h1 : (τ, w) ∉ {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} :=
            fun h' => h h'.1
          have h2 : w ∉ {w : EvolutionAmbientState d | w.1 ∈ {w' : PDE.Vec d | (τ, w') ∈ E}} := h
          rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
      rw [hfun, (lintegral_indicator_one (μ := K.master (elapsedQuery σ₀ p τ)) (s := {w : EvolutionAmbientState d | w.1 ∈ {w' : PDE.Vec d | (τ, w') ∈ E}}) (measurable_fst hsec)), ← K.firstMarginal_apply _ {w' : PDE.Vec d | (τ, w') ∈ E} hsec]
      have hq : elapsedQuery σ₀ p τ =
          wholeSpaceQuery σ₀ (σ₀ + τ.1) (le_add_of_nonneg_right τ.2.1.le) p.1.1 p.1.2 := rfl
      rw [hq, firstMarginal_startingPosition K hcov, occupationKernel_of_nonneg K σ₀ τ.1 τ.2.1.le]
    · rw [indicator_of_notMem hτ]
      have hz : ∀ w : EvolutionAmbientState d,
          {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T}.indicator
            (1 : GreenCarrier d → ℝ≥0∞) (τ, w) = 0 :=
        fun w => Set.indicator_of_notMem (fun h => hτ ⟨h.2.1, h.2.2⟩) _
      exact (lintegral_congr hz).trans lintegral_zero
  have hmapm : Measurable (fun p : EvolutionState (wholeSpace d) (fun _ => 0) σ₀ =>
      p.1.1) := measurable_fst.comp measurable_subtype_coe
  have : IsFiniteMeasure (μ.map (fun p : EvolutionState (wholeSpace d)
      (fun _ => 0) σ₀ => p.1.1)) := Measure.isFiniteMeasure_map _ _
  obtain ⟨g, hg, hnorm⟩ := hocc.2 (μ.map (fun p => p.1.1)) σ₀ (2 * T) (by linarith)
  have hint : Integrable g (volume.restrict (Ioo 0 (2 * T) ×ˢ (univ : Set (PDE.Vec d)))) := by
    have := (hnorm 1 le_rfl (one_le_slabGamma0 hd)).1
    rw [ENNReal.ofReal_one] at this
    exact memLp_one_iff_integrable.1 this
  refine ⟨fun y => ENNReal.ofReal (g (slabShift d 0 y)), ?_, ?_, ?_⟩
  · exact ENNReal.measurable_ofReal.comp (hg.1.comp (measurable_slabShift d 0))
  · intro E hE
    rw [green_slab_marginal_eq σ₀ μ Γ hΓ T hE]
    have := slab_occupation_identity K σ₀ 0 T (2 * T) hT.le hT (by linarith) (by linarith)
      (μ.map (fun p => p.1.1)) g hg hint hE
    simp at this
    exact this.symm
  · intro γ hγ1 hγ2
    obtain ⟨hmem, hbd⟩ := hnorm γ hγ1 hγ2
    set Cn : ℝ := C γ * ((μ.map (fun p => p.1.1)) univ).toReal * (2 * T) ^ slabBeta d γ with hCn_def
    have hbd' : eLpNorm g (ENNReal.ofReal γ)
        (volume.restrict (Ioo 0 (2 * T) ×ˢ (univ : Set (PDE.Vec d)))) ≤
          ENNReal.ofReal Cn := by
      rw [← ENNReal.ofReal_toReal hmem.eLpNorm_ne_top]
      exact ENNReal.ofReal_le_ofReal hbd
    have := eLpNorm_slabShift_le g hg.1 hg.2.1 0 T (2 * T) γ Cn hT.le (by linarith)
      (by linarith) hbd'
    refine this.trans (le_of_eq ?_)
    rw [hCn_def, Measure.map_apply hmapm MeasurableSet.univ, preimage_univ]
    rw [ofReal_marginal_bound (C γ) (2 ^ slabBeta d γ) ((μ univ).toReal)
      ((2 * T) ^ slabBeta d γ) (hocc.1 γ hγ1 hγ2) ENNReal.toReal_nonneg T hT.le (slabBeta d γ) rfl rfl,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]



variable {d : ℕ} (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))

/-- Initial phase `e^{-iξ·z₁}` at the half time. -/
def halfPhase (d : ℕ) (ξ : PDE.Vec d) (r : ℝ) :
    EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) r → ℂ :=
  fun w => fourierPhase ξ 0 w.1

/-- Velocity coordinate of a half-time state. -/
def halfVelocity (d : ℕ) (r : ℝ) :
    EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) r → PDE.Vec d := fun w => w.1.1

lemma measurable_halfPhase (ξ : PDE.Vec d) (r : ℝ) : Measurable (halfPhase d ξ r) :=
  (continuous_fourierPhase ξ 0).measurable.comp measurable_subtype_coe

lemma norm_halfPhase (ξ : PDE.Vec d) (r : ℝ) (w) : ‖halfPhase d ξ r w‖ = 1 :=
  norm_fourierPhase ξ 0 w.1

lemma measurable_halfVelocity (r : ℝ) : Measurable (halfVelocity d r) :=
  measurable_fst.comp measurable_subtype_coe

/-- The half-time fibre kernel. -/
def halfKernel (σ₀ r : ℝ) (hσr : σ₀ ≤ r) :
    ProbabilityTheory.Kernel (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀)
      (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) r) :=
  K.fiberKernel MeasurableSet.univ σ₀ r hσr

instance halfKernel_isFiniteKernel (σ₀ r : ℝ) (hσr : σ₀ ≤ r) :
    ProbabilityTheory.IsFiniteKernel (halfKernel K σ₀ r hσr) :=
  fiberKernel_isFiniteKernel K MeasurableSet.univ σ₀ r hσr


/-- Queries at equal times coincide. -/
lemma wholeSpaceQuery_congr (σ a b : ℝ) (h₁ : σ ≤ a) (h₂ : σ ≤ b) (hab : a = b)
    (v z : PDE.Vec d) : wholeSpaceQuery σ a h₁ v z = wholeSpaceQuery σ b h₂ v z := by
  subst hab; rfl

/-- The displacement phase integrated over a `v`-slab: `e^{-iξ·z}` times the Fourier kernel. -/
lemma master_phase_integral
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ K)
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ v z : PDE.Vec d) {E : Set (PDE.Vec d)} (hE : MeasurableSet E) :
    ∫ w, (E ×ˢ (univ : Set (PDE.Vec d))).indicator (fourierPhase ξ 0) w
        ∂K.master (wholeSpaceQuery σ τ hστ v z) =
      fourierPhase ξ 0 (v, z) * fourierKernel K σ τ hστ ξ v E := by
  rw [← fourierKernel_eq_startingPosition K hcov σ τ hστ ξ v z,
    fourierProjection_spec K (wholeSpaceQuery σ τ hστ v z) ξ E hE, ← integral_const_mul,
    ← integral_indicator (hE.prod MeasurableSet.univ)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
  by_cases hw : w ∈ E ×ˢ (univ : Set (PDE.Vec d))
  · simp only [Set.indicator_of_mem hw]
    exact fourierPhase_factor ξ 0 (v, z) w
  · simp only [Set.indicator_of_notMem hw]



/-- Each fibre of the half-time evolution has the total variation of the Fourier kernel. -/
lemma fibreMeasure_variation_le
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ K)
    (σ₀ r : ℝ) (hσr : σ₀ ≤ r) (ξ : PDE.Vec d)
    (x : EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀) :
    (fibreMeasure (halfKernel K σ₀ r hσr) (halfPhase d ξ r) (halfVelocity d r) x).variation univ ≤
      totalVariationNorm (fourierKernel K σ₀ r hσr ξ x.1.1)  := by
  have fibreMeasure_halfKernel (σ₀ r : ℝ) (hσr : σ₀ ≤ r) (ξ : PDE.Vec d) (x : EvolutionState (wholeSpace d) (fun _ => 0) σ₀) {E : Set (PDE.Vec d)} (hE : MeasurableSet E) :
      fibreMeasure (halfKernel K σ₀ r hσr) (halfPhase d ξ r) (halfVelocity d r) x E =
      fourierPhase ξ 0 x.1 * fourierKernel K σ₀ r hσr ξ x.1.1 E := by
    rw [fibreMeasure_apply _ _ _ (measurable_halfPhase ξ r) (norm_halfPhase ξ r)
      (measurable_halfVelocity r) x hE]
    let G := (E ×ˢ univ).indicator (fourierPhase ξ 0)
    have hG := (continuous_fourierPhase ξ 0).measurable.indicator
      (hE.prod MeasurableSet.univ)
    have h1 : ∀ y : EvolutionState (wholeSpace d) (fun _ => 0) r,
        (halfVelocity d r ⁻¹' E).indicator (halfPhase d ξ r) y = G y.1 := by
      intro y
      by_cases hy : y.1.1 ∈ E
      · have h2 : y ∈ halfVelocity d r ⁻¹' E := hy
        have h3 : y.1 ∈ E ×ˢ (univ : Set (PDE.Vec d)) := ⟨hy, mem_univ _⟩
        rw [Set.indicator_of_mem h2]
        simp only [G, Set.indicator_of_mem h3]
        rfl
      · have h2 : y ∉ halfVelocity d r ⁻¹' E := hy
        have h3 : y.1 ∉ E ×ˢ (univ : Set (PDE.Vec d)) := fun h => hy h.1
        rw [Set.indicator_of_notMem h2]
        simp only [G, Set.indicator_of_notMem h3]
    simp_rw [h1]
    have h4 : ∫ y, G y.1 ∂(halfKernel K σ₀ r hσr) x =
        ∫ w, G w ∂K.master (evolutionQueryOfState (wholeSpace d) (fun _ => 0) σ₀ r hσr x) := by
      rw [← K.map_fiberKernel_eq_master MeasurableSet.univ σ₀ r hσr x,
        integral_map measurable_subtype_coe.aemeasurable hG.aestronglyMeasurable]
      rfl
    rw [h4]
    exact master_phase_integral K hcov σ₀ r hσr ξ x.1.1 x.1.2 hE
  have hle : (fibreMeasure (halfKernel K σ₀ r hσr) (halfPhase d ξ r)
      (halfVelocity d r) x).variation ≤ (fourierKernel K σ₀ r hσr ξ x.1.1).variation := by
    refine VectorMeasure.variation_le_of_forall_enorm_le (fun E hE => ?_)
    have h1 : ‖fourierPhase ξ 0 x.1‖ₑ = 1 := by
      rw [← ofReal_norm, norm_fourierPhase]; simp
    rw [fibreMeasure_halfKernel σ₀ r hσr ξ x hE, enorm_mul, h1, one_mul]
    exact VectorMeasure.enorm_measure_le_variation _ E
  exact Measure.le_iff.1 hle univ MeasurableSet.univ


/-- The phase `e^{-iξ·z'}` cut to the velocity set `E`. -/
def phaseSection (d : ℕ) (ξ : PDE.Vec d) (E : Set (PDE.Vec d)) : EvolutionAmbientState d → ℂ :=
  (E ×ˢ (univ : Set (PDE.Vec d))).indicator (fourierPhase ξ 0)

lemma measurable_phaseSection (ξ : PDE.Vec d) {E : Set (PDE.Vec d)} (hE : MeasurableSet E) :
    Measurable (phaseSection d ξ E) :=
  (continuous_fourierPhase ξ 0).measurable.indicator (hE.prod MeasurableSet.univ)

lemma norm_phaseSection_le (ξ : PDE.Vec d) (E : Set (PDE.Vec d)) (w : EvolutionAmbientState d) :
    ‖phaseSection d ξ E w‖ ≤ 1 := by
  unfold phaseSection
  by_cases hw : w ∈ E ×ˢ (univ : Set (PDE.Vec d))
  · rw [Set.indicator_of_mem hw, norm_fourierPhase]
  · rw [Set.indicator_of_notMem hw, norm_zero]; exact zero_le_one



/-- The half time `σ₀ + T/2`. -/
lemma le_halfTime (σ₀ T : ℝ) (hT : 0 ≤ T) : σ₀ ≤ σ₀ + T / 2 :=
  le_add_of_nonneg_right (by positivity)

/-- The complex velocity measure `η_T^ξ` of the half-time evolution of `μ`. -/
def halfMeasure (σ₀ T : ℝ) (hT : 0 ≤ T)
    (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀)) (ξ : PDE.Vec d) :
    VectorMeasure (PDE.Vec d) ℂ :=
  evolvedMeasure μ (halfKernel K σ₀ (σ₀ + T / 2) (le_halfTime σ₀ T hT))
    (halfPhase d ξ (σ₀ + T / 2)) (halfVelocity d (σ₀ + T / 2))




/-- The Fourier phase on the Green carrier. -/
def greenPhase (d : ℕ) (ξ : PDE.Vec d) (p : GreenCarrier d) : ℂ :=
  Complex.exp (-((PDE.vecDot ξ p.2.2 : ℝ) * Complex.I))

lemma greenPhase_eq (ξ : PDE.Vec d) (τ : ElapsedTime ⊤) (w : EvolutionAmbientState d) :
    greenPhase d ξ (τ, w) = fourierPhase ξ 0 w := by
  unfold greenPhase fourierPhase
  rw [sub_zero, neg_mul, mul_comm]

lemma measurable_greenPhase (ξ : PDE.Vec d) : Measurable (greenPhase d ξ) := by
  unfold greenPhase PDE.vecDot
  fun_prop

lemma norm_greenPhase (ξ : PDE.Vec d) (p : GreenCarrier d) : ‖greenPhase d ξ p‖ = 1 := by
  rw [greenPhase_eq ξ p.1 p.2]
  exact norm_fourierPhase ξ 0 p.2

/-- The slab set of a measurable `E ⊆ SlabBase`. -/
lemma slabPreimage_eq {d : ℕ} (T : ℝ) (E : Set (SlabBase d)) :
    {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} =
      (fun p : GreenCarrier d => (p.1, p.2.1)) ⁻¹' E ∩ slabSet T := by
  ext p; simp [slabSet, slabTimeSet]

lemma measurableSet_slabPreimage {d : ℕ} (T : ℝ) {E : Set (SlabBase d)} (hE : MeasurableSet E) :
    MeasurableSet {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} := by
  rw [slabPreimage_eq]
  exact (hE.preimage (by fun_prop)).inter (measurableSet_slabSet T)

/-- **Domination of the Fourier marginal (`#fourier-domination`, inequality for sets).** -/
theorem slab_domination_ineq
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ K)
    (hcomp : K.HasComposition MeasurableSet.univ) (σ₀ : ℝ)
    (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)) (hΓ : IsGreenMeasure K σ₀ ⊤ μ Γ)
    {T : ℝ} (hT : 0 < T) (ξ : PDE.Vec d) {E : Set (SlabBase d)} (hE : MeasurableSet E) :
    ‖∫ p in {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T},
        greenPhase d ξ p ∂Γ‖ₑ ≤
      ∫⁻ v, (∫⁻ τ in slabTimeSet T, occupationKernel K (σ₀ + T / 2) (τ.1 - T / 2) v
          {w | (τ, w) ∈ E} ∂elapsedVolume ⊤) ∂(halfMeasure K σ₀ T hT.le μ ξ).variation   := by
  have occupationKernel_half (σ₀ T : ℝ) (τ : ℝ) (hτ : T < τ) (hT : 0 < T) (v : PDE.Vec d) :
      occupationKernel K (σ₀ + T / 2) (τ - T / 2) v =
      K.firstMarginal (wholeSpaceQuery (σ₀ + T / 2) (σ₀ + τ)
        (by linarith) v 0) := by
    rw [occupationKernel_of_nonneg K _ _ (by linarith) v]
    rw [wholeSpaceQuery_congr (σ₀ + T / 2) _ (σ₀ + τ) _ (by linarith) (by ring) v 0]
  have slab_section_bound (σ₀ : ℝ) (μ : Measure (EvolutionState (wholeSpace d) (fun _ => 0) σ₀)) [IsFiniteMeasure μ] {T : ℝ} (hT : 0 < T) (ξ : PDE.Vec d) (τ : ElapsedTime ⊤) (hτ : T < τ.1) {E : Set (PDE.Vec d)} (hE : MeasurableSet E) :
      ‖∫ p, ∫ w, phaseSection d ξ E w ∂K.master (elapsedQuery σ₀ p τ) ∂μ‖ₑ ≤
      ∫⁻ v, occupationKernel K (σ₀ + T / 2) (τ.1 - T / 2) v E
        ∂(halfMeasure K σ₀ T hT.le μ ξ).variation := by
    have slab_pairing (σ₀ : ℝ) (μ : Measure (EvolutionState (wholeSpace d) (fun _ => 0) σ₀)) [IsFiniteMeasure μ] (r : ℝ) (hσr : σ₀ ≤ r) (ξ : PDE.Vec d) (τ : ElapsedTime ⊤) (hrτ : r ≤ σ₀ + τ.1) {E : Set (PDE.Vec d)} (hE : MeasurableSet E) :
        ∫ p, ∫ w, phaseSection d ξ E w ∂K.master (elapsedQuery σ₀ p τ) ∂μ =
        ∫ x, ∫ y, fourierKernel K r (σ₀ + τ.1) hrτ ξ (halfVelocity d r y) E * halfPhase d ξ r y
          ∂halfKernel K σ₀ r hσr x ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      dsimp only
      have hq : elapsedQuery σ₀ p τ = evolutionQueryOfState (wholeSpace d) (fun _ => 0) σ₀ (σ₀ + τ.1)
          (le_add_of_nonneg_right τ.2.1.le) p := rfl
      rw [hq, master_integral_composition K MeasurableSet.univ hcomp σ₀ r (σ₀ + τ.1) hσr hrτ p
        (phaseSection d ξ E) (measurable_phaseSection ξ hE) ⟨1, norm_phaseSection_le ξ E⟩]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
      dsimp only
      have hq' : evolutionQueryOfState (wholeSpace d) (fun _ => 0) r (σ₀ + τ.1) hrτ y =
          wholeSpaceQuery r (σ₀ + τ.1) hrτ y.1.1 y.1.2 := rfl
      rw [hq']
      have := master_phase_integral K hcov r (σ₀ + τ.1) hrτ ξ y.1.1 y.1.2 hE
      rw [mul_comm]
      exact this
    have hrτ : σ₀ + T / 2 ≤ σ₀ + τ.1 := by linarith
    rw [slab_pairing σ₀ μ (σ₀ + T / 2) (le_halfTime σ₀ T hT.le) ξ τ hrτ hE]
    have hb : ∃ C : ℝ, ∀ v : PDE.Vec d,
        ‖fourierKernel K (σ₀ + T / 2) (σ₀ + τ.1) hrτ ξ v E‖ ≤ C :=
      ⟨1, fun v => fourierKernel_apply_norm_le_one K _ _ hrτ ξ v E⟩
    refine (evolved_integral_enorm_le μ (halfKernel K σ₀ (σ₀ + T / 2) (le_halfTime σ₀ T hT.le))
      (halfPhase d ξ (σ₀ + T / 2)) (halfVelocity d (σ₀ + T / 2)) (measurable_halfPhase ξ _)
      (norm_halfPhase ξ _) (measurable_halfVelocity _)
      (fun v => fourierKernel K (σ₀ + T / 2) (σ₀ + τ.1) hrτ ξ v E)
      (measurable_fourierKernel_apply K _ _ hrτ ξ E hE) hb).trans ?_
    refine lintegral_mono (fun v => ?_)
    rw [occupationKernel_half σ₀ T τ.1 hτ hT v]
    refine (VectorMeasure.enorm_measure_le_variation _ E).trans ?_
    exact Measure.le_iff.1 (fourierKernel_variation_le K _ _ hrτ ξ v) E hE
  set ρ := (halfMeasure K σ₀ T hT.le μ ξ).variation with hρ
  have hρfin : IsFiniteMeasure ρ :=
    evolved_variation_finite μ _ _ _ (measurable_halfPhase ξ _) (norm_halfPhase ξ _)
  have hSEm := measurableSet_slabPreimage T hE
  set SE : Set (GreenCarrier d) := {p | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} with hSE
  have hSEsub : SE ⊆ slabSet T := by
    intro p hp; exact ⟨hp.2.1, hp.2.2⟩
  have hf1m : Measurable (SE.indicator (greenPhase d ξ)) :=
    (measurable_greenPhase ξ).indicator hSEm
  have hf1b : ∀ p, ‖SE.indicator (greenPhase d ξ) p‖ ≤ 1 := by
    intro p
    by_cases hp : p ∈ SE
    · rw [Set.indicator_of_mem hp, norm_greenPhase]
    · rw [Set.indicator_of_notMem hp, norm_zero]; exact zero_le_one
  have hf1s : ∀ p, p ∉ slabSet T → SE.indicator (greenPhase d ξ) p = 0 :=
    fun p hp => Set.indicator_of_notMem (fun h => hp (hSEsub h)) _
  rw [← integral_indicator hSEm,
    green_integral K σ₀ μ Γ hΓ hT _ hf1m hf1b hf1s]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have hmeas : Measurable (fun x : ElapsedTime ⊤ × PDE.Vec d =>
      occupationKernel K (σ₀ + T / 2) (x.1.1 - T / 2) x.2 {w | (x.1, w) ∈ E}) := by
    have hE' : MeasurableSet {z : (ElapsedTime ⊤ × PDE.Vec d) × PDE.Vec d | (z.1.1, z.2) ∈ E} :=
      hE.preimage (by fun_prop)
    exact measurable_occupationKernel_sectionGen K (σ₀ + T / 2)
      (f := fun x : ElapsedTime ⊤ × PDE.Vec d => x.1.1 - T / 2) (u := fun x => x.2)
      (by fun_prop) (by fun_prop) hE'
  calc ∫⁻ τ, ‖∫ p, ∫ w, SE.indicator (greenPhase d ξ) (τ, w) ∂K.master (elapsedQuery σ₀ p τ) ∂μ‖ₑ
        ∂elapsedVolume ⊤
      ≤ ∫⁻ τ, (slabTimeSet T).indicator (fun τ => ∫⁻ v, occupationKernel K (σ₀ + T / 2)
          (τ.1 - T / 2) v {w | (τ, w) ∈ E} ∂ρ) τ ∂elapsedVolume ⊤ := by
        refine lintegral_mono (fun τ => ?_)
        by_cases hτ : τ ∈ slabTimeSet T
        · rw [Set.indicator_of_mem hτ]
          have hsec : MeasurableSet {w' : PDE.Vec d | (τ, w') ∈ E} := measurable_prodMk_left hE
          have hfun : ∀ w : EvolutionAmbientState d, SE.indicator (greenPhase d ξ) (τ, w) =
              phaseSection d ξ {w' : PDE.Vec d | (τ, w') ∈ E} w := by
            intro w
            unfold phaseSection
            by_cases hw : (τ, w.1) ∈ E
            · have h1 : (τ, w) ∈ SE := ⟨hw, hτ.1, hτ.2⟩
              have h2 : w ∈ ({w' : PDE.Vec d | (τ, w') ∈ E} ×ˢ (univ : Set (PDE.Vec d))) :=
                ⟨hw, mem_univ _⟩
              rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2, greenPhase_eq]
            · have h1 : (τ, w) ∉ SE := fun h => hw h.1
              have h2 : w ∉ ({w' : PDE.Vec d | (τ, w') ∈ E} ×ˢ (univ : Set (PDE.Vec d))) :=
                fun h => hw h.1
              rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
          simp_rw [hfun]
          exact slab_section_bound σ₀ μ hT ξ τ hτ.1 hsec
        · rw [Set.indicator_of_notMem hτ]
          have hz : ∀ w : EvolutionAmbientState d, SE.indicator (greenPhase d ξ) (τ, w) = 0 :=
            fun w => Set.indicator_of_notMem (fun h => hτ ⟨h.2.1, h.2.2⟩) _
          simp [hz]
    _ = ∫⁻ τ in slabTimeSet T, ∫⁻ v, occupationKernel K (σ₀ + T / 2) (τ.1 - T / 2) v
          {w | (τ, w) ∈ E} ∂ρ ∂elapsedVolume ⊤ :=
        lintegral_indicator (measurableSet_slabTimeSet T) _
    _ = _ := by
        refine lintegral_lintegral_swap ?_
        exact hmeas.aemeasurable

end HypoellipticAleksandrov.KineticAleksandrov.Green

