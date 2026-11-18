module

public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Radius
public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Unique
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierKernelsTranslation
public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabSetting
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierDomination
public import Mathlib.Probability.Kernel.RadonNikodym
public import Mathlib.Probability.Kernel.WithDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierBound
public import HypoellipticAleksandrov.KineticAleksandrov.Green.Main

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Green
open MeasureTheory Set HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal NNReal ProbabilityTheory


/-- The decay profile `exp(-c |ζ|^{2/3})` (Euclidean norm), as an `ℝ≥0∞`-valued function. -/
def decayProfile (d : ℕ) (c : ℝ) (ζ : PDE.Vec d) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(c * PDE.vecEuclideanNorm ζ ^ ((2 : ℝ) / 3))))

/-- The decay profile is Lebesgue integrable: `∫ exp(-c |ζ|^{2/3}) dζ < ∞`. -/
theorem lintegral_decayProfile_lt_top {d : ℕ} (hd : 0 < d) {c : ℝ} (hc : 0 < c) :
    ∫⁻ ζ, decayProfile d c ζ < ⊤ := by
  have : Nontrivial (PDE.Vec d) := by
    unfold PDE.Vec
    exact ⟨⟨0, 1, fun h => by simpa using congrFun h ⟨0, hd⟩⟩⟩
  have hint : Integrable (fun ζ : PDE.Vec d => Real.exp (-(c * ‖ζ‖ ^ ((2 : ℝ) / 3)))) := by
    refine (integrable_fun_norm_addHaar (volume : Measure (PDE.Vec d))
      (f := fun y : ℝ => Real.exp (-(c * y ^ (2 / 3))))).2 ?_
    have h1 := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 2 / 3) (s := (d : ℝ) - 1)
      (b := c) (by have : (1 : ℝ) ≤ d := by exact_mod_cast hd
                   linarith) (by norm_num) hc
    refine h1.congr_fun (fun y hy => ?_) measurableSet_Ioi
    simp only [Module.finrank_fin_fun, smul_eq_mul]
    rw [neg_mul, ← Real.rpow_natCast, Nat.cast_sub hd]
    simp
  have hle : ∀ ζ : PDE.Vec d, decayProfile d c ζ ≤
      ENNReal.ofReal (Real.exp (-(c * ‖ζ‖ ^ ((2 : ℝ) / 3)))) := by
    intro ζ
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have h2 : ‖ζ‖ ^ ((2 : ℝ) / 3) ≤ PDE.vecEuclideanNorm ζ ^ ((2 : ℝ) / 3) :=
      Real.rpow_le_rpow (norm_nonneg _) (PDE.norm_le_vecEuclideanNorm ζ) (by norm_num)
    nlinarith
  exact (lintegral_mono hle).trans_lt hint.lintegral_lt_top


lemma measurable_decayProfile (d : ℕ) (c : ℝ) : Measurable (decayProfile d c) := by
  have h : Measurable (fun ζ : PDE.Vec d => PDE.vecEuclideanNorm ζ) := by
    unfold PDE.vecEuclideanNorm PDE.vecNormSq PDE.vecDot
    fun_prop
  unfold decayProfile
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (((measurable_const.mul (h.pow_const _))).neg))

/-- **Scaling `ζ = T^{3/2} ξ`.** -/
theorem lintegral_decayProfile_scaling (d : ℕ) (c T : ℝ) (hT : 0 < T) :
    ∫⁻ ξ : PDE.Vec d,
        ENNReal.ofReal (Real.exp (-(c * T * PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3)))) =
      ENNReal.ofReal (T ^ (-(3 * (d : ℝ) / 2))) * ∫⁻ ζ, decayProfile d c ζ := by
  set a : ℝ := T ^ ((3 : ℝ) / 2) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos hT _
  have hfun : ∀ ξ : PDE.Vec d,
      ENNReal.ofReal (Real.exp (-(c * T * PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3)))) =
        decayProfile d c (a • ξ) := by
    intro ξ
    unfold decayProfile
    rw [PDE.vecEuclideanNorm_smul, abs_of_pos ha0, Real.mul_rpow ha0.le
      (PDE.vecEuclideanNorm_nonneg ξ), ha, ← Real.rpow_mul hT.le]
    norm_num
    ring_nf
  simp_rw [hfun]
  have hm : Measurable (fun ξ : PDE.Vec d => a • ξ) := measurable_const_smul a
  rw [← lintegral_map (measurable_decayProfile d c) hm, (Measure.map_addHaar_smul (volume : Measure (PDE.Vec d)) ha0.ne'), lintegral_smul_measure]
  congr 1
  simp only [Module.finrank_fin_fun, abs_inv, abs_pow, abs_of_pos ha0]
  congr 1
  rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hT.le, ← Real.rpow_neg hT.le]
  congr 1
  ring

section

open MeasureTheory ProbabilityTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal NNReal

variable {d : ℕ}

/-- The positive weight `w(τ, y) = exp(-|y|^{2/3})` making `w · slabBase` finite. -/
def slabWeight (d : ℕ) (y : SlabBase d) : ℝ≥0∞ := decayProfile d 1 y.2

lemma measurable_slabWeight (d : ℕ) : Measurable (slabWeight d) :=
  (measurable_decayProfile d 1).comp measurable_snd

lemma slabWeight_pos (y : SlabBase d) : 0 < slabWeight d y :=
  ENNReal.ofReal_pos.2 (Real.exp_pos _)

/-- The finite reference measure `m' = w · slabBase`. -/
def slabRef (d : ℕ) (T : ℝ) : Measure (SlabBase d) := (slabBase d T).withDensity (slabWeight d)

lemma isFiniteMeasure_slabRef (hd : 0 < d) {T : ℝ} (hT : 0 < T) :
    IsFiniteMeasure (slabRef d T) := by
  refine ⟨?_⟩
  rw [slabRef, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have h : ∫⁻ y, slabWeight d y ∂slabBase d T =
      (∫⁻ _τ : ElapsedTime ⊤, 1 ∂(elapsedVolume ⊤).restrict (slabTimeSet T)) *
        ∫⁻ ζ, decayProfile d 1 ζ := by
    unfold slabBase slabWeight
    have := lintegral_prod_mul (μ := (elapsedVolume ⊤).restrict (slabTimeSet T))
      (ν := (volume : Measure (PDE.Vec d))) (f := fun _ => 1)
      (g := decayProfile d 1) aemeasurable_const (measurable_decayProfile d 1).aemeasurable
    simpa using this
  rw [h, lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    elapsedVolume_slabTimeSet hT]
  exact ENNReal.mul_lt_top (by simp)
    (lintegral_decayProfile_lt_top hd one_pos)

/-- The `ℝ≥0∞`-valued density `ofReal (F (e^{-iξ·z'}))` on the Green carrier. -/
def phaseDensity (d : ℕ) (F : ℂ → ℝ) (ξ : PDE.Vec d) (p : GreenCarrier d) : ℝ≥0∞ :=
  ENNReal.ofReal (F (greenPhase d ξ p))

lemma measurable_greenPhase_joint (d : ℕ) :
    Measurable (fun x : PDE.Vec d × GreenCarrier d => greenPhase d x.1 x.2) := by
  unfold greenPhase PDE.vecDot
  fun_prop

lemma measurable_phaseDensity {F : ℂ → ℝ} (hF : Measurable F) :
    Measurable (Function.uncurry (phaseDensity d F)) :=
  ENNReal.measurable_ofReal.comp (hF.comp (measurable_greenPhase_joint d))

/-- The kernel `ξ ↦` pushforward of `φ_ξ`-channel `F` times `Γ|slab` to the slab base. -/
def phaseKernel (d : ℕ) (T : ℝ) (Γ : Measure (GreenCarrier d)) [IsFiniteMeasure
    (Γ.restrict (slabSet (d := d) T))] (F : ℂ → ℝ) : Kernel (PDE.Vec d) (SlabBase d) :=
  (Kernel.withDensity (Kernel.const (PDE.Vec d) (Γ.restrict (slabSet T)))
    (phaseDensity d F)).map (fun p : GreenCarrier d => (p.1, p.2.1))

section

variable {T : ℝ} {Γ : Measure (GreenCarrier d)} [IsFiniteMeasure (Γ.restrict (slabSet (d := d) T))]
  {F : ℂ → ℝ}

lemma phaseKernel_apply (hF : Measurable F) (ξ : PDE.Vec d) {E : Set (SlabBase d)}
    (hE : MeasurableSet E) :
    phaseKernel d T Γ F ξ E =
      ∫⁻ p in {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T},
        phaseDensity d F ξ p ∂Γ := by
  have hπ : Measurable (fun p : GreenCarrier d => (p.1, p.2.1)) := by fun_prop
  unfold phaseKernel
  rw [Kernel.map_apply' _ hπ _ hE, Kernel.withDensity_apply' _ (measurable_phaseDensity hF),
    Kernel.const_apply, Measure.restrict_restrict (hπ hE), slabPreimage_eq T E, inter_comm]

lemma phaseKernel_le (hF : Measurable F) (hFb : ∀ z : ℂ, ‖z‖ = 1 → F z ≤ 1) (ξ : PDE.Vec d)
    {E : Set (SlabBase d)} (hE : MeasurableSet E) :
    phaseKernel d T Γ F ξ E ≤
      Γ {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} := by
  rw [phaseKernel_apply hF ξ hE]
  calc ∫⁻ p in {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T},
        phaseDensity d F ξ p ∂Γ
      ≤ ∫⁻ _p in {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T}, 1 ∂Γ := by
        refine lintegral_mono (fun p => ?_)
        unfold phaseDensity
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (hFb _ (norm_greenPhase ξ p))
    _ = _ := by rw [setLIntegral_const, one_mul]

theorem phaseKernel_isFiniteKernel (hFb : ∀ z : ℂ, ‖z‖ = 1 → F z ≤ 1) :
    IsFiniteKernel (phaseKernel d T Γ F) := by
  have h : IsFiniteKernel (Kernel.withDensity (Kernel.const (PDE.Vec d) (Γ.restrict (slabSet T)))
      (phaseDensity d F)) := by
    refine Kernel.isFiniteKernel_withDensity_of_bounded _ (B := 1) ENNReal.one_ne_top
      (fun ξ p => ?_)
    unfold phaseDensity
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (hFb _ (norm_greenPhase ξ p))
  unfold phaseKernel
  infer_instance

/-- **One real channel.**  A jointly measurable family `r^ξ ≥ 0` of densities, on the slab base,
of the measures `E ↦ ∫_{S_E} ofReal (F (e^{-iξ·z'})) dΓ`. -/
theorem exists_channel (hd : 0 < d) (hT : 0 < T) (hF : Measurable F)
    (hFb : ∀ z : ℂ, ‖z‖ = 1 → F z ≤ 1) (g : SlabBase d → ℝ≥0∞)
    (hg : ∀ E : Set (SlabBase d), MeasurableSet E →
      Γ {p | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} = ∫⁻ y in E, g y ∂slabBase d T) :
    ∃ r : PDE.Vec d → SlabBase d → ℝ, Measurable (Function.uncurry r) ∧ (∀ ξ y, 0 ≤ r ξ y) ∧
      ∀ ξ, Integrable (r ξ) (slabBase d T) ∧ ∀ E : Set (SlabBase d), MeasurableSet E →
        ∫ y in E, r ξ y ∂slabBase d T =
          (∫⁻ p in {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T},
            ENNReal.ofReal (F (greenPhase d ξ p)) ∂Γ).toReal := by
  have hmfin := isFiniteMeasure_slabRef hd hT
  have hκfin := phaseKernel_isFiniteKernel (d := d) (T := T) (Γ := Γ) (F := F) hFb
  set κ := phaseKernel d T Γ F with hκ
  let η : Kernel (PDE.Vec d) (SlabBase d) := Kernel.const (PDE.Vec d) (slabRef d T)
  have hac : ∀ ξ, κ ξ ≪ η ξ := by
    intro ξ s hs
    rw [Kernel.const_apply] at hs
    obtain ⟨t, hst, ht, hnull⟩ := exists_measurable_superset_of_null hs
    refine measure_mono_null hst ?_
    have h1 : slabBase d T t = 0 := by
      rw [slabRef, withDensity_apply _ ht] at hnull
      have h2 := (lintegral_eq_zero_iff' (measurable_slabWeight d).aemeasurable).1 hnull
      have h3 :=
        h2.mono (fun x hx => (slabWeight_pos x).ne' hx)
      rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at h3
      have := congrArg (fun μ => μ univ) h3
      simpa using this
    have h2 := phaseKernel_le (T := T) (Γ := Γ) hF hFb ξ ht
    rw [hg t ht, setLIntegral_measure_zero _ _ h1] at h2
    exact nonpos_iff_eq_zero.1 h2
  have hset : ∀ (ξ : PDE.Vec d) (E : Set (SlabBase d)), MeasurableSet E →
      ∫⁻ y in E, slabWeight d y * κ.rnDeriv η ξ y ∂slabBase d T = κ ξ E := by
    intro ξ E hE
    have hr : Measurable (fun y => κ.rnDeriv η ξ y) :=
      (Kernel.measurable_rnDeriv κ η).comp (measurable_const.prodMk measurable_id)
    have h2 := Kernel.setLIntegral_rnDeriv (hac ξ) hE
    rw [Kernel.const_apply] at h2
    exact (setLIntegral_withDensity_eq_setLIntegral_mul (slabBase d T) (measurable_slabWeight d) hr hE).symm.trans h2
  refine ⟨fun ξ y => (slabWeight d y * κ.rnDeriv η ξ y).toReal, ?_,
    fun ξ y => ENNReal.toReal_nonneg,
    fun ξ => ?_⟩
  · exact ENNReal.measurable_toReal.comp (((measurable_slabWeight d).comp measurable_snd).mul
      (Kernel.measurable_rnDeriv κ η))
  · have hr : Measurable (fun y => κ.rnDeriv η ξ y) :=
      (Kernel.measurable_rnDeriv κ η).comp (measurable_const.prodMk measurable_id)
    have hmeas : Measurable (fun y => slabWeight d y * κ.rnDeriv η ξ y) :=
      (measurable_slabWeight d).mul hr
    have hfin : ∫⁻ y, slabWeight d y * κ.rnDeriv η ξ y ∂slabBase d T ≠ ⊤ := by
      have := hset ξ univ MeasurableSet.univ
      rw [Measure.restrict_univ] at this
      rw [this]
      exact measure_ne_top _ _
    refine ⟨integrable_toReal_of_lintegral_ne_top hmeas.aemeasurable hfin, fun E hE => ?_⟩
    have hfinE : ∫⁻ y in E, slabWeight d y * κ.rnDeriv η ξ y ∂slabBase d T ≠ ⊤ := by
      rw [hset ξ E hE]; exact measure_ne_top _ _
    rw [integral_toReal hmeas.aemeasurable (ae_lt_top hmeas hfinE), hset ξ E hE,
      hκ, phaseKernel_apply (T := T) (Γ := Γ) hF ξ hE]
    rfl

end

/-- **A jointly Borel family of Fourier densities.**  For every `ξ` the function `k^ξ` is a density
of the complex measure `E ↦ ∫_{(τ,w)∈E, T<τ<2T} e^{-iξ·z'} dΓ`, and `(ξ, y) ↦ k^ξ(y)` is Borel. -/
theorem exists_measurable_fourier_family (hd : 0 < d) {T : ℝ} (hT : 0 < T)
    (Γ : Measure (GreenCarrier d)) [IsFiniteMeasure (Γ.restrict (slabSet (d := d) T))]
    (g : SlabBase d → ℝ≥0∞)
    (hg : ∀ E : Set (SlabBase d), MeasurableSet E →
      Γ {p | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} = ∫⁻ y in E, g y ∂slabBase d T) :
    ∃ k : PDE.Vec d → SlabBase d → ℂ, Measurable (Function.uncurry k) ∧
      ∀ ξ, Integrable (k ξ) (slabBase d T) ∧ ∀ E : Set (SlabBase d), MeasurableSet E →
        ∫ y in E, k ξ y ∂slabBase d T =
          ∫ p in {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T},
            greenPhase d ξ p ∂Γ := by
  have hre : ∀ z : ℂ, ‖z‖ = 1 → z.re ≤ 1 :=
    fun z hz => (le_abs_self _).trans ((Complex.abs_re_le_norm z).trans hz.le)
  have hnre : ∀ z : ℂ, ‖z‖ = 1 → -z.re ≤ 1 :=
    fun z hz => (neg_le_abs _).trans ((Complex.abs_re_le_norm z).trans hz.le)
  have him : ∀ z : ℂ, ‖z‖ = 1 → z.im ≤ 1 :=
    fun z hz => (le_abs_self _).trans ((Complex.abs_im_le_norm z).trans hz.le)
  have hnim : ∀ z : ℂ, ‖z‖ = 1 → -z.im ≤ 1 :=
    fun z hz => (neg_le_abs _).trans ((Complex.abs_im_le_norm z).trans hz.le)
  obtain ⟨r1, hm1, -, h1⟩ := exists_channel (Γ := Γ) (F := fun z : ℂ => z.re) hd hT
    Complex.measurable_re hre g hg
  obtain ⟨r2, hm2, -, h2⟩ := exists_channel (Γ := Γ) (F := fun z : ℂ => -z.re) hd hT
    Complex.measurable_re.neg hnre g hg
  obtain ⟨r3, hm3, -, h3⟩ := exists_channel (Γ := Γ) (F := fun z : ℂ => z.im) hd hT
    Complex.measurable_im him g hg
  obtain ⟨r4, hm4, -, h4⟩ := exists_channel (Γ := Γ) (F := fun z : ℂ => -z.im) hd hT
    Complex.measurable_im.neg hnim g hg
  refine ⟨fun ξ y => ((r1 ξ y - r2 ξ y : ℝ) : ℂ) + ((r3 ξ y - r4 ξ y : ℝ) : ℂ) * Complex.I,
    ?_, fun ξ => ⟨?_, fun E hE => ?_⟩⟩
  · exact ((Complex.measurable_ofReal.comp (hm1.sub hm2)).add
      ((Complex.measurable_ofReal.comp (hm3.sub hm4)).mul_const Complex.I))
  · exact (((h1 ξ).1.sub (h2 ξ).1).ofReal).add
      (((h3 ξ).1.sub (h4 ξ).1).ofReal.mul_const Complex.I)
  · have hki : Integrable (fun y => ((r1 ξ y - r2 ξ y : ℝ) : ℂ) +
        ((r3 ξ y - r4 ξ y : ℝ) : ℂ) * Complex.I) (slabBase d T) :=
      (((h1 ξ).1.sub (h2 ξ).1).ofReal).add
        (((h3 ξ).1.sub (h4 ξ).1).ofReal.mul_const Complex.I)
    have hsub : {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} ⊆
        slabSet T := fun p hp => ⟨hp.2.1, hp.2.2⟩
    have hΓE : IsFiniteMeasure (Γ.restrict
        {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T}) :=
      isFiniteMeasure_of_le (Γ.restrict (slabSet (d := d) T)) (Measure.restrict_mono hsub le_rfl)
    have hφ : Integrable (greenPhase d ξ) (Γ.restrict
        {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T}) :=
      integrable_phase_finite _ _ (measurable_greenPhase ξ) (norm_greenPhase ξ)
    apply Complex.ext
    · have e1 := integral_re (hki.restrict (s := E))
      have e2 := integral_re hφ
      simp only [RCLike.re_eq_complex_re] at e1 e2
      rw [← e1, ← e2]
      simp
      rw [integral_sub (h1 ξ).1.integrableOn (h2 ξ).1.integrableOn, (h1 ξ).2 E hE, (h2 ξ).2 E hE]
      exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hφ.re).symm
    · have e1 := integral_im (hki.restrict (s := E))
      have e2 := integral_im hφ
      simp only [RCLike.im_eq_complex_im] at e1 e2
      rw [← e1, ← e2]
      simp
      rw [integral_sub (h3 ξ).1.integrableOn (h4 ξ).1.integrableOn, (h3 ξ).2 E hE, (h4 ξ).2 E hE]
      exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hφ.im).symm

end


/-- The Gauss-type constant `∫ exp(-c|ζ|^{2/3}) dζ` of the frequency integral. -/
def slabFreqConstant (d : ℕ) (c : ℝ) : ℝ := (∫⁻ ζ, decayProfile d c ζ).toReal

/-- The structural constant `K₁(γ) = 2^{β_γ} (1 + C)(1 + (2π)^{-d} A_{c/2})`. -/
def slabK1 (d : ℕ) (Cdec cdec γ : ℝ) : ℝ :=
  (2 : ℝ) ^ slabBeta d γ * (1 + Cdec) *
    (1 + ((2 * Real.pi) ^ d)⁻¹ * slabFreqConstant d (cdec / 2))

/-- The constants `C_γ` of Lemma 5.1: `C_γ^{occ} · K₁(γ)`. -/
def slabConstant' (d : ℕ) (Cocc : ℝ → ℝ) (Cdec cdec : ℝ) (γ : ℝ) : ℝ≥0 :=
  Real.toNNReal (Cocc γ * slabK1 d Cdec cdec γ)

lemma one_le_slabK1_factor {d : ℕ} {Cdec : ℝ} (hCdec : 0 < Cdec) (cdec : ℝ) :
    1 ≤ (1 + Cdec) * (1 + ((2 * Real.pi) ^ d)⁻¹ * slabFreqConstant d (cdec / 2)) := by
  have : 0 ≤ ((2 * Real.pi) ^ d)⁻¹ * slabFreqConstant d (cdec / 2) := by
    unfold slabFreqConstant; positivity
  nlinarith


/-- The frequency-integral arithmetic in `ℝ≥0∞`. -/
lemma freq_ennreal (Co Cd a M t1 t2 A q K1 s : ℝ) (hCo : 0 ≤ Co) (hCd : 0 ≤ Cd) (ha : 0 ≤ a)
    (hM : 0 ≤ M) (ht1 : 0 ≤ t1) (ht2 : 0 ≤ t2) (hA : 0 ≤ A) (hq : 0 ≤ q)
    (hK : K1 = a * (1 + Cd) * (1 + q * A)) (hs : s = t1 * t2) :
    ENNReal.ofReal q * (ENNReal.ofReal (Co * Cd * a) * ENNReal.ofReal M * ENNReal.ofReal t1 *
        (ENNReal.ofReal t2 * ENNReal.ofReal A)) ≤
      ENNReal.ofReal (Co * K1) * ENNReal.ofReal M * ENNReal.ofReal s  := by
  have freq_arith :
      q * ((Co * Cd * a) * M * t1 * (t2 * A)) ≤
      (Co * (a * (1 + Cd) * (1 + q * A))) * M * (t1 * t2) := by
    have hP : 0 ≤ Co * a * M * t1 * t2 := by positivity
    have key : q * Cd * A ≤ (1 + Cd) * (1 + q * A) := by
      nlinarith [mul_nonneg hq hA, mul_nonneg hCd (mul_nonneg hq hA)]
    calc q * ((Co * Cd * a) * M * t1 * (t2 * A)) = (Co * a * M * t1 * t2) * (q * Cd * A) := by ring
      _ ≤ (Co * a * M * t1 * t2) * ((1 + Cd) * (1 + q * A)) := mul_le_mul_of_nonneg_left key hP
      _ = _ := by ring
  have h1 : 0 ≤ Co * Cd * a := by positivity
  have h2 : 0 ≤ Co * Cd * a * M := by positivity
  have h3 : 0 ≤ Co * Cd * a * M * t1 := by positivity
  have h4 : 0 ≤ t2 * A := by positivity
  have hK0 : 0 ≤ K1 := by rw [hK]; positivity
  rw [← ENNReal.ofReal_mul ht2, ← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h2,
    ← ENNReal.ofReal_mul h3, ← ENNReal.ofReal_mul hq, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hK, hs]
  exact freq_arith

/-- The Fourier part of `SlabFourierBounds` for an explicit family `k` of densities: integrable
densities of the Fourier marginals, the decay bound, and the integrated height bound. -/
def SlabFourierBoundsFamily (d : ℕ) (C : ℝ → ℝ≥0) (c : ℝ) (M : ℝ≥0∞) (T : ℝ)
    (Γ : Measure (GreenCarrier d)) (k : PDE.Vec d → SlabBase d → ℂ) : Prop :=
  (∀ ξ, Integrable (k ξ) (slabBase d T) ∧
    ∀ E : Set (SlabBase d), MeasurableSet E →
      ∫ y in E, k ξ y ∂slabBase d T =
        ∫ p in {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T},
          Complex.exp (-((PDE.vecDot ξ p.2.2 : ℝ) * Complex.I)) ∂Γ) ∧
  ∀ γ : ℝ, 1 ≤ γ → γ ≤ slabGamma0 d →
    (∀ ξ, eLpNorm (k ξ) (ENNReal.ofReal γ) (slabBase d T) ≤
      (C γ : ℝ≥0∞) * M * ENNReal.ofReal (T ^ slabBeta d γ) *
        ENNReal.ofReal (Real.exp (-(c * T * PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3))))) ∧
    ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
        ∫⁻ ξ, eLpNorm (k ξ) (ENNReal.ofReal γ) (slabBase d T) ≤
      (C γ : ℝ≥0∞) * M * ENNReal.ofReal (T ^ (slabBeta d γ - 3 * (d : ℝ) / 2))

/-- **Lemma 5.1 for one realized kernel**, conditional on the occupation and decay
estimates for that kernel (constants `Cocc`, `Cdec`, `cdec`).  The Fourier densities can be taken
jointly Borel in `(ξ, y)`, so that `ξ ↦ ‖k^ξ‖_{L^γ}` is measurable. -/
theorem slabFourierBounds_meas_of_occupation_decay_kernel {d : ℕ} (hd : 0 < d)
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ K)
    (hcomp : K.HasComposition MeasurableSet.univ)
    (Cocc : ℝ → ℝ) (hocc : OccupationBoundedBy K Cocc)
    (Cdec cdec : ℝ) (hCdec : 0 < Cdec) (hcdec : 0 < cdec) (hdec : FourierDecayBoundedBy K Cdec cdec)
    (σ₀ : ℝ) (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)) (hΓ : IsGreenMeasure K σ₀ ⊤ μ Γ)
    {T : ℝ} (hT : 0 < T) :
    SlabFourierBounds d (slabConstant' d Cocc Cdec cdec) (cdec / 2) (μ univ) T Γ ∧
      ∃ k : PDE.Vec d → SlabBase d → ℂ, Measurable (Function.uncurry k) ∧
        SlabFourierBoundsFamily d (slabConstant' d Cocc Cdec cdec) (cdec / 2) (μ univ) T Γ k := by
  obtain ⟨g, hgm, hgE, hgnorm⟩ := slab_marginal_density hd K hcov Cocc hocc σ₀ μ Γ hΓ hT
  have hΓfin : IsFiniteMeasure (Γ.restrict (slabSet (d := d) T)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (green_slab_le K σ₀ μ Γ hΓ hT).trans_lt
      (ENNReal.mul_lt_top (measure_lt_top _ _) ENNReal.ofReal_lt_top)
  obtain ⟨kf, hkm, hkf⟩ := exists_measurable_fourier_family hd hT Γ g hgE
  have hk : ∀ (ξ : PDE.Vec d) (γ : ℝ), 1 ≤ γ → γ ≤ slabGamma0 d →
      eLpNorm (kf ξ) (ENNReal.ofReal γ) (slabBase d T) ≤
        ENNReal.ofReal (Cocc γ * Cdec * 2 ^ slabBeta d γ) * μ univ *
          ENNReal.ofReal (T ^ slabBeta d γ) *
          ENNReal.ofReal (Real.exp
            (-((cdec / 2) * T * PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3)))) :=
    fun ξ => slab_fourier_density_bound K hd hcov hcomp Cocc hocc Cdec cdec hCdec hdec σ₀ μ Γ hΓ
      hT ξ (kf ξ) (hkf ξ).1 (hkf ξ).2
  have hCγ : ∀ γ : ℝ, 1 ≤ γ → γ ≤ slabGamma0 d →
      (slabConstant' d Cocc Cdec cdec γ : ℝ≥0∞) = ENNReal.ofReal (Cocc γ * slabK1 d Cdec cdec γ) :=
    fun _ _ _ => rfl
  have hfin : ∫⁻ ζ, decayProfile d (cdec / 2) ζ < ⊤ :=
    lintegral_decayProfile_lt_top hd (by linarith)
  have hAeq : ∫⁻ ζ, decayProfile d (cdec / 2) ζ = ENNReal.ofReal (slabFreqConstant d (cdec / 2)) :=
    (ENNReal.ofReal_toReal hfin.ne).symm
  have hA0 : 0 ≤ slabFreqConstant d (cdec / 2) := ENNReal.toReal_nonneg
  set M : ℝ := (μ univ).toReal with hMdef
  have hM : μ univ = ENNReal.ofReal M := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hq0 : 0 ≤ ((2 * Real.pi) ^ d)⁻¹ := by positivity
  have hF1 := one_le_slabK1_factor (d := d) hCdec cdec
  have hF2 : Cdec ≤ (1 + Cdec) * (1 + ((2 * Real.pi) ^ d)⁻¹ * slabFreqConstant d (cdec / 2)) := by
    nlinarith [mul_nonneg hq0 hA0]
  have hK1 : ∀ γ : ℝ, slabK1 d Cdec cdec γ =
      2 ^ slabBeta d γ * ((1 + Cdec) *
        (1 + ((2 * Real.pi) ^ d)⁻¹ * slabFreqConstant d (cdec / 2))) := fun γ => by
    unfold slabK1; ring
  have hfam : SlabFourierBoundsFamily d (slabConstant' d Cocc Cdec cdec) (cdec / 2) (μ univ) T Γ
      kf := by
    refine ⟨fun ξ => ⟨(hkf ξ).1, (hkf ξ).2⟩, fun γ h1 h2 => ⟨fun ξ => ?_, ?_⟩⟩
    · have hC0 : 0 ≤ Cocc γ := hocc.1 γ h1 h2
      have h2b := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (slabBeta d γ)
      refine (hk ξ γ h1 h2).trans ?_
      rw [hCγ γ h1 h2]
      have hle : ENNReal.ofReal (Cocc γ * Cdec * (2 : ℝ) ^ slabBeta d γ) ≤
          ENNReal.ofReal (Cocc γ * slabK1 d Cdec cdec γ) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hK1]
        nlinarith [mul_nonneg hC0 h2b, mul_nonneg hC0 hCdec.le]
      exact mul_le_mul' (mul_le_mul' (mul_le_mul' hle le_rfl) le_rfl) le_rfl
    · have hC0 : 0 ≤ Cocc γ := hocc.1 γ h1 h2
      have h2b := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (slabBeta d γ)
      have ht1 : 0 ≤ T ^ slabBeta d γ := Real.rpow_nonneg hT.le _
      have ht2 : 0 ≤ T ^ (-(3 * (d : ℝ) / 2)) := Real.rpow_nonneg hT.le _
      set D : ℝ≥0∞ := ENNReal.ofReal (Cocc γ * Cdec * (2 : ℝ) ^ slabBeta d γ) * μ univ *
        ENNReal.ofReal (T ^ slabBeta d γ) with hD
      have hDtop : D ≠ ⊤ := by
        rw [hD]
        exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
          ENNReal.ofReal_ne_top
      calc ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
            ∫⁻ ξ, eLpNorm (kf ξ) (ENNReal.ofReal γ) (slabBase d T)
          ≤ ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
            ∫⁻ ξ : PDE.Vec d, D * ENNReal.ofReal (Real.exp
              (-((cdec / 2) * T * PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3)))) :=
            mul_le_mul' le_rfl (lintegral_mono (fun ξ => hk ξ γ h1 h2))
        _ = ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
            (D * (ENNReal.ofReal (T ^ (-(3 * (d : ℝ) / 2))) *
              ENNReal.ofReal (slabFreqConstant d (cdec / 2)))) := by
            rw [lintegral_const_mul' D _ hDtop, (lintegral_decayProfile_scaling d (cdec / 2) T hT), hAeq]
        _ ≤ _ := by
            rw [hCγ γ h1 h2, hD, hM]
            have hrp : T ^ (slabBeta d γ - 3 * (d : ℝ) / 2) =
                T ^ slabBeta d γ * T ^ (-(3 * (d : ℝ) / 2)) := by
              rw [← Real.rpow_add hT, sub_eq_add_neg]
            rw [hrp]
            exact freq_ennreal (Cocc γ) Cdec ((2 : ℝ) ^ slabBeta d γ) M (T ^ slabBeta d γ)
              (T ^ (-(3 * (d : ℝ) / 2))) (slabFreqConstant d (cdec / 2)) (((2 * Real.pi) ^ d)⁻¹)
              (slabK1 d Cdec cdec γ) _ hC0 hCdec.le h2b hM0 ht1 ht2 hA0 hq0
              (by unfold slabK1; ring) rfl
  refine ⟨⟨⟨g, hgm.aemeasurable, hgE, fun γ h1 h2 => ?_⟩, kf, hfam⟩, kf, hkm, hfam⟩
  · have hC0 : 0 ≤ Cocc γ := hocc.1 γ h1 h2
    refine (hgnorm γ h1 h2).trans ?_
    rw [hCγ γ h1 h2]
    have hle : ENNReal.ofReal (Cocc γ * (2 : ℝ) ^ slabBeta d γ) ≤
        ENNReal.ofReal (Cocc γ * slabK1 d Cdec cdec γ) := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hK1]
      nlinarith [mul_nonneg hC0 (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (slabBeta d γ))]
    exact mul_le_mul' (mul_le_mul' hle le_rfl) le_rfl


/-- **Lemma 5.1 (case W), family level, in the form consumed by Theorem 1.1.**  Exactly the
conclusion of `slabFourierBounds_meas_of_occupation_decay` without the measurability clause: the
`hbounds` premise of `Green.green_density_of_slab_marginals` and of
`TheoremA.green_density_bound_of_slabFourierBounds`. -/
theorem slabFourierBounds_of_occupation_decay {d : ℕ} (hd : 1 ≤ d) (lam Lam : ℝ)
    (hocc : ParabolicOccupationFamily d lam Lam) (hdec : FourierDecayFamily d lam Lam) :
    ∃ (C : ℝ → ℝ≥0) (c : ℝ), ∀ (B : CoefficientField d),
      IsSectionTwoCoefficient lam Lam B →
      ∀ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
        (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
      RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ
        (zIndependentCoefficient B) (identityDrift d) S K →
      ∀ (σ₀ : ℝ) (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
        [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)), IsGreenMeasure K σ₀ ⊤ μ Γ →
      ∀ T : ℝ, 0 < T → SlabFourierBounds d C c (μ univ) T Γ  := by
  have slabFourierBounds_meas_of_occupation_decay :
      ∃ (C : ℝ → ℝ≥0) (c : ℝ), ∀ (B : CoefficientField d),
      IsSectionTwoCoefficient lam Lam B →
      ∀ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
        (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
      RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ
        (zIndependentCoefficient B) (identityDrift d) S K →
      ∀ (σ₀ : ℝ) (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
        [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)), IsGreenMeasure K σ₀ ⊤ μ Γ →
      ∀ T : ℝ, 0 < T → SlabFourierBounds d C c (μ univ) T Γ ∧
        ∃ k : PDE.Vec d → SlabBase d → ℂ, Measurable (Function.uncurry k) ∧
          SlabFourierBoundsFamily d C c (μ univ) T Γ k := by
    have isTranslationCovariant_of_realizes {d : ℕ} (B : CoefficientField d) (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d))) (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))) (hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
        MeasurableSet.univ (zIndependentCoefficient B) (identityDrift d) S K) :
        IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ K := open HypoellipticAleksandrov.KineticAleksandrov.Scaling in by
      intro σ τ hστ h0 p
      let r1 : {r : ℝ // 0 < r} := ⟨1, one_pos⟩
      let Φ := KineticAffineScaling.ofRadius (d := d) 0 0 h0 (identityDrift d) r1
      have hmaps : Φ.MapsDomain (wholeSpace d) (fun _ => (0 : PDE.Vec d)) (wholeSpace d)
          (fun _ => (0 : PDE.Vec d)) := KineticAffineScaling.mapsDomain_wholeSpace Φ
      have hB : scaledCoefficient B 0 0 r1 = B := by
        funext t Y
        simp [scaledCoefficient, r1]
      have hreal' : RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          (measurableSet_of_isAdmissibleEvolutionDomain (wholeSpace_admissible d))
          (Φ.coefficient (zIndependentCoefficient B)) (Φ.drift (identityDrift d)) S K := by
        rw [KineticAffineScaling.ofRadius_coefficient, KineticAffineScaling.ofRadius_drift,
          scaledDrift_identity, hB]
        exact hreal
      have hmaster : ∀ q' : EvolutionQuery (wholeSpace d) (fun _ => (0 : PDE.Vec d)),
          K.master q' = (K.master (KineticAffineScaling.queryMap hmaps q')).map
            (Φ.ambientEquiv q'.1.2.1).symm := fun q' =>
        KineticAffineScaling.realizes_master_eq_map hmaps
          (wholeSpace_admissible d) (zeroCurve_piecewiseC1 d) (wholeSpace_admissible d) hreal hreal' q'
      set q' := evolutionQueryOfState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ τ hστ p with hq'
      have hqm : KineticAffineScaling.queryMap hmaps q' =
          evolutionQueryOfState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ τ hστ
            (evolutionStateShift (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ h0 p) := by
        apply Subtype.ext
        simp [KineticAffineScaling.queryMap, KineticAffineScaling.rawQuery, KineticAffineScaling.time,
          KineticAffineScaling.position, KineticAffineScaling.transport, Φ,
          KineticAffineScaling.ofRadius,
          r1, hq', evolutionQueryOfState, evolutionStateShift, evolutionAmbientStateShift,
          identityDrift, add_comm]
      have hM : Measure.map (evolutionAmbientStateShift h0) (K.master q') =
          K.master (evolutionQueryOfState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ τ hστ
            (evolutionStateShift (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ h0 p)) := by
        rw [hmaster q', hqm, Measure.map_map (measurable_evolutionAmbientStateShift h0)
          (Φ.ambientEquiv _).symm.measurable]
        have hid : evolutionAmbientStateShift h0 ∘ (Φ.ambientEquiv (q'.1.2.1)).symm = id := by
          funext x
          simp [evolutionAmbientStateShift, KineticAffineScaling.positionInv,
            KineticAffineScaling.transportInv, Φ, KineticAffineScaling.ofRadius, r1, identityDrift]
        rw [hid, Measure.map_id]
      have hU : MeasurableSet (wholeSpace d) := MeasurableSet.univ
      -- pass from master measures to fibre kernels
      have hemb := MeasurableEmbedding.subtype_coe
        (measurableSet_evolutionStateSet (γ := fun _ => (0 : PDE.Vec d)) hU τ)
      rw [← hemb.comap_map (Measure.map (evolutionStateShift (wholeSpace d) (fun _ => 0) τ h0)
          (K.fiberKernel hU σ τ hστ p)),
        ← hemb.comap_map (K.fiberKernel hU σ τ hστ
          (evolutionStateShift (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ h0 p))]
      congr 1
      rw [Measure.map_map measurable_subtype_coe (measurable_evolutionStateShift _ _ _ _),
        K.map_fiberKernel_eq_master hU σ τ hστ _]
      have hc : ((↑) : EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) τ →
          EvolutionAmbientState d) ∘ evolutionStateShift (wholeSpace d) (fun _ => 0) τ h0 =
          evolutionAmbientStateShift h0 ∘ ((↑) : EvolutionState (wholeSpace d)
            (fun _ => (0 : PDE.Vec d)) τ → EvolutionAmbientState d) := rfl
      rw [hc, ← Measure.map_map (measurable_evolutionAmbientStateShift h0) measurable_subtype_coe,
        K.map_fiberKernel_eq_master hU σ τ hστ p]
      exact hM
    obtain ⟨Cocc, hoc⟩ := hocc
    obtain ⟨Cdec, cdec, hCdec, hcdec, hdc⟩ := hdec
    refine ⟨slabConstant' d Cocc Cdec cdec, cdec / 2, fun B hB S K hreal σ₀ μ _ Γ hΓ T hT => ?_⟩
    exact slabFourierBounds_meas_of_occupation_decay_kernel (Nat.pos_of_ne_zero (by omega)) K
      (isTranslationCovariant_of_realizes B S K hreal) hreal.2.2.2 Cocc (hoc B hB S K hreal)
      Cdec cdec hCdec hcdec (hdc B hB S K hreal) σ₀ μ Γ hΓ hT
  obtain ⟨C, c, h⟩ := slabFourierBounds_meas_of_occupation_decay
  exact ⟨C, c, fun B hB S K hreal σ₀ μ _ Γ hΓ T hT => (h B hB S K hreal σ₀ μ Γ hΓ T hT).1⟩

end HypoellipticAleksandrov.KineticAleksandrov.Green

