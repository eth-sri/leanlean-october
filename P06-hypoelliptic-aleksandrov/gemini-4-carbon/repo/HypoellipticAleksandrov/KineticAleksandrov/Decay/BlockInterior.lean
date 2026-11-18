module

public import Mathlib.MeasureTheory.Measure.Complex
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import Mathlib.MeasureTheory.Measure.Sub
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceNotation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
section

open MeasureTheory Set
open scoped ENNReal

/-- The phase factor `exp (-i θ)` of a real phase `θ`. -/
noncomputable def phaseFactor (θ : ℝ) : ℂ := Complex.exp (-Complex.I * (θ : ℂ))

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- `ν` is the phase projection of `N` for the phase `ψ`: on every measurable `E`, `ν E` is
`∫_{E × univ} exp (-i ψ) dN`. -/
def IsPhaseProjection (ψ : α × β → ℝ) (N : Measure (α × β)) (ν : ComplexMeasure α) : Prop :=
  ∀ E : Set α, MeasurableSet E → ν E = ∫ x in E ×ˢ (univ : Set β), phaseFactor (ψ x) ∂N

theorem norm_phaseFactor (θ : ℝ) : ‖phaseFactor θ‖ = 1 := by
  unfold phaseFactor
  rw [show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The phase factor is a `1`-Lipschitz function of the phase. -/
theorem norm_phaseFactor_sub_le (θ Φ : ℝ) : ‖phaseFactor θ - phaseFactor Φ‖ ≤ |θ - Φ| := by
  have h : phaseFactor θ - phaseFactor Φ =
      phaseFactor Φ * (Complex.exp (Complex.I * ((-(θ - Φ) : ℝ) : ℂ)) - 1) := by
    unfold phaseFactor
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    · push_cast; ring
  rw [h, norm_mul, norm_phaseFactor, one_mul]
  have h2 := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -(θ - Φ))
  rwa [norm_neg, Real.norm_eq_abs] at h2

theorem continuous_phaseFactor : Continuous phaseFactor := by
  unfold phaseFactor
  fun_prop

theorem measurable_phaseFactor_comp {ψ : α × β → ℝ} (hψ : Measurable ψ) :
    Measurable fun x => phaseFactor (ψ x) :=
  continuous_phaseFactor.measurable.comp hψ

theorem integrable_phaseFactor_comp {ψ : α × β → ℝ} (hψ : Measurable ψ)
    (N : Measure (α × β)) [IsFiniteMeasure N] :
    Integrable (fun x => phaseFactor (ψ x)) N :=
  Integrable.of_bound (measurable_phaseFactor_comp hψ).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun _ => (norm_phaseFactor _).le)


/-- The real mass of a cylinder is the real mass of the first marginal. -/
theorem real_map_fst_apply_eq {N : Measure (α × β)} {E : Set α} (hE : MeasurableSet E) :
    (N.map Prod.fst).real E = N.real (E ×ˢ (univ : Set β))  := by
  have map_fst_apply_eq :
      (N.map Prod.fst) E = N (E ×ˢ (univ : Set β)) := by
    rw [Measure.map_apply measurable_fst hE]
    congr 1
    ext x
    simp
  simp [Measure.real, map_fst_apply_eq]

/-- Norm of the cylinder phase integral: the phase has modulus one. -/
theorem norm_integral_phase_le (ψ : α × β → ℝ) (N : Measure (α × β)) [IsFiniteMeasure N]
    (S : Set (α × β)) :
    ‖∫ x in S, phaseFactor (ψ x) ∂N‖ ≤ N.real S := by
  have := norm_setIntegral_le_of_norm_le_const_ae (μ := N)
    (f := fun x => phaseFactor (ψ x)) (measure_lt_top N S)
    (Filter.Eventually.of_forall fun x => (norm_phaseFactor _).le)
  simpa using this

/-- Setwise phase-error estimate: if `F` is carried by `{|ψ - Φ| ≤ ε}` then on every
cylinder the phase integral differs from `exp (-iΦ)` times the mass by at most `ε` times
the mass. -/
theorem norm_integral_phase_sub_le {ψ : α × β → ℝ} (hψ : Measurable ψ)
    {F : Measure (α × β)} [IsFiniteMeasure F] {Φ ε : ℝ}
    (hsupp : ∀ᵐ x ∂F, |ψ x - Φ| ≤ ε) (S : Set (α × β)) :
    ‖(∫ x in S, phaseFactor (ψ x) ∂F) - phaseFactor Φ * (F.real S : ℂ)‖ ≤ ε * F.real S := by
  have hint : IntegrableOn (fun x => phaseFactor (ψ x)) S F :=
    (integrable_phaseFactor_comp hψ F).integrableOn
  have hconst : (∫ _ in S, phaseFactor Φ ∂F) = phaseFactor Φ * (F.real S : ℂ) := by
    rw [setIntegral_const, Complex.real_smul, mul_comm]
  rw [← hconst, ← integral_sub hint (integrableOn_const (measure_lt_top F S).ne)]
  refine norm_setIntegral_le_of_norm_le_const_ae (measure_lt_top F S) ?_
  filter_upwards [ae_restrict_of_ae hsupp] with x hx
  exact (norm_phaseFactor_sub_le _ _).trans hx

end
section

open MeasureTheory Set
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Integral of the phase over a set splits along `M = (M - (F₁ + F₂)) + F₁ + F₂`. -/
theorem integral_phase_split {ψ : α × β → ℝ} (hψ : Measurable ψ)
    {M F₁ F₂ : Measure (α × β)} [IsFiniteMeasure M] [IsFiniteMeasure F₁]
    [IsFiniteMeasure F₂] (hF : F₁ + F₂ ≤ M) (S : Set (α × β)) :
    ∫ x in S, phaseFactor (ψ x) ∂M =
      ∫ x in S, phaseFactor (ψ x) ∂(M - (F₁ + F₂)) + ∫ x in S, phaseFactor (ψ x) ∂F₁ +
        ∫ x in S, phaseFactor (ψ x) ∂F₂ := by
  have : IsFiniteMeasure (M - (F₁ + F₂)) := isFiniteMeasure_of_le M Measure.sub_le
  have hM : M = (M - (F₁ + F₂)) + F₁ + F₂ := by
    rw [add_assoc, Measure.sub_add_cancel_of_le hF]
  have hi : ∀ (N : Measure (α × β)) [IsFiniteMeasure N],
      Integrable (fun x => phaseFactor (ψ x)) (N.restrict S) := fun N _ =>
    (integrable_phaseFactor_comp hψ N).restrict
  conv_lhs => rw [hM]
  rw [Measure.restrict_add, Measure.restrict_add,
    integral_add_measure (by exact (hi _).add_measure (hi _)) (hi _),
    integral_add_measure (hi _) (hi _)]

/-- Setwise form of the cancellation estimate. -/
theorem norm_apply_le_cancellation {ψ : α × β → ℝ} (hψ : Measurable ψ)
    {M F₁ F₂ : Measure (α × β)} [IsFiniteMeasure M] [IsFiniteMeasure F₁]
    [IsFiniteMeasure F₂] (hF : F₁ + F₂ ≤ M) {Θ : Measure α}
    (hΘ₁ : F₁.map Prod.fst = Θ) (hΘ₂ : F₂.map Prod.fst = Θ) {Φ₁ Φ₂ ε : ℝ}
    (hΦ : phaseFactor Φ₁ + phaseFactor Φ₂ = 0)
    (hsupp₁ : ∀ᵐ x ∂F₁, |ψ x - Φ₁| ≤ ε) (hsupp₂ : ∀ᵐ x ∂F₂, |ψ x - Φ₂| ≤ ε)
    {ν : ComplexMeasure α} (hν : IsPhaseProjection ψ M ν) {E : Set α} (hE : MeasurableSet E) :
    ‖ν E‖ ≤ (M - (F₁ + F₂)).real (E ×ˢ (univ : Set β)) + 2 * ε * Θ.real E := by
  set S : Set (α × β) := E ×ˢ (univ : Set β) with hS
  have h₁ := norm_integral_phase_sub_le hψ hsupp₁ S
  have h₂ := norm_integral_phase_sub_le hψ hsupp₂ S
  have hr₁ : F₁.real S = Θ.real E := by rw [← hΘ₁, real_map_fst_apply_eq hE]
  have hr₂ : F₂.real S = Θ.real E := by rw [← hΘ₂, real_map_fst_apply_eq hE]
  rw [hr₁] at h₁
  rw [hr₂] at h₂
  have hν' : ν E = (∫ x in S, phaseFactor (ψ x) ∂(M - (F₁ + F₂))) +
      ((∫ x in S, phaseFactor (ψ x) ∂F₁) - phaseFactor Φ₁ * (Θ.real E : ℂ)) +
      ((∫ x in S, phaseFactor (ψ x) ∂F₂) - phaseFactor Φ₂ * (Θ.real E : ℂ)) +
      (phaseFactor Φ₁ + phaseFactor Φ₂) * (Θ.real E : ℂ) := by
    rw [hν E hE, integral_phase_split hψ hF]
    ring
  rw [hΦ, zero_mul, add_zero] at hν'
  have hR := norm_integral_phase_le ψ (M - (F₁ + F₂)) S
  have : IsFiniteMeasure (M - (F₁ + F₂)) := isFiniteMeasure_of_le M Measure.sub_le
  rw [hν']
  calc _ ≤ ‖∫ x in S, phaseFactor (ψ x) ∂(M - (F₁ + F₂))‖ +
        ‖(∫ x in S, phaseFactor (ψ x) ∂F₁) - phaseFactor Φ₁ * (Θ.real E : ℂ)‖ +
        ‖(∫ x in S, phaseFactor (ψ x) ∂F₂) - phaseFactor Φ₂ * (Θ.real E : ℂ)‖ :=
        (norm_add₃_le).trans_eq rfl
    _ ≤ _ := by linarith

/-- **Doeblin--Fourier cancellation (Lemma 3.7), domination form.**  The variation measure
of the phase projection of `M` is dominated by the first marginal of the remainder
`M - (F₁ + F₂)` plus `2ε Θ`. -/
theorem variation_le_remainder_add_of_cancellation {ψ : α × β → ℝ} (hψ : Measurable ψ)
    {M F₁ F₂ : Measure (α × β)} [IsFiniteMeasure M] [IsFiniteMeasure F₁]
    [IsFiniteMeasure F₂] (hF : F₁ + F₂ ≤ M) {Θ : Measure α}
    (hΘ₁ : F₁.map Prod.fst = Θ) (hΘ₂ : F₂.map Prod.fst = Θ) {Φ₁ Φ₂ ε : ℝ} (hε : 0 ≤ ε)
    (hΦ : phaseFactor Φ₁ + phaseFactor Φ₂ = 0)
    (hsupp₁ : ∀ᵐ x ∂F₁, |ψ x - Φ₁| ≤ ε) (hsupp₂ : ∀ᵐ x ∂F₂, |ψ x - Φ₂| ≤ ε)
    {ν : ComplexMeasure α} (hν : IsPhaseProjection ψ M ν) :
    ν.variation ≤ (M - (F₁ + F₂)).map Prod.fst + ENNReal.ofReal (2 * ε) • Θ := by
  have : IsFiniteMeasure (M - (F₁ + F₂)) := isFiniteMeasure_of_le M Measure.sub_le
  have : IsFiniteMeasure Θ := hΘ₁ ▸ inferInstance
  refine VectorMeasure.variation_le_of_forall_enorm_le fun E hE => ?_
  have h := norm_apply_le_cancellation hψ hF hΘ₁ hΘ₂ hΦ hsupp₁ hsupp₂ hν hE
  rw [← real_map_fst_apply_eq hE] at h
  rw [Measure.add_apply, Measure.smul_apply, smul_eq_mul, ← ofReal_norm]
  calc ENNReal.ofReal ‖ν E‖
      ≤ ENNReal.ofReal (((M - (F₁ + F₂)).map Prod.fst).real E +
        2 * ε * Θ.real E) := ENNReal.ofReal_le_ofReal h
    _ = _ := by
      rw [Measure.real, Measure.real,
        ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity),
        ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- **Doeblin--Fourier cancellation (Lemma 3.7)**, additive `ℝ≥0∞` form:
`‖ν‖_TV + 2 (1 - ε) Θ(α) ≤ M(α × β)`. -/
theorem totalVariation_add_le_of_cancellation {ψ : α × β → ℝ} (hψ : Measurable ψ)
    {M F₁ F₂ : Measure (α × β)} [IsFiniteMeasure M] [IsFiniteMeasure F₁]
    [IsFiniteMeasure F₂] (hF : F₁ + F₂ ≤ M) {Θ : Measure α}
    (hΘ₁ : F₁.map Prod.fst = Θ) (hΘ₂ : F₂.map Prod.fst = Θ) {Φ₁ Φ₂ ε : ℝ} (hε : 0 ≤ ε)
    (hε₁ : ε ≤ 1) (hΦ : phaseFactor Φ₁ + phaseFactor Φ₂ = 0)
    (hsupp₁ : ∀ᵐ x ∂F₁, |ψ x - Φ₁| ≤ ε) (hsupp₂ : ∀ᵐ x ∂F₂, |ψ x - Φ₂| ≤ ε)
    {ν : ComplexMeasure α} (hν : IsPhaseProjection ψ M ν) :
    ν.variation univ + ENNReal.ofReal (2 * (1 - ε)) * Θ univ ≤ M univ := by
  have h := variation_le_remainder_add_of_cancellation hψ hF hΘ₁ hΘ₂ hε hΦ hsupp₁ hsupp₂ hν
    univ
  rw [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ] at h
  have hM : M univ = (M - (F₁ + F₂)) univ + Θ univ + Θ univ := by
    have h := congrArg (fun m => m univ) (Measure.sub_add_cancel_of_le hF)
    have hu : ∀ F : Measure (α × β), F.map Prod.fst = Θ → F univ = Θ univ := fun F hF' => by
      rw [← hF', Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ]
    simp at h
    rw [← h, hu F₁ hΘ₁, hu F₂ hΘ₂, add_assoc]
  calc ν.variation univ + ENNReal.ofReal (2 * (1 - ε)) * Θ univ
      ≤ ((M - (F₁ + F₂)) univ + ENNReal.ofReal (2 * ε) * Θ univ) +
        ENNReal.ofReal (2 * (1 - ε)) * Θ univ := by gcongr
    _ = (M - (F₁ + F₂)) univ + (ENNReal.ofReal (2 * ε) + ENNReal.ofReal (2 * (1 - ε))) *
        Θ univ := by rw [add_assoc, add_mul]
    _ = (M - (F₁ + F₂)) univ + 2 * Θ univ := by
      rw [← ENNReal.ofReal_add (by positivity) (by linarith)]
      have : 2 * ε + 2 * (1 - ε) = 2 := by ring
      rw [this]
      simp
    _ = M univ := by rw [hM, two_mul, add_assoc]

/-- **Doeblin--Fourier cancellation (companion paper, Lemma 3.7).**  With the hypotheses of
Lemma Lemma 3.7 (the phase projection `ν` of `M` being the complex measure
`E ↦ ∫_{E × β} exp (-iψ) dM`):
`‖ν‖_TV ≤ M(α × β) - 2 (1 - ε) Θ(α)`. -/
theorem totalVariation_toReal_le_of_cancellation {ψ : α × β → ℝ} (hψ : Measurable ψ)
    {M F₁ F₂ : Measure (α × β)} [IsFiniteMeasure M] [IsFiniteMeasure F₁]
    [IsFiniteMeasure F₂] (hF : F₁ + F₂ ≤ M) {Θ : Measure α}
    (hΘ₁ : F₁.map Prod.fst = Θ) (hΘ₂ : F₂.map Prod.fst = Θ) {Φ₁ Φ₂ ε : ℝ} (hε : 0 ≤ ε)
    (hε₁ : ε < 1) (hΦ : phaseFactor Φ₁ + phaseFactor Φ₂ = 0)
    (hsupp₁ : ∀ᵐ x ∂F₁, |ψ x - Φ₁| ≤ ε) (hsupp₂ : ∀ᵐ x ∂F₂, |ψ x - Φ₂| ≤ ε)
    {ν : ComplexMeasure α} (hν : IsPhaseProjection ψ M ν) :
    (ν.variation univ).toReal ≤ M.real univ - 2 * (1 - ε) * Θ.real univ := by
  have : IsFiniteMeasure Θ := hΘ₁ ▸ inferInstance
  have h := totalVariation_add_le_of_cancellation hψ hF hΘ₁ hΘ₂ hε hε₁.le hΦ hsupp₁ hsupp₂ hν
  have h2 := ENNReal.toReal_mono (measure_ne_top M univ) h
  rw [ENNReal.toReal_add (ne_top_of_le_ne_top (measure_ne_top M univ) (le_self_add.trans h)) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at h2
  simp only [Measure.real] at h2 ⊢
  linarith

end
open Set MeasureTheory
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic

/-- Pi-separated phase factors are exact opposites. -/
theorem phaseFactor_add_eq_zero_of_sub_eq_pi {Φ1 Φ2 : ℝ}
    (hΦ : Φ2 - Φ1 = Real.pi) : phaseFactor Φ1 + phaseFactor Φ2 = 0 := by
  have he : Φ2 = Φ1 + Real.pi := by linarith only [hΦ]
  rw [he]
  unfold phaseFactor
  have hc : -Complex.I * ((Φ1 + Real.pi : ℝ) : ℂ) =
      -Complex.I * (Φ1 : ℂ) - Real.pi * Complex.I := by
    push_cast
    ring
  rw [hc, Complex.exp_sub_pi_mul_I]
  exact add_neg_cancel _

/-- The source interior cancellation estimate, with the retained mass floor discharged. -/
theorem block_interior_cancellation {d : ℕ}
    (ξ z0 : PDE.Vec d) (M F1 F2 : Measure (EvolutionAmbientState d))
    [IsFiniteMeasure M] [IsFiniteMeasure F1] [IsFiniteMeasure F2]
    (Θ : Measure (PDE.Vec d)) (m0 h q0 Φ1 Φ2 : ℝ)
    (hM : M.real univ ≤ 1) (hF : F1 + F2 ≤ M)
    (hΘ1 : F1.map Prod.fst = Θ) (hΘ2 : F2.map Prod.fst = Θ)
    (hmass : m0 * h * q0 / 2 ≤ Θ.real univ)
    (hΦ : Φ2 - Φ1 = Real.pi)
    (hs1 : ∀ᵐ x ∂F1, |phaseCoordinate ξ z0 x - Φ1| ≤ 1 / 4)
    (hs2 : ∀ᵐ x ∂F2, |phaseCoordinate ξ z0 x - Φ2| ≤ 1 / 4)
    (ν : ComplexMeasure (PDE.Vec d))
    (hν : IsPhaseProjection (phaseCoordinate ξ z0) M ν) :
    TV ν ≤ 1 - (3 / 2) * Θ.real univ ∧ TV ν ≤ 1 - (3 / 4) * m0 * h * q0 := by
  have hψ : Measurable (phaseCoordinate ξ z0) := by
    unfold phaseCoordinate PDE.vecDot
    fun_prop
  have he := totalVariation_toReal_le_of_cancellation hψ hF hΘ1 hΘ2
    (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
    (phaseFactor_add_eq_zero_of_sub_eq_pi hΦ) hs1 hs2 hν
  change TV ν ≤ _ at he
  constructor <;> linarith only [he, hM, hmass]

end HypoellipticAleksandrov.KineticAleksandrov.Decay

