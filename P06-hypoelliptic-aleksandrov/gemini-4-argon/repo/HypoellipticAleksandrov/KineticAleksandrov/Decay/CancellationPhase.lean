module

public import Mathlib.MeasureTheory.Measure.Complex
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-!
# Phase projections of positive measures and their variation

Let `N` be a finite positive measure on `α × β` and `ψ : α × β → ℝ` a phase function.
The *phase projection* of `N` is the complex measure `ν` on `α` characterised on every
measurable `E` by `ν E = ∫_{E × β} exp (-i ψ) dN`.  (The Fourier projection of the
Doeblin--Fourier cancellation lemma is the case `ψ (w, z') = ξ · (z' - z₀)`.)

This file contains the two elementary variation estimates behind the cancellation lemma:

* `variation_le_map_fst_of_isPhaseProjection` (companion paper, (3.11)): the variation of
  the phase projection of `N` is bounded by the first marginal of `N`;
* `variation_sub_phaseFactor_smul_le` and `variation_add_le_of_phase_opposite` (companion paper,
  Lemma 3.7): if the mass of `F` is carried by `{|ψ - Φ| ≤ ε}`, the
  phase projection of `F` differs from `exp (-iΦ) • (F.map Prod.fst)` by variation at most
  `ε * F(α × β)`, and two such projections with opposite central phases and a common
  marginal add up to variation at most `2ε Θ`.

Complex measures are `MeasureTheory.ComplexMeasure`, and total variation is
`VectorMeasure.variation` (an `ℝ≥0∞`-valued measure).  No integrability is assumed
beyond finiteness of the positive measures, because the phase has modulus one.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

open MeasureTheory Set
open scoped ENNReal

/- The phase factor `exp (-i θ)` of a real phase `θ`. -/
noncomputable def phaseFactor (θ : ℝ) : ℂ := Complex.exp (-Complex.I * (θ : ℂ))

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/- `ν` is the phase projection of `N` for the phase `ψ`: on every measurable `E`, `ν E` is
`∫_{E × univ} exp (-i ψ) dN`. -/
def IsPhaseProjection (ψ : α × β → ℝ) (N : Measure (α × β)) (ν : ComplexMeasure α) : Prop :=
  ∀ E : Set α, MeasurableSet E → ν E = ∫ x in E ×ˢ (univ : Set β), phaseFactor (ψ x) ∂N

theorem norm_phaseFactor (θ : ℝ) : ‖phaseFactor θ‖ = 1 := by
  unfold phaseFactor
  rw [show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/- The phase factor is a `1`-Lipschitz function of the phase. -/
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

/- The first marginal of a measure of a measurable set is the mass of its cylinder. -/
theorem map_fst_apply_eq {N : Measure (α × β)} {E } (hE : MeasurableSet E) :
    (N.map Prod.fst) E = N (E ×ˢ (univ : Set β)) := by
  rw [Measure.map_apply measurable_fst hE]
  congr 1
  ext x
  simp

/- The real mass of a cylinder is the real mass of the first marginal. -/
theorem real_map_fst_apply_eq {N : Measure (α × β)} {E } (hE : MeasurableSet E) :
    (N.map Prod.fst).real E = N.real (E ×ˢ (univ : Set β)) := by
  simp [Measure.real, map_fst_apply_eq hE]

/- Norm of the cylinder phase integral: the phase has modulus one. -/
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

end HypoellipticAleksandrov.KineticAleksandrov.Decay
