/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.WithDensity
public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.MeasureTheory.Integral.Prod

/-! Integrating against measurable families of measures, without a uniform mass bound. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- A measurable family of finite measures is an s-finite kernel. Normalize the masses
by `μ u univ + 1`, then recover the original kernel by a finite density. -/
private theorem isSFiniteKernel_of_finite_family
    {U E : Type*} [MeasurableSpace U] [MeasurableSpace E]
    (μ : U → Measure E) (hμ : Measurable μ) (hfinite : ∀ u, IsFiniteMeasure (μ u)) :
    IsSFiniteKernel (⟨μ, hμ⟩ : Kernel U E) := by
  let c : U → ℝ≥0∞ := fun u => μ u Set.univ + 1
  have hc : Measurable c :=
    ((Measure.measurable_coe MeasurableSet.univ).comp hμ).add measurable_const
  have hc0 (u : U) : c u ≠ 0 := by simp [c]
  have hcTop (u : U) : c u ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.one_ne_top⟩
  let κ : Kernel U E := ⟨fun u => (c u)⁻¹ • μ u,
    Measure.measurable_of_measurable_coe _ fun s hs => by
      simp only [Measure.smul_apply, smul_eq_mul]
      exact hc.inv.mul ((Measure.measurable_coe hs).comp hμ)⟩
  haveI : IsFiniteKernel κ := ⟨⟨1, ENNReal.one_lt_top, fun u => by
    change (c u)⁻¹ * μ u Set.univ ≤ 1
    exact (mul_le_mul' le_rfl (le_self_add : μ u Set.univ ≤ c u)).trans_eq
      (ENNReal.inv_mul_cancel (hc0 u) (hcTop u))⟩⟩
  have heq : (⟨μ, hμ⟩ : Kernel U E) = κ.withDensity (fun u _ => c u) := by
    ext u s hs
    rw [Kernel.withDensity_apply' κ (f := fun u _ => c u) (hc.comp measurable_fst) u s, lintegral_const,
      Measure.restrict_apply_univ]
    change μ u s = c u * ((c u)⁻¹ * μ u s)
    rw [← mul_assoc, ENNReal.mul_inv_cancel (hc0 u) (hcTop u), one_mul]
  rw [heq]
  exact Kernel.IsSFiniteKernel.withDensity κ fun u _ => hcTop u

/-- A jointly measurable integrand can be integrated against a measurable family of finite
measures. -/
theorem measurable_lintegral_finite_family
    {U E : Type*} [MeasurableSpace U] [MeasurableSpace E]
    (μ : U → Measure E) (hμ : Measurable μ) (hfinite : ∀ u, IsFiniteMeasure (μ u))
    (f : U × E → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun u => ∫⁻ x, f (u, x) ∂μ u) := by
  let κ : Kernel U E := ⟨μ, hμ⟩
  letI : IsSFiniteKernel κ := isSFiniteKernel_of_finite_family μ hμ hfinite
  exact hf.lintegral_kernel_prod_right' (κ := κ)

/-- Bochner integration for jointly strongly measurable integrands and finite measures. -/
theorem stronglyMeasurable_integral_finite_family
    {U E B : Type*} [MeasurableSpace U] [MeasurableSpace E]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (μ : U → Measure E) (hμ : Measurable μ) (hfinite : ∀ u, IsFiniteMeasure (μ u))
    (f : U × E → B) (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun u => ∫ x, f (u, x) ∂μ u) := by
  let κ : Kernel U E := ⟨μ, hμ⟩
  letI : IsSFiniteKernel κ := isSFiniteKernel_of_finite_family μ hμ hfinite
  exact hf.integral_kernel_prod_right' (κ := κ)

/-- For a fixed integrand, measurability in the measure requires no mass bound. -/
theorem measurable_integral_of_measurable_measure
    {U E B : Type*} [MeasurableSpace U] [MeasurableSpace E]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]
    {μ : U → Measure E} (hμ : Measurable μ) {f : E → B} (hf : StronglyMeasurable f) :
    Measurable (fun u => ∫ x, f x ∂μ u) :=
  (hf.integral_kernel (κ := ⟨μ, hμ⟩)).measurable

/-- A jointly measurable test integrated against a varying finite measure. -/
theorem measurable_lintegral_finiteMeasure_parameter
    {X E : Type*} [MeasurableSpace X] [MeasurableSpace E]
    {f : X × E → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun z : X × FiniteMeasure E => ∫⁻ y, f (z.1, y) ∂(z.2 : Measure E)) :=
  measurable_lintegral_finite_family (fun z : X × FiniteMeasure E => z.2.toMeasure)
    (measurable_subtype_coe.comp measurable_snd) (fun z => z.2.prop) _
    (hf.comp (measurable_fst.fst.prodMk measurable_snd))

/-- Joint measurability of signed integrals against a varying finite measure. -/
theorem measurable_integral_finiteMeasure_parameter
    {U E B : Type*} [MeasurableSpace U] [MeasurableSpace E]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [SecondCountableTopology B]
    [MeasurableSpace B] [BorelSpace B] {f : U × E → B} (hf : Measurable f) :
    Measurable (fun q : U × FiniteMeasure E => ∫ x, f (q.1, x) ∂(q.2 : Measure E)) :=
  (stronglyMeasurable_integral_finite_family (fun q : U × FiniteMeasure E => q.2.toMeasure)
    (measurable_subtype_coe.comp measurable_snd) (fun q => q.2.prop) _
    (hf.comp (measurable_fst.fst.prodMk measurable_snd)).stronglyMeasurable).measurable

/-- A pointwise integral over an a.e. measurable family is genuinely measurable in the test
parameter: use a measurable version of the family, then identify the integral at each parameter. -/
theorem measurable_integral_ae_parameter
    {U Ω E B : Type*} [MeasurableSpace U] [MeasurableSpace Ω] [MeasurableSpace E]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [SecondCountableTopology B]
    [MeasurableSpace B] [BorelSpace B] {P : Measure Ω} [SFinite P]
    {M : Ω → FiniteMeasure E} (hM : AEMeasurable M P)
    {F : U × FiniteMeasure E → B} (hF : Measurable F) :
    Measurable (fun u => ∫ ω, F (u, M ω) ∂P) := by
  have h := hF.comp (measurable_fst.prodMk
    (hM.measurable_mk.comp (measurable_snd : Measurable (Prod.snd : U × Ω → Ω))))
  have hi := h.stronglyMeasurable.integral_prod_right' (ν := P)
  convert hi.measurable using 1
  funext u
  exact integral_congr_ae (hM.ae_eq_mk.mono fun ω hω => congrArg (fun μ => F (u, μ)) hω)

/-- The corresponding nonnegative integral over an a.e. measurable family. -/
theorem measurable_lintegral_ae_parameter
    {U Ω E : Type*} [MeasurableSpace U] [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} [SFinite P] {M : Ω → FiniteMeasure E} (hM : AEMeasurable M P)
    {F : U × FiniteMeasure E → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun u => ∫⁻ ω, F (u, M ω) ∂P) := by
  have h := hF.comp (measurable_fst.prodMk
    (hM.measurable_mk.comp (measurable_snd : Measurable (Prod.snd : U × Ω → Ω))))
  convert h.lintegral_prod_right' (ν := P) using 1
  funext u
  exact lintegral_congr_ae (hM.ae_eq_mk.mono fun ω hω => congrArg (fun μ => F (u, μ)) hω)

/-- Restriction to a fixed measurable set is measurable on the space of measures. -/
theorem measurable_measure_restrict {E : Type*} [MeasurableSpace E]
    (S : Set E) (hS : MeasurableSet S) :
    Measurable (fun μ : Measure E => μ.restrict S) := by
  apply Measure.measurable_of_measurable_coe
  intro T hT
  have heq : (fun μ : Measure E => μ.restrict S T) = fun μ => μ (T ∩ S) :=
    funext (fun μ => Measure.restrict_apply hT)
  rw [heq]
  exact Measure.measurable_coe (hT.inter hS)

/-- Restrict to a finite-mass set, with a measurable zero fallback. -/
noncomputable def finiteRestrictionOnSet {E : Type*} [MeasurableSpace E]
    (S : Set E) (μ : Measure E) : FiniteMeasure E :=
  @dite _ (μ S < ⊤) (Classical.propDecidable _) (fun h =>
    ⟨μ.restrict S, isFiniteMeasure_restrict.mpr h.ne⟩) fun _ => 0

theorem measurable_finiteRestrictionOnSet {E : Type*} [MeasurableSpace E]
    (S : Set E) (hS : MeasurableSet S) : Measurable (finiteRestrictionOnSet S) := by
  apply Measurable.subtype_mk
  have hgood : MeasurableSet {μ : Measure E | μ S < ⊤} :=
    measurableSet_lt (Measure.measurable_coe hS) measurable_const
  have hcode : Measurable (fun μ : Measure E => if μ S < ⊤ then μ.restrict S else 0) :=
    Measurable.ite hgood (measurable_measure_restrict S hS) measurable_const
  convert hcode using 1
  funext μ
  change (finiteRestrictionOnSet S μ : Measure E) = (if μ S < ⊤ then μ.restrict S else 0)
  by_cases h : μ S < ⊤ <;> simp [finiteRestrictionOnSet, h]

end DOZZ.Proofs
