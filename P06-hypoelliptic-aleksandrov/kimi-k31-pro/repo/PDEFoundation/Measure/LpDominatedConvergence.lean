module

public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Dominated convergence in finite-exponent `L^p`

This file packages the form of dominated convergence used by Sobolev
composition and truncation arguments.  The exponent is arbitrary and finite:
if a sequence converges almost everywhere and is pointwise dominated in norm
by one `L^p` function, then it converges in `L^p`.

The proof uses Mathlib's finite-measure Vitali theorem.  Domination supplies
uniform integrability directly, with no exponent-dependent loss.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory

/-- A family pointwise dominated in norm by one `L^p` function is uniformly
integrable at every finite exponent `p ≥ 1`. -/
theorem unifIntegrable_of_ae_norm_le
    {ι α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    {F : ι → α → E} {bound : α → E}
    (hF : ∀ i, AEStronglyMeasurable (F i) μ)
    (hboundMem : MemLp bound p μ)
    (hbound : ∀ i, ∀ᵐ x ∂μ, ‖F i x‖ ≤ ‖bound x‖) :
    UnifIntegrable F p μ := by
  rw [unifIntegrable_iff']
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ :=
    hboundMem.eLpNorm_indicator_le hp hpTop hε
  refine ⟨δ, hδ, fun i s hs hμs => ?_⟩
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hs]
  refine (eLpNorm_mono_ae ((hF i).indicator hs) ?_).trans (hsmall s hs hμs)
  filter_upwards [hbound i] with x hx
  by_cases hxs : x ∈ s
  · simp only [Set.indicator_of_mem hxs]
    exact hx
  · simp only [Set.indicator_of_notMem hxs, norm_zero]
    exact le_rfl

/-- Dominated almost-everywhere convergence implies convergence in
finite-exponent `L^p` on a finite measure space. -/
theorem tendsto_eLpNorm_sub_zero_of_tendsto_ae_of_dominated
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α}
    [IsFiniteMeasure μ] {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    {F : ℕ → α → E} {f bound : α → E}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hf : MemLp f p μ) (hboundMem : MemLp bound p μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ ‖bound x‖)
    (hFf :
      ∀ᵐ x ∂μ,
        Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto
      (fun n => eLpNorm (F n - f) p μ)
      atTop (𝓝 0) :=
  tendsto_Lp_finite_of_tendsto_ae
    hp hpTop hF hf
    (unifIntegrable_of_ae_norm_le hp hpTop hF hboundMem hbound)
    hFf

/-- Dominated convergence to zero in `L²`, without a finite-measure hypothesis. -/
theorem tendsto_eLpNorm_two_zero_of_ae_dominated
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {F : ℕ → α → E} {bound : α → E}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hboundMem : MemLp bound (2 : ℝ≥0∞) μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ ‖bound x‖)
    (hzero : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) (2 : ℝ≥0∞) μ) atTop (𝓝 0) := by
  let G : ℕ → α → ℝ≥0∞ := fun n x => ‖F n x‖ₑ ^ (2 : ℝ)
  let B : α → ℝ≥0∞ := fun x => ‖bound x‖ₑ ^ (2 : ℝ)
  have hGMeas : ∀ n, AEMeasurable (G n) μ := fun n => (hF n).enorm.pow_const _
  have hGBound : ∀ n, G n ≤ᵐ[μ] B := by
    intro n
    filter_upwards [hbound n] with x hx
    exact ENNReal.rpow_le_rpow (by
      simpa only [ofReal_norm_eq_enorm] using ENNReal.ofReal_le_ofReal hx) (by norm_num)
  have hBFinite : ∫⁻ x, B x ∂μ ≠ ∞ :=
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hboundMem).ne
  have hGZero : ∀ᵐ x ∂μ, Tendsto (fun n => G n x) atTop (𝓝 0) := by
    filter_upwards [hzero] with x hx
    have henorm : Tendsto (fun n => ‖F n x‖ₑ) atTop (𝓝 0) := by
      simpa only [Function.comp_def, enorm_zero] using (continuous_enorm.tendsto 0).comp hx
    simpa only [Function.comp_def, G, enorm_zero,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] using
      ((ENNReal.continuous_rpow_const :
        Continuous (fun a : ℝ≥0∞ => a ^ (2 : ℝ))).tendsto 0).comp henorm
  have hint : Tendsto (fun n => ∫⁻ x, G n x ∂μ) atTop (𝓝 0) := by
    simpa only [lintegral_zero] using
      tendsto_lintegral_of_dominated_convergence' B hGMeas hGBound hBFinite hGZero
  simpa only [Function.comp_def, G, eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (hF _), ENNReal.toReal_ofNat, one_div,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)] using
    ((ENNReal.continuous_rpow_const :
      Continuous (fun a : ℝ≥0∞ => a ^ ((2 : ℝ)⁻¹))).tendsto 0).comp hint

end PDE
