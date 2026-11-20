/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.MomentLimitD
public import DOZZ.FourPoint.BPZ.DerivLimit

/-! # Two derivatives of the negative moment of the four-point mass

Off the roots `0` and `1`, the negative moment `z ↦ E[I(z)^{-s}]` of the four-point mass is twice
differentiable, with first and second derivatives the expectations of the moment fields at
`ε = 0`, and the second derivative is continuous. The softened moments (`ε > 0`) are
differentiable with the softened moment fields as derivatives; these converge locally uniformly
bounded to the unsoftened ones, which are continuous. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

attribute [local instance low] bpzNormedAddCommGroupBilin bpzNormedSpaceBilin

variable {γ χ α₁ α₂ α₃ : ℝ}

/-- The plane without the roots `0` and `1` is open. -/
theorem bpz_isOpen_regularPlane : IsOpen {z : ℂ | z ≠ 0 ∧ z ≠ 1} := by
  have : {z : ℂ | z ≠ 0 ∧ z ≠ 1} = {z : ℂ | z ≠ 0} ∩ {z : ℂ | z ≠ 1} := rfl
  rw [this]
  exact isOpen_ne.inter isOpen_ne

/-- Bounds on the expectations of the moment fields, uniform near `z₀` and in the softening. -/
theorem bpz_momField_uniform {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (ha1 : γ * χ / 2 ≤ 1)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {s : ℝ} (hs : 0 ≤ s) {z₀ : ℂ}
    (hz0 : z₀ ≠ 0) (hz1 : z₀ ≠ 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ K : ℝ, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ z : ℂ, ‖z - z₀‖ < ρ →
      ‖∫ ω, bpzMomField1 (γ * χ / 2) s ε (bpzBaseWeight γ χ α₁ α₂ α₃)
          (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z ∂P‖ ≤ K ∧
      ‖∫ ω, bpzMomField2 (γ * χ / 2) s ε (bpzBaseWeight γ χ α₁ α₂ α₃)
          (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z ∂P‖ ≤ K := by
  obtain ⟨Y, hYint, hG⟩ := bpz_moment_setup P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hs hz0 hz1
  obtain ⟨h₁, h₂⟩ := bpz_momField_cutoff P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hs hz0 hz1 hYint hG
  obtain ⟨r₁, hr₁, K₁, hK₁⟩ := h₁.uniform hYint
  obtain ⟨r₂, hr₂, K₂, hK₂⟩ := h₂.uniform hYint
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, max K₁ K₂, fun ε h₀ h₁ z hz => ?_⟩
  exact ⟨(hK₁ ε h₀ h₁ z (hz.trans_le (min_le_left ..))).trans (le_max_left ..),
    (hK₂ ε h₀ h₁ z (hz.trans_le (min_le_right ..))).trans (le_max_right ..)⟩

/-- Sequential continuity at regular roots gives continuity on the regular plane. -/
theorem bpz_continuousOn_of_seq {F : Type*} [TopologicalSpace F] {g : ℂ → F}
    (h : ∀ z₀ : ℂ, z₀ ≠ 0 → z₀ ≠ 1 → ∀ zs : ℕ → ℂ, Tendsto zs atTop (𝓝 z₀) →
      Tendsto (fun n => g (zs n)) atTop (𝓝 (g z₀))) :
    ContinuousOn g {z : ℂ | z ≠ 0 ∧ z ≠ 1} := by
  intro z₀ hz₀
  refine ContinuousAt.continuousWithinAt ?_
  exact tendsto_nhds_iff_seq_tendsto.mpr fun zs hzs => h z₀ hz₀.1 hz₀.2 zs hzs

/-- The expectation of the second moment field at `ε = 0` is continuous on the regular plane. -/
theorem bpz_continuousOn_momField2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (ha1 : γ * χ / 2 ≤ 1)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {s : ℝ} (hs : 0 ≤ s) :
    ContinuousOn (fun z => ∫ ω, bpzMomField2 (γ * χ / 2) s 0 (bpzBaseWeight γ χ α₁ α₂ α₃)
      (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z ∂P) {z : ℂ | z ≠ 0 ∧ z ≠ 1} :=
  bpz_continuousOn_of_seq fun _ hz0 hz1 _ hzs =>
    bpz_tendsto_momField2_gmc P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hs hz0 hz1
      (fun _ => le_rfl) (fun _ => zero_le_one) tendsto_const_nhds hzs

/-- The softening parameters `1/(n+1)`. -/
theorem bpz_softSeq_props :
    (∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1)) ∧ (∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1) ∧
      Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  refine ⟨fun n => by positivity, fun n => ?_, tendsto_one_div_add_atTop_nhds_zero_nat⟩
  rw [div_le_one (by positivity)]
  linarith

/-- Derivatives of the softened moments, at a regular root. -/
theorem bpz_hasFDerivAt_softMoments {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (ha1 : γ * χ / 2 ≤ 1)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {s : ℝ} (hs : 0 < s) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) {z₀ : ℂ} (hz0 : z₀ ≠ 0) (hz1 : z₀ ≠ 1) :
    HasFDerivAt (fun z => ∫ ω, bpzSoftMassReal (γ * χ / 2) ε (bpzBaseWeight γ χ α₁ α₂ α₃)
        (M ω) z ^ (-s) ∂P)
      (∫ ω, bpzMomField1 (γ * χ / 2) s ε (bpzBaseWeight γ χ α₁ α₂ α₃)
        (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z₀ ∂P) z₀ ∧
    HasFDerivAt (fun z => ∫ ω, bpzMomField1 (γ * χ / 2) s ε (bpzBaseWeight γ χ α₁ α₂ α₃)
        (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z ∂P)
      (∫ ω, bpzMomField2 (γ * χ / 2) s ε (bpzBaseWeight γ χ α₁ α₂ α₃)
        (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z₀ ∂P) z₀ := by
  obtain ⟨Y, hYint, hG⟩ := bpz_moment_setup P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hs.le
    hz0 hz1
  have hw := measurable_bpzBaseWeight (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂) (α₃ := α₃)
  have hmeasI : ∀ z, AEStronglyMeasurable (fun ω => bpzSoftMassReal (γ * χ / 2) ε
      (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z) P := fun z =>
    ((bpz_measurable_softMassReal _ ε hw z).comp hMm).aestronglyMeasurable
  have hmeasD : ∀ z, AEStronglyMeasurable (fun ω => bpzSoftMassDeriv (γ * χ / 2) ε
      (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z) P := fun z =>
    ((bpz_stronglyMeasurable_softMassDeriv _ ε hw z).comp_measurable hMm).aestronglyMeasurable
  have hmeasD2 : AEStronglyMeasurable (fun ω => bpzSoftMassDeriv2 (γ * χ / 2) ε
      (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z₀) P :=
    ((bpz_stronglyMeasurable_softMassDeriv2 _ ε hw z₀).comp_measurable hMm).aestronglyMeasurable
  have hint : ∀ᵐ ω ∂P, Integrable (fun x => (Complex.normSq (x - z₀) + ε ^ 2) ^ (γ * χ / 2) *
      bpzBaseWeight γ χ α₁ α₂ α₃ x) (M ω) := by
    filter_upwards [hG] with ω h
    exact (h.near z₀ (by simp) ε hε.le hε1).1
  have hYpos  := hG.mono fun _ h => h.pos
  have hlow : ∀ᵐ ω ∂P, ∀ z ∈ Metric.ball z₀ 1, Y ω ≤ bpzSoftMassReal (γ * χ / 2) ε
      (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z := by
    filter_upwards [hG] with ω h z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    exact (h.near z hz.le ε hε.le hε1).2
  exact ⟨hasFDerivAt_bpzSoftMoment M hε hs hw bpzBaseWeight_nonneg hmeasI (hmeasD z₀) hint
      hYpos hlow hYint,
    hasFDerivAt_bpzSoftMomentDeriv M hε hs hw bpzBaseWeight_nonneg hmeasI
      (fun z _ => hmeasD z) hmeasD2 hint hYpos hlow hYint⟩

/-- **Two derivatives of the negative moment.** On the regular plane, `z ↦ E[I(z)^{-s}]` has
derivative the expectation of the first moment field, which in turn has derivative the
expectation of the second moment field. -/
theorem bpz_hasFDerivAt_moments {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (ha1 : γ * χ / 2 ≤ 1)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {s : ℝ} (hs : 0 < s) :
    (∀ z ∈ {z : ℂ | z ≠ 0 ∧ z ≠ 1},
      HasFDerivAt (fun z => ∫ ω, bpzSoftMassReal (γ * χ / 2) 0 (bpzBaseWeight γ χ α₁ α₂ α₃)
          (M ω) z ^ (-s) ∂P)
        (∫ ω, bpzMomField1 (γ * χ / 2) s 0 (bpzBaseWeight γ χ α₁ α₂ α₃)
          (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z ∂P) z) ∧
    (∀ z ∈ {z : ℂ | z ≠ 0 ∧ z ≠ 1},
      HasFDerivAt (fun z => ∫ ω, bpzMomField1 (γ * χ / 2) s 0 (bpzBaseWeight γ χ α₁ α₂ α₃)
          (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z ∂P)
        (∫ ω, bpzMomField2 (γ * χ / 2) s 0 (bpzBaseWeight γ χ α₁ α₂ α₃)
          (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z ∂P) z) := by
  obtain ⟨hεpos, hεle, hεlim⟩ := bpz_softSeq_props
  have hbd : ∀ z ∈ {z : ℂ | z ≠ 0 ∧ z ≠ 1}, ∃ r > 0, ∃ C : ℝ, ∀ n : ℕ, ∀ w ∈ Metric.ball z r,
      ‖∫ ω, bpzMomField1 (γ * χ / 2) s (1 / ((n : ℝ) + 1)) (bpzBaseWeight γ χ α₁ α₂ α₃)
          (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) w ∂P‖ ≤ C ∧
      ‖∫ ω, bpzMomField2 (γ * χ / 2) s (1 / ((n : ℝ) + 1)) (bpzBaseWeight γ χ α₁ α₂ α₃)
          (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) w ∂P‖ ≤ C := by
    intro z hz
    obtain ⟨ρ, hρ, K, hK⟩ := bpz_momField_uniform P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃
      hs.le hz.1 hz.2
    refine ⟨ρ, hρ, K, fun n w hw => ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hw
    exact hK _ (hεpos n).le (hεle n) w hw
  have h1 := bpz_hasFDerivAt_of_tendsto_deriv (U := {z : ℂ | z ≠ 0 ∧ z ≠ 1})
    (f := fun (n : ℕ) z => ∫ ω, bpzSoftMassReal (γ * χ / 2) (1 / ((n : ℝ) + 1))
      (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z ^ (-s) ∂P)
    (f' := fun (n : ℕ) z => ∫ ω, bpzMomField1 (γ * χ / 2) s (1 / ((n : ℝ) + 1))
      (bpzBaseWeight γ χ α₁ α₂ α₃) (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z ∂P)
    bpz_isOpen_regularPlane
    (fun n z hz => (bpz_hasFDerivAt_softMoments P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hs
      (hεpos n) (hεle n) hz.1 hz.2).1)
    (fun z hz => bpz_tendsto_mom0_gmc P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hs.le hz.1 hz.2
      (fun n => (hεpos n).le) hεle hεlim tendsto_const_nhds)
    (fun z hz => bpz_tendsto_momField1_gmc P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hs.le hz.1
      hz.2 (fun n => (hεpos n).le) hεle hεlim tendsto_const_nhds)
    (fun z hz => by
      obtain ⟨r, hr, C, hC⟩ := hbd z hz
      exact ⟨r, hr, C, fun n w hw => (hC n w hw).1⟩)
    ((bpz_continuousOn_of_seq fun _ hz0 hz1 _ hzs =>
      bpz_tendsto_momField1_gmc P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hs.le hz0 hz1
      (fun _ => le_rfl) (fun _ => zero_le_one) tendsto_const_nhds hzs))
  have h2 := bpz_hasFDerivAt_of_tendsto_deriv (U := {z : ℂ | z ≠ 0 ∧ z ≠ 1})
    (f := fun (n : ℕ) z => ∫ ω, bpzMomField1 (γ * χ / 2) s (1 / ((n : ℝ) + 1))
      (bpzBaseWeight γ χ α₁ α₂ α₃) (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z ∂P)
    (f' := fun (n : ℕ) z => ∫ ω, bpzMomField2 (γ * χ / 2) s (1 / ((n : ℝ) + 1))
      (bpzBaseWeight γ χ α₁ α₂ α₃) (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z ∂P)
    bpz_isOpen_regularPlane
    (fun n z hz => (bpz_hasFDerivAt_softMoments P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hs
      (hεpos n) (hεle n) hz.1 hz.2).2)
    (fun z hz => bpz_tendsto_momField1_gmc P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hs.le hz.1
      hz.2 (fun n => (hεpos n).le) hεle hεlim tendsto_const_nhds)
    (fun z hz => bpz_tendsto_momField2_gmc P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hs.le hz.1
      hz.2 (fun n => (hεpos n).le) hεle hεlim tendsto_const_nhds)
    (fun z hz => by
      obtain ⟨r, hr, C, hC⟩ := hbd z hz
      exact ⟨r, hr, C, fun n w hw => (hC n w hw).2⟩)
    (bpz_continuousOn_momField2 P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hs.le)
  exact ⟨h1, h2⟩

end DOZZ.Proofs
