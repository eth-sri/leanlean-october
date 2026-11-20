/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.MomentLimitC

/-! # Limits of the moments of the softened four-point mass

Along `(εₙ, zₙ) → (0, z₀)` with `z₀ ∉ {0, 1}` and `0 ≤ εₙ ≤ 1`, the expectations of
`I^{-s}` and of the moment fields `−s I^{−s−1} DI` and `s(s+1) I^{−s−2} DI ⊗ DI − s I^{−s−1} D²I`
of the softened four-point mass `I` converge to their values at `(0, z₀)`. The near-root parts
are small in expectation uniformly along the sequence (rooted bound), and the far parts converge
by dominated convergence. The same estimates give bounds on the expectations of the moment fields
that are uniform near `z₀` and in the softening. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

attribute [local instance low] bpzNormedAddCommGroupBilin bpzNormedSpaceBilin

variable {γ χ α₁ α₂ α₃ : ℝ}

/-- A field and its cutoff share a uniform local power error in L¹, and the cutoff is
controlled by the same integrable majorant at every nearby root and softening. -/
def BPZCutoffEstimate {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) (z₀ : ℂ) (F : ℝ → ℂ → Ω → E) (G : ℝ → ℝ → ℂ → Ω → E)
    (Y : Ω → ℝ) : Prop :=
  ∃ r₀ > 0, ∃ K e : ℝ, 0 < e ∧ ∃ A : ℝ → ℝ,
    ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∀ z : ℂ, ‖z - z₀‖ ≤ min 1 (r / 2) →
        Integrable (F ε z) P ∧ Integrable (G r ε z) P ∧
        (∫ ω, ‖F ε z ω - G r ε z ω‖ ∂P) ≤ K * (2 * r) ^ e ∧
        ∀ᵐ ω ∂P, ‖G r ε z ω‖ ≤ A r * Y ω

section
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Measure Ω} {z₀ : ℂ} {F : ℝ → ℂ → Ω → E} {G : ℝ → ℝ → ℂ → Ω → E} {Y : Ω → ℝ}

theorem BPZCutoffEstimate.tendsto (h : BPZCutoffEstimate P z₀ F G Y)
    {εs : ℕ → ℝ} (hε0 : ∀ n, 0 ≤ εs n) (hε1 : ∀ n, εs n ≤ 1)
    {zs : ℕ → ℂ} (hz : Tendsto zs atTop (𝓝 z₀))
    (hG : ∀ r : ℝ, 0 < r → Tendsto (fun n => ∫ ω, G r (εs n) (zs n) ω ∂P) atTop
      (𝓝 (∫ ω, G r 0 z₀ ω ∂P))) :
    Tendsto (fun n => ∫ ω, F (εs n) (zs n) ω ∂P) atTop (𝓝 (∫ ω, F 0 z₀ ω ∂P)) := by
  obtain ⟨r₀, hr₀, K, e, he, _, hbound⟩ := h
  refine bpz_tendsto_integral_of_approx fun η hη => ?_
  obtain ⟨r, hr, hrr, hrη⟩ := bpz_exists_small_radius (K := K) he hr₀ hη
  have hnear := (tendsto_iff_norm_sub_tendsto_zero.mp hz).eventually
    (ge_mem_nhds (lt_min one_pos (half_pos hr)))
  have hb ε hε₀ hε₁ z hzr := hbound r hr hrr ε hε₀ hε₁ z hzr
  refine ⟨fun n => G r (εs n) (zs n), G r 0 z₀, hG r hr,
    hnear.mono (fun n hn => ?_), ?_⟩
  · obtain ⟨hF, hG, hFG, _⟩ := hb _ (hε0 n) (hε1 n) _ hn
    exact ⟨hF, hG, hFG.trans hrη⟩
  · obtain ⟨hF, hG, hFG, _⟩ := hb 0 le_rfl zero_le_one z₀ (by simp; positivity)
    exact ⟨hF, hG, hFG.trans hrη⟩

theorem BPZCutoffEstimate.uniform [CompleteSpace E] (h : BPZCutoffEstimate P z₀ F G Y)
    (hY : Integrable Y P) :
    ∃ ρ > 0, ∃ K : ℝ, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ z : ℂ, ‖z - z₀‖ < ρ →
      ‖∫ ω, F ε z ω ∂P‖ ≤ K := by
  obtain ⟨r, hr, K, e, _, A, hbound⟩ := h
  refine ⟨min 1 (r / 2), lt_min one_pos (half_pos hr), K * (2 * r) ^ e + A r * ∫ ω, Y ω ∂P,
    fun ε hε₀ hε₁ z hz => ?_⟩
  obtain ⟨hF, hG, hFG, hA⟩ := hbound r hr le_rfl ε hε₀ hε₁ z hz.le
  have hd : Integrable (fun ω => ‖F ε z ω - G r ε z ω‖) P := (hF.sub hG).norm
  have hAr := hY.const_mul (A r)
  refine (norm_integral_le_integral_norm _).trans ((integral_mono_ae hF.norm (hd.add hAr) ?_).trans ?_)
  · filter_upwards [hA] with ω hw
    change ‖F ε z ω‖ ≤ ‖F ε z ω - G r ε z ω‖ + A r * Y ω
    simpa using (norm_add_le (F ε z ω - G r ε z ω) (G r ε z ω)).trans
          (add_le_add_right hw _)
  · change (∫ ω, ‖F ε z ω - G r ε z ω‖ + A r * Y ω ∂P) ≤ _
    rw [integral_add hd hAr, integral_const_mul]
    exact add_le_add hFG le_rfl

end

/-- The almost sure data at a regular root `z₀`, with an integrable lower bound `Y` of the mass
at all roots within distance `1` of `z₀`. -/
theorem bpz_moment_setup {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (ha1 : γ * χ / 2 ≤ 1)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {s : ℝ} (hs : 0 ≤ s) {z₀ : ℂ}
    (hz0 : z₀ ≠ 0) (hz1 : z₀ ≠ 1) :
    ∃ Y : Ω → ℝ, Integrable (fun ω => Y ω ^ (-s)) P ∧
      ∀ᵐ ω ∂P, BPZMomentData (γ * χ / 2) (bpzBaseWeight γ χ α₁ α₂ α₃) z₀ (M ω) (Y ω) := by
  have ha : 0 < γ * χ / 2 := by positivity
  obtain ⟨Y, -, hYpos, hYint, hYle⟩ := bpz_farBall_lower (χ := χ) (α₁ := α₁) (α₂ := α₂)
    (α₃ := α₃) P X hX hγ hγ2 M hM hMm (R := ‖z₀‖ + 1) (by positivity) hs
  refine ⟨Y, hYint, ?_⟩
  filter_upwards [bpz_moment_good_ae P X hX hγ hγ2 M hM hMm hχ hα₁ hα₂ hα₃ hz0 hz1, hYpos]
    with ω hω hY
  obtain ⟨h0, hintw, hint⟩ := hω
  refine ⟨h0, hY, hintw, hint, fun z hz ε hε0 hε1 => ?_⟩
  have hintz := bpzSoft_integrable_near ha ha1 hε0 hε1 measurable_bpzBaseWeight
    bpzBaseWeight_nonneg hint hintw hz
  refine ⟨hintz, hYle ω z ?_ ε hε0 hε1 hintz⟩
  have := norm_le_norm_add_norm_sub' z z₀
  linarith

/-- Rewriting the second-field bound as a multiple of `(2r)^{2a}`. -/
private theorem bpz_mom2_bound_eq {a s C r K₂ : ℝ} (hr : 0 < r) :
    (4 * a ^ 2 * s * (s + 1) + s * K₂) * (C * (2 * Real.pi * (2 * r) ^ (2 * a - 2 + 2) /
        (2 * a - 2 + 2))) +
      16 * a ^ 2 * s * (s + 1) / r * (C * (2 * Real.pi * (2 * r) ^ (2 * a - 1 + 2) /
        (2 * a - 1 + 2))) =
    ((4 * a ^ 2 * s * (s + 1) + s * K₂) * (C * (2 * Real.pi) / (2 * a - 2 + 2)) +
      32 * a ^ 2 * s * (s + 1) * (C * (2 * Real.pi) / (2 * a - 1 + 2))) *
        (2 * r) ^ (2 * a - 2 + 2) := by
  have h2r : 0 < 2 * r := by positivity
  have e : (2 * r) ^ (2 * a - 1 + 2) = (2 * r) ^ (2 * a - 2 + 2) * (2 * r) := by
    rw [show 2 * a - 1 + 2 = (2 * a - 2 + 2) + 1 by ring, Real.rpow_add h2r, Real.rpow_one]
  rw [e]
  field_simp
  ring

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (ha1 : γ * χ / 2 ≤ 1)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {s : ℝ} (hs : 0 ≤ s) {z₀ : ℂ}
    (hz0 : z₀ ≠ 0) (hz1 : z₀ ≠ 1)

include X hX hγ hγ2 hM hMm hχ ha1 hα₁ hα₂ hα₃ hs hz0 hz1

local notation "a" => (γ * χ / 2)
local notation "w₀" => bpzBaseWeight γ χ α₁ α₂ α₃

/-- The rooted estimates supply cutoffs for both differentiated moment fields. -/
theorem bpz_momField_cutoff {Y : Ω → ℝ} (hYint : Integrable (fun ω => Y ω ^ (-s)) P)
    (hG : ∀ᵐ ω ∂P, BPZMomentData a w₀ z₀ (M ω) (Y ω)) :
    BPZCutoffEstimate P z₀ (fun ε z ω => bpzMomField1 a s ε w₀ w₀ (M ω) z)
      (fun r ε z ω => bpzMomField1 a s ε w₀ (fun x => if r ≤ ‖x - z₀‖ then w₀ x else 0) (M ω) z)
      (fun ω => Y ω ^ (-s)) ∧
    BPZCutoffEstimate P z₀ (fun ε z ω => bpzMomField2 a s ε w₀ w₀ (M ω) z)
      (fun r ε z ω => bpzMomField2 a s ε w₀ (fun x => if r ≤ ‖x - z₀‖ then w₀ x else 0) (M ω) z)
      (fun ω => Y ω ^ (-s)) := by
  have ha : 0 < a := by positivity
  obtain ⟨r₀, hr₀, C, _, hC⟩ := bpz_near_real_bound P X hX hγ hγ2 M hM hMm hχ hα₁ hα₂ hα₃
    hs hz0 hz1
  have hgood r ε z (hz : ‖z - z₀‖ ≤ min 1 (r / 2)) hε₀ hε₁ := hG.mono fun ω h =>
    And.intro (h.atomless z) (And.intro h.pos (h.near z (hz.trans (min_le_left ..)) ε hε₀ hε₁).symm)
  constructor
  · refine ⟨r₀, hr₀, s * (2 * a) * (C * (2 * Real.pi) / (2 * a - 1 + 2)), 2 * a - 1 + 2,
      by linarith, fun r => s * (4 * a / r), fun r hr hrr ε he₀ he₁ z hz => ?_⟩
    have hzr := hz.trans (min_le_right ..)
    obtain ⟨hBi, hB, hnear⟩ := hC r hr hrr z hzr ε he₀ he₁ (2 * a - 1) (by linarith)
    obtain ⟨h₁, h₂, h₃, h₄⟩ := bpz_momField1_near hMm ha ha1 hs measurable_bpzBaseWeight
      bpzBaseWeight_nonneg hr hzr hYint (hgood r ε z hz he₀ he₁) hnear hBi hB
    exact ⟨h₁, h₂, h₃.trans_eq (by ring), h₄⟩
  · let b := 4 * a * (1 - a) + 2 * a
    refine ⟨r₀, hr₀, (4 * a ^ 2 * s * (s + 1) + s * b) * (C * (2 * Real.pi) / (2 * a - 2 + 2)) +
      32 * a ^ 2 * s * (s + 1) * (C * (2 * Real.pi) / (2 * a - 1 + 2)), 2 * a - 2 + 2,
      by linarith, fun r => s * (s + 1) * (4 * a / r) ^ 2 + s * (4 * b / r ^ 2),
      fun r hr hrr ε he₀ he₁ z hz => ?_⟩
    have hzr := hz.trans (min_le_right ..)
    obtain ⟨hB₁i, hB₁, hnear₁⟩ := hC r hr hrr z hzr ε he₀ he₁ (2 * a - 1) (by linarith)
    obtain ⟨hB₂i, hB₂, hnear₂⟩ := hC r hr hrr z hzr ε he₀ he₁ (2 * a - 2) (by linarith)
    obtain ⟨h₁, h₂, h₃, h₄⟩ := bpz_momField2_near hMm ha ha1 hs measurable_bpzBaseWeight
      bpzBaseWeight_nonneg hr hzr hYint (hgood r ε z hz he₀ he₁) hnear₁ hnear₂ hB₁i hB₁ hB₂i hB₂
    exact ⟨h₁, h₂, h₃.trans_eq (bpz_mom2_bound_eq hr), h₄⟩

variable {εs : ℕ → ℝ} (hε0 : ∀ n, 0 ≤ εs n) (hε1 : ∀ n, εs n ≤ 1)
    (hε : Tendsto εs atTop (𝓝 0)) {zs : ℕ → ℂ} (hz : Tendsto zs atTop (𝓝 z₀))
include hε0 hε1 hε hz

/-- Convergence of the zeroth moment along `(εₙ, zₙ) → (0, z₀)`. -/
theorem bpz_tendsto_mom0_gmc :
    Tendsto (fun n => ∫ ω, bpzSoftMassReal a (εs n) w₀ (M ω) (zs n) ^ (-s) ∂P) atTop
      (𝓝 (∫ ω, bpzSoftMassReal a 0 w₀ (M ω) z₀ ^ (-s) ∂P)) := by
  obtain ⟨Y, hYint, hG⟩ := bpz_moment_setup P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hs hz0 hz1
  exact bpz_tendsto_mom0 hMm (by positivity) ha1 hs measurable_bpzBaseWeight bpzBaseWeight_nonneg
    hYint hG hε0 hε1 hε hz

/-- Convergence of the first differentiated moment along `(εₙ, zₙ) → (0, z₀)`. -/
theorem bpz_tendsto_momField1_gmc :
    Tendsto (fun n => ∫ ω, bpzMomField1 a s (εs n) w₀ w₀ (M ω) (zs n) ∂P) atTop
      (𝓝 (∫ ω, bpzMomField1 a s 0 w₀ w₀ (M ω) z₀ ∂P)) := by
  obtain ⟨Y, hYint, hG⟩ := bpz_moment_setup P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hs hz0 hz1
  exact (bpz_momField_cutoff P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hs hz0 hz1 hYint hG).1.tendsto
    hε0 hε1 hz fun r hr => bpz_tendsto_momField1_far hMm (by positivity) ha1 hs measurable_bpzBaseWeight
      bpzBaseWeight_nonneg hr hYint hG hε0 hε1 hε hz

/-- Convergence of the second differentiated moment along `(εₙ, zₙ) → (0, z₀)`. -/
theorem bpz_tendsto_momField2_gmc :
    Tendsto (fun n => ∫ ω, bpzMomField2 a s (εs n) w₀ w₀ (M ω) (zs n) ∂P) atTop
      (𝓝 (∫ ω, bpzMomField2 a s 0 w₀ w₀ (M ω) z₀ ∂P)) := by
  obtain ⟨Y, hYint, hG⟩ := bpz_moment_setup P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hs hz0 hz1
  exact (bpz_momField_cutoff P X hX hγ hγ2 M hM hMm hχ ha1 hα₁ hα₂ hα₃ hs hz0 hz1 hYint hG).2.tendsto
    hε0 hε1 hz fun r hr => bpz_tendsto_momField2_far hMm (by positivity) ha1 hs measurable_bpzBaseWeight
      bpzBaseWeight_nonneg hr hYint hG hε0 hε1 hε hz

end

end DOZZ.Proofs
