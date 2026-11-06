module

public import ALCS.ZeroClass

@[expose] public section

/-!
# Continuity of the input response for `p = ∞` (Corollary 1.6)

**Corollary 1.6** (`cor:p-infty-solution-continuous`). Let `X`, `U` be Banach spaces and
`(𝕋, Φ)` an abstract linear control system with `p = ∞`. For all `u ∈ L^∞(ℝ₊; U)`,
`t ↦ Φ_t u` is continuous on `ℝ₊`.

This answers positively Problem 2.4 of [Weiss 1989]. The proof (§ 2.4 of the paper) only
uses Theorem 1.5 (`ALCS.zero_class`), the composition property and the continuity of
semigroup orbits (Proposition 1.2, `C0Semigroup.continuousOn_orbit`):

* at `t₀ = 0`, `‖Φ_t u‖ ≤ κ(t) ‖u‖ → 0`;
* at `t₀ > 0`, with `t₁ = t₀ - δ` and `u₁ = u (t₁ + ·)`, the composition property gives
  `Φ_{t₁ + r} u = T_r (Φ_{t₁} u) + Φ_r u₁`, and `‖Φ_r u₁‖ ≤ κ(2δ) ‖u‖` for `r ≤ 2δ`.

The main statement is `ALCS.continuousOn_Phi`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {U : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U]

namespace ALCS

/-- Consequence of Theorem 1.5: for `ε > 0` there is `η > 0` such that
`‖Φ r v‖ < ε` for all `r ∈ [0, η)` and all inputs `v` with `‖v‖ ≤ ‖u‖`. -/
theorem small_Phi [CompleteSpace X] [CompleteSpace U] (S : ALCS 𝕜 X U ∞)
    (u : Lp U ∞ muPlus) (ε : ℝ) (hε : 0 < ε) :
    ∃ η > 0, ∀ r, 0 ≤ r → r < η → ∀ v : Lp U ∞ muPlus, ‖v‖ ≤ ‖u‖ → ‖S.Φ r v‖ < ε := by
  -- `κ(r) = ‖Φ r‖ < ε / (‖u‖ + 1)` for `r ∈ [0, η)`
  obtain ⟨η, hη, hκ⟩ := Metric.tendsto_nhdsWithin_nhds.1 S.zero_class
    (ε / (‖u‖ + 1)) (by positivity)
  refine ⟨η, hη, fun r hr hrη v hv => ?_⟩
  have h2 : ‖S.Φ r‖ < ε / (‖u‖ + 1) := by
    simpa using hκ hr (by simpa [Real.dist_eq, abs_of_nonneg hr] using hrη)
  calc ‖S.Φ r v‖ ≤ ‖S.Φ r‖ * (‖u‖ + 1) :=
      (S.Φ r).le_opNorm_of_le (hv.trans (by linarith))
    _ < ε := (lt_div_iff₀ (by positivity)).1 h2

/-- **Corollary 1.6** (`cor:p-infty-solution-continuous`). Let `X`, `U` be real or complex
Banach spaces and `S = (𝕋, Φ)` an abstract linear control system with `p = ∞`. For every
input `u ∈ L^∞(ℝ₊; U)`, the map `t ↦ Φ t u` is continuous on `ℝ₊ = [0, ∞)`. -/
theorem continuousOn_Phi [CompleteSpace X] [CompleteSpace U] (S : ALCS 𝕜 X U ∞)
    (u : Lp U ∞ muPlus) :
    ContinuousOn (fun t => S.Φ t u) (Set.Ici 0) := by
  rw [Metric.continuousOn_iff]
  intro t₀ ht₀ ε hε
  rcases ht₀.eq_or_lt with h0 | hpos
  · -- continuity at `t₀ = 0`: `‖Φ t u‖ ≤ κ(t) ‖u‖ → 0`
    subst h0
    obtain ⟨η, hη, hsmall⟩ := S.small_Phi u ε hε
    refine ⟨η, hη, fun t ht hdist => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht] at hdist
    simpa [S.Phi_zero] using hsmall t ht hdist u le_rfl
  · -- continuity at `t₀ > 0`
    -- `‖Φ r v‖ < ε / 4` for `r ∈ [0, η)` and `‖v‖ ≤ ‖u‖`
    obtain ⟨η, hη, hsmall⟩ := S.small_Phi u (ε / 4) (by positivity)
    -- `0 < δ < t₀` and `2 δ < η`
    obtain ⟨δ, hδpos, hδt, hδη⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ t₀ / 2 ∧ δ ≤ η / 3 :=
      ⟨min (t₀ / 2) (η / 3), lt_min (by linarith) (by linarith), min_le_left _ _,
        min_le_right _ _⟩
    have ht₁ : 0 ≤ t₀ - δ := by linarith
    let u₁ := shiftLeft (t₀ - δ) u
    have hu₁ : ‖u₁‖ ≤ ‖u‖ := norm_shiftLeft_le _ _
    let y := S.Φ (t₀ - δ) u
    have hcomp (r : ℝ) (hr : 0 ≤ r) : S.Φ (t₀ - δ + r) u = S.T r y + S.Φ r u₁ :=
      S.composition (t₀ - δ) r ht₁ hr u u₁ u (by
        have hraw : (⇑u : ℝ → U) = concat (t₀ - δ) ⇑u
            (zeroExt ⇑u ∘ fun s => (t₀ - δ) + s) := by
          funext s
          by_cases hs : s < t₀ - δ
          · simp only [concat, ite_eq_left hs]
          · have hs' : 0 ≤ s := le_trans ht₁ (not_lt.1 hs)
            simp [concat, hs, Function.comp_apply, zeroExt, hs']
        exact (Filter.EventuallyEq.of_eq hraw).trans
          (concat_congr _ (.refl _ _) (shiftLeft_ae _ u)).symm)
    have e₀ : S.Φ t₀ u = S.T δ y + S.Φ δ u₁ := by
      simpa only [sub_add_cancel] using hcomp δ hδpos.le
    obtain ⟨δ', hδ', horbit⟩ := Metric.continuousOn_iff.1
      (S.toC0Semigroup.continuousOn_orbit y) δ hδpos.le (ε / 2) (by positivity)
    refine ⟨min δ δ', lt_min hδpos hδ', fun t _ hdist => ?_⟩
    obtain ⟨r, rfl⟩ : ∃ r, t = t₀ - δ + r := ⟨t - (t₀ - δ), by ring⟩
    rw [Real.dist_eq, show t₀ - δ + r - t₀ = r - δ by ring] at hdist
    have hd1 := lt_of_lt_of_le hdist (min_le_left _ _)
    have hd2 := lt_of_lt_of_le hdist (min_le_right _ _)
    obtain ⟨hr1, hr2⟩ := abs_lt.1 hd1
    have hr : 0 ≤ r := by linarith
    have h1 : ‖S.T r y - S.T δ y‖ < ε / 2 := by
      simpa only [dist_eq_norm] using horbit r hr (by simpa [Real.dist_eq] using hd2)
    have h2 := hsmall r hr (by linarith) u₁ hu₁
    have h3 := hsmall δ hδpos.le (by linarith) u₁ hu₁
    rw [dist_eq_norm, hcomp r hr, e₀, show S.T r y + S.Φ r u₁ - (S.T δ y + S.Φ δ u₁) =
      (S.T r y - S.T δ y) + S.Φ r u₁ - S.Φ δ u₁ by abel]
    exact ((norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans_lt (by linarith)

end ALCS

end
