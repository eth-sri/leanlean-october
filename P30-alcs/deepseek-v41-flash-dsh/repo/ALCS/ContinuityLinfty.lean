module

public import ALCS.ZeroClass

@[expose] public section

/-!
# Continuity of the input response for `p = ∞` (Corollary 1.6)

**Corollary 1.6**. Let `X`, `U` be Banach spaces and `(𝕋, Φ)` an abstract linear control
system with `p = ∞`. For all `u ∈ L^∞(ℝ₊; U)`, `t ↦ Φ_t u` is continuous on `ℝ₊`.
This answers positively Problem 2.4 of [Weiss 1989].

The proof only uses Theorem 1.5 (`ALCS.zero_class`), the composition property and the
strong continuity of the semigroup at `0`:

* at `t₀ = 0`, `‖Φ_t u‖ ≤ κ(t) ‖u‖ → 0` (`small_Phi`);
* at `t₀ > 0`, with `t₁ = t₀ - δ` and `u₁ = u (t₁ + ·)`, the composition property gives
  `Φ_{t₁ + r} u = T_r (Φ_{t₁} u) + Φ_r u₁`, and both terms are close to their values at
  `r = δ` because `r` and `δ` are small.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {U : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U]

namespace ALCS

variable (S : ALCS 𝕜 X U)

/-- Consequence of Theorem 1.5: for `ε > 0` there is `η > 0` such that
`‖Φ r v‖ < ε` for all `r ∈ [0, η)` and all inputs `v` with `‖v‖ ≤ ‖u‖`. -/
theorem small_Phi [CompleteSpace X] [CompleteSpace U] (u : Lp U ∞ muPlus) (ε : ℝ) (hε : 0 < ε) :
    ∃ η > 0, ∀ r, 0 ≤ r → r < η → ∀ v : Lp U ∞ muPlus, ‖v‖ ≤ ‖u‖ → ‖S.Φ r v‖ < ε := by
  obtain ⟨η, hη, hκ⟩ := Metric.tendsto_nhdsWithin_nhds.1 (S.zero_class) (ε / (‖u‖ + 1))
    (by positivity)
  refine ⟨η, hη, fun r hr hrη v hv => ?_⟩
  have h1 : ‖S.Φ r‖ < ε / (‖u‖ + 1) := by
    have := hκ (Set.mem_Ici.2 hr) (by rwa [Real.dist_eq, sub_zero, abs_of_nonneg hr] at *)
    simpa using this
  have h2 := (lt_div_iff₀ (by positivity)).1 h1
  calc ‖S.Φ r v‖ ≤ ‖S.Φ r‖ * ‖v‖ := (S.Φ r).le_opNorm _
    _ ≤ ‖S.Φ r‖ * (‖u‖ + 1) := by gcongr; linarith
    _ < ε := h2

/-- **Corollary 1.6**. Let `X`, `U` be real or complex Banach spaces and `S = (𝕋, Φ)` an
abstract linear control system with `p = ∞`. For every input `u ∈ L^∞(ℝ₊; U)`, the map
`t ↦ Φ t u` is continuous on `ℝ₊ = [0, ∞)`. -/
theorem continuousOn_Phi [CompleteSpace X] [CompleteSpace U] (u : Lp U ∞ muPlus) :
    ContinuousOn (fun t => S.Φ t u) (Set.Ici 0) := by
  rw [Metric.continuousOn_iff]
  intro t₀ ht₀ ε hε
  rw [Set.mem_Ici] at ht₀
  rcases ht₀.eq_or_lt with h0 | hpos
  · -- continuity at `t₀ = 0`
    subst h0
    obtain ⟨η, hη, hs⟩ := S.small_Phi u ε hε
    refine ⟨η, hη, fun t ht hd => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht] at hd
    show dist (S.Φ t u) (S.Φ 0 u) < ε
    rw [S.Phi_zero, zero_apply, dist_zero_right]
    exact hs t ht hd u le_rfl
  · -- continuity at `t₀ > 0`, comparing with the values at `t₁ = t₀ - δ`
    obtain ⟨τ, hτ, M, hM, hM'⟩ := S.toC0Semigroup.exists_bound_near_zero
    obtain ⟨η, hη, hsmall⟩ := S.small_Phi u (ε / 8) (by positivity)
    obtain ⟨δ, hδ, hδt, hδη, hδτ⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ t₀ / 2 ∧ δ ≤ η / 2 ∧ δ ≤ τ / 2 :=
      ⟨min (t₀ / 2) (min (η / 2) (τ / 2)), lt_min (by linarith) (lt_min (by positivity) (by positivity)),
        min_le_left _ _, le_trans (min_le_right _ _) (min_le_left _ _),
        le_trans (min_le_right _ _) (min_le_right _ _)⟩
    have ht₁ : 0 ≤ t₀ - δ := by linarith
    obtain ⟨u₁, hu₁, hcatu⟩ := exists_shift (t₀ - δ) u
    obtain ⟨y, hy⟩ : ∃ y : X, y = S.Φ (t₀ - δ) u := ⟨_, rfl⟩
    -- composition: `Φ (t₁ + r) u = T r y + Φ r u₁`
    have hcomp : ∀ r, 0 ≤ r → S.Φ (t₀ - δ + r) u = S.T r y + S.Φ r u₁ := by
      intro r hr
      rw [hy]
      exact S.composition (t₀ - δ) r ht₁ hr u u₁ u hcatu
    have e₀ : S.Φ t₀ u = S.T δ y + S.Φ δ u₁ := by
      have h := hcomp δ hδ.le
      rwa [sub_add_cancel] at h
    -- strong continuity at `0` for the fixed vector `y`
    obtain ⟨δ₂, hδ₂, hy2⟩ := Metric.tendsto_nhdsWithin_nhds.1 (S.T_cont y) (ε / (2 * (M + 1)))
      (by positivity)
    refine ⟨min δ δ₂, lt_min hδ hδ₂, fun t _ hdist => ?_⟩
    have hd : |t - t₀| < min δ δ₂ := by rwa [Real.dist_eq] at hdist
    obtain ⟨r, rfl⟩ : ∃ r, t = t₀ - δ + r := ⟨t - (t₀ - δ), by ring⟩
    rw [show t₀ - δ + r - t₀ = r - δ by ring] at hd
    obtain ⟨hr1, hr2⟩ := abs_lt.1 hd
    have hm1 : min δ δ₂ ≤ δ := min_le_left _ _
    have hr : 0 ≤ r := by linarith
    have hrη : r < η := by linarith
    have hsmall' : ∀ s : ℝ, 0 ≤ s → s < δ₂ → ‖S.T s y - y‖ < ε / (2 * (M + 1)) := by
      intro s hs hs2
      have h := hy2 (Set.mem_Ici.2 hs) (by rwa [Real.dist_eq, sub_zero, abs_of_nonneg hs])
      rwa [dist_eq_norm] at h
    -- the two terms
    have k1 : ‖S.T r y - S.T δ y‖ ≤ M * ‖S.T |r - δ| y - y‖ := by
      rcases le_total δ r with hle | hle
      · have hb : ‖S.T δ‖ ≤ M := hM' δ hδ.le (by linarith)
        have h := S.orbit_sub y δ (r - δ) hδ.le (show 0 ≤ r - δ by linarith)
        have e : S.T r y - S.T δ y = S.T δ (S.T (r - δ) y - y) := by
          simpa only [show δ + (r - δ) = r by ring] using h
        rw [e, abs_of_nonneg (by linarith)]
        calc ‖S.T δ (S.T (r - δ) y - y)‖ ≤ ‖S.T δ‖ * ‖S.T (r - δ) y - y‖ := (S.T δ).le_opNorm _
          _ ≤ M * ‖S.T (r - δ) y - y‖ := by gcongr
      · have hb : ‖S.T r‖ ≤ M := hM' r hr (by linarith)
        have h := S.orbit_sub y r (δ - r) hr (show 0 ≤ δ - r by linarith)
        have e : S.T r y - S.T δ y = -(S.T r (S.T (δ - r) y - y)) := by
          have h' : S.T (r + (δ - r)) y - S.T r y = S.T r (S.T (δ - r) y - y) := h
          rw [show r + (δ - r) = δ by ring] at h'
          rw [← h']
          abel
        rw [e, norm_neg]
        calc ‖S.T r (S.T (δ - r) y - y)‖ ≤ ‖S.T r‖ * ‖S.T (δ - r) y - y‖ := (S.T r).le_opNorm _
          _ ≤ M * ‖S.T |r - δ| y - y‖ := by
              rw [abs_of_nonpos (by linarith), show δ - r = -(r - δ) by ring]
              gcongr
    have k1' : ‖S.T r y - S.T δ y‖ < ε / 2 := by
      refine k1.trans_lt ?_
      have hrδ₂ : |r - δ| < δ₂ := lt_of_lt_of_le hd (min_le_right _ _)
      have h := hsmall' |r - δ| (abs_nonneg _) hrδ₂
      calc M * ‖S.T |r - δ| y - y‖ ≤ M * (ε / (2 * (M + 1))) := by gcongr
        _ < ε / 2 := by
            rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
            nlinarith
    have k2 : ‖S.Φ r u₁ - S.Φ δ u₁‖ ≤ ‖S.Φ r u₁‖ + ‖S.Φ δ u₁‖ := norm_sub_le _ _
    have h3 := hsmall r hr hrη u₁ hu₁
    have h4 := hsmall δ hδ.le (by linarith) u₁ hu₁
    show dist (S.Φ (t₀ - δ + r) u) (S.Φ t₀ u) < ε
    rw [dist_eq_norm, hcomp r hr, e₀]
    have key : S.T r y + S.Φ r u₁ - (S.T δ y + S.Φ δ u₁)
        = (S.T r y - S.T δ y) + S.Φ r u₁ - S.Φ δ u₁ := by abel
    rw [key]
    have n1 := norm_sub_le ((S.T r y - S.T δ y) + S.Φ r u₁) (S.Φ δ u₁)
    have n2 := norm_add_le (S.T r y - S.T δ y) (S.Φ r u₁)
    linarith [k1', h3, h4]

end ALCS

end
