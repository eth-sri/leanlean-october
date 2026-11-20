module

public import RequestProject.SmallTransport
public import RequestProject.IntervalFTC

/-!
# A double integration by parts for periodic kernels (proof of Lemma 8.4, kernel part)

Let `r(θ, s)` be a kernel on `[0, L]²` (`L = 2π`) that is periodic in both variables
(`r(θ, L) = r(θ, 0)`, `r(L, s) = r(0, s)`) and absolutely continuous in `s`,
`r(θ, s) = r(θ, 0) + ∫₀^s ρ(θ, t) dt`, where `ρ` is Lipschitz in `θ` with constant `M`.
For a bounded measurable `g` with primitive `G(θ) = ∫₀^θ g` and `G(L) = 0`, and any constant
`c`, we show (`norm_kernel_form_le`)

  `|∫₀^L conj(g(θ)) ∫₀^L r(θ, s) g(s) ds dθ| ≤ M (∫₀^L |G - c|)²`.

The proof integrates by parts in `s`, which gives
`∫₀^L r(θ, s) g(s) ds = -∫₀^L ρ(θ, t) (G(t) - c) dt =: Φ(θ)`; `Φ` is Lipschitz with constant
`M ∫|G - c|` and periodic, and a second integration by parts in `θ` gives the bound.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real Interval

noncomputable section

namespace PolyaNeumann

/-- Integration by parts for two complex-valued primitives of integrable functions. -/
theorem integral_primitives_by_parts {L : ℝ} {f g : ℝ → ℂ}
    (hf : IntervalIntegrable f volume 0 L) (hg : IntervalIntegrable g volume 0 L)
    (a b : ℂ) :
    ∫ t in (0 : ℝ)..L, (a + ∫ s in (0 : ℝ)..t, f s) * g t =
      (a + ∫ s in (0 : ℝ)..L, f s) * (b + ∫ s in (0 : ℝ)..L, g s) - a * b -
        ∫ t in (0 : ℝ)..L, f t * (b + ∫ s in (0 : ℝ)..t, g s) := by
  let F (t : ℝ) := a + ∫ s in (0 : ℝ)..t, f s
  let G (t : ℝ) := b + ∫ s in (0 : ℝ)..t, g s
  have hF : AbsolutelyContinuousOnInterval F 0 L := by
    simpa [AbsolutelyContinuousOnInterval, F] using
      absolutelyContinuousOnInterval_intervalIntegral_banach hf left_mem_uIcc
  have hG : AbsolutelyContinuousOnInterval G 0 L := by
    simpa [AbsolutelyContinuousOnInterval, G] using
      absolutelyContinuousOnInterval_intervalIntegral_banach hg left_mem_uIcc
  have hFG : AbsolutelyContinuousOnInterval (fun t => F t * G t) 0 L := hF.smul hG
  have hd : ∀ᵐ t, t ∈ uIcc 0 L → HasDerivAt (fun t => F t * G t)
      (f t * G t + F t * g t) t := by
    filter_upwards [hf.ae_hasDerivAt_integral, hg.ae_hasDerivAt_integral] with t hft hgt ht
    exact ((hft ht 0 left_mem_uIcc).const_add a).mul ((hgt ht 0 left_mem_uIcc).const_add b)
  have h₁ := hf.mul_continuousOn hG.continuousOn
  have h₂ := hg.continuousOn_mul hF.continuousOn
  have h := eq_add_intervalIntegral_of_ac_ae_deriv hFG (h₁.add h₂) hd L right_mem_uIcc
  rw [intervalIntegral.integral_add h₁ h₂] at h
  simp only [F, G, intervalIntegral.integral_same, add_zero] at h
  linear_combination -h

/-- Integration by parts for a periodic primitive against a function of mean zero. -/
lemma periodic_integral_mul_eq {L : ℝ} (hL : 0 ≤ L) {r ρ g : ℝ → ℂ}
    (hg : IntervalIntegrable g volume 0 L) (hρ : IntervalIntegrable ρ volume 0 L)
    (hr : ∀ s ∈ Icc 0 L, r s = r 0 + ∫ t in (0 : ℝ)..s, ρ t)
    (hper : r L = r 0) (hG : ∫ t in (0 : ℝ)..L, g t = 0) (c : ℂ) :
    ∫ s in (0 : ℝ)..L, r s * g s =
      -∫ t in (0 : ℝ)..L, ρ t * ((∫ u in (0 : ℝ)..t, g u) - c) := by
  calc
    _ = ∫ s in (0 : ℝ)..L, (r 0 + ∫ t in (0 : ℝ)..s, ρ t) * g s :=
      intervalIntegral.integral_congr fun s hs => congrArg (· * g s) (hr s (uIcc_of_le hL ▸ hs))
    _ = _ := by
      rw [integral_primitives_by_parts hρ hg (r 0) (-c), ← hr L ⟨hL, le_rfl⟩, hper, hG, add_zero, sub_self, zero_sub]
      congr 1
      exact intervalIntegral.integral_congr fun t _ => by ring

section

variable {L : ℝ} (hL : 0 ≤ L) {r ρ : ℝ → ℝ → ℂ} {g : ℝ → ℂ} {M : ℝ}
    (hM : 0 ≤ M) (hg : IntervalIntegrable g volume 0 L)
    (hρ : ∀ θ ∈ Icc 0 L, IntervalIntegrable (ρ θ) volume 0 L)
    (hr : ∀ θ ∈ Icc 0 L, ∀ s ∈ Icc 0 L, r θ s = r θ 0 + ∫ t in (0 : ℝ)..s, ρ θ t)
    (hρL : ∀ θ₁ ∈ Icc 0 L, ∀ θ₂ ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
      ‖ρ θ₁ t - ρ θ₂ t‖ ≤ M * |θ₁ - θ₂|)
    (hper_s : ∀ θ ∈ Icc 0 L, r θ L = r θ 0) (hG : ∫ t in (0 : ℝ)..L, g t = 0) (c : ℂ)

local notation "G" => fun t => (∫ u in (0 : ℝ)..t, g u) - c
local notation "N" => ∫ t in (0 : ℝ)..L, ‖G t‖
local notation "Φ" => fun θ => ∫ s in (0 : ℝ)..L, r θ s * g s

include hL hM hg hρ hr hρL hper_s hG in
/-- A centered primitive controls the Lipschitz constant of the kernel action. -/
lemma kernelAction_lipschitzOn : LipschitzOnWith (M * N).toNNReal Φ (Icc 0 L) := by
  have hA θ hθ : (∫ s in (0 : ℝ)..L, r θ s * g s) = -∫ t in (0 : ℝ)..L, ρ θ t * G t :=
    periodic_integral_mul_eq hL hg (hρ θ hθ) (hr θ hθ) (hper_s θ hθ) hG c
  have hGc : ContinuousOn G (uIcc 0 L) :=
    (intervalIntegral.continuousOn_primitive_interval' hg left_mem_uIcc).sub continuousOn_const
  have hGi θ hθ := (hρ θ hθ).mul_continuousOn hGc
  have hN : 0 ≤ N := intervalIntegral.integral_nonneg hL fun _ _ => norm_nonneg _
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [dist_eq_norm, Real.dist_eq, Real.coe_toNNReal _ (mul_nonneg hM hN), hA x hx, hA y hy,
    neg_sub_neg, norm_sub_rev, ← intervalIntegral.integral_sub (hGi x hx) (hGi y hy)]
  calc
    _ ≤ ∫ t in (0 : ℝ)..L, M * |x - y| * ‖G t‖ := by
      refine intervalIntegral.norm_integral_le_of_norm_le hL
        (Eventually.of_forall fun t ht => ?_) (hGc.norm.intervalIntegrable.const_mul _)
      rw [← sub_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (hρL x hx y hy t ⟨ht.1.le, ht.2⟩) (norm_nonneg _)
    _ = _ := by rw [intervalIntegral.integral_const_mul]; ring

include hL hM hg hρ hr hρL hper_s hG in
/-- Double integration by parts for a periodic kernel. -/
theorem norm_kernel_form_le (hper_θ : ∀ s ∈ Icc 0 L, r L s = r 0 s) :
    ‖∫ θ in (0 : ℝ)..L, conj (g θ) * Φ θ‖ ≤ M * N ^ 2 := by
  have h0 : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hL⟩
  have hL' : L ∈ Icc 0 L := ⟨hL, le_rfl⟩
  have hN : 0 ≤ N := intervalIntegral.integral_nonneg hL fun _ _ => norm_nonneg _
  have hGc : ContinuousOn G (uIcc 0 L) :=
    (intervalIntegral.continuousOn_primitive_interval' hg left_mem_uIcc).sub continuousOn_const
  have hΦ := kernelAction_lipschitzOn hL hM hg hρ hr hρL hper_s hG c
  let Ψ θ := Φ (projIcc 0 L hL θ)
  have hΨ : LipschitzWith (M * N).toNNReal Ψ := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    refine (hΦ.dist_le_mul _ (projIcc 0 L hL x).2 _ (projIcc 0 L hL y).2).trans ?_
    rw [Real.dist_eq, Real.dist_eq]
    exact mul_le_mul_of_nonneg_left (abs_projIcc_sub_projIcc hL) (by positivity)
  have hΨeq θ (hθ : θ ∈ Icc 0 L) : Ψ θ = Φ θ := by simp [Ψ, projIcc_of_mem hL hθ]
  have hper : Ψ L = Ψ 0 := by
    rw [hΨeq L hL', hΨeq 0 h0]
    exact intervalIntegral.integral_congr fun s hs => by rw [hper_θ s (uIcc_of_le hL ▸ hs)]
  have hdB t : ‖deriv Ψ t‖ ≤ M * N := by
    simpa only [Real.coe_toNNReal _ (mul_nonneg hM hN)] using
      norm_deriv_le_of_lipschitz hΨ (x₀ := t)
  have hdi := intervalIntegrable_of_norm_le (measurable_deriv Ψ).aestronglyMeasurable hdB 0 L
  have hmain : ∫ θ in (0 : ℝ)..L, conj (g θ) * Φ θ =
      -∫ t in (0 : ℝ)..L, deriv Ψ t * conj (G t) := by
    rw [intervalIntegral.integral_congr (g := fun θ => Ψ θ * conj (g θ)) (fun θ hθ => by
      exact (mul_comm _ _).trans (congrArg (fun z => z * conj (g θ)) (hΨeq θ (uIcc_of_le hL ▸ hθ)).symm))]
    rw [periodic_integral_mul_eq hL (intervalIntegrable_conj' hg) hdi (fun θ _ => by
      rw [integral_deriv_of_lipschitz hΨ]; ring) hper (by
        rw [intervalIntegral.intervalIntegral_conj, hG, map_zero]) (conj c)]
    congr 1
    exact intervalIntegral.integral_congr fun t _ => by
      rw [intervalIntegral.intervalIntegral_conj, map_sub]
  rw [hmain, norm_neg]
  calc
    _ ≤ ∫ t in (0 : ℝ)..L, M * N * ‖G t‖ := by
      refine intervalIntegral.norm_integral_le_of_norm_le hL
        (Eventually.of_forall fun t _ => ?_) (hGc.norm.intervalIntegrable.const_mul _)
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_right (hdB t) (norm_nonneg _)
    _ = _ := by rw [intervalIntegral.integral_const_mul]; ring

end

end PolyaNeumann

end
