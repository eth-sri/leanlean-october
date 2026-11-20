module

public import AnalyticESC.Dual.Projection
public import AnalyticESC.Analysis

@[expose] public section

/-!
# Super-exponential closeness on intervals

Cauchy estimates on a fixed complex neighbourhood bound every derivative uniformly.
On a real interval, small values force small first derivatives by comparing with a secant
of length `√η`; iterating this estimate preserves super-exponential smallness.
-/

namespace AnalyticESC

open Set Metric Filter Topology

/-- The error is eventually below every exponential. -/
def SuperExpOn (n : ℕ → ℕ) (S : ℕ → Set ℝ) (F : ℕ → ℂ → ℂ) : Prop :=
  ∀ θ > 0, ∃ A ≥ 0, ∀ᶠ k in atTop, ∀ x ∈ S k, ‖F k x‖ ≤ A * θ ^ n k

/-- Cauchy's estimate in any disc contained in the domain of a bounded holomorphic map. -/
theorem cauchy_bound {z : ℂ} {R B : ℝ} (hR : 0 < R) {U : Set ℂ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hB : ∀ z ∈ U, ‖f z‖ ≤ B)
    (hball : closedBall z R ⊆ U) (j : ℕ) : ‖iteratedDeriv j f z‖ ≤ j.factorial * B / R ^ j :=
  Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hR
    (hf.mono (closure_ball_subset_closedBall.trans hball)).diffContOnCl
    fun w hw => hB w (hball (sphere_subset_closedBall hw))

/-- Differentiation preserves super-exponential smallness on intervals at least exponentially wide. -/
theorem SuperExpOn.jet {n : ℕ → ℕ} {ε c B : ℝ} (hε : 0 < ε) (hc : 0 < c) (hB₀ : 0 ≤ B)
    {F : ℕ → ℂ → ℂ} (hf : ∀ i, DifferentiableOn ℂ (F i) (nbhd ε))
    (hB : ∀ i z, z ∈ nbhd ε → ‖F i z‖ ≤ B)
    {p q : ℕ → ℝ} (hI : ∀ i, Icc (p i) (q i) ⊆ I) (hw : ∀ i, c ^ n i ≤ q i - p i)
    (h : SuperExpOn n (fun i => Icc (p i) (q i)) F) (j : ℕ) :
    SuperExpOn n (fun i => Icc (p i) (q i)) fun i => iteratedDeriv j (F i) := by
  induction j with
  | zero => assumption
  | succ j ih =>
    intro θ hθ
    let Q := ((j + 2).factorial : ℝ) * B / (ε / 2) ^ (j + 2)
    have hQ : 0 ≤ Q := by positivity
    let b := min c θ
    obtain ⟨A, hA, H⟩ := ih (b ^ 2) (by positivity)
    refine ⟨8 * A + Q, by positivity, ?_⟩
    filter_upwards [H] with i hi x hx
    let r := b ^ n i / 2
    have hr : 0 < r := by positivity
    have hb' : b ^ n i ≤ θ ^ n i := by gcongr; grind
    have hw' : 2 * r ≤ q i - p i := by
      have hbc : b ^ n i ≤ c ^ n i := by gcongr; grind
      grind
    let f := iteratedDeriv j (F i)
    have hf' := (hf i).iteratedDeriv_complex (isOpen_nbhd _) j
    have hmem {t : ℝ} (ht : t ∈ Icc (p i) (q i)) := nbhd_mem_nhds (ofReal_mem_nbhd hε (hI i ht))
    have h₀ (t : ℝ) (ht : t ∈ Icc (p i) (q i)) : ‖f t‖ ≤ 4 * A * r ^ 2 := by
      have H := hi t ht
      rw [pow_right_comm b 2] at H
      grind
    have h₂ (t : ℝ) (ht : t ∈ Icc (p i) (q i)) : ‖deriv (deriv f) t‖ ≤ Q := by
      rw [← iteratedDeriv_succ, ← iteratedDeriv_succ]
      exact cauchy_bound (half_pos hε) (hf i) (hB i)
          ((closedBall_subset_ball (half_lt_self hε)).trans (ball_subset_nbhd (hI i ht))) (j + 2)
    obtain ⟨y, hy, hd⟩ : ∃ y ∈ Icc (p i) (q i), ‖y - x‖ = r := by
      by_cases h : x + r ≤ q i
      · exact ⟨x + r, ⟨by grind, h⟩, by simp [hr.le]⟩
      · exact ⟨x - r, ⟨by grind, by grind⟩, by simp [hr.le]⟩
    have hs := (convex_Icc (𝕜 := ℝ) (p i) (q i)).segment_subset hx hy
    let v := deriv f x
    have ht : ‖f y - f x - (y - x) • v‖ ≤ Q * r * r := by
      simpa [sub_smul, hd, sub_sub_sub_comm] using
        (convex_segment (𝕜 := ℝ) x y).norm_image_sub_le_of_norm_hasDerivWithin_le (C := Q * r)
          (fun t ht => (((hf'.differentiableAt (hmem (hs ht))).hasDerivAt.comp_ofReal).fun_sub
            ((hasDerivAt_id t).smul_const v)).hasDerivWithinAt)
          (fun t ht => by simpa only [one_smul] using ((convex_Icc (𝕜 := ℝ) (p i) (q i)).norm_image_sub_le_of_norm_hasDerivWithin_le
            (fun u hu => (((hf'.deriv (isOpen_nbhd ε)).differentiableAt (hmem hu)).hasDerivAt.comp_ofReal).hasDerivWithinAt)
            h₂ hx (hs ht)).trans (mul_le_mul_of_nonneg_left (hd ▸ norm_sub_le_of_mem_segment ht) hQ))
          (left_mem_segment ..) (right_mem_segment ..)
    have h := (norm_sub_le (f y - f x) (f y - f x - (y - x) • v)).trans (add_le_add ((norm_sub_le (f y) (f x)).trans (add_le_add (h₀ y hy) (h₀ x hx))) ht)
    rw [sub_sub_cancel, norm_smul, hd] at h
    rw [iteratedDeriv_succ]
    have H : ‖v‖ ≤ (8 * A + Q) * r := by
      apply (mul_le_mul_iff_left₀ hr).1
      nlinarith
    exact H.trans (by gcongr; grind)

end AnalyticESC
