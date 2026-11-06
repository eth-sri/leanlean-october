module

public import AnalyticESC.Basic

@[expose] public section

/-!
# The classes `S^ω_ε(I)` and `S^ω(I)`

The inclusion `f(cl B_ε) ⊆ B_ε` in condition (B) of the class `S^ω_ε(I)` follows from the other
conditions. Hence the classes `S^ω_ε(I)` decrease as `ε` increases, and their union `S^ω(I)` is
described by conditions on `[0,1]`.
-/

namespace AnalyticESC

open Set Metric Filter Topology

/-- Every point of `cl B_ε` lies within distance `ε` of a point of `I`. -/
theorem exists_mem_I_norm_sub_le {ε : ℝ} (hε : 0 ≤ ε) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    ∃ x ∈ I, ‖z - x‖ ≤ ε := by
  have hz' := closure_thickening_subset_cthickening ε _ hz
  rw [isCompact_image_I.cthickening_eq_biUnion_closedBall hε] at hz'
  obtain ⟨_, ⟨x, hx, rfl⟩, hzx⟩ := mem_iUnion₂.1 hz'
  exact ⟨x, hx, mem_closedBall_iff_norm.1 hzx⟩

/-- A map complex analytic on `B_{2ε}`, real at the real points of `B_{2ε}`, with
`f(I) ⊆ I` and `0 < |f'| < 1` on `cl B_ε`, lies in `S^ω_ε(I)`. -/
theorem InClass.of_deriv {ε : ℝ} (hε : 0 < ε) {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (nbhd (2 * ε)))
    (him : ∀ x : ℝ, (x : ℂ) ∈ nbhd (2 * ε) → (f x).im = 0)
    (hI : ∀ x ∈ I, (f x).re ∈ I)
    (hne : ∀ z ∈ closure (nbhd ε), deriv f z ≠ 0)
    (hlt : ∀ z ∈ closure (nbhd ε), ‖deriv f z‖ < 1) : InClass ε f := by
  refine ⟨hd, him, hI, ?_, hne, hlt⟩
  have hsub : closure (nbhd ε) ⊆ nbhd (2 * ε) := closure_nbhd_subset (by linarith)
  obtain ⟨w, hw, hmax⟩ := (isCompact_closure_nbhd ε).exists_isMaxOn
    ⟨0, zero_mem_closure_nbhd hε⟩ (((hd.deriv (isOpen_nbhd _)).continuousOn.mono hsub).norm)
  intro z hz
  obtain ⟨x, hx, hzx⟩ := exists_mem_I_norm_sub_le hε.le hz
  have hfx : f x = ((f x).re : ℂ) :=
    Complex.ext rfl (by simp [him x (ofReal_mem_nbhd (by linarith) hx)])
  refine ball_subset_nbhd (hI x hx) (mem_ball_iff_norm.2 ?_)
  rw [← hfx]
  exact (((convex_nbhd ε).closure.norm_image_sub_le_of_norm_deriv_le
    (fun y hy => hd.differentiableAt ((isOpen_nbhd _).mem_nhds (hsub hy)))
    (fun y hy => hmax hy) (subset_closure (ofReal_mem_nbhd hε hx)) hz).trans
    (mul_le_mul_of_nonneg_left hzx (norm_nonneg _))).trans_lt
    ((mul_lt_mul_of_pos_right (hlt w hw) hε).trans_eq (one_mul ε))

/-- Nesting of the classes: `S^ω_ε(I) ⊆ S^ω_{ε'}(I)` for `0 < ε' ≤ ε`. -/
theorem InClass.mono {ε ε' : ℝ} {f : ℂ → ℂ} (h : InClass ε f) (hε' : 0 < ε') (hle : ε' ≤ ε) :
    InClass ε' f := by
  have h2 : nbhd (2 * ε') ⊆ nbhd (2 * ε) := nbhd_mono (by linarith)
  have hcl : closure (nbhd ε') ⊆ closure (nbhd ε) := closure_mono (nbhd_mono hle)
  exact InClass.of_deriv hε' (h.differentiableOn.mono h2) (fun x hx => h.im_eq_zero x (h2 hx))
    h.re_mem_I (fun z hz => h.deriv_ne_zero z (hcl hz))
    (fun z hz => h.norm_deriv_lt_one z (hcl hz))

/-- The direction used for perturbations: a map complex analytic on an open
neighbourhood `U` of `I`, real at the real points of `U`, with `f(I) ⊆ I` and `0 < |f'| < 1` on
`I`, lies in `S^ω_ε(I)` for some `ε > 0`. -/
theorem exists_inClass {U : Set ℂ} (hU : IsOpen U) (hIU : ((↑) : ℝ → ℂ) '' I ⊆ U) {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f U) (him : ∀ x : ℝ, (x : ℂ) ∈ U → (f x).im = 0)
    (hI : ∀ x ∈ I, (f x).re ∈ I) (hne : ∀ x ∈ I, deriv f x ≠ 0)
    (hlt : ∀ x ∈ I, ‖deriv f x‖ < 1) : ∃ ε > 0, InClass ε f := by
  set V := U ∩ deriv f ⁻¹' ({0}ᶜ ∩ ball 0 1)
  have hV : IsOpen V := (hd.deriv hU).continuousOn.isOpen_inter_preimage hU
    (isOpen_compl_singleton.inter isOpen_ball)
  obtain ⟨δ, hδ, hδV⟩ := isCompact_image_I.exists_thickening_subset_open hV fun _ ⟨x, hx, h⟩ =>
    h ▸ ⟨hIU (mem_image_of_mem _ hx), hne x hx, mem_ball_zero_iff.2 (hlt x hx)⟩
  have h2 : nbhd (2 * (δ / 2)) ⊆ U := by
    rw [mul_div_cancel₀ _ two_ne_zero]; exact hδV.trans inter_subset_left
  have hcl : closure (nbhd (δ / 2)) ⊆ V := (closure_nbhd_subset (half_lt_self hδ)).trans hδV
  exact ⟨δ / 2, half_pos hδ, InClass.of_deriv (half_pos hδ) (hd.mono h2) (fun x hx => him x (h2 hx))
    hI (fun z hz => (hcl hz).2.1) (fun z hz => mem_ball_zero_iff.1 (hcl hz).2.2)⟩

/-- Finitely many maps of `S^ω(I)` lie in a common class `S^ω_ε(I)`. -/
theorem exists_inClass_forall {N : ℕ} (hN : 0 < N) {f : Fin N → ℂ → ℂ}
    (h : ∀ i, ∃ ε > 0, InClass ε (f i)) : ∃ ε > 0, ∀ i, InClass ε (f i) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  choose ε hε hf using h
  obtain ⟨j, hj⟩ := Finite.exists_min ε
  exact ⟨ε j, hε j, fun i => (hf i).mono (hε j) (hj i)⟩

end AnalyticESC
