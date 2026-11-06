module

public import AnalyticESC.Basic

public section

/-!
# The classes `S^ω_ε(I)` and `S^ω(I)`

The inclusion `f(cl B_ε) ⊆ B_ε` in condition (B) of the class `S^ω_ε(I)` follows from the other
conditions. Hence the classes `S^ω_ε(I)` decrease as `ε` increases, and their union `S^ω(I)` is
described by conditions on `[0,1]`.
-/

namespace AnalyticESC

variable {f : ℂ → ℂ} 

open Set Metric

/-- Every point of `cl B_ε` lies within distance `ε` of a point of `I`. -/
theorem exists_mem_I_norm_sub_le (hε : 0 ≤ ε) (hz : z ∈ 𝔹 ε) :
    ∃ x ∈ I, ‖z - x‖ ≤ ε := by
  have hz' := closure_thickening_subset_cthickening ε _ hz
  rw [isCompact_image_I.cthickening_eq_biUnion_closedBall hε] at hz'
  obtain ⟨_, ⟨x, hx, rfl⟩, hzx⟩ := mem_iUnion₂.1 hz'
  exact ⟨x, hx, mem_closedBall_iff_norm.1 hzx⟩

/-- A map complex analytic on `B_{2ε}`, real at the real points of `B_{2ε}`, with
`f(I) ⊆ I` and `0 < |f'| < 1` on `cl B_ε`, lies in `S^ω_ε(I)`. -/
theorem InClass.of_deriv (hε : 0 < ε)
    (hd : DifferentiableOn ℂ f (𝔑 ε))
    (him : ∀ x : ℝ, (x : ℂ) ∈ 𝔑 ε → (f x).im = 0)
    (hI : Ɐ (f x).re ∈ I)
    (hne : ∀ z ∈ 𝔹 ε, deriv f z ≠ 0)
    (hlt : ∀ z ∈ 𝔹 ε, ‖deriv f z‖ < 1) : InClass ε f := by
  refine ⟨hd, him, hI, ?_, hne, hlt⟩
  have hsub : 𝔹 ε ⊆ 𝔑 ε := closure_nbhd_subset (by linarith)
  -- `|f'|` attains its maximum `c < 1` on the compact set `cl B_ε`
  have hcont : ContinuousOn (fun z => ‖deriv f z‖) (𝔹 ε) :=
    ((hd.deriv isOpen_nbhd).continuousOn.mono hsub).norm
  obtain ⟨w, hw, hmax⟩ := (isCompact_closure_nbhd ε).exists_isMaxOn
    ⟨0, zero_mem_closure_nbhd hε⟩ hcont
  have hc : ‖deriv f w‖ < 1 := by simp_all
  intro z hz
  obtain ⟨x, hx, hzx⟩ := exists_mem_I_norm_sub_le hε.le hz
  have hxcl := ofReal_mem_closure hε hx
  -- the mean value inequality on the convex set `cl B_ε`
  have hmv : ‖f z - f x‖ ≤ ‖deriv f w‖ * ‖z - x‖ :=
    (convex_nbhd ε).closure.norm_image_sub_le_of_norm_deriv_le
      (fun y hy => hd.differentiableAt (isOpen_nbhd.mem_nhds (hsub hy)))
      (fun y hy => hmax hy) hxcl hz
  -- `f(x)` is the real point `(f x).re` of `I`
  have hfx : f x = ((f x).re : ℂ) :=
    Complex.ext rfl (by aesop)
  refine ball_subset_nbhd (hI x hx) (mem_ball_iff_norm.2 ?_)
  rw [← hfx]
  calc ‖f z - f x‖ ≤ ‖deriv f w‖ * ‖z - x‖ := hmv
    _ ≤ ‖deriv f w‖ * ε := by bound
    _ < 1 * ε := by nlinarith
    _ = ε := one_mul ε

/-- Nesting of the classes: `S^ω_ε(I) ⊆ S^ω_{ε'}(I)` for `0 < ε' ≤ ε`. -/
theorem InClass.mono (h : InClass ε f) (hε' : 0 < ε') (hle : ε' ≤ ε) :
    InClass ε' f := by
  exact InClass.of_deriv hε' (h.differentiableOn.mono (nbhd_mono (by linarith))) (fun x hx => h.im_eq_zero x ((nbhd_mono (by linarith)) hx))
    h.re_mem_I (fun z hz => h.deriv_ne_zero z ((closure_mono (nbhd_mono hle)) hz))
    (fun z hz => h.norm_deriv_lt_one z ((closure_mono (nbhd_mono hle)) hz))

/-- The direction used for perturbations: a map complex analytic on an open
neighbourhood `U` of `I`, real at the real points of `U`, with `f(I) ⊆ I` and `0 < |f'| < 1` on
`I`, lies in `S^ω_ε(I)` for some `ε > 0`. -/
theorem exists_inClass (hU : IsOpen U) (hIU : Iℂ ⊆ U)
    (hd : DifferentiableOn ℂ f U) (him : ∀ x : ℝ, (x : ℂ) ∈ U → (f x).im = 0)
    (hI : Ɐ (f x).re ∈ I) (hne : Ɐ deriv f x ≠ 0)
    (hlt : Ɐ ‖deriv f x‖ < 1) : ∃ ε > 0, InClass ε f := by
  -- the open set `{z ∈ U : 0 < |f'(z)| < 1}` contains the compact set `I`
  set V := U ∩ deriv f ⁻¹' ({0}ᶜ ∩ ball 0 1)
  obtain ⟨δ, hδ, hδV⟩ := isCompact_image_I.exists_cthickening_subset_open ((hd.deriv hU).continuousOn.isOpen_inter_preimage hU (isOpen_compl_singleton.inter isOpen_ball)) (by rintro _ ⟨x, hx, rfl⟩; exact ⟨hIU (mem_image_of_mem _ hx), hne x hx, mem_ball_zero_iff.2 (hlt x hx)⟩)
  obtain ⟨δ', hδ', hδ'U⟩ := isCompact_image_I.exists_cthickening_subset_open hU hIU
  set ε := min δ (δ' / 2)
  have h2 : 𝔑 ε ⊆ U := fun z hz =>
    hδ'U (thickening_subset_cthickening_of_le (by grind) _ hz)
  have hcl : 𝔹 ε ⊆ V := fun z hz =>
    hδV (cthickening_mono (min_le_left _ _) _ (closure_thickening_subset_cthickening ε _ hz))
  exact ⟨ε, lt_min hδ (half_pos hδ'), InClass.of_deriv (lt_min hδ (half_pos hδ')) (hd.mono h2) (fun x hx => him x (h2 hx)) hI
    (fun z hz => (hcl hz).2.1) (fun z hz => mem_ball_zero_iff.1 (hcl hz).2.2)⟩

/-- Finitely many maps of `S^ω(I)` lie in a common class `S^ω_ε(I)`. -/
theorem exists_inClass_forall {f : Fin N → ℂ → ℂ}
    (h : ∀ i, ∃ ε > 0, InClass ε (f i)) : ∃ ε > 0, ∀ i, InClass ε (f i) := by
  choose ε hε hf using h
  rcases isEmpty_or_nonempty (Fin N) with hN | hN
  · exact ⟨1, one_pos, isEmptyElim⟩
  · obtain ⟨j, hj⟩ := Finite.exists_min ε
    exact ⟨ε j, hε j, fun i => (hf i).mono (hε j) (hj i)⟩

namespace IFS


end IFS

end AnalyticESC
