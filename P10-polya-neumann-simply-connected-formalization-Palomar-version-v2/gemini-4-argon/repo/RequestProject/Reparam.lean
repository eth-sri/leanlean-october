module

public import Mathlib.Analysis.Calculus.Rademacher
public import RequestProject.BasePoint

/-!
# Reparametrization invariance of the transport (Lemma 10.3, first assertion)

An orientation-preserving Lipschitz change of parameter `τ` with `τ 0 = 0`, `τ L = L`
does not change the endpoint value `V_E = W_E(L)` of the transport.  More precisely, if `W`
is the transport of `γ` then `W ∘ τ` is the transport of `γ ∘ τ`.

The proof follows the paper: the absolutely continuous chain rule and uniqueness.  The only
measure-theoretic input beyond Mathlib's one-dimensional area formula is that a monotone
function has vanishing derivative almost everywhere on the preimage of a null set
(`ae_deriv_eq_zero_of_preimage_null`).
-/

@[expose] public section

open MeasureTheory Set Filter Asymptotics
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann

variable {τ : ℝ → ℝ} {Kτ : NNReal} {γ : ℝ → ℂ}

/-- If a monotone function takes the same value at `a < x`, its derivative at `x` vanishes. -/
lemma monotone_deriv_eq_zero_of_eq_left  (hm : Monotone τ) {a x : ℝ} (hax : a < x)
    (h : τ a = τ x) : deriv τ x = 0 := by
  by_cases hd : DifferentiableAt ℝ τ x
  · have h1 : HasDerivWithinAt τ 0 (Icc a x) x :=
      (hasDerivWithinAt_const x _ (τ x)).congr (fun y hy => le_antisymm (hm hy.2) (h ▸ hm hy.1))
        rfl
    exact (uniqueDiffOn_Icc hax x ⟨hax.le, le_rfl⟩).eq_deriv _
      hd.hasDerivAt.hasDerivWithinAt h1
  · exact deriv_zero_of_not_differentiableAt hd

/-- If a monotone function takes the same value at `x < b`, its derivative at `x` vanishes. -/
lemma monotone_deriv_eq_zero_of_eq_right  (hm : Monotone τ) {x b : ℝ} (hxb : x < b)
    (h : τ x = τ b) : deriv τ x = 0 := by
  by_cases hd : DifferentiableAt ℝ τ x
  · have h1 : HasDerivWithinAt τ 0 (Icc x b) x :=
      (hasDerivWithinAt_const x _ (τ x)).congr
        (fun y hy => le_antisymm (h ▸ hm hy.2) (hm hy.1)) rfl
    exact (uniqueDiffOn_Icc hxb x ⟨le_rfl, hxb.le⟩).eq_deriv _
      hd.hasDerivAt.hasDerivWithinAt h1
  · exact deriv_zero_of_not_differentiableAt hd

/-- A monotone function has vanishing derivative at almost every point which it maps into a
given null set. -/
theorem ae_deriv_eq_zero_of_preimage_null  (hm : Monotone τ) 
    (hN : volume N = 0) : ∀ᵐ s, τ s ∈ N → deriv τ s = 0 := by
  set N' := toMeasurable volume N
  set S := {s | DifferentiableAt ℝ τ s} ∩ ({s | deriv τ s ≠ 0} ∩ τ ⁻¹' N')
  have hS : MeasurableSet S :=
    (measurableSet_of_differentiableAt ℝ τ).inter
      (((measurable_deriv τ) (measurableSet_singleton 0)).compl.inter
        (hm.measurable (measurableSet_toMeasurable _ _)))
  have himg := lintegral_image_eq_lintegral_abs_deriv_mul hS (fun x hx => hx.1.hasDerivAt.hasDerivWithinAt) (by
    intro x hx y hy hxy
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hx.2.1 (monotone_deriv_eq_zero_of_eq_right hm h hxy)
    · exact hy.2.1 (monotone_deriv_eq_zero_of_eq_right hm h hxy.symm)) (fun _ => 1)
  have h0 : ∫⁻ x in S, ENNReal.ofReal |deriv τ x| * 1 = 0 := by
    rw [← himg]
    simp [Measure.restrict_apply MeasurableSet.univ]
    exact measure_mono_null (by
      rintro _ ⟨x, hx, rfl⟩; exact hx.2.2) (show volume N' = 0 by rw [measure_toMeasurable]; exact hN)
  rw [lintegral_eq_zero_iff (by fun_prop)] at h0
  filter_upwards [show ∀ᵐ s, s ∉ S by
    filter_upwards [(ae_restrict_iff' hS).mp h0] with x hx hxS
    have := hx hxS
    simp only [mul_one, Pi.zero_apply, ENNReal.ofReal_eq_zero] at this
    exact hxS.2.1 (abs_nonpos_iff.mp this)] with s hs hsN
  by_contra hne
  by_cases hd : DifferentiableAt ℝ τ s
  · exact hs ⟨hd, hne, subset_toMeasurable _ _ hsN⟩
  · exact hne (deriv_zero_of_not_differentiableAt hd)

/-- Composition of a function which is Lipschitz on a set `S` with a function having
derivative zero and mapping a neighbourhood into `S` has derivative zero. -/
lemma hasDerivAt_comp_zero_of_lipschitzOnWith {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : ℝ → F}    {x : ℝ}
    (hg : LipschitzOnWith K g S) (hτ : HasDerivAt τ 0 x) (hmap : ∀ᶠ y in 𝓝 x, τ y ∈ S) :
    HasDerivAt (fun y => g (τ y)) 0 x := by
  rw [hasDerivAt_iff_isLittleO] at hτ ⊢
  simp at hτ ⊢
  refine IsBigO.trans_isLittleO ?_ hτ
  refine IsBigO.of_bound K ?_
  filter_upwards [hmap] with y hy
  rw [← dist_eq_norm, Real.norm_eq_abs, ← Real.dist_eq]
  exact hg.dist_le_mul _ hy _ hmap.self_of_nhds

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
variable {C : ℝ → A} {M L L' : ℝ} {W : ℝ → A} {τ : ℝ → ℝ}

/-- Reparametrization of a linear Volterra equation: if `W` solves
`W(θ) = 1 + ∫₀^θ C W` on `[0, L]` and `τ` is monotone, Lipschitz, `τ 0 = 0`, `τ L' = L`, then
`W ∘ τ` solves the equation with coefficient `τ' · (C ∘ τ)` on `[0, L']`. -/
theorem volterra_reparam (hC : StronglyMeasurable C) (hM : ∀ s, ‖C s‖ ≤ M)
    (hW : ContinuousOn W (Icc 0 L))
    (eW : ∀ θ ∈ Icc 0 L, W θ = 1 + ∫ s in 0..θ, C s * W s)
    (hm : Monotone τ)  (hτ : LipschitzWith Kτ τ) (h0 : τ 0 = 0) (hL : τ L' = L) :
    ∀ s ∈ Icc 0 L', W (τ s) = 1 + ∫ u in 0..s, deriv τ u • C (τ u) * W (τ u) := by
  intro s hs
  have hmap : MapsTo τ (Icc 0 L') (Icc 0 L) := fun x hx => ⟨h0 ▸ hm hx.1, hL ▸ hm hx.2⟩
  obtain ⟨KW, hKW⟩ := volterra_lipschitzOn hC.aestronglyMeasurable hM hW eW
  obtain ⟨S, hS⟩ := isCompact_Icc.exists_bound_of_continuousOn hW
  have hf :=
    hKW.comp hτ.lipschitzOnWith hmap
  have hWτ := hW.comp hτ.continuous.continuousOn hmap
  have hgB : ∀ x ∈ Icc 0 L', ‖(deriv τ x • C (τ x)) * W (τ x)‖ ≤ Kτ * M * S := by
    intro x hx
    refine (norm_mul_le _ _).trans ?_
    rw [norm_smul]
    have h1 : ‖deriv τ x‖ ≤ Kτ := norm_deriv_le_of_lipschitz hτ
    have h2 := hM (τ x)
    have h3 := hS _ (hmap hx)
    have:= (norm_nonneg _).trans h2
    gcongr
  have hN := ae_iff.mp (volterra_ae_hasDerivAt hC.aestronglyMeasurable hM hW eW)
  have key := eq_add_integral_of_ae_hasDerivAt hf (by
    refine Integrable.of_bound ?_ (Kτ * M * S) ?_
    · exact ((measurable_deriv τ).aestronglyMeasurable.smul
        (hC.comp_measurable hm.measurable).aestronglyMeasurable).restrict.mul
        (hWτ.aestronglyMeasurable measurableSet_Icc)
    · exact (ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall hgB)) hgB (show ∀ᵐ x, x ∈ Ioo 0 L' → HasDerivAt (fun u => W (τ u)) ((deriv τ x • C (τ x)) * W (τ x)) x by
        filter_upwards [hτ.ae_differentiableAt, ae_deriv_eq_zero_of_preimage_null hm hN]
          with x hxd hxN hx
        by_cases hz : deriv τ x = 0
        · have h1 := hz ▸ hxd.hasDerivAt
          have := hasDerivAt_comp_zero_of_lipschitzOnWith hKW h1
            (by filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
                exact hmap (Ioo_subset_Icc_self hy))
          simpa [hz] using this
        · have hτx : τ x ∈ Ioo 0 L :=
            ⟨lt_of_le_of_ne (h0 ▸ hm hx.1.le)
              (fun h => hz (monotone_deriv_eq_zero_of_eq_left hm hx.1 (h0.trans h))),
             lt_of_le_of_ne (hL ▸ hm hx.2.le)
              (fun h => hz (monotone_deriv_eq_zero_of_eq_right hm hx.2 (h.trans hL.symm)))⟩
          have hWd : HasDerivAt W (C (τ x) * W (τ x)) (τ x) := by
            by_contra hc
            exact hz (hxN fun h => hc (h hτx))
          have := hWd.scomp x hxd.hasDerivAt
          rw [smul_mul_assoc]
          exact this) s hs
  simpa [h0, show W 0 = 1 by
    simpa using eW 0 (by
      have := hmap ⟨le_rfl, hs.1.trans hs.2⟩; rwa [h0] at this)] using key

/-- The almost-everywhere chain rule for a Lipschitz curve composed with a monotone Lipschitz
change of parameter. -/
theorem ae_deriv_comp  {K : NNReal} (hγ : LipschitzWith K γ) 
    (hm : Monotone τ)  (hτ : LipschitzWith Kτ τ) :
    ∀ᵐ s, deriv (γ ∘ τ) s = ((deriv τ s : ℝ) : ℂ) * deriv γ (τ s) := by
  filter_upwards [hτ.ae_differentiableAt, ae_deriv_eq_zero_of_preimage_null hm (ae_iff.mp (hγ.ae_differentiableAt (μ := volume)))]
    with s hsd hsN
  by_cases hz : deriv τ s = 0
  · have := hasDerivAt_comp_zero_of_lipschitzOnWith (hγ.lipschitzOnWith (s := univ))
      (hz ▸ hsd.hasDerivAt) (Eventually.of_forall fun _ => mem_univ _)
    rw [show γ ∘ τ = fun y => γ (τ y) from rfl, this.deriv, hz]
    simp
  · have hγd : DifferentiableAt ℝ γ (τ s) := by
      by_contra h
      exact hz (hsN h)
    rw [(hγd.hasDerivAt.scomp s hsd.hasDerivAt).deriv, Complex.real_smul]

/-- The transport coefficient of a reparametrized curve. -/
lemma transportCoeff_comp_of_deriv   
    (h : deriv (γ ∘ τ) s = ((deriv τ s : ℝ) : ℂ) * deriv γ (τ s)) :
    transportCoeff (γ ∘ τ) E s = deriv τ s • transportCoeff γ E (τ s) := by
  unfold transportCoeff
  rw [h, map_mul, Complex.conj_ofReal]
  ext1 v
  simp
  module

/-- Lemma 10.3 (reparametrization): an orientation-preserving Lipschitz change of parameter
fixing the endpoints does not change the monodromy. -/
theorem monodromy_comp   (hγ : LipschitzWith K γ) 
    (hm : Monotone τ) {Kτ} (hτ : LipschitzWith Kτ τ) (h0 : τ 0 = 0)
    (hL : τ (2 * π) = 2 * π) {E} {W W'} (hW : IsTransport γ E W)
    (hW' : IsTransport (γ ∘ τ) E W') : monodromy W' = monodromy W := by
  unfold monodromy
  rw [transport_unique_of_lipschitz (γ ∘ τ) (hγ.comp hτ) E hW' (by
    refine ⟨hW.1.comp hτ.continuous.continuousOn (fun x hx => ⟨h0 ▸ hm hx.1, hL ▸ hm hx.2⟩), fun s hs => ?_⟩
    rw [Function.comp_apply, volterra_reparam (by
      exact (show Continuous fun z : ℂ => (-(Complex.I * (Real.sqrt E)) / 2) • (z • ContinuousLinearMap.adjoint shiftN + conj z • shiftN) by
        fun_prop).comp_stronglyMeasurable (measurable_deriv γ).stronglyMeasurable)
      (transportCoeff_norm_le γ E hγ) hW.1 hW.2 hm hτ h0 hL s hs]
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_deriv_comp hγ hm hτ] with u hu _
    rw [transportCoeff_comp_of_deriv hu, Function.comp_apply]
    rfl) ⟨by positivity, le_rfl⟩, Function.comp_apply, hL]

end PolyaNeumann

end
