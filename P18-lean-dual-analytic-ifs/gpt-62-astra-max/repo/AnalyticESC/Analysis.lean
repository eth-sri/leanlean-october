module

public import AnalyticESC.Basic

@[expose] public section

/-!
# Real-variable and identity-theorem lemmas

Lemma 3.1 (closeness of two functions gives closeness of their derivatives), its iterate, the
identity theorem on `B_ε` in the forms used in the paper, and the elementary bound (4.3).
-/

namespace AnalyticESC

open Set Metric Filter Topology

/-! ## The identity theorem on `B_ε` -/

/-- An infinite agreement set has an accumulation point in the compact interval. -/
lemma agree_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ} {s : Set ℝ} {f g : ℝ → E}
    (hf : AnalyticOnNhd ℝ f (Icc a b)) (hg : AnalyticOnNhd ℝ g (Icc a b)) (hi : s.Infinite) (hs : s ⊆ Icc a b)
    (he : EqOn f g s) : EqOn f g (Icc a b) := by
  obtain ⟨p,hp,h⟩ := hi.exists_accPt_of_subset_isCompact isCompact_Icc hs
  exact hf.eqOn_of_preconnected_of_frequently_eq hg isPreconnected_Icc hp ((accPt_iff_frequently_nhdsNE.mp h).mono fun _ hx => he hx)

lemma real_slice {s : Set ℝ} {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Complex.ofReal '' s)) : AnalyticOnNhd ℝ (f ∘ Complex.ofReal) s :=
  fun x hx => (hf _ (mem_image_of_mem _ hx)).restrictScalars.comp (Complex.ofRealCLM.analyticAt x)

/-- Equality of jets means infinite analytic order of the difference, hence local
and then global agreement. -/
lemma agree_jets {s : Set ℂ} (hs : IsPreconnected s) {x} (hx : x ∈ s) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f s) (hg : AnalyticOnNhd ℂ g s) (h : ∀ k : ℕ, deriv^[k] f x = deriv^[k] g x) : EqOn f g s := by
  apply hf.eqOn_of_preconnected_of_eventuallyEq hg hs hx
  have H : analyticOrderAt (f-g) x = ⊤ := ENat.eq_top_iff_forall_ge.mpr fun n =>
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ((hf x hx).sub (hg x hx))).mpr fun k _ => by
      rw [iteratedDeriv_sub (hf x hx).contDiffAt (hg x hx).contDiffAt]; simp [iteratedDeriv_eq_iterate,h]
  exact (analyticOrderAt_eq_top.mp H).mono fun z hz => sub_eq_zero.mp hz

end AnalyticESC
