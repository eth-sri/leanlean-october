/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Strip.Representative

/-! The inversion representative: a global representative of an inversion germ with prescribed
physical values. The inversion germ is an explicit input; this module does not assert its
construction. -/

@[expose] public section
open Filter Topology Set
namespace DOZZ.Proofs

/-- Reflection about a real point preserves globally codiscrete properties. -/
theorem codiscrete_reflect {p : ℂ → Prop}
    (hp : ∀ᶠ z in codiscrete ℂ, p z) (q : ℝ) :
    ∀ᶠ z in codiscrete ℂ, p ((q : ℂ) - z) := by
  let e : ℂ ≃ₜ ℂ :=
    { toFun := fun z => q - z
      invFun := fun z => q - z
      left_inv := fun z => sub_sub_cancel ..
      right_inv := fun z => sub_sub_cancel ..
      continuous_toFun := continuous_const.sub continuous_id
      continuous_invFun := continuous_const.sub continuous_id }
  apply eventually_codiscrete_iff_forall_eventually_nhdsNE.mpr
  intro z
  have ht : Tendsto e (𝓝[≠] z) (𝓝[≠] (e z)) := by
    rw [Tendsto, e.map_punctured_nhds_eq]
  exact ht.eventually (eventually_codiscrete_iff_forall_eventually_nhdsNE.mp hp (e z))

/-- An inversion germ admits a global representative with prescribed physical values.
Outside the smaller strip both factors are one. The smaller strip also makes all
physical-value corrections globally codiscrete. -/
theorem exists_physical_inversion_representative
    (F : ℂ → ℂ) (v : ℝ → ℂ) (q H h lo hi : ℝ)
    (hh : 0 < h) (hhH : h < H)
    (hF : MeromorphicOn F (horizontalStrip H))
    (hinv : ∀ᶠ z in codiscreteWithin (horizontalStrip H),
      F z * F ((q : ℂ) - z) = 1)
    (hphysical : ∀ᶠ z in codiscreteWithin (horizontalStrip H),
      z.im = 0 → lo < z.re → z.re < hi → F z = v z.re) :
    ∃ R : ℂ → ℂ, MeromorphicOn R (horizontalStrip h) ∧
      (∀ α : ℝ, lo < α → α < hi → R (α : ℂ) = v α) ∧
      ∀ᶠ z in codiscrete ℂ, R z * R ((q : ℂ) - z) = 1 := by
  classical
  have hclosure : closure (horizontalStrip h) ⊆ horizontalStrip H := by
    have hc : IsClosed {z : ℂ | |z.im| ≤ h} :=
      isClosed_le Complex.continuous_im.abs continuous_const
    have hcl := closure_minimal
      (show horizontalStrip h ⊆ {z : ℂ | |z.im| ≤ h} from
        fun z hz => (show |z.im| < h from hz).le) hc
    exact fun z hz => (hcl hz).trans_lt hhH
  let R₀ : ℂ → ℂ := fun z => if z ∈ horizontalStrip h then F z else 1
  let R : ℂ → ℂ := fun z =>
    if z.im = 0 ∧ lo < z.re ∧ z.re < hi then v z.re else R₀ z
  have hreal (z : ℂ) (hz : z.im = 0) : z ∈ horizontalStrip h := by
    simpa only [horizontalStrip, mem_ofPred_eq, hz, abs_zero] using hh
  have hp := codiscreteWithin_restrict_closure
    (isOpen_horizontalStrip H) hclosure hphysical
  have heq : R₀ =ᶠ[codiscrete ℂ] R := by
    filter_upwards [hp] with z hz
    aesop
  have hm : MeromorphicOn R₀ (horizontalStrip h) := by
    apply (show MeromorphicOn F (horizontalStrip h) from
      fun z hz => hF z (hz.trans hhH)).congr _ (isOpen_horizontalStrip h)
    intro z hz
    simp only [R₀, ite_eq_left hz]
  refine ⟨R, hm.congr_codiscreteWithin
    (heq.filter_mono ((codiscreteWithin_le_codiscrete_inf_principal _).trans inf_le_left))
    (isOpen_horizontalStrip h), ?_, ?_⟩
  · aesop
  · have hg := codiscreteWithin_restrict_closure
      (isOpen_horizontalStrip H) hclosure hinv
    filter_upwards [hg, heq, codiscrete_reflect heq q] with z hz he he'
    rw [← he, ← he']
    have href : q - z ∈ horizontalStrip h ↔ z ∈ horizontalStrip h := by
      simp only [horizontalStrip, mem_ofPred_eq, Complex.sub_im, Complex.ofReal_im,
        zero_sub, abs_neg]
    grind

end DOZZ.Proofs
