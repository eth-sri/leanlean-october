/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.ShiftEquations.Strip.Representative
public import DOZZ.ShiftEquations.Shift.ShiftGluing
import DOZZ.Complex.Identity
/-! # Continuing real dual seeds and preserving common representatives -/
public section
open Filter Topology Set
namespace DOZZ.Proofs
/-- A real interval determines a meromorphic identity on its horizontal strip. -/
theorem dualFirstCase_continue_interval {F G : ℂ → ℂ} {H lo hi : ℝ}
    (hH : 0 < H) (hlohi : lo < hi)
    (hF : MeromorphicOn F (horizontalStrip H)) (hG : MeromorphicOn G (horizontalStrip H))
    (he : ∀ x : ℝ, lo < x → x < hi → F (x : ℂ) = G (x : ℂ)) :
    F =ᶠ[codiscreteWithin (horizontalStrip H)] G := by
  have hm : (((lo + hi) / 2 : ℝ) : ℂ) ∈ horizontalStrip H := by
    simpa only [horizontalStrip, mem_ofPred_eq, Complex.ofReal_im, abs_zero] using hH
  have hfreq := frequently_eq_of_real_interval ((lo + hi) / 2) ((hi - lo) / 4)
    (by positivity) F G (fun x hx => he x
      (by grind)
      (by grind))
  apply eventuallyEq_codiscreteWithin_iff_forall_eventually_nhdsNE.mpr
  intro z hz
  exact (ShiftGluing.meromorphicOn_eventuallyEq_of_frequently hF hG
    (convex_horizontalStrip H).isPreconnected hm hz hfreq).mono fun _ hw _ => hw
/-- Translations by real numbers preserve meromorphic strip germs. -/
theorem dualFirstCase_meromorphic_translate {F : ℂ → ℂ} {H : ℝ}
    (hF : MeromorphicOn F (horizontalStrip H)) (t : ℝ) :
    MeromorphicOn (fun z => F (z + (t : ℂ))) (horizontalStrip H) := by
  intro z hz
  exact (hF _ ((add_real_mem_horizontalStrip H z t).mpr hz)).comp_analyticAt (g := fun w : ℂ => w + t)
    (analyticAt_id.add analyticAt_const)
/-- Pulling a strip-codiscrete statement back by a real translation preserves its exceptions. -/
theorem dualFirstCase_codiscreteWithin_translate {p : ℂ → Prop} {H : ℝ}
    (hp : ∀ᶠ z in codiscreteWithin (horizontalStrip H), p z) (t : ℝ) :
    ∀ᶠ z in codiscreteWithin (horizontalStrip H), p (z + (t : ℂ)) := by
  apply eventually_codiscreteWithin_iff_forall_eventually_nhdsNE.mpr
  intro z hz
  have hl := eventually_codiscreteWithin_iff_forall_eventually_nhdsNE.mp hp
    (z + t) ((add_real_mem_horizontalStrip H z t).mpr hz)
  filter_upwards [ShiftGluing.eventually_comp_add t hl] with w hw hws
  simp_all
theorem dualFirstCase_common_representative (F R D A : ℂ → ℂ)
    (H b q : ℝ) (hH : 0 < H)
    (hF : MeromorphicOn F (horizontalStrip H)) (hR : MeromorphicOn R (horizontalStrip H))
    (hRD : R =ᶠ[codiscreteWithin (horizontalStrip H)] D)
    (hglue : ∀ᶠ z in codiscreteWithin (horizontalStrip H), F z = R z * F ((q : ℂ) - z))
    (hshift : ∀ᶠ z in codiscreteWithin (horizontalStrip H), F (z + b) = A z * F (z - b)) :
    ∃ C S : ℂ → ℂ,
      MeromorphicOn C (horizontalStrip (H / 2)) ∧
      MeromorphicOn S (horizontalStrip (H / 2)) ∧
      EqOn C F (horizontalStrip (H / 2)) ∧
      (∀ z : ℂ, z ∉ horizontalStrip (H / 2) → C z = 0) ∧ EqOn S R (horizontalStrip (H / 2)) ∧
      S =ᶠ[codiscrete ℂ] D ∧
      (∀ᶠ z in codiscrete ℂ, C z = S z * C ((q : ℂ) - z)) ∧
      ∀ᶠ z in codiscrete ℂ, C (z + b) = A z * C (z - b) := by
  classical
  let C := fun z : ℂ => if z ∈ horizontalStrip (H / 2) then F z else 0
  have hCF : EqOn C F (horizontalStrip (H / 2)) := fun z hz => by
    aesop
  let S := fun z => if z ∈ horizontalStrip (H / 2) then R z else D z
  have hRS : EqOn R S (horizontalStrip (H / 2)) := fun z hz => by
    aesop
  have hsub : horizontalStrip (H / 2) ⊆ horizontalStrip H :=
    fun _ hz => hz.trans (half_lt_self hH)
  have hclosure : closure (horizontalStrip (H / 2)) ⊆ horizontalStrip H := by
    have hc : IsClosed {z : ℂ | |z.im| ≤ H / 2} :=
      isClosed_le Complex.continuous_im.abs continuous_const
    have hcl := closure_minimal (fun z hz => (show |z.im| < H / 2 from hz).le) hc
    exact fun z hz => (hcl hz).trans_lt (half_lt_self hH)
  have hC :=
    (hF.mono_set hsub).congr hCF.symm (isOpen_horizontalStrip _)
  have hshiftg := codiscreteWithin_restrict_closure (isOpen_horizontalStrip H) hclosure hshift
  refine ⟨C, S, hC, (hR.mono_set hsub).congr hRS (isOpen_horizontalStrip _),
    hCF, (fun z hz => by aesop), hRS.symm, ?_, ?_, ?_⟩
  · filter_upwards [(codiscreteWithin_restrict_closure (isOpen_horizontalStrip H) hclosure hRD)] with z hz
    aesop
  · filter_upwards [(codiscreteWithin_restrict_closure (isOpen_horizontalStrip H) hclosure hglue)] with z hz
    have href : q - z ∈ horizontalStrip (H / 2) ↔ z ∈ horizontalStrip (H / 2) := by
      simp only [horizontalStrip, mem_ofPred_eq, Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg]
    aesop
  · filter_upwards [hshiftg] with z hz
    have hp := add_real_mem_horizontalStrip (H / 2) z b
    have hm : z - b ∈ horizontalStrip (H / 2) ↔ z ∈ horizontalStrip (H / 2) := by
      simpa only [sub_eq_add_neg, Complex.ofReal_neg] using add_real_mem_horizontalStrip _ z (-b)
    aesop
/-- Any additional homogeneous global shift survives the same zero extension. -/
theorem dualFirstCase_transfer_global_shift (F C A : ℂ → ℂ) (h b : ℝ)
    (hCF : EqOn C F (horizontalStrip h))
    (hCzero : ∀ z : ℂ, z ∉ horizontalStrip h → C z = 0)
    (hshift : ∀ᶠ z in codiscrete ℂ, F (z + (b : ℂ)) = A z * F (z - (b : ℂ))) :
    ∀ᶠ z in codiscrete ℂ, C (z + (b : ℂ)) = A z * C (z - (b : ℂ)) := by
  filter_upwards [hshift] with z hz
  have hp := add_real_mem_horizontalStrip h z b
  have hm : z - b ∈ horizontalStrip h ↔ z ∈ horizontalStrip h := by
    simpa only [sub_eq_add_neg, Complex.ofReal_neg] using add_real_mem_horizontalStrip h z (-b)
  grind
end DOZZ.Proofs
