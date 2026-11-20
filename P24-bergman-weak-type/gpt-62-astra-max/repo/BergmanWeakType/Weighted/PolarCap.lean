/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.PolarPotential
public import BergmanWeakType.Weighted.NormalizerRadial

/-! # Truncated angular means of polar supersolutions -/

@[expose] public section

noncomputable section

open MeasureTheory Set Real
open scoped Topology

namespace BergmanWeakType.Weighted

namespace Field

/-- The negative part of a polar subsolution still satisfies radial comparison.
Indeed, for a smooth increasing concave `g` with `g(0)=0`, the extra terms in
`L(g ∘ F)` are the concavity times a squared gradient, and the potential times
`g'(F)F - g(F)`, both nonpositive. Pass to `min x 0` through such `g`. -/
theorem min_comparison (A H : Field) (α c : ℝ)
    (L : ∀ r ∈ unitInterval, ∀ t, (A.eval r t).error (α+2) r ≤ 0)
    (Z : ∀ r ∈ unitInterval, ∀ t, (H.eval r t).error (α+2) r = 0) :
    AntitoneOn (fun r ↦ angularMean (fun r t ↦ min (A.val .v r t) (c*H.val .v r t)) r / normalizer α r) radii := by
  let F := A.subScaled H c
  let G ε r := angularMean (fun u t ↦ smoothCap ε (F.val .v u t) - (-c)*H.val .v u t) r / normalizer α r
  have smooth ε (he : 0 < ε) : AntitoneOn (G ε) radii := by
    apply ((F.comp (cap_jet he) (by unfold capDD; fun_prop (disch := intros; positivity))).subScaled H (-c)).mean_comparison α
    intro r hr t
    rw [error_subScaled, Z r hr t, mul_zero, sub_zero]
    have hf : (F.eval r t).error (α+2) r ≤ 0 := by grind [error_subScaled]
    obtain ⟨hd, hdd, hg⟩ := cap_signs he (F.val .v r t)
    have h₁ := mul_nonpos_of_nonneg_of_nonpos hd hf
    have h₂ := mul_nonpos_of_nonpos_of_nonneg hdd (show 0 ≤ F.val .r r t^2 + F.val .t r t^2/r^2 by positivity)
    have h₃ := mul_nonpos_of_nonneg_of_nonpos (div_nonneg (sq_nonneg (α+2)) (sub_nonneg.mpr (inner_sq hr).le)) (sub_nonpos.mpr hg)
    dsimp only [comp,Field.eval,Jet.map,Jet.error,rhs] at h₁ ⊢
    grind
  have lim r (hr : r ∈ radii) : Filter.Tendsto (fun ε ↦ G ε r) (𝓝[>] 0) (𝓝 (G 0 r)) := by
    have ct := F.slice_cont .v hr
    have ch := H.slice_cont .v hr
    have hc : Continuous (fun ε ↦ angularMean (fun _ t ↦ smoothCap ε (F.val .v r t) - (-c)*H.val .v r t) r) := by
      apply continuousOn_univ.mp (continuousOn_angularMean  ?_)
      change ContinuousOn (fun p : ℝ × ℝ ↦ smoothCap p.1 (F.val .v r p.2) - (-c)*H.val .v r p.2) _
      generalize F.val .v r = f at ct ⊢; generalize H.val .v r = g at ch ⊢
      unfold smoothCap; fun_prop
    exact (hc.div_const _).continuousWithinAt
  intro r hr R hR hrR
  simpa only [G,F,Field.val,Field.eval,subScaled,smoothCap_zero,neg_mul,sub_neg_eq_add,← min_add_add_right,sub_add_cancel,zero_add] using le_of_tendsto_of_tendsto (lim R hR) (lim r hr)
    (Filter.Eventually.mono self_mem_nhdsWithin (by aesop))

end Field
/-- Compare a potential with multiples of the exact boundary solution. -/
theorem normalized_cap_anti (s : PolarSource) [IsFiniteMeasure s] (α c : ℝ) :
    AntitoneOn (angularMean (fun r θ ↦ min (s.potential α (circleMap 0 r θ) / normalizer α r) c)) radii := by
  let q := -(α+2)/2
  have h := (s.field q).min_comparison (boundarySource.field q) α c
    (fun r hr t ↦ s.error_nonpos _ (inner_sq hr) hr.1.ne' t)
    (fun r hr t ↦ boundarySource.error_boundary _ (inner_sq hr) hr.1.ne' t ae_boundary_norm)
  simp only [q,polarIntegral_boundary_eq_normalizer] at h
  intro r hr R hR hle
  have pos x (hx : x ∈ radii) := normalizer_pos α hx
  simpa only [q,polarIntegral_boundary_eq_normalizer,PolarSource.value,angularMean, ← integral_div,
    ← min_div_div_right (pos r hr).le, ← min_div_div_right (pos R hR).le, mul_div_cancel_right₀ _ (pos r hr).ne',
    mul_div_cancel_right₀ _ (pos R hR).ne'] using h hr hR hle

end BergmanWeakType.Weighted
