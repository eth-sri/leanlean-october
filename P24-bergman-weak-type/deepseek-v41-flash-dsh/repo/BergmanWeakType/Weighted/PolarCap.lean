/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Notation

public import BergmanWeakType.Weighted.AngularMean

/-! # Truncated angular means of polar supersolutions -/

@[expose] public section

noncomputable section

open MeasureTheory Set Real

namespace BergmanWeakType.Weighted

/-- Truncations of a regular periodic polar supersolution have decreasing angular means. -/
theorem antitoneOn_angularMean_min_of_polar_flux {F Fr Frr Ft Ftt : ℝ → ℝ → ℝ}
    {w w' : ℝ → ℝ} (c : ℝ) (h : PolarSmooth F Fr Frr Ft Ftt)
    (hw : ContinuousOn w (Ico 0 1))
    (hwd : ∀ r ∈ Ioo01, HasDerivAt w (w' r) r)
    (hwpos : ∀ r ∈ Ioo01, 0 < w r)
    (hineq : ∀ r ∈ Ioo01, ∀ θ,
      r * w r * Frr r θ + (w r + r * w' r) * Fr r θ + (w r / r) * Ftt r θ ≤ 0) :
    AntitoneOn (angularMean (fun r θ ↦ min (F r θ) c)) (Ico 0 1) := by
  apply antitoneOn_angularMean_min_of_smoothCap
  · intro r hr
    apply continuousOn_univ.mp
    apply h.cont.comp (continuous_const.prodMk continuous_id).continuousOn
    exact fun θ _ ↦ ⟨hr, mem_univ θ⟩
  intro ε hε
  let d₁ := smoothCapInputDeriv ε c
  let d₂ := fun u ↦ -(ε ^ 2) / (2 * sqrt ((u - c) ^ 2 + ε ^ 2) ^ 3)
  have hd₁ : Continuous d₁ := continuous_iff_continuousAt.mpr
    (fun _ ↦ (hasDerivAt_smoothCapInputDeriv hε).continuousAt)
  have hd₂ : Continuous d₂ := by
    dsimp [d₂]
    apply Continuous.div continuous_const (by fun_prop)
    intro u
    have hp : 0 < (u - c) ^ 2 + ε ^ 2 := by positivity
    exact (mul_pos (by norm_num) (pow_pos (sqrt_pos.mpr hp) _)).ne'
  have hcap : Continuous (smoothCap ε c) := continuous_iff_continuousAt.mpr
    (fun _ ↦ (hasDerivAt_smoothCap_input hε).continuousAt)
  refine antitoneOn_angularMean_of_polar_flux
    (Fr := fun r θ ↦ d₁ (F r θ) * Fr r θ)
    (Frr := fun r θ ↦ d₂ (F r θ) * (Fr r θ) ^ 2 + d₁ (F r θ) * Frr r θ)
    (Ft := fun r θ ↦ d₁ (F r θ) * Ft r θ)
    (Ftt := fun r θ ↦ d₂ (F r θ) * (Ft r θ) ^ 2 + d₁ (F r θ) * Ftt r θ)
    (w := w) (w' := w') ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ hw hwd hwpos ?_
  · exact hcap.comp_continuousOn h.cont
  · exact (hd₁.comp_continuousOn h.cont).mul h.contR
  · exact ((hd₂.comp_continuousOn h.cont).mul (h.contR.pow 2)).add
      ((hd₁.comp_continuousOn h.cont).mul h.contRR)
  · exact (hd₁.comp_continuousOn h.cont).mul h.contT
  · exact ((hd₂.comp_continuousOn h.cont).mul (h.contT.pow 2)).add
      ((hd₁.comp_continuousOn h.cont).mul h.contTT)
  · intro r hr θ
    exact (hasDerivAt_smoothCap_input hε).comp r (h.deriv r hr θ)
  · intro r hr θ
    exact hasDerivAt_smoothCap_comp_first hε (h.deriv r hr θ) (h.derivR r hr θ)
  · intro r hr θ
    exact (hasDerivAt_smoothCap_input hε).comp θ (h.derivT r hr θ)
  · intro r hr θ
    exact hasDerivAt_smoothCap_comp_first hε (h.derivT r hr θ) (h.derivTT r hr θ)
  · intro r hr
    rw [h.periodF r hr]
  · intro r hr
    rw [h.periodF r hr, h.periodT r hr]
  · intro r hr θ
    exact smoothCap_polar_flux_nonpos hε hr.1 (hwpos r hr) (hineq r hr θ)

end BergmanWeakType.Weighted
