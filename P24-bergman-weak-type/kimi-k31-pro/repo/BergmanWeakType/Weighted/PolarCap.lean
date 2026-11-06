/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.AngularMean

/-! # Truncated angular means of polar supersolutions -/

@[expose] public section

noncomputable section

open MeasureTheory Set Real

namespace BergmanWeakType.Weighted

/-- Truncations of a regular periodic polar supersolution have decreasing angular means. -/
theorem antitoneOn_angularMean_min_of_polar_flux {F Fr Frr Ft Ftt : ℝ → ℝ → ℝ}
    {w w' : ℝ → ℝ} (c : ℝ)
    (hF : ContinuousOn (fun p : ℝ × ℝ ↦ F p.1 p.2) (Ico 0 1 ×ˢ univ))
    (hFr : ContinuousOn (fun p : ℝ × ℝ ↦ Fr p.1 p.2) (Ico 0 1 ×ˢ univ))
    (hFrr : ContinuousOn (fun p : ℝ × ℝ ↦ Frr p.1 p.2) (Ico 0 1 ×ˢ univ))
    (hFt : ContinuousOn (fun p : ℝ × ℝ ↦ Ft p.1 p.2) (Ico 0 1 ×ˢ univ))
    (hFtt : ContinuousOn (fun p : ℝ × ℝ ↦ Ftt p.1 p.2) (Ico 0 1 ×ˢ univ))
    (hFd : ∀ r ∈ Ioo (0 : ℝ) 1, ∀ θ, HasDerivAt (fun r ↦ F r θ) (Fr r θ) r)
    (hFrd : ∀ r ∈ Ioo (0 : ℝ) 1, ∀ θ, HasDerivAt (fun r ↦ Fr r θ) (Frr r θ) r)
    (hFdt : ∀ r ∈ Ioo (0 : ℝ) 1, ∀ θ, HasDerivAt (F r) (Ft r θ) θ)
    (hFtd : ∀ r ∈ Ioo (0 : ℝ) 1, ∀ θ, HasDerivAt (Ft r) (Ftt r θ) θ)
    (hperiodF : ∀ r ∈ Ioo (0 : ℝ) 1, F r (2 * π) = F r 0)
    (hperiodFt : ∀ r ∈ Ioo (0 : ℝ) 1, Ft r (2 * π) = Ft r 0)
    (hw : ContinuousOn w (Ico 0 1))
    (hwd : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt w (w' r) r)
    (hwpos : ∀ r ∈ Ioo (0 : ℝ) 1, 0 < w r)
    (hineq : ∀ r ∈ Ioo (0 : ℝ) 1, ∀ θ,
      r * w r * Frr r θ + (w r + r * w' r) * Fr r θ + (w r / r) * Ftt r θ ≤ 0) :
    AntitoneOn (angularMean (fun r θ ↦ min (F r θ) c)) (Ico 0 1) := by
  apply antitoneOn_angularMean_min_of_smoothCap
  · intro r hr
    apply continuousOn_univ.mp
    apply hF.comp (continuous_const.prodMk continuous_id).continuousOn
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
  apply antitoneOn_angularMean_of_polar_flux
    (Fr := fun r θ ↦ d₁ (F r θ) * Fr r θ)
    (Frr := fun r θ ↦ d₂ (F r θ) * (Fr r θ) ^ 2 + d₁ (F r θ) * Frr r θ)
    (Ft := fun r θ ↦ d₁ (F r θ) * Ft r θ)
    (Ftt := fun r θ ↦ d₂ (F r θ) * (Ft r θ) ^ 2 + d₁ (F r θ) * Ftt r θ)
    (w := w) (w' := w')
  · exact hcap.comp_continuousOn hF
  · exact (hd₁.comp_continuousOn hF).mul hFr
  · exact ((hd₂.comp_continuousOn hF).mul (hFr.pow 2)).add
      ((hd₁.comp_continuousOn hF).mul hFrr)
  · exact ((hd₂.comp_continuousOn hF).mul (hFt.pow 2)).add
      ((hd₁.comp_continuousOn hF).mul hFtt)
  · intro r hr θ
    exact (hasDerivAt_smoothCap_input hε).comp r (hFd r hr θ)
  · intro r hr θ
    exact hasDerivAt_smoothCap_comp_first hε (hFd r hr θ) (hFrd r hr θ)
  · intro r hr θ
    exact hasDerivAt_smoothCap_comp_first hε (hFdt r hr θ) (hFtd r hr θ)
  · intro r hr
    rw [hperiodF r hr, hperiodFt r hr]
  · exact hw
  · exact hwd
  · exact hwpos
  · intro r hr θ
    have hd₁ := (smoothCapInputDeriv_mem_Icc (c := c) (x := F r θ) hε).1
    have hd₂ := smoothCap_secondDeriv_nonpos (ε := ε) (c := c) (x := F r θ)
    have hfirst := mul_nonpos_of_nonneg_of_nonpos hd₁ (hineq r hr θ)
    have hsecond := mul_nonpos_of_nonpos_of_nonneg hd₂
      (show 0 ≤ r * w r * (Fr r θ) ^ 2 + (w r / r) * (Ft r θ) ^ 2 by
        exact add_nonneg (mul_nonneg (mul_nonneg hr.1.le (hwpos r hr).le) (sq_nonneg _))
          (mul_nonneg (div_nonneg (hwpos r hr).le hr.1.le) (sq_nonneg _)))
    nlinarith

end BergmanWeakType.Weighted
