/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Notation

public import BergmanWeakType.Weighted.CompactIntegral
public import BergmanWeakType.Weighted.RadialFlux
public import Mathlib.MeasureTheory.Integral.CircleAverage

/-! # Differentiation of angular means and radial divergence -/

@[expose] public section

noncomputable section

open MeasureTheory Set Real
open scoped Topology

namespace BergmanWeakType.Weighted

def angularMean (F : ℝ → ℝ → ℝ) (r : ℝ) : ℝ :=
  (τ)⁻¹ * ∫ θ in (0 : ℝ)..τ, F r θ

theorem continuousOn_angularMean {F : ℝ → ℝ → ℝ} {S : Set ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ ↦ F p.1 p.2) (S ×ˢ univ)) :
    ContinuousOn (angularMean F) S := by
  have hc : Continuous (fun p : S × ℝ ↦ F p.1 p.2) := by
    apply continuousOn_univ.mp
    apply hF.comp (continuous_subtype_val.comp continuous_fst |>.prodMk continuous_snd).continuousOn
    exact fun p _ ↦ ⟨p.1.property, mem_univ _⟩
  rw [continuousOn_iff_continuous_domRestrict]
  exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    hc 0 (τ)).const_mul _

theorem hasDerivAt_angularMean {F Fr : ℝ → ℝ → ℝ} {r : ℝ} (hr : r ∈ Ioo01)
    (hF : OnStrip F)
    (hFr : OnStrip Fr)
    (hd : ∀ r ∈ Ioo01, ∀ θ, HasDerivAt (fun r ↦ F r θ) (Fr r θ) r) :
    HasDerivAt (angularMean F) (angularMean Fr r) r := by
  let S := Icc (r / 2) ((r + 1) / 2)
  have hS : S ∈ nhds r := Icc_mem_nhds (by linarith [hr.1]) (by linarith [hr.2])
  have hsub : S ×ˢ Icc (0 : ℝ) (τ) ⊆ Ico 0 1 ×ˢ univ := by
    rintro ⟨u, θ⟩ ⟨hu, _⟩
    exact ⟨⟨by dsimp [S] at hu; linarith [hu.1, hr.1],
      by dsimp [S] at hu; linarith [hu.2, hr.2]⟩, mem_univ _⟩
  have hi := hasDerivAt_integral_mul_of_continuousOn_compact
    (μ := volume.restrict (Icc (0 : ℝ) (τ))) isCompact_Icc
    (ae_restrict_mem measurableSet_Icc) (show IsCompact S from isCompact_Icc) hS
    (integrable_const (1 : ℝ)) (hF.mono hsub) (hFr.mono hsub) (fun θ _ u hu ↦
      hd u ⟨by dsimp [S] at hu; linarith [hu.1, hr.1],
        by dsimp [S] at hu; linarith [hu.2, hr.2]⟩ θ)
  unfold angularMean
  simpa only [mul_one, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le two_pi_pos.le] using hi.2.const_mul ((τ)⁻¹)

theorem intervalIntegrable_polar_slice {F : ℝ → ℝ → ℝ} {r : ℝ}
    (hF : OnStrip F)
    (hr : r ∈ Ico01) : IntervalIntegrable (F r) volume 0 (τ) := by
  apply Continuous.intervalIntegrable
  apply continuousOn_univ.mp
  apply hF.comp (continuous_const.prodMk continuous_id).continuousOn
  exact fun θ _ ↦ ⟨hr, mem_univ θ⟩

/-- Smoothness and periodicity data for a two-variable family on the radial strip. -/
structure PolarSmooth (F Fr Frr Ft Ftt : ℝ → ℝ → ℝ) : Prop where
  cont : OnStrip F
  contR : OnStrip Fr
  contRR : OnStrip Frr
  contT : OnStrip Ft
  contTT : OnStrip Ftt
  deriv : ∀ r ∈ Ioo01, ∀ θ, HasDerivAt (fun r ↦ F r θ) (Fr r θ) r
  derivR : ∀ r ∈ Ioo01, ∀ θ, HasDerivAt (fun r ↦ Fr r θ) (Frr r θ) r
  derivT : ∀ r ∈ Ioo01, ∀ θ, HasDerivAt (F r) (Ft r θ) θ
  derivTT : ∀ r ∈ Ioo01, ∀ θ, HasDerivAt (Ft r) (Ftt r θ) θ
  periodF : ∀ r ∈ Ioo01, F r (τ) = F r 0
  periodT : ∀ r ∈ Ioo01, Ft r (τ) = Ft r 0

/-- Smoothness data for a positive radial coefficient. -/
structure RadialSmooth (J Jr Jrr : ℝ → ℝ) : Prop where
  cont : ContinuousOn J (Ico 0 1)
  contR : ContinuousOn Jr (Ico 0 1)
  contRR : ContinuousOn Jrr (Ico 0 1)
  deriv : ∀ r ∈ Ioo01, HasDerivAt J (Jr r) r
  derivR : ∀ r ∈ Ioo01, HasDerivAt Jr (Jrr r) r
  pos : ∀ r ∈ Ico01, 0 < J r

/-- A polar divergence inequality with periodic angular derivative makes the angular mean
nonincreasing, including at the origin. -/
theorem antitoneOn_angularMean_of_polar_flux {F Fr Frr Ft Ftt : ℝ → ℝ → ℝ}
    {w w' : ℝ → ℝ} (h : PolarSmooth F Fr Frr Ft Ftt)
    (hw : ContinuousOn w (Ico 0 1))
    (hwd : ∀ r ∈ Ioo01, HasDerivAt w (w' r) r)
    (hwpos : ∀ r ∈ Ioo01, 0 < w r)
    (hineq : ∀ r ∈ Ioo01, ∀ θ,
      r * w r * Frr r θ + (w r + r * w' r) * Fr r θ + (w r / r) * Ftt r θ ≤ 0) :
    AntitoneOn (angularMean F) (Ico 0 1) := by
  apply antitoneOn_of_radial_flux (w := w)
    (F := fun r ↦ r * w r * angularMean Fr r)
    (F' := fun r ↦ (w r + r * w' r) * angularMean Fr r +
      r * w r * angularMean Frr r)
    (continuousOn_angularMean h.cont) (fun r hr ↦ hasDerivAt_angularMean hr h.cont h.contR h.deriv)
    hwpos ((continuousOn_id.mul hw).mul (continuousOn_angularMean h.contR)) (by simp)
  · intro r hr
    convert ((hasDerivAt_id r).mul (hwd r hr)).mul
      (hasDerivAt_angularMean hr h.contR h.contRR h.derivR) using 1 <;>
      simp only [one_mul, Pi.mul_def, id_eq]
  · intro r hr
    have hr' : r ∈ Ico01 := ⟨hr.1.le, hr.2⟩
    have hir := intervalIntegrable_polar_slice h.contR hr'
    have hirr := intervalIntegrable_polar_slice h.contRR hr'
    have hitt := intervalIntegrable_polar_slice h.contTT hr'
    have hz := integral_periodic_derivative_eq_zero two_pi_pos.le
      (fun θ _ ↦ h.derivTT r hr θ) hitt (h.periodT r hr)
    have hn := integral_radial_term_nonpos (c := w r / r) two_pi_pos.le
      ((hirr.const_mul (r * w r)).add (hir.const_mul (w r + r * w' r))) hitt hz
      (fun θ _ ↦ hineq r hr θ)
    rw [intervalIntegral.integral_add (hirr.const_mul _) (hir.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hn
    have hm := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr two_pi_pos.le) hn
    dsimp only [angularMean]
    nlinarith
  · exact fun _ _ ↦ rfl

theorem angularMean_smoothCap_bounds {F : ℝ → ℝ → ℝ} {r ε c : ℝ}
    (hε : 0 < ε) (hF : Continuous (F r)) :
    angularMean (fun r θ ↦ min (F r θ) c) r ≤
        angularMean (fun r θ ↦ smoothCap ε c (F r θ)) r ∧
      angularMean (fun r θ ↦ smoothCap ε c (F r θ)) r ≤
        angularMean (fun r θ ↦ min (F r θ) c) r + ε / 2 := by
  have hmin : Continuous (fun θ ↦ min (F r θ) c) := hF.inf continuous_const
  have hcap : Continuous (fun θ ↦ smoothCap ε c (F r θ)) := by
    unfold smoothCap
    fun_prop
  have hlow := intervalIntegral.integral_mono_on (μ := volume) two_pi_pos.le
    (hmin.intervalIntegrable _ _) (hcap.intervalIntegrable _ _)
    (fun θ _ ↦ min_le_smoothCap hε.le)
  have hupp := intervalIntegral.integral_mono_on (μ := volume) two_pi_pos.le
    (hcap.intervalIntegrable _ _) ((hmin.add continuous_const).intervalIntegrable _ _)
    (fun θ _ ↦ smoothCap_le_min_add)
  dsimp only [Pi.add_def] at hupp
  rw [intervalIntegral.integral_add (hmin.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hupp
  have hπ : τ ≠ 0 := two_pi_pos.ne'
  dsimp only [angularMean]
  constructor
  · exact mul_le_mul_of_nonneg_left hlow (inv_nonneg.mpr two_pi_pos.le)
  · have h := mul_le_mul_of_nonneg_left hupp (inv_nonneg.mpr two_pi_pos.le)
    rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hπ, one_mul] at h
    exact h

theorem antitoneOn_angularMean_min_of_smoothCap {F : ℝ → ℝ → ℝ} {c : ℝ}
    (hF : ∀ r ∈ Ico01, Continuous (F r))
    (hcap : ∀ ε, 0 < ε →
      AntitoneOn (angularMean (fun r θ ↦ smoothCap ε c (F r θ))) (Ico 0 1)) :
    AntitoneOn (angularMean (fun r θ ↦ min (F r θ) c)) (Ico 0 1) := by
  intro r hr R hR hrR
  apply le_of_forall_pos_le_add
  intro ε hε
  have hleft := (angularMean_smoothCap_bounds (c := c) hε (hF R hR)).1
  have hright := (angularMean_smoothCap_bounds (c := c) hε (hF r hr)).2
  have hm := hcap ε hε hr hR hrR
  linarith

end BergmanWeakType.Weighted
