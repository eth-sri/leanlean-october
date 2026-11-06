/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Hypergeom.ODE.ConnectionAnalyticContinuation
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Tactic

/-! Shared real-box identity theorem for the four Euler connection coefficients. -/
public section
open Set
namespace DOZZ.Proofs

/-- No integer lies strictly between zero and one. -/
theorem euler_ofReal_noninteger {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (x : ℂ) ∈ gaussConnectionIntegerRangeᶜ := by
  rintro ⟨n, hn⟩
  have hnR : (n : ℝ) = x :=
    Complex.ofReal_injective (by simpa only [Complex.ofReal_intCast] using hn)
  have h0 : (0 : ℤ) < n := by ring_nf at * <;> aesop
  have h1 : n < 1 := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
  omega

/-- Equality on a real interval determines analytic functions on a connected complex domain. -/
theorem analytic_eqOn_of_real_interval {f g : ℂ → ℂ} {S : Set ℂ} {lo x hi : ℝ}
    (hf : AnalyticOnNhd ℂ f S) (hg : AnalyticOnNhd ℂ g S)
    (hS : IsPreconnected S) (hx : (x : ℂ) ∈ S) (hlo : lo < x) (hhi : x < hi)
    (heq : ∀ y ∈ Ioo lo hi, f (y : ℂ) = g (y : ℂ)) : EqOn f g S := by
  have hacc  :=
    mem_closure_image Complex.continuous_ofReal.continuousAt
      (by rw [closure_Ioo hhi.ne]; exact ⟨le_rfl, hhi.le⟩)
  apply hf.eqOn_of_preconnected_of_mem_closure hg hS hx (closure_mono ?_ hacc)
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨heq y ⟨hlo.trans hy.1, hy.2⟩,
    fun h => hy.1.ne' (Complex.ofReal_injective h)⟩

/-- Successive one-variable identity theorems extend an Euler real box to a complex product.
The parameter domain depends only on the first two coordinates, so no restriction on the third
slice is needed beyond connectedness and analyticity. -/
theorem gaussConnection_eqOn_of_real_box
    {f g : ℂ × ℂ × ℂ → ℂ}
    (hf : ∀ p ∈ gaussConnectionParameterDomain, DifferentiableAt ℂ f p)
    (hg : ∀ p ∈ gaussConnectionParameterDomain, DifferentiableAt ℂ g p)
    {S T V : Set ℂ} {cl ch dl dh al ah c₀ δ₀ a₀ : ℝ}
    (hSo : IsOpen S) (hTo : IsOpen T) (hVo : IsOpen V)
    (hSc : IsPreconnected S) (hTc : IsPreconnected T) (hVc : IsPreconnected V)
    (hSI : S ⊆ gaussConnectionIntegerRangeᶜ) (hTI : T ⊆ gaussConnectionIntegerRangeᶜ)
    (hSR : ∀ {x : ℝ}, x ∈ Ioo cl ch → (x : ℂ) ∈ S)
    (hTR : ∀ {x : ℝ}, x ∈ Ioo dl dh → (x : ℂ) ∈ T)
    (hVR : ∀ {x : ℝ}, x ∈ Ioo al ah → (x : ℂ) ∈ V)
    (hc₀ : c₀ ∈ Ioo cl ch) (hδ₀ : δ₀ ∈ Ioo dl dh) (ha₀ : a₀ ∈ Ioo al ah)
    (heq : ∀ c ∈ Ioo cl ch, ∀ δ ∈ Ioo dl dh, ∀ a ∈ Ioo al ah,
      f (gaussConnectionCoordinates (c : ℂ) (δ : ℂ) (a : ℂ)) =
        g (gaussConnectionCoordinates (c : ℂ) (δ : ℂ) (a : ℂ))) :
    ∀ c ∈ S, ∀ δ ∈ T, ∀ a ∈ V,
      f (gaussConnectionCoordinates c δ a) = g (gaussConnectionCoordinates c δ a) := by
  obtain ⟨hfC, hfD, hfA⟩ := analytic_gaussConnection_slices hf hSo hTo hVo hSI hTI
  obtain ⟨hgC, hgD, hgA⟩ := analytic_gaussConnection_slices hg hSo hTo hVo hSI hTI
  have heqC (δ : ℝ) (hδ : δ ∈ Ioo dl dh) (a : ℝ) (ha : a ∈ Ioo al ah) :=
    analytic_eqOn_of_real_interval (hfC δ a (hTR hδ)) (hgC δ a (hTR hδ))
      hSc (hSR hc₀) hc₀.1 hc₀.2 (fun c hc => heq c hc δ hδ a ha)
  have heqD (c : ℂ) (hc : c ∈ S) (a : ℝ) (ha : a ∈ Ioo al ah) :=
    analytic_eqOn_of_real_interval (hfD c a hc) (hgD c a hc)
      hTc (hTR hδ₀) hδ₀.1 hδ₀.2 (fun δ hδ => heqC δ hδ a ha hc)
  intro c hc δ hδ a ha
  exact analytic_eqOn_of_real_interval (hfA c δ hc hδ) (hgA c δ hc hδ)
    hVc (hVR ha₀) ha₀.1 ha₀.2 (fun a ha => heqD c hc a ha hδ) ha

end DOZZ.Proofs
