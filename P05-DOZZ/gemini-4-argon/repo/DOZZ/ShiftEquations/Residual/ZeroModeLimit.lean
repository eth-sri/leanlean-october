/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DozzFormula
public import DOZZ.Statements.Defs.IsUpsilon
public import DOZZ.Statements.Defs.SExp
import DOZZ.DOZZAlgebra.GenericLocus
import DOZZ.Upsilon.Uniqueness
import DOZZ.Upsilon.ZeroStructure
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The zero-mode limit of the DOZZ formula

As `α₁ → 2Q - α₂ - α₃` (so `s = (Σαᵢ - 2Q)/γ → 0`), the product `μ^s Γ(s)⁻¹ D(α₁, α₂, α₃)`
converges to `2/γ`: the simple zero of `Υ` at `0` in the denominator cancels the simple pole of
`Γ(s)`, the reflection `Υ(Q - x) = Υ(x)` cancels the remaining charge factors, and the
exponentials `μ^s B^(-s)` and `Γ(s + 1)⁻¹` tend to `1`.

The proof splits into four elementary limits (`cpow` at exponent `0`, `Γ` at `1`, the slope of
the entire function `Υ` at its zero `0`, and the ratio of the six non-singular `Υ`-values), a
pure-algebra rewrite of the product on the punctured neighbourhood, and the assembly.
-/

@[expose] public section

open Filter Topology

namespace DOZZ.Proofs


/-- A complex power with fixed nonzero base tends to `1` as the exponent tends to `0`. -/
theorem zeroMode_tendsto_cpow {ι : Type*} {l : Filter ι} {a : ℂ} (ha : a ≠ 0) {s : ι → ℂ}
    (hs : Tendsto s l (𝓝 0)) : Tendsto (fun i => a ^ s i) l (𝓝 1) := by
  simpa [Function.comp_def] using ((continuousAt_const_cpow (a := a) (b := 0) ha).tendsto.comp hs)

/-- `Γ(s + 1)⁻¹ → 1` as `s → 0`, since `Γ` is continuous at `1` with `Γ(1) = 1`. -/
theorem zeroMode_tendsto_inv_gamma {ι : Type*} {l} {s : ι → ℂ}
    (hs : Tendsto s l (𝓝 0)) : Tendsto (fun i => (Complex.Gamma (s i + 1))⁻¹) l (𝓝 1) := by
  have h2 := Complex.continuousAt_Gamma_one.tendsto.comp (by simpa using hs.add_const 1)
  rw [Complex.Gamma_one] at h2
  simpa [Function.comp_def] using h2.inv₀ one_ne_zero


/-- The slope limit along the shifted variable `w = (t - t₀) / 2`, as `t → t₀` with `t ≠ t₀`. -/
theorem zeroMode_tendsto_slope_comp {U} (hU : Differentiable ℂ U) (h0 : U 0 = 0)
    t₀ :
    Tendsto (fun t : ℝ => U (((t - t₀) / 2 : ℝ) : ℂ) / (((t - t₀) / 2 : ℝ) : ℂ))
      (𝓝[≠] t₀) (𝓝 (deriv U 0)) := by
  have zeroMode_tendsto_slope : Tendsto (fun x : ℝ => U (x : ℂ) / (x : ℂ)) (𝓝[≠] 0) (𝓝 (deriv U 0)) := by
    refine (show HasDerivAt (fun x : ℝ => U (x : ℂ)) (deriv U 0) 0 by exact HasDerivAt.comp_ofReal (z := 0) (by simpa using ((hU 0).hasDerivAt))).tendsto_slope_zero.congr (fun x => ?_)
    simp [h0, Complex.real_smul, div_eq_inv_mul]
  refine (zeroMode_tendsto_slope).comp ?_
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have hc : Continuous (fun t => (t - t₀) / 2) := by fun_prop
    have h := hc.tendsto t₀
    rw [sub_self, zero_div] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simpa using (sub_ne_zero.mpr ht)

/-- `Υ` does not vanish at a real point of the open strip `0 < x < Q`. -/
theorem zeroMode_ne_zero {γ} {U} (hU : IsUpsilon γ U) {x : ℝ} (hx : 0 < x)
    (hx' : x < Q γ) : U (x : ℂ) ≠ 0 := by
  rw [hU.2 (x : ℂ) (by simpa using hx) (by simpa using hx')]
  exact Complex.exp_ne_zero _

/-- `Υ` vanishes at `0`: the lattice point `m = n = 0`. -/
theorem zeroMode_zero {γ} {U} (hγ : 0 < γ) (hγ2 : γ < 2) (hU : IsUpsilon γ U) :
    U 0 = 0 := by
  rw [IsUpsilon.eq_zero_iff hγ hγ2 hU]
  exact ⟨0, 0, Or.inl (by simp)⟩


/-- **The bracket of non-singular `Υ`-values tends to `1`.** At `t = t₀` (where
`t₀ + α₂ + α₃ = 2Q`) the half-sum is `Q`, so the denominator is `Υ(Q - t₀) Υ(Q - α₂) Υ(Q - α₃)
= Υ(t₀) Υ(α₂) Υ(α₃)` by reflection, which equals the (nonzero) numerator. -/
theorem zeroMode_bracket_limit {γ} {U} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hU : IsUpsilon γ U) {α₂ α₃ t₀} (ht₀ : t₀ + α₂ + α₃ = 2 * Q γ) (h₁ : 0 < t₀)
    (h₁' : t₀ < Q γ) (h₂ : 0 < α₂) (h₂' : α₂ < Q γ) (h₃ : 0 < α₃) (h₃' : α₃ < Q γ) :
    Tendsto (fun t : ℝ => U t * U α₂ * U α₃ /
        (U (((t : ℂ) + α₂ + α₃) / 2 - t) * U (((t : ℂ) + α₂ + α₃) / 2 - α₂) *
          U (((t : ℂ) + α₂ + α₃) / 2 - α₃))) (𝓝[≠] t₀) (𝓝 1) := by
  have := hU.1.continuous
  have hhalf : ((t₀ : ℂ) + α₂ + α₃) / 2 = (Q γ : ℂ) := by
    rw [(show ((t₀ : ℂ) + α₂ + α₃) = ((t₀ + α₂ + α₃ : ℝ) : ℂ) by push_cast; ring), ht₀]
    push_cast
    ring
  have hDt₀ : U (((t₀ : ℂ) + α₂ + α₃) / 2 - t₀) * U (((t₀ : ℂ) + α₂ + α₃) / 2 - α₂) *
      U (((t₀ : ℂ) + α₂ + α₃) / 2 - α₃) = U t₀ * U α₂ * U α₃ := by
    rw [hhalf, IsUpsilon.reflect hγ hγ2 hU, IsUpsilon.reflect hγ hγ2 hU,
      IsUpsilon.reflect hγ hγ2 hU]
  have hne : U t₀ * U α₂ * U α₃ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (zeroMode_ne_zero hU h₁ h₁') (zeroMode_ne_zero hU h₂ h₂'))
      (zeroMode_ne_zero hU h₃ h₃')
  have hlim := ((show Continuous (fun t : ℝ => U t * U α₂ * U α₃) by fun_prop).tendsto t₀).div ((show Continuous (fun t : ℝ => U (((t : ℂ) + α₂ + α₃) / 2 - t) * U (((t : ℂ) + α₂ + α₃) / 2 - α₂) * U (((t : ℂ) + α₂ + α₃) / 2 - α₃)) by fun_prop).tendsto t₀) (by rw [hDt₀]; exact hne)
  rw [hDt₀, div_self hne] at hlim
  exact hlim.mono_left nhdsWithin_le_nhds


/-- The zero-mode limit with the critical value presented as a free `t₀` satisfying
`t₀ + α₂ + α₃ = 2Q`. -/
theorem zeroMode_limit_aux {γ μ : ℝ} {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hU : IsUpsilon γ U) {α₂ α₃ t₀ : ℝ} (ht₀ : t₀ + α₂ + α₃ = 2 * Q γ) (h₁ : 0 < t₀)
    (h₁' : t₀ < Q γ) (h₂ : 0 < α₂) (h₂' : α₂ < Q γ) (h₃ : 0 < α₃) (h₃' : α₃ < Q γ) :
    Tendsto (fun t : ℝ => ((μ : ℂ) ^ (sExp γ t α₂ α₃ : ℂ) / Complex.Gamma (sExp γ t α₂ α₃)) *
        dozzFormula γ μ U t α₂ α₃) (𝓝[≠] t₀) (𝓝 (2 / γ)) := by
  have zeroMode_formula_eq {μ : ℝ} {U : ℂ → ℂ} {t : ℝ} (ht : t ≠ t₀) : ((μ : ℂ) ^ (sExp γ t α₂ α₃ : ℂ) / Complex.Gamma (sExp γ t α₂ α₃)) * dozzFormula γ μ U t α₂ α₃ = ((μ : ℂ) ^ (sExp γ t α₂ α₃ : ℂ) * ((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ) : ℂ) ^ (-(sExp γ t α₂ α₃ : ℂ))) * (Complex.Gamma ((sExp γ t α₂ α₃ : ℂ) + 1))⁻¹ * (2 / (γ : ℂ)) * (deriv U 0 / (U (((t - t₀) / 2 : ℝ) : ℂ) / (((t - t₀) / 2 : ℝ) : ℂ))) * (U t * U α₂ * U α₃ / (U (((t : ℂ) + α₂ + α₃) / 2 - t) * U (((t : ℂ) + α₂ + α₃) / 2 - α₂) * U (((t : ℂ) + α₂ + α₃) / 2 - α₃))) := by
    have zeroMode_algebra {m : ℂ} {b : ℂ} {G : ℂ} {G₁ : ℂ} {s : ℂ} {g : ℂ} {D₀ : ℂ} {u₁ : ℂ} {u₂ : ℂ} {u₃ : ℂ} {v₀ : ℂ} {v₁ : ℂ} {v₂ : ℂ} {v₃ : ℂ} {w : ℂ} {q : ℂ} (hG : G₁ = s * G) (hv : v₀ = w * q) (hw : w = g * s / 2) : m / G * (b * (D₀ * u₁ * u₂ * u₃) / (v₀ * v₁ * v₂ * v₃)) = m * b * G₁⁻¹ * (2 / g) * (D₀ / q) * (u₁ * u₂ * u₃ / (v₁ * v₂ * v₃)) := by
      subst hG hv hw
      ring
    have := Complex.ofReal_ne_zero.mpr hγ.ne'
    have hQ : (2 * (Q γ : ℂ)) = (t₀ : ℂ) + α₂ + α₃ := by
      have h := congrArg (fun x : ℝ => (x : ℂ)) ht₀
      push_cast at h
      exact h.symm
    have hs : sExp γ t α₂ α₃ = (t - t₀) / γ := by
      unfold sExp
      congr 1
      linarith
    have hexp : (2 * (Q γ : ℂ) - ((t : ℂ) + α₂ + α₃)) / (γ : ℂ) = -(sExp γ t α₂ α₃ : ℂ) := by
      rw [hs]
      push_cast
      rw [hQ]
      ring
    have hv : U (((t : ℂ) + α₂ + α₃ - 2 * (Q γ : ℂ)) / 2) =
        (((t - t₀) / 2 : ℝ) : ℂ) *
          (U (((t - t₀) / 2 : ℝ) : ℂ) / (((t - t₀) / 2 : ℝ) : ℂ)) := by
      rw [mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (div_ne_zero (sub_ne_zero.mpr ht) two_ne_zero))]
      congr 1
      push_cast
      rw [hQ]
      ring
    unfold dozzFormula
    rw [hexp]
    exact zeroMode_algebra (Complex.Gamma_add_one _ (by rw [hs]; exact Complex.ofReal_ne_zero.mpr (div_ne_zero (sub_ne_zero.mpr ht) hγ.ne'))) hv (by rw [hs]; push_cast; field_simp)
  have zeroMode_deriv_ne_zero : deriv U 0 ≠ 0 := by
    rw [IsUpsilon.deriv_zero hγ hγ2 hU]
    have : 0 < 2 / γ := by positivity
    simpa using (zeroMode_ne_zero hU (x := γ / 2) (by positivity) (by unfold Q; linarith))
  have hD := zeroMode_deriv_ne_zero
  have hs : Tendsto (fun t : ℝ => (sExp γ t α₂ α₃ : ℂ)) (𝓝[≠] t₀) (𝓝 0) := by
    have h0 : sExp γ t₀ α₂ α₃ = 0 := by
      unfold sExp
      rw [ht₀]
      simp
    have h := (show Continuous (fun t : ℝ => (sExp γ t α₂ α₃ : ℂ)) by unfold sExp; fun_prop).tendsto t₀
    rw [h0, Complex.ofReal_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hmain := ((((show Tendsto (fun t : ℝ => (μ : ℂ) ^ (sExp γ t α₂ α₃ : ℂ) * ((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ) : ℂ) ^ (-(sExp γ t α₂ α₃ : ℂ))) (𝓝[≠] t₀) (𝓝 1) by simpa using (zeroMode_tendsto_cpow (Complex.ofReal_ne_zero.mpr hμ.ne') hs).mul (zeroMode_tendsto_cpow (show ((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ) : ℂ) ≠ 0 by apply Complex.ofReal_ne_zero.mpr; exact (mul_pos (dozzBase_pos hγ hγ2 hμ) (Real.rpow_pos_of_pos (by positivity) _)).ne') (by simpa using hs.neg))).mul (zeroMode_tendsto_inv_gamma hs)).mul (tendsto_const_nhds (x := (2 / (γ : ℂ))))).mul
    ((tendsto_const_nhds (x := deriv U 0)).div (zeroMode_tendsto_slope_comp hU.1 (zeroMode_zero hγ hγ2 hU) t₀) hD)).mul (zeroMode_bracket_limit hγ hγ2 hU ht₀ h₁ h₁' h₂ h₂' h₃ h₃')
  rw [div_self hD] at hmain
  simp only [one_mul, mul_one] at hmain
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (zeroMode_formula_eq ht).symm

/-- **The DOZZ companion at the zero mode.** As `α₁ → 2Q - α₂ - α₃` (so `s → 0`),
`μ^s Γ(s)⁻¹ D(α₁, α₂, α₃) → 2/γ`: the zero of `Υ` at `0` in the denominator cancels the pole of
`Γ(s)`, and `Υ(Q - x) = Υ(x)` cancels the remaining charge factors. -/
theorem dozzFormula_zeroMode_limit {γ μ : ℝ} {U} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hU : IsUpsilon γ U) {α₂ α₃ : ℝ} (h₂ : 0 < α₂) (h₂' : α₂ < Q γ) (h₃ : 0 < α₃)
    (h₃' : α₃ < Q γ) (h₁ : 0 < 2 * Q γ - α₂ - α₃) (h₁' : 2 * Q γ - α₂ - α₃ < Q γ) :
    Tendsto (fun t : ℝ => ((μ : ℂ) ^ (sExp γ t α₂ α₃ : ℂ) / Complex.Gamma (sExp γ t α₂ α₃)) *
        dozzFormula γ μ U t α₂ α₃) (𝓝[≠] (2 * Q γ - α₂ - α₃)) (𝓝 (2 / γ)) :=
  zeroMode_limit_aux hγ hγ2 hμ hU (t₀ := 2 * Q γ - α₂ - α₃) (by ring) h₁ h₁' h₂ h₂' h₃ h₃'

end DOZZ.Proofs

end
