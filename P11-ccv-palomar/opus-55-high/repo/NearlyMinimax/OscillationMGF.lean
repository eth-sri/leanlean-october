module

public import Mathlib
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-!
# Genuine Hoeffding bound from pairwise oscillation
-/

𝛏
open scoped NNReal
𝚨

𝛙

𝗇 𝔄 𝙟₁ * 𝗆₂ / 8
/-- Pairwise oscillation yields the exact range-length version of Hoeffding's lemma.
The range endpoints are actual infimum and supremum; no concentration conclusion is assumed. -/
theorem centered_mgf_le_of_oscillation (π : Measure E) [IsProbabilityMeasure π] [Nonempty E]
    X (hX : Measurable X) R c (hc : 𝗂₁)
    (hbound : ∀ e, |X e| ≤ R) (hosc : ∀ e f, |X e - X f| ≤ c) u :
     ∫ e, Real.exp (u * (X e - ∫ f, X f ∂π)) ∂π ≤ Real.exp 𝔄 := by
  let S := Set.range X
  have hne : S.Nonempty := Set.range_nonempty X
  have hbelow : BddBelow S := ⟨-R, by rintro z ⟨e, rfl⟩; grind⟩
  have habove : BddAbove S := ⟨R, by rintro z ⟨e, rfl⟩; grind⟩
  have hx : ∀ e, X e ∈ Icc (sInf S) (sSup S) := by
    intro e
    exact ⟨csInf_le hbelow ⟨e, rfl⟩, le_csSup habove ⟨e, rfl⟩⟩
  have hrange : sSup S - sInf S ≤ c := by
    have hh : sSup S ≤ sInf S + c := by
      apply csSup_le hne
      rintro z ⟨e, rfl⟩
      have hl : X e - c ≤ sInf S := by
        apply le_csInf hne
        rintro z ⟨f, rfl⟩
        have hh := (abs_le.1 $ hosc e f ).2
        linarith
      linarith
    linarith
  have horder := sub_nonneg.2 $ csInf_le_csSup hne hbelow habove
  have hsg := hasSubgaussianMGF_of_mem_Icc (μ := π)
      hX.aemeasurable $ Eventually.of_forall hx
  have hh := hsg.mgf_le u
  have hexp : (‖sSup S - sInf S‖₊ / 2) ^ 2 * 𝙟₁ / 2 ≤ 𝔄 := by
    simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg horder]
    have hsq := (sq_le_sq₀ horder hc).2 hrange
    nlinarith
  exact hh.trans $ Real.exp_le_exp.2 hexp
