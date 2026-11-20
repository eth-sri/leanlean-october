module

public import Mathlib
public import AnalyticESC.Main.Example
public import AnalyticESC.Conjugation.PeriodicPoints
public import AnalyticESC.Generic.OpenDense
public import AnalyticESC.Dimension.NaturalMeasure
public import AnalyticESC.Dimension.OpenDense
public import AnalyticESC.Dimension.Example
public import AnalyticESC.Dimension.Lq

@[expose] public section

/-!
# Proofs of the audited statements

Proofs of the theorems stated in `Challenge.lean`, for B. Bárány, I. Kolossváry and
S. Troscheit, *On exponential separation of analytic self-conformal sets on the real line*,
as stated in `../analytic.tex`. The shared statement vocabulary is in `AnalyticESC.Statements`; this module
proves the audited theorems without importing `Challenge.lean`.
-/

namespace Challenge

open Set Metric
open scoped AnalyticESC

variable {N : ℕ}

/-- The polynomial example of Section 1.2.2: the system `x/8`, `x/8 + x²/32`, `x/16 + x²/32 + 29/32` lies in
`𝔖_3` for some `ε > 0` and satisfies the strong exponential separation condition. -/
theorem audit_example_sesc : ∃ ε > 0, (∀ i, InClass ε (exampleMaps i)) ∧ SESC exampleMaps := ⟨_, AnalyticESC.exampleIFS.ε_pos, AnalyticESC.exampleIFS.inClass, AnalyticESC.exampleIFS_sesc⟩

/-- Individual-map linearisation for Theorem 1.12: an analytic coordinate with nonvanishing
derivative conjugates the chosen map `f_i` to a contracting similarity. -/
theorem audit_conj_similarity {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ)
    (hf : ∀ i, InClass ε (f i)) (i : Fin N) :
    ∃ g, IsAnalyticCoord g ∧ (∀ x ∈ I, deriv g x ≠ 0) ∧
      ∃ lam t : ℝ, lam ≠ 0 ∧ |lam| < 1 ∧ ∀ x ∈ I, g (f i x).re = lam * g x + t := by
  let Φ : AnalyticESC.IFS N ε := ⟨f, hε, hf⟩
  obtain ⟨g, hg, hg', hode⟩ := AnalyticESC.exists_coord_of_logDeriv hε
    (Φ.differentiableOn_dualProj (.inf fun _ => i))
  exact ⟨g, hg, hg', Φ.exists_conj_of_dual_fixed i hg.1 hg' (Φ.dualProj_const_fixed i) hode⟩

/-- Theorem 1.6 (Rapaport), from Rapaport's Theorem 1.2 and Corollary 1.3. Let
`Φ = (f_i)_{i ∈ Fin N}`, `N ≥ 1`, be an analytic IFS in `𝔖_N` whose attractor is not a singleton.
If `Φ` satisfies the ESC, then there is equality in (1.6). -/
theorem audit_dim_of_esc (hM : RapaportMeasureStatement) (hS : RapaportSetStatement) {ε : ℝ}
    (hε : 0 < ε) (f : Fin N → ℂ → ℂ) (hf : ∀ i, InClass ε (f i))
    (hN : 0 < N) (hnd : ¬ ∃ x, attractor f = {x}) (hesc : ESC f) : DimEquality f := AnalyticESC.IFS.theorem_1_6 ⟨f, hε, hf⟩ hM hS hN hnd hesc

end Challenge
