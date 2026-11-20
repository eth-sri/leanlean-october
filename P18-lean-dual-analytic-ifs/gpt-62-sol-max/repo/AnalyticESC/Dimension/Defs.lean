module

public import AnalyticESC.Main.LocalDimension

@[expose] public section

/-!
# Dimension theory: vocabulary and cited results

The vocabulary of Section 1.2.1 and of the natural measure of the polynomial example
in Section 1.2.2: entropy, Lyapunov exponent, self-conformal measures, the equality in (1.6),
the potential `s log|f'_{ω₀}(π(σω))|` and its Gibbs measures.

The cited results are shared with `Solution` via `AnalyticESC.Statements` and are taken as
explicit hypotheses.

* `BowenGibbsStatement`: R. Bowen, *Equilibrium states and the ergodic theory of Anosov
  diffeomorphisms*, Lecture Notes in Mathematics 470, Springer, 1975, Theorem 1.4, for the
  one-sided full shift.
* `RapaportMeasureStatement`: A. Rapaport, *Dimension of self-conformal measures associated to an
  exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2, Theorem 1.2, with the exact
  dimensionality of self-conformal measures of D.-J. Feng and H. Hu, *Dimension theory of iterated
  function systems*, Comm. Pure Appl. Math. 62 (2009).
* `RapaportSetStatement`: the same paper of Rapaport, Corollary 1.3.

Rapaport's statements are for real maps of `I = [0,1]`; `realComp` is the composition of real
maps and `RapaportHyp` collects his hypotheses.
-/

namespace AnalyticESC

open Set Metric Filter Topology MeasureTheory

export Challenge (divide Scale scaleZero logRatio realComp RapaportHyp RapaportMeasureStatement
  RapaportSetStatement IsGibbsMeasure BowenGibbsStatement entropy IsProbVec)

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

noncomputable abbrev lyapunov := Challenge.lyapunov Φ.f

abbrev IsSelfConformal := Challenge.IsSelfConformal Φ.f

noncomputable abbrev potential := Challenge.potential Φ.f

end IFS

/-- Restricting to scales in `(0,1)` does not change the filter at zero from above. -/
theorem scaleZero_map : map (fun r : Scale => (r : ℝ)) scaleZero = 𝓝[>] (0 : ℝ) := by
  apply map_comap_of_mem
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from zero_lt_one)] with r hr
  simpa

theorem scale_tendsto_iff (g : ℝ → ℝ) (l : Filter ℝ) :
    Tendsto (fun r : Scale => g r) scaleZero l ↔ Tendsto g (𝓝[>] 0) l := by
  rw [← scaleZero_map, tendsto_map'_iff]
  rfl

end AnalyticESC

namespace Challenge

open AnalyticESC Set Metric Filter Topology MeasureTheory

/-- The pressure limit vanishes at `s` and at no other exponent. -/
abbrev IsUniquePressureZero {N : ℕ} (f : Fin N → ℂ → ℂ) (s : ℝ) : Prop :=
  ∀ t, Tendsto (pressureRatio f t) atTop (𝓝 0) ↔ t = s

end Challenge
