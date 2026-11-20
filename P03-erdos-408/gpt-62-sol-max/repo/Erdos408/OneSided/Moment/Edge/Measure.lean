module

public import Erdos408.OneSided.Moment.Chain
public import Erdos408.OneSided.Bands

/-!
# Nonnegativity of the chain measure

The norm bounds of the edge (`Moment/Edge.lean`) add by Minkowski, which needs the chain
measure to be nonnegative. It is a product of birth weights `ν(p) = 1 / (V(p) (p + 1) b'_p)`
and a memory weight, so it suffices that the baselines `b'_p` are nonnegative at the band
primes. This holds once the band primes exceed `N = 2R`, which is eventually the case.

* `eventually_chainMeasure_nonneg`: eventually the chain measure with `N = 2R` is
  nonnegative.
-/

@[expose] public section

noncomputable section

namespace Erdos408.OneSided

open Filter Finset Real

variable {K : ℕ}

section Measure

variable {q x : ℝ} {d : Data K}

/-- Eventually the chain measure with `N = 2R` is nonnegative. -/
theorem eventually_chainMeasure_nonneg {C CX alo ahi g : ℝ} (hq : 0 < q)
    (halo : 1 / 10 < alo) :
    ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d →
      ∀ (Y d₀ u v r : ℝ) (B : ℕ) (s : ChainState x d Y d₀ u v r B),
        0 ≤ chainMeasure q x d Y d₀ u v r B (2 * momentPower x) s := by
  filter_upwards [eventually_two_mul_add_one_le halo] with x hbig d hd Y d₀ u v r B s
  have hν := primeWeight_nonneg_of_nonneg_baseline (N := 2 * momentPower x) fun p hp =>
    baseline_nonneg hq.le (by have := hbig d hd p hp; omega)
  exact mul_nonneg (prod_nonneg fun i _ => prod_nonneg fun h _ => hν _)
    (memWeight_nonneg (fun xp => hν _) _)

end Measure

end Erdos408.OneSided
