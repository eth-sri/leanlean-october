module
public import GuthMaynard.NativeSource.GuthMaynard.InghamBound

@[expose] public section

namespace GuthMaynard.NativeMoment

/-!
# Arithmetic for the finite classical density transfer

These lemmas isolate the exact range comparisons used when the finite
large-values estimates are specialized to the Ingham and Huxley endpoints.
They resolve only the exceptional short zeta-polynomial alternative: that
range is empty for Ingham and for the lower part of Huxley's interval, while
the proved Weyl threshold covers the remaining Huxley range.  They do not
remove the distinct medium ordinary-zeta Type-I reflection in ANTEDB Lemma
11.5.
-/

/-- In the interior of Ingham's interval, the upper end of the
zeta-polynomial range is strictly below its lower end `2`. -/
theorem ingham_zeta_polynomial_range_empty
    {σ τ : ℝ} (hσ : 1 / 2 < σ) (hτ : 2 ≤ τ) :
    ¬ τ < 4 * (2 - σ) / 3 := by grind

end GuthMaynard.NativeMoment
