module

public import IntervalCore

/-!
# Interval enclosures of the leaf functions, without Mathlib

Interval enclosures (in `IntervalCore.Ival`, at precision `prec`, default `128`) of the real
functions of `GradedNear/Functions.lean` whose values a certificate leaf stores (specification:
§1 of `research/notes/leaf-data-semantics-2026-09-29.md` in the research repository). The inputs are rationals. The soundness
theorems (every enclosure contains the true value) are in `GradedNear/LeafNumSound.lean`.

* The kernel constants `T`, `beta`, `kappa` and `H0` as rationals (the same rationals as
  `GradedNear.Kernel.T`, `beta`, `kappa`, and `H₀ = (κ Σ β_i)²`).
* `benv φ λ`: the envelope `B_φ(λ)` by its closed form
  `H₀ B_φ(λ) = Σ_i E^i (β_i² (Q₀ + (φ/2) U) + κ U β_i Σ_{j>i} β_j)`, `E = e^{−2κλ}`,
  `U = (1 − E)/λ`, `Q₀ = κ/λ − U/(2λ)` (for `λ ≠ 0`); the two polynomials in `E` are evaluated by
  Horner's rule.
* `gphi L φ λ = e^{−(L−2T)λ} B_φ(λ)`; `hratio λ = h(λ)`; `cpa p a = C(p, a)` from the exact
  step-cell sums (`a ≠ 0`); `jold`, `jnew`: the first-family bounds `J_old`, `J_new`.
* The far weight of a profile `(c₁, c₂, θ)`: with `a = 2λ − θ`, `ε = 10⁻⁷`,
  `w(λ)⁻¹ = 2 e^{a(u−ε)} ∫_{√ε}^{√(c₂+ε)} r² e^{a r²} dr + √(c₂+ε) ∫_v^x e^{at} dt`
  (`winv`), and `w = 1/winv` (`w`).
* `vUpper`: an upper bound for the constant `V` of the far bound, through
  `J_i = K(ih) − K((i+1)h)` with `K(d) = ∫_u^x w₀(t)⁻² (t − u − d)₊ dt`.

**The integrals `∫ (r² − D) e^{c r²} dr`** (`rInt`) over `[√y_a, √y_b]` are computed from the
Taylor polynomial `P_N` of `exp` with `N = seriesTerms + 4⌈|c| y_b⌉` terms: the polynomial part
integrates exactly to `√y_b Φ(y_b) − √y_a Φ(y_a)` with
`Φ(y) = Σ_{k<N} (cy)^k/k! (y/(2k+3) − D/(2k+1))` (`serPhi`), and
`|e^x − P_N(x)| ≤ 2|x|^N/N!` for `2|x| ≤ N + 1` bounds the rest. The square roots of rationals are
enclosed by rationals checked by squaring (`sqrtI`).

**Fixed point.** The two inner loops, Horner's rule (`horner`) and the series `Φ` (`serStep`),
run on `Fx`: intervals with integer ends at a fixed scale `2^w`, where additions are exact and
products round outward by one floor or ceiling division (about 4× faster than `Ival`, whose every
operation normalizes a `Rat`). The exponentials are `IntervalCore.Ival.exp`.

**Precision and cost.** With the default precision `128` the enclosures have widths of about
`10⁻³⁶` (relative) for `λ ∈ [0, 3]`. Natively compiled, one `gphi` takes about 0.25 ms and one
`w`/`winv` about 0.6 ms (on a loaded machine); `cpa` and `jnew` a few ms, `vUpper` about 20 ms.
-/

@[expose] public section

namespace LeafNumCore

open IntervalCore

/-! ## The kernel constants -/

/-! ## Interval helpers -/

/-! ### Fixed-point intervals

The two inner loops (Horner's rule and the Taylor series of `rInt`) run on intervals with integer
ends at a fixed scale `2^w`: additions are exact and the other operations round outward by a
floor or ceiling division, without the `gcd` normalizations of `Rat`. -/

/-- `⌊n / d⌋` for `d > 0`. -/
@[inline] def fdivI (n : Int) (d : Nat) : Int := n / (d : Int)

/-- `⌈n / d⌉` for `d > 0`. -/
@[inline] def cdivI (n : Int) (d : Nat) : Int := -((-n) / (d : Int))

namespace Fx

end Fx

/-! ## The envelope, `G_φ`, `h`, `C(p, a)` and the first-family bounds -/

/-! ## The integrals `∫ (r² − D) e^{c r²} dr` -/

/-! ## The far weight -/

/-! ## The constant `V` -/

/-! ## The two far profiles of the corpus -/

end LeafNumCore
