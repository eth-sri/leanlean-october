module

public import LeafNumCore
public import CertCore

/-!
# The near-row checker, without Mathlib

`rowCheck` decides, in exact rational and interval arithmetic, that the stored integers of one
near row of a leaf (its radius `d`, and the feature `v` and diagonal `D` of each entry with a
positive feature) are valid for a concrete instance of the graded near lemma
(`GradedNear/Row.lean`). The row's parameters `RowP` are those of
`computations/sieve_near/sieve_inputs.py` in the research repository (`SieveNearTest`): the parabolic detector of width `2γ`,
the parabolic Gram test of width `2g₁`, the anchors `s ≥ s₁ ≥ 0`, and the sieve heights `h_k` on
`m` cells of `[t₀, 2γ)`. Each entry `Ent` names the entry's semantics: its feature is taken at
`hi` from the response anchor `anc`, its diagonal at the offset `del ≤ s - anc`, and `sp` names a
second kept zero, if any (`Spec`).

The checker computes, as the builders do:
* an upper bound `I_L ≥ I_B` (`ibUpper`), the upper Riemann sum with `nShort = 2000` cells on
  `[0, t₀)` and the `m` sieve cells, whose exponentials run along geometric sequences;
* enclosures of `D(δ) = 2g₁ Φ(2g₁(2δ - s₁)) + e^{-2δt₀} Σ_k c_k ρ^k`, `ρ = e^{-2δ(2γ - t₀)/m}`
  (`dI`, Horner's rule), for the listed offsets;
* enclosures of `F(x) = 2γ Φ(2γ x)` (`fI`) for the listed feature points;
* for each entry, the values `(add, exc)` of its semantics (`specVals`): a lower bound for its
  second kept zero's term and an upper bound for its pair excess, from enclosures of
  `Re F(x + iy)` at complex points (`reFI`, with `cos` and `sin` from `cosSinI`) and of the
  exponential moment `E₂` (`e2I`);

and then chooses the normalizer `D_u` as the least value that the radius and every diagonal
allow (`duOf`), and checks every feature against it:
`(v + Sη)² I_L D_u ≤ S² (F(x) + add - 1/6)²` with `F(x) + add > 1/6`.

`Φ(u) = ∫₀¹ P(s) e^{-us} ds` is enclosed by its closed form for `|u| ≥ 1` and by its Taylor
polynomial of degree `< 40` with the remainder bound for `|u| < 1` (`phiI`, and `rePhiCI` at
complex points). The soundness theorems are `GradedNear.Row.rowCheck_sound`
(`GradedNear/Row/RowSound.lean`) and `GradedNear.Row.specVals_sound`
(`GradedNear/Row/SpecSound.lean`).

`checkRows` applies the check to every near row of a leaf (`CertCore.Leaf`) that has metadata
(`RowMeta`; the inherited two-test row has none): the entries are the columns with a positive
feature in the row, each of which must have a semantics, and the family terms with a positive
feature and a semantics. Every family term's diagonal must be positive.
-/

@[expose] public section

namespace RowCheckCore

open IntervalCore LeafNumCore

/-! ## The parabolic tests and `Φ` -/

/-! ## The row parameters -/

/-- The rational parameters of a near row (as `GradedNear.Row.Params`). -/
structure RowP where
  γ : Rat
  g1 : Rat
  t0 : Rat
  s : Rat
  s1 : Rat
  h : List Rat
  deriving Repr, Inhabited, BEq

namespace RowP

variable (p : RowP)

/-- The number of sieve cells. -/
def m : Nat := p.h.length

/-- The cell ends `t_k = t₀ + (2γ - t₀) k / m`. -/
def tk (k : Nat) : Rat := p.t0 + (2 * p.γ - p.t0) * k / p.m

/-- The sieve height of cell `k`. -/
def hk (k : Nat) : Rat := p.h.getD k 0

end RowP

/-! ## The Riemann sum of `I_B` -/

/-! ## The diagonal `D(δ)` -/

/-! ## Complex points -/

namespace CQ

end CQ

/-! ## `cos` and `sin` -/

/-! ## `Re ΦC` and `Re F` -/

/-! ## The exponential moment `E₂` -/

/-! ## The special entries (paper §9.4)

Three family terms keep a second zero besides the one at the entry's height: the `rc` pair and the
first family's second zero (a second zero left of the test point, at height difference `y`), and
the shifted `rc` entry (the conjugate zero, somewhere in `Re z ≥ a - s`). An entry's `Spec` names
the case, and `specVals` computes its values `(add, exc)`: a lower bound `add` for the second
zero's term and an upper bound `exc` for the entry's pair excess `(Re G(-s₁ + iy) - 1/6)₊`.
* `two`: `Re F(x + iy)` at the midpoint `x₀` of `[xa, xb]` and `Re G(-s₁ + iy)` on a uniform grid of
  `n` cells of `[ylo, min(yhi, ytop)]`, with the second-derivative slacks `c³m₂h²/8` and
  `c₁³E₂(c₁s₁)h²/8` and the Lipschitz slack `c²m₁(xb - xa)/2`; beyond `ytop` the closed-form tail
  of `G` and `Re F ≥ 0`; `add = max(R, 0)` and `exc = max(C - 1/6, 0)`;
* `cz`: `C ≥ -Re F` on the line `Re z = -d` from the cells between consecutive points of `ys`
  (starting at `0`), the second-derivative slack `c³E₂(cd)(b - a)²/8`, and the closed-form tail
  beyond the last point; `add = -C`, `exc = 0` (the half-plane follows by the minimum principle).
-/

/-! ## The row check -/

/-! ## The rows of a leaf -/

end RowCheckCore
