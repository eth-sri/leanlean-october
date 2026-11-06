module

/-!
# Interval arithmetic with rational endpoints, without Mathlib

An interval `Ival` is a pair of rationals `[lo, hi]`. Every operation returns an interval that
contains the image of its inputs: exact rational results are rounded outward (`roundDown` for
lower ends, `roundUp` for upper ends) to the dyadic grid `2^-p`, which keeps numerators and
denominators bounded. The precision `p` is the last argument of each operation, with default
`defaultPrec = 128` (about 38 decimal digits of absolute precision).

The library depends on Lean core only (`Int`, `Nat`, core `Rat`), so it can be compiled to native
code without compiling Mathlib. The soundness theorems (every operation contains the true values,
for real numbers and `Real.exp`) are in `GradedNear/Interval/Sound.lean`.

Nothing here assumes `lo ≤ hi`: for an interval with `lo > hi` no real number is a member, and
the inclusion theorems hold vacuously.

## The exponential

`expLo p q ≤ exp q ≤ expHi p q` for a rational `q`, and `Ival.exp` applies these to the two ends
(`exp` is increasing; `expBoth` shares the work when `lo = hi`). For `q ≥ 0` write `q = n / d`;
with `k = expShift n d` we have `Y = q / 2^k < 2^-8`. The computation is in fixed point: a natural
number `a` stands for `a / 2^w`, with `w = p + k + 12`. With `y = ⌊2^w Y⌋`, one pass of the Taylor
series of `exp (y / 2^w)` with the terms rounded down (`taylor`) gives a lower bound `s` and an
error bound `e`: every rounded term is within `3` units of the exact term, and the pass stops at
the first term that rounds to `0`, whose tail is at most twice the term (`Real.exp_bound`: the tail
after `m ≥ 1` terms is at most `Y^m (m+1)/(m!·m) ≤ 2 Y^m/m!`). The upper bound `s + e` is
multiplied by `1 + 2^(1-w) ≥ exp (2^-w)` to cover the rounding of `y`. Then `k` squarings, rounded
down or up, give `exp q = exp(Y)^(2^k)`. For `q < 0` we use `exp q = 1 / exp(-q)`, and for
`q ≤ -p` the bounds `0 ≤ exp q ≤ 2^-p`.

With the default precision the enclosures of `exp q` have width at most about `2^-128` for
`q ≤ 0` and relative width about `2^-128` for `q ≥ 0` (about 38 correct digits). Values below
`2^-p` are only known to lie in `[0, 2^-p]`, as the grid is absolute.
-/

@[expose] public section

namespace IntervalCore

/-- The default precision: results are rounded outward to the grid `2^-128`. -/
def defaultPrec : Nat := 128

/-! ## Comparisons of rationals -/

/-- `a ≤ b` as a `Bool`. -/
@[inline] def ratLe (a b : Rat) : Bool := decide (a ≤ b)

/-- `a < b` as a `Bool`. -/
@[inline] def ratLt (a b : Rat) : Bool := decide (a < b)

/-- The minimum of two rationals. -/
@[inline] def rmin (a b : Rat) : Rat := if a ≤ b then a else b

/-- The maximum of two rationals. -/
@[inline] def rmax (a b : Rat) : Rat := if a ≤ b then b else a

/-! ## Outward rounding to the grid `2^-p` -/

/-- `⌊n·2^p/d⌋ / 2^p`, the largest multiple of `2^-p` that is `≤ n / d` (for `d > 0`). -/
@[inline] def divDown (p : Nat) (n : Int) (d : Nat) : Rat :=
  mkRat (n * ((2 ^ p : Nat) : Int) / (d : Int)) (2 ^ p)

/-- `⌈n·2^p/d⌉ / 2^p`, the smallest multiple of `2^-p` that is `≥ n / d` (for `d > 0`). -/
@[inline] def divUp (p : Nat) (n : Int) (d : Nat) : Rat :=
  mkRat (-(-n * ((2 ^ p : Nat) : Int) / (d : Int))) (2 ^ p)

/-- `q` rounded down to the grid `2^-p`. Rationals on the grid (denominator dividing `2^p`) are
returned unchanged. -/
def roundDown (p : Nat) (q : Rat) : Rat :=
  if 2 ^ p % q.den = 0 then q else divDown p q.num q.den

/-- `q` rounded up to the grid `2^-p`. Rationals on the grid are returned unchanged. -/
def roundUp (p : Nat) (q : Rat) : Rat :=
  if 2 ^ p % q.den = 0 then q else divUp p q.num q.den

/-! ## Intervals -/

/-- The closed interval `[lo, hi]` of real numbers. -/
structure Ival where
  lo : Rat
  hi : Rat
  deriving Repr, Inhabited, BEq, DecidableEq

namespace Ival

/-! ### Constructors and checks -/

/-! ### Arithmetic -/

/-- `-I` (exact). -/
def neg (I : Ival) : Ival := ⟨-I.hi, -I.lo⟩

/-- `I + J`. -/
def add (I J : Ival) (p : Nat := defaultPrec) : Ival :=
  ⟨roundDown p (I.lo + J.lo), roundUp p (I.hi + J.hi)⟩

/-- `I - J`. -/
def sub (I J : Ival) (p : Nat := defaultPrec) : Ival :=
  ⟨roundDown p (I.lo - J.hi), roundUp p (I.hi - J.lo)⟩

/-- `I · J`: the minimum and maximum of the four products of ends, rounded outward (two products
when both intervals are nonnegative). -/
def mul (I J : Ival) (p : Nat := defaultPrec) : Ival :=
  if 0 ≤ I.lo ∧ 0 ≤ J.lo then
    ⟨roundDown p (I.lo * J.lo), roundUp p (I.hi * J.hi)⟩
  else
    let a := I.lo * J.lo
    let b := I.lo * J.hi
    let c := I.hi * J.lo
    let d := I.hi * J.hi
    ⟨roundDown p (rmin (rmin a b) (rmin c d)), roundUp p (rmax (rmax a b) (rmax c d))⟩

end Ival

/-! ## Fixed-point helpers: a natural number `a` stands for `a / 2^w` -/

/-- `⌊a / 2^w⌋ + 1`, an upper bound for `a / 2^w`. -/
@[inline] def shrUp (a w : Nat) : Nat := (a >>> w) + 1

namespace Ival

/-! ### Notation at the default precision -/

instance : Neg Ival := ⟨neg⟩
instance : Add Ival := ⟨fun I J => add I J⟩
instance : Sub Ival := ⟨fun I J => sub I J⟩
instance : Mul Ival := ⟨fun I J => mul I J⟩

end Ival

end IntervalCore
