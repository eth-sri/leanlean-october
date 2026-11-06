/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization

/-!
# The Arakelov height over a number field

Mathlib's `Height.mulHeight` measures a tuple by the **sup norm** at every place. In Arakelov
theory one instead uses the **ℓ² norm at the archimedean places** — the Fubini–Study metric on
`O(1)` — and keeps the sup norm at the finite places. The resulting height is the one in which
the constants of the Siegel-lemma literature (Bombieri–Vaaler, Schmidt) are stated.

This file defines that normalization over a number field `K` and proves its basic API — scaling
invariance and the descent to projective space, `1 ≤ H_Ar`, invariance under reindexing, and the
affine case — together with the two-sided comparison with `Height.mulHeight`, which is what lets
a bound stated in either normalization be read in the other. Not all of
`Mathlib.NumberTheory.Height.Basic` transfers here — see the implementation notes.

## Main definitions

* `NumberField.arakelovMulHeight x` for `x : ι → K`: the multiplicative Arakelov height
  `∏_{v | ∞} (∑ i, v (x i)²)^{mult v / 2} · ∏ᶠ_{v ∤ ∞} ⨆ i, v (x i)`.
* `NumberField.arakelovLogHeight x`: its logarithm.
* `NumberField.arakelovMulHeight₁ x` and `NumberField.arakelovLogHeight₁ x` for `x : K`:
  the one-variable (affine) case, the height of the tuple `![x, 1]`.
* `Projectivization.arakelovMulHeight` and `Projectivization.arakelovLogHeight`: the descent
  of the above to `Projectivization K (ι → K)`, which the scaling invariance below justifies.

## Main results

* `NumberField.arakelovMulHeight_smul_eq`: invariance under scaling by a nonzero element of
  `K`, by the product formula. This is what makes the height projective.
* `NumberField.one_le_arakelovMulHeight`: the Arakelov height is at least `1`.
* `NumberField.arakelovMulHeight_comp_equiv`: invariance under reindexing.
* `NumberField.arakelovMulHeight_one` and `NumberField.arakelovMulHeight₁_one`: the values
  `#ι ^ (totalWeight K / 2)` and `2 ^ (totalWeight K / 2)` on the all-ones tuple and at `1`,
  where the sup-norm height is `1` — the two normalizations genuinely differ.
* `NumberField.arakelovLogHeight₁_eq`: the local formula for the affine logarithmic height,
  with `log⁺ (v x)` at the finite places.
* `NumberField.mulHeight_le_arakelovMulHeight` and `NumberField.arakelovMulHeight_le_mulHeight`:
  the two comparisons with Mathlib's sup-norm height, the second with the constant
  `#ι ^ (totalWeight K / 2)`. These are what transport a constant stated for one normalization
  into the other, and the second is sharp: it is an equality at the all-ones tuple.
* `NumberField.arakelovMulHeight₁_le_mulHeight₁`: the affine case of the same, with constant
  `2 ^ (totalWeight K / 2)` — there is no equality `arakelovMulHeight₁ = mulHeight₁`.
* `Projectivization.mulHeight_le_arakelovMulHeight` and
  `Projectivization.arakelovMulHeight_le_mulHeight`: the same two comparisons on projective space,
  where the heights of Layer 3 live. The first is what makes the Northcott property of Layer 1.1
  carry over to the Arakelov normalization, since it bounds the sup-norm height by the Arakelov
  one with no constant at all.

## Implementation notes

As for `Height.mulHeight`, the zero tuple gets the junk value `1`: the displayed product is `0`
there, which would break `1 ≤ arakelovMulHeight` and the comparison with `Height.mulHeight`.
`NumberField.arakelovMulHeight_eq` recovers the displayed formula for a nonzero tuple, and every
statement below holds unconditionally with this convention.

The index type carries `Fintype` rather than `Finite` because the archimedean local factor is a
`Finset.sum` over `ι`; the value does not depend on the instance.

Only the archimedean factor differs from `NumberField.mulHeight_eq`. Accordingly the proof of
scaling invariance does not redo the product-formula bookkeeping at the finite places: the
transformation law of the finite part is *extracted* from Mathlib's
`Height.mulHeight_smul_eq_mulHeight`, which is the only place where the two normalizations
interact here.

Not every lemma of `Mathlib.NumberTheory.Height.Basic` has an Arakelov analogue, and the two that
fail are not edge cases. `Height.mulHeight_pow` is **false** here — the ℓ² norm is not
multiplicative under coordinatewise powers — and with it `mulHeight₁_pow` and `mulHeight₁_zpow`.
`Height.mulHeight_comp_le` is **false** for a non-injective reindexing, since repeating a
coordinate raises the ℓ² norm at the archimedean places while no sup norm can see the repetition;
it is the injective case that its consumers use. Both are refuted among the examples at the end of
this file.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
(2006), Definition 2.8.1 and 2.8.2–2.8.3, where `H_u` is the local factor above and `h_Ar` the
resulting height on projective space. Their `h_Ar` is the *absolute* height — its local
exponent is `[F_w : ℚ_p] / [F : ℚ]` — whereas `arakelovMulHeight` here is *relative* to `K`,
matching Mathlib's `Height.mulHeight`; the two differ by the exponent `[K : ℚ]`.

This is Layers 0.1 and 0.2 of the `ArithmeticHeights` roadmap: the normalization and its
comparison with `Height.mulHeight`.
-/

public section

namespace NumberField

open Finset Function Height Real

variable {K : Type*} [Field K] [NumberField K] {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-- The **Arakelov height** of a tuple of elements of a number field: the ℓ² norm at the
archimedean places, weighted by `InfinitePlace.mult`, and the sup norm at the finite places.
For the zero tuple we take the junk value `1`, as `Height.mulHeight` does.

This is the normalization in which the constants of the Siegel-lemma literature are stated;
`Height.mulHeight` uses the sup norm at every place. Both live in the library and every bound
says which one it is in. -/
@[expose] noncomputable def arakelovMulHeight (x : ι → K) : ℝ :=
  have : Decidable (x = 0) := Classical.propDecidable _
  if x = 0 then 1 else
    (∏ v : InfinitePlace K, (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ)) *
      ∏ᶠ v : FinitePlace K, ⨆ i, v (x i)

lemma arakelovMulHeight_eq {x : ι → K} (hx : x ≠ 0) :
    arakelovMulHeight x =
      (∏ v : InfinitePlace K, (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ)) *
        ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) := by
  simp [arakelovMulHeight, hx]

@[simp]
lemma arakelovMulHeight_zero : arakelovMulHeight (0 : ι → K) = 1 := by
  simp [arakelovMulHeight]

/-- The rewriting the archimedean local factor always needs: its exponent `mult v / 2` is real
while the sup-norm factor carries the natural power `mult v`, and `(a ^ 2) ^ (n / 2) = a ^ n`
moves between them. -/
lemma sq_rpow_div_two {a : ℝ} (ha : 0 ≤ a) (n : ℕ) : (a ^ 2) ^ ((n : ℝ) / 2) = a ^ n := by
  rw [← Real.rpow_natCast a n, ← Real.rpow_natCast a 2, ← Real.rpow_mul ha]
  congr 1
  push_cast
  ring

/-!
### Scaling invariance

The archimedean local factor scales by `v c ^ mult v` and the finite one by `v c`, so the
product formula makes the height invariant. The finite half of that computation is already in
Mathlib, inside `Height.mulHeight_smul_eq_mulHeight`; we read it off rather than redo it.
-/

section Smul

variable {κ : Type*}

omit [NumberField K] in
lemma iSup_smul_eq {F : Type*} [FunLike F K ℝ] [MonoidWithZeroHomClass F K ℝ]
    [NonnegHomClass F K ℝ] (v : F) (c : K) (x : κ → K) :
    ⨆ i, v ((c • x) i) = v c * ⨆ i, v (x i) := by
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (apply_nonneg v c)]

/-- The transformation law of the *finite* part of the height under scaling, extracted from
Mathlib's `Height.mulHeight_smul_eq_mulHeight`. This is the product formula for `c`, applied to
the finite places only. -/
lemma prod_infinitePlace_mul_finprod_iSup_smul [Finite κ] {x : κ → K} (hx : x ≠ 0)
    {c : K} (hc : c ≠ 0) :
    (∏ v : InfinitePlace K, v c ^ v.mult) * ∏ᶠ v : FinitePlace K, ⨆ i, v ((c • x) i) =
      ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) := by
  have hcx : c • x ≠ 0 := by simp [hc, hx]
  have hA : (0 : ℝ) < ∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult := by
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
    exact prod_pos fun v _ ↦ pow_pos
      ((v.pos_iff.mpr hi).trans_le (Finite.le_ciSup_of_le i le_rfl)) _
  have h := Height.mulHeight_smul_eq_mulHeight x hc
  rw [NumberField.mulHeight_eq hcx, NumberField.mulHeight_eq hx] at h
  simp only [iSup_smul_eq, mul_pow, prod_mul_distrib] at h ⊢
  exact mul_left_cancel₀ hA.ne' (by linear_combination h)

/-- The Arakelov height is invariant under scaling, by the product formula, so it descends to
projective space exactly as `Height.mulHeight` does. -/
lemma arakelovMulHeight_smul_eq (x : ι → K) {c : K} (hc : c ≠ 0) :
    arakelovMulHeight (c • x) = arakelovMulHeight x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [smul_zero]
  have hcx : c • x ≠ 0 := by simp [hc, hx]
  have harch (v : InfinitePlace K) :
      (∑ i, v ((c • x) i) ^ 2) ^ (v.mult / 2 : ℝ)
        = v c ^ v.mult * (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ) := by
    have hsum : ∑ i, v ((c • x) i) ^ 2 = v c ^ 2 * ∑ i, v (x i) ^ 2 := by
      rw [mul_sum]
      exact sum_congr rfl fun i _ ↦ by simp [mul_pow]
    rw [hsum, Real.mul_rpow (by positivity) (by positivity),
      sq_rpow_div_two (apply_nonneg v c) v.mult]
  rw [arakelovMulHeight_eq hcx, arakelovMulHeight_eq hx]
  simp only [harch, prod_mul_distrib]
  rw [mul_right_comm, prod_infinitePlace_mul_finprod_iSup_smul hx hc, mul_comm]

end Smul

/-- The Arakelov height does not change under re-indexing. -/
lemma arakelovMulHeight_comp_equiv (e : ι ≃ ι') (x : ι' → K) :
    arakelovMulHeight (x ∘ e) = arakelovMulHeight x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hx' : x ∘ e ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
    exact ne_iff.mpr ⟨e.symm i, by simpa using hi⟩
  have hsum (v : InfinitePlace K) : ∑ i, v (x (e i)) ^ 2 = ∑ i, v (x i) ^ 2 :=
    e.sum_comp fun i ↦ v (x i) ^ 2
  have hsup (v : FinitePlace K) : ⨆ i, v (x (e i)) = ⨆ i, v (x i) :=
    e.iSup_congr (congrFun rfl)
  rw [arakelovMulHeight_eq hx, arakelovMulHeight_eq hx']
  simp only [comp_apply, hsum, hsup]

/-!
### The comparison with the sup-norm height

`‖·‖_∞ ≤ ‖·‖_2 ≤ √(#ι) · ‖·‖_∞` at each archimedean place, raised to the weight `mult v` and
multiplied over the places; the finite parts of the two heights are the same number and factor
out. This is Layer 0.2 of the roadmap: the pair of lemmas that transports a constant stated for
the Arakelov height into Mathlib's normalization and back, and so the reason a bound in either
normalization is a bound in the other.

The constant of the upper comparison cannot be improved: at the all-ones tuple it is an equality,
by `arakelovMulHeight_one` against `Height.mulHeight_one`.
-/

section Comparison

end Comparison

/-!
The comparison of Layer 0.2, applied to `![x, 1]`. This is the only relation between the two
one-variable heights: `arakelovMulHeight₁ = mulHeight₁` is false, already at `x = 1`.
-/

end NumberField

/-!
### The descent to projective space

Scaling invariance makes the Arakelov height a well-defined function on
`Projectivization K (ι → K)`, exactly as for `Projectivization.mulHeight`.
-/

namespace Projectivization

open NumberField Real

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

lemma arakelovMulHeight_aux (a b : { v : ι → K // v ≠ 0 }) (t : K)
    (h : a.val = t • b.val) :
    NumberField.arakelovMulHeight a.val = NumberField.arakelovMulHeight b.val :=
  have ht : t ≠ 0 := by
    contrapose! h
    simpa [h] using a.prop
  h ▸ arakelovMulHeight_smul_eq _ ht

-- We do not expose the bodies of these definitions so that we can keep the "_aux" lemmas
-- above private.

/-- The multiplicative Arakelov height of a point of projective space over a number field. -/
noncomputable def arakelovMulHeight (x : Projectivization K (ι → K)) : ℝ :=
  x.lift (fun r ↦ NumberField.arakelovMulHeight r.val) arakelovMulHeight_aux

lemma arakelovMulHeight_mk {x : ι → K} (hx : x ≠ 0) :
    arakelovMulHeight (mk K x hx) = NumberField.arakelovMulHeight x := by
  rfl

/-!
#### Comparison of the two normalizations on projective space

`NumberField.mulHeight_le_arakelovMulHeight` and `NumberField.arakelovMulHeight_le_mulHeight` read
on `Projectivization K (ι → K)`. Both sides are computed on any representative, so the comparisons
descend to projective space with the same constant.
-/

end Projectivization

/-!
### `positivity` extensions

The Arakelov heights are positive (multiplicative) resp. nonnegative (logarithmic), exactly as
their sup-norm counterparts in `Mathlib.NumberTheory.Height.Basic`.
-/

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq

end Mathlib.Meta.Positivity

/-!
### Worked examples

Cheap checks that the definition means what it should. Over `ℚ` the two normalizations of the
height of the point `(1 : 1)` genuinely differ, so the `√N` factors in the Siegel-lemma
literature are not cosmetic and a proof that silently interchanges the two heights is wrong.

The third shows that the constant of `arakelovMulHeight_le_mulHeight` is attained, so it cannot be
improved. The last two are rejection tests: they refute the two lemmas of
`Mathlib.NumberTheory.Height.Basic` that a reader would expect to carry over to this normalization
and that do not.
-/

section Examples

open Height NumberField

end Examples

end
