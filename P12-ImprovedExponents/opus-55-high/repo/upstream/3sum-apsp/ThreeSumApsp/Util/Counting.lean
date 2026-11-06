/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Fin

/-!
# Cardinalities of finite sets

General facts about finite sets.

* A product with one value on `S` and another elsewhere (`Finset.prod_ite_mem_const`); two products
  that vanish unless one set lies in another (`Finset.prod_ite_ite_subset`,
  `Finset.prod_ite_ite_superset`); the number of sets of `k` elements inside a set or around a set
  (`Finset.sum_powersetCard_ite_subset`, `Finset.card_powersetCard_superset`).
* At most `c` elements of a set have a given quotient by `c` under an injective function
  (`Finset.card_filter_div_eq_le`).
* A finite subset of `Fin L` has `j` elements below its `j`-th lowest element
  (`Finset.card_filter_lt_orderEmbOfFin`, from `Finset.card_filter_lt_map` for any increasing
  sequence).

* A function `f : ι → α` has a property `p` at the place `i` if `p (f i)` holds. The number of
  functions `f` with `f i ∈ A i` that have `p` exactly at the places of a set `S` is a product over
  the places (`Finset.card_pi_places_eq`). The number of those that have `p` at exactly `k` places
  is the sum of these products over the sets `S` of `k` places (`Finset.card_pi_places_card`).
  Without the restriction to `A` it is a binomial coefficient times two powers
  (`Finset.card_places_card`).
-/


namespace Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {M : Type*}

/-- A product that takes the value `a` on `S` and `b` elsewhere. -/
theorem prod_ite_mem_const [CommMonoid M] (S : Finset ι) (a b : M) :
    (∏ i, if i ∈ S then a else b) = a ^ #S * b ^ (Fintype.card ι - #S) := by
  rw [prod_ite, prod_const, prod_const, filter_not,
    filter_mem_eq_inter, univ_inter, ← compl_eq_univ_sdiff, card_compl]

/-- A product with the factors `1` on `S ∩ Q`, `0` on `S \ Q`, `c` on `Q \ S` and `1` elsewhere: it
is `0` unless `S ⊆ Q`. -/
theorem prod_ite_ite_subset [CommMonoidWithZero M] (Q S : Finset ι) (c : M) :
    (∏ i, if i ∈ S then (if i ∈ Q then 1 else 0) else (if i ∈ Q then c else 1))
      = if S ⊆ Q then c ^ (#Q - #S) else 0 := by
  split_ifs with h
  · have hterm : ∀ i, (if i ∈ S then (if i ∈ Q then 1 else 0) else (if i ∈ Q then c else 1))
        = if i ∈ Q \ S then c else 1 := fun i => by
      grind
    simp_rw [hterm]
    rw [prod_ite_mem_const, one_pow, mul_one, card_sdiff_of_subset h]
  · obtain ⟨i, hiS, hiQ⟩ := not_subset.mp h
    exact prod_eq_zero (mem_univ i) (by simp_all)

/-- The number of sets of `k` elements inside `Q`, each counted `c` times. -/
theorem sum_powersetCard_ite_subset (Q : Finset ι) (k c : ℕ) :
    (∑ S ∈ powersetCard k (univ : Finset ι), if S ⊆ Q then c else 0) = (#Q).choose k * c := by
  rw [← sum_filter, sum_const, ← card_powersetCard]
  congr 2
  grind


variable {L k : ℕ}

/-! ## The elements below a bound -/

/-- An increasing sequence has `j` members below its member number `j`. -/
theorem card_filter_lt_map (f : Fin k ↪o Fin L) (j : Fin k) :
    ((Finset.univ.map f.toEmbedding).filter fun x : Fin L => (x : ℕ) < (f j : ℕ)).card = j := by
  have hbelow : Finset.univ.filter ((fun x => x < (f j)) ∘ f.toEmbedding)
      = Finset.Iio j := by
    aesop
  grind [Finset.filter_map, Finset.card_map, Fin.card_Iio]

/-- The number of elements of `s` below its `j`-th lowest element is `j`. -/
theorem card_filter_lt_orderEmbOfFin (s : Finset (Fin L)) (h : s.card = k) (j : Fin k) :
    (s.filter fun x : Fin L => (x : ℕ) < (s.orderEmbOfFin h j : ℕ)).card = j := by
  simpa [Finset.map_orderEmbOfFin_univ] using card_filter_lt_map (s.orderEmbOfFin h) j

/-! ## Functions by the set of places with a property -/

variable {α : Type*} [Fintype α]

/-- The number of functions `f` with `f i ∈ A i` whose set of places with `p` is exactly `S`: choose
a value with `p` at each place of `S` and one without `p` at every other place. -/
theorem card_pi_places_eq [DecidableEq α] (A : ι → Finset α) (p : α → Prop) [DecidablePred p]
    (S : Finset ι) :
    #{f : ι → α | (∀ i, f i ∈ A i) ∧ ({i | p (f i)} : Finset ι) = S} =
      ∏ i, if i ∈ S then #{a ∈ A i | p a} else #{a ∈ A i | ¬ p a} := by
  simp_rw [← apply_ite, ← Fintype.card_piFinset]
  congr 1
  grind

/-- The number of functions `f` with `f i ∈ A i` that have `p` at exactly `k` places, as a sum over
the possible sets of these places. -/
theorem card_pi_places_card [DecidableEq α] (A : ι → Finset α) (p : α → Prop) [DecidablePred p]
    (k : ℕ) :
    #{f : ι → α | (∀ i, f i ∈ A i) ∧ #{i | p (f i)} = k} =
      ∑ S ∈ powersetCard k (univ : Finset ι),
        ∏ i, if i ∈ S then #{a ∈ A i | p a} else #{a ∈ A i | ¬ p a} := by
  rw [card_eq_sum_card_fiberwise (f := fun f => ({i | p (f i)} : Finset ι))
    (t := powersetCard k univ)
    fun f hf => by simp_all]
  refine sum_congr rfl fun S hS => ?_
  rw [← card_pi_places_eq]
  exact congrArg card (by grind)

/-- The number of functions `ι → α` that have `p` at exactly `k` places. -/
theorem card_places_card (p : α → Prop) [DecidablePred p] (k : ℕ) :
    #{f : ι → α | #{i | p (f i)} = k} =
      (Fintype.card ι).choose k * (#{a | p a} ^ k * #{a | ¬ p a} ^ (Fintype.card ι - k)) := by
  classical
  have h := card_pi_places_card (ι := ι) (fun _ => univ) p k
  simp [mem_univ, implies_true, true_and] at h
  rw [h, sum_congr rfl fun S hS => by
    rw [prod_ite_mem_const, (mem_powersetCard.1 hS).2], sum_const, card_powersetCard, card_univ,
    smul_eq_mul]
