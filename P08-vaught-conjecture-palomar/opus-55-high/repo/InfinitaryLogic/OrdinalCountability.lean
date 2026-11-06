/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.OrdinalUtil
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.SetTheory.Cardinal.Continuum
public import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Generic countable-ordinal and Cantor helpers

Construction-free lemmas about ranks into the countable ordinals, requested by consumers of the
descriptive theory and placed here because they mention no logic.  `ω₁` is `Ordinal.omega 1`
throughout, as in `OrdinalUtil` (`Cardinal.ord_aleph` converts from `(aleph 1).ord`).  Mathlib is
reused wherever it already has the fact; nothing here adds an instance.

## Sections

* **Cantor space.**  `not_countable_univ_cantor`: Cantor space is uncountable, from
  `#(ℕ → Bool) = 𝔠` and `ℵ₀ < 𝔠`.
* **Suprema.**  `iSup_lt_omega1_of_forall_lt`: a sequence of countable ordinals has a countable
  supremum (regularity of `ℵ₁`).  `iSup_add_one_lt_omega1`: over any countable index type, the
  supremum of the successors of countable ordinals is countable.
* **Rank and countability.**  `countable_iff_rank_bounded`: for a rank `r` with `r x < ω₁` and
  countable fibers below `ω₁`, a set is countable iff its ranks are bounded below `ω₁`.  Forward:
  enumerate the set and bound the supremum by regularity of `ℵ₁`; backward
  (`countable_of_forall_rank_lt`, which needs only the countable fibers): a countable union of
  countable fibers over a countable initial segment (`setCountable_Iio_of_lt_omega1`).
* **Countable complements from losses.**  `compl_countable_of_loss`: countable successor losses and
  a limit-continuity hypothesis give countable complements below `ω₁`, by transfinite induction.
  The limit hypothesis is explicit and necessary; no monotonicity is assumed.
* **Exhaustion by domains.**  `mk_le_aleph_one_of_domains`: domains with countable complements
  below `ω₁`, left by every point, bound `#X` by `ℵ₁` (no monotonicity, no nonemptiness).
  `mk_eq_aleph_one_of_domains`: antitone such domains that are moreover nonempty below `ω₁` give
  `#X = ℵ₁`.  Both are universe-polymorphic (`aleph 1` in the universe of `X`;
  `Cardinal.lift_aleph` relates the universes).
* **Separation by an isolating observation.**  For an abstract satisfaction relation
  `Sat : F → X → Prop`: `notMem_of_isolating_of_uniform`, a point isolated by `φ` lies in no
  nonsingleton set on which `φ` is constant; `lt_index_of_isolating_of_antitone` (any linear
  order of stages), for antitone domains that are nonsingleton and agree on `φ` at an index `ζ`,
  every stage containing the point lies strictly below `ζ`, with the rank form
  `lt_rank_of_isolating_of_antitone` (`ζ := rank φ`) and its `Ordinal.{0}` form
  `stage_lt_rank_of_isolating`; `exists_countable_strict_stage_bound_of_isolation`, isolating
  observations of countable rank and rank-uniform nonsingleton domains below `ω₁` bound every
  point's stages by a countable ordinal.  See the section for the conventions.
* **Rank tails.**  `rankTail r η = {x | η ≤ r x}`, with the simp lemma `mem_rankTail` and the
  bridge `rankTail_eq_preimage_Ici`.  Unconditionally: `rankTail_zero`, `rankTail_antitone`,
  `compl_rankTail`, `notMem_rankTail_succ` (a point leaves the tail just above its rank),
  `rankTail_diff_succ` (the successor loss at `η` is the fiber at `η`) and
  `rankTail_eq_iInter_of_isSuccPrelimit` (continuity at every successor-prelimit, `0` included;
  `rankTail_eq_iInter_of_isSuccLimit` at limits).  Under `r x < ω₁` for all `x` and countable
  fibers below `ω₁`, each lemma assuming only what it uses: countable complements below `ω₁`
  (`rankTail_compl_countable`, fibers only), countable losses (`rankTail_loss_countable`), no
  point in every tail below `ω₁` (`biInter_rankTail_eq_empty`, rank bound only), empty tails from
  `ω₁` on (`rankTail_eq_empty_of_omega1_le`, rank bound only), `#X ≤ ℵ₁`
  (`mk_le_aleph_one_of_countable_fibers`), `#X = ℵ₁` for uncountable `X`
  (`mk_eq_aleph_one_of_countable_fibers`), and nonempty losses cofinal below `ω₁` iff `X` is
  uncountable (`rankTail_cofinal_losses_iff`).
* **Least level of a cover.**  `leastLevel Q x = sInf {α | x ∈ Q α}`.  With no hypothesis on `Q`:
  `leastLevel_le_of_mem`, and `leastLevel_mem_of_exists` for a point lying in some `Q α`.  Under
  the explicit covering hypothesis `⋃ α < ω₁, Q α = univ` (without it a point in no `Q α` gets
  level `sInf ∅ = 0`): `leastLevel_mem`, `leastLevel_lt_omega1`, `setOf_leastLevel_eq_subset`,
  `countable_fibers_leastLevel` (countable members below `ω₁` give countable fibers), and
  `rankTail_leastLevel`: the tail at `η` is the complement of `⋃ α < η, Q α`.  So a cover by
  countable sets feeds the rank-tail lemmas.
-/

@[expose] public section

universe u v w

open Cardinal Ordinal Set

namespace InfinitaryLogic

/-! ### Cantor space -/

/-! ### Suprema of countably many countable ordinals -/

/-! ### Rank and countability -/

variable {X : Type u}

/-! ### Countable complements from successor losses -/

/-- **Countable complements from countable successor losses and limit continuity.**  No
monotonicity of `D` is assumed; the limit hypothesis is necessary. -/
theorem compl_countable_of_loss (D : Ordinal.{0} → Set X) (h0 : D 0 = Set.univ)
    (hsucc : ∀ ξ, ξ < Ordinal.omega 1 → (D ξ \ D (ξ + 1)).Countable)
    (hlim : ∀ l, Order.IsSuccLimit l → l < Ordinal.omega 1 → (⋂ ξ < l, D ξ) ⊆ D l) :
    ∀ β, β < Ordinal.omega 1 → (D β)ᶜ.Countable := by
  intro β
  induction β using WellFoundedLT.induction with
  | _ β ih =>
    intro hβ
    rcases Ordinal.zero_or_succ_or_isSuccLimit β with rfl | ⟨ξ, rfl⟩ | hl
    · rw [h0, Set.compl_univ]
      exact Set.countable_empty
    · have hξ : ξ < Ordinal.omega 1 := lt_trans (Order.lt_succ ξ) hβ
      refine ((ih ξ (Order.lt_succ ξ) hξ).union (hsucc ξ hξ)).mono fun x hx => ?_
      rw [Order.succ_eq_add_one] at hx
      by_cases hxξ : x ∈ D ξ
      · exact Or.inr ⟨hxξ, hx⟩
      · exact Or.inl hxξ
    · refine (Set.Countable.biUnion (setCountable_Iio_of_lt_omega1 β hβ) fun ξ hξ =>
        ih ξ hξ (lt_trans hξ hβ)).mono fun x hx => ?_
      by_contra hall
      apply hx
      apply hlim β hl hβ
      refine Set.mem_iInter₂.mpr fun ξ hξ => ?_
      by_contra hxξ
      exact hall (Set.mem_iUnion₂.mpr ⟨ξ, hξ, hxξ⟩)

/-! ### Exhaustion by domains: cardinality exactly `ℵ₁` -/

/-! ### Separation by an isolating observation

`Sat : F → X → Prop` is an abstract satisfaction relation between observations and points, and
`φ` **isolates** `q` when `∀ x, Sat φ x ↔ x = q`.  No logic, order on `X`, topology or
countability enters `notMem_of_isolating_of_uniform`, `lt_index_of_isolating_of_antitone`,
`lt_rank_of_isolating_of_antitone` or `stage_lt_rank_of_isolating`.

* **Rank convention.**  Agreement at a stage `η` is for observations of rank **at most** `η`
  (`rank φ ≤ η` in `exists_countable_strict_stage_bound_of_isolation`, as in `EquivQRω`), and the
  strict exclusion happens at the isolating observation's own rank.  Under the convention
  "agreement for ranks strictly below `η`", the bound **at** `rank φ` (the conclusion of
  `stage_lt_rank_of_isolating`) is lost: an isolating observation of rank exactly `η` need not
  agree on the domain at `η`.  A countable strict bound as in
  `exists_countable_strict_stage_bound_of_isolation` still holds there, with `θ := rank φ + 1`,
  but it needs agreement and nonsingletonness at that later stage.
* **What the bound is.**  It is the rank of a *chosen* isolating observation, so it depends on
  that choice.  It is not an internal Scott rank, and it is not an attained stage: attainment of
  a greatest stage needs further closure hypotheses and is `exists_greatest_stage_lt_omega1` in
  `OrdinalUtil`.
* **Nonsingletonness is essential.**  With `D = {q}` and `Sat φ x := x = q`, isolation and
  agreement hold but `q ∈ D`; neither nonemptiness of `D` nor `Nontrivial X` can replace
  `D.Nontrivial`.
* **No countability of exceptional classes** (complements, losses or fibers of the domains) is
  assumed anywhere.
* **Vacuity on countable spaces.**  The hypotheses of
  `exists_countable_strict_stage_bound_of_isolation` imply that `X` is uncountable (countably
  many countable bounds have a countable supremum, and the domain there is nonempty), so it
  applies to a countable `X` only vacuously; the other two statements are not vacuous on finite
  spaces.
* **Exhaustion.**  Under antitonicity, `∀ η, q ∈ D η → η < θ` is equivalent to `q ∉ D θ`, so the
  conclusion of `exists_countable_strict_stage_bound_of_isolation` is the "every point leaves"
  premise of `mk_le_aleph_one_of_domains` and `mk_eq_aleph_one_of_domains`.

The application with `Sat` the satisfaction of `Lω₁ω` sentences on a presentation of
isomorphism classes, isolated by Scott sentences, and `rank` the quantifier rank, is
`IsolatedPresentation.exists_countable_strict_stage_bound` in `Descriptive/ScottDefinability`;
Scott theory enters there, through the isolation hypothesis only.

The separation bounds were offered for upstreaming by a consumer of this library. -/

/-! ### Rank tails -/

/-! ### The least level of a cover -/

end InfinitaryLogic
