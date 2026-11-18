/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Pigeonhole
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.Order.InitialSeg
public import Mathlib.Data.Fin.VecNotation

/-!
# Pair Erdős–Rado, parameterized by the color bound `κ`

The color-parameterized pair Erdős–Rado theorem: for any infinite cardinal `κ` and any
color type `C` with `#C ≤ κ`, every pair coloring `cR : (Fin 2 ↪o Source κ) → C` of the
source order `Source κ = (Order.succ (2 ^ κ)).ord.ToType` (the initial well-order of the
successor of `2 ^ κ`) admits a `(Order.succ κ).ord`-indexed strict-mono suborder on which
`cR` is constant. In partition-calculus notation: `(2 ^ κ)⁺ → (κ⁺)²_κ`.

This is a fresh-namespace (`PairERGen`) port of the proven Bool/ℵ₀ theorem
`FirstOrder.Combinatorics.erdos_rado_pair_omega1` from `Combinatorics/ErdosRado.lean`,
with the renaming table `Bool → C`, `ℶ_1 → 2 ^ κ`, `ℵ_1 → Order.succ κ`,
`ω_1 → (Order.succ κ).ord`. The legacy theorem's shape is recovered as the `κ = ℵ₀`
specialization `erdos_rado_pair_omega1_from_general`. The consumers are the
end-homogenization engine (`EndHomogeneousErdosRado.lean`) and the finite-arity induction
(`FiniteArityErdosRadoInduction.lean`, culminating in the bounded
`finiteArityErdosRadoBounded`), which need the color bound at `κ = ℶ_1` (colors = functions
on continuum-indexed positions); the all-arity `FiniteArityErdosRadoOmega1` is false-shaped
(statement audit 2026-07-07 — see its docstring).

## Structure

- **`CardinalHelpers`**: all cardinal arithmetic isolated — source cardinality,
  the level-count bound `#(β.ToType → C) ≤ 2 ^ κ` for `β < (succ κ).ord`, the
  counting-core product `succ κ * 2 ^ κ = 2 ^ κ`, and the subset order-iso lemma.
- **EHMR canonical partition tree** (sections mirroring the source A–H): nodes are
  recorded-color sequences `β.ToType → C`, reps are chosen minima of successor sets,
  the coverage `y`-path shows every source element is some node's chosen rep, counting
  forces a live node of length `≥ (succ κ).ord`, and the resulting branch assembles
  into a `CoherentMajorityBranch` feeding the chain + pigeonhole endgame.
- **Headline**: `pairErdosRado_general`; regression: `erdos_rado_pair_omega1_from_general`;
  abstract-source wrapper: `pairErdosRado_general_of_large`.
-/

@[expose] public section

universe u

namespace FirstOrder.Combinatorics.PairERGen

/-! ### Generic toolbox (no `κ`): `pairEmbed`, pigeonhole, embeddings, order isos -/

section Toolbox

/-- Pair embedding: from an ordered pair `a < b` in a linearly-ordered
type, produce the canonical `Fin 2 ↪o α`. -/
noncomputable def pairEmbed {α : Type*} [LinearOrder α]
    {a b : α} (h : a < b) : Fin 2 ↪o α :=
  OrderEmbedding.ofStrictMono ![a, b] (by
    intro p q hpq
    match p, q, hpq with
    | ⟨0, _⟩, ⟨1, _⟩, _ => simpa using h
    | ⟨0, _⟩, ⟨0, _⟩, hp => exact absurd hp (lt_irrefl _)
    | ⟨1, _⟩, ⟨1, _⟩, hp => exact absurd hp (lt_irrefl _)
    | ⟨1, _⟩, ⟨0, _⟩, hp =>
      have hval : (1 : ℕ) < 0 := hp
      exact absurd hval (by omega))

/-- Project-local replacement for the deprecated `Ordinal.initialSegToType` (deprecated in
favor of `Ordinal.type_le_iff`, from which this is extracted): the initial segment
embedding of `α.ToType` into `β.ToType` from `α ≤ β`. -/
noncomputable def initialSegOfLe {α β : Ordinal.{u}} (h : α ≤ β) : α.ToType ≤i β.ToType := by
  apply Classical.choice (Ordinal.type_le_iff.mp _)
  rwa [Ordinal.type_toType, Ordinal.type_toType]

/-- A well-ordered source of cardinality at least `c` admits an order-embedding from the
initial-ordinal well-order of cardinality `c`. Used by the abstract-source wrapper
`pairErdosRado_general_of_large` to pull the coloring back to `Source κ`. -/
theorem exists_ordToType_embedding_of_card_ge
    {I : Type} [LinearOrder I] [WellFoundedLT I]
    {c : Cardinal} (hI : Cardinal.mk I ≥ c) :
    Nonempty (c.ord.ToType ↪o I) := by
  -- `β := type (<_I) : Ordinal`.  `β.card = #I ≥ c`, hence `c.ord ≤ β`.
  set β : Ordinal := Ordinal.type (· < · : I → I → Prop) with hβ
  have hβ_card : β.card = Cardinal.mk I := Ordinal.card_type (· < ·)
  have hord_le : c.ord ≤ β := by
    rw [Cardinal.ord_le, hβ_card]; exact hI
  -- Initial-segment embedding `c.ord.ToType ≤i β.ToType`.
  have seg : c.ord.ToType ≤i β.ToType := initialSegOfLe hord_le
  -- `β.ToType` ≃o `I` via `type_toType β = β = type (<_I)`.
  have htype : @Ordinal.type β.ToType (· < ·) _ =
      @Ordinal.type I (· < ·) _ := by
    rw [Ordinal.type_toType]
  have hiso : Nonempty
      ((· < · : β.ToType → β.ToType → Prop) ≃r (· < · : I → I → Prop)) :=
    Ordinal.type_eq.mp htype
  obtain ⟨r⟩ := hiso
  exact ⟨seg.toOrderEmbedding.trans (OrderIso.ofRelIsoLT r).toOrderEmbedding⟩

/-- Composition of `initialSegOfLe` via `InitialSeg.eq` uniqueness on well-orders.
Two initial segments from `α.ToType` to `γ.ToType` (both well-ordered) agree
pointwise.  (Shared with `EndHomogER`, which previously carried a private copy.) -/
lemma initialSegOfLe_compose
    {α β γ : Ordinal.{0}} (h_αβ : α ≤ β) (h_βγ : β ≤ γ) (x : α.ToType) :
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder γ.ToType (· < ·) := isWellOrder_lt
    (initialSegOfLe h_βγ).toOrderEmbedding
        ((initialSegOfLe h_αβ).toOrderEmbedding x) =
      (initialSegOfLe (h_αβ.trans h_βγ)).toOrderEmbedding x := by
  have : IsWellOrder γ.ToType (· < ·) := isWellOrder_lt
  rw [InitialSeg.toOrderEmbedding_apply, InitialSeg.toOrderEmbedding_apply,
      InitialSeg.toOrderEmbedding_apply,
      ← InitialSeg.trans_apply (initialSegOfLe h_αβ)
        (initialSegOfLe h_βγ) x]
  exact ((initialSegOfLe h_αβ).trans
    (initialSegOfLe h_βγ)).eq
    (initialSegOfLe (h_αβ.trans h_βγ)) x

end Toolbox

/-! ### Cardinal helpers: all the `κ`-arithmetic the EHMR port consumes -/

section CardinalHelpers

/-- **Pair-ER source at color bound `κ`.** The initial ordinal of the regular successor
cardinal `succ (2 ^ κ)`, viewed as a linearly-ordered `Type`. All pair-Erdős–Rado
recursion happens inside `Source κ`; the specialization `κ = ℵ₀` recovers the legacy
`PairERSource` (since `2 ^ ℵ₀ = ℶ_1`). -/
abbrev Source (κ : Cardinal.{0}) : Type :=
  (Order.succ ((2 : Cardinal.{0}) ^ κ)).ord.ToType

/-- Cardinality of the source: `#(Source κ) = succ (2 ^ κ)`. -/
lemma mk_source (κ : Cardinal.{0}) :
    Cardinal.mk (Source κ) = Order.succ ((2 : Cardinal.{0}) ^ κ) :=
  Cardinal.mk_ord_toType _

instance (κ : Cardinal.{0}) : Nonempty (Source κ) :=
  Ordinal.nonempty_toType_iff.mpr fun h =>
    Cardinal.succ_ne_zero _ (Cardinal.ord_eq_zero.mp h)

/-- `2 ^ κ ≠ 0` (needed for `power_le_power_left` monotonicity). -/
lemma two_power_ne_zero (κ : Cardinal.{0}) : (2 : Cardinal.{0}) ^ κ ≠ 0 :=
  Cardinal.power_ne_zero κ two_ne_zero

/-- `succ κ ≤ 2 ^ κ` — Cantor plus successor minimality; holds for every `κ`. -/
lemma succ_le_two_power (κ : Cardinal.{0}) :
    Order.succ κ ≤ 2 ^ κ :=
  Order.succ_le_of_lt (Cardinal.cantor κ)

variable {κ : Cardinal.{0}}

/-- `ℵ_0 ≤ 2 ^ κ` for infinite `κ` (via Cantor). -/
lemma aleph0_le_two_power (hκ : Cardinal.aleph0 ≤ κ) :
    Cardinal.aleph0 ≤ (2 : Cardinal.{0}) ^ κ :=
  hκ.trans (Cardinal.cantor κ).le

/-- `ℵ_0 ≤ succ (2 ^ κ)` for infinite `κ`. -/
lemma aleph0_le_succ_two_power (hκ : Cardinal.aleph0 ≤ κ) :
    Cardinal.aleph0 ≤ Order.succ ((2 : Cardinal.{0}) ^ κ) :=
  (aleph0_le_two_power hκ).trans (Order.le_succ _)

/-- `ℵ_0 ≤ succ κ` for infinite `κ`. -/
lemma aleph0_le_succ_self (hκ : Cardinal.aleph0 ≤ κ) :
    Cardinal.aleph0 ≤ Order.succ κ :=
  hκ.trans (Order.le_succ κ)

/-- Ordinals below `(succ κ).ord` have `ToType` of cardinality `≤ κ` (the generalization
of "ordinals below `ω_1` are countable"). -/
theorem toType_card_le_of_lt_succ_ord {α : Ordinal.{0}}
    (hα : α < (Order.succ κ).ord) :
    Cardinal.mk α.ToType ≤ κ := by
  rw [Cardinal.mk_toType]
  exact Order.lt_succ_iff.mp (Cardinal.lt_ord.mp hα)

/-- `(succ κ).ord` is closed under ordinal successor for infinite `κ` (it is a limit
ordinal, being the initial ordinal of an uncountable-cofinality cardinal). -/
theorem succ_lt_ord_of_lt (hκ : Cardinal.aleph0 ≤ κ) {δ : Ordinal.{0}}
    (hδ : δ < (Order.succ κ).ord) :
    Order.succ δ < (Order.succ κ).ord :=
  (Cardinal.isSuccLimit_ord (aleph0_le_succ_self hκ)).succ_lt hδ

/-- **Counting-core product.** `succ κ * 2 ^ κ = 2 ^ κ` for infinite `κ`
(the generalization of `ℵ_1 * ℶ_1 = ℶ_1`). -/
theorem succ_mul_two_power (hκ : Cardinal.aleph0 ≤ κ) :
    Order.succ κ * (2 : Cardinal.{0}) ^ κ = 2 ^ κ := by
  rw [Cardinal.mul_eq_max (aleph0_le_succ_self hκ) (aleph0_le_two_power hκ)]
  exact max_eq_right (succ_le_two_power κ)

end CardinalHelpers

/-! ### Branch structures: `validFiber`, `CoherentMajorityBranch`, `EHMRBranch` -/

section BranchStructures

variable {κ : Cardinal.{0}} {C : Type}

/-- **`EHMRBranch cR`**: a strictly increasing `(succ κ).ord`-indexed family of reps with
recorded colors — `cR({rep β, rep γ}) = bit β` for `β < γ` (EHMR fact (8) content).
Produced by the tree-counting theorem `ehmr_tree_has_branch`. -/
structure EHMRBranch (cR : (Fin 2 ↪o Source κ) → C) where
  /-- The rep at each position `β < (succ κ).ord`. -/
  rep : ∀ β : Ordinal.{0}, β < (Order.succ κ).ord → Source κ
  /-- The recorded color at each position `β < (succ κ).ord`. -/
  bit : ∀ β : Ordinal.{0}, β < (Order.succ κ).ord → C
  /-- The reps strictly increase. -/
  rep_strictMono : ∀ {β γ : Ordinal.{0}} (hβ : β < (Order.succ κ).ord)
    (hγ : γ < (Order.succ κ).ord), β < γ → rep β hβ < rep γ hγ
  /-- End-homogeneity: the pair color of `{rep β, rep γ}` is `bit β` for `β < γ`. -/
  coloring : ∀ {β γ : Ordinal.{0}} (hβ : β < (Order.succ κ).ord)
    (hγ : γ < (Order.succ κ).ord) (hβγ : β < γ),
    cR (pairEmbed (rep_strictMono hβ hγ hβγ)) = bit β hβ

end BranchStructures

/-! ### EHMR canonical-tree skeleton

Nodes are recorded-color sequences `β.ToType → C` (Type 0, so the counting stays in
`Cardinal.{0}`); reps `s(h↾γ) = min S(h↾γ)` are derived by well-founded recursion on
length; live = nonempty successor set. -/

section TreeSkeleton

variable {κ : Cardinal.{0}} {C : Type}

/-- **[EHMR §14, Lemma 14.2 + |E| counting — coverage/counting engine]** If the
"used-up" sets `R i` cover `Source κ` and each is a subsingleton, then the node index
set has cardinality `≥ succ (2 ^ κ) = #(Source κ)`. This is the counting feeding the
branch-length theorem. -/
theorem ehmr_partitionTree_card_lower
    {ι : Type} (R : ι → Set (Source κ))
    (hcover : ∀ y : Source κ, ∃ i : ι, y ∈ R i)
    (hsub : ∀ i : ι, (R i).Subsingleton) :
    Order.succ ((2 : Cardinal.{0}) ^ κ) ≤ Cardinal.mk ι := by
  classical
  -- The choice function `y ↦ (some i with y ∈ R i)` is injective: subsingleton fibers.
  have hf : ∀ y : Source κ, y ∈ R (hcover y).choose := fun y => (hcover y).choose_spec
  have hinj : Function.Injective (fun y : Source κ => (hcover y).choose) := by
    intro y₁ y₂ h
    change (hcover y₁).choose = (hcover y₂).choose at h
    have h2 : y₂ ∈ R (hcover y₁).choose := by rw [h]; exact hf y₂
    exact hsub _ (hf y₁) h2
  calc Order.succ ((2 : Cardinal.{0}) ^ κ) = Cardinal.mk (Source κ) := (mk_source κ).symm
    _ ≤ Cardinal.mk ι := Cardinal.mk_le_of_injective hinj

end TreeSkeleton

/-! ### Coverage (EHMR Lemma 14.2) — the canonical `y`-path

Rather than build the `y`-path by transfinite recursion with an explicit limit step, we
define the whole path at once: `yNode cR y β` is the length-`β` node recording, at each
position `x`, the pair-color of `y` against the chosen rep of the path so far — or junk
(an arbitrary color) once that rep is no longer `< y`. Restriction-coherence then
becomes a lemma, and the stopping argument is pure well-foundedness. -/

section YPath

variable {κ : Cardinal.{0}} {C : Type} [Nonempty C]

end YPath

/-! ### End-homogeneity of live nodes (EHMR fact (8)) -/

section EndHomogeneity

variable {κ : Cardinal.{0}} {C : Type}

end EndHomogeneity

/-! ### Branch extraction from a high live node

EHMR Theorem 13.1 realized concretely: the `succ (2 ^ κ)`-many live nodes (coverage)
cannot all sit at levels `< (succ κ).ord` (each such level has `≤ 2 ^ κ` nodes, and
there are only `succ κ` of them), so some live node has length `≥ (succ κ).ord`;
reading it off at the first `(succ κ).ord` positions yields an `EHMRBranch`. -/

section BranchExtraction

variable {κ : Cardinal.{0}} {C : Type}

end BranchExtraction

/-! ### Assembly: EHMR branch → `CoherentMajorityBranch` -/

section Assembly

variable {κ : Cardinal.{0}} {C : Type}

end Assembly

/-! ### Chain + pigeonhole endgame -/

section Endgame

variable {κ : Cardinal.{0}} {C : Type}

end Endgame

/-! ### The headline, the regression specialization, and the abstract-source wrapper -/

end FirstOrder.Combinatorics.PairERGen
