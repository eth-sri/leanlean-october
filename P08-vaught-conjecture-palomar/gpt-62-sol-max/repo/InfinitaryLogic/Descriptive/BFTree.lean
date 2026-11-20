/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Descriptive.KleeneBrouwer
public import InfinitaryLogic.OrdinalUtil
public import InfinitaryLogic.Descriptive.SatisfactionBorel
public import InfinitaryLogic.Scott.BackAndForth
public import Mathlib.SetTheory.Cardinal.Aleph
public import Architect
public import InfinitaryLogic.Descriptive.StructureIsoSetoid
public import Mathlib.Basic.Finite.Sum

@[expose] public section

universe u v

namespace FirstOrder.Language

open Descriptive KleeneBrouwer Structure MeasureTheory

variable {L : Language.{u, v}} [L.IsRelational]

/-- `CodeBFEquiv α c d`: the empty tuples of the structures coded by `c` and `d` are
`α`-back-and-forth equivalent. -/
def CodeBFEquiv (α : Ordinal.{0}) (c d : StructureSpace L) : Prop :=
  @BFEquiv L ℕ c.toStructure ℕ d.toStructure α 0 Fin.elim0 Fin.elim0

variable (L) in
/-- **Back-and-forth equivalence at level `η`** on all codes: `CodeBFEquiv η`, an equivalence
relation by reflexivity, symmetry and transitivity of `BFEquiv`. -/
def codeBFEquivSetoid (η : Ordinal.{0}) : Setoid (StructureSpace L) where
  r := CodeBFEquiv η
  iseqv :=
    { refl := fun c ↦ @BFEquiv.refl L ℕ c.toStructure 0 η Fin.elim0
      symm := fun {c d} h ↦ @BFEquiv.symm L ℕ c.toStructure ℕ d.toStructure 0 η
        Fin.elim0 Fin.elim0 h
      trans := fun {c d e} h₁ h₂ ↦ @BFEquiv.trans L ℕ c.toStructure ℕ d.toStructure
        ℕ e.toStructure (n := 0) (α := η) (a := Fin.elim0) (b := Fin.elim0) (c := Fin.elim0)
        h₁ h₂ }

/-- The left tuple of a node: position `2 i` holds `i` (element `i` of the left structure enters
the domain), position `2 i + 1` holds the node's entry (the left answer to element `i` of the
right structure). -/
def bfLeft (s : List ℕ) : Fin s.length → ℕ :=
  fun j ↦ if j.val % 2 = 0 then j.val / 2 else s[j.val]

/-- The right tuple of a node: position `2 i` holds the node's entry (the right answer to
element `i` of the left structure), position `2 i + 1` holds `i` (element `i` of the right
structure enters the range). -/
def bfRight (s : List ℕ) : Fin s.length → ℕ :=
  fun j ↦ if j.val % 2 = 0 then s[j.val] else j.val / 2

/-- On a prefix, the decoded tuples are restrictions. -/
private theorem tuple_prefix (move : ℕ → ℕ → ℕ) {s t : List ℕ} (hst : s <+: t) :
    (fun j : Fin t.length => move j.val t[j.val]) ∘ Fin.castLE hst.length_le =
      fun j : Fin s.length => move j.val s[j.val] := by
  funext j
  exact congrArg (move j.val) (hst.getElem j.2).symm

private theorem bfLeft_comp_castLE {s t : List ℕ} (hst : s <+: t) :
    bfLeft t ∘ Fin.castLE hst.length_le = bfLeft s :=
  tuple_prefix (fun j x => if j % 2 = 0 then j / 2 else x) hst

private theorem bfRight_comp_castLE {s t : List ℕ} (hst : s <+: t) :
    bfRight t ∘ Fin.castLE hst.length_le = bfRight s :=
  tuple_prefix (fun j x => if j % 2 = 0 then x else j / 2) hst

private theorem tuple_snoc (move : ℕ → ℕ → ℕ) (s : List ℕ) (x : ℕ) :
    (fun j : Fin (s ++ [x]).length => move j.val (s ++ [x])[j.val]) =
      Fin.snoc (fun j : Fin s.length => move j.val s[j.val]) (move s.length x) ∘ Fin.cast (by simp) := by
  funext j
  obtain ⟨j, hj⟩ := j
  have hj' : j < s.length + 1 := by simp_all
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hlt | rfl
  · have : (Fin.cast (by simp) ⟨j, hj⟩ : Fin (s.length + 1)) = Fin.castSucc ⟨j, hlt⟩ := rfl
    simp only [Function.comp_apply, this, Fin.snoc_castSucc]
    simp_all
  · have : (Fin.cast (by simp) ⟨s.length, hj⟩ : Fin (s.length + 1)) = Fin.last _ := rfl
    simp_all

private theorem bfLeft_append_singleton (s : List ℕ) (x : ℕ) :
    bfLeft (s ++ [x]) = Fin.snoc (bfLeft s)
      (if s.length % 2 = 0 then s.length / 2 else x) ∘ Fin.cast (by simp) :=
  tuple_snoc (fun j x => if j % 2 = 0 then j / 2 else x) s x

private theorem bfRight_append_singleton (s : List ℕ) (x : ℕ) :
    bfRight (s ++ [x]) = Fin.snoc (bfRight s)
      (if s.length % 2 = 0 then x else s.length / 2) ∘ Fin.cast (by simp) :=
  tuple_snoc (fun j x => if j % 2 = 0 then x else j / 2) s x

/-- The nodes of the forced back-and-forth tree: the lists whose decoded left and right tuples
have the same atomic type (all equality and relation atoms agree). -/
def bfNodes (c d : StructureSpace L) : Set (List ℕ) :=
  {s | @SameAtomicType L ℕ c.toStructure s.length ℕ d.toStructure (bfLeft s) (bfRight s)}

/-- The node set is closed under one-step prefixes: restricting a partial isomorphism keeps the
atomic type (`SameAtomicType.relabel`). -/
theorem bfNodes_prefix (c d : StructureSpace L) ⦃s : List ℕ⦄ ⦃a : ℕ⦄
    (h : s ++ [a] ∈ bfNodes c d) : s ∈ bfNodes c d := by
  have hst : s <+: s ++ [a] := List.prefix_append s [a]
  have := @SameAtomicType.relabel L ℕ c.toStructure ℕ d.toStructure _ _ _ _ h
    (Fin.castLE hst.length_le)
  rwa [bfLeft_comp_castLE hst, bfRight_comp_castLE hst] at this

/-- **The forced back-and-forth tree** of a pair of codes. -/
def bfTree (c d : StructureSpace L) : tree ℕ :=
  ⟨bfNodes c d, fun _ _ h ↦ bfNodes_prefix c d h⟩

/-- Membership in the tree is atomic agreement of the decoded tuples. -/
theorem mem_bfTree_iff {c d : StructureSpace L} {s : List ℕ} :
    s ∈ bfTree c d ↔
      @SameAtomicType L ℕ c.toStructure s.length ℕ d.toStructure (bfLeft s) (bfRight s) :=
  Iff.rfl

private theorem mem_bfTree_of_bfEquiv {c d : StructureSpace L} {α : Ordinal.{0}}
    {s : List ℕ}
    (h : @BFEquiv L ℕ c.toStructure ℕ d.toStructure α s.length (bfLeft s) (bfRight s)) :
    s ∈ bfTree c d :=
  (@BFEquiv.zero L ℕ c.toStructure ℕ d.toStructure _ _ _).mp
    (@BFEquiv.monotone L ℕ c.toStructure ℕ d.toStructure _ _ _ zero_le _ _ h)

private theorem bfLeft_nil : bfLeft [] = Fin.elim0 := by trivial

private theorem bfRight_nil : bfRight [] = Fin.elim0 := by trivial

/-- `CodeBFEquiv` is back-and-forth equivalence at the root node. -/
private theorem codeBFEquiv_iff_root {α : Ordinal.{0}} {c d : StructureSpace L} :
    CodeBFEquiv α c d ↔ @BFEquiv L ℕ c.toStructure ℕ d.toStructure α ([] : List ℕ).length
      (bfLeft []) (bfRight []) := by
  rw [bfLeft_nil, bfRight_nil]
  rfl

/-- **The root is a node iff the empty tuples agree atomically**, i.e. iff every nullary
relation symbol has the same truth value in both structures. -/
theorem nil_mem_bfTree_iff {c d : StructureSpace L} :
    [] ∈ bfTree c d ↔ CodeBFEquiv 0 c d := by
  rw [codeBFEquiv_iff_root, @BFEquiv.zero L ℕ c.toStructure ℕ d.toStructure]
  rfl

/-- One atomic condition at fixed tuples is clopen on the pair space. -/
private theorem isClopen_setOf_holds_iff {n : ℕ} (a b : Fin n → ℕ) (idx : L.AtomicIdx n) :
    IsClopen {p : StructureSpace L × StructureSpace L |
      @AtomicIdx.holds L ℕ p.1.toStructure n idx a ↔
        @AtomicIdx.holds L ℕ p.2.toStructure n idx b} := by
  cases idx with
  | eq i j =>
    by_cases h : (a i = a j ↔ b i = b j) <;>
      simp [AtomicIdx.holds, h, isClopen_empty, isClopen_univ]
  | rel R f =>
    let g : StructureSpace L × StructureSpace L → Bool × Bool :=
      fun p ↦ (p.1 ⟨⟨_, R⟩, a ∘ f⟩, p.2 ⟨⟨_, R⟩, b ∘ f⟩)
    have hg : Continuous g :=
      by fun_prop
    exact (isClopen_discrete {x : Bool × Bool | x.1 = true ↔ x.2 = true}).preimage hg

/-- The node condition is the intersection, over all atoms, of the atomic conditions. -/
private theorem setOf_mem_bfTree_eq_iInter (s : List ℕ) :
    {p : StructureSpace L × StructureSpace L | s ∈ bfTree p.1 p.2} =
      ⋂ idx : L.AtomicIdx s.length, {p | @AtomicIdx.holds L ℕ p.1.toStructure _ idx (bfLeft s) ↔
        @AtomicIdx.holds L ℕ p.2.toStructure _ idx (bfRight s)} := by aesop

/-- **Node conditions are closed**, for every relational `L`: the set of code pairs whose tree
contains `s` is an intersection of clopen atomic conditions.  It need not be clopen, and the
assignment `p ↦ bfTree p.1 p.2` need not be continuous, when there are infinitely many relation
symbols (compare `isClopen_setOf_mem_bfTree`). -/
theorem isClosed_setOf_mem_bfTree (s : List ℕ) :
    IsClosed {p : StructureSpace L × StructureSpace L | s ∈ bfTree p.1 p.2} := by
  rw [setOf_mem_bfTree_eq_iInter]
  exact isClosed_iInter fun idx ↦ (isClopen_setOf_holds_iff _ _ idx).isClosed

/-- The left sequence along a branch `z`: even positions enumerate the left structure. -/
private def seqLeft (z : ℕ → ℕ) (j : ℕ) : ℕ := if j % 2 = 0 then j / 2 else z j

/-- The right sequence along a branch `z`: odd positions enumerate the right structure. -/
private def seqRight (z : ℕ → ℕ) (j : ℕ) : ℕ := if j % 2 = 0 then z j else j / 2

private theorem seqLeft_two_mul (z : ℕ → ℕ) (i : ℕ) : seqLeft z (2 * i) = i := by
  simp [seqLeft]

private theorem seqLeft_two_mul_add_one (z : ℕ → ℕ) (i : ℕ) :
    seqLeft z (2 * i + 1) = z (2 * i + 1) := by
  simp [seqLeft, Nat.add_mod]

private theorem seqRight_two_mul (z : ℕ → ℕ) (i : ℕ) : seqRight z (2 * i) = z (2 * i) := by
  simp [seqRight]

private theorem seqRight_two_mul_add_one (z : ℕ → ℕ) (i : ℕ) :
    seqRight z (2 * i + 1) = i := by
  simp [seqRight, Nat.add_mod]
  omega

private theorem bfLeft_ofFn (z : ℕ → ℕ) (n : ℕ)
    (j : Fin (List.ofFn fun i : Fin n ↦ z i).length) :
    bfLeft (List.ofFn fun i : Fin n ↦ z i) j = seqLeft z j := by
  simp [bfLeft, seqLeft]

private theorem bfRight_ofFn (z : ℕ → ℕ) (n : ℕ)
    (j : Fin (List.ofFn fun i : Fin n ↦ z i).length) :
    bfRight (List.ofFn fun i : Fin n ↦ z i) j = seqRight z j := by
  simp [bfRight, seqRight]

/-- Along a branch, every atom at every finite set of positions agrees: relabel a node long
enough to contain the positions. -/
private theorem holds_seq_of_branch {c d : StructureSpace L} {z : ℕ → ℕ}
    (hz : ∀ n, List.ofFn (fun i : Fin n ↦ z i) ∈ bfTree c d) {l : ℕ} (g : Fin l → ℕ)
    (idx : L.AtomicIdx l) :
    @AtomicIdx.holds L ℕ c.toStructure l idx (seqLeft z ∘ g) ↔
      @AtomicIdx.holds L ℕ d.toStructure l idx (seqRight z ∘ g) := by
  obtain ⟨N, hN⟩ : ∃ N, ∀ k, g k < N :=
    ⟨Finset.univ.sup g + 1, fun k ↦ Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ k))⟩
  have ht : ∀ k, g k < (List.ofFn fun i : Fin N ↦ z i).length := by simp_all
  let σ : Fin l → Fin (List.ofFn fun i : Fin N ↦ z i).length := fun k ↦ ⟨g k, ht k⟩
  have h := @SameAtomicType.relabel L ℕ c.toStructure ℕ d.toStructure _ _ _ _ (hz N) σ idx
  have hl : bfLeft (List.ofFn fun i : Fin N ↦ z i) ∘ σ = seqLeft z ∘ g :=
    funext fun k ↦ bfLeft_ofFn z N (σ k)
  have hr : bfRight (List.ofFn fun i : Fin N ↦ z i) ∘ σ = seqRight z ∘ g :=
    funext fun k ↦ bfRight_ofFn z N (σ k)
  simp_all

/-- **A branch gives an isomorphism**: `m ↦ z (2 m)`.  Equality atoms give injectivity, and
surjectivity by comparing position `2 n + 1` (where the right structure offers `n`) with
position `2 z(2 n + 1)`; relation atoms at long enough nodes give preservation. -/
private theorem nonempty_equiv_of_branch {c d : StructureSpace L} {z : ℕ → ℕ}
    (hz : ∀ n, List.ofFn (fun i : Fin n ↦ z i) ∈ bfTree c d) :
    Nonempty (@Language.Equiv L ℕ ℕ c.toStructure d.toStructure) := by
  have heq : ∀ i j, seqLeft z i = seqLeft z j ↔ seqRight z i = seqRight z j :=
    fun i j ↦ holds_seq_of_branch hz ![i, j] (.eq 0 1)
  let e : ℕ → ℕ := fun m ↦ z (2 * m)
  have hinj : Function.Injective e := by
    intro m m' hm
    have := (heq (2 * m) (2 * m')).mpr (by simpa [seqRight_two_mul] using hm)
    simpa [seqLeft_two_mul] using this
  have hsurj : Function.Surjective e := by
    intro n
    refine ⟨z (2 * n + 1), ?_⟩
    have := (heq (2 * z (2 * n + 1)) (2 * n + 1)).mp
      (by simp_all [seqLeft_two_mul, seqLeft_two_mul_add_one])
    rwa [seqRight_two_mul, seqRight_two_mul_add_one] at this
  refine ⟨@Language.Equiv.mk L ℕ ℕ c.toStructure d.toStructure (Equiv.ofBijective e ⟨hinj, hsurj⟩)
    (fun f ↦ isEmptyElim f) (fun {l} R v ↦ ?_)⟩
  have h := holds_seq_of_branch hz (fun k ↦ 2 * v k) (.rel R id)
  have hl : seqLeft z ∘ (fun k ↦ 2 * v k) = v := funext fun k ↦ seqLeft_two_mul z (v k)
  have hr : seqRight z ∘ (fun k ↦ 2 * v k) = e ∘ v := funext fun k ↦ seqRight_two_mul z (v k)
  simp only [AtomicIdx.holds, Function.comp_id, hl, hr] at h
  tauto

omit [L.IsRelational] in
/-- An isomorphism preserves the atomic type of every tuple.  The structures are implicit
arguments, not instances, so that two structures on the same carrier can be supplied.

This is the special case `(SameAtomicType.map_equiv (Language.Equiv.refl L M) e).mpr
(SameAtomicType.refl a)` of the library lemma `SameAtomicType.map_equiv`, which lives in
`Scott/AtomicDiagram.lean`, inside this module's minimal import closure; the proof is that one
line.  The helper is kept only to fix the structures as implicit arguments. -/
private theorem sameAtomicType_comp_equiv {M N : Type*} {iM : L.Structure M}
    {iN : L.Structure N} (e : @Language.Equiv L M N iM iN) {n : ℕ} (a : Fin n → M) :
    @SameAtomicType L M iM n N iN a (e.toEquiv ∘ a) := by
  let _ := iM
  let _ := iN
  exact (SameAtomicType.map_equiv (Language.Equiv.refl L M) e).mpr (SameAtomicType.refl a)

/-- **An isomorphism gives a branch**: `z (2 i) = e i` answers element `i` of the left
structure, `z (2 i + 1) = e⁻¹ i` answers element `i` of the right structure; every initial
segment decodes a tuple and its image under `e`. -/
private theorem branch_of_equiv {c d : StructureSpace L}
    (e : @Language.Equiv L ℕ ℕ c.toStructure d.toStructure) :
    ∃ z : ℕ → ℕ, ∀ n, List.ofFn (fun i : Fin n ↦ z i) ∈ bfTree c d := by
  let f : ℕ ≃ ℕ := @Language.Equiv.toEquiv L ℕ ℕ c.toStructure d.toStructure e
  set z : ℕ → ℕ := fun j ↦ if j % 2 = 0 then f (j / 2) else f.symm (j / 2) with hz
  refine ⟨z, fun n ↦ ?_⟩
  have hR : ∀ j, seqRight z j = f (seqLeft z j) := by
    grind [seqLeft, seqRight]
  have hfun : bfRight (List.ofFn fun i : Fin n ↦ z i) =
      f ∘ bfLeft (List.ofFn fun i : Fin n ↦ z i) := by
    funext j
    rw [Function.comp_apply, bfLeft_ofFn, bfRight_ofFn, hR]
  grind [mem_bfTree_iff, sameAtomicType_comp_equiv]

/-- **Branches are isomorphisms**: the forced back-and-forth tree of `c` and `d` has an infinite
branch iff the coded structures are isomorphic.  Every element of both structures is covered:
the left structure's element `i` enters at step `2 i`, the right structure's at step
`2 i + 1`. -/
theorem hasInfiniteBranch_bfTree_iff (c d : StructureSpace L) :
    HasInfiniteBranch (bfTree c d) ↔ (structureIsoSetoid L).r c d := by
  rw [hasInfiniteBranch_iff_exists_seq]
  constructor
  · rintro ⟨z, hz⟩
    exact nonempty_equiv_of_branch hz
  · rintro ⟨e⟩
    exact branch_of_equiv e

omit [L.IsRelational] in
/-- Reindexing along a cast of the tuple length does not change `BFEquiv`.  The structures are
implicit arguments, not instances. -/
private theorem bfEquiv_comp_cast {M N : Type*} {iM : L.Structure M} {iN : L.Structure N}
    {α : Ordinal.{0}} {n m : ℕ} (h : n = m) (a : Fin m → M) (b : Fin m → N) :
    @BFEquiv L M iM N iN α n (a ∘ Fin.cast h) (b ∘ Fin.cast h) ↔
      @BFEquiv L M iM N iN α m a b := by aesop

/-- `BFEquiv` at the tuples of a one-step extension is `BFEquiv` at the extended tuples. -/
private theorem bfEquiv_append_singleton_iff {c d : StructureSpace L} {α : Ordinal.{0}}
    (s : List ℕ) (x : ℕ) :
    @BFEquiv L ℕ c.toStructure ℕ d.toStructure α (s ++ [x]).length (bfLeft (s ++ [x]))
      (bfRight (s ++ [x])) ↔
    @BFEquiv L ℕ c.toStructure ℕ d.toStructure α (s.length + 1)
      (Fin.snoc (bfLeft s) (if s.length % 2 = 0 then s.length / 2 else x))
      (Fin.snoc (bfRight s) (if s.length % 2 = 0 then x else s.length / 2)) := by simp_all [bfLeft_append_singleton, bfRight_append_singleton, bfEquiv_comp_cast]

/-- **Node rank comparison**: if the decoded tuples of a node are `α`-back-and-forth
equivalent, the node has rank at least `α`, with no offset.  Each tree step is one move: at
even length the forth property answers the next left element, at odd length the back property
answers the next right element. -/
theorem le_rank_bfTree_of_bfEquiv {c d : StructureSpace L} [WellFounded (extBelow (bfTree c d))]
    {α : Ordinal.{0}} {s : List ℕ} (hs : s ∈ bfTree c d)
    (h : @BFEquiv L ℕ c.toStructure ℕ d.toStructure α s.length (bfLeft s) (bfRight s)) :
    α ≤ WellFounded.rank (extBelow (bfTree c d)) ⟨s, hs⟩ := by
  induction α using Ordinal.limitRecOn generalizing s with
  | zero => exact zero_le
  | add_one β ih =>
    rw [← Order.succ_eq_add_one] at h ⊢
    have hex : ∃ x, @BFEquiv L ℕ c.toStructure ℕ d.toStructure β (s ++ [x]).length
        (bfLeft (s ++ [x])) (bfRight (s ++ [x])) := by
      by_cases hk : s.length % 2 = 0
      · obtain ⟨y, hy⟩ :=
          @BFEquiv.forth L ℕ c.toStructure ℕ d.toStructure _ _ _ _ h (s.length / 2)
        exact ⟨y, (bfEquiv_append_singleton_iff s y).mpr (by simp_all)⟩
      · obtain ⟨y, hy⟩ :=
          @BFEquiv.back L ℕ c.toStructure ℕ d.toStructure _ _ _ _ h (s.length / 2)
        exact ⟨y, (bfEquiv_append_singleton_iff s y).mpr (by simp_all)⟩
    obtain ⟨x, hx⟩ := hex
    have hmem : s ++ [x] ∈ bfTree c d := mem_bfTree_of_bfEquiv hx
    have hrel : extBelow (bfTree c d) ⟨s ++ [x], hmem⟩ ⟨s, hs⟩ :=
      ⟨List.prefix_append s [x], fun he ↦ by simp_all⟩
    exact Order.succ_le_of_lt ((ih hmem hx).trans_lt (WellFounded.rank_lt_of_rel hrel))
  | limit β hβ ih =>
    by_contra hlt
    have hsucc := hβ.succ_lt (not_le.mp hlt)
    exact (Order.lt_succ _).not_ge (ih _ hsucc hs
      (@BFEquiv.monotone L ℕ c.toStructure ℕ d.toStructure _ _ _ hsucc.le _ _ h))

/-- **Root rank comparison**: if the empty tuples are `α`-back-and-forth equivalent, then
`α < treeHeight (bfTree c d)`.  Root membership is obtained from atomic agreement of the empty
tuples (`nil_mem_bfTree_iff`), not assumed; the strict inequality is the `succ` in
`treeHeight`. -/
theorem lt_treeHeight_bfTree_of_codeBFEquiv {c d : StructureSpace L}
    [WellFounded (extBelow (bfTree c d))] {α : Ordinal.{0}} (h : CodeBFEquiv α c d) :
    α < treeHeight (bfTree c d) := by
  have hnil : [] ∈ bfTree c d := nil_mem_bfTree_iff.mpr
    (@BFEquiv.monotone L ℕ c.toStructure ℕ d.toStructure _ _ _ zero_le _ _ h)
  have hle := le_rank_bfTree_of_bfEquiv hnil (codeBFEquiv_iff_root.mp h)
  calc α < Order.succ (WellFounded.rank (extBelow (bfTree c d)) ⟨[], hnil⟩) :=
        Order.lt_succ_of_le hle
    _ ≤ treeHeight (bfTree c d) :=
        Ordinal.le_iSup (fun x : ↥(bfTree c d) ↦
          Order.succ (WellFounded.rank (extBelow (bfTree c d)) x)) ⟨[], hnil⟩

end FirstOrder.Language
