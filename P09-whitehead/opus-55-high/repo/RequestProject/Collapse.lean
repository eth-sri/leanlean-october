import Mathlib


/-!
# Collapsing the top cells: the spine argument of Lemma 3.2 (ii)

Lemma 3.2 (ii) of the paper asserts that the truncated cube complex `M_q` collapses onto a
finite two-dimensional spine, and proves it as follows: every square meets at most two
three-cubes; the adjacency graph of the three-cells across their two-faces is connected;
one chooses a spanning tree rooted at a cell meeting the cut surface, collapses the root
across a cut face, and then each further cell across the face it formerly shared with its
parent — that face is free once the parent has been removed.

This file proves the combinatorial content of that argument, for an arbitrary finite family
of top cells `T` whose codimension one faces `F` satisfy the only property used: *a face is
contained in at most two top cells*.  An elementary collapse removes a top cell together
with a face which, at that moment, is contained in no other remaining top cell (`IsFree`),
and `IsCollapse` records a sequence of such moves removing a whole set of top cells.

The main results are:

* `FiniteChains.Collapse.exists_isCollapse`: a set of top cells can be collapsed away
  completely as soon as every nonempty subset closed under adjacency contains a cell with a
  free face — the invariant that the spanning-tree argument maintains;
* `FiniteChains.Collapse.exists_isCollapse_of_connected`: in particular, if the adjacency
  graph is connected and *one* cell has a free face (for `M_q`: a cell meeting the cut
  surface), then all top cells disappear.
-/

namespace FiniteChains.Collapse

variable {T F : Type*} [DecidableEq T]

variable (inc : F → Finset T)

/-- Two distinct top cells are adjacent if they share a codimension one face. -/
def Adj (t t' : T) := t ≠ t' ∧ ∃ f, t ∈ inc f ∧ t' ∈ inc f

/-- The face `f` is *free* for the set `S` of remaining top cells if `t` is the only
remaining top cell containing it. -/
def IsFree (S : Finset T) (f : F) (t : T) := inc f ∩ S = {t}

/-- `t` admits an elementary collapse in `S`: some face of `t` is free for `S`. -/
def HasFreeFace (S : Finset T) (t : T) := ∃ f, IsFree inc S f t

/-- A sequence of elementary collapses removing exactly the top cells of `S`. -/
def IsCollapse : List T → Finset T → Prop
  | [], S => S = ∅
  | t :: l, S => t ∈ S ∧ HasFreeFace inc S t ∧ IsCollapse l (S.erase t)

/-- The invariant maintained by the spanning-tree argument: every nonempty subset of the
remaining cells which is closed under adjacency contains a cell with a free face. -/
def Collapsible (S : Finset T) :=
  ∀ C, C ⊆ S → C.Nonempty → (∀ c ∈ C, ∀ t ∈ S, Adj inc c t → t ∈ C) →
    ∃ c ∈ C, HasFreeFace inc S c

/-- Connectivity of the adjacency graph inside `S`. -/
def Connected (S : Finset T) :=
  ∀ t ∈ S, ∀ t' ∈ S, Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ Adj inc a b) t t'

variable {inc}

/-- A nonempty collapsible set has a cell with a free face. -/
theorem exists_hasFreeFace (hS : Collapsible inc S) (hne : S.Nonempty) :
    ∃ t ∈ S, HasFreeFace inc S t :=
  by aesop

/-- **Collapsibility is preserved by an elementary collapse.**  This is the step "the face
formerly shared with the parent is free once the parent has been removed": a subset that
becomes closed only after the removal of `t` contains a neighbour of `t`, and the shared
face is free for the smaller set. -/
theorem collapsible_erase (hcard : ∀ f, (inc f).card ≤ 2) {S}
    (hS : Collapsible inc S) t : Collapsible inc (S.erase t) := by
  intro C hCS hne hclosed
  by_cases hadj : ∃ c ∈ C, Adj inc c t
  · -- the shared face becomes free
    obtain ⟨c, hcC, hne', f, htf, hcf⟩ := hadj
    refine ⟨c, hcC, f, ?_⟩
    have hsub : ({t, c}) ⊆ inc f := by
      grind
    have hcard2 : ({t, c} : Finset T).card = 2 := by
      grind
    have hfeq :=
      (Finset.eq_of_subset_of_card_le hsub (by simp_all)).symm
    have hcS := hCS hcC
    ext z
    simp_all
  · -- `C` was already closed in `S`, so the invariant applies directly
    have hCS' : C ⊆ S := by grind
    have hclosed' : ∀ c ∈ C, ∀ u ∈ S, Adj inc c u → u ∈ C := by
      grind
    obtain ⟨c, hcC, f, hf⟩ := hS C hCS' hne hclosed'
    refine ⟨c, hcC, f, ?_⟩
    have hct : c ≠ t := by grind
    ext z
    constructor
    · intro hz
      have : z ∈ inc f ∩ S := by simp_all
      rwa [hf] at this
    · intro hz
      simp [Finset.mem_singleton] at hz
      subst hz
      have hzf : z ∈ inc f ∩ S := by rw [hf]; simp
      simp_all

/-- **All top cells of a collapsible set can be collapsed away.** -/
theorem exists_isCollapse (hcard : ∀ f, (inc f).card ≤ 2) :
    ∀ (n : ℕ) (S : Finset T), S.card = n → Collapsible inc S → ∃ l : List T, IsCollapse inc l S
  | 0, S, hn, _ => ⟨[], Finset.card_eq_zero.1 hn⟩
  | n + 1, S, hn, hS => by
      have hne : S.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨t, htS, hfree⟩ := exists_hasFreeFace hS hne
      have hcard' : (S.erase t).card = n := by
        simp_all
      obtain ⟨l, hl⟩ :=
        exists_isCollapse hcard n (S.erase t) hcard' (collapsible_erase hcard hS t)
      exact ⟨t :: l, htS, hfree, hl⟩

/-- A connected set of top cells one of which has a free face is collapsible. -/
theorem collapsible_of_connected (hconn : Connected inc S)
    {t₀ : T} (ht₀ : t₀ ∈ S) (hfree : HasFreeFace inc S t₀) : Collapsible inc S := by
  intro C hCS hne hclosed
  cases' hne with c hcC
  have hcS := hCS hcC
  have key : ∀ x, Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ Adj inc a b) c x →
      x ∈ C := by
    intro x hx
    induction hx <;> grind
  aesop

/-- **The collapse of Lemma 3.2 (ii).**  If every codimension one face lies in at most two
top cells, the adjacency graph of the top cells is connected, and one top cell has a free
face, then all top cells can be removed by elementary collapses. -/
theorem exists_isCollapse_of_connected (hcard : ∀ f, (inc f).card ≤ 2) {S}
    (hconn : Connected inc S) {t₀ : T} (ht₀ : t₀ ∈ S) (hfree : HasFreeFace inc S t₀) :
    ∃ l, IsCollapse inc l S :=
  exists_isCollapse hcard S.card S rfl (collapsible_of_connected hconn ht₀ hfree)

/-! ### A nonempty instance -/
