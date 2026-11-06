module

public meta import Chazelle.Arithmetic

public import Chazelle.Separator.Cotree

/-!
# Lemma 3.6 (WP-H), part 3: planarity of two-page book maps

The preprocessing of Lemma 3.6 hands `ClusterSpec` a planar map (`PlanarMapAt`).  The map is
drawn as a **two-page book**: its vertices `0, …, N-1` lie on a circle (the *spine*, a cycle), the
*inner* chords are drawn inside the circle and the *outer* chords outside; the chords of one page
do not cross.  This file builds the combinatorial map of such a drawing and proves it planar.

## The rotation (`csucc`)

A generic construction: darts carry a vertex `g d` and a key `k d` that is injective on each
vertex; the rotation sends a dart to the dart of the next larger key at its vertex, cyclically
(`csucc`, a permutation `csuccPerm` whose cycles are exactly the vertices).

## The book map (`BookData`)

At vertex `x` the darts are ordered by the key: the forward spine dart (to `x + 1`, key `0`), the
inner chords by increasing offset of their other end, the backward spine dart (to `x - 1`, key
`N - 1`), the outer chords by decreasing offset.

## Planarity (`BookData.planar`)

By Euler's inequality (`CombMap.planar_iff`) it suffices to exhibit `E - V + 2` faces.  Each dart
gets a *label*: its page and the set of chords of that page enclosing the face on its left
(`Enc`, `Sup`, `SSup`).  The label is invariant under the face permutation (a case analysis at
the head of the dart, using the non-crossing condition: `label_fperm`), and the `|I| + |O| + 2`
labels `(inner, Sup c)`, `(inner, ∅)`, `(outer, Sup c)`, `(outer, ∅)` are attained and distinct.
-/

namespace Chazelle.Core

@[expose] public section

namespace OracleBook

open Equiv Finset

/-! ## The cyclic successor by key -/

section CSucc

variable {D : Type*} [Fintype D] [DecidableEq D] (g k : D → ℕ)

/-- The darts at the vertex of `d` with a larger key. -/
def above (d : D) : Finset D := Finset.univ.filter (fun e => g e = g d ∧ k d < k e)

/-- The darts at the vertex of `d`. -/
def fiber (d : D) : Finset D := Finset.univ.filter (fun e => g e = g d)

omit [DecidableEq D] in
theorem mem_fiber_self (d : D) : d ∈ fiber g d := by simp [fiber]

/-- A dart of minimal key in a nonempty set. -/
noncomputable def pickMin (s : Finset D) (hs : s.Nonempty) : D :=
  Classical.choose (s.exists_min_image k hs)

omit [Fintype D] [DecidableEq D] in
theorem pickMin_spec (s : Finset D) (hs : s.Nonempty) :
    pickMin k s hs ∈ s ∧ ∀ f ∈ s, k (pickMin k s hs) ≤ k f :=
  Classical.choose_spec (s.exists_min_image k hs)

/-- **The cyclic successor**: the dart of the next larger key at the same vertex, or the dart of
the smallest key if `d` has the largest. -/
noncomputable def csucc (d : D) : D :=
  if h : (above g k d).Nonempty then pickMin k _ h
  else pickMin k (fiber g d) ⟨d, mem_fiber_self g d⟩

omit [DecidableEq D] in
/-- Characterisation of the cyclic successor. -/
theorem csucc_spec (d : D) : g (csucc g k d) = g d ∧
    ((k d < k (csucc g k d) ∧ ∀ f, g f = g d → k d < k f → k (csucc g k d) ≤ k f) ∨
      ((∀ f, g f = g d → k f ≤ k d) ∧ ∀ f, g f = g d → k (csucc g k d) ≤ k f)) := by
  unfold csucc
  split_ifs with h
  · obtain ⟨hm, hmin⟩ := pickMin_spec k _ h
    aesop (add simp [above, Finset.mem_filter, Finset.mem_univ, true_and]) (add safe (by omega))
  · obtain ⟨hm, hmin⟩ := pickMin_spec k (fiber g d) ⟨d, mem_fiber_self g d⟩
    aesop (add simp [fiber, Finset.mem_filter, Finset.mem_univ, true_and, above]) (add safe (by omega))

variable {g k}

/-- The key is injective on each vertex. -/
def KeyInj (g k : D → ℕ) : Prop := ∀ a b, g a = g b → k a = k b → a = b

omit [DecidableEq D] in
/-- **Uniqueness**: a dart with the characterising property is the cyclic successor. -/
theorem csucc_eq (hinj : KeyInj g k) {d e : D} (he : g e = g d)
    (h : (k d < k e ∧ ∀ f, g f = g d → k d < k f → k e ≤ k f) ∨
      ((∀ f, g f = g d → k f ≤ k d) ∧ ∀ f, g f = g d → k e ≤ k f)) : csucc g k d = e := by
  obtain ⟨hg, hs⟩ := csucc_spec g k d
  refine hinj _ _ (hg.trans he.symm) ?_
  grind

omit [DecidableEq D] in
/-- The cyclic successor is injective. -/
theorem csucc_injective (hinj : KeyInj g k) : Function.Injective (csucc g k) := by
  intro a b hab
  obtain ⟨ha, hsa⟩ := csucc_spec g k a
  obtain ⟨hb, hsb⟩ := csucc_spec g k b
  core_grind

/-- The rotation as a permutation. -/
noncomputable def csuccPerm (hinj : KeyInj g k) : Perm D :=
  Equiv.ofBijective (csucc g k) (Finite.injective_iff_bijective.1 (csucc_injective hinj))

omit [DecidableEq D] in
@[simp] theorem csuccPerm_apply (hinj : KeyInj g k) (d : D) : csuccPerm hinj d = csucc g k d :=
  rfl

omit [DecidableEq D] in
/-- The rotation preserves vertices. -/
theorem g_csucc (d : D) : g (csucc g k d) = g d := (csucc_spec g k d).1

omit [DecidableEq D] in
/-- **The rotation cycles are the vertices.** -/
theorem csucc_sameCycle (hinj : KeyInj g k) {d e : D} (h : g d = g e) :
    (csuccPerm hinj).SameCycle d e := by
  -- the dart of smallest key at the vertex
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (fiber g d) k ⟨d, mem_fiber_self g d⟩
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hm hmin
  have key : ∀ n, ∀ x, g x = g d → k x ≤ n → (csuccPerm hinj).SameCycle m x := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro x hx hxn
    by_cases hlow : ∃ f, g f = g d ∧ k f < k x
    · -- the predecessor `p` of `x`
      obtain ⟨p, hp, hpmax⟩ := Finset.exists_max_image
        (Finset.univ.filter (fun f => g f = g d ∧ k f < k x)) k
        (by obtain ⟨f, hf⟩ := hlow; exact ⟨f, by simp [hf]⟩)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hpmax
      have hsucc : csucc g k p = x := by
        refine csucc_eq hinj (hx.trans hp.1.symm) (Or.inl ⟨hp.2, fun f hf hpf => ?_⟩)
        grind
      have ih' := ih (k p) (by omega) p hp.1 le_rfl
      refine ih'.trans ⟨1, ?_⟩
      simp [hsucc]
    · push Not at hlow
      have : m = x := hinj m x (hm.trans hx.symm) (le_antisymm (hmin x hx) (hlow m hm))
      aesop
  exact (key (k d) d rfl le_rfl).symm.trans (key (k e) e h.symm le_rfl)

end CSucc

/-! ## Chords of a page and the enclosure sets -/

/-- A chord `(u, v)` of a page on `N` spine vertices: `u + 2 ≤ v < N`, and not the spine edge
`(0, N - 1)`. -/
def ChordOK (N : ℕ) (c : ℕ × ℕ) : Prop := c.1 + 2 ≤ c.2 ∧ c.2 < N ∧ ¬ (c.1 = 0 ∧ c.2 + 1 = N)

/-- The chords of a page do not cross. -/
def NonCross (L : List (ℕ × ℕ)) : Prop :=
  ∀ c ∈ L, ∀ c' ∈ L, ¬ (c.1 < c'.1 ∧ c'.1 < c.2 ∧ c.2 < c'.2)

/-- The chords of the page enclosing the spine edge `(x, x + 1)` (none for the closing edge
`(N - 1, 0)`). -/
def Enc (N : ℕ) (L : List (ℕ × ℕ)) (x : ℕ) : Finset (ℕ × ℕ) :=
  if x + 1 < N then L.toFinset.filter (fun c => c.1 ≤ x ∧ x + 1 ≤ c.2) else ∅

section
variable (L : List (ℕ × ℕ)) (c : ℕ × ℕ)
include L c
/-- The chords of the page enclosing the chord `c` (including `c`). -/
def Sup : Finset (ℕ × ℕ) :=
  L.toFinset.filter (fun c' => c'.1 ≤ c.1 ∧ c.2 ≤ c'.2)

/-- The chords of the page strictly enclosing the chord `c`. -/
def SSup : Finset (ℕ × ℕ) := (Sup L c).erase c


end

section Enclosure

variable {N : ℕ} {L : List (ℕ × ℕ)}

section
variable {p : ℕ × ℕ}

section
variable (hp : p ∈ L)
include hp

theorem mem_pair' {b : ℕ} (h2 : p.2 = b) : (p.1, b) ∈ L := by
  grind



end

end

section
variable {c p : ℕ × ℕ}
theorem mem_Sup : p ∈ Sup L c ↔ p ∈ L ∧ p.1 ≤ c.1 ∧ c.2 ≤ p.2 := by
  simp [Sup]

theorem mem_SSup : p ∈ SSup L c ↔ p ≠ c ∧ p ∈ L ∧ p.1 ≤ c.1 ∧ c.2 ≤ p.2 := by
  simp [SSup, Sup]


end

theorem mem_Enc {x : ℕ} {p : ℕ × ℕ} :
    p ∈ Enc N L x ↔ x + 1 < N ∧ p ∈ L ∧ p.1 ≤ x ∧ x + 1 ≤ p.2 := by
  unfold Enc
  split_ifs with h <;> simp [h]

variable (hNC : NonCross L) (hOK : ∀ c ∈ L, ChordOK N c)
include hNC hOK

theorem encA1 {x w : ℕ} (hc : (x, w) ∈ L) (hmin : ∀ w', (x, w') ∈ L → w ≤ w') :
    Enc N L x = Sup L (x, w) := by
  core_grind [mem_Enc, mem_Sup]

theorem encA2 {x w : ℕ} (hc : (w, x) ∈ L) (hno : ∀ w', (x, w') ∉ L)
    (hmin : ∀ w', (w', x) ∈ L → w ≤ w') : Enc N L x = SSup L (w, x) := by
  core_grind [mem_Enc, mem_SSup]

omit hNC hOK in
theorem encA3 (_hNC : NonCross L) (hOK : ∀ c ∈ L, ChordOK N c) {x : ℕ} (hx : x < N)
    (hno : ∀ p ∈ L, p.1 ≠ x ∧ p.2 ≠ x) :
    Enc N L x = Enc N L ((x + N - 1) % N) := by
  ext p
  rw [mem_Enc, mem_Enc]
  rcases Nat.eq_zero_or_pos x with rfl | hpos
  · have e : (0 + N - 1) % N = N - 1 := by simp_all
    grind
  · have e : (x + N - 1) % N = x - 1 := by
      rw [show x + N - 1 = (x - 1) + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    ram_grind

theorem encB1 {u v w : ℕ} (hc : (u, v) ∈ L) (hc' : (w, v) ∈ L) (huw : u < w)
    (hmin : ∀ w', (w', v) ∈ L → u < w' → w ≤ w') : Sup L (u, v) = SSup L (w, v) := by
  core_grind [mem_Sup, mem_SSup]

theorem encB2 {u v : ℕ} (hc : (u, v) ∈ L) (hno : ∀ w', (w', v) ∈ L → w' ≤ u) :
    Sup L (u, v) = Enc N L (v - 1) := by
  core_grind [mem_Sup, mem_Enc]

section
variable {u v w : ℕ} (hc : (u, v) ∈ L)
include hc
theorem encC1 (hc' : (u, w) ∈ L) (hvw : v < w)
    (hmin : ∀ w', (u, w') ∈ L → v < w' → w ≤ w') : SSup L (u, v) = Sup L (u, w) := by
  core_grind [mem_SSup, mem_Sup]

theorem encC2 (hc' : (w, u) ∈ L)
    (hno : ∀ w', (u, w') ∈ L → w' ≤ v) (hmin : ∀ w', (w', u) ∈ L → w ≤ w') :
    SSup L (u, v) = SSup L (w, u) := by
  core_grind [mem_SSup]


end

theorem encC3 {u v : ℕ} (hc : (u, v) ∈ L) (hno : ∀ w', (u, w') ∈ L → w' ≤ v)
    (hno2 : ∀ w', (w', u) ∉ L) : SSup L (u, v) = Enc N L ((u + N - 1) % N) := by
  have hk := hOK _ hc
  simp only [ChordOK] at hk
  have hp1 : ∀ p ∈ L, p ≠ (u, v) → p.1 ≤ u → v ≤ p.2 → p.1 ≠ u := fun p hp hne _ h2 h => by
    grind
  ext p
  rw [mem_SSup, mem_Enc]
  simp only
  rcases Nat.eq_zero_or_pos u with hu | hpos
  · have e : (u + N - 1) % N = N - 1 := by
      simp_all
    grind
  · have e : (u + N - 1) % N = u - 1 := by
      rw [show u + N - 1 = (u - 1) + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [e]
    constructor
    · grind
    · rintro ⟨-, hp, h1, h2⟩
      have hp2 : p.2 ≠ u := fun h => hno2 _ (mem_pair' hp h)
      have hge : v ≤ p.2 := by
        by_contra hlt
        exact hNC _ hp _ hc (by omega)
      grind

section
variable {x w : ℕ} (hx : x < N)
include hx
theorem encD1 (hc : (w, (x + 1) % N) ∈ L)
    (hmax : ∀ w', (w', (x + 1) % N) ∈ L → w' ≤ w) : Enc N L x = Sup L (w, (x + 1) % N) := by
  have hk := hOK _ hc
  simp only [ChordOK] at hk
  have hx1 : x + 1 < N := by
    grind [Nat.mod_self]
  have e : (x + 1) % N = x + 1 := Nat.mod_eq_of_lt hx1
  core_grind [mem_Enc, mem_Sup]

theorem encD2 (hc : ((x + 1) % N, w) ∈ L)
    (hno : ∀ w', (w', (x + 1) % N) ∉ L) (hmax : ∀ w', ((x + 1) % N, w') ∈ L → w' ≤ w) :
    Enc N L x = SSup L ((x + 1) % N, w) := by
  have hk := hOK _ hc
  simp only [ChordOK] at hk
  ext p
  rw [mem_Enc, mem_SSup]
  simp only
  by_cases hx1 : x + 1 < N
  · have e : (x + 1) % N = x + 1 := Nat.mod_eq_of_lt hx1
    rw [e] at hc hno hmax hk ⊢
    constructor
    · rintro ⟨-, hp, h1, h2⟩
      have hp2 : p.2 ≠ x + 1 := fun h => hno _ (mem_pair' hp h)
      have hge : w ≤ p.2 := by
        by_contra hlt
        exact hNC _ hp _ hc (by omega)
      grind
    grind
  grind [Nat.mod_self]


end

theorem encD3 {x : ℕ} (hx : x < N) (hno : ∀ p ∈ L, p.1 ≠ (x + 1) % N ∧ p.2 ≠ (x + 1) % N) :
    Enc N L x = Enc N L ((x + 1) % N) := by
  have hN : 0 < N := by omega
  rw [encA3 hNC hOK (Nat.mod_lt _ hN) hno]
  congr 1
  rcases Nat.lt_or_ge (x + 1) N with h | h
  · rw [Nat.mod_eq_of_lt h, show x + 1 + N - 1 = x + N by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hx]
  · rw [show x + 1 = N by omega, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (by omega)]
    omega

theorem encE1 {u v w : ℕ} (hc : (u, v) ∈ L) (hc' : (u, w) ∈ L) (hwv : w < v)
    (hmax : ∀ w', (u, w') ∈ L → w' < v → w' ≤ w) : Sup L (u, v) = SSup L (u, w) := by
  core_grind [mem_Sup, mem_SSup]

theorem encE2 {u v : ℕ} (hc : (u, v) ∈ L) (hno : ∀ w', (u, w') ∈ L → v ≤ w') :
    Sup L (u, v) = Enc N L u := by
  core_grind [mem_Sup, mem_Enc]

section
variable {u v w : ℕ} (hc : (u, v) ∈ L)
include hc
theorem encF1 (hc' : (w, v) ∈ L) (hwu : w < u)
    (hmax : ∀ w', (w', v) ∈ L → w' < u → w' ≤ w) : SSup L (u, v) = Sup L (w, v) := by
  core_grind [mem_SSup, mem_Sup]

theorem encF2 (hc' : (v, w) ∈ L)
    (hno : ∀ w', (w', v) ∈ L → u ≤ w') (hmax : ∀ w', (v, w') ∈ L → w' ≤ w) :
    SSup L (u, v) = SSup L (v, w) := by
  core_grind [mem_SSup]


end

theorem encF3 {u v : ℕ} (hc : (u, v) ∈ L) (hno : ∀ w', (w', v) ∈ L → u ≤ w')
    (hno2 : ∀ w', (v, w') ∉ L) : SSup L (u, v) = Enc N L v := by
  core_grind [mem_SSup, mem_Enc]

end Enclosure

/-! ## Darts of a book map -/

/-- A dart of a book map, by kind: forward and backward spine darts of the spine edge
`(x, x + 1 mod N)`, the two darts `(u → v)`, `(v → u)` of an inner chord `(u, v)`, of an outer
chord. -/
inductive View where
  | spF (x : ℕ)
  | spB (x : ℕ)
  | inP (c : ℕ × ℕ)
  | inM (c : ℕ × ℕ)
  | outP (c : ℕ × ℕ)
  | outM (c : ℕ × ℕ)
  deriving DecidableEq

namespace View

section
variable (N : ℕ)
include N
/-- The tail (vertex) of a dart. -/
def tail : View → ℕ
  | spF x => x
  | spB x => (x + 1) % N
  | inP c => c.1
  | inM c => c.2
  | outP c => c.1
  | outM c => c.2

/-- The head of a dart. -/
def head : View → ℕ
  | spF x => (x + 1) % N
  | spB x => x
  | inP c => c.2
  | inM c => c.1
  | outP c => c.2
  | outM c => c.1

/-- The key of a dart at its tail: forward spine `0`, inner chords by increasing offset of the
head (`2 … N - 2`), backward spine `N - 1`, outer chords by decreasing offset (`N … 2 N - 4`). -/
def key : View → ℕ
  | spF _ => 0
  | spB _ => N - 1
  | inP c => c.2 - c.1
  | inM c => N - c.2 + c.1
  | outP c => 2 * N - 2 - (c.2 - c.1)
  | outM c => N - 2 + c.2 - c.1


end

/-- The opposite dart. -/
def rev : View → View
  | spF x => spB x
  | spB x => spF x
  | inP c => inM c
  | inM c => inP c
  | outP c => outM c
  | outM c => outP c

theorem tail_rev (N : ℕ) (v : View) : tail N v.rev = head N v := by cases v <;> rfl

end View

/-- **Data of a two-page book map**: `N` spine vertices, the inner and the outer chords. -/
structure BookData where
  /-- The number of spine vertices. -/
  N : ℕ
  /-- The inner chords. -/
  I : List (ℕ × ℕ)
  /-- The outer chords. -/
  O : List (ℕ × ℕ)

namespace BookData

variable (B : BookData)

/-- Validity: at least three spine vertices, distinct well-formed chords, no crossing within a
page. -/
def Valid : Prop :=
  3 ≤ B.N ∧ B.I.Nodup ∧ B.O.Nodup ∧ (∀ c ∈ B.I, ChordOK B.N c) ∧ (∀ c ∈ B.O, ChordOK B.N c) ∧
    NonCross B.I ∧ NonCross B.O

/-- The number of edges. -/
def E : ℕ := B.N + B.I.length + B.O.length

/-- The dart `d` (edge `d / 2`, direction `d % 2`) by kind: spine edges `0 … N - 1`, then the
inner chords, then the outer chords. -/
def view (d : ℕ) : View :=
  if d / 2 < B.N then (if d % 2 = 0 then .spF (d / 2) else .spB (d / 2))
  else if d / 2 < B.N + B.I.length then
    (if d % 2 = 0 then .inP (B.I.getD (d / 2 - B.N) (0, 0))
      else .inM (B.I.getD (d / 2 - B.N) (0, 0)))
  else (if d % 2 = 0 then .outP (B.O.getD (d / 2 - B.N - B.I.length) (0, 0))
      else .outM (B.O.getD (d / 2 - B.N - B.I.length) (0, 0)))

/-- The darts that exist. -/
def ViewOK : View → Prop
  | .spF x => x < B.N
  | .spB x => x < B.N
  | .inP c => c ∈ B.I
  | .inM c => c ∈ B.I
  | .outP c => c ∈ B.O
  | .outM c => c ∈ B.O

/-- **The face label** of a dart: its page and the chords of that page enclosing the face on its
left. -/
def label : View → Bool × Finset (ℕ × ℕ)
  | .spF x => (false, Enc B.N B.O x)
  | .spB x => (true, Enc B.N B.I x)
  | .inP c => (true, Sup B.I c)
  | .inM c => (true, SSup B.I c)
  | .outP c => (false, SSup B.O c)
  | .outM c => (false, Sup B.O c)

/-- `w` is the next dart after key `k₀` at vertex `t`, cyclically. -/
def IsNext (t k₀ : ℕ) (w : View) : Prop :=
  B.ViewOK w ∧ View.tail B.N w = t ∧
    ((k₀ < View.key B.N w ∧ ∀ w', B.ViewOK w' → View.tail B.N w' = t → k₀ < View.key B.N w' →
        View.key B.N w ≤ View.key B.N w') ∨
      ((∀ w', B.ViewOK w' → View.tail B.N w' = t → View.key B.N w' ≤ k₀) ∧
        ∀ w', B.ViewOK w' → View.tail B.N w' = t → View.key B.N w ≤ View.key B.N w'))

theorem pred_mod_eq {N x : ℕ} (hx : x < N) (hx0 : 1 ≤ x) : (x + N - 1) % N = x - 1 := by
  rw [show x + N - 1 = (x - 1) + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]


/-- The backward spine dart into `x` from `x - 1` has tail... (the spine dart `(x - 1, x)`
reversed): its tail is `x`. -/
theorem tail_spB_pred {N x : ℕ} (hx : x < N) : ((x + N - 1) % N + 1) % N = x := by
  rcases Nat.eq_zero_or_pos x with rfl | hpos
  · simp_all +arith
  · rw [pred_mod_eq hx hpos, Nat.sub_add_cancel hpos, Nat.mod_eq_of_lt hx]

/-- A spine vertex whose successor is `x` is `x - 1 mod N`. -/
theorem eq_pred_of_succ {N x y : ℕ} (hy : y < N) (h : (y + 1) % N = x) : y = (x + N - 1) % N := by
  rcases Nat.lt_or_ge (y + 1) N with hl | hl
  · rw [Nat.mod_eq_of_lt hl] at h
    subst h
    rw [show y + 1 + N - 1 = y + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hy]
  · rw [show y + 1 = N by omega, Nat.mod_self] at h
    aesop (add safe (by omega))

/-! ## Invariance of the face label -/

section Label

variable {B}

/-- Around a backward spine dart. -/
theorem label_next_spB (hV : B.Valid) {x : ℕ} (hx : x < B.N) {w : View}
    (hw : B.IsNext x 0 w) : B.label w = B.label (.spB x) := by
  obtain ⟨hN, -, -, hIok, hOok, hInc, hOnc⟩ := hV
  obtain ⟨hwok, hwt, hbr⟩ := hw
  have hwit : B.ViewOK (.spB ((x + B.N - 1) % B.N)) := Nat.mod_lt _ (by omega)
  have hwitt : View.tail B.N (.spB ((x + B.N - 1) % B.N)) = x := tail_spB_pred hx
  obtain ⟨hpos, hmin⟩ : 0 < View.key B.N w ∧ ∀ w', B.ViewOK w' → View.tail B.N w' = x →
      0 < View.key B.N w' → View.key B.N w ≤ View.key B.N w' := by
    grind [View.key]
  have hle := hmin _ hwit hwitt (by grind [View.key])
  cases w with
  | spF y => grind [View.key]
  | spB y =>
    simp only [ViewOK] at hwok
    simp only [View.tail] at hwt
    have hy := eq_pred_of_succ hwok hwt
    have hno : ∀ p ∈ B.I, p.1 ≠ x ∧ p.2 ≠ x := by
      intro p hp
      have hk := hIok p hp
      simp only [ChordOK] at hk
      constructor
      · intro h1
        have := hmin (.inP p) hp h1 (by grind [View.key])
        grind [View.key]
      · intro h2
        have := hmin (.inM p) hp h2 (by grind [View.key])
        grind [View.key]
    simp only [label]
    rw [hy, ← encA3 hInc hIok hx hno]
  | inP c =>
    rcases c with ⟨u, v⟩
    simp only [ViewOK] at hwok
    simp only [View.tail] at hwt
    subst hwt
    have hmin2 : ∀ w', (u, w') ∈ B.I → v ≤ w' := by
      intro w' hw'
      have hk := hIok _ hw'
      simp only [ChordOK] at hk
      have := hmin (.inP (u, w')) hw' rfl (by grind [View.key])
      grind [View.key]
    simp only [label]
    rw [encA1 hInc hIok hwok hmin2]
  | inM c =>
    rcases c with ⟨u, v⟩
    simp only [ViewOK] at hwok
    simp only [View.tail] at hwt
    subst hwt
    have hk := hIok _ hwok
    simp only [ChordOK] at hk
    have hno : ∀ w', (v, w') ∉ B.I := by
      intro w' hw'
      have hk' := hIok _ hw'
      simp only [ChordOK] at hk'
      have := hmin (.inP (v, w')) hw' rfl (by grind [View.key])
      grind [View.key]
    have hmin2 : ∀ w', (w', v) ∈ B.I → u ≤ w' := by
      intro w' hw'
      have hk' := hIok _ hw'
      simp only [ChordOK] at hk'
      have := hmin (.inM (w', v)) hw' rfl (by grind [View.key])
      grind [View.key]
    simp only [label]
    rw [encA2 hInc hIok hwok hno hmin2]
  | outP c =>
    rcases c with ⟨u, v⟩
    have hk := hOok _ hwok
    grind [ChordOK, View.key]
  | outM c =>
    rcases c with ⟨u, v⟩
    have hk := hOok _ hwok
    grind [ChordOK, View.key]

section
variable (hV : B.Valid) {u v : ℕ} (hc : (u, v) ∈ B.I) {w : View}
include hV hc
/-- Around the forward dart of an inner chord. -/
theorem label_next_inP
    (hw : B.IsNext v (B.N - v + u) w) : B.label w = B.label (.inP (u, v)) := by
  obtain ⟨hN, -, -, hIok, hOok, hInc, hOnc⟩ := hV
  obtain ⟨hwok, hwt, hbr⟩ := hw
  have hk := hIok _ hc
  simp only [ChordOK] at hk
  have hvN : v < B.N := hk.2.1
  have hwit : B.ViewOK (.spB ((v + B.N - 1) % B.N)) := Nat.mod_lt _ (by omega)
  have hwitt : View.tail B.N (.spB ((v + B.N - 1) % B.N)) = v := tail_spB_pred hvN
  obtain ⟨hpos, hmin⟩ : B.N - v + u < View.key B.N w ∧ ∀ w', B.ViewOK w' →
      View.tail B.N w' = v → B.N - v + u < View.key B.N w' →
        View.key B.N w ≤ View.key B.N w' := by
    grind [View.key]
  have hle := hmin _ hwit hwitt (by grind [View.key])
  cases w with
  | spF y => grind [View.key]
  | spB y =>
    simp only [ViewOK] at hwok
    simp only [View.tail] at hwt
    have hy := eq_pred_of_succ hwok hwt
    rw [pred_mod_eq hvN (by omega)] at hy
    have hno : ∀ w', (w', v) ∈ B.I → w' ≤ u := by
      intro w' hw'
      have hk' := hIok _ hw'
      simp only [ChordOK] at hk'
      by_contra hlt
      have := hmin (.inM (w', v)) hw' rfl (by grind [View.key])
      grind [View.key]
    simp only [label]
    rw [hy, encB2 hInc hIok hc hno]
  | inP c =>
    grind [ViewOK, ChordOK, View.tail, View.key]
  | inM c =>
    rcases c with ⟨a, b⟩
    simp only [ViewOK] at hwok
    simp only [View.tail] at hwt
    subst hwt
    simp only [View.key] at hpos
    have hmin2 : ∀ w', (w', b) ∈ B.I → u < w' → a ≤ w' := by
      intro w' hw' huw
      have hk' := hIok _ hw'
      simp only [ChordOK] at hk'
      have := hmin (.inM (w', b)) hw' rfl (by grind [View.key])
      grind [View.key]
    simp only [label]
    rw [encB1 hInc hIok hc hwok (by omega) hmin2]
  | outP c =>
    rcases c with ⟨a, b⟩
    have hk' := hOok _ hwok
    grind [ChordOK, View.key]
  | outM c =>
    rcases c with ⟨a, b⟩
    have hk' := hOok _ hwok
    grind [ChordOK, View.key]

/-- Around the backward dart of an inner chord. -/
theorem label_next_inM
    (hw : B.IsNext u (v - u) w) : B.label w = B.label (.inM (u, v)) := by
  obtain ⟨hN, -, -, hIok, hOok, hInc, hOnc⟩ := hV
  obtain ⟨hwok, hwt, hbr⟩ := hw
  have hk := hIok _ hc
  simp only [ChordOK] at hk
  have huN : u < B.N := by omega
  have hwit : B.ViewOK (.spB ((u + B.N - 1) % B.N)) := Nat.mod_lt _ (by omega)
  have hwitt : View.tail B.N (.spB ((u + B.N - 1) % B.N)) = u := tail_spB_pred huN
  obtain ⟨hpos, hmin⟩ : v - u < View.key B.N w ∧ ∀ w', B.ViewOK w' →
      View.tail B.N w' = u → v - u < View.key B.N w' →
        View.key B.N w ≤ View.key B.N w' := by
    grind [View.key]
  have hle := hmin _ hwit hwitt (by grind [View.key])
  cases w with
  | spF y => grind [View.key]
  | spB y =>
    simp only [ViewOK] at hwok
    simp only [View.tail] at hwt
    have hy := eq_pred_of_succ hwok hwt
    have hno : ∀ w', (u, w') ∈ B.I → w' ≤ v := by
      intro w' hw'
      have hk' := hIok _ hw'
      simp only [ChordOK] at hk'
      by_contra hlt
      have := hmin (.inP (u, w')) hw' rfl (by grind [View.key])
      grind [View.key]
    have hno2 : ∀ w', (w', u) ∉ B.I := by
      intro w' hw'
      have hk' := hIok _ hw'
      simp only [ChordOK] at hk'
      have := hmin (.inM (w', u)) hw' rfl (by grind [View.key])
      grind [View.key]
    simp only [label]
    rw [hy, encC3 hInc hIok hc hno hno2]
  | inP c =>
    rcases c with ⟨a, b⟩
    simp only [ViewOK] at hwok
    simp only [View.tail] at hwt
    subst hwt
    simp only [View.key] at hpos
    have hmin2 : ∀ w', (a, w') ∈ B.I → v < w' → b ≤ w' := by
      intro w' hw' hvw
      have hk' := hIok _ hw'
      simp only [ChordOK] at hk'
      have := hmin (.inP (a, w')) hw' rfl (by grind [View.key])
      grind [View.key]
    simp only [label]
    rw [encC1 hInc hIok hc hwok (by omega) hmin2]
  | inM c =>
    rcases c with ⟨a, b⟩
    simp only [ViewOK] at hwok
    simp only [View.tail] at hwt
    subst hwt
    have hkw := hIok _ hwok
    simp only [ChordOK] at hkw
    have hno : ∀ w', (b, w') ∈ B.I → w' ≤ v := by
      intro w' hw'
      have hk' := hIok _ hw'
      simp only [ChordOK] at hk'
      by_contra hlt
      have := hmin (.inP (b, w')) hw' rfl (by grind [View.key])
      grind [View.key]
    have hmin2 : ∀ w', (w', b) ∈ B.I → a ≤ w' := by
      intro w' hw'
      have hk' := hIok _ hw'
      simp only [ChordOK] at hk'
      have := hmin (.inM (w', b)) hw' rfl (by grind [View.key])
      grind [View.key]
    simp only [label]
    rw [encC2 hInc hIok hc hwok hno hmin2]
  | outP c =>
    rcases c with ⟨a, b⟩
    have hk' := hOok _ hwok
    grind [ChordOK, View.key]
  | outM c =>
    rcases c with ⟨a, b⟩
    have hk' := hOok _ hwok
    grind [ChordOK, View.key]


end

/-- In the wrap-around case at a vertex `t`, the next dart is the forward spine dart. -/
theorem eq_spF_of_wrap (hV : B.Valid) {t : ℕ} (ht : t < B.N) {w : View} (hwok : B.ViewOK w)
    (hwt : View.tail B.N w = t)
    (hmin : ∀ w', B.ViewOK w' → View.tail B.N w' = t → View.key B.N w ≤ View.key B.N w') :
    w = .spF t := by
  obtain ⟨hN, -, -, hIok, hOok, -, -⟩ := hV
  have h0 := hmin (.spF t) ht rfl
  cases w with
  | spF y => aesop
  | spB y => grind [View.key]
  | inP c =>
    have hk := hIok _ hwok; grind [ChordOK, View.key]
  | inM c =>
    have hk := hIok _ hwok; grind [ChordOK, View.key]
  | outP c =>
    have hk := hOok _ hwok; grind [ChordOK, View.key]
  | outM c =>
    have hk := hOok _ hwok; grind [ChordOK, View.key]

/-- Around a forward spine dart. -/
theorem label_next_spF (hV : B.Valid) {x : ℕ} (hx : x < B.N) {w : View}
    (hw : B.IsNext ((x + 1) % B.N) (B.N - 1) w) : B.label w = B.label (.spF x) := by
  have hV' := hV
  obtain ⟨hN, -, -, hIok, hOok, hInc, hOnc⟩ := hV
  obtain ⟨hwok, hwt, hbr⟩ := hw
  have hhN : (x + 1) % B.N < B.N := Nat.mod_lt _ (by omega)
  rcases hbr with ⟨hlt, hmin⟩ | ⟨hall, hmin⟩
  · cases w with
    | spF y => simp_all [View.key] <;> omega_nf
    | spB y => simp_all [View.key] <;> omega_nf
    | inP c =>
      have hk := hIok _ hwok; grind [ChordOK, View.key]
    | inM c =>
      have hk := hIok _ hwok; grind [ChordOK, View.key]
    | outM c =>
      rcases c with ⟨a, b⟩
      simp only [ViewOK] at hwok
      simp only [View.tail] at hwt
      subst hwt
      have hmax : ∀ w', (w', (x + 1) % B.N) ∈ B.O → w' ≤ a := by
        intro w' hw'
        have hk' := hOok _ hw'
        simp only [ChordOK] at hk'
        have := hmin (.outM (w', (x + 1) % B.N)) hw' rfl (by grind [View.key])
        grind [View.key]
      simp only [label]
      rw [encD1 hOnc hOok hx hwok hmax]
    | outP c =>
      rcases c with ⟨a, b⟩
      simp only [ViewOK] at hwok
      simp only [View.tail] at hwt
      subst hwt
      have hk := hOok _ hwok
      simp only [ChordOK] at hk
      have hno : ∀ w', (w', (x + 1) % B.N) ∉ B.O := by
        intro w' hw'
        have hk' := hOok _ hw'
        simp only [ChordOK] at hk'
        have := hmin (.outM (w', (x + 1) % B.N)) hw' rfl (by grind [View.key])
        grind [View.key]
      have hmax : ∀ w', ((x + 1) % B.N, w') ∈ B.O → w' ≤ b := by
        intro w' hw'
        have hk' := hOok _ hw'
        simp only [ChordOK] at hk'
        have := hmin (.outP ((x + 1) % B.N, w')) hw' rfl (by grind [View.key])
        grind [View.key]
      simp only [label]
      rw [encD2 hOnc hOok hx hwok hno hmax]
  · have hw := eq_spF_of_wrap hV' hhN hwok hwt hmin
    subst hw
    have hno : ∀ p ∈ B.O, p.1 ≠ (x + 1) % B.N ∧ p.2 ≠ (x + 1) % B.N := by
      intro p hp
      have hk := hOok p hp
      simp only [ChordOK] at hk
      constructor
      · intro h1
        have := hall (.outP p) hp h1
        grind [View.key]
      · intro h2
        have := hall (.outM p) hp h2
        grind [View.key]
    simp only [label]
    rw [encD3 hOnc hOok hx hno]

section
variable (hV : B.Valid) {u v : ℕ} (hc : (u, v) ∈ B.O) {w : View}
include hV hc
/-- Around the backward dart of an outer chord. -/
theorem label_next_outM
    (hw : B.IsNext u (2 * B.N - 2 - (v - u)) w) : B.label w = B.label (.outM (u, v)) := by
  have hV' := hV
  obtain ⟨hN, -, -, hIok, hOok, hInc, hOnc⟩ := hV
  obtain ⟨hwok, hwt, hbr⟩ := hw
  have hk := hOok _ hc
  simp only [ChordOK] at hk
  rcases hbr with ⟨hlt, hmin⟩ | ⟨hall, hmin⟩
  · cases w with
    | spF y => simp_all [View.key] <;> omega_nf
    | spB y => grind [View.key]
    | inP c =>
      have hk' := hIok _ hwok; grind [ChordOK, View.key]
    | inM c =>
      have hk' := hIok _ hwok; grind [ChordOK, View.key]
    | outM c =>
      grind [ChordOK, View.tail, View.key]
    | outP c =>
      rcases c with ⟨a, b⟩
      simp only [ViewOK] at hwok
      simp only [View.tail] at hwt
      subst hwt
      have hk' := hOok _ hwok
      simp only [ChordOK] at hk'
      simp only [View.key] at hlt
      have hmax : ∀ w', (a, w') ∈ B.O → w' < v → w' ≤ b := by
        intro w' hw' hwv
        have hk'' := hOok _ hw'
        simp only [ChordOK] at hk''
        have := hmin (.outP (a, w')) hw' rfl (by grind [View.key])
        grind [View.key]
      simp only [label]
      rw [encE1 hOnc hOok hc hwok (by omega) hmax]
  · have hw := eq_spF_of_wrap hV' (by omega) hwok hwt hmin
    subst hw
    have hno : ∀ w', (u, w') ∈ B.O → v ≤ w' := by
      intro w' hw'
      have hk' := hOok _ hw'
      simp only [ChordOK] at hk'
      by_contra hlt
      have := hall (.outP (u, w')) hw' rfl
      grind [View.key]
    simp only [label]
    rw [encE2 hOnc hOok hc hno]

/-- Around the forward dart of an outer chord. -/
theorem label_next_outP
    (hw : B.IsNext v (B.N - 2 + v - u) w) : B.label w = B.label (.outP (u, v)) := by
  have hV' := hV
  obtain ⟨hN, -, -, hIok, hOok, hInc, hOnc⟩ := hV
  obtain ⟨hwok, hwt, hbr⟩ := hw
  have hk := hOok _ hc
  simp only [ChordOK] at hk
  rcases hbr with ⟨hlt, hmin⟩ | ⟨hall, hmin⟩
  · cases w with
    | spF y => simp_all [View.key] <;> omega_nf
    | spB y => grind [View.key]
    | inP c =>
      have hk' := hIok _ hwok; grind [ChordOK, View.key]
    | inM c =>
      have hk' := hIok _ hwok; grind [ChordOK, View.key]
    | outM c =>
      rcases c with ⟨a, b⟩
      simp only [ViewOK] at hwok
      simp only [View.tail] at hwt
      subst hwt
      have hk' := hOok _ hwok
      simp only [ChordOK] at hk'
      simp only [View.key] at hlt
      have hmax : ∀ w', (w', b) ∈ B.O → w' < u → w' ≤ a := by
        intro w' hw' hwu
        have hk'' := hOok _ hw'
        simp only [ChordOK] at hk''
        have := hmin (.outM (w', b)) hw' rfl (by grind [View.key])
        grind [View.key]
      simp only [label]
      rw [encF1 hOnc hOok hc hwok (by omega) hmax]
    | outP c =>
      rcases c with ⟨a, b⟩
      simp only [ViewOK] at hwok
      simp only [View.tail] at hwt
      subst hwt
      have hk' := hOok _ hwok
      simp only [ChordOK] at hk'
      have hno : ∀ w', (w', a) ∈ B.O → u ≤ w' := by
        intro w' hw'
        have hk'' := hOok _ hw'
        simp only [ChordOK] at hk''
        by_contra hlt'
        have := hmin (.outM (w', a)) hw' rfl (by grind [View.key])
        grind [View.key]
      have hmax : ∀ w', (a, w') ∈ B.O → w' ≤ b := by
        intro w' hw'
        have hk'' := hOok _ hw'
        simp only [ChordOK] at hk''
        have := hmin (.outP (a, w')) hw' rfl (by grind [View.key])
        grind [View.key]
      simp only [label]
      rw [encF2 hOnc hOok hc hwok hno hmax]
  · have hw := eq_spF_of_wrap hV' (by omega) hwok hwt hmin
    subst hw
    have hno : ∀ w', (w', v) ∈ B.O → u ≤ w' := by
      intro w' hw'
      have hk' := hOok _ hw'
      simp only [ChordOK] at hk'
      by_contra hlt
      have := hall (.outM (w', v)) hw' rfl
      grind [View.key]
    have hno2 : ∀ w', (v, w') ∉ B.O := by
      intro w' hw'
      have hk' := hOok _ hw'
      simp only [ChordOK] at hk'
      have := hall (.outP (v, w')) hw' rfl
      grind [View.key]
    simp only [label]
    rw [encF3 hOnc hOok hc hno hno2]


end

/-- **The face label is invariant**: the dart following the reverse of `v` at the head of `v`
has the label of `v`. -/
theorem label_next (hV : B.Valid) {v : View} (hv : B.ViewOK v) {w : View}
    (hw : B.IsNext (View.head B.N v) (View.key B.N v.rev) w) : B.label w = B.label v := by
  cases v with
  | spF x => exact label_next_spF hV hv hw
  | spB x => exact label_next_spB hV hv hw
  | inP c => rcases c with ⟨u, v⟩; exact label_next_inP hV hv hw
  | inM c => rcases c with ⟨u, v⟩; exact label_next_inM hV hv hw
  | outP c => rcases c with ⟨u, v⟩; exact label_next_outP hV hv hw
  | outM c => rcases c with ⟨u, v⟩; exact label_next_outM hV hv hw

end Label

/-! ## Darts as numbers -/


theorem ite_f {α : Type*} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) :
    (if c then a else b) = b := by simp [h]

section Darts

variable {B}

section
variable {L : List (ℕ × ℕ)} {i : ℕ} (hi : i < L.length)
include hi
theorem getD_mem : L.getD i (0, 0) ∈ L := by
  simp_all



end

/-- Every dart has a kind that exists. -/
theorem view_ok {d : ℕ} (hd : d < 2 * B.E) : B.ViewOK (B.view d) := by
  core_grind [view]

/-- Every existing kind is a dart. -/
theorem exists_view {v : View} (hv : B.ViewOK v) : ∃ d, d < 2 * B.E ∧ B.view d = v := by
  unfold E
  cases v with
  | spF x =>
    refine ⟨2 * x, by simp_all [ViewOK] <;> omega_nf, ?_⟩
    simp_all [ViewOK, view] <;> omega_nf
  | spB x =>
    refine ⟨2 * x + 1, by simp_all [ViewOK] <;> omega_nf, ?_⟩
    core_grind [view]
  | inP c =>
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 (show c ∈ B.I from hv)
    refine ⟨2 * (B.N + i), by omega, ?_⟩
    simp_all [view] <;> omega_nf
  | inM c =>
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 (show c ∈ B.I from hv)
    refine ⟨2 * (B.N + i) + 1, by omega, ?_⟩
    unfold view
    grind
  | outP c =>
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 (show c ∈ B.O from hv)
    refine ⟨2 * (B.N + B.I.length + i), by omega, ?_⟩
    unfold view
    grind
  | outM c =>
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 (show c ∈ B.O from hv)
    refine ⟨2 * (B.N + B.I.length + i) + 1, by omega, ?_⟩
    unfold view
    grind

/-- Distinct darts have distinct kinds. -/
theorem view_inj (hV : B.Valid) {d d' : ℕ} (hd : d < 2 * B.E) (hd' : d' < 2 * B.E)
    (h : B.view d = B.view d') : d = d' := by
  obtain ⟨-, hIn, hOn, -⟩ := hV
  unfold E at hd hd'
  unfold view at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 <;> grind <;> first
    | omega
    | (rw [getD_eq (by omega), getD_eq (by omega), hIn.getElem_inj_iff] at h; omega)
    | (rw [getD_eq (by omega), getD_eq (by omega), hOn.getElem_inj_iff] at h; omega)

/-- The opposite dart as a number. -/
def oppN (d : ℕ) : ℕ := if d % 2 = 0 then d + 1 else d - 1

theorem oppN_lt {d : ℕ} (hd : d < 2 * B.E) : oppN d < 2 * B.E := by
  core_grind

section
variable (d : ℕ)
theorem oppN_oppN : oppN (oppN d) = d := by
  core_grind

theorem oppN_ne : oppN d ≠ d := by
  core_grind

theorem view_oppN : B.view (oppN d) = (B.view d).rev := by
  have h1 : oppN d / 2 = d / 2 := by core_grind
  have h2 : oppN d % 2 = 0 ↔ ¬ d % 2 = 0 := by core_grind
  unfold view
  rw [h1]
  by_cases hp : d % 2 = 0
  · have hq : ¬ oppN d % 2 = 0 := fun h => (h2.1 h) hp
    simp only [hp, hq, ite_true, ite_false]
    split_ifs <;> rfl
  · have hq : oppN d % 2 = 0 := h2.2 hp
    simp only [hp, hq, ite_true, ite_false]
    split_ifs <;> rfl


end

theorem tail_lt (hV : B.Valid) {v : View} (hv : B.ViewOK v) : View.tail B.N v < B.N := by
  obtain ⟨hN, -, -, hIok, hOok, -⟩ := hV
  cases v with
  | spF x => exact hv
  | spB x => exact Nat.mod_lt _ (by omega)
  | inP c => have := (hIok _ hv).2.1; have := (hIok _ hv).1; grind [View.tail]
  | inM c => exact (hIok _ hv).2.1
  | outP c => have := (hOok _ hv).2.1; have := (hOok _ hv).1; grind [View.tail]
  | outM c => exact (hOok _ hv).2.1

/-- **Keys are injective at a vertex.** -/
theorem key_inj (hV : B.Valid) {v v' : View} (hv : B.ViewOK v) (hv' : B.ViewOK v')
    (ht : View.tail B.N v = View.tail B.N v') (hk : View.key B.N v = View.key B.N v') :
    v = v' := by
  obtain ⟨hN, -, -, hIok, hOok, -⟩ := hV
  cases v with
  | spF x =>
    cases v' with
    | spF y => aesop
    | spB y => simp_all [View.key] <;> omega_nf
    | inP c => have := hIok _ hv'; grind [ChordOK, View.key]
    | inM c => have := hIok _ hv'; grind [ChordOK, View.key]
    | outP c => have := hOok _ hv'; grind [ChordOK, View.key]
    | outM c => have := hOok _ hv'; grind [ChordOK, View.key]
  | spB x =>
    cases v' with
    | spF y => simp_all [View.key] <;> omega_nf
    | spB y =>
      simp only [ViewOK] at hv hv'
      simp only [View.tail] at ht
      have e1 := eq_pred_of_succ hv rfl
      have e2 := eq_pred_of_succ hv' rfl
      grind
    | inP c => have := hIok _ hv'; grind [ChordOK, View.key]
    | inM c => have := hIok _ hv'; grind [ChordOK, View.key]
    | outP c => have := hOok _ hv'; grind [ChordOK, View.key]
    | outM c => have := hOok _ hv'; grind [ChordOK, View.key]
  | inP c =>
    have h0 := hIok _ hv; simp only [ChordOK] at h0
    cases v' with
    | spF y => simp_all [View.key] <;> omega_nf
    | spB y => grind [View.key]
    | inP c' =>
      grind [ChordOK, View.key, View.tail]
    | inM c' =>
      grind [ChordOK, View.key, View.tail]
    | outP c' => have := hOok _ hv'; grind [ChordOK, View.key]
    | outM c' => have := hOok _ hv'; grind [ChordOK, View.key]
  | inM c =>
    have h0 := hIok _ hv; simp only [ChordOK] at h0
    cases v' with
    | spF y => grind [View.key]
    | spB y => grind [View.key]
    | inP c' =>
      have := hIok _ hv'; grind [ChordOK, View.key, View.tail]
    | inM c' =>
      grind [ChordOK, View.key, View.tail]
    | outP c' => have := hOok _ hv'; grind [ChordOK, View.key]
    | outM c' => have := hOok _ hv'; grind [ChordOK, View.key]
  | outP c =>
    have h0 := hOok _ hv; simp only [ChordOK] at h0
    cases v' with
    | spF y => grind [View.key]
    | spB y => grind [View.key]
    | inP c' => have := hIok _ hv'; grind [ChordOK, View.key]
    | inM c' => have := hIok _ hv'; grind [ChordOK, View.key]
    | outP c' =>
      grind [ChordOK, View.key, View.tail]
    | outM c' =>
      grind [ChordOK, View.key, View.tail]
  | outM c =>
    have h0 := hOok _ hv; simp only [ChordOK] at h0
    cases v' with
    | spF y => grind [View.key]
    | spB y => grind [View.key]
    | inP c' => have := hIok _ hv'; grind [ChordOK, View.key]
    | inM c' => have := hIok _ hv'; grind [ChordOK, View.key]
    | outP c' =>
      have := hOok _ hv'; grind [ChordOK, View.key, View.tail]
    | outM c' =>
      grind [ChordOK, View.key, View.tail]

end Darts

/-! ## The map and its planarity -/

section Map

variable {B}

section
variable (d : Fin (2 * B.E))
include d
/-- The vertex of a dart (as a number). -/
def gN : ℕ := View.tail B.N (B.view d)

/-- The key of a dart (as a number). -/
def kN : ℕ := View.key B.N (B.view d)


end

theorem keyInj (hV : B.Valid) : KeyInj (gN (B := B)) (kN (B := B)) := by
  intro a b hg hk
  exact Fin.ext (view_inj hV a.2 b.2 (key_inj hV (view_ok a.2) (view_ok b.2) hg hk))

/-- The rotation of the book map. -/
noncomputable def rotP (hV : B.Valid) : Perm (Fin (2 * B.E)) := csuccPerm (keyInj hV)

/-- The opposite dart as a permutation. -/
def oppP : Perm (Fin (2 * B.E)) :=
  Function.Involutive.toPerm (fun d => ⟨oppN d, oppN_lt d.2⟩)
    (fun d => Fin.ext (oppN_oppN d))

@[simp] theorem oppP_val (d : Fin (2 * B.E)) : ((oppP (B := B)) d).1 = oppN d := rfl

section
variable (hV : B.Valid)
include hV
/-- The face permutation `rot ∘ opp` of the book map. -/
noncomputable def fpermP : Perm (Fin (2 * B.E)) := rotP hV * oppP

/-- **The face label is invariant under the face permutation.** -/
theorem label_fperm (d : Fin (2 * B.E)) :
    B.label (B.view (fpermP hV d)) = B.label (B.view d) := by
  set e := oppP (B := B) d with he
  have hev : B.view e = (B.view d).rev := by rw [he, oppP_val]; exact view_oppN d
  have hspec := csucc_spec (gN (B := B)) (kN (B := B)) e
  have hnext : B.IsNext (View.head B.N (B.view d)) (View.key B.N (B.view d).rev)
      (B.view (csucc (gN (B := B)) (kN (B := B)) e).1) := by
    have hge : gN e = View.head B.N (B.view d) := by
      grind [gN, View.tail_rev]
    have hke : kN e = View.key B.N (B.view d).rev := by grind [kN]
    obtain ⟨hg, hs⟩ := hspec
    refine ⟨view_ok (csucc (gN (B := B)) (kN (B := B)) e).2, by rw [← hge]; exact hg, ?_⟩
    rw [← hke, ← hge]
    rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine Or.inl ⟨h1, fun w' hw' ht hk => ?_⟩
      obtain ⟨f, hf, hfv⟩ := exists_view hw'
      have := h2 ⟨f, hf⟩ (by simp_all [gN] <;> omega_nf)
        (by unfold kN; simp_all)
      simp_all [kN] <;> omega_nf
    · refine Or.inr ⟨fun w' hw' ht => ?_, fun w' hw' ht => ?_⟩
      · obtain ⟨f, hf, hfv⟩ := exists_view hw'
        have := h1 ⟨f, hf⟩ (by simp_all [gN] <;> omega_nf)
        grind [kN]
      · obtain ⟨f, hf, hfv⟩ := exists_view hw'
        have := h2 ⟨f, hf⟩ (by simp_all [gN] <;> omega_nf)
        grind [kN]
  exact label_next hV (view_ok d.2) hnext

/-- The label is constant on the cycles of the face permutation. -/
theorem label_sameCycle {a b : Fin (2 * B.E)} (h : (fpermP hV).SameCycle a b) :
    B.label (B.view a) = B.label (B.view b) := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  have key : ∀ n : ℕ, B.label (B.view ((fpermP hV ^ n) a)) = B.label (B.view a) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => grind [pow_succ', Perm.mul_apply, label_fperm]
  simp_all

/-- The faces of the book map: the cycles of the face permutation. -/
abbrev FaceT : Type := Quotient (Perm.SameCycle.setoid (fpermP hV))

/-- **The book map.** -/
noncomputable def map :
    Separator.CombMap (Fin B.N) (FaceT hV) (Fin (2 * B.E)) where
  rot := rotP hV
  opp := oppP
  vert d := ⟨gN d, tail_lt hV (view_ok d.2)⟩
  face := Quotient.mk _
  opp_opp d := Fin.ext (oppN_oppN d)
  opp_ne d h := oppN_ne d.1 (congrArg Fin.val h)
  vert_rot d := Fin.ext (g_csucc (g := gN) (k := kN) d)
  sameCycle_of_vert d e h := csucc_sameCycle (keyInj hV) (congrArg Fin.val h)
  face_fperm d := Quotient.sound (show (fpermP hV).SameCycle (rotP hV (oppP d)) d from
    ⟨-1, by rw [zpow_neg_one, Perm.inv_eq_iff_eq]; rfl⟩)
  sameCycle_of_face _ _ h := Quotient.exact h
  vert_surj x := ⟨⟨2 * x.1, by unfold E; omega⟩, Fin.ext (by
    show View.tail B.N (B.view (2 * x.1)) = x.1
    simp_all [view, View.tail] <;> omega_nf)⟩
  face_surj := Quotient.mk_surjective


end

end Map

end BookData

namespace BookData

/-! ## Planarity -/

section Planar

variable {B : BookData}

noncomputable instance instFintypeFaceT (hV : B.Valid) : Fintype (FaceT hV) := Fintype.ofFinite _

noncomputable instance instDecEqFaceT (hV : B.Valid) : DecidableEq (FaceT hV) :=
  Classical.decEq _

section
variable {s : ℕ} (hs : s < B.N)
include hs
theorem view_spF : B.view (2 * s) = .spF s := by
  simp_all [view] <;> omega_nf

theorem view_spB : B.view (2 * s + 1) = .spB s := by
  unfold view
  grind

theorem two_mul_lt : 2 * s < 2 * B.E := by unfold E; omega

theorem two_mul_add_one_lt : 2 * s + 1 < 2 * B.E := by unfold E; omega


end

/-- **The book map is connected** (through the spine). -/
theorem connected (hV : B.Valid) : (B.map hV).Connected := by
  intro S hrot hopp d hd e
  have hN : 3 ≤ B.N := hV.1
  -- a set closed under the rotation contains whole vertices
  have hvert : ∀ x ∈ S, ∀ y : Fin (2 * B.E), gN y = gN x → y ∈ S := by
    intro x hx y hy
    have hsc : (rotP hV).SameCycle x y := csucc_sameCycle (keyInj hV) hy.symm
    obtain ⟨n, rfl⟩ := hsc.exists_nat_pow_eq
    clear hsc hy
    induction n with
    | zero => exact hx
    | succ n ih => rw [pow_succ', Perm.mul_apply]; exact hrot _ ih
  set t := gN d with ht
  have htN : t < B.N := tail_lt hV (view_ok d.2)
  have hstep : ∀ j : ℕ, ∀ y : Fin (2 * B.E), gN y = (t + j) % B.N → y ∈ S := by
    intro j
    induction j with
    | zero =>
      intro y hy
      refine hvert d hd y ?_
      rw [hy, Nat.add_zero, Nat.mod_eq_of_lt htN]
    | succ j ih =>
      intro y hy
      set s := (t + j) % B.N with hs
      have hsN : s < B.N := Nat.mod_lt _ (by omega)
      have hF : (⟨2 * s, two_mul_lt hsN⟩ : Fin (2 * B.E)) ∈ S := ih _ (by
        unfold gN; simp only; rw [view_spF hsN]; rfl)
      have hB := hopp _ hF
      refine hvert _ hB y ?_
      rw [hy]
      show (t + (j + 1)) % B.N = View.tail B.N (B.view (oppN (2 * s)))
      rw [show oppN (2 * s) = 2 * s + 1 by unfold oppN; split_ifs <;> omega, view_spB hsN]
      simp only [View.tail]
      grind
  have heN : gN e < B.N := tail_lt hV (view_ok e.2)
  refine hstep (gN e + B.N - t) e ?_
  rw [show t + (gN e + B.N - t) = gN e + B.N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt heN]

/-- The face label, on faces. -/
noncomputable def labelQ (hV : B.Valid) : FaceT hV → Bool × Finset (ℕ × ℕ) :=
  Quotient.lift (fun d => B.label (B.view d)) (fun _ _ h => label_sameCycle hV h)

section
variable {L : List (ℕ × ℕ)}
theorem Sup_inj {c c' : ℕ × ℕ} (hc : c ∈ L) (hc' : c' ∈ L)
    (h : Sup L c = Sup L c') : c = c' := by
  have h1 : c ∈ Sup L c' := h ▸ mem_Sup.2 ⟨hc, le_rfl, le_rfl⟩
  have h2 : c' ∈ Sup L c := h.symm ▸ mem_Sup.2 ⟨hc', le_rfl, le_rfl⟩
  rw [mem_Sup] at h1 h2
  aesop (add safe (by omega))

theorem Sup_nonempty {c : ℕ × ℕ} (hc : c ∈ L) : Sup L c ≠ ∅ := by
  intro h
  have : c ∈ Sup L c := mem_Sup.2 ⟨hc, le_rfl, le_rfl⟩
  simp_all


end

/-- **The book map has at least `|I| + |O| + 2` faces.** -/
theorem card_face_ge (hV : B.Valid) :
    B.I.length + B.O.length + 2 ≤ Fintype.card (FaceT hV) := by
  obtain ⟨hN, hIn, hOn, -⟩ := id hV
  -- the witness labels
  let f : Option (Fin B.I.length) ⊕ Option (Fin B.O.length) → Bool × Finset (ℕ × ℕ)
    | .inl none => (true, ∅)
    | .inl (some i) => (true, Sup B.I B.I[i])
    | .inr none => (false, ∅)
    | .inr (some j) => (false, Sup B.O B.O[j])
  have hmaps : ∀ a ∈ (Finset.univ : Finset (Option (Fin B.I.length) ⊕ Option (Fin B.O.length))),
      f a ∈ Finset.univ.image (labelQ hV) := by
    intro a _
    rw [Finset.mem_image]
    rcases a with (_ | i) | (_ | j)
    · refine ⟨Quotient.mk _ ⟨2 * (B.N - 1) + 1, two_mul_add_one_lt (by omega)⟩, Finset.mem_univ _,
        ?_⟩
      show B.label (B.view (2 * (B.N - 1) + 1)) = _
      rw [view_spB (by omega)]
      simp only [label, Enc, f]
      rw [ite_f (by omega)]
    · obtain ⟨d, hd, hdv⟩ := exists_view (B := B) (v := .inP B.I[i]) (List.getElem_mem _)
      refine ⟨Quotient.mk _ ⟨d, hd⟩, Finset.mem_univ _, ?_⟩
      show B.label (B.view d) = _
      rw [hdv]; rfl
    · refine ⟨Quotient.mk _ ⟨2 * (B.N - 1), two_mul_lt (by omega)⟩, Finset.mem_univ _, ?_⟩
      show B.label (B.view (2 * (B.N - 1))) = _
      rw [view_spF (by omega)]
      simp only [label, Enc, f]
      rw [ite_f (by omega)]
    · obtain ⟨d, hd, hdv⟩ := exists_view (B := B) (v := .outM B.O[j]) (List.getElem_mem _)
      refine ⟨Quotient.mk _ ⟨d, hd⟩, Finset.mem_univ _, ?_⟩
      show B.label (B.view d) = _
      rw [hdv]; rfl
  have hinj : Set.InjOn f (Finset.univ : Finset (Option (Fin B.I.length) ⊕
      Option (Fin B.O.length))) := by
    intro a _ b _ hab
    rcases a with (_ | i) | (_ | j) <;> rcases b with (_ | i') | (_ | j') <;>
      simp only [f, Prod.mk.injEq, Bool.true_eq_false, Bool.false_eq_true, false_and,
        true_and] at hab ⊢
    · exact absurd hab.symm (Sup_nonempty (List.getElem_mem _))
    · exact absurd hab (Sup_nonempty (List.getElem_mem _))
    · rw [Fin.ext ((hIn.getElem_inj_iff).1 (Sup_inj (List.getElem_mem _)
        (List.getElem_mem _) hab))]
    · exact absurd hab.symm (Sup_nonempty (List.getElem_mem _))
    · exact absurd hab (Sup_nonempty (List.getElem_mem _))
    · rw [Fin.ext ((hOn.getElem_inj_iff).1 (Sup_inj (List.getElem_mem _)
        (List.getElem_mem _) hab))]
  have h1 := Finset.card_le_card_of_injOn f hmaps hinj
  have h2 := Finset.card_image_le (s := (Finset.univ : Finset (FaceT hV))) (f := labelQ hV)
  simp only [Finset.card_univ, Fintype.card_sum, Fintype.card_option, Fintype.card_fin] at h1 h2
  omega

/-- **Planarity of the two-page book map.** -/
theorem planar (hV : B.Valid) : (B.map hV).Planar := by
  rw [Separator.CombMap.planar_iff]
  refine ⟨connected hV, ?_⟩
  have hF := card_face_ge hV
  unfold Separator.CombMap.euler Separator.CombMap.numE
  simp only [Fintype.card_fin]
  aesop (add simp [E]) (add safe (by omega))

end Planar

end BookData

end OracleBook

end

end Chazelle.Core
