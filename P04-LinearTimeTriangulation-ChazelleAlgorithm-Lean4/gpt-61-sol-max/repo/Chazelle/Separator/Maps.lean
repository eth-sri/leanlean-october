module

public meta import Chazelle.Arithmetic

public import Chazelle.Separator.Perm
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Linarith

/-!
# Combinatorial maps (planar separators, part 1)

A *combinatorial map* is a finite set of darts `D` with

* an involution `opp` without fixed points (the two darts of an edge),
* a permutation `rot` (the cyclic order of the darts around their vertex),

with *vertices* the cycles of `rot`, *edges* the cycles of `opp`, and *faces* the cycles of the
face permutation `fperm = rot * opp`, i.e. `fperm d = rot (opp d)`.  The face walk through `d`
goes along `d` to the head of `d` and continues with the next dart around that vertex.

To keep the vertex and face bookkeeping explicit, the structure `CombMap V F D` carries labels
`vert : D → V` and `face : D → F` whose fibres are exactly the `rot`- and `fperm`-cycles
(and which are onto).  Thus the numbers of vertices and faces are `Fintype.card V` and
`Fintype.card F`, and the number of edges is `Fintype.card D / 2`.

Main definitions and facts:

* `CombMap`, `fperm`, `head`, `numE`, `euler` (`χ = V - E + F`), `Connected`,
  `Planar := Connected ∧ χ = 2`, `faceDeg`, the underlying simple graph `graph`;
* `two_mul_numE : 2 * numE = |D|`, `card_darts_eq_sum_faceDeg : |D| = Σ faceDeg`;
* `numE_le_of_faceDeg` (**E ≤ 3V − 6** for planar maps whose faces have degree ≥ 3);
* `three_le_faceDeg_of_simple` (a connected loopless map without multiple edges on at least three
  vertices has all faces of degree ≥ 3), hence `numE_le_of_simple`;
* the dual map `dual` (vertices ↔ faces, rotation `fperm`), `Planar.dual`, and
  `dual_graph_adj` (its graph is the dual graph: faces sharing an edge);
* `ofPerm`: the map of two bare permutations (vertices, faces = quotient types of cycles).
-/

namespace Chazelle.Separator

@[expose] public section

open Equiv Finset

/-- A combinatorial map with labelled vertices `V`, faces `F` and darts `D`. -/
structure CombMap (V F D : Type*) where
  /-- rotation of the darts around their vertex -/
  rot : Perm D
  /-- the opposite dart of the same edge -/
  opp : Perm D
  /-- the vertex (tail) of a dart -/
  vert : D → V
  /-- the face to the left of a dart (the face cycle of `rot * opp` through it) -/
  face : D → F
  opp_opp : ∀ d, opp (opp d) = d
  opp_ne : ∀ d, opp d ≠ d
  vert_rot : ∀ d, vert (rot d) = vert d
  sameCycle_of_vert : ∀ d e, vert d = vert e → rot.SameCycle d e
  face_fperm : ∀ d, face (rot (opp d)) = face d
  sameCycle_of_face : ∀ d e, face d = face e → (rot * opp).SameCycle d e
  vert_surj : Function.Surjective vert
  face_surj : Function.Surjective face

namespace CombMap

variable {V F D : Type*} (M : CombMap V F D)

/-- The face permutation `fperm d = rot (opp d)`. -/
def fperm : Perm D := M.rot * M.opp

/-- The head of a dart: the vertex of the opposite dart. -/
def head (d : D) : V := M.vert (M.opp d)

section
variable (d : D)
/-- The face permutation: `fperm d = rot (opp d)`. -/
theorem fperm_apply : M.fperm d = M.rot (M.opp d) := rfl

/-- The face permutation preserves faces. -/
theorem face_fperm_apply : M.face (M.fperm d) = M.face d := M.face_fperm d

/-- The next dart along the face starts at the head of `d`. -/
theorem vert_fperm : M.vert (M.fperm d) = M.head d := M.vert_rot _

/-- The head of the opposite dart is the tail. -/
theorem head_opp : M.head (M.opp d) = M.vert d := by
  simp [head, M.opp_opp]


end

/-- `opp` is injective. -/
theorem opp_injective : Function.Injective M.opp := M.opp.injective

/-- The rotation in terms of the face permutation. -/
theorem rot_eq_fperm_opp (d : D) : M.rot d = M.fperm (M.opp d) := by
  rw [fperm_apply, M.opp_opp]



/-! ### Maps from bare permutations -/

/-! ### Counting -/

section Counting

variable [Fintype V] [Fintype F] [Fintype D]

/-- The number of edges. -/
def numE (_M : CombMap V F D) : ℕ := Fintype.card D / 2

/-- The Euler characteristic `V - E + F`. -/
def euler (M : CombMap V F D) : ℤ := (Fintype.card V : ℤ) - M.numE + Fintype.card F

omit [Fintype V] [Fintype F] in
/-- The number of darts is even. -/
theorem card_darts_even (M : CombMap V F D) : 2 ∣ Fintype.card D := by
  classical
  have h2 : M.opp ^ 2 = 1 := by
    ext d; simp [pow_two, M.opp_opp]
  have hs : M.opp.support = Finset.univ := by
    ext d; simp [Perm.mem_support, M.opp_ne]
  have := Perm.two_dvd_card_support h2
  simp_all

omit [Fintype V] [Fintype F] in
/-- Every edge has two darts: `|D| = 2E`. -/
theorem two_mul_numE : 2 * M.numE = Fintype.card D := by
  have := M.card_darts_even
  unfold numE; omega

/-- The Euler characteristic in dart form: `2χ = 2V - |D| + 2F`. -/
theorem two_mul_euler : 2 * M.euler =
    2 * (Fintype.card V : ℤ) - Fintype.card D + 2 * Fintype.card F := by
  have := M.two_mul_numE
  core_grind

variable [DecidableEq F]

/-- The degree of a face: its number of darts. -/
def faceDeg (g : F) : ℕ := (Finset.univ.filter (fun d => M.face d = g)).card

end Counting

/-! ### Connectivity and planarity -/

/-- A map is connected when the only nonempty dart set closed under `rot` and `opp` is
everything (the group generated by `rot` and `opp` acts transitively). -/
def Connected : Prop :=
  ∀ S : Set D, (∀ d ∈ S, M.rot d ∈ S) → (∀ d ∈ S, M.opp d ∈ S) → ∀ d ∈ S, ∀ e, e ∈ S

/-- A planar map: connected with Euler characteristic `2`. -/
def Planar [Fintype V] [Fintype F] [Fintype D] : Prop := M.Connected ∧ M.euler = 2

/-- Connectivity through faces: a nonempty dart set closed under `fperm` and `opp` is
everything. -/
theorem Connected.of_fperm {M : CombMap V F D} (hM : M.Connected) (S : Set D)
    (hf : ∀ d ∈ S, M.fperm d ∈ S)
    (ho : ∀ d ∈ S, M.opp d ∈ S) {d : D} (hd : d ∈ S) (e : D) : e ∈ S :=
  hM S (fun x hx => by rw [M.rot_eq_fperm_opp]; simp_all) ho d hd e

/-- Connectivity through face labels. -/
theorem Connected.of_face {M : CombMap V F D} (hM : M.Connected) (S : Set D)
    (hv : ∀ d e, M.face d = M.face e → d ∈ S → e ∈ S)
    (ho : ∀ d ∈ S, M.opp d ∈ S) {d : D} (hd : d ∈ S) (e : D) : e ∈ S :=
  hM.of_fperm S (fun x hx => hv x _ (M.face_fperm_apply x).symm hx) ho hd e

/-! ### The underlying simple graph -/

/-- The underlying simple graph: distinct vertices joined by some dart. -/
def graph : SimpleGraph V where
  Adj u w := u ≠ w ∧ ∃ d, M.vert d = u ∧ M.head d = w
  symm := ⟨by
    rintro u w ⟨hne, d, rfl, rfl⟩
    exact ⟨hne.symm, M.opp d, rfl, M.head_opp d⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

/-! ### The dual map -/

/-- `fperm * opp = rot`. -/
theorem fperm_mul_opp : M.fperm * M.opp = M.rot := by
  ext d; simp [fperm, M.opp_opp]

/-- The **dual map**: vertices and faces exchanged, the rotation of the dual is the face
permutation `fperm` and the edges are the same (`opp`). -/
def dual : CombMap F V D where
  rot := M.fperm
  opp := M.opp
  vert := M.face
  face := M.vert
  opp_opp := M.opp_opp
  opp_ne := M.opp_ne
  vert_rot := M.face_fperm_apply
  sameCycle_of_vert := M.sameCycle_of_face
  face_fperm d := by
    show M.vert (M.fperm (M.opp d)) = M.vert d
    rw [fperm_apply, M.opp_opp, M.vert_rot]
  sameCycle_of_face d e h := by rw [M.fperm_mul_opp]; exact M.sameCycle_of_vert d e h
  vert_surj := M.face_surj
  face_surj := M.vert_surj





end CombMap

end

end Chazelle.Separator
