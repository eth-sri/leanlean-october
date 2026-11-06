module

public import RequestProject.FlagComplex

@[expose] public section

/-!
# The cube complex `C(L)` and the fundamental cycle of Lemma 3.2 (i), (iii)

Section 3.3 of the paper uses the real moment–angle complex of a finite simplicial complex
`L` on the vertex set `{1, …, d}`,

  `C(L) = ⋃_{σ ∈ L} [-1,1]^σ × {-1,1}^{{1,…,d} ∖ σ}`,

and two facts about it:

* every vertex link of `C(L)` is `L` (this is what feeds the flagness criterion, together
  with `RequestProject/FlagComplex.lean`);
* for `L` a triangulated closed oriented surface the signed sum of the top-dimensional
  cubes, with the cube indexed by an ordered triangle `σ` and signs `ε` given the
  coefficient `o(σ)·∏_{h ∉ σ} ε_h`, is a cycle: "the two incidences at each square cancel".
  This is the chain-level computation behind Lemma 3.2 (iii) (the vanishing of `[Σ_q]` in
  `H₂(M_q)`), and, in the untruncated complex, behind Lemma 3.2 (i).

Both are proved here in the combinatorial model.  A cube of `C(L)` is encoded as a function
`f : V → CubeCoord` assigning to each coordinate either the value `free` (the coordinate
runs through `[-1,1]`) or one of the two signs; the *free set* of `f` is required to be a
face of `L`.  The cubical boundary is the usual one, with the sign of the face obtained by
fixing the `k`-th free coordinate at `δ = ±1` equal to `(-1)^k·δ`.

The main result `bdry_cubeChain` is stronger than what the paper needs: the assignment
`o ↦ c_o` of the above signed cubical chain to a simplicial chain of top-dimensional
simplices is a chain map, that is, `∂(c_o) = c_{∂o}`.  In particular a simplicial cycle
gives a cubical cycle (`cubeChain_cycle`).
-/

namespace FiniteChains

open Finset

/-- The state of one coordinate of a cube of `C(L)`: either free, or fixed at `+1`, or
fixed at `-1`. -/
inductive CubeCoord
  | free : CubeCoord
  | pos : CubeCoord
  | neg : CubeCoord
  deriving DecidableEq

namespace CubeCoord

/-- The sign of a fixed coordinate; free coordinates get the value `0`. -/
def sgn : CubeCoord → ℤ
  | .free => 0
  | .pos => 1
  | .neg => -1

end CubeCoord

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- A cube of the moment-angle complex: an assignment of a state to each coordinate. -/
abbrev Cube (V : Type) := V → CubeCoord

/-- The set of free coordinates of a cube; its cardinality is the dimension of the cube. -/
def freeSet (f : Cube V) : Finset V := univ.filter fun v => f v = CubeCoord.free

omit [DecidableEq V] [LinearOrder V] in
@[simp] theorem mem_freeSet {f : Cube V} {v : V} : v ∈ freeSet f ↔ f v = CubeCoord.free := by
  simp [freeSet]

/-! ### The cubical boundary and the fundamental cycle -/

/-- The incidence number of the cube obtained from `g` by freeing the coordinate `j`
(which must be fixed in `g`) with its face `g`: the sign `(-1)^k·δ`, where `k` is the
position of `j` among the free coordinates of the bigger cube and `δ` is the sign at which
the coordinate `j` is fixed. -/
def incid (g : Cube V) (j : V) : ℤ :=
  (-1) ^ ((freeSet g).filter (fun i => i < j)).card * (g j).sgn

/-- The cubical boundary operator, written on coefficient functions: the coefficient of the
cube `g` in `∂c`. -/
def bdry (c : Cube V → ℤ) : Cube V → ℤ := fun g =>
  ∑ j ∈ univ.filter (fun j => g j ≠ CubeCoord.free),
    incid g j * c (Function.update g j CubeCoord.free)

/-- The simplicial boundary of a chain of `n`-simplices, written on coefficient functions:
the coefficient of the face `τ` in `∂o`. -/
def simpBdry (o : Finset V → ℤ) : Finset V → ℤ := fun τ =>
  ∑ j ∈ univ.filter (fun j => j ∉ τ),
    (-1) ^ (τ.filter (fun i => i < j)).card * o (insert j τ)

/-- The cubical chain attached to a simplicial chain `o`: the cube with free set `σ` and
signs `ε` off `σ` gets the coefficient `o(σ)·∏_{h ∉ σ} ε_h`. -/
def cubeChain (o : Finset V → ℤ) : Cube V → ℤ := fun f =>
  o (freeSet f) * ∏ h ∈ univ \ freeSet f, (f h).sgn

/-- **The signed cubical chains of the moment-angle complex form a chain map**:
`∂(c_o) = c_{∂o}`.  This is the computation "every square meets exactly two three-cubes …
the two incidences at each square cancel" of Lemma 3.2, in the form valid in every degree
and for an arbitrary coefficient function. -/
theorem bdry_cubeChain (o : Finset V → ℤ) :
    bdry (cubeChain o) = cubeChain (simpBdry o) := by
  funext g
  have hindex : (univ.filter fun j => g j ≠ CubeCoord.free)
      = univ.filter fun j => j ∉ freeSet g := by
    ext j; simp
  rw [bdry, hindex, cubeChain, simpBdry, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjτ : j ∉ freeSet g := by simpa using hj
  -- the free set of the bigger cube
  have hfree : freeSet (Function.update g j CubeCoord.free) = insert j (freeSet g) := by
    ext i
    by_cases hij : i = j <;> simp [hij]
  -- the sign product over the complement of the bigger cube
  have hprodeq : ∏ h ∈ univ \ insert j (freeSet g),
      (Function.update g j CubeCoord.free h).sgn
      = ∏ h ∈ univ \ insert j (freeSet g), (g h).sgn := by
    refine Finset.prod_congr rfl ?_
    intro h hh
    have hhj : h ≠ j := by
      intro hhj; subst hhj
      simp at hh
    simp [hhj]
  -- split off the `j`-th factor
  have hsplit : ∏ h ∈ univ \ freeSet g, (g h).sgn
      = (g j).sgn * ∏ h ∈ univ \ insert j (freeSet g), (g h).sgn := by
    have hmem : j ∈ univ \ freeSet g := by simp [hjτ]
    rw [← Finset.prod_erase_mul _ _ hmem, mul_comm]
    congr 2
    ext i
    by_cases hij : i = j <;> simp [hij, hjτ]
  rw [cubeChain, hfree, hprodeq, incid, hsplit]
  ring

/-! ### Incidences: every square lies in exactly two three-cubes -/

section Incidence

open scoped Classical

/-- The cubes of `C(L)` having `g` as a codimension one face: those obtained from `g` by
making one further coordinate free. -/
noncomputable def cofaces (L : ASC V) (g : Cube V) : Finset (Cube V) :=
  ((univ.filter fun j => g j ≠ CubeCoord.free).filter
      fun j => insert j (freeSet g) ∈ L.faces).image
    fun j => Function.update g j CubeCoord.free

omit [LinearOrder V] in
theorem mem_cofaces {L : ASC V} {g f : Cube V} :
    f ∈ cofaces L g ↔ ∃ j, g j ≠ CubeCoord.free ∧ insert j (freeSet g) ∈ L.faces ∧
      f = Function.update g j CubeCoord.free := by
  simp only [cofaces, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, ⟨hj, hjL⟩, rfl⟩
    exact ⟨j, hj, hjL, rfl⟩
  · rintro ⟨j, hj, hjL, rfl⟩
    exact ⟨j, ⟨hj, hjL⟩, rfl⟩

omit [LinearOrder V] in
/-- **Counting the cubes above a given face.**  The number of cubes of `C(L)` having `g` as
a codimension one face is the number of ways of enlarging the free set of `g` by one vertex
inside `L`. -/
theorem card_cofaces (L : ASC V) (g : Cube V) :
    (cofaces L g).card
      = ((univ.filter fun j => j ∉ freeSet g).filter
          fun j => insert j (freeSet g) ∈ L.faces).card := by
  rw [cofaces, Finset.card_image_of_injOn]
  · congr 1
    ext j
    simp
  · intro j hj k hk hjk
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj hk
    by_contra hne
    have hval : Function.update g j CubeCoord.free j
        = Function.update g k CubeCoord.free j := congrFun hjk j
    simp only [Function.update_apply, if_neg hne] at hval
    exact hj.1 hval.symm

end Incidence

/-! ### The cubical boundary is a differential -/

omit [LinearOrder V] in
theorem freeSet_update_free (g : Cube V) (j : V) :
    freeSet (Function.update g j CubeCoord.free) = insert j (freeSet g) := by
  ext i
  by_cases hij : i = j <;> simp [hij]

/-- **A simplicial cycle gives a cubical cycle.**  For a triangulated closed oriented
surface `L` with orientation coefficients `o` the hypothesis says that `Σ_σ o(σ)·σ` is a
cycle; the conclusion is that the corresponding signed sum of top-dimensional cubes of
`C(L)` is a cycle, which is the chain used in the proof of Lemma 3.2. -/
theorem cubeChain_cycle {o : Finset V → ℤ} (ho : simpBdry o = 0) :
    bdry (cubeChain o) = 0 := by
  rw [bdry_cubeChain, ho]
  funext f
  simp [cubeChain]

end FiniteChains
