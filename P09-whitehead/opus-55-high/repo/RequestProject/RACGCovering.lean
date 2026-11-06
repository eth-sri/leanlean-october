import RequestProject.RACGCayleyGraph
import RequestProject.Tac


/-!
# The Cayley graph covers the one-skeleton of `C(L)`

The complex `C(L)` of the paper (the real moment-angle complex of `L`) has as vertex set the
sign vectors on the vertices of `L`, two of them being joined when they differ in exactly one
coordinate, and a square for every edge of `L`.  Its fundamental group is the kernel of the
abelianisation `W_L → (ℤ/2)^{L⁰}`.

This file constructs that abelianisation combinatorially and shows that it is a **covering map
of graphs** from the Cayley graph of `W_L` onto the one-skeleton of `C(L)`:

* `FiniteChains.RACG.phi` — the parity homomorphism `W_L → (ℤ/2)^{L⁰}`, defined on reduced
  traces (`FiniteChains.RACG.phi_mul`, `FiniteChains.RACG.phi_gen`);
* `FiniteChains.RACG.cubeGraph` — the one-skeleton of `C(L)`: sign vectors, with an edge for
  each change of one coordinate;
* `FiniteChains.RACG.phi_map_adj` — `phi` is a graph homomorphism;
* `FiniteChains.RACG.phi_unique_lift` — **the covering property**: every edge of `C(L)` at
  `phi x` lifts uniquely to an edge of the Cayley graph at `x`;
* `FiniteChains.RACG.phi_square` — squares of the Cayley graph go to squares of `C(L)`;
* `FiniteChains.RACG.phi_exists_preimage` — every vertex of `C(L)` (a finitely supported sign
  vector) is hit.

Together with `FiniteChains.RACG.cayleyGraph_connected`,
`FiniteChains.RACG.cayleyMedianSimpleGraph` and the simple connectivity of the square complex of
a median graph, this identifies the Cayley graph with the one-skeleton of the universal cover
of `C(L)`.
-/

bwd

namespace FiniteChains.RACG

universe u

variable {V : Type u} [DecidableEq V] (A : CommRel V)

/-! ### The parity of a word -/

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  revert a
  decide

/-- The indicator vector of a generator. -/
def eVec (s : V) : V → ZMod 2 := fun v => if v = s then 1 else 0

/-- The parity vector of a word: the number of occurrences of each letter, modulo two. -/
def parList (l : List V) : V → ZMod 2 := fun v => (l.count v : ZMod 2)


@[simp] theorem parList_cons s (l : List V) :
    parList (s :: l) = eVec s + parList l := by
  funext v
  by_cases h : v = s
  · subst h
    simp [parList, eVec, add_comm]
  · simp [parList, eVec, h, Ne.symm h]

theorem parList_append (l m : List V) : parList (l ++ m) = parList l + parList m := by
  funext v
  simp [parList, List.count_append, Pi.add_apply, Nat.cast_add]

omit [DecidableEq V] in
/-- A commutation of adjacent letters permutes the word. -/
theorem Swap.perm {Cm : V → V → Prop} {l m : List V} (h : Swap Cm l m) : l.Perm m := by
  induction h with
  | head _ q => tauto
  | cons x _ ih => exact ih.cons x

theorem parList_ceq (h : CEq A.rel l m) : parList l = parList m := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      refine ih.trans ?_
      funext v
      exact congrArg Nat.cast (hstep.perm |>.count_eq v)

/-- The parity vector of a reduced trace. -/
def parTr : Tr A → V → ZMod 2 :=
  Quotient.lift (parList ·.1)
    (fun _ _ h => parList_ceq A h)


/-- An elementary move changes the parity vector by the corresponding generator. -/
theorem parTr_act s t : parTr A (act A s t) = eVec s + parTr A t := by
  classical
  induction t using Quotient.inductionOn with
  | _ l =>
      by_cases hc : canStart A.rel s l.1
      · have hpop := actRep_of_canStart A hc
        have hceq :=
          ceq_popStart A.rel_symm hc
        have h1 : parList l.1 = eVec s + parList (popStart s l.1) := by
          rw [parList_ceq A hceq, parList_cons]
        have h2 : parTr A (act A s (Quotient.mk _ l)) = parList (popStart s l.1) := by
          show parList (actRep A s l).1 = _
          simp_all
        rw [h2]
        show parList (popStart s l.1) = eVec s + parList l.1
        rw [h1]
        grind [Pi.add_apply]
      · have hact := actRep_of_not_canStart A hc
        have h2 : parTr A (act A s (Quotient.mk _ l)) = parList (s :: l.1) := by
          show parList (actRep A s l).1 = _
          simp_all
        aesop

/-! ### The parity homomorphism of the group -/

/-- The parity homomorphism `W_L → (ℤ/2)^{L⁰}`: the abelianisation of the right-angled Coxeter
group, read on reduced traces. -/
noncomputable def phi (x : CayGroup A) :=
  parTr A ((x : Equiv.Perm (Tr A)) (oneTr A))

theorem cword_append l m : cword A (l ++ m) = cword A l * cword A m :=
  Subtype.ext (by simpa using wordPerm_append A l m)

theorem phi_cword l : phi A (cword A l) = parList l := by
  induction l with
  | nil =>
      rfl
  | cons s t ih =>
      have hval : ((cword A (s :: t) : CayGroup A) : Equiv.Perm (Tr A)) (oneTr A)
          = act A s (((cword A t : CayGroup A) : Equiv.Perm (Tr A)) (oneTr A)) := by
        rfl
      show parTr A _ = _
      rw [hval, parTr_act, parList_cons]
      tauto

theorem phi_mul x y : phi A (x * y) = phi A x + phi A y := by
  obtain ⟨l, _, rfl⟩ := exists_cword A x
  obtain ⟨m, _, rfl⟩ := exists_cword A y
  simp [← cword_append, phi_cword, parList_append]

/-! ### The one-skeleton of `C(L)` and the covering property -/

/-! ### The deck transformations -/

@[simp] theorem phi_one : phi A 1 = 0 := by
  rfl

theorem phi_inv x : phi A x⁻¹ = phi A x := by
  have h : phi A x + phi A x⁻¹ = 0 := by
    rw [← phi_mul, mul_inv_cancel, phi_one]
  funext v
  have hv : phi A x v + phi A x⁻¹ v = 0 := congrFun h v
  grind
