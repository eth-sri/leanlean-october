module

public import RequestProject.RACGSquareComplex
public import RequestProject.SquareComplexMonodromy
public import RequestProject.SquareComplexCoverExists

@[expose] public section

/-!
# The fundamental group of `C(L)` is the kernel of the parity map

The paper computes the fundamental group of the real moment-angle complex `C(L)`: it is the
kernel of the abelianisation `W_L → (ℤ/2)^{L⁰}` of the right-angled Coxeter group.  This file
proves that statement in the combinatorial category, for the edge-path group
`FiniteChains.SquareComplex.Pi1` of the square complex `C(L)`:

* `FiniteChains.RACG.kerPhi` — the kernel of the parity map, as a subgroup of `W_L`;
* `FiniteChains.RACG.liftEnd_deck` — the lift of a walk of `C(L)` is equivariant for the deck
  transformations, that is for left multiplication by elements of the kernel;
* `FiniteChains.RACG.pi1Equiv` — **the monodromy is a group isomorphism**
  `π₁(C(L)) ≃* ker(W_L → (ℤ/2)^{L⁰})`, and `FiniteChains.RACG.pi1_cubeCx_equiv` is the same
  statement with the base point written as the zero sign vector.

The proof uses the combinatorial covering theory of
`RequestProject/SquareComplexCovering.lean` (the parity map is a covering of square complexes,
`FiniteChains.RACG.isCovering_phi`), the simple connectivity of the Cayley complex and the
monodromy bijection of `RequestProject/SquareComplexMonodromy.lean`.
-/

namespace FiniteChains
namespace RACG

open SquareComplex

universe u

variable {V : Type u} [DecidableEq V] (A : CommRel V)

/-- The kernel of the parity homomorphism `W_L → (ℤ/2)^{L⁰}`, as a subgroup. -/
noncomputable def kerPhi : Subgroup (CayGroup A) where
  carrier := {x | phi A x = 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [phi_mul, ha, hb, add_zero]
  one_mem' := by simp [Set.mem_setOf_eq]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [phi_inv, ha]

@[simp] theorem mem_kerPhi {x : CayGroup A} : x ∈ kerPhi A ↔ phi A x = 0 := Iff.rfl

variable (hdim : ∀ t : Finset V, (∀ s ∈ t, ∀ r ∈ t, s ≠ r → A.rel s r) → t.card ≤ 3)

end RACG
end FiniteChains
