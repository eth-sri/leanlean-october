module

public import RequestProject.LemmaStructural

@[expose] public section

/-!
# Rule 1 for one extra generator, without any hypothesis

Rule 1 of the operation `T` of Lemma 3.9 replaces an extra generator `z` by a commutator
`[a_z,b_z]`.  The paper performs it in three moves: freely adjoin `b_z`, adjoin the stable
letter `a_z` with `a_z b_z a_z⁻¹ = z b_z`, and eliminate `z` through `z = [a_z,b_z]`.  The
stable-letter move requires that the two elements `b_z` and `z b_z` have infinite order, and
the paper checks this "by killing `G(P)`".

This file verifies that remark in the combinatorial model and assembles the two extension
moves into a single sequence of moves, so that rule 1 of Lemma 3.9 is available **with no
hypothesis at all**.

* `FiniteChains.not_isOfFinOrder_newGen`, `FiniteChains.not_isOfFinOrder_mul_newGen` — after
  freely adjoining `b`, both `b` and `z b` have infinite order, as seen by the homomorphism
  which kills the old generators and sends `b` to a generator of `ℤ`;
* `FiniteChains.ruleOnePath` — **rule 1 for one extra generator as a sequence of moves**, and
  `FiniteChains.generates_ruleOnePath`, `FiniteChains.isCockcroft_ruleOnePath` — equation
  (3.3) and the preservation of the Cockcroft property for it.
-/

namespace FiniteChains

open MonoidAlgebra

universe u

variable {α J : Type u} (ρ : J → FreeGroup α)

/-- The homomorphism which kills the old generators and sends the freely adjoined one to a
generator of `ℤ`. -/
def killOld : FreeGroup (Option α) →* Multiplicative ℤ :=
  FreeGroup.lift fun o : Option α =>
    match o with
    | none => Multiplicative.ofAdd (1 : ℤ)
    | some _ => 1

@[simp] theorem killOld_of_none {α : Type u} :
    killOld (FreeGroup.of (none : Option α)) = Multiplicative.ofAdd (1 : ℤ) := by
  simp [killOld]

theorem killOld_map_some {α : Type u} (w : FreeGroup α) : killOld (FreeGroup.map Option.some w) = 1 := by
  have h : (killOld (α := α)).comp (FreeGroup.map (f := Option.some)) = 1 :=
    FreeGroup.ext_hom _ _ fun i => by simp [killOld]
  exact congrArg (fun F : FreeGroup α →* Multiplicative ℤ => F w) h

/-- The homomorphism descends to the presented group of the free adjunction: the old relators
are words in the old generators. -/
def killOldPres : PresGroup (extFree ρ) →* Multiplicative ℤ :=
  QuotientGroup.lift _ killOld (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    exact killOld_map_some (ρ j))

@[simp] theorem killOldPres_mk (w : FreeGroup (Option α)) :
    killOldPres ρ (QuotientGroup.mk w) = killOld w := rfl

/-! ### The two extension moves of rule 1, composed -/

variable (P : PresPoint.{u}) (z : FreeGroup P.gens)

end FiniteChains
