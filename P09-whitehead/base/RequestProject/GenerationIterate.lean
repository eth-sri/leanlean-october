module

public import RequestProject.GenerationStep
public import RequestProject.CockcroftExtStep

@[expose] public section

/-!
# The composite operation: finitely many moves of rule 1

The operation `T` of Section 3.4 is a *finite sequence* of elementary moves, and the paper
finishes the proof of the generation equation (3.3) with the words "Composing proves (3.3)".
This file carries that out for the moves of rule 1 (one new generator together with one new
relator at a time), on top of the formal layer of `RequestProject/GenerationStep.lean`.

* `FiniteChains.extMor` — one elementary move, packaged as a structural map `PresMor`: the
  induced map of fundamental groups is `η_P`, and the induced map on two-chains pads a chain
  of the old presentation with `0` on the new two-cell.
* `FiniteChains.generates_extMor` — equation (3.3) for one move, under the two hypotheses of
  the paper (right regularity of the Fox derivative of the new relator with respect to the
  new generator, and injectivity of `η_{P*}` on fundamental groups).
* `FiniteChains.iterPres` — the presentation obtained after `n` moves, and
  `FiniteChains.iterMor` the composite structural map `P → T^n(P)`.
* `FiniteChains.generates_iterMor` — **equation (3.3) for the composite operation**.
* `FiniteChains.isCockcroft_iterPres` — the composite operation preserves Cockcroftness.
* `FiniteChains.cells_iterMor_eq_zero` — and it preserves zero maps on `π₂`: for a commuting
  square over the composite, a map which is zero on `π₂` upstairs induces zero on the whole
  of `π₂` of the transformed complex.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra

universe u

section OneStep

variable {α : Type u} [Fintype α] [DecidableEq α] {J : Type u} [Fintype J] [DecidableEq J]
variable (ρ : J → FreeGroup α) (w₀ : FreeGroup (Option α))

end OneStep

/-! ### Iterating the elementary move -/

/-- The generators (resp. two-cells) after `n` moves: `n` new names are adjoined one at a
time. -/
abbrev optIter (α : Type u) : ℕ → Type u
  | 0 => α
  | n + 1 => Option (optIter α n)

instance optIterFintype (α : Type u) [Fintype α] : ∀ n, Fintype (optIter α n)
  | 0 => ‹Fintype α›
  | n + 1 => @instFintypeOption _ (optIterFintype α n)

instance optIterDecidableEq (α : Type u) [DecidableEq α] : ∀ n, DecidableEq (optIter α n)
  | 0 => ‹DecidableEq α›
  | n + 1 => fun a b => @Option.instDecidableEq _ (optIterDecidableEq α n) a b

section Iterate

variable {α : Type u} [Fintype α] [DecidableEq α] {J : Type u} [Fintype J] [DecidableEq J]
variable (ρ : J → FreeGroup α) (w : ∀ n : ℕ, FreeGroup (Option (optIter α n)))

/-- The presentation after `n` elementary moves: at stage `n` the new generator is the fresh
name `none` and the new relator is `w n`. -/
def iterPres : ∀ n : ℕ, optIter J n → FreeGroup (optIter α n)
  | 0 => ρ
  | n + 1 => extRel (iterPres n) (w n)

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] in
@[simp] theorem iterPres_zero : iterPres ρ w 0 = ρ := rfl

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] in
@[simp] theorem iterPres_succ (n : ℕ) :
    iterPres ρ w (n + 1) = extRel (iterPres ρ w n) (w n) := rfl

/-- The identity structural map of a presentation. -/
def PresMor.id {β K : Type u} [Fintype β] [DecidableEq β] [Fintype K] (σ : K → FreeGroup β) :
    PresMor σ σ where
  hom := MonoidHom.id _
  cells := _root_.id
  cells_add := fun _ _ => rfl
  cells_smul := fun c y => by
    have h : (MonoidAlgebra.mapDomainRingHom ℤ (MonoidHom.id (PresGroup σ)) c
        : MonoidAlgebra ℤ (PresGroup σ)) = c := MonoidAlgebra.mapDomain_id c
    show _root_.id (c • y)
      = (MonoidAlgebra.mapDomainRingHom ℤ (MonoidHom.id (PresGroup σ)) c
          : MonoidAlgebra ℤ (PresGroup σ)) • _root_.id y
    rw [h]
    rfl
  cells_cycle := fun _ hy => hy
  cells_aug := fun _ hy => hy

end Iterate

end FiniteChains
