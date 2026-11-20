/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import Mathlib.Basic.Real.Basic
public import PottsDiscontinuity.FK.Wiring
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

namespace PottsDiscontinuity.FK

variable {V : Type*} [Fintype V] (G : SimpleGraph V)
  (ξ : BoundaryCondition V) (A : Configuration G)

/-- Potentials constant on each genuine wired FK component. -/
def componentConstantFunctions : Submodule ℝ (V → ℝ) where
  carrier := {f | ∀ ⦃u v⦄, (componentSetoid ξ A).r u v → f u = f v}
  zero_mem' := by intro u v h; rfl
  add_mem' := by
    intro f g hf hg u v h
    simp [hf h, hg h]
  smul_mem' := by
    intro c f hf u v h
    simp [hf h]

/-- The equivalent local conditions: equality across each actual open edge and
across each pair identified by the chosen boundary partition. -/
def componentPotentialLocalPredicate (f : V → ℝ) : Prop :=
  (∀ ⦃u v⦄, (openGraph A).Adj u v → f u = f v) ∧
  (∀ ⦃u v⦄, ξ.partition.r u v → f u = f v)

omit [Fintype V] in
theorem componentConstant_iff_local (f : V → ℝ) :
    f ∈ componentConstantFunctions G ξ A ↔ componentPotentialLocalPredicate G ξ A f := by
  constructor
  · intro hf
    constructor
    · intro u v hadj
      apply hf
      exact actualConnected_component ξ (actualConnected_of_adj G A hadj)
    · intro u v hboundary
      apply hf
      exact boundary_component G ξ A hboundary
  · rintro ⟨hopen, hboundary⟩
    let eqS : Setoid V :=
      { r := fun u v => f u = f v
        iseqv := {
          refl := by grind
          symm := by grind
          trans := by grind } }
    have hreach :=
      reachableSetoid_le_of_adj eqS (by
        assumption)
    have hb : ξ.partition ≤ eqS := by
      assumption
    have hcomp : componentSetoid ξ A ≤ eqS := sup_le hreach hb
    exact hcomp

 def componentQuotientPullback :
    (Quotient (componentSetoid ξ A) → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun f v := f (Quotient.mk (componentSetoid ξ A) v)
  map_add' f g := by funext v; rfl
  map_smul' c f := by funext v; rfl

/-- Componentwise potentials are precisely real-valued functions on the
actual quotient by open connectivity and the boundary partition. -/
noncomputable def componentConstantQuotientEquiv :
    (Quotient (componentSetoid ξ A) → ℝ) ≃ₗ[ℝ]
      componentConstantFunctions G ξ A := by
  classical
  let e := (componentQuotientPullback G ξ A).codRestrict
    (componentConstantFunctions G ξ A) (by
      intro f u v h
      change f (Quotient.mk (componentSetoid ξ A) u) =
        f (Quotient.mk (componentSetoid ξ A) v)
      exact congrArg f (Quotient.sound h))
  refine LinearEquiv.ofBijective e ⟨?_, ?_⟩
  · intro f g hfg
    have hfun : componentQuotientPullback G ξ A f =
        componentQuotientPullback G ξ A g := congrArg Subtype.val hfg
    funext q
    refine Quotient.inductionOn q ?_
    intro v
    have hv := congrFun hfun v
    change f (Quotient.mk (componentSetoid ξ A) v) =
      g (Quotient.mk (componentSetoid ξ A) v) at hv
    exact hv
  · intro g
    let back : Quotient (componentSetoid ξ A) → ℝ :=
      Quotient.lift g.1 (by
        intro u v h
        exact g.2 h)
    refine ⟨back, ?_⟩
    apply Subtype.ext
    funext v
    rfl

omit [Fintype V] in
theorem componentConstantFunctions_finrank [Finite V] :
    Module.finrank ℝ (componentConstantFunctions G ξ A) =
      componentCount ξ A := by
  classical
  let : Fintype V := Fintype.ofFinite V
  rw [← LinearEquiv.finrank_eq (componentConstantQuotientEquiv G ξ A)]
  simp [componentCount, Nat.card_eq_fintype_card]

end PottsDiscontinuity.FK
