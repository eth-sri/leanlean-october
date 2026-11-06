module
public import Mathlib

public import PottsDiscontinuity.FK.Graph
public import Mathlib.Data.Fintype.Option
public import Mathlib.Tactic

/-!
# Counting components after wiring a vertex boundary

The quotient definition of finite FK components agrees with the description
that counts every component disjoint from the boundary separately and all
components meeting the boundary as one. This proof is original to this port.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

noncomputable section

open Classical

variable {V : Type*}

abbrev boundaryAvoidingComponents (H : SimpleGraph V) (W : Set V) :=
  {c : H.ConnectedComponent // ∀ x, H.connectedComponentMk x = c → x ∉ W}

def componentBoundaryLabel (H : SimpleGraph V) (W : Set V)
    (c : H.ConnectedComponent) : Option (boundaryAvoidingComponents H W) := by
  classical
  exact if h : ∀ y, H.connectedComponentMk y = c → y ∉ W
    then some ⟨c, h⟩ else none

def wiredComponentLabel (H : SimpleGraph V) (W : Set V) (x : V)  :=
  componentBoundaryLabel H W (H.connectedComponentMk x)

section

variable (H : SimpleGraph V) (W : Set V)


private theorem wiredComponentLabel_eq_of_connected 
    {x y : V} (hxy : H.Reachable x y) :
    wiredComponentLabel H W x = wiredComponentLabel H W y := congrArg (componentBoundaryLabel H W) (SimpleGraph.ConnectedComponent.sound hxy)

private theorem wiredComponentLabel_eq_none 
    {x : V} (hx : x ∈ W) : wiredComponentLabel H W x = none := by
  grind +locals

private theorem wiredComponentSetoid_eq_ker  :
    H.reachableSetoid ⊔ (BoundaryCondition.wired W).partition =
      Setoid.ker (wiredComponentLabel H W) := by
  
  apply le_antisymm
  · apply sup_le
    · intro x y hxy
      exact wiredComponentLabel_eq_of_connected H W hxy
    · intro x y hxy
      rcases (BoundaryCondition.wired_rel W x y).mp hxy with rfl | ⟨hx, hy⟩
      · rfl
      · simp_all [wiredComponentLabel_eq_none]
  · intro x y hxy
    change wiredComponentLabel H W x = wiredComponentLabel H W y at hxy
    by_cases hx : ∀ z, H.connectedComponentMk z = H.connectedComponentMk x → z ∉ W
    · by_cases hy : ∀ z, H.connectedComponentMk z = H.connectedComponentMk y → z ∉ W
      · simp only [wiredComponentLabel, componentBoundaryLabel, dite_eq_left hx,
          dite_eq_left hy, Option.some.injEq] at hxy
        
        exact (le_sup_left : H.reachableSetoid ≤
          H.reachableSetoid ⊔ (BoundaryCondition.wired W).partition)
            (SimpleGraph.ConnectedComponent.exact (congrArg Subtype.val hxy))
      · grind +locals
    · by_cases hy : ∀ z, H.connectedComponentMk z = H.connectedComponentMk y → z ∉ W
      · grind +locals
      · push Not at hx hy
        obtain ⟨a, ha, haW⟩ := hx
        obtain ⟨b, hb, hbW⟩ := hy
        let s := H.reachableSetoid ⊔ (BoundaryCondition.wired W).partition
        
        
        
        exact s.trans ((le_sup_left : H.reachableSetoid ≤ s)
                         (SimpleGraph.ConnectedComponent.exact ha.symm)) (s.trans ((le_sup_right : (BoundaryCondition.wired W).partition ≤ s)
                                      ((BoundaryCondition.wired_rel W a b).mpr (Or.inr ⟨haW, hbW⟩))) ((le_sup_left : H.reachableSetoid ≤ s)
                                          (SimpleGraph.ConnectedComponent.exact hb)))

private theorem wiredComponentLabel_surjective 
    (hW : W.Nonempty) : Function.Surjective (wiredComponentLabel H W) := by
  
  intro c
  cases c with
  | none =>
      obtain ⟨x, hx⟩ := hW
      exact ⟨x, wiredComponentLabel_eq_none H W hx⟩
  | some c =>
      obtain ⟨x, hx⟩ := Quot.mk_surjective c.val
      have hc : ∀ y, H.connectedComponentMk y = H.connectedComponentMk x → y ∉ W := fun y hy => c.property y (hy.trans hx)
      refine ⟨x, ?_⟩
      simp only [wiredComponentLabel, componentBoundaryLabel, dite_eq_left hc]
      congr 1
      exact Subtype.ext hx

end

/-- Wiring a nonempty boundary leaves one boundary component and every original
component disjoint from that boundary. -/
theorem card_wiredComponentQuotient_of_nonempty [Finite V]
    (H : SimpleGraph V) (W : Set V) (hW : W.Nonempty) :
    Nat.card (Quotient (H.reachableSetoid ⊔ (BoundaryCondition.wired W).partition)) =
      Nat.card {c : H.ConnectedComponent //
        ∀ x, H.connectedComponentMk x = c → x ∉ W} + 1 := by
  
  rw [wiredComponentSetoid_eq_ker]
  
  let : Fintype (boundaryAvoidingComponents H W) := Fintype.ofFinite _
  rw [ Nat.card_congr
         (Setoid.quotientKerEquivOfSurjective (wiredComponentLabel H W)
           (wiredComponentLabel_surjective H W hW)) , Nat.card_eq_fintype_card, Fintype.card_option]
  rw [Nat.card_eq_fintype_card]

/-- The ported wired component count equals the frozen description: components
avoiding the boundary plus one exactly when a component meets the boundary. -/
theorem componentCount_wired_eq_boundary_avoiding [Finite V]
    (G : SimpleGraph V) (W : Set V) (A : Configuration G) :
    componentCount G (BoundaryCondition.wired W) A =
      Nat.card {c : (openGraph G A).ConnectedComponent //
        ∀ x, (openGraph G A).connectedComponentMk x = c → x ∉ W} +
      if ∃ c : (openGraph G A).ConnectedComponent,
          ∃ x, (openGraph G A).connectedComponentMk x = c ∧ x ∈ W then 1 else 0 := by
  
  have hex : (∃ c : (openGraph G A).ConnectedComponent,
      ∃ x, (openGraph G A).connectedComponentMk x = c ∧ x ∈ W) ↔ W.Nonempty := by
    aesop
  rw [hex]
  by_cases hW : W.Nonempty
  · rw [ite_eq_left hW]
    exact card_wiredComponentQuotient_of_nonempty (openGraph G A) W hW
  · have hWe  := Set.not_nonempty_iff_eq_empty.mp hW
    subst W
    have hp : (BoundaryCondition.wired (∅ : Set V)).partition = ⊥ := by
      aesop
    simp only [componentCount, componentSetoid, hp, sup_bot_eq, Set.mem_empty_iff_false, not_false_eq_true, implies_true, Nat.card_subtype_true, Set.not_nonempty_empty]
    rfl

end
end PottsDiscontinuity.FK
