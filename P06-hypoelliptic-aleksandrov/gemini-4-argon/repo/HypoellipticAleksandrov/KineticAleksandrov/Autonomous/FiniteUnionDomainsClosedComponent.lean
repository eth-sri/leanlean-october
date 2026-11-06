module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsNesting
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsComponents
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripIntervalBoundary

/-! # Literal union membership and exits on a fixed component closure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/- On the closure of a component, union interior membership is precisely component membership. -/
theorem FiniteIntervalUnion.mem_carrier_on_component_closure (H : FiniteIntervalUnion)
    (i ) {v } (hv : v ∈ closure (H.component i).carrier) :
    v ∈ H.carrier ↔ v ∈ (H.component i).carrier := by
  constructor
  · intro hu
    obtain ⟨j, hj⟩ := mem_iUnion.mp hu
    by_cases hji : j = i
    · exact hji ▸ hj
    · exact False.elim (Set.disjoint_left.mp
        ((H.disjoint (Ne.symm hji)).closure_left (show IsOpen (H.component j).carrier
          from isOpen_Ioo)) hv hj)
  · intro hm
    exact H.component_subset i hm

/- Union and component frontiers coincide on the closure of the chosen component. -/
theorem FiniteIntervalUnion.mem_frontier_on_component_closure (H : FiniteIntervalUnion)
    (i ) {v } (hv : v ∈ closure (H.component i).carrier) :
    v ∈ frontier H.carrier ↔ v ∈ frontier (H.component i).carrier := by
  rw [frontier, H.isOpen_carrier.interior_eq, frontier,
    (show IsOpen (H.component i).carrier from isOpen_Ioo).interior_eq]
  simp only [mem_sdiff]
  exact ⟨fun h => ⟨hv, fun hm => h.2 (H.component_subset i hm)⟩,
    fun h => ⟨closure_mono (H.component_subset i) hv,
      fun hm => h.2 ((H.mem_carrier_on_component_closure i hv).mp hm)⟩⟩

/- On a chosen closed component, the actual union exit is exactly the interval exit. -/
theorem FiniteIntervalUnion.exit_on_component_closure (H : FiniteIntervalUnion)
    (i ) (sMinus T : ℝ) (p : Point)
    (hv : p.velocity 0 ∈ Icc (H.component i).lo (H.component i).hi) :
    p ∈ finiteUnionExitSet H sMinus T ↔ p ∈ reconstructionExit (H.component i) sMinus T := by
  have hcl : p.velocity 0 ∈ closure (H.component i).carrier := by
    change p.velocity 0 ∈ closure (Ioo (H.component i).lo (H.component i).hi)
    rwa [closure_Ioo (H.component i).ordered.ne]
  have hf := H.mem_frontier_on_component_closure i hcl
  have hfaces : p.velocity 0 ∈ frontier (H.component i).carrier ↔
      p.velocity 0 = (H.component i).lo ∨ p.velocity 0 = (H.component i).hi := by
    change p.velocity 0 ∈ frontier (Ioo (H.component i).lo (H.component i).hi) ↔ _
    rw [frontier_Ioo (H.component i).ordered]
    simp only [mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro (hp | hp)
    · exact Or.inl ⟨hp.1, hv⟩
    · exact Or.inr ⟨hp.1, hp.2.1, hfaces.mp (hf.mp hp.2.2)⟩
  · rintro (hp | hp)
    · exact Or.inl ⟨hp.1, closure_mono (H.component_subset i) hcl⟩
    · exact Or.inr ⟨hp.1, hp.2.1, hf.mpr (hfaces.mpr hp.2.2)⟩

/- At a smaller component exit, the union internal boundary is the same interval internal face. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
