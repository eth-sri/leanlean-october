module
public import Mathlib.Tactic

public import Erdos821.S2.CycleCounts
public import Erdos821.S2.CycleSigns

/-! The factorial fibers of the cycle-support map. -/

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2

abbrev CycleChoices {a } (π : Finset (Finset (Fin a))) :=
  (B : π) → {c : Equiv.Perm (Fin a) // c ∈ cyclesOn B.val}

section
variable {a : ℕ}
include a

section
variable {π : Finset (Finset (Fin a))}
include π

lemma cycleChoice_spec    
    (τ : CycleChoices π)  B  : (τ B).val.IsCycle ∧ (τ B).val.support = B.val :=
  (Finset.mem_filter.mp (τ B).property).2

def cycleSelection {a } {π : Finset (Finset (Fin a))} (τ : CycleChoices π)  := Finset.univ.image (fun B : π => (τ B).val)

section
variable (hπ : BirthCollection π)
include hπ

section
variable (τ : CycleChoices π)
include τ

lemma cycleSelection_disjoint    
        :
    (cycleSelection τ : Set (Equiv.Perm (Fin a))).Pairwise Equiv.Perm.Disjoint := by
  intro c hc d hd hcd
  obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hd
  have hBC : B.val ≠ C.val := by
    grind
  apply Equiv.Perm.disjoint_iff_disjoint_support.mpr
  rw [(cycleChoice_spec τ B).2, (cycleChoice_spec τ C).2]
  exact hπ.2 B.property C.property hBC

def cycleProduct {a } {π : Finset (Finset (Fin a))}
    (hπ : BirthCollection π) (τ : CycleChoices π)  :=
  (cycleSelection τ).noncommProd id ((cycleSelection_disjoint hπ τ).mono' fun _ _ h => h.commute)

lemma cycleProduct_factors    
        :
    (cycleProduct hπ τ).cycleFactorsFinset = cycleSelection τ := by
  apply Equiv.Perm.cycleFactorsFinset_eq_finset.mpr
  constructor
  · intro c hc
    obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp hc
    exact (cycleChoice_spec τ B).1
  · exact ⟨cycleSelection_disjoint hπ τ, rfl⟩

lemma cycleProduct_blocks    
        :
    cycleBirthBlocks (cycleProduct hπ τ) = π := by
  unfold cycleBirthBlocks
  rw [cycleProduct_factors]
  ext B
  constructor
  · intro hB
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hc
    simp_all [cycleChoice_spec]
  · intro hB
    let C : π := ⟨B, hB⟩
    exact Finset.mem_image.mpr ⟨(τ C).val,
      Finset.mem_image.mpr ⟨C, Finset.mem_univ _, rfl⟩, (cycleChoice_spec τ C).2⟩

end

lemma cycleProduct_injective    
      : Function.Injective (cycleProduct hπ) := by
  intro τ τ' h
  have hsets : cycleSelection τ = cycleSelection τ' := by
    grind [cycleProduct_factors]
  funext B
  apply Subtype.ext
  have hc : (τ B).val ∈ cycleSelection τ' := by
    rw [← hsets]
    exact Finset.mem_image.mpr ⟨B, Finset.mem_univ _, rfl⟩
  obtain ⟨C, _, hC⟩ := Finset.mem_image.mp hc
  have hCB : C = B := by
    apply Subtype.ext
    have hs := congrArg Equiv.Perm.support hC
    simpa only [(cycleChoice_spec τ' C).2, (cycleChoice_spec τ B).2] using hs
  subst C
  exact hC.symm

lemma exists_cycleChoices    
      (σ : Equiv.Perm (Fin a))
    (hσ : cycleBirthBlocks σ = π) : ∃ τ : CycleChoices π, cycleProduct hπ τ = σ := by
  have hex : ∀ B : π, ∃ c : Equiv.Perm (Fin a),
      c ∈ σ.cycleFactorsFinset ∧ c.support = B.val := by
    grind [cycleBirthBlocks]
  choose c hc hs using hex
  let τ : CycleChoices π := fun B => ⟨c B, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (Equiv.Perm.mem_cycleFactorsFinset_iff.mp (hc B)).1, hs B⟩⟩
  have hsel : cycleSelection τ = σ.cycleFactorsFinset := by
    ext d
    constructor
    · intro hd
      obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp hd
      exact hc B
    · intro hd
      let B : π := ⟨d.support, by rw [← hσ]; exact Finset.mem_image.mpr ⟨d, hd, rfl⟩⟩
      have he : c B = d := cycleFactors_support_injective σ (hc B) hd (hs B)
      exact Finset.mem_image.mpr ⟨B, Finset.mem_univ _, he⟩
  refine ⟨τ, ?_⟩
  apply Equiv.Perm.cycleFactorsFinset_injective
  exact (cycleProduct_factors hπ τ).trans hsel

end

end

def permutationsWithBlocks {a } (π : Finset (Finset (Fin a)))  := Finset.univ.filter (fun σ => cycleBirthBlocks σ = π)

/-- The fiber over a block collection has exactly the product of cycle factorials. -/
theorem permutationsWithBlocks_card   (π : Finset (Finset (Fin a)))
    (hπ : BirthCollection π) :
    (permutationsWithBlocks π).card = ∏ B ∈ π, (B.card - 1).factorial := by
  have himage : Finset.univ.image (cycleProduct hπ) = permutationsWithBlocks π := by
    ext σ
    constructor
    · intro h
      obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, cycleProduct_blocks hπ τ⟩
    · intro h
      obtain ⟨_, hσ⟩ := Finset.mem_filter.mp h
      obtain ⟨τ, rfl⟩ := exists_cycleChoices hπ σ hσ
      exact Finset.mem_image.mpr ⟨τ, Finset.mem_univ _, rfl⟩
  rw [← himage, Finset.card_image_of_injOn (cycleProduct_injective hπ).injOn, Finset.card_univ]
  calc
    Fintype.card (CycleChoices π) = ∏ B : π, (cyclesOn B.val).card := by
      simp only [CycleChoices, Fintype.card_pi, Fintype.card_coe]
    _ = ∏ B : π, (B.val.card - 1).factorial := by
      apply Finset.prod_congr rfl
      intro B _
      exact cyclesOn_card B.val (hπ.1 B.val B.property)
    _ = ∏ B ∈ π, (B.card - 1).factorial := Finset.prod_coe_sort π (fun B => (B.card - 1).factorial)

end


end Erdos821.S2
