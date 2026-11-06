import Mathlib.Tactic

import RequestProject.GenerationStepFinsupp
import RequestProject.BlockFamilyBlockwiseFinsupp
import RequestProject.LemmaTerminal

/-! The terminal inclusion and the Cockcroft/trivial-group vanishing argument
for arbitrary presentations.  Only chains, not cell sets, are finite.
Pending Lean verification. -/

noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open BlockFamily

variable {A B J L I : Type} [DecidableEq A] [DecidableEq B]

  {ρ : J → FreeGroup A}
  {τ : L → FreeGroup B}
theorem PresMorFS.cells_finset_sum  
    (f : PresMorFS ρ τ) (s : Finset I)
    (v : I → J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    f.cells (∑ i ∈ s, v i) = ∑ i ∈ s, f.cells (v i) := by
  classical
  induction s using Finset.induction_on <;> simp_all [FiniteChains.relSub_normal, FiniteChains.PresMorFS.cells_zero, FiniteChains.PresMorFS.cells_add]

theorem fsCells_eq_zero_of_hom_trivial  
    (f : PresMorFS ρ τ) (htriv : ∀ g, f.hom g = 1)
    (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ))
    (hv : ∀ j, augPres ρ (v j) = 0) : f.cells v = 0 := by
  have hdec : v = ∑ j ∈ v.support, Finsupp.single j (v j) := (Finsupp.sum_single v).symm
  have hsingle (j : J) :
      Finsupp.single j (v j) = v j • Finsupp.single j (1 : MonoidAlgebra ℤ (PresGroup ρ)) := by
    ext k : 1
    by_cases h : j = k
    · subst k
      simp
    · simp [Ne.symm h]
  rw [hdec, f.cells_finset_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [hsingle, f.cells_smul, mapDomainRingHom_eq_single_augPres f.hom htriv, hv j]
  simp

abbrev fsCells_eq_zero_of_isCockcroft_of_hom_trivial
     
    (f : PresMorFS ρ τ) (hρ : FSIsCockcroft ρ) (htriv : ∀ g, f.hom g = 1)
    (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) (hv : FSIsFoxCycle ρ v)  :=
  FiniteChains.fsCells_eq_zero_of_hom_trivial f htriv v (hρ v hv)

variable (ρ : J → FreeGroup A) (ν : L → FreeGroup A)

variable (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ))
def addRelsCellsFS  :
    (J ⊕ L) →₀ MonoidAlgebra ℤ (PresGroup (addRels ρ ν)) :=
  Finsupp.mapDomain Sum.inl (v.mapRange (addRelsRingHom ρ ν) (map_zero _))

section
omit [DecidableEq A]
variable (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ))
@[simp] theorem addRelsCellsFS_inl  (j : J) :
    addRelsCellsFS ρ ν v (Sum.inl j) = addRelsRingHom ρ ν (v j) := by
  simp [addRelsCellsFS, Finsupp.mapDomain_apply_of_injective Sum.inl_injective]

@[simp] theorem addRelsCellsFS_inr  (l : L) :
    addRelsCellsFS ρ ν v (Sum.inr l) = 0 := by
  apply Finsupp.mapDomain_notin_range
  rintro ⟨j, h⟩
  exact Sum.inl_ne_inr h

@[simp] theorem addRelsCellsFS_single (j : J) (a : MonoidAlgebra ℤ (PresGroup ρ)) :
    addRelsCellsFS ρ ν (Finsupp.single j a) =
      Finsupp.single (Sum.inl j) (addRelsRingHom ρ ν a) := by
  simp [addRelsCellsFS]

theorem addRelsCellsFS_add (v w : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    addRelsCellsFS ρ ν (v + w) = addRelsCellsFS ρ ν v + addRelsCellsFS ρ ν w := by
  ext j : 1
  cases j <;> simp [map_add]
end

theorem addRelsCellsFS_boundary  (a : A) :
    coverSecondBoundary (relSub (addRels ρ ν)) (addRels ρ ν) (addRelsCellsFS ρ ν v) a =
      addRelsRingHom ρ ν (coverSecondBoundary (relSub ρ) ρ v a) := by
  induction v using Finsupp.induction_linear with
  | zero => simp [addRelsCellsFS]
  | add v w hv hw => simp_all [addRelsCellsFS_add]
  | single j c =>
      simp only [addRelsCellsFS_single, fsCoverSecondBoundary_apply,
        Finsupp.sum_single_index, zero_mul, foxMatrix_addRels_inl, map_mul]

def addRelsMorFS : PresMorFS ρ (addRels ρ ν) where
  hom := addRelsHom ρ ν
  cells := addRelsCellsFS ρ ν
  cells_add := addRelsCellsFS_add ρ ν
  cells_smul := by
    aesop
  cells_cycle := by
    intro v hv
    change coverSecondBoundary _ _ v = 0 at hv
    ext a : 1
    rw [addRelsCellsFS_boundary, hv, Finsupp.zero_apply, map_zero]
    rfl
  cells_aug := by
    simp_all [augPres_addRelsRingHom]

end FiniteChains
