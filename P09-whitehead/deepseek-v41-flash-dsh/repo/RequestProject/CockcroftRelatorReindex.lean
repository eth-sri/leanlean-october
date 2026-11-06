module

public import RequestProject.GenerationStep
public import RequestProject.CockcroftExtStep

@[expose] public section

/-! Relabelling the actual relators preserves Cockcroftness. All group,
coefficient, cycle and augmentation maps are constructed from the relator
equivalence and its literal word equality. Pending Lean verification. -/

noncomputable section
open scoped Classical

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.RelatorReindex

variable {A J K : Type u} [Fintype A] [DecidableEq A] [Fintype J] [Fintype K]
  (ρ : J → FreeGroup A) (τ : K → FreeGroup A) (e : J ≃ K)
  (hrel : ∀ j, τ (e j) = ρ j)

/-- The generators are fixed; only the names of relators change. -/
def groupMap : PresGroup ρ →* PresGroup τ :=
  QuotientGroup.lift _ (QuotientGroup.mk' (relSub τ)) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.subset_normalClosure ⟨e j, hrel j⟩)

def coefficientMap : MonoidAlgebra ℤ (PresGroup ρ) →+* MonoidAlgebra ℤ (PresGroup τ) :=
  MonoidAlgebra.mapDomainRingHom ℤ (groupMap ρ τ e hrel)

omit [Fintype A] [DecidableEq A] [Fintype J] [Fintype K] in
theorem coefficientMap_quot (x : FreeGroupRing A) :
    coefficientMap ρ τ e hrel (quotRingHom ℤ (relSub ρ) x) =
      quotRingHom ℤ (relSub τ) x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single g n =>
      change MonoidAlgebra.mapDomain _ (MonoidAlgebra.mapDomain _ (MonoidAlgebra.single g n)) =
        MonoidAlgebra.mapDomain _ (MonoidAlgebra.single g n)
      simp
      rfl

omit [Fintype A] [Fintype J] [Fintype K] in
theorem coefficientMap_matrix (a : A) (j : J) :
    coefficientMap ρ τ e hrel (foxMatrixPres ρ a j) = foxMatrixPres τ a (e j) := by
  change coefficientMap ρ τ e hrel (quotRingHom ℤ (relSub ρ) (fox a (ρ j))) =
    quotRingHom ℤ (relSub τ) (fox a (τ (e j)))
  rw [coefficientMap_quot, hrel]

end FiniteChains.RelatorReindex
