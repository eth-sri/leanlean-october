module

public import RequestProject.Pi2Extension
public import RequestProject.BaseChangeCycles
public import RequestProject.FinsuppBasis
public import RequestProject.CockcroftExtStep

@[expose] public section

/-! Relabelling the actual relators preserves Cockcroftness. All group,
coefficient, cycle and augmentation maps are constructed from the relator
equivalence and its literal word equality. Pending Lean verification. -/

noncomputable section
open scoped Classical


namespace FiniteChains.RelatorReindex

universe u
variable {A J K : Type u}
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


theorem coefficientMap_quot (x : FreeGroupRing A) :
    coefficientMap ρ τ e hrel (quotRingHom ℤ (relSub ρ) x) =
      quotRingHom ℤ (relSub τ) x := by
  simp only [coefficientMap, quotRingHom, MonoidAlgebra.mapDomainRingHom_apply_comp]
  rfl

theorem coefficientMap_matrix (a : A) (j : J) :
    coefficientMap ρ τ e hrel (foxMatrixPres ρ a j) = foxMatrixPres τ a (e j) := by
  change coefficientMap ρ τ e hrel (quotRingHom ℤ (relSub ρ) (fox a (ρ j))) =
    quotRingHom ℤ (relSub τ) (fox a (τ (e j)))
  rw [coefficientMap_quot, hrel]

end FiniteChains.RelatorReindex
