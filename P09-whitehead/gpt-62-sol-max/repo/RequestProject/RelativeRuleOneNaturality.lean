module

public import RequestProject.RelativeBlockNaturality
public import RequestProject.RelativeStructuralOperation

@[expose] public section

/-! Actual rule-1 squares for shared ambient generator labels. All stage
inclusions are literal labelled presentation inclusions. Unverified source.
-/

noncomputable section
open scoped Classical

namespace FiniteChains.RelativeNormalForm

theorem coefficient_square {G H K L I J : Type*}
    [Group G] [Group H] [Group K] [Group L]
    {a : G →* H} {b : G →* K} {c : H →* L} {d : K →* L}
    (h : c.comp a = d.comp b) (f : I → J) (x : I →₀ MonoidAlgebra ℤ G) :
    Finsupp.mapDomain f
      ((x.mapRange (MonoidAlgebra.mapDomainRingHom ℤ a) (map_zero _)).mapRange
        (MonoidAlgebra.mapDomainRingHom ℤ c) (map_zero _)) =
      (Finsupp.mapDomain f (x.mapRange (MonoidAlgebra.mapDomainRingHom ℤ b) (map_zero _))).mapRange
        (MonoidAlgebra.mapDomainRingHom ℤ d) (map_zero _) := by
  rw [← Finsupp.mapDomain_mapRange _ _ _ _ (map_add _)]
  congr 1
  ext i : 1
  simp only [Finsupp.mapRange_apply, MonoidAlgebra.mapDomainRingHom_apply_comp, h]

variable {A C Z S : Type} (core : C → FreeGroup A)
  (extra : S → FreeGroup (A ⊕ Z))
  {p t : S → Prop} (hpt : ∀ s, p s → t s)

def restrictedExtra (p : S → Prop) (s : {s // p s}) := extra s.val

def rawInclusion : PresMorFS (rawPresentation core (restrictedExtra extra p))
    (rawPresentation core (restrictedExtra extra t)) :=
  PresInclusionFS.mor _ _ id (oldCellIncl hpt) Function.injective_id
    (oldCellIncl_injective hpt) (by aesop)

def pairInclusion : PresMorFS (beforeCorrection core (restrictedExtra extra p))
    (beforeCorrection core (restrictedExtra extra t)) :=
  PresInclusionFS.mor _ _ id (oldCellIncl hpt) Function.injective_id
    (oldCellIncl_injective hpt) (by aesop)

theorem ruleOne_group_square :
    (pairInclusion core extra hpt).hom.comp
      (relativeRuleOneMap core (restrictedExtra extra p)).hom =
    (relativeRuleOneMap core (restrictedExtra extra t)).hom.comp
      (rawInclusion core extra hpt).hom := by
  apply MonoidHom.ext
  intro g
  induction g using QuotientGroup.induction_on with
  | H w =>
      simp only [MonoidHom.comp_apply, relativeRuleOneMap_hom_mk]
      change QuotientGroup.mk (FreeGroup.map id (pairSubstitution w)) =
        (relativeRuleOneMap core (restrictedExtra extra t)).hom
          (QuotientGroup.mk (FreeGroup.map id w))
      simp

theorem ruleOne_chain_square
    (x : (C ⊕ {s // p s}) →₀ MonoidAlgebra ℤ
      (PresGroup (rawPresentation core (restrictedExtra extra p)))) :
    (pairInclusion core extra hpt).cells
      ((relativeRuleOneMap core (restrictedExtra extra p)).cells x) =
    (relativeRuleOneMap core (restrictedExtra extra t)).cells
      ((rawInclusion core extra hpt).cells x) := by
  rw [relativeRuleOneMap_cells, relativeRuleOneMap_cells]
  exact coefficient_square (ruleOne_group_square core extra hpt) (oldCellIncl hpt) x

theorem ruleOne_preserves_zero
    (hzero : ∀ x, FSIsFoxCycle (rawPresentation core (restrictedExtra extra p)) x →
      (rawInclusion core extra hpt).cells x = 0)
    {x} (hx : FSIsFoxCycle (beforeCorrection core (restrictedExtra extra p)) x) :
    (pairInclusion core extra hpt).cells x = 0 :=
  fsCells_eq_zero_of_generates
    (relativeRuleOneMap core (restrictedExtra extra p))
    (relativeRuleOneMap core (restrictedExtra extra t))
    (rawInclusion core extra hpt) (pairInclusion core extra hpt)
    (ruleOne_chain_square core extra hpt) hzero
    (relativeRuleOneMap_generates core (restrictedExtra extra p)) hx

end FiniteChains.RelativeNormalForm
