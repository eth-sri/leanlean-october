import RequestProject.RelativeBlockNaturality
import RequestProject.RelativeStructuralOperation


/-! Actual rule-1 squares for shared ambient generator labels. All stage
inclusions are literal labelled presentation inclusions. Unverified source.
-/

noncomputable section
open scoped Classical

namespace FiniteChains.RelativeNormalForm

variable {A C Z S : Type} (core : C → FreeGroup A)
  (extra : S → FreeGroup (A ⊕ Z))
  {p t : S → Prop} (hpt : ∀ s, p s → t s)

def restrictedExtra (p : S → Prop) (s : {s // p s}) := extra s.val

def rawInclusion : PresMorFS (rawPresentation core (restrictedExtra extra p))
    (rawPresentation core (restrictedExtra extra t)) :=
  PresInclusionFS.mor _ _ id _ Function.injective_id
    (oldCellIncl_injective hpt) (by aesop)

def pairInclusion : PresMorFS (beforeCorrection core (restrictedExtra extra p))
    (beforeCorrection core (restrictedExtra extra t)) :=
  PresInclusionFS.mor _ _ id _ Function.injective_id
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
      simp [MonoidHom.comp_apply, relativeRuleOneMap_hom_mk]
      change QuotientGroup.mk (FreeGroup.map id (pairSubstitution w)) =
        (relativeRuleOneMap core _).hom
          (QuotientGroup.mk (FreeGroup.map id w))
      simp

theorem ruleOne_chain_square
    x :
    (pairInclusion core extra hpt).cells
      ((relativeRuleOneMap core (restrictedExtra extra p)).cells x) =
    (relativeRuleOneMap core (restrictedExtra extra t)).cells
      ((rawInclusion core extra hpt).cells x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      simp [PresMorFS.cells_add, hx, hy]
  | single j a =>
      rw [relativeRuleOneMap_cells, Finsupp.mapRange_single]
      change Finsupp.mapDomain (oldCellIncl hpt)
        ((Finsupp.single j _).mapRange _ _) = _
      rw [Finsupp.mapRange_single, Finsupp.mapDomain_single]
      rw [relativeRuleOneMap_cells]
      change _ = (Finsupp.mapDomain (oldCellIncl hpt)
        ((Finsupp.single j a).mapRange _ _)).mapRange _ _
      rw [Finsupp.mapRange_single, Finsupp.mapDomain_single, Finsupp.mapRange_single]
      congr 1
      change MonoidAlgebra.mapDomainRingHom ℤ (pairInclusion core extra hpt).hom
          (MonoidAlgebra.mapDomainRingHom ℤ
            (relativeRuleOneMap core _).hom a) =
        MonoidAlgebra.mapDomainRingHom ℤ (relativeRuleOneMap core _).hom
          (MonoidAlgebra.mapDomainRingHom ℤ (rawInclusion core extra hpt).hom a)
      grind [BlockMor.mapDomainRingHom_comp', ruleOne_group_square]

theorem ruleOne_preserves_zero
    (hzero : ∀ x, FSIsFoxCycle (rawPresentation core (restrictedExtra extra p)) x →
      (rawInclusion core extra hpt).cells x = 0)
    {x} (hx : FSIsFoxCycle (beforeCorrection core (restrictedExtra extra p)) x) :
    (pairInclusion core extra hpt).cells x = 0 :=
  fsCells_eq_zero_of_generates
    _
    _
    _ _
    (ruleOne_chain_square core extra hpt) hzero
    (relativeRuleOneMap_generates core _) hx
