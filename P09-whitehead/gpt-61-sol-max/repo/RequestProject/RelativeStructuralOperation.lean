import Mathlib.Tactic

import RequestProject.RelativePairGeneration

/-! All three actual structural rules over a fixed core, in finite-support
coordinates. No rule-1 injection, slide filling, commutator factorization,
or block-generation assumption remains. Unverified source.
-/

noncomputable section
open scoped Classical

namespace FiniteChains.RelativeNormalForm

variable {A C Z S : Type} (core : C → FreeGroup A)
  (hcore : Function.Surjective (expMatrix core))
  (extra : S → FreeGroup (A ⊕ Z))

def rawPresentation  :=
  Sum.elim (fun c => FreeGroup.map Sum.inl (core c)) extra

theorem pairRel_rawPresentation : pairRel (rawPresentation core extra) =
    beforeCorrection core extra := by
  funext j
  cases j with
  | inl c => exact pairSubstitution_map_core (core c)
  | inr s => rfl

def relativeRuleOneMap  :=
  (pairStructuralMap (rawPresentation core extra)).castTarget (pairRel_rawPresentation core extra)

variable {B W J : Type}
def pairGroupHomTo  (ρ : J → FreeGroup (B ⊕ W))
    (τ : J → FreeGroup (PairGen B W)) (h : pairRel ρ = τ) : PresGroup ρ →* PresGroup τ :=
  QuotientGroup.lift _ ((QuotientGroup.mk' _).comp pairSubstitution) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.subset_normalClosure ⟨j, (congrFun h j).symm⟩)

theorem pairCast_hom  (ρ : J → FreeGroup (B ⊕ W))
    (τ : J → FreeGroup (PairGen B W)) (h : pairRel ρ = τ) :
    ((pairStructuralMap ρ).castTarget h).hom = pairGroupHomTo ρ τ h := by
  cases h
  rfl

theorem pairCast_cells  (ρ : J → FreeGroup (B ⊕ W))
    (τ : J → FreeGroup (PairGen B W)) (h : pairRel ρ = τ)
    (x : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    ((pairStructuralMap ρ).castTarget h).cells x =
      x.mapRange (MonoidAlgebra.mapDomainRingHom ℤ ((pairStructuralMap ρ).castTarget h).hom)
        (map_zero _) := by
  cases h
  rfl

@[simp] theorem relativeRuleOneMap_hom_mk (w : FreeGroup (A ⊕ Z)) :
    (relativeRuleOneMap core extra).hom (QuotientGroup.mk w) =
      QuotientGroup.mk (pairSubstitution w) := by
  rw [relativeRuleOneMap, pairCast_hom]
  rfl

theorem relativeRuleOneMap_cells
    (x : (C ⊕ S) →₀ MonoidAlgebra ℤ (PresGroup (rawPresentation core extra))) :
    (relativeRuleOneMap core extra).cells x =
      x.mapRange (MonoidAlgebra.mapDomainRingHom ℤ (relativeRuleOneMap core extra).hom)
        (map_zero _) := pairCast_cells _ _ _ x

theorem relativeRuleOneMap_generates : FSGenerates (relativeRuleOneMap core extra) :=
  (pairStructuralMap_generates (rawPresentation core extra)).castTarget
    (pairRel_rawPresentation core extra)

/-- Rules 1 and 2 supply the normalized source used by the terminal theorem. -/
def relativeNormalizationMap  :=
  (normalizationSlideMap core hcore extra).comp (relativeRuleOneMap core extra)

abbrev relativeNormalizationMap_generates  :=
  FiniteChains.FSGenerates.comp (FiniteChains.RelativeNormalForm.normalizationSlideMap_generates core hcore extra)
    (FiniteChains.RelativeNormalForm.relativeRuleOneMap_generates core extra)

abbrev normalizedPresentation_cockcroft (hP : FSIsCockcroft (rawPresentation core extra))  :=
  FiniteChains.fsIsCockcroft_of_generates (FiniteChains.RelativeNormalForm.relativeNormalizationMap core hcore extra)
    (FiniteChains.RelativeNormalForm.relativeNormalizationMap_generates core hcore extra) hP

end FiniteChains.RelativeNormalForm
