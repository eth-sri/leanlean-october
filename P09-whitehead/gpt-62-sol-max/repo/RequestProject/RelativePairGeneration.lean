module

public import RequestProject.RelativePairInjection
public import RequestProject.RelativeCoreSlides
public import RequestProject.FoxCoordinateSubstitution
public import RequestProject.Pi2Extension

@[expose] public section

/-! Actual simultaneous rule-1 generation. Distinct pairs have disjoint
Fox coordinates. The first coordinate of the pair at z is multiplied by
1−a_z b_z a_z⁻¹, whose right regularity follows from the b_z exponent map.
All cell and coefficient chains are finitely supported. Unverified source.
-/

noncomputable section
open scoped Classical


namespace FiniteChains

namespace RelativeNormalForm
open BlockFamily

variable {A Z J : Type}

def pairOldCoordinate : PairGen A Z → A ⊕ Z :=
  Sum.elim Sum.inl (fun p => Sum.inr p.1)

def pairFoxWeight (i : PairGen A Z) : FreeGroupRing (PairGen A Z) :=
  fox i (pairSubstitution (FreeGroup.of (pairOldCoordinate i)))

theorem pairSubstitution_generator_fox (i : PairGen A Z) (j : A ⊕ Z) :
    fox i (pairSubstitution (FreeGroup.of j)) =
      if pairOldCoordinate i = j then pairFoxWeight i else 0 := by
  by_cases h : pairOldCoordinate i = j
  · aesop
  · rw [if_neg h]
    cases i with
    | inl a =>
        cases j with
        | inl b =>
            have hab : a ≠ b := by simpa [pairOldCoordinate] using h
            simp_all
        | inr z =>
            simp [commutatorElement_def, fox_mul, fox_inv, fox_of]
    | inr p =>
        cases j with
        | inl a => aesop
        | inr z =>
            have hpz : p.1 ≠ z := by simpa [pairOldCoordinate] using h
            obtain ⟨p, b⟩ := p
            simp [commutatorElement_def, fox_mul, fox_inv, fox_of, hpz]

theorem pairSubstitution_fox (i : PairGen A Z) (w : FreeGroup (A ⊕ Z)) :
    fox i (pairSubstitution w) =
      MonoidAlgebra.mapDomainRingHom ℤ pairSubstitution (fox (pairOldCoordinate i) w) *
        pairFoxWeight i :=
  fox_subst_weighted_coordinate (pairSubstitution (A := A) (Z := Z))
    (pairOldCoordinate i) i (pairFoxWeight i) (pairSubstitution_generator_fox i) w

@[simp] theorem pairFoxWeight_core (a : A) : pairFoxWeight (Sum.inl (β := Z × Bool) a) = 1 := by
  simp [pairFoxWeight, pairOldCoordinate, fox_of]

def pairConjugate (z : Z) : FreeGroup (PairGen A Z) :=
  FreeGroup.of (Sum.inr (z, false)) * FreeGroup.of (Sum.inr (z, true)) *
    (FreeGroup.of (Sum.inr (z, false)))⁻¹

theorem pairFoxWeight_left (z : Z) :
    pairFoxWeight (Sum.inr (α := A) (z, false)) = 1 - grp (pairConjugate z) := by
  simp [pairFoxWeight, pairOldCoordinate, commutatorElement_def, fox_mul,
    fox_inv, fox_of, pairConjugate, grp_mul]
  noncomm_ring

variable (ρ : J → FreeGroup (A ⊕ Z))

def pairCoefficients := MonoidAlgebra.mapDomainRingHom ℤ (pairSubGroupHom ρ)

theorem pairCoefficients_proj (x : FreeGroupRing (A ⊕ Z)) :
    pairCoefficients ρ (proj (relSub ρ) x) =
      proj (relSub (pairRel ρ)) (MonoidAlgebra.mapDomainRingHom ℤ pairSubstitution x) :=
  quotRingHom_natural (relSub (pairRel ρ)) pairSubstitution (pairSubGroupHom ρ) rfl x

def pairOldBoundary := fsRingMapBoundary (pairCoefficients ρ)
  (fun j => coverFoxGradient (relSub ρ) (ρ j))

theorem pair_boundary_coordinate
    (x : J →₀ MonoidAlgebra ℤ (PresGroup (pairRel ρ))) (i : PairGen A Z) :
    coverSecondBoundary (relSub (pairRel ρ)) (pairRel ρ) x i =
      pairOldBoundary ρ x (pairOldCoordinate i) *
        proj (relSub (pairRel ρ)) (pairFoxWeight i) := by
  rw [fsCoverSecondBoundary_apply]
  have hcol (j : J) : foxMatrixPres (pairRel ρ) i j =
      pairCoefficients ρ (foxMatrixPres ρ (pairOldCoordinate i) j) *
        proj (relSub (pairRel ρ)) (pairFoxWeight i) := by
    change proj _ (fox i (pairSubstitution (ρ j))) = _
    rw [pairSubstitution_fox, map_mul, ← pairCoefficients_proj]
    rfl
  simp_rw [hcol, ← mul_assoc]
  rw [Finsupp.sum, ← Finset.sum_mul]
  congr 1
  simp only [pairOldBoundary, fsRingMapBoundary, Finsupp.linearCombination_apply,
    Finsupp.sum_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.mapRange_apply]
  rfl

def pairExponent (z : Z) : PresGroup (pairRel ρ) →* Multiplicative ℤ :=
  QuotientGroup.lift _ (expSum (Sum.inr (α := A) (z, true))) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    exact pairSubstitution_exp_pair (ρ j) (z, true))

theorem pairConjugate_infinite_order (z : Z) :
    ¬ IsOfFinOrder (QuotientGroup.mk (pairConjugate (A := A) z) : PresGroup (pairRel ρ)) := by
  apply not_isOfFinOrder_of_map (pairExponent ρ z)
  have he : pairExponent ρ z (QuotientGroup.mk (pairConjugate z)) =
      Multiplicative.ofAdd 1 := by
    change expSum (Sum.inr (z, true)) (pairConjugate z) = _
    simp [pairConjugate, expSum]
  rw [he]
  exact not_isOfFinOrder_ofAdd_one

/-- Every new cycle is an actual old Fox cycle over the enlarged coefficient
ring. This is the content of rule 1, before the injective base-change step. -/
theorem pair_cycle_reflection
    (x : J →₀ MonoidAlgebra ℤ (PresGroup (pairRel ρ)))
    (hx : FSIsFoxCycle (pairRel ρ) x) : pairOldBoundary ρ x = 0 := by
  ext i : 1
  cases i with
  | inl a =>
      have h := congrArg (fun c => c (Sum.inl a)) hx
      simpa only [pair_boundary_coordinate, pairOldCoordinate, Sum.elim_inl, Sum.elim_inr, pairFoxWeight_core,
        map_one, mul_one, Finsupp.zero_apply] using h
  | inr z =>
      apply mul_one_sub_single_eq_zero (pairConjugate_infinite_order ρ z)
      have h := congrArg (fun c => c (Sum.inr (z, false))) hx
      simpa only [pair_boundary_coordinate, pairOldCoordinate, Sum.elim_inl, Sum.elim_inr, pairFoxWeight_left,
        map_sub, map_one, proj_grp, qgrp, Finsupp.zero_apply] using h

def pairStructuralMap : PresMorFS ρ (pairRel ρ) where
  hom := pairSubGroupHom ρ
  cells := Finsupp.mapRange.linearMap (pairCoefficients ρ).toSemilinearMap
  cells_cycle := by
    intro x hx
    change coverSecondBoundary _ _ _ = 0
    ext i : 1
    rw [pair_boundary_coordinate]
    change fsRingMapBoundary (pairCoefficients ρ) _
      (x.mapRange _ (map_zero (pairCoefficients ρ))) _ * _ = 0
    rw [fsRingMapBoundary_mapRange]
    erw [hx]
    simp
  cells_aug := by
    intro x hx j
    exact (augQ_mapDomain (pairSubGroupHom ρ) (x j)).trans (hx j)

/-- Equation (3.3) for simultaneous rule 1 with every input discharged. -/
theorem pairStructuralMap_generates : FSGenerates (pairStructuralMap ρ) := by
  intro x hx
  exact fs_cycle_mem_span_groupMap_cycles (pairSubGroupHom ρ)
    (pairSubGroupHom_injective ρ)
    (fun j => coverFoxGradient (relSub ρ) (ρ j)) x (pair_cycle_reflection ρ x hx)

end RelativeNormalForm
end FiniteChains
