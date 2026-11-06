import RequestProject.CoverComplex
import RequestProject.CrowellFinsupp
import RequestProject.PresentationNecessityFinsupp
import RequestProject.Tac


/-! Actual presentation covers with arbitrarily many edges and faces. -/

bwd

namespace FiniteChains.Comb

open MonoidAlgebra
universe u

variable {α J : Type u} [DecidableEq α] (N : Subgroup (FreeGroup α)) [N.Normal]

noncomputable def fsCoords (β : Type u) :
    (((FreeGroup α ⧸ N) × β) →₀ ℤ) ≃ₗ[ℤ] (β →₀ CoverRing N) :=
  (Finsupp.domLCongr (Equiv.prodComm _ β)).trans
    ((Finsupp.curryLinearEquiv (R := ℤ)).trans
      (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv ℤ).symm))

omit [DecidableEq α] in
theorem fsCoords_apply (β : Type u) (c : ((FreeGroup α ⧸ N) × β) →₀ ℤ)
    (i : β) (q : FreeGroup α ⧸ N) : (fsCoords N β c i).coeff q = c (q, i) := by
  rfl

omit [DecidableEq α] in
theorem fsCoords_single (β : Type u) (q : FreeGroup α ⧸ N) (i : β) (n : ℤ) :
    fsCoords N β (Finsupp.single (q, i) n) =
      Finsupp.single i (MonoidAlgebra.single q n : CoverRing N) := by
  classical
  apply Finsupp.ext
  intro j
  apply MonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro r
  rw [fsCoords_apply]
  by_cases hj : j = i <;> by_cases hr : r = q <;>
    simp [hj, hr]

theorem fsCoords_pathChain_liftPath_apply L
    q i :
    fsCoords N α (pathChain (liftPath L q)) i =
      (MonoidAlgebra.single q (1 : ℤ)) * proj N (fox i (FreeGroup.mk L)) := by
  classical
  induction L generalizing q with
  | nil =>
      aesop
  | cons a L ih =>
      obtain ⟨k, b⟩ := a
      cases b
      · have hq : (MonoidAlgebra.single (q * (qof N k)⁻¹) (1)) =
            (MonoidAlgebra.single q (1)) * proj N (grp (FreeGroup.of k)⁻¹) := by
          rw [proj_grp, qgrp, QuotientGroup.mk_inv, MonoidAlgebra.single_mul_single, mul_one]
          rfl
        rw [liftPath_cons_false, pathChain_cons]
        simp [Bool.false_eq_true, if_false, map_add, map_neg,
          Finsupp.add_apply, Finsupp.neg_apply]
        rw [ih, fsCoords_single, mk_cons_false, fox_mul, fox_inv,
          map_add, map_neg, map_mul, map_mul, mul_add, mul_neg,
          ← mul_assoc, ← mul_assoc]
        aesop
      · have hq : (MonoidAlgebra.single (q * qof N k) (1)) =
            (MonoidAlgebra.single q (1)) * proj N (grp (FreeGroup.of k)) := by
          rw [proj_grp, qgrp, MonoidAlgebra.single_mul_single, mul_one]
          rfl
        rw [liftPath_cons_true, pathChain_cons]
        simp [if_true, map_add, Finsupp.add_apply]
        rw [ih, fsCoords_single, mk_cons_true, fox_mul, map_add, map_mul, mul_add,
          ← mul_assoc]
        aesop

variable (ρ : J → FreeGroup α) (hρ : ∀ j, ρ j ∈ N)

include hρ in
theorem fs_coverComplex_bdry2 (c : ((FreeGroup α ⧸ N) × J) →₀ ℤ) :
    coverSecondBoundary N ρ (fsCoords N J c) =
      fsCoords N α (bdry2 (coverComplex N ρ hρ) c) := by
  classical
  lin_ind c f n =>
      cases' f with q j
      rw [fsCoords_single, bdry2_single, map_smul, coverSecondBoundary_single]
      apply Finsupp.ext
      intro i
      simp only [Finsupp.smul_apply, smul_eq_mul]
      rw [fsCoords_pathChain_liftPath_apply, FreeGroup.mk_toWord]
      change (MonoidAlgebra.single q n : CoverRing N) * proj N (fox i (ρ j)) =
        n • ((MonoidAlgebra.single q 1 : CoverRing N) * proj N (fox i (ρ j)))
      rw [show (MonoidAlgebra.single q n : CoverRing N) =
          n • (MonoidAlgebra.single q 1 : CoverRing N) by
        simp, smul_mul_assoc]
