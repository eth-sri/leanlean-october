import Mathlib.Tactic

import RequestProject.CoverComplex
import RequestProject.CrowellFinsupp
import RequestProject.PresentationNecessityFinsupp

/-! Actual presentation covers with arbitrarily many edges and faces. -/

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb



variable {α J : Type u} [DecidableEq α] (N : Subgroup (FreeGroup α)) [N.Normal]

noncomputable def fsCoords (β : Type u) :
    (((FreeGroup α ⧸ N) × β) →₀ ℤ) ≃ₗ[ℤ] (β →₀ CoverRing N) :=
  (Finsupp.domLCongr (Equiv.prodComm (FreeGroup α ⧸ N) β)).trans
    ((Finsupp.curryLinearEquiv (R := ℤ)).trans
      (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv ℤ).symm))

section
omit [DecidableEq α]
theorem fsCoords_apply (β : Type u) (c : ((FreeGroup α ⧸ N) × β) →₀ ℤ)
    (i : β) (q : FreeGroup α ⧸ N) : (fsCoords N β c i).coeff q = c (q, i) := rfl

theorem fsCoords_single (β : Type u) (q : FreeGroup α ⧸ N) (i : β) (n : ℤ) :
    fsCoords N β (Finsupp.single (q, i) n) =
      Finsupp.single i (MonoidAlgebra.single q n : CoverRing N) := by
  apply Finsupp.ext
  intro j
  apply MonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro r
  rw [fsCoords_apply]
  by_cases hj : j = i <;> by_cases hr : r = q <;>
    simp [*]
end

theorem fsCoords_pathChain_liftPath_apply (L : List (α × Bool))
    (q : FreeGroup α ⧸ N) (i : α) :
    fsCoords N α (pathChain (liftPath L q)) i =
      (MonoidAlgebra.single q (1 : ℤ) : CoverRing N) * proj N (fox i (FreeGroup.mk L)) := by
  classical
  induction L generalizing q with
  | nil =>
      rw [show FreeGroup.mk ([] : List (α × Bool)) = 1 from rfl]
      simp
  | cons a L ih =>
      obtain ⟨k, b⟩ := a
      cases b
      · have hq : (MonoidAlgebra.single (q * (qof N k)⁻¹) (1 : ℤ) : CoverRing N) =
            (MonoidAlgebra.single q (1 : ℤ) : CoverRing N) * proj N (grp (FreeGroup.of k)⁻¹) := by
          rw [proj_grp, qgrp, QuotientGroup.mk_inv, MonoidAlgebra.single_mul_single, mul_one]
          rfl
        rw [liftPath_cons_false, pathChain_cons]
        simp only [Bool.false_eq_true, if_false, map_add, map_neg,
          Finsupp.add_apply, Finsupp.neg_apply]
        rw [ih, fsCoords_single, mk_cons_false, fox_mul, fox_inv,
          map_add, map_neg, map_mul, map_mul, mul_add, mul_neg,
          ← mul_assoc, ← mul_assoc, ← hq]
        congr 1
        by_cases h : i = k <;> simp [fox_of, h]
      · have hq : (MonoidAlgebra.single (q * qof N k) (1 : ℤ) : CoverRing N) =
            (MonoidAlgebra.single q (1 : ℤ) : CoverRing N) * proj N (grp (FreeGroup.of k)) := by
          rw [proj_grp, qgrp, MonoidAlgebra.single_mul_single, mul_one]
          rfl
        rw [liftPath_cons_true, pathChain_cons]
        simp only [if_true, map_add, Finsupp.add_apply]
        rw [ih, fsCoords_single, mk_cons_true, fox_mul, map_add, map_mul, mul_add,
          ← mul_assoc, ← hq]
        congr 1
        by_cases h : i = k <;> simp [fox_of, h]

variable (ρ : J → FreeGroup α) (hρ : ∀ j, ρ j ∈ N)

include hρ in
theorem fs_coverComplex_bdry2 (c : ((FreeGroup α ⧸ N) × J) →₀ ℤ) :
    coverSecondBoundary N ρ (fsCoords N J c) =
      fsCoords N α (bdry2 (coverComplex N ρ hρ) c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single f n =>
      obtain ⟨q, j⟩ := f
      rw [fsCoords_single, bdry2_single, map_smul, coverSecondBoundary_single]
      apply Finsupp.ext
      intro i
      simp only [Finsupp.smul_apply, smul_eq_mul]
      rw [fsCoords_pathChain_liftPath_apply, FreeGroup.mk_toWord]
      change (MonoidAlgebra.single q n : CoverRing N) * proj N (fox i (ρ j)) =
        n • ((MonoidAlgebra.single q 1 : CoverRing N) * proj N (fox i (ρ j)))
      rw [show (MonoidAlgebra.single q n : CoverRing N) =
          n • (MonoidAlgebra.single q 1 : CoverRing N) by
        simp_all, smul_mul_assoc]

end FiniteChains.Comb
