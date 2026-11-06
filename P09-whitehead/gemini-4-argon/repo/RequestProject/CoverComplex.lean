module

public import RequestProject.CellComplex
public import RequestProject.CoverAcyclic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb

open MonoidAlgebra

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]
variable {J : Type u} [Fintype J] [DecidableEq J]

theorem isPath_of_subsingleton {V E : Type*} [Subsingleton V] (src tgt : E → V)
    (p : List (E × Bool)) (a b : V) : IsPath src tgt p a b := by
  induction p generalizing a with
  | nil => exact Subsingleton.elim _ _
  | cons _ _ ih => exact ⟨Subsingleton.elim _ _, ih _⟩

abbrev presComplex (ρ : J → FreeGroup α) : Complex2.{u} where
  V := PUnit.{u + 1}
  E := α
  F := J
  src _ := PUnit.unit
  tgt _ := PUnit.unit
  base _ := PUnit.unit
  att j := FreeGroup.toWord (ρ j)
  att_isLoop _ := isPath_of_subsingleton _ _ _ _ _

variable (Nsub : Subgroup (FreeGroup α)) [Nsub.Normal]

def qof (i : α) : FreeGroup α ⧸ Nsub := QuotientGroup.mk (FreeGroup.of i)

variable {Nsub}

def liftPath : List (α × Bool) → (FreeGroup α ⧸ Nsub) →
    List (((FreeGroup α ⧸ Nsub) × α) × Bool)
  | [], _ => []
  | (i, true) :: L, q => ((q, i), true) :: liftPath L (q * qof Nsub i)
  | (i, false) :: L, q => ((q * (qof Nsub i)⁻¹, i), false) :: liftPath L (q * (qof Nsub i)⁻¹)

omit [Fintype α] [DecidableEq α] in
@[simp] theorem liftPath_nil (q : FreeGroup α ⧸ Nsub) : liftPath [] q = [] := rfl

omit [Fintype α] [DecidableEq α] in
@[simp] theorem liftPath_cons_true (i : α) (L : List (α × Bool)) (q : FreeGroup α ⧸ Nsub) :
    liftPath ((i, true) :: L) q = ((q, i), true) :: liftPath L (q * qof Nsub i) := rfl

omit [Fintype α] [DecidableEq α] in
@[simp] theorem liftPath_cons_false (i : α) (L : List (α × Bool)) (q : FreeGroup α ⧸ Nsub) :
    liftPath ((i, false) :: L) q
      = ((q * (qof Nsub i)⁻¹, i), false) :: liftPath L (q * (qof Nsub i)⁻¹) := rfl

omit [Fintype α] in
theorem mk_cons_true (i : α) (L : List (α × Bool)) :
    FreeGroup.mk ((i, true) :: L) = FreeGroup.of i * FreeGroup.mk L :=
  FreeGroup.toWord_inj.mp rfl

omit [Fintype α] in
theorem mk_cons_false (i : α) (L : List (α × Bool)) :
    FreeGroup.mk ((i, false) :: L) = (FreeGroup.of i)⁻¹ * FreeGroup.mk L :=
  FreeGroup.toWord_inj.mp rfl

variable (Nsub)

omit [Fintype α] in
theorem liftPath_isPath (L : List (α × Bool)) (q : FreeGroup α ⧸ Nsub) :
    IsPath (fun e : (FreeGroup α ⧸ Nsub) × α => e.1)
      (fun e : (FreeGroup α ⧸ Nsub) × α => e.1 * qof Nsub e.2) (liftPath L q) q
      (q * QuotientGroup.mk (FreeGroup.mk L)) := by
  induction L generalizing q with
  | nil =>
      show q = q * QuotientGroup.mk (FreeGroup.mk ([] : List (α × Bool)))
      rw [show FreeGroup.mk ([] : List (α × Bool)) = 1 from rfl]; simp
  | cons a L ih =>
      rcases a with ⟨i, _ | _⟩
      · refine ⟨by show q = (q * (qof Nsub i)⁻¹) * qof Nsub i; group, ?_⟩
        simpa [qof, mk_cons_false, QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_assoc] using
          ih (q * (qof Nsub i)⁻¹)
      · refine ⟨rfl, ?_⟩
        simpa [qof, mk_cons_true, QuotientGroup.mk_mul, mul_assoc] using ih (q * qof Nsub i)

variable (ρ : J → FreeGroup α)

abbrev coverComplex (hρ : ∀ j, ρ j ∈ Nsub) : Complex2.{u} where
  V := FreeGroup α ⧸ Nsub
  E := (FreeGroup α ⧸ Nsub) × α
  F := (FreeGroup α ⧸ Nsub) × J
  src e := e.1
  tgt e := e.1 * qof Nsub e.2
  base f := f.1
  att f := liftPath (FreeGroup.toWord (ρ f.2)) f.1
  att_isLoop f := by
    have h := liftPath_isPath Nsub (FreeGroup.toWord (ρ f.2)) f.1
    rwa [FreeGroup.mk_toWord, (QuotientGroup.eq_one_iff (ρ f.2)).2 (hρ f.2), mul_one] at h

variable {Nsub ρ}
variable (Nsub)

noncomputable def coords (β : Type u) [Fintype β] [DecidableEq β] :
    (((FreeGroup α ⧸ Nsub) × β) →₀ ℤ) ≃ₗ[ℤ] (β → CoverRing Nsub) :=
  (Finsupp.domLCongr (Equiv.prodComm (FreeGroup α ⧸ Nsub) β)).trans
    ((Finsupp.curryLinearEquiv (R := ℤ)).trans
      ((Finsupp.linearEquivFunOnFinite ℤ ((FreeGroup α ⧸ Nsub) →₀ ℤ) β).trans
        (LinearEquiv.piCongrRight (fun _ => (MonoidAlgebra.coeffLinearEquiv ℤ).symm))))

variable {Nsub}

omit [Fintype α] [DecidableEq α] [Nsub.Normal] in
theorem coords_apply (β : Type u) [Fintype β] [DecidableEq β]
    (c : ((FreeGroup α ⧸ Nsub) × β) →₀ ℤ) (i : β) (q : FreeGroup α ⧸ Nsub) :
    ((coords Nsub β c) i).coeff q = c (q, i) := by
  show ((Finsupp.equivMapDomain (Equiv.prodComm _ β) c).curry i) q = c (q, i)
  rw [Finsupp.curry_apply, Finsupp.equivMapDomain_apply]; rfl

omit [Fintype α] [DecidableEq α] in
theorem coords_single (β : Type u) [Fintype β] [DecidableEq β] (q : FreeGroup α ⧸ Nsub)
    (i : β) (n : ℤ) :
    coords Nsub β (Finsupp.single (q, i) n) = Pi.single i (MonoidAlgebra.single q n) := by
  classical
  funext k; apply MonoidAlgebra.coeff_injective; refine Finsupp.ext fun q' => ?_
  rw [coords_apply, Finsupp.single_apply]
  by_cases h : k = i
  · subst h
    rw [Pi.single_eq_same, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hq : q = q' <;> simp [hq]
  · simp [Pi.single_eq_of_ne h, Ne.symm h]

theorem coords_pathChain_liftPath (L : List (α × Bool)) (q : FreeGroup α ⧸ Nsub) :
    coords Nsub α (pathChain (liftPath L q))
      = fun i => (MonoidAlgebra.single q (1 : ℤ) : CoverRing Nsub) *
          proj Nsub (fox i (FreeGroup.mk L)) := by
  classical
  induction L generalizing q with
  | nil =>
      funext i
      rw [show FreeGroup.mk ([] : List (α × Bool)) = 1 from rfl]; simp
  | cons a L ih =>
      rcases a with ⟨i₀, _ | _⟩
      · have hq : (MonoidAlgebra.single (q * (qof Nsub i₀)⁻¹) (1 : ℤ) : CoverRing Nsub)
            = (MonoidAlgebra.single q (1 : ℤ) : CoverRing Nsub) *
              proj Nsub (grp (FreeGroup.of i₀)⁻¹) := by
          rw [proj_grp, qgrp, QuotientGroup.mk_inv, MonoidAlgebra.single_mul_single, mul_one]; rfl
        rw [liftPath_cons_false, pathChain_cons]
        simp only [Bool.false_eq_true, if_false, map_add, map_neg]
        rw [ih (q * (qof Nsub i₀)⁻¹)]
        funext i
        rw [Pi.add_apply, Pi.neg_apply, coords_single, mk_cons_false, fox_mul, fox_inv,
          map_add, map_neg, map_mul, map_mul, mul_add, mul_neg, ← mul_assoc, ← mul_assoc, ← hq]
        congr 1
        by_cases h : i = i₀
        · subst h; rw [Pi.single_eq_same, fox_of, if_pos rfl, map_one, mul_one]
        · rw [Pi.single_eq_of_ne h, fox_of, if_neg h, map_zero, mul_zero, neg_zero]
      · have hq : (MonoidAlgebra.single (q * qof Nsub i₀) (1 : ℤ) : CoverRing Nsub)
            = (MonoidAlgebra.single q (1 : ℤ) : CoverRing Nsub) *
              proj Nsub (grp (FreeGroup.of i₀)) := by
          rw [proj_grp, qgrp, MonoidAlgebra.single_mul_single, mul_one]; rfl
        rw [liftPath_cons_true, pathChain_cons]
        simp only [if_true, map_add]
        rw [ih (q * qof Nsub i₀)]
        funext i
        rw [Pi.add_apply, coords_single, mk_cons_true, fox_mul, map_add, map_mul, mul_add,
          ← mul_assoc, ← hq]
        congr 1
        by_cases h : i = i₀
        · subst h; rw [Pi.single_eq_same, fox_of, if_pos rfl, map_one, mul_one]
        · rw [Pi.single_eq_of_ne h, fox_of, if_neg h, map_zero, mul_zero]

variable (hρ : ∀ j, ρ j ∈ Nsub)

include hρ in
theorem coverComplex_bdry2 (u : ((FreeGroup α ⧸ Nsub) × J) →₀ ℤ) :
    _root_.FiniteChains.bdry2 Nsub ρ (coords Nsub J u)
      = coords Nsub α (Comb.bdry2 (coverComplex Nsub ρ hρ) u) := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => rw [map_zero, _root_.FiniteChains.bdry2_zero, map_zero, map_zero]
  | add _ _ h₁ h₂ =>
      rw [map_add, _root_.FiniteChains.bdry2_add, h₁, h₂, map_add, ← map_add]
  | single f n =>
      obtain ⟨q, j⟩ := f
      rw [coords_single, bdry2_single, map_smul, coords_pathChain_liftPath, FreeGroup.mk_toWord]
      funext i
      show ∑ j' : J, (Pi.single j (MonoidAlgebra.single q n) : J → CoverRing Nsub) j' *
          proj Nsub (fox i (ρ j')) = _
      rw [Finset.sum_eq_single j (fun j' _ h => by simp [Pi.single_eq_of_ne h])
        (fun h => absurd (Finset.mem_univ j) h)]
      simp only [Pi.single_eq_same, Pi.smul_apply]
      rw [show (MonoidAlgebra.single q n : CoverRing Nsub)
          = n • (MonoidAlgebra.single q (1 : ℤ) : CoverRing Nsub) by
        rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one], smul_mul_assoc]

def coverProj : Hom (coverComplex Nsub ρ hρ) (presComplex ρ) where
  onV _ := PUnit.unit
  onE e := e.2
  onF f := f.2
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF f := by
    have hmap : ∀ (L : List (α × Bool)) (q : FreeGroup α ⧸ Nsub),
        (liftPath L q).map (fun eb => (eb.1.2, eb.2)) = L := by
      intro L; induction L with
      | nil => intro _; rfl
      | cons a L ih => rcases a with ⟨i, _ | _⟩ <;> intro q <;> simpa using ih _
    exact (hmap (FreeGroup.toWord (ρ f.2)) f.1).symm

end FiniteChains.Comb
