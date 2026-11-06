module

public import RequestProject.MonoidAlgebraMapDomain
public import RequestProject.FoxLinear

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open scoped commutatorElement

noncomputable section
namespace FiniteChains

open MonoidAlgebra

variable {α : Type*} (Nsub : Subgroup (FreeGroup α)) [Nsub.Normal]

abbrev CoverRing : Type _ := MonoidAlgebra ℤ (FreeGroup α ⧸ Nsub)

def proj : FreeGroupRing α →+* CoverRing Nsub :=
  MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' Nsub)

def qgrp (g : FreeGroup α) : CoverRing Nsub :=
  MonoidAlgebra.single (QuotientGroup.mk g) 1

def augQ : CoverRing Nsub →+* ℤ :=
  (MonoidAlgebra.lift ℤ ℤ (FreeGroup α ⧸ Nsub) 1).toRingHom

def liftQ (z : CoverRing Nsub) : FreeGroupRing α :=
  MonoidAlgebra.mapDomain Quotient.out z

@[simp] theorem proj_single (g : FreeGroup α) (n : ℤ) :
    proj Nsub (single g n) = single (QuotientGroup.mk g : FreeGroup α ⧸ Nsub) n :=
  MonoidAlgebra.mapDomain_single

theorem proj_grp (g : FreeGroup α) : proj Nsub (grp g) = qgrp Nsub g := by
  rw [grp_eq_single, proj_single, qgrp]

theorem qgrp_eq_one_of_mem {g : FreeGroup α} (hg : g ∈ Nsub) : qgrp Nsub g = 1 :=
  congrArg (single · 1) ((QuotientGroup.eq_one_iff g).2 hg)

@[simp] theorem augQ_single (q : FreeGroup α ⧸ Nsub) (n : ℤ) : augQ Nsub (single q n) = n := by
  simp [augQ]

theorem augQ_proj (b : FreeGroupRing α) : augQ Nsub (proj Nsub b) = aug b := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add _ _ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add]
  | single g n => rw [proj_single, augQ_single, aug_single]

theorem proj_liftQ (z : CoverRing Nsub) : proj Nsub (liftQ Nsub z) = z := by
  show MonoidAlgebra.mapDomain (QuotientGroup.mk' Nsub) (MonoidAlgebra.mapDomain Quotient.out z) = z
  rw [← MonoidAlgebra.mapDomain_comp,
    show ⇑(QuotientGroup.mk' Nsub) ∘ Quotient.out = id from funext QuotientGroup.out_eq',
    MonoidAlgebra.mapDomain_id]

variable [DecidableEq α]

def foxVec (w : FreeGroup α) : α → CoverRing Nsub := fun i => proj Nsub (fox i w)

@[simp] theorem foxVec_one : foxVec Nsub 1 = 0 := by funext i; simp [foxVec]

variable {Nsub}

theorem foxVec_mul {v : FreeGroup α} (hv : v ∈ Nsub) (w : FreeGroup α) :
    foxVec Nsub (v * w) = foxVec Nsub v + foxVec Nsub w := by
  funext i; simp [foxVec, fox_mul, proj_grp, qgrp_eq_one_of_mem Nsub hv]

theorem foxVec_inv {v : FreeGroup α} (hv : v ∈ Nsub) :
    foxVec Nsub v⁻¹ = - foxVec Nsub v := by
  have h := foxVec_mul (Subgroup.inv_mem _ hv) v
  rw [inv_mul_cancel, foxVec_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem foxVec_conj {r : FreeGroup α} (hr : r ∈ Nsub) (f : FreeGroup α) :
    foxVec Nsub (f * r * f⁻¹) = proj Nsub (grp f) • foxVec Nsub r := by
  funext i
  have hff : proj Nsub (grp f) * proj Nsub (grp f⁻¹) = 1 := by
    rw [← map_mul, ← grp_mul, mul_inv_cancel, grp_one, map_one]
  simp only [foxVec, Pi.smul_apply, smul_eq_mul, fox_mul, fox_inv i f, grp_mul, map_add, map_mul,
    map_neg, show proj Nsub (grp r) = 1 by rw [proj_grp, qgrp_eq_one_of_mem Nsub hr], mul_one]
  rw [mul_neg, ← mul_assoc, hff, one_mul]; abel

theorem foxVec_zpow {r : FreeGroup α} (hr : r ∈ Nsub) (n : ℤ) :
    foxVec Nsub (r ^ n) = n • foxVec Nsub r := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih => rw [zpow_add_one, foxVec_mul (Subgroup.zpow_mem _ hr _), ih, add_smul, one_smul]
  | pred k ih =>
      rw [zpow_sub_one, foxVec_mul (Subgroup.zpow_mem _ hr _), foxVec_inv hr, ih, sub_smul,
        one_smul, sub_eq_add_neg]

variable (Nsub)

def foxMod : Submodule (CoverRing Nsub) (α → CoverRing Nsub) where
  carrier := {c | ∃ r ∈ Nsub, c = foxVec Nsub r}
  zero_mem' := ⟨1, Subgroup.one_mem _, by simp⟩
  add_mem' := by
    rintro a b ⟨r, hr, rfl⟩ ⟨s, hs, rfl⟩
    exact ⟨r * s, Subgroup.mul_mem _ hr hs, by rw [foxVec_mul hr]⟩
  smul_mem' := by
    rintro u a ⟨r, hr, rfl⟩
    induction u using MonoidAlgebra.induction_linear with
    | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
    | add _ _ h₁ h₂ =>
        obtain ⟨r₁, hr₁, e₁⟩ := h₁; obtain ⟨r₂, hr₂, e₂⟩ := h₂
        exact ⟨r₁ * r₂, Subgroup.mul_mem _ hr₁ hr₂, by rw [foxVec_mul hr₁, ← e₁, ← e₂, add_smul]⟩
    | single q n =>
        obtain ⟨f, rfl⟩ := Quotient.exists_rep q
        have hconj : f * r * f⁻¹ ∈ Nsub := Subgroup.Normal.conj_mem ‹Nsub.Normal› r hr f
        refine ⟨(f * r * f⁻¹) ^ n, Subgroup.zpow_mem _ hconj n, ?_⟩
        rw [foxVec_zpow hconj, foxVec_conj hr,
          show (single (QuotientGroup.mk f : FreeGroup α ⧸ Nsub) n : CoverRing Nsub)
            = n • proj Nsub (grp f) by rw [proj_grp, qgrp, MonoidAlgebra.smul_single, smul_eq_mul, mul_one],
          smul_assoc]

def foxProj (b : FreeGroupRing α) : α → CoverRing Nsub := fun i => proj Nsub (foxLin i b)

theorem foxProj_mem_foxMod (b : FreeGroupRing α) (hb : proj Nsub b = 0) :
    foxProj Nsub b ∈ foxMod (Nsub := Nsub) := by
  classical
  let φ : FreeGroup α → FreeGroup α := fun g => Quotient.out (QuotientGroup.mk g : FreeGroup α ⧸ Nsub)
  have hrel : b ∈ Submodule.span (FreeGroupRing α) {y | ∃ r ∈ Nsub, y = grp r - 1} := by
    have hmap : MonoidAlgebra.mapDomain φ b = 0 := by
      show MonoidAlgebra.mapDomain (Quotient.out ∘ QuotientGroup.mk' Nsub) b = 0
      rw [MonoidAlgebra.mapDomain_comp, show MonoidAlgebra.mapDomain (QuotientGroup.mk' Nsub) b = proj Nsub b from rfl,
        hb, MonoidAlgebra.mapDomain_zero]
    have key (c : FreeGroupRing α) :
        c - MonoidAlgebra.mapDomain φ c ∈ Submodule.span (FreeGroupRing α) {y | ∃ r ∈ Nsub, y = grp r - 1} := by
      induction c using MonoidAlgebra.induction_linear with
      | zero => rw [MonoidAlgebra.mapDomain_zero, sub_zero]; exact Submodule.zero_mem _
      | add c₁ c₂ h₁ h₂ =>
          rw [show (c₁ + c₂) - MonoidAlgebra.mapDomain φ (c₁ + c₂) =
            (c₁ - MonoidAlgebra.mapDomain φ c₁) + (c₂ - MonoidAlgebra.mapDomain φ c₂) by
              rw [MonoidAlgebra.mapDomain_add]; abel]
          exact Submodule.add_mem _ h₁ h₂
      | single g n =>
          have hmem : (φ g)⁻¹ * g ∈ Nsub := QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
          rw [show (single g n : FreeGroupRing α) - MonoidAlgebra.mapDomain φ (single g n) =
              ((n : ℤ) : FreeGroupRing α) • (grp (φ g) • (grp ((φ g)⁻¹ * g) - 1)) by
            rw [MonoidAlgebra.mapDomain_single, smul_eq_mul, smul_eq_mul, mul_sub, ← grp_mul,
              mul_inv_cancel_left, mul_one, single_eq_smul_grp, single_eq_smul_grp, ← smul_sub, zsmul_eq_mul]]
          exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hmem, rfl⟩))
    have hb' := key b; rwa [hmap, sub_zero] at hb'
  refine (Submodule.span_induction
    (p := fun y _ => aug y = 0 ∧ foxProj Nsub y ∈ foxMod (Nsub := Nsub)) ?_
    ⟨by simp, Submodule.zero_mem _⟩ ?_ ?_ hrel).2
  · rintro _ ⟨r, hr, rfl⟩
    exact ⟨by simp [map_sub], r, hr, funext fun i => by simp [foxProj, foxVec, ← grp_one, foxLin_grp, fox_one]⟩
  · rintro x y _ _ ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨by rw [map_add, hx1, hy1, add_zero],
      by rw [show foxProj Nsub (x + y) = foxProj Nsub x + foxProj Nsub y by funext i; simp [foxProj]]
         exact Submodule.add_mem _ hx2 hy2⟩
  · rintro a x _ ⟨hx1, hx2⟩
    exact ⟨by rw [smul_eq_mul, map_mul, hx1, mul_zero],
      by rw [show foxProj Nsub (a • x) = proj Nsub a • foxProj Nsub x by
            funext i; simp [smul_eq_mul, foxProj, foxLin_mul, hx1]]
         exact Submodule.smul_mem _ _ hx2⟩

variable {J : Type*} [Fintype J] (ρ : J → FreeGroup α)

def bdry2 (u : J → CoverRing Nsub) : α → CoverRing Nsub :=
  fun i => ∑ j : J, u j * proj Nsub (fox i (ρ j))

theorem bdry2_add (u v : J → CoverRing Nsub) :
    bdry2 Nsub ρ (u + v) = bdry2 Nsub ρ u + bdry2 Nsub ρ v := by
  funext i; simp [bdry2, add_mul, Finset.sum_add_distrib]

theorem bdry2_zero : bdry2 Nsub ρ 0 = 0 := by funext i; simp [bdry2]
