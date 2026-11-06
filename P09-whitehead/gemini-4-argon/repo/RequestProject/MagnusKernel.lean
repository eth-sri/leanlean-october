module

public import RequestProject.CoverChainComplex
public import RequestProject.SchreierTransversal

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FiniteChains

open MonoidAlgebra FreeGroup

variable {α : Type*} (Nsub : Subgroup (FreeGroup α))

def coefAt (s : FreeGroup α) : CoverRing Nsub →+ ℤ :=
  (Finsupp.applyAddHom (QuotientGroup.mk s : FreeGroup α ⧸ Nsub)).comp
    MonoidAlgebra.coeffAddEquiv.toAddMonoidHom

theorem coefAt_qgrp_of_ne {s u : FreeGroup α}
    (h : (QuotientGroup.mk u : FreeGroup α ⧸ Nsub) ≠ QuotientGroup.mk s) :
    coefAt Nsub s (qgrp Nsub u) = 0 :=
  Finsupp.single_eq_of_ne h.symm

variable [Nsub.Normal]

theorem qgrp_mul (u v : FreeGroup α) :
    qgrp Nsub (u * v) = qgrp Nsub u * qgrp Nsub v := by
  rw [qgrp, qgrp, qgrp, MonoidAlgebra.single_mul_single, QuotientGroup.mk_mul, mul_one]

theorem schreierGen_eq_one {t : FreeGroup α} (x : α)
    (h : t * FreeGroup.of x ∈ repSet Nsub) : schreierGen Nsub t x = 1 := by
  rw [schreierGen, rep_mk_of_mem Nsub h, mul_inv_cancel]

variable [DecidableEq α]

theorem foxVec_mul' (u v : FreeGroup α) (x : α) :
    foxVec Nsub (u * v) x = foxVec Nsub u x + qgrp Nsub u * foxVec Nsub v x := by
  show proj Nsub (fox x (u * v)) = proj Nsub (fox x u) + qgrp Nsub u * proj Nsub (fox x v)
  rw [fox_mul, map_add, _root_.map_mul (proj Nsub), proj_grp]

theorem foxVec_inv' (u : FreeGroup α) (x : α) :
    foxVec Nsub u⁻¹ x = -(qgrp Nsub u⁻¹ * foxVec Nsub u x) := by
  show proj Nsub (fox x u⁻¹) = -(qgrp Nsub u⁻¹ * proj Nsub (fox x u))
  rw [fox_inv, map_neg, _root_.map_mul (proj Nsub), proj_grp]

@[simp] theorem foxVec_of (x y : α) :
    foxVec Nsub (FreeGroup.of y) x = if x = y then 1 else 0 := by
  show proj Nsub (fox x (FreeGroup.of y)) = _
  rw [fox_of]; split <;> simp

theorem coefAt_foxVec_rep (q : FreeGroup α ⧸ Nsub) {s : FreeGroup α} (hs : s ∈ repSet Nsub)
    (x : α) (hsx : s * FreeGroup.of x ∉ repSet Nsub) :
    coefAt Nsub s (foxVec Nsub (rep Nsub q) x) = 0 := by
  have key : ∀ n : ℕ, ∀ q : FreeGroup α ⧸ Nsub, clen Nsub q ≤ n →
      coefAt Nsub s (foxVec Nsub (rep Nsub q) x) = 0 := by
    intro n; induction n with
    | zero =>
        intro q hq
        rw [rep_of_clen_eq_zero Nsub (Nat.le_zero.1 hq), foxVec_one]; rfl
    | succ n ih =>
        intro q hq
        by_cases h : clen Nsub q = 0
        · rw [rep_of_clen_eq_zero Nsub h, foxVec_one]; rfl
        · have hlt := parentData_clen Nsub h
          have hIH : coefAt Nsub s (foxVec Nsub (rep Nsub (parentData Nsub h).1) x) = 0 :=
            ih _ (by omega)
          set t' := rep Nsub (parentData Nsub h).1 with ht'
          have ht'mem : t' ∈ repSet Nsub := rep_mem_repSet Nsub _
          have hstep := rep_mul_letter Nsub h
          rw [← ht'] at hstep
          rcases hy : (parentData Nsub h).2 with ⟨y, _ | _⟩ <;> rw [hy] at hstep
          · have hqrep : rep Nsub q = t' * (FreeGroup.of y)⁻¹ := hstep
            rw [hqrep, foxVec_mul' Nsub, map_add, hIH, zero_add]
            by_cases hxy : x = y
            · subst hxy
              rw [foxVec_inv' Nsub, foxVec_of, if_pos rfl, mul_one, mul_neg, ← qgrp_mul, map_neg]
              by_cases hst : (QuotientGroup.mk (t' * (FreeGroup.of x)⁻¹) :
                  FreeGroup α ⧸ Nsub) = QuotientGroup.mk s
              · have hts := eq_of_mk_eq Nsub hs (hqrep ▸ rep_mem_repSet Nsub q) hst.symm
                exact absurd (by simpa [hts] using ht'mem) hsx
              · rw [coefAt_qgrp_of_ne Nsub hst, neg_zero]
            · rw [foxVec_inv' Nsub, foxVec_of, if_neg hxy, mul_zero, neg_zero, mul_zero, map_zero]
          · have hqrep : rep Nsub q = t' * FreeGroup.of y := hstep
            rw [hqrep, foxVec_mul' Nsub, map_add, hIH, zero_add]
            by_cases hxy : x = y
            · subst hxy
              rw [foxVec_of, if_pos rfl, mul_one]
              by_cases hst : (QuotientGroup.mk t' : FreeGroup α ⧸ Nsub) = QuotientGroup.mk s
              · have hts := eq_of_mk_eq Nsub hs ht'mem hst.symm
                exact absurd (hts.symm ▸ hqrep ▸ rep_mem_repSet Nsub q) hsx
              · exact coefAt_qgrp_of_ne Nsub hst
            · rw [foxVec_of, if_neg hxy, mul_zero, map_zero]
  exact key (clen Nsub q) q le_rfl

theorem coefAt_foxVec_schreierGen {t : FreeGroup α} (ht : t ∈ repSet Nsub) (y : α)
    {s : FreeGroup α} (hs : s ∈ repSet Nsub) (x : α) (hsx : s * FreeGroup.of x ∉ repSet Nsub) :
    coefAt Nsub s (foxVec Nsub (schreierGen Nsub t y) x)
      = if s = t ∧ x = y then 1 else 0 := by
  obtain ⟨qt, rfl⟩ := ht
  set t := rep Nsub qt
  set u := rep Nsub (QuotientGroup.mk (t * FreeGroup.of y))
  have hone : qgrp Nsub (t * FreeGroup.of y * u⁻¹) = 1 :=
    qgrp_eq_one_of_mem Nsub (schreierGen_mem Nsub t y)
  have hexp : foxVec Nsub (schreierGen Nsub t y) x =
      foxVec Nsub t x + qgrp Nsub t * foxVec Nsub (FreeGroup.of y) x - foxVec Nsub u x := by
    change foxVec Nsub (t * FreeGroup.of y * u⁻¹) x = _
    rw [foxVec_mul' Nsub, foxVec_mul' Nsub, foxVec_inv' Nsub,
      mul_neg, ← mul_assoc, ← qgrp_mul, hone, one_mul, ← sub_eq_add_neg]
  rw [hexp, map_sub, map_add, coefAt_foxVec_rep Nsub qt hs x hsx,
    coefAt_foxVec_rep Nsub _ hs x hsx, zero_add, sub_zero]
  by_cases hxy : x = y
  · subst hxy
    rw [foxVec_of, if_pos rfl, mul_one]
    by_cases hst : s = t
    · subst hst; rw [if_pos ⟨rfl, rfl⟩]; exact Finsupp.single_eq_same
    · rw [coefAt_qgrp_of_ne Nsub fun hq => hst (eq_of_mk_eq Nsub hs ⟨qt, rfl⟩ hq.symm),
        if_neg (by tauto)]
  · rw [foxVec_of, if_neg hxy, mul_zero, if_neg (by tauto), map_zero]

def foxHomNsub : Nsub →* Multiplicative (α → CoverRing Nsub) where
  toFun w := Multiplicative.ofAdd (foxVec Nsub (w : FreeGroup α))
  map_one' := by show Multiplicative.ofAdd (foxVec Nsub 1) = 1; rw [foxVec_one]; rfl
  map_mul' a b := by
    show Multiplicative.ofAdd (foxVec Nsub (a.1 * b.1)) = _
    rw [foxVec_mul a.2]; rfl

def foxAbAdd : Additive (Abelianization Nsub) →+ (α → CoverRing Nsub) where
  toFun a := Multiplicative.toAdd (Abelianization.lift (foxHomNsub Nsub) (Additive.toMul a))
  map_zero' := by
    show Multiplicative.toAdd (Abelianization.lift (foxHomNsub Nsub) 1) = 0
    rw [_root_.map_one]; rfl
  map_add' a b := by
    show Multiplicative.toAdd (Abelianization.lift (foxHomNsub Nsub) (Additive.toMul a * Additive.toMul b)) = _
    rw [_root_.map_mul]; rfl

theorem foxAbAdd_of (w : Nsub) :
    foxAbAdd Nsub (Additive.ofMul (Abelianization.of w)) = foxVec Nsub w.1 := by
  show Multiplicative.toAdd (Abelianization.lift (foxHomNsub Nsub) (Abelianization.of w)) = _
  rw [Abelianization.lift_apply_of]; rfl

def SchreierIdx : Type _ :=
  {p : (FreeGroup α ⧸ Nsub) × α // rep Nsub p.1 * FreeGroup.of p.2 ∉ repSet Nsub}

def schreierClass (i : SchreierIdx Nsub) : Additive (Abelianization Nsub) :=
  Additive.ofMul (Abelianization.of
    ⟨schreierGen Nsub (rep Nsub i.1.1) i.1.2, schreierGen_mem Nsub _ _⟩)

def schreierCoef (i : SchreierIdx Nsub) :
    Additive (Abelianization Nsub) →+ ℤ :=
  (coefAt Nsub (rep Nsub i.1.1)).comp
    ((Pi.evalAddMonoidHom (fun _ : α => CoverRing Nsub) i.1.2).comp (foxAbAdd Nsub))

theorem foxVec_eq_zero_iff {w : FreeGroup α} (hw : w ∈ Nsub) :
    foxVec Nsub w = 0 ↔ w ∈ ⁅Nsub, Nsub⁆ := by
  classical
  constructor
  · intro h0
    have hmem : w ∈ Subgroup.closure (schreierSet Nsub) := by rwa [closure_schreierGen Nsub]
    have hrep : ∀ u ∈ Subgroup.closure (schreierSet Nsub),
        ∃ (hu : u ∈ Nsub) (d : SchreierIdx Nsub →₀ ℤ),
          Additive.ofMul (Abelianization.of ⟨u, hu⟩) = d.sum fun i n => n • schreierClass Nsub i := by
      intro u hu
      induction hu using Subgroup.closure_induction with
      | mem g hg =>
          obtain ⟨⟨q, x⟩, rfl⟩ := hg
          by_cases h : rep Nsub q * FreeGroup.of x ∈ repSet Nsub
          · refine ⟨schreierGen_mem Nsub _ _, 0, ?_⟩
            simp [schreierGen_eq_one Nsub x h, show (⟨1, _⟩ : Nsub) = 1 from rfl]
          · exact ⟨schreierGen_mem Nsub _ _, Finsupp.single ⟨(q, x), h⟩ 1, by simp [schreierClass]⟩
      | one => exact ⟨Nsub.one_mem, 0, by simp [show (⟨1, _⟩ : Nsub) = 1 from rfl]⟩
      | mul x y _ _ ihx ihy =>
          obtain ⟨hx, d₁, h₁⟩ := ihx; obtain ⟨hy, d₂, h₂⟩ := ihy
          refine ⟨Nsub.mul_mem hx hy, d₁ + d₂, ?_⟩
          rw [show (⟨x * y, _⟩ : Nsub) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, _root_.map_mul, ofMul_mul,
            h₁, h₂, Finsupp.sum_add_index' (by simp) (fun _ _ _ => add_smul _ _ _)]
      | inv x _ ihx =>
          obtain ⟨hx, d, hd⟩ := ihx
          refine ⟨Nsub.inv_mem hx, -d, ?_⟩
          rw [show (⟨x⁻¹, _⟩ : Nsub) = ⟨x, hx⟩⁻¹ from rfl, _root_.map_inv, ofMul_inv,
            hd, Finsupp.sum_neg_index (by simp)]
          simp [neg_smul, Finsupp.sum_neg]
    obtain ⟨_, d, hd⟩ := hrep w hmem
    have hd0 : d = 0 := by
      ext i
      have hci : schreierCoef Nsub i (Additive.ofMul (Abelianization.of ⟨w, hw⟩)) = 0 := by
        show coefAt Nsub (rep Nsub i.1.1) (foxAbAdd Nsub (Additive.ofMul (Abelianization.of ⟨w, hw⟩)) i.1.2) = 0
        rw [foxAbAdd_of, h0]; rfl
      rw [hd, map_finsuppSum] at hci
      have hterm (j : SchreierIdx Nsub) (n : ℤ) :
          schreierCoef Nsub i (n • schreierClass Nsub j) = if j = i then n else 0 := by
        rw [map_zsmul]
        show n • coefAt Nsub (rep Nsub i.1.1)
          (foxAbAdd Nsub (schreierClass Nsub j) i.1.2) = _
        rw [schreierClass, foxAbAdd_of, coefAt_foxVec_schreierGen Nsub (rep_mem_repSet Nsub j.1.1) j.1.2
          (rep_mem_repSet Nsub i.1.1) i.1.2 i.2]
        by_cases hji : j = i
        · subst hji; simp
        · rw [if_neg ?_, if_neg hji, smul_zero]
          rintro ⟨h1, h2⟩
          refine hji (Subtype.ext (Prod.ext ?_ h2.symm))
          have := congrArg (QuotientGroup.mk : FreeGroup α → FreeGroup α ⧸ Nsub) h1
          simpa [mk_rep] using this.symm
      rw [Finsupp.sum_congr (g2 := fun j n => if j = i then n else 0) (fun j _ => hterm j (d j)),
        Finsupp.sum_ite_eq' d i (fun _ n => n)] at hci
      by_cases hi : i ∈ d.support
      · rwa [if_pos hi] at hci
      · exact Finsupp.notMem_support_iff.1 hi
    rw [hd0, Finsupp.sum_zero_index] at hd
    rw [← Subgroup.map_subtype_commutator Nsub]
    exact ⟨⟨w, hw⟩, (QuotientGroup.eq_one_iff _).1 (Additive.ofMul.injective hd), rfl⟩
  · intro hcomm
    rw [← Subgroup.map_subtype_commutator Nsub] at hcomm
    obtain ⟨u, hu, rfl⟩ := Subgroup.map_mono
      (Abelianization.commutator_subset_ker (foxHomNsub Nsub)) hcomm
    exact hu
