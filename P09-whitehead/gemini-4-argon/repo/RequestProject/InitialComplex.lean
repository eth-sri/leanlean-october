module

public import RequestProject.Cockcroft
public import RequestProject.AbelianElimination
public import RequestProject.FoxNaturality
public import RequestProject.InitialPair
public import RequestProject.Pi2Dictionary

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FiniteChains

open MonoidAlgebra
open scoped commutatorElement IsMulCommutative

universe u

variable {I J : Type u}

abbrev GenY (I : Type u) : Type u := I ⊕ (I × Bool)

abbrev CrossY (I : Type u) [LinearOrder I] : Type u := {p : I × I // p.1 < p.2} × Bool × Bool

abbrev CellY (I J : Type u) [LinearOrder I] : Type u := J ⊕ (I ⊕ CrossY I)

def xGen (i : I) : FreeGroup (GenY I) := FreeGroup.of (Sum.inl i)
def yGen (i : I) (s : Bool) : FreeGroup (GenY I) := FreeGroup.of (Sum.inr (i, s))

def thetaFree : FreeGroup (GenY I) →* Multiplicative (I × Bool →₀ ℤ) :=
  FreeGroup.lift fun
    | Sum.inl _ => 1
    | Sum.inr P => Multiplicative.ofAdd (Finsupp.single P (1 : ℤ))

variable [LinearOrder I]

def relY (r : J → FreeGroup I) : CellY I J → FreeGroup (GenY I)
  | Sum.inl j => FreeGroup.map Sum.inl (r j)
  | Sum.inr (Sum.inl i) => xGen i * ⁅yGen i false, yGen i true⁆⁻¹
  | Sum.inr (Sum.inr (⟨p, _⟩, s, t)) => ⁅yGen p.1 s, yGen p.2 t⁆

variable (r : J → FreeGroup I)

abbrev GroupY : Type u := PresGroup (relY r)

def xEl (i : I) : GroupY r := QuotientGroup.mk (xGen i)
def yEl (i : I) (s : Bool) : GroupY r := QuotientGroup.mk (yGen i s)

theorem mk_relY (c : CellY I J) : (QuotientGroup.mk (relY r c) : GroupY r) = 1 :=
  (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_normalClosure ⟨c, rfl⟩)

theorem commute_yEl_of_ne {i k : I} (hik : i ≠ k) (s t : Bool) :
    Commute (yEl r i s) (yEl r k t) := by
  have hlt {a b : I} (hab : a < b) (u v : Bool) : Commute (yEl r a u) (yEl r b v) := by
    have h : (QuotientGroup.mk' (relSub (relY r))) ⁅yGen a u, yGen b v⁆ = 1 :=
      mk_relY r (Sum.inr (Sum.inr (⟨(a, b), hab⟩, u, v)))
    rwa [map_commutatorElement, commutatorElement_eq_one_iff_commute] at h
  exact (lt_or_gt_of_ne hik).elim (fun h => hlt h s t) fun h => (hlt h t s).symm

theorem xEl_eq_commutator (i : I) : xEl r i = ⁅yEl r i false, yEl r i true⁆ := by
  have h : (QuotientGroup.mk' (relSub (relY r))) (xGen i * ⁅yGen i false, yGen i true⁆⁻¹) = 1 :=
    mk_relY r (Sum.inr (Sum.inl i))
  rw [map_mul, map_inv, map_commutatorElement] at h
  exact mul_inv_eq_one.1 h

def ExpSurjective : Prop := Function.Surjective (Finsupp.linearCombination ℤ (expCol r))

variable {r}

theorem commutator_yEl_eq_one (hM : ExpSurjective r) (i : I) :
    ⁅yEl r i false, yEl r i true⁆ = 1 := by
  have hab : CrossCommuting (fun i => yEl r i false) (fun i => yEl r i true) := fun i k hik =>
    ⟨commute_yEl_of_ne r hik false false, commute_yEl_of_ne r hik false true,
      commute_yEl_of_ne r hik true false, commute_yEl_of_ne r hik true true⟩
  have hrel (j : J) : FreeGroup.lift (fun i => ⁅yEl r i false, yEl r i true⁆) (r j) = 1 := by
    rw [congrArg FreeGroup.lift (funext fun i => (xEl_eq_commutator r i).symm),
      show FreeGroup.lift (xEl r) (r j) = QuotientGroup.mk (FreeGroup.map Sum.inl (r j)) from
        DFunLike.congr_fun (FreeGroup.ext_hom _ ((QuotientGroup.mk' _).comp (FreeGroup.map Sum.inl))
          fun _ => FreeGroup.lift_apply_of) (r j)]
    exact mk_relY r (Sum.inl j)
  exact eq_one_of_expCol_surjective _ (commute_pairComm _ _ hab) r hrel hM i

theorem xEl_eq_one (hM : ExpSurjective r) (i : I) : xEl r i = 1 := by
  rw [xEl_eq_commutator, commutator_yEl_eq_one hM]

def yRing (i : I) (s : Bool) : MonoidAlgebra ℤ (GroupY r) :=
  MonoidAlgebra.of ℤ (GroupY r) (yEl r i s)

theorem proj_fox_commutator {β : Type*} [DecidableEq β] (Nsub : Subgroup (FreeGroup β))
    [Nsub.Normal] (A B g : β)
    (hcomm : Commute (QuotientGroup.mk (FreeGroup.of A) : FreeGroup β ⧸ Nsub)
      (QuotientGroup.mk (FreeGroup.of B))) :
    proj Nsub (fox g ⁅FreeGroup.of A, FreeGroup.of B⁆)
      = (if g = A then 1 - qgrp Nsub (FreeGroup.of B) else 0)
        + (if g = B then qgrp Nsub (FreeGroup.of A) - 1 else 0) := by
  have hfree : fox g ⁅FreeGroup.of A, FreeGroup.of B⁆
      = (if g = A then (1 : FreeGroupRing β)
            - grp (FreeGroup.of A * FreeGroup.of B * (FreeGroup.of A)⁻¹) else 0)
        + (if g = B then grp (FreeGroup.of A) - grp ⁅FreeGroup.of A, FreeGroup.of B⁆ else 0) := by
    rcases eq_or_ne A B with rfl | hAB
    · rw [show ⁅FreeGroup.of A, FreeGroup.of A⁆ = 1 by simp,
        show FreeGroup.of A * FreeGroup.of A * (FreeGroup.of A)⁻¹ = FreeGroup.of A by group, fox_one]
      by_cases hA : g = A <;> simp [hA]
    · show fox g (FreeGroup.of A * FreeGroup.of B * (FreeGroup.of A)⁻¹ * (FreeGroup.of B)⁻¹) = _
      rw [fox_mul, fox_mul, fox_mul, fox_inv, fox_inv, fox_of, fox_of]
      by_cases hA : g = A <;> by_cases hB : g = B <;>
        simp [hA, hB, hAB, hAB.symm, grp_mul, commutatorElement_def] <;> noncomm_ring
  have hq1 : qgrp Nsub (FreeGroup.of A * FreeGroup.of B * (FreeGroup.of A)⁻¹)
      = qgrp Nsub (FreeGroup.of B) := congrArg (MonoidAlgebra.single · 1) <| by
    show (QuotientGroup.mk' Nsub) (FreeGroup.of A * FreeGroup.of B * (FreeGroup.of A)⁻¹) = _
    rw [map_mul, map_mul, map_inv]; simp only [QuotientGroup.mk'_apply, hcomm.eq, mul_inv_cancel_right]
  have hq2 : qgrp Nsub ⁅FreeGroup.of A, FreeGroup.of B⁆ = 1 := congrArg (MonoidAlgebra.single · 1) <| by
    rw [← QuotientGroup.mk'_apply, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.2 hcomm
  rw [hfree, map_add, apply_ite (proj Nsub), apply_ite (proj Nsub),
    map_zero, map_sub, map_sub, map_one, proj_grp, proj_grp, proj_grp, hq1, hq2]

variable (r)

def thetaY : GroupY r →* Multiplicative (I × Bool →₀ ℤ) :=
  QuotientGroup.lift (relSub (relY r)) thetaFree fun w hw =>
    Subgroup.normalClosure_le_normal (by
      rintro _ ⟨j | i | ⟨⟨⟨p, q⟩, _⟩, u, v⟩, rfl⟩
      · show thetaFree (FreeGroup.map Sum.inl (r j)) = 1
        generalize r j = u
        induction u using FreeGroup.induction_on <;> simp_all [thetaFree]
      · show thetaFree (xGen i * ⁅yGen i false, yGen i true⁆⁻¹) = 1
        rw [map_mul, map_inv, map_commutatorElement,
          commutatorElement_eq_one_iff_commute.2 (Commute.all _ _)]
        simp [xGen, thetaFree]
      · show thetaFree ⁅yGen p u, yGen q v⁆ = 1
        rw [map_commutatorElement, commutatorElement_eq_one_iff_commute.2 (Commute.all _ _)]) hw

def psiY (P : I × Bool) : MonoidAlgebra ℤ (GroupY r) →ₗ[ℤ] ℤ :=
  (Finsupp.linearCombination ℤ fun g : GroupY r => (Multiplicative.toAdd (thetaY r g)) P).comp
    (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

variable [DecidableEq I] {r}

theorem commute_yEl (hM : ExpSurjective r) (i k : I) (s t : Bool) :
    Commute (yEl r i s) (yEl r k t) := by
  by_cases hik : i = k
  · subst hik
    have hc := commutatorElement_eq_one_iff_commute.mp (commutator_yEl_eq_one hM i)
    cases s <;> cases t <;> first | exact Commute.refl _ | exact hc | exact hc.symm
  · exact commute_yEl_of_ne r hik s t

theorem foxMatrix_inr_inl (i : I) (s : Bool) (j : J) :
    foxMatrixPres (relY r) (Sum.inr (i, s)) (Sum.inl j) = 0 := by
  show proj (relSub (relY r)) (fox (Sum.inr (i, s)) (FreeGroup.map Sum.inl (r j))) = 0
  rw [fox_map_of_not_mem_range Sum.inl (by simp), map_zero]

theorem foxMatrix_inr_mid (hM : ExpSurjective r) (i k : I) (s : Bool) :
    foxMatrixPres (relY r) (Sum.inr (i, s)) (Sum.inr (Sum.inl k))
      = if k = i then (if s then -(yRing (r := r) i false - 1) else yRing (r := r) i true - 1) else 0 := by
  show proj (relSub (relY r)) (fox (Sum.inr (i, s))
    ((FreeGroup.of (Sum.inl k) : FreeGroup (GenY I)) *
      ⁅FreeGroup.of (Sum.inr (k, false)), FreeGroup.of (Sum.inr (k, true))⁆⁻¹)) = _
  have hx : proj (relSub (relY r))
      (fox (Sum.inr (i, s)) (FreeGroup.of (Sum.inl k) : FreeGroup (GenY I))) = 0 := by
    rw [fox_of, if_neg (by simp), map_zero]
  have hqx : qgrp (relSub (relY r)) (FreeGroup.of (Sum.inl k) : FreeGroup (GenY I)) = 1 :=
    congrArg (MonoidAlgebra.single · 1) (xEl_eq_one hM k)
  have hqc : qgrp (relSub (relY r)) (⁅(FreeGroup.of (Sum.inr (k, false)) : FreeGroup (GenY I)),
      FreeGroup.of (Sum.inr (k, true))⁆⁻¹) = 1 :=
    congrArg (MonoidAlgebra.single · 1) (by
      show (QuotientGroup.mk' (relSub (relY r))) _ = 1
      rw [map_inv, map_commutatorElement, inv_eq_one]; exact commutator_yEl_eq_one hM k)
  rw [fox_mul, fox_inv, map_add, map_mul, map_neg, map_mul, hx, zero_add, proj_grp,
    hqx, one_mul, proj_grp, hqc, one_mul,
    proj_fox_commutator (relSub (relY r)) (Sum.inr (k, false)) (Sum.inr (k, true))
      (Sum.inr (i, s)) (commute_yEl hM k k false true)]
  change -((if (Sum.inr (i, s) : GenY I) = Sum.inr (k, false) then 1 - yRing (r := r) k true else 0) +
    (if (Sum.inr (i, s) : GenY I) = Sum.inr (k, true) then yRing (r := r) k false - 1 else 0)) = _
  by_cases hik : k = i
  · subst hik; cases s <;> simp
  · have hne (b : Bool) : (Sum.inr (i, s) : GenY I) ≠ Sum.inr (k, b) := by simp [Ne.symm hik]
    simp [hik, hne]

variable (r)

theorem psiY_mul_sub_one (P Q : I × Bool) (z : MonoidAlgebra ℤ (GroupY r)) :
    psiY r P (z * (yRing (r := r) Q.1 Q.2 - 1)) = augPres (relY r) z * (if Q = P then 1 else 0) := by
  have hgrp (g : GroupY r) : psiY r P (z * (MonoidAlgebra.of ℤ (GroupY r) g - 1))
      = augPres (relY r) z * (Multiplicative.toAdd (thetaY r g)) P := by
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add z₁ z₂ h₁ h₂ => rw [add_mul, map_add, h₁, h₂, map_add, add_mul]
    | single h n =>
        rw [show (MonoidAlgebra.single h n : MonoidAlgebra ℤ (GroupY r)) *
            (MonoidAlgebra.of ℤ (GroupY r) g - 1) =
            MonoidAlgebra.single (h * g) n - MonoidAlgebra.single h n by
          rw [mul_sub, mul_one, of_apply, MonoidAlgebra.single_mul_single, mul_one],
          map_sub, augQ_single]
        show Finsupp.linearCombination ℤ _ (Finsupp.single (h * g) n) -
          Finsupp.linearCombination ℤ _ (Finsupp.single h n) = _
        rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single, smul_eq_mul, smul_eq_mul, map_mul]
        change n * (Multiplicative.toAdd (thetaY r h) P + Multiplicative.toAdd (thetaY r g) P) - _ = _
        ring
  rw [show yRing (r := r) Q.1 Q.2 = MonoidAlgebra.of ℤ (GroupY r) (yEl r Q.1 Q.2) from rfl,
    hgrp, show Multiplicative.toAdd (thetaY r (yEl r Q.1 Q.2)) = Finsupp.single Q 1 from
      congrArg Multiplicative.toAdd FreeGroup.lift_apply_of]
  simp [Finsupp.single_apply]

variable {r}

theorem psiY_cross_term (hM : ExpSurjective r) (P : I × Bool) (i : I) (s : Bool)
    (c : CrossY I) (z : MonoidAlgebra ℤ (GroupY r)) :
    psiY r P (z * foxMatrixPres (relY r) (Sum.inr (i, s)) (Sum.inr (Sum.inr c)))
      = (if (i, s) = (c.1.1.1, c.2.1)
            then -(augPres (relY r) z * (if (c.1.1.2, c.2.2) = P then 1 else 0)) else 0)
        + (if (i, s) = (c.1.1.2, c.2.2)
            then augPres (relY r) z * (if (c.1.1.1, c.2.1) = P then 1 else 0) else 0) := by
  have hcross : foxMatrixPres (relY r) (Sum.inr (i, s)) (Sum.inr (Sum.inr c))
      = (if (i, s) = (c.1.1.1, c.2.1) then 1 - yRing (r := r) c.1.1.2 c.2.2 else 0)
        + (if (i, s) = (c.1.1.2, c.2.2) then yRing (r := r) c.1.1.1 c.2.1 - 1 else 0) := by
    obtain ⟨⟨⟨p, q⟩, _⟩, u, v⟩ := c
    show proj (relSub (relY r)) (fox (Sum.inr (i, s))
      ⁅(FreeGroup.of (Sum.inr (p, u)) : FreeGroup (GenY I)), FreeGroup.of (Sum.inr (q, v))⁆) = _
    rw [proj_fox_commutator (relSub (relY r)) (Sum.inr (p, u)) (Sum.inr (q, v))
      (Sum.inr (i, s)) (commute_yEl hM p q u v)]
    change (if (Sum.inr (i, s) : GenY I) = Sum.inr (p, u) then 1 - yRing (r := r) q v else 0) +
      (if (Sum.inr (i, s) : GenY I) = Sum.inr (q, v) then yRing (r := r) p u - 1 else 0) = _
    simp [Prod.ext_iff]
  have hsub (Q : I × Bool) : psiY r P (z * (1 - yRing (r := r) Q.1 Q.2)) =
      -(augPres (relY r) z * (if Q = P then 1 else 0)) := by
    rw [show z * (1 - yRing (r := r) Q.1 Q.2) = -(z * (yRing (r := r) Q.1 Q.2 - 1)) by noncomm_ring,
      map_neg, psiY_mul_sub_one]
  rw [hcross, mul_add, map_add]
  congr 1 <;> split_ifs <;>
    simp_all [hsub (c.1.1.2, c.2.2), psiY_mul_sub_one r P (c.1.1.1, c.2.1) z]
