import RequestProject.Cockcroft
import RequestProject.AbelianElimination
import RequestProject.FoxNaturality
import RequestProject.InitialPair
import RequestProject.Pi2Dictionary
import RequestProject.Tac
noncomputable section


/-!
# The initial Cockcroft pair `D ⊂ Y_D` of Lemma 3.1

Let `D` be given by a finite presentation `⟨x_i (i ∈ I) | r_j (j ∈ J)⟩` with exponent-sum
matrix `M`.  Lemma 3.1 of the paper builds the complex

  `Y_D = ⟨x_i, a_i, b_i | r_j, x_i[a_i,b_i]⁻¹, [a_i,a_k], [a_i,b_k], [b_i,a_k], [b_i,b_k]⟩`
                                                                            `(i < k)`

and proves: `G(Y_D) = ⊕_i (ℤ a_i ⊕ ℤ b_i)`, the complex `Y_D` is Cockcroft, and the
inclusion `D ⊂ Y_D` kills `π₁(D)` and is zero on `π₂`.

This file carries out the whole of Lemma 3.1 inside the combinatorial model of the project:
`Y_D` is the presentation `FiniteChains.relY` on the generators `FiniteChains.GenY` and the
two-cells `FiniteChains.CellY`, `π₂` is the module of Fox cycles and the Cockcroft property
is `FiniteChains.IsCockcroft` (see `RequestProject/Cockcroft.lean`).

The paper obtains the Cockcroft property of `Y_D` from a comparison with a torus, using
`π₂(torus) = 0` and naturality of the Hurewicz map.  Here it is proved directly: a Fox
cycle is evaluated by the homomorphism `ℤ[G] → ℤ^{(I × Bool)}` induced by
`G(Y_D) → ⊕_i (ℤ a_i ⊕ ℤ b_i)`, which kills products of elements of the augmentation ideal.
That evaluation makes the cycle equations at the generators `a_i, b_i` force the
coefficients of the cells `x_i[a_i,b_i]⁻¹` and of the cross-commutators to have zero
augmentation, and the cycle equations at the generators `x_i` then say that the remaining
augmentation vector is killed by `M`, hence is zero because `D` is acyclic.
-/

bwd

namespace FiniteChains

open MonoidAlgebra
open scoped commutatorElement IsMulCommutative

universe u

variable {I J : Type u}

/-- The generators of `Y_D`: the generators `x_i` of `D` (`Sum.inl i`) and the two added
generators `a_i = y_{i,false}`, `b_i = y_{i,true}` (`Sum.inr (i, s)`). -/
abbrev GenY (I : Type u) := I ⊕ (I × Bool)

/-- The index set of the cross-commutators `[y_{i,s}, y_{k,t}]`, one for each pair `i < k`
and each pair of signs. -/
abbrev CrossY (I : Type u) [LinearOrder I] := {p : I × I // p.1 < p.2} × Bool × Bool

/-- The two-cells of `Y_D`: the relators `r_j` of `D`, the new relators `x_i[a_i,b_i]⁻¹`,
and the cross-commutators. -/
abbrev CellY (I J : Type u) [LinearOrder I] := J ⊕ (I ⊕ CrossY I)

/-- The generator `x_i` of `Y_D`. -/
def xGen (i : I) : FreeGroup (GenY I) := FreeGroup.of (Sum.inl i)

/-- The generator `a_i` (`s = false`) or `b_i` (`s = true`) of `Y_D`. -/
def yGen (i : I) (s : Bool) : FreeGroup (GenY I) := FreeGroup.of (Sum.inr (i, s))

variable [LinearOrder I]

/-- The relators of `Y_D`. -/
def relY (r : J → FreeGroup I) : CellY I J → FreeGroup (GenY I)
  | Sum.inl j => FreeGroup.map Sum.inl (r j)
  | Sum.inr (Sum.inl i) => xGen i * ⁅yGen i false, yGen i true⁆⁻¹
  | Sum.inr (Sum.inr (⟨p, _⟩, s, t)) => ⁅yGen p.1 s, yGen p.2 t⁆

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] (r : J → FreeGroup I)

/-- The fundamental group `G(Y_D)` of the complex `Y_D`. -/
abbrev GroupY := PresGroup (relY r)

/-- The image of `x_i` in `G(Y_D)`. -/
def xEl (i : I) : GroupY r := QuotientGroup.mk (xGen i)

/-- The image of `a_i`, `b_i` in `G(Y_D)`. -/
def yEl (i : I) (s : Bool) : GroupY r := QuotientGroup.mk (yGen i s)

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem mk_relY (c : CellY I J) : (QuotientGroup.mk (relY r c) : GroupY r) = 1 := by
  rw [QuotientGroup.eq_one_iff]
  exact Subgroup.subset_normalClosure ⟨c, rfl⟩

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- The cross-commutators: generators with a smaller and a larger index commute. -/
theorem commute_yEl_of_lt {i k : I} (hik : i < k) (s t : Bool) :
    Commute (yEl r i s) (yEl r k t) := by
  have h : (QuotientGroup.mk (relY r (Sum.inr (Sum.inr (⟨(i, k), hik⟩, s, t)))) : GroupY r) = 1 :=
    mk_relY r _
  have hrel : relY r (Sum.inr (Sum.inr (⟨(i, k), hik⟩, s, t))) = ⁅yGen i s, yGen k t⁆ := rfl
  exact commutatorElement_eq_one_iff_commute.1 h

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- The cross-commutators: generators with different indices commute in `G(Y_D)`. -/
theorem commute_yEl_of_ne {i k : I} (hik : i ≠ k) (s t : Bool) :
    Commute (yEl r i s) (yEl r k t) := by
  rcases lt_or_gt_of_ne hik with h | h
  · exact commute_yEl_of_lt r h s t
  · exact (commute_yEl_of_lt r h t s).symm

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- The relator `x_i[a_i,b_i]⁻¹`: in `G(Y_D)` one has `x_i = [a_i, b_i]`. -/
theorem xEl_eq_commutator (i : I) : xEl r i = ⁅yEl r i false, yEl r i true⁆ := by
  have h :=
    mk_relY r (Sum.inr (Sum.inl i))
  exact mul_inv_eq_one.1 h

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- The homomorphism `π₁(D) → G(Y_D)` induced by the inclusion, on the level of free
groups. -/
theorem lift_xEl (w : FreeGroup I) :
    FreeGroup.lift (xEl r) w = (QuotientGroup.mk (FreeGroup.map Sum.inl w) : GroupY r) := by
  have h : FreeGroup.lift (xEl r)
      = ((QuotientGroup.mk' _).comp (FreeGroup.map Sum.inl)) := by
    aesop
  simp_all

/-- Surjectivity of the exponent-sum matrix of `D` — part of the acyclicity of `D`. -/
def ExpSurjective := Function.Surjective (Finsupp.linearCombination ℤ (expCol r))

variable {r}

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- **The elimination step of Lemma 3.1.**  If the exponent-sum matrix of `D` is surjective,
then `[a_i, b_i] = 1` in `G(Y_D)`. -/
theorem commutator_yEl_eq_one (hM : ExpSurjective r) (i : I) :
    ⁅yEl r i false, yEl r i true⁆ = 1 := by
  have hab : CrossCommuting (yEl r · false) (yEl r · true) := by
    intro i k hik
    exact ⟨commute_yEl_of_ne r hik false false, commute_yEl_of_ne r hik false true,
      commute_yEl_of_ne r hik true false, commute_yEl_of_ne r hik true true⟩
  have hu :=
    (commute_pairComm _ _ hab)
  have hlift : FreeGroup.lift (fun i => ⁅yEl r i false, yEl r i true⁆)
      = FreeGroup.lift (xEl r) := by
    refine congrArg _ (funext fun i => ?_)
    exact (xEl_eq_commutator r i).symm
  have hrel : ∀ j, FreeGroup.lift (fun i => ⁅yEl r i false, yEl r i true⁆) (r j) = 1 := by
    intro j
    rw [hlift, lift_xEl r]
    exact mk_relY r (Sum.inl j)
  exact eq_one_of_expCol_surjective _ hu r hrel hM i

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- **The inclusion `D ⊂ Y_D` kills `π₁(D)`**: every generator `x_i` of `D` becomes trivial
in `G(Y_D)`. -/
theorem xEl_eq_one (hM : ExpSurjective r) (i : I) : xEl r i = 1 := by
  rw [xEl_eq_commutator, commutator_yEl_eq_one hM]

omit [Fintype I] [Fintype J] [DecidableEq J] in
/-- **All added generators commute** in `G(Y_D)`. -/
theorem commute_yEl (hM : ExpSurjective r) (i k : I) (s t : Bool) :
    Commute (yEl r i s) (yEl r k t) := by
  by_cases hik : i = k
  · subst hik
    have hc := commutatorElement_eq_one_iff_commute.mp (commutator_yEl_eq_one hM i)
    cases s <;> cases t <;>
      first
        | exact Commute.refl _
        | exact hc
        | exact hc.symm
  · exact commute_yEl_of_ne r hik s t

/-! ### The Fox matrix of `Y_D` -/

/-- The image of the group element `y_{i,s}` in the group ring `ℤ[G(Y_D)]`. -/
def yRing (i : I) (s : Bool) :=
  MonoidAlgebra.of ℤ _ (yEl r i s)

/-- The Fox derivative of a commutator of two free generators. -/
theorem fox_commutator_free {β : Type*} [DecidableEq β] A B g :
    fox g ⁅FreeGroup.of A, FreeGroup.of B⁆
      = (if g = A then (1 : FreeGroupRing β)
            - grp (FreeGroup.of A * FreeGroup.of B * (FreeGroup.of A)⁻¹) else 0)
        + (if g = B then grp (FreeGroup.of A)
            - grp ⁅FreeGroup.of A, FreeGroup.of B⁆ else 0) := by
  rcases eq_or_ne A B with rfl | hAB
  · aesop
  · show fox g (FreeGroup.of A * FreeGroup.of B * (FreeGroup.of A)⁻¹ * (FreeGroup.of B)⁻¹) = _
    rw [fox_mul, fox_mul, fox_mul, fox_inv, fox_inv, fox_of, fox_of]
    by_cases hA : g = A <;> by_cases hB : g = B <;>
      simp [hA, hB, hAB, hAB.symm, grp_mul, commutatorElement_def] <;> noncomm_ring

/-- The Fox derivative of a commutator of two free generators, read in a quotient in which
the two images commute. -/
theorem proj_fox_commutator {β : Type*} [DecidableEq β] (Nsub : Subgroup (FreeGroup β))
    [Nsub.Normal] A B g
    (hcomm : Commute (QuotientGroup.mk (FreeGroup.of A) : FreeGroup β ⧸ Nsub)
      (QuotientGroup.mk (FreeGroup.of B))) :
    proj Nsub (fox g ⁅FreeGroup.of A, FreeGroup.of B⁆)
      = (if g = A then 1 - qgrp Nsub (FreeGroup.of B) else 0)
        + (if g = B then qgrp Nsub (FreeGroup.of A) - 1 else 0) := by
  have hconj : (QuotientGroup.mk (FreeGroup.of A * FreeGroup.of B * (FreeGroup.of A)⁻¹)
      : FreeGroup β ⧸ Nsub) = QuotientGroup.mk (FreeGroup.of B) := by
    simp [map_mul, map_inv, QuotientGroup.mk'_apply, hcomm.eq, mul_inv_cancel_right]
  have hcom1 : (QuotientGroup.mk ⁅FreeGroup.of A, FreeGroup.of B⁆) = 1 := commutatorElement_eq_one_iff_commute.2 hcomm
  have hq1 : qgrp Nsub (FreeGroup.of A * FreeGroup.of B * (FreeGroup.of A)⁻¹)
      = qgrp Nsub (FreeGroup.of B) :=
    congrArg (MonoidAlgebra.single · (1)) hconj
  have hq2 : qgrp Nsub ⁅FreeGroup.of A, FreeGroup.of B⁆ = 1 := by
    unfold qgrp
    rw [hcom1]
    rfl
  simp [fox_commutator_free, map_add, apply_ite (proj Nsub), map_zero, map_sub, map_one, proj_grp, hq1, hq2]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem yRing_eq_qgrp (i : I) (s : Bool) :
    yRing (r := r) i s
      = qgrp (relSub (relY r)) (FreeGroup.of (Sum.inr (i, s)) : FreeGroup (GenY I)) := rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- In `G(Y_D)` the generators `x_k` are trivial, so they are trivial in the group ring. -/
theorem qgrp_xGen (hM : ExpSurjective r) (k : I) :
    qgrp (relSub (relY r)) (FreeGroup.of (Sum.inl k) : FreeGroup (GenY I)) = 1 := by
  have h : (QuotientGroup.mk (FreeGroup.of (Sum.inl k) : FreeGroup (GenY I)) : GroupY r) = 1 :=
    xEl_eq_one hM k
  unfold qgrp
  rw [h]
  rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- The commutator `[a_k, b_k]` is trivial in `G(Y_D)`. -/
theorem qgrp_comm_inv (hM : ExpSurjective r) (k : I) :
    qgrp (relSub (relY r)) (⁅(FreeGroup.of (Sum.inr (k, false)) : FreeGroup (GenY I)),
      FreeGroup.of (Sum.inr (k, true))⁆⁻¹) = 1 := by
  have h : (QuotientGroup.mk (⁅(FreeGroup.of (Sum.inr (k, false)) : FreeGroup (GenY I)),
      FreeGroup.of (Sum.inr (k, true))⁆⁻¹) : GroupY r) = 1 := by
    show (QuotientGroup.mk' _)
      (⁅(FreeGroup.of (Sum.inr (k, false)) : FreeGroup (GenY I)),
        FreeGroup.of (Sum.inr (k, true))⁆⁻¹) = 1
    rw [map_inv, map_commutatorElement, inv_eq_one]
    exact commutator_yEl_eq_one hM k
  unfold qgrp
  rw [h]
  rfl

omit [Fintype I] [Fintype J] [DecidableEq J] in
/-- The Fox matrix of `Y_D` at a new generator and an old two-cell vanishes. -/
theorem foxMatrix_inr_inl (i : I) (s : Bool) (j : J) :
    foxMatrixPres (relY r) (Sum.inr (i, s)) (Sum.inl j) = 0 := by
  show proj _ (fox (Sum.inr (i, s)) (FreeGroup.map Sum.inl (r j))) = 0
  rw [fox_map_of_not_mem_range Sum.inl (by simp), map_zero]

omit [Fintype I] [Fintype J] [DecidableEq J] in
/-- The Fox matrix of `Y_D` at a new generator and a cell `x_k[a_k,b_k]⁻¹`. -/
theorem foxMatrix_inr_mid (hM : ExpSurjective r) (i k : I) (s : Bool) :
    foxMatrixPres (relY r) (Sum.inr (i, s)) (Sum.inr (Sum.inl k))
      = if k = i then (if s then -(yRing (r := r) i false - 1) else yRing (r := r) i true - 1) else 0 := by
  show proj (relSub (relY r)) (fox (Sum.inr (i, s))
    ((FreeGroup.of (Sum.inl k) : FreeGroup (GenY I)) *
      ⁅FreeGroup.of (Sum.inr (k, false)), FreeGroup.of (Sum.inr (k, true))⁆⁻¹)) = _
  have hx : proj (relSub (relY r))
      (fox (Sum.inr (i, s)) (FreeGroup.of (Sum.inl k) : FreeGroup (GenY I))) = 0 := by
    simp
  have hcomm := proj_fox_commutator (relSub (relY r)) _ _
    (Sum.inr (i, s)) (commute_yEl hM k k false true)
  rw [fox_mul, fox_inv, map_add, map_mul, map_neg, map_mul, hx, zero_add, proj_grp,
    qgrp_xGen hM, one_mul, proj_grp, qgrp_comm_inv hM, one_mul, hcomm]
  aesop

omit [Fintype I] [Fintype J] [DecidableEq J] in
/-- The Fox matrix of `Y_D` at a new generator and a cross-commutator. -/
theorem foxMatrix_inr_cross (hM : ExpSurjective r) (i : I) (s : Bool) (c : CrossY I) :
    foxMatrixPres (relY r) (Sum.inr (i, s)) (Sum.inr (Sum.inr c))
      = (if (i, s) = (c.1.1.1, c.2.1) then 1 - yRing (r := r) c.1.1.2 c.2.2 else 0)
        + (if (i, s) = (c.1.1.2, c.2.2) then yRing (r := r) c.1.1.1 c.2.1 - 1 else 0) := by
  obtain ⟨⟨⟨p, q⟩, hpq⟩, u, v⟩ := c
  show proj _ (fox (Sum.inr (i, s))
    ⁅(FreeGroup.of (Sum.inr (p, u)) : FreeGroup (GenY I)), FreeGroup.of (Sum.inr (q, v))⁆) = _
  simp [proj_fox_commutator (relSub (relY r)) _ _
    _ (commute_yEl hM p q u v), ← yRing_eq_qgrp]

/-! ### The evaluation homomorphism -/

variable (r)

/-- The homomorphism of the free group onto `⊕_i (ℤ a_i ⊕ ℤ b_i)` used in Lemma 3.1: the
generators `x_i` go to `0` and the generators `a_i, b_i` to the corresponding basis
vectors. -/
def thetaFree : FreeGroup (GenY I) →* Multiplicative (I × Bool →₀ ℤ) :=
  FreeGroup.lift fun g =>
    match g with
    | Sum.inl _ => 1
    | Sum.inr P => Multiplicative.ofAdd (Finsupp.single P (1 : ℤ))

omit [LinearOrder I] [Fintype I] [DecidableEq I] in
theorem thetaFree_map_inl (w : FreeGroup I) :
    thetaFree (FreeGroup.map Sum.inl w) = 1 := by
  have h : thetaFree.comp (FreeGroup.map (Sum.inl : I → GenY I))
      = (1 : FreeGroup I →* Multiplicative (I × Bool →₀ ℤ)) := by
    aesop
  exact congrArg (· w) h

omit [Fintype J] [DecidableEq J] in
omit [Fintype I] [DecidableEq I] in
theorem thetaFree_relY (c : CellY I J) : thetaFree (relY r c) = 1 := by
  match c with
  | Sum.inl j => exact thetaFree_map_inl _
  | Sum.inr (Sum.inl i) =>
      show thetaFree ((FreeGroup.of (Sum.inl i) : FreeGroup (GenY I)) *
        ⁅FreeGroup.of (Sum.inr (i, false)), FreeGroup.of (Sum.inr (i, true))⁆⁻¹) = 1
      rw [map_mul, map_inv, map_commutatorElement,
        commutatorElement_eq_one_iff_commute.2 (Commute.all _ _)]
      aesop
  | Sum.inr (Sum.inr ⟨⟨(p, q), hpq⟩, u, v⟩) =>
      show thetaFree ⁅(FreeGroup.of (Sum.inr (p, u)) : FreeGroup (GenY I)),
        FreeGroup.of (Sum.inr (q, v))⁆ = 1
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.2 (Commute.all _ _)

/-- The homomorphism `G(Y_D) → ⊕_i (ℤ a_i ⊕ ℤ b_i)` of Lemma 3.1. -/
def thetaY : GroupY r →* Multiplicative (I × Bool →₀ ℤ) :=
  QuotientGroup.lift (relSub (relY r)) thetaFree
    (by
      have hsub : relSub (relY r) ≤ thetaFree.ker := by
        refine Subgroup.normalClosure_le_normal ?_
        rintro _ ⟨c, rfl⟩
        exact thetaFree_relY r c
      omega)

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem thetaY_yEl (i : I) (s : Bool) :
    Multiplicative.toAdd (thetaY r (yEl r i s)) = Finsupp.single (i, s) 1 := by
  show Multiplicative.toAdd (thetaFree (FreeGroup.of (Sum.inr (i, s)) : FreeGroup (GenY I)))
    = Finsupp.single (i, s) 1
  rw [thetaFree, FreeGroup.lift_apply_of]
  rfl

/-- The coordinate functional `ℤ[G(Y_D)] → ℤ` attached to a generator `y_P`: the
composition of `thetaY` with the `P`-th coordinate.  It kills products of two elements of
the augmentation ideal, which is what makes the cycle equations computable. -/
def psiY (P : I × Bool) : MonoidAlgebra ℤ (GroupY r) →ₗ[ℤ] ℤ :=
  (Finsupp.linearCombination ℤ fun g => (Multiplicative.toAdd (thetaY r g)) P).comp
    (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem psiY_single (P : I × Bool) (g : GroupY r) (n : ℤ) :
    psiY r P (MonoidAlgebra.single g n) = n * (Multiplicative.toAdd (thetaY r g)) P := by
  show Finsupp.linearCombination ℤ
      (fun g => (Multiplicative.toAdd (thetaY r g)) P) (Finsupp.single g n) = _
  simp

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- **The key computation.**  Evaluating `z · (g - 1)` returns the augmentation of `z`
times the `P`-th coordinate of the image of `g`; in particular products of two elements of
the augmentation ideal are killed. -/
theorem psiY_mul_group_sub_one (P : I × Bool) (g : GroupY r)
    (z : MonoidAlgebra ℤ (GroupY r)) :
    psiY r P (z * (MonoidAlgebra.of ℤ (GroupY r) g - 1))
      = augPres (relY r) z * (Multiplicative.toAdd (thetaY r g)) P := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add z₁ z₂ h₁ h₂ =>
      simp_all [add_mul, map_add, h₁, h₂]
  | single h n =>
      have hmul : (MonoidAlgebra.single h n : MonoidAlgebra ℤ (GroupY r)) *
          (MonoidAlgebra.of ℤ _ g - 1)
          = MonoidAlgebra.single (h * g) n - MonoidAlgebra.single h n := by
        rw [mul_sub, mul_one]
        simp
      rw [hmul, map_sub, psiY_single, psiY_single, augQ_single]
      simp [mul_add]

omit [Fintype I] [Fintype J] [DecidableEq J] in
theorem psiY_mul_sub_one (P Q : I × Bool) (z : MonoidAlgebra ℤ (GroupY r)) :
    psiY r P (z * (yRing (r := r) Q.1 Q.2 - 1)) = augPres (relY r) z * (if Q = P then 1 else 0) := by
  rw [show yRing (r := r) Q.1 Q.2 = MonoidAlgebra.of ℤ _ (yEl r Q.1 Q.2) from rfl,
    psiY_mul_group_sub_one, thetaY_yEl]
  grind

omit [Fintype I] [Fintype J] [DecidableEq J] in
theorem psiY_mul_one_sub (P Q : I × Bool) (z : MonoidAlgebra ℤ (GroupY r)) :
    psiY r P (z * (1 - yRing (r := r) Q.1 Q.2)) = -(augPres (relY r) z * (if Q = P then 1 else 0)) := by
  have h : z * (1 - yRing (r := r) Q.1 Q.2) = -(z * (yRing (r := r) Q.1 Q.2 - 1)) := by noncomm_ring
  rw [h, map_neg, psiY_mul_sub_one]

/-! ### Lemma 3.1 -/

variable {r}

omit [Fintype I] [Fintype J] [DecidableEq J] in
/-- The contribution of a cross-commutator cell to the cycle equation at a generator
`y_{i,s}`, evaluated in the coordinate `P`. -/
theorem psiY_cross_term (hM : ExpSurjective r) (P : I × Bool) (i : I) (s : Bool)
    (c : CrossY I) (z : MonoidAlgebra ℤ (GroupY r)) :
    psiY r P (z * foxMatrixPres (relY r) (Sum.inr (i, s)) (Sum.inr (Sum.inr c)))
      = (if (i, s) = (c.1.1.1, c.2.1)
            then -(augPres (relY r) z * (if (c.1.1.2, c.2.2) = P then 1 else 0)) else 0)
        + (if (i, s) = (c.1.1.2, c.2.2)
            then augPres (relY r) z * (if (c.1.1.1, c.2.1) = P then 1 else 0) else 0) := by
  rw [foxMatrix_inr_cross hM, mul_add, map_add]
  congr 1
  · by_cases h : (i, s) = (c.1.1.1, c.2.1)
    · rw [if_pos h, if_pos h]
      exact psiY_mul_one_sub r P (c.1.1.2, c.2.2) z
    grind
  · by_cases h : (i, s) = (c.1.1.2, c.2.2)
    · rw [if_pos h, if_pos h]
      exact psiY_mul_sub_one r P (c.1.1.1, c.2.1) z
    grind

/-! ### The inclusion `D ⊂ Y_D` -/

variable (r)

variable {r}

/-! ### The fundamental group of `Y_D` -/
