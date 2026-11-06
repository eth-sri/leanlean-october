import Mathlib
import RequestProject.GroupRingFree
import RequestProject.Tac
noncomputable section


/-!
# Reduction of group-ring coefficients along `Q → Q/H`

This file contains the dictionary that turns the reduction of a matrix over
`k[Q]` along `k[Q] → k[Q/H]` into the coefficientwise reduction, along the
augmentation `k[H] → k`, of the same matrix written over the commutative ring
`k[H]` in the basis of coset representatives.
-/

bwd

namespace FiniteChains

open MonoidAlgebra

variable (k : Type*) [CommRing k] {Q : Type*} [Group Q] (H : Subgroup Q)

/-- The augmentation `k[H] → k`. -/
def augH [IsMulCommutative H] : MonoidAlgebra k H →+* k :=
  (MonoidAlgebra.lift k k H (1 : H →* k)).toRingHom

/-- The reduction map of group rings `k[Q] → k[Q/H]`. -/
def quotRingHom [H.Normal] :=
  MonoidAlgebra.mapDomainRingHom k (QuotientGroup.mk' H)

variable {k H}

@[simp] theorem augH_single [IsMulCommutative H] h a :
    augH k H (single h a) = a := by
  simp [augH]

@[simp] theorem quotRingHom_single [H.Normal] q a :
    quotRingHom k H (single q a) = single (q : Q ⧸ H) a := MonoidAlgebra.mapDomain_single

variable (H) in
/-- For a normal subgroup the right cosets are the elements of the quotient group. -/
def cosetQuotEquiv [H.Normal] : RightCosets H ≃ Q ⧸ H where
  toFun := Quotient.map' id (by
    intro a b h
    rw [QuotientGroup.rightRel_apply] at h
    rw [QuotientGroup.leftRel_apply]
    have := (Subgroup.Normal.conj_mem (by infer_instance) _ h a⁻¹)
    have e : a⁻¹ * (b * a⁻¹) * a⁻¹⁻¹ = a⁻¹ * b := by group
    simp_all)
  invFun := Quotient.map' id (by
    intro a b h
    rw [QuotientGroup.leftRel_apply] at h
    rw [QuotientGroup.rightRel_apply]
    have := (Subgroup.Normal.conj_mem (by infer_instance) _ h a)
    simp_all)
  left_inv := by rintro ⟨q⟩; rfl
  right_inv := by rintro ⟨q⟩; rfl

@[simp] theorem cosetQuotEquiv_mk [H.Normal] q :
    cosetQuotEquiv H (Quotient.mk (QuotientGroup.rightRel H) q) = q := rfl

/-- The coordinates of an element of `k[Q]` in the `k[H]`-basis of coset representatives. -/
theorem cosetBasis_repr_cosetCombination [IsMulCommutative H]
    F :
    (cosetBasis (k := k) (H := H)).repr (cosetCombination F) = F := by
  simp [cosetBasis, cosetCombination]

theorem cosetCombination_single_single [IsMulCommutative H] q a :
    cosetCombination (Finsupp.single (Quotient.mk (QuotientGroup.rightRel H) q)
      (single ⟨q * (cosetRep H (Quotient.mk (QuotientGroup.rightRel H) q))⁻¹,
        mul_cosetRep_inv_mem q⟩ a)) = (single q a : MonoidAlgebra k Q) := by
  rw [cosetCombination, Finsupp.linearCombination_single, smul_def', groupRingIncl_single,
    MonoidAlgebra.single_mul_single]
  simp

theorem cosetBasis_repr_single [IsMulCommutative H] q a :
    (cosetBasis (k := k) (H := H)).repr (single q a) =
      Finsupp.single (Quotient.mk (QuotientGroup.rightRel H) q)
        (single ⟨q * (cosetRep H (Quotient.mk (QuotientGroup.rightRel H) q))⁻¹,
          mul_cosetRep_inv_mem q⟩ a) := by
  rw [← cosetCombination_single_single (k := k) (H := H) q a, cosetBasis_repr_cosetCombination]

/-- The key compatibility, on the generators `single q a` of `k[Q]`. -/
theorem augH_cosetBasis_repr_single [H.Normal] [IsMulCommutative H] q a
    c :
    augH k H ((cosetBasis (k := k) (H := H)).repr (single q a) c) =
      (quotRingHom k H (single q a)).coeff (cosetQuotEquiv H c) := by
  classical
  rw [cosetBasis_repr_single (k := k) (H := H) q a, quotRingHom_single (k := k) (H := H) q a]
  by_cases hc : c = Quotient.mk _ q
  · simp_all
  · rw [Finsupp.single_apply, if_neg (by grind), map_zero, MonoidAlgebra.coeff_single, Finsupp.single_apply,
      if_neg]
    intro h
    exact hc ((cosetQuotEquiv H).injective (by simp_all))

/-- **The key compatibility.**  Reducing an element of `k[Q]` to `k[Q/H]` amounts to
applying the augmentation `k[H] → k` to each of its coordinates in the basis of coset
representatives. -/
theorem augH_cosetBasis_repr [H.Normal] [IsMulCommutative H] x
    c :
    augH k H ((cosetBasis (k := k) (H := H)).repr x c) = (quotRingHom k H x).coeff (cosetQuotEquiv H c) := by
  classical
  -- both sides are additive in `x`, so it suffices to treat `x = single q a`
  set L : MonoidAlgebra k Q →+ k :=
    (augH k H).toAddMonoidHom.comp
      ((Finsupp.applyAddHom c).comp
        ((cosetBasis (k := k) (H := H)).repr.toLinearMap.toAddMonoidHom)) with hL
  set M : MonoidAlgebra k Q →+ k :=
    (Finsupp.applyAddHom (cosetQuotEquiv H c)).comp
      (MonoidAlgebra.coeffAddEquiv.toAddMonoidHom.comp (quotRingHom k H).toAddMonoidHom) with hM
  have hLM : L = M := by
    refine MonoidAlgebra.addMonoidHom_ext ?_
    intro q a
    exact augH_cosetBasis_repr_single q a c
  have := congrArg (· x) hLM
  tauto

variable (k H)

/-- A vector of elements of `k[Q]`, written in the `k[H]`-basis of coset representatives:
this exhibits `k[Q]^{(ι)}` as a free `k[H]`-module on `ι × (H \ Q)`. -/
def vecCoords ι [IsMulCommutative H] :
    (ι →₀ MonoidAlgebra k Q) ≃ₗ[MonoidAlgebra k H]
      ((ι × RightCosets H) →₀ MonoidAlgebra k H) :=
  (Finsupp.mapRange.linearEquiv (cosetBasis (k := k) (H := H)).repr).trans
    (Finsupp.curryLinearEquiv (MonoidAlgebra k H)).symm

/-- A vector of elements of `k[Q/H]`, written in the `k`-basis `Q/H`, indexed through the
bijection between `Q/H` and the right cosets. -/
def redCoords ι [H.Normal] :
    (ι →₀ MonoidAlgebra k (Q ⧸ H)) ≃ₗ[k] ((ι × RightCosets H) →₀ k) :=
  (Finsupp.mapRange.linearEquiv
      ((MonoidAlgebra.coeffLinearEquiv k).trans
        (Finsupp.domLCongr (R := k) (cosetQuotEquiv H).symm) :
        MonoidAlgebra k (Q ⧸ H) ≃ₗ[k] (RightCosets H →₀ k))).trans
    (Finsupp.curryLinearEquiv k).symm

variable {k H}

@[simp] theorem vecCoords_apply [IsMulCommutative H] {ι : Type*} u
    i c :
    vecCoords k H ι u (i, c) = (cosetBasis (k := k) (H := H)).repr (u i) c := by
  rfl

@[simp] theorem redCoords_apply [H.Normal] {ι : Type*} w
    i c :
    redCoords k H ι w (i, c) = (w i).coeff (cosetQuotEquiv H c) := by
  rfl

/-- **The commuting square.**  Reducing a vector over `k[Q]` to `k[Q/H]` is the same as
applying the augmentation `k[H] → k` to all its coordinates in the basis of coset
representatives. -/
theorem mapRange_augH_vecCoords [H.Normal] [IsMulCommutative H] {ι : Type*}
    u :
    Finsupp.mapRange (augH k H) (map_zero _) (vecCoords k H ι u) =
      redCoords k H ι (Finsupp.mapRange (quotRingHom k H) (map_zero _) u) := by
  ext ⟨i, c⟩
  by_cases hi : u i = 0
  · simp_all
  · simpa using augH_cosetBasis_repr _ c
