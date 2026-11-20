module


public import RequestProject.GroupRingFree

@[expose] public section

/-!
# Reduction of group-ring coefficients along `Q → Q/H`

This file contains the dictionary that turns the reduction of a matrix over
`k[Q]` along `k[Q] → k[Q/H]` into the coefficientwise reduction, along the
augmentation `k[H] → k`, of the same matrix written over the commutative ring
`k[H]` in the basis of coset representatives.
-/

noncomputable section

namespace FiniteChains

open MonoidAlgebra

variable (k : Type*) [CommRing k] {Q : Type*} [Group Q] (H : Subgroup Q)

/-- The augmentation `k[H] → k`. -/
def augH [IsMulCommutative H] :=
  (MonoidAlgebra.lift k k H 1).toRingHom

/-- The reduction map of group rings `k[Q] → k[Q/H]`. -/
def quotRingHom [H.Normal] :=
  MonoidAlgebra.mapDomainRingHom k (QuotientGroup.mk' H)

variable {k H}

@[simp] theorem augH_single [IsMulCommutative H] (h : H) (a : k) :
    augH k H (single h a) = a := by
  simp [augH]

section

variable [H.Normal]

@[simp] theorem quotRingHom_single (q : Q) (a : k) :
    quotRingHom k H (single q a) = single (q : Q ⧸ H) a := MonoidAlgebra.mapDomain_single

variable (H) in
/-- For a normal subgroup the right cosets are the elements of the quotient group. -/
def cosetQuotEquiv : RightCosets H ≃ Q ⧸ H where
  toFun := Quotient.map' id (by
    intro a b h
    rw [QuotientGroup.rightRel_apply] at h
    rw [QuotientGroup.leftRel_apply]
    have := (Subgroup.Normal.conj_mem (inferInstance) _ h a⁻¹)
    have e : a⁻¹ * (b * a⁻¹) * a⁻¹⁻¹ = a⁻¹ * b := by group
    simp_all)
  invFun := Quotient.map' id (by
    intro a b h
    rw [QuotientGroup.leftRel_apply] at h
    rw [QuotientGroup.rightRel_apply]
    have := (Subgroup.Normal.conj_mem (inferInstance) _ h a)
    simp_all)
  left_inv := by rintro ⟨q⟩; rfl
  right_inv := by rintro ⟨q⟩; rfl

@[simp] theorem cosetQuotEquiv_mk (q : Q) :
    cosetQuotEquiv H (Quotient.mk (QuotientGroup.rightRel H) q) = q := rfl

end

section

variable [IsMulCommutative H]

/-- The coordinates of an element of `k[Q]` in the `k[H]`-basis of coset representatives. -/
theorem cosetBasis_repr_cosetCombination
    (F : RightCosets H →₀ MonoidAlgebra k H) :
    (cosetBasis (k := k) (H := H)).repr (cosetCombination F) = F := by
  simp [cosetBasis, cosetCombination]

variable (q : Q) (a : k)

theorem cosetCombination_single_single :
    cosetCombination (Finsupp.single (Quotient.mk (QuotientGroup.rightRel H) q)
      (single (⟨q * (cosetRep H (Quotient.mk (QuotientGroup.rightRel H) q))⁻¹,
        mul_cosetRep_inv_mem q⟩) a)) = (single q a) := by
  simp [cosetCombination, Finsupp.linearCombination_single, smul_def', groupRingIncl_single, MonoidAlgebra.single_mul_single]

theorem cosetBasis_repr_single :
    (cosetBasis (k := k) (H := H)).repr (single q a) =
      Finsupp.single (Quotient.mk _ q)
        (single (⟨q * (cosetRep H (Quotient.mk (QuotientGroup.rightRel H) q))⁻¹,
          mul_cosetRep_inv_mem q⟩) a) := by
  rw [← cosetCombination_single_single (H := H) q a, cosetBasis_repr_cosetCombination]

end

section

variable [H.Normal] [IsMulCommutative H]

/-- The key compatibility, on the generators `single q a` of `k[Q]`. -/
theorem augH_cosetBasis_repr_single (q : Q) (a : k)
    (c : RightCosets H) :
    augH k H ((cosetBasis (k := k) (H := H)).repr (single q a) c) =
      (quotRingHom k H (single q a)).coeff (cosetQuotEquiv H c) := by
  classical
  rw [cosetBasis_repr_single (H := H) q a, quotRingHom_single (H := H) q a]
  by_cases hc : c = Quotient.mk _ q
  · simp_all
  · rw [Finsupp.single_apply, if_neg (fun h => hc h.symm), map_zero, MonoidAlgebra.coeff_single, Finsupp.single_apply,
      if_neg]
    intro h
    exact hc ((cosetQuotEquiv H).injective (by simp_all))

/-- **The key compatibility.**  Reducing an element of `k[Q]` to `k[Q/H]` amounts to
applying the augmentation `k[H] → k` to each of its coordinates in the basis of coset
representatives. -/
theorem augH_cosetBasis_repr (x : MonoidAlgebra k Q)
    (c : RightCosets H) :
    augH k H ((cosetBasis (k := k) (H := H)).repr x c) = (quotRingHom k H x).coeff (cosetQuotEquiv H c) := by
  classical
  -- both sides are additive in `x`, so it suffices to treat `x = single q a`
  set L : MonoidAlgebra k Q →+ k :=
    (augH k H).toAddMonoidHom.comp
      ((Finsupp.applyAddHom c).comp
        ((cosetBasis (k := k) (H := H)).repr.toLinearMap.toAddMonoidHom)) with hL
  set M : MonoidAlgebra k Q →+ k :=
    (Finsupp.applyAddHom (cosetQuotEquiv H c)).comp
      ((MonoidAlgebra.coeffAddEquiv).toAddMonoidHom.comp (quotRingHom k H).toAddMonoidHom) with hM
  have hLM : L = M := by
    refine MonoidAlgebra.addMonoidHom_ext ?_
    simp_all [augH_cosetBasis_repr_single]
  have := congrArg (fun g : MonoidAlgebra k Q →+ k => g x) hLM
  assumption

end

variable (k H)

/-- A vector of elements of `k[Q]`, written in the `k[H]`-basis of coset representatives:
this exhibits `k[Q]^{(ι)}` as a free `k[H]`-module on `ι × (H \ Q)`. -/
def vecCoords (ι : Type*) [IsMulCommutative H] :
    (ι →₀ MonoidAlgebra k Q) ≃ₗ[MonoidAlgebra k H]
      ((ι × RightCosets H) →₀ MonoidAlgebra k H) :=
  (Finsupp.mapRange.linearEquiv (cosetBasis (k := k) (H := H)).repr).trans
    (Finsupp.curryLinearEquiv (MonoidAlgebra k H)).symm

/-- A vector of elements of `k[Q/H]`, written in the `k`-basis `Q/H`, indexed through the
bijection between `Q/H` and the right cosets. -/
def redCoords (ι : Type*) [H.Normal] :
    (ι →₀ MonoidAlgebra k (Q ⧸ H)) ≃ₗ[k] ((ι × RightCosets H) →₀ k) :=
  (Finsupp.mapRange.linearEquiv
      ((MonoidAlgebra.coeffLinearEquiv k).trans
        (Finsupp.domLCongr (cosetQuotEquiv H).symm))).trans
    (Finsupp.curryLinearEquiv k).symm

variable {k H}

@[simp] theorem vecCoords_apply [IsMulCommutative H] {ι : Type*} (u : ι →₀ MonoidAlgebra k Q)
    (i : ι) (c : RightCosets H) :
    vecCoords k H ι u (i, c) = (cosetBasis (k := k) (H := H)).repr (u i) c := rfl

variable [H.Normal]

@[simp] theorem redCoords_apply {ι : Type*} (w : ι →₀ MonoidAlgebra k (Q ⧸ H))
    (i : ι) (c : RightCosets H) :
    redCoords k H ι w (i, c) = (w i).coeff (cosetQuotEquiv H c) := rfl

/-- **The commuting square.**  Reducing a vector over `k[Q]` to `k[Q/H]` is the same as
applying the augmentation `k[H] → k` to all its coordinates in the basis of coset
representatives. -/
theorem mapRange_augH_vecCoords [IsMulCommutative H] {ι : Type*}
    (u : ι →₀ MonoidAlgebra k Q) :
    Finsupp.mapRange (augH k H) (map_zero _) (vecCoords k H ι u) =
      redCoords k H ι (Finsupp.mapRange (quotRingHom k H) (map_zero _) u) := by
  ext ⟨i, c⟩
  simp_all [augH_cosetBasis_repr]

end FiniteChains
