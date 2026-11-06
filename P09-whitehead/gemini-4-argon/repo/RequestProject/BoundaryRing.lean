module

public import Mathlib
public import RequestProject.LemmaTwoOne

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains

open MonoidAlgebra

variable (k : Type*) [CommRing k] {G : Type*} [Group G] {I J : Type*}

noncomputable def redVecK (M : Subgroup G) [M.Normal] (v : J →₀ MonoidAlgebra k G) :
    J →₀ MonoidAlgebra k (G ⧸ M) :=
  Finsupp.mapRange (quotRingHom k M) (map_zero _) v

variable {k}

@[simp] theorem redVecK_apply (M : Subgroup G) [M.Normal] (v : J →₀ MonoidAlgebra k G) (j : J) :
    redVecK k M v j = quotRingHom k M (v j) := rfl

variable (k) in
noncomputable def boundaryColK (b : I → J → MonoidAlgebra k G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal] (j : J) :
    I →₀ MonoidAlgebra k (G ⧸ M) :=
  Finsupp.onFinset (hcol j).toFinset (fun i => quotRingHom k M (b i j)) fun i hi => by
    have hb : b i j ≠ 0 := fun h => hi (by rw [h, map_zero])
    simpa using hb

@[simp] theorem boundaryColK_apply (b : I → J → MonoidAlgebra k G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal] (j : J) (i : I) :
    boundaryColK k b hcol M j i = quotRingHom k M (b i j) := rfl

variable (k) in
noncomputable def boundaryMapK (b : I → J → MonoidAlgebra k G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal] :
    (J →₀ MonoidAlgebra k (G ⧸ M)) →ₗ[MonoidAlgebra k (G ⧸ M)]
      (I →₀ MonoidAlgebra k (G ⧸ M)) :=
  Finsupp.linearCombination _ (boundaryColK k b hcol M)

theorem boundaryMapK_apply_coord (b : I → J → MonoidAlgebra k G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal]
    (u : J →₀ MonoidAlgebra k (G ⧸ M)) (i : I) :
    boundaryMapK k b hcol M u i = ∑ j ∈ u.support, u j * quotRingHom k M (b i j) := by
  classical
  rw [boundaryMapK, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finset_sum_apply]
  exact Finset.sum_congr rfl fun _ _ => rfl

variable (k) in
noncomputable def foxBoundaryK (b : I → J → MonoidAlgebra k G)
    (v : J →₀ MonoidAlgebra k G) (i : I) : MonoidAlgebra k G :=
  ∑ j ∈ v.support, v j * b i j

theorem boundaryMapK_redVecK (b : I → J → MonoidAlgebra k G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal]
    (v : J →₀ MonoidAlgebra k G) (i : I) :
    boundaryMapK k b hcol M (redVecK k M v) i = quotRingHom k M (foxBoundaryK k b v i) := by
  classical
  rw [boundaryMapK_apply_coord, foxBoundaryK, map_sum,
    Finset.sum_congr rfl fun j (_ : j ∈ v.support) => map_mul (quotRingHom k M) (v j) (b i j)]
  refine Finset.sum_subset (fun j hj => by
    simp only [Finsupp.mem_support_iff, redVecK_apply] at hj ⊢
    exact fun h => hj (by rw [h, map_zero])) fun j _ hj => ?_
  simp only [Finsupp.mem_support_iff, not_not, redVecK_apply] at hj
  rw [redVecK_apply, hj, zero_mul]

theorem exists_liftK (M : Subgroup G) [M.Normal] (u : J →₀ MonoidAlgebra k (G ⧸ M)) :
    ∃ v : J →₀ MonoidAlgebra k G, redVecK k M v = u := by
  classical
  have hsurj : Function.Surjective (quotRingHom k M) := fun y =>
    let ⟨x, hx⟩ := Finsupp.mapDomain_surjective (M := k) (QuotientGroup.mk'_surjective M) y.coeff
    ⟨MonoidAlgebra.ofCoeff x, MonoidAlgebra.coeff_injective hx⟩
  choose lift hlift using hsurj
  refine ⟨Finsupp.mapRange (fun y => if y = 0 then 0 else lift y) (by simp) u,
    Finsupp.ext fun j => ?_⟩
  simp only [redVecK_apply, Finsupp.mapRange_apply]
  by_cases h : u j = 0 <;> simp [h, hlift]

theorem injective_boundaryMapK_of_injective [IsDomain k] (b : I → J → MonoidAlgebra k G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (C N : Subgroup G) [C.Normal] [N.Normal]
    (hCN : C ≤ N)
    [IsMulCommutative (N.map (QuotientGroup.mk' C))]
    [IsMulTorsionFree (N.map (QuotientGroup.mk' C))]
    (h : Function.Injective (boundaryMapK k b hcol N)) :
    Function.Injective (boundaryMapK k b hcol C) := by
  classical
  set H : Subgroup (G ⧸ C) := N.map (QuotientGroup.mk' C) with hH
  set e : ((G ⧸ C) ⧸ H) ≃* (G ⧸ N) := QuotientGroup.quotientQuotientEquivQuotient C N hCN with he
  set E : MonoidAlgebra k ((G ⧸ C) ⧸ H) →+* MonoidAlgebra k (G ⧸ N) :=
    MonoidAlgebra.mapDomainRingHom k e.toMonoidHom with hE
  have L1 (x : MonoidAlgebra k G) :
      E (quotRingHom k H (quotRingHom k C x)) = quotRingHom k N x :=
    congrArg (fun f : MonoidAlgebra k G →+* MonoidAlgebra k (G ⧸ N) => f x)
      (show (E.comp ((quotRingHom k H).comp (quotRingHom k C)) : MonoidAlgebra k G →+* _) =
          quotRingHom k N from
        MonoidAlgebra.ringHom_ext
          (fun r => by simp [hE, quotRingHom, MonoidAlgebra.mapDomainRingHom, Finsupp.mapDomain_single])
          (fun g => by simp [hE, quotRingHom, MonoidAlgebra.mapDomainRingHom, Finsupp.mapDomain_single, he]; rfl))
  have hEv : Function.Injective (Finsupp.mapRange (α := J) E (map_zero _)) :=
    Finsupp.mapRange_injective E (map_zero _) fun _ _ h =>
      MonoidAlgebra.coeff_injective (Finsupp.mapDomain_injective (M := k) e.injective
        (congrArg MonoidAlgebra.coeff h))
  have hsq : ∀ w : J →₀ MonoidAlgebra k ((G ⧸ C) ⧸ H),
      Finsupp.mapRange E (map_zero _) (reduceLinQ k H (boundaryMapK k b hcol C) w) =
        boundaryMapK k b hcol N (Finsupp.mapRange E (map_zero _) w) := by
    intro w; induction w using Finsupp.induction_linear with
    | zero => simp
    | add _ _ h₁ h₂ =>
        rw [map_add, Finsupp.mapRange_add (by simp) (f := E), h₁, h₂,
          Finsupp.mapRange_add (by simp) (f := E), map_add]
    | single j y =>
        rw [reduceLinQ_single, Finsupp.mapRange_single,
          show Finsupp.mapRange E (map_zero _)
              (y • reduceVecQ k H (boundaryMapK k b hcol C (Finsupp.single j 1))) =
            E y • boundaryColK k b hcol N j from
            Finsupp.ext fun i => by
              simp only [Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul, map_mul,
                reduceVecQ_apply, boundaryColK_apply]
              rw [boundaryMapK, Finsupp.linearCombination_single, one_smul, boundaryColK_apply, L1]]
        conv_rhs => rw [boundaryMapK, Finsupp.linearCombination_single]
  exact injective_of_reduceLinQ_injective (boundaryMapK k b hcol C) fun w z hwz =>
    hEv (h (by rw [← hsq w, ← hsq z, hwz]))

end FiniteChains
