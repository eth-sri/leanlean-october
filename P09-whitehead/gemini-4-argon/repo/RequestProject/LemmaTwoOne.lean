module

public import Mathlib
public import RequestProject.GroupRingReduction
public import RequestProject.QuotientInjectivity
public import RequestProject.TorsionFreeGroupRing

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open scoped IsMulCommutative

namespace FiniteChains

open MonoidAlgebra

variable (k : Type*) [CommRing k] {Q : Type*} [Group Q] (H : Subgroup Q)

noncomputable def reduceVecQ [H.Normal] {ι : Type*} (u : ι →₀ MonoidAlgebra k Q) :
    ι →₀ MonoidAlgebra k (Q ⧸ H) :=
  Finsupp.mapRange (quotRingHom k H) (map_zero _) u

noncomputable def reduceLinQ [H.Normal] {ι κ : Type*}
    (f : (ι →₀ MonoidAlgebra k Q) →ₗ[MonoidAlgebra k Q] (κ →₀ MonoidAlgebra k Q)) :
    (ι →₀ MonoidAlgebra k (Q ⧸ H)) →ₗ[MonoidAlgebra k (Q ⧸ H)]
      (κ →₀ MonoidAlgebra k (Q ⧸ H)) :=
  Finsupp.linearCombination _ fun i => reduceVecQ k H (f (Finsupp.single i 1))

variable {k H}

@[simp] theorem reduceVecQ_apply [H.Normal] {ι : Type*} (u : ι →₀ MonoidAlgebra k Q) (i : ι) :
    reduceVecQ k H u i = quotRingHom k H (u i) := rfl

theorem reduceLinQ_single [H.Normal] {ι κ : Type*}
    (f : (ι →₀ MonoidAlgebra k Q) →ₗ[MonoidAlgebra k Q] (κ →₀ MonoidAlgebra k Q))
    (i : ι) (b : MonoidAlgebra k (Q ⧸ H)) :
    reduceLinQ k H f (Finsupp.single i b) = b • reduceVecQ k H (f (Finsupp.single i 1)) := by
  simp [reduceLinQ]

variable (H) in
noncomputable def restrictToH [IsMulCommutative H] {ι κ : Type*}
    (f : (ι →₀ MonoidAlgebra k Q) →ₗ[MonoidAlgebra k Q] (κ →₀ MonoidAlgebra k Q)) :
    (ι →₀ MonoidAlgebra k Q) →ₗ[MonoidAlgebra k H] (κ →₀ MonoidAlgebra k Q) where
  toFun := f
  map_add' := f.map_add
  map_smul' r u := by
    change f (groupRingIncl k H r • u) = groupRingIncl k H r • f u
    exact f.map_smul _ u

theorem vecCoords_symm_single [IsMulCommutative H] {ι : Type*} (i : ι) (c : RightCosets H) :
    (vecCoords k H ι).symm (Finsupp.single (i, c) 1) =
      Finsupp.single i (single (cosetRep H c) (1 : k)) := by
  classical
  rw [LinearEquiv.symm_apply_eq]
  refine Finsupp.ext fun ⟨i', c'⟩ => ?_
  rw [vecCoords_apply]
  by_cases hi : i' = i
  · subst hi
    have hrepr : (cosetBasis (k := k) (H := H)).repr (single (cosetRep H c) (1 : k)) =
        Finsupp.single c (1 : MonoidAlgebra k H) := by
      rw [cosetBasis_repr_single (k := k) (H := H)]
      have hc : Quotient.mk (QuotientGroup.rightRel H) (cosetRep H c) = c := Quotient.out_eq c
      simp only [hc]
      congr 1
      rw [show (⟨cosetRep H c * (cosetRep H c)⁻¹, by simp⟩ : H) = 1 from Subtype.ext (by simp)]; rfl
    rw [Finsupp.single_eq_same, hrepr, Finsupp.single_apply, Finsupp.single_apply]
    simp [Prod.ext_iff]
  · rw [show (Finsupp.single i (single (cosetRep H c) (1 : k)) : ι →₀ MonoidAlgebra k Q) i' = 0 from
      Finsupp.single_eq_of_ne hi, map_zero, Finsupp.coe_zero, Pi.zero_apply, Finsupp.single_apply,
      if_neg (fun hcon => hi (congrArg Prod.fst hcon).symm)]

theorem redCoords_symm_single [H.Normal] {ι : Type*} (i : ι) (c : RightCosets H) (a : k) :
    (redCoords k H ι).symm (Finsupp.single (i, c) a) =
      Finsupp.single i (single (cosetQuotEquiv H c) a) := by
  classical
  rw [LinearEquiv.symm_apply_eq]
  refine Finsupp.ext fun ⟨i', c'⟩ => ?_
  rw [redCoords_apply]
  by_cases hi : i' = i
  · subst hi
    rw [Finsupp.single_eq_same, MonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.single_apply]
    simp [Prod.ext_iff, (cosetQuotEquiv H).injective.eq_iff]
  · rw [show (Finsupp.single i (single (cosetQuotEquiv H c) a) :
        ι →₀ MonoidAlgebra k (Q ⧸ H)) i' = 0 from Finsupp.single_eq_of_ne hi,
      Finsupp.single_apply, if_neg (fun hcon => hi (congrArg Prod.fst hcon).symm)]; rfl

variable [IsDomain k] [H.Normal] [IsMulCommutative H] [IsMulTorsionFree H]

theorem injective_of_reduceLinQ_injective {ι κ : Type*}
    (f : (ι →₀ MonoidAlgebra k Q) →ₗ[MonoidAlgebra k Q] (κ →₀ MonoidAlgebra k Q))
    (hred : Function.Injective (reduceLinQ k H f)) : Function.Injective f := by
  classical
  haveI : IsDomain (MonoidAlgebra k H) := monoidAlgebra_isDomain k H
  set F : ((ι × RightCosets H) →₀ MonoidAlgebra k H) →ₗ[MonoidAlgebra k H]
      ((κ × RightCosets H) →₀ MonoidAlgebra k H) :=
    (vecCoords k H κ).toLinearMap ∘ₗ (restrictToH H f) ∘ₗ (vecCoords k H ι).symm.toLinearMap with hF
  have hsquare : ∀ w, reduceMap (augH k H) F w =
      redCoords k H κ (reduceLinQ k H f ((redCoords k H ι).symm w)) := by
    intro w; induction w using Finsupp.induction_linear with
    | zero => simp
    | add _ _ h₁ h₂ => simp [h₁, h₂]
    | single p a =>
        obtain ⟨i, c⟩ := p
        rw [reduceMap_single, hF]
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, vecCoords_symm_single, restrictToH,
          LinearMap.coe_mk, AddHom.coe_mk]
        rw [show (Finsupp.single i (single (cosetRep H c) (1 : k)) : ι →₀ MonoidAlgebra k Q) =
            (single (cosetRep H c) (1 : k) : MonoidAlgebra k Q) • Finsupp.single i 1 by
          ext j; by_cases hj : j = i <;> simp [hj, Finsupp.single_apply], f.map_smul,
          show reduceVec (augH k H) (vecCoords k H κ
              ((single (cosetRep H c) (1 : k) : MonoidAlgebra k Q) • f (Finsupp.single i 1))) =
            redCoords k H κ (reduceVecQ k H
              ((single (cosetRep H c) (1 : k) : MonoidAlgebra k Q) • f (Finsupp.single i 1)))
          from mapRange_augH_vecCoords (k := k) (H := H) _,
          show ∀ (x : MonoidAlgebra k Q) (u : κ →₀ MonoidAlgebra k Q),
            reduceVecQ k H (x • u) = quotRingHom k H x • reduceVecQ k H u from
            fun _ _ => by ext i; simp [reduceVecQ, Finsupp.smul_apply, smul_eq_mul],
          quotRingHom_single, show ((cosetRep H c : Q) : Q ⧸ H) = cosetQuotEquiv H c by
            (conv_rhs => rw [← Quotient.out_eq c]); rfl,
          redCoords_symm_single, reduceLinQ_single, ← map_smul (redCoords k H κ)]
        congr 1; rw [← smul_assoc]; congr 1; simp
  have hFinj' : Function.Injective F := injective_of_reduceMap_injective (augH k H) F <| by
    rw [show (reduceMap (augH k H) F : _ → _) =
      (redCoords k H κ) ∘ (reduceLinQ k H f) ∘ (redCoords k H ι).symm from funext hsquare]
    exact (redCoords k H κ).injective.comp (hred.comp (redCoords k H ι).symm.injective)
  intro u v huv
  exact (vecCoords k H ι).injective <| hFinj' <| by
    simp only [hF, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      restrictToH, LinearMap.coe_mk, AddHom.coe_mk, huv]

end FiniteChains
