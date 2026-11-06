import Mathlib.Tactic

import Mathlib
import RequestProject.GroupRingReduction
import RequestProject.QuotientInjectivity
import RequestProject.TorsionFreeGroupRing

/-!
# Lemma 2.1: injectivity detected by the quotient `Q → Q/H`

This file proves Lemma 2.1 of the paper in the form in which it is used, with no
appeal to Strebel's theorem:

> Let `Q` be a group and `H ◁ Q` a torsion-free abelian normal subgroup, and let
> `f : k[Q]^{(ι)} → k[Q]^{(κ)}` be a map of free left `k[Q]`-modules of arbitrary
> rank, `k` any integral domain (in the paper `k = ℤ` and `k = 𝔽ₚ`).  If the
> reduction of `f` along `k[Q] → k[Q/H]` is injective, then `f` is injective.

The proof is the elementary one outlined in the paper.  Restricting scalars to
`R = k[H]`, which is a commutative domain
(`FiniteChains.monoidAlgebra_isDomain`), the modules stay free, with basis the
coset representatives (`FiniteChains.cosetBasis`), and reduction along
`k[Q] → k[Q/H]` becomes coefficientwise reduction along the augmentation
`k[H] → k` (`FiniteChains.mapRange_augH_vecCoords`).  In that form the statement
is the commutative-algebra core proved in
`RequestProject/QuotientInjectivity.lean`.
-/

set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 800000

open scoped IsMulCommutative

namespace FiniteChains

open MonoidAlgebra

variable (k : Type*) [CommRing k] {Q : Type*} [Group Q] (H : Subgroup Q)

/-- Coefficientwise reduction of a vector over `k[Q]` to a vector over `k[Q/H]`. -/
noncomputable def reduceVecQ [H.Normal] {ι : Type*} (u : ι →₀ MonoidAlgebra k Q)  :=
  Finsupp.mapRange (quotRingHom k H) (map_zero _) u

/-- The reduction along `k[Q] → k[Q/H]` of a map of free left `k[Q]`-modules: the map given
by the reduced matrix. -/
noncomputable def reduceLinQ [H.Normal] {ι κ : Type*}
    (f : (ι →₀ MonoidAlgebra k Q) →ₗ[MonoidAlgebra k Q] (κ →₀ MonoidAlgebra k Q)) :
    (ι →₀ MonoidAlgebra k (Q ⧸ H)) →ₗ[MonoidAlgebra k (Q ⧸ H)]
      (κ →₀ MonoidAlgebra k (Q ⧸ H)) :=
  Finsupp.linearCombination _ fun i => reduceVecQ k H (f (Finsupp.single i 1))

variable {k H}

@[simp] theorem reduceVecQ_apply [H.Normal] {ι : Type*} (u : ι →₀ MonoidAlgebra k Q) (i : ι) :
    reduceVecQ k H u i = quotRingHom k H (u i) := rfl

theorem reduceVecQ_smul [H.Normal] {ι : Type*} (x : MonoidAlgebra k Q)
    (u : ι →₀ MonoidAlgebra k Q) :
    reduceVecQ k H (x • u) = quotRingHom k H x • reduceVecQ k H u := by
  aesop

theorem reduceLinQ_single [H.Normal] {ι κ : Type*}
    (f : (ι →₀ MonoidAlgebra k Q) →ₗ[MonoidAlgebra k Q] (κ →₀ MonoidAlgebra k Q))
    (i : ι) (b : MonoidAlgebra k (Q ⧸ H)) :
    reduceLinQ k H f (Finsupp.single i b) = b • reduceVecQ k H (f (Finsupp.single i 1)) := by
  simp [reduceLinQ]

/-- The `k[H]`-scalar action on vectors over `k[Q]` is the action of the image in `k[Q]`. -/
theorem smul_vec_eq {ι : Type*} [IsMulCommutative H] (r : MonoidAlgebra k H)
    (u : ι →₀ MonoidAlgebra k Q) : r • u = groupRingIncl k H r • u := rfl

variable (H) in
/-- A map of free left `k[Q]`-modules, viewed as a map of `k[H]`-modules. -/
noncomputable def restrictToH [IsMulCommutative H] {ι κ : Type*}
    (f : (ι →₀ MonoidAlgebra k Q) →ₗ[MonoidAlgebra k Q] (κ →₀ MonoidAlgebra k Q)) :
    (ι →₀ MonoidAlgebra k Q) →ₗ[MonoidAlgebra k H] (κ →₀ MonoidAlgebra k Q) where
  toFun := f
  map_add' := f.map_add
  map_smul' r u := by
    simp_all [smul_vec_eq]

variable (H) in
@[simp] theorem restrictToH_apply [IsMulCommutative H] {ι κ : Type*}
    (f : (ι →₀ MonoidAlgebra k Q) →ₗ[MonoidAlgebra k Q] (κ →₀ MonoidAlgebra k Q))
    (u : ι →₀ MonoidAlgebra k Q) : restrictToH H f u = f u := rfl

theorem cosetQuotEquiv_cosetRep [H.Normal] (c : RightCosets H) :
    ((cosetRep H c : Q) : Q ⧸ H) = cosetQuotEquiv H c := by
  conv_rhs => rw [← Quotient.out_eq c]
  rfl

/-- The coordinates of a chosen coset representative: it is the corresponding basis vector. -/
theorem cosetBasis_repr_cosetRep [IsMulCommutative H] (c : RightCosets H) :
    (cosetBasis (k := k) (H := H)).repr (single (cosetRep H c) (1 : k)) =
      Finsupp.single c (1 : MonoidAlgebra k H) := by
  classical aesop (add simp [cosetBasis_repr_single, cosetRep])

theorem vecCoords_symm_single [IsMulCommutative H] {ι : Type*} (i : ι) (c : RightCosets H) :
    (vecCoords k H ι).symm (Finsupp.single (i, c) 1) =
      Finsupp.single i (single (cosetRep H c) (1 : k)) := by
  classical
  rw [LinearEquiv.symm_apply_eq]
  refine Finsupp.ext ?_
  rintro ⟨i', c'⟩
  rw [vecCoords_apply]
  by_cases hi : i' = i
  · simp_all [cosetBasis_repr_cosetRep, Finsupp.single_apply]
  · simp_all

theorem redCoords_symm_single [H.Normal] {ι : Type*} (i : ι) (c : RightCosets H) (a : k) :
    (redCoords k H ι).symm (Finsupp.single (i, c) a) =
      Finsupp.single i (single (cosetQuotEquiv H c) a) := by
  rw [LinearEquiv.symm_apply_eq]
  refine Finsupp.ext ?_
  rintro ⟨i', c'⟩
  rw [redCoords_apply]
  by_cases hi : i' = i
  · classical simp_all [Finsupp.single_apply]
  · simp_all

section

variable [IsDomain k] [H.Normal] [IsMulCommutative H] [IsMulTorsionFree H]

/-- **Lemma 2.1.**  For a torsion-free abelian normal subgroup `H ◁ Q` and an integral
domain `k`, a map of free left `k[Q]`-modules of arbitrary rank is injective as soon as its
reduction along `k[Q] → k[Q/H]` is. -/
theorem injective_of_reduceLinQ_injective {ι κ : Type*}
    (f : (ι →₀ MonoidAlgebra k Q) →ₗ[MonoidAlgebra k Q] (κ →₀ MonoidAlgebra k Q))
    (hred : Function.Injective (reduceLinQ k H f)) : Function.Injective f := by
  classical
  haveI  := monoidAlgebra_isDomain k H
  -- `f` written in the `k[H]`-basis of coset representatives
  set F : ((ι × RightCosets H) →₀ MonoidAlgebra k H) →ₗ[MonoidAlgebra k H]
      ((κ × RightCosets H) →₀ MonoidAlgebra k H) :=
    (vecCoords k H κ).toLinearMap ∘ₗ (restrictToH H f) ∘ₗ (vecCoords k H ι).symm.toLinearMap with hF
  -- the reduced map, in coordinates, is the reduction of `f` along `k[Q] → k[Q/H]`
  have hsquare : ∀ w, reduceMap (augH k H) F w =
      redCoords k H κ (reduceLinQ k H f ((redCoords k H ι).symm w)) := by
    intro w
    induction w using Finsupp.induction_linear with
    | zero => simp
    | add w₁ w₂ h₁ h₂ => simp [h₁, h₂]
    | single p a =>
        obtain ⟨i, c⟩ := p
        rw [reduceMap_single, hF]
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, vecCoords_symm_single,
          restrictToH_apply]
        have hsingle : (Finsupp.single i (single (cosetRep H c) (1 : k)) :
            ι →₀ MonoidAlgebra k Q) =
            (single (cosetRep H c) (1 : k) : MonoidAlgebra k Q) • Finsupp.single i 1 := by
          simp_all
        rw [hsingle, f.map_smul]
        -- pass to the reduced side
        rw [show (reduceVec (augH k H)
              (vecCoords k H κ ((single (cosetRep H c) (1 : k) : MonoidAlgebra k Q) •
                f (Finsupp.single i 1)))) =
            redCoords k H κ (reduceVecQ k H
              ((single (cosetRep H c) (1 : k) : MonoidAlgebra k Q) • f (Finsupp.single i 1)))
          from mapRange_augH_vecCoords (k := k) (H := H) _]
        rw [reduceVecQ_smul, quotRingHom_single, cosetQuotEquiv_cosetRep,
          redCoords_symm_single, reduceLinQ_single, ← map_smul (redCoords k H κ)]
        congr 1
        rw [← smul_assoc]
        congr 1
        simp
  have hFinj : Function.Injective (reduceMap (augH k H) F) := by
    have hfun  := funext hsquare
    rw [hfun]
    exact (redCoords k H κ).injective.comp (hred.comp (redCoords k H ι).symm.injective)
  have hFinj'  := injective_of_reduceMap_injective (augH k H) F hFinj
  aesop

end

end FiniteChains
