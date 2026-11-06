module

public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.ArithmeticIdealDecompositionLaw

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Ideal norms and arithmetic Artin exactness

For a finite abelian extension `L / K` and a defining modulus `m`, the
genuine ideal group

`N_{L/K} J_L^m P_K^m`

is `RayClass.idealNormSubgroup`.  This module identifies it with the
kernel of the arithmetic ideal Artin map, descends that map to the
corresponding quotient, and states the unramified decomposition law
entirely in terms of this norm-defined ideal group.
-/

open scoped NumberField Classical IsMulCommutative

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open NumberField IsDedekindDomain

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

attribute [local instance]
  ideleClassSubgroupNormal idealArtinKernelNormal

/-- The kernel of the arithmetic, Galois-valued ideal Artin map is the
genuine norm-defined ideal group `N_{L/K} J_L^m P_K^m`. -/
theorem arithmeticIdealArtinGaloisMap_ker_eq_idealNormSubgroup
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    (arithmeticIdealArtinGaloisMap
        (K := K) (L := L) m hm).ker =
      RayClass.idealNormSubgroup
        (K := K) (L := L) m := by
  rw [arithmeticIdealArtinGaloisMap_ker,
    idealArtinKernel_eq_idealNormSubgroup]





/-- The vertical isomorphism in the ideal/idèle Artin diagram:

`J_K^m / (N_{L/K} J_L^{m_L} P_K^m) ≃ C_K / N_{L/K} C_L`.

It is the first-isomorphism-theorem comparison for the ideal Artin
map, transported across the equality between its kernel and the
genuine norm-defined ideal group. -/
noncomputable def idealNormQuotientEquivIdeleClassNormQuotient
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    RayClass.primeToModulusIdeals m ⧸
        RayClass.idealNormSubgroup
          (K := K) (L := L) m ≃*
      IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range :=
  (QuotientGroup.quotientMulEquivOfEq
      (idealArtinKernel_eq_idealNormSubgroup
        (K := K) (L := L) m hm).symm).trans
    (idealClassQuotientEquivNormQuotient m
      ((_root_.ideleClassNorm K L).range) hm)

omit [IsAbelianGalois K L] in
/-- The ideal-norm quotient comparison sends an ideal representative to its
class in the idèle-class norm quotient. -/
@[simp]
theorem idealNormQuotientEquivIdeleClassNormQuotient_mk
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (a : RayClass.primeToModulusIdeals m) :
    idealNormQuotientEquivIdeleClassNormQuotient
        (K := K) (L := L) m hm
        (QuotientGroup.mk'
          (RayClass.idealNormSubgroup
            (K := K) (L := L) m) a) =
      idealArtinMap m
        ((_root_.ideleClassNorm K L).range) hm a := by
  let h :=
    (idealArtinKernel_eq_idealNormSubgroup
      (K := K) (L := L) m hm).symm
  change
    idealClassQuotientEquivNormQuotient m
        ((_root_.ideleClassNorm K L).range) hm
        (QuotientGroup.quotientMulEquivOfEq h
          (QuotientGroup.mk'
            (RayClass.idealNormSubgroup
              (K := K) (L := L) m) a)) =
      idealArtinMap m
        ((_root_.ideleClassNorm K L).range) hm a
  calc
    _ = idealClassQuotientEquivNormQuotient m
          ((_root_.ideleClassNorm K L).range) hm
          (QuotientGroup.mk'
            (idealArtinKernel m
              ((_root_.ideleClassNorm K L).range) hm) a) :=
      congrArg
        (idealClassQuotientEquivNormQuotient m
          ((_root_.ideleClassNorm K L).range) hm)
        (QuotientGroup.quotientMulEquivOfEq_mk h a)
    _ = idealArtinMap m
          ((_root_.ideleClassNorm K L).range) hm a :=
      idealClassQuotientEquivNormQuotient_mk m
        ((_root_.ideleClassNorm K L).range) hm a

/-- The arithmetic ideal Artin map descended through the concrete
norm-defined ideal group. -/
noncomputable def arithmeticIdealNormQuotientArtinMap
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    RayClass.primeToModulusIdeals m ⧸
        RayClass.idealNormSubgroup
          (K := K) (L := L) m →*
      (L ≃ₐ[K] L) :=
  QuotientGroup.lift
    (RayClass.idealNormSubgroup
      (K := K) (L := L) m)
    (arithmeticIdealArtinGaloisMap
      (K := K) (L := L) m hm)
    (by
      intro a ha
      rw [arithmeticIdealArtinGaloisMap_ker_eq_idealNormSubgroup]
      exact ha)

/-- The descended arithmetic ideal Artin map evaluates on quotient
representatives as the original arithmetic ideal Artin map. -/
@[simp]
theorem arithmeticIdealNormQuotientArtinMap_mk
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (a : RayClass.primeToModulusIdeals m) :
    arithmeticIdealNormQuotientArtinMap
        (K := K) (L := L) m hm
        (QuotientGroup.mk'
          (RayClass.idealNormSubgroup
            (K := K) (L := L) m) a) =
      arithmeticIdealArtinGaloisMap
        (K := K) (L := L) m hm a :=
  QuotientGroup.lift_mk _ _ _

/-- The arithmetic ideal Artin map on the concrete norm quotient is
injective. -/
theorem arithmeticIdealNormQuotientArtinMap_injective
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    Function.Injective
      (arithmeticIdealNormQuotientArtinMap
        (K := K) (L := L) m hm) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (RayClass.idealNormSubgroup
        (K := K) (L := L) m) x
  obtain ⟨b, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (RayClass.idealNormSubgroup
        (K := K) (L := L) m) y
  rw [arithmeticIdealNormQuotientArtinMap_mk,
    arithmeticIdealNormQuotientArtinMap_mk] at hxy
  apply
    (QuotientGroup.eq_iff_div_mem
      (N := RayClass.idealNormSubgroup
        (K := K) (L := L) m)
      (x := a) (y := b)).2
  rw [← arithmeticIdealArtinGaloisMap_ker_eq_idealNormSubgroup]
  change
    arithmeticIdealArtinGaloisMap
        (K := K) (L := L) m hm (a / b) =
      1
  rw [map_div, hxy]
  exact div_self' _

/-- The arithmetic ideal Artin map on the concrete norm quotient is
surjective. -/
theorem arithmeticIdealNormQuotientArtinMap_surjective
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    Function.Surjective
      (arithmeticIdealNormQuotientArtinMap
        (K := K) (L := L) m hm) := by
  intro σ
  obtain ⟨a, ha⟩ :=
    arithmeticIdealArtinGaloisMap_surjective
      (K := K) (L := L) m hm σ
  refine
    ⟨QuotientGroup.mk'
        (RayClass.idealNormSubgroup
          (K := K) (L := L) m) a, ?_⟩
  rw [arithmeticIdealNormQuotientArtinMap_mk]
  exact ha



/-- The canonical arithmetic ideal class-field isomorphism

`J_K^m / (N_{L/K} J_L^m P_K^m) ≃ Gal(L/K)`.

Both the source subgroup and the target Galois group are the concrete
objects occurring in the extension `L / K`. -/
noncomputable def arithmeticIdealNormQuotientEquivGaloisGroup
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    RayClass.primeToModulusIdeals m ⧸
        RayClass.idealNormSubgroup
          (K := K) (L := L) m ≃*
      (L ≃ₐ[K] L) :=
  MulEquiv.ofBijective
    (arithmeticIdealNormQuotientArtinMap
      (K := K) (L := L) m hm)
    ⟨arithmeticIdealNormQuotientArtinMap_injective m hm,
      arithmeticIdealNormQuotientArtinMap_surjective m hm⟩

/-- The arithmetic ideal norm-quotient equivalence sends a quotient
representative to its arithmetic ideal Artin symbol. -/
@[simp]
theorem arithmeticIdealNormQuotientEquivGaloisGroup_mk
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (a : RayClass.primeToModulusIdeals m) :
    arithmeticIdealNormQuotientEquivGaloisGroup
        (K := K) (L := L) m hm
        (QuotientGroup.mk'
          (RayClass.idealNormSubgroup
            (K := K) (L := L) m) a) =
      arithmeticIdealArtinGaloisMap
        (K := K) (L := L) m hm a :=
  arithmeticIdealNormQuotientArtinMap_mk m hm a











end IdealClassFieldTheory
end GlobalClassFieldTheory

namespace ClassFieldTheory

open NumberField IsDedekindDomain

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]





end ClassFieldTheory

end
