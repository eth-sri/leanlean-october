module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Algebraic.Construction
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Algebraic.Evaluation

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Norm-residue evaluation for a closed finite-index class field

This leaf proves that the selected class-field reciprocity equivalence sends
the global norm-residue symbol to the corresponding quotient class.
-/

open scoped Classical IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity

/-- Canonical class-group commutativity supplies normality for quotient evaluation. -/
alias closedFiniteIndexNormResidueClassGroupIsMulCommutative := GlobalClassFieldTheory.Reciprocity.realizedTowerIdeleClassIsMulCommutative

attribute [local instance] closedFiniteIndexNormResidueClassGroupIsMulCommutative

variable {K : Type} [Field K] [NumberField K]

private theorem quotientTransport_inverse_apply
    {G A : Type*} [Group G] [Group A]
    (N H : Subgroup G) [N.Normal] [H.Normal]
    (e : Additive (G ⧸ N) ≃+ Additive A)
    (h : N = H) (c : G) :
    QuotientGroup.quotientMulEquivOfEq h
        (Additive.toMul
          (e.symm
            (e (Additive.ofMul (QuotientGroup.mk' N c))))) =
      QuotientGroup.mk' H c := by
  calc
    _ = QuotientGroup.quotientMulEquivOfEq h
          (Additive.toMul
            (Additive.ofMul (QuotientGroup.mk' N c))) :=
      congrArg
        (fun z => QuotientGroup.quotientMulEquivOfEq h
          (Additive.toMul z))
        (e.symm_apply_apply _)
    _ = QuotientGroup.mk' H c :=
      QuotientGroup.quotientMulEquivOfEq_mk h c

/-- Under the direct class-field reciprocity equivalence, the global
norm-residue symbol of an idèle class is its quotient class modulo
`H`. -/
@[simp]
theorem
    closedFiniteIndexClassFieldGaloisEquivNormQuotient_globalNormResidue
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (c : IdeleClassGroup K) :
    closedFiniteIndexClassFieldGaloisEquivNormQuotient
        (K := K) H hclosed
        (globalNormResidueMonoidHom K
          (closedFiniteIndexClassField
            (K := K) H hclosed) c) =
      QuotientGroup.mk' H c := by
  have hNormResidue :=
    congrArg (fun σ => Additive.ofMul σ)
      (globalNormResidueMonoidHom_apply K
        (closedFiniteIndexClassField
           H hclosed) c)
  let globalNormResidueEquiv₀ := globalNormResidueEquiv K (closedFiniteIndexClassField H hclosed)
  calc
    _ = QuotientGroup.quotientMulEquivOfEq
          (closedFiniteIndexClassField_ideleClassNorm_range
             H hclosed)
          (Additive.toMul
            ((globalNormResidueEquiv₀).symm
              (Additive.ofMul
                (globalNormResidueMonoidHom K
                  (closedFiniteIndexClassField
                     H hclosed) c)))) :=
      closedFiniteIndexClassFieldGaloisEquivNormQuotient_apply
         H hclosed _
    _ = QuotientGroup.quotientMulEquivOfEq
          (closedFiniteIndexClassField_ideleClassNorm_range
             H hclosed)
          (Additive.toMul
            ((globalNormResidueEquiv₀).symm
              (globalNormResidueEquiv₀
                (Additive.ofMul
                  (QuotientGroup.mk'
                    (_root_.ideleClassNorm K
                      (closedFiniteIndexClassField
                         H hclosed)).range c))))) :=
      congrArg
        (fun τ =>
          QuotientGroup.quotientMulEquivOfEq
              (closedFiniteIndexClassField_ideleClassNorm_range
                 H hclosed)
            (Additive.toMul
              ((globalNormResidueEquiv₀).symm τ)))
        hNormResidue
    _ = QuotientGroup.mk' H c :=
      quotientTransport_inverse_apply
      ((_root_.ideleClassNorm K
        (closedFiniteIndexClassField
           H hclosed)).range)
      H
      (globalNormResidueEquiv₀)
      (closedFiniteIndexClassField_ideleClassNorm_range
         H hclosed)
      c

end GlobalClassFields
end GlobalClassFieldTheory

end
