module

public import ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertSymbol
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteLocalFamily
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.OnePlaceNormKernel

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# The local--global norm-symbol bridge

This file isolates the exact quotient calculation used by the Hilbert-symbol
product formula.  The one-place embedding sends the chosen local norm group
directly into the ordinary idele-class norm group, so it descends without an
intermediate raw-idele quotient.  The resulting character identity gives the
finite-support and
principal-idèle product identities for every character of that target.
-/

open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain
open IdeleGroup RelativeIdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

theorem productFormulaIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] productFormulaIdeleClassGroupIsMulCommutative

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The one-place embedding, descended directly from the chosen local norm
quotient to the ordinary idele-class norm quotient. -/
noncomputable def finitePlaceNormQuotientToGlobalClass
    (v : HeightOneSpectrum (𝓞 K)) :
    ChosenFinitePlaceNormQuotient
      (K := K) (L := L) v →*
      IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range :=
  QuotientGroup.lift
    (chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v)
    ((globalNormClassFromIdele K L).comp
      (finitePlaceIdele v))
    (by
      intro x hx
      have hnorm :
          finitePlaceIdele v x ∈
            ideleNormSubgroup (K := K) (L := L) :=
        (finitePlaceIdele_mem_ideleNormSubgroup_iff_chosenLocalNorm
          (K := K) (L := L) v x).2 hx
      obtain ⟨z, hz⟩ := hnorm
      change
        QuotientGroup.mk'
          (_root_.ideleClassNorm K L).range
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K)
            (finitePlaceIdele v x)) = 1
      apply (QuotientGroup.eq_one_iff _).2
      refine
        ⟨QuotientGroup.mk'
            (IdeleGroup.principalSubgroup L)
            (relativeIdeleBaseChangeMulEquiv
              (K := K) (L := L) z), ?_⟩
      rw [_root_.ideleClassNorm_mk,
        IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv,
        hz])

/-- Exact local--global compatibility on representatives. -/
@[simp]
theorem finitePlaceNormQuotientToGlobalClass_localClass
    (v : HeightOneSpectrum (𝓞 K))
    (a : (v.adicCompletion K)ˣ) :
    finitePlaceNormQuotientToGlobalClass
        (K := K) (L := L) v
        (finitePlaceTensorNormClass
          (K := K) (L := L) v a) =
      globalNormClassFromIdele K L
        (finitePlaceIdele v a) := by
  rfl




























































































end Reciprocity
end GlobalClassFieldTheory

end
