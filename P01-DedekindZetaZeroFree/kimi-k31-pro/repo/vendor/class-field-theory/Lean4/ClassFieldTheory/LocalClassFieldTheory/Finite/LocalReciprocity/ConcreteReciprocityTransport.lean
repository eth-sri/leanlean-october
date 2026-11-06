module

public import Mathlib.FieldTheory.Galois.Basic
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main
public import ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/








set_option autoImplicit false

namespace LocalClassFieldTheory
open RamificationTheory KummerTheory CyclicCohomology

open LocalFieldTheory

open ClassFormation

/-!
# Finite local reciprocity: transport of abstract reciprocity to a field extension

This file contains the final comparison step in the proof of the local
reciprocity law.  Once the actual absolute-Galois datum, henselian valuation,
and class-field axiom have been constructed, the abstract reciprocity theorem is transported
through the concrete finite Galois realization in a separable closure and
through the actual field norm.

The coefficient module remains `(SeparableClosure K)ˣ`; this is essential in
imperfect positive characteristic.
-/

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

 abbrev concreteReciprocityAbsoluteGalois (K : Type) [Field K] :=
  intrinsicAbsoluteGalois K

 abbrev concreteReciprocityAbsoluteUnits (K : Type) [Field K] : Rep ℤ (concreteReciprocityAbsoluteGalois K) :=
  intrinsicAbsoluteUnits K

 abbrev concreteReciprocityAbstractBase (K : Type) [Field K] : ClosedSubgroup (concreteReciprocityAbsoluteGalois K) :=
  intrinsicAbstractBase K

 noncomputable instance intrinsicAbsoluteGaloisT2 : T2Space (concreteReciprocityAbsoluteGalois K) :=
  krullTopology_t2

/-! ## Transport relative to an explicit embedding -/

/-- The finite abstract extension object determined by an explicit
embedding of `L` into the fixed separable closure. -/
def finiteGaloisAbstractExtensionOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) : FiniteGaloisSubextension (concreteReciprocityAbstractBase K) where
  field := finiteGaloisClosedFixingSubgroupOfEmbedding K L i
  below := fixingSubgroupLeBase K (SeparableClosure K)
    (finiteGaloisFieldRangeOfEmbedding K L i)
  normal := inferInstance
  finite := baseFixingExtensionQuotient_finite K (SeparableClosure K)
    (finiteGaloisFieldRangeOfEmbedding K L i)



/-- The additive reciprocity equivalence transported through an explicit
realization of `L/K` in the separable closure. -/
def concreteReciprocityAddEquivOfEmbedding
    (i : L →ₐ[K] SeparableClosure K)
    (D : DegreeData (concreteReciprocityAbsoluteGalois K)) (v : ValuationData D (concreteReciprocityAbsoluteUnits K))
    (hcf : SatisfiesClassFieldAxiom (concreteReciprocityAbsoluteUnits K)) :
    Additive (Abelianization Gal(L / K)) ≃+
      Additive (NormQuotient K L) :=
  (MulEquiv.toAdditive
      ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i).abelianizationCongr.symm)).trans
    ((D.abstractReciprocityEquiv (concreteReciprocityAbsoluteUnits K) v hcf (intrinsicFiniteAbstractBase K)
      (finiteGaloisAbstractExtensionOfEmbedding K L i)).trans
        (finiteNormQuotientEquivEmbeddedNormQuotient
          K (SeparableClosure K) L i))

/-- Multiplicative form of reciprocity transported through an explicit
embedding. -/
def concreteReciprocityEquivOfEmbedding
    (i : L →ₐ[K] SeparableClosure K)
    (D : DegreeData (concreteReciprocityAbsoluteGalois K)) (v : ValuationData D (concreteReciprocityAbsoluteUnits K))
    (hcf : SatisfiesClassFieldAxiom (concreteReciprocityAbsoluteUnits K)) :
    Abelianization Gal(L / K) ≃* NormQuotient K L := by
  let e : Additive (Abelianization Gal(L / K)) ≃+
      Additive (NormQuotient K L) :=
    concreteReciprocityAddEquivOfEmbedding K L i D v hcf
  let em : Multiplicative (Additive (Abelianization Gal(L / K))) ≃*
      Multiplicative (Additive (NormQuotient K L)) :=
    @AddEquiv.toMultiplicative
      (Additive (Abelianization Gal(L / K)))
      (Additive (NormQuotient K L)) inferInstance inferInstance e
  exact (MulEquiv.multiplicativeAdditive
      (Abelianization Gal(L / K))).symm.trans
    (em.trans
        (MulEquiv.multiplicativeAdditive (NormQuotient K L)))

/-- Norm-residue symbol obtained from an explicit separable-closure
realization. -/
def concreteNormResidueSymbolOfEmbedding
    (i : L →ₐ[K] SeparableClosure K)
    (D : DegreeData (concreteReciprocityAbsoluteGalois K)) (v : ValuationData D (concreteReciprocityAbsoluteUnits K))
    (hcf : SatisfiesClassFieldAxiom (concreteReciprocityAbsoluteUnits K)) :
    Kˣ →* Abelianization Gal(L / K) :=
  (concreteReciprocityEquivOfEmbedding K L i D v hcf).symm.toMonoidHom.comp
    (normClass K L)



/-- The public multiplicative form of the transported reciprocity
isomorphism `G(L/K)ᵃᵇ ≃ Kˣ/N_{L/K}Lˣ`. -/
def concreteReciprocityEquiv
    (D : DegreeData (concreteReciprocityAbsoluteGalois K)) (v : ValuationData D (concreteReciprocityAbsoluteUnits K))
    (hcf : SatisfiesClassFieldAxiom (concreteReciprocityAbsoluteUnits K)) :
    Abelianization Gal(L / K) ≃* NormQuotient K L :=
  concreteReciprocityEquivOfEmbedding K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L) D v hcf







end
end LocalClassFieldTheory
