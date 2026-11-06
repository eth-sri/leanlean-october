module

public import ValuedFieldTheory.Valuation.UniqueRing
public import Mathlib.RingTheory.Polynomial.GaussLemma

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# reduction of irreducible factors

This file develops the Galois/residue input in the converse direction.  A
monic polynomial over the base valuation ring whose roots lie in a splitting
field in fact splits over every extension valuation ring: its roots are
integral over the base and hence belong to that ring.
-/

noncomputable section

open Polynomial
open UniqueFactorizationMonoid

namespace AlgebraicNumberTheory
namespace Valuations

open ValuationTheory.Valuations

universe u


/-- A monic polynomial over the base valuation ring that splits in the
extension field already splits over any extension valuation ring. -/
theorem monic_splits_in_extension_valuationSubring
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    [hW : V.valuation.HasExtension W.valuation]
    (F : Polynomial V) (hFmonic : F.Monic)
    (hsplit : (F.map ((algebraMap K L).comp V.subtype)).Splits) :
    (F.map (valuationSubringMapOfHasExtension V W hW)).Splits := by
  let ιVW : V →+* W := valuationSubringMapOfHasExtension V W hW
  let FW : Polynomial W := F.map ιVW
  have hmap : FW.map W.subtype =
      F.map ((algebraMap K L).comp V.subtype) := by
    ext i
    simp only [FW, Polynomial.coeff_map, Function.comp_apply,
      RingHom.coe_comp, ιVW]
    rfl
  have hsplit_map : (FW.map W.subtype).Splits := by
    rw [hmap]
    exact hsplit
  apply Polynomial.Splits.of_splits_map_of_injective W.subtype_injective hsplit_map
  intro α hα
  have hαroot : (F.map ((algebraMap K L).comp V.subtype)).eval α = 0 := by
    rw [← hmap]
    exact (Polynomial.mem_roots
      ((Polynomial.map_ne_zero_iff W.subtype_injective).2
        (hFmonic.map ιVW).ne_zero)).1 hα
  have hαint : IsIntegral V α := by
    refine ⟨F, hFmonic, ?_⟩
    have hVL : (algebraMap V L) =
        (algebraMap K L).comp V.subtype := by
      ext x
      rfl
    rw [hVL]
    rw [Polynomial.eval_map] at hαroot
    exact hαroot
  have hαmem : α ∈ W := by
    have hαint' : IsIntegral V.valuation.valuationSubring α := by
      rw [ValuationSubring.valuationSubring_valuation]
      exact hαint
    have hz : α ∈ W.valuation.valuationSubring :=
      ValuationTheory.DiscreteValuationField.Valuation.integralClosure_mem_valuationSubring_of_hasExtension
        (L := L) V.valuation W.valuation ⟨α, hαint'⟩
    simpa [ValuationSubring.valuationSubring_valuation] using hz
  exact ⟨⟨α, hαmem⟩, rfl⟩



/-- The canonical residue-field map sends the residue of a base-ring element
to the residue of its image in the extension valuation ring. -/
theorem residueFieldMapOfHasExtension_residue
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    (hW : V.valuation.HasExtension W.valuation) (x : V) :
    residueFieldMapOfHasExtension V W hW (IsLocalRing.residue V x) =
      IsLocalRing.residue W (valuationSubringMapOfHasExtension V W hW x) := by
  let : IsLocalHom (valuationSubringMapOfHasExtension V W hW) :=
    valuationSubringMapOfHasExtension_isLocalHom V W hW
  exact IsLocalRing.ResidueField.map_residue
    (valuationSubringMapOfHasExtension V W hW) x



/-- In a normal extension with a unique extension valuation ring, reductions
of two roots of one irreducible ground-field polynomial are conjugate under
the induced residue-field automorphism. -/
theorem residues_of_irreducible_roots_are_conjugate
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Normal K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    (hW : V.valuation.HasExtension W.valuation)
    (huniq : ∀ W' : ValuationSubring L,
      V.valuation.HasExtension W'.valuation → W' = W)
    (F : Polynomial V)
    (hirr : Irreducible (F.map V.subtype))
    {a b : W}
    (ha : (F.map (valuationSubringMapOfHasExtension V W hW)).eval a = 0)
    (hb : (F.map (valuationSubringMapOfHasExtension V W hW)).eval b = 0) :
    ∃ σ : L ≃ₐ[K] L,
      residueFieldEquivOfUniqueExtension V W hW huniq σ
          (IsLocalRing.residue W b) =
        IsLocalRing.residue W a := by
  let p : Polynomial K := F.map V.subtype
  let ιVW : V →+* W := valuationSubringMapOfHasExtension V W hW
  have hmap :
      (F.map ιVW).map W.subtype =
        p.map (algebraMap K L) := by
    ext i
    simp only [Polynomial.coeff_map, p, ιVW]
    rfl
  have haL : (p.map (algebraMap K L)).eval (a : L) = 0 := by
    rw [← hmap]
    rw [Polynomial.eval_map]
    change Polynomial.eval₂ W.subtype (W.subtype a) (F.map ιVW) = 0
    rw [Polynomial.eval₂_hom]
    exact congrArg W.subtype ha
  have hbL : (p.map (algebraMap K L)).eval (b : L) = 0 := by
    rw [← hmap]
    rw [Polynomial.eval_map]
    change Polynomial.eval₂ W.subtype (W.subtype b) (F.map ιVW) = 0
    rw [Polynomial.eval₂_hom]
    exact congrArg W.subtype hb
  have haeval : (aeval (a : L)) p = 0 := by
    simpa [aeval_def, Polynomial.eval_map] using haL
  have hbeval : (aeval (b : L)) p = 0 := by
    simpa [aeval_def, Polynomial.eval_map] using hbL
  have hmin : minpoly K (a : L) = minpoly K (b : L) := by
    rw [← minpoly.eq_of_irreducible hirr haeval,
      ← minpoly.eq_of_irreducible hirr hbeval]
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit L).1 hmin
  refine ⟨σ, ?_⟩
  rw [residueFieldEquivOfUniqueExtension_residue]
  congr 1
  ext
  exact hσ

/-- A monic irreducible factor over the ground field cannot acquire two
coprime positive-degree factors after reduction when the extension valuation
ring on its splitting field is unique.  This is the precise primary-reduction
input used in the proof of the unique-extension criterion. -/
theorem irreducible_monic_reduction_coprime_factor_degree_zero
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    [hW : V.valuation.HasExtension W.valuation]
    (huniq : ∀ W' : ValuationSubring L,
      V.valuation.HasExtension W'.valuation → W' = W)
    (F : Polynomial V) (hFmonic : F.Monic)
    (hirr : Irreducible (F.map V.subtype))
    [IsSplittingField K L (F.map V.subtype)]
    (gbar hbar : Polynomial (IsLocalRing.ResidueField V))
    (hfactor : F.map (IsLocalRing.residue V) = gbar * hbar)
    (hcoprime : IsCoprime gbar hbar) :
    gbar.natDegree = 0 ∨ hbar.natDegree = 0 := by
  let : Normal K L := Normal.of_isSplittingField (F.map V.subtype)
  by_contra hdegrees
  push Not at hdegrees
  have hgpos : 0 < gbar.natDegree := Nat.pos_of_ne_zero hdegrees.1
  have hhpos : 0 < hbar.natDegree := Nat.pos_of_ne_zero hdegrees.2
  let k := IsLocalRing.ResidueField V
  let l := IsLocalRing.ResidueField W
  let φ : k →+* l := residueFieldMapOfHasExtension V W hW
  let Fbar : Polynomial k := F.map (IsLocalRing.residue V)
  let FW : Polynomial W := F.map (valuationSubringMapOfHasExtension V W hW)
  have hsplitL :
      (F.map ((algebraMap K L).comp V.subtype)).Splits := by
    have hs := IsSplittingField.splits L (F.map V.subtype)
    simpa [Polynomial.map_map] using hs
  have hsplitW : FW.Splits := by
    exact monic_splits_in_extension_valuationSubring V W F hFmonic hsplitL
  have hpolyResidue :
      Fbar.map φ = FW.map (IsLocalRing.residue W) := by
    ext i
    simp only [Fbar, FW, Polynomial.coeff_map, φ]
    exact residueFieldMapOfHasExtension_residue V W hW (F.coeff i)
  have hsplitBar : (Fbar.map φ).Splits := by
    rw [hpolyResidue]
    exact hsplitW.map (IsLocalRing.residue W)
  have hFbar0 : Fbar.map φ ≠ 0 :=
    (hFmonic.map (IsLocalRing.residue V)).map φ |>.ne_zero
  have hfactorMap : Fbar.map φ = gbar.map φ * hbar.map φ := by
    rw [← Polynomial.map_mul, ← hfactor]
  have hgSplit : (gbar.map φ).Splits :=
    hsplitBar.of_dvd hFbar0 (by
      rw [hfactorMap]
      exact dvd_mul_right _ _)
  have hhSplit : (hbar.map φ).Splits :=
    hsplitBar.of_dvd hFbar0 (by
      rw [hfactorMap]
      exact dvd_mul_left _ _)
  have hgRootsNe : (gbar.map φ).roots ≠ 0 := by
    intro hz
    have hc := hgSplit.natDegree_eq_card_roots
    rw [hz] at hc
    have : gbar.natDegree = 0 := by
      simpa [Polynomial.natDegree_map] using hc
    exact hdegrees.1 this
  have hhRootsNe : (hbar.map φ).roots ≠ 0 := by
    intro hz
    have hc := hhSplit.natDegree_eq_card_roots
    rw [hz] at hc
    have : hbar.natDegree = 0 := by
      simpa [Polynomial.natDegree_map] using hc
    exact hdegrees.2 this
  obtain ⟨γ, hγg⟩ := Multiset.exists_mem_of_ne_zero hgRootsNe
  obtain ⟨δ, hδh⟩ := Multiset.exists_mem_of_ne_zero hhRootsNe
  have hprod0 : gbar.map φ * hbar.map φ ≠ 0 := by
    rw [← hfactorMap]
    exact hFbar0
  have hg0 : gbar.map φ ≠ 0 := left_ne_zero_of_mul hprod0
  have hh0 : hbar.map φ ≠ 0 := right_ne_zero_of_mul hprod0
  have hγF : γ ∈ (Fbar.map φ).roots := by
    rw [hfactorMap, Polynomial.roots_mul hprod0]
    simp [hγg]
  have hδF : δ ∈ (Fbar.map φ).roots := by
    rw [hfactorMap, Polynomial.roots_mul hprod0]
    simp [hδh]
  have hγFW : γ ∈ (FW.map (IsLocalRing.residue W)).roots := by
    rwa [← hpolyResidue]
  have hδFW : δ ∈ (FW.map (IsLocalRing.residue W)).roots := by
    rwa [← hpolyResidue]
  have hrootsMap :
      FW.roots.map (IsLocalRing.residue W) =
        (FW.map (IsLocalRing.residue W)).roots :=
    (hFmonic.map (valuationSubringMapOfHasExtension V W hW)).roots_map_of_card_eq_natDegree
      (IsLocalRing.residue W) hsplitW.natDegree_eq_card_roots.symm
  rw [← hrootsMap] at hγFW hδFW
  obtain ⟨a, haRoot, haResidue⟩ := Multiset.mem_map.mp hγFW
  obtain ⟨b, hbRoot, hbResidue⟩ := Multiset.mem_map.mp hδFW
  have haEval : FW.eval a = 0 :=
    (Polynomial.mem_roots (hFmonic.map
      (valuationSubringMapOfHasExtension V W hW)).ne_zero).1 haRoot
  have hbEval : FW.eval b = 0 :=
    (Polynomial.mem_roots (hFmonic.map
      (valuationSubringMapOfHasExtension V W hW)).ne_zero).1 hbRoot
  obtain ⟨σ, hσres⟩ :=
    residues_of_irreducible_roots_are_conjugate V W hW huniq F hirr hbEval haEval
  let τ : l ≃+* l := residueFieldEquivOfUniqueExtension V W hW huniq σ
  have hτγδ : τ γ = δ := by
    dsimp [τ]
    rw [← haResidue, ← hbResidue]
    exact hσres
  have hτcoeff : (gbar.map φ).map τ.toRingHom = gbar.map φ := by
    ext i
    simp only [Polynomial.coeff_map, φ, τ]
    exact residueFieldEquivOfUniqueExtension_algebraMap
      V W huniq σ (gbar.coeff i)
  have hγeval : (gbar.map φ).eval γ = 0 :=
    (Polynomial.mem_roots hg0).1 hγg
  have hδg : (gbar.map φ).eval δ = 0 := by
    calc
      (gbar.map φ).eval δ = (gbar.map φ).eval (τ γ) := by rw [hτγδ]
      _ = ((gbar.map φ).map τ.toRingHom).eval (τ γ) := by rw [hτcoeff]
      _ = τ ((gbar.map φ).eval γ) := by
        change ((gbar.map φ).map τ.toRingHom).eval (τ.toRingHom γ) = _
        exact Polynomial.eval_map_apply (p := gbar.map φ) (f := τ.toRingHom) γ
      _ = 0 := by rw [hγeval, map_zero]
  have hδeval : (hbar.map φ).eval δ = 0 :=
    (Polynomial.mem_roots hh0).1 hδh
  have hcoprimeMap : IsCoprime (gbar.map φ) (hbar.map φ) := by
    simpa using hcoprime.map (Polynomial.mapRingHom φ)
  rcases hcoprimeMap with ⟨A, B, hbez⟩
  have hbezEval := congrArg (Polynomial.eval δ) hbez
  simp [hδg, hδeval] at hbezEval





end Valuations
end AlgebraicNumberTheory

end
