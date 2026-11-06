module

public import ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
public import ValuedFieldTheory.Valuation.Henselian.Factorization.CoefficientMinimum
public import ValuedFieldTheory.Valuation.Henselian.PrimitiveFactorization
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Polynomial.Vieta

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/








set_option autoImplicit false

/-!
# Monic Hensel factor lifting

This file isolates the algebraic condition used in the factor-lifting criterion.
The condition is the exact condition: a monic polynomial whose
reduction is a product of relatively prime monic polynomials has monic factors
with exactly those reductions.
-/

noncomputable section

open Polynomial

namespace DiscreteValuationField
open ValuationTheory.DiscreteValuationField

universe u





























/-- The monic residual coprime-factor lifting property appearing in
the factor-lifting criterion.  Both residual factors and both lifted factors are monic, and
both residual identities are retained. -/
def MonicResidualCoprimeFactorLifting
    {K : Type u} [Field K] (V : ValuationSubring K) : Prop :=
  ∀ {f : Polynomial V}
      {gbar hbar : Polynomial (IsLocalRing.ResidueField V)},
    f.Monic →
      gbar.Monic →
        hbar.Monic →
          f.map (IsLocalRing.residue V) = gbar * hbar →
            IsCoprime gbar hbar →
              ∃ G H : Polynomial V,
                G.Monic ∧ H.Monic ∧ f = G * H ∧
                  G.map (IsLocalRing.residue V) = gbar ∧
                    H.map (IsLocalRing.residue V) = hbar

/-- the primitive factorization definition's primitive factorization property contains, in
particular, the exact monic lifting property of the factor-lifting criterion.  The factors
returned by the primitive factorization definition are normalized by the mutually inverse leading
coefficients; their reductions stay fixed because both leading coefficients
reduce to `1`. -/
theorem monicResidualCoprimeFactorLifting_of_henselFactorization
    {K : Type u} [Field K] {V : ValuationSubring K}
    (hhensel : HenselFactorizationProperty V) :
    MonicResidualCoprimeFactorLifting V := by
  intro f gbar hbar hf hgbar hhbar hfactor hcoprime
  have hprimitive : f.map (IsLocalRing.residue V) ≠ 0 :=
    (hf.map (IsLocalRing.residue V)).ne_zero
  rcases hhensel hprimitive hfactor hcoprime with
    ⟨G, H, hGdegree, _hHdegree, hGH, hGmap, hHmap⟩
  have hG0 : G ≠ 0 := by
    intro hzero
    rw [hzero] at hGmap
    exact hgbar.ne_zero (by simpa using hGmap.symm)
  have hH0 : H ≠ 0 := by
    intro hzero
    rw [hzero] at hHmap
    exact hhbar.ne_zero (by simpa using hHmap.symm)
  have hleadProduct : G.leadingCoeff * H.leadingCoeff = 1 := by
    calc
      G.leadingCoeff * H.leadingCoeff = (G * H).leadingCoeff := by
        rw [Polynomial.leadingCoeff_mul]
      _ = f.leadingCoeff := by rw [← hGH]
      _ = 1 := hf
  have hGleadResidue :
      IsLocalRing.residue V G.leadingCoeff = 1 := by
    change IsLocalRing.residue V (G.coeff G.natDegree) = 1
    rw [hGdegree]
    calc
      IsLocalRing.residue V (G.coeff gbar.natDegree) =
          (G.map (IsLocalRing.residue V)).coeff gbar.natDegree := by
        rw [Polynomial.coeff_map]
      _ = gbar.coeff gbar.natDegree := by rw [hGmap]
      _ = 1 := hgbar
  have hHleadResidue :
      IsLocalRing.residue V H.leadingCoeff = 1 := by
    have h := congrArg (IsLocalRing.residue V) hleadProduct
    simpa [map_mul, hGleadResidue] using h
  let G' : Polynomial V := Polynomial.C H.leadingCoeff * G
  let H' : Polynomial V := Polynomial.C G.leadingCoeff * H
  have hG' : G'.Monic := by
    apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    simpa [mul_comm] using hleadProduct
  have hH' : H'.Monic := by
    apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    exact hleadProduct
  have hfactor' : f = G' * H' := by
    have hC :
        Polynomial.C H.leadingCoeff * Polynomial.C G.leadingCoeff =
          (1 : Polynomial V) := by
      rw [← Polynomial.C_mul, mul_comm, hleadProduct]
      simp
    calc
      f = G * H := hGH
      _ = 1 * (G * H) := by simp
      _ = (Polynomial.C H.leadingCoeff * Polynomial.C G.leadingCoeff) *
          (G * H) := by rw [hC]
      _ = G' * H' := by
        dsimp [G', H']
        ring
  refine ⟨G', H', hG', hH', hfactor', ?_, ?_⟩
  · simp [G', Polynomial.map_mul, hGmap, hHleadResidue]
  · simp [H', Polynomial.map_mul, hHmap, hGleadResidue]

/-- A factor of positive degree and degree strictly below the product rules
out irreducibility over a field. -/
theorem not_irreducible_of_factor_natDegree_lt
    {K : Type u} [Field K] {f g h : Polynomial K}
    (hfactor : f = g * h)
    (hgpos : 0 < g.natDegree)
    (hglt : g.natDegree < f.natDegree) :
    ¬ Irreducible f := by
  intro hirr
  rcases hirr.isUnit_or_isUnit hfactor with hgunit | hhunit
  · exact (Nat.ne_of_gt hgpos) (Polynomial.natDegree_eq_zero_of_isUnit hgunit)
  · have hg0 : g ≠ 0 := by
      intro hzero
      simp [hzero] at hgpos
    have hh0 : h ≠ 0 := hhunit.ne_zero
    have hdegree : f.natDegree = g.natDegree := by
      rw [hfactor, Polynomial.natDegree_mul hg0 hh0,
        Polynomial.natDegree_eq_zero_of_isUnit hhunit, Nat.add_zero]
    exact (Nat.ne_of_lt hglt) hdegree.symm

/-- The zero-slope contradiction in Artin's proof of the factor-lifting criterion.
A nonconstant coprime residual splitting of a monic polynomial lifts to a
genuine factor of intermediate degree, so its image in the fraction field is
not irreducible. -/
theorem MonicResidualCoprimeFactorLifting.not_irreducible_map
    {K : Type u} [Field K] {V : ValuationSubring K}
    (hlift : MonicResidualCoprimeFactorLifting V)
    {f : Polynomial V}
    {gbar hbar : Polynomial (IsLocalRing.ResidueField V)}
    (hf : f.Monic) (hgbar : gbar.Monic) (hhbar : hbar.Monic)
    (hfactor : f.map (IsLocalRing.residue V) = gbar * hbar)
    (hcoprime : IsCoprime gbar hbar)
    (hgpos : 0 < gbar.natDegree) (hhpos : 0 < hbar.natDegree) :
    ¬ Irreducible (f.map (algebraMap V K)) := by
  rcases hlift hf hgbar hhbar hfactor hcoprime with
    ⟨G, H, hG, _hH, hGH, hGmap, _hHmap⟩
  have hGdegree : G.natDegree = gbar.natDegree := by
    calc
      G.natDegree = (G.map (IsLocalRing.residue V)).natDegree :=
        (hG.natDegree_map (IsLocalRing.residue V)).symm
      _ = gbar.natDegree := by rw [hGmap]
  have hfdegree :
      f.natDegree = gbar.natDegree + hbar.natDegree := by
    calc
      f.natDegree = (f.map (IsLocalRing.residue V)).natDegree :=
        (hf.natDegree_map (IsLocalRing.residue V)).symm
      _ = (gbar * hbar).natDegree := by rw [hfactor]
      _ = gbar.natDegree + hbar.natDegree :=
        Polynomial.natDegree_mul hgbar.ne_zero hhbar.ne_zero
  let Gk : Polynomial K := G.map (algebraMap V K)
  let Hk : Polynomial K := H.map (algebraMap V K)
  have hinj : Function.Injective (algebraMap V K) := by
    intro x y hxy
    exact Subtype.ext hxy
  have hGkdegree : Gk.natDegree = gbar.natDegree := by
    calc
      Gk.natDegree = G.natDegree :=
        Polynomial.natDegree_map_eq_of_injective hinj G
      _ = gbar.natDegree := hGdegree
  have hfkdegree : (f.map (algebraMap V K)).natDegree = f.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hinj f
  have hfieldFactor : f.map (algebraMap V K) = Gk * Hk := by
    rw [hGH, Polynomial.map_mul]
  apply not_irreducible_of_factor_natDegree_lt hfieldFactor
  · simpa [hGkdegree] using hgpos
  · rw [hGkdegree, hfkdegree, hfdegree]
    exact Nat.lt_add_of_pos_right hhpos

/-- A monic polynomial irreducible over the fraction field cannot have a
coprime residual splitting into two positive-degree monic factors. -/
theorem MonicResidualCoprimeFactorLifting.irreducible_monic_reduction_coprime_factor_degree_zero
    {K : Type u} [Field K] {V : ValuationSubring K}
    (hlift : MonicResidualCoprimeFactorLifting V)
    {f : Polynomial V}
    {gbar hbar : Polynomial (IsLocalRing.ResidueField V)}
    (hf : f.Monic)
    (hirr : Irreducible (f.map (algebraMap V K)))
    (hgbar : gbar.Monic) (hhbar : hbar.Monic)
    (hfactor : f.map (IsLocalRing.residue V) = gbar * hbar)
    (hcoprime : IsCoprime gbar hbar) :
    gbar.natDegree = 0 ∨ hbar.natDegree = 0 := by
  by_contra hdegree
  push Not at hdegree
  exact
    (hlift.not_irreducible_map hf hgbar hhbar hfactor hcoprime
      (Nat.pos_of_ne_zero hdegree.1) (Nat.pos_of_ne_zero hdegree.2)) hirr









end DiscreteValuationField

end
