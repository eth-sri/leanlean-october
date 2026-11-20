module

public import ValuedFieldTheory.Ramification.HilbertRamification.Monogeneity

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# First ramification-quotient homomorphism over general DVFs

This file constructs the graded uniformizer homomorphism under the standing
hypotheses of ramification-number theory.  Completeness is not assumed.  The
injectivity statement includes the necessary separability hypothesis on the
residue extension; the unconditional printed assertion is false for fiercely
ramified extensions.
-/

noncomputable section

universe u v w x

namespace RamificationTheory.HilbertRamification
namespace Higher

open ValuationTheory.DiscreteValuationField.ResidueField

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [FiniteDimensional K L] [base.valuation.HasExtension target.valuation]
variable [IsGalois K L]

section

variable (target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L) (n : ℕ)

/-- The principal-unit filtration attached to a general DVF. -/
def dvfHigherPrincipalUnitGroup :
    Subgroup target.valuationSubringˣ where
  carrier := {a | (a : target.valuationSubring) - 1 ∈ target.maximalIdeal ^ n}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    have hre :
        ((a * b : target.valuationSubringˣ) : target.valuationSubring) - 1 =
          (a : target.valuationSubring) *
              ((b : target.valuationSubring) - 1) +
            ((a : target.valuationSubring) - 1) := by
      simp
      ring
    change
      ((a * b : target.valuationSubringˣ) : target.valuationSubring) - 1 ∈
        target.maximalIdeal ^ n
    rw [hre]
    exact Ideal.add_mem _
      (Ideal.mul_mem_left _ _ hb) ha
  inv_mem' := by
    intro a ha
    have hre :
        ((a⁻¹ : target.valuationSubringˣ) : target.valuationSubring) - 1 =
          -(((a⁻¹ : target.valuationSubringˣ) : target.valuationSubring) *
            ((a : target.valuationSubring) - 1)) := by
      calc
        _ =
            ((a⁻¹ : target.valuationSubringˣ) : target.valuationSubring) -
              ((a⁻¹ : target.valuationSubringˣ) : target.valuationSubring) *
                (a : target.valuationSubring) := by simp
        _ = _ := by ring
    change
      ((a⁻¹ : target.valuationSubringˣ) : target.valuationSubring) - 1 ∈
        target.maximalIdeal ^ n
    rw [hre]
    exact (target.maximalIdeal ^ n).neg_mem
      (Ideal.mul_mem_left _ _ ha)

/-- States the theorem `mem_dvfHigherPrincipalUnitGroup_iff`. -/
@[simp] theorem mem_dvfHigherPrincipalUnitGroup_iff (a : target.valuationSubringˣ) :
    a ∈ dvfHigherPrincipalUnitGroup target n ↔
      (a : target.valuationSubring) - 1 ∈ target.maximalIdeal ^ n :=
  Iff.rfl

/-- The literal target U_L^n/U_L^(n+1). -/
abbrev dvfPrincipalUnitGradedPiece :=
  dvfHigherPrincipalUnitGroup target n ⧸
    (dvfHigherPrincipalUnitGroup target (n + 1)).subgroupOf
      (dvfHigherPrincipalUnitGroup target n)

end

section

variable
    (huniq : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x} base target)

/-- The literal source G_n/G_(n+1) formed from the real lower groups. -/
abbrev lowerRamificationGradedPiece
    (n : ℕ) :=
  lowerRamificationGroup
      (base := base) (target := target) huniq (n : ℝ) ⧸
    (lowerRamificationGroup
      (base := base) (target := target) huniq ((n + 1 : ℕ) : ℝ)).subgroupOf
      (lowerRamificationGroup
        (base := base) (target := target) huniq (n : ℝ))

/-- The unique-extension action on target valuation-ring units. -/
abbrev dvfValuationSubringUnitAut
    (sigma : Gal(L/K)) :
    target.valuationSubringˣ →* target.valuationSubringˣ :=
  Units.map
    (valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq sigma).toMonoidHom

end

omit [FiniteDimensional K L] [IsGalois K L] in
/-- States the theorem `dvfValuationSubringUnitAut_apply`. -/
@[simp] theorem dvfValuationSubringUnitAut_apply
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (sigma : Gal(L/K)) (a : target.valuationSubringˣ) :
    ((dvfValuationSubringUnitAut huniq sigma a :
        target.valuationSubringˣ) : target.valuationSubring) =
      valuationSubringAutOfUniqueExtension huniq sigma
        (a : target.valuationSubring) :=
  rfl

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Every Galois conjugate of a target uniformizer differs from it by a
valuation-ring unit. -/
theorem exists_dvfUniformizerQuotientUnit
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {pi : target.valuationSubring}
    (hpi : target.valuation.IsUniformizer (pi : L))
    (sigma : Gal(L/K)) :
    ∃ a : target.valuationSubringˣ,
      valuationSubringAutOfUniqueExtension huniq sigma pi =
        (a : target.valuationSubring) * pi := by
  let sigmaPi :=
    valuationSubringAutOfUniqueExtension
        huniq sigma pi
  have hpiMem : pi ∈ target.maximalIdeal :=
    target.uniformizer_mem_maximalIdeal hpi
  have hpiDvd : pi ∣ sigmaPi := by
    have hsigmaMem : sigmaPi ∈ target.maximalIdeal ^ 1 := (valuationSubringAutOfUniqueExtension_mem_maximalIdeal_pow_iff huniq sigma 1 pi).2
          (by simpa using hpiMem)
    rw [← Ideal.mem_span_singleton]
    have hsigmaMem' : sigmaPi ∈ target.maximalIdeal := by
      simpa using hsigmaMem
    rw [target.maximalIdeal_eq_span_uniformizer hpi] at hsigmaMem'
    exact hsigmaMem'
  have hsigmaDvd : sigmaPi ∣ pi := by
    have hinvMem :
        valuationSubringAutOfUniqueExtension huniq sigma⁻¹ pi ∈
          target.maximalIdeal ^ 1 :=
      (valuationSubringAutOfUniqueExtension_mem_maximalIdeal_pow_iff huniq sigma⁻¹ 1 pi).2
        (by simpa using hpiMem)
    have hdiv :
        pi ∣ valuationSubringAutOfUniqueExtension
              huniq sigma⁻¹ pi := by
      rw [← Ideal.mem_span_singleton]
      have hinvMem' :
          valuationSubringAutOfUniqueExtension
                huniq sigma⁻¹ pi ∈
            target.maximalIdeal := by
        simpa using hinvMem
      rw [target.maximalIdeal_eq_span_uniformizer hpi] at hinvMem'
      exact hinvMem'
    rcases hdiv with ⟨b, hb⟩
    refine
      ⟨valuationSubringAutOfUniqueExtension
          huniq sigma b, ?_⟩
    calc
      pi =
          valuationSubringAutOfUniqueExtension
              huniq sigma
            (valuationSubringAutOfUniqueExtension
                huniq sigma⁻¹ pi) := by
        simp
      _ = valuationSubringAutOfUniqueExtension
              huniq sigma (pi * b) := by
        rw [hb]
      _ = sigmaPi *
          valuationSubringAutOfUniqueExtension
              huniq sigma b := by
        simp [sigmaPi]
  rcases hpiDvd with ⟨a, ha⟩
  rcases hsigmaDvd with ⟨b, hb⟩
  have hpi0 : pi ≠ 0 := by
    intro hzero
    exact hpi.ne_zero (by exact (congrArg (fun z : target.valuationSubring => (z : L)) hzero))
  have hab : a * b = 1 := by
    apply mul_left_cancel₀ hpi0
    calc
      _ = (pi * a) * b := by rw [mul_assoc]
      _ = sigmaPi * b := by rw [← ha]
      _ = pi := hb.symm
      _ = pi * 1 := by rw [mul_one]
  refine ⟨⟨a, b, hab, ?_⟩, ?_⟩
  · simpa [mul_comm] using hab
  · simpa [mul_comm] using ha

/-- The chosen unit sigma(pi)/pi. -/
noncomputable def dvfUniformizerQuotientUnit
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (pi : target.valuationSubring)
    (hpi : target.valuation.IsUniformizer (pi : L))
    (sigma : Gal(L/K)) : target.valuationSubringˣ :=
  Classical.choose
    (exists_dvfUniformizerQuotientUnit
      (base := base) (target := target) huniq hpi sigma)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- States the theorem `dvfUniformizerQuotientUnit_mul_uniformizer`. -/
@[simp] theorem dvfUniformizerQuotientUnit_mul_uniformizer
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (pi : target.valuationSubring)
    (hpi : target.valuation.IsUniformizer (pi : L))
    (sigma : Gal(L/K)) :
    valuationSubringAutOfUniqueExtension huniq sigma pi =
      (dvfUniformizerQuotientUnit huniq pi hpi sigma :
          target.valuationSubring) * pi :=
  Classical.choose_spec
    (exists_dvfUniformizerQuotientUnit huniq hpi sigma)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Exact cocycle identity for the chosen quotient units. -/
theorem dvfUniformizerQuotientUnit_mul_eq
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (pi : target.valuationSubring)
    (hpi : target.valuation.IsUniformizer (pi : L))
    (sigma tau : Gal(L/K)) :
    dvfUniformizerQuotientUnit huniq pi hpi (sigma * tau) =
      dvfValuationSubringUnitAut
          (base := base) (target := target) huniq sigma
          (dvfUniformizerQuotientUnit huniq pi hpi tau) *
        dvfUniformizerQuotientUnit huniq pi hpi sigma := by
  apply Units.ext
  have hpi0 : pi ≠ 0 := by
    intro hzero
    exact hpi.ne_zero (by exact (congrArg (fun z : target.valuationSubring => (z : L)) hzero))
  apply mul_right_cancel₀ hpi0
  calc
    ((dvfUniformizerQuotientUnit
          huniq pi hpi (sigma * tau) :
          target.valuationSubringˣ) : target.valuationSubring) * pi =
        valuationSubringAutOfUniqueExtension
            huniq (sigma * tau) pi := by
      simp_all
    _ = valuationSubringAutOfUniqueExtension
            huniq sigma
          (valuationSubringAutOfUniqueExtension
              huniq tau pi) := by
      rfl
    _ = valuationSubringAutOfUniqueExtension
            huniq sigma
          ((dvfUniformizerQuotientUnit
                huniq pi hpi tau :
                target.valuationSubringˣ) : target.valuationSubring) *
            valuationSubringAutOfUniqueExtension
                huniq sigma pi := by
      simp_all
    _ =
        ((dvfValuationSubringUnitAut
                huniq sigma
              (dvfUniformizerQuotientUnit
                  huniq pi hpi tau) *
            dvfUniformizerQuotientUnit
                huniq pi hpi sigma :
            target.valuationSubringˣ) : target.valuationSubring) * pi := by
      simp_all [mul_assoc]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Quotient-unit membership is equivalent to one-deeper displacement of the
uniformizer. -/
theorem dvfUniformizerQuotientUnit_mem_iff_uniformizer_sub_mem
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {pi : target.valuationSubring}
    (hpi : target.valuation.IsUniformizer (pi : L))
    (n : ℕ) (sigma : Gal(L/K)) :
    dvfUniformizerQuotientUnit huniq pi hpi sigma ∈
      dvfHigherPrincipalUnitGroup target n ↔
      valuationSubringAutOfUniqueExtension huniq sigma pi - pi ∈
        target.maximalIdeal ^ (n + 1) := by
  let a :=
    (dvfUniformizerQuotientUnit
        huniq pi hpi sigma :
        target.valuationSubring)
  change a - 1 ∈ target.maximalIdeal ^ n ↔ _
  have hmul :
      (a - 1) * pi =
        valuationSubringAutOfUniqueExtension huniq sigma pi - pi := by
    dsimp [a]
    rw [dvfUniformizerQuotientUnit_mul_uniformizer huniq pi hpi sigma]
    ring
  constructor
  · intro ha
    rw [← hmul]
    rw [target.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd
      (pi := pi) (x := (a - 1) * pi) hpi (n + 1)]
    rw [target.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd
      (pi := pi) (x := a - 1) hpi n] at ha
    rcases ha with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    calc
      (a - 1) * pi = (pi ^ n * b) * pi := by rw [hb]
      _ = pi ^ (n + 1) * b := by ring
  · intro hdiff
    rw [← hmul] at hdiff
    rw [target.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd
      (pi := pi) (x := (a - 1) * pi) hpi (n + 1)] at hdiff
    rw [target.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd
      (pi := pi) (x := a - 1) hpi n]
    rcases hdiff with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    have hpi0 : pi ≠ 0 := by
      intro hzero
      exact hpi.ne_zero (by exact (congrArg (fun z : target.valuationSubring => (z : L)) hzero))
    apply mul_right_cancel₀ hpi0
    calc
      _ = pi ^ (n + 1) * b := hb
      _ = (pi ^ n * b) * pi := by ring

omit [FiniteDimensional K L] [IsGalois K L] in
/-- If sigma lies in G_n, then sigma(pi)/pi lies in U_L^n. -/
theorem dvfUniformizerQuotientUnit_mem_of_mem_lowerRamificationGroup
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {pi : target.valuationSubring}
    (hpi : target.valuation.IsUniformizer (pi : L))
    {n : ℕ} {sigma : Gal(L/K)}
    (hsigma :
      sigma ∈ lowerRamificationGroup huniq (n : ℝ)) :
    dvfUniformizerQuotientUnit huniq pi hpi sigma ∈
      dvfHigherPrincipalUnitGroup target n := (dvfUniformizerQuotientUnit_mem_iff_uniformizer_sub_mem
        huniq hpi n sigma).2
      ((mem_lowerRamificationGroup_nat_iff
          huniq n sigma).1 hsigma pi)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A G_n automorphism acts trivially on every unit modulo U_L^(n+1). -/
theorem dvfValuationSubringUnitAut_div_mem_succ
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {n : ℕ} {sigma : Gal(L/K)}
    (hsigma :
      sigma ∈ lowerRamificationGroup huniq (n : ℝ))
    (a : target.valuationSubringˣ) :
    dvfValuationSubringUnitAut huniq sigma a / a ∈
      dvfHigherPrincipalUnitGroup target (n + 1) := by
  rw [mem_dvfHigherPrincipalUnitGroup_iff]
  have hre :
      ((dvfValuationSubringUnitAut
            huniq sigma a / a :
            target.valuationSubringˣ) : target.valuationSubring) - 1 =
        ((a⁻¹ : target.valuationSubringˣ) : target.valuationSubring) *
          (valuationSubringAutOfUniqueExtension
                huniq sigma
              (a : target.valuationSubring) -
            (a : target.valuationSubring)) := by
    simp [div_eq_mul_inv]
    have hinv :
        ((a⁻¹ : target.valuationSubringˣ) : target.valuationSubring) *
          (a : target.valuationSubring) = 1 := by
      exact_mod_cast Units.inv_mul a
    rw [mul_sub, hinv]
    ring
  rw [hre]
  exact Ideal.mul_mem_left _ _ ((mem_lowerRamificationGroup_nat_iff
    huniq n sigma).1 hsigma a)

/-- Representative homomorphism from G_n to the literal principal-unit
graded quotient. -/
noncomputable def dvfUniformizerRepresentativeHom
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (pi : target.valuationSubring)
    (hpi : target.valuation.IsUniformizer (pi : L))
    (n : ℕ) :
    lowerRamificationGroup
        (base := base) (target := target) huniq (n : ℝ) →*
      dvfPrincipalUnitGradedPiece target n where
  toFun sigma :=
    QuotientGroup.mk'
      ((dvfHigherPrincipalUnitGroup target (n + 1)).subgroupOf
        (dvfHigherPrincipalUnitGroup target n))
      ⟨dvfUniformizerQuotientUnit
          (base := base) (target := target) huniq pi hpi
          (sigma : Gal(L/K)),
        dvfUniformizerQuotientUnit_mem_of_mem_lowerRamificationGroup
          (base := base) (target := target) huniq hpi sigma.property⟩
  map_one' := by
    let oneN :
        lowerRamificationGroup
            huniq (n : ℝ) := 1
    let u1 : dvfHigherPrincipalUnitGroup target n :=
      ⟨dvfUniformizerQuotientUnit
          (base := base) (target := target) huniq pi hpi 1,
        dvfUniformizerQuotientUnit_mem_of_mem_lowerRamificationGroup
          (base := base) (target := target) huniq hpi oneN.property⟩
    change
      QuotientGroup.mk'
          ((dvfHigherPrincipalUnitGroup target (n + 1)).subgroupOf
            (dvfHigherPrincipalUnitGroup target n)) u1 = 1
    apply
      (QuotientGroup.eq_one_iff
         u1).2
    change
      dvfUniformizerQuotientUnit
            huniq pi hpi 1 ∈
        dvfHigherPrincipalUnitGroup target (n + 1)
    exact
      dvfUniformizerQuotientUnit_mem_of_mem_lowerRamificationGroup
          huniq hpi
        (lowerRamificationGroup
            huniq
          ((n + 1 : ℕ) : ℝ)).one_mem
  map_mul' := by
    intro sigma tau
    apply
      (QuotientGroup.eq_iff_div_mem
        ).2
    change
      dvfUniformizerQuotientUnit
              huniq pi hpi
            (sigma * tau) /
          (dvfUniformizerQuotientUnit
                huniq pi hpi
              sigma *
            dvfUniformizerQuotientUnit
                huniq pi hpi
              tau) ∈
        dvfHigherPrincipalUnitGroup target (n + 1)
    have hact :=
      dvfValuationSubringUnitAut_div_mem_succ
          huniq sigma.property
        (dvfUniformizerQuotientUnit
            huniq pi hpi
          tau)
    rw [dvfUniformizerQuotientUnit_mul_eq
        huniq pi hpi
      sigma tau]
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hact

omit [FiniteDimensional K L] [IsGalois K L] in
/-- States the theorem `dvfUniformizerRepresentativeHom_apply`. -/
@[simp] theorem dvfUniformizerRepresentativeHom_apply
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (pi : target.valuationSubring)
    (hpi : target.valuation.IsUniformizer (pi : L))
    (n : ℕ)
    (sigma :
      lowerRamificationGroup huniq (n : ℝ)) :
    dvfUniformizerRepresentativeHom huniq pi hpi n sigma =
      QuotientGroup.mk'
        ((dvfHigherPrincipalUnitGroup target (n + 1)).subgroupOf
          (dvfHigherPrincipalUnitGroup target n))
        ⟨dvfUniformizerQuotientUnit huniq pi hpi
            (sigma : Gal(L/K)),
          dvfUniformizerQuotientUnit_mem_of_mem_lowerRamificationGroup huniq hpi sigma.property⟩ :=
  rfl

/-- The first ramification-quotient homomorphism: the uniformizer quotient descends
to G_n/G_(n+1) with values in U_L^n/U_L^(n+1). -/
noncomputable def uniformizerGradedHom
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (pi : target.valuationSubring)
    (hpi : target.valuation.IsUniformizer (pi : L))
    (n : ℕ) :
    lowerRamificationGradedPiece (base := base) (target := target) huniq n →*
      dvfPrincipalUnitGradedPiece target n :=
  QuotientGroup.lift
    ((lowerRamificationGroup
      (base := base) (target := target) huniq
      ((n + 1 : ℕ) : ℝ)).subgroupOf
      (lowerRamificationGroup
        (base := base) (target := target) huniq (n : ℝ)))
    (dvfUniformizerRepresentativeHom
      (base := base) (target := target) huniq pi hpi n)
    (by
      intro sigma hsigma
      rw [MonoidHom.mem_ker]
      change
        QuotientGroup.mk'
            ((dvfHigherPrincipalUnitGroup target (n + 1)).subgroupOf
              (dvfHigherPrincipalUnitGroup target n))
            ⟨dvfUniformizerQuotientUnit
                  huniq pi hpi
                sigma,
              dvfUniformizerQuotientUnit_mem_of_mem_lowerRamificationGroup
                  huniq hpi sigma.property⟩ =
          1
      apply
        (QuotientGroup.eq_one_iff
          (N := (dvfHigherPrincipalUnitGroup target (n + 1)).subgroupOf
            (dvfHigherPrincipalUnitGroup target n))
          ⟨dvfUniformizerQuotientUnit
              (base := base) (target := target) huniq pi hpi
              (sigma : Gal(L/K)),
            dvfUniformizerQuotientUnit_mem_of_mem_lowerRamificationGroup
              (base := base) (target := target) huniq hpi sigma.property⟩).2
      change
        dvfUniformizerQuotientUnit
              huniq pi hpi
            sigma ∈
          dvfHigherPrincipalUnitGroup target (n + 1)
      exact
        dvfUniformizerQuotientUnit_mem_of_mem_lowerRamificationGroup
            huniq hpi
          (by simpa [Subgroup.mem_subgroupOf] using hsigma))

omit [FiniteDimensional K L] [IsGalois K L] in
/-- States the theorem `uniformizerGradedHom_mk`. -/
@[simp] theorem uniformizerGradedHom_mk
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (pi : target.valuationSubring)
    (hpi : target.valuation.IsUniformizer (pi : L))
    (n : ℕ)
    (sigma :
      lowerRamificationGroup huniq (n : ℝ)) :
    uniformizerGradedHom
        (base := base) (target := target) huniq pi hpi n
        (QuotientGroup.mk'
          ((lowerRamificationGroup
            (base := base) (target := target) huniq
            ((n + 1 : ℕ) : ℝ)).subgroupOf
            (lowerRamificationGroup huniq (n : ℝ))) sigma) =
      dvfUniformizerRepresentativeHom huniq pi hpi n sigma :=
  rfl

/-- The unique-extension ring automorphism as an algebra automorphism over
the base valuation ring. -/
def valuationSubringAlgEquivOfUniqueExtension
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (sigma : Gal(L/K)) :
    target.valuationSubring ≃ₐ[base.valuationSubring]
      target.valuationSubring :=
  { valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq sigma with
    commutes' := by
      intro a
      apply Subtype.ext
      simp [valuationSubringAutOfUniqueExtension] }

end Higher
end RamificationTheory.HilbertRamification

end
