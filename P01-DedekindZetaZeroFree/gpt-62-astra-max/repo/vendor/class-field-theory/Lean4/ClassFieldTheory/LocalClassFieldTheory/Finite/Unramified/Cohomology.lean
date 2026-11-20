module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.FieldTheory.Galois.Basic
public import GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientTower
public import GaloisCohomology.Cyclic.Herbrand.HerbrandFiniteness
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.IntegerUnitsHerbrand
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisCohomology
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.Norm

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Tate cohomology of units in unramified extensions

For an unramified extension of local fields the actual low-degree Tate
cohomology of the integer units and of every principal-unit group is trivial.
The norm statements are the corresponding actual norm surjections.
-/

noncomputable section

universe u

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand

section

variable (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (n : Nat)

/-- The actual integral-closure Galois action on `U_L^n`, packaged as the
multiplicative action used by low-degree Tate cohomology. -/
@[implicit_reducible]
def galoisGroupPrincipalUnitsMulDistribMulActionOfIsIntegralClosure :
    MulDistribMulAction Gal(L / K) (principalUnits L n) where
  smul sigma a := galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n sigma a
  one_smul := by
    intro a
    exact congrArg (fun e : principalUnits L n ≃* principalUnits L n => e a)
      (map_one (galoisGroupPrincipalUnitsMapEquivHomOfIsIntegralClosure K L n))
  mul_smul := by
    intro sigma tau a
    exact congrArg (fun e : principalUnits L n ≃* principalUnits L n => e a)
      (map_mul (galoisGroupPrincipalUnitsMapEquivHomOfIsIntegralClosure K L n) sigma tau)
  smul_mul := fun sigma a b => map_mul (galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n sigma) a b
  smul_one := fun sigma => map_one (galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n sigma)

/-- States the theorem `galoisGroupPrincipalUnitsMulDistribMulActionOfIsIntegralClosure_smul`. -/
@[simp]
theorem galoisGroupPrincipalUnitsMulDistribMulActionOfIsIntegralClosure_smul
    (sigma : Gal(L / K)) (a : principalUnits L n) :
    letI := galoisGroupPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
    sigma • a = galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n sigma a :=
  rfl

end

/-- Inclusion in the actual short exact sequence
`1 → U_L^n → 𝒪_Lˣ → 𝒪_Lˣ/U_L^n → 1`. -/
 def principalUnitsIntegerUnitsInclusion
    (L : Type u) [Field L] [ValuativeRel L] (n : Nat) :
    principalUnits L n →* 𝒪[L]ˣ :=
  (principalUnits L n).subtype

/-- Quotient map in the actual short exact sequence
`1 → U_L^n → 𝒪_Lˣ → 𝒪_Lˣ/U_L^n → 1`. -/
 def integerUnitsPrincipalUnitsQuotientMap
    (L : Type u) [Field L] [ValuativeRel L] (n : Nat) :
    𝒪[L]ˣ →* IntegerUnitsModPrincipalUnitsAtLevel L n :=
  integerUnitsModPrincipalUnitsAtLevelMk L n

section

variable (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]

/-- The standard principal-unit sequence is short exact and equivariant for
the actual integral-closure Galois actions. -/
private theorem principalUnitsIntegerUnits_shortExact
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (n : Nat) :
    letI := galoisGroupPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    letI := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
    (∀ (sigma : Gal(L / K)) (a : principalUnits L n),
        principalUnitsIntegerUnitsInclusion L n (sigma • a) =
          sigma • principalUnitsIntegerUnitsInclusion L n a) ∧
      (∀ (sigma : Gal(L / K)) (a : 𝒪[L]ˣ),
        integerUnitsPrincipalUnitsQuotientMap L n (sigma • a) =
          sigma • integerUnitsPrincipalUnitsQuotientMap L n a) ∧
      (∀ a : 𝒪[L]ˣ, integerUnitsPrincipalUnitsQuotientMap L n a = 1 ↔
        ∃ v : principalUnits L n,
          principalUnitsIntegerUnitsInclusion L n v = a) ∧
      Function.Injective (principalUnitsIntegerUnitsInclusion L n) ∧
      Function.Surjective (integerUnitsPrincipalUnitsQuotientMap L n) := by
  let := galoisGroupPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  let := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
  refine ⟨?_, ?_, ?_, (principalUnits L n).subtype_injective,
    integerUnitsModPrincipalUnitsAtLevelMk_surjective L n⟩
  · intro sigma a
    rfl
  · intro sigma a
    rw [integerUnitsPrincipalUnitsQuotientMap,
      galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smul,
      galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure_smul,
      galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure_mk]
  · intro a
    constructor
    · intro ha
      refine ⟨⟨a, ?_⟩, rfl⟩
      exact (integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff L n a).1 ha
    · rintro ⟨v, rfl⟩
      exact (integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff L n
        v).2 v.2

/-- A Galois-fixed actual integer unit descends to a base integer unit.  This
is valuation-ring descent, not an assumed comparison of fixed parts. -/
private theorem exists_integerUnit_map_eq_of_galoisGroup_fixed [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (a : 𝒪[L]ˣ)
    (ha : letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
      ∀ sigma : Gal(L / K), sigma • a = a) :
    ∃ b : 𝒪[K]ˣ, integerUnitsMapOfValuationExtension K L b = a := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  have hfixed : ∀ sigma : Gal(L / K),
      sigma (((a : 𝒪[L]) : L)) = ((a : 𝒪[L]) : L) := by
    intro sigma
    simpa [galoisGroupIntegerRingEquivOfIsIntegralClosure_apply] using (congrArg (fun z : 𝒪[L]ˣ => ((z : 𝒪[L]) : L)) (ha sigma))
  rcases ((IsGalois.mem_range_algebraMap_iff_fixed
    (((a : 𝒪[L]) : L))).2 hfixed) with ⟨y, hy⟩
  have hy0 : y ≠ 0 := by
    intro hzero
    have : ((a : 𝒪[L]) : L) = 0 := by
      rw [← hy, hzero, map_zero]
    exact a.ne_zero (Subtype.ext this)
  have hy_mem : ValuativeRel.valuation K y ≤ 1 := by
    apply (Valuation.HasExtension.val_map_le_one_iff
      (vR := ValuativeRel.valuation K) (vA := ValuativeRel.valuation L) y).1
    rw [hy]
    exact a.val.property
  have hy_inv_mem : ValuativeRel.valuation K y⁻¹ ≤ 1 := by
    apply (Valuation.HasExtension.val_map_le_one_iff
      (vR := ValuativeRel.valuation K) (vA := ValuativeRel.valuation L) y⁻¹).1
    rw [map_inv₀, hy]
    have hinv :=
      a.inv.property
    rw [(eq_inv_of_mul_eq_one_right (congrArg (fun z : 𝒪[L] => (z : L)) a.val_inv))] at hinv
    exact hinv
  let b : 𝒪[K]ˣ :=
    { val := ⟨y, hy_mem⟩
      inv := ⟨y⁻¹, hy_inv_mem⟩
      val_inv := by ext; simp [hy0]
      inv_val := by ext; simp [hy0] }
  refine ⟨b, ?_⟩
  apply Units.ext
  apply Subtype.ext
  exact hy

end

/-- The normal-basis construction, restricted to its actual
integer-unit conclusion `h(G,𝒪_Lˣ)=1`. -/
private theorem integerUnits_herbrandQuotient_eq_one
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    (g : Gal(L / K)) (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    ∃ hU : HerbrandQuotientDefined Gal(L / K) 𝒪[L]ˣ g,
      @herbrandQuotient Gal(L / K) 𝒪[L]ˣ _ _ _
        (galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L)
        g hU.1 hU.2 = 1 := by
  rcases exists_chosenNormalBasisPrincipalUnitSubgroup (K := K) (L := L) with
    ⟨cV, hcV⟩
  rcases exists_chosenNormalBasisPrincipalUnit_herbrand_subsingleton
      (K := K) (L := L) g hg with ⟨cH, hcH⟩
  rcases exists_integerUnits_herbrandQuotient_eq_one_of_large_chosenNormalBasisLevel
      (K := K) (L := L) with ⟨cU, hcU⟩
  let n := max cV (max cH cU)
  have hrest := le_max_right cV (max cH cU)
  rcases hcV n (le_max_left cV (max cH cU)) with ⟨V, hV, _⟩
  let := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  let := chosenNormalBasisIntegerUnitsQuotMulDistribMulAction K L n V hV
  have hcoh := hcH n (le_trans (le_max_left cH cU) hrest) V hV
  exact hcU n (le_trans (le_max_right cH cU) hrest) V hV g hg hcoh.1 hcoh.2

private theorem herbrandHMinusOne_subsingleton_of_h0_subsingleton_of_quotient_eq_one
    (G A : Type u) [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A] (g : G)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A g)]
    [Subsingleton (HerbrandH0 G A)]
    (hquot : herbrandQuotient (G := G) (A := A) g = 1) :
    Subsingleton (HerbrandHMinusOne G A g) := by
  have hcardQ : (1 : ℚ) = Nat.card (HerbrandHMinusOne G A g) := by
    unfold herbrandQuotient at hquot
    rw [Nat.card_unique] at hquot
    exact (div_eq_one_iff_eq (Nat.cast_ne_zero.mpr
      (Finite.card_pos).ne')).1 hquot
  refine (Nat.card_eq_one_iff_unique.mp ?_).1
  exact_mod_cast hcardQ.symm

/-- The unramified unit-cohomology theorem for the actual integer-unit module: both low-degree Tate
groups are trivial in an unramified extension. -/
theorem unramified_integerUnits_herbrand_subsingleton
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [IsUnramifiedValuedExtension K L]
    (g : Gal(L / K)) (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    Subsingleton (HerbrandH0 Gal(L / K) 𝒪[L]ˣ) ∧
      Subsingleton (HerbrandHMinusOne Gal(L / K) 𝒪[L]ˣ g) := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  rcases integerUnits_herbrandQuotient_eq_one K L g hg with
    ⟨hU, hUone⟩
  let : Finite (HerbrandH0 Gal(L / K) 𝒪[L]ˣ) := hU.1
  let : Finite (HerbrandHMinusOne Gal(L / K) 𝒪[L]ˣ g) := hU.2
  have hfixed : fixedSubgroup Gal(L / K) 𝒪[L]ˣ ≤
      tateNormSubgroup Gal(L / K) 𝒪[L]ˣ := by
    intro a ha
    rcases exists_integerUnit_map_eq_of_galoisGroup_fixed K L a ha with
      ⟨b, hb⟩
    rcases normIntegerUnits_surjective_unramified_of_isIntegralClosure K L b with
      ⟨z, hz⟩
    refine ⟨z, ?_⟩
    calc
      tateNorm Gal(L / K) 𝒪[L]ˣ z =
          Finset.univ.prod (fun sigma : Gal(L / K) =>
            Units.mapEquiv
              (galoisGroupIntegerRingEquivOfIsIntegralClosure K L sigma).toMulEquiv z) := rfl
      _ = integerUnitsMapOfValuationExtension K L (normIntegerUnits K L z) :=
        (integerUnitsMap_normIntegerUnits_eq_galoisGroup_prod_of_isIntegralClosure K L z).symm
      _ = integerUnitsMapOfValuationExtension K L b := by rw [hz]
      _ = a := hb
  let : Subsingleton (HerbrandH0 Gal(L / K) 𝒪[L]ˣ) :=
    herbrandH0_subsingleton_of_fixed_le_tateNormSubgroup hfixed
  exact ⟨inferInstance,
    herbrandHMinusOne_subsingleton_of_h0_subsingleton_of_quotient_eq_one
      Gal(L / K) 𝒪[L]ˣ g hUone⟩

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]] [IsUnramifiedValuedExtension K L]

/-- The unramified unit-cohomology theorem for the actual `n`-th principal-unit module.  The proof
uses the actual sequence `1 → U_L^n → 𝒪_Lˣ → 𝒪_Lˣ/U_L^n → 1`,
Herbrand-quotient multiplicativity, and the actual unramified norm lifting. -/
private theorem unramified_principalUnits_herbrand_subsingleton
    (n : Nat) (hn : 1 ≤ n) (g : Gal(L / K))
    (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) :
    letI := galoisGroupPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
    Subsingleton (HerbrandH0 Gal(L / K) (principalUnits L n)) ∧
      Subsingleton
        (HerbrandHMinusOne Gal(L / K) (principalUnits L n) g) := by
  let := galoisGroupPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  let := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure
    K L n
  rcases integerUnits_herbrandQuotient_eq_one K L g hg with
    ⟨hU, hUone⟩
  let :=
    integerUnitsModPrincipalUnitsAtLevel_finite_of_isNonarchimedeanLocalField L n
  let hQ : HerbrandQuotientDefined Gal(L / K)
      (IntegerUnitsModPrincipalUnitsAtLevel L n) g :=
    ⟨inferInstance, inferInstance⟩
  let hseq := principalUnitsIntegerUnits_shortExact K L n
  let hP :=
    herbrandQuotientDefined_left_of_middle_right

      (principalUnitsIntegerUnitsInclusion L n)
      (integerUnitsPrincipalUnitsQuotientMap L n)
      hseq.1 hseq.2.1 hseq.2.2.1 hseq.2.2.2.1 hseq.2.2.2.2
      g hg hU hQ
  let := hU.1
  let := hU.2
  let := hQ.1
  let := hQ.2
  let := hP.1
  let := hP.2
  have hfixed : fixedSubgroup Gal(L / K) (principalUnits L n) ≤
      tateNormSubgroup Gal(L / K) (principalUnits L n) := by
    intro a ha
    have haUnits : ∀ sigma : Gal(L / K),
        letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
        sigma • ((a : principalUnits L n) : 𝒪[L]ˣ) =
          ((a : principalUnits L n) : 𝒪[L]ˣ) := fun sigma => congrArg (fun z : principalUnits L n => (z : 𝒪[L]ˣ)) (ha sigma)
    rcases exists_integerUnit_map_eq_of_galoisGroup_fixed K L a haUnits with
      ⟨b, hb⟩
    let bP : principalUnits K n := ⟨b, (principalUnits_of_integerUnitsMap_mem_principalUnits_of_unramifiedValuation
      K L n (by rw [hb]; exact a.2))⟩
    rcases principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_surjective
        K L n hn bP with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    calc
      _ =
          Finset.univ.prod (fun sigma : Gal(L / K) =>
            galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n sigma z) := rfl
      _ = principalUnitsNormExtensionSideOfIsIntegralClosure K L n z :=
        (principalUnitsNormExtensionSideOfIsIntegralClosure_eq_galoisGroup_prod
          K L n z).symm
      _ = principalUnitsMapOfUnramifiedValuation K L n
          (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n z) :=
        (principalUnitsMap_normOfUnramifiedValuationOfIsIntegralClosure_eq_normExtensionSide
          K L n z).symm
      _ = principalUnitsMapOfUnramifiedValuation K L n bP := by rw [hz]
      _ = a := (by
        apply Subtype.ext
        exact hb)
  let :=
    herbrandH0_subsingleton_of_fixed_le_tateNormSubgroup hfixed
  refine ⟨inferInstance,
    herbrandHMinusOne_subsingleton_of_h0_subsingleton_of_quotient_eq_one
      Gal(L / K) (principalUnits L n) g ?_⟩
  have hmul := herbrandQuotient_multiplicative_of_shortExact

    (principalUnitsIntegerUnitsInclusion L n)
    (integerUnitsPrincipalUnitsQuotientMap L n)
    hseq.1 hseq.2.1 hseq.2.2.1 hseq.2.2.2.1 hseq.2.2.2.2 g hg
  rw [hUone, (integerUnitsModPrincipalUnitsAtLevel_herbrandQuotient_eq_one_of_isNonarchimedeanLocalField
    K L n g hg), mul_one] at hmul
  exact hmul.symm

/-- Generator-explicit form of the unramified unit-cohomology theorem.  The canonical
endpoint below supplies the canonical unramified arithmetic Frobenius. -/
theorem unramified_units_tateCohomology_and_norm_surjective_for_generator
    (g : Gal(L / K)) (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    (Subsingleton (HerbrandH0 Gal(L / K) 𝒪[L]ˣ) ∧
      Subsingleton (HerbrandHMinusOne Gal(L / K) 𝒪[L]ˣ g)) ∧
      (∀ n : Nat, 1 ≤ n →
        letI := galoisGroupPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
        Subsingleton (HerbrandH0 Gal(L / K) (principalUnits L n)) ∧
          Subsingleton
            (HerbrandHMinusOne Gal(L / K) (principalUnits L n) g)) ∧
      MonoidHom.range (normIntegerUnits K L) = ⊤ ∧
      ∀ n : Nat, 1 ≤ n → MonoidHom.range
        (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n) = ⊤ := by
  refine ⟨unramified_integerUnits_herbrand_subsingleton K L g hg, ?_,
    MonoidHom.range_eq_top_of_surjective (normIntegerUnits K L)
      (normIntegerUnits_surjective_unramified_of_isIntegralClosure K L), ?_⟩
  · intro n hn
    exact unramified_principalUnits_herbrand_subsingleton K L n hn g hg
  · intro n hn
    exact MonoidHom.range_eq_top_of_surjective
      (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n)
      (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_surjective
        K L n hn)

end LocalClassFieldTheory

end
