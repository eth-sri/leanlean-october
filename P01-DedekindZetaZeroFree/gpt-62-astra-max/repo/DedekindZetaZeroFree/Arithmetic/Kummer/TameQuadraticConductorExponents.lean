module

public import DedekindZetaZeroFree.Arithmetic.Kummer.QuadraticRadicalCharacterLaws

@[expose] public section

namespace DedekindZetaZeroFree.RMTameQuadraticExponent

noncomputable section
universe u v w
open scoped NumberField Classical ValuativeRel WithZero
open IsDedekindDomain ValuativeRel LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (F : Type) [Field F] [NumberField F]

def radicalOrder (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) : ℤ :=
  -WithZero.log (v.valuation F (x : F))

variable (q : HeightOneSpectrum (𝓞 F))
local instance : ValuativeRel (q.adicCompletion F) := ClassFieldTheory.finitePlaceCompletionValuativeRel F q
local instance : IsNonarchimedeanLocalField (q.adicCompletion F) := ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F q
 theorem ints_eq : (valuation (q.adicCompletion F)).integer = (q.adicCompletionIntegers F).toSubring := by
  letI : (Valued.v : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  ext x
  exact (ValuativeRel.isEquiv (valuation (q.adicCompletion F)) (Valued.v)).le_one_iff_le_one

private theorem iso_unique (e : WithZero (Multiplicative ℤ) ≃*o WithZero (Multiplicative ℤ)) : e = OrderMonoidIso.refl _ := by
  have hf : OrderMonoidIso.withZero.symm e = OrderMonoidIso.refl (Multiplicative ℤ) := Subsingleton.elim _ _
  have := congrArg OrderMonoidIso.withZero hf
  have hh : e = OrderMonoidIso.withZero (OrderMonoidIso.refl (Multiplicative ℤ)) := by simpa using this
  exact hh.trans (by ext x; cases x <;> rfl)

alias TameQuadraticConductorExponents.iso_unique := iso_unique
private theorem val_eq (x : q.adicCompletion F) :
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (q.adicCompletion F) (valuation (q.adicCompletion F) x) = Valued.v x := by
  let ν : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  letI : ν.Compatible := Valuation.Compatible.ofValuation _
  let e := (ValuativeRel.ValueGroupWithZero.orderMonoidIso ν).trans
    (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt ν)
  have he : e = IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (q.adicCompletion F) := by
    ext a
    simpa using (congrArg (fun f => f (e a)) (iso_unique (e.symm.trans (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (q.adicCompletion F))))).symm
  rw [← he]
  change Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt ν
    (ValuativeRel.ValueGroupWithZero.orderMonoidIso ν (valuation (q.adicCompletion F) x)) = _
  rw [ValuativeRel.ValueGroupWithZero.orderMonoidIso_valuation_eq_restrict₀]
  exact Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
    (q.valuedAdicCompletion_surjective F) x

alias TameQuadraticConductorExponents.val_eq := val_eq
private theorem order_eq (x : Fˣ) :
    -(valuationMap (q.adicCompletion F) (Additive.ofMul (Units.map (algebraMap F (q.adicCompletion F)).toMonoidHom x))) = radicalOrder F q x := by
  rw [valuationMap_apply, v_apply, WithZero.toAdd_unzero_eq_log]
  rw [val_eq]
  exact congrArg (fun a : WithZero (Multiplicative ℤ) => -WithZero.log a)
    (q.valuedAdicCompletion_eq_valuation' (x : F))
 def intEquiv : (valuation (q.adicCompletion F)).integer ≃+* q.adicCompletionIntegers F :=
  RingEquiv.subringCongr (ints_eq F q)
private theorem tame (hodd : ringChar (IsLocalRing.ResidueField (q.adicCompletionIntegers F)) ≠ 2) :
    valuation (q.adicCompletion F) (2 : q.adicCompletion F) = 1 := by
  have hu : IsUnit (2 : q.adicCompletionIntegers F) := by
    apply isUnit_of_map_unit (IsLocalRing.residue (q.adicCompletionIntegers F)) (2 : q.adicCompletionIntegers F)
    rw [map_ofNat]
    exact isUnit_iff_ne_zero.mpr (CharP.cast_ne_zero_of_ne_of_prime
      (IsLocalRing.ResidueField (q.adicCompletionIntegers F)) Nat.prime_two hodd)
  have hu' : IsUnit (2 : (valuation (q.adicCompletion F)).integer) := by
    have hh := hu.map (intEquiv F q).symm.toRingHom
    rw [map_ofNat] at hh
    exact hh
  exact (Valuation.integer.integers (valuation (q.adicCompletion F))).isUnit_iff_valuation_eq_one.mp hu'

variable (h12 : (primitiveRoots 12 F).Nonempty)
private theorem lambda_tame (x : Fˣ)
    (hodd : ringChar (IsLocalRing.ResidueField (q.adicCompletionIntegers F)) ≠ 2)
    (u : (valuation (q.adicCompletion F)).integerˣ) :
    RMKummerCharacterAPI.lambda F h12 x q (integerUnitsToFieldUnits (q.adicCompletion F) u) =
      (rmKummerQuadraticRootsComplexMap F h12 (q.adicCompletion F)
        (KummerTheory.nthRootsSubgroupEquivRootsOfUnity (q.adicCompletion F) 2
          (LocalClassFieldTheory.Kummer.localTamePowerResidueSymbol (q.adicCompletion F) 2
            (tame F q hodd) (RMKummerLocalHilbertComparison.localPrimitiveTwo F h12 q) u))) ^
          (-radicalOrder F q x) := by
  rw [RMKummerLocalHilbertComparison.lambda_eq_inverse_localHilbertSymbol]
  unfold ClassFieldTheory.localHilbertSymbol
  have hh := LocalClassFieldTheory.Kummer.localHilbertSymbol_tame_formula (q.adicCompletion F) 2
    (tame F q hodd) (RMKummerLocalHilbertComparison.localPrimitiveTwo F h12 q) u
      (Units.map (algebraMap F (q.adicCompletion F)).toMonoidHom x)
  erw [hh]
  rw [order_eq F q x]
  simp only [map_zpow]
  erw [map_zpow]
  rw [zpow_neg]
  rfl

private theorem local_residue_odd
    (hodd : ringChar (IsLocalRing.ResidueField (q.adicCompletionIntegers F)) ≠ 2) :
    ringChar (IsLocalRing.ResidueField (valuation (q.adicCompletion F)).integer) ≠ 2 := by
  have hn : (2 : IsLocalRing.ResidueField (valuation (q.adicCompletion F)).integer) ≠ 0 := by
    intro hh
    have he := congrArg (IsLocalRing.ResidueField.mapEquiv (intEquiv F q)) hh
    simp only [map_ofNat, map_zero] at he
    exact CharP.cast_ne_zero_of_ne_of_prime
      (IsLocalRing.ResidueField (q.adicCompletionIntegers F)) Nat.prime_two hodd he
  intro he
  exact hn (by simpa only [he, Nat.cast_ofNat] using CharP.cast_eq_zero (IsLocalRing.ResidueField (valuation (q.adicCompletion F)).integer) (ringChar (IsLocalRing.ResidueField (valuation (q.adicCompletion F)).integer)))
private theorem even_units (x : Fˣ)
    (hodd : ringChar (IsLocalRing.ResidueField (q.adicCompletionIntegers F)) ≠ 2)
    (hev : Even (radicalOrder F q x))
    (u : (valuation (q.adicCompletion F)).integerˣ) :
    RMKummerCharacterAPI.lambda F h12 x q (integerUnitsToFieldUnits (q.adicCompletion F) u) = 1 := by
  rw [lambda_tame F q h12 x hodd u]
  obtain ⟨j, hj⟩ := hev
  have hj' : -radicalOrder F q x = 2 * (-j) := by omega
  rw [hj', zpow_mul]
  have hz := rmKummerQuadraticRootsComplexMap_pow_two F h12 (q.adicCompletion F)
    (KummerTheory.nthRootsSubgroupEquivRootsOfUnity (q.adicCompletion F) 2
      (LocalClassFieldTheory.Kummer.localTamePowerResidueSymbol (q.adicCompletion F) 2
        (tame F q hodd) (RMKummerLocalHilbertComparison.localPrimitiveTwo F h12 q) u))
  simp [hz]

private theorem detecting_unit
    (hodd : ringChar (IsLocalRing.ResidueField (q.adicCompletionIntegers F)) ≠ 2) :
    ∃ u : (valuation (q.adicCompletion F)).integerˣ,
      LocalClassFieldTheory.Kummer.localTamePowerResidueSymbol (q.adicCompletion F) 2
        (tame F q hodd) (RMKummerLocalHilbertComparison.localPrimitiveTwo F h12 q) u ≠ 1 := by
  let K := q.adicCompletion F
  letI : Fintype (IsLocalRing.ResidueField (valuation K).integer) := Fintype.ofFinite _
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (local_residue_odd F q hodd)
  let b := Units.mk0 a (by rintro rfl; exact ha (IsSquare.zero))
  obtain ⟨u, hu⟩ := integerUnitsToResidueUnits_surjective K b
  refine ⟨u, ?_⟩
  intro hs
  have hr := LocalClassFieldTheory.Kummer.localNthRootsReductionEquiv_localTamePowerResidueSymbol K 2
    (tame F q hodd) (RMKummerLocalHilbertComparison.localPrimitiveTwo F h12 q) u
  rw [hs, map_one, hu] at hr
  obtain ⟨c, hc⟩ := (AlgebraicNumberTheory.PowerResidueSymbols.finiteFieldPowerResidueSymbol_eq_one_iff _ 2 _ b).mp hr.symm
  apply ha
  refine ⟨c, ?_⟩
  have hh := congrArg Units.val hc
  change c ^ (2 : ℕ) = a at hh
  simpa only [pow_two] using hh.symm

private theorem odd_unit_nontrivial (x : Fˣ)
    (hodd : ringChar (IsLocalRing.ResidueField (q.adicCompletionIntegers F)) ≠ 2)
    (ho : Odd (radicalOrder F q x)) :
    ∃ u : (valuation (q.adicCompletion F)).integerˣ,
      RMKummerCharacterAPI.lambda F h12 x q (integerUnitsToFieldUnits (q.adicCompletion F) u) ≠ 1 := by
  obtain ⟨u, hu⟩ := detecting_unit F q h12 hodd
  refine ⟨u, ?_⟩
  rw [lambda_tame F q h12 x hodd u]
  let z := KummerTheory.nthRootsSubgroupEquivRootsOfUnity (q.adicCompletion F) 2
    (LocalClassFieldTheory.Kummer.localTamePowerResidueSymbol (q.adicCompletion F) 2
      (tame F q hodd) (RMKummerLocalHilbertComparison.localPrimitiveTwo F h12 q) u)
  let c := rmKummerQuadraticRootsComplexMap F h12 (q.adicCompletion F) z
  obtain ⟨j, hj⟩ := ho
  have hj' : -radicalOrder F q x = 2 * (-j - 1) + 1 := by omega
  rw [hj', zpow_add, zpow_mul, zpow_ofNat, (rmKummerQuadraticRootsComplexMap_pow_two F h12 _ z), one_zpow, zpow_one, one_mul]
  intro hh
  exact hu ((KummerTheory.nthRootsSubgroupEquivRootsOfUnity (q.adicCompletion F) 2).injective
    (((rmKummerQuadraticRootsComplexMap_injective F h12 (q.adicCompletion F))
      (hh.trans (map_one _).symm)).trans (map_one _).symm))
private theorem inclusion_mem (u : (valuation (q.adicCompletion F)).integerˣ) :
    integerUnitsToFieldUnits (q.adicCompletion F) u ∈ (q.adicCompletionIntegers F).units := by
  constructor
  · rw [← ints_eq F q]
    simp
  · rw [← ints_eq F q]
    exact ((u⁻¹ : (valuation (q.adicCompletion F)).integerˣ) : (valuation (q.adicCompletion F)).integer).property
private theorem exists_intunit (t : (q.adicCompletion F)ˣ) (ht : t ∈ (q.adicCompletionIntegers F).units) :
    ∃ u : (valuation (q.adicCompletion F)).integerˣ, integerUnitsToFieldUnits (q.adicCompletion F) u = t := by
  exact ⟨(Units.map (intEquiv F q).symm.toRingHom.toMonoidHom
    ((q.adicCompletionIntegers F).toSubmonoid.unitsEquivUnitsType (⟨t, ht⟩))), Units.ext rfl⟩
private theorem principal_trivial (x : Fˣ)
    (hodd : ringChar (IsLocalRing.ResidueField (q.adicCompletionIntegers F)) ≠ 2)
    (t : (q.adicCompletion F)ˣ) (ht : t ∈ ClassFieldTheory.rayLocalHigherUnitGroup q 1) :
    RMKummerCharacterAPI.lambda F h12 x q t = 1 := by
  obtain ⟨w, hw, hc⟩ := (ClassFieldTheory.mem_rayLocalHigherUnitGroup_iff q 1 t).mp ht
  let u := Units.map (intEquiv F q).symm.toRingHom.toMonoidHom w
  have hu : integerUnitsToFieldUnits (q.adicCompletion F) u = t := by
    apply Units.ext
    exact congrArg Units.val hw
  have hc' : IsLocalRing.residue (q.adicCompletionIntegers F) w = 1 := by
    exact (Ideal.Quotient.mk_eq_one_iff_sub_mem (w : q.adicCompletionIntegers F)).mpr (by simpa only [pow_one] using hc)
  have hu' : integerUnitsToResidueUnits (q.adicCompletion F) u = 1 := by
    apply Units.ext
    change IsLocalRing.residue (valuation (q.adicCompletion F)).integer u = 1
    apply (IsLocalRing.ResidueField.mapEquiv (intEquiv F q)).injective
    letI : IsLocalHom (intEquiv F q).toRingHom := IsLocalHom.of_surjective _ (intEquiv F q).surjective
    change IsLocalRing.ResidueField.map (intEquiv F q).toRingHom
      (IsLocalRing.residue (valuation (q.adicCompletion F)).integer ((intEquiv F q).symm (w : q.adicCompletionIntegers F))) = _
    rw [IsLocalRing.ResidueField.map_residue]
    change IsLocalRing.residue (q.adicCompletionIntegers F)
      ((intEquiv F q) ((intEquiv F q).symm (w : q.adicCompletionIntegers F))) = _
    rw [RingEquiv.apply_symm_apply, map_one]
    exact hc'
  rw [← hu, lambda_tame F q h12 x hodd u]
  have hs : LocalClassFieldTheory.Kummer.localTamePowerResidueSymbol (q.adicCompletion F) 2
      (tame F q hodd) (RMKummerLocalHilbertComparison.localPrimitiveTwo F h12 q) u = 1 := by
    apply (LocalClassFieldTheory.Kummer.localNthRootsReductionEquiv (q.adicCompletion F) 2
      (tame F q hodd) (RMKummerLocalHilbertComparison.localPrimitiveTwo F h12 q)).injective
    rw [map_one]
    have hr := LocalClassFieldTheory.Kummer.localNthRootsReductionEquiv_localTamePowerResidueSymbol (q.adicCompletion F) 2
      (tame F q hodd) (RMKummerLocalHilbertComparison.localPrimitiveTwo F h12 q) u
    rw [hu'] at hr
    erw [map_one] at hr
    exact hr
  rw [hs]
  erw [map_one]
  simp

variable (x : Fˣ) (v : HeightOneSpectrum (𝓞 F))

theorem conductor_exponent_eq_parity
    (hodd : ringChar (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) ≠ 2) :
    idealPrimeExponent v.asIdeal (RMKummerCharacterAPI.m F h12 x) =
      if Odd (radicalOrder F v x) then (1 : ℕ) else 0 := by
        have hleast := RMKummerCharacterAPI.local_conductor F h12 x v
        have hle := hleast.2 (fun t ht => MonoidHom.mem_ker.mpr (principal_trivial F v h12 x hodd t ht))
        by_cases ho : Odd (radicalOrder F v x)
        · rw [if_pos ho]
          have hn : idealPrimeExponent v.asIdeal (RMKummerCharacterAPI.m F h12 x) ≠ 0 := by
            intro he
            obtain ⟨u, hu⟩ := odd_unit_nontrivial F v h12 x hodd ho
            apply hu
            apply RMKummerLeastLocalExponent.lambda_trivial_on_conductor_units F h12 x v _
            rw [he, RMKummerCharacterAPI.higher_units_zero]
            exact inclusion_mem F v u
          omega
        · rw [if_neg ho]
          apply Nat.le_zero.mp
          apply hleast.2
          change ClassFieldTheory.rayLocalHigherUnitGroup v 0 ≤ (RMKummerCharacterAPI.lambda F h12 x v).ker
          rw [RMKummerCharacterAPI.higher_units_zero]
          intro t ht
          obtain ⟨u, rfl⟩ := exists_intunit F v t ht
          exact MonoidHom.mem_ker.mpr (even_units F v h12 x hodd (Int.not_odd_iff_even.mp ho) u)

theorem lambda_eq_one_of_local_square
    (hx : IsSquare (algebraMap F (v.adicCompletion F) (x : F)))
    (t : (v.adicCompletion F)ˣ) :
    RMKummerCharacterAPI.lambda F h12 x v t = 1 := by
  let K := v.adicCompletion F
  have h2 : ((((2 : ℕ+) : ℕ)) : K) ≠ 0 :=
    RMKummerLocalHilbertComparison.localTwo_ne_zero F v
  have hmu : (primitiveRoots (((2 : ℕ+) : ℕ)) K).Nonempty :=
    RMKummerLocalHilbertComparison.localPrimitiveTwo F h12 v
  obtain ⟨y, hy⟩ := hx
  have hyne : y ≠ 0 := by
    intro h
    have h0 : (algebraMap F K) (x : F) = 0 := by rw [hy, h, mul_zero]
    exact x.ne_zero ((algebraMap F K).injective (by simpa using h0))
  let c : Kˣ := Units.mk0 y hyne
  have hb : Units.map (algebraMap F K).toMonoidHom x = c * c := by
    apply Units.ext
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Units.val_mk0]
    exact hy
  have h1 : ClassFieldTheory.localHilbertSymbol K (2 : ℕ+) h2 hmu t
      (Units.map (algebraMap F K).toMonoidHom x) = 1 := by
    rw [hb, ClassFieldTheory.localHilbertSymbol_mul_right]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two]
    exact (ClassFieldTheory.localHilbertSymbol K (2 : ℕ+) h2 hmu t c).property
  rw [RMKummerLocalHilbertComparison.lambda_eq_inverse_localHilbertSymbol F h12 x v t]
  rw [h1]
  rw [show (rmKummerQuadraticRootsComplexMap F h12 K) (1 : rootsOfUnity (((2 : ℕ+) : ℕ)) K) = 1
      from map_one (rmKummerQuadraticRootsComplexMap F h12 K)]
  exact inv_one

end
end DedekindZetaZeroFree.RMTameQuadraticExponent
