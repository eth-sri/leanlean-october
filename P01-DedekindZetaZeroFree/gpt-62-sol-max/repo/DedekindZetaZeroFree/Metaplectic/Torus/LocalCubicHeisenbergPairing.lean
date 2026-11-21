module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.FilteredCubicCharacterCounts
public import DedekindZetaZeroFree.Arithmetic.LocalFields.UnitCubeIndex
public import DedekindZetaZeroFree.Arithmetic.LocalFields.MultiplicativeCubeIndex

@[expose] public section

namespace DedekindZetaZeroFree.KPLocalTorus

open scoped Valued
open ValuativeRel

abbrev CubeClasses (K : Type*) [CommGroup K] := K ⧸ CubicCharacters.cubes K

noncomputable def inverseThreeModule (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] : ℕ :=
  (Nat.card 𝓀[K]) ^ (IsDiscreteValuationRing.addVal 𝒪[K] (3 : 𝒪[K])).toNat

theorem finite_cubeClasses (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ζ : K) (hζ : IsPrimitiveRoot ζ 3) : Finite (CubeClasses Kˣ) := by
  exact ClassFieldTheory.powerClassGroup_finite K 3 (by norm_num)

private theorem integral_root (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    ∃ z : 𝒪[K], IsPrimitiveRoot z 3 := by
  have hv : valuation K ζ = 1 := by
    have hp : (valuation K ζ) ^ 3 = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    exact (pow_eq_one_iff_of_nonneg zero_le (by decide)).mp hp
  let z : 𝒪[K] := ⟨ζ, hv.le⟩
  exact ⟨z, hζ.of_map_of_injective (f := (valuation K).integer.subtype)
    Subtype.val_injective⟩

open KPCubicUnitIndices

theorem card_cubeClasses (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    Nat.card (CubeClasses Kˣ) = 9 * inverseThreeModule K := by
  obtain ⟨z, hz⟩ := integral_root K ζ hζ
  have hlog := KPCubicHaarTransport.log_integer K (3 : 𝒪[K]) (by norm_num)
  have hmodule : KPCubicHaarTransport.abs K (3 : K) =
      ((inverseThreeModule K : ℕ) : ℝ)⁻¹ := by
    simp only [KPCubicHaarTransport.abs, if_neg (show (3 : K) ≠ 0 by norm_num)]
    rw [show (3 : K) = ((3 : 𝒪[K]) : K) from rfl, hlog]
    simp [inverseThreeModule, residueCard, zpow_neg, zpow_natCast]
  have hc := KPCubicHaarTransport.unit_cube_index K z hz
  rw [hmodule, div_inv_eq_mul] at hc
  have hnat : (cubeUnits K).index = 3 * inverseThreeModule K := by
    exact_mod_cast hc
  change (CubicCharacters.cubes Kˣ).index = _
  rw [CubicCharacters.cubes, KPCubicHaarTransport.field_cube_index K, hnat]
  omega

theorem inverseThreeModule_eq_one_of_tame (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (htame : (3 : 𝒪[K]) ∉ 𝓂[K]) : inverseThreeModule K = 1 := by
  have hunit : IsUnit (3 : 𝒪[K]) := by
    by_contra h
    exact htame ((IsLocalRing.mem_maximalIdeal (3 : 𝒪[K])).mpr (mem_nonunits_iff.mpr h))
  have hval : IsDiscreteValuationRing.addVal 𝒪[K] (3 : 𝒪[K]) = 0 :=
    IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hunit
  simp [inverseThreeModule, hval]

theorem card_cubeClasses_tame (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ζ : K) (hζ : IsPrimitiveRoot ζ 3) (htame : (3 : 𝒪[K]) ∉ 𝓂[K]) :
    Nat.card (CubeClasses Kˣ) = 9 := by
  rw [card_cubeClasses K ζ hζ, inverseThreeModule_eq_one_of_tame K htame, mul_one]

end DedekindZetaZeroFree.KPLocalTorus
