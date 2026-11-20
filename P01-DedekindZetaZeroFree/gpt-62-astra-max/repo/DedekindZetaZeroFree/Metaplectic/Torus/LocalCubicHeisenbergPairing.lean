module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.FilteredCubicCharacterCounts
public import DedekindZetaZeroFree.Arithmetic.LocalFields.UnitCubeIndex
public import DedekindZetaZeroFree.Arithmetic.LocalFields.MultiplicativeCubeIndex

@[expose] public section

namespace DedekindZetaZeroFree.KPLocalTorus

open scoped Valued
open ValuativeRel

abbrev CubeClasses (K : Type*) [CommGroup K] := K ⧸ CubicCharacters.cubes K

section

variable (K : Type*) [Field K]

noncomputable def inverseThreeModule [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] : ℕ :=
  (Nat.card 𝓀[K]) ^ (IsDiscreteValuationRing.addVal 𝒪[K] (3 : 𝒪[K])).toNat

theorem finite_cubeClasses [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ζ : K) (hζ : IsPrimitiveRoot ζ 3) : Finite (CubeClasses Kˣ) := ClassFieldTheory.powerClassGroup_finite K 3 (by norm_num)

private theorem integral_root [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    ∃ z : 𝒪[K], IsPrimitiveRoot z 3 := by
  have hv : valuation K ζ = 1 := by
    have hp : (valuation K ζ) ^ 3 = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    exact (pow_eq_one_iff_of_nonneg zero_le (by decide)).mp hp
  exact ⟨(⟨ζ, hv.le⟩), hζ.of_map_of_injective (f := (valuation K).integer.subtype)
    Subtype.val_injective⟩

end

open KPCubicUnitIndices

private alias log_integer := DedekindZetaZeroFree.KPCubicHaarTransport.UnitCubeIndex.log_integer

variable (K : Type*) [Field K]

theorem card_cubeClasses [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    Nat.card (CubeClasses Kˣ) = 9 * inverseThreeModule K := by
  obtain ⟨z, hz⟩ := integral_root K ζ hζ
  have hmodule : KPCubicHaarTransport.abs K (3 : K) =
      ((inverseThreeModule K : ℕ) : ℝ)⁻¹ := by
    simp only [KPCubicHaarTransport.abs, if_neg (show (3 : K) ≠ 0 by norm_num)]
    rw [show (3 : K) = ((3 : 𝒪[K]) : K) from rfl, (log_integer K (3 : 𝒪[K]) (by norm_num))]
    simp [inverseThreeModule, residueCard, zpow_neg, zpow_natCast]
  have hc := KPCubicHaarTransport.unit_cube_index K z hz
  rw [hmodule, div_inv_eq_mul] at hc
  have hnat : (cubeUnits K).index = 3 * inverseThreeModule K := by
    exact_mod_cast hc
  change (CubicCharacters.cubes Kˣ).index = _
  rw [CubicCharacters.cubes, KPCubicHaarTransport.field_cube_index K, hnat]
  omega

theorem inverseThreeModule_eq_one_of_tame [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (htame : (3 : 𝒪[K]) ∉ 𝓂[K]) : inverseThreeModule K = 1 := by
  have hunit : IsUnit (3 : 𝒪[K]) := by
    by_contra h
    exact htame ((IsLocalRing.mem_maximalIdeal (3 : 𝒪[K])).mpr (mem_nonunits_iff.mpr h))
  simp [inverseThreeModule, (IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hunit)]

theorem card_cubeClasses_tame [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ζ : K) (hζ : IsPrimitiveRoot ζ 3) (htame : (3 : 𝒪[K]) ∉ 𝓂[K]) :
    Nat.card (CubeClasses Kˣ) = 9 := by
  rw [card_cubeClasses K ζ hζ, inverseThreeModule_eq_one_of_tame K htame, mul_one]

end DedekindZetaZeroFree.KPLocalTorus
