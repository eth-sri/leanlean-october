module

public import NormalizerDelta.Basic

@[expose] public section

open Matrix MatrixGroups

namespace NormalizerLean

variable {N : ℕ}

/-- The lower-right entry modulo the level, as a unit. -/
abbrev unitMap (N : ℕ) : CongruenceSubgroup.Gamma0 N →* (ZMod N)ˣ :=
  (CongruenceSubgroup.Gamma0Map N).toHomUnits

private theorem unitMap_surjective [NeZero N] : Function.Surjective (unitMap N) := by
  intro u
  obtain ⟨x, y, hdet⟩ := exists_lift_unit u
  refine ⟨⟨mkSL _ _ _ _ hdet, CongruenceSubgroup.Gamma0_mem.2 (by simp [mkSL])⟩,
    Units.ext ?_⟩
  change (((u : ZMod N).val : ℤ) : ZMod N) = _
  simp

private theorem GammaDelta_subgroupOf (Δ : Subgroup (ZMod N)ˣ) :
    (GammaDelta N Δ).subgroupOf (CongruenceSubgroup.Gamma0 N) = Δ.comap (unitMap N) := by
  ext γ
  constructor
  · rintro ⟨-, u, hu, h⟩
    change unitMap N γ ∈ Δ
    exact (Units.ext h : u = unitMap N γ) ▸ hu
  · exact fun h => ⟨γ.2, unitMap N γ, h, rfl⟩

theorem Gamma0R_le_normG_GammaDeltaR (N : ℕ) (Δ : Subgroup (ZMod N)ˣ) :
    Gamma0R N ≤ NormG (GammaDeltaR N Δ) := by
  have : ((GammaDelta N Δ).subgroupOf (CongruenceSubgroup.Gamma0 N)).Normal := by
    rw [GammaDelta_subgroupOf]
    infer_instance
  exact (Subgroup.map_mono (Subgroup.le_normalizer_of_normal_subgroupOf GammaDelta_le_Gamma0)).trans
    (Subgroup.le_normalizer_map _)

theorem relIndex_GammaDeltaR_Gamma0R (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    (GammaDeltaR N Δ).relIndex (Gamma0R N) = Δ.index := by
  rw [GammaDeltaR, toR, Gamma0R,
    Subgroup.relIndex_map_map_of_injective _ _ SpecialLinearGroup.map_intCast_injective,
    Subgroup.relIndex, GammaDelta_subgroupOf, Subgroup.index_comap_of_surjective _ unitMap_surjective]

end NormalizerLean
