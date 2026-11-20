module

public import NormalizerLean.Basic

@[expose] public section

/-! Inside Γ₀(N), the subgroup Γ_Δ(N) is the preimage of Δ under the lower-right-entry
homomorphism to the units modulo N. -/

open Matrix CongruenceSubgroup

namespace NormalizerLean

variable {N : ℕ} {Δ : Subgroup (ZMod N)ˣ}

lemma delta_le : GammaDelta N Δ ≤ Gamma0 N := fun _ h => h.1

lemma delta_subgroupOf : (GammaDelta N Δ).subgroupOf (Gamma0 N) = Δ.comap (Gamma0Map N).toHomUnits := by
  ext x
  let f := (Gamma0Map N).toHomUnits
  change (_ ∧ ∃ u ∈ Δ, (u : ZMod N) = (f x : ZMod N)) ↔ f x ∈ Δ
  simp [x.property, Units.val_inj]

lemma gamma0_normalizes : Gamma0R N ≤ NormG (GammaDeltaR N Δ) := by
  apply le_trans (Subgroup.map_mono _) (Subgroup.le_normalizer_map _)
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer delta_le).mp
  rw [delta_subgroupOf]; infer_instance

lemma delta_index [NeZero N] : (GammaDeltaR N Δ).relIndex (Gamma0R N) = Δ.index := by
  rw [GammaDeltaR, toR, Gamma0R, Subgroup.relIndex_map_map_of_injective _ _ SpecialLinearGroup.map_intCast_injective, Subgroup.relIndex, delta_subgroupOf]
  apply Subgroup.index_comap_of_surjective
  intro u
  obtain ⟨a, b, h⟩ := lift_unit u
  exact ⟨⟨mkSL _ _ _ _ h, gamma0_dvd.mpr dvd_rfl⟩, Units.ext (by simp [Gamma0Map, mkSL])⟩

end NormalizerLean
