module

public import NormalizerDelta.NewmanDelta
public import NormalizerLean.Basic

@[expose] public section

/-!
# §D (rest) and §C: Γ₀(N) normalizes Γ_Δ(N); the index i_Δ; Nor(Γ_Δ(N)) ≤ Nor(Γ₀(N)) and the index

* `Gamma0R_le_normG_GammaDeltaR'`: the lower right entry of g γ g⁻¹ is ≡ γ₁₁ mod N for g, γ ∈ Γ₀(N);
* `relindex_GammaDelta'`: Γ_Δ(N) ∩ Γ₀(N) is the preimage of Δ under the surjection
  Γ₀(N) → (ℤ/N)ˣ, γ ↦ γ₁₁;
* `normG_GammaDeltaR_le_Norm0'`: `newman_delta'` with h_Δ = h(N) gives (8′), and (8′)-matrices normalize Γ₀(N)
  (frozen T1);
* `card_BG_GammaDeltaR'`: Γ_Δ ≤ Γ₀ ≤ Nor(Γ_Δ) ≤ Nor(Γ₀), so [Nor(Γ_Δ) : Γ_Δ] = i_Δ · [Nor(Γ_Δ) : Γ₀(N)],
  and Nor(Γ_Δ)/Γ₀(N) is the set of elements of B(N) normalizing Γ_Δ(N);
* `newman_delta_not_sufficient'`: S₂ at N = 8.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

variable {N : ℕ}

/-! ### Γ₀(N) normalizes Γ_Δ(N) -/

/-- The lower right entry of g γ g⁻¹ mod N, for g, γ ∈ Γ₀(N). -/
theorem conj_entry_11 {g γ : SLℤ} (hg : ((g 1 0 : ℤ) : ZMod N) = 0)
    (hγ : ((γ 1 0 : ℤ) : ZMod N) = 0) :
    (((g * γ * g⁻¹) 1 1 : ℤ) : ZMod N) = ((γ 1 1 : ℤ) : ZMod N) := by
  have hdet : ((g 0 0 : ℤ) : ZMod N) * ((g 1 1 : ℤ) : ZMod N) = 1 := by
    simpa only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one, hg,
      mul_zero, sub_zero] using congrArg (fun x : ℤ => (x : ZMod N)) g.2
  have e : ((g * γ * g⁻¹) 1 1 : ℤ) = (g 1 0 * γ 0 0 + g 1 1 * γ 1 0) * (-g 0 1) +
      (g 1 0 * γ 0 1 + g 1 1 * γ 1 1) * g 0 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]
  rw [e]
  push_cast
  rw [hg, hγ]
  linear_combination ((γ 1 1 : ℤ) : ZMod N) * hdet

theorem conj_mem_GammaDelta {Δ : Subgroup (ZMod N)ˣ} {g γ : SLℤ}
    (hg : g ∈ CongruenceSubgroup.Gamma0 N) (hγ : γ ∈ GammaDelta N Δ) :
    g * γ * g⁻¹ ∈ GammaDelta N Δ := by
  obtain ⟨h0, u, hu, hud⟩ := hγ
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg h0) (Subgroup.inv_mem _ hg), u, hu, ?_⟩
  rw [hud, conj_entry_11 (CongruenceSubgroup.Gamma0_mem.1 hg) (CongruenceSubgroup.Gamma0_mem.1 h0)]

theorem Gamma0R_le_normG_GammaDeltaR' (N : ℕ) (Δ : Subgroup (ZMod N)ˣ) :
    Gamma0R N ≤ NormG (GammaDeltaR N Δ) := by
  rintro _ ⟨g, hg, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro Y
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨g * γ * g⁻¹, conj_mem_GammaDelta hg hγ, ?_⟩
    simp [map_mul, map_inv]
  · rintro ⟨γ', hγ', hY⟩
    refine ⟨g⁻¹ * γ' * g⁻¹⁻¹, conj_mem_GammaDelta (inv_mem hg) hγ', ?_⟩
    simp only [map_mul, map_inv, inv_inv] at hY ⊢
    rw [hY]
    group

/-! ### The index i_Δ -/

/-- γ ↦ γ₁₁ mod N, as a homomorphism Γ₀(N) → (ℤ/N)ˣ. -/
def unitMap (N : ℕ) : CongruenceSubgroup.Gamma0 N →* (ZMod N)ˣ :=
  (CongruenceSubgroup.Gamma0Map N).toHomUnits

theorem coe_unitMap (γ : CongruenceSubgroup.Gamma0 N) :
    ((unitMap N γ : (ZMod N)ˣ) : ZMod N) = (((γ : SLℤ) 1 1 : ℤ) : ZMod N) := rfl



/-! ### S₂ at N = 8 -/

end

end NormalizerLean
