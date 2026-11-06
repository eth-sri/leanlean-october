module

public import NormalizerDelta.SanityD
public import NormalizerLean.Proofs

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

theorem toR_le_normG {H Γ : Subgroup SL(2, ℤ)} (h : ∀ g ∈ H, ∀ γ ∈ Γ, g * γ * g⁻¹ ∈ Γ) :
    toR H ≤ NormG (toR Γ) := by
  rintro _ ⟨g, hg, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro Y
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨g * γ * g⁻¹, h g hg γ hγ, ?_⟩
    simp [map_mul, map_inv]
  · rintro ⟨γ', hγ', hY⟩
    refine ⟨g⁻¹ * γ' * g⁻¹⁻¹, h _ (inv_mem hg) γ' hγ', ?_⟩
    simp only [map_mul, map_inv, inv_inv] at hY ⊢
    rw [hY]
    group

/-- The lower right entry of g γ g⁻¹ mod N, for g, γ ∈ Γ₀(N). -/
theorem conj_entry_11 {g γ : SL(2, ℤ)} (hg : ((g 1 0 : ℤ) : ZMod N) = 0)
    (hγ : ((γ 1 0 : ℤ) : ZMod N) = 0) :
    (((g * γ * g⁻¹) 1 1 : ℤ) : ZMod N) = ((γ 1 1 : ℤ) : ZMod N) := by
  have hdet : ((g 0 0 : ℤ) : ZMod N) * ((g 1 1 : ℤ) : ZMod N) = 1 := by
    have h1 := congrArg (fun x : ℤ => (x : ZMod N)) g.2
    simp only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one] at h1
    rw [hg, mul_zero, sub_zero] at h1
    exact h1
  have e : ((g * γ * g⁻¹) 1 1 : ℤ) = (g 1 0 * γ 0 0 + g 1 1 * γ 1 0) * (-g 0 1) +
      (g 1 0 * γ 0 1 + g 1 1 * γ 1 1) * g 0 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]
  rw [e]
  push_cast
  rw [hg, hγ]
  linear_combination ((γ 1 1 : ℤ) : ZMod N) * hdet

theorem conj_mem_GammaDelta {Δ : Subgroup (ZMod N)ˣ} {g γ : SL(2, ℤ)}
    (hg : g ∈ CongruenceSubgroup.Gamma0 N) (hγ : γ ∈ GammaDelta N Δ) :
    g * γ * g⁻¹ ∈ GammaDelta N Δ := by
  obtain ⟨h0, u, hu, hud⟩ := hγ
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg h0) (Subgroup.inv_mem _ hg), u, hu, ?_⟩
  rw [hud, conj_entry_11 (CongruenceSubgroup.Gamma0_mem.1 hg) (CongruenceSubgroup.Gamma0_mem.1 h0)]

theorem Gamma0R_le_normG_GammaDeltaR' (N : ℕ) (Δ : Subgroup (ZMod N)ˣ) :
    Gamma0R N ≤ NormG (GammaDeltaR N Δ) :=
  toR_le_normG (fun _ hg _ hγ => conj_mem_GammaDelta hg hγ)

/-! ### The index i_Δ -/

/-- γ ↦ γ₁₁ mod N, as a homomorphism Γ₀(N) → (ℤ/N)ˣ. -/
def unitMap (N : ℕ) : CongruenceSubgroup.Gamma0 N →* (ZMod N)ˣ :=
  (CongruenceSubgroup.Gamma0Map N).toHomUnits

theorem coe_unitMap (γ : CongruenceSubgroup.Gamma0 N) :
    ((unitMap N γ : (ZMod N)ˣ) : ZMod N) = (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) := rfl

theorem unitMap_surjective [NeZero N] : Function.Surjective (unitMap N) := by
  intro u
  set v := (u : ZMod N).val
  have hcopN : Nat.Coprime v N := ZMod.val_coe_unit_coprime u
  have hb := Int.gcd_eq_gcd_ab v N
  rw [Int.gcd_natCast_natCast, hcopN] at hb
  have hdet : Int.gcdA v N * v - (-Int.gcdB v N) * N = 1 := by
    push_cast at hb; linear_combination -hb
  refine ⟨⟨mkSL _ _ _ _ hdet, CongruenceSubgroup.Gamma0_mem.2 (by simp [mkSL])⟩, Units.ext ?_⟩
  rw [coe_unitMap]
  simp [mkSL, v]

theorem GammaDelta_subgroupOf (Δ : Subgroup (ZMod N)ˣ) :
    (GammaDelta N Δ).subgroupOf (CongruenceSubgroup.Gamma0 N) = Δ.comap (unitMap N) := by
  ext γ
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  constructor
  · rintro ⟨-, u, hu, hud⟩
    have : unitMap N γ = u := Units.ext (by rw [coe_unitMap, hud])
    rwa [this]
  · intro h
    exact ⟨γ.2, unitMap N γ, h, rfl⟩

theorem relindex_GammaDelta' (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    (GammaDelta N Δ).relIndex (CongruenceSubgroup.Gamma0 N) = Δ.index := by
  rw [Subgroup.relIndex, GammaDelta_subgroupOf, Subgroup.index_comap_of_surjective _ unitMap_surjective]

/-! ### Nor(Γ_Δ(N)) ≤ Nor(Γ₀(N)) -/

/-! ### The index [Nor(Γ_Δ) : Γ_Δ] = i_Δ · s_Δ -/

theorem ofZ_injective : Function.Injective (SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom ℝ)) := by
  intro a b h
  ext i j
  have := congrArg (fun g : SL(2, ℝ) => (g : Matrix (Fin 2) (Fin 2) ℝ) i j) h
  simpa using this

/-! ### S₂ at N = 8 -/

end

end NormalizerLean
