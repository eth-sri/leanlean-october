module

public import NormalizerDelta.SigmaH

@[expose] public section

/-! Counting cosets using the inverses of their projective Hermite representatives. -/

open Matrix CongruenceSubgroup Subgroup

namespace NormalizerLean
noncomputable section

variable {N : ℕ} {R : Set SL₂ℤ} {K : Subgroup SL₂ℝ}

private lemma reps_iff : IsGamma0Reps N R ↔ IsComplement (Gamma0 N) R := by
  simp [IsGamma0Reps, isComplement_iff_existsUnique_mul_inv_mem, ExistsUnique, Subtype.ext_iff, and_left_comm, and_assoc]

theorem exists_Gamma0Reps (N : ℕ) : ∃ R : Set SL₂ℤ, IsGamma0Reps N R :=
  ⟨_, reps_iff.mpr (default : (Gamma0 N).RightTransversal).2⟩

-- The index set for the count, written once for all intermediate subgroups.
set_option quotPrecheck false in
local notation "Pairs " N:arg R:arg K:arg =>
  {x : SL₂ℤ × ℕ × ℕ × ℕ // x.1 ∈ R ∧ IsHermiteN N x.2.1 x.2.2.1 x.2.2.2 ∧
    projSL (σH x.1 x.2.1 x.2.2.1 x.2.2.2) ∈ K}

-- Inversion converts our right cosets to the left quotient used by `QuotientGroup`.
variable (N R K) in
private abbrev pairMap (x : Pairs N R K) : K ⧸ (Gamma0R N).subgroupOf K :=
  QuotientGroup.mk ((⟨_, x.2.2.2⟩ : K)⁻¹)

variable [NeZero N]

private lemma injective (hR : IsGamma0Reps N R) : Function.Injective (pairMap N R K) := by
  rintro ⟨⟨r, a, b, d⟩, hr, H, hP⟩ ⟨⟨r', A, B, D⟩, hr', H', hP'⟩ h
  let P := projSL (σH r a b d)
  let Q := projSL (σH r' A B D)
  have hm := QuotientGroup.eq.mp h
  have hγ : P * Q⁻¹ ∈ Gamma0R N := inv_inv P ▸ hm
  have hp := pos_det r H; have hq := pos_det r' H'
  have eq : P.1 = (P * Q⁻¹).1 * Q.1 := congrArg Subtype.val (inv_mul_cancel_right P Q).symm
  rw [coe_projSL hp, coe_projSL hq] at eq
  obtain ⟨rfl, rfl, rfl, rfl⟩ := sigmaH_unique hR hr hr' H H' (by positivity) (by positivity) hγ eq
  rfl

variable (Δ : Subgroup (ZMod N)ˣ)

private lemma surjective (hR : IsGamma0Reps N R) (hK : Gamma0R N ≤ K) (hM : K ≤ MDelta N Δ) :
    Function.Surjective (pairMap N R K) := by
  rintro ⟨⟨k, hk⟩⟩
  obtain ⟨r, hr, a, b, d, H, ht⟩ := representative Δ hR (hM (inv_mem hk))
  rw [inv_inv] at ht
  refine ⟨⟨(r, a, b, d), hr, H, (K.mul_mem_cancel_right hk).mp (hK ht)⟩, QuotientGroup.eq.mpr ?_⟩
  change _⁻¹⁻¹ * k ∈ Gamma0R N; simpa using ht

private lemma finite_pairs (hR : IsGamma0Reps N R) : Finite (Pairs N R K) := by
  apply Set.Finite.to_subtype
  have I := Set.finite_Iic N
  apply ((reps_iff.mp hR).finite_right.prod (I.prod (I.prod I))).subset
  rintro ⟨r, a, b, d⟩ ⟨hr, ⟨ha, hd, had, hbd, _⟩, _⟩
  have := Nat.le_of_dvd (NeZero.pos N) had
  refine ⟨hr, ?_, ?_, ?_⟩ <;> change _ ≤ N <;> nlinarith

theorem relIndex_normG_eq_card_sigmaH {R : Set SL₂ℤ}
    (hR : IsGamma0Reps N R) :
    (Gamma0R N).relIndex (NormG (GammaDeltaR N Δ)) =
      Nat.card (Pairs N R (NormG (GammaDeltaR N Δ))) :=
  (Nat.card_congr (Equiv.ofBijective _ ⟨injective hR, surjective Δ hR gamma0_normalizes (normG_GammaDeltaR_le_MDelta N Δ)⟩)).symm

variable (N)

theorem relIndex_Gamma0R_MDelta_ne_zero : (Gamma0R N).relIndex (MDelta N Δ) ≠ 0 := by
  obtain ⟨R, hR⟩ := exists_Gamma0Reps N
  have := finite_pairs (K := MDelta N Δ) hR
  exact Subgroup.index_ne_zero_iff_finite.mpr (Finite.of_surjective _ (surjective Δ hR (Gamma0R_le_MDelta N Δ) le_rfl))

theorem card_BG_GammaDeltaR_eq : Nat.card (BG (GammaDeltaR N Δ)) = Δ.index * (Gamma0R N).relIndex (NormG (GammaDeltaR N Δ)) := by
  rw [← delta_index]
  exact (Subgroup.relIndex_mul_relIndex (hHK := Subgroup.map_mono delta_le) (hKL := gamma0_normalizes)).symm

theorem finite_BG_GammaDeltaR : Finite (BG (GammaDeltaR N Δ)) := by
  apply (Nat.card_ne_zero.mp _).2
  rw [card_BG_GammaDeltaR_eq]
  exact mul_ne_zero Subgroup.index_ne_zero_of_finite fun h => relIndex_Gamma0R_MDelta_ne_zero N Δ
    (Subgroup.relIndex_eq_zero_of_le_right (normG_GammaDeltaR_le_MDelta N Δ) h)
end

end NormalizerLean
