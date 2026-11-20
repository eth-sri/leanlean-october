module

public import NormalizerDelta.SigmaH
public import NormalizerDelta.IndexDelta

@[expose] public section

/-! Counting right cosets using the normalized matrices σH. -/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

private theorem reps_iff {N : ℕ} {R : Set SL(2, ℤ)} :
    IsGamma0Reps N R ↔ Subgroup.IsComplement (CongruenceSubgroup.Gamma0 N : Set SL(2, ℤ)) R := by
  simp [IsGamma0Reps, Subgroup.isComplement_iff_existsUnique_mul_inv_mem, ExistsUnique,
    Subtype.exists, Subtype.forall, and_imp, and_assoc]
  exact forall_congr' fun _ => exists_congr fun _ => by tauto

theorem exists_Gamma0Reps (N : ℕ) : ∃ R : Set SL(2, ℤ), IsGamma0Reps N R := by
  obtain ⟨R, hR, -⟩ := Subgroup.exists_isComplement_right (CongruenceSubgroup.Gamma0 N) 1
  exact ⟨R, reps_iff.2 hR⟩

local notation "Pairs" => SL(2, ℤ) × ℕ × ℕ × ℕ

private def sigmaMat (x : Pairs) : Mat₂R := (ofZ x.1 : Mat₂R) * hermMat x.2.1 x.2.2.1 x.2.2.2

private abbrev SigmaHSet (N : ℕ) (R : Set SL(2, ℤ)) (K : Subgroup SL(2, ℝ)) : Type :=
  {x : Pairs // x.1 ∈ R ∧ IsHermiteN N x.2.1 x.2.2.1 x.2.2.2 ∧ projSL (sigmaMat x) ∈ K}

private theorem det_sigma (r : SL(2, ℤ)) {N a b d : ℕ} (h : IsHermiteN N a b d) :
    0 < (sigmaMat (r, a, b, d)).det := by
  change 0 < ((ofZ r : Mat₂R) * hermMat a b d).det
  rw [det_mul, (ofZ r).2, one_mul]
  simpa [hermMat, det_fin_two_of] using mul_pos
    (Nat.cast_pos.2 h.1 : (0 : ℝ) < a) (Nat.cast_pos.2 h.2.1)

private theorem neg_mem_Gamma0R {N : ℕ} {g : SL(2, ℝ)} (hg : g ∈ Gamma0R N) : -g ∈ Gamma0R N := by
  obtain ⟨γ, hγ, rfl⟩ := hg
  exact ⟨-γ, by simpa [SpecialLinearGroup.coe_neg] using hγ, SpecialLinearGroup.coe_int_neg γ⟩

private theorem projSL_eq_or_eq_neg {A : Mat₂R} {g : SL(2, ℝ)} {c : ℝ} (hA : 0 < A.det)
    (hg : (g : Mat₂R) = c • A) : projSL A = g ∨ projSL A = -g := by
  have h := g.2
  rw [hg, det_smul, Fintype.card_fin] at h
  have e : c^2 = (Real.sqrt A.det)⁻¹ ^ 2 := by
    rw [inv_pow, Real.sq_sqrt hA.le]
    exact eq_inv_of_mul_eq_one_left h
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 e with e | e
  · exact Or.inl (Subtype.ext (by simpa [coe_projSL _ hA, e] using hg.symm))
  · exact Or.inr (Subtype.ext (by simpa [coe_projSL _ hA, e] using congrArg Neg.neg hg.symm))

/-- Inversion converts right cosets to the left quotients used for relative index. -/
private def sigmaHMap (N : ℕ) (R : Set SL(2, ℤ)) (K : Subgroup SL(2, ℝ)) :
    SigmaHSet N R K → K ⧸ (Gamma0R N).subgroupOf K :=
  fun x => QuotientGroup.mk ⟨(projSL (sigmaMat x))⁻¹, inv_mem x.2.2.2⟩

private theorem sigmaHMap_surjective {N : ℕ} [NeZero N] (Δ : Subgroup (ZMod N)ˣ) {R : Set SL(2, ℤ)}
    (hR : IsGamma0Reps N R) {K : Subgroup SL(2, ℝ)} (hK0 : Gamma0R N ≤ K) (hKM : K ≤ MDelta N Δ) :
    Function.Surjective (sigmaHMap N R K) := by
  intro y
  obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨γ, hγ, r, hr, a, b, d, hH, c, -, h⟩ := exists_sigmaH Δ hR (hKM (inv_mem hk))
  let P := projSL (sigmaMat (r, a, b, d))
  have hP : P * k ∈ Gamma0R N := by
    rcases projSL_eq_or_eq_neg (det_sigma r hH) h with e | e
    · simpa [P, e] using hγ
    · simpa [P, e, neg_mul] using neg_mem_Gamma0R hγ
  refine ⟨⟨(r, a, b, d), hr, hH, (mul_mem_cancel_right hk).1 (hK0 hP)⟩, QuotientGroup.eq.2 ?_⟩
  simpa [sigmaHMap, Subgroup.mem_subgroupOf, P] using hP

private theorem sigmaHMap_injective {N : ℕ} [NeZero N] {R : Set SL(2, ℤ)} (hR : IsGamma0Reps N R)
    {K : Subgroup SL(2, ℝ)} : Function.Injective (sigmaHMap N R K) := by
  rintro ⟨⟨r, a, b, d⟩, hr, hH, hPK⟩ ⟨⟨r', a', b', d'⟩, hr', hH', hPK'⟩ xy
  let P := projSL (sigmaMat (r, a, b, d))
  let Q := projSL (sigmaMat (r', a', b', d'))
  have hγ : P * Q⁻¹ ∈ Gamma0R N := by
    simpa [P, Q, Subgroup.mem_subgroupOf] using QuotientGroup.eq.1 xy
  have h : (P : Mat₂R) = (↑(P * Q⁻¹) : Mat₂R) * (Q : Mat₂R) := by
    exact congrArg (fun g : SL(2, ℝ) => (g : Mat₂R)) (by simp : P = P * Q⁻¹ * Q)
  have hp := det_sigma r hH
  have hq := det_sigma r' hH'
  change (projSL (sigmaMat _) : Mat₂R) = _ * (projSL (sigmaMat _) : Mat₂R) at h
  rw [coe_projSL _ hp, coe_projSL _ hq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := sigmaH_unique hR hr hr' hH hH'
    (inv_ne_zero (Real.sqrt_pos.2 hp).ne') (inv_ne_zero (Real.sqrt_pos.2 hq).ne') hγ h
  rfl

theorem relIndex_normG_eq_card_sigmaH {N : ℕ} [NeZero N] (Δ : Subgroup (ZMod N)ˣ)
    {R : Set SL(2, ℤ)} (hR : IsGamma0Reps N R) :
    (Gamma0R N).relIndex (NormG (GammaDeltaR N Δ)) =
      Nat.card {x : SL(2, ℤ) × ℕ × ℕ × ℕ // x.1 ∈ R ∧ IsHermiteN N x.2.1 x.2.2.1 x.2.2.2 ∧
        projSL ((ofZ x.1 : Matrix (Fin 2) (Fin 2) ℝ) * hermMat x.2.1 x.2.2.1 x.2.2.2) ∈
          NormG (GammaDeltaR N Δ)} :=
  (Nat.card_congr (Equiv.ofBijective _ ⟨sigmaHMap_injective hR,
    sigmaHMap_surjective Δ hR (Gamma0R_le_normG_GammaDeltaR N Δ) (normG_GammaDeltaR_le_MDelta N Δ)⟩)).symm

theorem relIndex_Gamma0R_MDelta_ne_zero (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    (Gamma0R N).relIndex (MDelta N Δ) ≠ 0 := by
  obtain ⟨R, hR⟩ := exists_Gamma0Reps N
  have : Finite (SigmaHSet N R (MDelta N Δ)) := by
    have h := (reps_iff.1 hR).finite_right.prod ((Set.finite_Iic N).prod ((Set.finite_Iic N).prod (Set.finite_Iic N)))
    refine (h.subset ?_).to_subtype
    rintro ⟨r, a, b, d⟩ ⟨hr, ⟨ha, hd, had, hb, -⟩, -⟩
    have := Nat.le_of_dvd (NeZero.pos N) had
    refine ⟨hr, ?_, ?_, ?_⟩ <;> change _ ≤ N <;> nlinarith
  exact Subgroup.index_ne_zero_iff_finite.2
    (Finite.of_surjective _ (sigmaHMap_surjective Δ hR (Gamma0R_le_MDelta N Δ) le_rfl))

theorem card_BG_GammaDeltaR_eq (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    Nat.card (BG (GammaDeltaR N Δ)) = Δ.index * (Gamma0R N).relIndex (NormG (GammaDeltaR N Δ)) := by
  change (GammaDeltaR N Δ).relIndex _ = _
  rw [← Subgroup.relIndex_mul_relIndex (hHK := GammaDeltaR_le_Gamma0R)
      (hKL := Gamma0R_le_normG_GammaDeltaR N Δ),
    relIndex_GammaDeltaR_Gamma0R]

theorem finite_BG_GammaDeltaR (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    Finite (BG (GammaDeltaR N Δ)) := by
  refine (Nat.card_ne_zero.1 ?_).2
  rw [card_BG_GammaDeltaR_eq]
  exact mul_ne_zero Subgroup.index_ne_zero_of_finite (mt
    (Subgroup.relIndex_eq_zero_of_le_right (normG_GammaDeltaR_le_MDelta N Δ))
    (relIndex_Gamma0R_MDelta_ne_zero N Δ))

end

end NormalizerLean
