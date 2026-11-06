module

public import NormalizerDelta.SigmaH
public import NormalizerDelta.IndexDelta

@[expose] public section

/-!
# §M: [K : Γ₀(N)] = #{(σ, H) : σH ∈ K} for Γ₀(N) ≤ K ≤ M_Δ, finiteness, and the index i_Δ·[Nor : Γ₀]

The map (σ, H) ↦ (σH)⁻¹ Γ₀(N) ∈ K/Γ₀(N) (left cosets; σH rescaled into SL₂(ℝ) by `projSL`) is
* onto: for k ∈ K, `exists_sigmaH` applied to k⁻¹ ∈ M_Δ gives γ k⁻¹ = c σH, and det = 1 forces
  projSL(σH) = ±γ k⁻¹;
* injective: `sigmaH_unique'`.
The pairs form a finite set (R is finite since [SL₂(ℤ) : Γ₀(N)] < ∞, and a, b, d ≤ N), so [M_Δ : Γ₀(N)] < ∞.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ### Sets of representatives -/

theorem exists_Gamma0Reps (N : ℕ) : ∃ R : Set SLℤ, IsGamma0Reps N R := by
  refine ⟨Set.range (fun q : SLℤ ⧸ CongruenceSubgroup.Gamma0 N => (Quotient.out q)⁻¹), ?_⟩
  intro σ
  refine ⟨(Quotient.out (QuotientGroup.mk σ⁻¹ : SLℤ ⧸ CongruenceSubgroup.Gamma0 N))⁻¹,
    ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
  · have h := QuotientGroup.out_eq' (QuotientGroup.mk σ⁻¹ : SLℤ ⧸ CongruenceSubgroup.Gamma0 N)
    have := QuotientGroup.eq.1 h.symm
    simpa using this
  · rintro r ⟨⟨q, rfl⟩, hq⟩
    congr 1
    have h1 : (QuotientGroup.mk σ⁻¹ : SLℤ ⧸ CongruenceSubgroup.Gamma0 N) = q := by
      rw [← QuotientGroup.out_eq' q]
      apply QuotientGroup.eq.2
      simpa using hq
    rw [h1]

/-! ### The pairs (σ, H) -/

/-- The pairs (σ, H), σ ∈ R, H a Hermite form, with σH (rescaled) in K. -/
abbrev SigmaHSet (N : ℕ) (R : Set SLℤ) (K : Subgroup SLℝ) : Type :=
  {x : SLℤ × ℕ × ℕ × ℕ // x.1 ∈ R ∧ IsHermiteN N x.2.1 x.2.2.1 x.2.2.2 ∧
    projSL (σH x.1 x.2.1 x.2.2.1 x.2.2.2) ∈ K}

theorem det_sigmaH (r : SLℤ) (a b d : ℕ) :
    (σH r a b d).det = a * d := by
  rw [det_mul, Matrix.SpecialLinearGroup.det_coe, one_mul, hermMat, det_fin_two_of]; ring

theorem coe_projSL_sigmaH (r : SLℤ) {a b d : ℕ} (ha : 0 < a) (hd : 0 < d) :
    ((projSL (σH r a b d) : SLℝ) :
        Matℝ) =
      (Real.sqrt (a * d))⁻¹ • (σH r a b d) := by
  rw [coe_projSL _ (by rw [det_sigmaH]; positivity), det_sigmaH]

theorem finite_SigmaHSet {N : ℕ} [NeZero N] {R : Set SLℤ} (hR : IsGamma0Reps N R)
    (K : Subgroup SLℝ) : Finite (SigmaHSet N R K) := by
  have hRf : R.Finite := by
    have : Finite (SLℤ ⧸ CongruenceSubgroup.Gamma0 N) := Subgroup.finite_quotient_of_finiteIndex
    refine Set.finite_coe_iff.1 (Finite.of_injective
      (fun r : R => (QuotientGroup.mk (r : SLℤ)⁻¹ : SLℤ ⧸ CongruenceSubgroup.Gamma0 N)) ?_)
    intro r r' hrr
    have h1 : (r : SLℤ) * (r' : SLℤ)⁻¹ ∈ CongruenceSubgroup.Gamma0 N := by
      have := QuotientGroup.eq.1 hrr
      simpa using this
    exact Subtype.ext ((hR r).unique ⟨r.2, by rw [mul_inv_cancel]; exact one_mem _⟩ ⟨r'.2, h1⟩)
  have hT : (R ×ˢ (Set.Iic N ×ˢ (Set.Iic N ×ˢ Set.Iic N))).Finite :=
    hRf.prod ((Set.finite_Iic N).prod ((Set.finite_Iic N).prod (Set.finite_Iic N)))
  have hsub : {x : SLℤ × ℕ × ℕ × ℕ | x.1 ∈ R ∧ IsHermiteN N x.2.1 x.2.2.1 x.2.2.2} ⊆
      R ×ˢ (Set.Iic N ×ˢ (Set.Iic N ×ˢ Set.Iic N)) := by
    rintro ⟨r, a, b, d⟩ ⟨hr, ha, hd, hadN, hbd, -⟩
    have hN := Nat.pos_of_ne_zero (NeZero.ne N)
    have h1 : a * d ≤ N := Nat.le_of_dvd hN hadN
    refine ⟨hr, ?_, ?_, ?_⟩ <;> simp only [Set.mem_Iic] <;> nlinarith
  have := (hT.subset hsub).to_subtype
  exact Finite.of_injective
    (fun x : SigmaHSet N R K => (⟨x.1, x.2.1, x.2.2.1⟩ :
      {x : SLℤ × ℕ × ℕ × ℕ | x.1 ∈ R ∧ IsHermiteN N x.2.1 x.2.2.1 x.2.2.2}))
    (fun x y h => Subtype.ext (by have := congrArg Subtype.val h; exact this))

theorem neg_one_mem_Gamma0R (N : ℕ) : (-1 : SLℝ) ∈ Gamma0R N := by
  have h : ofZ (-1) = -1 := by ext i j; simp [SpecialLinearGroup.coe_neg]
  rw [← h]
  exact Subgroup.mem_map_of_mem _ (neg_one_mem_Gamma0 N)

/-- The map (σ, H) ↦ (σH)⁻¹ Γ₀(N). -/
def sigmaHMap (N : ℕ) (R : Set SLℤ) (K : Subgroup SLℝ) :
    SigmaHSet N R K → K ⧸ (Gamma0R N).subgroupOf K :=
  fun x => QuotientGroup.mk ⟨(projSL (σH x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2))⁻¹,
    K.inv_mem x.2.2.2⟩

theorem sigmaHMap_surjective {N : ℕ} [NeZero N] (Δ : Subgroup (ZMod N)ˣ) {R : Set SLℤ}
    (hR : IsGamma0Reps N R) {K : Subgroup SLℝ} (hK0 : Gamma0R N ≤ K) (hKM : K ≤ MDelta N Δ) :
    Function.Surjective (sigmaHMap N R K) := by
  intro y
  obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective y
  have hgM : k⁻¹ ∈ MDelta N Δ := hKM (K.inv_mem hk)
  obtain ⟨γ, hγ, r, hr, a, b, d, hH, c, -, heq⟩ := exists_sigmaH Δ hR hgM
  set X := σH r a b d
  set P := projSL X
  have ha := hH.1
  have hd := hH.2.1
  have hP' := coe_projSL_sigmaH r (b := b) ha hd
  have hdet : c ^ 2 * (a * d) = 1 := by
    have h1 := congrArg Matrix.det heq
    rw [Matrix.SpecialLinearGroup.det_coe, det_smul, Fintype.card_fin, det_sigmaH] at h1
    exact h1.symm
  have hsq : 0 < (a : ℝ) * d := by positivity
  have hPm : (P : Matℝ) =
      (c * Real.sqrt (a * d)) • ((γ * k⁻¹ : SLℝ) : Matℝ) := by
    rw [hP', heq, smul_smul]
    congr 1
    field_simp
    rw [Real.sq_sqrt hsq.le]; linear_combination -hdet
  have hu := mul_self_eq_one_iff.1
    (show (c * Real.sqrt (a * d)) * (c * Real.sqrt (a * d)) = 1 by
      rw [← pow_two, mul_pow, Real.sq_sqrt hsq.le, hdet])
  have hPK : P ∈ K ∧ P * k ∈ Gamma0R N := by
    rcases hu with hu | hu
    · have hPe : P = γ * k⁻¹ := Subtype.ext (by rw [hPm, hu, one_smul])
      refine ⟨hPe ▸ mul_mem (hK0 hγ) (K.inv_mem hk), ?_⟩
      rw [hPe, inv_mul_cancel_right]; exact hγ
    · have hPe : P = -1 * (γ * k⁻¹) := Subtype.ext (by
        rw [hPm, hu, neg_one_mul, Matrix.SpecialLinearGroup.coe_neg, neg_one_smul])
      refine ⟨hPe ▸ mul_mem (hK0 (neg_one_mem_Gamma0R N)) (mul_mem (hK0 hγ) (K.inv_mem hk)), ?_⟩
      rw [hPe, mul_assoc, inv_mul_cancel_right]
      exact mul_mem (neg_one_mem_Gamma0R N) hγ
  refine ⟨⟨(r, a, b, d), hr, hH, hPK.1⟩, ?_⟩
  apply QuotientGroup.eq.2
  rw [Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
  exact hPK.2

theorem sigmaHMap_injective {N : ℕ} [NeZero N] {R : Set SLℤ} (hR : IsGamma0Reps N R)
    {K : Subgroup SLℝ} : Function.Injective (sigmaHMap N R K) := by
  rintro ⟨⟨r, a, b, d⟩, hr, hH, hPK⟩ ⟨⟨r', a', b', d'⟩, hr', hH', hPK'⟩ hxy
  have h1 := QuotientGroup.eq.1 hxy
  rw [Subgroup.mem_subgroupOf] at h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at h1
  set P := projSL (σH r a b d)
  set P' := projSL (σH r' a' b' d')
  obtain ⟨γ, hγdef⟩ : ∃ γ, γ = P * P'⁻¹ := ⟨_, rfl⟩
  rw [← hγdef] at h1
  have hPP : P = γ * P' := by rw [hγdef]; group
  have hm := congrArg (fun g : SLℝ => (g : Matℝ)) hPP
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hm
  rw [coe_projSL_sigmaH r hH.1 hH.2.1, coe_projSL_sigmaH r' hH'.1 hH'.2.1] at hm
  have hsq : 0 < (a : ℝ) * d := by have := hH.1; have := hH.2.1; positivity
  have hsq' : 0 < (a' : ℝ) * d' := by have := hH'.1; have := hH'.2.1; positivity
  obtain ⟨h1', h2, h3, h4⟩ := sigmaH_unique hR hr hr' hH hH'
    (inv_ne_zero (Real.sqrt_pos.2 hsq).ne') (inv_ne_zero (Real.sqrt_pos.2 hsq').ne') h1 hm
  subst h1' h2 h3 h4
  rfl

theorem relIndex_normG_eq_card_sigmaH {N : ℕ} [NeZero N] (Δ : Subgroup (ZMod N)ˣ)
    {R : Set SLℤ} (hR : IsGamma0Reps N R) :
    (Gamma0R N).relIndex (NormG (GammaDeltaR N Δ)) =
      Nat.card {x : SLℤ × ℕ × ℕ × ℕ // x.1 ∈ R ∧ IsHermiteN N x.2.1 x.2.2.1 x.2.2.2 ∧
        projSL (σH x.1 x.2.1 x.2.2.1 x.2.2.2) ∈
          NormG (GammaDeltaR N Δ)} :=
  (Nat.card_congr (Equiv.ofBijective _ ⟨sigmaHMap_injective hR,
    sigmaHMap_surjective Δ hR (Gamma0R_le_normG_GammaDeltaR' N Δ)
      (normG_GammaDeltaR_le_MDelta N Δ)⟩)).symm

/-! ### Finiteness and the index -/

theorem relIndex_Gamma0R_MDelta_ne_zero (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    (Gamma0R N).relIndex (MDelta N Δ) ≠ 0 := by
  obtain ⟨R, hR⟩ := exists_Gamma0Reps N
  have := finite_SigmaHSet hR (MDelta N Δ)
  have hfin : Finite (MDelta N Δ ⧸ (Gamma0R N).subgroupOf (MDelta N Δ)) :=
    Finite.of_surjective _ (sigmaHMap_surjective Δ hR (Gamma0R_le_MDelta N Δ) le_rfl)
  exact Subgroup.index_ne_zero_iff_finite.2 hfin

theorem card_BG_GammaDeltaR_eq (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    Nat.card (BG (GammaDeltaR N Δ)) = Δ.index * (Gamma0R N).relIndex (NormG (GammaDeltaR N Δ)) := by
  have h1 : GammaDeltaR N Δ ≤ Gamma0R N := GammaDeltaR_le_Gamma0R
  have h2 : Gamma0R N ≤ NormG (GammaDeltaR N Δ) := Gamma0R_le_normG_GammaDeltaR' N Δ
  have hBG : Nat.card (BG (GammaDeltaR N Δ)) =
      (GammaDeltaR N Δ).relIndex (NormG (GammaDeltaR N Δ)) := rfl
  rw [hBG, ← Subgroup.relIndex_mul_relIndex (hHK := h1) (hKL := h2), GammaDeltaR, toR, Gamma0R,
    Subgroup.relIndex_map_map_of_injective _ _ (by
      intro a b h
      ext i j
      have := congrArg (fun g : SLℝ => (g : Matℝ) i j) h
      simpa using this)]
  rw [Subgroup.relIndex, show (GammaDelta N Δ).subgroupOf (CongruenceSubgroup.Gamma0 N) =
      Δ.comap (unitMap N) by
    ext γ
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    constructor
    · rintro ⟨-, u, hu, hud⟩
      have : unitMap N γ = u := Units.ext (by rw [coe_unitMap, hud])
      rwa [this]
    · intro h
      exact ⟨γ.2, unitMap N γ, h, rfl⟩,
    Subgroup.index_comap_of_surjective _ (by
      intro u
      set v := (u : ZMod N).val
      have hcopN : Nat.Coprime v N := ZMod.val_coe_unit_coprime u
      have hb := Int.gcd_eq_gcd_ab v N
      rw [Int.gcd_natCast_natCast, hcopN] at hb
      have hdet : Int.gcdA v N * v - (-Int.gcdB v N) * N = 1 := by
        push_cast at hb; linear_combination -hb
      refine ⟨⟨mkSL _ _ _ _ hdet, CongruenceSubgroup.Gamma0_mem.2 (by simp [mkSL])⟩,
        Units.ext ?_⟩
      rw [coe_unitMap]
      simp [mkSL, v])]

theorem finite_BG_GammaDeltaR (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    Finite (BG (GammaDeltaR N Δ)) := by
  have hn : (Gamma0R N).relIndex (NormG (GammaDeltaR N Δ)) ≠ 0 := by
    have h := Subgroup.relIndex_mul_relIndex (hHK := Gamma0R_le_normG_GammaDeltaR' N Δ)
      (hKL := normG_GammaDeltaR_le_MDelta N Δ)
    intro h0
    rw [h0, zero_mul] at h
    exact relIndex_Gamma0R_MDelta_ne_zero N Δ h.symm
  have h : Nat.card (BG (GammaDeltaR N Δ)) ≠ 0 := by
    rw [card_BG_GammaDeltaR_eq]
    exact mul_ne_zero Subgroup.index_ne_zero_of_finite hn
  exact (Nat.card_ne_zero.1 h).2

end

end NormalizerLean
