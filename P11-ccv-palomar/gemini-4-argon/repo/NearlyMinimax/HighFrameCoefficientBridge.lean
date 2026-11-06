module
public import NearlyMinimax.HighPeriodizedFrame
public import NearlyMinimax.SpatialCardinalCovariance
@[expose] public section
noncomputable section
open Set MeasureTheory MvPolynomial
open scoped BigOperators ENNReal ContDiff
namespace NearlyMinimax
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable {d : ℕ}
def boundedMultiIndexMultiset (d ℓ ) (γ : Fin d → Fin (ℓ + 1)) : Multiset (Fin (d + 1)) :=
  (∑ r, Multiset.replicate (γ r).val r.castSucc) +
    Multiset.replicate (ℓ - ∑ r, (γ r).val) (Fin.last d)
theorem boundedMultiIndexMultiset_card (d ℓ γ)
    (hγ : (∑ r, (γ r).val) ≤ ℓ) :
    (boundedMultiIndexMultiset d ℓ γ).card = ℓ := by
  simp only [boundedMultiIndexMultiset, Multiset.card_add, Multiset.card_sum,
    Multiset.card_replicate]
  omega
theorem bounded_multiIndex_count_le (d ℓ : ℕ) :
    (Finset.univ.filter (fun γ : Fin d → Fin (ℓ + 1) => (∑ r, (γ r).val) ≤ ℓ)).card ≤
      (d + ℓ).choose d := by
  let A := Finset.univ.filter (fun γ : Fin d → Fin (ℓ + 1) => (∑ r, (γ r).val) ≤ ℓ)
  let encode : A → Sym (Fin (d + 1)) ℓ := fun γ =>
    ⟨boundedMultiIndexMultiset d ℓ γ, boundedMultiIndexMultiset_card d ℓ γ
      (Finset.mem_filter.mp γ.property).2⟩
  have hinj : Function.Injective encode := by
    intro γ δ he
    apply Subtype.ext
    funext r
    apply Fin.ext
    have hm := congrArg (fun s : Sym (Fin (d + 1)) ℓ => s.val.count r.castSucc) he
    change (boundedMultiIndexMultiset d ℓ γ).count r.castSucc =
      (boundedMultiIndexMultiset d ℓ δ).count r.castSucc at hm
    have h_boundedMultiIndexMultiset_count (γ : Fin d → Fin (ℓ + 1)) (r : Fin d) : (boundedMultiIndexMultiset d ℓ γ).count r.castSucc = (γ r).val := by
      simp only [boundedMultiIndexMultiset, Multiset.count_add, Multiset.count_sum',
        Multiset.count_replicate]
      have hlast : Fin.last d ≠ r.castSucc := by
        intro he
        have hv := congrArg Fin.val he
        simp only [Fin.val_last, Fin.val_castSucc] at hv
        omega
      simp only [hlast, ite_false, add_zero, Fin.castSucc_inj]
      simpa only [Finset.mem_univ, ite_true] using
        Finset.sum_ite_eq' Finset.univ r (fun i => (γ i).val)
    simpa only [h_boundedMultiIndexMultiset_count] using hm
  have hc := Fintype.card_le_of_injective encode hinj
  rw [Fintype.card_coe, Sym.card_sym_eq_choose, Fintype.card_fin] at hc
  have hsum : d + 1 + ℓ - 1 = d + ℓ := by omega
  rw [hsum, ← Nat.choose_symm (by omega : ℓ ≤ d + ℓ)] at hc
  have hsub : d + ℓ - ℓ = d := by omega
  simpa only [A, hsub] using hc
theorem holderNorm_of_global_mixed_bounds_binomial  (U F ℓ) (α B L : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hsup : ∀ γ : Fin d → Fin (ℓ + 1), (∑ i, (γ i).val) ≤ ℓ →
      ∀ x, |multiPartial F (fun i => (γ i).val) x| ≤ B)
    (hmod : ∀ γ : Fin d → Fin (ℓ + 1), (∑ i, (γ i).val) = ℓ → ∀ x y,
      |multiPartial F (fun i => (γ i).val) x - multiPartial F (fun i => (γ i).val) y| ≤
        L * euclideanNorm (x - y) ^ α) :
    holderNorm U F ℓ α ≤ ENNReal.ofReal (((d + ℓ).choose d : ℝ) * B + L) := by
  have hs (γ : Fin d → Fin (ℓ + 1)) (hγ : (∑ i, (γ i).val) ≤ ℓ) :
      derivativeSup U (multiPartial F (fun i => (γ i).val)) ≤ ENNReal.ofReal B := by
    apply iSup_le
    intro x
    exact ENNReal.ofReal_le_ofReal (hsup γ hγ x)
  have hh (γ : Fin d → Fin (ℓ + 1)) (hγ : (∑ i, (γ i).val) = ℓ) :
      holderSeminorm U (multiPartial F (fun i => (γ i).val)) α ≤ ENNReal.ofReal L := by
    apply iSup_le
    intro x
    apply iSup_le
    intro y
    by_cases hxy : (x : Covariate d) = y
    · simp [hxy]
    · simp only [ite_eq_right_iff.mpr (fun h => False.elim (hxy h))]
      apply ENNReal.ofReal_le_ofReal
      apply (div_le_iff₀ (Real.rpow_pos_of_pos
        (euclideanNorm_pos_of_ne_zero (x.val - y.val) (sub_ne_zero.mpr hxy)) α)).mpr
      exact hmod γ hγ x y
  let A := Finset.univ.filter (fun γ : Fin d → Fin (ℓ + 1) => (∑ i, (γ i).val) ≤ ℓ)
  have hsum : (∑ γ : Fin d → Fin (ℓ + 1),
      if (∑ i, (γ i).val) ≤ ℓ then
        derivativeSup U (multiPartial F (fun i => (γ i).val)) else 0) ≤
      ENNReal.ofReal (((d + ℓ).choose d : ℝ) * B) := by
    calc
      _ = ∑ γ ∈ A, derivativeSup U (multiPartial F (fun i => (γ i).val)) := by
        rw [Finset.sum_filter]
      _ ≤ ∑ _γ ∈ A, ENNReal.ofReal B := by
        apply Finset.sum_le_sum
        intro γ hγ
        exact hs γ (Finset.mem_filter.mp hγ).2
      _ = ENNReal.ofReal (↑A.card * B) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hB)]
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (by exact_mod_cast bounded_multiIndex_count_le d ℓ) hB)
  have hsem : (⨆ γ : Fin d → Fin (ℓ + 1), if (∑ i, (γ i).val) = ℓ then
      holderSeminorm U (multiPartial F (fun i => (γ i).val)) α else 0) ≤ ENNReal.ofReal L := by
    apply iSup_le
    intro γ
    split_ifs with h
    · exact hh γ h
    · exact bot_le
  rw [ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg _) hB) hL]
  exact add_le_add hsum hsem
def highWindowHolderConstant  (C : ModelConstants d) : ℝ :=
  ↑2 ^ d * (((d + C.order).choose d : ℝ) + 2)
theorem highFrameField_original_model_bounds  (C : ModelConstants d) :
    ∃ Cfr : ℝ, 1 ≤ Cfr ∧ ∀ k : ℕ, ∀ (_ : NeZero k), 4 ≤ k →
      ∀ cf : ℝ, 0 ≤ cf → ∀ P : HighWindowLabels d k → MvPolynomial (Fin d) ℝ,
      (∀ j, frameCoefficientL1 (P j) ≤ Cfr⁻¹) →
      let F := highFrameField d k (cf * ↑k ^ (-C.smoothness)) P
      (∀ x, |F x| ≤ ↑2 ^ d * (cf * ↑k ^ (-C.smoothness))) ∧
      (∀ γ : Fin d → Fin (C.order + 1), (∑ r, (γ r).val) ≤ C.order → ∀ x,
        |multiPartial F (fun r => (γ r).val) x| ≤ ↑2 ^ d * cf) ∧
      (∀ γ : Fin d → Fin (C.order + 1), (∑ r, (γ r).val) = C.order → ∀ x y,
        |multiPartial F (fun r => (γ r).val) x - multiPartial F (fun r => (γ r).val) y| ≤
          (2 * (↑2 ^ d * cf)) * euclideanNorm (x - y) ^ C.alpha) ∧
      (∀ U : Set (Covariate d), holderNorm U F C.order C.alpha ≤
        ENNReal.ofReal (highWindowHolderConstant C * cf)) := by
  have h_highFrameField_model_bounds : ∃ Cfr : ℝ, 1 ≤ Cfr ∧ ∀ k : ℕ, ∀ (_ : NeZero k), 4 ≤ k →
      ∀ cf : ℝ, 0 ≤ cf → ∀ P : HighWindowLabels d k → MvPolynomial (Fin d) ℝ,
      (∀ j, frameCoefficientL1 (P j) ≤ Cfr⁻¹) →
      let F := highFrameField d k (cf * (k : ℝ) ^ (-C.smoothness)) P
      (∀ x, |F x| ≤ (2 : ℝ) ^ d * (cf * (k : ℝ) ^ (-C.smoothness))) ∧
      (∀ γ : Fin d → Fin (C.order + 1), (∑ r, (γ r).val) ≤ C.order → ∀ x,
        |multiPartial F (fun r => (γ r).val) x| ≤ (2 : ℝ) ^ d * cf) ∧
      (∀ γ : Fin d → Fin (C.order + 1), (∑ r, (γ r).val) = C.order → ∀ x y,
        |multiPartial F (fun r => (γ r).val) x - multiPartial F (fun r => (γ r).val) y| ≤
          (2 * ((2 : ℝ) ^ d * cf)) * euclideanNorm (x - y) ^ C.alpha) ∧
      (∀ U : Set (Covariate d), holderNorm U F C.order C.alpha ≤
        ENNReal.ofReal (((((C.order + 1 : ℕ) : ℝ) ^ d + 2) * (2 : ℝ) ^ d) * cf)) := by
    have h_highFrameField_derivative_bound : ∃ Cfr : ℝ, 1 ≤ Cfr ∧ ∀ k : ℕ, ∀ (_ : NeZero k), 4 ≤ k → ∀ η : ℝ,
        ∀ P : HighWindowLabels d k → MvPolynomial (Fin d) ℝ,
        (∀ j, frameCoefficientL1 (P j) ≤ Cfr⁻¹) → ∀ q ≤ (C.order + 1), ∀ x : Covariate d,
        ‖iteratedFDeriv ℝ q (highFrameField d k η P) x‖ ≤
          |η| * (2 : ℝ) ^ d * (k : ℝ) ^ q := by
      obtain ⟨B, hB0, hB⟩ := highFrameProfile_derivative_bound d (C.order + 1)
      let Cfr := max B 1
      have hCfr1 : 1 ≤ Cfr := le_max_right _ _
      have hCfr0 : 0 < Cfr := lt_of_lt_of_le (by norm_num) hCfr1
      refine ⟨Cfr, hCfr1, ?_⟩
      intro k hk0 hk η P hP q hq x
      letI := hk0
      have hprofile (j : HighWindowLabels d k) (u : Covariate d) :
          ‖iteratedFDeriv ℝ q (highFrameProfile (P j)) u‖ ≤ 1 := by
        calc
          _ ≤ B * frameCoefficientL1 (P j) := hB (P j) q hq u
          _ ≤ Cfr * Cfr⁻¹ := mul_le_mul (le_max_left _ _) (hP j)
            (frameCoefficientL1_nonneg _) hCfr0.le
          _ = 1 := mul_inv_cancel₀ hCfr0.ne'
      have hchart (j : HighWindowLabels d k) :
          ‖iteratedFDeriv ℝ q (highPeriodizedChart d k j (highFrameProfile (P j))) x‖ ≤
            (k : ℝ) ^ q := by
        have h_highPeriodizedChart_derivative_bound (G : Covariate d → ℝ) (hG : ContDiff ℝ ∞ G) (hG0 : ∀ u, highWindowTensor d u = 0 → G u = 0) (hB : ∀ u, ‖iteratedFDeriv ℝ q G u‖ ≤ 1) : ‖iteratedFDeriv ℝ q (highPeriodizedChart d k j G) x‖ ≤ 1 * (k : ℝ) ^ q := by
          obtain ⟨z, hz, he⟩ := highPeriodizedChart_eventuallyEq_single d k hk j G hG0 x
          rw [(he.iteratedFDeriv ℝ q).eq_of_nhds]
          have hh := smooth_affine_iteratedFDeriv_bound G hG (k : ℝ)
            (fun r => (z r : ℝ)) x q 1 hB
          change ‖iteratedFDeriv ℝ q (fun y => G (fun r => (k : ℝ) * y r - z r)) x‖ ≤
            1 * |(k : ℝ)| ^ q at hh
          rwa [abs_of_nonneg (show (0 : ℝ) ≤ k from Nat.cast_nonneg k)] at hh
        simpa only [one_mul] using (h_highPeriodizedChart_derivative_bound _ (highFrameProfile_contDiff (P j)) (highFrameProfile_zero_of_window_zero (P j)) (hprofile j))
      have hsmooth (j : HighWindowLabels d k) :
          ContDiffAt ℝ q (highPeriodizedChart d k j (highFrameProfile (P j))) x :=
        ((highPeriodizedChart_contDiff d k j _ (highFrameProfile_contDiff (P j))
          (highFrameProfile_zero_of_window_zero (P j))).of_le (by simp)).contDiffAt
      have he : iteratedFDeriv ℝ q (highFrameField d k η P) x =
          η • ∑ j, iteratedFDeriv ℝ q (highPeriodizedChart d k j (highFrameProfile (P j))) x := by
        change iteratedFDeriv ℝ q
          (fun y => η • ∑ j, highPeriodizedChart d k j (highFrameProfile (P j)) y) x = _
        rw [iteratedFDeriv_const_smul_apply' (by
          apply ContDiffAt.sum
          intro j hj
          exact hsmooth j), iteratedFDeriv_fun_sum_apply (fun j _ => hsmooth j)]
      rw [he, norm_smul, Real.norm_eq_abs]
      have hh := finite_sum_norm_le_active_count
        (fun j => iteratedFDeriv ℝ q (highPeriodizedChart d k j (highFrameProfile (P j))) x)
        (2 ^ d) ((k : ℝ) ^ q) (pow_nonneg (Nat.cast_nonneg k) _) hchart
        (highPeriodizedChart_derivative_overlap d k hk (fun j => highFrameProfile (P j))
          (fun j => highFrameProfile_zero_of_window_zero (P j)) q x)
      have hh' := mul_le_mul_of_nonneg_left hh (abs_nonneg η)
      push_cast at hh'
      convert hh' using 1 <;> ring
    obtain ⟨Cfr, hCfr1, hCfr⟩ := h_highFrameField_derivative_bound
    refine ⟨Cfr, hCfr1, ?_⟩
    intro k hk0 hk cf hcf P hP
    letI := hk0
    let F := highFrameField d k (cf * (k : ℝ) ^ (-C.smoothness)) P
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    have hA : 0 ≤ (2 : ℝ) ^ d * cf := by positivity
    have hbound : ∀ q ≤ C.order + 1, ∀ x,
        ‖iteratedFDeriv ℝ q F x‖ ≤ ((2 : ℝ) ^ d * cf) *
          (k : ℝ) ^ ((q : ℝ) - C.smoothness) := by
      intro q hq x
      have hh := hCfr k hk0 hk (cf * (k : ℝ) ^ (-C.smoothness)) P hP q hq x
      have hη : 0 ≤ cf * (k : ℝ) ^ (-C.smoothness) := by positivity
      rw [abs_of_nonneg hη] at hh
      have hp : (k : ℝ) ^ (-C.smoothness) * (k : ℝ) ^ q =
          (k : ℝ) ^ ((q : ℝ) - C.smoothness) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add (lt_of_lt_of_le (by norm_num) hkR)]
        congr 1
        ring
      convert hh using 1
      rw [← hp]
      ring
    obtain ⟨hs, hm⟩ := mixed_bounds_of_scaled_derivatives C F
      (highFrameField_contDiff _ _ _ _) (k : ℝ) ((2 : ℝ) ^ d * cf) hkR hA hbound
    have hvalue (x : Covariate d) :
        |F x| ≤ (2 : ℝ) ^ d * (cf * (k : ℝ) ^ (-C.smoothness)) := by
      have hh := hCfr k hk0 hk (cf * (k : ℝ) ^ (-C.smoothness)) P hP 0 (by omega) x
      have hη : 0 ≤ cf * (k : ℝ) ^ (-C.smoothness) := by positivity
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_nonneg hη, pow_zero,
        mul_one] at hh
      simpa only [F, mul_comm] using hh
    refine ⟨hvalue, hs, hm, ?_⟩
    intro U
    have hh := holderNorm_of_scaled_derivatives C U F (highFrameField_contDiff _ _ _ _)
      (k : ℝ) ((2 : ℝ) ^ d * cf) hkR hA hbound
    convert hh using 1
    congr 1
    ring
  obtain ⟨Cfr, hCfr, hbound⟩ := h_highFrameField_model_bounds
  refine ⟨Cfr, hCfr, ?_⟩
  intro k hk0 hk cf hcf P hP
  letI := hk0
  obtain ⟨hv, hs, hm, _⟩ := hbound k hk0 hk cf hcf P hP
  refine ⟨hv, hs, hm, ?_⟩
  intro U
  have hh := holderNorm_of_global_mixed_bounds_binomial U _ C.order C.alpha
    (↑2 ^ d * cf) (2 * (↑2 ^ d * cf)) (by positivity) (by positivity) hs hm
  convert hh using 1
  congr 1
  unfold highWindowHolderConstant
  ring
theorem highFrame_ternary_amplitude_guards  {C : ModelConstants d}
    (Q : LowSmoothnessTernaryConstants C) :
    ∃ η0 : ℝ, 0 < η0 ∧ ∀ η : ℝ, 0 ≤ η → η ≤ η0 →
      η ^ 2 ≤ Q.ρ ∧ ↑2 ^ d * η ≤ Q.ρ / 2 := by
  let η0 := min (Real.sqrt Q.ρ) (Q.ρ / (2 * ↑2 ^ d))
  refine ⟨η0, (by dsimp [η0]; exact lt_min (Real.sqrt_pos.2 Q.ρ_pos) (div_pos Q.ρ_pos (by positivity))), ?_⟩
  intro η hη hηU
  have  := hηU.trans (min_le_left _ _)
  constructor
  · nlinarith [Real.sq_sqrt Q.ρ_pos.le, Real.sqrt_nonneg Q.ρ]
  · have := (le_div_iff₀ (by positivity : 0 < 2 * (2 : ℝ) ^ d)).mp (hηU.trans (min_le_right _ _))
    nlinarith
theorem highWindowHolderConstant_pos  (C : ModelConstants d) :
    0 < highWindowHolderConstant C := by
  unfold highWindowHolderConstant
  positivity
theorem frameCoefficientL1_sum_monomial_le   [Fintype I]
    (e : I → Fin d →₀ ℕ) (c : I → ℝ) :
    frameCoefficientL1 (∑ i, MvPolynomial.monomial (e i) (c i)) ≤ ∑ i, |c i| := by
  let P : MvPolynomial (Fin d) ℝ := ∑ i, MvPolynomial.monomial (e i) (c i)
  calc
    _ ≤ ∑ β ∈ P.support, ∑ i, |(MvPolynomial.monomial (e i) (c i)).coeff β| := by
      apply Finset.sum_le_sum
      intro β hβ
      rw [MvPolynomial.coeff_sum]
      simpa only [Real.norm_eq_abs] using norm_sum_le Finset.univ
        (fun i => (MvPolynomial.monomial (e i) (c i)).coeff β)
    _ = ∑ i, ∑ β ∈ P.support, |(MvPolynomial.monomial (e i) (c i)).coeff β| :=
      Finset.sum_comm
    _ ≤ ∑ i, |c i| := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [MvPolynomial.coeff_monomial, apply_ite abs, abs_zero]
      rw [Finset.sum_ite_eq]
      split_ifs
      · exact le_rfl
      · exact abs_nonneg _
def highFramePolynomial  (c : HighFrameIndex d D → ℝ) :
    MvPolynomial (Fin d) ℝ :=
  ∑ γ, MvPolynomial.monomial (polynomialBoxExponent γ.val) (c γ)
theorem highFramePolynomial_coefficientL1_le {d D : ℕ} (c : HighFrameIndex d D → ℝ) :
    frameCoefficientL1 (highFramePolynomial c) ≤ ∑ γ, |c γ| :=
  frameCoefficientL1_sum_monomial_le _ _
end NearlyMinimax
