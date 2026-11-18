/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FieldChaosNegativePower
public import DOZZ.GMC.FiniteChaosMultiNegativePower
public import DOZZ.GMC.FiniteMultiMellin
public import DOZZ.Statements.GMC.FieldChaosMass

/-! Multiblock negative powers for continuum field chaos. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

private lemma fieldChaosMass_sum_toReal_ae
    {Ω S κ : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Fintype κ] [Nonempty S]
    (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (ν : FiniteMeasure S) (hν : ν ≠ 0) (h : κ → S → ℝ≥0) (hh : ∀ k, Measurable (h k))
    (hhb : ∀ k, ∃ c : ℝ≥0, ∀ x, h k x ≤ c) (γ : ℝ) (t : κ → ℝ) (ht : ∀ k, 0 ≤ t k)
    (hpos : ∀ k, 0 < ∫ x, (h k x : ℝ) ∂(ν.normalize : Measure S)) :
    ∀ᵐ ω ∂P, (DOZZ.fieldChaosMass P Φ (ν : Measure S)
        (fun x => ∑ k, Real.toNNReal (t k) * h k x) γ ω).toReal =
      ∑ k, t k * (DOZZ.fieldChaosMass P Φ (ν : Measure S) (h k) γ ω).toReal := by
  classical
  have hvar : Measurable fun x => ∫ ω', Φ ω' x ^ 2 ∂P := by
    simpa [DOZZ.gaussianVariance, DOZZ.gaussianCovariance, pow_two] using
      centeredGaussianField_variance_measurable P Φ hΦ
  have hfin (k : κ) : ∀ᵐ ω ∂P, DOZZ.fieldChaosMass P Φ (ν : Measure S) (h k) γ ω ≠ ∞ := by
    filter_upwards [fieldChaosMass_eq_ofReal_modified_toReal_ae P Φ hΦ ν hν (h k)
      (hh k) (hhb k) γ (hpos k)] with ω hω
    rw [hω]; exact ENNReal.ofReal_ne_top
  filter_upwards [ae_all_iff.2 hfin] with ω hω
  have : Measurable fun x => Φ ω x := hΦ.1.comp (measurable_const.prodMk measurable_id)
  let wick : S → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (γ * Φ ω x - γ ^ 2 / 2 * ∫ ω', Φ ω' x ^ 2 ∂P))
  have hw_meas (k : κ) : Measurable fun x => (h k x : ℝ≥0∞) * wick x := by fun_prop
  have hsum_eq : DOZZ.fieldChaosMass P Φ (ν : Measure S)
      (fun x => ∑ k, Real.toNNReal (t k) * h k x) γ ω =
      ∑ k, ENNReal.ofReal (t k) * DOZZ.fieldChaosMass P Φ (ν : Measure S) (h k) γ ω := by
    unfold DOZZ.fieldChaosMass
    rw [show (fun x => (↑(∑ k, Real.toNNReal (t k) * h k x) : ℝ≥0∞) * wick x) =
        fun x => ∑ k, ENNReal.ofReal (t k) * ((h k x : ℝ≥0∞) * wick x) by
      ext x; simp [Finset.sum_mul, ENNReal.ofReal, mul_assoc]]
    rw [lintegral_finsetSum' _ fun k _ => ((hw_meas k).const_mul _).aemeasurable]
    exact Finset.sum_congr rfl fun k _ => lintegral_const_mul'' _ (hw_meas k).aemeasurable
  rw [hsum_eq, ENNReal.toReal_sum fun k _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hω k)]
  exact Finset.sum_congr rfl fun k _ => by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (ht k)]

private lemma fieldChaosMass_multi_mellin
    {Ω S K : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Fintype K] [Nonempty S]
    (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (ν : FiniteMeasure S) (hν : ν ≠ 0) (h : K → S → ℝ≥0) (hh : ∀ k, Measurable (h k))
    (hhb : ∀ k, ∃ c : ℝ≥0, ∀ x, h k x ≤ c) (γ : ℝ) (q : K → ℝ) (hq : ∀ k, 0 < q k)
    (hpos : ∀ k, 0 < ∫ x, (h k x : ℝ) ∂(ν.normalize : Measure S)) :
    (∫⁻ ω, ∏ k : K, ENNReal.rpow (DOZZ.fieldChaosMass P Φ (ν : Measure S) (h k) γ ω) (-q k) ∂P) =
      (∏ k : K, ENNReal.ofReal (1 / Real.Gamma (q k))) *
        ∫⁻ t, ENNReal.ofReal (∏ k : K, t k ^ (q k - 1)) *
          (∫⁻ ω, ENNReal.ofReal (Real.exp (-∑ k : K, t k *
            (DOZZ.fieldChaosMass P Φ (ν : Measure S) (h k) γ ω).toReal)) ∂P)
        ∂Measure.pi (fun _ : K => volume.restrict (Ioi (0 : ℝ))) := by
  classical
  have := (hΦ.2 0 Fin.elim0).1
  let M : Ω → K → ℝ≥0∞ := fun ω k => DOZZ.fieldChaosMass P Φ (ν : Measure S) (h k) γ ω
  let m : Ω → K → ℝ := fun ω k => if (M ω k).toReal = 0 then 1 else (M ω k).toReal
  have hmPos (ω : Ω) (k : K) : 0 < m ω k := by
    dsimp [m]; split_ifs with hz <;> [norm_num; exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz)]
  have hEq (k : K) : ∀ᵐ ω ∂P, M ω k = ENNReal.ofReal (m ω k) :=
    fieldChaosMass_eq_ofReal_modified_toReal_ae P Φ hΦ ν hν (h k) (hh k) (hhb k) γ (hpos k)
  have htoR (k : K) : ∀ᵐ ω ∂P, (M ω k).toReal = m ω k := by
    filter_upwards [hEq k] with ω hω; rw [hω, ENNReal.toReal_ofReal (hmPos ω k).le]
  let νK : K → Measure ℝ := fun _ => volume.restrict (Ioi (0 : ℝ))
  let T : Measure (K → ℝ) := Measure.pi νK
  let f : Ω → (K → ℝ) → ℝ≥0∞ := fun ω t =>
    ∏ k : K, ENNReal.ofReal (t k ^ (q k - 1) * Real.exp (-(m ω k * t k)))
  have hmMeas (k : K) : Measurable fun ω => m ω k := by
    have hMm := centeredGaussianField_fieldChaosMass_measurable P Φ hΦ (ν : Measure S) (h k) (hh k) γ
    exact Measurable.ite (measurableSet_eq_fun hMm.ennreal_toReal measurable_const)
      measurable_const hMm.ennreal_toReal
  have hfProd : AEMeasurable (Function.uncurry f) (P.prod T) := by fun_prop
  have hpt : ∀ᵐ ω ∂P, (∏ k : K, ENNReal.rpow (M ω k) (-q k)) =
      (∏ k : K, ENNReal.ofReal (1 / Real.Gamma (q k))) * ∫⁻ t, f ω t ∂T := by
    filter_upwards [ae_all_iff.2 hEq] with ω hω
    have hsc (k : K) : ENNReal.rpow (M ω k) (-q k) =
        ENNReal.ofReal (1 / Real.Gamma (q k)) * ∫⁻ s in Ioi (0 : ℝ),
          ENNReal.ofReal (s ^ (q k - 1) * Real.exp (-(m ω k * s))) := by
      rw [hω k]
      change ENNReal.ofReal (m ω k) ^ (-q k) = _
      rw [ENNReal.ofReal_rpow_of_pos (hmPos ω k)]
      exact ofReal_rpow_neg_eq_mellin_lintegral (hmPos ω k) (hq k)
    simp_rw [hsc, Finset.prod_mul_distrib]
    congr 1
    simpa [T, νK, f] using (lintegral_pi_prod νK
      (fun k s => ENNReal.ofReal (s ^ (q k - 1) * Real.exp (-(m ω k * s))))
      (fun _ => inferInstance) (fun _ => by fun_prop)).symm
  rw [lintegral_congr_ae hpt, lintegral_const_mul'' _ hfProd.lintegral_prod_right,
    lintegral_lintegral_swap hfProd]
  congr 1
  have htPos : ∀ᵐ t ∂T, ∀ k : K, 0 < t k := ae_all_iff.2 fun k => by
    rw [ae_iff]
    have h0 : νK k (Iic (0 : ℝ)) = 0 := by
      rw [show νK k = volume.restrict (Ioi (0 : ℝ)) from rfl,
        Measure.restrict_apply measurableSet_Iic, inter_comm, Ioi_inter_Iic]
      simp
    simpa [Function.eval, preimage, mem_Iic] using Measure.pi_eval_preimage_null νK h0
  refine lintegral_congr_ae ?_
  filter_upwards [htPos] with t ht
  have hfk (ω : Ω) : f ω t = ENNReal.ofReal (∏ k : K, t k ^ (q k - 1)) *
      ENNReal.ofReal (Real.exp (-∑ k : K, t k * m ω k)) := by
    dsimp [f]
    rw [Finset.prod_congr rfl fun k _ => ENNReal.ofReal_mul (Real.rpow_nonneg (ht k).le _),
      Finset.prod_mul_distrib,
      ← ENNReal.ofReal_prod_of_nonneg fun k _ => Real.rpow_nonneg (ht k).le _,
      ← ENNReal.ofReal_prod_of_nonneg fun _ _ => Real.exp_nonneg _, ← Real.exp_sum]
    congr 3; simp [Finset.sum_neg_distrib, mul_comm]
  simp_rw [hfk]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [ae_all_iff.2 htoR] with ω hω
  congr 3
  exact Finset.sum_congr rfl fun k _ => congrArg (t k * ·) (hω k).symm

/-- The continuum multiblock negative-power comparison follows by taking the Mellin transform of
the joint Laplace comparison for positive linear combinations of block masses. -/
theorem kahane_field_multi_negative_power
    {ΩX ΩY S κ : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [MeasurableSpace S] [Fintype κ]
    (PX : Measure ΩX) (PY : Measure ΩY) (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField PX Φ) (hΨ : DOZZ.IsCenteredGaussianField PY Ψ)
    (ν : Measure S) [IsFiniteMeasure ν] (h : κ → S → ℝ≥0)
    (hh : ∀ k, Measurable (h k))
    (hhb : ∀ k, ∃ c : ℝ≥0, ∀ x, h k x ≤ c)
    (γ : ℝ) (q : κ → ℝ) (hq : ∀ k, 0 ≤ q k)
    (hcov : ∀ᵐ xy ∂ν.prod ν,
      ∫ ω, Φ ω xy.1 * Φ ω xy.2 ∂PX ≤ ∫ ω, Ψ ω xy.1 * Ψ ω xy.2 ∂PY)
    (hdiag : ∀ᵐ x ∂ν,
      ∫ ω, Φ ω x ^ 2 ∂PX ≤ ∫ ω, Ψ ω x ^ 2 ∂PY) :
    ∫⁻ ω, ∏ k, ENNReal.rpow (DOZZ.fieldChaosMass PX Φ ν (h k) γ ω) (-q k) ∂PX ≤
      ∫⁻ ω, ∏ k, ENNReal.rpow (DOZZ.fieldChaosMass PY Ψ ν (h k) γ ω) (-q k) ∂PY := by
  classical
  have hPX := (hΦ.2 0 Fin.elim0).1
  have hPY := (hΨ.2 0 Fin.elim0).1
  let K := {k : κ // 0 < q k}
  by_cases hK : Nonempty K
  · by_cases hν0 : ν = 0
    · obtain ⟨k₀⟩ := hK
      have htop (ω : ΩY) : (∏ k, ENNReal.rpow (DOZZ.fieldChaosMass PY Ψ ν (h k) γ ω) (-q k)) = ⊤ := by
        refine WithTop.prod_eq_top (Finset.mem_univ k₀.val) ?_ fun k _ => ?_
        · rw [ENNReal.rpow_eq_pow]; simp [DOZZ.fieldChaosMass, hν0, ENNReal.zero_rpow_of_neg (neg_lt_zero.mpr k₀.2)]; rfl
        · by_cases hk0 : q k = 0
          · rw [ENNReal.rpow_eq_pow, hk0, neg_zero, ENNReal.rpow_zero]; exact (one_ne_zero : (1 : ℝ≥0∞) ≠ 0)
          · rw [ENNReal.rpow_eq_pow]
            simp [DOZZ.fieldChaosMass, hν0,
              ENNReal.zero_rpow_of_neg (neg_lt_zero.mpr (lt_of_le_of_ne (hq k) (Ne.symm hk0)))]
            exact ENNReal.top_ne_zero
      simp_rw [htop]
      rw [lintegral_const, hPY.measure_univ, mul_one]
      exact le_top
    let νf : FiniteMeasure S := ⟨ν, inferInstance⟩
    have hνf : νf ≠ 0 := fun hz => hν0 (congrArg (fun μ : FiniteMeasure S => (μ : Measure S)) hz)
    obtain ⟨x₀, _⟩ := nonempty_of_measure_ne_zero (Measure.measure_univ_ne_zero.mpr hν0)
    have : Nonempty S := ⟨x₀⟩
    have hsub (z : κ → ℝ≥0∞) (hz : ∀ k : {k : κ // ¬ 0 < q k}, z k.1 = 1) :
        (∏ k : κ, z k) = ∏ k : K, z k.1 := by
      rw [← Fintype.prod_subtype_mul_prod_subtype (fun k => 0 < q k),
        Finset.prod_eq_one fun k _ => hz k, mul_one]
    rw [lintegral_congr_ae (ae_of_all _ fun ω => hsub _ fun k => by
        rw [ENNReal.rpow_eq_pow, le_antisymm (not_lt.mp k.2) (hq k.1), neg_zero, ENNReal.rpow_zero]),
      lintegral_congr_ae (ae_of_all _ fun ω => hsub _ fun k => by
        rw [ENNReal.rpow_eq_pow, le_antisymm (not_lt.mp k.2) (hq k.1), neg_zero, ENNReal.rpow_zero])]
    change (∫⁻ ω, ∏ k : K, ENNReal.rpow (DOZZ.fieldChaosMass PX Φ (νf : Measure S) (h k.1) γ ω) (-q k.1) ∂PX) ≤
      ∫⁻ ω, ∏ k : K, ENNReal.rpow (DOZZ.fieldChaosMass PY Ψ (νf : Measure S) (h k.1) γ ω) (-q k.1) ∂PY
    by_cases hw : ∀ k : K, 0 < ∫ x, (h k.val x : ℝ) ∂(νf.normalize : Measure S)
    · rw [fieldChaosMass_multi_mellin PX Φ hΦ νf hνf (fun k : K => h k.1) (fun k => hh k.1)
          (fun k => hhb k.1) γ (fun k : K => q k.1) (fun k => k.2) hw,
        fieldChaosMass_multi_mellin PY Ψ hΨ νf hνf (fun k : K => h k.1) (fun k => hh k.1)
          (fun k => hhb k.1) γ (fun k : K => q k.1) (fun k => k.2) hw]
      refine mul_le_mul_right (lintegral_mono_ae ?_) _
      have htPos : ∀ᵐ t ∂Measure.pi (fun _ : K => volume.restrict (Ioi (0 : ℝ))), ∀ k : K, 0 < t k :=
        ae_all_iff.2 fun k => by
          rw [ae_iff]
          have h0 : (volume.restrict (Ioi (0 : ℝ))) (Iic (0 : ℝ)) = 0 := by
            rw [Measure.restrict_apply measurableSet_Iic, inter_comm, Ioi_inter_Iic]; simp
          simpa [Function.eval, preimage, mem_Iic] using
            Measure.pi_eval_preimage_null (fun _ : K => volume.restrict (Ioi (0 : ℝ))) h0
      filter_upwards [htPos] with t ht
      refine mul_le_mul_right ?_ _
      choose c hc using fun k : K => hhb k.1
      have hsumB : ∃ B : ℝ≥0, ∀ x, (∑ k : K, Real.toNNReal (t k) * h k.1 x) ≤ B :=
        ⟨∑ k, Real.toNNReal (t k) * c k, fun x => Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_left (hc k x) (NNReal.coe_nonneg _)⟩
      have ht0 (k : K) : 0 ≤ t k := (ht k).le
      have hX := fieldChaosMass_sum_toReal_ae PX Φ hΦ νf hνf (fun k => h k.1)
        (fun k => hh k.1) (fun k => hhb k.1) γ t ht0 hw
      have hY := fieldChaosMass_sum_toReal_ae PY Ψ hΨ νf hνf (fun k => h k.1)
        (fun k => hh k.1) (fun k => hhb k.1) γ t ht0 hw
      have hLap := kahane_field_laplace_of_nonzero_finite_measure_eq PX PY Φ Ψ hΦ hΨ νf hνf
        (fun x => ∑ k : K, Real.toNNReal (t k) * h k.1 x) (by fun_prop) hsumB γ 1 zero_le_one
        hcov (by
          filter_upwards [hdiag] with x hx
          simpa [DOZZ.gaussianVariance, DOZZ.gaussianCovariance, pow_two] using hx)
      refine (lintegral_congr_ae ?_).trans_le ((show _ ≤ _ by simpa using hLap).trans_eq (lintegral_congr_ae ?_))
      · filter_upwards [hX] with ω hω; rw [hω]
      · filter_upwards [hY] with ω hω; rw [hω]
    · push Not at hw
      obtain ⟨kbad, hkbad⟩ := hw
      have hz0 : ∫ x, (h kbad.1 x : ℝ) ∂(νf.normalize : Measure S) = 0 :=
        le_antisymm hkbad (integral_nonneg fun _ => NNReal.coe_nonneg _)
      have hne0 (k : K) : ∀ᵐ ω ∂PY,
          ENNReal.rpow (DOZZ.fieldChaosMass PY Ψ (νf : Measure S) (h k.1) γ ω) (-q k.1) ≠ 0 := by
        by_cases hk0 : ∫ x, (h k.1 x : ℝ) ∂(νf.normalize : Measure S) = 0
        · have hz := centeredGaussianField_fieldChaosMass_eq_zero_of_zero_weight_integral
            PY Ψ νf (h k.1) (hh k.1) (hhb k.1) γ hk0
          exact ae_of_all _ fun ω => by
            rw [ENNReal.rpow_eq_pow, hz ω, ENNReal.zero_rpow_of_neg (neg_lt_zero.mpr k.2)]
            exact ENNReal.top_ne_zero
        · have hpos : 0 < ∫ x, (h k.1 x : ℝ) ∂(νf.normalize : Measure S) :=
            lt_of_le_of_ne (integral_nonneg fun _ => NNReal.coe_nonneg _) (Ne.symm hk0)
          filter_upwards [centeredGaussianField_fieldChaosMass_pos_ae_of_pos_weight_integral
              PY Ψ hΨ νf hνf (h k.1) (hh k.1) (hhb k.1) γ hpos,
            fieldChaosMass_eq_ofReal_modified_toReal_ae PY Ψ hΨ νf hνf (h k.1) (hh k.1) (hhb k.1) γ hpos]
            with ω hp hf
          exact (ENNReal.rpow_pos hp (by rw [hf]; exact ENNReal.ofReal_ne_top)).ne'
      have htopY : ∀ᵐ ω ∂PY, (∏ k : K, ENNReal.rpow
          (DOZZ.fieldChaosMass PY Ψ (νf : Measure S) (h k.1) γ ω) (-q k.1)) = ⊤ := by
        have hbad0 := centeredGaussianField_fieldChaosMass_eq_zero_of_zero_weight_integral
          PY Ψ νf (h kbad.1) (hh kbad.1) (hhb kbad.1) γ hz0
        filter_upwards [ae_all_iff.2 hne0] with ω hω
        refine WithTop.prod_eq_top (Finset.mem_univ kbad) ?_ fun k _ => hω k
        rw [ENNReal.rpow_eq_pow, hbad0 ω, ENNReal.zero_rpow_of_neg (neg_lt_zero.mpr kbad.2)]; rfl
      rw [lintegral_congr_ae htopY, lintegral_const, hPY.measure_univ, mul_one]
      exact le_top
  · have hq0 (k : κ) : q k = 0 := by
      by_contra hne
      exact hK ⟨⟨k, lt_of_le_of_ne (hq k) (Ne.symm hne)⟩⟩
    simp_rw [ENNReal.rpow_eq_pow, hq0, neg_zero, ENNReal.rpow_zero]
    simp [hPX.measure_univ, hPY.measure_univ]

end DOZZ.Proofs
