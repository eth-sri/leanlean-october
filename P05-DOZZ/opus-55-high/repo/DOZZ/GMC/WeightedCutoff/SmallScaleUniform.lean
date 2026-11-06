module

public import DOZZ.GMC.WeightedCutoff.ReferenceUniform
public import DOZZ.GMC.Moments.WeightedCutoffAllOrders

/-! # Exact small-ball scale bounds uniform in the coupling and moment order -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Reference moment uniformity combined with the exact local scaling law, including the
order one endpoint. -/
theorem regularizedGMC_openBall_root_bound_compact_gamma_small_chart
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (Γ : Set ℝ) (hΓ : IsCompact Γ) (hΓpos : ∀ γ ∈ Γ, 0 < γ)
    (q : ℝ) (hq : 1 < q) (hcrit : ∀ γ ∈ Γ, q < 4 / γ ^ 2) :
    ∃ A : ℝ≥0∞, A < ⊤ ∧ ∀ γ ∈ Γ, ∀ p : ℝ, 1 ≤ p → p ≤ q →
      ∀ (z : ℂ) (R δ : ℝ), 0 < R → R ≤ 1 / 8 → 0 < δ → δ ≤ R →
      ‖z‖ + 2 * R ≤ 1 →
      ((∫⁻ ω, (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) ^ p ∂P) ^
        (1 / p) ≤ A * ENNReal.ofReal ((R / (1 / 8 : ℝ)) ^
          ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p))) ∧
      (∫⁻ ω, (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) ^ p ∂P) < ⊤ := by
  let _ := hX.1
  obtain ⟨Cref, hCref, hRef⟩ := regularizedGMC_reference_positive_moment_compact_gamma_all_cutoffs
    P X hX Xc hXc Γ hΓ hΓpos q hq hcrit
  let R₀ : ℝ := 1 / 8
  let Csmall : ℝ≥0∞ := 1 + Cref
  let A := Csmall
  have hCsmall := ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hCref⟩
  have hCsmallOne : 1 ≤ Csmall := by aesop
  have hCsmallA : Csmall ≤ A := le_rfl
  refine ⟨A, hCsmall, ?_⟩
  intro γ hγ p hp hpq z R δ hR hRsmall hδ hδR hchart
  have hp0 := lt_of_lt_of_le zero_lt_one hp
  let beta := (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p
  let t := Real.log (1 / δ)
  have hR₀pos : 0 < R₀ := by positivity
  have hR₀one : R₀ < 1 := by norm_num
  have hδeq : Real.exp (-t) = δ := by
    dsimp [t]
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  have hratio : δ * (R₀ / R) ≤ R₀ := by
    calc
      δ * (R₀ / R) ≤ R * (R₀ / R) := (mul_le_mul_of_nonneg_right hδR (div_nonneg (le_of_lt hR₀pos) hR.le))
      _ = R₀ := by field_simp
  have hbase : R₀ + Real.exp (-t) * (R₀ / R) ≤ 1 := by
    rw [hδeq]
    calc
      R₀ + δ * (R₀ / R) ≤ R₀ + R₀ := by
        simpa [add_comm] using add_le_add_left hratio R₀
      _ ≤ 1 := by norm_num
  have htarget : ‖z‖ + R + Real.exp (-t) ≤ 1 := by
    rw [hδeq]
    linarith
  have htbase : 0 ≤ t + Real.log (R / R₀) := by
    have hquot : 1 ≤ R / (δ * R₀) := by
      apply (le_div_iff₀ (mul_pos hδ hR₀pos)).2
      have hδR₀ :=
        mul_le_mul_of_nonneg_right hδR (le_of_lt hR₀pos)
      have hR₀le : R * R₀ ≤ R := by nlinarith
      simpa using hδR₀.trans hR₀le
    have hlog := Real.log_nonneg hquot
    have hlogmul : Real.log (R / (δ * R₀)) = t + Real.log (R / R₀) := by
      have hmul : (1 / δ) * (R / R₀) = R / (δ * R₀) := by
        field_simp [ne_of_gt hδ, ne_of_gt hR₀pos]
      rw [← hmul, Real.log_mul (by positivity) (by positivity)]
    rwa [← hlogmul]
  let massQ : Ω → ℝ≥0∞ := fun ω =>
    regularizedGMC P Xc γ (t + Real.log (R / R₀)) ω (Metric.ball 0 R₀)
  have hmassQ : AEMeasurable massQ P := regularizedGMC_mass_aemeasurable P X hX Xc hXc γ
      (t + Real.log (R / R₀)) (Metric.ball 0 R₀) Metric.isOpen_ball.measurableSet
  have hRefp : (∫⁻ ω, ENNReal.rpow (massQ ω) p ∂P) ≤ Csmall := by
    calc
      _ ≤ P Set.univ + ∫⁻ ω, ENNReal.rpow (massQ ω) q ∂P :=
        lintegral_rpow_le_measure_add_larger_order P massQ hmassQ
          (by linarith) (hpq)
      _ = 1 + gmcMassMoment P
          (regularizedGMC P Xc γ (t + Real.log (R / R₀)))
          (Metric.ball 0 R₀) q := by
        change P Set.univ + gmcMassMoment P
          (regularizedGMC P Xc γ (t + Real.log (R / R₀)))
          (Metric.ball 0 R₀) q = _
        rw [hX.1.measure_univ]
      _ ≤ Csmall := by
        dsimp [Csmall]
        simpa [add_comm, gmcMassMoment, R₀] using add_le_add_left (hRef γ hγ (t + Real.log (R / R₀)) htbase) 1
  have hRefpMass : gmcMassMoment P
      (regularizedGMC P Xc γ (t + Real.log (R / R₀))) (Metric.ball 0 R₀) p ≤ Csmall := by
    simpa [gmcMassMoment, massQ] using hRefp
  have hscale := regularizedGMC_local_ball_moment_scale P X hX γ Xc hXc z
    (s := R) hR hRsmall hR₀pos hR₀one
    (by linarith) hbase htarget p
  have hmoment : (∫⁻ ω, ENNReal.rpow
      (regularizedGMC P Xc γ t ω (Metric.ball z R)) p ∂P) ≤
        Csmall * ENNReal.ofReal ((R / R₀) ^
          (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2)) := by
    change gmcMassMoment P _ _ p ≤ _
    rw [hscale]
    calc
      _ = gmcMassMoment P
          (regularizedGMC P Xc γ (t + Real.log (R / R₀)))
          (Metric.ball 0 R₀) p * ENNReal.ofReal
            ((R / R₀) ^ (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2)) := by ac_rfl
      _ ≤ Csmall * ENNReal.ofReal
          ((R / R₀) ^ (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2)) :=
        mul_le_mul' hRefpMass le_rfl
  have hrootConst := ennreal_root_mul_ofReal_rpow_eq Csmall hCsmall
    (R / R₀) (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) p
    (div_pos hR hR₀pos) hp0
  have hCroot : Csmall ^ (1 / p) ≤ Csmall := by
    calc
      Csmall ^ (1 / p) ≤ Csmall ^ 1 :=
        ENNReal.rpow_le_rpow_of_exponent_le hCsmallOne
          ((div_le_iff₀ hp0).2 (by linarith))
      _ = Csmall := by simp
  have hroot :
      (∫⁻ ω, ENNReal.rpow
        (regularizedGMC P Xc γ t ω (Metric.ball z R)) p ∂P) ^ (1 / p) ≤
        Csmall * ENNReal.ofReal ((R / R₀) ^ beta) := by
    calc
      _ ≤ (Csmall * ENNReal.ofReal ((R / R₀) ^
          (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2))) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hmoment (one_div_nonneg.mpr hp0.le)
      _ = Csmall ^ (1 / p) * ENNReal.ofReal _ := by
        rw [hrootConst]
      _ ≤ Csmall * ENNReal.ofReal _ :=
        mul_le_mul_of_nonneg_right hCroot (by positivity)
  refine ⟨?_, (hmoment.trans_lt (ENNReal.mul_lt_top hCsmall ENNReal.ofReal_lt_top))⟩
  calc
    _ ≤ Csmall * ENNReal.ofReal _ := hroot
    _ ≤ A * ENNReal.ofReal _ :=
      mul_le_mul_of_nonneg_right hCsmallA (by positivity)
    _ = _ := by rfl

end DOZZ.Proofs
