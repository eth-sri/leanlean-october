module
public import DensityEnergyGM.LargeValuesCubic
public import GuthMaynard.NativeSource.GuthMaynard.TypeIIFourthMomentReduction

@[expose] public section

open Complex Finset Filter MeasureTheory Real Set ComplexConjugate
open scoped BigOperators Interval

namespace GuthMaynard.NativeMoment

/-!
# Quantitative complete-frequency smooth reflection

This file completes Guth--Maynard Lemma 6.2 for the exact trace Fourier
coefficient and connects it to the complete scaled tail used by `gmCubicS2`.
-/

/-- The complete unscaled nonzero integer-frequency series in Lemma 6.2. -/
noncomputable def gmTraceNonzeroFourierSum
    (cutoff : GMSmoothCutoff) (N : ℕ) (t : ℝ) : ℂ :=
  ∑' m : ℤ, if m = 0 then 0 else
    gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ))

/-- The omitted unscaled frequencies outside the symmetric window. -/
noncomputable def gmTraceFourierFarTail
    (cutoff : GMSmoothCutoff) (N M : ℕ) (t : ℝ) : ℂ :=
  ∑' m : ℤ, if M < m.natAbs then
    gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ)) else 0

theorem gmTraceFourier_summable (cutoff : GMSmoothCutoff)
    (N : ℕ) (hN : 0 < N) (t : ℝ) :
    Summable (fun m : ℤ =>
      gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ))) := by
  have hScaled := gmScaledTraceFourier_summable cutoff t (N : ℝ)
    (by exact_mod_cast hN)
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  exact (summable_mul_left_iff hNC).mp (by simpa using hScaled)

/-- Exact sign decomposition of the finite nonzero integer window. -/
theorem gmTraceFourierCentral_eq_signed
    (cutoff : GMSmoothCutoff) (N M : ℕ) (t : ℝ) :
    (∑ z ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        if z = 0 then 0 else
          gmTraceFourier cutoff t ((N : ℝ) * (z : ℝ))) =
      ∑ m ∈ Finset.Icc 1 M,
        (gmTraceFourier cutoff t ((N : ℝ) * m) +
          gmTraceFourier cutoff t (-((N : ℝ) * m))) := by
  induction M with
  | zero => simp
  | succ M ih =>
      let f : ℤ → ℂ := fun z =>
        if z = 0 then 0 else
          gmTraceFourier cutoff t ((N : ℝ) * (z : ℝ))
      have hInt : Finset.Icc (-(M.succ : ℤ)) (M.succ : ℤ) =
          insert (-(M.succ : ℤ))
            (insert (M.succ : ℤ) (Finset.Icc (-(M : ℤ)) (M : ℤ))) := by
        ext z
        simp only [Finset.mem_Icc, Finset.mem_insert, Int.natCast_succ]
        omega
      have hNat : Finset.Icc 1 M.succ =
          insert M.succ (Finset.Icc 1 M) := by
        ext n
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      change (∑ z ∈ Finset.Icc (-(M.succ : ℤ)) (M.succ : ℤ), f z) = _
      rw [hInt, hNat]
      have hNegNotInner : -(M.succ : ℤ) ∉
          insert (M.succ : ℤ) (Finset.Icc (-(M : ℤ)) (M : ℤ)) := by
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      have hPosNot : (M.succ : ℤ) ∉
          Finset.Icc (-(M : ℤ)) (M : ℤ) := by
        simp only [Finset.mem_Icc]
        omega
      have hNatNot : M.succ ∉ Finset.Icc 1 M := by
        simp only [Finset.mem_Icc]
        omega
      rw [Finset.sum_insert hNegNotInner, Finset.sum_insert hPosNot,
        Finset.sum_insert hNatNot]
      change f (-(M.succ : ℤ)) +
          (f (M.succ : ℤ) +
            ∑ z ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), f z) = _
      rw [show (∑ z ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), f z) =
          ∑ m ∈ Finset.Icc 1 M,
            (gmTraceFourier cutoff t ((N : ℝ) * m) +
              gmTraceFourier cutoff t (-((N : ℝ) * m))) by
        simpa only [f] using ih]
      dsimp only [f]
      have hneg : -(M.succ : ℤ) ≠ 0 := by omega
      have hpos : (M.succ : ℤ) ≠ 0 := by omega
      rw [ite_eq_right hneg, ite_eq_right hpos]
      push_cast
      ring_nf

/-- Exact decomposition of the complete nonzero integer series into the
retained signed window and its absolutely summable complement. -/
theorem gmTraceNonzeroFourierSum_eq_signed_add_far
    (cutoff : GMSmoothCutoff) (N M : ℕ) (hN : 0 < N) (t : ℝ) :
    gmTraceNonzeroFourierSum cutoff N t =
      (∑ m ∈ Finset.Icc 1 M,
        (gmTraceFourier cutoff t ((N : ℝ) * m) +
          gmTraceFourier cutoff t (-((N : ℝ) * m)))) +
        gmTraceFourierFarTail cutoff N M t := by
  let f : ℤ → ℂ := fun m =>
    gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ))
  have hf : Summable f := by
    simpa only [f] using gmTraceFourier_summable cutoff N hN t
  have hcentral : Summable (fun m : ℤ =>
      if m.natAbs ≤ M then (if m = 0 then 0 else f m) else 0) := by
    have hi := hf.indicator {m : ℤ | m.natAbs ≤ M ∧ m ≠ 0}
    convert hi using 1
    funext m
    by_cases hm : m.natAbs ≤ M <;> by_cases hm0 : m = 0 <;>
      simp [hm, hm0]
  have hfar : Summable (fun m : ℤ =>
      if M < m.natAbs then f m else 0) := by
    have hi := hf.indicator {m : ℤ | M < m.natAbs}
    convert hi using 1
    funext m
    by_cases hm : M < m.natAbs <;> simp [hm]
  have hsplit : gmTraceNonzeroFourierSum cutoff N t =
      (∑' m : ℤ,
        if m.natAbs ≤ M then (if m = 0 then 0 else f m) else 0) +
      ∑' m : ℤ, if M < m.natAbs then f m else 0 := by
    unfold gmTraceNonzeroFourierSum
    change (∑' m : ℤ, if m = 0 then 0 else f m) = _
    rw [← hcentral.tsum_add hfar]
    congr 1
    funext m
    by_cases hm : m.natAbs ≤ M
    · simp [hm, Nat.not_lt_of_ge hm]
    · have hm' : M < m.natAbs := Nat.lt_of_not_ge hm
      have hm0 : m ≠ 0 := by
        intro hzero
        subst m
        simp at hm'
      simp [hm, hm', hm0]
  rw [hsplit]
  congr 1
  · rw [tsum_eq_sum (s := Finset.Icc (-(M : ℤ)) (M : ℤ))]
    · calc
        (∑ z ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
            if z.natAbs ≤ M then (if z = 0 then 0 else f z) else 0) =
            ∑ z ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
              if z = 0 then 0 else f z := by
                apply Finset.sum_congr rfl
                intro z hz
                rw [ite_eq_left]
                have hzData := Finset.mem_Icc.mp hz
                omega
        _ = _ := by
          simpa only [f] using gmTraceFourierCentral_eq_signed cutoff N M t
    · intro z hz
      rw [ite_eq_right]
      intro hzAbs
      have hzOut : z < -(M : ℤ) ∨ (M : ℤ) < z := by
        simpa only [Finset.mem_Icc, not_and_or, not_le] using hz
      omega

/-- Arbitrary-order summation of the omitted integer frequencies.  The
summable `|m|^-2` factor is retained before taking the `tsum`. -/
theorem gmTraceFourierFarTail_bound_order
    (cutoff : GMSmoothCutoff) (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N M : ℕ), 0 < N → 0 < M → ∀ t : ℝ,
      ‖gmTraceFourierFarTail cutoff N M t‖ ≤
        K * (1 + |t|) ^ (n + 2) /
          ((N : ℝ) ^ (n + 2) * (M : ℝ) ^ n) := by
  obtain ⟨C₀, hC₀, hDecay⟩ := gmTraceFourier_uniform_decay cutoff (n + 2)
  let C : ℝ := C₀ + 1
  have hC : 0 < C := by dsimp only [C]; linarith
  have hPSeries : Summable (fun m : ℤ => ‖1 / (m : ℂ) ^ 2‖) := by
    have hNorm : (fun m : ℤ => ‖1 / (m : ℂ) ^ 2‖) =
        fun m : ℤ => |1 / (m : ℝ) ^ 2| := by
      funext m
      simp only [norm_div, norm_one, norm_pow, Complex.norm_intCast,
        abs_div, abs_one, pow_abs]
    rw [hNorm, summable_abs_iff]
    exact Real.summable_one_div_int_pow.mpr (by norm_num)
  let B : ℝ := ∑' m : ℤ, ‖1 / (m : ℂ) ^ 2‖
  have hB : 0 ≤ B := tsum_nonneg fun m => norm_nonneg _
  refine ⟨C * B + 1, by positivity, ?_⟩
  intro N M hN hM t
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  let scale : ℝ := C * (1 + |t|) ^ (n + 2) /
    ((N : ℝ) ^ (n + 2) * (M : ℝ) ^ n)
  have hPointwise : ∀ m : ℤ, M < m.natAbs →
      ‖gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ))‖ ≤
        scale * ‖1 / (m : ℂ) ^ 2‖ := by
    intro m hm
    have hmNatPos : 0 < m.natAbs := hM.trans hm
    have hmNe : m ≠ 0 := Int.natAbs_ne_zero.mp hmNatPos.ne'
    have hmReal : (m : ℝ) ≠ 0 := by exact_mod_cast hmNe
    have hmAbsPos : 0 < |(m : ℝ)| := abs_pos.mpr hmReal
    have hmAbs : (M : ℝ) ≤ |(m : ℝ)| := by
      have hcast : (M : ℝ) ≤ (m.natAbs : ℝ) := by
        exact_mod_cast (Nat.le_of_lt hm)
      simpa using hcast
    have hFreqAbs : |(N : ℝ) * (m : ℝ)| =
        (N : ℝ) * |(m : ℝ)| := by
      rw [abs_mul, abs_of_pos hNr]
    have hFreqPos : 0 < |(N : ℝ) * (m : ℝ)| := by
      rw [hFreqAbs]
      positivity
    have hFourier :
        ‖gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ))‖ ≤
          C₀ * (1 + |t|) ^ (n + 2) /
            |(N : ℝ) * (m : ℝ)| ^ (n + 2) := by
      rw [le_div_iff₀ (pow_pos hFreqPos (n + 2))]
      simpa [mul_comm] using hDecay t ((N : ℝ) * (m : ℝ))
    have hpow : (M : ℝ) ^ n * |(m : ℝ)| ^ 2 ≤
        |(m : ℝ)| ^ (n + 2) := by
      calc
        (M : ℝ) ^ n * |(m : ℝ)| ^ 2 ≤
            |(m : ℝ)| ^ n * |(m : ℝ)| ^ 2 := by gcongr
        _ = |(m : ℝ)| ^ (n + 2) := by rw [pow_add]
    rw [norm_div, norm_one, norm_pow, Complex.norm_intCast]
    calc
      ‖gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ))‖ ≤
          C₀ * (1 + |t|) ^ (n + 2) /
            |(N : ℝ) * (m : ℝ)| ^ (n + 2) := hFourier
      _ ≤ C * (1 + |t|) ^ (n + 2) /
          ((N : ℝ) ^ (n + 2) * |(m : ℝ)| ^ (n + 2)) := by
        rw [hFreqAbs, mul_pow]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith)
            (by positivity)) (by positivity)
      _ ≤ C * (1 + |t|) ^ (n + 2) /
          ((N : ℝ) ^ (n + 2) *
            ((M : ℝ) ^ n * |(m : ℝ)| ^ 2)) := by
        exact div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left hpow (by positivity))
      _ = scale * (1 / |(m : ℝ)| ^ 2) := by
        dsimp only [scale]
        field_simp [hNr.ne', hMr.ne', hmAbsPos.ne']
  have hComparison : ∀ m : ℤ,
      ‖if M < m.natAbs then
          gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ)) else 0‖ ≤
        scale * ‖1 / (m : ℂ) ^ 2‖ := by
    intro m
    by_cases hm : M < m.natAbs
    · simpa only [ite_eq_left hm] using hPointwise m hm
    · have hscale : 0 ≤ scale := by dsimp only [scale]; positivity
      rw [ite_eq_right hm, norm_zero]
      exact mul_nonneg hscale (norm_nonneg _)
  have hScaled : Summable (fun m : ℤ => scale * ‖1 / (m : ℂ) ^ 2‖) :=
    hPSeries.mul_left scale
  have hBound := tsum_of_norm_bounded hScaled.hasSum hComparison
  rw [tsum_mul_left] at hBound
  change ‖gmTraceFourierFarTail cutoff N M t‖ ≤ scale * B at hBound
  have hDen : 0 < (N : ℝ) ^ (n + 2) * (M : ℝ) ^ n := by positivity
  calc
    ‖gmTraceFourierFarTail cutoff N M t‖ ≤ scale * B := hBound
    _ ≤ (C * B + 1) * (1 + |t|) ^ (n + 2) /
          ((N : ℝ) ^ (n + 2) * (M : ℝ) ^ n) := by
      dsimp only [scale]
      rw [div_mul_eq_mul_div]
      apply (div_le_div_iff_of_pos_right hDen).2
      have hpowNonneg : 0 ≤ (1 + |t|) ^ (n + 2) := by positivity
      nlinarith

/-! ## The cancellation-preserving Mellin core and tail -/

theorem continuous_gmReflectionDirichletPoly
    (t : ℝ) (M : ℕ) : Continuous (gmReflectionDirichletPoly t M) := by
  unfold gmReflectionDirichletPoly
  apply continuous_finsetSum
  intro m hm
  apply Continuous.const_cpow
  · fun_prop
  · left
    exact_mod_cast (show m ≠ 0 by
      exact (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hm).1).ne')

theorem integral_norm_gmReflectionDirichletPoly_comp_neg
    (t : ℝ) (M : ℕ) (H : ℝ) :
    (∫ u in -H..H, ‖gmReflectionDirichletPoly t M (-u)‖) =
      ∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖ := by
  simpa using (intervalIntegral.integral_comp_neg
    (f := fun u : ℝ => ‖gmReflectionDirichletPoly t M u‖)
    (a := -H) (b := H))

/-- The positive-frequency core of Lemma 6.2, with the coefficient-one
polynomial retained inside the integral. -/
theorem gmPositiveMellinCore_bound (cutoff : GMSmoothCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ {t T₀ H : ℝ} {N M : ℕ},
      4 ≤ T₀ → T₀ ≤ t → 0 < H → H ≤ T₀ / 2 →
      0 < N → 0 < M →
      ∫ r : ℝ in Set.Icc (-H) H,
          (1 / (2 * Real.pi) : ℝ) * ‖gmCutoffMellin cutoff r‖ *
            ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
              ‖gmPositiveDualDirichletPoly t N M r‖ ≤
        C / Real.sqrt T₀ *
          ∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖ := by
  obtain ⟨C₀, hC₀, hMellin⟩ := gmCutoffMellin_polynomial_decay cutoff 0
  let C : ℝ := 20 * (C₀ + 1) / (2 * Real.pi)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro t T₀ H N M hT₀ ht hH hHT hN hM
  have hT₀Pos : 0 < T₀ := by linarith
  have hA : (0 : ℝ) < N := by exact_mod_cast hN
  have hAB : (N : ℝ) ≤ 2 * N * M := by
    have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hSqrtPos : 0 < Real.sqrt T₀ := Real.sqrt_pos.2 hT₀Pos
  have hHalfPos : 0 < Real.sqrt (T₀ / 2) := Real.sqrt_pos.2 (by positivity)
  have hSqrtCompare : Real.sqrt T₀ / 2 ≤ Real.sqrt (T₀ / 2) := by
    have hsq0 := Real.sq_sqrt hT₀Pos.le
    have hsq1 := Real.sq_sqrt (show 0 ≤ T₀ / 2 by positivity)
    nlinarith [Real.sqrt_nonneg T₀, Real.sqrt_nonneg (T₀ / 2)]
  have hStationary : 10 / Real.sqrt (T₀ / 2) ≤
      20 / Real.sqrt T₀ := by
    rw [div_le_div_iff₀ hHalfPos hSqrtPos]
    nlinarith
  have hDom : IntegrableOn (fun r : ℝ =>
      C / Real.sqrt T₀ * ‖gmReflectionDirichletPoly t M (-r)‖)
      (Set.Icc (-H) H) := by
    have hPoly := ((continuous_gmReflectionDirichletPoly t M).comp
      continuous_neg).norm
    exact (hPoly.continuousOn.integrableOn_compact isCompact_Icc).const_mul _
  have hTarget : IntegrableOn (fun r : ℝ =>
      (1 / (2 * Real.pi) : ℝ) * ‖gmCutoffMellin cutoff r‖ *
        ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
          ‖gmPositiveDualDirichletPoly t N M r‖) (Set.Icc (-H) H) :=
    (integrable_norm_gmPositiveDualAggregate cutoff t (M := M) hN).integrableOn
  calc
    ∫ r : ℝ in Set.Icc (-H) H,
        (1 / (2 * Real.pi) : ℝ) * ‖gmCutoffMellin cutoff r‖ *
          ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
            ‖gmPositiveDualDirichletPoly t N M r‖ ≤
      ∫ r : ℝ in Set.Icc (-H) H,
        C / Real.sqrt T₀ * ‖gmReflectionDirichletPoly t M (-r)‖ := by
      apply integral_mono_ae hTarget hDom
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      have hrAbs : |r| ≤ H := (abs_le).2 ⟨hr.1, hr.2⟩
      have hrCore : |r| ≤ T₀ / 2 := hrAbs.trans hHT
      have hMellinAt : ‖gmCutoffMellin cutoff r‖ ≤ C₀ := by
        simpa using hMellin r
      have hReflect := norm_gmReflectionIntegral_pos_core_le
        hT₀ ht hrCore hA hAB
      rw [norm_gmPositiveDualDirichletPoly_eq t r hN]
      dsimp only [C]
      have hPolyNonneg : 0 ≤ ‖gmReflectionDirichletPoly t M (-r)‖ :=
        norm_nonneg _
      have hPi : 0 < 2 * Real.pi := by positivity
      calc
        (1 / (2 * Real.pi)) * ‖gmCutoffMellin cutoff r‖ *
              ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
                ‖gmReflectionDirichletPoly t M (-r)‖ ≤
            (1 / (2 * Real.pi)) * C₀ *
              (10 / Real.sqrt (T₀ / 2)) *
                ‖gmReflectionDirichletPoly t M (-r)‖ := by gcongr
        _ ≤ (20 * (C₀ + 1) / (2 * Real.pi)) /
              Real.sqrt T₀ *
                ‖gmReflectionDirichletPoly t M (-r)‖ := by
          have hCcmp : C₀ ≤ C₀ + 1 := by linarith
          calc
            _ ≤ (1 / (2 * Real.pi)) * (C₀ + 1) *
                (20 / Real.sqrt T₀) *
                  ‖gmReflectionDirichletPoly t M (-r)‖ := by gcongr
            _ = _ := by ring
    _ = C / Real.sqrt T₀ *
        ∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖ := by
      have hset : (∫ r : ℝ in Set.Icc (-H) H,
          ‖gmReflectionDirichletPoly t M (-r)‖) =
          ∫ r in -H..H, ‖gmReflectionDirichletPoly t M (-r)‖ := by
        rw [integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by linarith : -H ≤ H)]
      rw [MeasureTheory.integral_const_mul]
      rw [hset, integral_norm_gmReflectionDirichletPoly_comp_neg]

/-- Uniform Mellin-tail estimate.  The polynomial is bounded by `M` only
on this omitted range; no mode-cardinality loss enters the core. -/
theorem gmPositiveMellinTail_bound_order
    (cutoff : GMSmoothCutoff) (q : ℕ) (hq : 2 ≤ q) :
    ∃ K : ℝ, 0 < K ∧ ∀ (t H : ℝ) (N M : ℕ),
      1 ≤ H → 0 < N → 0 < M →
      ∫ r : ℝ in (Set.Icc (-H) H)ᶜ,
          (1 / (2 * Real.pi) : ℝ) * ‖gmCutoffMellin cutoff r‖ *
            ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
              ‖gmPositiveDualDirichletPoly t N M r‖ ≤
        K * (M : ℝ) ^ 2 * H ^ (1 - (q : ℝ)) := by
  obtain ⟨C₀, hC₀, hDecay⟩ := gmCutoffMellin_polynomial_decay cutoff q
  let K : ℝ := max 1 (C₀ / Real.pi * (2 / ((q : ℝ) - 1)))
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨K, hK, ?_⟩
  intro t H N M hH hN hM
  have hHPos : 0 < H := zero_lt_one.trans_le hH
  have hA : (0 : ℝ) < N := by exact_mod_cast hN
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hAB : (N : ℝ) ≤ 2 * N * M := by nlinarith
  have hqReal : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have ha : -(q : ℝ) < -1 := by linarith
  have hDom : IntegrableOn (fun r : ℝ =>
      (C₀ / Real.pi * (M : ℝ) ^ 2) * |r| ^ (-(q : ℝ)))
      (Set.Icc (-H) H)ᶜ :=
    (integrableOn_abs_rpow_compl_Icc ha hHPos).const_mul _
  have hTarget : IntegrableOn (fun r : ℝ =>
      (1 / (2 * Real.pi) : ℝ) * ‖gmCutoffMellin cutoff r‖ *
        ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
          ‖gmPositiveDualDirichletPoly t N M r‖) (Set.Icc (-H) H)ᶜ :=
    (integrable_norm_gmPositiveDualAggregate cutoff t (M := M) hN).integrableOn
  have hPoint : ∀ r ∈ (Set.Icc (-H) H)ᶜ,
      (1 / (2 * Real.pi) : ℝ) * ‖gmCutoffMellin cutoff r‖ *
          ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
            ‖gmPositiveDualDirichletPoly t N M r‖ ≤
        (C₀ / Real.pi * (M : ℝ) ^ 2) * |r| ^ (-(q : ℝ)) := by
    intro r hr
    have hrAbs : H < |r| := by
      by_contra hnot
      exact hr ((abs_le).mp (le_of_not_gt hnot))
    have hrPos : 0 < |r| := hHPos.trans hrAbs
    have hMellin : ‖gmCutoffMellin cutoff r‖ ≤
        C₀ / |r| ^ q := by
      rw [le_div_iff₀ (pow_pos hrPos q)]
      simpa [mul_comm] using hDecay r
    have hReflect := norm_gmReflectionIntegral_le_log
      (tau := t - r) hA hAB
    have hRatio : (2 * (N : ℝ) * M) / N = 2 * (M : ℝ) := by
      field_simp [hA.ne']
    rw [hRatio] at hReflect
    have hLog : Real.log (2 * (M : ℝ)) ≤ 2 * (M : ℝ) :=
      Real.log_le_self (by positivity)
    have hPoly := norm_gmPositiveDualDirichletPoly_le t (M := M) hN r
    have hRpow : 1 / |r| ^ q = |r| ^ (-(q : ℝ)) := by
      rw [Real.rpow_neg hrPos.le]
      simp
    have hMellin' : ‖gmCutoffMellin cutoff r‖ ≤
        C₀ * |r| ^ (-(q : ℝ)) := by
      calc
        ‖gmCutoffMellin cutoff r‖ ≤ C₀ / |r| ^ q := hMellin
        _ = C₀ * (1 / |r| ^ q) := by ring
        _ = C₀ * |r| ^ (-(q : ℝ)) := by rw [hRpow]
    calc
      (1 / (2 * Real.pi)) * ‖gmCutoffMellin cutoff r‖ *
            ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
              ‖gmPositiveDualDirichletPoly t N M r‖ ≤
          (1 / (2 * Real.pi)) *
            (C₀ * |r| ^ (-(q : ℝ))) * (2 * (M : ℝ)) * M := by
        gcongr
        exact hReflect.trans hLog
      _ = (C₀ / Real.pi * (M : ℝ) ^ 2) *
          |r| ^ (-(q : ℝ)) := by ring
  calc
    ∫ r : ℝ in (Set.Icc (-H) H)ᶜ,
        (1 / (2 * Real.pi) : ℝ) * ‖gmCutoffMellin cutoff r‖ *
          ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
            ‖gmPositiveDualDirichletPoly t N M r‖ ≤
      ∫ r : ℝ in (Set.Icc (-H) H)ᶜ,
        (C₀ / Real.pi * (M : ℝ) ^ 2) *
          |r| ^ (-(q : ℝ)) := by
      apply integral_mono_ae hTarget hDom
      filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with r hr
      exact hPoint r hr
    _ = (C₀ / Real.pi * (M : ℝ) ^ 2) *
        (-2 * H ^ (1 - (q : ℝ)) / (1 - (q : ℝ))) := by
      rw [integral_const_mul, integral_abs_rpow_compl_Icc ha hHPos]
      ring_nf
    _ ≤ K * (M : ℝ) ^ 2 * H ^ (1 - (q : ℝ)) := by
      have hpow : 0 ≤ H ^ (1 - (q : ℝ)) := Real.rpow_nonneg hHPos.le _
      have hcoef : C₀ / Real.pi * (2 / ((q : ℝ) - 1)) ≤ K :=
        le_max_right _ _
      have hden : 1 - (q : ℝ) ≠ 0 := by linarith
      have hden' : (q : ℝ) - 1 ≠ 0 := by linarith
      have heq :
          (C₀ / Real.pi * (M : ℝ) ^ 2) *
              (-2 * H ^ (1 - (q : ℝ)) / (1 - (q : ℝ))) =
            (C₀ / Real.pi * (2 / ((q : ℝ) - 1))) *
              (M : ℝ) ^ 2 * H ^ (1 - (q : ℝ)) := by
        field_simp [hden, hden']
        ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef (sq_nonneg (M : ℝ))) hpow

/-- The negative-frequency core, expressed with the same coefficient-one
polynomial as the positive half. -/
theorem gmNegativeMellinCore_bound (cutoff : GMSmoothCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ {t T₀ H : ℝ} {N M : ℕ},
      4 ≤ T₀ → T₀ ≤ t → 0 < H → H ≤ T₀ / 2 →
      0 < N → 0 < M →
      ∫ r : ℝ in Set.Icc (-H) H,
          (1 / (2 * Real.pi) : ℝ) * ‖gmCutoffMellin cutoff r‖ *
            ‖gmReflectionIntegral (-t - r) N (2 * N * M)‖ *
              ‖gmPositiveDualDirichletPoly (-t) N M r‖ ≤
        C / Real.sqrt T₀ *
          ∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖ := by
  obtain ⟨C₀, hC₀, hMellin⟩ := gmCutoffMellin_polynomial_decay cutoff 0
  let C : ℝ := 20 * (C₀ + 1) / (2 * Real.pi)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro t T₀ H N M hT₀ ht hH hHT hN hM
  have hT₀Pos : 0 < T₀ := by linarith
  have hA : (0 : ℝ) < N := by exact_mod_cast hN
  have hAB : (N : ℝ) ≤ 2 * N * M := by
    have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hSqrtPos : 0 < Real.sqrt T₀ := Real.sqrt_pos.2 hT₀Pos
  have hHalfPos : 0 < Real.sqrt (T₀ / 2) := Real.sqrt_pos.2 (by positivity)
  have hSqrtCompare : Real.sqrt T₀ / 2 ≤ Real.sqrt (T₀ / 2) := by
    have hsq0 := Real.sq_sqrt hT₀Pos.le
    have hsq1 := Real.sq_sqrt (show 0 ≤ T₀ / 2 by positivity)
    nlinarith [Real.sqrt_nonneg T₀, Real.sqrt_nonneg (T₀ / 2)]
  have hStationary : 10 / Real.sqrt (T₀ / 2) ≤
      20 / Real.sqrt T₀ := by
    rw [div_le_div_iff₀ hHalfPos hSqrtPos]
    nlinarith
  have hDom : IntegrableOn (fun r : ℝ =>
      C / Real.sqrt T₀ * ‖gmReflectionDirichletPoly t M r‖)
      (Set.Icc (-H) H) := by
    have hPoly := (continuous_gmReflectionDirichletPoly t M).norm
    exact (hPoly.continuousOn.integrableOn_compact isCompact_Icc).const_mul _
  have hTarget : IntegrableOn (fun r : ℝ =>
      (1 / (2 * Real.pi) : ℝ) * ‖gmCutoffMellin cutoff r‖ *
        ‖gmReflectionIntegral (-t - r) N (2 * N * M)‖ *
          ‖gmPositiveDualDirichletPoly (-t) N M r‖) (Set.Icc (-H) H) :=
    (integrable_norm_gmPositiveDualAggregate cutoff (-t) (M := M) hN).integrableOn
  calc
    ∫ r : ℝ in Set.Icc (-H) H,
        (1 / (2 * Real.pi) : ℝ) * ‖gmCutoffMellin cutoff r‖ *
          ‖gmReflectionIntegral (-t - r) N (2 * N * M)‖ *
            ‖gmPositiveDualDirichletPoly (-t) N M r‖ ≤
      ∫ r : ℝ in Set.Icc (-H) H,
        C / Real.sqrt T₀ * ‖gmReflectionDirichletPoly t M r‖ := by
      apply integral_mono_ae hTarget hDom
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      have hrAbs : |r| ≤ H := (abs_le).2 ⟨hr.1, hr.2⟩
      have hrCore : |r| ≤ T₀ / 2 := hrAbs.trans hHT
      have hMellinAt : ‖gmCutoffMellin cutoff r‖ ≤ C₀ := by
        simpa using hMellin r
      have hReflect := norm_gmReflectionIntegral_neg_core_le
        hT₀ ht hrCore hA hAB
      rw [norm_gmPositiveDualDirichletPoly_eq (-t) r hN,
        norm_gmReflectionDirichletPoly_neg_time]
      simp only [neg_neg]
      dsimp only [C]
      calc
        (1 / (2 * Real.pi)) * ‖gmCutoffMellin cutoff r‖ *
              ‖gmReflectionIntegral (-t - r) N (2 * N * M)‖ *
                ‖gmReflectionDirichletPoly t M r‖ ≤
            (1 / (2 * Real.pi)) * C₀ *
              (10 / Real.sqrt (T₀ / 2)) *
                ‖gmReflectionDirichletPoly t M r‖ := by gcongr
        _ ≤ (20 * (C₀ + 1) / (2 * Real.pi)) /
              Real.sqrt T₀ * ‖gmReflectionDirichletPoly t M r‖ := by
          calc
            _ ≤ (1 / (2 * Real.pi)) * (C₀ + 1) *
                (20 / Real.sqrt T₀) *
                  ‖gmReflectionDirichletPoly t M r‖ := by
                    gcongr
                    linarith
            _ = _ := by ring
    _ = C / Real.sqrt T₀ *
        ∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖ := by
      have hset : (∫ r : ℝ in Set.Icc (-H) H,
          ‖gmReflectionDirichletPoly t M r‖) =
          ∫ r in -H..H, ‖gmReflectionDirichletPoly t M r‖ := by
        rw [integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by linarith : -H ≤ H)]
      rw [MeasureTheory.integral_const_mul, hset]

/-- Finite retained signed window with both Mellin tails removed at an
arbitrary order. -/
theorem gmRetainedSignedReflection_bound_order
    (cutoff : GMSmoothCutoff) (q : ℕ) (hq : 2 ≤ q) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ {t T₀ H : ℝ} {N M : ℕ},
        4 ≤ T₀ → T₀ ≤ t → 1 ≤ H → H ≤ T₀ / 2 →
        0 < N → 0 < M →
        ‖∑ m ∈ Finset.Icc 1 M,
            (gmTraceFourier cutoff t ((N : ℝ) * m) +
              gmTraceFourier cutoff t (-((N : ℝ) * m)))‖ ≤
          C / Real.sqrt T₀ *
              (∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖) +
            K * (M : ℝ) ^ 2 * H ^ (1 - (q : ℝ)) := by
  obtain ⟨C₁, hC₁, hPos⟩ := gmPositiveMellinCore_bound cutoff
  obtain ⟨C₂, hC₂, hNeg⟩ := gmNegativeMellinCore_bound cutoff
  obtain ⟨K₀, hK₀, hTail⟩ := gmPositiveMellinTail_bound_order cutoff q hq
  refine ⟨C₁ + C₂, 2 * K₀, by positivity, by positivity, ?_⟩
  intro t T₀ H N M hT₀ ht hH hHT hN hM
  let fpos : ℝ → ℝ := fun r =>
    (1 / (2 * Real.pi) : ℝ) * ‖gmCutoffMellin cutoff r‖ *
      ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
        ‖gmPositiveDualDirichletPoly t N M r‖
  let fneg : ℝ → ℝ := fun r =>
    (1 / (2 * Real.pi) : ℝ) * ‖gmCutoffMellin cutoff r‖ *
      ‖gmReflectionIntegral (-t - r) N (2 * N * M)‖ *
        ‖gmPositiveDualDirichletPoly (-t) N M r‖
  have hPosInt : Integrable fpos := by
    simpa only [fpos] using
      integrable_norm_gmPositiveDualAggregate cutoff t (M := M) hN
  have hNegInt : Integrable fneg := by
    simpa only [fneg] using
      integrable_norm_gmPositiveDualAggregate cutoff (-t) (M := M) hN
  have hSourceNonneg : 0 ≤
      ∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖ := by
    exact intervalIntegral.integral_nonneg (by linarith) fun u _ => norm_nonneg _
  have hCorePos := hPos hT₀ ht (zero_lt_one.trans_le hH) hHT hN hM
  have hCoreNeg := hNeg hT₀ ht (zero_lt_one.trans_le hH) hHT hN hM
  have hTailPos := hTail t H N M hH hN hM
  have hTailNeg := hTail (-t) H N M hH hN hM
  calc
    ‖∑ m ∈ Finset.Icc 1 M,
        (gmTraceFourier cutoff t ((N : ℝ) * m) +
          gmTraceFourier cutoff t (-((N : ℝ) * m)))‖ ≤
        (∫ r : ℝ, fpos r) + ∫ r : ℝ, fneg r := by
      simpa only [fpos, fneg] using
        norm_gmTraceFourier_signed_sum_le_dualPoly cutoff t hN
    _ = ((∫ r : ℝ in Set.Icc (-H) H, fpos r) +
          ∫ r : ℝ in (Set.Icc (-H) H)ᶜ, fpos r) +
        ((∫ r : ℝ in Set.Icc (-H) H, fneg r) +
          ∫ r : ℝ in (Set.Icc (-H) H)ᶜ, fneg r) := by
      rw [integral_add_compl measurableSet_Icc hPosInt,
        integral_add_compl measurableSet_Icc hNegInt]
    _ ≤ (C₁ + C₂) / Real.sqrt T₀ *
          (∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖) +
        (2 * K₀) * (M : ℝ) ^ 2 * H ^ (1 - (q : ℝ)) := by
      have hPieces := add_le_add
        (add_le_add hCorePos hTailPos) (add_le_add hCoreNeg hTailNeg)
      simpa only [fpos, fneg] using hPieces.trans_eq (by ring)

/-! ## Ordinate symmetry -/

/-- The complete nonzero-frequency series at the opposite ordinate is its
complex conjugate.  The proof reindexes the entire integer `tsum`; no finite
window or cardinality estimate is involved. -/
theorem gmTraceNonzeroFourierSum_neg_eq_conj
    (cutoff : GMSmoothCutoff) (N : ℕ) (t : ℝ) :
    gmTraceNonzeroFourierSum cutoff N (-t) =
      star (gmTraceNonzeroFourierSum cutoff N t) := by
  unfold gmTraceNonzeroFourierSum
  rw [← (Equiv.neg ℤ).tsum_eq]
  change _ = conj (∑' m : ℤ,
    if m = 0 then 0 else gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ)))
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro m
  by_cases hm : m = 0
  · subst m
    simp
  · have hneg : -m ≠ 0 := neg_ne_zero.mpr hm
    change (if -m = 0 then 0 else
        gmTraceFourier cutoff (-t) ((N : ℝ) * ((-m : ℤ) : ℝ))) =
      star (if m = 0 then 0 else
        gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ)))
    rw [ite_eq_right hneg, ite_eq_right hm]
    have hfreq : (N : ℝ) * ((-m : ℤ) : ℝ) =
        -((N : ℝ) * (m : ℝ)) := by push_cast; ring
    rw [hfreq, gmTraceFourier_neg_eq_conj]
    simp

theorem norm_gmTraceNonzeroFourierSum_neg
    (cutoff : GMSmoothCutoff) (N : ℕ) (t : ℝ) :
    ‖gmTraceNonzeroFourierSum cutoff N (-t)‖ =
      ‖gmTraceNonzeroFourierSum cutoff N t‖ := by
  rw [gmTraceNonzeroFourierSum_neg_eq_conj]
  exact norm_star _

theorem integral_norm_gmReflectionDirichletPoly_neg_time
    (t H : ℝ) (M : ℕ) :
    (∫ u in -H..H, ‖gmReflectionDirichletPoly (-t) M u‖) =
      ∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖ := by
  simp_rw [norm_gmReflectionDirichletPoly_neg_time]
  exact integral_norm_gmReflectionDirichletPoly_comp_neg t M H

/-! ## Complete-frequency core-plus-tail theorem -/

/-- The complete nonzero integer series, before choosing the source scales.
This is the analytic heart of Lemma 6.2: the first error is the Mellin tail
and the second is the absolutely summed omitted-frequency tail. -/
theorem gmCompleteSmoothReflection_bound_order
    (cutoff : GMSmoothCutoff) (q : ℕ) (hq : 2 ≤ q) :
    ∃ C K L : ℝ, 0 < C ∧ 0 < K ∧ 0 < L ∧
      ∀ {t T₀ H : ℝ} {N M : ℕ},
        4 ≤ T₀ → T₀ ≤ |t| → 1 ≤ H → H ≤ T₀ / 2 →
        0 < N → 0 < M →
        ‖gmTraceNonzeroFourierSum cutoff N t‖ ≤
          C / Real.sqrt T₀ *
              (∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖) +
            K * (M : ℝ) ^ 2 * H ^ (1 - (q : ℝ)) +
            L * (1 + |t|) ^ (q + 2) /
              ((N : ℝ) ^ (q + 2) * (M : ℝ) ^ q) := by
  obtain ⟨C, K, hC, hK, hRetained⟩ :=
    gmRetainedSignedReflection_bound_order cutoff q hq
  obtain ⟨L, hL, hFar⟩ := gmTraceFourierFarTail_bound_order cutoff q
  refine ⟨C, K, L, hC, hK, hL, ?_⟩
  intro t T₀ H N M hT₀ ht hH hHT hN hM
  have hAbsNonneg : 0 ≤ |t| := abs_nonneg t
  have hFarAt := hFar N M hN hM t
  by_cases htnonneg : 0 ≤ t
  · have hRet := hRetained (t := t) hT₀
      (by simpa only [abs_of_nonneg htnonneg] using ht) hH hHT hN hM
    rw [gmTraceNonzeroFourierSum_eq_signed_add_far cutoff N M hN t]
    calc
      ‖(∑ m ∈ Finset.Icc 1 M,
            (gmTraceFourier cutoff t ((N : ℝ) * m) +
              gmTraceFourier cutoff t (-((N : ℝ) * m)))) +
          gmTraceFourierFarTail cutoff N M t‖ ≤
          ‖∑ m ∈ Finset.Icc 1 M,
            (gmTraceFourier cutoff t ((N : ℝ) * m) +
              gmTraceFourier cutoff t (-((N : ℝ) * m)))‖ +
            ‖gmTraceFourierFarTail cutoff N M t‖ := norm_add_le _ _
      _ ≤ (C / Real.sqrt T₀ *
              (∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖) +
            K * (M : ℝ) ^ 2 * H ^ (1 - (q : ℝ))) +
          L * (1 + |t|) ^ (q + 2) /
            ((N : ℝ) ^ (q + 2) * (M : ℝ) ^ q) :=
        add_le_add hRet hFarAt
      _ = _ := by ring
  · have htneg : t < 0 := lt_of_not_ge htnonneg
    let s : ℝ := -t
    have hs : s = |t| := by dsimp only [s]; rw [abs_of_neg htneg]
    have hsNonneg : 0 ≤ s := by rw [hs]; exact hAbsNonneg
    have hRet := hRetained (t := s) hT₀ (by simpa only [hs] using ht)
      hH hHT hN hM
    have hFarNeg := hFar N M hN hM s
    have hNorm : ‖gmTraceNonzeroFourierSum cutoff N t‖ =
        ‖gmTraceNonzeroFourierSum cutoff N s‖ := by
      have htEq : t = -s := by dsimp only [s]; ring
      rw [htEq, norm_gmTraceNonzeroFourierSum_neg]
    rw [hNorm, gmTraceNonzeroFourierSum_eq_signed_add_far cutoff N M hN s]
    calc
      ‖(∑ m ∈ Finset.Icc 1 M,
            (gmTraceFourier cutoff s ((N : ℝ) * m) +
              gmTraceFourier cutoff s (-((N : ℝ) * m)))) +
          gmTraceFourierFarTail cutoff N M s‖ ≤
          ‖∑ m ∈ Finset.Icc 1 M,
            (gmTraceFourier cutoff s ((N : ℝ) * m) +
              gmTraceFourier cutoff s (-((N : ℝ) * m)))‖ +
            ‖gmTraceFourierFarTail cutoff N M s‖ := norm_add_le _ _
      _ ≤ (C / Real.sqrt T₀ *
              (∫ u in -H..H, ‖gmReflectionDirichletPoly s M u‖) +
            K * (M : ℝ) ^ 2 * H ^ (1 - (q : ℝ))) +
          L * (1 + |s|) ^ (q + 2) /
            ((N : ℝ) ^ (q + 2) * (M : ℝ) ^ q) :=
        add_le_add hRet hFarNeg
      _ = C / Real.sqrt T₀ *
              (∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖) +
            K * (M : ℝ) ^ 2 * H ^ (1 - (q : ℝ)) +
          L * (1 + |t|) ^ (q + 2) /
            ((N : ℝ) ^ (q + 2) * (M : ℝ) ^ q) := by
        have hst : s = -t := rfl
        rw [hst, integral_norm_gmReflectionDirichletPoly_neg_time]
        simp only [abs_neg]

/-! ## Source scale selection -/

/-- The epsilon reserve used for both the Mellin and frequency tails.  Capping
it at `1/16` keeps the smoothing window below the physical height even when
the caller supplies a large epsilon. -/
noncomputable def gmReflectionEta (ε : ℝ) : ℝ :=
  min (ε / 16) (1 / 16)

/-- The `gmReflectionHeight` definition used by the source-facing construction in `QuantitativeSmoothReflection`. -/
noncomputable def gmReflectionHeight (T ε : ℝ) : ℝ :=
  T ^ gmReflectionEta ε

theorem gmReflectionEta_pos {ε : ℝ} (hε : 0 < ε) :
    0 < gmReflectionEta ε := by
  unfold gmReflectionEta
  exact lt_min (by positivity) (by norm_num)

theorem gmReflectionEta_le_one {ε : ℝ} :
    gmReflectionEta ε ≤ 1 := by
  unfold gmReflectionEta
  exact (min_le_right _ _).trans (by norm_num)

theorem gmReflectionEta_lt_eps {ε : ℝ} (hε : 0 < ε) :
    gmReflectionEta ε < ε := by
  have hle : gmReflectionEta ε ≤ ε / 16 := by
    unfold gmReflectionEta
    exact min_le_left _ _
  nlinarith

/-- The `gmReflectionDecayOrder` definition used by the source-facing construction in `QuantitativeSmoothReflection`. -/
noncomputable def gmReflectionDecayOrder (A ε : ℝ) : ℕ :=
  Nat.ceil ((A + 6) / gmReflectionEta ε) + 2

theorem gmReflectionDecayOrder_two_le (A ε : ℝ) :
    2 ≤ gmReflectionDecayOrder A ε := by
  unfold gmReflectionDecayOrder
  omega

theorem gmReflectionDecayOrder_budget {A ε : ℝ}
    (hA : 0 < A) (hε : 0 < ε) :
    A + 5 ≤ gmReflectionEta ε *
      ((gmReflectionDecayOrder A ε : ℝ) - 1) := by
  have hη := gmReflectionEta_pos hε
  have hRatioNonneg : 0 ≤ (A + 6) / gmReflectionEta ε := by positivity
  have hceil : (A + 6) / gmReflectionEta ε ≤
      (Nat.ceil ((A + 6) / gmReflectionEta ε) : ℝ) := Nat.le_ceil _
  have hscaled : A + 6 ≤ gmReflectionEta ε *
      (Nat.ceil ((A + 6) / gmReflectionEta ε) : ℝ) := by
    rw [div_le_iff₀ hη] at hceil
    simpa only [mul_comm] using hceil
  unfold gmReflectionDecayOrder
  push_cast
  nlinarith

/-! ## Public Guth--Maynard Lemma 6.2 theorem -/

/-- The scaled cubic-trace tail is exactly `N` times the unscaled complete
nonzero-frequency series. -/
theorem gmTraceNonzeroTailAt_eq_scale_mul
    (cutoff : GMSmoothCutoff) (N : ℕ) (t : ℝ) :
    gmTraceNonzeroTailAt cutoff N t =
      (N : ℂ) * gmTraceNonzeroFourierSum cutoff N t := by
  unfold gmTraceNonzeroTailAt gmTraceNonzeroFourierSum gmScaledTraceMode
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  by_cases hm : m = 0 <;> simp [hm]

theorem norm_gmTraceNonzeroTailAt_eq
    (cutoff : GMSmoothCutoff) (N : ℕ) (t : ℝ) :
    ‖gmTraceNonzeroTailAt cutoff N t‖ =
      (N : ℝ) * ‖gmTraceNonzeroFourierSum cutoff N t‖ := by
  rw [gmTraceNonzeroTailAt_eq_scale_mul, norm_mul, Complex.norm_natCast]

end GuthMaynard.NativeMoment
