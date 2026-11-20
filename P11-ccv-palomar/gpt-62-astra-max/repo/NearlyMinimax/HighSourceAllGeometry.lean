module

public import NearlyMinimax.HighCompleteGeometry
public import NearlyMinimax.HighCompleteSourceMarkedTail
public import NearlyMinimax.HighSourceCanonicalResponse
public import NearlyMinimax.HigherBandRawCollapse
public import NearlyMinimax.HighSourceHigherCounts
public import NearlyMinimax.HighUnionFisher


@[expose] public section

/-! Uniform, actual canonical-source domination by the full-count geometry
H. No hypothesis asserts score boundedness or a stochastic covariance. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

 theorem completeSource_original_all_geometry {d : ℕ} [NeZero d]
    {C : ModelConstants d} (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr0 eta0 : ℝ, 1 ≤ Cfr0 ∧ 0 < eta0 ∧
      ∀ k D M q : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder (HighWindowLabels d k)),
      4 ≤ k → 3 ≤ D → 2 ≤ q → highCenterResolutionThreshold C ≤ (M : ℝ) →
      ∀ Cfr c0 ell N mu cf : ℝ, Cfr0 ≤ Cfr → 1 ≤ ell → ell < N → 0 ≤ cf →
      cf*(k : ℝ)^(-C.smoothness) ≤ eta0 →
      shrunkDensityExponent C.densityLower C.densityUpper M ≤ c0 →
      (∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N mu) →
      (∀ j : Fin (D-2), ell < higherBandTargetScale d (j.val+3) N mu → j.val+3 ≤ M) →
      ∀ Rbound : ℕ, (∀ r ∈ ordinaryFineAliasTargetSet d D ell N mu, 1 ≤ r ∧ r ≤ Rbound) →
      ∀ V : ℝ, |V-Q.v| ≤ Q.ρ → ∀ j : HighWindowLabels d k,
      ∀ h : HighCompleteSourceHistory C k D M q Cfr (spatialInterpolationLambda d) ell N mu,
      ∀ n : ℕ, ∀ x : DesignSample d n, (∀ i, x i ∈ highTorusPatch j) →
      let R := completeSourceRows C k D M q Cfr (spatialInterpolationLambda d) ell N mu
      let eta := cf*(k : ℝ)^(-C.smoothness)
      let Chi := highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1
      selectedRawSquareEnergy (highUnionSourceRawNumerator C R n Q.a V eta h j) x ≤
        completeSourceGeometryEnvelope D M Rbound q C.densityLower C.densityUpper c0 ell N mu Cfr Q.a Q.ρ eta
          Chi (highRowTotalMass R.rowMass) n (highPatchProductChart j x) := by
  obtain ⟨C0,e0,hC0,he0,hguards⟩ := completeSource_original_local_guards Q
  refine ⟨C0,e0,hC0,he0,?_⟩
  intro k D M q hk0 horder hk hD hq hM Cfr c0 ell N mu cf hfr hell hellN hcf heta htau hnu hFine
    Rbound hI V hV j h n x hx
  letI := hk0
  letI := horder
  let lam := spatialInterpolationLambda d
  let R := completeSourceRows C k D M q Cfr lam ell N mu
  let eta := cf*(k : ℝ)^(-C.smoothness)
  let c := (highUnionSourceState C R h).2
  let U := highPatchProductChart j x
  let p := fun i : Fin n => highUnionSourceDensity C R h (x i)
  let g := fun i : Fin n => highLocalFieldWithout eta c j (x i)
  let w := fun i : Fin n => highPeriodicTensor j (x i)
  let Chi := highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1
  have hellp  := lt_of_lt_of_le zero_lt_one hell
  have hfr1 := hC0.trans hfr
  have hq1 : 1 ≤ q := by omega
  have H := hguards k D M q hk0 horder hk hD hq1 hM Cfr lam ell N mu cf hfr hellp hellN hcf heta h
  have G := completeSourceRows_guards k hD hq1 hM lam mu hfr1 hellp hellN
  let ad := C.densityLower + 1/(M : ℝ)
  let bd := C.densityUpper - 1/(M : ℝ)
  obtain ⟨had,hab⟩ := high_source_interval_numeric hM
  have hpi (i : Fin n) : p i ∈ Icc ad bd := highUnionSourceDensity_interval C R G h (x i)
  have hU (i : Fin n) (l : Fin d) : |U i l| ≤ 2 := (highLocalCoordinates_abs_le_one j (x i) l).trans (by norm_num)
  have hmass f (hf : |f| ≤ Q.ρ) u : 0 ≤ ternaryMass Q.a f V u := Q.c_pos.le.trans ((Q.legal f V hf hV).2.2.1 u)
  have he (y : TernaryVector n) : highUnionSourceRawNumerator C R n Q.a V eta h j x y =
      completeSourceRawNumerator ad bd lam ell N mu M q Cfr Q.a V eta U p g w (c j) y :=
    completeSourceRawNumerator_eq_canonical C hD hq1 hM Cfr lam ell N mu hfr1 hellp hellN j h x hx
      Q.a V eta Q.a_pos.ne' g w (fun v hv i => hmass _ (H.regression_abs j v hv (x i))) y
  have hE : selectedRawSquareEnergy (highUnionSourceRawNumerator C R n Q.a V eta h j) x =
      ∑ y : TernaryVector n, completeSourceRawNumerator ad bd lam ell N mu M q Cfr Q.a V eta U p g w (c j) y ^ 2 :=
    Finset.sum_congr (by ext; simp) (fun y _ => congrArg (· ^ 2) (he y))
  change selectedRawSquareEnergy (highUnionSourceRawNumerator C R n Q.a V eta h j) x ≤
    _
  rcases n with _|_|_|n
  · simp [hE, completeSourceGeometryEnvelope,
      completeSourceRawNumerator_count_zero ad bd lam ell N mu had hab D M q (by omega)]
  · simp only [hE, completeSourceGeometryEnvelope,
      completeSourceRawNumerator_count_one ad bd lam ell N mu had hab D M q (by omega) hq1
        Cfr Q.a V eta (by linarith) hU p g w hpi, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, le_refl]
  · have hM2 : 2 ≤ M := by exact_mod_cast (highCenterResolution_guards hM).1
    simp only [hE, completeSourceGeometryEnvelope,
      completeSourceRawNumerator_count_two ad bd lam ell N mu had hab (by omega : 2 ≤ D)
        Cfr Q.a V eta hU p g w hpi]
    simpa only [ad,bd,one_div] using finePairCountTwoRawNumerator_sum_square_le_geometry hD had hab hellp.le hellN.le
      D M q (by omega) hM2 hq Cfr Q.a V eta Q.ρ (by linarith) Q.a_pos Q.ρ_pos.le (U := U)
      (fun i => highLocalCoordinates_abs_le_one j (x i)) hpi (fun i => H.weight_abs j (x i))
      (fun i => H.regression_abs j (c j) (H.coefficient_ball j) (x i))
  · simp [completeSourceGeometryEnvelope]
    split_ifs with hnD
    · simp [hE]
      simpa only [ad, bd, one_div] using completeSourceRawNumerator_higher_square_le_geometry
        C.densityLower_pos hell (by simpa only [one_div] using hab) htau (by omega : 3 ≤ n+3) hnD hq1
        hnu hFine hI hfr1 Q.a_pos H.amplitude_nonneg Q.ρ_pos.le H.amplitude_half hU p g w
        (by simpa only [ad,bd,one_div] using hpi) (fun i => H.without_abs j (x i)) (fun i => H.weight_abs j (x i))
        (H.coefficient_ball j) hmass
    · apply crude_raw_square_energy_pointwise Chi eta (highRowTotalMass R.rowMass)
        (highSeparatedScoreExponentialConstant_pos Q.a Q.ρ C.densityUpper 1 1).le G.total_positive.le
      exact fun z => completeSourceNumerator_all_count_exponential_bound C hD hq1 hM Cfr lam ell N mu hfr1 hellp hellN
        (by omega) j h Q.a V eta Q.ρ Q.a_pos H.amplitude_nonneg Q.ρ_pos.le H.amplitude_half z
        (fun u => H.without_abs j (z u)) (fun u => H.weight_abs j (z u))
        (fun v hv u => H.profile_abs j v hv (z u)) hmass

end NearlyMinimax
