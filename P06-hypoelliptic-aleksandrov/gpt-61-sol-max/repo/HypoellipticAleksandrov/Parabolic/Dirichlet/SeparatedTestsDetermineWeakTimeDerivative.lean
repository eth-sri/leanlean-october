module

public import HypoellipticAleksandrov.Measure.L2PairingConvergence
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SeparatedSpacetimeTestDensity
public import HypoellipticAleksandrov.Measure.TimeVelocity


/-!
# Separated tests determine the weak time derivative

This module passes from the distributional identity on separated time--space tests to the
identity on arbitrary smooth compactly supported spacetime tests.
-/

 public section

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ}

private theorem memLp_two_separatedProduct
     {S : HypoellipticAleksandrov.Parabolic.Region d}
    (a : ℝ → ℝ) (ha : Continuous a) (haK : HasCompactSupport a)
    (b : PDE.ScalarField d) (hb : Continuous b) (hbK : HasCompactSupport b) :
    MemLp (fun z : TimeVelocity d => a z.1 * b z.2) 2 (timeVelocityVolumeOn S) := (((ha.comp continuous_fst).mul (hb.comp continuous_snd)).memLp_of_hasCompactSupport (by
      apply HasCompactSupport.of_support_subset_isCompact (haK.isCompact.prod hbK.isCompact)
      intro z hz
      rw [mem_support] at hz
      exact ⟨subset_tsupport a (fun h => hz (by simp [h])),
        subset_tsupport b (fun h => hz (by simp [h]))⟩)).restrict S

variable {τ₁ τ₂ : ℝ} {O : PDE.VelocityRegion d}

private theorem finiteSeparated_identity

    {U W : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hU : ParabolicMemLpOn (Ioo τ₁ τ₂ ×ˢ O) 2 U)
    (hW : ParabolicMemLpOn (Ioo τ₁ τ₂ ×ˢ O) 2 W)
    (hseparated :
      ∀ (eta : OriginalTimeScalarTest τ₁ τ₂) (psi : PDE.WeakTestFunction O),
        (∫ z in Ioo τ₁ τ₂ ×ˢ O,
            U z * (eta.deriv z.1 * psi z.2) ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
          -∫ z in Ioo τ₁ τ₂ ×ˢ O,
            W z * (eta z.1 * psi z.2) ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))
    (q : FiniteSeparatedSpacetimeTest τ₁ τ₂ O) :
    (∫ z, U z * q.timeDeriv z ∂timeVelocityVolumeOn (Ioo τ₁ τ₂ ×ˢ O)) =
      -∫ z, W z * q.toFun z ∂timeVelocityVolumeOn (Ioo τ₁ τ₂ ×ˢ O) := by
  let μ := timeVelocityVolumeOn (Ioo τ₁ τ₂ ×ˢ O)
  have hdLp (m : Fin q.termCount) : MemLp
      (fun z : TimeVelocity d => (q.timeFactor m).deriv z.1 * q.spatialFactor m z.2) 2 μ :=
    memLp_two_separatedProduct _
      (contDiff_infty_iff_deriv.mp (q.timeFactor m).contDiff).2.continuous
      ((q.timeFactor m).hasCompactSupport.deriv)
      _ (q.spatialFactor m).contDiff.continuous (q.spatialFactor m).hasCompactSupport
  have hvLp (m : Fin q.termCount) : MemLp
      (fun z : TimeVelocity d => q.timeFactor m z.1 * q.spatialFactor m z.2) 2 μ :=
    memLp_two_separatedProduct _ (q.timeFactor m).contDiff.continuous
      (q.timeFactor m).hasCompactSupport _ (q.spatialFactor m).contDiff.continuous
      (q.spatialFactor m).hasCompactSupport
  have hUint (m : Fin q.termCount) : Integrable
      (fun z => U z * ((q.timeFactor m).deriv z.1 * q.spatialFactor m z.2)) μ := by
    simpa only [Pi.mul_def] using hU.integrable_mul (hdLp m)
  have hWint (m : Fin q.termCount) : Integrable
      (fun z => W z * (q.timeFactor m z.1 * q.spatialFactor m z.2)) μ := by
    simpa only [Pi.mul_def] using hW.integrable_mul (hvLp m)
  change (∫ z, U z * (∑ m : Fin q.termCount,
      (q.timeFactor m).deriv z.1 * q.spatialFactor m z.2) ∂μ) =
    -∫ z, W z * (∑ m : Fin q.termCount,
      q.timeFactor m z.1 * q.spatialFactor m z.2) ∂μ
  rw [show (fun z => U z * ∑ m : Fin q.termCount,
      (q.timeFactor m).deriv z.1 * q.spatialFactor m z.2) =
      fun z => ∑ m : Fin q.termCount,
        U z * ((q.timeFactor m).deriv z.1 * q.spatialFactor m z.2) by
        funext z; rw [Finset.mul_sum],
    integral_finset_sum Finset.univ (fun m _ => hUint m)]
  rw [show (fun z => W z * ∑ m : Fin q.termCount,
      q.timeFactor m z.1 * q.spatialFactor m z.2) =
      fun z => ∑ m : Fin q.termCount,
        W z * (q.timeFactor m z.1 * q.spatialFactor m z.2) by
        funext z; rw [Finset.mul_sum],
    integral_finset_sum Finset.univ (fun m _ => hWint m), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro m _
  exact hseparated (q.timeFactor m) (q.spatialFactor m)

variable (q : FiniteSeparatedSpacetimeTest τ₁ τ₂ O)

private theorem finiteSeparated_toFun_continuous

     : Continuous q.toFun := by
  unfold FiniteSeparatedSpacetimeTest.toFun
  apply continuous_finset_sum Finset.univ
  intro m _
  exact ((q.timeFactor m).contDiff.continuous.comp continuous_fst).mul
    ((q.spatialFactor m).contDiff.continuous.comp continuous_snd)

private theorem finiteSeparated_timeDeriv_continuous

     : Continuous q.timeDeriv := by
  unfold FiniteSeparatedSpacetimeTest.timeDeriv
  apply continuous_finset_sum Finset.univ
  intro m _
  exact ((contDiff_infty_iff_deriv.mp (q.timeFactor m).contDiff).2.continuous.comp
    continuous_fst).mul ((q.spatialFactor m).contDiff.continuous.comp continuous_snd)

private theorem finiteSeparated_hasCompactSupport_of_commonCompact


    (Kt : TopologicalSpace.Compacts ℝ) (Ky : TopologicalSpace.Compacts (PDE.Vec d))
    (hq : ∀ m, tsupport (q.timeFactor m : ℝ → ℝ) ×ˢ
      tsupport (q.spatialFactor m : PDE.ScalarField d) ⊆ (Kt : Set ℝ) ×ˢ (Ky : PDE.VelocityRegion d)) :
    HasCompactSupport q.toFun ∧ HasCompactSupport q.timeDeriv := ⟨HasCompactSupport.of_support_subset_isCompact (Kt.isCompact.prod Ky.isCompact) (by
      intro z hz
      by_contra hn
      apply hz
      unfold FiniteSeparatedSpacetimeTest.toFun
      apply Finset.sum_eq_zero
      intro m _
      by_contra hm
      exact hn (hq m ⟨subset_tsupport _ (fun ht => hm (by simp [ht])),
        subset_tsupport _ (fun hs => hm (by simp [hs]))⟩)),
    HasCompactSupport.of_support_subset_isCompact (Kt.isCompact.prod Ky.isCompact) (by
        intro z hz
        by_contra hn
        apply hz
        unfold FiniteSeparatedSpacetimeTest.timeDeriv
        apply Finset.sum_eq_zero
        intro m _
        by_contra hm
        have ht : z.1 ∈ tsupport ((q.timeFactor m).deriv) :=
          subset_tsupport _ (fun h => by
            apply hm
            rw [h, zero_mul])

        exact hn (hq m ⟨((closure_minimal support_deriv_subset (isClosed_tsupport _)) ht), subset_tsupport _ (fun hs => hm (by simp [hs]))⟩))⟩

/-- An identity against every separated test determines the weak time derivative. -/
theorem hasWeakTimeDerivOn_of_forall_separatedProduct

    (hO : IsOpen O)
    {U W : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hU : ParabolicMemLpOn (Ioo τ₁ τ₂ ×ˢ O) (2 ) U)
    (hW : ParabolicMemLpOn (Ioo τ₁ τ₂ ×ˢ O) (2 ) W)
    (hseparated :
      ∀ (eta : OriginalTimeScalarTest τ₁ τ₂) (psi : PDE.WeakTestFunction O),
        (∫ z in Ioo τ₁ τ₂ ×ˢ O,
            U z * (eta.deriv z.1 * psi z.2) ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
          -∫ z in Ioo τ₁ τ₂ ×ˢ O,
            W z * (eta z.1 * psi z.2) ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) :
    HasWeakTimeDerivOn (Ioo τ₁ τ₂ ×ˢ O) U W := by
  intro φ hφ hφcompact hφsubset
  let Kφ : TopologicalSpace.Compacts (TimeVelocity d) := ⟨tsupport φ, hφcompact.isCompact⟩
  let φsupported : ContDiffMapSupportedIn (TimeVelocity d) ℝ (⊤ ) Kφ :=
    { toFun := φ
      contDiff' := hφ
      zero_on_compl' := fun z hz => image_eq_zero_of_notMem_tsupport hz }
  let Φ : TestFunction (originalTimeOpenCylinderOpens τ₁ τ₂ O hO) ℝ (⊤ ) :=
    TestFunction.ofSupportedIn hφsubset φsupported
  obtain ⟨Kt, Ky, q, _hKt, _hKy, hqsupport, hval, hderiv⟩ :=
    exists_finiteSeparatedSpacetimeTest_tendsto_integral_sq hO Φ
  let μ := timeVelocityVolumeOn (Ioo τ₁ τ₂ ×ˢ O)
  have hΦ : (Φ : HypoellipticAleksandrov.Parabolic.ScalarField d) = φ := rfl
  have hdΦ : timeDerivative (Φ : HypoellipticAleksandrov.Parabolic.ScalarField d) = timeDerivative φ := by rw [hΦ]
  have hφdcont : Continuous (timeDerivative φ) := by
    unfold timeDerivative
    simpa using (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφdcompact : HasCompactSupport (timeDerivative φ) := by
    unfold timeDerivative
    simpa using hφcompact.fderiv_apply (𝕜 := ℝ) ((1, 0) )
  have hqcompact (n : ℕ)  :=
    finiteSeparated_hasCompactSupport_of_commonCompact (q n) Kt Ky (hqsupport n)
  have hvalLp (n : ℕ) : MemLp (fun z => (q n).toFun z - φ z) 2 μ :=
    ((finiteSeparated_toFun_continuous (q n)).sub hφ.continuous).memLp_of_hasCompactSupport
      ((hqcompact n).1.sub hφcompact)
  have hderivLp (n : ℕ) : MemLp
      (fun z => (q n).timeDeriv z - timeDerivative φ z) 2 μ :=
    ((finiteSeparated_timeDeriv_continuous (q n)).sub hφdcont).memLp_of_hasCompactSupport
      ((hqcompact n).2.sub hφdcompact)
  have hpVal := tendsto_integral_mul_of_memLp_two_of_tendsto_integral_sq
    hW hvalLp (by simpa only [μ, hΦ] using hval)
  have hpDeriv := tendsto_integral_mul_of_memLp_two_of_tendsto_integral_sq
    hU hderivLp (by simpa only [μ, hdΦ] using hderiv)



  have hright : Tendsto (fun n => ∫ z, W z * (q n).toFun z ∂μ)
      atTop (nhds (∫ z, W z * φ z ∂μ)) := by
    have hconst : Tendsto (fun _ : ℕ => ∫ z, W z * φ z ∂μ) atTop
        (nhds (∫ z, W z * φ z ∂μ)) := tendsto_const_nhds
    have hsum := hconst.add hpVal
    have hsum' : Tendsto (fun n => (∫ z, W z * φ z ∂μ) +
        ∫ z, W z * ((q n).toFun z - φ z) ∂μ) atTop
        (nhds (∫ z, W z * φ z ∂μ)) := by
      simpa only [add_zero] using hsum
    apply hsum'.congr'
    filter_upwards with n
    symm

    have herr : Integrable (fun z => W z * ((q n).toFun z - φ z)) μ := by
      simpa only [Pi.mul_def] using hW.integrable_mul (hvalLp n)
    rw [← integral_add (by
        simpa only [Pi.mul_def] using hW.integrable_mul (show MemLp φ 2 μ from hφ.continuous.memLp_of_hasCompactSupport hφcompact)) herr]
    apply integral_congr_ae
    filter_upwards with z
    ring
  have hnegRight : Tendsto (fun n => ∫ z, U z * (q n).timeDeriv z ∂μ)
      atTop (nhds (-∫ z, W z * φ z ∂μ)) := by
    apply hright.neg.congr'
    filter_upwards with n
    exact (finiteSeparated_identity hU hW hseparated (q n)).symm
  simpa only [μ, timeVelocityVolumeOn] using tendsto_nhds_unique (by
      have hconst : Tendsto (fun _ : ℕ => ∫ z, U z * timeDerivative φ z ∂μ) atTop
          (nhds (∫ z, U z * timeDerivative φ z ∂μ)) := tendsto_const_nhds
      have hsum := hconst.add hpDeriv
      have hsum' : Tendsto (fun n => (∫ z, U z * timeDerivative φ z ∂μ) +
          ∫ z, U z * ((q n).timeDeriv z - timeDerivative φ z) ∂μ) atTop
          (nhds (∫ z, U z * timeDerivative φ z ∂μ)) := by
        simpa only [add_zero] using hsum
      apply hsum'.congr'
      filter_upwards with n
      symm
      have hbase : Integrable (fun z => U z * timeDerivative φ z) μ := by
        simpa only [Pi.mul_def] using hU.integrable_mul (show MemLp (timeDerivative φ) 2 μ from hφdcont.memLp_of_hasCompactSupport hφdcompact)
      have herr : Integrable
          (fun z => U z * ((q n).timeDeriv z - timeDerivative φ z)) μ := by
        simpa only [Pi.mul_def] using hU.integrable_mul (hderivLp n)
      rw [← integral_add hbase herr]
      apply integral_congr_ae
      filter_upwards with z
      ring) hnegRight

end HypoellipticAleksandrov.Parabolic.Dirichlet
