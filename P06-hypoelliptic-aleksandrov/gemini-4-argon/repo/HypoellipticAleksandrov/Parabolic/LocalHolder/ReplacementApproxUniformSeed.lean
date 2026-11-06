module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxClassicalJet
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxSeedNorm
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalGradientCollar
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalHessianCollar
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalTimeCoercivity
import Mathlib.Tactic.Linarith
import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxCoefficientBounds
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalHessianBound
import HypoellipticAleksandrov.Parabolic.OriginalTimePlateau
import HypoellipticAleksandrov.Parabolic.QuantitativeSmoothCutoffExistence
import HypoellipticAleksandrov.Coefficients.Ellipticity
import HypoellipticAleksandrov.Parabolic.C2ToScalarC12
import HypoellipticAleksandrov.Parabolic.SpatialCoordinateDerivatives

/-! # Uniform weight-two energy for homogeneous classical approximations

The seed estimate depends only on outer value energy. Neither a bound on boundary
 derivatives nor a solution-dependent constant enters its conclusion.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise

private theorem square_integral_entry_le_sum {d S} (G : TimeVelocity d → PDE.Vec d)
    (hG : ∀ j, MemLp (fun z => G z j) 2 (timeVelocityVolumeOn S)) (j : Fin d) :
    (∫ z in S, G z j ^ 2) ≤ ∫ z in S, ∑ k, G z k ^ 2 := by
  classical
  have hi (k : Fin d) : IntegrableOn (fun z => G z k ^ 2) S := by
    simpa only [Real.norm_eq_abs, sq_abs, timeVelocityVolumeOn, IntegrableOn] using
      (hG k).integrable_norm_pow (by norm_num)
  apply integral_mono_ae (hi j) (integrable_finsetSum Finset.univ (fun k _ => hi k))
  exact Eventually.of_forall (fun z =>
    Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ j))

private theorem square_integral_hessian_entry_le_sum {d S} (H : TimeVelocity d → PDE.Mat d)
    (hH : ∀ i j, MemLp (fun z => H z i j) 2 (timeVelocityVolumeOn S)) (i j : Fin d) :
    (∫ z in S, H z i j ^ 2) ≤ ∫ z in S, ∑ k, ∑ l, H z k l ^ 2 := by
  classical
  have hi (k l : Fin d) : IntegrableOn (fun z => H z k l ^ 2) S := by
    simpa only [Real.norm_eq_abs, sq_abs, timeVelocityVolumeOn, IntegrableOn] using
      (hH k l).integrable_norm_pow (by norm_num)
  apply integral_mono_ae (hi i j) (integrable_finsetSum Finset.univ (fun k _ =>
    integrable_finsetSum Finset.univ (fun l _ => hi k l)))
  exact Eventually.of_forall (fun z => (Finset.single_le_sum
    (fun l _ => sq_nonneg _) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg _))
      (Finset.mem_univ i)))

/- The literal weight-two seed is uniformly bounded by outer value energy. -/
theorem exists_uniform_classical_seed_constant {d }
    (a T q₀ s₀ s₁ q₁ : ℝ)
    (hq₀s₀ : q₀ < s₀) (hs₀s₁ : s₀ ≤ s₁) (hs₁q₁ : s₁ < q₁)
    (Ω O₀ O ) (hΩ : IsOpen Ω)
    (hDc : IsCompact (closure (Ioo a T ×ˢ Ω)))
    (hO₀ : IsOpen O₀) (hO₀c : IsCompact (closure O₀))
    (hQc : IsCompact (closure (Ioo q₀ q₁ ×ˢ O₀)))
    (hQD : closure (Ioo q₀ q₁ ×ˢ O₀) ⊆ Ioo a T ×ˢ Ω)
    (hO : IsOpen O) (hOc : IsCompact (closure O)) (hOO₀ : closure O ⊆ O₀)
    (hVc : IsCompact (closure (Ioo s₀ s₁ ×ˢ O)))
    (hVQ : closure (Ioo s₀ s₁ ×ˢ O) ⊆ Ioo q₀ q₁ ×ˢ O₀)
    (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : TimeVelocity d → ℝ)
      (hu : IsScalarC12On u (Ioo a T ×ˢ Ω)),
      IntegrableOn (fun z => u z ^ 2) (Ioo a T ×ˢ Ω) →
      (∀ z ∈ Ioo a T ×ˢ Ω, scalarTimeDerivative u z +
        matrixContraction (coefficientAt A z) (scalarSpatialHessian u z) = 0) →
      ((classicalLocalW12Jet u hu (isOpen_Ioo.prod hO) hVc
        (hVQ.trans (subset_closure.trans hQD))).toWeakDerivativeFamily
          (isOpen_Ioo.prod hO)).squaredL2Norm ≤
        C * ∫ z in Ioo a T ×ˢ Ω, u z ^ 2 := by
  classical
  let D := Ioo a T ×ˢ Ω
  let Q := Ioo q₀ q₁ ×ˢ O₀
  let V := Ioo s₀ s₁ ×ˢ O
  have hQ : IsOpen Q := isOpen_Ioo.prod hO₀
  have hV : IsOpen V := isOpen_Ioo.prod hO
  have hVD := hVQ.trans (subset_closure.trans hQD)
  obtain ⟨Cg, hCg, hgrad⟩ := exists_local_gradient_collar_constant
    a T Ω hΩ hDc Q hQ.measurableSet hQc hQD A hA lam hlam
    (fun z _ => hlo z.1 z.2)
  obtain ⟨Ch, hCh, hhess⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ J : ParabolicW12Function d (Ioo q₀ q₁ ×ˢ O₀) 2,
      (∀ᵐ z ∂timeVelocityVolumeOn (Ioo q₀ q₁ ×ˢ O₀),
        J.timeDeriv z + ∑ i, ∑ j, A z.1 z.2 i j * J.velocityHessian z j i = 0) →
      (∫ z in Ioo s₀ s₁ ×ˢ O, ∑ k, ∑ i, J.velocityHessian z k i ^ 2) ≤
        C * ((eLpNorm J.toFun 2 (timeVelocityVolumeOn (Ioo q₀ q₁ ×ˢ O₀))).toReal ^ 2 +
          ∑ j, (eLpNorm (fun z => J.velocityGrad z j) 2
            (timeVelocityVolumeOn (Ioo q₀ q₁ ×ˢ O₀))).toReal ^ 2) := by
    let V := O
    have hV := hO
    have hVc := hOc
    classical
    let Q := Ioo q₀ q₁ ×ˢ O₀
    have hQ : IsOpen Q := isOpen_Ioo.prod hO₀
    have hQc : IsCompact (closure Q) := by
      rw [closure_prod_eq]
      exact (isCompact_Icc.of_isClosed_subset isClosed_closure
        (closure_minimal Ioo_subset_Icc_self isClosed_Icc)).prod hO₀c
    obtain ⟨M, hM, hDA⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ (closure Q), ∀ i j k,
      |spatialPartial k (fun y => A z.1 y i j) z.2| ≤ M := by
      let K := (closure Q)
      let D (z : TimeVelocity d) (k i j : Fin d) :=
        spatialPartial k (fun y => A z.1 y i j) z.2
      have hD : Continuous D := by
        apply continuous_pi
        intro k
        apply continuous_pi
        intro i
        apply continuous_pi
        intro j
        have hcoeff :=
          (contDiff_apply ℝ ℝ j).comp ((contDiff_apply ℝ (Fin d → ℝ) i).comp hA)
        have hc12 := isScalarC12On_of_contDiff_two (hcoeff.of_le (by simp)) univ
        exact (continuous_apply k).comp
          (continuousOn_univ.mp hc12.continuousOn_scalarSpatialGradient)
      obtain ⟨C, hC⟩ := hQc.exists_bound_of_continuousOn hD.continuousOn
      refine ⟨max C 0, le_max_right _ _, ?_⟩
      intro z hz i j k
      calc
        _ = ‖D z k i j‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖D z k i‖ := norm_le_pi_norm _ j
        _ ≤ ‖D z k‖ := norm_le_pi_norm _ i
        _ ≤ ‖D z‖ := norm_le_pi_norm _ k
        _ ≤ C := hC z hz
        _ ≤ max C 0 := le_max_left _ _
    obtain ⟨Kη, ⟨η⟩⟩ := exists_quantitativeSmoothCutoff_tsupport_subset hVc hO₀ hOO₀
    have hKη : 0 ≤ Kη := (PDE.vecEuclideanNorm_nonneg _).trans (η.gradient_bound 0)
    obtain ⟨ζ, Kζ, hζ, hcζ, hKζ, hζ0, hζ1, hζone, hsζ, hdζ⟩ :=
      exists_smooth_timePlateau_with_deriv_bound q₀ s₀ s₁ q₁ hq₀s₀ hs₀s₁ hs₁q₁
    have hAs : ∀ t ∈ Ioo q₀ q₁, ∀ i j,
        ContDiffOn ℝ 1 (fun y => A t y i j) O₀ := by
      intro t _ i j
      have hc : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => A z.1 z.2 i j) :=
        (contDiff_apply ℝ ℝ j).comp ((contDiff_apply ℝ (Fin d → ℝ) i).comp hA)
      exact ((hc.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)).contDiffOn
    obtain ⟨C, hC, hrun⟩ := exists_local_homogeneous_hessian_constant q₀ q₁ O₀ hO₀
      (fun z => A z.1 z.2) hA.continuous.aestronglyMeasurable.restrict hAs
      lam Lam M hlam hlamLam hM (fun z _ => hlo z.1 z.2) (fun z _ => hhi z.1 z.2)
      (fun z hz i j k => hDA z (subset_closure hz) i j k)
      η.toFun η.smooth η.hasCompactSupport η.tsupport_subset η.nonneg η.le_one
      Kη hKη (fun y _ i => η.abs_classicalGradient_apply_le y i)
      ζ hζ hcζ hsζ hζ0 hζ1 Kζ hKζ (fun t _ => hdζ t)
    refine ⟨C, hC, ?_⟩
    intro J heq
    let f (z : TimeVelocity d) := ∑ k, ∑ i, J.velocityHessian z k i ^ 2
    have hfi : IntegrableOn f Q := by
      apply integrable_finsetSum
      intro k _
      apply integrable_finsetSum
      intro i _
      simpa only [Real.norm_eq_abs, sq_abs, timeVelocityVolumeOn, IntegrableOn] using
        (J.velocityHessian_memLp k i).integrable_norm_pow (by norm_num)
    have hwcont : Continuous (fun z : TimeVelocity d => ζ z.1 * η.toFun z.2 ^ 2) :=
      (hζ.continuous.comp continuous_fst).mul ((η.smooth.continuous.comp continuous_snd).pow 2)
    have hwbound : ∀ᵐ z ∂volume.restrict Q,
        ‖ζ z.1 * η.toFun z.2 ^ 2‖ ≤ 1 := Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hζ0 _) (sq_nonneg _))]
      exact (mul_le_mul_of_nonneg_left
        (pow_le_one₀ (η.nonneg _) (η.le_one _)) (hζ0 _)).trans
          (by simpa only [mul_one] using hζ1 z.1)
    have hwi := hfi.bdd_mul hwcont.aestronglyMeasurable.restrict hwbound
    have hmono := setIntegral_mono_set hwi
      (Eventually.of_forall (fun z => mul_nonneg
        (mul_nonneg (hζ0 _) (sq_nonneg _))
        (Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun i _ => sq_nonneg _)))))
      (Eventually.of_forall (fun z (hz : z ∈ Ioo s₀ s₁ ×ˢ V) =>
        ⟨⟨hq₀s₀.trans hz.1.1, hz.1.2.trans hs₁q₁⟩, hOO₀ (subset_closure hz.2)⟩))
    have he : (∫ z in Ioo s₀ s₁ ×ˢ V, ζ z.1 * η.toFun z.2 ^ 2 * f z) =
        ∫ z in Ioo s₀ s₁ ×ˢ V, f z := by
      apply setIntegral_congr_fun (isOpen_Ioo.prod hV).measurableSet
      intro z hz
      change ζ z.1 * η.toFun z.2 ^ 2 * f z = f z
      rw [hζone z.1 ⟨hz.1.1.le, hz.1.2.le⟩,
        η.eq_one_on_inner z.2 (subset_closure hz.2), one_pow, one_mul, one_mul]
    rw [he] at hmono
    exact hmono.trans (hrun J heq)
  let Ct := (d : ℝ) ^ 2 * Lam ^ 2
  let B := 1 + Cg + Ch * (1 + Cg) + Ct * Ch * (1 + Cg)
  refine ⟨(Fintype.card (ParabolicDerivativeIndex d 2) : ℝ) * B, by
    dsimp [B, Ct]
    positivity, ?_⟩
  intro u hu hq heq
  let Jq := classicalLocalW12Jet u hu hQ hQc hQD
  let Jv := classicalLocalW12Jet u hu hV hVc hVD
  let N := ∫ z in D, u z ^ 2
  have hN : 0 ≤ N := integral_nonneg (fun _ => sq_nonneg _)
  have hqQ : (∫ z in Q, u z ^ 2) ≤ N :=
    setIntegral_mono_set hq (Eventually.of_forall (fun z => sq_nonneg _))
      (Eventually.of_forall (fun z hz => hQD (subset_closure hz)))
  have hqV : (∫ z in V, u z ^ 2) ≤ N :=
    setIntegral_mono_set hq (Eventually.of_forall (fun z => sq_nonneg _))
      (Eventually.of_forall (fun z hz => hVD (subset_closure hz)))
  have hgQ :=
    hgrad u hu hq heq
  have hPDE : ∀ᵐ z ∂timeVelocityVolumeOn Q,
      Jq.timeDeriv z + ∑ i, ∑ j, A z.1 z.2 i j * Jq.velocityHessian z j i = 0 := by
    apply ae_restrict_of_forall_mem hQ.measurableSet
    intro z hz
    have hh := scalarSpatialHessian_isSymm_of_c12 hu (hQD (subset_closure hz))
    have hentry (i j : Fin d) : scalarSpatialHessian u z j i =
        scalarSpatialHessian u z i j := congrArg (fun M : PDE.Mat d => M i j) hh
    simpa only [Jq, classicalLocalW12Jet, matrixContraction, coefficientAt, hentry]
      using heq z (hQD (subset_closure hz))
  have hH := hhess Jq hPDE
  have hqnorm : (eLpNorm Jq.toFun 2 (timeVelocityVolumeOn Q)).toReal ^ 2 =
      ∫ z in Q, u z ^ 2 := (integral_square_eq_eLpNorm_two_sq u Jq.memLp).symm
  have hgnorm : (∑ j, (eLpNorm (fun z => Jq.velocityGrad z j) 2
      (timeVelocityVolumeOn Q)).toReal ^ 2) =
      ∫ z in Q, ∑ j, scalarSpatialGradient u z j ^ 2 := by
    rw [integral_finsetSum Finset.univ (fun j _ => by
      simpa only [Jq, classicalLocalW12Jet, Real.norm_eq_abs, sq_abs,
        timeVelocityVolumeOn, IntegrableOn] using
        (Jq.velocityGrad_memLp j).integrable_norm_pow (by norm_num))]
    apply Finset.sum_congr rfl
    intro j _
    exact (integral_square_eq_eLpNorm_two_sq _ (Jq.velocityGrad_memLp j)).symm
  rw [hqnorm, hgnorm] at hH
  have hHbound : (∫ z in V, ∑ k, ∑ i, scalarSpatialHessian u z k i ^ 2) ≤
      Ch * (1 + Cg) * N := by
    calc
      _ ≤ Ch * ((∫ z in Q, u z ^ 2) +
        ∫ z in Q, ∑ j, scalarSpatialGradient u z j ^ 2) := hH
      _ ≤ Ch * (N + Cg * N) :=
        mul_le_mul_of_nonneg_left (add_le_add hqQ hgQ) hCh
      _ = _ := by ring
  have hgi : IntegrableOn
      (fun z => ∑ j, scalarSpatialGradient u z j ^ 2) Q := by
    apply integrable_finsetSum
    intro j _
    simpa only [Jq, classicalLocalW12Jet, Real.norm_eq_abs, sq_abs,
      timeVelocityVolumeOn, IntegrableOn] using
      (Jq.velocityGrad_memLp j).integrable_norm_pow (by norm_num)
  have hgV : (∫ z in V, ∑ j, scalarSpatialGradient u z j ^ 2) ≤ Cg * N := by
    exact (setIntegral_mono_set hgi
      (Eventually.of_forall (fun z => Finset.sum_nonneg (fun j _ => sq_nonneg _)))
      (Eventually.of_forall (fun z hz => hVQ (subset_closure hz)))).trans hgQ
  have htime := integral_local_time_derivative_sq_le V hV.measurableSet u A Lam
    (hlam.le.trans hlamLam)
    (fun z _ i j => abs_apply_le_of_loewner hlam (hlo z.1 z.2) (hhi z.1 z.2) i j)
    Jv.timeDeriv_memLp Jv.velocityHessian_memLp
    (fun z hz => heq z (hVD (subset_closure hz)))
  have hswap : (∫ z in V, ∑ i, ∑ j, scalarSpatialHessian u z j i ^ 2) =
      ∫ z in V, ∑ i, ∑ j, scalarSpatialHessian u z i j ^ 2 := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => Finset.sum_comm)
  rw [hswap] at htime
  have htimeB : (∫ z in V, scalarTimeDerivative u z ^ 2) ≤
      Ct * Ch * (1 + Cg) * N := by
    exact htime.trans (by
      simpa only [Ct, mul_assoc] using
        mul_le_mul_of_nonneg_left hHbound (show 0 ≤ Ct by dsimp [Ct]; positivity))
  have hcoef : 0 ≤ Ch * (1 + Cg) := by positivity
  have htcoef : 0 ≤ Ct * Ch * (1 + Cg) := by dsimp [Ct]; positivity
  have h1B : 1 ≤ B := by dsimp [B]; linarith only [hCg, hcoef, htcoef]
  have hgB : Cg ≤ B := by dsimp [B]; linarith only [hcoef, htcoef]
  have hhB : Ch * (1 + Cg) ≤ B := by dsimp [B]; linarith only [hCg, htcoef]
  have htB : Ct * Ch * (1 + Cg) ≤ B := by dsimp [B]; linarith only [hCg, hcoef]
  apply (squaredL2Norm_classical_seed_le hV Jv (B * N) ?_ ?_ ?_ ?_).trans
  · exact le_of_eq (by ring)
  · rw [← integral_square_eq_eLpNorm_two_sq _ Jv.memLp]
    exact hqV.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right h1B hN)
  · rw [← integral_square_eq_eLpNorm_two_sq _ Jv.timeDeriv_memLp]
    exact htimeB.trans (mul_le_mul_of_nonneg_right htB hN)
  · intro j
    rw [← integral_square_eq_eLpNorm_two_sq _ (Jv.velocityGrad_memLp j)]
    exact (square_integral_entry_le_sum (scalarSpatialGradient u)
      Jv.velocityGrad_memLp j).trans (hgV.trans (mul_le_mul_of_nonneg_right hgB hN))
  · intro i j
    rw [← integral_square_eq_eLpNorm_two_sq _ (Jv.velocityHessian_memLp i j)]
    exact (square_integral_hessian_entry_le_sum (scalarSpatialHessian u)
      Jv.velocityHessian_memLp i j).trans
        (hHbound.trans (mul_le_mul_of_nonneg_right hhB hN))

end HypoellipticAleksandrov.Parabolic.LocalHolder
