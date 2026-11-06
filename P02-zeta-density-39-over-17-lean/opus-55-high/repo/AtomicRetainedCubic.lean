module
public import AtomicBoxBand
public import GuthMaynard.Improvement.CubicRetainedPartition
public import GuthMaynard.Improvement.RadialScaleBudget
import WeylPort.Analytic.RealLaplace

public section

open Finset MeasureTheory Set
open scoped FourierTransform ContDiff
namespace Montgomery.RationalMoment
open GuthMaynard.Improvement
open GuthMaynard.Improvement.AtomicCubic

/-- The retained Poisson cubic for the literal atomic time measure. Every
Fourier moment is supplied by fixed-width box smoothing; the remainder
retains its full cardinality-cubed factor. No limiting density is used. -/
theorem retained_atomic_cubic_estimate (w : MathCollab.Density.ReflectionCutoff)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η C T₀ : ℝ, 0 < η ∧ η < (4:ℝ)/5 ∧ 0 < C ∧ 2 ≤ T₀ ∧
      ∀ T L : ℝ, T₀ ≤ T → T^((4:ℝ)/5) ≤ L → L ≤ T →
      ∀ W : Finset ℝ,
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      ‖kernelCubic (finiteTimeMeasure W)
        (retainedPoissonKernel (volume.restrict (Icc (1/2:ℝ) 5))
          (fun x => (w x:ℂ)) L (poissonModes (T^(1+η)/L)))‖ ≤
      C*(T^ε*(T^2*(W.card:ℝ)*Real.sqrt (W.card:ℝ)+
        T*L*Real.sqrt (W.card:ℝ)*Real.sqrt (discreteAdditiveEnergy W:ℝ))+
        T^(-100:ℝ)*(W.card:ℝ)^3) := by
  obtain ⟨η,Cs,T₀,hη,hη1,hCs,hT₀,hstrip⟩ := cubic_masked_near_estimate
    (1/10) 10 (by norm_num) (by norm_num) (by norm_num) hε
  obtain ⟨n,hn⟩ := choose_radial_discard_order hη
  pm_107 Cn Ct hCn hCt hprofile radial_profile_sum_bound w n
  let D : ℝ := 27*Ct*(99/10:ℝ)^2
  refine ⟨η,2048*Cn*Cs+D,T₀,hη,hη1,by dsimp [D]; positivity,hT₀,?_⟩
  intro T L hT hLl hLu W hsep
  pm_2721
  let μ := boxTimeDensity W
  let M := ∫ t, μ t^2
  let EF := ∫ ξ, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^4
  pm_5436
  let S := retainedCubicModes U
  pm_5085 R E
  have hT2 : 2 ≤ T := hT₀.trans hT
  pm_4572
  pm_4573
  pm_1364
  pm_2722 hR hE
  pm_4586 hM M
  pm_8870 hEF EF
  pm_4556
  have hMb : M ≤ 32*R := box_time_square_bound W hsep
  have hEb : EF ≤ 64*E := box_time_fourth_bound W
  have hrootM : Real.sqrt M ≤ 8*Real.sqrt R := by
    pm_6866 hR
    nlinarith
  have hrootE : Real.sqrt EF ≤ 8*Real.sqrt E := by
    pm_6866 hE
    nlinarith [hEb]
  have hS : ∀ m ∈ S, m.1 ∈ poissonModes U ∧ m.2.1 ∈ poissonModes U ∧ m.2.2 ∈ poissonModes U :=
    fun m hm => (retainedCubicModes_mem U m).mp hm
  have hs := hstrip T L μ univ univ univ univ S hT hLl hLu
    (box_time_measurable W) (box_time_nonneg W) (box_time_integrable W)
    (box_time_square_integrable W) MeasurableSet.univ MeasurableSet.univ
    MeasurableSet.univ MeasurableSet.univ (by simp) (by simp) Subset.rfl Subset.rfl hS
  have hs' : L^3*(∑ m ∈ S, ∫ p in ratioBox, maskedRadialNearMass μ univ univ univ L (T^η) m p) ≤
      256*Cs*T^ε*X := by
    have hs0 : L^3*(∑ m ∈ S, ∫ p in ratioBox, maskedRadialNearMass μ univ univ univ L (T^η) m p) ≤
        Cs*T^ε*Real.sqrt M*(T^2*M+T*L*Real.sqrt EF) := by
      have hPl : (∫ ξ, ‖𝓕 (fun t => (μ t:ℂ)) ξ‖^2) = M :=
        ordinary_real_fourier_integral_square (box_time_integrable W) (box_time_square_integrable W)
      pm_89 setIntegral_univ hPl ratioBox EF hs
    calc
      _ ≤ Cs*T^ε*Real.sqrt M*(T^2*M+T*L*Real.sqrt EF) := hs0
      _ ≤ Cs*T^ε*(8*Real.sqrt R)*(T^2*(32*R)+T*L*(8*Real.sqrt E)) := by gcongr
      _ ≤ 256*Cs*T^ε*X := by
        dsimp [X]
        nlinarith [show 0 ≤ Cs*T^ε*T*L*Real.sqrt R*Real.sqrt E by positivity]
  have hbF (ξ : ℝ) : ‖measureFourier (finiteTimeMeasure W) ξ‖ ≤ R := by
    rw [finite_time_fourier]
    exact (norm_sum_le _ _).trans_eq (by simp [phase_norm,R])
  have hp := hprofile L (T^η) S (measureFourier (finiteTimeMeasure W)) R 8 μ
    hH (operator_measureFourier_continuous _) hR hbF (by norm_num)
    (box_time_measurable W) (box_time_nonneg W) (box_time_integrable W)
    (fun p hp => atomic_ratio_box_domination W hp)
  have hU : 1 ≤ U := by
    dsimp [U]
    apply (le_div_iff₀ hLp).mpr
    simpa only [one_mul] using hLu.trans (by
      calc
        T = T^(1:ℝ) := (Real.rpow_one T).symm
        _ ≤ T^(1+η) := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith))
  have hcard : (S.card:ℝ) ≤ 27*U^3 := by
    have hh : (S.card:ℝ) ≤ (cubicModes U).card := by
      exact_mod_cast Finset.card_le_card (retainedCubicModes_subset U)
    exact hh.trans (cubicModes_card hU)
  have hscale : L^3*U^3 ≤ T^(6+3*η) := by
    have he : L^3*U^3 = T^(3+3*η) := by
      dsimp [U]
      rw [← mul_pow,mul_div_cancel₀ _ hLp.ne',← Real.rpow_natCast (T^(1+η)) 3,
        ← Real.rpow_mul hTp.le]
      congr 1
      ring
    rw [he]
    exact Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have htail : L^3*(S.card:ℝ)*Ct/(T^η)^n*R^3*(99/10:ℝ)^2 ≤ D*T^(-100:ℝ)*R^3 := by
    calc
      _ ≤ L^3*(27*U^3)*Ct/(T^η)^n*R^3*(99/10:ℝ)^2 := by gcongr
      _ = D*((L^3*U^3)/(T^η)^n)*R^3 := by dsimp [D]; ring
      _ ≤ D*(T^(6+3*η)/(T^η)^n)*R^3 := by gcongr
      _ ≤ _ := by gcongr; exact hn T hT1
  have hsupp : ∀ x, x ∉ Icc (1/2:ℝ) 5 → (w x:ℂ)=0 := by
    pm_4496
    simp [hz]
  have heq := GuthMaynard.Improvement.AtomicCubic.retained_cubic_radial_assembly
    (finiteTimeMeasure W) w.complex_smooth (by norm_num : (0:ℝ)<1/2)
    (by norm_num : (1/2:ℝ)≤5) hsupp L (poissonModes U)
  have heq' : kernelCubic (finiteTimeMeasure W)
      (retainedPoissonKernel (volume.restrict (Icc (1/2:ℝ) 5)) (fun x => (w x:ℂ)) L (poissonModes U)) =
      (L:ℂ)^3*(∑ m ∈ S, ∫ p in ratioBox,
        radialKernel (fun x => (w x:ℂ)) L m p*GuthMaynard.Improvement.AtomicCubic.ratioFourierProduct
          (measureFourier (finiteTimeMeasure W)) p) := by
    simpa only [S,retainedCubicModes,sum_product,ratioBox,show (1/2:ℝ)/5=1/10 by norm_num,
      show (5:ℝ)/(1/2)=10 by norm_num] using heq
  rw [abs_of_pos hLp] at hp
  rw [heq']
  calc
    _ ≤ L^3*Cn*8*(∑ m ∈ S, ∫ p in ratioBox, maskedRadialNearMass μ univ univ univ L (T^η) m p)+
        L^3*(S.card:ℝ)*Ct/(T^η)^n*R^3*(99/10:ℝ)^2 := hp
    _ ≤ (Cn*8)*(256*Cs*T^ε*X)+D*T^(-100:ℝ)*R^3 := by
      apply add_le_add _ htail
      convert mul_le_mul_of_nonneg_left hs' (show 0 ≤ Cn*8 by positivity) using 1
      ring
    _ ≤ (2048*Cn*Cs+D)*(T^ε*X+T^(-100:ℝ)*R^3) := by
      nlinarith [mul_nonneg (show 0 ≤ D by dsimp [D]; positivity) (show 0 ≤ T^ε*X by positivity),
        mul_nonneg (show 0 ≤ 2048*Cn*Cs by positivity) (show 0 ≤ T^(-100:ℝ)*R^3 by positivity)]

end Montgomery.RationalMoment
