module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitFourierShortTime
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitFourierOptimization
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitFourierSplit
import HypoellipticAleksandrov.KineticAleksandrov.Decay.FourierDecay
import HypoellipticAleksandrov.KineticAleksandrov.Decay.UnitBlock
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.Assembly
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.KilledFourierConstants
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.KilledFourierDefect
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.KilledFourierWhole
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ShortTimeExit
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ShortTimeExitCanonical
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierKernelsTranslation

/-! # Optimized Fourier decay of the full local ball exit measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Parabolic
open HypoellipticAleksandrov Decay

/- The actual exit measure retains time and velocity and has the source's optimized decay. -/
theorem ballExit_fourier_decay
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
        (v₀ : PDE.Vec d) (R : ℝ) (hR : 0 < R)
        (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t}),
      P.1.velocity ∈ PDE.euclideanBall v₀ (3 * R / 4) →
      T.1 - P.1.time = R ^ 2 / 8 →
      let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
      ∀ ξ : PDE.Vec d,
        ((exitFourier ν ξ).variation univ).toReal ≤
          C * Real.exp (-c * (R ^ 3 * PDE.vecEuclideanNorm ξ) ^ (1 / 3 : ℝ)) := by
  obtain ⟨C₀, c₀, hC₀, hc₀, htwo⟩ : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
        (v₀ : PDE.Vec d) (R : ℝ) (hR : 0 < R)
        (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
        (H : {t : ℝ // P.1.time < t ∧ t < T.1}),
      P.1.velocity ∈ PDE.euclideanBall v₀ (3 * R / 4) →
      H.1 - P.1.time ≤ R ^ 2 / 8 → ∀ ξ : PDE.Vec d,
      ((exitFourier (ballExit hH hLE hd hlam hLam B hB v₀ hR P T) ξ).variation univ).toReal ≤
        C * (Real.exp (-c * R ^ 2 / (H.1 - P.1.time)) +
          Real.exp (-c * (H.1 - P.1.time) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ))) := by
    obtain ⟨Cs, cs, hCs, hcs, hloss⟩ :=
      ballKernel_short_time_loss hH hLE d hd lam Lam hlam hLam
    obtain ⟨Ck, ck, hCk, hck, hkilled⟩ :
        ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
              ∀ (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
                (v₀ : PDE.Vec d) (R : ℝ) (hR : 0 < R)
                (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t}),
              P.1.velocity ∈ PDE.euclideanBall v₀ (3 * R / 4) →
              T.1 - P.1.time ≤ R ^ 2 / 8 →
              let Kb := localBallKernel hH hLE hd hlam hLam B hB v₀ hR
              ∀ (ξ : PDE.Vec d)
                (q : EvolutionQuery (PDE.euclideanBall v₀ R) (fun _ => 0)),
                q.1 = (P.1.time, (T.1, (P.1.velocity, P.1.position))) →
                ((fourierProjection Kb q ξ).variation univ).toReal ≤
                  C * (Real.exp (-c * R ^ 2 / (T.1 - P.1.time)) +
                    Real.exp (-c * (T.1 - P.1.time) *
                      PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ))) := by
      obtain ⟨Cs, cs, hCs, hcs, hloss⟩ :=
        ballKernel_short_time_loss hH hLE d hd lam Lam hlam hLam
      obtain ⟨Cf, cf, hCf, hcf, hdecay⟩ : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
          ∀ (B : CoefficientField d), IsSectionTwoCoefficient lam Lam B →
          ∀ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => 0))
            (K : MovingFiberKernel (wholeSpace d) (fun _ => 0)),
          RealizesTerminalEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ
            (zIndependentCoefficient B) (identityDrift d) S K →
          ∀ (σ τ : ℝ) (hστ : σ < τ), ∀ v ξ z : PDE.Vec d,
            ((fourierProjection K (wholeSpaceQuery σ τ hστ.le v z) ξ).variation
              univ).toReal ≤ C * Real.exp (-c * (τ - σ) *
                PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ)) := by
          have hEvol : IterationEvolutionStatement := exists_terminalEvolution_of_classical hLE hH
          obtain ⟨C, c, hC, hc, hdecay⟩ := fourier_decay_whole_space_of_unitBlock
            d hd lam Lam hlam hLam hEvol (unit_frequency_block_W hEvol d hd lam Lam hlam hLam)
          refine ⟨C, c, hC, hc, ?_⟩
          intro B hB S K hreal σ τ hστ v ξ z
          have hcov := (iteration_evolution_clauses hEvol hd hlam hLam B hB S K hreal).2.2
          rw [fourierKernel_eq_startingPosition K hcov]
          exact hdecay B hB S K hreal σ τ hστ v ξ (wholeSpaceQuery σ τ hστ.le v 0)
            rfl _ (fourierKernel_spec K σ τ hστ.le ξ v)



      refine ⟨max Cs Cf, min cs cf, hCs.trans_le (le_max_left _ _), lt_min hcs hcf, ?_⟩
      intro B hB v₀ R hR P T hv hsmall
      dsimp only
      intro ξ q hq
      have hq0 : q = ballEvolutionQuery P T := Subtype.ext hq
      rw [hq0]
      obtain ⟨Sf, Kf, hreal, hdom⟩ : ∃ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => 0))
          (K : MovingFiberKernel (wholeSpace d) (fun _ => 0)),
          RealizesTerminalEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ
            (zIndependentCoefficient B) (identityDrift d) S K ∧
          ∀ q : EvolutionQuery (PDE.euclideanBall v₀ R) (fun _ => 0),
            (localBallKernel hH hLE hd hlam hLam B hB v₀ hR).master q ≤
              K.master (wholeSpaceQuery q.1.1 q.1.2.1 q.2.1 q.1.2.2.1 q.1.2.2.2) := by
        obtain ⟨hBs, hBsym, hBell⟩ := sectionTwoCoefficient_fullBounds lam Lam B hB
        have hb := identityDrift_bounds d
        obtain ⟨S, K, hc, -, -, -, -, hi, -, -, -, -, he, hcomp, -, hmono, -⟩ :=
          exists_terminalEvolution_of_classical hLE hH d hd lam Lam 1 1 hlam hLam
            one_pos le_rfl (wholeSpace d) (fun _ => 0)
            (zIndependentCoefficient B) (identityDrift d) (wholeSpace_admissible d)
            (zeroCurve_piecewiseC1 d) hBs hBsym hBell (identityDrift_smooth d) hb.1 hb.2
        have hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ
            (zIndependentCoefficient B) (identityDrift d) S K := ⟨hc, hi, he, hcomp⟩
        refine ⟨S, K, hreal, ?_⟩
        have hsub : ∀ σ, movingDomain (PDE.euclideanBall v₀ R) (fun _ => 0) σ ⊆
            movingDomain (wholeSpace d) (fun _ => 0) σ := by
          intro σ
          simp only [movingDomain, PDE.translateSet_zero]
          exact subset_univ _
        have hdom := domainMonotone_of_realizes (zIndependentCoefficient B) (identityDrift d)
          K hmono (PDE.euclideanBall v₀ R) (fun _ => 0) (localBall_admissible v₀ hR)
          (zeroCurve_piecewiseC1 d) hsub (localBallEvolution hH hLE hd hlam hLam B hB v₀ hR).1
          (localBallKernel hH hLE hd hlam hLam B hB v₀ hR)
          (localBallEvolution_realizes hH hLE hd hlam hLam B hB v₀ hR)
        intro q
        exact hdom q
      let Kb := localBallKernel hH hLE hd hlam hLam B hB v₀ hR
      let qf := wholeSpaceQuery P.1.time T.1 T.2.le P.1.velocity P.1.position
      have hdef := killedFourier_variation_le_full_add_loss Kb Kf (ballEvolutionQuery P T)
        qf rfl (hdom (ballEvolutionQuery P T)) ξ
      have hf := hdecay B hB Sf Kf hreal P.1.time T.1 T.2
        P.1.velocity ξ P.1.position
      have hs := hloss B hB v₀ R hR P T hv hsmall
      let x := R ^ 2 / (T.1 - P.1.time)
      let y := (T.1 - P.1.time) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ)
      have hx : 0 ≤ x := div_nonneg (sq_nonneg R) (sub_pos.mpr T.2).le
      have hy : 0 ≤ y := mul_nonneg (sub_pos.mpr T.2).le
        (Real.rpow_nonneg (PDE.vecEuclideanNorm_nonneg ξ) _)
      have hs' : 1 - (Kb.master (ballEvolutionQuery P T)).real univ ≤
          Cs * Real.exp (-cs * x) := by
        change 1 - (Kb.master (ballEvolutionQuery P T)).real univ ≤
          Cs * Real.exp (-cs * R ^ 2 / (T.1 - P.1.time)) at hs
        have he : -cs * R ^ 2 / (T.1 - P.1.time) = -cs * x := by
          dsimp only [x]
          ring
        rwa [he] at hs
      have hf' : ((fourierProjection Kf qf ξ).variation univ).toReal ≤
          Cf * Real.exp (-cf * y) := by
        convert hf using 1
        congr 2
        dsimp only [y]
        ring
      calc
        _ ≤ ((fourierProjection Kf qf ξ).variation univ).toReal +
            (1 - (Kb.master (ballEvolutionQuery P T)).real univ) := by
          linarith only [hdef]
        _ ≤ Cs * Real.exp (-cs * x) + Cf * Real.exp (-cf * y) := by
          exact (add_le_add hf' hs').trans_eq (add_comm _ _)
        _ ≤ max Cs Cf * (Real.exp (-min cs cf * x) + Real.exp (-min cs cf * y)) :=
          ballExit_combine_exponentials hCs.le hCf.le hx hy
        _ = _ := by
          congr 2 <;> congr 1 <;> dsimp only [x, y] <;> ring
    let c := min cs ck
    refine ⟨Cs + Ck, c, add_pos hCs hCk, lt_min hcs hck, ?_⟩
    intro B hB v₀ R hR P T H hv hsmall ξ
    let x := R ^ 2 / (H.1 - P.1.time)
    let y := (H.1 - P.1.time) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ)
    have hh : 0 < H.1 - P.1.time := sub_pos.mpr H.2.1
    have hx := div_nonneg (sq_nonneg R) hh.le
    have hy : 0 ≤ y := mul_nonneg hh.le (Real.rpow_nonneg (PDE.vecEuclideanNorm_nonneg _) _)
    have hs := hloss B hB v₀ R hR P ⟨H.1, H.2.1⟩ hv hsmall
    have hk := hkilled B hB v₀ R hR P ⟨H.1, H.2.1⟩ hv hsmall ξ
      (ballEvolutionQuery P ⟨H.1, H.2.1⟩) rfl
    have es : -cs * R ^ 2 / (H.1 - P.1.time) = -cs * x := by dsimp only [x]; ring
    have ek : -ck * R ^ 2 / (H.1 - P.1.time) = -ck * x := by dsimp only [x]; ring
    have ey : -ck * (H.1 - P.1.time) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ) = -ck * y := by
      dsimp only [y]
      ring
    rw [es] at hs
    rw [ek, ey] at hk
    have hs' := hs.trans (mul_le_mul_of_nonneg_left
      (exitFourier_exp_rate (min_le_left cs ck) hx) hCs.le)
    have hk' := hk.trans (mul_le_mul_of_nonneg_left
      (add_le_add (exitFourier_exp_rate (min_le_right cs ck) hx)
        (exitFourier_exp_rate (min_le_right cs ck) hy)) hCk.le)
    have hb := (ballExit_fourier_short_strip_bound hH hLE hd hlam hLam B hB v₀ hR
      P T H ξ).trans (add_le_add hs' hk')
    have he := exitFourier_add_positive_bounds (B := Ck) (X := Real.exp (-c * x))
      hCs.le (Real.exp_pos (-c * y)).le
    have ee : -c * R ^ 2 / (H.1 - P.1.time) = -c * x := by dsimp only [x]; ring
    have ef : -c * (H.1 - P.1.time) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ) = -c * y := by
      dsimp only [y]
      ring
    rw [ee, ef]
    exact hb.trans he
  let c := c₀ / 16
  let A := 2 * C₀ + 1
  have hc : 0 < c := div_pos hc₀ (by norm_num)
  have hA : 1 ≤ A := by dsimp only [A]; linarith only [hC₀]
  have hec : 1 ≤ Real.exp c := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hc.le
  have hCf : 2 * C₀ ≤ A * Real.exp c := by
    calc
      2 * C₀ ≤ A := by dsimp only [A]; linarith
      _ ≤ A * Real.exp c := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hec (zero_le_one.trans hA)
  refine ⟨A * Real.exp c, c, mul_pos (zero_lt_one.trans_le hA) (Real.exp_pos _), hc, ?_⟩
  intro B hB v₀ R hR P T hv htime
  dsimp only
  intro ξ
  let n := PDE.vecEuclideanNorm ξ
  let y := (R ^ 3 * n) ^ (1 / 3 : ℝ)
  have hn := PDE.vecEuclideanNorm_nonneg ξ
  by_cases hhigh : 1 ≤ R ^ 3 * n
  · let h := R ^ 2 / (16 * y)
    have hopt :
        let y := (R ^ 3 * n) ^ (1 / 3 : ℝ)
            let h := R ^ 2 / (16 * y)
            1 ≤ y ∧ 0 < h ∧ h < R ^ 2 / 8 ∧
              R ^ 2 / h = 16 * y ∧ h * n ^ (2 / 3 : ℝ) = y / 16 := by
      let y := (R ^ 3 * n) ^ (1 / 3 : ℝ)
      have hy : 1 ≤ y := by
        simpa only [Real.one_rpow] using
          Real.rpow_le_rpow zero_le_one hhigh (by norm_num : 0 ≤ (1 / 3 : ℝ))
      have hyp := zero_lt_one.trans_le hy
      have hR2 := sq_pos_of_pos hR
      have hh : R ^ 2 / (16 * y) ≤ R ^ 2 / 16 := by
        apply div_le_div_of_nonneg_left hR2.le (by norm_num)
        nlinarith only [hy]
      refine ⟨hy, div_pos hR2 (mul_pos (by norm_num) hyp),
        hh.trans_lt (by linarith only [hR2]), ?_, ?_⟩
      · field_simp
      · have hs := exitFrequency_square hR.le hn
        change y ^ 2 = R ^ 2 * n ^ (2 / 3 : ℝ) at hs
        calc
          R ^ 2 / (16 * y) * n ^ (2 / 3 : ℝ) =
              (R ^ 2 * n ^ (2 / 3 : ℝ)) / (16 * y) := by ring
          _ = y ^ 2 / (16 * y) := by rw [← hs]
          _ = y / 16 := by field_simp
    change 1 ≤ y ∧ 0 < h ∧ h < R ^ 2 / 8 ∧
      R ^ 2 / h = 16 * y ∧ h * n ^ (2 / 3 : ℝ) = y / 16 at hopt
    obtain ⟨hy, hh, hmax, hfirst, hsecond⟩ := hopt
    let H : {t : ℝ // P.1.time < t ∧ t < T.1} :=
      ⟨P.1.time + h, by constructor <;> linarith only [hh, hmax, htime]⟩
    have hdiff : H.1 - P.1.time = h := by dsimp only [H]; ring
    have hb := htwo B hB v₀ R hR P T H hv
      (by rw [hdiff]; exact hmax.le) ξ
    rw [hdiff] at hb
    have he := exitFrequency_exponential_pair hC₀.le hc₀.le (zero_le_one.trans hy)
      hfirst hsecond
    exact (hb.trans he).trans
      (mul_le_mul_of_nonneg_right hCf (Real.exp_pos (-(c₀ / 16) * y)).le)
  · have hy : y ≤ 1 := by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow
        (mul_nonneg (pow_nonneg hR.le _) hn) (le_of_not_ge hhigh)
        (by norm_num : 0 ≤ (1 / 3 : ℝ))
    have hb := ENNReal.toReal_mono ENNReal.one_ne_top
      (ballExit_fourier_totalVariation_le_one hH hLE hd hlam hLam B hB v₀ hR P T ξ)
    simp only [ENNReal.toReal_one] at hb
    have _h_xinl_0 : 1 ≤ (A * Real.exp c) * Real.exp (-c * y) := by
      have hc := hc.le
      rw [mul_assoc, ← Real.exp_add]
      have hs : 0 ≤ c + -c * y := by
        have h := mul_nonneg hc (sub_nonneg.mpr hy)
        linarith only [h]
      calc
        1 ≤ Real.exp (c + -c * y) := by
          simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hs
        _ ≤ A * Real.exp (c + -c * y) := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
    exact hb.trans _h_xinl_0

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
