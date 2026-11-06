module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreStartBandVisits
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationStatement
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FarVelocityDensityDomination
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreStartBandScaling
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumReal
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionVisitMassesStatement
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GeometricCoreCoverSeries
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumFinite
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumPower
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumDiscrete
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumPartition
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Topology.Algebra.InfiniteSum.Order
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumGrid
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionVisitsStatement
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumKernel
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapCells
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapMixture
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapPartition
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapRestriction
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapSupport

/-! # The source core-start band estimate in an arbitrary observation velocity strip -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory
open scoped ENNReal
open Filter
open ProbabilityTheory
open scoped Classical

/- A literal bounded outer interval containing both closed velocity intervals. -/
def coreStartOuterInterval (H : Interval) (c : Clock) : Interval where
  lo := min H.lo c.activeInterval.lo - 1
  hi := max H.hi c.activeInterval.hi + 1
  ordered := by
    have hl := min_le_left H.lo c.activeInterval.lo
    have hh := le_max_left H.hi c.activeInterval.hi
    linarith [H.ordered]

/- The observation interval lies inside the chosen bounded outer interval. -/
theorem below_four_core_start_band (hpush : PushforwardStatement)
    (htail : RestartTailStatement) (hvisits : PositionVisitsStatement)
    (hmasses : PositionVisitMassesStatement) (hcore : CoreDominationStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam) (alpha q )
    (ha : enlargedAdmissibleAlpha lam Lam hlam hLam alpha) (hq : 1 < q ∧ q < 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (H : Interval) (s R : ℝ) (_hR : 0 < R)
      (e : StripPole H ((s + R ^ 2 : ℝ) : WithTop ℝ)),
      s ≤ e.1.time → e.1.velocity 0 ∈ closure c.entrance →
      |c.vbar| = 2 * c.r → c.r ≤ 6 * R →
      ∃ G : Point → ℝ, Measurable G ∧ (∀ z, 0 ≤ G z) ∧
        (stripGreen hH hLE hlam hLam A H (s + R ^ 2) e).restrict
          {z | z.velocity 0 ∈ c.core} =
            volume.withDensity (fun z => ENNReal.ofReal (G z)) ∧
        MemLp G (ENNReal.ofReal q) volume ∧
        (eLpNorm G (ENNReal.ofReal q) volume).toReal ≤
          (C * R ^ (6 - 4 * q) *
            (c.r / R) ^ (4 - 3 * q + (1 - alpha) * (q - 1))) ^ (1 / q) := by
  obtain ⟨C, hC, hd⟩ : ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (J : Interval) (R T : ℝ) (P : Point),
      0 < R → 0 < T → T ≤ R ^ 2 → |c.vbar| = 2 * c.r → c.r ≤ 6 * R →
      closure c.active ⊆ J.carrier → P.velocity 0 ∈ closure c.entrance →
      ∃ G : Point → ℝ, Measurable G ∧ (∀ z, 0 ≤ G z) ∧
        enlargedActiveGreen hH hLE hlam hLam A c
          (visitsFromZero hH hLE hlam hLam A c J T P) =
            volume.withDensity (fun z => ENNReal.ofReal (G z)) ∧
        MemLp G (ENNReal.ofReal q) volume ∧
        (eLpNorm G (ENNReal.ofReal q) volume).toReal ≤
          (C * R ^ (6 - 4 * q) *
            (c.r / R) ^ (4 - 3 * q + (1 - alpha) * (q - 1))) ^ (1 / q) := by
    obtain ⟨Cd, hCd, hd⟩ : ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
      (c : Clock) (_hc : |c.vbar| = 2 * c.r) (s x : ℝ)
      (nu : Measure Point) [IsFiniteMeasure nu],
      (∀ᵐ e ∂nu, s ≤ e.time ∧ e.velocity 0 ∈ c.active) →
      ∃ G : Point → ℝ, Measurable G ∧ (∀ z, 0 ≤ G z) ∧
        enlargedActiveGreen hH hLE hlam hLam A c nu =
          volume.withDensity (fun z => ENNReal.ofReal (G z)) ∧
        MemLp G (ENNReal.ofReal q) volume ∧
        (∫⁻ z, ‖G z‖ₑ ^ q ∂volume) ≤ ENNReal.ofReal (C * c.r ^ (6 - 4 * q)) *
          ∑' a : ℕ × ℤ, nu (enlargedStartCell c s x a.1 a.2) ^ q := by
      obtain ⟨C, hC, hd⟩ : ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
      (c : Clock) (_hc : |c.vbar| = 2 * c.r) (s x : ℝ)
      (nu : Measure Point) [IsFiniteMeasure nu],
      (∀ᵐ e ∂nu, s ≤ e.time ∧ e.velocity 0 ∈ c.active) →
      (∫⁻ z, positionMixtureDensity hH hLE hlam hLam A c nu z ^ q ∂volume) ≤
        ENNReal.ofReal (C * c.r ^ (6 - 4 * q)) *
          ∑' a : ℕ × ℤ, nu (enlargedStartCell c s x a.1 a.2) ^ q := by
        obtain ⟨C, c₀, hC, hc₀, hd⟩ : ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (_hc : |c.vbar| = 2 * c.r) (s x : ℝ) (nu : Measure Point) [IsFiniteMeasure nu], (∀ᵐ e ∂nu, s ≤ e.time ∧ e.velocity 0 ∈ c.active) → ∀ (i : ℕ) (ell : ℤ), positionPositiveNorm (volume.restrict (enlargedOutputCell c s x i ell)) q (positionMixtureDensity hH hLE hlam hLam A c nu) ≤ ENNReal.ofReal (C * c.r ^ (6 / q - 4)) * ∑' a : ℕ × ℤ, positionOverlapWeight c₀ i a.1 ell a.2 * nu (enlargedStartCell c s x a.1 a.2) := by
          have : SigmaFinite (volume : Measure Point) := density_volume_sigmaFinite
          obtain ⟨C, c₀, hC, hc₀, hd⟩ : ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧ ∀ (A : SmoothAutonomous lam Lam)
              (c : Clock) (_hc : |c.vbar| = 2 * c.r) (s x : ℝ)
              (nu : Measure Point) [IsFiniteMeasure nu],
              (∀ᵐ e ∂nu, e.velocity 0 ∈ c.active) →
              ∀ (i j : ℕ) (ell k : ℤ),
              positionPositiveNorm (volume.restrict (enlargedOutputCell c s x i ell)) q
                (positionMixtureDensity hH hLE hlam hLam A c
                  (nu.restrict (enlargedStartCell c s x j k))) ≤
                ENNReal.ofReal (C * c.r ^ (6 / q - 4)) *
                  positionOverlapWeight c₀ i j ell k * nu (enlargedStartCell c s x j k) := by
              have : SigmaFinite (volume : Measure Point) := density_volume_sigmaFinite
              obtain ⟨C, c₀, hC, hc₀, hd⟩ := positionActiveDensity_tail hpush htail hH hLE hlam hLam q hq
              refine ⟨C, c₀, hC, hc₀, ?_⟩
              intro A c hc s x nu hfinite hnu i j ell k
              let E := enlargedOutputCell c s x i ell
              let B := enlargedStartCell c s x j k
              let F := positionActiveDensity hH hLE hlam hLam A c
              have hF := measurable_positionActiveDensity hH hLE hlam hLam A c
              have hq0 : 0 < q := by linarith [hq.1]
              by_cases hover : j ≤ i ∧ |((ell - k : ℤ) : ℝ)| ≤ 5 * ((i : ℝ) - (j : ℝ) + 1)
              · let K := ENNReal.ofReal (C * Real.exp (-c₀ * positionOverlapDelay i j) *
                  c.r ^ (6 / q - 4))
                have hpole : ∀ᵐ e ∂nu.restrict B, positionPositiveNorm (volume.restrict E) q (F e) ≤ K := by
                  filter_upwards [ae_restrict_of_ae hnu,
                    ae_restrict_mem (measurableSet_enlargedStartCell c s x j k)] with e hv he
                  have hdelay : 0 ≤ positionOverlapDelay i j * c.r ^ 2 :=
                    mul_nonneg (le_max_right _ _) (sq_nonneg _)
                  have h := hd A c e hv (positionOverlapDelay i j * c.r ^ 2) hdelay
                  have hexp : -c₀ * (positionOverlapDelay i j * c.r ^ 2) / c.r ^ 2 =
                      -c₀ * positionOverlapDelay i j := by field_simp [c.positive.ne']
                  rw [hexp] at h
                  apply LE.le.trans _ h
                  apply positionPositiveNorm_restrict_le volume _ q hq0 _ _
                    (measurableSet_enlargedOutputCell c s x i ell)
                    ((isClosed_le continuous_const continuous_time).measurableSet.inter
                      (isOpen_Ioo.measurableSet.preimage
                        ((continuous_apply 0).comp continuous_velocity).measurable))
                  filter_upwards [positionActiveDensity_support hpush hH hLE hlam hLam A c hc e hv]
                    with z hz hcell hnonzero
                  have hs := hz hnonzero
                  have _h_xinl_0 : e.time + positionOverlapDelay i j * c.r ^ 2 ≤ z.time := by
                    have hz := hcell.1
                    have ht := hs.1
                    unfold positionOverlapDelay
                    by_cases h : 0 ≤ (i : ℝ) - (j : ℝ) - 1
                    · rw [max_eq_left h]
                      have heup := (enlargedTimeBin_bounds c.r s e.time j he.1).2
                      nlinarith only [heup, ((enlargedTimeBin_bounds c.r s z.time i hz.1).1)]
                    · rw [max_eq_right (le_of_not_ge h), zero_mul, add_zero]
                      exact ht.le
                  exact ⟨_h_xinl_0, hs.2.1⟩
                have hn := positionPositiveNorm_mixture_le (nu.restrict B) (volume.restrict E)
                  F hF q hq.1 K hpole
                change positionPositiveNorm (volume.restrict E) q
                  (positionMixtureDensity hH hLE hlam hLam A c (nu.restrict B)) ≤
                    (nu.restrict B) univ * K at hn
                apply hn.trans_eq
                rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
                unfold K positionOverlapWeight
                rw [ite_eq_left hover]
                rw [show C * Real.exp (-c₀ * positionOverlapDelay i j) * c.r ^ (6 / q - 4) =
                  (C * c.r ^ (6 / q - 4)) * Real.exp (-c₀ * positionOverlapDelay i j) by ring,
                  ENNReal.ofReal_mul (mul_nonneg hC.le (Real.rpow_nonneg c.positive.le _))]
                exact mul_comm _ _
              · have hpole : ∀ᵐ e ∂nu.restrict B, positionPositiveNorm (volume.restrict E) q (F e) ≤ 0 := by
                  filter_upwards [ae_restrict_of_ae hnu,
                    ae_restrict_mem (measurableSet_enlargedStartCell c s x j k)] with e hv he
                  have hz : ∀ᵐ z ∂volume.restrict (enlargedOutputCell c s x i ell),
              positionActiveDensity hH hLE hlam hLam A c e z = 0 := by
                    filter_upwards [ae_restrict_of_ae
                      (positionActiveDensity_support hpush hH hLE hlam hLam A c hc e hv),
                      ae_restrict_mem (measurableSet_enlargedOutputCell c s x i ell)] with z hz hcell
                    by_contra hnonzero
                    have hs := hz hnonzero
                    apply hover
                    have _h_xinl_0 : |((ell - k : ℤ) : ℝ)| ≤ 5 * ((i : ℝ) - (j : ℝ) + 1) := by
                      have hz := hcell.1
                      have ht := hs.1
                      have hcone := hs.2.2
                      have hji := positionOverlap_time_index c s x j i k ell e z he hz ht
                      have hcast : (j : ℝ) ≤ (i : ℝ) := by exact_mod_cast hji
                      have hd : 1 ≤ (i : ℝ) - (j : ℝ) + 1 := by linarith only [hcast]
                      have hdt : z.time - e.time ≤ ((i : ℝ) - (j : ℝ) + 1) * c.r ^ 2 := by
                          have helo := (enlargedTimeBin_bounds c.r s e.time j he.1).1
                          have hzup := (enlargedTimeBin_bounds c.r s z.time i hz.1).2
                          linarith only [helo, hzup]


                      have hs : |z.position 0 - e.position 0| ≤
                          3 * ((i : ℝ) - (j : ℝ) + 1) * c.r ^ 3 := by
                        apply hcone.trans
                        calc
                          _ ≤ 3 * c.r * (((i : ℝ) - (j : ℝ) + 1) * c.r ^ 2) :=
                            mul_le_mul_of_nonneg_left hdt (by linarith [c.positive])
                          _ = _ := by ring
                      have hep := he.2
                      have hzp := hz.2
                      change x + (k : ℝ) * c.r ^ 3 ≤ e.position 0 ∧
                        e.position 0 < x + ((k : ℝ) + 1) * c.r ^ 3 at hep
                      change x + (ell : ℝ) * c.r ^ 3 ≤ z.position 0 ∧
                        z.position 0 < x + ((ell : ℝ) + 1) * c.r ^ 3 at hzp
                      have hplus := le_abs_self (z.position 0 - e.position 0)
                      have hminus := neg_le_abs (z.position 0 - e.position 0)
                      have hr3 := pow_pos c.positive 3
                      have hleft : ((ell : ℝ) - (k : ℝ)) * c.r ^ 3 ≤
                          (3 * ((i : ℝ) - (j : ℝ) + 1) + 1) * c.r ^ 3 := by
                        nlinarith only [hep.2, hzp.1, hs, hplus]
                      have hright : -((ell : ℝ) - (k : ℝ)) * c.r ^ 3 ≤
                          (3 * ((i : ℝ) - (j : ℝ) + 1) + 1) * c.r ^ 3 := by
                        nlinarith only [hep.1, hzp.2, hs, hminus]
                      have hl := (mul_le_mul_iff_left₀ hr3).mp hleft
                      have hr := (mul_le_mul_iff_left₀ hr3).mp hright
                      rw [Int.cast_sub, abs_le]
                      constructor <;> linarith only [hl, hr, hd]
                    exact ⟨positionOverlap_time_index c s x j i k ell e z he hcell.1 hs.1,
                      _h_xinl_0⟩
                  unfold positionPositiveNorm
                  have hi : (∫⁻ z, F e z ^ q ∂volume.restrict E) = 0 := by
                    rw [← lintegral_zero]
                    apply lintegral_congr_ae
                    filter_upwards [hz] with z hz
                    simp only [F, hz, ENNReal.zero_rpow_of_pos hq0]
                  rw [hi, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hq0)]
                have hn := positionPositiveNorm_mixture_le (nu.restrict B) (volume.restrict E)
                  F hF q hq.1 0 hpole
                change positionPositiveNorm (volume.restrict E) q
                  (positionMixtureDensity hH hLE hlam hLam A c (nu.restrict B)) ≤
                    (nu.restrict B) univ * 0 at hn
                simpa only [positionOverlapWeight, ite_eq_right hover, mul_zero, zero_mul] using hn


          refine ⟨C, c₀, hC, hc₀, ?_⟩
          intro A c hc s x nu hfinite hnu i ell
          have ht := hnu.mono (fun _ h => h.1)
          have hv := hnu.mono (fun _ h => h.2)
          have _h_xinl_0 : positionMixtureDensity hH hLE hlam hLam A c nu =
              fun z => ∑' a : ℕ × ℤ, positionMixtureDensity hH hLE hlam hLam A c
                (nu.restrict (enlargedStartCell c s x a.1 a.2)) z := by
            calc
              _ = positionMixtureDensity hH hLE hlam hLam A c
                  (Measure.sum (fun a : ℕ × ℤ => nu.restrict
                    (enlargedStartCell c s x a.1 a.2))) :=
                congrArg (positionMixtureDensity hH hLE hlam hLam A c)
                  (enlargedStartCell_measure_sum nu c s x ht)
              _ = _ := by
                funext z
                exact lintegral_sum_measure _ _
          rw [_h_xinl_0]
          apply (positionPositiveNorm_tsum (volume.restrict (enlargedOutputCell c s x i ell))
            q hq.1.le
            (fun a : ℕ × ℤ => positionMixtureDensity hH hLE hlam hLam A c
              (nu.restrict (enlargedStartCell c s x a.1 a.2)))
            (fun a : ℕ × ℤ => measurable_positionMixtureDensity hH hLE hlam hLam A c
              (nu.restrict (enlargedStartCell c s x a.1 a.2)))).trans
          calc
            _ ≤ ∑' a : ℕ × ℤ, ENNReal.ofReal (C * c.r ^ (6 / q - 4)) *
                positionOverlapWeight c₀ i a.1 ell a.2 * nu (enlargedStartCell c s x a.1 a.2) :=
              ENNReal.tsum_le_tsum (fun a => hd A c hc s x nu hv i a.1 ell a.2)
            _ = _ := by simp_rw [mul_assoc]; rw [ENNReal.tsum_mul_left]
        let W := ∑' h, positionYoungKernel (c₀ / 12) h
        have hs := positionYoungKernel_summable (c₀ / 12) (by linarith)
        have hw (h : ℤ × ℤ) : 0 ≤ positionYoungKernel (c₀ / 12) h :=
          mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
        have hW : 0 < W := hs.tsum_pos (fun _ => hw _) (0, 0) (by
          exact mul_pos (Real.exp_pos _) (Real.exp_pos _))
        have hWe : (∑' h, ENNReal.ofReal (positionYoungKernel (c₀ / 12) h)) =
            ENNReal.ofReal W := (ENNReal.ofReal_tsum_of_nonneg hw hs).symm
        let D := C * Real.exp (2 * c₀) * W
        have hD : 0 < D := mul_pos (mul_pos hC (Real.exp_pos _)) hW
        refine ⟨D ^ q, Real.rpow_pos_of_pos hD q, ?_⟩
        intro A c hc s x nu hfinite hnu
        have hq0 : 0 < q := by linarith [hq.1]
        have _h_xinl_1 : (∫⁻ z, positionMixtureDensity hH hLE hlam hLam A c nu z ^ q ∂volume) =
            ∑' a : ℕ × ℤ,
              positionPositiveNorm (volume.restrict (enlargedOutputCell c s x a.1 a.2)) q
                (positionMixtureDensity hH hLE hlam hLam A c nu) ^ q := by
          let F := positionMixtureDensity hH hLE hlam hLam A c nu
          let U := {z : Point | s ≤ z.time ∧ z.velocity 0 ∈ c.active}
          have hU : MeasurableSet U := (measurableSet_Ici.preimage continuous_time.measurable).inter
            (isOpen_Ioo.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable)
          have he : (∫⁻ z, F z ^ q ∂volume) = ∫⁻ z in U, F z ^ q ∂volume := by
            rw [← lintegral_indicator hU]
            apply lintegral_congr_ae
            have _h_inl_11 : ∀ᵐ z ∂(volume : Measure Point),
              positionMixtureDensity hH hLE hlam hLam A c nu z ≠ 0 →
                s ≤ z.time ∧ z.velocity 0 ∈ c.active := by
                have hm := measurable_positionMixtureDensity hH hLE hlam hLam A c nu
                apply (ae_withDensity_iff hm).mp
                rw [withDensity_positionMixtureDensity hpush hH hLE hlam hLam]
                have hS : MeasurableSet {z : Point | s ≤ z.time ∧ z.velocity 0 ∈ c.active} :=
                  (measurableSet_Ici.preimage continuous_time.measurable).inter
                    (isOpen_Ioo.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable)
                apply Measure.ae_comp_of_ae_ae hS
                filter_upwards [hnu] with e he
                rw [← withDensity_positionActiveDensity hpush hH hLE hlam hLam]
                apply (ae_withDensity_iff ((measurable_positionActiveDensity hH hLE hlam hLam A c).comp
                  (measurable_const.prodMk measurable_id))).mpr
                filter_upwards [positionActiveDensity_support hpush hH hLE hlam hLam A c hc e he.2]
                  with z hz hnonzero
                exact ⟨he.1.trans (hz hnonzero).1.le, (hz hnonzero).2.1⟩

              /- Summing output-cell q-power norms recovers the full density power integral. -/
            filter_upwards [_h_inl_11]
              with z hz
            by_cases h : z ∈ U
            · simp only [indicator_of_mem h]
            · have hf : F z = 0 := by by_contra hn; exact h (hz hn)
              simp only [indicator_of_notMem h, hf, ENNReal.zero_rpow_of_pos hq0]
          rw [he]
          dsimp only [U]
          have _h_inl_9 : (⋃ a : ℕ × ℤ, enlargedOutputCell c s x a.1 a.2) =
              {p | s ≤ p.time ∧ p.velocity 0 ∈ c.active} := by
              unfold enlargedOutputCell
              rw [← iUnion_inter, enlargedStartCell_iUnion]
              rfl

            /- The output-cell partition is pairwise disjoint. -/
          have _h_xinl_0 : Pairwise (fun a b : ℕ × ℤ => Disjoint (enlargedOutputCell c s x a.1 a.2) (enlargedOutputCell c s x b.1 b.2)) := by
            intro a b hab
            exact (enlargedStartCell_pairwiseDisjoint c s x hab).mono inter_subset_left inter_subset_left
          rw [← _h_inl_9,
            lintegral_iUnion (fun a : ℕ × ℤ => measurableSet_enlargedOutputCell c s x a.1 a.2)
              _h_xinl_0]
          apply tsum_congr
          intro a
          exact (positionPositiveNorm_rpow _ q hq0 F).symm
        rw [_h_xinl_1]
        calc
          _ ≤ ∑' b : ℕ × ℤ, (ENNReal.ofReal (C * c.r ^ (6 / q - 4)) *
              ∑' a : ℕ × ℤ, positionOverlapWeight c₀ b.1 a.1 b.2 a.2 *
                nu (enlargedStartCell c s x a.1 a.2)) ^ q :=
            ENNReal.tsum_le_tsum (fun b => ENNReal.rpow_le_rpow
              (hd A c hc s x nu hnu b.1 b.2) hq0.le)
          _ = ENNReal.ofReal (C * c.r ^ (6 / q - 4)) ^ q *
              ∑' b : ℕ × ℤ, (∑' a : ℕ × ℤ, positionOverlapWeight c₀ b.1 a.1 b.2 a.2 *
                nu (enlargedStartCell c s x a.1 a.2)) ^ q := by
            simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
            rw [ENNReal.tsum_mul_left]
          _ ≤ ENNReal.ofReal (C * c.r ^ (6 / q - 4)) ^ q *
              ((ENNReal.ofReal (Real.exp (2 * c₀)) * ENNReal.ofReal W) ^ q *
                ∑' a : ℕ × ℤ, nu (enlargedStartCell c s x a.1 a.2) ^ q) := by
            rw [← hWe]
            have _h_xinl_0 : (∑' b : ℕ × ℤ, (∑' a : ℕ × ℤ,
      positionOverlapWeight c₀ b.1 a.1 b.2 a.2 *
        nu (enlargedStartCell c s x a.1 a.2)) ^ q) ≤
      (ENNReal.ofReal (Real.exp (2 * c₀)) *
        ∑' h, ENNReal.ofReal (positionYoungKernel (c₀ / 12) h)) ^ q *
      ∑' a : ℕ × ℤ, nu (enlargedStartCell c s x a.1 a.2) ^ q := by
              have hq := hq.1
              let w := fun h => ENNReal.ofReal (positionYoungKernel (c₀ / 12) h)
              let a := positionMassSequence nu c s x
              let D := ENNReal.ofReal (Real.exp (2 * c₀))
              have hcell (b : ℕ × ℤ) : (∑' z : ℕ × ℤ,
                  positionOverlapWeight c₀ b.1 z.1 b.2 z.2 *
                    nu (enlargedStartCell c s x z.1 z.2)) ≤
                  D * ∑' h, w (positionIndexEmbedding b - h) * a h := by
                calc
                  _ ≤ ∑' z : ℕ × ℤ, D * w (positionIndexEmbedding b - positionIndexEmbedding z) *
                      a (positionIndexEmbedding z) := by
                    apply ENNReal.tsum_le_tsum
                    intro z
                    change _ ≤ D * w (positionIndexEmbedding b - positionIndexEmbedding z) *
                      positionMassSequence nu c s x (positionIndexEmbedding z)
                    rw [positionMassSequence_embed]
                    exact mul_le_mul_left (positionOverlapWeight_le c₀ hc₀ b.1 z.1 b.2 z.2) _
                  _ = D * ∑' z : ℕ × ℤ,
                      w (positionIndexEmbedding b - positionIndexEmbedding z) *
                        a (positionIndexEmbedding z) := by
                    simp_rw [mul_assoc]
                    rw [ENNReal.tsum_mul_left]
                  _ ≤ _ := mul_le_mul_right (ENNReal.tsum_comp_le_tsum_of_injective
                    positionIndexEmbedding_injective
                    (fun h => w (positionIndexEmbedding b - h) * a h)) D
              calc
                _ ≤ ∑' b : ℕ × ℤ, (D * ∑' h, w (positionIndexEmbedding b - h) * a h) ^ q :=
                  ENNReal.tsum_le_tsum (fun b => ENNReal.rpow_le_rpow (hcell b) (by linarith))
                _ = D ^ q * ∑' b : ℕ × ℤ,
                    (∑' h, w (positionIndexEmbedding b - h) * a h) ^ q := by
                  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ q)]
                  rw [ENNReal.tsum_mul_left]
                _ ≤ D ^ q * ∑' g, (∑' h, w (g - h) * a h) ^ q :=
                  mul_le_mul_right (ENNReal.tsum_comp_le_tsum_of_injective
                    positionIndexEmbedding_injective (fun g => (∑' h, w (g - h) * a h) ^ q)) _
                _ ≤ D ^ q * ((∑' h, w h) ^ q * ∑' g, a g ^ q) :=
                  mul_le_mul_right (position_two_index_young_source w a q hq) _
                _ = _ := by
                  have _h_xinl_0 : (∑' a : ℤ × ℤ, positionMassSequence nu c s x a ^ q) = ∑' a : ℕ × ℤ, nu (enlargedStartCell c s x a.1 a.2) ^ q := by
                    have hq : 0 < q := by
                      linarith
                    rw [ENNReal.tsum_prod', ENNReal.tsum_prod',
                      tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable]
                    have hpos : (∑' n : ℕ, ∑' k : ℤ, positionMassSequence nu c s x ((n : ℤ), k) ^ q) =
                        ∑' n : ℕ, ∑' k : ℤ, nu (enlargedStartCell c s x n k) ^ q := by
                      simp only [positionMassSequence, Int.natCast_nonneg, ite_true, Int.toNat_natCast]
                    have hneg : (∑' n : ℕ, ∑' k : ℤ,
                        positionMassSequence nu c s x (-((n : ℤ) + 1), k) ^ q) = 0 := by
                      have hn (n : ℕ) : ¬(0 ≤ -((n : ℤ) + 1)) := by omega
                      simp only [positionMassSequence, hn, ite_false, ENNReal.zero_rpow_of_pos hq, tsum_zero]
                    rw [hpos, hneg, add_zero]
                  rw [← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ q),
                    _h_xinl_0]
            exact mul_le_mul_right _h_xinl_0 _
          _ = _ := by
            rw [← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ hq0.le,
              ← ENNReal.ofReal_mul (Real.exp_pos _).le,
              ← ENNReal.ofReal_mul (mul_nonneg hC.le (Real.rpow_nonneg c.positive.le _)),
              ENNReal.ofReal_rpow_of_pos
                (mul_pos (mul_pos hC (Real.rpow_pos_of_pos c.positive _))
                  (mul_pos (Real.exp_pos _) hW))]
            congr 2
            have hbase : C * c.r ^ (6 / q - 4) * (Real.exp (2 * c₀) * W) =
                D * c.r ^ (6 / q - 4) := by dsimp [D]; ring
            rw [hbase, Real.mul_rpow hD.le (Real.rpow_nonneg c.positive.le _),
              ← Real.rpow_mul c.positive.le]
            congr 2
            field_simp
      refine ⟨C, hC, ?_⟩
      intro A c hc s x nu hfinite hnu
      have hq0 : 0 < q := by linarith [hq.1]
      let F := positionMixtureDensity hH hLE hlam hLam A c nu
      have hF := measurable_positionMixtureDensity hH hLE hlam hLam A c nu
      have hm := withDensity_positionMixtureDensity hpush hH hLE hlam hLam A c nu
      have : IsFiniteMeasure (enlargedActiveGreen hH hLE hlam hLam A c nu) := by
        unfold enlargedActiveGreen
        infer_instance
      obtain ⟨hG, hG0, hGd, hGi⟩ := position_density_real volume
        (enlargedActiveGreen hH hLE hlam hLam A c nu) F hF hm q
      have hbound := hd A c hc s x nu hnu
      have hsum := enlargedStartCell_power_sum_le nu c s x q hq.1.le
        (hnu.mono (fun _ h => h.1))
      have hsumfinite : (∑' a : ℕ × ℤ, nu (enlargedStartCell c s x a.1 a.2) ^ q) < ⊤ :=
        hsum.trans_lt (ENNReal.rpow_lt_top_of_nonneg (by linarith [hq.1]) (measure_ne_top _ _))
      have hi : (∫⁻ z, ‖(F z).toReal‖ₑ ^ q ∂volume) < ⊤ := by
        rw [hGi]
        exact hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsumfinite)
      refine ⟨fun z => (F z).toReal, hG, hG0, hGd, ?_, ?_⟩
      · change eLpNorm (fun z => (F z).toReal) (ENNReal.ofReal q) volume < ⊤
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal 
          (ne_of_gt (ENNReal.ofReal_pos.mpr hq0)) ENNReal.ofReal_ne_top
          hG.aestronglyMeasurable, ENNReal.toReal_ofReal (by linarith : 0 ≤ q)]
        exact ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr hq0.le) hi.ne
      · rwa [hGi]
    obtain ⟨Cv, hCv, hv⟩ := (hvisits hH hLE lam Lam hlam hLam alpha ha).2 q hq
    obtain ⟨Cm, _, hm⟩ := hmasses hH hLE lam Lam hlam hLam
    let eta := 1 - (2 - alpha) * (q - 1)
    have hb := bellmanAdjointExponent_range (Lam / lam) ((le_div_iff₀ hlam).2
      (by simpa only [one_mul] using hLam))
    have ha0 : 0 < alpha := by dsimp [enlargedAdmissibleAlpha] at ha; linarith [ha.1, hb.1]
    have heta : 0 ≤ eta := by dsimp [eta]; nlinarith [hq.1, hq.2, ha.2]
    let C := Cd * Cv * 7 ^ eta
    have hC : 0 < C := mul_pos (mul_pos hCd hCv) (Real.rpow_pos_of_pos (by norm_num) _)
    refine ⟨C, hC, ?_⟩
    intro A c J R T P hR hT hTR hc hr hJ hvel
    let nu := visitsFromZero hH hLE hlam hLam A c J T P
    have hp := hm A c J R T P hR hT hTR hc hJ hvel
    have : IsFiniteMeasure nu := hp.1
    have hnu : ∀ᵐ p ∂nu, P.time ≤ p.time ∧ p.velocity 0 ∈ c.active :=
      hp.2.1.mono (fun _ h => ⟨h.1, enlargedEntrance_subset_active c h.2.2⟩)
    obtain ⟨G, hG, hG0, hGd, hGp, hGi⟩ := hd A c hc P.time 0 nu hnu
    have hsum := hv A c J R T P hR hT hTR hc hJ hvel
    rw [enlargedVisit_power_sum_eq nu c P.time q (by linarith) (hp.2.1.mono (fun _ h => h.2.2))]
      at hGi
    have hscale := coreStartBand_scaling c.r R (6 - 4 * q) eta c.positive hR heta hr
    have _h_xinl_0 : (6 - 4 * q) - (1 - (2 - alpha) * (q - 1)) = 4 - 3 * q + (1 - alpha) * (q - 1) := by
      ring
    rw [_h_xinl_0] at hscale
    let K := C * R ^ (6 - 4 * q) * (c.r / R) ^
      (4 - 3 * q + (1 - alpha) * (q - 1))
    have hK : 0 ≤ K :=
      mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hR.le _))
        (Real.rpow_nonneg (div_pos c.positive hR).le _)
    have hi : (∫⁻ z, ‖G z‖ₑ ^ q ∂volume) ≤ ENNReal.ofReal K := by
      apply hGi.trans
      apply (mul_le_mul_right hsum _).trans
      rw [← ENNReal.ofReal_mul (mul_nonneg hCd.le (Real.rpow_nonneg c.positive.le _))]
      apply ENNReal.ofReal_le_ofReal
      have he : Cd * c.r ^ (6 - 4 * q) * (Cv * (1 + R / c.r) ^ eta) =
          (Cd * Cv) * (c.r ^ (6 - 4 * q) * (1 + R / c.r) ^ eta) := by ring
      rw [he]
      exact (mul_le_mul_of_nonneg_left hscale (mul_nonneg hCd.le hCv.le)).trans_eq
        (by dsimp [K, C]; ring)
    obtain ⟨_, hnorm⟩ := density_norm_of_power_bound volume G hG q K (by linarith) hK hi
    exact ⟨G, hG, hG0, hGd, hGp, hnorm⟩
  refine ⟨C, hC, ?_⟩
  intro A c H s R hR e hs he hc hr
  let J := coreStartOuterInterval H c
  let T := s + R ^ 2 - e.1.time
  have ht : 0 < T := sub_pos.mpr (WithTop.coe_lt_coe.mp e.2.1)
  have htR : T ≤ R ^ 2 := by dsimp [T]; linarith
  have hJ : closure c.active ⊆ (coreStartOuterInterval H c).carrier := by
      change closure (Ioo c.activeInterval.lo c.activeInterval.hi) ⊆ _
      rw [closure_Ioo c.activeInterval.ordered.ne]
      intro v hv
      change min H.lo c.activeInterval.lo - 1 < v ∧ v < max H.hi c.activeInterval.hi + 1
      constructor
      · linarith [hv.1, min_le_right H.lo c.activeInterval.lo]
      · linarith [hv.2, le_max_right H.hi c.activeInterval.hi]

    /- The improved core-start norm is uniform in all positions and starting times in the strip. -/
  obtain ⟨G, hG, hG0, hGd, hGp, hGn⟩ := hd A c J R T e.1 hR ht htR hc hr hJ he
  have hsub : H.carrier ⊆ (coreStartOuterInterval H c).carrier := by
      intro v hv
      change min H.lo c.activeInterval.lo - 1 < v ∧ v < max H.hi c.activeInterval.hi + 1
      constructor
      · linarith [hv.1, min_le_left H.lo c.activeInterval.lo]
      · linarith [hv.2, le_max_left H.hi c.activeInterval.hi]

    /- The closed active interval lies strictly inside the chosen bounded outer interval. -/
  let ep := stripEnlargePole H J hsub (s + R ^ 2) (s + R ^ 2) le_rfl e
  have hh := hcore hH hLE lam Lam hlam hLam A c J e.1.time (s + R ^ 2) e.1
    ⟨WithTop.coe_lt_coe.mp e.2.1, hsub e.2.2⟩ hc hJ le_rfl
  have heq : e.1.time + T = s + R ^ 2 := by dsimp [T]; ring
  have hnu : visitsFromZero hH hLE hlam hLam A c J T e.1 =
      enlargedVisitStarts hH hLE hlam hLam A c J e.1.time (s + R ^ 2) e.1 := by
    unfold visitsFromZero
    rw [heq]
  rw [hnu] at hGd
  have hdle := ((Measure.restrict_mono_measure (stripGreen_mono hH hLE hlam hLam A H J hsub (s + R ^ 2) (s + R ^ 2) le_rfl e) {z | z.velocity 0 ∈ c.core}).trans hh.2).trans Measure.restrict_le_self
  rw [hGd] at hdle
  have : SigmaFinite (volume : Measure Point) := density_volume_sigmaFinite
  obtain ⟨g, hgm, hg0, hgd, hgp, hgn⟩ := density_of_le_withDensity volume
    ((stripGreen hH hLE hlam hLam A H (s + R ^ 2) e).restrict
      {z | z.velocity 0 ∈ c.core}) G hG hG0 (ENNReal.ofReal q) hGp hdle
  exact ⟨g, hgm, hg0, hgd, hgp,
    (ENNReal.toReal_mono hGp.ne hgn).trans hGn⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
