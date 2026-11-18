module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapMixture
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapCells

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter
open scoped ENNReal

/-- A chosen positive density has no greater norm than any nonnegative representative. -/
theorem positionPositiveNorm_of_density_le {X : Type*} [MeasurableSpace X]
    (m : Measure X) [SigmaFinite m] (F : X → ℝ≥0∞) (hF : Measurable F)
    (S E : Set X) (hS : MeasurableSet S) (G : X → ℝ)
    (hG : Measurable G) (hG0 : ∀ x, 0 ≤ G x)
    (hd : m.withDensity F = (m.restrict S).withDensity (fun x => ENNReal.ofReal (G x)))
    (q K : ℝ) (hq : 0 < q) (hK : 0 ≤ K)
    (hp : MemLp G (ENNReal.ofReal q) (m.restrict E))
    (hn : (eLpNorm G (ENNReal.ofReal q) (m.restrict E)).toReal ≤ K) :
    positionPositiveNorm (m.restrict E) q F ≤ ENNReal.ofReal K := by
  have heq : m.withDensity F =
      m.withDensity (S.indicator (fun x => ENNReal.ofReal (G x))) := by
    rwa [withDensity_indicator hS]
  have he := (withDensity_eq_iff_of_sigmaFinite hF.aemeasurable
    (hG.ennreal_ofReal.indicator hS).aemeasurable).mp heq
  have hle : ∀ᵐ x ∂m.restrict E, F x ≤ ENNReal.ofReal (G x) := by
    filter_upwards [ae_restrict_of_ae he] with x hx
    rw [hx]
    by_cases hxS : x ∈ S
    · rw [indicator_of_mem hxS]
    · rw [indicator_of_notMem hxS]
      exact zero_le
  have hnorm : positionPositiveNorm (m.restrict E) q F ≤
      eLpNorm G (ENNReal.ofReal q) (m.restrict E) := by
    rw [eLpNorm_eq_eLpNorm' (by positivity) ENNReal.ofReal_ne_top
      hp.aestronglyMeasurable, ENNReal.toReal_ofReal hq.le,
      eLpNorm'_eq_lintegral_enorm]
    unfold positionPositiveNorm
    apply ENNReal.rpow_le_rpow _ (one_div_nonneg.mpr hq.le)
    apply lintegral_mono_ae
    filter_upwards [hle] with x hx
    have he : ‖G x‖ₑ = ENNReal.ofReal (G x) := by
      simp only [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hG0 x)]
    rw [he]
    exact ENNReal.rpow_le_rpow hx hq.le
  exact hnorm.trans ((ENNReal.le_ofReal_iff_toReal_le hp.ne hK).2 hn)

/-- The canonical active density obeys precisely the source restarted tail estimate. -/
theorem positionActiveDensity_tail (hpush : PushforwardStatement)
    (htail : RestartTailStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (q : ℝ) (hq : 1 < q ∧ q < 3 / 2) :
    ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧ ∀ (A : SmoothAutonomous lam Lam)
      (c : Clock) (e : Point) (_he : e.velocity 0 ∈ c.active) (t : ℝ),
      0 ≤ t →
      positionPositiveNorm
        (volume.restrict {p | e.time + t ≤ p.time ∧ p.velocity 0 ∈ c.active}) q
        (positionActiveDensity hH hLE hlam hLam A c e) ≤
          ENNReal.ofReal (C * Real.exp (-c₀ * t / c.r ^ 2) * c.r ^ (6 / q - 4)) := by
  have : SigmaFinite (volume : Measure Point) := density_volume_sigmaFinite
  obtain ⟨C, c₀, hC, hc, hd⟩ := htail hH hLE lam Lam hlam hLam q hq
  refine ⟨C, c₀, hC, hc, ?_⟩
  intro A c e he t ht
  obtain ⟨G, hG, hGt⟩ := hd A c e he
  have hdens := (withDensity_positionActiveDensity hpush hH hLE hlam hLam A c e).trans
    ((enlargedActiveGreenKernel_apply hH hLE hlam hLam A c e he).trans hG.2.2)
  apply positionPositiveNorm_of_density_le volume _
    ((measurable_positionActiveDensity hH hLE hlam hLam A c).comp
      (measurable_const.prodMk measurable_id)) (densityClockStrip c e) _
      (by
        exact (isOpen_lt continuous_const continuous_time).measurableSet.inter
          (isOpen_Ioo.measurableSet.preimage
            ((continuous_apply 0).comp continuous_velocity).measurable))
      G hG.1 hG.2.1 hdens q _ (by linarith [hq.1])
      (mul_nonneg (mul_nonneg hC.le (Real.exp_pos _).le)
        (Real.rpow_nonneg c.positive.le _))
      (hGt t ht).1 (hGt t ht).2







/-- Every nonzero canonical active density value lies in its strict future finite-speed cone. -/
theorem positionActiveDensity_support (hpush : PushforwardStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (hc : |c.vbar| = 2 * c.r)
    (e : Point) (he : e.velocity 0 ∈ c.active) :
    ∀ᵐ z ∂(volume : Measure Point),
      positionActiveDensity hH hLE hlam hLam A c e z ≠ 0 →
        e.time < z.time ∧ z.velocity 0 ∈ c.active ∧
          |z.position 0 - e.position 0| ≤ 3 * c.r * (z.time - e.time)  := by
  have positionActive_speed :
      max |c.activeInterval.lo| |c.activeInterval.hi| ≤ 3 * c.r := by
    apply max_le
    · have h := abs_sub c.vbar (3 * c.r / 4)
      rw [hc, abs_of_nonneg (by linarith [c.positive] : 0 ≤ 3 * c.r / 4)] at h
      change |c.vbar - 3 * c.r / 4| ≤ 3 * c.r
      linarith only [h, c.positive]
    · have h := abs_add_le c.vbar (3 * c.r / 4)
      rw [hc, abs_of_nonneg (by linarith [c.positive] : 0 ≤ 3 * c.r / 4)] at h
      change |c.vbar + 3 * c.r / 4| ≤ 3 * c.r
      linarith only [h, c.positive]
  have hm : Measurable (positionActiveDensity hH hLE hlam hLam A c e) :=
    (measurable_positionActiveDensity hH hLE hlam hLam A c).comp
      (measurable_const.prodMk measurable_id)
  apply (ae_withDensity_iff hm).mp
  rw [withDensity_positionActiveDensity hpush hH hLE hlam hLam,
    enlargedActiveGreenKernel_apply hH hLE hlam hLam A c e he]
  obtain ⟨C, _, hd⟩ := (hpush hH hLE lam Lam hlam hLam).2 (5 / 4) (by norm_num)
  obtain ⟨G, _, _, hG, _, _⟩ := hd A c e he
  have hS : MeasurableSet (densityClockStrip c e) :=
    (isOpen_lt continuous_const continuous_time).measurableSet.inter
      (isOpen_Ioo.measurableSet.preimage
        ((continuous_apply 0).comp continuous_velocity).measurable)
  have hmem : ∀ᵐ z ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      (densityClockPole c e he), z ∈ densityClockStrip c e := by
    rw [hG]
    exact (ae_restrict_mem hS).filter_mono (withDensity_absolutelyContinuous _ _).ae_le
  have hcone : ∀ᵐ z ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      (densityClockPole c e he),
      |z.position 0 - e.position 0| ≤
        max |c.activeInterval.lo| |c.activeInterval.hi| * (z.time - e.time) := by
    rw [ae_iff]
    simpa only [not_le, densityClockPole] using strip_cone hH hLE hlam hLam A c.activeInterval ⊤
      (densityClockPole c e he)
  filter_upwards [hmem, hcone] with z hz hcZ
  exact ⟨hz.1, hz.2, hcZ.trans
    (mul_le_mul_of_nonneg_right (positionActive_speed) (sub_nonneg.mpr hz.1.le))⟩


/-- Support inside a larger observation set transfers the positive Lq norm bound. -/
theorem positionPositiveNorm_restrict_le {X : Type*} [MeasurableSpace X]
    (m : Measure X) (F : X → ℝ≥0∞) (q : ℝ) (hq : 0 < q)
    (E T : Set X) (hE : MeasurableSet E) (hT : MeasurableSet T)
    (hs : ∀ᵐ x ∂m, x ∈ E → F x ≠ 0 → x ∈ T) :
    positionPositiveNorm (m.restrict E) q F ≤ positionPositiveNorm (m.restrict T) q F := by
  unfold positionPositiveNorm
  apply ENNReal.rpow_le_rpow _ (one_div_nonneg.mpr hq.le)
  rw [← lintegral_indicator hE, ← lintegral_indicator hT]
  apply lintegral_mono_ae
  filter_upwards [hs] with x hx
  by_cases he : x ∈ E
  · rw [indicator_of_mem he]
    by_cases hf : F x = 0
    · rw [hf, ENNReal.zero_rpow_of_pos hq]
      exact zero_le
    · rw [indicator_of_mem (hx he hf)]
  · rw [indicator_of_notMem he]
    exact zero_le

/-- The elapsed tail used on output bin `i` after source bin `j`. -/
def positionOverlapDelay (i j : ℕ) : ℝ := max ((i : ℝ) - (j : ℝ) - 1) 0


/-- A source pole obeys the restarted-tail norm bound on any output cell. -/
theorem positionActiveDensity_output_tail (hpush : PushforwardStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (hc : |c.vbar| = 2 * c.r)
    (s x : ℝ) (j i : ℕ) (k ell : ℤ) (e : Point)
    (he : e ∈ enlargedStartCell c s x j k) (hv : e.velocity 0 ∈ c.active)
    (q : ℝ) (hq : 0 < q) (K : ℝ≥0∞)
    (htail : positionPositiveNorm
      (volume.restrict {z | e.time + positionOverlapDelay i j * c.r ^ 2 ≤ z.time ∧
        z.velocity 0 ∈ c.active}) q
      (positionActiveDensity hH hLE hlam hLam A c e) ≤ K) :
    positionPositiveNorm (volume.restrict (enlargedOutputCell c s x i ell)) q
      (positionActiveDensity hH hLE hlam hLam A c e) ≤ K  := by
  have positionOverlapDelay_le (z : Point) (hz : z ∈ enlargedStartCell c s x i ell) (ht : e.time < z.time) :
      e.time + positionOverlapDelay i j * c.r ^ 2 ≤ z.time := by
    unfold positionOverlapDelay
    by_cases h : 0 ≤ (i : ℝ) - (j : ℝ) - 1
    · rw [max_eq_left h]
      nlinarith only [((enlargedTimeBin_bounds c.r s e.time j he.1).2), ((enlargedTimeBin_bounds c.r s z.time i hz.1).1)]
    · rw [max_eq_right (le_of_not_ge h), zero_mul, add_zero]
      exact ht.le
  apply LE.le.trans _ htail
  apply positionPositiveNorm_restrict_le volume _ q hq _ _
    (measurableSet_enlargedOutputCell c s x i ell)
    ((isClosed_le continuous_const continuous_time).measurableSet.inter
      (isOpen_Ioo.measurableSet.preimage
        ((continuous_apply 0).comp continuous_velocity).measurable))
  filter_upwards [positionActiveDensity_support hpush hH hLE hlam hLam A c hc e hv]
    with z hz hcell hnonzero
  have hs := hz hnonzero
  exact ⟨positionOverlapDelay_le z hcell.1 hs.1, hs.2.1⟩

/-- Cells outside the finite-speed overlap region receive no density contribution. -/
theorem positionActiveDensity_output_zero (hpush : PushforwardStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (hc : |c.vbar| = 2 * c.r)
    (s x : ℝ) (j i : ℕ) (k ell : ℤ) (e : Point)
    (he : e ∈ enlargedStartCell c s x j k) (hv : e.velocity 0 ∈ c.active)
    (hno : ¬(j ≤ i ∧ |((ell - k : ℤ) : ℝ)| ≤ 5 * ((i : ℝ) - (j : ℝ) + 1))) :
    ∀ᵐ z ∂volume.restrict (enlargedOutputCell c s x i ell),
      positionActiveDensity hH hLE hlam hLam A c e z = 0   := by
  have positionOverlap_time_index (z : Point) (hz : z ∈ enlargedStartCell c s x i ell) (ht : e.time < z.time) :
      j ≤ i := by
    by_contra hji
    have helo := enlargedTimeBin_lower_strict c.r s e.time j (by omega) he.1
    have hzup := (enlargedTimeBin_bounds c.r s z.time i hz.1).2
    have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (lt_of_not_ge hji)
    nlinarith only [helo, hzup, hcast, sq_nonneg c.r, ht]
  have positionOverlap_position_index (z : Point) (hz : z ∈ enlargedStartCell c s x i ell) (ht : e.time < z.time) (hcone : |z.position 0 - e.position 0| ≤ 3 * c.r * (z.time - e.time)) :
      |((ell - k : ℤ) : ℝ)| ≤ 5 * ((i : ℝ) - (j : ℝ) + 1) := by
    have positionOverlap_elapsed :
        z.time - e.time ≤ ((i : ℝ) - (j : ℝ) + 1) * c.r ^ 2 := by
      linarith only [((enlargedTimeBin_bounds c.r s e.time j he.1).1), ((enlargedTimeBin_bounds c.r s z.time i hz.1).2)]
    have hcast : (j : ℝ) ≤ (i : ℝ) := by exact_mod_cast (positionOverlap_time_index z hz ht)
    have hd : 1 ≤ (i : ℝ) - (j : ℝ) + 1 := by linarith only [hcast]
    have hs : |z.position 0 - e.position 0| ≤
        3 * ((i : ℝ) - (j : ℝ) + 1) * c.r ^ 3 := by
      apply hcone.trans
      calc
        _ ≤ 3 * c.r * (((i : ℝ) - (j : ℝ) + 1) * c.r ^ 2) :=
          mul_le_mul_of_nonneg_left positionOverlap_elapsed (by linarith [c.positive])
        _ = _ := by ring
    have hep := he.2
    have hzp := hz.2
    have hr3 := pow_pos c.positive 3
    have hleft : ((ell : ℝ) - (k : ℝ)) * c.r ^ 3 ≤
        (3 * ((i : ℝ) - (j : ℝ) + 1) + 1) * c.r ^ 3 := by
      nlinarith only [hep.2, hzp.1, hs, (le_abs_self (z.position 0 - e.position 0))]
    have hright : -((ell : ℝ) - (k : ℝ)) * c.r ^ 3 ≤
        (3 * ((i : ℝ) - (j : ℝ) + 1) + 1) * c.r ^ 3 := by
      nlinarith only [hep.1, hzp.2, hs, (neg_le_abs (z.position 0 - e.position 0))]
    rw [Int.cast_sub, abs_le]
    constructor <;> linarith only [((mul_le_mul_iff_left₀ hr3).mp hleft), ((mul_le_mul_iff_left₀ hr3).mp hright), hd]
  filter_upwards [ae_restrict_of_ae
    (positionActiveDensity_support hpush hH hLE hlam hLam A c hc e hv),
    ae_restrict_mem (measurableSet_enlargedOutputCell c s x i ell)] with z hz hcell
  by_contra hnonzero
  have hs := hz hnonzero
  apply hno
  exact ⟨positionOverlap_time_index z hcell.1 hs.1,
    positionOverlap_position_index z hcell.1 hs.1 hs.2.2⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

