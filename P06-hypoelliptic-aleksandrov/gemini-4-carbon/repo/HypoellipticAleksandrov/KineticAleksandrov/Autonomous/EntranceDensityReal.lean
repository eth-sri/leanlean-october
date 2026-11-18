module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.MixtureDensity
import Mathlib.Algebra.Order.Floor.Ring
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapRestriction
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TailRestartDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockPushforward
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PoleDensityStatement
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumPartition
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumReal

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter
open scoped ENNReal Classical

/-- The literal source time bin of length r² on the full integer grid. -/
def entranceTimeBin (r : ℝ) (j : ℤ) : Set Point :=
  {p | p.time ∈ Ioc ((j : ℝ) * r ^ 2) (((j : ℝ) + 1) * r ^ 2)}

/-- Every full-grid source bin is Borel. -/
theorem measurableSet_entranceTimeBin (r : ℝ) (j : ℤ) :
    MeasurableSet (entranceTimeBin r j) :=
  measurableSet_Ioc.preimage continuous_time.measurable

/-- Full-grid right-closed source bins are pairwise disjoint. -/
theorem entranceTimeBin_pairwise (r : ℝ) :
    Pairwise (fun i j => Disjoint (entranceTimeBin r i) (entranceTimeBin r j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro p hi hj
  have hi' : (i : ℝ) * r ^ 2 < p.time ∧ p.time ≤ ((i : ℝ) + 1) * r ^ 2 := hi
  have hj' : (j : ℝ) * r ^ 2 < p.time ∧ p.time ≤ ((j : ℝ) + 1) * r ^ 2 := hj
  rcases lt_or_gt_of_ne hij with h | h
  · have hc : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast h
    have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg r)
    linarith
  · have hc : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast h
    have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg r)
    linarith

/-- Every real time lies in exactly one right-closed integer bin. -/
theorem iUnion_entranceTimeBin (r : ℝ) (hr : 0 < r) :
    (⋃ j : ℤ, entranceTimeBin r j) = univ := by
  apply Set.eq_univ_of_forall
  intro p
  let a := p.time / r ^ 2
  let j := Int.ceil a - 1
  apply mem_iUnion.mpr
  refine ⟨j, ?_⟩
  have hl : (j : ℝ) < a := Int.lt_ceil.mp (by dsimp [j]; omega)
  have hu : a ≤ (j : ℝ) + 1 := by
    simpa only [j, Int.cast_sub, Int.cast_one, sub_add_cancel] using Int.le_ceil a
  have hr2 := sq_pos_of_pos hr
  exact ⟨(lt_div_iff₀ hr2).mp hl, (div_le_iff₀ hr2).mp hu⟩




/-- The observation bin includes every position and the entire active velocity interval. -/
def entranceOutputBin (c : Clock) (j : ℤ) : Set Point :=
  entranceTimeBin c.r j ∩ {p | p.velocity 0 ∈ c.active}

/-- Full-position observation bins are Borel. -/
theorem measurableSet_entranceOutputBin (c : Clock) (j : ℤ) :
    MeasurableSet (entranceOutputBin c j) :=
  (measurableSet_entranceTimeBin c.r j).inter
    (isOpen_Ioo.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)

/-- The canonical positive pole density retains its exact strict future support. -/
theorem timeActiveDensity_support (hpush : PushforwardStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    ∀ᵐ z ∂(volume : Measure Point),
      positionActiveDensity hH hLE hlam hLam A c e z ≠ 0 →
        e.time < z.time ∧ z.velocity 0 ∈ c.active := by
  have hm : Measurable (positionActiveDensity hH hLE hlam hLam A c e) :=
    (measurable_positionActiveDensity hH hLE hlam hLam A c).comp
    (measurable_const.prodMk measurable_id)
  apply (ae_withDensity_iff hm).mp
  rw [withDensity_positionActiveDensity hpush hH hLE hlam hLam,
    enlargedActiveGreenKernel_apply hH hLE hlam hLam A c e he]
  obtain ⟨_, _, hd⟩ := (hpush hH hLE lam Lam hlam hLam).2 (5 / 4) (by norm_num)
  obtain ⟨G, _, _, hG, _, _⟩ := hd A c e he
  have hS : MeasurableSet (densityClockStrip c e) :=
    (continuous_time.measurable measurableSet_Ioi).inter
      (isOpen_Ioo.measurableSet.preimage
        ((continuous_apply 0).comp continuous_velocity).measurable)
  rw [hG]
  exact (ae_restrict_mem hS).filter_mono (withDensity_absolutelyContinuous _ _).ae_le

/-- Source and output bins determine the nonnegative elapsed restart delay. -/
def entranceBinDelay (j k : ℤ) : ℝ := max ((j : ℝ) - (k : ℝ) - 1) 0

/-- A valid pole obeys its exponential tail on a whole-position output bin. -/
theorem timeActiveDensity_output_tail (hpush : PushforwardStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (j k : ℤ)
    (he : e ∈ entranceTimeBin c.r k) (hv : e.velocity 0 ∈ c.active)
    (q : ℝ) (hq : 0 < q) (K : ℝ≥0∞)
    (htail : positionPositiveNorm
      (volume.restrict {z | e.time + entranceBinDelay j k * c.r ^ 2 ≤ z.time ∧
        z.velocity 0 ∈ c.active}) q
      (positionActiveDensity hH hLE hlam hLam A c e) ≤ K) :
    positionPositiveNorm (volume.restrict (entranceOutputBin c j)) q
      (positionActiveDensity hH hLE hlam hLam A c e) ≤ K := by
  apply LE.le.trans _ htail
  apply positionPositiveNorm_restrict_le volume _ q hq _ _
    (measurableSet_entranceOutputBin c j)
    ((continuous_time.measurable measurableSet_Ici).inter
      (isOpen_Ioo.measurableSet.preimage
        ((continuous_apply 0).comp continuous_velocity).measurable))
  filter_upwards [timeActiveDensity_support hpush hH hLE hlam hLam A c e hv]
    with z hz hcell hnonzero
  have hs := hz hnonzero
  refine ⟨?_, hs.2⟩
  unfold entranceBinDelay
  by_cases h : 0 ≤ (j : ℝ) - (k : ℝ) - 1
  · rw [max_eq_left h]
    calc
      _ ≤ ((k : ℝ) + 1) * c.r ^ 2 + ((j : ℝ) - (k : ℝ) - 1) * c.r ^ 2 :=
        add_le_add he.2 le_rfl
      _ = (j : ℝ) * c.r ^ 2 := by ring
      _ ≤ z.time := hcell.1.1.le
  · rw [max_eq_right (le_of_not_ge h), zero_mul, add_zero]
    exact hs.1.le

/-- Later starting bins cannot contribute to an earlier output bin. -/
theorem timeActiveDensity_output_zero (hpush : PushforwardStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (j k : ℤ)
    (he : e ∈ entranceTimeBin c.r k) (hv : e.velocity 0 ∈ c.active) (hjk : j < k) :
    ∀ᵐ z ∂volume.restrict (entranceOutputBin c j),
      positionActiveDensity hH hLE hlam hLam A c e z = 0 := by
  filter_upwards [ae_restrict_of_ae
    (timeActiveDensity_support hpush hH hLE hlam hLam A c e hv),
    ae_restrict_mem (measurableSet_entranceOutputBin c j)] with z hz hcell
  by_contra hn
  have hs := (hz hn).1
  have hcast : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hjk
  have hh := mul_le_mul_of_nonneg_right hcast (sq_nonneg c.r)
  have helo := he.1
  have hzup := hcell.1.2
  linarith


/-- The causal time-bin kernel, including the adjacent-bin delay. -/
def entranceBinWeight (c₀ : ℝ) (j k : ℤ) : ℝ≥0∞ :=
  if k ≤ j then ENNReal.ofReal (Real.exp (-c₀ * entranceBinDelay j k)) else 0


/-- The actual positive mixture decomposes into its full-grid source-bin mixtures. -/
theorem entranceMixtureDensity_sum_bins
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (nu : Measure Point) :
    positionMixtureDensity hH hLE hlam hLam A c nu =
      fun z => ∑' k : ℤ, positionMixtureDensity hH hLE hlam hLam A c
        (nu.restrict (entranceTimeBin c.r k)) z := by
  have he : nu = Measure.sum (fun k => nu.restrict (entranceTimeBin c.r k)) := by
    have hh := Measure.restrict_iUnion (μ := nu) (entranceTimeBin_pairwise c.r)
      (measurableSet_entranceTimeBin c.r)
    rw [iUnion_entranceTimeBin c.r c.positive, Measure.restrict_univ] at hh
    exact hh
  calc
    _ = positionMixtureDensity hH hLE hlam hLam A c
        (Measure.sum (fun k => nu.restrict (entranceTimeBin c.r k))) :=
      congrArg (positionMixtureDensity hH hLE hlam hLam A c) he
    _ = _ := by funext z; exact lintegral_sum_measure _ _




/-- Exponential time-bin weights have a summable integer majorant. -/
theorem entranceBinWeight_le (c₀ : ℝ) (hc₀ : 0 < c₀) (j k : ℤ) :
    entranceBinWeight c₀ j k ≤ ENNReal.ofReal (Real.exp c₀) *
      ENNReal.ofReal (Real.exp (-c₀ * |((j - k : ℤ) : ℝ)|)) := by
  unfold entranceBinWeight
  split_ifs with hkj
  · rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh : 0 ≤ (j : ℝ) - (k : ℝ) := by exact_mod_cast sub_nonneg.mpr hkj
    rw [Int.cast_sub, abs_of_nonneg hh]
    change -c₀ * max ((j : ℝ) - (k : ℝ) - 1) 0 ≤ _
    nlinarith only [hc₀, (le_max_left ((j : ℝ) - (k : ℝ) - 1) 0)]
  · exact zero_le

/-- The actual causal time convolution has its q-power sum bounded by the input mass sum. -/
theorem entrance_convolution_power_sum (c₀ : ℝ) (hc₀ : 0 < c₀)
    (a : ℤ → ℝ≥0∞) (q : ℝ) (hq : 1 < q) :
    (∑' j : ℤ, (∑' k : ℤ, entranceBinWeight c₀ j k * a k) ^ q) ≤
      (ENNReal.ofReal (Real.exp c₀) *
        ∑' k : ℤ, ENNReal.ofReal (Real.exp (-c₀ * |(k : ℝ)|))) ^ q *
          ∑' k : ℤ, a k ^ q  := by
  have entrance_time_young (w : ℤ → ℝ≥0∞) :
      (∑' j : ℤ, (∑' k : ℤ, w (j - k) * a k) ^ q) ≤
      (∑' k : ℤ, w k) ^ q * ∑' j : ℤ, a j ^ q := by
    have he (j : ℤ) : (∑' k : ℤ, w (j - k) * a k) =
        ∑' k : ℤ, w k * a (j - k) := by
      have h := (Equiv.subLeft j).tsum_eq (fun k => w (j - k) * a k)
      simpa using h.symm
    simp_rw [he]
    exact position_two_index_young w a q hq
  let D := ENNReal.ofReal (Real.exp c₀)
  let w := fun k : ℤ => ENNReal.ofReal (Real.exp (-c₀ * |(k : ℝ)|))
  have hc (j : ℤ) : (∑' k : ℤ, entranceBinWeight c₀ j k * a k) ≤
      D * ∑' k : ℤ, w (j - k) * a k := by
    calc
      _ ≤ ∑' k : ℤ, D * w (j - k) * a k := by
        apply ENNReal.tsum_le_tsum
        intro k
        gcongr
        exact entranceBinWeight_le c₀ hc₀ j k
      _ = _ := by simp_rw [mul_assoc]; rw [ENNReal.tsum_mul_left]
  calc
    _ ≤ ∑' j : ℤ, (D * ∑' k : ℤ, w (j - k) * a k) ^ q :=
      ENNReal.tsum_le_tsum (fun j => ENNReal.rpow_le_rpow (hc j) (by linarith))
    _ = D ^ q * ∑' j : ℤ, (∑' k : ℤ, w (j - k) * a k) ^ q := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ q)]
      rw [ENNReal.tsum_mul_left]
    _ ≤ D ^ q * ((∑' k : ℤ, w k) ^ q * ∑' k : ℤ, a k ^ q) := by
      gcongr
      exact entrance_time_young w
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ q)]





/-- Summing output-bin q-power norms gives exactly the whole density power integral. -/
theorem entranceMixtureDensity_power_partition (hpush : PushforwardStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (nu : Measure Point) [SFinite nu]
    (q : ℝ) (hq : 0 < q) (hnu : ∀ᵐ e ∂nu, e.velocity 0 ∈ c.active) :
    (∫⁻ z, positionMixtureDensity hH hLE hlam hLam A c nu z ^ q ∂volume) =
      ∑' j : ℤ, positionPositiveNorm (volume.restrict (entranceOutputBin c j)) q
        (positionMixtureDensity hH hLE hlam hLam A c nu) ^ q    := by
  have entranceMixtureDensity_support :
      ∀ᵐ z ∂(volume : Measure Point),
      positionMixtureDensity hH hLE hlam hLam A c nu z ≠ 0 → z.velocity 0 ∈ c.active := by
    apply (ae_withDensity_iff (measurable_positionMixtureDensity hH hLE hlam hLam A c nu)).mp
    rw [withDensity_positionMixtureDensity hpush hH hLE hlam hLam]
    have hS : MeasurableSet {z : Point | z.velocity 0 ∈ c.active} :=
      isOpen_Ioo.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable
    apply Measure.ae_comp_of_ae_ae hS
    filter_upwards [hnu] with e he
    rw [← withDensity_positionActiveDensity hpush hH hLE hlam hLam]
    apply (ae_withDensity_iff ((measurable_positionActiveDensity hH hLE hlam hLam A c).comp
      (measurable_const.prodMk measurable_id))).mpr
    filter_upwards [timeActiveDensity_support hpush hH hLE hlam hLam A c e he]
      with z hz hn
    exact (hz hn).2
  have entranceOutputBin_pairwise :
      Pairwise (fun i j => Disjoint (entranceOutputBin c i) (entranceOutputBin c j)) := by
    intro i j hij
    exact (entranceTimeBin_pairwise c.r hij).mono inter_subset_left inter_subset_left
  have entranceOutputBin_iUnion :
      (⋃ j : ℤ, entranceOutputBin c j) = {p | p.velocity 0 ∈ c.active} := by
    unfold entranceOutputBin
    rw [← iUnion_inter, iUnion_entranceTimeBin c.r c.positive, univ_inter]
  let F := positionMixtureDensity hH hLE hlam hLam A c nu
  let U := {z : Point | z.velocity 0 ∈ c.active}
  have hU : MeasurableSet U :=
    isOpen_Ioo.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable
  have he : (∫⁻ z, F z ^ q ∂volume) = ∫⁻ z in U, F z ^ q ∂volume := by
    rw [← lintegral_indicator hU]
    apply lintegral_congr_ae
    filter_upwards [entranceMixtureDensity_support]
      with z hz
    by_cases h : z ∈ U
    · simp only [indicator_of_mem h]
    · have hf : F z = 0 := by by_contra hn; exact h (hz hn)
      simp only [indicator_of_notMem h, hf, ENNReal.zero_rpow_of_pos hq]
  rw [he]
  change (∫⁻ z in {p | p.velocity 0 ∈ c.active}, F z ^ q ∂volume) = _
  rw [← entranceOutputBin_iUnion,
    lintegral_iUnion (measurableSet_entranceOutputBin c) (entranceOutputBin_pairwise)]
  apply tsum_congr
  intro j
  exact (positionPositiveNorm_rpow _ q hq F).symm




/-- Total and short-window starting masses yield the exact source integrated norm scaling. -/
theorem entrance_density_from_counts
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (q : ℝ) (hq : 1 < q ∧ q < 3 / 2) (B M : ℝ) (hB : 0 < B) (hM : 0 < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (nu : Measure Point) [IsFiniteMeasure nu] (b : ℝ), 0 ≤ b →
      (∀ᵐ e ∂nu, e.velocity 0 ∈ c.active) →
      nu univ ≤ ENNReal.ofReal (B * b) →
      (∀ k : ℤ, nu (entranceTimeBin c.r k) ≤ ENNReal.ofReal M) →
      ∃ G : Point → ℝ, Measurable G ∧ (∀ z, 0 ≤ G z) ∧
        enlargedActiveGreen hH hLE hlam hLam A c nu =
          volume.withDensity (fun z => ENNReal.ofReal (G z)) ∧
        MemLp G (ENNReal.ofReal q) volume ∧
        (eLpNorm G (ENNReal.ofReal q) volume).toReal ≤
          C * c.r ^ (6 / q - 4) * b ^ (1 / q)   := by
  have entranceTimeBin_mass_rpow_sum (nu : Measure Point) (r : ℝ) (hr : 0 < r) (hq : 1 ≤ q) (M : ℝ≥0∞) (hM : ∀ j : ℤ, nu (entranceTimeBin r j) ≤ M) :
      (∑' j : ℤ, nu (entranceTimeBin r j) ^ q) ≤ nu univ * M ^ (q - 1) := by
    have entranceTimeBin_mass_sum :
        (∑' j : ℤ, nu (entranceTimeBin r j)) = nu univ := by
      rw [← measure_iUnion (entranceTimeBin_pairwise r) (measurableSet_entranceTimeBin r),
        iUnion_entranceTimeBin r hr]
    have hq' := sub_nonneg.mpr hq
    calc
      _ ≤ ∑' j : ℤ, nu (entranceTimeBin r j) * M ^ (q - 1) := by
        apply ENNReal.tsum_le_tsum
        intro j
        have he : nu (entranceTimeBin r j) ^ q =
            nu (entranceTimeBin r j) * nu (entranceTimeBin r j) ^ (q - 1) := by
          calc
            _ = nu (entranceTimeBin r j) ^ (1 + (q - 1)) := by congr 1; ring
            _ = _ := by
              rw [ENNReal.rpow_add_of_nonneg 1 (q - 1) zero_le_one hq', ENNReal.rpow_one]
        rw [he]
        gcongr
        exact hM j
      _ = (∑' j : ℤ, nu (entranceTimeBin r j)) * M ^ (q - 1) :=
        ENNReal.tsum_mul_right
      _ = _ := by rw [entranceTimeBin_mass_sum]
  have entrance_density_sum :
      ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
      (c : Clock) (nu : Measure Point) [IsFiniteMeasure nu],
      (∀ᵐ e ∂nu, e.velocity 0 ∈ c.active) →
      ∃ G : Point → ℝ, Measurable G ∧ (∀ z, 0 ≤ G z) ∧
        enlargedActiveGreen hH hLE hlam hLam A c nu =
          volume.withDensity (fun z => ENNReal.ofReal (G z)) ∧
        MemLp G (ENNReal.ofReal q) volume ∧
        (∫⁻ z, ‖G z‖ₑ ^ q ∂volume) ≤ ENNReal.ofReal (C * c.r ^ (6 - 4 * q)) *
          ∑' k : ℤ, nu (entranceTimeBin c.r k) ^ q := by
    have entrance_density_power_sum :
        ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
        (c : Clock) (nu : Measure Point) [IsFiniteMeasure nu],
        (∀ᵐ e ∂nu, e.velocity 0 ∈ c.active) →
        (∫⁻ z, positionMixtureDensity hH hLE hlam hLam A c nu z ^ q ∂volume) ≤
          ENNReal.ofReal (C * c.r ^ (6 - 4 * q)) *
            ∑' k : ℤ, nu (entranceTimeBin c.r k) ^ q := by
      have entrance_time_bin_convolution :
          ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧ ∀ (A : SmoothAutonomous lam Lam)
          (c : Clock) (nu : Measure Point) [IsFiniteMeasure nu],
          (∀ᵐ e ∂nu, e.velocity 0 ∈ c.active) → ∀ j : ℤ,
          positionPositiveNorm (volume.restrict (entranceOutputBin c j)) q
            (positionMixtureDensity hH hLE hlam hLam A c nu) ≤
            ENNReal.ofReal (C * c.r ^ (6 / q - 4)) *
              ∑' k : ℤ, entranceBinWeight c₀ j k * nu (entranceTimeBin c.r k) := by
        have entrance_source_bin_norm (hpush : PushforwardStatement) (htail : RestartTailStatement) :
            ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧ ∀ (A : SmoothAutonomous lam Lam)
            (c : Clock) (nu : Measure Point) [IsFiniteMeasure nu],
            (∀ᵐ e ∂nu, e.velocity 0 ∈ c.active) → ∀ j k : ℤ,
            positionPositiveNorm (volume.restrict (entranceOutputBin c j)) q
              (positionMixtureDensity hH hLE hlam hLam A c (nu.restrict (entranceTimeBin c.r k))) ≤
              ENNReal.ofReal (C * c.r ^ (6 / q - 4)) * entranceBinWeight c₀ j k *
                nu (entranceTimeBin c.r k) := by
          have : SigmaFinite (volume : Measure Point) := density_volume_sigmaFinite
          obtain ⟨C, c₀, hC, hc₀, hd⟩ := positionActiveDensity_tail hpush htail hH hLE hlam hLam q hq
          refine ⟨C, c₀, hC, hc₀, ?_⟩
          intro A c nu hfinite hnu j k
          let E := entranceOutputBin c j
          let B := entranceTimeBin c.r k
          let F := positionActiveDensity hH hLE hlam hLam A c
          have hF := measurable_positionActiveDensity hH hLE hlam hLam A c
          have hq0 : 0 < q := by linarith [hq.1]
          by_cases hkj : k ≤ j
          · let K := ENNReal.ofReal (C * Real.exp (-c₀ * entranceBinDelay j k) *
              c.r ^ (6 / q - 4))
            have hpole : ∀ᵐ e ∂nu.restrict B, positionPositiveNorm (volume.restrict E) q (F e) ≤ K := by
              filter_upwards [ae_restrict_of_ae hnu,
                ae_restrict_mem (measurableSet_entranceTimeBin c.r k)] with e hv he
              have hdelay : 0 ≤ entranceBinDelay j k * c.r ^ 2 :=
                mul_nonneg (le_max_right _ _) (sq_nonneg _)
              have h := hd A c e hv (entranceBinDelay j k * c.r ^ 2) hdelay
              have hexp : -c₀ * (entranceBinDelay j k * c.r ^ 2) / c.r ^ 2 =
                  -c₀ * entranceBinDelay j k := by field_simp [c.positive.ne']
              rw [hexp] at h
              exact timeActiveDensity_output_tail hpush hH hLE hlam hLam A c e j k he hv q hq0 K h
            have hn := positionPositiveNorm_mixture_le (nu.restrict B) (volume.restrict E)
              F hF q hq.1 K hpole
            change positionPositiveNorm (volume.restrict E) q
              (positionMixtureDensity hH hLE hlam hLam A c (nu.restrict B)) ≤
                (nu.restrict B) univ * K at hn
            apply hn.trans_eq
            rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
            unfold K entranceBinWeight
            rw [ite_eq_left hkj]
            rw [show C * Real.exp (-c₀ * entranceBinDelay j k) * c.r ^ (6 / q - 4) =
              (C * c.r ^ (6 / q - 4)) * Real.exp (-c₀ * entranceBinDelay j k) by ring,
              ENNReal.ofReal_mul (mul_nonneg hC.le (Real.rpow_nonneg c.positive.le _))]
            exact mul_comm _ _
          · have hpole : ∀ᵐ e ∂nu.restrict B, positionPositiveNorm (volume.restrict E) q (F e) ≤ 0 := by
              filter_upwards [ae_restrict_of_ae hnu,
                ae_restrict_mem (measurableSet_entranceTimeBin c.r k)] with e hv he
              have hz := timeActiveDensity_output_zero hpush hH hLE hlam hLam A c e j k
                he hv (lt_of_not_ge hkj)
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
            simpa [entranceBinWeight, ite_eq_right hkj] using hn
        obtain ⟨C, c₀, hC, hc₀, hd⟩ := entrance_source_bin_norm
          (pushforwardStatement_holds) (restartTailStatement_holds)
        refine ⟨C, c₀, hC, hc₀, ?_⟩
        intro A c nu hfinite hnu j
        rw [entranceMixtureDensity_sum_bins hH hLE hlam hLam A c nu]
        apply (positionPositiveNorm_tsum (volume.restrict (entranceOutputBin c j)) q hq.1.le
          (fun k => positionMixtureDensity hH hLE hlam hLam A c
            (nu.restrict (entranceTimeBin c.r k)))
          (fun k => measurable_positionMixtureDensity hH hLE hlam hLam A c
            (nu.restrict (entranceTimeBin c.r k)))).trans
        calc
          _ ≤ ∑' k : ℤ, ENNReal.ofReal (C * c.r ^ (6 / q - 4)) *
              entranceBinWeight c₀ j k * nu (entranceTimeBin c.r k) :=
            ENNReal.tsum_le_tsum (fun k => hd A c nu hnu j k)
          _ = _ := by simp_rw [mul_assoc]; rw [ENNReal.tsum_mul_left]
      obtain ⟨C, c₀, hC, hc₀, hd⟩ := entrance_time_bin_convolution
      let W := ∑' k : ℤ, Real.exp (-c₀ * |(k : ℝ)|)
      have hs := position_exp_abs_summable c₀ hc₀
      have hw (k : ℤ) : 0 ≤ Real.exp (-c₀ * |(k : ℝ)|) := (Real.exp_pos _).le
      have hW := hs.tsum_pos hw 0 (Real.exp_pos _)
      let D := C * Real.exp c₀ * W
      have hD : 0 < D := mul_pos (mul_pos hC (Real.exp_pos _)) hW
      refine ⟨D ^ q, Real.rpow_pos_of_pos hD q, ?_⟩
      intro A c nu hfinite hnu
      have hq0 : 0 < q := by linarith [hq.1]
      rw [entranceMixtureDensity_power_partition (pushforwardStatement_holds)
        hH hLE hlam hLam A c nu q hq0 hnu]
      calc
        _ ≤ ∑' j : ℤ, (ENNReal.ofReal (C * c.r ^ (6 / q - 4)) *
            ∑' k : ℤ, entranceBinWeight c₀ j k * nu (entranceTimeBin c.r k)) ^ q :=
          ENNReal.tsum_le_tsum (fun j => ENNReal.rpow_le_rpow (hd A c nu hnu j) hq0.le)
        _ = ENNReal.ofReal (C * c.r ^ (6 / q - 4)) ^ q *
            ∑' j : ℤ, (∑' k : ℤ, entranceBinWeight c₀ j k * nu (entranceTimeBin c.r k)) ^ q := by
          simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
          rw [ENNReal.tsum_mul_left]
        _ ≤ ENNReal.ofReal (C * c.r ^ (6 / q - 4)) ^ q *
            ((ENNReal.ofReal (Real.exp c₀) * ENNReal.ofReal W) ^ q *
              ∑' k : ℤ, nu (entranceTimeBin c.r k) ^ q) := by
          rw [← ((ENNReal.ofReal_tsum_of_nonneg hw hs).symm)]
          exact mul_le_mul_right (entrance_convolution_power_sum c₀ hc₀
            (fun k => nu (entranceTimeBin c.r k)) q hq.1) _
        _ = _ := by
          rw [← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ hq0.le,
            ← ENNReal.ofReal_mul (Real.exp_pos _).le,
            ← ENNReal.ofReal_mul (mul_nonneg hC.le (Real.rpow_nonneg c.positive.le _)),
            ENNReal.ofReal_rpow_of_pos
              (mul_pos (mul_pos hC (Real.rpow_pos_of_pos c.positive _))
                (mul_pos (Real.exp_pos _) hW))]
          congr 2
          have hbase : C * c.r ^ (6 / q - 4) * (Real.exp c₀ * W) =
              D * c.r ^ (6 / q - 4) := by dsimp [D]; ring
          rw [hbase, Real.mul_rpow hD.le (Real.rpow_nonneg c.positive.le _),
            ← Real.rpow_mul c.positive.le]
          congr 2
          field_simp
    obtain ⟨C, hC, hd⟩ := entrance_density_power_sum
    refine ⟨C, hC, ?_⟩
    intro A c nu hfinite hnu
    have hq0 : 0 < q := by linarith [hq.1]
    let F := positionMixtureDensity hH hLE hlam hLam A c nu
    have hF := measurable_positionMixtureDensity hH hLE hlam hLam A c nu
    have hm := withDensity_positionMixtureDensity (pushforwardStatement_holds)
      hH hLE hlam hLam A c nu
    have : IsFiniteMeasure (enlargedActiveGreen hH hLE hlam hLam A c nu) :=
      enlargedActiveGreen_isFiniteMeasure hH hLE hlam hLam A c nu
    obtain ⟨hG, hG0, hGd, hGi⟩ := position_density_real volume
      (enlargedActiveGreen hH hLE hlam hLam A c nu) F hF hm q
    have hbound := hd A c nu hnu
    have hsum := entranceTimeBin_mass_rpow_sum nu c.r c.positive hq.1.le (nu univ)
      (fun _ => measure_mono (subset_univ _))
    have hsumfinite :=
      hsum.trans_lt (ENNReal.mul_lt_top (measure_lt_top _ _)
        (ENNReal.rpow_lt_top_of_nonneg (by linarith [hq.1]) (measure_ne_top _ _)))
    have hi : (∫⁻ z, ‖(F z).toReal‖ₑ ^ q ∂volume) < ⊤ := by
      rw [hGi]
      exact hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsumfinite)
    refine ⟨fun z => (F z).toReal, hG, hG0, hGd, ?_, ?_⟩
    · change eLpNorm (fun z => (F z).toReal) (ENNReal.ofReal q) volume < ⊤
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (ne_of_gt (ENNReal.ofReal_pos.mpr hq0)) ENNReal.ofReal_ne_top
        hG.aestronglyMeasurable, ENNReal.toReal_ofReal hq0.le]
      exact ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr hq0.le) hi.ne
    · rwa [hGi]
  obtain ⟨D, hD, hd⟩ := entrance_density_sum
  let C := (D * B * M ^ (q - 1)) ^ (1 / q)
  have hbase : 0 < D * B * M ^ (q - 1) :=
    mul_pos (mul_pos hD hB) (Real.rpow_pos_of_pos hM _)
  refine ⟨C, Real.rpow_pos_of_pos hbase _, ?_⟩
  intro A c nu hfinite b hb hnu htotal hshort
  obtain ⟨G, hGm, hG0, hGd, hGp, hGi⟩ := hd A c nu hnu
  have hq0 : 0 < q := by linarith [hq.1]
  have hsum := entranceTimeBin_mass_rpow_sum nu c.r c.positive hq.1.le _ hshort
  have hp : (∫⁻ z, ‖G z‖ₑ ^ q ∂volume) ≤
      ENNReal.ofReal (D * c.r ^ (6 - 4 * q) * (B * b) * M ^ (q - 1)) := by
    calc
      _ ≤ ENNReal.ofReal (D * c.r ^ (6 - 4 * q)) *
          (nu univ * ENNReal.ofReal M ^ (q - 1)) := by
        exact hGi.trans (mul_le_mul_right hsum _)
      _ ≤ ENNReal.ofReal (D * c.r ^ (6 - 4 * q)) *
          (ENNReal.ofReal (B * b) * ENNReal.ofReal M ^ (q - 1)) := by gcongr
      _ = _ := by
        rw [ENNReal.ofReal_rpow_of_pos hM, ← mul_assoc,
          ← ENNReal.ofReal_mul (mul_nonneg hD.le (Real.rpow_nonneg c.positive.le _)),
          ← ENNReal.ofReal_mul (mul_nonneg
            (mul_nonneg hD.le (Real.rpow_nonneg c.positive.le _)) (mul_nonneg hB.le hb))]
  have hn : eLpNorm G (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (C * c.r ^ (6 / q - 4) * b ^ (1 / q)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ne_of_gt (ENNReal.ofReal_pos.mpr hq0)) ENNReal.ofReal_ne_top
      hGm.aestronglyMeasurable, ENNReal.toReal_ofReal hq0.le]
    apply (ENNReal.rpow_le_rpow hp (one_div_nonneg.mpr hq0.le)).trans_eq
    rw [ENNReal.ofReal_rpow_of_nonneg
      (mul_nonneg (mul_nonneg
        (mul_nonneg hD.le (Real.rpow_nonneg c.positive.le _)) (mul_nonneg hB.le hb))
          (Real.rpow_nonneg hM.le _)) (one_div_nonneg.mpr hq0.le)]
    congr 1
    have he : D * c.r ^ (6 - 4 * q) * (B * b) * M ^ (q - 1) =
        (D * B * M ^ (q - 1)) * c.r ^ (6 - 4 * q) * b := by ring
    rw [he, Real.mul_rpow (mul_nonneg hbase.le (Real.rpow_nonneg c.positive.le _)) hb,
      Real.mul_rpow hbase.le (Real.rpow_nonneg c.positive.le _),
      ← Real.rpow_mul c.positive.le]
    have hex : (6 - 4 * q) * (1 / q) = 6 / q - 4 := by field_simp
    rw [hex]
  refine ⟨G, hGm, hG0, hGd, hGp, ?_⟩
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hn).trans_eq
    (ENNReal.toReal_ofReal (mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hbase.le _) (Real.rpow_nonneg c.positive.le _))
        (Real.rpow_nonneg hb _)))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

