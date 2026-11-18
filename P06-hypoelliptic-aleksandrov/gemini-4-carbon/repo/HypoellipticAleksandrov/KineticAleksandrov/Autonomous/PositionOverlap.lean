module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapMixture
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapCells
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapRestriction

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter
open scoped ENNReal Classical

/-- The two-index source cells form a pairwise disjoint grid. -/
theorem enlargedStartCell_pairwiseDisjoint (c : Clock) (s x : ℝ) :
    Pairwise (fun a b : ℕ × ℤ =>
      Disjoint (enlargedStartCell c s x a.1 a.2) (enlargedStartCell c s x b.1 b.2)) := by
  intro a b hab
  apply disjoint_left.mpr
  intro p ha hb
  by_cases ht : a.1 = b.1
  · have hk : a.2 ≠ b.2 := by
      intro hk
      exact hab (Prod.ext ht hk)
    exact disjoint_left.mp (enlargedPositionCell_disjoint c.r x c.positive hk) ha.2 hb.2
  · exact disjoint_left.mp (enlargedTimeBin_disjoint c.r s c.positive ht) ha.1 hb.1

/-- The time-position grid covers all starting points on and after its time origin. -/
theorem enlargedStartCell_iUnion (c : Clock) (s x : ℝ) :
    (⋃ a : ℕ × ℤ, enlargedStartCell c s x a.1 a.2) = {p | s ≤ p.time} := by
  ext p
  constructor
  · intro hp
    obtain ⟨a, ha⟩ := mem_iUnion.mp hp
    have hj : 0 ≤ (a.1 : ℝ) := Nat.cast_nonneg _
    exact (le_add_of_nonneg_right (mul_nonneg hj (sq_nonneg c.r))).trans ((enlargedTimeBin_bounds c.r s p.time a.1 ha.1).1)
  · intro hp
    obtain ⟨j, hj⟩ := enlargedTimeBin_covers c.r s p.time c.positive hp
    obtain ⟨k, hk⟩ := enlargedPositionCell_covers c.r x (p.position 0) c.positive
    exact mem_iUnion.mpr ⟨(j, k), hj, hk⟩

/-- A positive starting measure after the origin is the sum of its cell restrictions. -/
theorem enlargedStartCell_measure_sum (nu : Measure Point) (c : Clock) (s x : ℝ)
    (hnu : ∀ᵐ e ∂nu, s ≤ e.time) :
    nu = Measure.sum (fun a : ℕ × ℤ => nu.restrict (enlargedStartCell c s x a.1 a.2)) := by
  have he : nu.restrict (⋃ a : ℕ × ℤ, enlargedStartCell c s x a.1 a.2) = nu := by
    rw [enlargedStartCell_iUnion]
    exact Measure.restrict_eq_self_of_ae_mem hnu
  exact he.symm.trans (Measure.restrict_iUnion (enlargedStartCell_pairwiseDisjoint c s x)
    (fun a => measurableSet_enlargedStartCell c s x a.1 a.2))

/-- The actual positive mixture density decomposes into the same source-cell mixtures. -/
theorem positionMixtureDensity_sum_cells
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (nu : Measure Point) (s x : ℝ)
    (hnu : ∀ᵐ e ∂nu, s ≤ e.time) :
    positionMixtureDensity hH hLE hlam hLam A c nu =
      fun z => ∑' a : ℕ × ℤ, positionMixtureDensity hH hLE hlam hLam A c
        (nu.restrict (enlargedStartCell c s x a.1 a.2)) z := by
  calc
    _ = positionMixtureDensity hH hLE hlam hLam A c
        (Measure.sum (fun a : ℕ × ℤ => nu.restrict
          (enlargedStartCell c s x a.1 a.2))) :=
      congrArg (positionMixtureDensity hH hLE hlam hLam A c)
        (enlargedStartCell_measure_sum nu c s x hnu)
    _ = _ := by
      funext z
      exact lintegral_sum_measure _ _


/-- The literal exponential delay and finite-speed position overlap kernel. -/
def positionOverlapWeight (c₀ : ℝ) (i j : ℕ) (ell k : ℤ) : ℝ≥0∞ :=
  if j ≤ i ∧ |((ell - k : ℤ) : ℝ)| ≤ 5 * ((i : ℝ) - (j : ℝ) + 1) then
    ENNReal.ofReal (Real.exp (-c₀ * positionOverlapDelay i j)) else 0


/-- The canonical mixture satisfies the source exponential two-index overlap convolution. -/
theorem position_density_convolution_positive (hpush : PushforwardStatement)
    (htail : RestartTailStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (q : ℝ) (hq : 1 < q ∧ q < 3 / 2) :
    ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧ ∀ (A : SmoothAutonomous lam Lam)
      (c : Clock) (_hc : |c.vbar| = 2 * c.r) (s x : ℝ)
      (nu : Measure Point) [IsFiniteMeasure nu],
      (∀ᵐ e ∂nu, s ≤ e.time ∧ e.velocity 0 ∈ c.active) →
      ∀ (i : ℕ) (ell : ℤ),
      positionPositiveNorm (volume.restrict (enlargedOutputCell c s x i ell)) q
        (positionMixtureDensity hH hLE hlam hLam A c nu) ≤
        ENNReal.ofReal (C * c.r ^ (6 / q - 4)) *
          ∑' a : ℕ × ℤ, positionOverlapWeight c₀ i a.1 ell a.2 *
            nu (enlargedStartCell c s x a.1 a.2)  := by
  have position_source_cell_norm :
      ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧ ∀ (A : SmoothAutonomous lam Lam)
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
        exact positionActiveDensity_output_tail hpush hH hLE hlam hLam A c hc s x j i k ell
          e he hv q hq0 K h
      have hn := positionPositiveNorm_mixture_le (nu.restrict B) (volume.restrict E)
        F hF q hq.1 K hpole
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
        have hz := positionActiveDensity_output_zero hpush hH hLE hlam hLam A c hc s x j i k ell
          e he hv hover
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
  have : SigmaFinite (volume : Measure Point) := density_volume_sigmaFinite
  obtain ⟨C, c₀, hC, hc₀, hd⟩ := position_source_cell_norm
  refine ⟨C, c₀, hC, hc₀, ?_⟩
  intro A c hc s x nu hfinite hnu i ell
  rw [positionMixtureDensity_sum_cells hH hLE hlam hLam A c nu s x (hnu.mono (fun _ h => h.1))]
  apply (positionPositiveNorm_tsum (volume.restrict (enlargedOutputCell c s x i ell))
    q hq.1.le
    (fun a => positionMixtureDensity hH hLE hlam hLam A c
      (nu.restrict (enlargedStartCell c s x a.1 a.2)))
    (fun a : ℕ × ℤ => measurable_positionMixtureDensity hH hLE hlam hLam A c
      (nu.restrict (enlargedStartCell c s x a.1 a.2)))).trans
  calc
    _ ≤ ∑' a : ℕ × ℤ, ENNReal.ofReal (C * c.r ^ (6 / q - 4)) *
        positionOverlapWeight c₀ i a.1 ell a.2 * nu (enlargedStartCell c s x a.1 a.2) :=
      ENNReal.tsum_le_tsum (fun a => hd A c hc s x nu (hnu.mono (fun _ h => h.2)) i a.1 ell a.2)
    _ = _ := by simp_rw [mul_assoc]; rw [ENNReal.tsum_mul_left]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

