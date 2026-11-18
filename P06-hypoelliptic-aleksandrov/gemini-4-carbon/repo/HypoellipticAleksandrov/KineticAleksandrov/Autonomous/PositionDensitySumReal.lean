module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlap
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumPartition
import Mathlib.Topology.Algebra.InfiniteSum.Order
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GeometricCoreCoverSeries
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter
open scoped ENNReal Classical

/-- Include the nonnegative time-bin lattice in the full two-index group. -/
def positionIndexEmbedding (a : ℕ × ℤ) : ℤ × ℤ := ((a.1 : ℤ), a.2)

/-- The source grid embedding is injective. -/
theorem positionIndexEmbedding_injective : Function.Injective positionIndexEmbedding := by
  intro a b h
  apply Prod.ext
  · have he := congrArg Prod.fst h
    change (a.1 : ℤ) = (b.1 : ℤ) at he
    exact_mod_cast he
  · exact congrArg (fun a => a.2) h

/-- Extend the source starting masses by zero to negative time indices. -/
def positionMassSequence (nu : Measure Point) (c : Clock) (s x : ℝ) (a : ℤ × ℤ) : ℝ≥0∞ :=
  if 0 ≤ a.1 then nu (enlargedStartCell c s x a.1.toNat a.2) else 0

/-- On the source grid the extended mass sequence is exactly the starting-cell mass. -/
theorem positionMassSequence_embed (nu : Measure Point) (c : Clock) (s x : ℝ) (a : ℕ × ℤ) :
    positionMassSequence nu c s x (positionIndexEmbedding a) =
      nu (enlargedStartCell c s x a.1 a.2) := by
  simp [positionMassSequence, positionIndexEmbedding, Int.natCast_nonneg, Int.toNat_natCast]


/-- The source overlap weight is bounded by the same summable two-index majorant. -/
theorem positionOverlapWeight_le (c₀ : ℝ) (hc₀ : 0 < c₀) (i j : ℕ) (ell k : ℤ) :
    positionOverlapWeight c₀ i j ell k ≤ ENNReal.ofReal (Real.exp (2 * c₀)) *
      ENNReal.ofReal (positionYoungKernel (c₀ / 12)
        (positionIndexEmbedding (i, ell) - positionIndexEmbedding (j, k))) := by
  unfold positionOverlapWeight
  split
  · rename_i hover
    have hj : (j : ℝ) ≤ (i : ℝ) := by exact_mod_cast hover.1
    have h := position_overlap_majorant c₀ ((i : ℝ) - (j : ℝ))
      ((ell - k : ℤ) : ℝ) hc₀ (sub_nonneg.mpr hj) hover.2
    apply (ENNReal.ofReal_le_ofReal h).trans_eq
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
    simp only [positionYoungKernel, positionIndexEmbedding, Prod.fst_sub, Prod.snd_sub,
      Int.cast_sub, Int.cast_natCast]
  · exact zero_le



/-- The source overlap q-power sum is bounded by the starting-mass q-power sum. -/
theorem position_overlap_power_sum (c₀ : ℝ) (hc₀ : 0 < c₀)
    (nu : Measure Point) (c : Clock) (s x q : ℝ) (hq : 1 < q) :
    (∑' b : ℕ × ℤ, (∑' a : ℕ × ℤ,
      positionOverlapWeight c₀ b.1 a.1 b.2 a.2 *
        nu (enlargedStartCell c s x a.1 a.2)) ^ q) ≤
      (ENNReal.ofReal (Real.exp (2 * c₀)) *
        ∑' h, ENNReal.ofReal (positionYoungKernel (c₀ / 12) h)) ^ q *
      ∑' a : ℕ × ℤ, nu (enlargedStartCell c s x a.1 a.2) ^ q   := by
  have position_two_index_young_source (w : ℤ × ℤ → ℝ≥0∞) (a : ℤ × ℤ → ℝ≥0∞) :
      (∑' g, (∑' h, w (g - h) * a h) ^ q) ≤
      (∑' h, w h) ^ q * ∑' g, a g ^ q := by
    have he (g : ℤ × ℤ) : (∑' h, w (g - h) * a h) =
        ∑' h, w h * a (g - h) := by
      have h := (Equiv.subLeft g).tsum_eq (fun h => w (g - h) * a h)
      simpa using h.symm
    simp_rw [he]
    exact position_two_index_young w a q hq
  have positionMassSequence_power_sum (hq : 0 < q) :
      (∑' a : ℤ × ℤ, positionMassSequence nu c s x a ^ q) =
      ∑' a : ℕ × ℤ, nu (enlargedStartCell c s x a.1 a.2) ^ q := by
    rw [ENNReal.tsum_prod', ENNReal.tsum_prod',
      tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable]
    have hpos : (∑' n : ℕ, ∑' k : ℤ, positionMassSequence nu c s x ((n : ℤ), k) ^ q) =
        ∑' n : ℕ, ∑' k : ℤ, nu (enlargedStartCell c s x n k) ^ q := by
      simp [positionMassSequence, Int.natCast_nonneg, Int.toNat_natCast]
    have hneg : (∑' n : ℕ, ∑' k : ℤ,
        positionMassSequence nu c s x (-((n : ℤ) + 1), k) ^ q) = 0 := by
      have hn (n : ℕ) : ¬(0 ≤ -((n : ℤ) + 1)) := by omega
      simp only [positionMassSequence, hn, ite_false, ENNReal.zero_rpow_of_pos hq, tsum_zero]
    rw [hpos, hneg, add_zero]
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
      mul_le_mul_right (position_two_index_young_source w a) _
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ q),
        positionMassSequence_power_sum (by linarith)]



/-- A finite starting measure has a finite q-power sum, bounded by its total mass to q. -/
theorem enlargedStartCell_power_sum_le (nu : Measure Point) (c : Clock) (s x q : ℝ)
    (hq : 1 ≤ q) (hnu : ∀ᵐ e ∂nu, s ≤ e.time) :
    (∑' a : ℕ × ℤ, nu (enlargedStartCell c s x a.1 a.2) ^ q) ≤ (nu univ) ^ q  := by
  have enlargedStartCell_mass_sum :
      (∑' a : ℕ × ℤ, nu (enlargedStartCell c s x a.1 a.2)) = nu univ := by
    simpa using (congrArg (fun m => m univ) (enlargedStartCell_measure_sum nu c s x hnu)).symm
  calc
    _ ≤ ∑' a : ℕ × ℤ, (nu univ) ^ (q - 1) *
        nu (enlargedStartCell c s x a.1 a.2) := by
      apply ENNReal.tsum_le_tsum
      intro a
      rw [← position_rpow_sub_one_mul _ q hq]
      exact mul_le_mul_left (ENNReal.rpow_le_rpow (measure_mono (subset_univ _))
        (sub_nonneg.mpr hq)) _
    _ = (nu univ) ^ (q - 1) * nu univ := by
      rw [ENNReal.tsum_mul_left, enlargedStartCell_mass_sum]
    _ = _ := position_rpow_sub_one_mul _ q hq



/-- The real representative has exactly the original positive density and power integral. -/
theorem position_density_real {X : Type*} [MeasurableSpace X]
    (m mu : Measure X) [IsFiniteMeasure mu] (F : X → ℝ≥0∞) (hF : Measurable F)
    (hd : m.withDensity F = mu) (q : ℝ) :
    Measurable (fun x => (F x).toReal) ∧ (∀ x, 0 ≤ (F x).toReal) ∧
      mu = m.withDensity (fun x => ENNReal.ofReal (F x).toReal) ∧
      (∫⁻ x, ‖(F x).toReal‖ₑ ^ q ∂m) = ∫⁻ x, F x ^ q ∂m  := by
  have position_density_finite :
      ∀ᵐ x ∂m, F x ≠ ⊤ := by
    have hi : (∫⁻ x, F x ∂m) ≠ ⊤ := by
      have he : (m.withDensity F) univ = ∫⁻ x, F x ∂m := by
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      rw [← he, hd]
      exact measure_ne_top _ _
    exact (ae_lt_top hF hi).mono (fun _ h => h.ne)
  have hf := position_density_finite
  refine ⟨hF.ennreal_toReal, fun _ => ENNReal.toReal_nonneg, ?_, ?_⟩
  · rw [← hd]
    apply withDensity_congr_ae
    exact hf.mono (fun _ h => (ENNReal.ofReal_toReal h).symm)
  · apply lintegral_congr_ae
    filter_upwards [hf] with x hx
    rw [Real.enorm_toReal hx]

/-- The actual active mixture has a real density with precisely the source power bound. -/
theorem position_density_sum (hpush : PushforwardStatement) (htail : RestartTailStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (q : ℝ) (hq : 1 < q ∧ q < 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
      (c : Clock) (_hc : |c.vbar| = 2 * c.r) (s x : ℝ)
      (nu : Measure Point) [IsFiniteMeasure nu],
      (∀ᵐ e ∂nu, s ≤ e.time ∧ e.velocity 0 ∈ c.active) →
      ∃ G : Point → ℝ, Measurable G ∧ (∀ z, 0 ≤ G z) ∧
        enlargedActiveGreen hH hLE hlam hLam A c nu =
          volume.withDensity (fun z => ENNReal.ofReal (G z)) ∧
        MemLp G (ENNReal.ofReal q) volume ∧
        (∫⁻ z, ‖G z‖ₑ ^ q ∂volume) ≤ ENNReal.ofReal (C * c.r ^ (6 - 4 * q)) *
          ∑' a : ℕ × ℤ, nu (enlargedStartCell c s x a.1 a.2) ^ q  := by
  have position_density_power_sum :
      ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
      (c : Clock) (_hc : |c.vbar| = 2 * c.r) (s x : ℝ)
      (nu : Measure Point) [IsFiniteMeasure nu],
      (∀ᵐ e ∂nu, s ≤ e.time ∧ e.velocity 0 ∈ c.active) →
      (∫⁻ z, positionMixtureDensity hH hLE hlam hLam A c nu z ^ q ∂volume) ≤
        ENNReal.ofReal (C * c.r ^ (6 - 4 * q)) *
          ∑' a : ℕ × ℤ, nu (enlargedStartCell c s x a.1 a.2) ^ q := by
    obtain ⟨C, c₀, hC, hc₀, hd⟩ :=
      position_density_convolution_positive hpush htail hH hLE hlam hLam q hq
    let W := ∑' h, positionYoungKernel (c₀ / 12) h
    have hs := positionYoungKernel_summable (c₀ / 12) (by linarith)
    have hw (h : ℤ × ℤ) : 0 ≤ positionYoungKernel (c₀ / 12) h :=
      mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    have hW := hs.tsum_pos (fun _ => hw _) (0, 0) (by
      exact mul_pos (Real.exp_pos _) (Real.exp_pos _))
    let D := C * Real.exp (2 * c₀) * W
    have hD : 0 < D := mul_pos (mul_pos hC (Real.exp_pos _)) hW
    refine ⟨D ^ q, Real.rpow_pos_of_pos hD q, ?_⟩
    intro A c hc s x nu hfinite hnu
    have hq0 : 0 < q := by linarith [hq.1]
    rw [positionMixtureDensity_power_partition hpush hH hLE hlam hLam A c hc nu s x q hq0 hnu]
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
        rw [← ((ENNReal.ofReal_tsum_of_nonneg hw hs).symm)]
        exact mul_le_mul_right (position_overlap_power_sum c₀ hc₀ nu c s x q hq.1) _
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
  obtain ⟨C, hC, hd⟩ := position_density_power_sum
  refine ⟨C, hC, ?_⟩
  intro A c hc s x nu hfinite hnu
  have hq0 : 0 < q := by linarith [hq.1]
  let F := positionMixtureDensity hH hLE hlam hLam A c nu
  have : IsFiniteMeasure (enlargedActiveGreen hH hLE hlam hLam A c nu) := by
    unfold enlargedActiveGreen
    infer_instance
  obtain ⟨hG, hG0, hGd, hGi⟩ := position_density_real volume
    (enlargedActiveGreen hH hLE hlam hLam A c nu) F (measurable_positionMixtureDensity hH hLE hlam hLam A c nu) (withDensity_positionMixtureDensity hpush hH hLE hlam hLam A c nu) q
  have hbound := hd A c hc s x nu hnu
  have hsumfinite :=
    (enlargedStartCell_power_sum_le nu c s x q hq.1.le (hnu.mono (fun _ h => h.1))).trans_lt (ENNReal.rpow_lt_top_of_nonneg (by linarith [hq.1]) (measure_ne_top _ _))
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

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

