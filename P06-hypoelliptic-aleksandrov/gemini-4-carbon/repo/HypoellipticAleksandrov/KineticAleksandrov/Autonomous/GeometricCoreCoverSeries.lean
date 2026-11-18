module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BelowFourBandStatement
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FarVelocityDensityDomination
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter
open scoped ENNReal

/-- The source geometric centre magnitudes, 8R(7/8)^j. -/
def geometricCoreScale (R : ℝ) (j : ℕ) : ℝ := 8 * R * (7 / 8 : ℝ) ^ j

/-- Every source centre magnitude is positive. -/
theorem geometricCoreScale_pos (R : ℝ) (hR : 0 < R) (j : ℕ) :
    0 < geometricCoreScale R j := by unfold geometricCoreScale; positivity

/-- The source positive and negative clock data have radius half the centre magnitude. -/
def geometricCoreClock (R : ℝ) (hR : 0 < R) (j : ℕ) (positive : Bool) : Clock where
  vbar := if positive then geometricCoreScale R j else -geometricCoreScale R j
  r := geometricCoreScale R j / 2
  nonzero := by split <;> have h := geometricCoreScale_pos R hR j <;> linarith
  positive := by have h := geometricCoreScale_pos R hR j; positivity
  radius := by
    have h := geometricCoreScale_pos R hR j
    split <;> simp only [abs_of_pos h, abs_neg] <;> linarith

/-- The source signed geometric clocks satisfy the band-centre relation. -/
theorem geometricCoreClock_center (R : ℝ) (hR : 0 < R) (j : ℕ) (s : Bool) :
    |(geometricCoreClock R hR j s).vbar| = 2 * (geometricCoreClock R hR j s).r := by
  cases s <;> simp [geometricCoreClock, Bool.false_eq_true, abs_neg, abs_of_pos (geometricCoreScale_pos R hR j)] <;> ring

/-- Every geometric band radius is at most 4R, hence within the allowed 6R. -/
theorem geometricCoreClock_radius (R : ℝ) (hR : 0 < R) (j : ℕ) (s : Bool) :
    (geometricCoreClock R hR j s).r ≤ 6 * R := by
  have hj : (7 / 8 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  change 8 * R * (7 / 8 : ℝ) ^ j / 2 ≤ 6 * R
  nlinarith


/-- The actual closed cores cover both signs of every nonzero velocity up to 9R. -/
theorem geometricCoreClock_covers (R v : ℝ) (hR : 0 < R) (hv : v ≠ 0)
    (hupper : |v| ≤ 9 * R) :
    ∃ j : ℕ, ∃ s : Bool, v ∈ (geometricCoreClock R hR j s).core  := by
  have geometricCoreScale_covers (v : ℝ) (hR : 0 < R) (hv : 0 < v) (hupper : v ≤ 9 * R) :
      ∃ j : ℕ, geometricCoreScale R j * (7 / 8) ≤ v ∧
      v ≤ geometricCoreScale R j * (9 / 8) := by
    have hex : ∃ j : ℕ, geometricCoreScale R j * (7 / 8) ≤ v := by
      obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (show 0 < v / (8 * R) by positivity)
        (show (7 / 8 : ℝ) < 1 by norm_num)
      refine ⟨j, ?_⟩
      have hj' : 8 * R * (7 / 8 : ℝ) ^ j < v :=
        by
        simpa only [mul_comm] using
          (lt_div_iff₀ (by positivity : 0 < 8 * R)).mp hj
      have hp := pow_nonneg (show 0 ≤ 7 / 8 by norm_num) j
      unfold geometricCoreScale
      nlinarith
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    cases hn : Nat.find hex with
    | zero => simp [geometricCoreScale]; linarith
    | succ j =>
      have hj : ¬geometricCoreScale R j * (7 / 8) ≤ v :=
        Nat.find_min hex (by omega)
      have he : geometricCoreScale R (j + 1) = geometricCoreScale R j * (7 / 8) := by
        simp only [geometricCoreScale, pow_succ]; ring
      rw [he]
      linarith
  obtain ⟨j, hl, hu⟩ := geometricCoreScale_covers |v| hR (abs_pos.mpr hv) hupper
  refine ⟨j, ?_⟩
  rcases lt_or_gt_of_ne hv with hneg | hpos
  · refine ⟨false, ?_⟩
    rw [abs_of_neg hneg] at hl hu
    change -geometricCoreScale R j - (geometricCoreScale R j / 2) / 4 ≤ v ∧
      v ≤ -geometricCoreScale R j + (geometricCoreScale R j / 2) / 4
    constructor <;> linarith
  · refine ⟨true, ?_⟩
    rw [abs_of_pos hpos] at hl hu
    change geometricCoreScale R j - (geometricCoreScale R j / 2) / 4 ≤ v ∧
      v ≤ geometricCoreScale R j + (geometricCoreScale R j / 2) / 4
    constructor <;> linarith

/-- The characterized Bellman degree forces exactly the positive geometric exponent. -/
theorem belowFour_exponent_range (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (alpha q : ℝ)
    (ha : bellmanAdjointExponent (Lam / lam) ((le_div_iff₀ hlam).2
      (by simpa only [one_mul] using hLam)) - 2 < alpha ∧ alpha < 1)
    (hq : 1 < q ∧ q < (4 - (1 - alpha)) / (3 - (1 - alpha))) :
    0 < alpha ∧ q < 3 / 2 ∧ 0 < 4 - 3 * q + (1 - alpha) * (q - 1) := by
  have ha0 : 0 < alpha := by linarith [(bellmanAdjointExponent_range (Lam / lam) ((le_div_iff₀ hlam).2 (by simpa using hLam))).1, ha.1]
  have hd : 0 < 3 - (1 - alpha) := by linarith
  have hq' := (lt_div_iff₀ hd).mp hq.2
  refine ⟨ha0, ?_, ?_⟩ <;> nlinarith [ha.2]


/-- A finite absolutely continuous measure has a nonnegative measurable real density. -/
theorem density_of_absolutelyContinuous {X : Type*} [MeasurableSpace X]
    (m ν : Measure X) [SigmaFinite m] [IsFiniteMeasure ν] (hac : ν ≪ m) :
    ∃ g : X → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x) ∧
      ν = m.withDensity (fun x => ENNReal.ofReal (g x)) := by
  let g := fun x => (ν.rnDeriv m x).toReal
  refine ⟨g,
    (Measure.measurable_rnDeriv ν m).ennreal_toReal,
    fun _ => ENNReal.toReal_nonneg, ?_⟩
  rw [← Measure.withDensity_rnDeriv_eq ν m hac]
  apply withDensity_congr_ae
  filter_upwards [Measure.rnDeriv_lt_top ν m] with x hx
  exact (ENNReal.ofReal_toReal hx.ne).symm

/-- A local density dominates the same restriction of any global nonnegative density. -/
theorem density_local_norm_le {X : Type*} [MeasurableSpace X]
    (m : Measure X) [SigmaFinite m] (g f : X → ℝ)
    (hgm : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (_hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (S : Set X) (hS : MeasurableSet S) (p : ℝ≥0∞)
    (hle : (m.withDensity (fun x => ENNReal.ofReal (g x))).restrict S ≤
      m.withDensity (fun x => ENNReal.ofReal (f x))) :
    eLpNorm g p (m.restrict S) ≤ eLpNorm f p m := by
  have hle' : (m.restrict S).withDensity (fun x => ENNReal.ofReal (g x)) ≤
      (m.restrict S).withDensity (fun x => ENNReal.ofReal (f x)) := by
    rw [← restrict_withDensity hS, ← restrict_withDensity hS]
    simpa only [Measure.restrict_restrict hS, inter_self] using
      Measure.restrict_mono_measure hle S
  have hgf : ∀ᵐ x ∂m.restrict S, ENNReal.ofReal (g x) ≤ ENNReal.ofReal (f x) := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀
      hgm.ennreal_ofReal.aemeasurable.restrict
    intro E hE _
    have h := Measure.le_iff.1 hle' E hE
    rwa [withDensity_apply _ hE, withDensity_apply _ hE] at h
  have hn : ∀ᵐ x ∂m.restrict S, ‖g x‖ ≤ ‖f x‖ := by
    filter_upwards [hgf] with x hx
    simpa [abs_of_nonneg (hg0 x), abs_of_nonneg (hf0 x)]
      using (ENNReal.ofReal_le_ofReal_iff (hf0 x)).mp hx
  exact (eLpNorm_mono_ae hgm.aestronglyMeasurable.restrict hn).trans
    (eLpNorm_restrict_le f p m S)

/-- A source real norm bound gives the equivalent bound for its q-power integral. -/
theorem density_power_integral_le {X : Type*} [MeasurableSpace X]
    (m : Measure X) (f : X → ℝ) (q K : ℝ) (hq : 0 < q) (hK : 0 ≤ K)
    (hf : MemLp f (ENNReal.ofReal q) m)
    (hn : (eLpNorm f (ENNReal.ofReal q) m).toReal ≤ K ^ (1 / q)) :
    ∫⁻ x, ‖f x‖ₑ ^ q ∂m ≤ ENNReal.ofReal K := by
  have he : ∫⁻ x, ‖f x‖ₑ ^ q ∂m = eLpNorm f (ENNReal.ofReal q) m ^ q := by
    rw [eLpNorm_eq_eLpNorm' (by positivity) ENNReal.ofReal_ne_top
      hf.aestronglyMeasurable, ENNReal.toReal_ofReal hq.le]
    exact lintegral_rpow_enorm_eq_rpow_eLpNorm' hq
  rw [he]
  calc
    _ ≤ ENNReal.ofReal (K ^ (1 / q)) ^ q := ENNReal.rpow_le_rpow ((ENNReal.le_ofReal_iff_toReal_le hf.ne (Real.rpow_nonneg hK _)).2 hn) hq.le
    _ = ENNReal.ofReal K := by
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hK _) hq.le,
        ← Real.rpow_mul hK, one_div_mul_cancel hq.ne', Real.rpow_one]

/-- Local densities on a countable cover glue, with a bound by the sum of power integrals. -/
theorem density_of_countable_cover {X ι : Type*} [MeasurableSpace X] [Countable ι]
    (m ν : Measure X) [SigmaFinite m] [IsFiniteMeasure ν]
    (S : ι → Set X) (hS : ∀ i, MeasurableSet (S i))
    (hcover : ν (⋃ i, S i)ᶜ = 0)
    (f : ι → X → ℝ) (hfm : ∀ i, Measurable (f i)) (hf0 : ∀ i x, 0 ≤ f i x)
    (q : ℝ) (hq : 0 < q)
    (hle : ∀ i, ν.restrict (S i) ≤ m.withDensity (fun x => ENNReal.ofReal (f i x))) :
    ∃ g : X → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x) ∧
      ν = m.withDensity (fun x => ENNReal.ofReal (g x)) ∧
      (∫⁻ x, ‖g x‖ₑ ^ q ∂m) ≤ ∑' i, ∫⁻ x, ‖f i x‖ₑ ^ q ∂m := by
  have hac : ν ≪ m := by
    intro E hE
    have hz : ∀ i, ν (E ∩ S i) = 0 := by
      intro i
      have hi0 := (hle i).absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _) hE
      simpa only [Measure.restrict_apply' (hS i)] using hi0
    have hu : ν (E ∩ ⋃ i, S i) = 0 := by
      rw [inter_iUnion]
      exact measure_iUnion_null hz
    apply measure_mono_null (t := (E ∩ ⋃ i, S i) ∪ (⋃ i, S i)ᶜ)
    · intro x hx
      by_cases hs : x ∈ ⋃ i, S i
      · exact Or.inl ⟨hx, hs⟩
      · exact Or.inr hs
    · exact measure_union_null hu hcover
  obtain ⟨g, hgm, hg0, hgd⟩ := density_of_absolutelyContinuous m ν hac
  have hout : ∀ᵐ x ∂m.restrict (⋃ i, S i)ᶜ, g x = 0 := by
    have hz : ∫⁻ x in (⋃ i, S i)ᶜ, ENNReal.ofReal (g x) ∂m = 0 := by
      rw [← withDensity_apply _ (MeasurableSet.iUnion hS).compl, ← hgd, hcover]
    have hz' := (lintegral_eq_zero_iff' hgm.ennreal_ofReal.aemeasurable.restrict).mp hz
    filter_upwards [hz'] with x hx
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp hx) (hg0 x)
  have hpout : ∫⁻ x in (⋃ i, S i)ᶜ, ‖g x‖ₑ ^ q ∂m = 0 := by
    rw [← lintegral_zero (μ := m.restrict (⋃ i, S i)ᶜ)]
    apply lintegral_congr_ae
    filter_upwards [hout] with x hx
    simp only [hx, enorm_zero, ENNReal.zero_rpow_of_pos hq]
  refine ⟨g, hgm, hg0, hgd, ?_⟩
  have hint : ∫⁻ x, ‖g x‖ₑ ^ q ∂m = ∫⁻ x in ⋃ i, S i, ‖g x‖ₑ ^ q ∂m := by
    rw [← lintegral_add_compl _ (MeasurableSet.iUnion hS), hpout, add_zero]
  rw [hint]
  apply (lintegral_iUnion_le S _).trans
  apply ENNReal.tsum_le_tsum
  intro i
  have hn := density_local_norm_le m g (f i) hgm hg0 (hfm i) (hf0 i)
    (S i) (hS i) (ENNReal.ofReal q) (hgd ▸ hle i)
  have hfme := (hfm i).aestronglyMeasurable (μ := m)
  rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' hq,
    lintegral_rpow_enorm_eq_rpow_eLpNorm' hq]
  have he (u : X → ℝ) (μ : Measure X) (hu : AEStronglyMeasurable u μ) :
      eLpNorm u (ENNReal.ofReal q) μ = eLpNorm' u q μ := by
    rw [eLpNorm_eq_eLpNorm' (by positivity) ENNReal.ofReal_ne_top hu,
      ENNReal.toReal_ofReal hq.le]
  rw [he g _ (hgm.aestronglyMeasurable (μ := m.restrict (S i))), he (f i) _ hfme] at hn
  exact ENNReal.rpow_le_rpow hn hq.le


/-- The positive geometric power appearing in the source cover. -/
def geometricBandPower (delta : ℝ) (j : ℕ) : ℝ :=
  (4 * (7 / 8 : ℝ) ^ j) ^ delta

/-- The geometric band powers are summable exactly in the positive-exponent regime. -/
theorem geometricBandPower_summable (delta : ℝ) (hd : 0 < delta) :
    Summable (geometricBandPower delta) := by
  have he (j : ℕ) : geometricBandPower delta j =
      4 ^ delta * ((7 / 8 : ℝ) ^ delta) ^ j := by
    unfold geometricBandPower
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num), mul_comm (j : ℝ) delta,
      Real.rpow_mul (by norm_num), Real.rpow_natCast]
  rw [(funext he)]
  apply Summable.mul_left
  apply summable_geometric_of_lt_one
  · positivity
  · exact Real.rpow_lt_one (by norm_num) (by norm_num) hd

/-- The geometric band sum is strictly positive. -/
theorem geometricBandPower_tsum_pos (delta : ℝ) (hd : 0 < delta) :
    0 < ∑' j, geometricBandPower delta j := by
  exact (geometricBandPower_summable delta hd).tsum_pos
    (fun j => by unfold geometricBandPower; positivity) 0
    (by unfold geometricBandPower; positivity)

/-- Sum both velocity signs, retaining the source uniform power of R. -/
theorem geometricBandPower_sum (C R delta k : ℝ) (hC : 0 ≤ C) (hR : 0 < R)
    (hd : 0 < delta) :
    (∑' i : Bool × ℕ, ENNReal.ofReal (C * R ^ k * geometricBandPower delta i.2)) =
      ENNReal.ofReal (2 * C * (∑' j, geometricBandPower delta j) * R ^ k) := by
  have hs := (geometricBandPower_summable delta hd).mul_left (C * R ^ k)
  have hn (j : ℕ) : 0 ≤ C * R ^ k * geometricBandPower delta j := by
    unfold geometricBandPower; positivity
  rw [ENNReal.tsum_prod']
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_bool, two_nsmul]
  rw [← ENNReal.ofReal_tsum_of_nonneg hn hs, ← ENNReal.ofReal_add (tsum_nonneg hn)
    (tsum_nonneg hn), tsum_mul_left]
  congr 1
  ring

/-- A finite q-power integral bound yields the source real Lq norm bound. -/
theorem density_norm_of_power_bound {X : Type*} [MeasurableSpace X]
    (m : Measure X) (g : X → ℝ) (hgm : Measurable g)
    (q K : ℝ) (hq : 0 < q) (hK : 0 ≤ K)
    (hint : ∫⁻ x, ‖g x‖ₑ ^ q ∂m ≤ ENNReal.ofReal K) :
    MemLp g (ENNReal.ofReal q) m ∧
      (eLpNorm g (ENNReal.ofReal q) m).toReal ≤ K ^ (1 / q) := by
  have he : eLpNorm g (ENNReal.ofReal q) m =
      (∫⁻ x, ‖g x‖ₑ ^ q ∂m) ^ (1 / q) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top
      hgm.aestronglyMeasurable, ENNReal.toReal_ofReal hq.le]
  have hn : eLpNorm g (ENNReal.ofReal q) m ≤ ENNReal.ofReal (K ^ (1 / q)) := by
    rw [he]
    exact (ENNReal.rpow_le_rpow hint (by positivity)).trans_eq
      (ENNReal.ofReal_rpow_of_nonneg hK (by positivity))
  refine ⟨hn.trans_lt ENNReal.ofReal_lt_top, ?_⟩
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hn).trans_eq
    (ENNReal.toReal_ofReal (Real.rpow_nonneg hK _))

/-- Taking the q-th root gives exactly the homogeneous source power 6/q-4. -/
theorem geometricBandPower_root (C R delta q : ℝ) (hC : 0 ≤ C) (hR : 0 < R)
    (hd : 0 < delta) (hq : 0 < q) :
    (2 * C * (∑' j, geometricBandPower delta j) * R ^ (6 - 4 * q)) ^ (1 / q) =
      (2 * C * (∑' j, geometricBandPower delta j)) ^ (1 / q) * R ^ (6 / q - 4) := by
  have hs := (geometricBandPower_tsum_pos delta hd).le
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hR.le]
  congr 2
  field_simp

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

