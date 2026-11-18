module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionVisitsStatement
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitsPieces
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumReal
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationStatement
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FarVelocityDensityDomination
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripGreen
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationWaiting
import Mathlib.MeasureTheory.Integral.Prod
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PushforwardStatement
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonOrder
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceStatement
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GeometricCoreCoverSeries
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PoleDensityStatement
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SmoothABPPotentials
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ABPAbstract
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.SmoothEstimateReflection
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SmoothAutonomousP6Statement
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomousAdmissibilitySource
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonLinear
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonConstant
import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryTopology
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionCells
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassCanonical
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionCellCount
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionVisitSumHorizon
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceLimitsInfinite
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TailRestartDensity

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter ProbabilityTheory HypoellipticAleksandrov Parabolic Holder
open scoped ENNReal

/-- Finiteness, cell definitions, total count, and active domination for positioned visits. -/
def PositionVisitMassesStatement : Prop :=
  ∀ (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam),
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (J : Interval) (R T : ℝ) (P : Point),
      0 < R → ∀ (_hT : 0 < T), T ≤ R ^ 2 → |c.vbar| = 2 * c.r →
      ∀ (_hJ : closure c.active ⊆ J.carrier)
        (_hvel : P.velocity 0 ∈ closure c.entrance),
      let nu := visitsFromZero hH hLE hlam hLam A c J T P
      IsFiniteMeasure nu ∧
      (∀ᵐ p ∂nu, P.time ≤ p.time ∧ p.time < P.time + T ∧ p.velocity 0 ∈ closure c.entrance) ∧
      nu univ ≤ ENNReal.ofReal (C * (1 + R / c.r)) ∧
      (∀ j : ℕ, (∑' k : ℤ, enlargedPositionVisitMass nu c P.time 0 j k) =
        enlargedTimeVisitMass nu c P.time j) ∧
      (∀ N : ℕ,
        (∑ n ∈ Finset.range N, enlargedActivePiece hH hLE hlam hLam A c J P.time (P.time + T) P n) ≤
          enlargedFullSpaceOccupation hH hLE hlam hLam A P T) ∧
      (∀ (N : ℕ) (b : ℝ), P.time ≤ b → b ≤ P.time + T →
        enlargedActiveTerminal hH hLE hlam hLam A c J P.time (P.time + T) P N b ≤
          enlargedFullSpaceTerminal hH hLE hlam hLam A P b)



/-- The visit-sum factor converts to the exact relative-radius power, uniformly up to `6R`. -/
theorem coreStartBand_scaling (r R a eta : ℝ) (hr : 0 < r) (hR : 0 < R)
    (heta : 0 ≤ eta) (hscale : r ≤ 6 * R) :
    r ^ a * (1 + R / r) ^ eta ≤
      7 ^ eta * R ^ a * (r / R) ^ (a - eta) := by
  have hu := div_pos hr hR
  have hbase : 1 + R / r ≤ 7 * (R / r) := by
    have h : 1 ≤ 6 * (R / r) := by
      rw [← mul_div_assoc]
      exact (le_div_iff₀ hr).2 (by simpa using hscale)
    linarith
  have heq : r ^ a * (7 * (R / r)) ^ eta =
      7 ^ eta * R ^ a * (r / R) ^ (a - eta) := by
    have hrrep : r = R * (r / R) := by field_simp
    have hinv : R / r = (r / R)⁻¹ := by field_simp
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 7) (by positivity), hinv,
      Real.inv_rpow hu.le, ← Real.rpow_neg hu.le]
    nth_rw 1 [hrrep]
    rw [Real.mul_rpow hR.le hu.le]
    calc
      _ = 7 ^ eta * R ^ a * ((r / R) ^ a * (r / R) ^ (-eta)) := by ring
      _ = 7 ^ eta * R ^ a * (r / R) ^ (a - eta) := by
        rw [← Real.rpow_add hu]
        simp only [sub_eq_add_neg]

  exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity : 0 ≤ 1 + R / r) hbase heta) (Real.rpow_nonneg hr.le a)).trans_eq heq


/-- The closed entrance band lies strictly inside the active band. -/
theorem enlargedEntrance_subset_active (c : Clock) : closure c.entrance ⊆ c.active := by
  rw [Clock.entrance, closure_Ioo (by linarith [c.positive])]
  intro v hv
  change c.vbar - 3 * c.r / 4 < v ∧ v < c.vbar + 3 * c.r / 4
  constructor <;> linarith [hv.1, hv.2, c.positive]




/-- A literal bounded outer interval containing both closed velocity intervals. -/
def coreStartOuterInterval (H : Interval) (c : Clock) : Interval where
  lo := min H.lo c.activeInterval.lo - 1
  hi := max H.hi c.activeInterval.hi + 1
  ordered := by
    have hl := min_le_left H.lo c.activeInterval.lo
    have hh := le_max_left H.hi c.activeInterval.hi
    linarith [H.ordered]

/-- The observation interval lies inside the chosen bounded outer interval. -/
theorem coreStartOuterInterval_contains (H : Interval) (c : Clock) :
    H.carrier ⊆ (coreStartOuterInterval H c).carrier := by
  intro v hv
  change min H.lo c.activeInterval.lo - 1 < v ∧ v < max H.hi c.activeInterval.hi + 1
  constructor
  · linarith [hv.1, min_le_left H.lo c.activeInterval.lo]
  · linarith [hv.2, le_max_left H.hi c.activeInterval.hi]

/-- The closed active interval lies strictly inside the chosen bounded outer interval. -/
theorem coreStartOuterInterval_contains_active (H : Interval) (c : Clock) :
    closure c.active ⊆ (coreStartOuterInterval H c).carrier := by
  change closure (Ioo c.activeInterval.lo c.activeInterval.hi) ⊆ _
  rw [closure_Ioo c.activeInterval.ordered.ne]
  intro v hv
  change min H.lo c.activeInterval.lo - 1 < v ∧ v < max H.hi c.activeInterval.hi + 1
  constructor
  · linarith [hv.1, min_le_right H.lo c.activeInterval.lo]
  · linarith [hv.2, le_max_right H.hi c.activeInterval.hi]

/-- The improved core-start norm is uniform in all positions and starting times in the strip. -/
theorem below_four_core_start_band (hpush : PushforwardStatement)
    (htail : RestartTailStatement) (hvisits : PositionVisitsStatement)
    (hmasses : PositionVisitMassesStatement) (hcore : CoreDominationStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (alpha q : ℝ)
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
            (c.r / R) ^ (4 - 3 * q + (1 - alpha) * (q - 1))) ^ (1 / q)  := by
  have core_start_visit_density :
      ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
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
    have enlargedVisit_power_sum_eq (nu : Measure Point) [IsFiniteMeasure nu] (c : Clock) (s : ℝ) (hq : 0 < q) (hnu : ∀ᵐ p ∂nu, p.velocity 0 ∈ closure c.entrance) :
        (∑' a : ℕ × ℤ, nu (enlargedStartCell c s 0 a.1 a.2) ^ q) =
        ∑' j : ℕ, ∑' k : ℤ, ENNReal.ofReal (enlargedPositionVisitMass nu c s 0 j k ^ q) := by
      rw [ENNReal.tsum_prod']
      apply tsum_congr
      intro j
      apply tsum_congr
      intro k
      rw [enlargedPositionVisitMass_eq_startCellMass nu c s 0 j k hnu]
      unfold enlargedStartCellMass
      rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hq.le,
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
    have coreStartBand_exponent :
        (6 - 4 * q) - (1 - (2 - alpha) * (q - 1)) =
        4 - 3 * q + (1 - alpha) * (q - 1) := by
      ring
    obtain ⟨Cd, hCd, hd⟩ := position_density_sum hpush htail hH hLE hlam hLam q hq
    obtain ⟨Cv, hCv, hv⟩ := (hvisits hH hLE lam Lam hlam hLam alpha ha).2 q hq
    obtain ⟨Cm, _, hm⟩ := hmasses hH hLE lam Lam hlam hLam
    let eta := 1 - (2 - alpha) * (q - 1)
    have ha0 : 0 < alpha := by dsimp [enlargedAdmissibleAlpha] at ha; linarith [ha.1, (bellmanAdjointExponent_range (Lam / lam) ((le_div_iff₀ hlam).2 (by simpa using hLam))).1]
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
    rw [enlargedVisit_power_sum_eq nu c P.time (by linarith) (hp.2.1.mono (fun _ h => h.2.2))]
      at hGi
    have hscale := coreStartBand_scaling c.r R (6 - 4 * q) eta c.positive hR heta hr
    rw [coreStartBand_exponent] at hscale
    let K := C * R ^ (6 - 4 * q) * (c.r / R) ^
      (4 - 3 * q + (1 - alpha) * (q - 1))
    have hK : 0 ≤ K :=
      mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hR.le _))
        (Real.rpow_nonneg (div_pos c.positive hR).le _)
    have hi : (∫⁻ z, ‖G z‖ₑ ^ q ∂volume) ≤ ENNReal.ofReal K := by
      apply hGi.trans
      apply (mul_le_mul_right (hv A c J R T P hR hT hTR hc hJ hvel) _).trans
      rw [← ENNReal.ofReal_mul (mul_nonneg hCd.le (Real.rpow_nonneg c.positive.le _))]
      apply ENNReal.ofReal_le_ofReal
      have he : Cd * c.r ^ (6 - 4 * q) * (Cv * (1 + R / c.r) ^ eta) =
          (Cd * Cv) * (c.r ^ (6 - 4 * q) * (1 + R / c.r) ^ eta) := by ring
      rw [he]
      exact (mul_le_mul_of_nonneg_left hscale (mul_nonneg hCd.le hCv.le)).trans_eq
        (by dsimp [K, C]; ring)
    obtain ⟨_, hnorm⟩ := density_norm_of_power_bound volume G hG q K (by linarith) hK hi
    exact ⟨G, hG, hG0, hGd, hGp, hnorm⟩
  obtain ⟨C, hC, hd⟩ := core_start_visit_density
  refine ⟨C, hC, ?_⟩
  intro A c H s R hR e hs he hc hr
  let J := coreStartOuterInterval H c
  let T := s + R ^ 2 - e.1.time
  have htR : T ≤ R ^ 2 := by dsimp [T]; linarith
  have hJ := coreStartOuterInterval_contains_active H c
  obtain ⟨G, hG, hG0, hGd, hGp, hGn⟩ := hd A c J R T e.1 hR (sub_pos.mpr (WithTop.coe_lt_coe.mp e.2.1)) htR hc hr hJ he
  have hsub := coreStartOuterInterval_contains H c
  have heq : e.1.time + T = s + R ^ 2 := by dsimp [T]; ring
  have hnu : visitsFromZero hH hLE hlam hLam A c J T e.1 =
      enlargedVisitStarts hH hLE hlam hLam A c J e.1.time (s + R ^ 2) e.1 := by
    unfold visitsFromZero
    rw [heq]
  rw [hnu] at hGd
  have hle := (Measure.restrict_mono_measure
    (stripGreen_mono hH hLE hlam hLam A H J hsub
      (s + R ^ 2) (s + R ^ 2) le_rfl e) {z | z.velocity 0 ∈ c.core}).trans (hcore hH hLE lam Lam hlam hLam A c J e.1.time (s + R ^ 2) e.1 ⟨WithTop.coe_lt_coe.mp e.2.1, hsub e.2.2⟩ hc hJ le_rfl).2
  have hdle := hle.trans Measure.restrict_le_self
  rw [hGd] at hdle
  have : SigmaFinite (volume : Measure Point) := density_volume_sigmaFinite
  obtain ⟨g, hgm, hg0, hgd, hgp, hgn⟩ := density_of_le_withDensity volume
    ((stripGreen hH hLE hlam hLam A H (s + R ^ 2) e).restrict
      {z | z.velocity 0 ∈ c.core}) G hG hG0 (ENNReal.ofReal q) hGp hdle
  exact ⟨g, hgm, hg0, hgd, hgp,
    (ENNReal.toReal_mono hGp.ne hgn).trans hGn⟩


/-- Convert a finite positive density norm bound to its real measurable representative. -/
theorem belowFour_real_density_of_positive_bound {X : Type*} [MeasurableSpace X]
    (m mu : Measure X) [IsFiniteMeasure mu] (F : X → ℝ≥0∞) (hF : Measurable F)
    (hd : m.withDensity F = mu) (q K : ℝ) (hq : 0 < q) (hK : 0 ≤ K)
    (hn : positionPositiveNorm m q F ≤ ENNReal.ofReal K) :
    ∃ G : X → ℝ, Measurable G ∧ (∀ x, 0 ≤ G x) ∧
      mu = m.withDensity (fun x => ENNReal.ofReal (G x)) ∧
      MemLp G (ENNReal.ofReal q) m ∧ (eLpNorm G (ENNReal.ofReal q) m).toReal ≤ K := by
  obtain ⟨hG, hG0, hGd, hGi⟩ := position_density_real m mu F hF hd q
  have he : eLpNorm (fun x => (F x).toReal) (ENNReal.ofReal q) m =
      positionPositiveNorm m q F := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ne_of_gt (ENNReal.ofReal_pos.mpr hq)) ENNReal.ofReal_ne_top hG.aestronglyMeasurable,
      ENNReal.toReal_ofReal hq.le, hGi]
    rfl
  refine ⟨fun x => (F x).toReal, hG, hG0, hGd, ?_, ?_⟩
  · change eLpNorm _ _ _ < ⊤
    rw [he]
    exact hn.trans_lt ENNReal.ofReal_lt_top
  · rw [he]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hn).trans_eq
      (ENNReal.toReal_ofReal hK)

/-- Actual kernel mixtures preserve a uniform real Lq density bound under mass at most one. -/
theorem belowFour_density_subprobability_mixture {X : Type*} [MeasurableSpace X]
    [MeasurableSpace.CountableOrCountablyGenerated X Point]
    (nu : Measure X) [IsFiniteMeasure nu] (k : Kernel X Point) [IsFiniteKernel k]
    (q K : ℝ) (hq : 1 < q) (hK : 0 ≤ K) (hnu : nu univ ≤ 1)
    (hbound : ∀ᵐ x ∂nu, ∃ G : Point → ℝ,
      Measurable G ∧ (∀ z, 0 ≤ G z) ∧
      k x = volume.withDensity (fun z => ENNReal.ofReal (G z)) ∧
      MemLp G (ENNReal.ofReal q) volume ∧ (eLpNorm G (ENNReal.ofReal q) volume).toReal ≤ K) :
    ∃ G : Point → ℝ, Measurable G ∧ (∀ z, 0 ≤ G z) ∧
      k ∘ₘ nu = volume.withDensity (fun z => ENNReal.ofReal (G z)) ∧
      MemLp G (ENNReal.ofReal q) volume ∧ (eLpNorm G (ENNReal.ofReal q) volume).toReal ≤ K := by
  have : SigmaFinite (volume : Measure Point) := density_volume_sigmaFinite
  let F := positionKernelDensity k (volume : Measure Point)
  have hF := measurable_positionKernelDensity k (volume : Measure Point)
  have hd : ∀ᵐ x ∂nu, volume.withDensity (F x) = k x := by
    filter_upwards [hbound] with x hx
    obtain ⟨G, _, _, hGd, _, _⟩ := hx
    apply withDensity_positionKernelDensity
    rw [hGd]
    exact withDensity_absolutelyContinuous _ _
  have hp : ∀ᵐ x ∂nu, positionPositiveNorm volume q (F x) ≤ ENNReal.ofReal K := by
    filter_upwards [hbound, hd] with x hx hdx
    obtain ⟨G, hG, hG0, hGd, hGp, hGn⟩ := hx
    simpa using (positionPositiveNorm_of_density_le volume (F x) (hF.comp (measurable_const.prodMk measurable_id)) univ univ MeasurableSet.univ G hG hG0 (by simpa using hdx.trans hGd) q K (by linarith) hK (by simpa using hGp) (by simpa using hGn))
  let M := fun z => ∫⁻ x, F x z ∂nu
  have hM : Measurable M := hF.lintegral_prod_left'
  have hm : volume.withDensity M = k ∘ₘ nu := by
    ext B hB
    rw [withDensity_apply _ hB, Measure.bind_apply hB k.aemeasurable]
    change (∫⁻ z in B, ∫⁻ x, F x z ∂nu ∂volume) = ∫⁻ x, k x B ∂nu
    rw [← lintegral_lintegral_swap (μ := nu) (ν := volume.restrict B)
      (f := F) hF.aemeasurable]
    apply lintegral_congr_ae
    filter_upwards [hd] with x hx
    rw [← withDensity_apply _ hB, hx]
  have hn' :=
    (positionPositiveNorm_mixture_le nu volume F hF q hq (ENNReal.ofReal K) hp).trans ((mul_le_mul_left hnu _).trans_eq (one_mul _))
  exact belowFour_real_density_of_positive_bound volume (k ∘ₘ nu) M hM hm q K
    (by linarith) hK hn'


/-- The native strip Green kernel restricted to the source closed core. -/
def belowFour_coreGreenKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (H : Interval) (T : ℝ) :
    Kernel (StripPole H (T : WithTop ℝ)) Point where
  toFun e := (stripGreen hH hLE hlam hLam A H T e).restrict {z | z.velocity 0 ∈ c.core}
  measurable' := nested_measurable_family_restrict _
    (Measure.measurable_measure.mpr (fun B hB =>
      stripGreen_measurable_apply hH hLE hlam hLam A H T B hB)) _
    (isClosed_Icc.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)

/-- Uniform quadratic strip mass makes the native core Green family a finite kernel. -/
instance belowFour_coreGreenKernel_isFinite
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (H : Interval) (T : ℝ) :
    IsFiniteKernel (belowFour_coreGreenKernel hH hLE hlam hLam A c H T) := by
  refine ⟨ENNReal.ofReal ((H.hi - H.lo) ^ 2 / (2 * lam)), ENNReal.ofReal_lt_top, ?_⟩
  intro e
  apply (Measure.restrict_le_self (μ := stripGreen hH hLE hlam hLam A H T e)
    (s := {z | z.velocity 0 ∈ c.core}) univ).trans
  apply (stripGreen_quadratic_mass hH hLE hlam hLam A H T e).trans
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_div_iff_of_pos_right (by linarith : 0 < 2 * lam)).2
  nlinarith only [sq_nonneg (e.1.velocity 0 - H.lo),
    sq_nonneg (H.hi - e.1.velocity 0), sq_nonneg (H.hi - H.lo)]




/-- The actual core Green measure inherits a uniform entrance-pole bound by first arrival. -/
theorem belowFour_first_arrival
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (H : Interval) (s T q K : ℝ)
    (hq : 1 < q) (hK : 0 ≤ K)
    (hstart : ∀ ep : StripPole H (T : WithTop ℝ), s ≤ ep.1.time →
      ep.1.velocity 0 ∈ closure c.entrance →
      ∃ G : Point → ℝ, Measurable G ∧ (∀ z, 0 ≤ G z) ∧
        (stripGreen hH hLE hlam hLam A H T ep).restrict {z | z.velocity 0 ∈ c.core} =
          volume.withDensity (fun z => ENNReal.ofReal (G z)) ∧
        MemLp G (ENNReal.ofReal q) volume ∧
        (eLpNorm G (ENNReal.ofReal q) volume).toReal ≤ K)
    (e : StripPole H (T : WithTop ℝ)) (he : s < e.1.time) :
    ∃ G : Point → ℝ, Measurable G ∧ (∀ z, 0 ≤ G z) ∧
      (stripGreen hH hLE hlam hLam A H T e).restrict {z | z.velocity 0 ∈ c.core} =
        volume.withDensity (fun z => ENNReal.ofReal (G z)) ∧
      MemLp G (ENNReal.ofReal q) volume ∧
      (eLpNorm G (ENNReal.ofReal q) volume).toReal ≤ K    := by
  have belowFour_restart_ae_internal (W : Interval) (e : StripPole W (T : WithTop ℝ)) :
      ∀ᵐ ep ∂nestedIntervalRestartPoles hH hLE hlam hLam A W H s T e,
      ep.1 ∈ nestedIntervalInternalExit W H s T := by
    have hp := ae_restrict_mem (μ := stripExit hH hLE hlam hLam A W T e)
      (measurableSet_nestedIntervalInternalExit W H s T)
    rw [← nestedIntervalRestartPoles_map hH hLE hlam hLam A W H s T e] at hp
    exact ((MeasurableEmbedding.subtype_coe (measurableSet_nestedIntervalPole H T)).ae_map_iff).mp hp
  have belowFour_restart_mass_le_one (W : Interval) (e : StripPole W (T : WithTop ℝ)) (he : s ≤ e.1.time) :
      nestedIntervalRestartPoles hH hLE hlam hLam A W H s T e univ ≤ 1 := by
    have hm := congrArg (fun mu : Measure Point => mu univ)
      (nestedIntervalRestartPoles_map hH hLE hlam hLam A W H s T e)
    rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ,
      preimage_univ, Measure.restrict_apply_univ] at hm
    rw [hm]
    exact (measure_mono (subset_univ _)).trans_eq
      (strip_exit_probability hH hLE hlam hLam A W s T e he).1
  have belowFour_waiting_interval (v : ℝ) (hv : v ∈ H.carrier) (hnot : v ∉ closure c.entrance) :
      ∃ W : Interval, v ∈ W.carrier ∧ W.carrier ⊆ H.carrier ∧
      Disjoint W.carrier c.core ∧
      ∀ w : ℝ, (w = W.lo ∨ w = W.hi) → w ∈ H.carrier → w ∈ closure c.entrance := by
    have hlo : c.vbar - c.r / 2 < c.vbar + c.r / 2 := by linarith [c.positive]
    rw [Clock.entrance, closure_Ioo hlo.ne] at hnot ⊢
    change H.lo < v ∧ v < H.hi at hv
    by_cases hl : v < c.vbar - c.r / 2
    · have hp : H.lo < min H.hi (c.vbar - c.r / 2) := lt_min H.ordered (hv.1.trans hl)
      let W : Interval := ⟨H.lo, min H.hi (c.vbar - c.r / 2), hp⟩
      refine ⟨W, ⟨hv.1, lt_min hv.2 hl⟩, ?_, ?_, ?_⟩
      · intro w hw
        exact ⟨hw.1, hw.2.trans_le (min_le_left _ _)⟩
      · apply disjoint_left.mpr
        intro w hw hc
        change c.vbar - c.r / 4 ≤ w ∧ w ≤ c.vbar + c.r / 4 at hc
        have hh := hw.2.trans_le (min_le_right H.hi (c.vbar - c.r / 2))
        linarith [hc.1, c.positive]
      · intro w hw hwH
        rcases hw with hw | hw
        · change w = H.lo at hw
          exact (lt_irrefl w (hw ▸ hwH.1)).elim
        · change w = min H.hi (c.vbar - c.r / 2) at hw
          have he : min H.hi (c.vbar - c.r / 2) = c.vbar - c.r / 2 := by
            by_cases hh : H.hi ≤ c.vbar - c.r / 2
            · rw [min_eq_left hh] at hw
              exact (lt_irrefl w (hw ▸ hwH.2)).elim
            · exact min_eq_right (le_of_not_ge hh)
          rw [hw, he]
          exact ⟨le_rfl, hlo.le⟩
    · have hr : c.vbar + c.r / 2 < v := by
        by_contra hh
        exact hnot ⟨le_of_not_gt hl, le_of_not_gt hh⟩
      have hp := max_lt H.ordered (hr.trans hv.2)
      let W : Interval := ⟨max H.lo (c.vbar + c.r / 2), H.hi, hp⟩
      refine ⟨W, ⟨max_lt hv.1 hr, hv.2⟩, ?_, ?_, ?_⟩
      · intro w hw
        exact ⟨(le_max_left _ _).trans_lt hw.1, hw.2⟩
      · apply disjoint_left.mpr
        intro w hw hc
        change c.vbar - c.r / 4 ≤ w ∧ w ≤ c.vbar + c.r / 4 at hc
        have hh := (le_max_right H.lo (c.vbar + c.r / 2)).trans_lt hw.1
        linarith [hc.2, c.positive]
      · intro w hw hwH
        rcases hw with hw | hw
        · change w = max H.lo (c.vbar + c.r / 2) at hw
          have he : max H.lo (c.vbar + c.r / 2) = c.vbar + c.r / 2 := by
            by_cases hh : c.vbar + c.r / 2 ≤ H.lo
            · rw [max_eq_left hh] at hw
              exact (lt_irrefl w (hw ▸ hwH.1)).elim
            · exact max_eq_right (le_of_not_ge hh)
          rw [hw, he]
          exact ⟨hlo.le, le_rfl⟩
        · change w = H.hi at hw
          exact (lt_irrefl w (hw ▸ hwH.2)).elim
  by_cases hvel : e.1.velocity 0 ∈ closure c.entrance
  · exact hstart e he.le hvel
  obtain ⟨W, hv, hsub, hdisj, hface⟩ := belowFour_waiting_interval (e.1.velocity 0) e.2.2 hvel
  let ew : StripPole W (T : WithTop ℝ) := ⟨e.1, e.2.1, hv⟩
  let tau := nestedIntervalRestartPoles hH hLE hlam hLam A W H s T ew
  let k := belowFour_coreGreenKernel hH hLE hlam hLam A c H T
  have hbound : ∀ᵐ ep ∂tau, ∃ G : Point → ℝ,
      Measurable G ∧ (∀ z, 0 ≤ G z) ∧
      k ep = volume.withDensity (fun z => ENNReal.ofReal (G z)) ∧
      MemLp G (ENNReal.ofReal q) volume ∧ (eLpNorm G (ENNReal.ofReal q) volume).toReal ≤ K := by
    filter_upwards [belowFour_restart_ae_internal W ew] with ep hp
    exact hstart ep hp.1.le (hface _ hp.2.2.1 hp.2.2.2)
  obtain ⟨G, hG, hG0, hGd, hGp, hGn⟩ := belowFour_density_subprobability_mixture tau k q K hq hK
    (belowFour_restart_mass_le_one W ew he.le) hbound
  have hC : MeasurableSet {z : Point | z.velocity 0 ∈ c.core} :=
    isClosed_Icc.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable
  have hz : (stripGreen hH hLE hlam hLam A W T ew).restrict {z | z.velocity 0 ∈ c.core} = 0 := by
    apply Measure.restrict_eq_zero.mpr
    have hzero := ae_iff.mp ((stripGreenOfKernel_ae_mem_stripPast W (stripEvolution hH hLE hlam hLam A W).2 T ew).mono (fun z hz => hz.2))
    exact le_antisymm ((measure_mono (show {z : Point | z.velocity 0 ∈ c.core} ⊆
      {z | z.velocity 0 ∉ W.carrier} from
        fun z hc hw => disjoint_left.mp hdisj hw hc)).trans_eq hzero) zero_le
  have hid := nestedIntervalGreen_identity hH hLE hlam hLam A W H hsub s T ew he
  have hep : nestedPoleInclusion W H hsub T ew = e := Subtype.ext rfl
  rw [hep] at hid
  have hr : (nestedIntervalRestartGreen hH hLE hlam hLam A W H s T ew).restrict
      {z | z.velocity 0 ∈ c.core} = k ∘ₘ tau := by
    exact nested_bind_restrict tau _
      (Measure.measurable_measure.mpr (fun B hB =>
        stripGreen_measurable_apply hH hLE hlam hLam A H T B hB)) _ hC
  have hm : (stripGreen hH hLE hlam hLam A H T e).restrict {z | z.velocity 0 ∈ c.core} =
      k ∘ₘ tau := by
    rw [hid, Measure.restrict_add, hz, zero_add, hr]
  exact ⟨G, hG, hG0, hm.trans hGd, hGp, hGn⟩


/-- The band proposition follows from its direct predecessors. -/
theorem below_four_band_of_predecessors (hpush : PushforwardStatement)
    (htail : RestartTailStatement) (hvisits : PositionVisitsStatement)
    (hmasses : PositionVisitMassesStatement) (hcore : CoreDominationStatement) :
    BelowFourBandStatement := by
  intro hH hLE lam Lam hlam hLam alpha q ha hq
  obtain ⟨C, hC, hd⟩ := below_four_core_start_band hpush htail hvisits hmasses hcore
    hH hLE hlam hLam alpha q ha hq
  refine ⟨C, hC, ?_⟩
  intro A c Z₀ R hR P hP hc hr
  let H := capacityCylinderInterval Z₀ R hR
  let T := Z₀.time + R ^ 2
  let e := capacityCylinderPole Z₀ P R hR hP
  let K := (C * R ^ (6 - 4 * q) *
    (c.r / R) ^ (4 - 3 * q + (1 - alpha) * (q - 1))) ^ (1 / q)
  have hK : 0 ≤ K := Real.rpow_nonneg
    (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hR.le _))
      (Real.rpow_nonneg (div_pos c.positive hR).le _)) _
  have hstart (ep : StripPole H (T : WithTop ℝ)) (hs : Z₀.time ≤ ep.1.time)
      (hv : ep.1.velocity 0 ∈ closure c.entrance) := hd A c H Z₀.time R hR ep hs hv hc hr
  obtain ⟨G, hG, hG0, hGd, hGp, hGn⟩ := belowFour_first_arrival hH hLE hlam hLam A c H
    Z₀.time T q K hq.1 hK hstart e hP.1
  let mu := (stripGreen hH hLE hlam hLam A H T e).restrict {z | z.velocity 0 ∈ c.core}
  let D := densityObservationStrip Z₀ R hR
  have hD : MeasurableSet D :=
    (isOpen_lt continuous_const continuous_time).measurableSet.inter
      ((isOpen_lt continuous_time continuous_const).measurableSet.inter
        (isOpen_Ioo.measurableSet.preimage
          ((continuous_apply 0).comp continuous_velocity).measurable))
  let ei : StripPole H ⊤ := ⟨e.1, WithTop.coe_lt_top _, e.2.2⟩
  have hmu : ∀ᵐ z ∂mu, z ∈ D := by
    filter_upwards [ae_restrict_of_ae (stripGreenOfKernel_ae_mem_stripPast H (stripEvolution hH hLE hlam hLam A H).2 T e), ae_restrict_of_ae ((stripGreen_infinite_ae_future_carrier hH hLE hlam hLam A H ei).filter_mono (stripGreen_mono hH hLE hlam hLam A H H Subset.rfl T ⊤ le_top e).absolutelyContinuous.ae_le)] with z hz ht
    exact ⟨hP.1.trans ht.1, hz.1, hz.2⟩
  have hdensity : mu = (volume.restrict D).withDensity (fun z => ENNReal.ofReal (G z)) := by
    rw [← (Measure.restrict_eq_self_of_ae_mem hmu)]
    dsimp only [mu]
    rw [hGd, restrict_withDensity hD]
  refine ⟨G, hG, hG0, hdensity, hGp.restrict D, ?_⟩
  exact (ENNReal.toReal_mono hGp.ne (eLpNorm_restrict_le G (ENNReal.ofReal q) volume D)).trans hGn


/-- The source's single clock, with centre v₀ and radius 4R. -/
def farVelocityClock (Z₀ : Point) (R : ℝ) (hR : 0 < R)
    (hfar : 8 * R < |Z₀.velocity 0|) : Clock where
  vbar := Z₀.velocity 0
  r := 4 * R
  nonzero := by intro h; rw [h, abs_zero] at hfar; linarith
  positive := by positivity
  radius := by linarith

/-- The cylinder velocity interval is contained in the single clock's active interval. -/
theorem farVelocityClock_contains (Z₀ : Point) (R : ℝ) (hR : 0 < R)
    (hfar : 8 * R < |Z₀.velocity 0|) :
    (capacityCylinderInterval Z₀ R hR).carrier ⊆
      (farVelocityClock Z₀ R hR hfar).active := by
  intro v hv
  change Z₀.velocity 0 - R < v ∧ v < Z₀.velocity 0 + R at hv
  change Z₀.velocity 0 - 3 * (4 * R) / 4 < v ∧
    v < Z₀.velocity 0 + 3 * (4 * R) / 4
  constructor <;> linarith [hv.1, hv.2]

/-- The source far-velocity density estimate, conditional only on p:pushforward. -/
theorem cylinder_density_far (hpush : PushforwardStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (q : ℝ) (hq : 1 < q ∧ q < 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
      (Z₀ : Point) (R : ℝ) (hR : 0 < R) (P : Point)
      (hP : P ∈ forwardCylinder Z₀ R hR),
      8 * R < |Z₀.velocity 0| →
      ∃ G : Point → ℝ, Measurable G ∧ (∀ z, 0 ≤ G z) ∧
        (stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z₀ R hR)
          (Z₀.time + R ^ 2) (capacityCylinderPole Z₀ P R hR hP)).restrict
            (forwardCylinder Z₀ R hR) =
          (volume.restrict (forwardCylinder Z₀ R hR)).withDensity
            (fun z => ENNReal.ofReal (G z)) ∧
        MemLp G (ENNReal.ofReal q) (volume.restrict (forwardCylinder Z₀ R hR)) ∧
        (eLpNorm G (ENNReal.ofReal q)
          (volume.restrict (forwardCylinder Z₀ R hR))).toReal ≤ C * R ^ (6 / q - 4) := by
  obtain ⟨C, hC, hc⟩ := (hpush hH hLE lam Lam hlam hLam).2 q hq
  refine ⟨C * 4 ^ (6 / q - 4), by positivity, ?_⟩
  intro A Z₀ R hR P hP hfar
  let c := farVelocityClock Z₀ R hR hfar
  have hsub := farVelocityClock_contains Z₀ R hR hfar
  let e := capacityCylinderPole Z₀ P R hR hP
  have he : P.velocity 0 ∈ c.active := hsub e.2.2
  obtain ⟨f, hfm, hf0, hfd, hfp, hfn⟩ := hc A c P he
  have hm := stripGreen_mono hH hLE hlam hLam A
    (capacityCylinderInterval Z₀ R hR) c.activeInterval hsub
    (Z₀.time + R ^ 2) ⊤ le_top e
  have hep : stripEnlargePole (capacityCylinderInterval Z₀ R hR) c.activeInterval hsub
      (Z₀.time + R ^ 2) ⊤ le_top e = densityClockPole c P he := Subtype.ext rfl
  rw [hep, hfd] at hm
  have hD : MeasurableSet (densityClockStrip c P) :=
    (isOpen_Ioi.preimage continuous_time).measurableSet.inter
      (isOpen_Ioo.preimage ((continuous_apply 0).comp continuous_velocity)).measurableSet
  have := density_volume_sigmaFinite
  obtain ⟨g, hgm, hg0, hgd, hgp, hgn⟩ := density_restrict_of_le_withDensity volume
    (stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z₀ R hR)
      (Z₀.time + R ^ 2) e) (densityClockStrip c P) (forwardCylinder Z₀ R hR)
    hD (isOpen_forwardCylinder Z₀ R hR).measurableSet f hfm hf0
    (ENNReal.ofReal q) hfp hm
  refine ⟨g, hgm, hg0, hgd, hgp, ?_⟩
  have hn := (ENNReal.toReal_mono hfp.ne hgn).trans hfn
  have hr : c.r ^ (6 / q - 4) = 4 ^ (6 / q - 4) * R ^ (6 / q - 4) :=
    Real.mul_rpow (by norm_num) hR.le
  rw [hr] at hn
  simpa only [mul_assoc] using hn


/-- The sixth-fifths power of the core estimate has a summable positive scale power. -/
theorem preliminary_core_power_le (C R r : ℝ) (hC : 0 < C) (hR : 0 < R)
    (hr : 0 < r) (hrR : r ≤ 6 * R) :
    (C * r * (1 + R / r) ^ (5 / 6 : ℝ)) ^ (6 / 5 : ℝ) ≤
      7 * C ^ (6 / 5 : ℝ) * R ^ (6 / 5 : ℝ) * (r / R) ^ (1 / 5 : ℝ) := by
  have hnon : 0 ≤ 1 + R / r := by positivity
  have he : (C * r * (1 + R / r) ^ (5 / 6 : ℝ)) ^ (6 / 5 : ℝ) =
      C ^ (6 / 5 : ℝ) * (r ^ (1 / 5 : ℝ) * (r + R)) := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow hC.le hr.le, ← Real.rpow_mul hnon]
    norm_num
    have hx : r ^ (6 / 5 : ℝ) = r ^ (1 / 5 : ℝ) * r := by
      calc
        _ = r ^ ((1 / 5 : ℝ) + 1) := by norm_num
        _ = _ := by rw [Real.rpow_add hr, Real.rpow_one]
    rw [hx]
    field_simp
  have he' : 7 * C ^ (6 / 5 : ℝ) * R ^ (6 / 5 : ℝ) *
      (r / R) ^ (1 / 5 : ℝ) =
      C ^ (6 / 5 : ℝ) * r ^ (1 / 5 : ℝ) * (7 * R) := by
    rw [Real.div_rpow hr.le hR.le]
    have hx : R ^ (6 / 5 : ℝ) = R ^ (1 / 5 : ℝ) * R := by
      calc
        _ = R ^ ((1 / 5 : ℝ) + 1) := by norm_num
        _ = _ := by rw [Real.rpow_add hR, Real.rpow_one]
    rw [hx]
    field_simp
  rw [he, he']
  have hp : 0 ≤ C ^ (6 / 5 : ℝ) * r ^ (1 / 5 : ℝ) := by positivity
  have hh : r + R ≤ 7 * R := by linarith only [hrR]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh hp

/-- A real norm bound also bounds its positive power integral. -/
theorem preliminary_density_power_le {X : Type*} [MeasurableSpace X]
    (m : MeasureTheory.Measure X) (f : X → ℝ) (q K : ℝ) (hq : 0 < q) (hK : 0 ≤ K)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal q) m)
    (hn : (MeasureTheory.eLpNorm f (ENNReal.ofReal q) m).toReal ≤ K) :
    (∫⁻ x, ‖f x‖ₑ ^ q ∂m) ≤ ENNReal.ofReal (K ^ q) := by
  apply density_power_integral_le m f q (K ^ q) hq (by positivity) hf
  rw [← Real.rpow_mul hK, mul_one_div_cancel hq.ne', Real.rpow_one]
  exact hn




/-- The corrected mass conditions, assuming the terminal domination estimate. -/
theorem positionVisitMassesStatement_holds_of_terminal_domination
    (hTerminal : ∀ (hH : HormanderHypoellipticityStatement)
      (hLE : LiebermanEllipsoidDirichletStatement)
      (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
      (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ) (P : Point),
      |c.vbar| = 2 * c.r → 0 < T → closure c.active ⊆ J.carrier →
      P.velocity 0 ∈ closure c.entrance →
      ∀ (N : ℕ) (b : ℝ), P.time ≤ b → b ≤ P.time + T →
        enlargedActiveTerminal hH hLE hlam hLam A c J P.time (P.time + T) P N b ≤
          enlargedFullSpaceTerminal hH hLE hlam hLam A P b) :
    PositionVisitMassesStatement := by
  intro hH hLE lam Lam hlam hLam
  refine ⟨enlargedVisitMassConstant lam Lam, enlargedVisitMassConstant_pos hlam hLam, ?_⟩
  intro A c J R T P hR hT hTR hbar hJ hvel
  dsimp only
  have hPT : P.time < P.time + T := by linarith
  have : IsFiniteMeasure (visitsFromZero hH hLE hlam hLam A c J T P) :=
    enlargedVisitStarts_isFiniteMeasure hH hLE hlam hLam A c J R T P
      hR hT hTR hbar hJ hvel
  refine ⟨inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · exact enlargedVisitStarts_ae_support hH hLE hlam hLam A c J P.time (P.time + T)
      P le_rfl hPT
  · exact enlargedVisitStarts_mass_le hH hLE hlam hLam A c J R T P hR hT hTR hbar hJ hvel
  · intro j
    exact enlargedPositionVisitMass_sum _ c P.time 0 j
  · intro N
    exact enlarged_active_occupation_le_fullspace hH hLE hlam hLam A c J T hT P
      (hJ (subset_closure (enlarged_closedEntrance_subset_active c hvel))) N
  · exact hTerminal hH hLE lam Lam hlam hLam A c J T P hbar hT hJ hvel




/-- Source l:timed-entrance#time-bin-count: the exact AU-14 hTime binder. -/
def TimeBinCountStatement : Prop :=
  ∀ (hH : HormanderHypoellipticityStatement)
      (hLE : LiebermanEllipsoidDirichletStatement)
      (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam),
      ∃ Ct : ℝ, 0 < Ct ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (J : Interval) (T : ℝ) (P : Point),
      |c.vbar| = 2 * c.r → closure c.active ⊆ J.carrier → 0 < T →
      P.velocity 0 ∈ closure c.entrance → ∀ j : ℕ,
        enlargedTimeVisitMass (visitsFromZero hH hLE hlam hLam A c J T P) c P.time j ≤
          Ct * (1 + (j : ℝ)) ^ (-1 / 2 : ℝ)

/-- Source e:position-start-identity: the exact AU-14 hStart binder. -/
def PositionStartStatement : Prop :=
  ∀ (hH : HormanderHypoellipticityStatement)
      (hLE : LiebermanEllipsoidDirichletStatement)
      (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam),
      ∃ A0 Cs : ℝ, 0 < A0 ∧ 0 < Cs ∧
      ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ) (P : Point),
      |c.vbar| = 2 * c.r → closure c.active ⊆ J.carrier → 0 < T →
      P.velocity 0 ∈ closure c.entrance → ∀ (a b : ℝ) (k : ℤ),
      0 ≤ a → a < b → b - a ≤ c.r ^ 2 → b ≤ T →
      enlargedPositionSlabMass (visitsFromZero hH hLE hlam hLam A c J T P)
        c P.time 0 a b k ≤ Cs *
          ((kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal b)
            (P.position 0, P.velocity 0)
              (box A0 c.r (((k : ℝ) + 1 / 2) * c.r ^ 3))).toReal +
           c.r ^ (-2 : ℤ) * ∫ t in Ioc a b,
             (kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t)
               (P.position 0, P.velocity 0)
                 (box A0 c.r (((k : ℝ) + 1 / 2) * c.r ^ 3))).toReal)

/-- Source e:position-visit-masses (AU-14a): the exact hTerminal binder. -/
def TerminalDominationStatement : Prop :=
  ∀ (hH : HormanderHypoellipticityStatement)
      (hLE : LiebermanEllipsoidDirichletStatement)
      (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
      (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ) (P : Point),
      |c.vbar| = 2 * c.r → 0 < T → closure c.active ⊆ J.carrier →
      P.velocity 0 ∈ closure c.entrance →
      ∀ (N : ℕ) (b : ℝ), P.time ≤ b → b ≤ P.time + T →
        enlargedActiveTerminal hH hLE hlam hLam A c J P.time (P.time + T) P N b ≤
          enlargedFullSpaceTerminal hH hLE hlam hLam A P b

/-- Exactly the four still-open inputs of the autonomous conditional chain. -/
def AutonomousRemainingFrontier : Prop :=
  TimeBinCountStatement ∧ PositionStartStatement ∧
    TerminalDominationStatement ∧ CoreDominationStatement


/-- The exact improved density statement follows from the band and clock propositions. -/
theorem below_four_density_of_band (hband : BelowFourBandStatement)
    (hpush : PushforwardStatement) : BelowFourDensityStatement  := by
  intro hH hLE lam Lam hlam hLam alpha q ha hq
  have below_four_near_velocity_density :
      ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
      (Z₀ : Point) (R : ℝ) (hR : 0 < R) (P : Point)
      (hP : P ∈ forwardCylinder Z₀ R hR),
      |Z₀.velocity 0| ≤ 8 * R →
      ∃ G : Point → ℝ, Measurable G ∧ (∀ z, 0 ≤ G z) ∧
        (stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z₀ R hR)
          (Z₀.time + R ^ 2) (capacityCylinderPole Z₀ P R hR hP)).restrict
            (forwardCylinder Z₀ R hR) =
          (volume.restrict (forwardCylinder Z₀ R hR)).withDensity
            (fun z => ENNReal.ofReal (G z)) ∧
        MemLp G (ENNReal.ofReal q) (volume.restrict (forwardCylinder Z₀ R hR)) ∧
        (eLpNorm G (ENNReal.ofReal q)
          (volume.restrict (forwardCylinder Z₀ R hR))).toReal ≤ C * R ^ (6 / q - 4) := by
    have hx := belowFour_exponent_range lam Lam hlam hLam alpha q ha hq
    let delta := 4 - 3 * q + (1 - alpha) * (q - 1)
    have hd : 0 < delta := hx.2.2
    have hq0 : 0 < q := zero_lt_one.trans hq.1
    obtain ⟨C, hC, hc⟩ := hband hH hLE lam Lam hlam hLam alpha q ha ⟨hq.1, hx.2.1⟩
    let total := ∑' j, geometricBandPower delta j
    have ht : 0 < total := geometricBandPower_tsum_pos delta hd
    refine ⟨(2 * C * total) ^ (1 / q), by positivity, ?_⟩
    intro A Z₀ R hR P hP hnear
    let Q := forwardCylinder Z₀ R hR
    let D := densityObservationStrip Z₀ R hR
    let ν := stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z₀ R hR)
      (Z₀.time + R ^ 2) (capacityCylinderPole Z₀ P R hR hP)
    let S : Bool × ℕ → Set Point := fun i =>
      {z | z.velocity 0 ∈ (geometricCoreClock R hR i.2 i.1).core}
    have hS (i : Bool × ℕ) : MeasurableSet (S i) :=
      (isClosed_Icc.preimage ((continuous_apply 0).comp continuous_velocity)).measurableSet
    have hQ : MeasurableSet Q := (isOpen_forwardCylinder Z₀ R hR).measurableSet
    have hQD : Q ⊆ D := cylinder_subset_density_strip Z₀ R hR
    have hmeasure : volume.restrict Q ≤ volume.restrict D := Measure.restrict_mono_set _ hQD
    have hlocal (i : Bool × ℕ) : ∃ f : Point → ℝ, Measurable f ∧ (∀ z, 0 ≤ f z) ∧
        ν.restrict (S i) = (volume.restrict D).withDensity (fun z => ENNReal.ofReal (f z)) ∧
        MemLp f (ENNReal.ofReal q) (volume.restrict D) ∧
        (eLpNorm f (ENNReal.ofReal q) (volume.restrict D)).toReal ≤
          (C * R ^ (6 - 4 * q) * geometricBandPower delta i.2) ^ (1 / q) := by
      have hr : (geometricCoreClock R hR i.2 i.1).r / R = 4 * (7 / 8 : ℝ) ^ i.2 := by
        dsimp [geometricCoreClock, geometricCoreScale]
        field_simp [ne_of_gt hR]
        ring
      simpa only [hr, geometricBandPower] using (hc A (geometricCoreClock R hR i.2 i.1) Z₀ R hR P hP (geometricCoreClock_center R hR i.2 i.1) (geometricCoreClock_radius R hR i.2 i.1))
    choose f hfm hf0 hfd hfp hfn using hlocal
    have hle (i : Bool × ℕ) : (ν.restrict Q).restrict (S i) ≤
        (volume.restrict Q).withDensity (fun z => ENNReal.ofReal (f i z)) := by
      have he : (ν.restrict Q).restrict (S i) =
          (volume.restrict Q).withDensity (fun z => ENNReal.ofReal (f i z)) := by
        rw [Measure.restrict_comm (hS i), hfd i, restrict_withDensity hQ,
          Measure.restrict_restrict hQ, inter_eq_left.mpr hQD]
      exact he.le
    have hcover : (ν.restrict Q) (⋃ i, S i)ᶜ = 0 := by
      rw [Measure.restrict_apply (MeasurableSet.iUnion hS).compl]
      apply measure_mono_null (t := {z | z.velocity 0 = 0})
      · intro z hz
        by_contra hv
        have hvQ := (capacityCylinderPole Z₀ z R hR hz.2).2.2
        have hab : |z.velocity 0| ≤ 9 * R := by
          have h := abs_le.mp hnear
          change Z₀.velocity 0 - R < z.velocity 0 ∧
            z.velocity 0 < Z₀.velocity 0 + R at hvQ
          apply abs_le.mpr
          constructor <;> linarith [h.1, h.2, hvQ.1, hvQ.2]
        obtain ⟨j, s, hs⟩ := geometricCoreClock_covers R (z.velocity 0) hR hv hab
        exact hz.1 (mem_iUnion.mpr ⟨(s, j), hs⟩)
      · exact cylinder_strip_velocity_slice_zero hH hLE hlam hLam A Z₀ P R hR hP 0
    have : IsFiniteMeasure ν := stripGreen_isFiniteMeasure hH hLE hlam hLam A
      (capacityCylinderInterval Z₀ R hR) (Z₀.time + R ^ 2)
      (capacityCylinderPole Z₀ P R hR hP)
    have := density_volume_sigmaFinite
    obtain ⟨g, hgm, hg0, hgd, hgi⟩ := density_of_countable_cover
      (volume.restrict Q) (ν.restrict Q) S hS hcover f hfm hf0 q hq0 hle
    have hi : ∫⁻ z, ‖g z‖ₑ ^ q ∂volume.restrict Q ≤
        ENNReal.ofReal (2 * C * total * R ^ (6 - 4 * q)) := by
      apply hgi.trans
      calc
        (∑' i, ∫⁻ z, ‖f i z‖ₑ ^ q ∂volume.restrict Q) ≤
            ∑' i : Bool × ℕ,
              ENNReal.ofReal (C * R ^ (6 - 4 * q) * geometricBandPower delta i.2) := by
          apply ENNReal.tsum_le_tsum
          intro i
          exact (lintegral_mono' hmeasure le_rfl).trans
            (density_power_integral_le (volume.restrict D) (f i) q
              (C * R ^ (6 - 4 * q) * geometricBandPower delta i.2) hq0
              (by unfold geometricBandPower; positivity) (hfp i) (hfn i))
        _ = _ := geometricBandPower_sum C R delta (6 - 4 * q) hC.le hR hd
    obtain ⟨hgp, hgn⟩ := density_norm_of_power_bound (volume.restrict Q) g hgm q
      (2 * C * total * R ^ (6 - 4 * q)) hq0 (by positivity) hi
    refine ⟨g, hgm, hg0, hgd, hgp, ?_⟩
    exact hgn.trans_eq (geometricBandPower_root C R delta q hC.le hR hd hq0)
  obtain ⟨Cn, hCn, hn⟩ := below_four_near_velocity_density
  obtain ⟨Cf, hCf, hf⟩ := cylinder_density_far
    hpush hH hLE lam Lam hlam hLam q ⟨hq.1, (belowFour_exponent_range lam Lam hlam hLam alpha q ha hq).2.1⟩
  refine ⟨max Cn Cf, hCn.trans_le (le_max_left _ _), ?_⟩
  intro A Z₀ R hR P hP
  have hr : 0 ≤ R ^ (6 / q - 4) := Real.rpow_nonneg hR.le _
  by_cases hnear : |Z₀.velocity 0| ≤ 8 * R
  · obtain ⟨g, hgm, hg0, hgd, hgp, hgn⟩ := hn A Z₀ R hR P hP hnear
    exact ⟨g, hgm, hg0, hgd, hgp,
      hgn.trans (mul_le_mul_of_nonneg_right (le_max_left Cn Cf) hr)⟩
  · obtain ⟨g, hgm, hg0, hgd, hgp, hgn⟩ := hf A Z₀ R hR P hP (lt_of_not_ge hnear)
    exact ⟨g, hgm, hg0, hgd, hgp,
      hgn.trans (mul_le_mul_of_nonneg_right (le_max_right Cn Cf) hr)⟩


/-- The exact source entrance proposition holds relative to the PDE classical inputs. -/
theorem entranceStatement_holds :
    EntranceStatement := by
  intro hH hLE lam Lam hlam hLam
  constructor
  · obtain ⟨B, hB, hb⟩ := exists_visitStartsQ_mass_constant hlam hLam
    obtain ⟨M, hM, hm⟩ := visit_short_time_mass hlam hLam
    refine ⟨B + M, add_pos hB hM, ?_⟩
    intro A c Z0 R hR P hP _hcore
    refine ⟨visitStartsQ_isFiniteMeasure hH hLE hlam hLam A c Z0 R hR P hP,
      entrance_visitStartsQ_ae_closedEntrance hH hLE hlam hLam A c Z0 R hR P hP,
      ?_, ?_, ?_⟩
    · apply (hb hH hLE A c Z0 R hR P hP).trans
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hM.le)
      exact add_nonneg zero_le_one (div_nonneg hR.le c.positive.le)
    · intro a
      exact (hm hH hLE A c Z0 R hR P hP a).trans
        (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left hB.le))
    · exact (core_green_le_visitGreen hH hLE hlam hLam A c Z0 R hR P hP).trans_eq
        (congrArg (fun rho : Measure Point => rho.restrict {p | p.velocity 0 ∈ c.core})
          (entrance_coreAllTimeGreen_eq hH hLE hlam hLam A c (visitStartsQ hH hLE hlam hLam A c Z0 R hR P hP)))
  · intro q hq
    exact entrance_density hH hLE hlam hLam q hq


/-- Preliminary exponent-six admissibility, relative only to the three classical inputs. -/
theorem smoothAutonomousP6_holds
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement) :
    ∀ (lam Lam : ℝ), 0 < lam → lam ≤ Lam → SmoothAutonomousP6Statement lam Lam  := by
  intro lam Lam hlam hLam
  have smoothAutonomousP6_of_entrance (hentrance : EntranceStatement) :
      SmoothAutonomousP6Statement lam Lam := open Parabolic Holder in by
    have preliminary_backward_abp_of_entrance :
        ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
        (P₀ : Point) (R : ℝ), 0 < R → ∀ (u f : Point → ℝ),
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        IsKineticC112On u (backwardCylinder P₀ R) →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal 6)
          (volume.restrict (backwardCylinder P₀ R)) →
        (∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
          autonomousScalarOperator A.a u P ≤ f P) →
        ∀ P ∈ closure (backwardCylinder P₀ R), u P ≤
          sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - 6 / (6 : ℝ)) *
              (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0))
                (ENNReal.ofReal 6) (volume.restrict (backwardCylinder P₀ R))).toReal := open TheoremA in by
      have preliminary_forward_abp_of_entrance :
          ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
          (Z₀ : Point) (R : ℝ) (hR : 0 < R) (u g : Point → ℝ),
          ContinuousOn u (closure (forwardCylinder Z₀ R hR)) →
          IsKineticC112On u (forwardCylinder Z₀ R hR) →
          (∀ P ∈ forwardCylinder Z₀ R hR, 0 ≤ g P) →
          MemLp g (ENNReal.ofReal 6) (volume.restrict (forwardCylinder Z₀ R hR)) →
          (∀ᵐ P ∂volume.restrict (forwardCylinder Z₀ R hR),
            -g P ≤ forwardScalarOperator A.a u P) →
          ∀ P ∈ closure (forwardCylinder Z₀ R hR), u P ≤
            sSup ((fun P => max (u P) 0) '' exitBoundary Z₀ R hR) +
              C * R ^ (2 - 6 / (6 : ℝ)) *
                (eLpNorm ({P | 0 < u P}.indicator g) (ENNReal.ofReal 6)
                  (volume.restrict (forwardCylinder Z₀ R hR))).toReal := by
        have preliminary_cylinder_density_of_entrance :
            ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
            (Z₀ : Point) (R : ℝ) (hR : 0 < R) (P : Point)
            (hP : P ∈ forwardCylinder Z₀ R hR),
            enlargedDensityBound
              ((stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z₀ R hR)
                (Z₀.time + R ^ 2) (capacityCylinderPole Z₀ P R hR hP)).restrict
                  (forwardCylinder Z₀ R hR)) (forwardCylinder Z₀ R hR) (6 / 5) (C * R) := by
          have preliminary_near_density_of_entrance :
              ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
              (Z₀ : Point) (R : ℝ) (hR : 0 < R) (P : Point)
              (hP : P ∈ forwardCylinder Z₀ R hR),
              |Z₀.velocity 0| ≤ 8 * R →
              enlargedDensityBound
                ((stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z₀ R hR)
                  (Z₀.time + R ^ 2) (capacityCylinderPole Z₀ P R hR hP)).restrict
                    (forwardCylinder Z₀ R hR)) (forwardCylinder Z₀ R hR) (6 / 5) (C * R) := by
            have preliminary_core_density_of_entrance :
                ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
                (Z₀ : Point) (R : ℝ) (hR : 0 < R) (P : Point)
                (hP : P ∈ forwardCylinder Z₀ R hR),
                (c.core ∩ (capacityCylinderInterval Z₀ R hR).carrier).Nonempty →
                enlargedDensityBound
                  ((stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z₀ R hR)
                    (Z₀.time + R ^ 2) (capacityCylinderPole Z₀ P R hR hP)).restrict
                      {p | p.velocity 0 ∈ c.core})
                  (densityObservationStrip Z₀ R hR) (6 / 5)
                  (C * c.r * (1 + R / c.r) ^ (5 / 6 : ℝ)) := by
              obtain ⟨C, hC, hc⟩ := (hentrance hH hLE lam Lam hlam hLam).2 (6 / 5)
                (by norm_num)
              refine ⟨C, hC, ?_⟩
              intro A c Z₀ R hR P hP hmeet
              simpa only [show (6 / (6 / 5) - 4 : ℝ) = 1 by norm_num,
                show (1 / (6 / 5) : ℝ) = 5 / 6 by norm_num, Real.rpow_one]
                using hc A c Z₀ R hR P hP hmeet
            obtain ⟨C, hC, hc⟩ := preliminary_core_density_of_entrance
            let total := ∑' j, geometricBandPower (1 / 5) j
            have ht : 0 < total := geometricBandPower_tsum_pos _ (by norm_num)
            let B := 7 * C ^ (6 / 5 : ℝ)
            have hB : 0 < B := by dsimp [B]; positivity
            refine ⟨(2 * B * total) ^ (5 / 6 : ℝ), by positivity, ?_⟩
            intro A Z₀ R hR P hP hnear
            let Q := forwardCylinder Z₀ R hR
            let D := densityObservationStrip Z₀ R hR
            let ν := stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z₀ R hR)
              (Z₀.time + R ^ 2) (capacityCylinderPole Z₀ P R hR hP)
            let S : Bool × ℕ → Set Point := fun i =>
              {z | z.velocity 0 ∈ (geometricCoreClock R hR i.2 i.1).core}
            have hS (i : Bool × ℕ) : MeasurableSet (S i) :=
              (isClosed_Icc.preimage ((continuous_apply 0).comp continuous_velocity)).measurableSet
            have hQ : MeasurableSet Q := (isOpen_forwardCylinder Z₀ R hR).measurableSet
            have hQD : Q ⊆ D := cylinder_subset_density_strip Z₀ R hR
            have hlocal (i : Bool × ℕ) : ∃ f : Point → ℝ, Measurable f ∧ (∀ z, 0 ≤ f z) ∧
                (ν.restrict Q).restrict (S i) =
                  (volume.restrict Q).withDensity (fun z => ENNReal.ofReal (f z)) ∧
                MemLp f (ENNReal.ofReal (6 / 5)) (volume.restrict Q) ∧
                (∫⁻ z, ‖f z‖ₑ ^ (6 / 5 : ℝ) ∂volume.restrict Q) ≤
                  ENNReal.ofReal (B * R ^ (6 / 5 : ℝ) * geometricBandPower (1 / 5) i.2) := by
              classical
              by_cases hm : (Q ∩ S i).Nonempty
              · obtain ⟨z, hzQ, hzS⟩ := hm
                have hmeet : ((geometricCoreClock R hR i.2 i.1).core ∩
                    (capacityCylinderInterval Z₀ R hR).carrier).Nonempty :=
                  ⟨z.velocity 0, hzS, (capacityCylinderPole Z₀ z R hR hzQ).2.2⟩
                obtain ⟨f, ⟨hfm, hf0, hfd⟩, hfp, hfn⟩ := hc A
                  (geometricCoreClock R hR i.2 i.1) Z₀ R hR P hP hmeet
                have heq : (ν.restrict Q).restrict (S i) =
                    (volume.restrict Q).withDensity (fun z => ENNReal.ofReal (f z)) := by
                  rw [Measure.restrict_comm (hS i), hfd, restrict_withDensity hQ,
                    Measure.restrict_restrict hQ, inter_eq_left.mpr hQD]
                have hfpQ := hfp.mono_measure (Measure.restrict_mono_set volume hQD)
                refine ⟨f, hfm, hf0, heq, hfpQ, ?_⟩
                have hi := preliminary_density_power_le (volume.restrict Q) f (6 / 5)
                  (C * (geometricCoreClock R hR i.2 i.1).r *
                    (1 + R / (geometricCoreClock R hR i.2 i.1).r) ^ (5 / 6 : ℝ))
                  (by norm_num) (by
                    have hr := (geometricCoreClock R hR i.2 i.1).positive
                    positivity) hfpQ ((ENNReal.toReal_mono hfp.ne (eLpNorm_mono_measure f (Measure.restrict_mono_set volume hQD))).trans hfn)
                have hb := preliminary_core_power_le C R (geometricCoreClock R hR i.2 i.1).r
                  hC hR (geometricCoreClock R hR i.2 i.1).positive
                  (geometricCoreClock_radius R hR i.2 i.1)
                have hr : (geometricCoreClock R hR i.2 i.1).r / R =
                    4 * (7 / 8 : ℝ) ^ i.2 := by
                  dsimp [geometricCoreClock, geometricCoreScale]
                  field_simp [ne_of_gt hR]
                  ring
                rw [hr] at hb
                exact hi.trans (ENNReal.ofReal_le_ofReal (by
                  simpa only [B, geometricBandPower] using hb))
              · have he : Q ∩ S i = ∅ := not_nonempty_iff_eq_empty.mp hm
                refine ⟨0, measurable_const, fun _ => le_rfl, ?_, MemLp.zero, ?_⟩
                · rw [Measure.restrict_restrict (hS i), inter_comm, he, Measure.restrict_empty]
                  simp only [Pi.zero_apply, ENNReal.ofReal_zero]
                  change 0 = (volume.restrict Q).withDensity 0
                  exact withDensity_zero.symm
                · simp [enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num :
                    (0 : ℝ) < 6 / 5), lintegral_zero, zero_le]
            choose f hfm hf0 hfd hfp hfi using hlocal
            have hcover : (ν.restrict Q) (⋃ i, S i)ᶜ = 0 := by
              rw [Measure.restrict_apply (MeasurableSet.iUnion hS).compl]
              apply measure_mono_null (t := {z | z.velocity 0 = 0})
              · intro z hz
                by_contra hv
                have hvQ := (capacityCylinderPole Z₀ z R hR hz.2).2.2
                have hab : |z.velocity 0| ≤ 9 * R := by
                  have h := abs_le.mp hnear
                  change Z₀.velocity 0 - R < z.velocity 0 ∧
                    z.velocity 0 < Z₀.velocity 0 + R at hvQ
                  apply abs_le.mpr
                  constructor <;> linarith [h.1, h.2, hvQ.1, hvQ.2]
                obtain ⟨j, s, hs⟩ := geometricCoreClock_covers R (z.velocity 0) hR hv hab
                exact hz.1 (mem_iUnion.mpr ⟨(s, j), hs⟩)
              · exact cylinder_strip_velocity_slice_zero hH hLE hlam hLam A Z₀ P R hR hP 0
            have : IsFiniteMeasure ν := stripGreen_isFiniteMeasure hH hLE hlam hLam A
              (capacityCylinderInterval Z₀ R hR) (Z₀.time + R ^ 2)
              (capacityCylinderPole Z₀ P R hR hP)
            have := density_volume_sigmaFinite
            obtain ⟨g, hgm, hg0, hgd, hgi⟩ := density_of_countable_cover
              (volume.restrict Q) (ν.restrict Q) S hS hcover f hfm hf0 (6 / 5)
              (by norm_num) (fun i => (hfd i).le)
            have hi : (∫⁻ z, ‖g z‖ₑ ^ (6 / 5 : ℝ) ∂volume.restrict Q) ≤
                ENNReal.ofReal (2 * B * total * R ^ (6 / 5 : ℝ)) := by
              apply hgi.trans
              calc
                _ ≤ ∑' i : Bool × ℕ,
                    ENNReal.ofReal (B * R ^ (6 / 5 : ℝ) * geometricBandPower (1 / 5) i.2) :=
                  ENNReal.tsum_le_tsum hfi
                _ = _ := geometricBandPower_sum B R (1 / 5) (6 / 5) hB.le hR (by norm_num)
            obtain ⟨hgp, hgn⟩ := density_norm_of_power_bound (volume.restrict Q) g hgm
              (6 / 5) (2 * B * total * R ^ (6 / 5 : ℝ)) (by norm_num) (by positivity) hi
            refine ⟨g, ⟨hgm, hg0, hgd⟩, hgp, hgn.trans_eq ?_⟩
            rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hR.le]
            norm_num
          obtain ⟨C₁, hC₁, hn⟩ := preliminary_near_density_of_entrance
          obtain ⟨C₂, hC₂, hf⟩ := cylinder_density_far (pushforwardStatement_holds)
            hH hLE lam Lam hlam hLam (6 / 5) (by norm_num)
          refine ⟨max C₁ C₂, hC₁.trans_le (le_max_left _ _), ?_⟩
          intro A Z₀ R hR P hP
          by_cases hnear : |Z₀.velocity 0| ≤ 8 * R
          · obtain ⟨g, hg, hgp, hgn⟩ := hn A Z₀ R hR P hP hnear
            exact ⟨g, hg, hgp, hgn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hR.le)⟩
          · obtain ⟨g, hgm, hg0, hgd, hgp, hgn⟩ := hf A Z₀ R hR P hP (lt_of_not_ge hnear)
            norm_num only [show (6 / (6 / 5) - 4 : ℝ) = 1 by norm_num, Real.rpow_one] at hgn
            exact ⟨g, ⟨hgm, hg0, hgd⟩, hgp,
              hgn.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hR.le)⟩
        obtain ⟨C, hC, hden⟩ := preliminary_cylinder_density_of_entrance
        have hq : (1 : ℝ) < 6 / (6 - 1) := by norm_num
        have hid : (6 / (6 - 1)) / (6 / (6 - 1) - 1) = (6 : ℝ) ∧
            6 / (6 / (6 - 1)) - 4 = 2 - 6 / (6 : ℝ) := by norm_num
        refine ⟨C, hC, ?_⟩
        intro A Z₀ R hR u g hcont hreg hg0 hLp hsub
        have hAc : ContinuousOn (fun P : Point =>
            autonomousCoefficient A.a P.time P.position P.velocity) (forwardCylinder Z₀ R hR) := by
          apply continuousOn_pi.mpr
          intro i
          apply continuousOn_pi.mpr
          intro j
          exact (A.smooth.continuous.comp
            (((continuous_apply 0).comp continuous_position).prodMk
              ((continuous_apply 0).comp continuous_velocity))).continuousOn
        have hpos : ∀ P ∈ forwardCylinder Z₀ R hR,
            (autonomousCoefficient A.a P.time P.position P.velocity).PosSemidef := by
          intro P _
          have heq : autonomousCoefficient A.a P.time P.position P.velocity =
              A.a (P.position 0) (P.velocity 0) • 1 := by
            ext i j
            fin_cases i
            fin_cases j
            simp [autonomousCoefficient]
          rw [heq]
          exact Matrix.PosSemidef.smul Matrix.PosSemidef.one
            (hlam.le.trans (A.bounds _ _).1)
        have hden' : ∀ P ∈ forwardCylinder Z₀ R hR, ∃ G : Point → ℝ,
            Measurable G ∧ (∀ z, 0 ≤ G z) ∧
            autonomousCylinderGreen hH hLE hlam hLam A Z₀ R hR P =
              (volume.restrict (forwardCylinder Z₀ R hR)).withDensity
                (fun z => ENNReal.ofReal (G z)) ∧
            (eLpNorm G (ENNReal.ofReal (6 / (6 - 1)))
              (volume.restrict (forwardCylinder Z₀ R hR))).toReal ≤ C * R ^ (2 - 6 / (6 : ℝ)) ∧
            MemLp G (ENNReal.ofReal (6 / (6 - 1)))
              (volume.restrict (forwardCylinder Z₀ R hR)) := by
          intro P hP
          obtain ⟨G, ⟨hG, hG0, heq⟩, hGLp, hGN⟩ := hden A Z₀ R hR P hP
          have hpower : R ^ (2 - 6 / (6 : ℝ)) = R := by norm_num
          have hGN' : (eLpNorm G (ENNReal.ofReal (6 / (6 - 1)))
              (volume.restrict (forwardCylinder Z₀ R hR))).toReal ≤
                C * R ^ (2 - 6 / (6 : ℝ)) := by
            simpa only [hpower, show (6 / (6 - 1) : ℝ) = 6 / 5 by norm_num] using hGN
          refine ⟨G, hG, hG0, ?_, hGN', ?_⟩
          · simp only [autonomousCylinderGreen, dite_eq_left hP]
            exact heq
          · simpa only [show (6 / (6 - 1) : ℝ) = 6 / 5 by norm_num] using hGLp
        have hs : ∀ᵐ P ∂volume.restrict (forwardCylinder Z₀ R hR),
            -g P ≤ forwardKineticOperator (autonomousCoefficient A.a) u P := by
          simpa only [forwardOperator_autonomous] using hsub
        have hl : MemLp g (ENNReal.ofReal ((6 / (6 - 1)) / (6 / (6 - 1) - 1)))
            (volume.restrict (forwardCylinder Z₀ R hR)) := by rwa [hid.1]
        simpa only [hid.1] using (kinetic_abp_abstract_of_continuous Z₀ R hR (autonomousCoefficient A.a) hAc hpos (6 / (6 - 1)) hq (C * R ^ (2 - 6 / 6)) (mul_pos hC (Real.rpow_pos_of_pos hR _)) (autonomousCylinderGreen hH hLE hlam hLam A Z₀ R hR) (autonomous_cylinder_green_potentials hH hLE hlam hLam A Z₀ R hR) hden' u g hcont hreg hg0 hl hs)
      obtain ⟨C, hC, hforward⟩ := preliminary_forward_abp_of_entrance
      refine ⟨C, hC, ?_⟩
      intro A P₀ R hR u f hcont hreg hLp hsub P hP
      let B : SmoothAutonomous lam Lam :=
        ⟨reflectedAutonomous A.a, reflectedAutonomous_smooth A, reflectedAutonomous_bounds A⟩
      let Z₀ := kineticReflection P₀
      let Q := forwardCylinder Z₀ R hR
      let U := u ∘ kineticReflection
      let g := (fun P => max (f P) 0) ∘ kineticReflection
      have hmp := measurePreserving_reflection_forward P₀ R hR
      have hUc : ContinuousOn U (closure Q) := by
        simpa only [preimage_closure_backwardCylinder_reflection P₀ R hR] using (hcont.comp (continuous_kineticReflection 1).continuousOn (fun x hx => hx : MapsTo kineticReflection (kineticReflection ⁻¹' closure (backwardCylinder P₀ R)) _))
      have hUr : IsKineticC112On U Q := by
        simpa only [preimage_backwardCylinder_reflection P₀ R hR] using
          isKineticC112On_kineticReflection u (backwardCylinder P₀ R) hreg
      have hgLp : MemLp g (ENNReal.ofReal 6) (volume.restrict Q) :=
        hLp.comp_measurePreserving hmp
      have hUs : ∀ᵐ P ∂volume.restrict Q, -g P ≤ forwardScalarOperator B.a U P := by
        filter_upwards [hmp.quasiMeasurePreserving.ae hsub] with P hP
        rw [autonomousScalarOperator_reflection]
        exact neg_le_neg (hP.trans (le_max_left _ _))
      have hPr : kineticReflection P ∈ closure Q := by
        rw [← preimage_closure_backwardCylinder_reflection P₀ R hR]
        change kineticReflection (kineticReflection P) ∈ closure (backwardCylinder P₀ R)
        rw [kineticReflection_involutive P]
        exact hP
      have hresult := (hforward B Z₀ R hR U g hUc hUr (fun _ _ => le_max_right _ _) hgLp hUs) (kineticReflection P) hPr
      have hnorm : eLpNorm ({P | 0 < U P}.indicator g) (ENNReal.ofReal 6)
          (volume.restrict Q) =
          eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (ENNReal.ofReal 6)
            (volume.restrict (backwardCylinder P₀ R)) := by
        have hL := borelSource_memLp (isOpen_backwardCylinder P₀ R hR) true u f
          hreg.continuousOn hLp
        change MemLp ({P | 0 < u P}.indicator (fun P => max (f P) 0)) _ _ at hL
        have hfun : {P | 0 < U P}.indicator g =
            ({P | 0 < u P}.indicator (fun P => max (f P) 0)) ∘ kineticReflection := rfl
        rw [hfun]
        exact eLpNorm_comp_measurePreserving hL.aestronglyMeasurable hmp
      rw [hnorm, boundarySup_reflection P₀ R hR u] at hresult
      simpa [U, kineticReflection_involutive P] using hresult
    obtain ⟨C_A, hC, hestimate⟩ := preliminary_backward_abp_of_entrance
    refine ⟨C_A, hC, ?_⟩
    intro A O hO u hu heq
    have hsup (w : Point → ℝ) (hw : IsKineticC112On w O)
        (heqw : ∀ᵐ P ∂volume.restrict O, autonomousScalarOperator A.a w P = 0) :
        IsAdmissibleSupersolution (autonomousCoefficient A.a) O 6 C_A w := by
      refine ⟨hw.continuousOn, ?_⟩
      intro P₀ R hR hQ psi hpsi
      obtain ⟨U, _hU, hUQ, hps⟩ := smoothNear_regular hpsi
      have hQQ : backwardCylinder P₀ R ⊆ O := subset_closure.trans hQ
      have hpr := comparison_regular_mono hps (subset_closure.trans hUQ)
      have hwr := comparison_regular_mono hw hQQ
      have hneg := comparison_regular_const_mul hwr (-1)
      have hdiff : IsKineticC112On (fun P => psi P - w P) (backwardCylinder P₀ R) := by
        simpa only [neg_one_mul, sub_eq_add_neg] using comparison_regular_add hpr hneg
      have hop : ∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
          autonomousScalarOperator A.a (fun Q => psi Q - w Q) P ≤
            autonomousScalarOperator A.a psi P := by
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hQQ heqw,
          ae_restrict_mem (isOpen_backwardCylinder P₀ R hR).measurableSet] with P he hP
        have hadd := autonomous_operator_add hpr hneg A.a hP
        have hmul := autonomous_operator_const_mul hwr (-1) A.a hP
        simp only [neg_one_mul, ← sub_eq_add_neg] at hadd hmul
        rw [hadd, hmul, he]
        simp [le_refl]
      obtain ⟨_hmeas, hLp⟩ := autonomous_test_source hlam
        A.smooth.continuous.measurable A.bounds P₀ R hR hpsi
      have hn : {P | 0 < psi P - w P} = {P | w P < psi P} := by
        ext P
        exact sub_pos
      have hbnd' : ∀ P ∈ closure (backwardCylinder P₀ R), psi P - w P ≤
          sSup ((fun P => max (psi P - w P) 0) '' kineticBoundary P₀ R) +
            C_A * R ^ (2 - (4 * (1 : ℝ) + 2) / 6) *
              (eLpNorm (localizedSource (autonomousCoefficient A.a) psi w) (ENNReal.ofReal 6)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
        simpa only [hn, localizedSource, backwardOperator_autonomous,
          show 4 * (1 : ℝ) + 2 = 6 by norm_num] using (hestimate A P₀ R hR (fun P => psi P - w P) (autonomousScalarOperator A.a psi) (hpsi.continuousOn.sub (hw.continuousOn.mono hQ)) hdiff hLp hop)
      apply csSup_le
      · exact (backwardCylinder_nonempty P₀ hR).closure.image _
      · rintro y ⟨P, hP, rfl⟩
        simpa only [Nat.cast_one] using hbnd' P hP
    refine ⟨hsup u hu heq, ?_⟩
    have hneg : IsKineticC112On (fun P => -u P) O := by
      simpa only [neg_one_mul] using comparison_regular_const_mul hu (-1)
    apply hsup (fun P => -u P) hneg
    filter_upwards [heq, ae_restrict_mem hO.measurableSet] with P he hP
    simpa only [neg_one_mul, he, neg_zero] using (autonomous_operator_const_mul hu (-1) A.a hP)
  exact smoothAutonomousP6_of_entrance (entranceStatement_holds)

/-- The improved cylinder density follows from exactly the remaining source frontier. -/
theorem below_four_density_of_frontier (hfront : AutonomousRemainingFrontier)
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement) : BelowFourDensityStatement  := by
  have positionVisitsStatement_holds_of_start_time (hTime : ∀ (hH : HormanderHypoellipticityStatement)
      (hLE : LiebermanEllipsoidDirichletStatement)
      (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam),
      ∃ Ct : ℝ, 0 < Ct ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (J : Interval) (T : ℝ) (P : Point),
      |c.vbar| = 2 * c.r → closure c.active ⊆ J.carrier → 0 < T →
      P.velocity 0 ∈ closure c.entrance → ∀ j : ℕ,
        enlargedTimeVisitMass (visitsFromZero hH hLE hlam hLam A c J T P) c P.time j ≤
          Ct * (1 + (j : ℝ)) ^ (-1 / 2 : ℝ)) (hStart : ∀ (hH : HormanderHypoellipticityStatement)
      (hLE : LiebermanEllipsoidDirichletStatement)
      (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam),
      ∃ A0 Cs : ℝ, 0 < A0 ∧ 0 < Cs ∧
      ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ) (P : Point),
      |c.vbar| = 2 * c.r → closure c.active ⊆ J.carrier → 0 < T →
      P.velocity 0 ∈ closure c.entrance → ∀ (a b : ℝ) (k : ℤ),
      0 ≤ a → a < b → b - a ≤ c.r ^ 2 → b ≤ T →
      enlargedPositionSlabMass (visitsFromZero hH hLE hlam hLam A c J T P)
        c P.time 0 a b k ≤ Cs *
          ((kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal b)
            (P.position 0, P.velocity 0)
              (box A0 c.r (((k : ℝ) + 1 / 2) * c.r ^ 3))).toReal +
           c.r ^ (-2 : ℤ) * ∫ t in Ioc a b,
             (kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t)
               (P.position 0, P.velocity 0)
                 (box A0 c.r (((k : ℝ) + 1 / 2) * c.r ^ 3))).toReal)) :
      PositionVisitsStatement := by
    intro hH hLE lam Lam hlam hLam alpha ha
    have ht := hTime hH hLE lam Lam hlam hLam
    obtain ⟨Cp, hCp, hcell⟩ := position_cell_count_of_start_time
      hH hLE hlam hLam alpha ha ((smoothAutonomousP6_holds hH hLE) lam Lam hlam hLam) ht (hStart hH hLE lam Lam hlam hLam)
    obtain ⟨Ct, hCt, htime⟩ := ht
    have hg := enlargedAdmissibleAlpha_gamma_range hlam hLam alpha ha
    constructor
    · refine ⟨Ct + Cp, add_pos hCt hCp, ?_⟩
      intro A c J T P hbar hJ hT hvel j
      constructor
      · apply (htime A c J T P hbar hJ hT hvel j).trans
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCp.le)
          (Real.rpow_nonneg (by positivity) _)
      · intro k
        apply (hcell A c J T P hbar hJ hT hvel j k).trans
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCt.le)
          (Real.rpow_nonneg (by positivity) _)
    · intro q hq
      let g := 2 - alpha
      let F := (1 + 1 / (1 - (1 + g * (q - 1)) / 2)) *
        (3 : ℝ) ^ (1 - (1 + g * (q - 1)) / 2)
      have hprod : g * (q - 1) < 1 := by
        have hh := mul_lt_mul_of_pos_right hg.2 (by linarith [hq.1] : 0 < q - 1)
        change (2 - alpha) * (q - 1) < 1
        linarith [hq.2]
      have hb : 0 < 1 - (1 + g * (q - 1)) / 2 := by linarith
      have hF : 0 < F := by dsimp only [F]; positivity
      refine ⟨Cp ^ (q - 1) * Ct * F, by positivity, ?_⟩
      intro A c J R T P hR hT hTR hbar hJ hvel
      have : IsFiniteMeasure (visitsFromZero hH hLE hlam hLam A c J T P) :=
        visitsFromZero_isFiniteMeasure hH hLE hlam hLam A c J T P hbar hJ hT hvel
      apply enlargedPositionVisitMass_power_sum_horizon_le
        (visitsFromZero hH hLE hlam hLam A c J T P) c P.time 0 R T hR hT hTR
      · exact (enlargedVisitStarts_ae_support hH hLE hlam hLam A c J P.time (P.time + T)
          P le_rfl (by linarith)).mono fun _ hp => hp.2.1
      · exact hCt.le
      · exact hCp.le
      · exact hg
      · exact hq
      · exact htime A c J T P hbar hJ hT hvel
      · exact hcell A c J T P hbar hJ hT hvel
  obtain ⟨hTime, hStart, hTerminal, hCore⟩ := hfront
  have hpush := pushforwardStatement_holds
  exact below_four_density_of_band
    (below_four_band_of_predecessors hpush (restartTailStatement_holds)
      (positionVisitsStatement_holds_of_start_time hTime hStart) (positionVisitMassesStatement_holds_of_terminal_domination hTerminal) hCore) hpush

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

