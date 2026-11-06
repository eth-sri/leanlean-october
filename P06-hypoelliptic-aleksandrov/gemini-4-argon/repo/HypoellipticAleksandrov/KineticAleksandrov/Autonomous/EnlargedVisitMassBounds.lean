module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassQuadratic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassCapacity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassGreenCapacity
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitsPieces
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.IntegratedVelocity

/-! # Outer-independent bounds for canonical enlarged visit counts

Only the exact finite-piece occupation and terminal domination conclusions
are hypotheses here, as they belong to the enlarged recursion.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov

/- Actual active pieces have the physical active-velocity support. -/
theorem enlargedActivePiece_partial_capacity_of_domination
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T )
    (P : Point) (hT : 0 < T) (hbar : |c.vbar| = 2 * c.r) (N )
    (hOccupation : (∑ n ∈ Finset.range N,
      enlargedActivePiece hH hLE hlam hLam A c J P.time (P.time + T) P n) ≤
        enlargedFullSpaceOccupation hH hLE hlam hLam A P T) :
    (∑ n ∈ Finset.range N,
      (enlargedActivePiece hH hLE hlam hLam A c J P.time (P.time + T) P n univ).toReal) ≤
        (64 * c.r / lam) * Real.sqrt (2 * Lam * T) := by
  let gm := enlargedActivePiece hH hLE hlam hLam A c J P.time (P.time + T) P
  have hPT : P.time < P.time + T := by linarith
  have : ∀ n, IsFiniteMeasure (gm n) := fun n =>
    enlargedActivePiece_isFiniteMeasure hH hLE hlam hLam A c J P.time (P.time + T)
      P le_rfl hPT n
  let B : Set Point := {q | |q.velocity 0| ≤ 3 * c.r}
  have hB : MeasurableSet B := measurableSet_le
    (continuous_abs.measurable.comp ((continuous_apply 0).comp continuous_velocity).measurable)
    measurable_const
  have hs : ∀ᵐ q ∂(∑ n ∈ Finset.range N, gm n), q ∈ B := by
    apply ae_finsetSum_measure_iff.mpr
    intro n _
    have _h_inl_9 : ∀ᵐ q ∂enlargedActivePiece hH hLE hlam hLam A c J P.time (P.time + T) P n,
      q.velocity 0 ∈ c.active := by
      let s := P.time
      let T := (P.time + T)
      unfold enlargedActivePiece
      rw [enlargedVisitGreen_comp_eq_clipped hH hLE hlam hLam A (visitActiveUnion c J) s T _
        ((enlargedVisitEntrance_ae_support hH hLE hlam hLam A c J s T P le_rfl hPT n).mono
          fun _ hp => hp.1)]
      exact visitActiveGreenMixture_ae_active hH hLE hlam hLam A c J (s - 1) T _
    apply _h_inl_9.mono
    intro q hq
    have hv := (c.active_abs_bounds hq).2
    rw [hbar] at hv
    change |q.velocity 0| ≤ 3 * c.r
    linarith
  have he := congrArg (fun m : Measure Point => m univ)
    (Measure.restrict_eq_self_of_ae_mem hs)
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter] at he
  have _h_xinl_0 : enlargedFullSpaceOccupation hH hLE hlam hLam A P T {p | |p.velocity 0| ≤ 3 * c.r} ≤ ENNReal.ofReal ((64 * c.r / lam) * Real.sqrt (2 * Lam * T)) := by
    let r := c.r
    have hr := c.positive
    have _h_inl_10 (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement) (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam) (P : Point) (T r) : enlargedFullSpaceOccupation hH hLE hlam hLam A P T {p | |p.velocity 0| ≤ 3 * r} = ∫⁻ t in Ioc 0 T, kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t) (P.position 0, P.velocity 0) {w | |w.2| ≤ 3 * r} := by
      have hB : MeasurableSet {p : Point | |p.velocity 0| ≤ 3 * r} :=
        measurableSet_le (continuous_abs.measurable.comp
          ((continuous_apply 0).comp continuous_velocity).measurable) measurable_const
      change (((volume.restrict (Ioc 0 T)) ⊗ₘ
        physicalElapsedKernel (fullSpaceEvolution hH hLE hlam hLam A)
          (P.position 0, P.velocity 0)).map
            (fun tz => enlargedTerminalPoint (P.time + tz.1) tz.2)) _ = _
      rw [Measure.map_apply (measurable_enlargedOccupationPoint P) hB,
        Measure.compProd_apply (hB.preimage (measurable_enlargedOccupationPoint P))]
      rfl
    rw [_h_inl_10]
    simp_rw [← velocityBandProbability_eq_kernelXV]
    rw [← restrict_Ioo_eq_restrict_Ioc,
      ← velocityGreenRaw_band_eq_lintegral _ hT]
    exact velocityGreenRaw_band_mass_le hH hlam hLam A _
      (fullSpaceEvolution_spec hH hLE hlam hLam A) hr hT _
  have hb := (hOccupation B).trans
    _h_xinl_0
  rw [he] at hb
  have hradius := c.positive
  have hnon : 0 ≤ (64 * c.r / lam) * Real.sqrt (2 * Lam * T) := by positivity
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal hnon, visit_partial_real_mass gm N univ MeasurableSet.univ] at hr
  exact hr

/- Source horizon conversion for the quadratic count inequality. -/
theorem enlarged_mass_arithmetic {r R M D : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hD : 0 ≤ D) (hM : 5 * r ^ 2 / 16 * M ≤ 9 * r ^ 2 / 16 + D * R * r) :
    M ≤ (9 / 5 + 16 / 5 * D) * (1 + R / r) := by
  have hraw : M ≤ 9 / 5 + 16 / 5 * D * (R / r) := by
    have hd : M ≤ (9 * r ^ 2 / 16 + D * R * r) / (5 * r ^ 2 / 16) :=
      (le_div_iff₀ (by positivity : 0 < 5 * r ^ 2 / 16)).mpr
        (by simpa only [mul_comm] using hM)
    convert hd using 1
    field_simp
  have hx : 0 ≤ R / r := div_nonneg hR hr.le
  nlinarith

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
