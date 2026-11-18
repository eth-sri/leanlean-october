module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionDomination
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassTerminal
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassQuadratic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassCapacity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassGreenCapacity
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassSummation
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionOccupation

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory





/-- Source horizon conversion for the quadratic count inequality. -/
theorem enlarged_mass_arithmetic {r R M D : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hD : 0 ≤ D) (hM : 5 * r ^ 2 / 16 * M ≤ 9 * r ^ 2 / 16 + D * R * r) :
    M ≤ (9 / 5 + 16 / 5 * D) * (1 + R / r) := by
  have hraw : M ≤ 9 / 5 + 16 / 5 * D * (R / r) := by
    convert (le_div_iff₀ (by positivity : 0 < 5 * r ^ 2 / 16)).mpr (by simpa only [mul_comm] using hM) using 1
    field_simp
  have hx := div_nonneg hR hr.le
  nlinarith


/-- An explicit ellipticity-only constant for the enlarged-strip visit count. -/
def enlargedVisitMassConstant (lam Lam : ℝ) : ℝ :=
  9 / 5 + 16 / 5 * (128 * Lam / lam * Real.sqrt (2 * Lam))

/-- The explicit counting constant is positive under the source ellipticity assumptions. -/
theorem enlargedVisitMassConstant_pos {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) : 0 < enlargedVisitMassConstant lam Lam := by
  have hLp := hlam.trans_le hLam
  unfold enlargedVisitMassConstant
  positivity


/-- The actual enlarged count has the source horizon bound independently of the outer interval. -/
theorem enlargedVisitStarts_mass_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (R T : ℝ)
    (P : Point) (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R ^ 2)
    (hbar : |c.vbar| = 2 * c.r) (hJ : closure c.active ⊆ J.carrier)
    (hvel : P.velocity 0 ∈ closure c.entrance) :
    enlargedVisitStarts hH hLE hlam hLam A c J P.time (P.time + T) P univ ≤
      ENNReal.ofReal (enlargedVisitMassConstant lam Lam * (1 + R / c.r))   := by
  have enlarged_active_terminal_mass_le_one (s : ℝ) (T : ℝ) (hP : s ≤ P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (N : ℕ) :
      enlargedActiveTerminal hH hLE hlam hLam A c J s T P N T univ ≤ 1 := by
    let gamma := enlargedVisitEntrance hH hLE hlam hLam A c J s T P
    let outer := finiteUnionExitSet J.toFiniteUnion s T
    have hpiece (n : ℕ) :
        (gamma n).bind (enlargedActiveTerminalFamily hH hLE hlam hLam A c J T) ≤
          ((enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T) ∘ₘ gamma n).restrict outer := by
      rw [enlargedActiveTerminal_bind_eq_restrict hH hLE hlam hLam A c J T (gamma n)
        ((enlargedVisitEntrance_ae_support hH hLE hlam hLam A c J s T P hP.1 hP.2.1 n).mono
          fun _ hp => hp.2.1)]
      apply Measure.restrict_mono_ae
      filter_upwards [enlargedActiveExitMixture_ae_velocity hH hLE hlam hLam A c J T (gamma n)]
        with q hq
      intro ht
      apply Or.inl
      refine ⟨ht, ?_⟩
      rw [Interval.toFiniteUnion_carrier]
      exact subset_closure (hJ hq)
    exact ((Finset.sum_le_sum (s := Finset.range N) (fun n _ => hpiece n)) univ).trans
      (enlarged_piece_domination hH hLE hlam hLam A c J s T P hP N).1
  have enlargedActivePiece_partial_capacity_of_domination (N : ℕ) (hOccupation : (∑ n ∈ Finset.range N,
      enlargedActivePiece hH hLE hlam hLam A c J P.time (P.time + T) P n) ≤
        enlargedFullSpaceOccupation hH hLE hlam hLam A P T) :
      (∑ n ∈ Finset.range N,
      (enlargedActivePiece hH hLE hlam hLam A c J P.time (P.time + T) P n univ).toReal) ≤
        (64 * c.r / lam) * Real.sqrt (2 * Lam * T) := by
    have enlargedActivePiece_ae_active (s : ℝ) (T : ℝ) (hs : s ≤ P.time) (hT : P.time < T) (n : ℕ) :
        ∀ᵐ q ∂enlargedActivePiece hH hLE hlam hLam A c J s T P n,
        q.velocity 0 ∈ c.active := by
      unfold enlargedActivePiece
      rw [enlargedVisitGreen_comp_eq_clipped hH hLE hlam hLam A (visitActiveUnion c J) s T _
        ((enlargedVisitEntrance_ae_support hH hLE hlam hLam A c J s T P hs hT n).mono
          fun _ hp => hp.1)]
      exact visitActiveGreenMixture_ae_active hH hLE hlam hLam A c J (s - 1) T _
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
      apply (enlargedActivePiece_ae_active P.time (P.time + T) le_rfl hPT n).mono
      intro q hq
      have hv := (c.active_abs_bounds hq).2
      rw [hbar] at hv
      change |q.velocity 0| ≤ 3 * c.r
      linarith
    have he := congrArg (fun m => m univ)
      (Measure.restrict_eq_self_of_ae_mem hs)
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter] at he
    have hb := (hOccupation B).trans
      (enlargedFullSpaceOccupation_band_le hH hLE hlam hLam A P T c.r hT c.positive)
    rw [he] at hb
    have hradius := c.positive
    have hnon : 0 ≤ (64 * c.r / lam) * Real.sqrt (2 * Lam * T) := by positivity
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    rwa [ENNReal.toReal_ofReal hnon, visit_partial_real_mass gm N univ MeasurableSet.univ] at hr
  have hPT : P.time < P.time + T := by linarith
  have hv :=
    hJ (subset_closure (enlarged_closedEntrance_subset_active c hvel))
  have hLn := hlam.le.trans hLam
  have hr := c.positive
  have hsqrt : Real.sqrt T ≤ R := by
    have h := Real.sqrt_le_sqrt hTR
    rwa [Real.sqrt_sq_eq_abs, abs_of_pos hR] at h
  have hscale : (64 * c.r / lam) * Real.sqrt (2 * Lam * T) ≤
      (64 * c.r / lam) * (Real.sqrt (2 * Lam) * R) := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Lam)]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)) (by positivity)
  apply visit_sum_mass_le_of_partial_mass_le
  intro N
  let mu := enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P
  let tm := fun n => (mu n).bind
    (enlargedActiveTerminalFamily hH hLE hlam hLam A c J (P.time + T))
  have : ∀ n, IsFiniteMeasure (tm n) := fun n =>
    enlarged_terminalPiece_isFiniteMeasure hH hLE hlam hLam A c J P.time (P.time + T)
      P le_rfl hPT n
  have he := ENNReal.toReal_mono ENNReal.one_ne_top (enlarged_active_terminal_mass_le_one P.time (P.time + T) ⟨le_rfl, hPT, hv⟩ N)
  change ((∑ n ∈ Finset.range N, tm n) univ).toReal ≤ (1 : ENNReal).toReal at he
  rw [visit_partial_real_mass tm N univ MeasurableSet.univ, ENNReal.toReal_one] at he
  have hnum := (enlargedQuadratic_partial_mass_bound hH hLE hlam hLam A c J P.time (P.time + T) P le_rfl hPT hJ N).trans (add_le_add
    (mul_le_mul_of_nonneg_left he (by positivity))
    (mul_le_mul_of_nonneg_left ((enlargedActivePiece_partial_capacity_of_domination N (enlarged_active_occupation_le_fullspace hH hLE hlam hLam A c J T hT P hv N)).trans hscale) (by positivity : 0 ≤ 2 * Lam)))
  have heq : 2 * Lam * ((64 * c.r / lam) * (Real.sqrt (2 * Lam) * R)) =
      (128 * Lam / lam * Real.sqrt (2 * Lam)) * R * c.r := by ring
  rw [mul_one, heq] at hnum
  have hbound := enlarged_mass_arithmetic hr hR.le
    (by positivity : 0 ≤ 128 * Lam / lam * Real.sqrt (2 * Lam)) hnum
  rw [← visit_partial_real_mass mu N univ MeasurableSet.univ] at hbound
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ univ) ?_).mpr hbound
  exact mul_nonneg (enlargedVisitMassConstant_pos hlam hLam).le (by positivity)


/-- The canonical total enlarged visit count is finite, including the initial atom. -/
theorem enlargedVisitStarts_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (R T : ℝ)
    (P : Point) (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R ^ 2)
    (hbar : |c.vbar| = 2 * c.r) (hJ : closure c.active ⊆ J.carrier)
    (hvel : P.velocity 0 ∈ closure c.entrance) :
    IsFiniteMeasure (enlargedVisitStarts hH hLE hlam hLam A c J P.time (P.time + T) P) :=
  ⟨(enlargedVisitStarts_mass_le hH hLE hlam hLam A c J R T P
    hR hT hTR hbar hJ hvel).trans_lt ENNReal.ofReal_lt_top⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

