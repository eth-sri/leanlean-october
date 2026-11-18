module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGreenTestSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripBoundary
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripMeasureExt
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtension
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitCone
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitMeasureRiesz
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitFunctional
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitFunctionalDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonConsistency
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonGreenSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonOrder
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonMonotone
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripMassQuadratic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitMeasureSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionBounded

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov SectionTwo TheoremA Evolution Parabolic
open scoped Topology


/-- The actual normalized test is continuous on the full closed velocity strip and zero on
both lateral faces; the boundary conclusions come from the genuine Duhamel theorem. -/
theorem clockSourcePotential_boundary
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (R T : ℝ) (hRT : R < T)
    (f : exitProbeSubmodule) (hfn : ∀ p, 0 ≤ exitProbePhysical f p)
    (hs : tsupport (exitProbePhysical f) ⊆
      {p | p.time < T ∧ p.velocity 0 ∈ clockNormalizedInterval.carrier})
    (hz : ∀ p, R ≤ p.time → exitProbePhysical f p = 0) :
    ContinuousOn (clockSourcePotential hH hLE hlam hLam A c e T f)
      {p | p.position ∈ closure (intervalDomain clockNormalizedInterval)} ∧
    (∀ p, p.position 0 = -3 / 4 ∨ p.position 0 = 3 / 4 →
      clockSourcePotential hH hLE hlam hLam A c e T f p = 0)  := by
  have clock_continuous_of_zero_after (u : Point → ℝ) (hu : ContinuousOn u {p | p.time ≤ T ∧
      p.position ∈ closure (intervalDomain clockNormalizedInterval)}) (hz : ∀ p, R ≤ p.time → u p = 0) :
      ContinuousOn u {p | p.position ∈ closure (intervalDomain clockNormalizedInterval)} := by
    intro p hp
    by_cases ht : p.time < T
    · apply (hu p ⟨ht.le, hp⟩).mono_of_mem_nhdsWithin
      have hn : ∀ᶠ q in 𝓝 p, q.time < T :=
        (isOpen_lt continuous_time continuous_const).mem_nhds ht
      filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with q hq hmem
      exact ⟨hq.le, hmem⟩
    · have hRp : R < p.time := hRT.trans_le (not_lt.mp ht)
      have hn : ∀ᶠ q in 𝓝 p, R < q.time :=
        (isOpen_lt continuous_const continuous_time).mem_nhds hRp
      exact (continuousAt_const.congr_of_eventuallyEq (hn.mono (fun q hq => hz q hq.le))).continuousWithinAt
  let E := clockEvolution hH hLE hlam hLam A c e
  have hsetting := c.extended_sourceSetting hlam hLam A e
  obtain ⟨hBs, hBsym, hBell⟩ := sectionTwoCoefficient_fullBounds (3 * lam / 5) (3 * Lam)
    (c.extendedCoefficient lam A.a e) hsetting.1
  obtain ⟨-, -, -, -, -, hc, -, hv, -⟩ :=
    kinetic_duhamel hH (by omega)
      (intervalDomain_admissible clockNormalizedInterval) (zeroCurve_piecewiseC1 1)
      (by positivity : 0 < 3 * lam / 5) (by linarith : 3 * lam / 5 ≤ 3 * Lam)
      (by norm_num : (0 : ℝ) < 9 / 25)
      (zIndependentCoefficient (c.extendedCoefficient lam A.a e)) hBs hBsym hBell
      c.extendedVectorDrift hsetting.2.1 hsetting.2.2.2.2.1 E.1 E.2
      (clockEvolution_spec hH hLE hlam hLam A c e) T
      (exitProbePhysical f ∘ sectionTwoPoint) (fun p => hfn _)
      (nested_native_probe_raw_smooth f)
      ((exitProbePhysical_continuous_compact f).2.comp_homeomorph (sectionTwoHomeomorph 1))
      (nested_native_probe_source_support clockNormalizedInterval T f hs)
  refine ⟨clock_continuous_of_zero_after _ ?_ ((clockSourcePotential_regular hH hLE hlam hLam A c e R T hRT f hfn hs hz).2.2.1), ?_⟩
  · apply hc.mono
    intro p hp
    refine ⟨hp.1, ?_⟩
    rw [mem_closure_movingDomain_iff, sub_zero]
    exact hp.2
  · intro p hp
    apply hv p
    rw [mem_frontier_movingDomain_iff, sub_zero]
    exact nested_intervalDomain_frontier_of_endpoint clockNormalizedInterval p.position hp


/-- Scalar-coordinate smoothness of a normalized test gives literal physical C112 smoothness
of its clock pullback throughout the physical active strip. -/
theorem clock_pullback_C112 (c : Clock) (e : Point) (h : Point → ℝ)
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) (h ∘ scalarPoint)
      {q : Fin 3 → ℝ | q 2 ∈ normalizedActive}) :
    IsKineticC112On (h ∘ c.map e) {p | p.velocity 0 ∈ c.active} := by
  let l : (ℝ × PDE.Vec 1 × PDE.Vec 1) → (Fin 3 → ℝ) := fun q =>
    ![q.1, q.2.1 0, q.2.2 0]
  have hl : ContDiff ℝ (⊤ : ℕ∞) l := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × PDE.Vec 1 × PDE.Vec 1 => q.1)
      exact contDiff_fst
    · change ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × PDE.Vec 1 × PDE.Vec 1 => q.2.1 0)
      exact (contDiff_apply ℝ ℝ 0).comp contDiff_snd.fst
    · change ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × PDE.Vec 1 × PDE.Vec 1 => q.2.2 0)
      exact (contDiff_apply ℝ ℝ 0).comp contDiff_snd.snd
  have hm : MapsTo (c.mapCoordinates e ∘ l)
      (KineticPoint.equivProd 1 '' {p : Point | p.velocity 0 ∈ c.active})
      {q : Fin 3 → ℝ | q 2 ∈ normalizedActive} := by
    rintro q ⟨p, hp, rfl⟩
    change (c.map e (scalarPoint (l (KineticPoint.equivProd 1 p)))).velocity 0 ∈
      normalizedActive
    have heq : scalarPoint (l (KineticPoint.equivProd 1 p)) = p := by
      exact scalarPoint_coordinates p
    rw [heq]
    exact (c.mem_active_iff (p.velocity 0)).mp hp
  have hs := hh.comp ((c.mapCoordinates_smooth e).comp hl).contDiffOn hm
  have heq : (h ∘ scalarPoint) ∘ (c.mapCoordinates e ∘ l) =
      (h ∘ c.map e) ∘ (KineticPoint.equivProd 1).symm := by
    funext q
    change h (scalarPoint (scalarCoordinates (c.map e (scalarPoint (l q))))) = _
    rw [scalarPoint_coordinates]
    apply congrArg (h ∘ c.map e)
    apply (KineticPoint.equivProd 1).injective
    rw [Equiv.apply_symm_apply]
    refine Prod.ext rfl (Prod.ext ?_ ?_) <;> funext i <;>
      have hi := Fin.eq_zero i <;> subst i <;> rfl
  apply nested_raw_isKineticC112On
    (isOpen_Ioo.preimage ((continuous_apply 0).comp continuous_velocity))
  rwa [heq] at hs


/-- The physical active interval on the existing interval carrier. -/
def Clock.activeInterval (c : Clock) : Interval :=
  ⟨c.vbar - 3 * c.r / 4, c.vbar + 3 * c.r / 4, by linarith [c.positive]⟩


/-- The source's physical forward cone implies a lower bound on elapsed position-clock time. -/
theorem clock_forward_cone_finite
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (T : ℝ)
    (e : StripPole c.activeInterval (T : WithTop ℝ)) :
    (∀ᵐ p ∂stripExit hH hLE hlam hLam A c.activeInterval T e,
      p.time - e.1.time ≤ 2 * c.r ^ 2 * (c.map e.1 p).time) ∧
    ∀ᵐ p ∂stripGreen hH hLE hlam hLam A c.activeInterval T e,
      p.time - e.1.time ≤ 2 * c.r ^ 2 * (c.map e.1 p).time  := by
  have active_ratio_lower {v : ℝ} (hv : v ∈ c.active) :
      1 / 2 ≤ v / c.vbar := by
    rcases lt_or_gt_of_ne c.nonzero with hneg | hpos
    · apply (le_div_iff_of_neg hneg).mpr
      have hr := c.radius
      rw [abs_of_neg hneg] at hr
      have hv' := hv.2
      nlinarith
    · apply (le_div_iff₀ hpos).mpr
      have hr := c.radius
      rw [abs_of_pos hpos] at hr
      have hv' := hv.1
      nlinarith
  have hh := reconstruction_transport_cone_ae hH hlam hLam A c.activeInterval
    (stripEvolution hH hLE hlam hLam A c.activeInterval)
    (stripEvolution_spec hH hLE hlam hLam A c.activeInterval) T e
    1 (-2 / c.vbar) (2 * e.1.position 0 / c.vbar - e.1.time)
    (by dsimp only [reconstructionConeCoordinate]; ring) (fun v hv => by
      have hr := active_ratio_lower hv
      have he : v * (-2 / c.vbar) = -2 * (v / c.vbar) := by ring
      rw [he]
      linarith)
  have hb (p : Point)
      (hp : reconstructionConeCoordinate 1 (-2 / c.vbar)
        (2 * e.1.position 0 / c.vbar - e.1.time) p ≤ 0) :
      p.time - e.1.time ≤ 2 * c.r ^ 2 * (c.map e.1 p).time := by
    have he : 2 * c.r ^ 2 * (c.map e.1 p).time =
        2 * (p.position 0 - e.1.position 0) / c.vbar := by
      dsimp [Clock.map]
      field_simp [c.nonzero, ne_of_gt c.positive]
    rw [he]
    have hp' : p.time - e.1.time -
        2 * (p.position 0 - e.1.position 0) / c.vbar ≤ 0 := by
      convert hp using 1
      · dsimp only [reconstructionConeCoordinate]
        ring
    linarith
  exact ⟨hh.1.mono hb, hh.2.mono hb⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

