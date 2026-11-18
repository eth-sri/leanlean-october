module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisits
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PoleDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SurvivalHalfMass
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ABPAbstractHolder
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripKernelIntegral
public import HypoellipticAleksandrov.KineticAleksandrov.BoundedBorel
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.DensityFromTests
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Normed.Group.Bounded
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory SectionTwo
open scoped ENNReal

/-- The all-time active Green kernel is uniformly finite by the quadratic occupation bound. -/
theorem mixtureActiveGreenKernel_isFiniteKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) :
    IsFiniteKernel (enlargedActiveGreenKernel hH hLE hlam hLam A c) := by
  classical
  refine ⟨ENNReal.ofReal (activeHalfMassTime lam c / 2), ENNReal.ofReal_lt_top, ?_⟩
  intro e
  change (if he : e.velocity 0 ∈ c.active then
    stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e he)
      else 0) univ ≤ _
  split
  · rename_i he
    exact (stripGreen_quadratic_mass hH hLE hlam hLam A c.activeInterval ⊤
      (densityClockPole c e he)).trans
        (ENNReal.ofReal_le_ofReal (active_quadratic_occupation_le hlam c (e.velocity 0)))
  · exact zero_le

/-- A finite starting measure gives a finite all-time Green mixture. -/
theorem enlargedActiveGreen_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (nu : Measure Point) [IsFiniteMeasure nu] :
    IsFiniteMeasure (enlargedActiveGreen hH hLE hlam hLam A c nu) := by
  unfold enlargedActiveGreen
  have := mixtureActiveGreenKernel_isFiniteKernel hH hLE hlam hLam A c
  infer_instance




/-- Pairing against every real test identifies an integrable nonnegative density exactly. -/
theorem mixture_density_eq_of_pairing {X : Type*} [MeasurableSpace X]
    (mu m : Measure X) [IsFiniteMeasure mu] (g : X → ℝ)
    (hgn : ∀ x, 0 ≤ g x) (hgi : Integrable g m)
    (hpair : ∀ f : X → ℝ, (∫ x, f x * g x ∂m) = ∫ x, f x ∂mu) :
    mu = m.withDensity (fun x => ENNReal.ofReal (g x)) := by
  ext B hB
  have he : (∫ x in B, g x ∂m) = (mu B).toReal := by
    have hh := hpair (B.indicator (fun _ => 1))
    have hi : (fun x => B.indicator (fun _ => 1) x * g x) = B.indicator g := by
      funext x
      by_cases hx : x ∈ B
      · simp [indicator_of_mem hx]
      · simp [indicator_of_notMem hx]
    rw [hi] at hh
    simpa [integral_indicator hB, integral_const, Measure.real, Measure.restrict_apply hB, Measure.restrict_apply MeasurableSet.univ, univ_inter] using hh
  calc
    mu B = ENNReal.ofReal (mu B).toReal :=
      (ENNReal.ofReal_toReal (measure_ne_top mu B)).symm
    _ = ENNReal.ofReal (∫ x in B, g x ∂m) := congrArg ENNReal.ofReal he.symm
    _ = ∫⁻ x in B, ENNReal.ofReal (g x) ∂m :=
      ofReal_integral_eq_lintegral_ofReal hgi.restrict
        (Filter.Eventually.of_forall hgn)
    _ = _ := (withDensity_apply (fun x => ENNReal.ofReal (g x)) hB).symm

/-- Bounded conjugate tests give a sharp measurable nonnegative density with its Lq norm. -/
theorem mixture_density_bound_of_bounded_tests {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (m mu : Measure E)
    [m.IsAddHaarMeasure] [IsFiniteMeasure mu] (q C : ℝ) (hq : 1 < q) (hC : 0 ≤ C)
    (htest : ∀ f : BoundedBorel E,
      MemLp f (ENNReal.ofReal (q / (q - 1))) m → (∀ x, 0 ≤ f x) →
      (∫ x, f x ∂mu) ≤ C * (eLpNorm f (ENNReal.ofReal (q / (q - 1))) m).toReal) :
    ∃ g : E → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x) ∧
      mu = m.withDensity (fun x => ENNReal.ofReal (g x)) ∧
      MemLp g (ENNReal.ofReal q) m ∧ (eLpNorm g (ENNReal.ofReal q) m).toReal ≤ C := by
  have hs : ∀ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      tsupport f ⊆ univ → (∀ x, 0 ≤ f x) →
      (∫ x, f x ∂mu) ≤ C *
        (eLpNorm f (ENNReal.ofReal (q / (q - 1))) (m.restrict univ)).toReal := by
    intro f hf hfc _ hfn
    obtain ⟨M, hM⟩ := hfc.exists_bound_of_continuous hf.continuous
    let F : BoundedBorel E := ⟨f, hf.continuous.measurable, max M 0,
      le_max_right _ _, fun x => by
        simpa using (hM x).trans (le_max_left M 0)⟩
    simpa using
      htest F (hf.continuous.memLp_of_hasCompactSupport hfc) hfn
  obtain ⟨_, g, hgm, hgn, hgi, hgp, hgb, _, hpair⟩ :=
    Occupation.exists_density_of_smooth_tests m mu isOpen_univ (by simp) hq hC hs
  simp at hgi hgp hgb hpair
  exact ⟨g, hgm, hgn, mixture_density_eq_of_pairing mu m g hgn hgi hpair, hgp, hgb⟩


/-- A measurable coordinate map commutes with multiplication by a pulled-back density. -/
theorem mixture_map_withDensity {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (m : Measure X) (f : X → Y) (hf : Measurable f) (w : Y → ℝ≥0∞)
    (hw : Measurable w) :
    (m.withDensity (w ∘ f)).map f = (m.map f).withDensity w := by
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  rw [lintegral_map hg hf]
  change (∫⁻ x, (g ∘ f) x ∂m.withDensity (w ∘ f)) = _
  rw [lintegral_withDensity_eq_lintegral_mul m (hw.comp hf) (hg.comp hf),
    lintegral_withDensity_eq_lintegral_mul (m.map f) hw hg,
    lintegral_map (hw.mul hg) hf]
  rfl



/-- Integrating the actual one-pole Green family preserves its uniform Lq estimate. -/
theorem enlargedActiveGreen_density
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (q : ℝ) (hq : 1 < q) (hq2 : q < (3 : ℝ) / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (nu : Measure Point) [IsFiniteMeasure nu],
      ∃ g : Point → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x) ∧
        enlargedActiveGreen hH hLE hlam hLam A c nu =
          volume.withDensity (fun x => ENNReal.ofReal (g x)) ∧
        MemLp g (ENNReal.ofReal q) volume ∧
        (eLpNorm g (ENNReal.ofReal q) volume).toReal ≤
          C * c.r ^ (6 / q - 4) * (nu Set.univ).toReal   := by
  have mixture_density_conjugate_tests (p : ℝ) (hpq : q.HolderConjugate p) :
      ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (nu : Measure Point) [IsFiniteMeasure nu] (f : BoundedBorel Point),
      MemLp f (ENNReal.ofReal p) volume → (∀ z, 0 ≤ f z) →
      (∫ z, f z ∂enlargedActiveGreen hH hLE hlam hLam A c nu) ≤
        C * c.r ^ (6 / q - 4) * (eLpNorm f (ENNReal.ofReal p) volume).toReal *
          (nu univ).toReal := by
    obtain ⟨C, hC, hc⟩ := one_sign_pole_density hH hLE hlam hLam q hpq.lt hq2
    refine ⟨C, hC, ?_⟩
    intro A c nu _ f hfp hfn
    classical
    let K := enlargedActiveGreenKernel hH hLE hlam hLam A c
    let L := C * c.r ^ (6 / q - 4) * (eLpNorm f (ENNReal.ofReal p) volume).toReal
    have hL : 0 ≤ L := mul_nonneg
      (mul_nonneg hC.le (Real.rpow_nonneg c.positive.le _)) ENNReal.toReal_nonneg
    have : IsFiniteKernel K := mixtureActiveGreenKernel_isFiniteKernel hH hLE hlam hLam A c
    have hpoint : ∀ e, (∫ z, f z ∂K e) ≤ L := by
      intro e
      by_cases he : e.velocity 0 ∈ c.active
      · obtain ⟨g, hgm, hgn, hgd, hgb, _⟩ := hc A c e he
        have hgp :=
          hgb.trans_lt ENNReal.ofReal_lt_top
        have hgr :=
          (ENNReal.toReal_mono ENNReal.ofReal_ne_top hgb).trans_eq
            (ENNReal.toReal_ofReal (mul_nonneg hC.le (Real.rpow_nonneg c.positive.le _)))
        have htest := abp_potential_holder volume _ g f hpq hgm hgn
          (Filter.Eventually.of_forall hfn) hgd hgp hfp hgr
        change (∫ z, f z ∂(if hv : e.velocity 0 ∈ c.active then
          stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e hv)
            else 0)) ≤ L
        rw [dite_eq_left he]
        exact htest
      · change (∫ z, f z ∂(if hv : e.velocity 0 ∈ c.active then
          stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e hv)
            else 0)) ≤ L
        rw [dite_eq_right he, integral_zero_measure]
        exact hL
    have hfi : Integrable f (K ∘ₘ nu) := boundedBorel_integrable f _
    have hi : Integrable (fun e => ∫ z, f z ∂K e) nu := by
      rw [Measure.comp_eq_comp_const_apply] at hfi
      simpa using hfi.integral_comp
    have hm := integral_mono hi (integrable_const (μ := nu) L) hpoint
    change (∫ z, f z ∂K ∘ₘ nu) ≤ L * (nu univ).toReal
    rw [(nested_integral_bind nu K K.measurable f hfi)]
    simpa [integral_const, Measure.real, mul_comm] using hm
  have mixture_point_density_of_tests (mu : Measure (KineticPoint 1)) [IsFiniteMeasure mu] (C : ℝ) (hC : 0 ≤ C) (htest : ∀ f : BoundedBorel (KineticPoint 1),
      MemLp f (ENNReal.ofReal (q / (q - 1))) volume → (∀ x, 0 ≤ f x) →
      (∫ x, f x ∂mu) ≤ C *
        (eLpNorm f (ENNReal.ofReal (q / (q - 1))) volume).toReal) :
      ∃ g : KineticPoint 1 → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x) ∧
      mu = volume.withDensity (fun x => ENNReal.ofReal (g x)) ∧
      MemLp g (ENNReal.ofReal q) volume ∧
      (eLpNorm g (ENNReal.ofReal q) volume).toReal ≤ C := by
    let F := KineticPoint.equivProd 1
    have hm := KineticPoint.measurable_equivProd 1
    have hp : MeasurePreserving F volume volume :=
      KineticPoint.measurePreserving_equivProd 1
    have he : MeasurableEmbedding F := (KineticPoint.homeomorphProd 1).measurableEmbedding
    have : (volume : Measure (PDE.Vec 1 × PDE.Vec 1)).IsAddHaarMeasure :=
      Measure.prod.instIsAddHaarMeasure volume volume
    have : (volume : Measure (ℝ × (PDE.Vec 1 × PDE.Vec 1))).IsAddHaarMeasure :=
      Measure.prod.instIsAddHaarMeasure volume volume
    have ht : ∀ f : BoundedBorel (ℝ × (PDE.Vec 1 × PDE.Vec 1)),
        MemLp f (ENNReal.ofReal (q / (q - 1))) volume → (∀ x, 0 ≤ f x) →
        (∫ x, f x ∂mu.map F) ≤ C *
          (eLpNorm f (ENNReal.ofReal (q / (q - 1))) volume).toReal := by
      intro f hfp hfn
      have hh := htest (f.pullback F hm) (hfp.comp_measurePreserving hp)
        (fun x => hfn (F x))
      change (∫ x, f (F x) ∂mu) ≤ C *
        (eLpNorm ((↑f) ∘ F) (ENNReal.ofReal (q / (q - 1))) volume).toReal at hh
      rw [he.integral_map f]
      simpa only [eLpNorm_comp_measurePreserving hfp.aestronglyMeasurable hp] using hh
    obtain ⟨g, hgm, hgn, hgd, hgp, hgb⟩ :=
      mixture_density_bound_of_bounded_tests volume (mu.map F) q C hq hC ht
    refine ⟨g ∘ F, hgm.comp hm, fun x => hgn (F x), ?_,
      hgp.comp_measurePreserving hp, ?_⟩
    · apply he.map_injective
      change mu.map F = (volume.withDensity ((fun x => ENNReal.ofReal (g x)) ∘ F)).map F
      rw [mixture_map_withDensity volume F hm _ hgm.ennreal_ofReal, hp.map_eq]
      exact hgd
    · simpa only [eLpNorm_comp_measurePreserving hgp.aestronglyMeasurable hp] using hgb
  obtain ⟨C, hC, ht⟩ :=
    mixture_density_conjugate_tests _ ((Real.holderConjugate_iff_eq_conjExponent hq).2 rfl)
  refine ⟨C, hC, ?_⟩
  intro A c nu _
  let mu := enlargedActiveGreen hH hLE hlam hLam A c nu
  have : IsFiniteMeasure mu := enlargedActiveGreen_isFiniteMeasure hH hLE hlam hLam A c nu
  apply mixture_point_density_of_tests mu
    (C * c.r ^ (6 / q - 4) * (nu Set.univ).toReal)
    (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg c.positive.le _))
      ENNReal.toReal_nonneg)
  intro f hfp hfn
  simpa only [mul_assoc, mul_comm, mul_left_comm] using ht A c nu f hfp hfn

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

