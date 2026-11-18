module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Duhamel
import Mathlib.Topology.Order.Compact

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set

/-- Source-time integration vanishes outside the source's time support window. -/
theorem duhamelIntegrand_eq_zero_of_time_not_mem {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (g : KineticPoint d → ℝ)
    (a b : ℝ) (hgt : ∀ p, p.time ∉ Icc a b → g p = 0)
    (p : KineticPoint d) (r : ℝ) (hr : r ∉ Icc a b) :
    duhamelIntegrand K g p r = 0 := by
  unfold duhamelIntegrand
  split
  · unfold duhamelSourceIntegral
    have hf : (fun w : EvolutionAmbientState d => g ⟨r, w.1, w.2⟩) = 0 := by
      funext w
      exact hgt ⟨r, w.1, w.2⟩ hr
    rw [hf]
    exact integral_zero' _ _
  · rfl

/-- A finite source time window gives a uniform bound on the entire Duhamel potential. -/
theorem duhamelPotential_le_time_window {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (τplus : ℝ)
    (g : KineticPoint d → ℝ) (hgn : ∀ p, 0 ≤ g p)
    (C : ℝ) (hC : 0 ≤ C) (hgb : ∀ p, g p ≤ C)
    (a b : ℝ) (hab : a ≤ b) (hgt : ∀ p, p.time ∉ Icc a b → g p = 0)
    (p : KineticPoint d) : duhamelPotential K τplus g p ≤ (b - a) * C := by
  let f := (Icc a b).indicator (fun _ => C)
  have hf :=
    (integrableOn_const (C := C) (s := Icc a b)
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Icc
  have hfn : ∀ r, 0 ≤ f r := by
    intro r
    exact indicator_nonneg (fun _ _ => hC) r
  have hn : ∀ r, ‖duhamelIntegrand K g p r‖ ≤ f r := by
    intro r
    by_cases hr : r ∈ Icc a b
    · rw [Real.norm_eq_abs, abs_of_nonneg (duhamelIntegrand_nonneg K g hgn p r)]
      exact (duhamelIntegrand_le K g hgn C hC hgb p r).trans_eq
        (indicator_of_mem hr (fun _ => C)).symm
    · rw [duhamelIntegrand_eq_zero_of_time_not_mem K g a b hgt p r hr]
      simp only [norm_zero, f, indicator_of_notMem hr, le_refl]
  have hnorm := norm_integral_le_of_norm_le
    (μ := volume.restrict (Ioc p.time τplus))
    (hf.mono_measure Measure.restrict_le_self) (Filter.Eventually.of_forall hn)
  have hnon : 0 ≤ duhamelPotential K τplus g p :=
    integral_nonneg (fun r => duhamelIntegrand_nonneg K g hgn p r)
  calc
    duhamelPotential K τplus g p ≤ ∫ r in Ioc p.time τplus, f r := by
      change |duhamelPotential K τplus g p| ≤ _ at hnorm
      rwa [abs_of_nonneg hnon] at hnorm
    _ ≤ ∫ r, f r := integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall hfn) hf
    _ = (b - a) * C := by
      rw [integral_indicator measurableSet_Icc, setIntegral_const]
      simp [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

/-- Compact spacetime support is contained in a finite absolute-time window. -/
theorem exists_time_window_of_hasCompactSupport {d : ℕ}
    (g : KineticPoint d → ℝ) (hg : HasCompactSupport g) :
    ∃ a b : ℝ, a ≤ b ∧ ∀ p, p.time ∉ Icc a b → g p = 0 := by
  have ht := hg.image continuous_time
  obtain ⟨a, ha⟩ := ht.bddBelow
  obtain ⟨b, hb⟩ := ht.bddAbove
  refine ⟨min a b, max a b, min_le_max, ?_⟩
  intro p hp
  apply image_eq_zero_of_notMem_tsupport
  intro hpg
  apply hp
  have hpt : p.time ∈ KineticPoint.time '' tsupport g := ⟨p, hpg, rfl⟩
  exact ⟨(min_le_left a b).trans (ha hpt), (hb hpt).trans (le_max_right a b)⟩

/-- Continuous compact nonnegative sources give a globally bounded Duhamel potential. -/
theorem duhamelPotential_exists_bound {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (τplus : ℝ)
    (g : KineticPoint d → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgn : ∀ p, 0 ≤ g p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p, |duhamelPotential K τplus g p| ≤ C := by
  obtain ⟨C, hC⟩ := hg.bddAbove_range_of_hasCompactSupport hgc
  obtain ⟨a, b, hab, hgt⟩ := exists_time_window_of_hasCompactSupport g hgc
  refine ⟨(b - a) * max C 0, mul_nonneg (sub_nonneg.mpr hab) (le_max_right C 0), ?_⟩
  intro p
  have hnon : 0 ≤ duhamelPotential K τplus g p :=
    integral_nonneg (fun r => duhamelIntegrand_nonneg K g hgn p r)
  rw [abs_of_nonneg hnon]
  exact duhamelPotential_le_time_window K τplus g hgn (max C 0) (le_max_right C 0)
    (fun q => (hC (mem_range_self q)).trans (le_max_left C 0)) a b hab hgt p

/-- The source potential is bounded Borel for continuous compact nonnegative sources. -/
theorem duhamelPotential_boundedBorel {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)
    (hγ : Continuous γ) (τplus : ℝ) (g : KineticPoint d → ℝ)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgn : ∀ p, 0 ≤ g p) :
    Measurable (duhamelPotential K τplus g) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ p, |duhamelPotential K τplus g p| ≤ C :=
  ⟨measurable_duhamelPotential K hΩ hγ τplus g hg.measurable,
    duhamelPotential_exists_bound K τplus g hg hgc hgn⟩


/-- A bounded Borel spacetime source restricted to one absolute-time state slice. -/
def duhamelSlice {d : ℕ} (g : BoundedBorel (KineticPoint d)) (r : ℝ) :
    BoundedBorel (EvolutionAmbientState d) := by
  refine ⟨fun w => g ⟨r, w.1, w.2⟩, ?_, ?_⟩
  · convert g.measurable.comp ((KineticPoint.measurable_equivProd_symm d).comp
      (measurable_const.prodMk measurable_id)) using 1
    rfl
  · obtain ⟨C, hC, hg⟩ := g.exists_bound
    exact ⟨C, hC, fun w => hg ⟨r, w.1, w.2⟩⟩

/-- Each source-time kernel integral equals the supplied terminal evolution action. -/
theorem duhamelSourceIntegral_eq_evolution {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (hΩ : MeasurableSet Ω)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (g : BoundedBorel (KineticPoint d)) (σ r : ℝ) (hσr : σ ≤ r)
    (p : EvolutionState Ω γ σ) :
    duhamelSourceIntegral K g (evolutionQueryOfState Ω γ σ r hσr p) =
      S σ r hσr (terminalStateDatum (duhamelSlice g r)) p := by
  rw [hreal.2.1 σ r hσr p (terminalStateDatum (duhamelSlice g r))]
  unfold duhamelSourceIntegral
  rw [← K.map_fiberKernel_eq_master hΩ σ r hσr p]
  exact integral_map measurable_subtype_coe.aemeasurable
    (duhamelSlice g r).measurable.aestronglyMeasurable


variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- A continuous compactly supported kinetic source as bounded Borel data. -/
def duhamelSourceBorel (g : KineticPoint d → ℝ) (hg : Continuous g)
    (hc : HasCompactSupport g) : BoundedBorel (KineticPoint d) :=
  ⟨g, hg.measurable, by
    obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hc
    refine ⟨max C 0, le_max_right _ _, fun p => ?_⟩
    simpa only [Real.norm_eq_abs] using (hC p).trans (le_max_left _ _)⟩


/-- The supplied terminal evolution identifies every source slice with a classical solution. -/
theorem exists_duhamelSlice_solution (hΩ : MeasurableSet Ω)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (g : KineticPoint d → ℝ) (hg : Continuous g) (hc : HasCompactSupport g)
    (hs : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d =>
      g ⟨q.1, q.2.1, q.2.2⟩)) (T : ℝ)
    (hU : tsupport g ⊆ evolutionPastOpenCylinder Ω γ T) (r : ℝ) :
    ∃ V : KineticPoint d → ℝ,
      IsClassicalTerminalSolution Ω γ B b r
        (duhamelSlice (duhamelSourceBorel g hg hc) r) V ∧
      ∀ (s : ℝ) (hsr : s ≤ r) (p : EvolutionState Ω γ s),
        V ⟨s, p.1.1, p.1.2⟩ =
          duhamelSourceIntegral K g (evolutionQueryOfState Ω γ s r hsr p)  := by
  have isSmoothCompactTerminalDatum_duhamelSlice :
      IsSmoothCompactTerminalDatum Ω γ r (duhamelSlice (duhamelSourceBorel g hg hc) r) := by
    let f : EvolutionAmbientState d → ℝ := fun w => g ⟨r, w.1, w.2⟩
    let P : KineticPoint d → EvolutionAmbientState d := fun p => (p.position, p.velocity)
    have hP : Continuous P := continuous_position.prodMk continuous_velocity
    have hsub : tsupport f ⊆ P '' (tsupport g ∩ KineticPoint.time ⁻¹' {r}) := by
      apply closure_minimal
      · intro w hw
        exact ⟨⟨r, w.1, w.2⟩, ⟨subset_closure hw, rfl⟩, rfl⟩
      · exact ((hc.inter_right (isClosed_eq continuous_time continuous_const)).image hP).isClosed
    refine ⟨hs.comp (contDiff_const.prodMk contDiff_id), ?_, ?_⟩
    · exact ((hc.inter_right (isClosed_eq continuous_time continuous_const)).image hP
        ).of_isClosed_subset (isClosed_tsupport f) hsub
    · intro w hw
      obtain ⟨p, ⟨hp, hpr⟩, rfl⟩ := hsub hw
      refine ⟨?_, mem_univ _⟩
      change p.time = r at hpr
      simpa only [hpr] using ((hU hp).2)
  obtain ⟨V, hV, hVS, -⟩ := hreal.1 r _
    (isSmoothCompactTerminalDatum_duhamelSlice)
  refine ⟨V, hV, fun s hsr p => ?_⟩
  rw [hVS s hsr p]
  exact (duhamelSourceIntegral_eq_evolution hΩ B b S K hreal
    (duhamelSourceBorel g hg hc) s r hsr p).symm

/-- On the closed source cylinder the zero-extended integrand is the classical slice solution. -/
theorem duhamelIntegrand_eq_slice_solution (hΩa : IsAdmissibleEvolutionDomain Ω)
    (K : MovingFiberKernel Ω γ) (g : KineticPoint d → ℝ) (r : ℝ)
    (V : KineticPoint d → ℝ)
    (hlat : ∀ p ∈ evolutionLateralFrontier Ω γ r, V p = 0)
    (hV : ∀ (s : ℝ) (hsr : s ≤ r) (p : EvolutionState Ω γ s),
      V ⟨s, p.1.1, p.1.2⟩ =
        duhamelSourceIntegral K g (evolutionQueryOfState Ω γ s r hsr p))
    (p : KineticPoint d) (hp : p ∈ evolutionPastClosedCylinder Ω γ r) :
    duhamelIntegrand K g p r = V p := by
  classical
  by_cases hm : p.position ∈ movingDomain Ω γ p.time
  · rw [duhamelIntegrand, dite_eq_left ⟨hp.1, hm⟩]
    exact (hV p.time hp.1 ⟨(p.position, p.velocity), hm, mem_univ _⟩).symm
  · rw [duhamelIntegrand, dite_eq_right (fun h => hm h.2)]
    have hf : p.position ∈ frontier (movingDomain Ω γ p.time) := by
      rw [(isOpen_movingDomain_of_isAdmissibleEvolutionDomain γ hΩa p.time).frontier_eq]
      exact ⟨hp.2, hm⟩
    exact (hlat p ⟨hp.1, hf⟩).symm

/-- Source slices are continuous on their closed past cylinders. -/
theorem continuousOn_duhamelIntegrand (hΩa : IsAdmissibleEvolutionDomain Ω)
    (hΩ : MeasurableSet Ω) (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (g : KineticPoint d → ℝ) (hg : Continuous g) (hc : HasCompactSupport g)
    (hs : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d =>
      g ⟨q.1, q.2.1, q.2.2⟩)) (T : ℝ)
    (hU : tsupport g ⊆ evolutionPastOpenCylinder Ω γ T) (r : ℝ) :
    ContinuousOn (fun p => duhamelIntegrand K g p r)
      (evolutionPastClosedCylinder Ω γ r) := by
  obtain ⟨V, hV, hVe⟩ := exists_duhamelSlice_solution hΩ B b S K hreal g hg hc hs T hU r
  exact hV.2.1.congr (fun p hp =>
    duhamelIntegrand_eq_slice_solution hΩa K g r V hV.2.2.2.2.2 hVe p hp)

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

