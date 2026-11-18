module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Green
public import HypoellipticAleksandrov.Parabolic.Geometry
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Integral.Prod

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
section

open MeasureTheory Set
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open scoped ENNReal ProbabilityTheory

variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- The source integral `∫ g(r,w) P_{s,r}(y,dw)` against the parabolic marginal kernel. -/
def parabolicSourceIntegral (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)
    (g : TimeVelocity d → ℝ) (s r : ℝ) (h : s ≤ r) (y : EvolutionPosition Ω γ s) : ℝ :=
  ∫ y', g (r, y'.1) ∂(parabolicMarginalKernel K hΩ s r h y)

/-- The source-time integrand, extended by zero outside the valid starting fiber. -/
def parabolicDuhamelIntegrand (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)
    (g : TimeVelocity d → ℝ) (p : TimeVelocity d) (r : ℝ) : ℝ := by
  classical
  exact if h : p.1 ≤ r ∧ p.2 ∈ movingDomain Ω γ p.1 then
    parabolicSourceIntegral K hΩ g p.1 r h.1 ⟨p.2, h.2⟩ else 0

/-- The parabolic Duhamel potential `W(s,v) = ∫_s^T ∫ g(r,w) P_{s,r}(v,dw) dr`,
extended by zero outside the starting fiber. -/
def parabolicDuhamelPotential (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω) (T : ℝ)
    (g : TimeVelocity d → ℝ) (p : TimeVelocity d) : ℝ :=
  ∫ r in Ioc p.1 T, parabolicDuhamelIntegrand K hΩ g p r

/-- The source integral against the master kernel, at a valid query. -/
def parabolicMasterIntegral (K : MovingFiberKernel Ω γ) (g : TimeVelocity d → ℝ)
    (q : EvolutionQuery Ω γ) : ℝ :=
  ∫ w, g (q.1.2.1, w.1) ∂K.master q


/-- The marginal-kernel source integral is the master-kernel integral at `z = 0`. -/
theorem parabolicSourceIntegral_eq_master (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)
    (g : TimeVelocity d → ℝ) (s r : ℝ) (h : s ≤ r) (y : EvolutionPosition Ω γ s)
    (hg : Measurable (fun v : PDE.Vec d => g (r, v))) :
    parabolicSourceIntegral K hΩ g s r h y =
      parabolicMasterIntegral K g ⟨(s, (r, (y.1, 0))), h, y.2, mem_univ _⟩  := by
  have parabolicSourceIntegral_eq_master_of_state (hΩ : MeasurableSet Ω) (g : TimeVelocity d → ℝ) (s : ℝ) (r : ℝ) (h : s ≤ r) (y : EvolutionPosition Ω γ s) (z : PDE.Vec d) (hz : parabolicMarginalKernel K hΩ s r h y =
      K.fiberFirstMarginal hΩ s r h (evolutionStateOfPosition Ω γ s y z)) (hg : Measurable (fun v => g (r, v))) :
      parabolicSourceIntegral K hΩ g s r h y =
      parabolicMasterIntegral K g ⟨(s, (r, (y.1, z))), h, y.2, mem_univ _⟩ := by
    unfold parabolicSourceIntegral parabolicMasterIntegral
    rw [hz, MovingFiberKernel.fiberFirstMarginal,
      ProbabilityTheory.Kernel.map_apply _ (MovingFiberKernel.measurable_firstPosition Ω γ r)]
    have hf : Measurable (fun y' : EvolutionPosition Ω γ r => g (r, y'.1)) :=
      hg.comp measurable_subtype_coe
    rw [integral_map (f := fun y' => g (r, y'.1))
      (MovingFiberKernel.measurable_firstPosition Ω γ r).aemeasurable hf.aestronglyMeasurable]
    have hq := K.map_fiberKernel_eq_master hΩ s r h (evolutionStateOfPosition Ω γ s y z)
    have hf2 : Measurable (fun w : EvolutionAmbientState d => g (r, w.1)) :=
      hg.comp measurable_fst
    change _ = ∫ w, g (r, w.1) ∂K.master
      (evolutionQueryOfState Ω γ s r h (evolutionStateOfPosition Ω γ s y z))
    rw [← hq, integral_map (f := fun w : EvolutionAmbientState d => g (r, w.1))
      measurable_subtype_coe.aemeasurable hf2.aestronglyMeasurable]
    rfl
  exact parabolicSourceIntegral_eq_master_of_state hΩ g s r h y 0 rfl hg




variable (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)

/-- Away from the valid fiber the integrand is zero. -/
theorem parabolicDuhamelIntegrand_of_not_valid (g : TimeVelocity d → ℝ) (p : TimeVelocity d)
    (r : ℝ) (h : ¬ (p.1 ≤ r ∧ p.2 ∈ movingDomain Ω γ p.1)) :
    parabolicDuhamelIntegrand K hΩ g p r = 0 := by
  unfold parabolicDuhamelIntegrand
  exact dite_eq_right h

/-- On the valid fiber the integrand is the marginal-kernel source integral. -/
theorem parabolicDuhamelIntegrand_of_valid (g : TimeVelocity d → ℝ) (p : TimeVelocity d)
    (r : ℝ) (h : p.1 ≤ r ∧ p.2 ∈ movingDomain Ω γ p.1) :
    parabolicDuhamelIntegrand K hΩ g p r =
      parabolicSourceIntegral K hΩ g p.1 r h.1 ⟨p.2, h.2⟩ := by
  unfold parabolicDuhamelIntegrand
  exact dite_eq_left h

open Classical in
/-- The integrand equals the zero-extended master-kernel integral. -/
theorem parabolicDuhamelIntegrand_eq_master (g : TimeVelocity d → ℝ)
    (hg : ∀ r, Measurable (fun v : PDE.Vec d => g (r, v))) (p : TimeVelocity d) (r : ℝ) :
    parabolicDuhamelIntegrand K hΩ g p r =
      if h : p.1 ≤ r ∧ p.2 ∈ movingDomain Ω γ p.1 then
        parabolicMasterIntegral K g ⟨(p.1, (r, (p.2, 0))), h.1, h.2, mem_univ _⟩ else 0 := by
  by_cases h : p.1 ≤ r ∧ p.2 ∈ movingDomain Ω γ p.1
  · rw [parabolicDuhamelIntegrand_of_valid K hΩ g p r h]
    simp only [h, and_self, ↓reduceDIte]
    exact parabolicSourceIntegral_eq_master K hΩ g p.1 r h.1 ⟨p.2, h.2⟩ (hg r)
  · rw [parabolicDuhamelIntegrand_of_not_valid K hΩ g p r h]
    simp only [h, ↓reduceDIte]

/-- Nonnegativity of the integrand for a nonnegative Borel source. -/
theorem parabolicDuhamelIntegrand_nonneg (g : TimeVelocity d → ℝ)
    (hg : ∀ r, Measurable (fun v : PDE.Vec d => g (r, v))) (hgn : ∀ p, 0 ≤ g p)
    (p : TimeVelocity d) (r : ℝ) : 0 ≤ parabolicDuhamelIntegrand K hΩ g p r  := by
  have parabolicMasterIntegral_nonneg (K : MovingFiberKernel Ω γ) (q : EvolutionQuery Ω γ) : 0 ≤ parabolicMasterIntegral K g q :=
    integral_nonneg (fun _ => hgn _)
  rw [parabolicDuhamelIntegrand_eq_master K hΩ g hg]
  split_ifs
  · exact parabolicMasterIntegral_nonneg K _
  · exact le_rfl

/-- Upper bound of the integrand by any upper bound of a nonnegative source. -/
theorem parabolicDuhamelIntegrand_le (g : TimeVelocity d → ℝ)
    (hg : ∀ r, Measurable (fun v : PDE.Vec d => g (r, v))) (hgn : ∀ p, 0 ≤ g p)
    (C : ℝ) (hgb : ∀ p, g p ≤ C) (p : TimeVelocity d) (r : ℝ) :
    parabolicDuhamelIntegrand K hΩ g p r ≤ C  := by
  have parabolicMasterIntegral_le (K : MovingFiberKernel Ω γ) (q : EvolutionQuery Ω γ) :
      parabolicMasterIntegral K g q ≤ C := by
    have hC := (hgn (0, 0)).trans (hgb _)
    have hn : ‖parabolicMasterIntegral K g q‖ ≤ C * (K.master q).real univ := by
      apply norm_integral_le_of_norm_le_const
      exact Filter.Eventually.of_forall fun _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hgn _)]
        exact hgb _
    have hm : (K.master q).real univ ≤ 1 := by
      simpa only [Measure.real, ENNReal.toReal_one] using
        ENNReal.toReal_mono ENNReal.one_ne_top (K.mass_le_one q)
    rw [Real.norm_eq_abs] at hn
    exact (le_abs_self _).trans (hn.trans (by nlinarith))
  rw [parabolicDuhamelIntegrand_eq_master K hΩ g hg]
  split_ifs
  · exact parabolicMasterIntegral_le K _
  · exact (hgn (0, 0)).trans (hgb _)

/-- Joint Borel dependence of the integrand on the point and the source time. -/
theorem measurable_parabolicDuhamelIntegrand (hγ : Continuous γ) (g : TimeVelocity d → ℝ)
    (hgm : Measurable g) :
    Measurable (fun q : TimeVelocity d × ℝ => parabolicDuhamelIntegrand K hΩ g q.1 q.2)  := by
  have measurable_parabolicMasterIntegral (K : MovingFiberKernel Ω γ) (hg : Measurable g) :
      Measurable (parabolicMasterIntegral K g) := by
    have hm : Measurable (fun q : EvolutionQuery Ω γ × EvolutionAmbientState d =>
        g (q.1.1.2.1, q.2.1)) := by
      have ht : Measurable (fun q : EvolutionQuery Ω γ × EvolutionAmbientState d =>
          q.1.1.2.1) := measurable_subtype_coe.snd.fst.comp measurable_fst
      exact hg.comp (ht.prodMk (measurable_snd.fst))
    exact (hm.stronglyMeasurable.integral_kernel_prod_right' (κ := K.master)).measurable
  classical
  have hg : ∀ r, Measurable (fun v : PDE.Vec d => g (r, v)) := fun r =>
    hgm.comp (measurable_const.prodMk measurable_id)
  let D : Set (TimeVelocity d × ℝ) :=
    {q | q.1.1 ≤ q.2 ∧ q.1.2 ∈ movingDomain Ω γ q.1.1}
  have hD : MeasurableSet D := by
    have ht : MeasurableSet {q : TimeVelocity d × ℝ | q.1.1 ≤ q.2} :=
      measurableSet_le (measurable_fst.fst) measurable_snd
    have hp : MeasurableSet {q : TimeVelocity d × ℝ | q.1.2 - γ q.1.1 ∈ Ω} :=
      hΩ.preimage ((measurable_fst.snd).sub (hγ.measurable.comp measurable_fst.fst))
    convert ht.inter hp using 1
    ext q
    simp
    change (_ ∧ _ ∈ PDE.translateSet (γ q.1.1) Ω) ↔ _
    rw [PDE.mem_translateSet_iff_sub_mem]
  let Q : D → EvolutionQuery Ω γ := fun q =>
    ⟨(q.1.1.1, (q.1.2, (q.1.1.2, 0))), q.2.1, q.2.2, mem_univ _⟩
  have hQ : Measurable Q := by
    apply Measurable.subtype_mk
    exact (measurable_subtype_coe.fst.fst).prodMk
      (measurable_subtype_coe.snd.prodMk
        ((measurable_subtype_coe.fst.snd).prodMk measurable_const))
  have hmi : Measurable (fun q : TimeVelocity d × ℝ =>
      if h : q.1.1 ≤ q.2 ∧ q.1.2 ∈ movingDomain Ω γ q.1.1 then
        parabolicMasterIntegral K g ⟨(q.1.1, (q.2, (q.1.2, 0))), h.1, h.2, mem_univ _⟩
      else 0) :=
    ((measurable_parabolicMasterIntegral K hgm).comp hQ).dite measurable_const hD
  convert hmi using 1
  funext q
  exact parabolicDuhamelIntegrand_eq_master K hΩ g hg q.1 q.2

/-- The integrand vanishes at source times whose slice of the source is zero. -/
theorem parabolicDuhamelIntegrand_eq_zero_of_slice (g : TimeVelocity d → ℝ)
    (hg : ∀ r, Measurable (fun v : PDE.Vec d => g (r, v))) (p : TimeVelocity d) (r : ℝ)
    (h0 : ∀ v, g (r, v) = 0) : parabolicDuhamelIntegrand K hΩ g p r = 0 := by
  rw [parabolicDuhamelIntegrand_eq_master K hΩ g hg]
  split_ifs
  · simp only [parabolicMasterIntegral, h0, integral_zero]
  · exact rfl

/-- The potential of a nonnegative source is nonnegative. -/
theorem parabolicDuhamelPotential_nonneg (T : ℝ) (g : TimeVelocity d → ℝ)
    (hg : ∀ r, Measurable (fun v : PDE.Vec d => g (r, v))) (hgn : ∀ p, 0 ≤ g p)
    (p : TimeVelocity d) : 0 ≤ parabolicDuhamelPotential K hΩ T g p :=
  integral_nonneg (fun r => parabolicDuhamelIntegrand_nonneg K hΩ g hg hgn p r)

/-- Contraction gives the Duhamel estimate `W ≤ (T - s) C` for `g ≤ C`. -/
theorem parabolicDuhamelPotential_le (T : ℝ) (g : TimeVelocity d → ℝ)
    (hg : ∀ r, Measurable (fun v : PDE.Vec d => g (r, v))) (hgn : ∀ p, 0 ≤ g p)
    (C : ℝ) (hgb : ∀ p, g p ≤ C) (p : TimeVelocity d) (hp : p.1 ≤ T) :
    parabolicDuhamelPotential K hΩ T g p ≤ (T - p.1) * C := by
  have hnon := parabolicDuhamelPotential_nonneg K hΩ T g hg hgn p
  have hn := norm_integral_le_of_norm_le_const
    (μ := volume.restrict (Ioc p.1 T))
    (C := C) (Filter.Eventually.of_forall fun r => by
      rw [Real.norm_eq_abs, abs_of_nonneg (parabolicDuhamelIntegrand_nonneg K hΩ g hg hgn p r)]
      exact parabolicDuhamelIntegrand_le K hΩ g hg hgn C hgb p r)
  unfold parabolicDuhamelPotential at hnon ⊢
  rw [Real.norm_eq_abs, abs_of_nonneg hnon] at hn
  simpa only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hp), mul_comm] using hn

/-- At and after the terminal time the potential vanishes. -/
theorem parabolicDuhamelPotential_eq_zero_of_terminal_le (T : ℝ) (g : TimeVelocity d → ℝ)
    (p : TimeVelocity d) (hp : T ≤ p.1) : parabolicDuhamelPotential K hΩ T g p = 0 := by
  rw [parabolicDuhamelPotential, Ioc_eq_empty_of_le hp, Measure.restrict_empty,
    integral_zero_measure]

/-- Outside the open starting fiber the zero extension vanishes. -/
theorem parabolicDuhamelPotential_eq_zero_of_not_mem (T : ℝ) (g : TimeVelocity d → ℝ)
    (p : TimeVelocity d) (hp : p.2 ∉ movingDomain Ω γ p.1) :
    parabolicDuhamelPotential K hΩ T g p = 0 := by
  have hz : parabolicDuhamelIntegrand K hΩ g p = 0 := by
    funext r
    exact parabolicDuhamelIntegrand_of_not_valid K hΩ g p r (fun h => hp h.2)
  simp [parabolicDuhamelPotential, hz, integral_zero]

end

open MeasureTheory Set
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open scoped ENNReal ProbabilityTheory

variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- The open starting set `U₀ = {(s,v) : s < T, v ∈ Ω_s}` of the Duhamel potential. -/
def duhamelFiber (Ω : Set (PDE.Vec d)) (γ : ℝ → PDE.Vec d) (T : ℝ) : Set (TimeVelocity d) :=
  {p | p.1 < T ∧ p.2 ∈ movingDomain Ω γ p.1}

/-- The closed region `{(s,v) : s ≤ T, v ∈ closure Ω_s}` carrying the continuous extension. -/
def duhamelClosedFiber (Ω : Set (PDE.Vec d)) (γ : ℝ → PDE.Vec d) (T : ℝ) :
    Set (TimeVelocity d) :=
  {p | p.1 ≤ T ∧ p.2 ∈ closure (movingDomain Ω γ p.1)}

/-- The open past cylinder at the source time `r`. -/
def sliceOpenCylinder (Ω : Set (PDE.Vec d)) (γ : ℝ → PDE.Vec d) (r : ℝ) :
    Set (TimeVelocity d) :=
  ParabolicProbe.scalarPastOpenCylinder Ω γ r

/-- The closed past cylinder at the source time `r`. -/
def sliceClosedCylinder (Ω : Set (PDE.Vec d)) (γ : ℝ → PDE.Vec d) (r : ℝ) :
    Set (TimeVelocity d) :=
  ParabolicProbe.scalarPastClosedCylinder Ω γ r

/-- The fiber `U₀` is open when the curve is continuous and the base domain is open. -/
theorem isOpen_duhamelFiber (hΩ : IsOpen Ω) (hγ : Continuous γ) (T : ℝ) :
    IsOpen (duhamelFiber Ω γ T) := by
  have hc :=
    continuous_snd.sub (hγ.comp continuous_fst)
  have h1 : IsOpen {p : TimeVelocity d | p.2 - γ p.1 ∈ Ω} := hΩ.preimage hc
  have h2 : IsOpen {p : TimeVelocity d | p.1 < T} := isOpen_lt continuous_fst continuous_const
  convert h2.inter h1 using 1
  ext p
  simp
  change (_ ∧ _ ∈ PDE.translateSet (γ p.1) Ω) ↔ _
  rw [PDE.mem_translateSet_iff_sub_mem]

/-- `U₀` lies in the closed region. -/
theorem duhamelFiber_subset_closedFiber (T : ℝ) :
    duhamelFiber Ω γ T ⊆ duhamelClosedFiber Ω γ T := fun _ hp =>
  ⟨hp.1.le, subset_closure hp.2⟩

/-- The slice `v ↦ g(r,v)` of a continuous compactly supported source, as a bounded Borel
function. -/
def sliceBorel (g : TimeVelocity d → ℝ) (hg : Continuous g) (hc : HasCompactSupport g) (r : ℝ) :
    BoundedBorel (PDE.Vec d) :=
  ⟨fun v => g (r, v), (hg.comp (continuous_const.prodMk continuous_id)).measurable, by
    obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hc
    refine ⟨max C 0, le_max_right _ _, fun v => ?_⟩
    simpa only [Real.norm_eq_abs] using (hC (r, v)).trans (le_max_left _ _)⟩

@[simp] theorem sliceBorel_apply (g : TimeVelocity d → ℝ) (hg : Continuous g)
    (hc : HasCompactSupport g) (r : ℝ) (v : PDE.Vec d) : sliceBorel g hg hc r v = g (r, v) :=
  rfl


variable (K : MovingFiberKernel Ω γ)

/-- The classical solution of the source slice at time `r`, identified with the
marginal-kernel source integral. -/
theorem exists_slice_solution {B : CoefficientField d}
    (hΩ : MeasurableSet Ω)
    (hP : SectionTwo.HasParabolicMarginalBundle Ω γ hΩ (zIndependentCoefficient B) K)
    (g : TimeVelocity d → ℝ) (hgs : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) (T : ℝ)
    (hgU : tsupport g ⊆ duhamelFiber Ω γ T) (r : ℝ) :
    ∃ V : TimeVelocity d → ℝ,
      ParabolicProbe.IsClassicalScalarTerminalSolution Ω γ (zIndependentCoefficient B) r
        (sliceBorel g hgs.continuous hgc r) V ∧
      ∀ (s : ℝ) (hsr : s ≤ r) (y : EvolutionPosition Ω γ s),
        V (s, y.1) = parabolicSourceIntegral K hΩ g s r hsr y  := by
  have isSmoothCompactScalarTerminalDatum_slice :
      ParabolicProbe.IsSmoothCompactScalarTerminalDatum Ω γ r
      (sliceBorel g hgs.continuous hgc r) := by
    have hsub : tsupport (fun v : PDE.Vec d => g (r, v)) ⊆
        Prod.snd '' (tsupport g ∩ Prod.fst ⁻¹' {r}) := by
      apply closure_minimal
      · intro v hv
        exact ⟨(r, v), ⟨subset_closure hv, rfl⟩, rfl⟩
      · exact ((hgc.inter_right (isClosed_eq continuous_fst continuous_const)).image
          continuous_snd).isClosed
    refine ⟨hgs.comp (contDiff_const.prodMk contDiff_id), ?_, ?_⟩
    · exact ((hgc.inter_right (isClosed_eq continuous_fst continuous_const)).image
        continuous_snd).of_isClosed_subset (isClosed_tsupport _) hsub
    · intro v hv
      obtain ⟨p, ⟨hp1, hp2⟩, rfl⟩ := hsub hv
      have : p = (r, p.2) := Prod.ext hp2 rfl
      have h := (hgU hp1).2
      rw [hp2] at h
      exact h
  obtain ⟨Q, -, -, -, -, -, h6, -, -, -, h10⟩ := hP (fun σ y z z' => rfl)
  obtain ⟨V, hV, hVQ, -⟩ := h10 r (sliceBorel g hgs.continuous hgc r)
    (isSmoothCompactScalarTerminalDatum_slice)
  refine ⟨V, hV, fun s hsr y => ?_⟩
  rw [hVQ s hsr y, h6 s r hsr y (terminalPositionDatum (sliceBorel g hgs.continuous hgc r))]
  rfl

end HypoellipticAleksandrov.KineticAleksandrov.Occupation

