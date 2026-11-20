module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Green
public import HypoellipticAleksandrov.Parabolic.Geometry
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Parabolic Duhamel potentials against the marginal kernel

For a source `g` on `ℝ × ℝ^d` the parabolic Duhamel potential is
`W(s,v) = ∫_s^T ∫ g(r,w) P_{s,r}(v,dw) dr`, where `P` is the parabolic marginal kernel
`parabolicMarginalKernel` of a supplied moving-fiber kernel, extended by zero outside the
starting fiber.  This module defines the integrand and the potential, identifies the source
integrals with integrals against the master kernel, and proves joint Borel measurability and the
elementary bounds `0 ≤ W ≤ (T - s) sup g`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open scoped ENNReal ProbabilityTheory

variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

section
variable (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω) (T : ℝ) (g : TimeVelocity d → ℝ)
    (s r : ℝ) (hgn : ∀ p, 0 ≤ g p) (p : TimeVelocity d) (h : s ≤ r) (C : ℝ)
    (y : EvolutionPosition Ω γ s) (hgb : ∀ p, g p ≤ C) (z : PDE.Vec d) (q : EvolutionQuery Ω γ)
    (hz : parabolicMarginalKernel K hΩ s r h y =
      K.fiberFirstMarginal hΩ s r h (evolutionStateOfPosition Ω γ s y z))
    (hg : Measurable (fun v : PDE.Vec d => g (r, v)))

include K hΩ g h y in
/-- The source integral `∫ g(r,w) P_{s,r}(y,dw)` against the parabolic marginal kernel. -/
def parabolicSourceIntegral : ℝ :=
  ∫ y', g (r, y'.1) ∂(parabolicMarginalKernel K hΩ s r h y)

include K hΩ g p in
/-- The source-time integrand, extended by zero outside the valid starting fiber. -/
def parabolicDuhamelIntegrand (r : ℝ) : ℝ := by
  classical
  exact if h : p.1 ≤ r ∧ p.2 ∈ movingDomain Ω γ p.1 then
    parabolicSourceIntegral K hΩ g p.1 r h.1 ⟨p.2, h.2⟩ else 0

include K hΩ T g p in
/-- The parabolic Duhamel potential `W(s,v) = ∫_s^T ∫ g(r,w) P_{s,r}(v,dw) dr`,
extended by zero outside the starting fiber. -/
def parabolicDuhamelPotential : ℝ :=
  ∫ r in Ioc p.1 T, parabolicDuhamelIntegrand K hΩ g p r

include K g q in
/-- The source integral against the master kernel, at a valid query. -/
def parabolicMasterIntegral : ℝ :=
  ∫ w, g (q.1.2.1, w.1) ∂K.master q

include hz hg in
/-- If the marginal kernel at `y` is the first marginal of the fiber kernel at the state `(y, z)`,
the marginal-kernel source integral is the master-kernel integral of the first coordinate. -/
theorem parabolicSourceIntegral_eq_master_of_state :
    parabolicSourceIntegral K hΩ g s r h y =
      parabolicMasterIntegral K g ⟨(s, (r, (y.1, z))), h, y.2, mem_univ _⟩ := by
  unfold parabolicSourceIntegral parabolicMasterIntegral
  rw [hz, MovingFiberKernel.fiberFirstMarginal,
    ProbabilityTheory.Kernel.map_apply _ (MovingFiberKernel.measurable_firstPosition Ω γ r)]
  rw [integral_map (f := fun y' : EvolutionPosition Ω γ r => g (r, y'.1))
    (MovingFiberKernel.measurable_firstPosition Ω γ r).aemeasurable (hg.comp measurable_subtype_coe).aestronglyMeasurable]
  have hq := K.map_fiberKernel_eq_master hΩ s r h (evolutionStateOfPosition Ω γ s y z)
  have hf2 : Measurable (fun w : EvolutionAmbientState d => g (r, w.1)) :=
    hg.comp measurable_fst
  change _ = ∫ w, g (r, w.1) ∂K.master
    (evolutionQueryOfState Ω γ s r h (evolutionStateOfPosition Ω γ s y z))
  rw [← hq, integral_map (f := fun w : EvolutionAmbientState d => g (r, w.1))
    measurable_subtype_coe.aemeasurable hf2.aestronglyMeasurable]
  rfl

include hg in
/-- The marginal-kernel source integral is the master-kernel integral at `z = 0`. -/
theorem parabolicSourceIntegral_eq_master :
    parabolicSourceIntegral K hΩ g s r h y =
      parabolicMasterIntegral K g ⟨(s, (r, (y.1, 0))), h, y.2, mem_univ _⟩ :=
  parabolicSourceIntegral_eq_master_of_state K hΩ g s r h y 0 rfl hg

/-- The master-kernel source integral is Borel in the query. -/
theorem measurable_parabolicMasterIntegral (hg : Measurable g) :
    Measurable (parabolicMasterIntegral K g) := by
  have hm : Measurable (fun q : EvolutionQuery Ω γ × EvolutionAmbientState d =>
      g (q.1.1.2.1, q.2.1)) := by
    fun_prop
  exact (hm.stronglyMeasurable.integral_kernel_prod_right' (κ := K.master)).measurable

include hgn in
/-- Nonnegative sources have nonnegative master integrals. -/
theorem parabolicMasterIntegral_nonneg : 0 ≤ parabolicMasterIntegral K g q :=
  integral_nonneg (fun _ => hgn _)

include hgn hgb in
/-- Contraction bounds the master integral of a bounded nonnegative source. -/
theorem parabolicMasterIntegral_le :
    parabolicMasterIntegral K g q ≤ C := by
  have hC := (hgn (0, 0)).trans (hgb _)
  have hn : ‖parabolicMasterIntegral K g q‖ ≤ C * (K.master q).real univ := by
    apply norm_integral_le_of_norm_le_const
    exact Filter.Eventually.of_forall fun _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hgn _)]
      apply hgb
  have hm : (K.master q).real univ ≤ 1 := by
    exact ENNReal.toReal_mono ENNReal.one_ne_top (K.mass_le_one q)
  rw [Real.norm_eq_abs] at hn
  exact (le_abs_self _).trans (hn.trans (by nlinarith))

end

variable (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)

section
variable (g : TimeVelocity d → ℝ) (p : TimeVelocity d) (r : ℝ)

/-- Away from the valid fiber the integrand is zero. -/
theorem parabolicDuhamelIntegrand_of_not_valid (h : ¬ (p.1 ≤ r ∧ p.2 ∈ movingDomain Ω γ p.1)) :
    parabolicDuhamelIntegrand K hΩ g p r = 0 := by
  exact dite_eq_right h

/-- On the valid fiber the integrand is the marginal-kernel source integral. -/
theorem parabolicDuhamelIntegrand_of_valid (h : p.1 ≤ r ∧ p.2 ∈ movingDomain Ω γ p.1) :
    parabolicDuhamelIntegrand K hΩ g p r =
      parabolicSourceIntegral K hΩ g p.1 r h.1 ⟨p.2, h.2⟩ := by
  exact dite_eq_left h

end

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
    solve_by_elim [parabolicSourceIntegral_eq_master]
  · rw [parabolicDuhamelIntegrand_of_not_valid K hΩ g p r h]
    grind

variable (T : ℝ) (hγ : Continuous γ) (g : TimeVelocity d → ℝ)
    (hg : ∀ r, Measurable (fun v : PDE.Vec d => g (r, v))) (hgn : ∀ p, 0 ≤ g p) (C : ℝ)
    (hgb : ∀ p, g p ≤ C) (p : TimeVelocity d) (r : ℝ)

include hg hgn in
/-- Nonnegativity of the integrand for a nonnegative Borel source. -/
theorem parabolicDuhamelIntegrand_nonneg : 0 ≤ parabolicDuhamelIntegrand K hΩ g p r := by
  rw [parabolicDuhamelIntegrand_eq_master K hΩ g hg]
  split_ifs
  · exact parabolicMasterIntegral_nonneg K g hgn _
  positivity

include hg hgn hgb in
/-- Upper bound of the integrand by any upper bound of a nonnegative source. -/
theorem parabolicDuhamelIntegrand_le :
    parabolicDuhamelIntegrand K hΩ g p r ≤ C := by
  rw [parabolicDuhamelIntegrand_eq_master K hΩ g hg]
  split_ifs
  · apply parabolicMasterIntegral_le <;> assumption
  · exact (hgn (0, 0)).trans (hgb _)

include hγ in
/-- Joint Borel dependence of the integrand on the point and the source time. -/
theorem measurable_parabolicDuhamelIntegrand
    (hgm : Measurable g) :
    Measurable (fun q : TimeVelocity d × ℝ => parabolicDuhamelIntegrand K hΩ g q.1 q.2) := by
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
    simp only [D, mem_ofPred_eq, mem_inter_iff]
    change (_ ∧ _ ∈ PDE.translateSet (γ q.1.1) Ω) ↔ _
    rw [PDE.mem_translateSet_iff_sub_mem]
  let Q : D → EvolutionQuery Ω γ := fun q =>
    ⟨(q.1.1.1, (q.1.2, (q.1.1.2, 0))), q.2.1, q.2.2, mem_univ _⟩
  have hQ : Measurable Q := by
    fun_prop
  convert (((measurable_parabolicMasterIntegral K g hgm).comp hQ).dite measurable_const hD) using 1
  funext q
  apply parabolicDuhamelIntegrand_eq_master <;> assumption

include hg in
/-- The integrand vanishes at source times whose slice of the source is zero. -/
theorem parabolicDuhamelIntegrand_eq_zero_of_slice
    (h0 : ∀ v, g (r, v) = 0) : parabolicDuhamelIntegrand K hΩ g p r = 0 := by
  rw [parabolicDuhamelIntegrand_eq_master K hΩ g hg]
  simp_all [parabolicMasterIntegral, h0]

include hg hgn in
/-- The potential of a nonnegative source is nonnegative. -/
theorem parabolicDuhamelPotential_nonneg : 0 ≤ parabolicDuhamelPotential K hΩ T g p :=
  integral_nonneg (fun r => parabolicDuhamelIntegrand_nonneg K hΩ g hg hgn p r)

include hg hgn hgb in
/-- Contraction gives the Duhamel estimate `W ≤ (T - s) C` for `g ≤ C`. -/
theorem parabolicDuhamelPotential_le (hp : p.1 ≤ T) :
    parabolicDuhamelPotential K hΩ T g p ≤ (T - p.1) * C := by
  have hnon := parabolicDuhamelPotential_nonneg K hΩ T g hg hgn p
  have hn := norm_integral_le_of_norm_le_const
    (μ := volume.restrict (Ioc p.1 T)) (f := parabolicDuhamelIntegrand K hΩ g p)
    (C := C) (Filter.Eventually.of_forall fun r => by
      rw [Real.norm_eq_abs, abs_of_nonneg (parabolicDuhamelIntegrand_nonneg K hΩ g hg hgn p r)]
      apply parabolicDuhamelIntegrand_le <;> assumption)
  unfold parabolicDuhamelPotential at hnon ⊢
  simp_all <;> grind

/-- At and after the terminal time the potential vanishes. -/
theorem parabolicDuhamelPotential_eq_zero_of_terminal_le (hp : T ≤ p.1) : parabolicDuhamelPotential K hΩ T g p = 0 := by
  rw [parabolicDuhamelPotential, Ioc_eq_empty_of_le hp, Measure.restrict_empty,
    integral_zero_measure]

/-- Outside the open starting fiber the zero extension vanishes. -/
theorem parabolicDuhamelPotential_eq_zero_of_not_mem (hp : p.2 ∉ movingDomain Ω γ p.1) :
    parabolicDuhamelPotential K hΩ T g p = 0 := by
  have hz : parabolicDuhamelIntegrand K hΩ g p = 0 := by
    funext r
    exact parabolicDuhamelIntegrand_of_not_valid K hΩ g p r (fun h => hp h.2)
  simp [parabolicDuhamelPotential, hz]

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
