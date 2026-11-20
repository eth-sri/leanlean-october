module

import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.MarginalCutoffLimitClassical
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.MarginalRegularityScalar
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TranslationCovariance
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalIntegralOperator

/-!
# The canonical scalar marginal solution (Proposition 2.1)

Companion paper, Proposition 2.1 (marginal smoothness and the scalar marginal clause).  Assume `B`
does not depend on the transported coordinate (`hBz`), and let `F` be a smooth compactly supported
scalar datum in the moving terminal domain.

1. The cutoff solutions `u_N` of `F(y) χ_N(z)` (from the premise `hEx`) converge on the whole past
   closed cylinder to a classical solution `V` of the `z`-independent datum `F(y)`
   (`exists_cutoff_limit_classical`, uses the Hörmander input `hH`).
2. `V` is the canonical integral `∫ F(y') dμ_{σ,y,z}(y', z')` of the terminal measures,
   by bounded convergence, and is `z`-independent by the translation covariance.
3. Restricting to `z = 0` gives the scalar classical solution; the scalar solution is unique
   (the lifted scalar solution is a kinetic classical solution with the same datum).

The statement holds for every `K : MovingFiberKernel Ω γ` whose master measures are
the terminal measures `μ q` of terminal measures (the master kernel `K₀` is such a kernel by
definition), in the pattern of `terminalKernel_translation_of_master_eq`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set MeasureTheory
open scoped Topology ENNReal ProbabilityTheory

section EvolutionData

variable {n : ℕ} {lam Lam m L_b : ℝ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (data : TerminalEvolutionData lam Lam m L_b Ω γ B b)
include data

local notation "S" => terminalValue data.exists_solution
local notation "μ" => terminalMeasure data

/-- The limit `V` of the cutoff solutions at a point of the open fiber is the integral of the
`z`-independent datum against the terminal measure, and it is invariant under the shift of the
transported coordinate. -/
theorem terminalMeasure_integral_lowerDatum_limit {τ : ℝ}
    (F : BoundedBorel (PDE.Vec n)) (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, |F x| ≤ C)
    (hF : ParabolicProbe.IsSmoothCompactScalarTerminalDatum Ω γ τ F)
    (u : ℕ → KineticPoint n → ℝ)
    (hu : ∀ N, IsClassicalTerminalSolution Ω γ B b τ (cutoffDatum F N) (u N))
    (σ : ℝ) (hστ : σ ≤ τ) (s : EvolutionState Ω γ σ) (v : ℝ)
    (hv : Tendsto (fun N => u N ⟨σ, s.1.1, s.1.2⟩) atTop (𝓝 v)) :
    v = ∫ x, lowerDatum F x ∂(μ (evolutionQueryOfState Ω γ σ τ hστ s)) := by
  have hspec := terminalMeasure_spec data
    (evolutionQueryOfState Ω γ σ τ hστ s)
  have : IsFiniteMeasure (μ (evolutionQueryOfState Ω γ σ τ hστ s)) :=
    ⟨lt_of_le_of_lt hspec.1 ENNReal.one_lt_top⟩
  have heq : ∀ N, u N ⟨σ, s.1.1, s.1.2⟩ =
      ∫ x, cutoffDatum F N x ∂(μ (evolutionQueryOfState Ω γ σ τ hστ s)) := by
    intro N
    rw [hspec.2.2 (cutoffDatum F N) (cutoffDatum_isSmoothCompact hF N)]
    exact (terminalValue_eq_of_solution data.exists_solution σ τ hστ s _
      (cutoffDatum_isSmoothCompact hF N) (u N) (hu N)).symm
  have hlim : Tendsto (fun N => ∫ x, cutoffDatum F N x ∂(μ (evolutionQueryOfState Ω γ σ τ hστ s)))
      atTop (𝓝 (∫ x, lowerDatum F x ∂(μ (evolutionQueryOfState Ω γ σ τ hστ s)))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun N => (cutoffDatum F N).measurable.aestronglyMeasurable) (integrable_const C)
      (fun N => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · rw [Real.norm_eq_abs]
      exact abs_cutoffDatum_le hC hC0 N x
    · refine tendsto_const_nhds.congr' ?_
      obtain ⟨N₀, hN₀⟩ := exists_nat_ge ‖x.2‖
      filter_upwards [eventually_ge_atTop N₀] with N hN
      rw [cutoffDatum_apply, lowerDatum_apply,
        zCutoffN_eq_one (by
          have : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
          linarith), mul_one]
  exact tendsto_nhds_unique (hv.congr heq) hlim

/-- **Scalar marginal solution** (Proposition 2.1, scalar clause), for
every moving fiber kernel `K` whose master measures are the terminal measures `μ q`.  If `B` does
not depend on the transported coordinate, the canonical marginal integral
`V(σ, y) = ∫ F(y') dK_{σ,τ}` is the unique classical scalar terminal solution with datum
`F` and zero lateral trace.  The Hörmander input `hH` is used for the interior smoothness
of the cutoff limit. -/
theorem exists_classical_terminalMarginal_of_master_eq
    (K : MovingFiberKernel Ω γ) (hK : ∀ q, K.master q = μ q)
    (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec n), B σ y z = B σ y z')
    (τ : ℝ) (F : BoundedBorel (PDE.Vec n))
    (hF : ParabolicProbe.IsSmoothCompactScalarTerminalDatum Ω γ τ F) :
    ∃ V : TimeVelocity n → ℝ,
      ParabolicProbe.IsClassicalScalarTerminalSolution Ω γ B τ F V ∧
      (∀ (σ : ℝ) (hστ : σ ≤ τ) (y : EvolutionPosition Ω γ σ),
        V (σ, y.1) = ∫ y', F y'.1 ∂(parabolicMarginalKernel K
          (measurableSet_of_isAdmissibleEvolutionDomain data.domain) σ τ hστ y)) ∧
      (∀ W : TimeVelocity n → ℝ,
        ParabolicProbe.IsClassicalScalarTerminalSolution Ω γ B τ F W →
          EqOn W V (ParabolicProbe.scalarPastClosedCylinder Ω γ τ)) := by
  have hΩo := isOpen_of_isAdmissibleEvolutionDomain data.domain
  obtain ⟨C, hC0, hC⟩ := F.exists_bound
  have hFN := fun N => cutoffDatum_isSmoothCompact hF N
  choose u hu hub _ using fun N => data.exists_solution τ (cutoffDatum F N) (hFN N)
  have hbd : ∀ N, ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, |u N p| ≤ C :=
    fun N => hub N C hC0 (fun q => abs_cutoffDatum_le hC hC0 N q)
  obtain ⟨V, hVlim, hVcl⟩ := exists_cutoff_limit_classical n data.dim_pos lam Lam m L_b data.lam_pos data.lam_le data.m_pos
    data.m_le Ω γ B b data.domain data.curve data.smooth_coefficient data.symmetric data.elliptic data.smooth_drift data.lipschitz data.coercive τ F C hC0 hC
    u hu hbd
  have hint : ∀ (σ : ℝ) (hστ : σ ≤ τ) (s : EvolutionState Ω γ σ),
      V ⟨σ, s.1.1, s.1.2⟩ =
        ∫ x, lowerDatum F x ∂(μ (evolutionQueryOfState Ω γ σ τ hστ s)) := fun σ hστ s =>
    terminalMeasure_integral_lowerDatum_limit data F C hC0 hC hF u hu
      σ hστ s _ (hVlim _ (mk_mem_evolutionPastClosedCylinder hστ s))
  have hshift : ∀ (σ : ℝ) (hστ : σ ≤ τ) (s : EvolutionState Ω γ σ) (h : PDE.Vec n),
      V ⟨σ, s.1.1, s.1.2 + h⟩ = V ⟨σ, s.1.1, s.1.2⟩ := by
    intro σ hστ s h
    have e1 := hint σ hστ (evolutionStateShift Ω γ σ h s)
    have e2 := hint σ hστ s
    rw [← terminalMeasure_shift data hBz σ τ hστ h s,
      integral_map (measurable_ambientShift h).aemeasurable
        (lowerDatum F).measurable.aestronglyMeasurable] at e1
    exact e1.trans e2.symm
  have hzind : ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, V p = V ⟨p.time, p.position, 0⟩ := by
    intro p hp
    by_cases hy : p.position ∈ movingDomain Ω γ p.time
    · have := hshift p.time hp.1 ⟨(p.position, 0), ⟨hy, mem_univ _⟩⟩ p.velocity
      simpa using this
    · have hf : p.position ∈ frontier (movingDomain Ω γ p.time) := by
        rw [(isOpen_movingDomain hΩo p.time).frontier_eq]
        exact ⟨hp.2, hy⟩
      rw [hVcl.2.2.2.2.2 p ⟨hp.1, hf⟩, hVcl.2.2.2.2.2 ⟨p.time, p.position, 0⟩ ⟨hp.1, hf⟩]
  refine ⟨fun q => V ⟨q.1, q.2, 0⟩, hVcl.toScalar hzind, ?_, ?_⟩
  · intro σ hστ y
    have e := hint σ hστ (positionStateZero Ω γ σ y)
    have hrhs : ∫ y', F y'.1 ∂(parabolicMarginalKernel K
        (measurableSet_of_isAdmissibleEvolutionDomain data.domain) σ τ hστ y) =
        ∫ x, lowerDatum F x ∂(μ (evolutionQueryOfState Ω γ σ τ hστ
          (positionStateZero Ω γ σ y))) := by
      rw [parabolicMarginalKernel_apply, MovingFiberKernel.fiberFirstMarginal,
        ProbabilityTheory.Kernel.map_apply _ (MovingFiberKernel.measurable_firstPosition Ω γ τ),
        integral_map (MovingFiberKernel.measurable_firstPosition Ω γ τ).aemeasurable
          (f := fun y' : EvolutionPosition Ω γ τ => (F : PDE.Vec n → ℝ) y'.1)
          (F.measurable.comp measurable_subtype_coe).aestronglyMeasurable, ← hK,
        ← MovingFiberKernel.map_fiberKernel_eq_master K
          (measurableSet_of_isAdmissibleEvolutionDomain data.domain) σ τ hστ (positionStateZero Ω γ σ y),
        integral_map measurable_subtype_coe.aemeasurable
          (lowerDatum F).measurable.aestronglyMeasurable]
      rfl
    rw [hrhs]
    exact e
  · intro W hW q hq
    have hEq := IsClassicalTerminalSolution.eqOn_of_lam hΩo data.curve.1 data.lam_pos data.elliptic data.lipschitz
      (hW.toKinetic (b := b) hBz) hVcl
    exact hEq (show (⟨q.1, q.2, 0⟩ : KineticPoint n) ∈ evolutionPastClosedCylinder Ω γ τ from hq)

end EvolutionData

end HypoellipticAleksandrov.KineticAleksandrov
