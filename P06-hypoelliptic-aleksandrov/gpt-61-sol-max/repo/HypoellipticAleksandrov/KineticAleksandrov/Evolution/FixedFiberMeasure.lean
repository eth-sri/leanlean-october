module

import Mathlib.Tactic.Linarith
public import Mathlib.Probability.Kernel.Defs
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.FixedFiberMeasureGeneral
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalMeasure

/-!
# The fixed-time fiber kernel

Companion paper, Proposition 2.1.  For fixed times `σ ≤ τ` the fiber measures
`p ↦ comap (↑) (μ (σ, τ, p))` of the terminal measures depend measurably on the source
state, BEFORE any composition or joint-Borel statement.  Measurability is proved from the
integrals against smooth probes: for a probe `F` the integral is the point value
`terminalValue`, which is continuous in `p` (a single classical solution evaluates all of them);
`FixedFiberMeasureGeneral` passes from probes to all measures.

* `measurable_terminalFiberMeasure`: measurable dependence of the fiber measure.
* `terminalFiberKernel`: the kernel `κ σ τ hστ` with `κ σ τ hστ p = comap (↑) (μ q)`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov MeasureTheory Set
open scoped CompactlySupported ProbabilityTheory

section EvolutionData

variable (n : ℕ) (hn : 1 ≤ n) (lam Lam m L_b : ℝ)
variable (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
variable (hm : 0 < m) (hmLb : m ≤ L_b)
variable (Ω : PDE.VelocityRegion n) (γ : ℝ → PDE.Vec n)
variable (B : FullKineticCoefficient n) (b : PDE.VectorField n)
variable (hΩ : IsAdmissibleEvolutionDomain Ω)
variable (hγ : IsContinuousPiecewiseC1 γ)
variable (hB_smooth : IsSmoothFullKineticCoefficient B)
variable (hB_symm : IsSymmetricFullKineticCoefficient B)
variable (hB_ell : HasEverywhereLoewnerBounds lam Lam B)
variable (hb_smooth : IsSmoothDrift b)
variable (hb_lipschitz : HasEuclideanLipschitzDrift L_b b)
variable (hb_coercive : HasUnitDirectionDriftCoercivity m b)
variable (hEx : ClassicalTerminalExistence Ω γ B b)
include hn hlam hlamLam hm hmLb hΩ hγ hB_smooth hB_symm hB_ell
include hb_smooth hb_lipschitz hb_coercive hEx

local notation "S" => terminalValue n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
local notation "ℓ_" => terminalFunctional n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
local notation "ν_" => terminalFiberRieszMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
local notation "μ" => terminalMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

variable (σ τ : ℝ) (hστ : σ ≤ τ)

/-- For fixed times `σ ≤ τ` the fiber measure of the terminal measure depends
measurably on the source state. -/
theorem measurable_terminalFiberMeasure
     :
    Measurable (fun p  =>
      Measure.comap ((↑) : EvolutionState Ω γ τ → EvolutionAmbientState n)
        (μ (evolutionQueryOfState Ω γ σ τ hστ p))) := by
  have hΩo := isOpen_of_isAdmissibleEvolutionDomain hΩ
  have hfun : (fun p  =>
      Measure.comap ((↑) : EvolutionState Ω γ τ → EvolutionAmbientState n)
        (μ (evolutionQueryOfState Ω γ σ τ hστ p))) = (ν_ σ τ hστ) := by
    funext p
    exact comap_terminalMeasure_eq_rieszMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
      (evolutionQueryOfState Ω γ σ τ hστ p)
  rw [hfun]
  have := locallyCompactSpace_evolutionState (γ := γ) (τ := τ) hΩo
  have hfin  := (isFiniteMeasure_terminalFiberRieszMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
  hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ)
  have hmass  := (terminalFiberRieszMeasure_univ_le_one n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
  hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ)
  refine measurable_of_integral_measurable ((ν_ σ τ hστ)) ?_
  refine measurable_integral_of_dense (terminalProbeCcLinear (Ω := Ω) (γ := γ) (τ := τ))
    ((ν_ σ τ hστ)) hmass
    ((exists_terminalProbe_close hΩo)) (fun F => ?_)
  have hint : (fun p  => ∫ x, terminalProbeCcLinear F x ∂(ν_ σ τ hστ p)) =
      fun p => S σ τ hστ p _ (terminalProbeDatum_isSmoothCompact F) := by
    funext p
    rw [integral_terminalFiberRieszMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p]
    exact (terminalFunctional_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p).2
      _ _
      _ fun x => rfl
  rw [hint]
  exact (continuous_terminalValue_source n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ
    (terminalProbeDatum F) (terminalProbeDatum_isSmoothCompact F)).measurable

/-- The fixed-time fiber kernel `κ σ τ hστ`, defined literally as the measurable
fiber-measure function of `measurable_terminalFiberMeasure`. -/
def terminalFiberKernel  :
    ProbabilityTheory.Kernel (EvolutionState Ω γ σ) (EvolutionState Ω γ τ) :=
  ⟨fun p  =>
      Measure.comap ((↑) : EvolutionState Ω γ τ → EvolutionAmbientState n)
        (μ (evolutionQueryOfState Ω γ σ τ hστ p)),
    measurable_terminalFiberMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ⟩

local notation "κ" => terminalFiberKernel n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

variable (σ τ : ℝ) (hστ : σ ≤ τ)

variable (p : EvolutionState Ω γ σ)

/-- The value of the fiber kernel at a source state. -/
theorem terminalFiberKernel_apply   :
    κ σ τ hστ p =
      Measure.comap ((↑) : EvolutionState Ω γ τ → EvolutionAmbientState n)
        (μ (evolutionQueryOfState Ω γ σ τ hστ p)) :=
  rfl

/-- The fiber kernel has mass at most one. -/
theorem terminalFiberKernel_univ_le_one   :
    κ σ τ hστ p univ ≤ 1 := by
  have hU := measurableSet_evolutionStateSet_of_isOpen (γ := γ) (τ := τ)
    (isOpen_of_isAdmissibleEvolutionDomain hΩ)
  rw [terminalFiberKernel_apply, (MeasurableEmbedding.subtype_coe hU).comap_apply,
    image_univ, Subtype.range_coe]
  exact (measure_mono (subset_univ _)).trans
    (terminalMeasure_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
      (evolutionQueryOfState Ω γ σ τ hστ p)).1

/-- The fiber kernel is a finite kernel. -/
theorem isFiniteKernel_terminalFiberKernel  :
    ProbabilityTheory.IsFiniteKernel (κ σ τ hστ) :=
  ⟨⟨1, ENNReal.one_lt_top, (terminalFiberKernel_univ_le_one n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth
  hb_lipschitz hb_coercive hEx σ τ hστ)⟩⟩

end EvolutionData

end HypoellipticAleksandrov.KineticAleksandrov
