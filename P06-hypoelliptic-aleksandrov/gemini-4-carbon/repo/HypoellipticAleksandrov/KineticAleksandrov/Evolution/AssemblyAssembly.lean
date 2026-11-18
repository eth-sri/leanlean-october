module

public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Topology.Algebra.Support
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.FixedFiberMeasure
import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalIntegralOperator
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.MarginalCutoffLimit
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonEvolution
import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.MarginalCutoffLimitClassical
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Realization
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalPointValueLinear
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CompositionTraceRepresentation
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.EvolutionConclusion

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
section
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set MeasureTheory
open scoped ENNReal ProbabilityTheory


variable {n : ℕ}

/-- Shift the transported coordinate of a kinetic point by `h`. -/
def kineticVelocityShift (h : PDE.Vec n) (p : KineticPoint n) : KineticPoint n :=
  ⟨p.time, p.position, p.velocity + h⟩


/-- The shift of the transported coordinate of an ambient state is Borel. -/
theorem measurable_ambientShift (h : PDE.Vec n) :
    Measurable (evolutionAmbientStateShift h) :=
  measurable_fst.prodMk (measurable_snd.add_const h)


/-- The terminal datum `F ∘ (z ↦ z + h)`. -/
def terminalDatumShift (h : PDE.Vec n) (F : BoundedBorel (EvolutionAmbientState n)) :
    BoundedBorel (EvolutionAmbientState n) :=
  F.pullback (evolutionAmbientStateShift h) (measurable_ambientShift h)

@[simp] theorem terminalDatumShift_apply (h : PDE.Vec n)
    (F : BoundedBorel (EvolutionAmbientState n)) (x : EvolutionAmbientState n) :
    terminalDatumShift h F x = F (evolutionAmbientStateShift h x) :=
  rfl

/-- The transported-coordinate shift preserves smooth compactly supported terminal data. -/
theorem IsSmoothCompactTerminalDatum.shift {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n} {τ : ℝ}
    {F : BoundedBorel (EvolutionAmbientState n)} (h : PDE.Vec n)
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
    IsSmoothCompactTerminalDatum Ω γ τ (terminalDatumShift h F)  := by
  let ambientShiftHomeomorph :=
    (Homeomorph.refl (PDE.Vec n)).prodCongr (Homeomorph.addRight h)
  refine ⟨?_, ?_, ?_⟩
  · exact hF.1.comp (contDiff_fst.prodMk (contDiff_snd.add contDiff_const))
  · exact hF.2.1.comp_homeomorph (ambientShiftHomeomorph)
  · intro x hx
    have hx' : ambientShiftHomeomorph x ∈ tsupport (F : EvolutionAmbientState n → ℝ) := by
      have := tsupport_comp_eq_preimage (F : EvolutionAmbientState n → ℝ)
        (ambientShiftHomeomorph)
      rw [← mem_preimage, ← this]
      exact hx
    exact ⟨(hF.2.2 hx').1, mem_univ _⟩


/-- A shifted classical terminal solution is a classical terminal solution for the shifted datum,
provided the coefficient does not depend on the transported coordinate. -/
theorem IsClassicalTerminalSolution.velocityShift {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n} {τ : ℝ}
    {F : BoundedBorel (EvolutionAmbientState n)} {u : KineticPoint n → ℝ}
    (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec n), B σ y z = B σ y z') (h : PDE.Vec n)
    (hu : IsClassicalTerminalSolution Ω γ B b τ F u) :
    IsClassicalTerminalSolution Ω γ B b τ (terminalDatumShift h F)
      (fun p => u (kineticVelocityShift h p))   := by
  have transportedForwardOperator_comp_velocityShift (h : PDE.Vec n) (u : KineticPoint n → ℝ) (p : KineticPoint n) :
      transportedForwardOperator B b (fun q => u (kineticVelocityShift h q)) p =
      transportedForwardOperator B b u (kineticVelocityShift h p) := by
    rw [transportedForwardOperator_apply, transportedForwardOperator_apply]
    have e1 : kineticTimeDerivative (fun q => u (kineticVelocityShift h q)) p =
        kineticTimeDerivative u (kineticVelocityShift h p) := rfl
    have e2 : diffusedHessian (fun q => u (kineticVelocityShift h q)) p =
        diffusedHessian u (kineticVelocityShift h p) := rfl
    have e3 : kineticVelocityGradient (fun q => u (kineticVelocityShift h q)) p =
        kineticVelocityGradient u (kineticVelocityShift h p) := by
      funext i
      simp only [kineticVelocityGradient, PDE.classicalGradient_apply]
      have := fderiv_comp_add_right (𝕜 := ℝ) (f := fun v : PDE.Vec n => u ⟨p.time, p.position, v⟩)
        (x := p.velocity) h
      exact congrArg (fun L => L (PDE.basisVec i)) this
    have e4 : fullKineticCoefficientAt B p = fullKineticCoefficientAt B (kineticVelocityShift h p) :=
      hBz _ _ _ _
    rw [e1, e2, e3, e4]
    rfl
  have continuous_kineticVelocityShift : Continuous (kineticVelocityShift h) :=
    KineticPoint.continuous_mk continuous_time continuous_position
        (continuous_velocity.add continuous_const)
  obtain ⟨⟨C, hC0, hC⟩, hc, hs, hop, ht, hl⟩ := hu
  refine ⟨⟨C, hC0, fun p hp => hC (kineticVelocityShift h p) hp⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact hc.comp (continuous_kineticVelocityShift).continuousOn (fun p hp => hp)
  · have hf : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun q : ℝ × (PDE.Vec n × PDE.Vec n) => (q.1, (q.2.1, q.2.2 + h)))
        (evolutionPastInteriorRaw Ω γ τ) :=
      (contDiff_fst.prodMk
        (contDiff_snd.fst.prodMk (contDiff_snd.snd.add contDiff_const))).contDiffOn
    exact ContDiffOn.comp
      (g := fun q : ℝ × (PDE.Vec n × PDE.Vec n) => u ⟨q.1, q.2.1, q.2.2⟩) hs hf (fun q hq => hq)
  · intro p hp
    rw [transportedForwardOperator_comp_velocityShift]
    exact hop (kineticVelocityShift h p) hp
  · intro p hp
    exact ht (kineticVelocityShift h p) hp
  · intro p hp
    exact hl (kineticVelocityShift h p) hp



section Outside

variable {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n} {τ : ℝ}

/-- The transported-coordinate shift of a fiber state is Borel. -/
theorem measurable_evolutionStateShift' (σ : ℝ) (h : PDE.Vec n) :
    Measurable (evolutionStateShift Ω γ σ h) :=
  ((measurable_ambientShift h).comp measurable_subtype_coe).subtype_mk

/-- The preimage of the terminal fiber under the ambient shift is the terminal fiber. -/
theorem preimage_ambientShift_evolutionStateSet (h : PDE.Vec n) :
    evolutionAmbientStateShift h ⁻¹' evolutionStateSet Ω γ τ = evolutionStateSet Ω γ τ := by
  ext x
  simp [evolutionStateSet, evolutionAmbientStateShift]

/-- Pulling back along the fiber inclusion intertwines the ambient and the fiber shift. -/
theorem comap_map_ambientShift (hU : MeasurableSet (evolutionStateSet Ω γ τ))
    (h : PDE.Vec n) (ν : Measure (EvolutionAmbientState n)) :
    Measure.comap ((↑) : EvolutionState Ω γ τ → EvolutionAmbientState n)
        (ν.map (evolutionAmbientStateShift h)) =
      (Measure.comap ((↑) : EvolutionState Ω γ τ → EvolutionAmbientState n) ν).map
        (evolutionStateShift Ω γ τ h) := by
  have he := MeasurableEmbedding.subtype_coe hU
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply (measurable_evolutionStateShift' τ h) hA, he.comap_apply, he.comap_apply,
    Measure.map_apply (measurable_ambientShift h) (he.measurableSet_image.2 hA)]
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, hax⟩
    have hxU : x ∈ evolutionStateSet Ω γ τ := by
      have : evolutionAmbientStateShift h x ∈ evolutionStateSet Ω γ τ := hax ▸ a.2
      rwa [← mem_preimage, preimage_ambientShift_evolutionStateSet] at this
    refine ⟨⟨x, hxU⟩, ?_, rfl⟩
    show evolutionStateShift Ω γ τ h ⟨x, hxU⟩ ∈ A
    have : evolutionStateShift Ω γ τ h ⟨x, hxU⟩ = a := Subtype.ext hax.symm
    rwa [this]
  · rintro ⟨a, ha, rfl⟩
    exact ⟨evolutionStateShift Ω γ τ h a, ha, rfl⟩

end Outside

section EvolutionData

variable (n : ℕ) (hn : 1 ≤ n) (lam Lam m L_b : ℝ)
variable (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
variable (hm : 0 < m) (hmLb : m ≤ L_b)
variable (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
variable (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
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
local notation "μ" => terminalMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
local notation "κ" => terminalFiberKernel n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

/-- The terminal point value is invariant under shifting the transported coordinate of both the
source and the datum. -/
theorem terminalValue_shift
    (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec n), B σ y z = B σ y z')
    (σ τ : ℝ) (hστ : σ ≤ τ) (h : PDE.Vec n) (p : EvolutionState Ω γ σ)
    (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
    S σ τ hστ p (terminalDatumShift h F) (hF.shift h) =
      S σ τ hστ (evolutionStateShift Ω γ σ h p) F hF := by
  obtain ⟨u, hu, hu'⟩ := terminalValue_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ
    (evolutionStateShift Ω γ σ h p) F hF
  rw [terminalValue_eq_of_solution n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p _
    (hF.shift h) _ (hu.velocityShift hBz h), ← hu']
  rfl

/-- The ambient push-forward of the terminal measure along the shift of the transported coordinate
is the terminal measure of the shifted source. -/
theorem terminalMeasure_shift
    (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec n), B σ y z = B σ y z')
    (σ τ : ℝ) (hστ : σ ≤ τ) (h : PDE.Vec n) (p : EvolutionState Ω γ σ) :
    (μ (evolutionQueryOfState Ω γ σ τ hστ p)).map (evolutionAmbientStateShift h) =
      μ (evolutionQueryOfState Ω γ σ τ hστ (evolutionStateShift Ω γ σ h p)) := by
  have hspec := terminalMeasure_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
    (evolutionQueryOfState Ω γ σ τ hστ p)
  have hsh := measurable_ambientShift (n := n) h
  have hU := measurableSet_evolutionStateSet_of_isOpen (γ := γ) (τ := τ)
    (isOpen_of_isAdmissibleEvolutionDomain hΩ)
  refine terminalMeasure_eq_of_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
    (evolutionQueryOfState Ω γ σ τ hστ (evolutionStateShift Ω γ σ h p)) _ ?_ ?_ ?_
  · rw [Measure.map_apply hsh MeasurableSet.univ, preimage_univ]
    exact hspec.1
  · show ((μ (evolutionQueryOfState Ω γ σ τ hστ p)).map (evolutionAmbientStateShift h)).restrict
        (evolutionStateSet Ω γ τ) = _
    rw [Measure.restrict_map hsh hU, preimage_ambientShift_evolutionStateSet]
    exact congrArg (fun ν => ν.map (evolutionAmbientStateShift h)) hspec.2.1
  · intro F hF
    rw [integral_map hsh.aemeasurable F.measurable.aestronglyMeasurable]
    exact (hspec.2.2 (terminalDatumShift h F) (hF.shift h)).trans
      (terminalValue_shift n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
        hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx hBz
        σ τ hστ h p F hF)

/-- Translation covariance at the level of the fixed-time fiber kernel `κ`: the pushforward of `κ σ
τ p` under the transported-coordinate shift is `κ σ τ` of the shifted source. -/
theorem terminalFiberKernel_translation
    (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec n), B σ y z = B σ y z')
    (σ τ : ℝ) (hστ : σ ≤ τ) (h : PDE.Vec n) (p : EvolutionState Ω γ σ) :
    Measure.map (evolutionStateShift Ω γ τ h) (κ σ τ hστ p) =
      κ σ τ hστ (evolutionStateShift Ω γ σ h p) := by
  have hU := measurableSet_evolutionStateSet_of_isOpen (γ := γ) (τ := τ)
    (isOpen_of_isAdmissibleEvolutionDomain hΩ)
  rw [terminalFiberKernel_apply, terminalFiberKernel_apply,
    ← terminalMeasure_shift n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx hBz σ τ hστ h p,
    comap_map_ambientShift hU]

/-- Translation covariance for every moving fiber kernel `K` whose master measures are the
terminal measures `μ q`; the master kernel `K₀` is such a kernel by definition. -/
theorem terminalKernel_translation_of_master_eq
    (K : MovingFiberKernel Ω γ) (hK : ∀ q, K.master q = μ q)
    (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec n), B σ y z = B σ y z')
    (σ τ : ℝ) (hστ : σ ≤ τ) (h : PDE.Vec n) (p : EvolutionState Ω γ σ) :
    Measure.map (evolutionStateShift Ω γ τ h)
      (K.fiberKernel (measurableSet_of_isAdmissibleEvolutionDomain hΩ) σ τ hστ p) =
    K.fiberKernel (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
      σ τ hστ (evolutionStateShift Ω γ σ h p) := by
  rw [MovingFiberKernel.fiberKernel_apply, MovingFiberKernel.fiberKernel_apply, hK, hK]
  exact terminalFiberKernel_translation n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx hBz σ τ hστ h p

end EvolutionData

end
section
section

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set
open scoped ENNReal ProbabilityTheory

section Outside

variable {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
  (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)

/-- The scalar marginal kernel has mass at most one. -/
theorem parabolicMarginalKernel_univ_le_one (σ τ : ℝ) (hστ : σ ≤ τ)
    (y : EvolutionPosition Ω γ σ) : parabolicMarginalKernel K hΩ σ τ hστ y univ ≤ 1 := by
  rw [parabolicMarginalKernel_apply, MovingFiberKernel.fiberFirstMarginal,
    ProbabilityTheory.Kernel.map_apply _ (MovingFiberKernel.measurable_firstPosition Ω γ τ),
    Measure.map_apply (MovingFiberKernel.measurable_firstPosition Ω γ τ) MeasurableSet.univ,
    preimage_univ]
  exact K.fiberKernel_mass_le_one hΩ σ τ hστ _

/-- The scalar marginal kernel is a finite kernel. -/
theorem isFiniteKernel_parabolicMarginalKernel (σ τ : ℝ) (hστ : σ ≤ τ) :
    ProbabilityTheory.IsFiniteKernel (parabolicMarginalKernel K hΩ σ τ hστ) :=
  ⟨⟨1, ENNReal.one_lt_top, fun y => parabolicMarginalKernel_univ_le_one K hΩ σ τ hστ y⟩⟩

/-- The integral of a bounded Borel function against the scalar marginal kernel, as a bounded
Borel function of the source position. -/
def marginalIntegralDatum (σ τ : ℝ) (hστ : σ ≤ τ) (f : BoundedBorel (EvolutionPosition Ω γ τ)) :
    BoundedBorel (EvolutionPosition Ω γ σ) :=
  haveI := isFiniteKernel_parabolicMarginalKernel K hΩ σ τ hστ
  ⟨fun y => ∫ y', f y' ∂(parabolicMarginalKernel K hΩ σ τ hστ y),
    (MeasureTheory.StronglyMeasurable.integral_kernel f.measurable.stronglyMeasurable :
      StronglyMeasurable fun y => ∫ y', f y' ∂(parabolicMarginalKernel K hΩ σ τ hστ y)).measurable,
    by
      obtain ⟨C, hC0, hC⟩ := f.exists_bound
      exact ⟨C, hC0, fun y => abs_integral_boundedBorel_le f _
        (parabolicMarginalKernel_univ_le_one K hΩ σ τ hστ y) hC0 hC⟩⟩

/-- Evaluation of `marginalIntegralDatum`. -/
theorem marginalIntegralDatum_apply (σ τ : ℝ) (hστ : σ ≤ τ)
    (f : BoundedBorel (EvolutionPosition Ω γ τ)) (y : EvolutionPosition Ω γ σ) :
    marginalIntegralDatum K hΩ σ τ hστ f y =
      ∫ y', f y' ∂(parabolicMarginalKernel K hΩ σ τ hστ y) :=
  rfl

/-- The integral operator against the scalar marginal kernel is the unique real-linear
map of bounded Borel functions with the integral formula. -/
theorem exists_unique_marginalIntegralOperator (σ τ : ℝ) (hστ : σ ≤ τ) :
    ∃! T : BoundedBorel (EvolutionPosition Ω γ τ) →ₗ[ℝ] BoundedBorel (EvolutionPosition Ω γ σ),
      ∀ (f : BoundedBorel (EvolutionPosition Ω γ τ)) (y : EvolutionPosition Ω γ σ),
        T f y = ∫ y', f y' ∂(parabolicMarginalKernel K hΩ σ τ hστ y) := by
  let T : BoundedBorel (EvolutionPosition Ω γ τ) →ₗ[ℝ] BoundedBorel (EvolutionPosition Ω γ σ) :=
    { toFun := marginalIntegralDatum K hΩ σ τ hστ
      map_add' := fun f g => BoundedBorel.ext fun y => by
        simp
        have := isFiniteKernel_parabolicMarginalKernel K hΩ σ τ hστ
        exact integral_add (integrable_boundedBorel f _) (integrable_boundedBorel g _)
      map_smul' := fun c f => BoundedBorel.ext fun y => by
        simp [marginalIntegralDatum_apply, BoundedBorel.smul_apply, RingHom.id_apply]
        exact integral_const_mul c _ }
  refine ⟨T, fun f y => rfl, fun T' hT' => ?_⟩
  exact LinearMap.ext fun f => BoundedBorel.ext fun y => by
    rw [hT' f y]; rfl

/-- The family `Q₀` of scalar marginal integral operators, chosen from the `∃!`
statements `exists_unique_marginalIntegralOperator`. -/
def marginalOperators : ParabolicOperatorFamily Ω γ :=
  fun σ τ hστ => (exists_unique_marginalIntegralOperator K hΩ σ τ hστ).choose

/-- The integral formula for the marginal operators. -/
theorem marginalOperators_apply (σ τ : ℝ) (hστ : σ ≤ τ)
    (f : BoundedBorel (EvolutionPosition Ω γ τ)) (y : EvolutionPosition Ω γ σ) :
    marginalOperators K hΩ σ τ hστ f y =
      ∫ y', f y' ∂(parabolicMarginalKernel K hΩ σ τ hστ y) :=
  (exists_unique_marginalIntegralOperator K hΩ σ τ hστ).choose_spec.1 f y

/-- The marginal operators are positive. -/
theorem marginalOperators_nonneg (σ τ : ℝ) (hστ : σ ≤ τ)
    (f : BoundedBorel (EvolutionPosition Ω γ τ)) (hf : 0 ≤ f) :
    0 ≤ marginalOperators K hΩ σ τ hστ f := fun y => by
  rw [BoundedBorel.zero_apply, marginalOperators_apply]
  exact integral_nonneg fun x => hf x

/-- The marginal operators are contractions on the constant one. -/
theorem marginalOperators_one_le (σ τ : ℝ) (hστ : σ ≤ τ) :
    marginalOperators K hΩ σ τ hστ (1 : BoundedBorel (EvolutionPosition Ω γ τ)) ≤
      (1 : BoundedBorel (EvolutionPosition Ω γ σ)) := fun y => by
  rw [marginalOperators_apply]
  simp [BoundedBorel.one_apply, integral_const]
  have hmass := parabolicMarginalKernel_univ_le_one K hΩ σ τ hστ y
  rw [Measure.real]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hmass)

/-- The lift of a parabolic query to the kinetic query with transported source `0`. -/
def parabolicQueryLift (q : ParabolicEvolutionQuery Ω γ) : EvolutionQuery Ω γ :=
  evolutionQueryOfState Ω γ q.1.1 q.1.2.1 q.property.1
    (positionStateZero Ω γ q.1.1 (parabolicQuerySource q))

/-- The parabolic query lift is measurable. -/
theorem measurable_parabolicQueryLift : Measurable (parabolicQueryLift (Ω := Ω) (γ := γ)) := by
  apply Measurable.subtype_mk
  show Measurable fun q : ParabolicEvolutionQuery Ω γ =>
    ((q.1.1, (q.1.2.1, (q.1.2.2, 0))) : RawEvolutionQuery n)
  fun_prop

/-- The ambient marginal measure is the first marginal of the master measure at the lifted query. -/
theorem parabolicMarginalAmbientMeasure_eq (q : ParabolicEvolutionQuery Ω γ) :
    parabolicMarginalAmbientMeasure K hΩ q = K.firstMarginal (parabolicQueryLift q) := by
  rw [parabolicMarginalAmbientMeasure, parabolicMarginalKernel_apply,
    MovingFiberKernel.map_fiberFirstMarginal_eq_firstMarginal]
  rfl

/-- Constrained joint measurability of the ambient marginal measure: the evaluation on
a Borel set is measurable in the parabolic query (no hypothesis on `B`). -/
theorem measurable_parabolicMarginalAmbientMeasure (E : Set (PDE.Vec n)) (hE : MeasurableSet E) :
    Measurable (fun q : ParabolicEvolutionQuery Ω γ =>
      parabolicMarginalAmbientMeasure K hΩ q E) := by
  have h : (fun q : ParabolicEvolutionQuery Ω γ => parabolicMarginalAmbientMeasure K hΩ q E) =
      fun q => K.master (parabolicQueryLift q) {p | p.1 ∈ E} := by
    funext q
    rw [parabolicMarginalAmbientMeasure_eq, MovingFiberKernel.firstMarginal_apply _ _ _ hE]
  rw [h]
  exact (K.master.measurable_coe (measurable_fst hE)).comp measurable_parabolicQueryLift

end Outside

section EvolutionData

variable (n : ℕ) (hn : 1 ≤ n) (lam Lam m L_b : ℝ)
variable (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
variable (hm : 0 < m) (hmLb : m ≤ L_b)
variable (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
variable (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
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

local notation "μ" => terminalMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

/-- **Marginal independence** (Proposition 2.1, first clause), for every moving fiber kernel `K`
whose master measures are the terminal measures `μ q`.  If `B` does not depend on the transported
coordinate, the zero-`z` pullback of the first marginal equals the first marginal at every
transported coordinate `z` of the source. -/
theorem parabolicMarginalKernel_eq_fiberFirstMarginal_of_master_eq
    (K : MovingFiberKernel Ω γ) (hK : ∀ q, K.master q = μ q)
    (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec n), B σ y z = B σ y z')
    (σ τ : ℝ) (hστ : σ ≤ τ) (y : EvolutionPosition Ω γ σ) (z : PDE.Vec n) :
    parabolicMarginalKernel K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) σ τ hστ y =
      K.fiberFirstMarginal (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
        σ τ hστ (evolutionStateOfPosition Ω γ σ y z) := by
  have hs : evolutionStateOfPosition Ω γ σ y z =
      evolutionStateShift Ω γ σ z (positionStateZero Ω γ σ y) :=
    Subtype.ext (Prod.ext rfl (zero_add z).symm)
  have hfs : ∀ (p : EvolutionState Ω γ τ) (h : PDE.Vec n),
      MovingFiberKernel.firstPosition Ω γ τ (evolutionStateShift Ω γ τ h p) =
        MovingFiberKernel.firstPosition Ω γ τ p := fun p h => rfl
  rw [parabolicMarginalKernel_apply, hs, MovingFiberKernel.fiberFirstMarginal,
    ProbabilityTheory.Kernel.map_apply _ (MovingFiberKernel.measurable_firstPosition Ω γ τ),
    ProbabilityTheory.Kernel.map_apply _ (MovingFiberKernel.measurable_firstPosition Ω γ τ),
    ← terminalKernel_translation_of_master_eq n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx K hK hBz σ τ hστ z,
    Measure.map_map (MovingFiberKernel.measurable_firstPosition Ω γ τ)
      (measurable_evolutionStateShift' τ z)]
  congr 1

end EvolutionData

end
section

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set MeasureTheory

section Scalar

variable {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n} {B : FullKineticCoefficient n}
  {b : PDE.Vec n → PDE.Vec n} {τ : ℝ} {F : BoundedBorel (PDE.Vec n)}

theorem classicalGradient_const_eq_zero (c : ℝ) (x : PDE.Vec n) :
    PDE.classicalGradient (fun _ : PDE.Vec n => c) x = 0 := by
  ext i
  simp [PDE.classicalGradient]

/-- A classical scalar terminal solution, lifted along `(σ, y, z) ↦ (σ, y)`, is a classical
kinetic terminal solution for the `z`-independent datum, when `B` does not depend on `z`. -/
theorem ParabolicProbe.IsClassicalScalarTerminalSolution.toKinetic
    {W : TimeVelocity n → ℝ}
    (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec n), B σ y z = B σ y z')
    (hW : ParabolicProbe.IsClassicalScalarTerminalSolution Ω γ B τ F W) :
    IsClassicalTerminalSolution Ω γ B b τ (lowerDatum F)
      (fun p => W (p.time, p.position)) := by
  obtain ⟨⟨C, hC0, hC⟩, hcont, hsmooth, hop, hterm, hlat⟩ := hW
  have hpr : Continuous (fun p : KineticPoint n => (p.time, p.position)) :=
    continuous_time.prodMk continuous_position
  refine ⟨⟨C, hC0, fun p hp => hC _ hp⟩, hcont.comp hpr.continuousOn (fun p hp => hp), ?_, ?_,
    ?_, ?_⟩
  · have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × (PDE.Vec n × PDE.Vec n) => (q.1, q.2.1)) :=
      contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
    exact hsmooth.comp h2.contDiffOn (fun q hq => hq)
  · intro p hp
    have h0 := hop (p.time, p.position) hp
    have hz : kineticVelocityGradient (fun p : KineticPoint n => W (p.time, p.position)) p = 0 :=
      classicalGradient_const_eq_zero (n := n) (W (p.time, p.position)) p.velocity
    have hv1 : PDE.vecDot (b p.position) 0 = 0 := by simp [PDE.vecDot]
    have hv2 : ∀ g : PDE.Vec n,
        PDE.vecDot ((0 : ℝ → PDE.Vec n → PDE.Vec n) p.time p.position) g = 0 := by
      intro g
      simp [PDE.vecDot]
    rw [transportedForwardOperator_apply, hz, hv1, fullKineticCoefficientAt_apply,
      hBz p.time p.position p.velocity 0, add_zero]
    rwa [scalarParabolicOperator_apply, hv2, add_zero] at h0
  · intro p hp
    exact hterm (p.time, p.position) hp
  · intro p hp
    exact hlat (p.time, p.position) hp


end Scalar

end
section

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set MeasureTheory
open scoped Topology ENNReal ProbabilityTheory

section EvolutionData

variable (n : ℕ) (hn : 1 ≤ n) (lam Lam m L_b : ℝ)
variable (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
variable (hm : 0 < m) (hmLb : m ≤ L_b)
variable (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
variable (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
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
local notation "μ" => terminalMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

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
  have hspec := terminalMeasure_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
    (evolutionQueryOfState Ω γ σ τ hστ s)
  have : IsFiniteMeasure (μ (evolutionQueryOfState Ω γ σ τ hστ s)) :=
    ⟨lt_of_le_of_lt hspec.1 ENNReal.one_lt_top⟩
  have heq : ∀ N, u N ⟨σ, s.1.1, s.1.2⟩ =
      ∫ x, cutoffDatum F N x ∂(μ (evolutionQueryOfState Ω γ σ τ hστ s)) := by
    intro N
    rw [hspec.2.2 (cutoffDatum F N) (cutoffDatum_isSmoothCompact hF N)]
    exact (terminalValue_eq_of_solution n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ s _
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
    (hH : HormanderHypoellipticityStatement)
    (K : MovingFiberKernel Ω γ) (hK : ∀ q, K.master q = μ q)
    (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec n), B σ y z = B σ y z')
    (τ : ℝ) (F : BoundedBorel (PDE.Vec n))
    (hF : ParabolicProbe.IsSmoothCompactScalarTerminalDatum Ω γ τ F) :
    ∃ V : TimeVelocity n → ℝ,
      ParabolicProbe.IsClassicalScalarTerminalSolution Ω γ B τ F V ∧
      (∀ (σ : ℝ) (hστ : σ ≤ τ) (y : EvolutionPosition Ω γ σ),
        V (σ, y.1) = ∫ y', F y'.1 ∂(parabolicMarginalKernel K
          (measurableSet_of_isAdmissibleEvolutionDomain hΩ) σ τ hστ y)) ∧
      (∀ W : TimeVelocity n → ℝ,
        ParabolicProbe.IsClassicalScalarTerminalSolution Ω γ B τ F W →
          EqOn W V (ParabolicProbe.scalarPastClosedCylinder Ω γ τ))  := by
  have toScalar {V : KineticPoint n → ℝ} (hV : IsClassicalTerminalSolution Ω γ B b τ (lowerDatum F) V) (hz : ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, V p = V ⟨p.time, p.position, 0⟩) :
      ParabolicProbe.IsClassicalScalarTerminalSolution Ω γ B τ F
      (fun q => V ⟨q.1, q.2, 0⟩) := by
    obtain ⟨⟨C, hC0, hC⟩, hcont, hsmooth, hop, hterm, hlat⟩ := hV
    have hin : ∀ q : TimeVelocity n,
        q ∈ ParabolicProbe.scalarPastClosedCylinder Ω γ τ →
          (⟨q.1, q.2, 0⟩ : KineticPoint n) ∈ evolutionPastClosedCylinder Ω γ τ :=
      fun q hq => hq
    have hemb : Continuous (fun q : TimeVelocity n => (⟨q.1, q.2, 0⟩ : KineticPoint n)) :=
      (KineticPoint.homeomorphProd n).symm.continuous.comp
        (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))
    refine ⟨⟨C, hC0, fun q hq => hC _ (hin q hq)⟩, hcont.comp hemb.continuousOn hin, ?_, ?_, ?_, ?_⟩
    · have h2 : ContDiff ℝ (⊤ : ℕ∞)
          (fun q : TimeVelocity n => ((q.1, (q.2, (0 : PDE.Vec n))) :
            ℝ × (PDE.Vec n × PDE.Vec n))) :=
        contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)
      exact hsmooth.comp h2.contDiffOn (fun q hq => hq)
    · intro q hq
      have h0 := hop ⟨q.1, q.2, 0⟩ hq
      have hconst : (fun v : PDE.Vec n => V ⟨q.1, q.2, v⟩) = fun _ => V ⟨q.1, q.2, 0⟩ := by
        funext v
        exact hz ⟨q.1, q.2, v⟩ ⟨hq.1.le, subset_closure hq.2⟩
      have hg : kineticVelocityGradient V ⟨q.1, q.2, 0⟩ = 0 := by
        show PDE.classicalGradient (fun v : PDE.Vec n => V ⟨q.1, q.2, v⟩) 0 = 0
        rw [hconst]
        exact classicalGradient_const_eq_zero _ _
      have hv1 : PDE.vecDot (b q.2) (0 : PDE.Vec n) = 0 := by simp [PDE.vecDot]
      have hv2 : ∀ g : PDE.Vec n,
          PDE.vecDot ((0 : ℝ → PDE.Vec n → PDE.Vec n) q.1 q.2) g = 0 := by
        intro g
        simp [PDE.vecDot]
      rw [transportedForwardOperator_apply, hg] at h0
      rw [hv1, add_zero] at h0
      rw [scalarParabolicOperator_apply, hv2, add_zero]
      exact h0
    · intro q hq
      have := hterm ⟨q.1, q.2, 0⟩ hq
      simpa using this
    · intro q hq
      exact hlat ⟨q.1, q.2, 0⟩ hq
  have hΩo := isOpen_of_isAdmissibleEvolutionDomain hΩ
  obtain ⟨C, hC0, hC⟩ := F.exists_bound
  have hFN := fun N => cutoffDatum_isSmoothCompact hF N
  choose u hu hub _ using fun N => hEx τ (cutoffDatum F N) (hFN N)
  have hbd : ∀ N, ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, |u N p| ≤ C :=
    fun N => hub N C hC0 (fun q => abs_cutoffDatum_le hC hC0 N q)
  obtain ⟨V, hVlim, hVcl⟩ := exists_cutoff_limit_classical hH n hn lam Lam m L_b hlam hlamLam hm
    hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive τ F C hC0 hC
    u hu hbd
  have hint : ∀ (σ : ℝ) (hστ : σ ≤ τ) (s : EvolutionState Ω γ σ),
      V ⟨σ, s.1.1, s.1.2⟩ =
        ∫ x, lowerDatum F x ∂(μ (evolutionQueryOfState Ω γ σ τ hστ s)) := fun σ hστ s =>
    terminalMeasure_integral_lowerDatum_limit n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx F C hC0 hC hF u hu
      σ hστ s _ (hVlim _ (mk_mem_evolutionPastClosedCylinder hστ s))
  have hshift : ∀ (σ : ℝ) (hστ : σ ≤ τ) (s : EvolutionState Ω γ σ) (h : PDE.Vec n),
      V ⟨σ, s.1.1, s.1.2 + h⟩ = V ⟨σ, s.1.1, s.1.2⟩ := by
    intro σ hστ s h
    have e1 := hint σ hστ (evolutionStateShift Ω γ σ h s)
    rw [← terminalMeasure_shift n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx hBz σ τ hστ h s,
      integral_map (measurable_ambientShift h).aemeasurable
        (lowerDatum F).measurable.aestronglyMeasurable] at e1
    exact e1.trans (hint σ hστ s).symm
  have hzind : ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, V p = V ⟨p.time, p.position, 0⟩ := by
    intro p hp
    by_cases hy : p.position ∈ movingDomain Ω γ p.time
    · have := hshift p.time hp.1 ⟨(p.position, 0), ⟨hy, mem_univ _⟩⟩ p.velocity
      simpa using this
    · have hf : p.position ∈ frontier (movingDomain Ω γ p.time) := by
        rw [(isOpen_movingDomain hΩo p.time).frontier_eq]
        exact ⟨hp.2, hy⟩
      rw [hVcl.2.2.2.2.2 p ⟨hp.1, hf⟩, hVcl.2.2.2.2.2 ⟨p.time, p.position, 0⟩ ⟨hp.1, hf⟩]
  refine ⟨fun q => V ⟨q.1, q.2, 0⟩, toScalar hVcl hzind, ?_, ?_⟩
  · intro σ hστ y
    have hrhs : ∫ y', F y'.1 ∂(parabolicMarginalKernel K
        (measurableSet_of_isAdmissibleEvolutionDomain hΩ) σ τ hστ y) =
        ∫ x, lowerDatum F x ∂(μ (evolutionQueryOfState Ω γ σ τ hστ
          (positionStateZero Ω γ σ y))) := by
      rw [parabolicMarginalKernel_apply, MovingFiberKernel.fiberFirstMarginal,
        ProbabilityTheory.Kernel.map_apply _ (MovingFiberKernel.measurable_firstPosition Ω γ τ),
        integral_map (MovingFiberKernel.measurable_firstPosition Ω γ τ).aemeasurable
          (f := fun y' : EvolutionPosition Ω γ τ => (F : PDE.Vec n → ℝ) y'.1)
          (F.measurable.comp measurable_subtype_coe).aestronglyMeasurable, ← hK,
        ← MovingFiberKernel.map_fiberKernel_eq_master K
          (measurableSet_of_isAdmissibleEvolutionDomain hΩ) σ τ hστ (positionStateZero Ω γ σ y),
        integral_map measurable_subtype_coe.aemeasurable
          (lowerDatum F).measurable.aestronglyMeasurable]
      rfl
    rw [hrhs]
    exact hint σ hστ (positionStateZero Ω γ σ y)
  · intro W hW q hq
    exact (IsClassicalTerminalSolution.eqOn_of_lam hΩo hγ.1 hlam hB_ell hb_lipschitz (hW.toKinetic (b := b) hBz) hVcl) (show (⟨q.1, q.2, 0⟩ : KineticPoint n) ∈ evolutionPastClosedCylinder Ω γ τ from hq)

end EvolutionData

end

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set
open scoped ENNReal ProbabilityTheory

section EvolutionData

variable (n : ℕ) (hn : 1 ≤ n) (lam Lam m L_b : ℝ)
variable (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
variable (hm : 0 < m) (hmLb : m ≤ L_b)
variable (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
variable (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
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

local notation "μ" => terminalMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
local notation "κ" => terminalFiberKernel n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

/-- The fiber kernel of a moving fiber kernel with master measures `μ q` is `κ`. -/
theorem fiberKernel_eq_terminalFiberKernel_of_master_eq
    (K : MovingFiberKernel Ω γ) (hK : ∀ q, K.master q = μ q) (σ τ : ℝ) (hστ : σ ≤ τ) :
    K.fiberKernel (measurableSet_of_isAdmissibleEvolutionDomain hΩ) σ τ hστ = κ σ τ hστ := by
  refine ProbabilityTheory.Kernel.ext fun p => ?_
  rw [MovingFiberKernel.fiberKernel_apply, hK]
  rfl

/-- Endpoint identity of the fiber kernel for a kernel with master measures `μ q`. -/
theorem hasEndpoint_of_master_eq (K : MovingFiberKernel Ω γ) (hK : ∀ q, K.master q = μ q) :
    K.HasEndpoint (measurableSet_of_isAdmissibleEvolutionDomain hΩ) := fun σ => by
  rw [fiberKernel_eq_terminalFiberKernel_of_master_eq n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ
    B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx K hK]
  exact terminalFiberKernel_self n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ

/-- Endpoint identity of the scalar marginal kernel (clause 8). -/
theorem parabolicMarginalKernel_self_of_master_eq
    (K : MovingFiberKernel Ω γ) (hK : ∀ q, K.master q = μ q) (σ : ℝ) :
    parabolicMarginalKernel K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) σ σ le_rfl =
      (ProbabilityTheory.Kernel.id :
        ProbabilityTheory.Kernel (EvolutionPosition Ω γ σ) (EvolutionPosition Ω γ σ)) := by
  refine ProbabilityTheory.Kernel.ext fun y => ?_
  rw [parabolicMarginalKernel_apply, MovingFiberKernel.fiberFirstMarginal,
    ProbabilityTheory.Kernel.map_apply _ (MovingFiberKernel.measurable_firstPosition Ω γ σ), (hasEndpoint_of_master_eq n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx K hK σ),
    ProbabilityTheory.Kernel.id_apply, ProbabilityTheory.Kernel.id_apply]
  exact Measure.map_dirac' (MovingFiberKernel.measurable_firstPosition Ω γ σ)
    (positionStateZero Ω γ σ y)

/-- Chapman-Kolmogorov for the scalar marginal kernels (clause 9), from the Chapman-Kolmogorov
identity `hComp` of the fiber kernel and the marginal independence. -/
theorem parabolicMarginalKernel_comp_of_master_eq
    (K : MovingFiberKernel Ω γ) (hK : ∀ q, K.master q = μ q)
    (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec n), B σ y z = B σ y z')
    (hComp : K.HasComposition (measurableSet_of_isAdmissibleEvolutionDomain hΩ))
    (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ) :
    parabolicMarginalKernel K (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
        σ τ (hσr.trans hrτ) =
      parabolicMarginalKernel K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) r τ hrτ ∘ₖ
        parabolicMarginalKernel K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) σ r hσr := by
  refine ProbabilityTheory.Kernel.ext fun y => Measure.ext fun s hs => ?_
  have hfirst :=
    MovingFiberKernel.measurable_firstPosition Ω γ
  have hind : ∀ x : EvolutionState Ω γ r,
      parabolicMarginalKernel K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) r τ hrτ
          (MovingFiberKernel.firstPosition Ω γ r x) =
        K.fiberFirstMarginal (measurableSet_of_isAdmissibleEvolutionDomain hΩ) r τ hrτ x := by
    intro x
    have := parabolicMarginalKernel_eq_fiberFirstMarginal_of_master_eq n hn lam Lam m L_b hlam
      hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive
      hEx K hK hBz r τ hrτ (MovingFiberKernel.firstPosition Ω γ r x) x.1.2
    exact this
  rw [ProbabilityTheory.Kernel.comp_apply' _ _ _ hs]
  rw [parabolicMarginalKernel_apply, MovingFiberKernel.fiberFirstMarginal,
    ProbabilityTheory.Kernel.map_apply _ (hfirst τ), Measure.map_apply (hfirst τ) hs,
    hComp σ r τ hσr hrτ, ProbabilityTheory.Kernel.comp_apply' _ _ _ (hfirst τ hs)]
  have hmarg : parabolicMarginalKernel K (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
      σ r hσr y =
      Measure.map (MovingFiberKernel.firstPosition Ω γ r)
        (K.fiberKernel (measurableSet_of_isAdmissibleEvolutionDomain hΩ) σ r hσr
          (positionStateZero Ω γ σ y)) := by
    rw [parabolicMarginalKernel_apply, MovingFiberKernel.fiberFirstMarginal,
      ProbabilityTheory.Kernel.map_apply _ (hfirst r)]
  rw [hmarg, lintegral_map ((parabolicMarginalKernel K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) r τ hrτ).measurable_coe hs) (hfirst r)]
  refine lintegral_congr fun x => ?_
  rw [hind x, MovingFiberKernel.fiberFirstMarginal,
    ProbabilityTheory.Kernel.map_apply _ (hfirst τ), Measure.map_apply (hfirst τ) hs]

/-- The full parabolic marginal package of the terminal evolution (companion paper,
Proposition 2.1), for every moving fiber kernel `K` whose master measures are the terminal
measures `μ q`, with ONE shared operator family `Q₀ = marginalOperators K`.  The
Chapman-Kolmogorov identity `hComp` of the fiber kernel (Proposition 2.1, composition) is
used for the two Chapman-Kolmogorov clauses; Hörmander enters only through `hH`. -/
theorem terminalMarginal_properties_of_master_eq
    (hH : HormanderHypoellipticityStatement)
    (K : MovingFiberKernel Ω γ) (hK : ∀ q, K.master q = μ q)
    (hComp : K.HasComposition (measurableSet_of_isAdmissibleEvolutionDomain hΩ)) :
    SectionTwo.HasParabolicMarginalBundle Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ) B K := by
  unfold SectionTwo.HasParabolicMarginalBundle
  intro hBz
  have hCK := parabolicMarginalKernel_comp_of_master_eq n hn lam Lam m L_b hlam hlamLam hm hmLb
    Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx K hK hBz hComp
  have hQ := marginalOperators_apply K (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
  refine ⟨marginalOperators K (measurableSet_of_isAdmissibleEvolutionDomain hΩ), ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun σ τ hστ y z =>
      parabolicMarginalKernel_eq_fiberFirstMarginal_of_master_eq n hn lam Lam m L_b hlam hlamLam
        hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx K
        hK hBz σ τ hστ y z
  · intro σ
    refine LinearMap.ext fun f => BoundedBorel.ext fun y => ?_
    rw [hQ, parabolicMarginalKernel_self_of_master_eq n hn lam Lam m L_b hlam hlamLam hm hmLb
      Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx K hK,
      ProbabilityTheory.Kernel.id_apply, integral_dirac' _ _ f.measurable.stronglyMeasurable]
    rfl
  · exact fun σ τ hστ f hf =>
      marginalOperators_nonneg K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) σ τ hστ f hf
  · exact fun σ τ hστ =>
      marginalOperators_one_le K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) σ τ hστ
  · intro σ r τ hσr hrτ
    refine LinearMap.ext fun f => BoundedBorel.ext fun y => ?_
    have h1 := isFiniteKernel_parabolicMarginalKernel K
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ) σ r hσr
    have h2 := isFiniteKernel_parabolicMarginalKernel K
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ) r τ hrτ
    rw [LinearMap.comp_apply, hQ, hQ, hCK σ r τ hσr hrτ,
      ProbabilityTheory.Kernel.integral_comp (integrable_boundedBorel f _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y' => ?_)
    exact (hQ r τ hrτ f y').symm
  · exact fun σ τ hστ y f => hQ σ τ hστ f y
  · exact fun E hE => measurable_parabolicMarginalAmbientMeasure K
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ) E hE
  · exact fun σ => parabolicMarginalKernel_self_of_master_eq n hn lam Lam m L_b hlam hlamLam hm
      hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx K hK σ
  · exact hCK
  · intro τ F hF
    obtain ⟨V, hV1, hV2, hV3⟩ := exists_classical_terminalMarginal_of_master_eq n hn lam Lam m L_b
      hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz
      hb_coercive hEx hH K hK hBz τ F hF
    exact ⟨V, hV1, fun σ hστ y =>
      (hV2 σ hστ y).trans (hQ σ τ hστ (terminalPositionDatum F) y).symm, hV3⟩

end EvolutionData

end
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set MeasureTheory SectionTwo
open scoped ProbabilityTheory
section
open HypoellipticAleksandrov Set MeasureTheory
open scoped ProbabilityTheory

section EvolutionData

variable (n : ℕ) (hn : 1 ≤ n) (lam Lam m L_b : ℝ)
variable (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hm : 0 < m) (hmLb : m ≤ L_b)
variable (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
variable (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
variable (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ)
variable (hB_smooth : IsSmoothFullKineticCoefficient B)
variable (hB_symm : IsSymmetricFullKineticCoefficient B)
variable (hB_ell : HasEverywhereLoewnerBounds lam Lam B) (hb_smooth : IsSmoothDrift b)
variable (hb_lipschitz : HasEuclideanLipschitzDrift L_b b)
variable (hb_coercive : HasUnitDirectionDriftCoercivity m b)
variable (hEx : ClassicalTerminalExistence Ω γ B b)
include hn hlam hlamLam hm hmLb hΩ hγ hB_smooth hB_symm hB_ell
include hb_smooth hb_lipschitz hb_coercive hEx

local notation "μ" => terminalMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
local notation "κ" => terminalFiberKernel n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

/-- The ambient master is literally the family of terminal measures, with joint measurability
supplied explicitly. -/
def constructionTerminalKernel (hJoint : Measurable (fun q : EvolutionQuery Ω γ => μ q)) :
    MovingFiberKernel Ω γ where
  master := ⟨μ, hJoint⟩
  terminal_support q := (terminalMeasure_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx q).2.1
  mass_le_one q := (terminalMeasure_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx q).1

/-- The fiber identification follows from the identical map/comap constructions. -/
theorem constructionTerminalKernel_fiber_eq
    (hJoint : Measurable (fun q : EvolutionQuery Ω γ => μ q))
    (σ τ : ℝ) (hστ : σ ≤ τ) :
    (constructionTerminalKernel n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx hJoint).fiberKernel
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ) σ τ hστ = κ σ τ hστ := by
  apply ProbabilityTheory.Kernel.ext
  intro p
  rw [MovingFiberKernel.fiberKernel_apply, terminalFiberKernel_apply]
  rfl

end EvolutionData
end


variable {n : ℕ}

/-- A classical terminal solution with nonnegative datum is nonnegative on the past closed
cylinder. -/
theorem IsClassicalTerminalSolution.nonneg_of_nonneg {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    (hΩ : IsOpen Ω) (hγ : Continuous γ) {lam Lam : ℝ} (hlam : 0 < lam)
    {B : FullKineticCoefficient n} (hB : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ}
    {b : PDE.Vec n → PDE.Vec n} (hb : HasEuclideanLipschitzDrift Lb b) {τ : ℝ}
    {F : BoundedBorel (EvolutionAmbientState n)} {u : KineticPoint n → ℝ}
    (hu : IsClassicalTerminalSolution Ω γ B b τ F u) (hF : ∀ q, 0 ≤ F q) :
    ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, 0 ≤ u p := by
  intro p hp
  have hle := IsClassicalTerminalSolution.le_of_le hΩ hγ hlam hB hb (IsClassicalTerminalSolution.smul hΩ hγ 0 hu) hu
    (fun y z _ => by simpa using hF (y, z)) p hp
  simpa using hle

/-- A solution on a moving subdomain is dominated by the solution on the large domain with the
same nonnegative datum. -/
theorem classical_le_of_subdomain {Ω Ω' : Set (PDE.Vec n)} {γ γ' : ℝ → PDE.Vec n}
    (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') (hγ : Continuous γ) (hγ' : Continuous γ')
    (hsub : ∀ σ, movingDomain Ω' γ' σ ⊆ movingDomain Ω γ σ) {lam Lam : ℝ} (hlam : 0 < lam)
    {B : FullKineticCoefficient n} (hB : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ}
    {b : PDE.Vec n → PDE.Vec n} (hb : HasEuclideanLipschitzDrift Lb b) {τ : ℝ}
    {F : BoundedBorel (EvolutionAmbientState n)} {u u' : KineticPoint n → ℝ}
    (hu : IsClassicalTerminalSolution Ω γ B b τ F u)
    (hu' : IsClassicalTerminalSolution Ω' γ' B b τ F u') (hF : ∀ q, 0 ≤ F q) :
    ∀ p ∈ evolutionPastClosedCylinder Ω' γ' τ, u' p ≤ u p := by
  have hcl : ∀ t, closure (movingDomain Ω' γ' t) ⊆ closure (movingDomain Ω γ t) :=
    fun t => closure_mono (hsub t)
  have hu0 := (isClassicalViscousTerminalSolution_zero_iff Ω γ B b τ F u).2 hu
  have hu0' := (isClassicalViscousTerminalSolution_zero_iff Ω' γ' B b τ F u').2 hu'
  have hslab' : ∀ a, movingClosedSlab Ω' γ' a τ ⊆ evolutionPastClosedCylinder Ω' γ' τ :=
    fun a p hp => ⟨hp.2.1, hp.2.2⟩
  have hslab : ∀ a, movingClosedSlab Ω' γ' a τ ⊆ evolutionPastClosedCylinder Ω γ τ :=
    fun a p hp => ⟨hp.2.1, hcl _ hp.2.2⟩
  have hact' : ∀ a, movingActiveSlab Ω' γ' a τ ⊆ evolutionPastOpenCylinder Ω' γ' τ :=
    fun a p hp => ⟨hp.2.1, hp.2.2⟩
  have hact : ∀ a, movingActiveSlab Ω' γ' a τ ⊆ evolutionPastOpenCylinder Ω γ τ :=
    fun a p hp => ⟨hp.2.1, hsub _ hp.2.2⟩
  obtain ⟨C', -, hC'⟩ := hu'.1
  obtain ⟨C, -, hC⟩ := hu.1
  intro p₀ hp₀
  have hp₀slab : p₀ ∈ movingClosedSlab Ω' γ' p₀.time τ := ⟨le_rfl, hp₀.1, hp₀.2⟩
  have hres := growth_comparison (a := p₀.time) (T := τ) (u := fun q => u' q - u q) hΩ' hγ'
    hlam hB hb le_rfl zero_le_one ?_ ?_ ?_ ?_ ?_ ?_ p₀ hp₀slab
  · linarith
  · refine ⟨C' + C, fun p hp => ?_⟩
    have h1 := hC' p (hslab' _ hp)
    have h2 := hC p (hslab _ hp)
    have := le_abs_self (u' p)
    have := neg_abs_le (u p)
    linarith
  · exact (hu0'.2.1.mono (hslab' _)).sub (hu0.2.1.mono (hslab _))
  · intro p hp
    exact (hu0'.isSliceRegularAt hΩ' hγ' (hact' _ hp)).sub
      (hu0.isSliceRegularAt hΩ hγ (hact _ hp))
  · intro p hp
    have hr' := hu0'.isSliceRegularAt hΩ' hγ' (hact' _ hp)
    have hr := hu0.isSliceRegularAt hΩ hγ (hact _ hp)
    rw [viscousTransportedOperator_sub hr' hr, hu0'.2.2.2.1 p (hact' _ hp),
      hu0.2.2.2.1 p (hact _ hp)]
    simp
  · intro p hp hpT
    have hterm' : p ∈ evolutionTerminalClosure Ω' γ' τ := ⟨hpT, hpT ▸ hp.2.2⟩
    have hterm : p ∈ evolutionTerminalClosure Ω γ τ := ⟨hpT, hcl _ (hpT ▸ hp.2.2)⟩
    show u' p - u p ≤ 0
    rw [hu0'.2.2.2.2.1 p hterm', hu0.2.2.2.2.1 p hterm]
    simp
  · intro p hp hfr
    have hlat' : p ∈ evolutionLateralFrontier Ω' γ' τ := ⟨hp.2.1, hfr⟩
    show u' p - u p ≤ 0
    rw [hu0'.2.2.2.2.2 p hlat']
    have := (hu.nonneg_of_nonneg hΩ hγ hlam hB hb hF) p (hslab _ hp)
    linarith

section

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set
open scoped ENNReal ProbabilityTheory


section EvolutionData

variable (n : ℕ) (hn : 1 ≤ n) (lam Lam m L_b : ℝ)
variable (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
variable (hm : 0 < m) (hmLb : m ≤ L_b)
variable (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
variable (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
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
local notation "μ" => terminalMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

/-- Domain domination at the level of master measures, from clauses 1 and 6 of the antecedent only:
the master measure of ANY small kernel `K'` with the clause-1 solution representation and the
clause-6 operator integral is dominated by the terminal measure of the corresponding large query. -/
theorem terminalMeasure_domination
    (Ω' : Set (PDE.Vec n)) (γ' : ℝ → PDE.Vec n)
    (hΩ' : IsAdmissibleEvolutionDomain Ω') (hγ' : IsContinuousPiecewiseC1 γ')
    (hsub : ∀ σ, movingDomain Ω' γ' σ ⊆ movingDomain Ω γ σ)
    (P' : TerminalOperatorFamily Ω' γ') (K' : MovingFiberKernel Ω' γ')
    (h1 : ∀ (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n)),
      IsSmoothCompactTerminalDatum Ω' γ' τ F →
        ∃ u : KineticPoint n → ℝ,
          IsClassicalTerminalSolution Ω' γ' B b τ F u ∧
          (∀ (σ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω' γ' σ),
            u ⟨σ, p.1.1, p.1.2⟩ = P' σ τ hστ (terminalStateDatum F) p) ∧
          (∀ v : KineticPoint n → ℝ,
            IsClassicalTerminalSolution Ω' γ' B b τ F v →
              EqOn v u (evolutionPastClosedCylinder Ω' γ' τ)))
    (h6 : ∀ (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω' γ' σ)
      (f : BoundedBorel (EvolutionState Ω' γ' τ)),
        P' σ τ hστ f p = ∫ q, f q ∂(K'.fiberKernel
          (measurableSet_of_isAdmissibleEvolutionDomain hΩ') σ τ hστ p))
    (q' : EvolutionQuery Ω' γ') :
    K'.master q' ≤ μ (largeQueryOfSmall hsub q')  := by
  have integral_master_eq_operator {Ω' : Set (PDE.Vec n)} {γ' : ℝ → PDE.Vec n} (hΩ' : IsAdmissibleEvolutionDomain Ω') (K' : MovingFiberKernel Ω' γ') (P' : TerminalOperatorFamily Ω' γ') {τ : ℝ} (h6 : ∀ (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω' γ' σ)
      (f : BoundedBorel (EvolutionState Ω' γ' τ)),
        P' σ τ hστ f p = ∫ q, f q ∂(K'.fiberKernel
          (measurableSet_of_isAdmissibleEvolutionDomain hΩ') σ τ hστ p)) (σ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω' γ' σ) (F : BoundedBorel (EvolutionAmbientState n)) :
      P' σ τ hστ (terminalStateDatum F) p =
      ∫ x, F x ∂(K'.master (evolutionQueryOfState Ω' γ' σ τ hστ p)) := by
    rw [h6 σ τ hστ p (terminalStateDatum F),
      ← MovingFiberKernel.map_fiberKernel_eq_master K'
        (measurableSet_of_isAdmissibleEvolutionDomain hΩ') σ τ hστ p,
      integral_map measurable_subtype_coe.aemeasurable F.measurable.aestronglyMeasurable]
    rfl
  obtain ⟨⟨σ, τ, w⟩, hστ, hw⟩ := q'
  have hΩo := isOpen_of_isAdmissibleEvolutionDomain hΩ
  have hΩo' := isOpen_of_isAdmissibleEvolutionDomain hΩ'
  have hU : IsOpen (evolutionStateSet Ω' γ' τ) := (isOpen_movingDomain hΩo' τ).prod isOpen_univ
  have hspec := terminalMeasure_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
    (largeQueryOfSmall hsub ⟨(σ, τ, w), hστ, hw⟩)
  have hfinν : IsFiniteMeasure (K'.master ⟨(σ, τ, w), hστ, hw⟩) :=
    ⟨(K'.mass_le_one ⟨(σ, τ, w), hστ, hw⟩).trans_lt ENNReal.one_lt_top⟩
  have hfinμ : IsFiniteMeasure (μ (largeQueryOfSmall hsub ⟨(σ, τ, w), hστ, hw⟩)) :=
    ⟨hspec.1.trans_lt ENNReal.one_lt_top⟩
  refine measure_le_of_smooth_integral_le hU (K'.terminal_support ⟨(σ, τ, w), hστ, hw⟩) ?_
  intro f hfs hfc hfU hfnn
  obtain ⟨C, hC⟩ := hfc.exists_bound_of_continuous hfs.continuous
  let F : BoundedBorel (EvolutionAmbientState n) :=
    ⟨f, hfs.continuous.measurable, ⟨max C 0, le_max_right _ _,
      fun x => (hC x).trans (le_max_left _ _)⟩⟩
  have hF' : IsSmoothCompactTerminalDatum Ω' γ' τ F := ⟨hfs, hfc, hfU⟩
  have hF : IsSmoothCompactTerminalDatum Ω γ τ F :=
    ⟨hfs, hfc, hfU.trans fun x hx => ⟨hsub τ hx.1, mem_univ _⟩⟩
  obtain ⟨u', hu', hrep, -⟩ := h1 τ F hF'
  obtain ⟨u, hu, -, -⟩ := hEx τ F hF
  have hcmp := classical_le_of_subdomain hΩo hΩo' hγ.1 hγ'.1 hsub hlam hB_ell hb_lipschitz
    hu hu' hfnn ⟨σ, w.1, w.2⟩ ⟨hστ, subset_closure hw.1⟩
  have hA := integral_master_eq_operator hΩ' K' P' h6 σ hστ ⟨w, hw⟩ F
  have hlhs : ∫ x, f x ∂(K'.master ⟨(σ, τ, w), hστ, hw⟩) = u' ⟨σ, w.1, w.2⟩ :=
    ((hrep σ hστ ⟨w, hw⟩).trans hA).symm
  have hS := terminalValue_eq_of_solution n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ
    ⟨w, ⟨hsub σ hw.1, hw.2⟩⟩ F hF u hu
  have hrhs := (hspec.2.2 F hF).trans hS
  rw [hlhs, hrhs]
  exact hcmp

/-- Domain domination for every moving fiber kernel `K` whose master measures are the
terminal measures `μ q` (the master kernel `K₀` is such a kernel by definition): ANY
smaller admissible problem `(Ω', γ', P', K')` satisfying the complete eight-clause antecedent of
the fourteenth conjunct is zero-extension dominated by `K`. -/
theorem terminalKernel_domain_domination_of_master_eq
    (K : MovingFiberKernel Ω γ) (hK : ∀ q, K.master q = μ q) :
    ∀ (Ω' : Set (PDE.Vec n)) (γ' : ℝ → PDE.Vec n)
            (hΩ' : IsAdmissibleEvolutionDomain Ω')
            (hγ' : IsContinuousPiecewiseC1 γ')
            (hsub : ∀ σ, movingDomain Ω' γ' σ ⊆
              movingDomain Ω γ σ)
            (P' : TerminalOperatorFamily Ω' γ')
            (K' : MovingFiberKernel Ω' γ'),
          ((∀ (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n)),
              IsSmoothCompactTerminalDatum Ω' γ' τ F →
                ∃ u : KineticPoint n → ℝ,
                  IsClassicalTerminalSolution Ω' γ' B b τ F u ∧
                  (∀ (σ : ℝ) (hστ : σ ≤ τ)
                      (p : EvolutionState Ω' γ' σ),
                    u ⟨σ, p.1.1, p.1.2⟩ =
                      P' σ τ hστ (terminalStateDatum F) p) ∧
                  (∀ v : KineticPoint n → ℝ,
                    IsClassicalTerminalSolution Ω' γ' B b τ F v →
                      EqOn v u (evolutionPastClosedCylinder Ω' γ' τ)))) ∧
           (∀ (σ : ℝ),
             P' σ σ le_rfl =
               (LinearMap.id :
                 BoundedBorel (EvolutionState Ω' γ' σ) →ₗ[ℝ]
                   BoundedBorel (EvolutionState Ω' γ' σ))) ∧
           (∀ (σ τ : ℝ) (hστ : σ ≤ τ)
               (f : BoundedBorel (EvolutionState Ω' γ' τ)),
             0 ≤ f → 0 ≤ P' σ τ hστ f) ∧
           (∀ (σ τ : ℝ) (hστ : σ ≤ τ),
             P' σ τ hστ (1 : BoundedBorel (EvolutionState Ω' γ' τ)) ≤
               (1 : BoundedBorel (EvolutionState Ω' γ' σ))) ∧
           (∀ (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ),
             P' σ τ (hσr.trans hrτ) =
               (P' σ r hσr).comp (P' r τ hrτ)) ∧
           (∀ (σ τ : ℝ) (hστ : σ ≤ τ)
               (p : EvolutionState Ω' γ' σ)
               (f : BoundedBorel (EvolutionState Ω' γ' τ)),
             P' σ τ hστ f p =
               ∫ q, f q ∂(K'.fiberKernel
                 (measurableSet_of_isAdmissibleEvolutionDomain hΩ')
                 σ τ hστ p)) ∧
           MovingFiberKernel.HasEndpoint K'
             (measurableSet_of_isAdmissibleEvolutionDomain hΩ') ∧
           MovingFiberKernel.HasComposition K'
             (measurableSet_of_isAdmissibleEvolutionDomain hΩ') →
          MovingFiberKernel.IsZeroExtensionDominatedBy K' K hsub := by
  rintro Ω' γ' hΩ' hγ' hsub P' K' ⟨h1, -, -, -, -, h6, -, -⟩ q'
  rw [hK]
  exact terminalMeasure_domination n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
    Ω' γ' hΩ' hγ' hsub P' K' h1 h6 q'

end EvolutionData

end

section EvolutionData
variable (n : ℕ) (hn : 1 ≤ n) (lam Lam m L_b : ℝ)
variable (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hm : 0 < m) (hmLb : m ≤ L_b)
variable (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
variable (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
variable (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ)
variable (hB_smooth : IsSmoothFullKineticCoefficient B)
variable (hB_symm : IsSymmetricFullKineticCoefficient B)
variable (hB_ell : HasEverywhereLoewnerBounds lam Lam B) (hb_smooth : IsSmoothDrift b)
variable (hb_lipschitz : HasEuclideanLipschitzDrift L_b b)
variable (hb_coercive : HasUnitDirectionDriftCoercivity m b)
variable (hEx : ClassicalTerminalExistence Ω γ B b)
include hn hlam hlamLam hm hmLb hΩ hγ hB_smooth hB_symm hB_ell
include hb_smooth hb_lipschitz hb_coercive hEx

local notation "μ" => terminalMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
local notation "κ" => terminalFiberKernel n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
local notation "P₀" => terminalOperators n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

/-- Assemble every conjunct using one operator and one master-kernel witness.
The premises are the composition identity and the joint measurability of the master kernel;
the marginal package is consumed directly. -/
theorem construction_terminalEvolution_assembly
    (hH : HormanderHypoellipticityStatement)
    (hComp : ∀ σ r τ hσr hrτ,
      P₀ σ τ (hσr.trans hrτ) = (P₀ σ r hσr).comp (P₀ r τ hrτ))
    (hKComp : ∀ σ r τ hσr hrτ,
      κ σ τ (hσr.trans hrτ) = κ r τ hrτ ∘ₖ κ σ r hσr)
    (hJoint : Measurable (fun q : EvolutionQuery Ω γ => μ q)) :
    ∃ P : TerminalOperatorFamily Ω γ,
      ∃ K : MovingFiberKernel Ω γ,
        (∀ (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n)),
          IsSmoothCompactTerminalDatum Ω γ τ F →
            ∃ u : KineticPoint n → ℝ,
              IsClassicalTerminalSolution Ω γ B b τ F u ∧
              (∀ (σ : ℝ) (hστ : σ ≤ τ)
                  (p : EvolutionState Ω γ σ),
                u ⟨σ, p.1.1, p.1.2⟩ =
                  P σ τ hστ (terminalStateDatum F) p) ∧
              (∀ v : KineticPoint n → ℝ,
                IsClassicalTerminalSolution Ω γ B b τ F v →
                  EqOn v u (evolutionPastClosedCylinder Ω γ τ))) ∧
        (∀ (σ : ℝ),
          P σ σ le_rfl =
            (LinearMap.id :
              BoundedBorel (EvolutionState Ω γ σ) →ₗ[ℝ]
                BoundedBorel (EvolutionState Ω γ σ))) ∧
        (∀ (σ τ : ℝ) (hστ : σ ≤ τ)
            (f : BoundedBorel (EvolutionState Ω γ τ)),
          0 ≤ f → 0 ≤ P σ τ hστ f) ∧
        (∀ (σ τ : ℝ) (hστ : σ ≤ τ),
          P σ τ hστ (1 : BoundedBorel (EvolutionState Ω γ τ)) ≤
            (1 : BoundedBorel (EvolutionState Ω γ σ))) ∧
        (∀ (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ),
          P σ τ (hσr.trans hrτ) =
            (P σ r hσr).comp (P r τ hrτ)) ∧
        (∀ (σ τ : ℝ) (hστ : σ ≤ τ)
            (p : EvolutionState Ω γ σ)
            (f : BoundedBorel (EvolutionState Ω γ τ)),
          P σ τ hστ f p =
            ∫ q, f q ∂(K.fiberKernel
              (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
              σ τ hστ p)) ∧
        (∀ q : EvolutionQuery Ω γ,
          (K.master q).restrict (evolutionStateSet Ω γ q.1.2.1) =
            K.master q) ∧
        (∀ q : EvolutionQuery Ω γ, K.master q Set.univ ≤ 1) ∧
        (∀ (E : Set (EvolutionAmbientState n))
            (hE : MeasurableSet E),
          let _ := hE
          Measurable (fun q : EvolutionQuery Ω γ => K.master q E)) ∧
        (∀ (σ τ : ℝ) (hστ : σ ≤ τ)
            (p : EvolutionState Ω γ σ),
          K.fiberKernel
            (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
            σ τ hστ p Set.univ ≤ 1) ∧
        MovingFiberKernel.HasEndpoint K
          (measurableSet_of_isAdmissibleEvolutionDomain hΩ) ∧
        MovingFiberKernel.HasComposition K
          (measurableSet_of_isAdmissibleEvolutionDomain hΩ) ∧
        (∀ (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec n), B σ y z = B σ y z'),
          let _ := hBz
          IsTranslationCovariantEvolution Ω γ
            (measurableSet_of_isAdmissibleEvolutionDomain hΩ) K) ∧
        IsDomainMonotoneEvolution Ω γ B b K ∧
        HasParabolicMarginalBundle Ω γ
          (measurableSet_of_isAdmissibleEvolutionDomain hΩ) B K
 := by
  let K := constructionTerminalKernel n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx hJoint
  have hK (q : EvolutionQuery Ω γ) : K.master q = μ q := rfl
  have hFiber (σ τ : ℝ) (hστ : σ ≤ τ) :
      K.fiberKernel (measurableSet_of_isAdmissibleEvolutionDomain hΩ) σ τ hστ =
        κ σ τ hστ :=
    constructionTerminalKernel_fiber_eq n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx hJoint σ τ hστ
  have hComposition : K.HasComposition
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ) := by
    intro σ r τ hσr hrτ
    rw [hFiber, hFiber, hFiber]
    exact hKComp σ r τ hσr hrτ
  have hBasic := terminalOperators_basic n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
  refine ⟨P₀, K, ?_, hBasic.1, hBasic.2.1, hBasic.2.2.1, ?_, ?_,
    K.terminal_support, K.mass_le_one, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact terminalOperators_classical n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
  · exact hComp
  · intro σ τ hστ p f
    rw [hFiber]
    exact terminalOperators_apply n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ f p
  · exact K.jointlyMeasurable_apply
  · exact K.fiberKernel_mass_le_one (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
  · intro σ
    rw [hFiber]
    exact hBasic.2.2.2 σ
  · exact hComposition
  · exact terminalKernel_translation_of_master_eq n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx K hK
  · exact terminalKernel_domain_domination_of_master_eq n hn lam Lam m L_b hlam hlamLam hm hmLb
      Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx K hK
  · exact terminalMarginal_properties_of_master_eq n hn lam Lam m L_b
      hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth
      hb_lipschitz hb_coercive hEx hH K hK hComposition

end EvolutionData
end HypoellipticAleksandrov.KineticAleksandrov

