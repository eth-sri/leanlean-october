module

public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Topology.Algebra.Support
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Translation of the transported coordinate: solutions (translation covariance ingredient)

Companion paper, Proposition 2.1 (domain covariance).  When the coefficient `B` does not depend
on the transported coordinate `z`, the slice-wise operator `∂_σ + B : D_y² + b(y) · ∇_z` commutes
with the shift `z ↦ z + h`.  Consequently the shift of a classical terminal solution is a classical
terminal solution for the shifted datum.

* `kineticVelocityShift`, `terminalDatumShift`: the shifts of points and of terminal data.
* `IsSmoothCompactTerminalDatum.shift`: shifted smooth compact data are smooth compact data.
* `transportedForwardOperator_comp_velocityShift`: the operator commutes with the shift.
* `IsClassicalTerminalSolution.velocityShift`: shifted classical solutions.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set

variable {n : ℕ}

variable (h : PDE.Vec n)

/-- Shift the transported coordinate of a kinetic point by `h`. -/
def kineticVelocityShift  (p : KineticPoint n) : KineticPoint n :=
  ⟨p.time, p.position, p.velocity + h⟩

/-- The velocity shift of kinetic points is continuous. -/
theorem continuous_kineticVelocityShift  :
    Continuous (kineticVelocityShift h) :=
  KineticPoint.continuous_mk continuous_time continuous_position
    (continuous_velocity.add continuous_const)

/-- The shift of the transported coordinate of an ambient state is Borel. -/
theorem measurable_ambientShift  :
    Measurable (evolutionAmbientStateShift h) :=
  measurable_fst.prodMk (measurable_snd.add_const h)

/-- The shift of the transported coordinate of an ambient state, as a homeomorphism. -/
def ambientShiftHomeomorph  :
    EvolutionAmbientState n ≃ₜ EvolutionAmbientState n :=
  (Homeomorph.refl (PDE.Vec n)).prodCongr (Homeomorph.addRight h)

variable (F : BoundedBorel (EvolutionAmbientState n))

/-- The terminal datum `F ∘ (z ↦ z + h)`. -/
def terminalDatumShift   :
    BoundedBorel (EvolutionAmbientState n) :=
  F.pullback _ (measurable_ambientShift h)



/-- The transported-coordinate shift preserves smooth compactly supported terminal data. -/
theorem IsSmoothCompactTerminalDatum.shift {Ω : PDE.VelocityRegion n} {γ : ℝ → PDE.Vec n} {τ : ℝ}
    {F : BoundedBorel (EvolutionAmbientState n)} (h : PDE.Vec n)
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
    IsSmoothCompactTerminalDatum Ω γ τ (terminalDatumShift h F) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hF.1.comp (contDiff_fst.prodMk (contDiff_snd.add contDiff_const))
  · exact hF.2.1.comp_homeomorph (ambientShiftHomeomorph h)
  · intro x hx
    have hx' : ambientShiftHomeomorph h x ∈ tsupport (F : EvolutionAmbientState n → ℝ) := by
      have := tsupport_comp_eq_preimage (F : EvolutionAmbientState n → ℝ)
        (ambientShiftHomeomorph h)
      rw [← mem_preimage, ← this]
      exact hx
    exact ⟨(hF.2.2 hx').1, mem_univ _⟩

/-- The transported forward operator commutes with the transported-coordinate shift when the
coefficient does not depend on that coordinate. -/
theorem transportedForwardOperator_comp_velocityShift {B : FullKineticCoefficient n}
    {b : PDE.VectorField n} (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec n), B σ y z = B σ y z')
    (h : PDE.Vec n) (u : HypoellipticAleksandrov.KineticScalarField n) (p : KineticPoint n) :
    transportedForwardOperator B b (fun q => u (kineticVelocityShift h q)) p =
      transportedForwardOperator B b u (kineticVelocityShift h p) := by
  let sharedTerm_9e010cb6dd := ((fun q => u (kineticVelocityShift h q)))
  rw [transportedForwardOperator_apply, transportedForwardOperator_apply]
  have e1 : kineticTimeDerivative sharedTerm_9e010cb6dd p =
      kineticTimeDerivative u (kineticVelocityShift h p) := rfl
  have e2 : diffusedHessian sharedTerm_9e010cb6dd p =
      diffusedHessian u (kineticVelocityShift h p) := rfl
  have e3 : kineticVelocityGradient sharedTerm_9e010cb6dd p =
      kineticVelocityGradient u (kineticVelocityShift h p) := by
    funext i
    simp only [kineticVelocityGradient, PDE.classicalGradient_apply]
    have := fderiv_comp_add_right (𝕜 := ℝ) (f := fun v  => u ⟨p.time, p.position, v⟩)
      (x := p.velocity) h
    exact congrArg (fun L => L (PDE.basisVec i)) this
  have e4 : fullKineticCoefficientAt B p = fullKineticCoefficientAt B (kineticVelocityShift h p) :=
    hBz _ _ _ _
  rw [e1, e2, e3, e4]
  rfl

/-- A shifted classical terminal solution is a classical terminal solution for the shifted datum,
provided the coefficient does not depend on the transported coordinate. -/
theorem IsClassicalTerminalSolution.velocityShift {Ω : PDE.VelocityRegion n} {γ : ℝ → PDE.Vec n}
    {B : FullKineticCoefficient n} {b : PDE.VectorField n} {τ : ℝ}
    {F : BoundedBorel (EvolutionAmbientState n)} {u : HypoellipticAleksandrov.KineticScalarField n}
    (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec n), B σ y z = B σ y z') (h : PDE.Vec n)
    (hu : IsClassicalTerminalSolution Ω γ B b τ F u) :
    IsClassicalTerminalSolution Ω γ B b τ (terminalDatumShift h F)
      (fun p => u (kineticVelocityShift h p)) := by
  obtain ⟨⟨C, hC0, hC⟩, hc, hs, hop, ht, hl⟩ := hu
  refine ⟨⟨C, hC0, fun p hp => hC _ hp⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact hc.comp (continuous_kineticVelocityShift h).continuousOn (fun p hp => hp)
  · have hf : ContDiffOn ℝ PDE.smoothOrder
        (fun q : ℝ × (PDE.Vec n × PDE.Vec n) => (q.1, (q.2.1, q.2.2 + h)))
        (evolutionPastInteriorRaw Ω γ τ) :=
      (contDiff_fst.prodMk
        (contDiff_snd.fst.prodMk (contDiff_snd.snd.add contDiff_const))).contDiffOn
    exact ContDiffOn.comp
      (g := fun q : ℝ × (PDE.Vec n × PDE.Vec n) => u ⟨q.1, q.2.1, q.2.2⟩) hs hf (fun q hq => hq)
  · intro p hp
    rw [transportedForwardOperator_comp_velocityShift hBz]
    exact hop _ hp
  · intro p hp
    exact ht _ hp
  · intro p hp
    exact hl _ hp

end HypoellipticAleksandrov.KineticAleksandrov
