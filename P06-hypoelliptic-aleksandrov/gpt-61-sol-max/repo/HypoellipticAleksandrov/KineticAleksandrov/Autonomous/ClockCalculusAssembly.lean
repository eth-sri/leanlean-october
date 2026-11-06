module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockCalculusConjugacy
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.CaseW
import Aesop
public import PDEFoundation.Calculus.RegularityOrder




/-! # Source-smooth operator conjugacy in the transported carrier -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.TheoremA

variable (c : Clock)

/-- The local normalized scalar diffusion on the full coefficient carrier. -/
def Clock.normalizedCoefficient  (a : ℝ → ℝ → ℝ) (e : Point) :
    FullKineticCoefficient 1 := fun s y _ _ _ => c.diffusion a e s (y 0)

/-- The local normalized scalar transport on the drift carrier. -/
def Clock.normalizedDrift  : PDE.VectorField 1 :=
  fun y _ => c.drift (y 0)

variable (a : ℝ → ℝ → ℝ)

/-- Exact field-order identification with the Section Two operator. -/
theorem Clock.normalizedOperator_eq_transport
    (e q : Point) (h : Point → ℝ) :
    c.normalizedOperator a e h q =
      transportedForwardOperator (c.normalizedCoefficient a e) c.normalizedDrift
        (h ∘ sectionTwoPoint) (sectionTwoPoint q) := by
  simp_all [Clock.normalizedOperator, transportedForwardOperator, Clock.normalizedCoefficient, Clock.normalizedDrift, fullKineticCoefficientAt, sectionTwoPoint, matrixContraction, PDE.vecDot] <;> aesop

/-- The source conjugacy for every function smooth on the normalized open velocity strip. -/
theorem Clock.conjugacy   (e : Point) (h : Point → ℝ)
    (hh : ContDiffOn ℝ PDE.smoothOrder (h ∘ scalarPoint)
      {q : Fin 3 → ℝ | q 2 ∈ normalizedActive})
    (p : Point) (hp : p.velocity 0 ∈ c.active) :
    forwardScalarOperator a (h ∘ c.map e) p =
      |p.velocity 0| / (|c.vbar| * c.r ^ 2) *
        transportedForwardOperator (c.normalizedCoefficient a e) c.normalizedDrift
          (h ∘ sectionTwoPoint) (sectionTwoPoint (c.map e p)) := by

  have hmem  :=
    (c.mem_active_iff (p.velocity 0)).mp hp

  rw [← c.normalizedOperator_eq_transport a e (c.map e p) h]
  exact c.conjugacy_at a e p h hp (((hh _ hmem).contDiffAt ((isOpen_Ioo.preimage (continuous_apply 2)).mem_nhds hmem)).of_le (by norm_num))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
