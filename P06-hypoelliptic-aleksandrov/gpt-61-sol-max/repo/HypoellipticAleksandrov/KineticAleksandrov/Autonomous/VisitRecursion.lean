module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Setting
public import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Tactic

/-! # Literal alternating entrance and exit recursion

Index zero represents the source's first entrance measure. The measure sum includes
this initial visit once. The kernels are the Borel exit families consumed from AU-06;
this module makes no assertion that a finite-union exit family has been constructed.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory
open scoped Classical

variable (s T : ℝ) (I J : Interval)

/-- Internal velocity boundary in the literal open physical time slab. -/
def visitBoundary  : Set Point :=
  {p | s < p.time ∧ p.time < T ∧ p.velocity 0 ∈ frontier I.carrier ∩ J.carrier}

/-- The internal boundary is measurable in physical coordinates. -/
theorem measurableSet_visitBoundary  :
    MeasurableSet (visitBoundary s T I J) := by
  have ht : MeasurableSet {p : Point | p.time ∈ Ioo s T} :=
    isOpen_Ioo.measurableSet.preimage continuous_time.measurable
  have hv : MeasurableSet {p : Point | p.velocity 0 ∈ frontier I.carrier ∩ J.carrier} :=
    (isClosed_frontier.measurableSet.inter isOpen_Ioo.measurableSet).preimage
      ((continuous_apply 0).comp continuous_velocity).measurable
  convert ht.inter hv using 1
  ext p
  simp only [visitBoundary, mem_inter_iff, mem_ofPred_eq, mem_Ioo, and_assoc]

/-- Initial entrance, including the initial point exactly when it is already in the interval. -/
def visitInitial (P : Point) (I : Interval) (Sin : Set Point)
    (exitWaiting : Kernel Point Point) : Measure Point :=
  if P.velocity 0 ∈ closure I.carrier then Measure.dirac P
  else (exitWaiting P).restrict Sin

/-- Entrance measures, with index zero denoting the source's first visit. -/
def visitGamma (P : Point) (I : Interval) (Sin Sout : Set Point)
    (exitActive exitWaiting : Kernel Point Point) : ℕ → Measure Point
  | 0 => visitInitial P I Sin exitWaiting
  | n + 1 => (exitWaiting ∘ₘ ((exitActive ∘ₘ
      visitGamma P I Sin Sout exitActive exitWaiting n).restrict Sout)).restrict Sin

/-- Exit from the active domain onto the internal outgoing face. -/
def visitBeta (P : Point) (I : Interval) (Sin Sout : Set Point)
    (exitActive exitWaiting : Kernel Point Point) (n : ℕ) : Measure Point :=
  (exitActive ∘ₘ visitGamma P I Sin Sout exitActive exitWaiting n).restrict Sout

/-- Every entrance is finite when both consumed exit kernels are finite. -/
instance visitGamma_isFiniteMeasure (P : Point) (I : Interval) (Sin Sout : Set Point)
    (exitActive exitWaiting : Kernel Point Point)
    [IsFiniteKernel exitActive] [IsFiniteKernel exitWaiting] (n : ℕ) :
    IsFiniteMeasure (visitGamma P I Sin Sout exitActive exitWaiting n) := by
  induction n with
  | zero =>
    dsimp only [visitGamma, visitInitial]
    split <;> infer_instance
  | succ n ih =>
    dsimp only [visitGamma]
    infer_instance

/-- Every active outgoing measure is finite. -/
instance visitBeta_isFiniteMeasure (P : Point) (I : Interval) (Sin Sout : Set Point)
    (exitActive exitWaiting : Kernel Point Point)
    [IsFiniteKernel exitActive] [IsFiniteKernel exitWaiting] (n : ℕ) :
    IsFiniteMeasure (visitBeta P I Sin Sout exitActive exitWaiting n) := by
  dsimp only [visitBeta]
  infer_instance





end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
