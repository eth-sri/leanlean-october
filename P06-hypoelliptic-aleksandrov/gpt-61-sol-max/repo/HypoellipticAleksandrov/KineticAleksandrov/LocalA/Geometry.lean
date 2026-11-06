module

public import HypoellipticAleksandrov.KineticAleksandrov.Geometry
public import HypoellipticAleksandrov.KineticAleksandrov.MovingKernel
public import HypoellipticAleksandrov.Parabolic.Geometry
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
public import Mathlib.Analysis.Complex.Exponential

/-! # Local velocity-ball geometry

Points retain physical coordinate order (time, position, velocity). Evolution states
instead use (velocity, position); the conversions below expose that permutation.
All balls and increments use the Euclidean geometry of PDEFoundation.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic

variable {d : ℕ} (a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ)

/-- The open time strip with velocity constrained to a Euclidean ball. -/
def localStrip  :
    Set (KineticPoint d) :=
  {P | a < P.time ∧ P.time < T ∧ P.velocity ∈ PDE.euclideanBall v₀ R}

/-- The closed time strip with velocity constrained to the closed ball. -/
def localClosedStrip  :
    Set (KineticPoint d) :=
  {P | a ≤ P.time ∧ P.time ≤ T ∧ P.velocity ∈ closure (PDE.euclideanBall v₀ R)}

/-- Terminal and lateral velocity faces, including their common corner. -/
def localTrace  :
    Set (KineticPoint d) :=
  {P | (P.time = T ∧ P.velocity ∈ closure (PDE.euclideanBall v₀ R)) ∨
    (a ≤ P.time ∧ P.time ≤ T ∧ P.velocity ∈ frontier (PDE.euclideanBall v₀ R))}

/-- A physical starting point whose velocity is valid for the ball evolution. -/
abbrev LocalBallStart {d : ℕ} (v₀ : PDE.Vec d) (R : ℝ) :=
  {P : KineticPoint d // P.velocity ∈ PDE.euclideanBall v₀ R}

variable {d : ℕ}

/-- The physical position slice through a spacetime point. -/
def physicalPositionSlice  (u : HypoellipticAleksandrov.KineticScalarField d) (P : KineticPoint d) :
    PDE.ScalarField d := fun x => u ⟨P.time, x, P.velocity⟩

/-- The source kinetic increment based at the center velocity. -/
def kineticIncrement  (P₀ P Q : KineticPoint d) : ℝ :=
  |P.time - Q.time| ^ (1 / 2 : ℝ) + PDE.vecEuclideanNorm (P.velocity - Q.velocity) +
    PDE.vecEuclideanNorm
      (P.position - Q.position - (P.time - Q.time) • P₀.velocity) ^ (1 / 3 : ℝ)

/-- Position displacement in the centered free-transport frame, with absolute exit data. -/
def exitCoordinates  (P : KineticPoint d) (v₀ : PDE.Vec d)
    (Q : KineticPoint d) : PDE.Vec d × TimeVelocity d :=
  (Q.position - P.position - (Q.time - P.time) • v₀, (Q.time, Q.velocity))

/-- Fourier phase of the centered position coordinate, retaining exit time and velocity. -/
def exitPhase  (ξ : PDE.Vec d) (Q : PDE.Vec d × TimeVelocity d) : ℂ :=
  Complex.exp (-Complex.I * (PDE.vecDot ξ Q.1 : ℂ))

/-- Parabolic time--velocity distance, with Euclidean velocity norm. -/
def parabolicDistance  (z z' : TimeVelocity d) : ℝ :=
  |z.1 - z'.1| ^ (1 / 2 : ℝ) + PDE.vecEuclideanNorm (z.2 - z'.2)

variable {a T R : ℝ} {v₀ : PDE.Vec d} {P : KineticPoint d}

/-- Membership in the open strip unfolds without a coordinate change. -/
@[simp] theorem mem_localStrip_iff   :
    P ∈ localStrip a T v₀ R ↔
      a < P.time ∧ P.time < T ∧ P.velocity ∈ PDE.euclideanBall v₀ R := Iff.rfl

/-- Membership in the closed strip unfolds without a coordinate change. -/
@[simp] theorem mem_localClosedStrip_iff   :
    P ∈ localClosedStrip a T v₀ R ↔
      a ≤ P.time ∧ P.time ≤ T ∧ P.velocity ∈ closure (PDE.euclideanBall v₀ R) := Iff.rfl

variable (a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ)

/-- The open strip is open in the ordinary spacetime topology. -/
theorem isOpen_localStrip   :
    IsOpen (localStrip a T v₀ R) :=
  (isOpen_lt continuous_const continuous_time).inter
    ((isOpen_lt continuous_time continuous_const).inter
      ((PDE.isOpen_euclideanBall v₀ R).preimage continuous_velocity))

/-- The closed strip is closed in the ordinary spacetime topology. -/
theorem isClosed_localClosedStrip   :
    IsClosed (localClosedStrip a T v₀ R) :=
  (isClosed_le continuous_const continuous_time).inter
    ((isClosed_le continuous_time continuous_const).inter
      (isClosed_closure.preimage continuous_velocity))

/-- The terminal/lateral trace is closed, including the terminal velocity corner. -/
theorem isClosed_localTrace   :
    IsClosed (localTrace a T v₀ R) :=
  ((isClosed_eq continuous_time continuous_const).inter
    (isClosed_closure.preimage continuous_velocity)).union
    ((isClosed_le continuous_const continuous_time).inter
      ((isClosed_le continuous_time continuous_const).inter
        (isClosed_frontier.preimage continuous_velocity)))

/-- The source strip is a Borel set. -/
theorem measurableSet_localStrip   :
    MeasurableSet (localStrip a T v₀ R) := (isOpen_localStrip a T v₀ R).measurableSet

/-- The exit trace is a Borel set. -/
theorem measurableSet_localTrace   :
    MeasurableSet (localTrace a T v₀ R) := (isClosed_localTrace a T v₀ R).measurableSet

/-- Every open-strip point belongs to the closed strip. -/
theorem localStrip_subset_closed   :
    localStrip a T v₀ R ⊆ localClosedStrip a T v₀ R := by
  intro P hP
  exact ⟨hP.1.le, hP.2.1.le, subset_closure hP.2.2⟩

/-- With ordered endpoints, both exit faces belong to the closed strip. -/
theorem localTrace_subset_closed  {a T : ℝ} (haT : a ≤ T)
    (v₀ : PDE.Vec d) (R : ℝ) :
    localTrace a T v₀ R ⊆ localClosedStrip a T v₀ R := by
  intro P hP
  rcases hP with hP | hP
  · exact ⟨hP.1.symm ▸ haT, hP.1.le, hP.2⟩
  · exact ⟨hP.1, hP.2.1, frontier_subset_closure hP.2.2⟩

/-- A stationary moving domain is the original velocity ball. -/
@[simp] theorem movingDomain_ball_zero  (v₀ : PDE.Vec d) (R t : ℝ) :
    movingDomain (PDE.euclideanBall v₀ R) (fun _ => 0) t = PDE.euclideanBall v₀ R :=
  PDE.translateSet_zero _

variable {v₀ : PDE.Vec d} {R : ℝ}

/-- Physical starting coordinates give a valid evolution state. -/
theorem ball_start_state_mem
    (P : LocalBallStart v₀ R) :
    (P.1.velocity, P.1.position) ∈
      evolutionStateSet (PDE.euclideanBall v₀ R) (fun _ => 0) P.1.time := ⟨(movingDomain_ball_zero v₀ R P.1.time).symm ▸ P.2, mem_univ _⟩

/-- A valid evolution state's first coordinate is its physical velocity. -/
theorem ball_state_velocity_mem   (t : ℝ)
    (w : EvolutionState (PDE.euclideanBall v₀ R) (fun _ => 0) t) :
    w.1.1 ∈ PDE.euclideanBall v₀ R := by
  have hw := w.2.1
  rw [movingDomain_ball_zero] at hw
  exact hw

/-- Convert a physical ball start to its (velocity, position) evolution state. -/
def ballStartState   (P : LocalBallStart v₀ R) :
    EvolutionState (PDE.euclideanBall v₀ R) (fun _ => 0) P.1.time :=
  ⟨_, ball_start_state_mem P⟩

/-- Convert an evolution state at t to a physical point with valid velocity. -/
def ballStateStart   (t : ℝ)
    (w : EvolutionState (PDE.euclideanBall v₀ R) (fun _ => 0) t) :
    LocalBallStart v₀ R :=
  ⟨⟨t, w.1.2, w.1.1⟩, ball_state_velocity_mem t w⟩





/-- Exit coordinates depend continuously on the physical exit point. -/
theorem continuous_exitCoordinates  (P : KineticPoint d) (v₀ : PDE.Vec d) :
    Continuous (exitCoordinates P v₀) :=
  ((continuous_position.sub continuous_const).sub
    ((continuous_time.sub continuous_const).smul continuous_const)).prodMk
    (continuous_time.prodMk continuous_velocity)

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
