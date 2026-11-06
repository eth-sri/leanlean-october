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

/- The open time strip with velocity constrained to a Euclidean ball. -/
def localStrip {d } (a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ) :
    Set (KineticPoint d) :=
  {P | a < P.time ∧ P.time < T ∧ P.velocity ∈ PDE.euclideanBall v₀ R}

/- The closed time strip with velocity constrained to the closed ball. -/
def localClosedStrip {d } (a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ) :
    Set (KineticPoint d) :=
  {P | a ≤ P.time ∧ P.time ≤ T ∧ P.velocity ∈ closure (PDE.euclideanBall v₀ R)}

/- Terminal and lateral velocity faces, including their common corner. -/
def localTrace {d } (a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ) :
    Set (KineticPoint d) :=
  {P | (P.time = T ∧ P.velocity ∈ closure (PDE.euclideanBall v₀ R)) ∨
    (a ≤ P.time ∧ P.time ≤ T ∧ P.velocity ∈ frontier (PDE.euclideanBall v₀ R))}

/- A physical starting point whose velocity is valid for the ball evolution. -/
abbrev LocalBallStart {d : ℕ} (v₀ : PDE.Vec d) (R : ℝ) :=
  {P : KineticPoint d // P.velocity ∈ PDE.euclideanBall v₀ R}

/- The physical position slice through a spacetime point. -/
def physicalPositionSlice {d } (u : KineticPoint d → ℝ) (P : KineticPoint d) :
    PDE.Vec d → ℝ := fun x => u ⟨P.time, x, P.velocity⟩

/- The source kinetic increment based at the center velocity. -/
def kineticIncrement {d } (P₀ P Q : KineticPoint d) : ℝ :=
  |P.time - Q.time| ^ (1 / 2 : ℝ) + PDE.vecEuclideanNorm (P.velocity - Q.velocity) +
    PDE.vecEuclideanNorm
      (P.position - Q.position - (P.time - Q.time) • P₀.velocity) ^ (1 / 3 : ℝ)

/- Position displacement in the centered free-transport frame, with absolute exit data. -/
def exitCoordinates {d } (P : KineticPoint d) (v₀ : PDE.Vec d)
    (Q : KineticPoint d) : PDE.Vec d × TimeVelocity d :=
  (Q.position - P.position - (Q.time - P.time) • v₀, (Q.time, Q.velocity))

/- Fourier phase of the centered position coordinate, retaining exit time and velocity. -/
def exitPhase {d } (ξ : PDE.Vec d) (Q : PDE.Vec d × TimeVelocity d) : ℂ :=
  Complex.exp (-Complex.I * (PDE.vecDot ξ Q.1 : ℂ))

/- Parabolic time--velocity distance, with Euclidean velocity norm. -/
def parabolicDistance {d } (z z' : TimeVelocity d) : ℝ :=
  |z.1 - z'.1| ^ (1 / 2 : ℝ) + PDE.vecEuclideanNorm (z.2 - z'.2)

/- Membership in the open strip unfolds without a coordinate change. -/
theorem isOpen_localStrip {d } (a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ) :
    IsOpen (localStrip a T v₀ R) :=
  (isOpen_lt continuous_const continuous_time).inter
    ((isOpen_lt continuous_time continuous_const).inter
      ((PDE.isOpen_euclideanBall v₀ R).preimage continuous_velocity))

/- The closed strip is closed in the ordinary spacetime topology. -/
theorem isClosed_localClosedStrip {d } (a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ) :
    IsClosed (localClosedStrip a T v₀ R) :=
  (isClosed_le continuous_const continuous_time).inter
    ((isClosed_le continuous_time continuous_const).inter
      (isClosed_closure.preimage continuous_velocity))

/- The terminal/lateral trace is closed, including the terminal velocity corner. -/
theorem isClosed_localTrace {d } (a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ) :
    IsClosed (localTrace a T v₀ R) :=
  ((isClosed_eq continuous_time continuous_const).inter
    (isClosed_closure.preimage continuous_velocity)).union
    ((isClosed_le continuous_const continuous_time).inter
      ((isClosed_le continuous_time continuous_const).inter
        (isClosed_frontier.preimage continuous_velocity)))

/- The source strip is a Borel set. -/
theorem measurableSet_localStrip {d } (a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ) :
    MeasurableSet (localStrip a T v₀ R) := (isOpen_localStrip a T v₀ R).measurableSet

/- The exit trace is a Borel set. -/
theorem measurableSet_localTrace {d } (a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ) :
    MeasurableSet (localTrace a T v₀ R) := (isClosed_localTrace a T v₀ R).measurableSet

/- Every open-strip point belongs to the closed strip. -/
theorem localStrip_subset_closed {d } (a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ) :
    localStrip a T v₀ R ⊆ localClosedStrip a T v₀ R := by
  intro P hP
  exact ⟨hP.1.le, hP.2.1.le, subset_closure hP.2.2⟩

/- With ordered endpoints, both exit faces belong to the closed strip. -/
theorem localTrace_subset_closed {d a T} (haT : a ≤ T)
    (v₀ : PDE.Vec d) (R : ℝ) :
    localTrace a T v₀ R ⊆ localClosedStrip a T v₀ R := by
  intro P hP
  rcases hP with hP | hP
  · exact ⟨hP.1.symm ▸ haT, hP.1.le, hP.2⟩
  · exact ⟨hP.1, hP.2.1, frontier_subset_closure hP.2.2⟩

/- A stationary moving domain is the original velocity ball. -/
@[simp] theorem movingDomain_ball_zero {d } (v₀ : PDE.Vec d) (R t : ℝ) :
    movingDomain (PDE.euclideanBall v₀ R) (fun _ => 0) t = PDE.euclideanBall v₀ R :=
  PDE.translateSet_zero _

/- Physical starting coordinates give a valid evolution state. -/
theorem ball_start_state_mem {d } {v₀ : PDE.Vec d} {R }
    (P : LocalBallStart v₀ R) :
    (P.1.velocity, P.1.position) ∈
      evolutionStateSet (PDE.euclideanBall v₀ R) (fun _ => 0) P.1.time :=  ⟨(movingDomain_ball_zero v₀ R P.1.time).symm ▸ P.2, mem_univ _⟩

/- A valid evolution state's first coordinate is its physical velocity. -/
theorem ball_state_velocity_mem {d } {v₀ : PDE.Vec d} {R } (t )
    (w : EvolutionState (PDE.euclideanBall v₀ R) (fun _ => 0) t) :
    w.1.1 ∈ PDE.euclideanBall v₀ R := by
  have hw := w.2.1
  rw [movingDomain_ball_zero] at hw
  exact hw

/- Convert a physical ball start to its (velocity, position) evolution state. -/
def ballStartState {d } {v₀ : PDE.Vec d} {R } (P : LocalBallStart v₀ R) :
    EvolutionState (PDE.euclideanBall v₀ R) (fun _ => 0) P.1.time :=
  ⟨(P.1.velocity, P.1.position), ball_start_state_mem P⟩

/- Convert an evolution state at t to a physical point with valid velocity. -/
def ballStateStart {d } {v₀ : PDE.Vec d} {R } (t )
    (w : EvolutionState (PDE.euclideanBall v₀ R) (fun _ => 0) t) :
    LocalBallStart v₀ R :=
  ⟨⟨t, w.1.2, w.1.1⟩, ball_state_velocity_mem t w⟩

/- Starting-point conversion preserves every physical coordinate. -/
theorem continuous_exitCoordinates {d } (P : KineticPoint d) (v₀ : PDE.Vec d) :
    Continuous (exitCoordinates P v₀) :=
  ((continuous_position.sub continuous_const).sub
    ((continuous_time.sub continuous_const).smul continuous_const)).prodMk
    (continuous_time.prodMk continuous_velocity)

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
