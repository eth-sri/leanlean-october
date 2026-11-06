module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockCalculusDirectional
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarAdaptersCalculus
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockCalculus
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! # The three affine clock slices and the scalar/native derivative bridge -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov.Parabolic
open scoped Topology

/- Clock direction when physical time alone varies. -/
def Clock.timeDirection (c : Clock) : Fin 3 → ℝ :=
  (-c.vbar / c.r ^ 3) • coordinateDirection 1

/- Clock direction when physical position alone varies. -/
def Clock.positionDirection (c : Clock) : Fin 3 → ℝ :=
  (1 / (c.vbar * c.r ^ 2)) • coordinateDirection 0 +
    (1 / c.r ^ 3) • coordinateDirection 1

/- Clock direction when physical velocity alone varies. -/
def Clock.velocityDirection (c : Clock) : Fin 3 → ℝ :=
  (1 / c.r) • coordinateDirection 2

/- The physical time slice is the explicit affine line in clock coordinates. -/
theorem Clock.map_time_line (c : Clock) (e p : Point) (t : ℝ) :
    scalarCoordinates (c.map e ⟨t, p.position, p.velocity⟩) =
      scalarCoordinates (c.map e p) + (t-p.time) • c.timeDirection := by
  ext i
  fin_cases i
  all_goals simp [scalarCoordinates, Clock.map, Clock.timeDirection, coordinateDirection]
  all_goals ring

/- The physical position slice is the explicit affine line in clock coordinates. -/
theorem Clock.map_position_line (c : Clock) (e p : Point) (x : ℝ) :
    scalarCoordinates (c.map e ⟨p.time, fun _ => x, p.velocity⟩) =
      scalarCoordinates (c.map e p) + (x-p.position 0) • c.positionDirection := by
  ext i
  fin_cases i
  all_goals simp [scalarCoordinates, Clock.map, Clock.positionDirection, coordinateDirection]
  all_goals ring

/- The physical velocity slice is the explicit affine line in clock coordinates. -/
theorem Clock.map_velocity_line (c : Clock) (e p : Point) (v : ℝ) :
    scalarCoordinates (c.map e ⟨p.time, p.position, fun _ => v⟩) =
      scalarCoordinates (c.map e p) + (v-p.velocity 0) • c.velocityDirection := by
  ext i
  fin_cases i
  all_goals simp [scalarCoordinates, Clock.map, Clock.velocityDirection, coordinateDirection]
  all_goals ring

/- Every scalar coordinate slice reconstructs its literal kinetic slice. -/
theorem scalarPoint_update (p : Point) (i : Fin 3) (t : ℝ) :
    scalarPoint (Function.update (scalarCoordinates p) i t) =
      match i with
      | 0 => ⟨t, p.position, p.velocity⟩
      | 1 => ⟨p.time, fun _ => t, p.velocity⟩
      | 2 => ⟨p.time, p.position, fun _ => t⟩ := by
  fin_cases i <;> ext j
  all_goals try (have hj := Fin.eq_zero j; subst j)
  all_goals simp [scalarPoint, scalarCoordinates, Function.update]

/- Native kinetic derivatives equal the three scalar-coordinate directional derivatives. -/
theorem Clock.pullback_derivatives (c : Clock) (e p : Point) (h )
    (hh : ContDiffAt ℝ 2 (h ∘ scalarPoint) (scalarCoordinates (c.map e p))) :
    kineticTimeDerivative (h ∘ c.map e) p =
        directional (h ∘ scalarPoint) c.timeDirection (scalarCoordinates (c.map e p)) ∧
      kineticPositionGradient (h ∘ c.map e) p 0 =
        directional (h ∘ scalarPoint) c.positionDirection (scalarCoordinates (c.map e p)) ∧
      kineticVelocityHessian (h ∘ c.map e) p 0 0 =
        directional (directional (h ∘ scalarPoint) c.velocityDirection)
          c.velocityDirection (scalarCoordinates (c.map e p)) := by
  have ht : (fun t => h (c.map e ⟨t, p.position, p.velocity⟩)) =
      fun t => (h ∘ scalarPoint)
        (scalarCoordinates (c.map e p) + (t-p.time) • c.timeDirection) := by
    funext t
    rw [← c.map_time_line e p t]
    simp only [Function.comp_apply, scalarPoint_coordinates]
  have hx : (fun x => h (c.map e ⟨p.time, fun _ => x, p.velocity⟩)) =
      fun x => (h ∘ scalarPoint)
        (scalarCoordinates (c.map e p) + (x-p.position 0) • c.positionDirection) := by
    funext x
    rw [← c.map_position_line e p x]
    simp only [Function.comp_apply, scalarPoint_coordinates]
  have hv : (fun v => h (c.map e ⟨p.time, p.position, fun _ => v⟩)) =
      fun v => (h ∘ scalarPoint)
        (scalarCoordinates (c.map e p) + (v-p.velocity 0) • c.velocityDirection) := by
    funext v
    rw [← c.map_velocity_line e p v]
    simp only [Function.comp_apply, scalarPoint_coordinates]
  rw [kineticPositionGradient_scalar, kineticVelocityHessian_scalar]
  change deriv _ p.time = _ ∧ deriv _ (p.position 0) = _ ∧ deriv (deriv _) (p.velocity 0) = _
  simp only [Function.comp_apply]
  rw [ht, hx, hv]
  exact ⟨deriv_coordinateLine _ _ _ _ (hh.differentiableAt (by norm_num)),
    deriv_coordinateLine _ _ _ _ (hh.differentiableAt (by norm_num)),
    deriv_deriv_coordinateLine _ _ _ _ hh⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
