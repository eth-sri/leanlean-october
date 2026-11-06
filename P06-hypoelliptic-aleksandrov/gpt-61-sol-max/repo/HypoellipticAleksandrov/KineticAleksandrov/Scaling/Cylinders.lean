module

public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Affine
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonEvolution
import Lean.Elab.Tactic.SolveByElim



/-!
# Moving cylinders under an affine change of variables

For compatible moving domains (`MapsDomain`), every cylinder, terminal face and lateral
frontier of the hat data is the preimage of the corresponding original set under the change
of variables on kinetic points (resp. raw coordinates).
-/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov.Scaling

open MeasureTheory Set
open HypoellipticAleksandrov

namespace KineticAffineScaling

variable {d : ℕ} (Φ : KineticAffineScaling d)

variable {x y : ℝ}

theorem time_lt_iff  : Φ.time x < Φ.time y ↔ x < y := by
  unfold time
  constructor
  · intro h
    exact lt_of_mul_lt_mul_left (by linarith) Φ.a_pos.le
  · intro h
    nlinarith [Φ.a_pos]

theorem time_le_iff  : Φ.time x ≤ Φ.time y ↔ x ≤ y := by
  unfold time
  constructor
  · intro h
    exact le_of_mul_le_mul_left (by linarith) Φ.a_pos
  · intro h
    nlinarith [Φ.a_pos]

theorem time_inj  : Φ.time x = Φ.time y ↔ x = y := by
  constructor
  · intro h
    exact le_antisymm (Φ.time_le_iff.1 h.le) (Φ.time_le_iff.1 h.ge)
  · intro h
    rw [h]

variable {Ω Ω' : PDE.VelocityRegion d} {γ γ' : ℝ → PDE.Vec d}



/-- The raw interior cylinder of an open domain with continuous curve is open. -/
theorem isOpen_evolutionPastInteriorRaw (hΩ : IsOpen Ω) (hγ : Continuous γ) (τ : ℝ) :
    IsOpen (evolutionPastInteriorRaw Ω γ τ) := (KineticAleksandrov.isOpen_evolutionPastInteriorRaw hΩ hγ τ)

variable {Φ}

variable (h : Φ.MapsDomain Ω γ Ω' γ')
include h

variable (τ : ℝ)

variable (p : KineticPoint d)

theorem MapsDomain.mem_openCylinder_iff   :
    p ∈ evolutionPastOpenCylinder Ω' γ' τ ↔
      Φ.point p ∈ evolutionPastOpenCylinder Ω γ (Φ.time τ) := by
  simp only [evolutionPastOpenCylinder, mem_ofPred_eq, point_time, point_position,
    Φ.time_lt_iff, h.mem_iff]

theorem MapsDomain.mem_closedCylinder_iff   :
    p ∈ evolutionPastClosedCylinder Ω' γ' τ ↔
      Φ.point p ∈ evolutionPastClosedCylinder Ω γ (Φ.time τ) := by
  simp only [evolutionPastClosedCylinder, mem_ofPred_eq, point_time, point_position,
    Φ.time_le_iff, h.closure_eq, mem_preimage]

theorem MapsDomain.mem_terminalClosure_iff   :
    p ∈ evolutionTerminalClosure Ω' γ' τ ↔
      Φ.point p ∈ evolutionTerminalClosure Ω γ (Φ.time τ) := by
  simp only [evolutionTerminalClosure, mem_ofPred_eq, point_time, point_position,
    Φ.time_inj, h.closure_eq, mem_preimage]

theorem MapsDomain.mem_lateralFrontier_iff   :
    p ∈ evolutionLateralFrontier Ω' γ' τ ↔
      Φ.point p ∈ evolutionLateralFrontier Ω γ (Φ.time τ) := by
  simp only [evolutionLateralFrontier, mem_ofPred_eq, point_time, point_position,
    Φ.time_le_iff, h.frontier_eq, mem_preimage]

theorem MapsDomain.mem_interiorRaw_iff  (q : ℝ × (PDE.Vec d × PDE.Vec d)) :
    q ∈ evolutionPastInteriorRaw Ω' γ' τ ↔
      Φ.raw q ∈ evolutionPastInteriorRaw Ω γ (Φ.time τ) := by
  simp only [evolutionPastInteriorRaw, mem_ofPred_eq, raw, Φ.time_lt_iff, h.mem_iff]

end KineticAffineScaling

end HypoellipticAleksandrov.KineticAleksandrov.Scaling
