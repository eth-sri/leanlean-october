module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnGeometryDistance
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Assembly
import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationContractionGeometry
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnGeometryBoxes

/-! # The local Holder modulus relative to the larger return-box supremum -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Set MeasureTheory Holder

/- The concrete return boxes increase with their radius parameter. -/
theorem returnBox_mono (v : ℝ) {a b } (hab : a ≤ b) :
    returnBox v a ⊆ returnBox v b := by
  intro p hp
  exact ⟨hp.1.trans_le (by linarith), hp.2.1.trans_le (by linarith),
    hp.2.2.trans_le (by linarith)⟩

/- The generic Holder theorem gives a modulus measured against the larger supremum. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
