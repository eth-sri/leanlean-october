module
public import Mathlib.Tactic

public import Erdos821.S2.MemoryEdge

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

lemma norm_imaginaryPower  n   ζ  : ‖imaginaryPower n ζ‖ = 1 := by
  unfold imaginaryPower
  rw [Complex.norm_exp]
  simp_all [Real.log, Complex.I]

lemma norm_phase  t  : ‖phase t‖ = 1 := by
  unfold phase
  rw [Complex.norm_exp]
  simp_all

end Erdos821.P3Edge
