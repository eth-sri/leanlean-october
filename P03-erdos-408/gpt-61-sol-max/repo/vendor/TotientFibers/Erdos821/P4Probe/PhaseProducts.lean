module
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import Erdos821.P3Clean.Phases

public import Erdos821.P4Probe.RawKernel
public import Erdos821.P4Probe.CancellationTasks

@[expose] public section

set_option autoImplicit false

namespace Erdos821.P4Probe
open Blueprint.Graph

lemma imaginaryPower_eq_mellin  n   ζ  :
    imaginaryPower n ζ = Blueprint.Analytic.mellin n ζ := by
  unfold imaginaryPower Blueprint.Analytic.mellin
  congr 1
  ring

lemma imaginaryPower_mul  n k  (hn : 0 < n) (hk : 0 < k)  ζ  :
    imaginaryPower (n * k) ζ = imaginaryPower n ζ * imaginaryPower k ζ := by solve_by_elim [_root_.Erdos821.P3Clean.imaginaryPower_mul]

lemma phase_mul_shift  θ C D  :
    phase (θ * (C * D)) = Blueprint.Analytic.e ((θ * C) * D) := by
  unfold phase Blueprint.Analytic.e
  congr 1
  ring_nf

end Erdos821.P4Probe
