module

public import Chazelle.Golf

public import Chazelle.Exec.Interp
public import Chazelle.Machine.Basic

/-!
# The rational interpreter simulates the real RAM

`castPoly : QPolygon → Polygon` and `castConfig : QConfig → Config` embed rational data into the
real semantics of `Chazelle/Spec.lean` (through the ordered-field embedding `ℚ → ℝ`; natural
words and outputs are unchanged).  The main results:

* `step_castConfig`: `step prog (castPoly Pq) (castConfig c) = (stepQ prog Pq c).map castConfig`
  (real comparisons agree with rational ones since the cast is an order embedding, and
  division by zero faults in both);
* `run_castConfig`: the same for any number of steps;
* `runQ_sound`: if the executable run `runQ prog Pq fuel` halts with `(cq, k)`, then the real
  machine on `castPoly Pq` executes exactly `k` instructions, sits at `halt`, and has emitted
  `cq.output`;
* `runQ_runsWithin`: with the maximal natural word `W` recorded along the run (computed by
  `runQW`), a halting rational run yields `RunsWithin prog (castPoly Pq) W (k + 1) cq.output`.
-/

namespace Chazelle

namespace Exec

open Std

@[expose] public section

/-- Embed a rational point into the real plane. -/
noncomputable def castPt (p : ℚ × ℚ) : Point := ((p.1 : ℝ), (p.2 : ℝ))

/-- Embed a rational polygon into the real plane. -/
noncomputable def castPoly (Pq : QPolygon) : Polygon := ⟨Pq.map castPt⟩

/-- Embed a rational configuration into a real one (absent keys read as `0`). -/
noncomputable def castConfig (c : QConfig) : Config where
  pc := c.pc
  nreg := fun i => c.nr i
  rreg := fun i => (c.rr i : ℝ)
  nmem := fun i => c.nm i
  rmem := fun i => (c.rm i : ℝ)
  output := c.output

/-- The embedded polygon has the same number of vertices. -/
@[simp] theorem castPoly_n (Pq : QPolygon) : (castPoly Pq).n = Pq.length := by
  Θ castPoly, Polygon.n

/-- Vertex lookup commutes with the embedding (including the out-of-range origin). -/
@[simp] theorem castPoly_vtx (Pq : QPolygon) (i : ℕ) :
    (castPoly Pq).vtx i = castPt (listVtx Pq i) := by
  ϴ castPoly, Polygon.vtx, listVtx, List.getD_eq_getElem?_getD, List.getElem?_map
  cases Pq[i]? <;> simp [castPt]

@[simp] theorem castConfig_pc (c : QConfig) : (castConfig c).pc = c.pc := rfl

@[simp] theorem castConfig_output (c : QConfig) : (castConfig c).output = c.output := rfl

end

end Exec

end Chazelle
