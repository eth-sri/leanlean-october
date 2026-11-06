module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvRExtSpec
public import Chazelle.Core.DownPhaseMathHR1

/-!
# Down phase, extraction (D6): the index arithmetic of the extraction RAM

The extraction runs over the chord records `(h, lp, rp)` of a normal form `N_R` of the chain
model of the region chain `C = ⟨H.poly Q, 0, m⟩` (`H = regHost li n N r`, `m + 1` host points).
A chord end is the walk position `⟨p, h + 1⟩` of the corrected walk `C.sideWalk C.sideBeta`:
walk edges `0 … 5` box and slit, `6 … 2m + 5` the tour of the double boundary from the top vertex
`T = C.topIdx`, `2m + 6` up the slit.  For `6 ≤ p ≤ 2m + 6`:

* `tU m T β p = (sideS + (p - 6)) mod 2m` is the position in the Euler tour of the path
  `0, 1, …, m`; the tour edge goes up (side `A`, `tU < m`) or down (side `B`);
* `tK m T β p = sideE m (tU …)` is the chain vertex (= host point) at its start;
* `tZ … h p`: the chord height `h` is the height vertex of that host point, i.e. the end is the
  start vertex of the walk edge (distinct heights);
* `RegIn`: the end is at a **regular position on the inner side** (side `A` iff `li`): not at a
  chain end `0` or `m` (where the tour turns around), not on the slit above the top vertex;
* `KeptT`: the extraction keeps a chord iff one of its ends is at such a position (X-R1);
* `pEdge`, `xPos`: the interior walk position of a kept end (X-R2), from the symbolic host point
  at the start of its walk edge.

The comparison of interior keys (`posLt`) and the bucket formula (`bktF`) are also here.
-/

namespace Chazelle.Core

namespace DrvX

@[expose] public section

open Chazelle.Chain (sideE)
open DrvR (ivB qE)

/-- The symbolic host point number `k`. -/
def hpt (n : ℕ) (H : Host) (k : ℕ) : SymPt := (H.pts n).getD k (.vtx 0)

/-- The height vertex of a symbolic point. -/
def hidx : SymPt → ℕ
  | .vtx j => j
  | .onEdge _ h => h

/-- The tour offset (`Chain.sideS`). -/
def tS (m T : ℕ) (β : Bool) : ℕ := if β then T else 2 * m - T

/-- The tour position of walk edge `p`. -/
def tU (m T : ℕ) (β : Bool) (p : ℕ) : ℕ := (tS m T β + (p - 6)) % (2 * m)

/-- The chain vertex at the start of walk edge `p`. -/
def tK (m T : ℕ) (β : Bool) (p : ℕ) : ℕ := sideE m (tU m T β p)

/-- The end at walk edge `p`, height `h` is the start vertex of `p`. -/
def tZ (n : ℕ) (H : Host) (m T : ℕ) (β : Bool) (h p : ℕ) : Prop :=
  h = hidx (hpt n H (tK m T β p))

instance (n : ℕ) (H : Host) (m T : ℕ) (β : Bool) (h p : ℕ) : Decidable (tZ n H m T β h p) := by
  unfold tZ; infer_instance

/-- **A regular position on the inner side.** -/
def RegIn (n : ℕ) (H : Host) (li : Bool) (m T : ℕ) (β : Bool) (h p : ℕ) : Prop :=
  6 ≤ p ∧ p ≤ 2 * m + 6 ∧ (p = 2 * m + 6 → tZ n H m T β h p) ∧
    ¬ (tZ n H m T β h p ∧ (tK m T β p = 0 ∨ tK m T β p = m)) ∧ (tU m T β p < m ↔ li = true)

instance (n : ℕ) (H : Host) (li : Bool) (m T : ℕ) (β : Bool) (h p : ℕ) :
    Decidable (RegIn n H li m T β h p) := by
  unfold RegIn; infer_instance

/-- **The kept test** (X-R1). -/
def KeptT (n : ℕ) (H : Host) (li : Bool) (m T : ℕ) (β : Bool) (h lp rp : ℕ) : Prop :=
  RegIn n H li m T β h lp ∨ RegIn n H li m T β h rp

instance (n : ℕ) (H : Host) (li : Bool) (m T : ℕ) (β : Bool) (h lp rp : ℕ) :
    Decidable (KeptT n H li m T β h lp rp) := by
  unfold KeptT; infer_instance

/-- **The interior walk edge of a host point** (X-R2): the walk edge starting at a vertex, or the
walk edge carrying an edge point, or the next one if the point is the end of that walk edge (an arc
end at a vertex). -/
def pEdge (li : Bool) (n : ℕ) : SymPt → ℕ
  | .vtx j => ivB li n j
  | .onEdge e h => if h = ivB li n ((qE li n e + 1) % n) then (qE li n e + 1) % n else qE li n e

/-- **The interior walk position of a kept end.** -/
def xPos (n : ℕ) (H : Host) (li : Bool) (m T : ℕ) (β : Bool) (h p : ℕ) : WPos :=
  ⟨pEdge li n (hpt n H (tK m T β p)), h + 1⟩

/-- The interior triple of a kept chord record. -/
def xTriple (n : ℕ) (H : Host) (li : Bool) (m T : ℕ) (β : Bool) (h lp rp : ℕ) : ℕ × ℕ × ℕ :=
  (h, (xPos n H li m T β h lp).edge, (xPos n H li m T β h rp).edge)

/-! ## Comparing interior keys -/

/-- The interior walk edge `q` goes up (`Q` vertex heights). -/
def EdgeUp (Q : Polygon) (li : Bool) (q : ℕ) : Prop :=
  (Q.vtx (ivB li Q.n q)).2 < (Q.vtx (ivB li Q.n ((q + 1) % Q.n))).2

/-- **The key order of two positions of the interior walk**, by edges, then heights. -/
def PosLt (Q : Polygon) (li : Bool) (x y : WPos) : Prop :=
  x.edge < y.edge ∨ (x.edge = y.edge ∧ x.hgt ≠ y.hgt ∧
    (EdgeUp Q li x.edge ↔ (Q.vtx (x.hgt - 1)).2 < (Q.vtx (y.hgt - 1)).2))

/-- Equal keys: equal positions. -/
def PosEq (x y : WPos) : Prop := x.edge = y.edge ∧ x.hgt = y.hgt

/-- **The bucket formula** for a position `x` on the closure of arc `j` (`A` arcs). -/
def bktF (A j : ℕ) (eqS eqE gtS : Prop) [Decidable eqS] [Decidable eqE] [Decidable gtS] : ℕ :=
  if eqS then 2 * j + 1 else if eqE then 2 * ((j + 1) % A) + 1 else if gtS then 2 * j + 2 else 0

/-! ## Basic arithmetic -/

theorem tU_lt {m T : ℕ} (β : Bool) (hm : 1 ≤ m) (p : ℕ) : tU m T β p < 2 * m :=
  Nat.mod_lt _ (⋄)

theorem tK_le {m T : ℕ} (β : Bool) (hm : 1 ≤ m) (p : ℕ) : tK m T β p ≤ m :=
  Chazelle.Chain.sideE_le (tU_lt β hm p).le

theorem tK_eq_of_lt {m T : ℕ} {β : Bool} {p : ℕ} (h : tU m T β p < m) : tK m T β p = tU m T β p := by
  unfold tK sideE; rw [ite_eq_left h.le]

theorem tK_eq_of_ge {m T : ℕ} {β : Bool} {p : ℕ} (h : m ≤ tU m T β p) :
    tK m T β p = 2 * m - tU m T β p := by
  unfold tK sideE; split_ifs with h' <;> omega

theorem tK_eq_zero_iff {m T : ℕ} (β : Bool) (hm : 1 ≤ m) (p : ℕ) :
    tK m T β p = 0 ↔ tU m T β p = 0 := by
  have := tU_lt (T := T) β hm p
  unfold tK sideE; split_ifs <;> omega

theorem tK_eq_m_iff {m T : ℕ} (β : Bool) (hm : 1 ≤ m) (p : ℕ) :
    tK m T β p = m ↔ tU m T β p = m := by
  have := tU_lt (T := T) β hm p
  unfold tK sideE; split_ifs <;> omega

/-- The last walk edge (up the slit) has the tour position of the first one. -/
theorem tU_last (m T : ℕ) (β : Bool) : tU m T β (2 * m + 6) = tU m T β 6 := by
  unfold tU
  rw [show 2 * m + 6 - 6 = 2 * m by omega, show 6 - 6 = 0 by rfl, add_zero, Nat.add_mod_right]

theorem tK_last (m T : ℕ) (β : Bool) : tK m T β (2 * m + 6) = tK m T β 6 := by
  unfold tK; rw [tU_last]

/-- `ivB` is an involution. -/
theorem ivB_ivB (li : Bool) {n p : ℕ} (hp : p < n) : ivB li n (ivB li n p) = p := by
  unfold ivB; cases li <;> simp; omega

/-- `qE` is an involution. -/
theorem qE_qE (li : Bool) {n e : ℕ} (he : e < n) : qE li n (qE li n e) = e := by
  unfold qE
  cases li
  · ϴ Bool.false_eq_true, ite_false
    by_cases h : e + 1 < n
    · rw [ite_eq_left h, ite_eq_left (⋄)]; omega
    · rw [ite_eq_right h, ite_eq_right (⋄)]; omega
  · simp

end

end DrvX

end Chazelle.Core
