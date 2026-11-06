module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Programs.Sec3.Theorem17.Witnesses.Scan

@[expose] public section

/-!
# All-edges Exact Triangle as a task

Footnote 10 of the paper: the proof of Theorem 17 "also solves the all-edges version of Exact
Triangle (scanning each pair only until its zero triangle is found), to which the (min,+)-product
reduces on the same `n` vertices".  The all-edges version asks, for every pair `(a, b)` of the two
outer parts, whether it lies in a zero triangle.

This file fixes the task (`aeTask`), in the calling convention of upstream's tasks
(`Light.Sec3.pairsTask` is the pattern): ae(n, U, ab, bc, ac, out, fr) writes `n²` flags to `out`,
cell `a n + b` holding 1 if `w(a,b) + w(b,c) + w(a,c) = 0` for some `c` and 0 if not (`aeFlags`).
-/

namespace ImprovedExponents.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

/-- Three `n × n` matrices of weights in the memory, and the place for `n²` flags. -/
structure AeInst where
  (n U ab bc ac out : ℕ)
  (AB BC AC : List ℤ)

/-- The three matrices of an instance, as a `TriInst` (the instance of upstream's `etTask`). -/
abbrev AeInst.tri (x : AeInst) : TriInst := ⟨x.n, x.U, x.ab, x.bc, x.ac, x.AB, x.BC, x.AC⟩

/-- The triangle input contract, plus room for the flags. -/
structure AeInst.Pre (x : AeInst) (μ : Light.Memory) (fr : ℕ) : Prop extends
    tri : x.tri.Pre μ fr where
  belowOut : x.out + x.n * x.n ≤ fr

/-- The flags: cell `a n + b` holds 1 if `w(a,b) + w(b,c) + w(a,c) = 0` for some `c < n`, and 0 if
not; the pair `(a, b)` of the cell `q < n²` is `(q / n, q % n)`. -/
noncomputable def aeFlags n (AB BC AC : List ℤ) :=
  (List.range (n * n)).map fun q =>
    flag (∃ c < n, AB.getD q 0 + BC.getD (q % n * n + c) 0 + AC.getD (q / n * n + c) 0 = 0)

@[simp] theorem length_aeFlags n AB BC AC :
    (aeFlags n AB BC AC).length = n * n := by
  simp [aeFlags]

/-- The flag of the cell `q < n²`. -/
theorem aeFlags_getD {n} AB BC AC {q} (hq : q < n * n) :
    (aeFlags n AB BC AC).getD q 0 =
      flag (∃ c < n, AB.getD q 0 + BC.getD (q % n * n + c) 0 + AC.getD (q / n * n + c) 0 = 0) := by
  simp [aeFlags, List.getD_eq_getElem?_getD, hq]

/-- The flag of the pair `(a, b)`, in terms of the scan of the whole part `C` (upstream's
`scanHit n AB BC AC a b 0 n`, the pure function behind the brute force of Theorem 17). -/
theorem aeFlags_getD_eq_bit_scanHit {n} AB BC AC {a b} (ha : a < n)
    (hb : b < n) :
    (aeFlags n AB BC AC).getD (a * n + b) 0 = bit (scanHit n AB BC AC a b 0 n) := by



  rw [aeFlags_getD _ _ _ (by nlinarith), (by
    grind [Nat.add_mul_div_right, Nat.div_eq_of_lt]
   : (a * n + b) / n = a), (by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
   : (a * n + b) % n = b), ← flag_eq_bit]
  ram_arith [scanHit]

/-- **All-edges Exact Triangle**: ae(n, U, ab, bc, ac, out, fr) writes the `n²` flags to `out`. -/
noncomputable def aeTask : Task where
  Inst := AeInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.ab, x.bc, x.ac, x.out]
  Pre := AeInst.Pre
  Post x μ fr _ μ' := Seg μ' x.out (aeFlags x.n x.AB x.BC x.AC) ∧ KeptBut μ μ' fr x.out (x.n * x.n)

end ImprovedExponents.AllEdges
