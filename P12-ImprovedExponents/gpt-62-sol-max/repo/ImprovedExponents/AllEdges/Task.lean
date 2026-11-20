module

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
structure AeInst extends TriInst where
  out : ℕ

/-- An Exact Triangle instance with a separate output region. -/
structure AeInst.Pre (x : AeInst) (μ : ℕ → ℤ) (fr : ℕ) extends x.toTriInst.Pre μ fr where
  belowOut : x.out + x.n * x.n ≤ fr
  apartAB : Apart x.ab (x.n * x.n) x.out (x.n * x.n)
  apartBC : Apart x.bc (x.n * x.n) x.out (x.n * x.n)
  apartAC : Apart x.ac (x.n * x.n) x.out (x.n * x.n)

/-- Put the output of a decision instance immediately after its inputs. -/
abbrev AeInst.scratch (x : TriInst) (fr : ℕ) : AeInst := ⟨x, fr⟩

theorem AeInst.scratch_pre {x : TriInst} {μ : ℕ → ℤ} {fr : ℕ} (h : x.Pre μ fr) :
    (AeInst.scratch x fr).Pre μ (fr + x.n * x.n) :=
  ⟨h.mono (Nat.le_add_right ..), le_rfl, .inl h.arrAB.below, .inl h.arrBC.below, .inl h.arrAC.below⟩

/-- The flags: cell `a n + b` holds 1 if `w(a,b) + w(b,c) + w(a,c) = 0` for some `c < n`, and 0 if
not; the pair `(a, b)` of the cell `q < n²` is `(q / n, q % n)`. -/
noncomputable def aeFlags (n : ℕ) (AB BC AC : List ℤ) : List ℤ :=
  (List.range (n * n)).map fun q =>
    flag (∃ c < n, AB.getD q 0 + BC.getD (q % n * n + c) 0 + AC.getD (q / n * n + c) 0 = 0)

@[simp] theorem length_aeFlags (n : ℕ) (AB BC AC : List ℤ) :
    (aeFlags n AB BC AC).length = n * n := by
  simp [aeFlags]

/-- The flag of the cell `q < n²`. -/
theorem aeFlags_getD {n : ℕ} (AB BC AC : List ℤ) {q : ℕ} (hq : q < n * n) :
    (aeFlags n AB BC AC).getD q 0 =
      flag (∃ c < n, AB.getD q 0 + BC.getD (q % n * n + c) 0 + AC.getD (q / n * n + c) 0 = 0) := by
  simp [aeFlags, hq]

/-- The flag of the pair `(a, b)`, in terms of the scan of the whole part `C` (upstream's
`scanHit n AB BC AC a b 0 n`, the pure function behind the brute force of Theorem 17). -/
theorem aeFlags_getD_eq_bit_scanHit {n : ℕ} (AB BC AC : List ℤ) {a b : ℕ} (ha : a < n)
    (hb : b < n) :
    (aeFlags n AB BC AC).getD (a * n + b) 0 = bit (scanHit n AB BC AC a b 0 n) := by
  rw [aeFlags_getD _ _ _ (Nat.mul_add_lt_mul ha hb), Nat.mul_add_div_of_lt hb,
    Nat.mul_add_mod_of_lt hb, ← flag_eq_bit]
  congr 1
  simp only [scanHit, List.any_eq_true, List.mem_range, decide_eq_true_eq, Nat.add_zero]

/-- **All-edges Exact Triangle**: ae(n, U, ab, bc, ac, out, fr) writes the `n²` flags to `out`. -/
noncomputable def aeTask : Task where
  Inst := AeInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.ab, x.bc, x.ac, x.out]
  Pre := AeInst.Pre
  Post x μ fr _ μ' := Seg μ' x.out (aeFlags x.n x.AB x.BC x.AC) ∧ KeptBut μ μ' fr x.out (x.n * x.n)

end ImprovedExponents.AllEdges
