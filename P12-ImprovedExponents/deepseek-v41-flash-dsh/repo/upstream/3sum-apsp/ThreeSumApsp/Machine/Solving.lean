/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperStatements
public import ThreeSumApsp.Util.Asymptotics.Dominated
public import ThreeSumApsp.Util.Asymptotics.Powers
public import Mathlib.Tactic.Linarith
public import ThreeSumApsp.TacticsShort

/-!
# The notions of solving are monotone

That the program `P` with slope `b` solves the problem on the instances in `dom` within time `T`, at
every admissible word size, stays true for a larger slope, a smaller set of instances and a larger
time bound (`Solves.mono`).  The same holds for a two-stage data structure (`IsDataStructure.mono`).

* The item statements on the problems of the end statement use `SolvesWithin`.  It is `Solves` for
  the problem `ofEnd Q`, whose instances carry their size and a bound on their numbers
  (`solvesWithin_iff`, `solvedInTimeAt_iff`).

* A statement "there are a program and a constant `C` such that the time is at most `C f(x)`" stays
  true for every bound `g` with `f = O(g)`: `exists_solves_of_dominated`, and
  `exists_isDataStructure_of_dominated` for a data structure.
* For the bounds `O(n^a (log n)^e)` in one size: a larger exponent (`SolvedInTime.mono_exponent`),
  and a larger exponent that absorbs the logarithms (`SolvedInPolylogTime.solvedInTime`).
-/

public section

namespace ThreeSumApsp.WordRam

open EndStatement (Instr)
open Filter

/-! ## The problems of the end statement as problems in the sense of `Problem` -/

/-- An instance of a problem of the end statement, with its size `n` and a bound `U` on its
numbers. -/
structure Bounded (Q : EndStatement.Problem) where
  /-- The size. -/
  n : ℕ
  /-- The bound on the absolute values of the numbers of the input. -/
  U : ℕ
  /-- The instance. -/
  x : Q.Instance n
  /-- The numbers are bounded. -/
  bounded : ∀ a ∈ Q.input x, a.natAbs ≤ U

/-- The numbers of the input of a bounded instance are within the bound. -/
theorem Bounded.abs_le {Q : EndStatement.Problem} {x : Bounded Q} {a : ℤ} (ha : a ∈ Q.input x.x) :
    |a| ≤ (x.U : ℤ) := by
  rw [Int.abs_eq_natAbs]
  exact_mod_cast x.bounded a ha

/-- A problem of the end statement as a `Problem`, read as `EndStatement.Problem.SolvedBy` reads it:
the size is the one parameter of the word size, it stands in cell 0 in front of the input, the
verdict has to be `accept` exactly if the answer is yes, and the output has to be right. -/
abbrev ofEnd (Q : EndStatement.Problem) : Problem where
  Inst := Bounded Q
  params x := [x.n]
  input x := (x.n : ℤ) :: Q.input x.x
  IsAnswer x verdict out := (verdict = true ↔ Q.yes x.x) ∧ Q.output x.x out

/-- `EndStatement.Problem.SolvedBy` counts the output cells as `1 + len + i`, and `output` counts
them as `(len + 1) + i`. -/
theorem output_cons {W : ℕ} (c : ℤ → BitVec W) (n : ℤ) (l : List ℤ) :
    (fun i : ℕ => (c ((1 + l.length + i : ℕ) : ℤ)).toInt) = output c (n :: l).length := by
  funext i
  simp only [output, List.length_cons, Nat.add_comm 1]
  rfl

/-- `SolvesWithin` is `Solves` for the problem `ofEnd Q`, on the instances with `U = n^κ`. -/
theorem solvesWithin_iff {Q : EndStatement.Problem} {κ : ℕ} {P : List Instr} {b : ℕ} {T : ℕ → ℝ} :
    SolvesWithin Q κ P b T ↔ Solves (ofEnd Q) P b (fun x => x.U = x.n ^ κ) fun x => T x.n := by
  constructor
  · intro h x hx bits hbits
    obtain ⟨t, ht, verdict, m, hexec, hyes, hout⟩ :=
      h x.n x.x (hx ▸ x.bounded) bits (by simpa [Admissible] using hbits)
    exact ⟨t, verdict, m, ht, hexec, hyes, output_cons m x.n (Q.input x.x) ▸ hout⟩
  · intro h n x hx W hW
    obtain ⟨t, verdict, c, ht, hrun, hyes, hout⟩ :=
      h ⟨n, n ^ κ, x, hx⟩ rfl W (by simpa [Admissible] using hW)
    exact ⟨t, ht, verdict, c, hrun, hyes, (output_cons c n (Q.input x)).symm ▸ hout⟩

/-- `SolvedInTimeAt` in terms of `Solves`. -/
theorem solvedInTimeAt_iff {Q : EndStatement.Problem} {κ : ℕ} {a : ℝ} {e : ℕ} :
    SolvedInTimeAt Q κ a e ↔ ∃ (P : List Instr) (b : ℕ) (C : ℝ),
      Solves (ofEnd Q) P b (fun x => x.U = x.n ^ κ)
        fun x => C * ((x.n : ℝ) ^ a * Real.log x.n ^ e + 1) := by
  simp only [SolvedInTimeAt, solvesWithin_iff]

/-! ## Monotonicity -/

/-- `Solves` stays true for a larger slope, a smaller set of instances and a larger time bound. -/
theorem Solves.mono {prob : Problem} {P : List Instr} {b b' : ℕ} {dom dom' : prob.Inst → Prop}
    {T T' : prob.Inst → ℝ} (h : Solves prob P b dom T) (hb : b ≤ b') (hdom : ∀ x, dom' x → dom x)
    (hT : ∀ x, dom' x → T x ≤ T' x) : Solves prob P b' dom' T' := by
  intro x hx bits hadm
  obtain ⟨t, verdict, c, ht, he, ha⟩ :=
    h x (hdom x hx) bits (le_trans (Nat.mul_le_mul_right _ hb) hadm)
  exact ⟨t, verdict, c, ht.trans (hT x hx), he, ha⟩

/-! ## Bounds up to a constant -/

/-- A program that solves a problem in time `O(f)` solves it in time `O(f')` if `f = O(f')`. -/
theorem exists_solves_of_dominated {prob : Problem} {dom dom' : prob.Inst → Prop}
    {f f' : prob.Inst → ℝ}
    (h : ∃ (P : List Instr) (b : ℕ) (C : ℝ), Solves prob P b dom fun x => C * f x)
    (hdom : ∀ x, dom' x → dom x) (hf : Dominated dom' f f')
    (hf0 : ∀ x, dom' x → 0 ≤ f x := by intro _ _; positivity) :
    ∃ (P : List Instr) (b : ℕ) (C : ℝ), Solves prob P b dom' fun x => C * f' x := by
  obtain ⟨P, b, C, h⟩ := h
  obtain ⟨K, -, hf⟩ := hf.const_mul_of_nonneg C hf0
  exact ⟨P, b, K, h.mono le_rfl hdom hf⟩

/-! ## Bounds in one size -/

/-- The bound `O(n^a (log n)^e)` may be replaced by a bound `O(n^a' (log n)^e')` that is at least as
large, up to a constant, for all large `n`. -/
theorem SolvedInTimeAt.of_eventually_le {Q : EndStatement.Problem} {κ : ℕ} {a a' C : ℝ} {e e' : ℕ}
    (h : SolvedInTimeAt Q κ a e)
    (hle : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ a * Real.log n ^ e ≤ C * ((n : ℝ) ^ a' * Real.log n ^ e')) :
    SolvedInTimeAt Q κ a' e' := by
  have hall : Dominated (fun _ : ℕ => True) (fun n => (n : ℝ) ^ a * Real.log n ^ e + 1)
      fun n => (n : ℝ) ^ a' * Real.log n ^ e' + 1 :=
    (Dominated.of_eventually_add_one hle fun n => by positivity).add
      (.of_le fun n _ => le_add_of_nonneg_left tac_positivity)
  exact solvedInTimeAt_iff.2 (exists_solves_of_dominated (solvedInTimeAt_iff.1 h) (fun _ hx => hx)
    (hall.comp (fun x : Bounded Q => x.n) fun _ _ => trivial))

/-- A bound `O(n^a (log n)^{O(1)})` is a bound `O(n^a')` for `a < a'`. -/
theorem SolvedInPolylogTime.solvedInTime {Q : EndStatement.Problem} {a a' : ℝ}
    (h : SolvedInPolylogTime Q a) (ha : a < a') : SolvedInTime Q a' 0 := fun κ =>
  let ⟨e, he⟩ := h κ
  he.of_eventually_le (C := 1) <| by
    simpa only [one_mul, pow_zero, mul_one] using eventually_mul_rpow_mul_log_pow_le 1 ha e

end ThreeSumApsp.WordRam