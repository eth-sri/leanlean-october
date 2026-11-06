/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Lang.RowMajor
import ThreeSumApsp.Lang.Tactics
import ThreeSumApsp.Lang.Tasks
import ThreeSumApsp.Lang.ToMachine
import ThreeSumApsp.Machine.Realized
import ThreeSumApsp.Util.Flag

/-!
# From a solver of a task to a program for the layout of the end statement

A solver gets its size, the bound on the numbers and its addresses as arguments.  A problem of the
end statement has a fixed layout: cell 0 holds the size n, then comes the input, then the output;
the bound U = n^κ is not in the memory.  For every κ one more procedure, `topBody`, is appended to
the program of the solver.  It reads n.  At size 0 it answers at once.  Otherwise it forms U = n^κ
by κ multiplications and n², computes the addresses, calls the solver, and returns the result of
the solver (for a decision problem) or 1.

`Wrap` collects what has to be said about a problem and a task for this to work.  `Wrap.body_ends`
and `Wrap.body_ends_zero` follow the procedure through its text, `Wrap.small` bounds the word size,
the memory and the depth that the run needs by a polynomial in n, and `Wrap.realized` is the
conclusion: if the task is solved in time T, then the problem is solved on the word RAM within a
constant times T.
-/


namespace Light

open ThreeSumApsp.WordRam

variable {lim : Limits} {P : Program} {d : ℕ}

/-- Local 2 is multiplied κ times by local 1. -/
def powStmt : ℕ → Stmt
  | 0 => .skip
  | κ + 1 => powStmt κ ;; .set 2 (v 2 *' v 1)

/-- The outermost procedure.  Local 1 is n, the content of cell 0.  At size 0 the result is 0 for a
decision problem and 1 for a problem with an output.  Otherwise local 2 is U = n^κ, local 3 is n²,
and the arguments of the solver are expressions in these three; for a problem with an output the
result of the solver is replaced by 1. -/
def topBody (κ p : ℕ) (args : List Expr) (dec : Bool) : Stmt :=
  .set 1 (M (k 0)) ;;
  Stmt.iteNe (v 1) (k 0)
    (.set 2 (k 1) ;;
    powStmt κ ;;
    .set 3 (v 1 *' v 1) ;;
    .call p args 0 ;;
    (if dec then .skip else .set 0 (k 1)))
    (.set 0 (k (if dec then 0 else 1)))

variable {n : ℕ}

/-- The loop that is written out κ times turns U = 1 into U = n^κ. -/
theorem pow_spec (hn : 1 ≤ n) (a : ℤ) (μ : ℕ → ℤ) : ∀ κ : ℕ, ((n ^ κ : ℕ) : ℤ) ≤ lim.word →
    Ends lim P d (powStmt κ) ⟨frame [a, n, 1], μ⟩ (4 * κ) (· = ⟨frame [a, n, ((n ^ κ : ℕ) : ℤ)], μ⟩)
  | 0, _ => Ends.skip (by simp)
  | κ + 1, hw => by
    have hle : ((n ^ κ : ℕ) : ℤ) ≤ ((n ^ (κ + 1) : ℕ) : ℤ) := by
      exact_mod_cast Nat.pow_le_pow_right hn (by omega)
    have hval : ((n ^ κ : ℕ) : ℤ) * n = ((n ^ (κ + 1) : ℕ) : ℤ) := by
      push_cast
      ring
    unfold powStmt
    refine Ends.next (4 * κ) ((pow_spec hn a μ κ (hle.trans hw)).mono le_rfl ?_)
    rintro _ rfl
    -- U := U * n
    refine Ends.setTo ((n ^ (κ + 1) : ℕ) : ℤ) rfl ⟨?_, ?_⟩
    · light_norm
      change |((n ^ κ : ℕ) : ℤ) * n| ≤ lim.word
      rw [hval, abs_of_nonneg (Int.natCast_nonneg _)]
      exact hw
    · exact hval

/-- The arguments n, U and four addresses 1, 1 + n², 1 + 2n², 1 + c n² are safe. -/
theorem safe_fourAddresses {c : ℕ} (hc : c ≤ 4) {lim : Limits} {σ : State}
    (h3 : σ.loc 3 = ((n * n : ℕ) : ℤ)) (hw : ((8 * (n * n + 1) : ℕ) : ℤ) ≤ lim.word) :
    ∀ e ∈ [v 1, v 2, k 1, k 1 +' v 3, k 1 +' k 2 *' v 3, k 1 +' k c *' v 3], e.Safe lim σ := by
  have hcn : c * (n * n) ≤ 4 * (n * n) :=
    by simp_all [mul_le_mul_of_nonneg_right]
  simp [Expr.Safe, Expr.val, Op.eval, true_and, Nat.cast_ofNat]
  refine ⟨by omega, by grind,
    by grind,
    by omega, by grind, by grind⟩

/-- The verdict that belongs to the result of a decision procedure. -/
theorem verdictOf_flag (p : Prop) : verdictOf true (ThreeSumApsp.flag p) = true ↔ p := by
  by_cases h : p
  · rw [ThreeSumApsp.flag_of h]
    aesop
  · rw [ThreeSumApsp.flag_of_not h]
    aesop

/-! ## The problems of `EndStatement` -/

section OfEnd

variable {Q : EndStatement.Problem} (x : Bounded Q)


/-- All cells of the input are within the size and the bound. -/
theorem ofEnd_input_le : ∀ a ∈ (ofEnd Q).input x, |a| ≤ ((x.n + x.U + 1 : ℕ) : ℤ) := by
  intro a ha
  rcases List.mem_cons.1 ha with rfl | ha
  · grind
  · have := Bounded.abs_le ha
    omega

/-- Cell 0 may be read. -/
theorem safe_cell0 {lim : Limits} {σ : State} (h0 : 0 ≤ lim.word) (h1 : 1 ≤ lim.space) :
    (M (k 0)).Safe lim σ := by
  light_norm
  exact ⟨h0, le_rfl, by omega⟩

end OfEnd

/-! ## Polynomials in the size -/

/-- A polynomial in `n` and `U = n^κ` is a polynomial in `n`. -/
theorem polyBound_pow_le (s k κ n : ℕ) {r : ℕ} (hr : (κ + 1) * k ≤ r) :
    polyBound s k [n, n ^ κ] ≤ 2 ^ (s + k) * (n + 1) ^ r := by
  have hpos : 1 ≤ n + 1 := by omega
  have hU : n ^ κ + 1 ≤ 2 * (n + 1) ^ κ := by
    have h1 : n ^ κ ≤ (n + 1) ^ κ := by simp_all [Nat.pow_le_pow_left]
    grind
  unfold polyBound
  simp [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  calc 2 ^ s * ((n + 1) * (n ^ κ + 1)) ^ k
      ≤ 2 ^ s * ((n + 1) * (2 * (n + 1) ^ κ)) ^ k :=
        by simp_all [Nat.pow_le_pow_left]
    _ = 2 ^ (s + k) * (n + 1) ^ ((κ + 1) * k) := by
        grind [mul_pow, pow_mul]
    _ ≤ 2 ^ (s + k) * (n + 1) ^ r := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hpos hr)

/-- What connects a problem in the layout of the end statement with a task. -/
structure Wrap (Q : EndStatement.Problem) (task : Task) (dec : Bool) where
  /-- The input and the output take at most cst (n² + 1) cells. -/
  cst : ℕ := 8
  cst_pos : 1 ≤ cst := by omega
  /-- The arguments of the solver, the free pointer last, as expressions in the locals 1 (n), 2 (U)
  and 3 (n²). -/
  args : List Expr
  /-- The instance of the task. -/
  inst : Bounded Q → task.Inst
  /-- The free pointer: the first cell after the output. -/
  fr : Bounded Q → ℕ
  size_eq : ∀ x : Bounded Q, task.size (inst x) = x.n
  bound_eq : ∀ x : Bounded Q, task.bound (inst x) = x.U
  fr_pos : ∀ x : Bounded Q, 1 ≤ fr x
  fr_le : ∀ x : Bounded Q, fr x ≤ cst * (x.n * x.n + 1)
  /-- The expressions have the values that the solver expects. -/
  vals : ∀ (x : Bounded Q) (σ : State), σ.loc 1 = x.n → σ.loc 2 = x.U →
    σ.loc 3 = ((x.n * x.n : ℕ) : ℤ) → args.map (·.val σ) = task.args (inst x) ++ [(fr x : ℤ)]
  /-- They may be evaluated as soon as the addresses of the input and the output fit in a word. -/
  safe : ∀ (x : Bounded Q) (lim : Limits) (σ : State), σ.loc 1 = x.n → σ.loc 2 = x.U →
    σ.loc 3 = ((x.n * x.n : ℕ) : ℤ) → ((cst * (x.n * x.n + 1) : ℕ) : ℤ) ≤ lim.word →
    ∀ e ∈ args, e.Safe lim σ
  /-- At size 0 it is right to reject, for a decision problem, and to accept, whatever the output
  cells hold, for a problem with an output. -/
  zero : ∀ x : Bounded Q, x.n = 0 → ∀ out, (ofEnd Q).IsAnswer x (!dec) out
  /-- The input meets the precondition of the task. -/
  pre : ∀ x : Bounded Q, 1 ≤ x.n → 1 ≤ x.U →
    task.Pre (inst x) (memOf ((ofEnd Q).input x)) (fr x)
  /-- What the task promises is a right answer. -/
  post : ∀ (x : Bounded Q) r μ', 1 ≤ x.n →
    task.Post (inst x) (memOf ((ofEnd Q).input x)) (fr x) r μ' →
    (ofEnd Q).IsAnswer x (verdictOf dec (if dec then r else 1)) fun i =>
      μ' (((ofEnd Q).input x).length + i)

namespace Wrap

variable {Q : EndStatement.Problem} {task : Task} {dec : Bool}

/-- The steps of the outermost procedure, beside those of the solver. -/
def bodySteps (w : Wrap Q task dec) (κ : ℕ) : ℕ := 4 * κ + (w.args.map Expr.cost).sum + 20

/-- The steps of the outermost procedure and of its call, beside those of the solver. -/
def extra (w : Wrap Q task dec) (κ : ℕ) : ℕ := w.bodySteps κ + 4

/-- The limits of the run on an instance. -/
def limits (w : Wrap Q task dec) (need : ℕ → ℕ → Need) (x : Bounded Q) : Limits :=
  ⟨((need x.n x.U).word + (w.fr x + (need x.n x.U).cells) + w.cst * (x.n * x.n + 1) +
      x.U + x.n + 1 : ℕ), w.fr x + (need x.n x.U).cells, (need x.n x.U).depth + 2⟩

/-- What the run asks of the limits. -/
structure Room (w : Wrap Q task dec) (need : ℕ → ℕ → Need) (x : Bounded Q) (lim : Limits) :
    Prop where
  /-- The addresses of the input and the output fit in a word. -/
  cells : ((w.cst * (x.n * x.n + 1) : ℕ) : ℤ) ≤ lim.word
  /-- The bound on the numbers, and 1, fit in a word. -/
  bound : ((x.U + 1 : ℕ) : ℤ) ≤ lim.word
  space : 1 ≤ lim.space
  depth : 2 ≤ lim.depth
  /-- The solver, called at depth 2 with the free pointer behind the output, has what it needs. -/
  solver : (need x.n x.U).Ok lim (w.fr x) 2

variable (w : Wrap Q task dec)

/-- The limits of the run leave that room. -/
theorem room (need : ℕ → ℕ → Need) (x : Bounded Q) :
    w.Room need x (w.limits need x) := by
  have hfr := w.fr_pos x
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩ <;> simp only [limits] <;> omega

/-- The final state holds a right answer to the instance. -/
abbrev Answered (x : Bounded Q) (dec : Bool) (σ : State) : Prop :=
  (ofEnd Q).IsAnswer x (verdictOf dec (σ.loc 0)) fun i => σ.mem (((ofEnd Q).input x).length + i)

variable {p : ℕ} {Tn : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Need}

/-- The run of the outermost procedure on an instance of size at least 1. -/
theorem body_ends {P : Program}     (hsol : Solves task P p Tn need) (κ : ℕ) (x : Bounded Q) (hn : 1 ≤ x.n) (hU : x.U = x.n ^ κ)
    {lim : Limits} (hroom : w.Room need x lim) :
    Ends lim (P ++ [topBody κ p w.args dec]) 1 (topBody κ p w.args dec)
      ⟨frame [0, 0], memOf ((ofEnd Q).input x)⟩ (Tn x.n x.U + w.bodySteps κ) (Answered x dec) := by
  have hbound := hroom.bound
  have hcells := hroom.cells
  have hdepth := hroom.depth
  have hcst : x.n * x.n + 1 ≤ w.cst * (x.n * x.n + 1) := Nat.le_mul_of_pos_left _ w.cst_pos
  have hU1 : 1 ≤ x.U := by grind
  unfold topBody bodySteps
  -- n := mem[0]
  refine Ends.setToThen x.n ?_ ⟨safe_cell0 (by omega) hroom.space, by rfl⟩
  -- if n ≠ 0
  refine Ends.iteLast (by aesop) fun _ => ?_
  -- U := 1
  light_set 1
  -- U := U * n, κ times
  refine Ends.next _ ((pow_spec hn 0 _ κ (by omega)).mono le_rfl ?_)
  rintro _ rfl
  rw [← hU]
  -- local 3 := n * n
  light_set (x.n * x.n)
  -- result := solver(…)
  refine Ends.callToThen (hsol.meets _ _ _ (w.pre x hn hU1)
    (by rw [w.size_eq, w.bound_eq]; exact hroom.solver)) ?_
    ⟨w.safe x lim _ rfl rfl rfl hcells, w.vals x _ rfl rfl rfl⟩ (by omega)
    (by rw [w.size_eq, w.bound_eq]; light_time)
  intro r μ' hpost
  rw [w.size_eq, w.bound_eq]
  have hanswer := w.post x r μ' hn hpost
  -- for a problem with an output: result := 1
  cases dec
  · exact Ends.set (by light_norm; omega) (by light_time) (by assumption)
  · exact Ends.skip (by assumption)

/-- The run of the outermost procedure on an instance of size 0. -/
theorem body_ends_zero (P : Program) (p κ : ℕ) (x : Bounded Q) (hn : x.n = 0)
    {lim : Limits} (hroom : w.Room need x lim) :
    Ends lim (P ++ [topBody κ p w.args dec]) 1 (topBody κ p w.args dec)
      ⟨frame [0, 0], memOf ((ofEnd Q).input x)⟩ 9 (Answered x dec) := by
  have hbound := hroom.bound
  refine Ends.setToThen x.n ?_ ⟨safe_cell0 (by omega) hroom.space, by rfl⟩
  -- if n ≠ 0 … else result := 0 or 1
  refine Ends.iteLast (fun _ => ?_) (by simp_all)
  cases dec <;>
    exact Ends.set (by simp; omega) (by light_time) (by simpa [Answered, verdictOf] using w.zero x hn _)

/-- The outermost call, from the run of its procedure. -/
theorem ends_of_body {P : Program} {κ T : ℕ} (x : Bounded Q)
   
    (h : Ends (w.limits need x) (P ++ [topBody κ p w.args dec]) 1 (topBody κ p w.args dec)
      ⟨frame [0, 0], memOf ((ofEnd Q).input x)⟩ T (Answered x dec)) :
    Ends (w.limits need x) (P ++ [topBody κ p w.args dec]) 0 (mainStmt P.length)
      ⟨frame [0, 0, 0], memOf ((ofEnd Q).input x)⟩ (T + 4) (Answered x dec) :=
  Ends.call T (by simp) (by simp) (by grind [limits])
    (h.mono le_rfl fun _ hσ => by assumption) (by light_time)

/-- The limits are polynomial in the size. -/
theorem small (hpoly : PolyNeed need) (κ : ℕ) :
    ∃ s k : ℕ, ∀ x : Bounded Q, x.U = x.n ^ κ → Small s k [x.n] (w.limits need x) := by
  obtain ⟨s, k, hpoly⟩ := hpoly
  obtain ⟨r, hr⟩ : ∃ r, r = (κ + 1) * k + κ + 2 := by simp
  refine ⟨s + k + 5 + w.cst.size, r, fun x hU => ?_⟩
  obtain ⟨hword, hcells, hdepth⟩ := hpoly x.n x.U
  have hpos : 1 ≤ x.n + 1 := by omega
  have hneed := polyBound_pow_le s k κ x.n (r := r) (by omega)
  have hsquare : x.n * x.n + 1 ≤ (x.n + 1) ^ r :=
    (by nlinarith : x.n * x.n + 1 ≤ (x.n + 1) ^ 2).trans (by simp_all [Nat.pow_le_pow_right])
  have hbound : x.n ^ κ ≤ (x.n + 1) ^ r :=
    (Nat.pow_le_pow_left (by omega) κ).trans (Nat.pow_le_pow_right hpos (by omega))
  have hsize : x.n + 1 ≤ (x.n + 1) ^ r := by grind [Nat.le_self_pow]
  have hfr := w.fr_le x
  rw [← hU] at hneed hbound
  -- `X` bounds the parts that do not come from the solver, `Z ≥ X` those that do
  have hXZ : (x.n + 1) ^ r ≤ 2 ^ (s + k) * (x.n + 1) ^ r := Nat.le_mul_of_pos_left _ (by positivity)
  have hgoal : polyBound (s + k + 5 + Nat.size w.cst) r [x.n] =
      32 * (2 ^ Nat.size w.cst * (2 ^ (s + k) * (x.n + 1) ^ r)) := by
    unfold polyBound
    grind
  generalize 2 ^ (s + k) * (x.n + 1) ^ r = Z at *
  have hcst :=
    Nat.mul_le_mul (Nat.lt_size_self w.cst).le (hsquare.trans hXZ)
  have hZY : Z ≤ 2 ^ Nat.size w.cst * Z := Nat.le_mul_of_pos_left _ Nat.one_le_two_pow
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [limits, hgoal] <;> omega

variable {T : ℕ → ℝ → ℝ}

/-- The compiled program is run within these limits: what the interface to the machine asks for. -/
theorem topSolves {P : Program}     (hpoly : PolyNeed need) (hsol : Solves task P p Tn need)
    (hT : ∀ (n U : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ U → (U : ℝ) ≤ u → (Tn n U : ℝ) ≤ T n u) (κ : ℕ) :
    ∃ s k : ℕ, ProgramSolves (ofEnd Q) (P ++ [topBody κ p w.args dec]) P.length dec s k
      (fun x => x.U = x.n ^ κ) fun x => max (T x.n x.U) 0 + w.extra κ := by
  obtain ⟨s, k, hsmall⟩ := w.small hpoly κ
  refine ⟨s, k, fun x hU => ?_⟩
  have hinput : ∀ a ∈ (ofEnd Q).input x, |a| ≤ (w.limits need x).word := fun a ha =>
    (ofEnd_input_le x a ha).trans (by grind [limits])
  rcases x.n.eq_zero_or_pos with hn | hn
  · obtain ⟨σ', c, hrun, hc, hanswer⟩ :=
      w.ends_of_body x (w.body_ends_zero P p κ x hn (w.room need x))
    have hc' : (c : ℝ) ≤ w.extra κ := by exact_mod_cast by grind [extra, bodySteps]
    exact ⟨w.limits need x, σ', c, hrun, by grind, hinput,
      by grind, hanswer⟩
  · obtain ⟨σ', c, hrun, hc, hanswer⟩ :=
      w.ends_of_body x (w.body_ends hsol κ x hn hU (w.room need x))
    have hc' : c ≤ (Tn x.n x.U : ℝ) + w.extra κ := by
      exact_mod_cast by assumption
    have hTn := hT x.n x.U x.U hn (by grind) le_rfl
    exact ⟨w.limits need x, σ', c, hrun, by grind, hinput,
      by simp_all, hanswer⟩

/-- **If the task is solved in time T, the problem is solved on the word RAM within a constant times
T.** -/
theorem realized (w : Wrap Q task dec) (h : SolvedIn task T) : Realized Q T := by
  obtain ⟨P, p, Tn, need, hpoly, hsol, hT⟩ := h
  intro κ
  obtain ⟨s, k, htop⟩ := w.topSolves hpoly hsol hT κ
  refine ⟨_, _, timeConst (P ++ [topBody κ p w.args dec]) dec * (w.extra κ + 1),
    by positivity,
    (solves_of_programSolves htop (r := 1) fun x => by simp).mono le_rfl (by omega)
      fun x _ => ?_⟩
  -- `K (T + E) + K ≤ K (E + 1) T + K (E + 1)` for `K, E, T ≥ 0`
  have hT0 : 0 ≤ max (T x.n x.U) 0 := by simp
  have hK : 0 ≤ (timeConst (P ++ [topBody κ p w.args dec]) dec : ℝ) := by positivity
  have hE : 0 ≤ (w.extra κ : ℝ) := by positivity
  nlinarith [mul_nonneg (mul_nonneg hK hE) hT0]
