/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Lang.Calls
public import ThreeSumApsp.Lang.Lib.Seg
public import ThreeSumApsp.Lang.WordSize

/-!
# Problems, solvers, and the interpretation of "is solved in time T" in the light language

A *task* is a problem together with a calling convention: which arguments a procedure gets, what the
memory holds when it is called, and what the result and the memory have to be when it returns.
`Solves task P p T need` says that procedure number `p` of the program `P` solves the task within
`T` steps, if the limits of the run allow for `need`.  A reduction of the paper is a *host*: a
procedure that calls an arbitrary solver of another task.

Conventions.

* A solver gets sizes, a bound `U` on the absolute values of the numbers, the addresses of its
  arrays, and as last argument the free pointer `fr`.  All inputs and outputs lie below `fr`.  The
  solver may write its output segments and any cell from `fr` on, and no other cell.  Nothing is
  assumed about the cells from `fr` on, so a solver can be called again and again.
* A solver has to be correct for every valid bound `U` that it is given.
* A solver is a pair of a program and a procedure number.  What is proved about it holds for every
  program that begins with this program, so a host appends its own procedures.

A `Task` is a problem whose time and need depend on a size and a bound.  `TaskN` and `SolvesN` are
the same notions with a list of parameters.
-/

@[expose] public section

namespace Light



/-! ## Limits -/

/-- What a run needs: the largest absolute value it forms, the number of cells it uses from the free
pointer on, and the number of levels of calls below the procedure. -/
structure Need where
  (word cells depth : ℕ)

/-- Resource requirements as a function of size and entry bound. -/
abbrev NeedFn := Nat → Nat → Need
/-- Resource requirements as a function of a call's size arguments. -/
abbrev InputNeed := List Nat → Need

/-- The limits allow for the need of a procedure that is called at depth `d` with the free pointer
`fr`.  An address always fits in a word. -/
structure Need.Ok (r : Need) (lim : Limits) (fr d : ℕ) : Prop where
  word : (r.word : ℤ) ≤ lim.word
  cells : fr + r.cells ≤ lim.space
  space : (lim.space : ℤ) ≤ lim.word
  depth : d + r.depth ≤ lim.depth

/-- A smaller need is allowed for if a larger one is, also with a larger free pointer and at a
larger depth if the sums are not larger. -/
theorem Need.Ok.mono {r r' : Need} {lim} {fr fr' d d'} (h : r.Ok lim fr d)
    (hw : r'.word ≤ r.word) (hc : fr' + r'.cells ≤ fr + r.cells)
    (hd : d' + r'.depth ≤ d + r.depth) : r'.Ok lim fr' d' :=
  ⟨le_trans (mod_cast hw) h.word, hc.trans h.cells, h.space, hd.trans h.depth⟩

/-- A need that depends on a size and a bound is polynomially bounded in the two: by
`2^s ((n + 1) (U + 1))^k`. -/
def PolyNeed (need : Light.NeedFn) :=
  ∃ s k : ℕ, ∀ n U , (need n U).word ≤ polyBound s k [n, U] ∧ (need n U).cells ≤
    polyBound s k [n, U] ∧
    (need n U).depth ≤ polyBound s k [n, U]

/-! ## Specifications of single routines -/

/-! ## Tasks and solvers -/

/-- A problem with a calling convention. -/
structure Task : Type 1 where
  /-- The instances, as they lie in the memory: sizes, bound, addresses, contents. -/
  Inst : Type
  /-- The size of an instance. -/
  size : Inst → ℕ
  /-- The bound on the absolute values of its numbers that is handed to the solver. -/
  bound : Inst → ℕ
  /-- The arguments of the call, without the free pointer, which comes last. -/
  args : Inst → List ℤ
  /-- The instance is valid, and it lies in the memory below the free pointer. -/
  Pre : Inst → Light.Memory → ℕ → Prop
  /-- The result and the final memory are right.  (That the cells below the free pointer are
  otherwise unchanged is part of this.) -/
  Post : Inst → Light.Memory → ℕ → ℤ → Light.Memory → Prop

/-- **Procedure `p` of the program `P` solves the task** within `T (size) (bound)` steps, whenever
the limits allow for `need (size) (bound)`; and so it does in every program that begins with `P`. -/
def Solves (task : Task) P (p : ℕ) (T : Light.SolverTime) (need : Light.NeedFn) :=
  ∃ body, P[p]? = some body ∧
    ∀ (R : Program) (lim : Limits) (d : ℕ) (x : task.Inst) (μ : Light.Memory) (fr : ℕ), task.Pre x μ fr →
      (need (task.size x) (task.bound x)).Ok lim fr d →
      Ends lim (P ++ R) d body ⟨frame (task.args x ++ [(fr : ℤ)]), μ⟩
        (T (task.size x) (task.bound x))
        fun σ' => task.Post x μ fr (σ'.loc 0) σ'.mem

/-- A solver stays a solver when procedures are appended to its program. -/
theorem Solves.append {task} {P} {p} {T} {need}
    (h : Solves task P p T need) R : Solves task (P ++ R) p T need := by
  grind [Light.Solves]

/-- **A solver meets the specification that its task prescribes**, in every program that begins with
its program. -/
theorem Solves.meets {task} {P₀} {p} {T₀} {need}
    (h : Solves task P₀ p T₀ need) R {lim} {d} x {μ}
     fr (hpre : task.Pre x μ fr) (hok : (need (task.size x) (task.bound x)).Ok lim fr d) :
    Meets lim (P₀ ++ R) p d (task.args x ++ [(fr : ℤ)]) μ (T₀ (task.size x) (task.bound x))
      (task.Post x μ fr) := by
  obtain ⟨body, hp, hb⟩ := h
  exact ⟨body, getElem?_append_of_eq_some hp R, hb R lim d x μ fr hpre hok⟩

/-- "The task is solved in time `T`", for a real-valued `T` whose second argument is an upper bound
on the numbers: some solver with a polynomially bounded need takes at most `T n u` steps on every
instance of size `n ≥ 1` with a bound `1 ≤ U ≤ u`. -/
def SolvedIn (task : Task) (T : ℕ → ℝ → ℝ) : Prop :=
  ∃ (P : Program) (p : ℕ) (Tn : Light.SolverTime) (need : Light.NeedFn), PolyNeed need ∧
    Solves task P p Tn need ∧
    ∀ (n U : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ U → U ≤ u → Tn n U ≤ T n u

/-- A larger bound on the running time is still a bound on the running time. -/
theorem SolvedIn.mono {task} {T T'} (h : SolvedIn task T)
    (hT : ∀ n u, 1 ≤ n → 1 ≤ u → T n u ≤ T' n u) : SolvedIn task T' := by
  obtain ⟨P, p, Tn, need, h1, h2, h3⟩ := h
  refine ⟨P, p, Tn, need, h1, h2, fun n U u hn hU hu => (h3 n U u hn hU hu).trans (hT n u hn ?_)⟩
  exact le_trans (mod_cast hU) hu

/-- The largest time `Tn n U` for a bound `U ≤ u`.  A program has a natural number as the bound on
its numbers, and a claim on running times a real number. -/
noncomputable def timeUpTo (Tn : Light.SolverTime) (n : ℕ) (u : ℝ) : ℝ :=
  ((Finset.range (⌊u⌋₊ + 1)).sup (Tn n) : ℕ)

theorem le_timeUpTo Tn n {U : ℕ} {u} (hu : (U : ℝ) ≤ u) :
    (Tn n U : ℝ) ≤ timeUpTo Tn n u :=
  Nat.cast_le.2 (Finset.le_sup (f := Tn n)
    (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor hu))))

/-- What bounds the time for every natural number `U ≤ u` bounds `timeUpTo`.  For a negative `u`
there is still `U = 0`. -/
theorem timeUpTo_le {Tn} {n} {u B}
    (h : ∀ U : ℕ, (U : ℝ) ≤ max u 0 → (Tn n U : ℝ) ≤ B) : timeUpTo Tn n u ≤ B := by
  obtain ⟨U, hU, hsup⟩ := Finset.exists_mem_eq_sup (Finset.range (⌊u⌋₊ + 1))
    ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩ (Tn n)
  rw [timeUpTo, hsup]
  refine h U ((Nat.cast_le.2 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hU))).trans ?_)
  rcases le_total 0 u with hu | hu
  · grind [Nat.floor_le]
  · ram_arith

/-- A solver with a polynomially bounded need solves its task in its own time. -/
theorem Solves.solvedIn {task} {P} {p} {Tn} {need}
    (hs : Solves task P p Tn need) (hp : PolyNeed need) : SolvedIn task (timeUpTo Tn) :=
  ⟨P, p, Tn, need, hp, hs, fun n _ _ _ _ hu => le_timeUpTo Tn n hu⟩

/-! ## Hosts -/

/-- A host from the task `lower` to the task `upper`: from every solver of `lower` it makes a solver
of `upper`, by appending procedures, whose time and need are given functions of those of the solver,
and whose need stays polynomially bounded. -/
def IsHost lower upper (time : Light.SolverTime → Light.SolverTime)
    (need : Light.NeedFn → Light.NeedFn) :=
  (∀ (P : Program) (p : ℕ) (T : Light.SolverTime) (r : Light.NeedFn), Solves lower P p T r →
    ∃ (R : Program) (p' : ℕ), Solves upper (P ++ R) p' (time T) (need r)) ∧
  ∀ r , PolyNeed r → PolyNeed (need r)

/-- From a host to a transfer of running times.  What remains is arithmetic: a bound for the host's
time function, given a bound for the solver's. -/
theorem IsHost.solvedIn {lower upper} {time}
    {need} (h : IsHost lower upper time need) {T T'}
    (hs : SolvedIn lower T)
    (hb : ∀ Tn , (∀ (n U : ℕ) u, 1 ≤ n → 1 ≤ U → (U : ℝ) ≤ u → (Tn n U : ℝ) ≤
    T n u) → ∀ (n U : ℕ) u, 1 ≤ n → 1 ≤ U → (U : ℝ) ≤ u → (time Tn n U : ℝ) ≤ T' n u) :
    SolvedIn upper T' := by
  grind [Light.SolvedIn, Light.IsHost]

/-! ## Tasks with a list of parameters -/

/-- A problem with a calling convention and a list of parameters. -/
structure TaskN : Type 1 where
  /-- The instances, as they lie in the memory. -/
  Inst : Type
  /-- The parameters on which time and need depend. -/
  pars : Inst → List ℕ
  /-- The arguments of the call, without the free pointer, which comes last. -/
  args : Inst → List ℤ
  /-- The instance is valid, and it lies in the memory below the free pointer. -/
  Pre : Inst → Light.Memory → ℕ → Prop
  /-- The result and the final memory are right. -/
  Post : Inst → Light.Memory → ℕ → ℤ → Light.Memory → Prop

/-- Procedure `p` of the program `P` solves the task within `T pars` steps, whenever the limits
allow for `need pars`; and so it does in every program that begins with `P`. -/
def SolvesN (task : TaskN) P (p : ℕ) (T : Light.InputTime) (need : Light.InputNeed) :=
  ∃ body, P[p]? = some body ∧
    ∀ (R : Program) (lim : Limits) (d : ℕ) (x : task.Inst) (μ : Light.Memory) (fr : ℕ), task.Pre x μ fr →
      (need (task.pars x)).Ok lim fr d →
      Ends lim (P ++ R) d body ⟨frame (task.args x ++ [(fr : ℤ)]), μ⟩ (T (task.pars x))
        fun σ' => task.Post x μ fr (σ'.loc 0) σ'.mem

/-- A solver stays a solver when procedures are appended to its program. -/
theorem SolvesN.append {task} {P} {p} {T} {need}
    (h : SolvesN task P p T need) R : SolvesN task (P ++ R) p T need := by
  grind [Light.SolvesN]

/-- A solver meets the specification of its task, at the depth d at which it runs. -/
theorem SolvesN.meets {task} {P₀} {p} {T₀}
    {need} (h : SolvesN task P₀ p T₀ need) R {lim} {d}
     x {μ} {fr} (hpre : task.Pre x μ fr)
    (hok : (need (task.pars x)).Ok lim fr d) :
    Meets lim (P₀ ++ R) p d (task.args x ++ [(fr : ℤ)]) μ (T₀ (task.pars x))
      (task.Post x μ fr) := by
  obtain ⟨body, hp, hb⟩ := h
  exact ⟨body, getElem?_append_of_eq_some hp R, hb R lim d x μ fr hpre hok⟩

/-- A need that is polynomially bounded in the parameters. -/
def PolyNeedN (need : Light.InputNeed) :=
  ∃ s k : ℕ, ∀ ps , (need ps).word ≤ polyBound s k ps ∧ (need ps).cells ≤ polyBound s k ps ∧
    (need ps).depth ≤ polyBound s k ps

end Light
