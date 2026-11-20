module

public import HK.Defs

/-!
# Orbit certificates

`Orbit` separates verification of a proposed closed form from induction on the HK trajectory.
`Mode` checks stronger identities on an affine line: all its visited matrices have the same
negative contracting mode. This gives the frozen limits and instability as well as the actual
trajectory. `finite_check` reduces each numerical certificate to scalar arithmetic.
-/

@[expose] public section

namespace HK

/-- Name a direct specialization of a theorem (a term-valued version of `alias`). -/
macro "corollary " n:ident bs:bracketedBinder* " := " p:term : command =>
  `(theorem $n $bs* : type_of% ($p) := $p)

open Filter

scoped notation "Rows" n:arg => (Fin n → Finset (Fin n))
scoped macro "rows![" xs:term,* "]" : term => `((![$xs,*] : Rows _))

/-- Inclusive block of consecutive indices, expanded as an increasing set literal. -/
scoped macro:max l:num "⋯" u:num : term => do
  let xs := (List.range' l.getNat (u.getNat + 1 - l.getNat)).toArray.map Lean.quote
  if xs.isEmpty then `(∅) else `({$[$xs:term],*})

variable {n : ℕ} (m : Model) (r x L v : State n) (y : ℕ → State n) (q : ℝ) (N : ℕ → Rows n)

/-- A candidate trajectory can be checked one row and one step at a time. -/
structure Orbit : Prop where
  init : x = y 0
  rows : ∀ t, neighbors m r (y t) = N t
  next : ∀ t, (weights (N t)).mulVec (y t) = y (t + 1)

/-- Box for the scalar coordinate of a negative, contracting mode. -/
@[hk_data] def Box (t : ℕ) (u : ℝ) := u ∈ Set.Icc q 1 ∧ (if Even t then 0 < u else u < 0)

local notation "line" u:arg => L + u • v

/-- A negative single mode. Each visited table acts in the same way on the entire affine line,
not just at the point visited. This extra information also gives the final value at frozen topology. -/
structure Mode : Prop where
  rate : |q| < 1 ∧ q < 0
  moves : ∃ i, v i ≠ 0
  positive : PositiveRadii r
  init : x = L + v
  rows : ∀ t u, Box q t u → neighbors m r (line u) = N t
  act : ∀ t u, (weights (N t)).mulVec (line u) = line (q * u)

variable {m r x L v y q N}
local notation "X" => traj m r x
local notation "G" => proximityDigraph m r

theorem traj_succ (t : ℕ) : X (t + 1) = step m r (X t) :=
  Function.iterate_succ_apply' ..

theorem graph_iff {y z : State n} : G y = G z ↔
    neighbors m r y = neighbors m r z := by
  simp [proximityDigraph, funext_iff, Finset.ext_iff]

namespace Orbit
variable (h : Orbit m r x y N)
include h

theorem form (t : ℕ) : X t = y t := by
  induction t with
  | zero => exact h.init
  | succ t ih => rw [traj_succ, ih, step, adjMatrix, h.rows, h.next]

theorem table (t : ℕ) : neighbors m r (X t) = N t := by rw [h.form, h.rows]

/-- Consecutive distinct tables rule out finite-time stabilization. For alternating
literal tables the default proof just compares the two parities. -/
theorem changes (diff : ∀ t, N (t + 1) ≠ N t := by
    intro t; simp only [Nat.even_add_one, ← Nat.not_even_iff_odd]; split_ifs <;> decide) (τ : ℕ) :
    ∃ t, τ ≤ t ∧ G (X t) ≠ G (X τ) := by
  refine ⟨τ + 1, by omega, ?_⟩
  simpa only [ne_eq, graph_iff, h.table] using diff τ

end Orbit

theorem Orbit.constant {R} (h : Orbit m r x y fun _ => R) (t : ℕ) : G (X t) = G x :=
  graph_iff.2 ((h.table t).trans (h.table 0).symm)

section
variable (m r) (t : ℕ)
local notation "average" => Matrix.mulVec (adjMatrix m r (y t))

/-- On a convergent tail governed by the current matrix, the frozen limit is the true limit,
and that matrix fixes it. -/
theorem frozen_tail (hy : Converges y L)
    (hs : ∀ s ≥ t, average (y s) = y (s + 1)) :
    fvct m r (y t) = L ∧ average L = L := by
  constructor
  · apply Tendsto.limUnder_eq
    apply (hy.comp (tendsto_add_atTop_nat t)).congr
    intro k; dsimp; symm
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, hs _ (by omega), Nat.succ_add]
  · have hc : Continuous average := by fun_prop
    exact tendsto_nhds_unique_of_eventuallyEq ((hc.tendsto _).comp hy)
      (hy.comp (tendsto_add_atTop_nat 1)) (eventually_atTop.2 ⟨t, hs⟩)

end

/-- A settled agent eventually stays on the same side of its limit. -/
theorem crossing (hc : Converges y L) (i : Fin n)
    (h : ∀ t, ¬ ∀ s ≥ t, y s i < L i ↔ y t i < L i) : Unstable y := by
  constructor
  · intro t hf; exact h t fun s hs => by rw [hf s hs]
  · rintro z t ⟨hz, F, C,-,-,-,cover, hs⟩
    obtain rfl := tendsto_nhds_unique hc hz
    apply h t
    have hi : i ∈ F ∨ i ∈ C := by simp [← Finset.mem_union, cover]
    exact Nat.le_induction Iff.rfl fun s hst ih => by
      grind [hs s hst, hs (s + 1) (by omega)]

theorem refutes_of_unstable (h : Unstable X) (hr : PositiveRadii r)
    (hg : ∀ t, G (X t) = G x) :
    (¬ Conjecture23ForAgents m n) ∧ ¬ Theorem64ivForAgents m n := by
  constructor <;> intro c
  · grind [c r x hr]
  · grind [c r x hr 0 (fun t _ => hg t)]

theorem refute22 (hr : PositiveRadii r)
    (hg : ∀ τ, ∃ t ≥ τ, G (X t) ≠ G (X τ)) :
    ¬ Conjecture22ForAgents m n := by
  contrapose! hg
  exact hg r x hr

theorem power_bounds (hq : |q| < 1 ∧ q < 0) (t : ℕ) : Box q t (q ^ t) := by
  induction t <;>
    simp_all [hk_data, pow_succ, Nat.even_add_one, -Nat.not_even_iff_odd] <;>
    (try split_ifs at *) <;> (repeat' constructor) <;> nlinarith

/-- Normalize a finite table or coordinate calculation to scalar goals. First unfold the
finite-system data and enumerate the coordinates; split a conditional table when needed. Then
compute the finite memberships and sums. What remains is polynomial arithmetic. -/
macro "finite_check" : tactic => `(tactic| (
  try simp only [↓Real.inv_goldenRatio, hk_data, funext_iff] at *
  all_goals intros
  (try split_ifs) <;> norm_num [hk_data, Finset.ext_iff, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]
  all_goals (repeat' constructor) <;> intros <;> first | linarith | nlinarith | grind))

/-- Rational enclosures for the radicals in a numerical example. -/
macro "radical " n:num : tactic => do
  let k := n.getNat.sqrt
  `(tactic|
    obtain ⟨lo, hi⟩ : $(Lean.quote k) < Real.sqrt $n ∧ Real.sqrt $n < $(Lean.quote (k + 1)) := by
      norm_num [Real.lt_sqrt, Real.sqrt_lt'])

/-- Discharge the fields of an explicit finite-system certificate. -/
macro "certify" : tactic => `(tactic| constructor <;> finite_check)

namespace Mode
variable (h : Mode m r x L v q N)
include h

theorem orbit : Orbit m r x (fun t => line (q ^ t)) N where
  init := by simpa using h.init
  rows t := h.rows t _ (power_bounds h.rate t)
  next t := by rw [h.act, pow_succ']

/-- Coordinates of the orbit, optionally presented using a rescaled direction. -/
theorem form (f : ℕ → State n := fun t i => q ^ t * v i)
    (e : ∀ t i, q ^ t * v i = f t i := by simp [mul_assoc, div_eq_mul_inv]) (t : ℕ) :
    X t = fun i => L i + f t i := by
  simp [h.orbit.form, funext_iff, e]

theorem conv : Converges X L := by
  rw [funext h.orbit.form]
  simpa using
    ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one h.rate.1).smul_const v).const_add L

theorem final (t : ℕ) : fvct m r (X t) = L := by
  refine (frozen_tail m r t h.conv ?_).1
  intro s _
  simp_rw [adjMatrix, h.orbit.table, h.orbit.form, h.act, pow_succ']

variable (S : Finset (Fin n))

theorem factor (hv : ∀ i ∈ S, v i ≠ 0 := by finite_check) (t : ℕ) (i : Fin n) (hi : i ∈ S) :
    perStepFactor m r X i t = q := by
  simp [perStepFactor, ↓h.final, h.orbit.form, pow_succ', mul_assoc, hv i hi, h.rate.2.ne]

theorem noFactorLimit (hf : ∀ t i, i ∈ S → perStepFactor m r X i t = q)
    (i : Fin n) (hi : i ∈ S) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ¬ Converges (fun t => perStepFactor m r X i t) ρ := by
  simp [hf _ _ hi, tendsto_const_nhds_iff, (h.rate.2.trans_le hρ).ne]

theorem unstable : Unstable X := by
  obtain ⟨i, hi⟩ := h.moves
  apply crossing h.conv i
  intro t hs
  specialize hs (t + 1) (by omega)
  simp [h.orbit.form, pow_succ', mul_assoc, mul_neg_iff (a := q), h.rate.2, h.rate.2.not_gt] at hs
  grind [mul_ne_zero (pow_ne_zero t h.rate.2.ne) hi]

end Mode

corollary Mode.refutes {R} (h : Mode m r x L v q fun _ => R) :=
  refutes_of_unstable h.unstable h.positive h.orbit.constant

scoped notation "sbcRate" => (-1 / 6 : ℝ)

set_option quotPrecheck false in
/-- Substitute the two geometric sequences into a state formula. -/
scoped notation "powers" a:arg b:arg Y:arg => fun t => beta% Y (a ^ t) (b ^ t)

/-- Check the bounding rectangle for the two powers, then the initial state and averaging identity. -/
macro "check_powers " a:term " and " b:term : tactic => `(tactic| (
  constructor
  case rows =>
    intro t
    have := (power_bounds (q := $a) (by finite_check) t).1
    have : ($b : ℝ) ^ t ∈ Set.Icc 0 1 := by constructor <;> bound
    finite_check
  all_goals simp only [pow_zero, pow_succ] <;> finite_check))

theorem faster_power (a b : ℝ) {t : ℕ} (ht : 1 ≤ t) (h : |a| < b := by finite_check) :
    a ^ t < b ^ t := by
  refine (le_abs_self _).trans_lt ?_
  rw [abs_pow]; gcongr

end HK
