module

public import Chazelle.MacT
public import Chazelle.Core.Lemma41Cover

namespace Chazelle
namespace Programs
open Machine Machine.Stmt
@[expose] public section
section spec
variable {P : Polygon} {W : ℕ}
variable {c : Config} {Q : Config → ℕ → Prop} {i : Instr} {a b : ℕ} {t e : Stmt} {s : Stmt}
/-- The empty block: the postcondition holds now, at cost `0`. -/
theorem spec_nil (hw : WordsBounded W c) (hQ : Q c 0) :
    ∃ c' k, Exec P W zttgw c c' k ∧ Q c' k :=
  ⟨c, 0, Exec.block_nil hw, hQ⟩

/-- One instruction of a block: run it (rule `h₁`, giving the explicit next configuration
`c₁`), then continue with the rest at cost `k + 1`. -/
theorem spec_step {l : List Instr} {c c₁ : Config} {Q : Config → ℕ → Prop}
    (h₁ : Exec P W ztbgj c c₁ 1)
    (h₂ : WordsBounded W c₁ → ∃ c' k, Exec P W ztgfk c₁ c' k ∧ Q c' zts) :
    ∃ c' k, Exec P W ztoyd c c' k ∧ Q c' k := by
  obtain ⟨c', k, e, q⟩ := h₂ h₁.wb_right
  exact ⟨c', k + 1, Exec.block_cons h₁ e, q⟩

/-- A single instruction statement. -/
theorem spec_instr {c c₁ : Config} {Q : Config → ℕ → Prop}
    (h₁ : Exec P W ztbgj c c₁ 1) (hQ : WordsBounded W c₁ → Q c₁ 1) :
    ∃ c' k, Exec P W ztbgj c c' k ∧ Q c' k :=
  ⟨c₁, 1, h₁, hQ h₁.wb_right⟩

/-- `skip`. -/
theorem spec_skip (hw : WordsBounded W c) (hQ : Q c 0) :
    ∃ c' k, Exec P W .skip c c' k ∧ Q c' k :=
  ⟨c, 0, .skip hw, hQ⟩

/-- Sequencing: run `s`, then `t` from where `s` stopped; costs add. -/
theorem spec_seq {s t : Stmt} {c : Config} {Q : Config → ℕ → Prop}
    (h : ∃ c₁ k₁, Exec P W s c c₁ k₁ ∧ ∃ c' k₂, Exec P W t c₁ c' k₂ ∧ Q c' ztbct) :
    ∃ c' k, Exec P W ztfmm c c' k ∧ Q c' k := by
  obtain ⟨c₁, k₁, e₁, c', k₂, e₂, q⟩ := h
  exact ⟨c', k₁ + k₂, .seq e₁ e₂, q⟩

/-- `ifLtN`, test true: cost `k + 1`. -/
theorem spec_ifLtN_true {c : Config} {Q : Config → ℕ → Prop}
    (ht : c.nreg a < c.nreg b) (h : ∃ c' k, Exec P W t c c' k ∧ Q c' zts) :
    ∃ c' k, Exec P W ztva c c' k ∧ Q c' k := by
  tauto

/-- `ifLtN`, test false: cost `k + 2`. -/
theorem spec_ifLtN_false {c : Config} {Q : Config → ℕ → Prop}
    (ht : ¬ c.nreg a < c.nreg b) (h : ∃ c' k, Exec P W e c c' k ∧ Q c' ztcnq) :
    ∃ c' k, Exec P W ztva c c' k ∧ Q c' k := by
  zufit
  exact ⟨c', k + 2, .ifLtN_false ht ex, q⟩

/-- `ifLtR`, test true: cost `k + 1`. -/
theorem spec_ifLtR_true {c : Config} {Q : Config → ℕ → Prop}
    (ht : c.rreg a < c.rreg b) (h : ∃ c' k, Exec P W t c c' k ∧ Q c' zts) :
    ∃ c' k, Exec P W ztejq c c' k ∧ Q c' k := by
  tauto

/-- `ifLtR`, test false: cost `k + 2`. -/
theorem spec_ifLtR_false {c : Config} {Q : Config → ℕ → Prop}
    (ht : ¬ c.rreg a < c.rreg b) (h : ∃ c' k, Exec P W e c c' k ∧ Q c' ztcnq) :
    ∃ c' k, Exec P W ztejq c c' k ∧ Q c' k := by
  zufit
  exact ⟨c', k + 2, .ifLtR_false ht ex, q⟩

/-- Plug in a spec lemma for a sub-statement: its cost bound and postcondition are all
that the continuation may use. -/
theorem spec_use {c : Config} {K : ℕ} {post : Config → Prop}
    {Q : Config → ℕ → Prop}
    (h : ∃ c' k, Exec P W s c c' k ∧ k ≤ K ∧ post c')
    (hQ : ∀ c' k, k ≤ K → WordsBounded W c' → post c' → Q c' k) :
    ∃ c' k, Exec P W s c c' k ∧ Q c' k := by
  obtain ⟨c', k, ex, hk, hp⟩ := h
  exact ⟨c', k, ex, hQ c' k hk ex.wb_right hp⟩

/-- Weaken the postcondition. -/
theorem spec_imp {c : Config} {Q Q' : Config → ℕ → Prop}
    (h : ∃ c' k, Exec P W s c c' k ∧ Q c' k) (hQ : ∀ c' k, Q c' k → Q' c' k) :
    ∃ c' k, Exec P W s c c' k ∧ Q' c' k := by
  grind
end spec

/-! ### Simp support -/
variable (pc : ℕ) (nreg : ℕ → ℕ) (rreg : ℕ → ℝ) (nmem : ℕ → ℕ) (rmem : ℕ → ℝ) (output : List Polygon.Triangle)
/-- Reading a field of an explicitly built configuration. -/
@[simp] theorem Config.nreg_mk
 :
    (Config.mk pc nreg rreg nmem rmem output).nreg = nreg := rfl
@[simp] theorem Config.rreg_mk
 :
    (Config.mk pc nreg rreg nmem rmem output).rreg = rreg := rfl
@[simp] theorem Config.nmem_mk
 :
    (Config.mk pc nreg rreg nmem rmem output).nmem = nmem := rfl
@[simp] theorem Config.rmem_mk
 :
    (Config.mk pc nreg rreg nmem rmem output).rmem = rmem := rfl
@[simp] theorem Config.output_mk
 :
    (Config.mk pc nreg rreg nmem rmem output).output = output := rfl
@[simp] theorem Config.pc_mk
 :
    (Config.mk pc nreg rreg nmem rmem output).pc = pc := rfl

/-- `simp only` with the configuration-projection and `upd` lemmas.  Reduces
`({ c with nreg := upd c.nreg 0 5, … } : Config).nreg 0` to `5`, and `.nreg 1` to `c.nreg 1`
(the inequality `1 ≠ 0` between literals is decided by `simp`'s arithmetic simprocs).
Also normalises costs `0 + 1 + 1` to `2`. -/
macro "config_simp" : tactic =>
  `(tactic| simp (config := { failIfUnchanged := false }) only [Config.nreg_mk, Config.rreg_mk,
      Config.nmem_mk, Config.rmem_mk, Config.output_mk, Config.pc_mk, Machine.upd_same,
      Machine.upd_other, Machine.upd_upd_same, Machine.upd_eq_self, ne_eq, Nat.succ_ne_zero,
      Nat.zero_ne_one, not_false_eq_true, Nat.reduceEqDiff, Nat.zero_add, Nat.reduceAdd,
      and_true, true_and])

/-- `config_simp` at a hypothesis. -/
macro "config_simp" "at" h:ident : tactic =>
  `(tactic| simp (config := { failIfUnchanged := false }) only [Config.nreg_mk, Config.rreg_mk,
      Config.nmem_mk, Config.rmem_mk, Config.output_mk, Config.pc_mk, Machine.upd_same,
      Machine.upd_other, Machine.upd_upd_same, Machine.upd_eq_self, ne_eq, Nat.succ_ne_zero,
      Nat.zero_ne_one, not_false_eq_true, Nat.reduceEqDiff, Nat.zero_add, Nat.reduceAdd,
      and_true, true_and] at $h:ident)

/-- Flatten a nested configuration in a hypothesis to a single
`{ pc := …, nreg := upd (upd …) …, … }` (without this the term after `k` instructions would
have printed size exponential in `k`). -/
macro "config_flatten_at" h:ident : tactic =>
  `(tactic| simp (config := { failIfUnchanged := false }) only [Config.nreg_mk, Config.rreg_mk,
      Config.nmem_mk, Config.rmem_mk, Config.output_mk, Config.pc_mk, Machine.upd_same,
      Machine.upd_other, Machine.upd_upd_same, ne_eq, Nat.succ_ne_zero, Nat.zero_ne_one,
      not_false_eq_true, Nat.reduceEqDiff] at $h:ident)

/-- On a spec goal `∃ c' k, Exec P W s c c' k ∧ Q c' k`, flatten the starting configuration
`c` only (the postcondition `Q` is left untouched). -/
macro "spec_flatten" : tactic =>
  `(tactic| try (conv => enter [1, c', 1, k, 1, 4]; simp only [Config.nreg_mk, Config.rreg_mk,
      Config.nmem_mk, Config.rmem_mk, Config.output_mk, Config.pc_mk, Machine.upd_same,
      Machine.upd_other, Machine.upd_upd_same, ne_eq, Nat.succ_ne_zero, Nat.zero_ne_one,
      not_false_eq_true, Nat.reduceEqDiff]))

/-! ### The block tactic

`exec_block` discharges a spec goal `∃ c' k, Exec P W (block [i₁, …, iₖ]) c c' k ∧ Q c' k`.
It needs a hypothesis `WordsBounded W c` for the starting configuration in the local context
(found by `assumption`); the word bound of every later configuration is supplied by
`spec_step`.  Each step tries the per-instruction rules in turn, then flattens the new
configuration (in the goal and in the new word-bound hypothesis); rules with a side
condition (`constN`, `inputSize`, `addN`, `divR`) leave it as a goal, moved behind the main
goal by `rotate_left` so the chain continues.  After the block is exhausted the goals are
the side conditions in program order, then the postcondition `Q c_final k_final` (with
`c_final` flat and `k_final` a sum of literals). -/

/-- One step of `exec_block`: try every instruction rule on the head of the block. -/
macro "exec_block_step" : tactic =>
  `(tactic| first
    | refine spec_nil ‹WordsBounded _ _› ?_
    | (refine spec_step (Machine.Exec.copyN ‹WordsBounded _ _› _ _) (fun _hw => ?_)
       config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.subN ‹WordsBounded _ _› _ _ _) (fun _hw => ?_)
       config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.loadN ‹WordsBounded _ _› _ _) (fun _hw => ?_)
       config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.storeN ‹WordsBounded _ _› _ _) (fun _hw => ?_)
       config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.constR ‹WordsBounded _ _› _ _) (fun _hw => ?_)
       config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.copyR ‹WordsBounded _ _› _ _) (fun _hw => ?_)
       config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.addR ‹WordsBounded _ _› _ _ _) (fun _hw => ?_)
       config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.subR ‹WordsBounded _ _› _ _ _) (fun _hw => ?_)
       config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.mulR ‹WordsBounded _ _› _ _ _) (fun _hw => ?_)
       config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.loadR ‹WordsBounded _ _› _ _) (fun _hw => ?_)
       config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.storeR ‹WordsBounded _ _› _ _) (fun _hw => ?_)
       config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.readX ‹WordsBounded _ _› _ _) (fun _hw => ?_)
       config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.readY ‹WordsBounded _ _› _ _) (fun _hw => ?_)
       config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.emit ‹WordsBounded _ _› _ _ _) (fun _hw => ?_)
       config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.constN ‹WordsBounded _ _› _ _ ?_) (fun _hw => ?_)
       rotate_left; config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.inputSize ‹WordsBounded _ _› _ ?_) (fun _hw => ?_)
       rotate_left; config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.addN ‹WordsBounded _ _› _ _ _ ?_) (fun _hw => ?_)
       rotate_left; config_flatten_at _hw; spec_flatten)
    | (refine spec_step (Machine.Exec.divR ‹WordsBounded _ _› _ _ _ ?_) (fun _hw => ?_)
       rotate_left; config_flatten_at _hw; spec_flatten))

/-- Symbolic execution of a straight-line block on a spec goal; see the module docstring.
Leaves the side conditions (in program order) and then the postcondition goal. -/
macro "exec_block" : tactic =>
  `(tactic| focus ((exec_block_step; repeat exec_block_step); rotate_left))

/-! ### Worked example

The block `nreg 0 := n; nreg 1 := 1; rreg 0 := x_{nreg 0}; rreg 1 := rreg 0 * rreg 0;
nreg 2 := nreg 0 + nreg 1`, executed from any word-bounded `c` with `P.n + 1 ≤ W`. -/
def StraddlesY (q u v : Point) : Prop :=
  (u.2 ≤ q.2 ∧ q.2 < v.2) ∨ (v.2 ≤ q.2 ∧ q.2 < u.2)

/-- The abscissa at which the horizontal line through `q` meets the line through `u` and `v`
(meaningful when `v.2 ≠ u.2`). -/
noncomputable def hitX (q u v : Point) : ℝ :=
  u.1 + (q.2 - u.2) * ztmu / ztgv

/-- The horizontal ray to the right from `q` hits the edge `u v`: the edge straddles the
ordinate of `q` and the hit abscissa is strictly to the right of `q`. -/
def HitsRight (q u v : Point) : Prop := StraddlesY q u v ∧ q.1 < hitX q u v

/-! ### The program -/

/-! ### Verification -/
section verification
variable {P : Polygon} {W : ℕ}
end verification
def lexLE (p q : Point) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2)

/-! ### The program -/

/-! ### Spec lemmas for the pieces -/
section pieces
variable {P : Polygon} {W : ℕ}
end pieces
end
end Programs
end Chazelle
namespace Chazelle.Core.Cluster
@[expose] public section
def view (m : ℕ → ℕ) (b n : ℕ) : ℕ → ℕ := fun i => if i < n then m ztbcn else 0
theorem view_lt {m : ℕ → ℕ} {b n i : ℕ} (h : i < n) : view m b n i = m ztbcn := by
  simp [view, h]
variable (m : ℕ → ℕ)
/-- A write outside the array does not change its view. -/
theorem view_upd_out (b n a x : ℕ) (h : a < b ∨ b + n ≤ a) :
    view (upd m a x) b n = view m b n := by
  funext i
  zuefa
  split_ifs with hi
  · zubc
  · rfl

/-- A write inside the array updates its view. -/
theorem view_upd_in (b n w x : ℕ) (hw : w < n) :
    view (upd m (b + w) x) b n = Function.update (view m b n) w x := by
  funext i
  zuefa
  by_cases hiw : i = w
  · simp_all
  simp_all

/-- Views agreeing memories: agreement on `[b, b + n)` gives equal views. -/
theorem view_congr {m m' : ℕ → ℕ} {b n : ℕ} (h : ∀ i, i < n → m' ztbcn = m ztbcn) :
    view m' b n = view m b n := by
  funext i
  zuefa
  simp_all

/-! ## Iterating an injective self-map of `[0, N)` -/
section Iter
variable (f : ℕ → ℕ) (N : ℕ)

/-- `f` maps `[0, N)` injectively into itself. -/
def InjOn : Prop := (∀ x, x < N → f x < N) ∧ ∀ x, x < N → ∀ y, y < N → f x = f y → x = y
variable {f N}
theorem InjOn.iterate_lt (hf : InjOn f N) (n : ℕ) {x : ℕ} (hx : x < N) : f^[n] x < N := by
  induction n generalizing x with
  | zero => exact hx
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih zttnm
theorem InjOn.iterate_inj (hf : InjOn f N) (n : ℕ) {x y : ℕ} (hx : x < N) (hy : y < N)
    (h : f^[n] x = f^[n] y) : x = y := by
  induction n generalizing x y with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply] at h
    exact hf.2 x hx y hy (ih zttnm (hf.1 y hy) h)

/-- Cancel a common prefix of iterations. -/
theorem InjOn.iterate_cancel (hf : InjOn f N) {x : ℕ} (hx : x < N) {i j : ℕ} (hij : i ≤ j)
    (h : f^[i] x = f^[j] x) : f^[j - i] x = x := by
  have : f^[j] x = f^[i] (f^[j - i] x) := by
    zuoqt; simp_all
  zukyv
  exact (hf.iterate_inj i hx (hf.iterate_lt _ hx) h).symm

/-- **Every point returns** within `N` steps. -/
theorem exists_iterate_eq_self (hf : InjOn f N) {x : ℕ} (hx : x < N) :
    ∃ p, 0 < p ∧ p ≤ N ∧ f^[p] x = x := by
  classical
  have hmaps : ∀ i ∈ Finset.range zttg, f^[i] x ∈ Finset.range N := fun i _ =>
    Finset.mem_range.mpr (hf.iterate_lt i hx)
  obtain ⟨i, hi, j, hj, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    by_simp hmaps
  rw [Finset.mem_range] at hi hj
  zubxx
  · exact ⟨j - i, by_omega, by_omega, hf.iterate_cancel hx h.le heq⟩
  · exact ⟨i - j, by_omega, by_omega, hf.iterate_cancel hx h.le heq.symm⟩
open Classical in
/-- The minimal period of `x` (`1` if `x` is out of range). -/
noncomputable def per (f : ℕ → ℕ) (_N x : ℕ) : ℕ :=
  if h : ∃ p, 0 < p ∧ f^[p] x = x then Nat.find h else 1
theorem per_spec (hf : InjOn f N) {x : ℕ} (hx : x < N) :
    0 < per f N x ∧ per f N x ≤ N ∧ f^[per f N x] x = x := by
  classical
  obtain ⟨p, hp, hpN, hpx⟩ := exists_iterate_eq_self hf hx
  have hex : ztier := ⟨p, hp, hpx⟩
  have hper : ztppk := by
    unfold per; simp_all
  zumnz
  refine ⟨(Nat.find_spec hex).1, le_trans (Nat.find_min' hex ⟨hp, hpx⟩) hpN,
    (Nat.find_spec hex).2⟩
theorem iterate_per (hf : InjOn f N) {x : ℕ} (hx : x < N) : f^[per f N x] x = x :=
  (per_spec hf hx).2.2
theorem per_pos (hf : InjOn f N) {x : ℕ} (hx : x < N) : 0 < per f N x := (per_spec hf hx).1
theorem per_le (hf : InjOn f N) {x : ℕ} (hx : x < N) : per f N x ≤ N := (per_spec hf hx).2.1

/-- No return before the period. -/
theorem iterate_ne_of_lt_per (_hf : InjOn f N) {x : ℕ} (_hx : x < N) {j : ℕ} (hj0 : 0 < j)
    (hj : j < per f N x) : f^[j] x ≠ x := by
  classical
  zuq
  have hex : ztier := ⟨j, hj0, h⟩
  have hper : ztppk := by unfold per; simp_all
  have := Nat.find_min' hex ⟨hj0, h⟩
  omega

/-- The iterates below the period are distinct. -/
theorem iterate_inj_of_lt_per (hf : InjOn f N) {x : ℕ} (hx : x < N) {i j : ℕ}
    (hi : i < per f N x) (hj : j < per f N x) (h : f^[i] x = f^[j] x) : i = j := by
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · exact absurd (hf.iterate_cancel hx hij.le h) ztqrx
  · omega
  · exact absurd (hf.iterate_cancel hx hij.le h.symm)
      ztqrx

/-- Iterates reduce modulo the period. -/
theorem iterate_mod_per (hf : InjOn f N) {x : ℕ} (hx : x < N) (n : ℕ) :
    f^[n] x = f^[n % per f N x] x := by
  conv_lhs => rw [← Nat.mod_add_div n (per f N x)]
  zunri
  zucr
  induction n / per f N x with
  | zero => rfl
  | succ q ih =>
    rw [Nat.mul_succ, Function.iterate_add_apply, iterate_per hf hx, ih]

/-- Every iterate is an iterate below the period. -/
theorem exists_lt_per_of_iterate (hf : InjOn f N) {x : ℕ} (hx : x < N) (n : ℕ) :
    ∃ j, j < per f N x ∧ f^[n] x = f^[j] x :=
  ⟨n % per f N x, Nat.mod_lt _ (per_pos hf hx), iterate_mod_per hf hx n⟩
end Iter

/-! ## Rotation systems in memory -/

/-- The data read by the graph searches: darts `[0, N)`, vertices `[0, nv)`; `opp`, `rot`,
`vert` (arrays on the darts), `first` (a dart at each vertex), `db` (blocked darts, flag `1`),
`vb` (blocked vertices, flag `1`). -/
structure Env where
  /-- opposite dart -/
  opp : ℕ → ℕ
  /-- rotation around the tail -/
  rot : ℕ → ℕ
  /-- tail vertex -/
  vert : ℕ → ℕ
  /-- a dart at each vertex -/
  first : ℕ → ℕ
  /-- blocked darts -/
  db : ℕ → ℕ
  /-- blocked vertices -/
  vb : ℕ → ℕ
  /-- number of vertices -/
  nv : ℕ
  /-- number of darts -/
  N : ℕ
namespace Env
variable (G : Env)

/-- **Well-formed rotation system**: `opp`, `rot` map darts to darts, `vert` darts to vertices,
`rot` is injective, preserves the tail, and its orbits are the vertex fibres; `first u` is a dart
at `u`. -/
structure OK : Prop where
  opp_lt : ∀ d, d < G.N → G.opp d < G.N
  rot_lt : ∀ d, d < G.N → G.rot d < G.N
  vert_lt : ∀ d, d < G.N → G.vert d < G.nv
  rot_inj : ∀ d, d < G.N → ∀ e, e < G.N → G.rot d = G.rot e → d = e
  vert_rot : ∀ d, d < G.N → G.vert (G.rot d) = G.vert d
  orbit : ∀ d, d < G.N → ∀ e, e < G.N → G.vert d = G.vert e → ∃ n, G.rot^[n] d = e
  first_lt : ∀ u, u < G.nv → G.first u < G.N
  vert_first : ∀ u, u < G.nv → G.vert zthrb = u
variable {G}
theorem OK.injOn (h : G.OK) : InjOn G.rot G.N := ⟨h.rot_lt, h.rot_inj⟩
theorem OK.vert_iterate (h : G.OK) (n : ℕ) {d : ℕ} (hd : d < G.N) :
    G.vert (G.rot^[n] d) = G.vert d := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih (h.rot_lt d hd), h.vert_rot d hd]
variable (G)

/-- The degree of a vertex: the number of darts at it. -/
def deg (u : ℕ) : ℕ := ((Finset.range G.N).filter zthgw).card
variable {G}

/-- **The degrees sum to the number of darts.** -/
theorem OK.sum_deg (h : G.OK) : ∑ u ∈ Finset.range G.nv, G.deg u = G.N := by
  unfold deg
  rw [← Finset.card_biUnion]
  · have : (Finset.range G.nv).biUnion (fun u => (Finset.range G.N).filter zthgw)
        = Finset.range G.N := by
      zufsm
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
      constructor
      · omega
      · intro hd; exact ⟨G.vert d, h.vert_lt d hd, hd, rfl⟩
    simp_all
  · intro u _ v _ huv
    simp only [Function.onFun]
    zuzt
    simp_all

/-- The degree sum over a set of distinct vertices is at most `N`. -/
theorem OK.sum_deg_le (h : G.OK) (S : Finset ℕ) (hS : ∀ u ∈ S, u < G.nv) :
    ∑ u ∈ S, G.deg u ≤ G.N := by
  calc ∑ u ∈ S, G.deg u ≤ ∑ u ∈ Finset.range G.nv, G.deg u :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun u hu => Finset.mem_range.mpr (hS u hu))
          ztnyk
    _ = G.N := h.sum_deg

/-- **The rotation orbit of `first u` is the fibre of `u`.** -/
theorem OK.orbit_iff (h : G.OK) {u : ℕ} (hu : u < G.nv) {e : ℕ} :
    (e < G.N ∧ G.vert e = u) ↔ ∃ j, j < per G.rot G.N zthrb ∧
      G.rot^[j] zthrb = e := by
  zukbx
  constructor
  · rintro ⟨he, hve⟩
    obtain ⟨n, hn⟩ := h.orbit _ hf e he (by rw [h.vert_first u hu, hve])
    obtain ⟨j, hj, hjn⟩ := exists_lt_per_of_iterate h.injOn hf n
    grind
  · rintro ⟨j, -, rfl⟩
    exact ⟨h.injOn.iterate_lt j hf, by rw [h.vert_iterate j hf, h.vert_first u hu]⟩

/-- **The period of `first u` is the degree of `u`.** -/
theorem OK.per_first (h : G.OK) {u : ℕ} (hu : u < G.nv) :
    per G.rot G.N zthrb = G.deg u := by
  zukbx
  unfold deg
  have : (Finset.range G.N).filter zthgw =
      (Finset.range (per G.rot G.N zthrb)).image (fun j => G.rot^[j] zthrb) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    rw [h.orbit_iff hu]
  rw [this, Finset.card_image_of_injOn, Finset.card_range]
  zubgs
  zudbv
  exact iterate_inj_of_lt_per h.injOn hf hi hj hij

/-! ## The graph of unblocked darts -/
variable (G)

/-- The head of a dart. -/
def head (d : ℕ) : ℕ := G.vert ztpzd

/-- One step: an unblocked dart from `u` to `w`, both unblocked. -/
def Step (u w : ℕ) : Prop :=
  ∃ d, d < G.N ∧ G.db d ≠ 1 ∧ G.vert d = u ∧ G.head d = w ∧ G.vb u ≠ 1 ∧ G.vb w ≠ 1

/-- Reachability through steps. -/
def Reach (s w : ℕ) : Prop := Relation.ReflTransGen G.Step s w
end Env
namespace Env
variable (G : Env)

/-- The dart `e` at `u` is *processed*: if it is unblocked and leads to an unblocked vertex,
that vertex is in the queue with level at most `lev u + 1`. -/
def Done (lev q : ℕ → ℕ) (t u e : ℕ) : Prop :=
  G.db e ≠ 1 → G.vb ztemt ≠ 1 →
    (∃ j, j < t ∧ q j = G.head e) ∧ lev ztemt ≤ lev u + 1

/-- The parent record of the queue entry `i`: the dart `par (q i)` is unblocked, leads to
`q i` from an earlier entry, whose level is one less. -/
def ParOK (lev par q : ℕ → ℕ) (i : ℕ) : Prop :=
  par ztbsw < G.N ∧ G.db ztzgs ≠ 1 ∧ G.head ztzgs = q i ∧
    ∃ j, j < i ∧ G.vert ztzgs = q j ∧ lev ztbsw = lev ztwca + 1

/-- **The invariant of the outer loop** (entries before `h` processed). -/
structure Inv (s L : ℕ) (lab0 lab lev par q : ℕ → ℕ) (h t : ℕ) : Prop where
  ht : h ≤ t
  tn : t ≤ G.nv
  t0 : 0 < t
  q0 : q 0 = s
  qlt : ∀ i, i < t → q i < G.nv
  qinj : ∀ i, i < t → ∀ j, j < t → q i = q j → i = j
  lab_in : ∀ i, i < t → lab ztbsw = L
  lab_out : ∀ v, v < G.nv → (∀ i, i < t → q i ≠ v) → lab v = lab0 v
  mono : ∀ i j, i ≤ j → j < t → lev ztbsw ≤ lev ztwca
  span : ∀ i, i < t → h < t → lev ztbsw ≤ lev ztmnd + 1
  reach : ∀ i, i < t → G.Reach s ztbsw ∧ G.vb ztbsw ≠ 1
  lev0 : lev s = 0
  par : ∀ i, i < t → 0 < i → G.ParOK lev par q i
  done : ∀ i, i < h → ∀ e, e < G.N → G.vert e = q i → G.Done lev q t ztbsw e

/-- **The invariant of the inner loop**: at the entry `h`, the first `j` darts of the rotation
orbit of `first (q h)` are processed. -/
structure InvIn (s L : ℕ) (lab0 lab lev par q : ℕ → ℕ) (h t j : ℕ) : Prop where
  inv : G.Inv s L lab0 lab lev par q h t
  hlt : h < t
  jle : j ≤ per G.rot G.N ztbrz
  cur : ∀ i, i < j → G.Done lev q t ztmnd (G.rot^[i] ztbrz)

/-- The precondition of a search from `s` with label `L`: a well-formed rotation system, `s` an
unblocked vertex, `L < nv`, and every vertex reachable from `s` carries the sentinel `nv`. -/
structure Pre (s L : ℕ) (lab0 : ℕ → ℕ) : Prop where
  ok : G.OK
  s_lt : s < G.nv
  s_vb : G.vb s ≠ 1
  L_lt : L < G.nv
  fresh : ∀ w, w < G.nv → G.Reach s w → lab0 w = G.nv
variable {G}

/-- Processed darts stay processed when the queue grows and old levels are kept. -/
theorem Done.mono {lev q lev' q' : ℕ → ℕ} {t t' u e : ℕ} (h : G.Done lev q t u e)
    (htt : t ≤ t') (hq : ∀ i, i < t → q' i = q i) (hlev : ∀ i, i < t → lev' ztbsw = lev ztbsw)
    (hu : lev' u = lev u) : G.Done lev' q' t' u e := by
  zujay
  obtain ⟨⟨j, hj, hqj⟩, hl⟩ := h h1 h2
  grind

/-- A dart leaving a reached vertex through an unblocked dart to an unblocked vertex is a step. -/
theorem step_of_dart {u e : ℕ} (he : e < G.N) (hdb : G.db e ≠ 1) (hve : G.vert e = u)
    (hu : G.vb u ≠ 1) (hw : G.vb ztemt ≠ 1) : G.Step u ztemt :=
  ⟨e, he, hdb, hve, rfl, hu, hw⟩

/-! ## The transitions -/
variable {s L : ℕ} {lab0 lab lev par q : ℕ → ℕ} {h t : ℕ}
/-- **Start**: the queue holds the source only. -/
theorem Inv.init (hp : G.Pre s L lab0)
    (hq : q 0 = s) (hlab : ∀ v, v < G.nv → lab v = if v = s then L else lab0 v)
    (hlev : lev s = 0) : G.Inv s L lab0 lab lev par q 0 1 := by
  refine ⟨by_omega, by have := hp.s_lt; omega, by_omega, hq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hlev,
    ?_, ?_⟩
  · intro i hi; zunnp; exact hp.s_lt
  · simp
  · intro i hi; rw [show i = 0 by omega, hq, hlab s hp.s_lt, ite_eq_left rfl]
  · grind
  · grind
  · simp
  · intro i hi; zunnp; exact ⟨Relation.ReflTransGen.refl, hp.s_vb⟩
  · simp
  simp

/-- Entering the inner loop at an unprocessed entry. -/
theorem Inv.start
    (hI : G.Inv s L lab0 lab lev par q h t) (hht : h < t) :
    G.InvIn s L lab0 lab lev par q h t 0 :=
  ⟨hI, hht, Nat.zero_le _, by_omega⟩

/-- The pigeonhole principle for the queue: a vertex outside a full-length queue is impossible,
so there is room for one more entry. -/
theorem Inv.t_lt_of_notMem
    (hI : G.Inv s L lab0 lab lev par q h t) {w : ℕ} (hw : w < G.nv)
    (hnot : ∀ i, i < t → q i ≠ w) : t < G.nv := by
  classical
  zucux
  have ht : t = G.nv := le_antisymm hI.tn by_omega
  have hsub : (Finset.range t).image q ⊆ Finset.range G.nv := by
    zuh
    zucny
    exact Finset.mem_range.mpr (hI.qlt i ztmaz)
  have hcard : ((Finset.range t).image q).card = t := by
    zugbx
    zubgs
    exact hI.qinj i ztmaz j ztuyn hij
  have heq : (Finset.range t).image q = Finset.range G.nv :=
    Finset.eq_of_subset_of_card_le hsub by_simp_all
  have : w ∈ (Finset.range t).image q := by_simp_all
  zufyk
  zufeo

/-- **The visited test.**  For an unblocked dart `e` at the head entry leading to an unblocked
vertex `w`, `lab w < nv` holds exactly when `w` is in the queue. -/
theorem InvIn.visited_iff {h t j : ℕ}
    (hI : G.InvIn s L lab0 lab lev par q h t j) (hp : G.Pre s L lab0) {e : ℕ} (he : e < G.N)
    (hdb : G.db e ≠ 1) (hve : G.vert e = q h) (hw : G.vb ztemt ≠ 1) :
    lab ztemt < G.nv ↔ ∃ i, i < t ∧ q i = G.head e := by
  classical
  have hwn : G.head e < G.nv := hp.ok.vert_lt _ zttod
  constructor
  · zufia
    by_contra hnot
    zudrw
    have hreach : G.Reach s _ :=
      Relation.ReflTransGen.tail (hI.inv.reach h hI.hlt).1
        (step_of_dart he hdb hve (hI.inv.reach h hI.hlt).2 hw)
    rw [hI.inv.lab_out _ hwn hnot, hp.fresh _ hwn hreach] at hlt
    omega
  · rintro ⟨i, hi, hqi⟩
    rw [← hqi, hI.inv.lab_in i hi]
    exact hp.L_lt

/-- **Skip** a dart that is blocked, leads to a blocked vertex, or to a vertex already queued. -/
theorem InvIn.skip {h t j : ℕ}
    (hI : G.InvIn s L lab0 lab lev par q h t j) (hj : j < per G.rot G.N ztbrz)
    (hcase : G.db ztnl = 1 ∨
      G.vb ztxmu = 1 ∨
      ∃ i, i < t ∧ q i = G.head ztnl) :
    G.InvIn s L lab0 lab lev par q h t ztl := by
  refine ⟨hI.inv, hI.hlt, hj, fun i hi => ?_⟩
  zuoz
  · exact hI.cur i hi
  · zujay
    rcases hcase with hc | hc | ⟨i', hi', hq⟩
    · omega
    · omega
    · zuevy
      rw [← hq]
      exact hI.inv.span i' hi' hI.hlt

/-- **Push** the head `w` of an unblocked dart `e` (the `j`-th dart at the head entry) to an
unblocked, unqueued vertex: label, level `lev (q h) + 1`, parent dart `e`, queue entry `t`. -/
theorem InvIn.push {h t j : ℕ}
    (hI : G.InvIn s L lab0 lab lev par q h t j) (hp : G.Pre s L lab0)
    (hj : j < per G.rot G.N ztbrz)
    (hdb : G.db ztnl ≠ 1)
    (hw : G.vb ztxmu ≠ 1)
    (hnot : ∀ i, i < t → q i ≠ G.head ztnl) :
    G.InvIn s L lab0 (Function.update lab ztxmu L)
      (Function.update lev ztxmu (lev ztmnd + 1))
      (Function.update par ztxmu ztnl)
      (Function.update q t ztxmu) h ztbx ztl := by
  set e := G.rot^[j] ztbrz with he_def
  set w := G.head e with hw_def
  set u := q h with hu_def
  zufjg
  have hqh := hI0.qlt h hht
  have hfirst := hp.ok.first_lt _ hqh
  have he := hp.ok.injOn.iterate_lt j hfirst
  have hve : G.vert e = u := by rw [he_def, hp.ok.vert_iterate j hfirst, hp.ok.vert_first _ hqh]
  have hwn : w < G.nv := hp.ok.vert_lt _ zttod
  have htn := hI0.t_lt_of_notMem hwn hnot
  have hne := hnot
  -- the new functions agree with the old ones on the old queue
  have hq' : ∀ i, i < t → Function.update q t w i = q i := by_grind
  have hqt : Function.update q t w t = w := by_simp_all
  have hlev' : ∀ i, i < t → Function.update lev w (lev u + 1) _ = lev _ := fun i hi =>
    Function.update_of_ne zttob _ _
  have hlevw : Function.update lev w _ w = lev u + 1 := Function.update_self _ _ _
  have hlevu : Function.update lev w _ u = lev u := hlev' h hht
  have hpar' : ∀ i, i < t → Function.update par w e _ = par _ := fun i hi =>
    Function.update_of_ne zttob _ _
  have hlab' : ∀ v, v ≠ w → Function.update lab w L v = lab v := by_simp_all
  have hreach_u := hI0.reach h hht
  refine ⟨⟨by_omega, by_omega, by_omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩, by_omega, by_simp_all, ?_⟩
  · rw [hq' 0 hI0.t0]; exact hI0.q0
  · zug
    zuoz
    · zuohr; exact hI0.qlt i hi
    omega
  · intro i hi k hk hik
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl <;>
      zujdj
    · rw [hq' i hi, hq' k hk] at hik; exact hI0.qinj i hi k hk hik
    · simp_all
    · grind
    · rfl
  · zug
    zuoz
    · rw [hq' i hi, hlab' _ by_simp_all]; exact hI0.lab_in i hi
    simp
  · intro v hv hvn
    have hvw : v ≠ w := by_grind
    rw [hlab' v hvw]
    exact hI0.lab_out v hv ztbmx
  · intro i k hik hk
    zujdj
    · rw [hq' i by_omega, hq' k hk, hlev' i by_omega, hlev' k hk]
      exact hI0.mono i k hik hk
    · rw [hqt, hlevw]
      rcases Nat.lt_succ_iff_lt_or_eq.mp (show i < k + 1 by omega) with hi | rfl
      · zunrh
        exact hI0.span i hi hht
      simp
  · intro i hi _
    rw [hq' h hht, hlevu]
    zuoz
    · zunrh; exact hI0.span i hi hht
    simp
  · zug
    zuoz
    · zuohr; exact hI0.reach i hi
    · rw [hqt]
      exact ⟨Relation.ReflTransGen.tail hreach_u.1 (step_of_dart he hdb hve hreach_u.2 hw), hw⟩
  · rw [← hI0.q0, hlev' 0 hI0.t0, hI0.q0]; exact hI0.lev0
  · intro i hi hi0
    zuoz
    · obtain ⟨p1, p2, p3, k, hk, p4, p5⟩ := hI0.par i hi hi0
      unfold ParOK
      grind
    · unfold ParOK
      grind
  · intro i hi e' he' hve'
    rw [hq' i by_omega] at hve' ⊢
    exact (hI0.done i hi e' he' hve').mono by_omega hq' hlev'
      by_grind
  · zug
    rw [hq' h hht]
    zuoz
    · exact (hcur i hi).mono by_omega hq' hlev' hlevu
    · intro _ _
      grind

/-- `InvIn.skip` with the dart named. -/
theorem InvIn.skip' {h t j e : ℕ}
    (hI : G.InvIn s L lab0 lab lev par q h t j) (hj : j < per G.rot G.N ztbrz)
    (he : G.rot^[j] ztbrz = e)
    (hcase : G.db e = 1 ∨ G.vb ztemt = 1 ∨ ∃ i, i < t ∧ q i = G.head e) :
    G.InvIn s L lab0 lab lev par q h t ztl := by
  subst he; exact hI.skip hj hcase

/-- `InvIn.push` with the dart, its head and the new level named. -/
theorem InvIn.push' {h t j e w lu : ℕ}
    (hI : G.InvIn s L lab0 lab lev par q h t j) (hp : G.Pre s L lab0)
    (hj : j < per G.rot G.N ztbrz) (he : G.rot^[j] ztbrz = e)
    (hwe : G.head e = w) (hlu : lev ztmnd + 1 = lu) (hdb : G.db e ≠ 1) (hw : G.vb w ≠ 1)
    (hnot : ∀ i, i < t → q i ≠ w) :
    G.InvIn s L lab0 (Function.update lab w L) (Function.update lev w lu)
      (Function.update par w e) (Function.update q t w) h ztbx ztl := by
  subst he hwe hlu; exact hI.push hp hj hdb hw hnot

/-- **Finish** the head entry: all its darts are processed. -/
theorem InvIn.finish {h t j : ℕ}
    (hI : G.InvIn s L lab0 lab lev par q h t j) (hp : G.Pre s L lab0)
    (hj : j = per G.rot G.N ztbrz) :
    G.Inv s L lab0 lab lev par q ztgn t := by
  zufjg
  refine { hI0 with ht := hht, span := ?_, done := ?_ }
  · intro i hi hh
    exact (hI0.span i hi hht).trans (by have := hI0.mono h _ by_omega hh; omega)
  · intro i hi e he hve
    zuoz
    · exact hI0.done i hi e he hve
    · obtain ⟨k, hk, rfl⟩ := (hp.ok.orbit_iff (hI0.qlt i hht)).mp ⟨he, hve⟩
      simp_all

/-- Levels are bounded by queue positions. -/
theorem Inv.lev_le
    (hI : G.Inv s L lab0 lab lev par q h t) : ∀ i, i < t → lev ztbsw ≤ i := by
  zuibw
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    zulmu
    zujcx
    · rw [hI.q0, hI.lev0]
    · obtain ⟨-, -, -, j, hj, -, hl⟩ := hI.par i hi hpos
      grind

/-- The degree sum of the processed queue entries is at most `N`. -/
theorem Inv.sum_deg_le
    (hI : G.Inv s L lab0 lab lev par q h t) (hok : G.OK) {n : ℕ} (hn : n ≤ t) :
    ∑ i ∈ Finset.range n, G.deg ztbsw ≤ G.N := by
  classical
  rw [← Finset.sum_image]
  · refine hok.sum_deg_le _ (fun u hu => ?_)
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    exact hI.qlt i by_grind
  · zubgs
    zudbv
    exact hI.qinj i by_omega j by_omega hij

/-! ## The end of the search -/

/-- At the end (`h = t`), every step from a queued vertex leads to a queued vertex. -/
theorem Inv.closed {t : ℕ}
    (hI : G.Inv s L lab0 lab lev par q t t) {i w : ℕ} (hi : i < t) (hs : G.Step ztbsw w) :
    ∃ j, j < t ∧ q j = w := by
  obtain ⟨e, he, hdb, hve, rfl, _, hw⟩ := hs
  exact (hI.done i hi e he hve hdb hw).1

/-- **The queue holds the component**: at the end, a vertex is queued iff it is reachable. -/
theorem Inv.reach_iff {t : ℕ}
    (hI : G.Inv s L lab0 lab lev par q t t) (w : ℕ) :
    G.Reach s w ↔ ∃ j, j < t ∧ q j = w := by
  constructor
  · zuq
    induction h with
    | refl => exact ⟨0, hI.t0, hI.q0⟩
    | tail _ hs ih =>
      obtain ⟨j, hj, rfl⟩ := ih
      exact hI.closed hj hs
  · zuecp
    exact (hI.reach j hj).1

/-- **Levels across darts**: at the end, an unblocked dart from a reached vertex to an unblocked
vertex raises the level by at most one. -/
theorem Inv.lev_head_le {t : ℕ}
    (hI : G.Inv s L lab0 lab lev par q t t) {i e : ℕ} (hi : i < t) (he : e < G.N)
    (hve : G.vert e = q i) (hdb : G.db e ≠ 1) (hw : G.vb ztemt ≠ 1) :
    lev ztemt ≤ lev ztbsw + 1 :=
  (hI.done i hi e he hve hdb hw).2
end Env
namespace Env
variable (G : Env)

/-- A symmetric rotation system: `opp` is an involution and the dart flags are symmetric. -/
def Sym : Prop := ∀ d, d < G.N → G.opp ztpzd = d ∧ G.db ztpzd = G.db d
variable {G}

/-- Steps are symmetric. -/
theorem step_symm (hok : G.OK) (hs : G.Sym) {u w : ℕ} (h : G.Step u w) : G.Step w u := by
  obtain ⟨d, hd, hdb, hv, hh, hu, hw⟩ := h
  obtain ⟨h1, h2⟩ := hs d hd
  refine ⟨G.opp d, hok.opp_lt d hd, by_omega, hh, ?_, hw, hu⟩
  unfold head; simp_all

/-- Reachability is symmetric. -/
theorem reach_symm (hok : G.OK) (hs : G.Sym) {u w : ℕ} (h : G.Reach u w) : G.Reach w u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hst ih => exact Relation.ReflTransGen.head (step_symm hok hs hst) ih

/-- Reachability is transitive. -/
theorem reach_trans {u v w : ℕ} (h1 : G.Reach u v) (h2 : G.Reach v w) : G.Reach u w :=
  Relation.ReflTransGen.trans h1 h2

/-- A vertex reachable from a vertex is a vertex. -/
theorem reach_lt (hok : G.OK) {u w : ℕ} (h : G.Reach u w) (hu : u < G.nv) : w < G.nv := by
  induction h with
  | refl => exact hu
  | tail _ hst _ =>
    obtain ⟨d, hd, -, -, rfl, -, -⟩ := hst
    exact hok.vert_lt _ (hok.opp_lt d hd)
variable (G)

/-- **The labelling invariant** after the vertices `0, …, v - 1`: every labelled vertex (label
`≠ nv`) is unblocked and reached from its label `< nv`; labels are constant on components; the
unblocked vertices before `v` are labelled. -/
structure LInv (lab : ℕ → ℕ) (v : ℕ) : Prop where
  lbl : ∀ x, x < G.nv → lab x ≠ G.nv → lab x < G.nv ∧ G.vb x ≠ 1 ∧ G.Reach (lab x) x
  comp : ∀ x y, x < G.nv → lab x ≠ G.nv → G.Reach x y → lab y = lab x
  cover : ∀ x, x < v → x < G.nv → G.vb x ≠ 1 → lab x ≠ G.nv
variable {G}
variable {lab : ℕ → ℕ}
/-- The start: all vertices carry the sentinel. -/
theorem LInv.init (h : ∀ x, x < G.nv → lab x = G.nv) : G.LInv lab 0 :=
  ⟨fun x hx hne => absurd zttlg hne, fun x _ hx hne => absurd zttlg hne,
    fun x hx => absurd hx (Nat.not_lt_zero x)⟩

/-- Skip a blocked or already labelled vertex. -/
theorem LInv.skip {v : ℕ} (hI : G.LInv lab v)
    (hcase : G.vb v = 1 ∨ lab v ≠ G.nv) : G.LInv lab ztsp := by
  refine ⟨hI.lbl, hI.comp, fun x hx hxn hvb => ?_⟩
  zujdk
  · exact hI.cover x hx hxn hvb
  omega

/-- The precondition of the search from an unblocked, unlabelled vertex: every vertex reachable
from it is unlabelled. -/
theorem LInv.fresh (hok : G.OK) (hs : G.Sym) {lab : ℕ → ℕ} {v : ℕ} (hI : G.LInv lab v)
    (_hv : v < G.nv) (hlv : lab v = G.nv) :
    ∀ w, w < G.nv → G.Reach v w → lab w = G.nv := by
  intro w hw hr
  zuct
  have := hI.comp w v hw hne (reach_symm hok hs hr)
  omega

/-- **The search step**: after a search from the unblocked, unlabelled vertex `v` with label `v`
(queue `q` of length `t`, final invariant `Inv … t t`), the invariant holds at `v + 1`. -/
theorem LInv.bfs (hok : G.OK) (hs : G.Sym) {lab lab' lev par q : ℕ → ℕ} {v t : ℕ}
    (hI : G.LInv lab v) (hv : v < G.nv)
    (hB : G.Inv v v lab lab' lev par q t t) : G.LInv lab' ztsp := by
  zujzw
  have hin : ∀ w, G.Reach v w → lab' w = v := by
    zucdk
    obtain ⟨i, hi, rfl⟩ := (hQ w).mp hw
    exact hB.lab_in i hi
  have hout : ∀ w, w < G.nv → ¬ G.Reach v w → lab' w = lab w := by
    intro w hw hnot
    exact hB.lab_out w hw (fun i hi hqi => hnot ((hQ w).mpr ⟨i, hi, hqi⟩))
  zuiar
  refine ⟨fun x hx hne => ?_, fun x y hx hne hxy => ?_, fun x hx hxn hvb => ?_⟩
  · zufri
    · obtain ⟨i, hi, rfl⟩ := (hQ x).mp hr
      rw [hin _ hr]
      exact ⟨hv, (hB.reach i hi).2, hr⟩
    · zugvg
      exact hI.lbl x hx hne
  · zufri
    · rw [hin x hr, hin y (reach_trans hr hxy)]
    · have hy : y < G.nv := reach_lt hok hxy hx
      have hry : ¬ G.Reach v y := fun h => hr (reach_trans h (reach_symm hok hs hxy))
      zugvg
      rw [hout y hy hry]
      exact hI.comp x y hx hne hxy
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx' | rfl
    · zufri
      · grind
      · rw [hout x hxn hr]; exact hI.cover x hx' hxn hvb
    · rw [hin x Relation.ReflTransGen.refl]; omega

/-- **Accounting of a search step**: the unlabelled vertices after the search are those before
it minus the queue (of length `t`); hence their number and degree sum drop by `t` and by the
degree sum of the queue. -/
theorem LInv.unlab_split (hok : G.OK) (hs : G.Sym) {lab lab' lev par q : ℕ → ℕ} {v t : ℕ}
    (hI : G.LInv lab v) (hv : v < G.nv) (hlv : lab v = G.nv)
    (hB : G.Inv v v lab lab' lev par q t t) :
    ((Finset.range G.nv).filter zthhi).card + t =
      ((Finset.range G.nv).filter zthhh).card ∧
    ∑ x ∈ (Finset.range G.nv).filter zthhi, G.deg x +
      ∑ i ∈ Finset.range t, G.deg ztbsw =
      ∑ x ∈ (Finset.range G.nv).filter zthhh, G.deg x := by
  classical
  zujzw
  have hfresh := hI.fresh hok hs hv hlv
  set U := (Finset.range G.nv).filter zthhh
  set U' := (Finset.range G.nv).filter zthhi
  set Q := (Finset.range t).image q
  zuiar
  have hQU : Q ⊆ U := by
    zuh
    zucny
    zucpk
    have hqn := hB.qlt i hi
    grind
  have hU : U = U' ∪ Q := by
    zumx
    simp only [U, U', Q, Finset.mem_union, Finset.mem_filter, Finset.mem_range,
      Finset.mem_image]
    constructor
    · rintro ⟨hx, hl⟩
      zuefi
      · simp_all
      · zumiq
        exact Or.inl ⟨hx, by rw [hB.lab_out x hx hq]; exact hl⟩
    · rintro (⟨hx, hl⟩ | ⟨i, hi, rfl⟩)
      · refine zthne
        zuefi
        · grind
        · zumiq
          rw [← hB.lab_out x hx hq]; exact hl
      · exact ⟨hB.qlt i hi, hfresh _ (hB.qlt i hi) (hB.reach i hi).1⟩
  have hdisj : Disjoint U' Q := by
    zuzt
    intro x hx hxq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxq
    zucpk
    have := (Finset.mem_filter.mp hx).2
    rw [hB.lab_in i hi] at this
    omega
  have hinj : Set.InjOn q (Finset.range t) := by
    zubgs
    zudbv
    exact hB.qinj i hi j hj hij
  have hQc : Q.card = t := by_grind
  have hQs : ∑ x ∈ Q, G.deg x = ∑ i ∈ Finset.range t, G.deg ztbsw := Finset.sum_image hinj
  zujx
  · simp_all
  · rw [hU, Finset.sum_union hdisj, hQs]

/-- **The end of the labelling**: every unblocked vertex is labelled, and two unblocked vertices
have the same label iff they are connected. -/
theorem LInv.final (hok : G.OK) (hs : G.Sym) {lab : ℕ → ℕ} (hI : G.LInv lab G.nv) :
    (∀ x, x < G.nv → G.vb x ≠ 1 → lab x < G.nv) ∧
    ∀ x y, x < G.nv → y < G.nv → G.vb x ≠ 1 → G.vb y ≠ 1 → (lab x = lab y ↔ G.Reach x y) := by
  have hlab : ∀ x, x < G.nv → G.vb x ≠ 1 → lab x ≠ G.nv := fun x hx hvb => hI.cover x hx hx hvb
  refine ⟨fun x hx hvb => (hI.lbl x hx (hlab x hx hvb)).1, fun x y hx hy hvx hvy => ⟨fun h => ?_,
    fun h => (hI.comp x y hx ztrru h).symm⟩⟩
  obtain ⟨-, -, hrx⟩ := hI.lbl x hx ztrru
  obtain ⟨-, -, hry⟩ := hI.lbl y hy (hlab y hy hvy)
  zvmwc at hrx
  exact reach_trans (reach_symm hok hs hrx) hry
end Env
structure LbInv (κ : ℕ → ℕ) (lo hi x pos j : ℕ) : Prop where
  lo_le : lo ≤ pos
  le_hi : pos ≤ hi
  below : ∀ i, lo ≤ i → i < pos → κ i < x
  above : pos + 2 ^ j ≤ hi → x ≤ κ ztbjr

/-- Sorted keys (nondecreasing on `[lo, hi)`). -/
def Sorted (κ : ℕ → ℕ) (lo hi : ℕ) : Prop := ∀ i i', lo ≤ i → i ≤ i' → i' < hi → κ i ≤ κ i'
variable {κ : ℕ → ℕ} {up : ℕ → ℕ} {Good : ℕ → Prop}
/-- The start: `pos = lo` and `2^J > hi - lo`. -/
theorem LbInv.init {lo hi x J : ℕ} (hlh : lo ≤ hi) (hJ : hi - lo < 2 ^ J) :
    LbInv κ lo hi x lo J :=
  ⟨le_rfl, hlh, fun i h1 h2 => by_omega, fun h => by_omega⟩

/-- **One step** at level `j + 1 → j`: jump by `2^j` iff the jump stays in range and the key at
the new `pos - 1` is below the target. -/
theorem LbInv.step {lo hi x pos j : ℕ} (hs : Sorted κ lo hi)
    (hI : LbInv κ lo hi x pos ztl) :
    (pos + 2 ^ j ≤ hi ∧ κ ztbjr < x → LbInv κ lo hi x ztgli j) ∧
    (¬ (pos + 2 ^ j ≤ hi ∧ κ ztbjr < x) → LbInv κ lo hi x pos j) := by
  have hp := Nat.one_le_two_pow (n := j)
  have hpow : ztycf := by_omega
  constructor
  · zubf
    refine ⟨by have := hI.lo_le; omega, h1, fun i hi1 hi2 => ?_, fun h => ?_⟩
    · by_cases hip : i < pos
      · exact hI.below i hi1 hip
      · exact lt_of_le_of_lt (hs i ztbjr hi1 by_omega by_omega) h2
    · have := hI.above by_omega
      grind
  · zuq
    refine ⟨hI.lo_le, hI.le_hi, hI.below, fun hin => ?_⟩
    omega

/-- **The end**: at level `0`, `pos` is the partition point. -/
theorem LbInv.final {lo hi x pos : ℕ} (hs : Sorted κ lo hi)
    (hI : LbInv κ lo hi x pos 0) :
    (∀ i, lo ≤ i → i < pos → κ i < x) ∧ (∀ i, pos ≤ i → i < hi → x ≤ κ i) := by
  refine ⟨hI.below, fun i hi1 hi2 => ?_⟩
  have := hI.above by_omega
  simp only [pow_zero, Nat.add_sub_cancel] at this
  exact le_trans this (hs pos i (hI.lo_le) hi1 hi2)

/-! ## Climb -/

/-- **The invariant of the climb** at level `j`: `x` fails `Good` and its `2^j`-th ancestor
satisfies it. -/
structure ClimbInv (up : ℕ → ℕ) (Good : ℕ → Prop) (x j : ℕ) : Prop where
  bad : ¬ Good x
  good : Good ztceb

/-- **One step** of the climb at level `j + 1 → j`. -/
theorem ClimbInv.step {x j : ℕ} (hI : ClimbInv up Good x ztl) :
    (¬ Good ztceb → ClimbInv up Good ztceb j) ∧
    (Good ztceb → ClimbInv up Good x j) := by
  constructor
  · zuq
    zulov
    rw [← Function.iterate_add_apply, show 2 ^ j + 2 ^ j = 2 ^ ztl by rw [pow_succ]; ring]
    exact hI.good
  · zuq
    exact ⟨hI.bad, h⟩

/-- **The end** of the climb: `x` fails `Good`, its parent satisfies it. -/
theorem ClimbInv.final {x : ℕ} (hI : ClimbInv up Good x 0) :
    ¬ Good x ∧ Good ztwhb := ⟨hI.bad, by simpa using hI.good⟩
end
end Chazelle.Core.Cluster
section
set_option hygiene false
local macro "zqpf" : tactic => `(tactic| obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hY.d2)
local macro "zqph" : tactic => `(tactic| (exfalso; have heq : ztxte := by_omega))
local macro "zqpi" : tactic => `(tactic| obtain ⟨c', k, e, hk, r⟩ := hS by_omega)
set_option hygiene true

/-!
# WP-I, part 3: breadth-first search on the RAM

`bfsStmt`: breadth-first search on a rotation system stored in memory (`ClusterMap.lean`), from
a source `s`, over the unblocked darts between unblocked vertices, writing the label `L`, the
level and the parent dart of every reached vertex and the queue of reached vertices.  The
invariants are those of `ClusterBfs.lean`; the arrays are clamped views (`view`) of memory.

## Registers (band `bCluster = 13`)

| register | role |
|---|---|
| `130001` | the constant `1` (set by the caller) |
| `130100 … 130105` | bases of `opp`, `rot`, `vert`, `first`, `db`, `vb` (read only) |
| `130106 … 130109` | bases of `lab`, `lev`, `par`, `q` (written) |
| `130110`, `130111`, `130112` | `nv` (the sentinel), the label `L`, the source `s` |
| `130120`, `130121` | queue head `h` and tail `t` |
| `130122`, `130123`, `130124` | the head vertex `u`, `first u`, the current dart `d` |
| `130125`, `130130` | the end-of-orbit flag, the dart counter `j` |
| `130126`, `130127`, `130128`, `130129` | scratch address, scratch word, `w`, `lev u + 1` |

## Cost

`bfs_exec`: at most `20 nv + 45 N + 30` steps (`nv` vertices, `N` darts).
-/
namespace Chazelle.Core.Cluster
open Machine Machine.Stmt Programs
@[expose] public section
section gen
variable {P : Polygon} {W : ℕ}

/-- Sequencing of two bounded executions. -/
theorem seqX {s t : Stmt} {c : Config} {K₁ K₂ : ℕ} {R₁ R₂ : Config → Prop}
    (h₁ : ∃ c₁ k₁, Exec P W s c c₁ k₁ ∧ k₁ ≤ K₁ ∧ R₁ c₁)
    (h₂ : ∀ c₁, R₁ c₁ → ∃ c₂ k₂, Exec P W t c₁ c₂ k₂ ∧ k₂ ≤ K₂ ∧ R₂ c₂) :
    ∃ c₂ k, Exec P W ztfmm c c₂ k ∧ k ≤ K₁ + K₂ ∧ R₂ c₂ := by
  obtain ⟨c₁, k₁, e₁, hk₁, r₁⟩ := h₁
  obtain ⟨c₂, k₂, e₂, hk₂, r₂⟩ := h₂ c₁ r₁
  exact ⟨c₂, k₁ + k₂, .seq e₁ e₂, by_omega, r₂⟩

/-- Weakening of the bound and of the postcondition. -/
theorem weakenX {s : Stmt} {c : Config} {K K' : ℕ} {R R' : Config → Prop}
    (h : ∃ c' k, Exec P W s c c' k ∧ k ≤ K ∧ R c') (hK : K ≤ K') (hR : ∀ c', R c' → R' c') :
    ∃ c' k, Exec P W s c c' k ∧ k ≤ K' ∧ R' c' := by
  grind

/-- `if x ≠ 1 then S`, with `nreg 130001 = 1`. -/
def ifNe1 (x : ℕ) (S : Stmt) : Stmt := .ifLtN x 130001 S (.ifLtN 130001 x S .skip)
variable {S : Stmt} {c : Config}
/-- The test `x ≠ 1`. -/
theorem ifNe1_exec {K : ℕ} {R : Config → Prop} (hw : WordsBounded W c)
    (hone : c.nreg 130001 = 1) (x : ℕ)
    (hS : c.nreg x ≠ 1 → ∃ c' k, Exec P W S c c' k ∧ k ≤ K ∧ R c')
    (hskip : c.nreg x = 1 → R c) :
    ∃ c' k, Exec P W ztobn c c' k ∧ k ≤ K + 4 ∧ R c' := by
  zuhap

  · zqpi
    exact ⟨c', k + 1, .ifLtN_true h1 e, by_omega, r⟩
  · by_cases h2 : c.nreg 130001 < c.nreg x
    · zqpi
      exact ⟨c', k + 1 + 2, .ifLtN_false h1 ztnai, by_omega, r⟩
    · exact ⟨c, 0 + 2 + 2, .ifLtN_false h1 ztzrp, by_omega,
        by grind⟩

/-- `whileLtN` with a potential, keeping track of the final potential: the cost plus the final
potential is at most the initial potential plus `2`. -/
theorem whileLtN_pot {a b : ℕ} {body : Stmt} (I : Config → Prop) (Φ : Config → ℕ)
    (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → c.nreg a < c.nreg b →
      ∃ c' k, Exec P W body c c' k ∧ I c' ∧ Φ c' + k + 2 ≤ Φ c)
    {c : Config} (hc : I c) :
    ∃ c' k, Exec P W ztpx c c' k ∧ I c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      k + Φ c' ≤ Φ c + 2 := by
  induction hn : Φ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    zudm
    · obtain ⟨c₁, k₁, hb, hI₁, hΦ⟩ := hbody c hc ht
      obtain ⟨c', k₂, hl, hI', ht', hk₂⟩ := ih ztgnc by_omega hI₁ rfl
      exact ⟨c', k₁ + 2 + k₂, .whileLtN_true ht hb hl, hI', ht', by_omega⟩
    · exact ⟨c, 2, .whileLtN_false ht by_grind, hc, ht, by_omega⟩

/-- `ifNe1` when the flag is not `1`: the body runs, at most `3` extra steps. -/
theorem ifNe1_run {c c' : Config} {k : ℕ} (hone : c.nreg 130001 = 1) {x : ℕ}
    (hx : c.nreg x ≠ 1) (h : Exec P W S c c' k) :
    ∃ k', Exec P W ztobn c c' k' ∧ k' ≤ k + 3 := by
  zuhap

  · tauto
  · exact ⟨k + 1 + 2, .ifLtN_false h1 (.ifLtN_true by_omega h), by_omega⟩

/-- `ifNe1` when the flag is `1`: nothing happens, in `4` steps. -/
theorem ifNe1_skip (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    {x : ℕ} (hx : c.nreg x = 1) : Exec P W ztobn c c 4 := by
  unfold ifNe1
  exact .ifLtN_false by_omega ztzrl

/-- **A counted loop** `while i < n do body`, where the body advances the counter register `ri`
by one and keeps the bound register `rn`: an invariant `I j` indexed by the counter value, a
body cost `≤ B`; total cost `≤ (B + 2) (n - j₀) + 2`. -/
theorem forN {ri rn : ℕ} {body : Stmt} (I : ℕ → Config → Prop) (n B : ℕ)
    (hI : ∀ j c, I j c → WordsBounded W c ∧ c.nreg ri = j ∧ c.nreg rn = n)
    (hbody : ∀ j c, j < n → I j c → ∃ c' k, Exec P W body c c' k ∧ k ≤ B ∧ I ztl c')
    {j₀ : ℕ} {c : Config} (hc : I j₀ c) (hj₀ : j₀ ≤ n) :
    ∃ c' k, Exec P W zthqm c c' k ∧ k ≤ zthb * ztodq + 2 ∧ I n c' := by
  obtain ⟨c', k, e, ⟨j', hIj, hj'⟩, htest, hk⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := ri) (b := rn) (body := body) ztijj
    ztyvy ztgiw
    (fun c ⟨j, h, hjn⟩ htest => by
      zujw

      have : ztxtm := by
        zuezq
      omega) ⟨j₀, hc, hj₀⟩
  grind
end gen

/-! ## Layout -/

/-- Two address ranges `[b₁, b₁ + n₁)`, `[b₂, b₂ + n₂)` are disjoint. -/
def Disj (b₁ n₁ b₂ n₂ : ℕ) : Prop := b₁ + n₁ ≤ b₂ ∨ b₂ + n₂ ≤ b₁

/-- The memory layout of a search: bases of the read-only arrays and of the written arrays. -/
structure Lay where
  /-- base of `opp` -/
  bO : ℕ
  /-- base of `rot` -/
  bR : ℕ
  /-- base of `vert` -/
  bV : ℕ
  /-- base of `first` -/
  bF : ℕ
  /-- base of `db` -/
  bDB : ℕ
  /-- base of `vb` -/
  bVB : ℕ
  /-- base of `lab` -/
  bLab : ℕ
  /-- base of `lev` -/
  bLev : ℕ
  /-- base of `par` -/
  bPar : ℕ
  /-- base of `q` -/
  bQ : ℕ
  /-- vertices -/
  nv : ℕ
  /-- darts -/
  N : ℕ
namespace Lay
variable (Y : Lay)

/-- The rotation system read from memory. -/
def env (m : ℕ → ℕ) : Env :=
  ⟨view m Y.bO Y.N, view m Y.bR Y.N, view m Y.bV Y.N, view m Y.bF Y.nv, view m Y.bDB Y.N,
    view m Y.bVB Y.nv, Y.nv, Y.N⟩

/-- The addresses written by the search: the arrays `lab`, `lev`, `par`, `q`. -/
def Written (a : ℕ) : Prop :=
  (Y.bLab ≤ a ∧ a < Y.bLab + Y.nv) ∨ (Y.bLev ≤ a ∧ a < Y.bLev + Y.nv) ∨
    (Y.bPar ≤ a ∧ a < Y.bPar + Y.nv) ∨ (Y.bQ ≤ a ∧ a < Y.bQ + Y.nv)

/-- **A good layout** for the word bound `W`: the written arrays are pairwise disjoint and
disjoint from the read-only ones, and every address and count stays below `W`. -/
structure Good (W : ℕ) : Prop where
  d1 : ∀ b n, zteoz ∨ ztepa ∨ ztepb ∨
      zteoy ∨ zteox ∨ ztepc →
    Disj b n Y.bLab Y.nv ∧ Disj b n Y.bLev Y.nv ∧ Disj b n Y.bPar Y.nv ∧ Disj b n Y.bQ Y.nv
  d2 : Disj Y.bLab Y.nv Y.bLev Y.nv ∧ Disj Y.bLab Y.nv Y.bPar Y.nv ∧
    Disj Y.bLab Y.nv Y.bQ Y.nv ∧ Disj Y.bLev Y.nv Y.bPar Y.nv ∧ Disj Y.bLev Y.nv Y.bQ Y.nv ∧
    Disj Y.bPar Y.nv Y.bQ Y.nv
  wO : Y.bO + Y.N ≤ W
  wR : Y.bR + Y.N ≤ W
  wV : Y.bV + Y.N ≤ W
  wF : Y.bF + Y.nv ≤ W
  wDB : Y.bDB + Y.N ≤ W
  wVB : Y.bVB + Y.nv ≤ W
  wLab : Y.bLab + Y.nv ≤ W
  wLev : Y.bLev + Y.nv ≤ W
  wPar : Y.bPar + Y.nv ≤ W
  wQ : Y.bQ + Y.nv ≤ W
  wn : Y.nv + 1 ≤ W
  wN : Y.N + 1 ≤ W
variable {Y}

/-- Memories agreeing outside the written arrays read the same rotation system. -/
@[simp] theorem env_nv (m : ℕ → ℕ) : (Y.env m).nv = Y.nv := rfl
theorem env_congr {W : ℕ} (hY : Y.Good W) {m m' : ℕ → ℕ} (h : ∀ a, ¬ Y.Written a → m' a = m a) :
    Y.env m' = Y.env m := by
  have key : ∀ b n, zteoz ∨ ztepa ∨ ztepb ∨
      zteoy ∨ zteox ∨ ztepc →
      view m' b n = view m b n := by
    intro b n hbn
    obtain ⟨h1, h2, h3, h4⟩ := hY.d1 b n hbn
    refine view_congr (fun i hi => h _ ?_)
    unfold Written Disj at *
    omega
  unfold env
  simp_all
end Lay

/-! ## Views of the written arrays after a push -/
section views
variable {Y : Lay} {W : ℕ}

/-- The written arrays of a configuration's memory. -/
def labV (Y : Lay) (m : ℕ → ℕ) : ℕ → ℕ := view m Y.bLab Y.nv
/-- The level array. -/
def levV (Y : Lay) (m : ℕ → ℕ) : ℕ → ℕ := view m Y.bLev Y.nv
/-- The parent array. -/
def parV (Y : Lay) (m : ℕ → ℕ) : ℕ → ℕ := view m Y.bPar Y.nv
/-- The queue array. -/
def qV (Y : Lay) (m : ℕ → ℕ) : ℕ → ℕ := view m Y.bQ Y.nv

/-- The memory after a push. -/
def pushMem (Y : Lay) (m : ℕ → ℕ) (w t L lu e : ℕ) : ℕ → ℕ :=
  upd (upd (upd (upd m (Y.bLab + w) L) (Y.bLev + w) lu) (Y.bPar + w) e) (Y.bQ + t) w
theorem labV_push (hY : Y.Good W) (m : ℕ → ℕ) {w t : ℕ} (hw : w < Y.nv) (ht : t < Y.nv)
    (L lu e : ℕ) :
    labV Y zteao = Function.update (labV Y m) w L := by
  zqpf
  unfold labV pushMem Disj at *
  rw [view_upd_out _ _ _ _ _ by_omega, view_upd_out _ _ _ _ _ by_omega,
    view_upd_out _ _ _ _ _ by_omega, view_upd_in _ _ _ _ _ hw]
theorem levV_push (hY : Y.Good W) (m : ℕ → ℕ) {w t : ℕ} (hw : w < Y.nv) (ht : t < Y.nv)
    (L lu e : ℕ) :
    levV Y zteao = Function.update (levV Y m) w lu := by
  zqpf
  unfold levV pushMem Disj at *
  rw [view_upd_out _ _ _ _ _ by_omega, view_upd_out _ _ _ _ _ by_omega,
    view_upd_in _ _ _ _ _ hw, view_upd_out _ _ _ _ _ by_omega]
theorem parV_push (hY : Y.Good W) (m : ℕ → ℕ) {w t : ℕ} (hw : w < Y.nv) (ht : t < Y.nv)
    (L lu e : ℕ) :
    parV Y zteao = Function.update (parV Y m) w e := by
  zqpf
  unfold parV pushMem Disj at *
  rw [view_upd_out _ _ _ _ _ by_omega, view_upd_in _ _ _ _ _ hw,
    view_upd_out _ _ _ _ _ by_omega, view_upd_out _ _ _ _ _ by_omega]
theorem qV_push (hY : Y.Good W) (m : ℕ → ℕ) {w t : ℕ} (hw : w < Y.nv) (ht : t < Y.nv)
    (L lu e : ℕ) :
    qV Y zteao = Function.update (qV Y m) t w := by
  zqpf
  unfold qV pushMem Disj at *
  rw [view_upd_in _ _ _ _ _ ht, view_upd_out _ _ _ _ _ by_omega,
    view_upd_out _ _ _ _ _ by_omega, view_upd_out _ _ _ _ _ by_omega]

/-- A push writes only the written arrays. -/
theorem pushMem_other (m : ℕ → ℕ) {w t : ℕ} (hw : w < Y.nv) (ht : t < Y.nv) (L lu e : ℕ)
    {a : ℕ} (ha : ¬ Y.Written a) : pushMem Y m w t L lu e a = m a := by
  unfold pushMem Lay.Written at *
  rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
    Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega]
end views

/-! ## Registers and the frame of the search -/

/-- The registers holding the layout, the label, the source and the constant `1`. -/
structure Regs (Y : Lay) (s L : ℕ) (c : Config) : Prop where
  one : c.nreg 130001 = 1
  rO : c.nreg 130100 = Y.bO
  rR : c.nreg 130101 = Y.bR
  rV : c.nreg 130102 = Y.bV
  rF : c.nreg 130103 = Y.bF
  rDB : c.nreg 130104 = Y.bDB
  rVB : c.nreg 130105 = Y.bVB
  rLab : c.nreg 130106 = Y.bLab
  rLev : c.nreg 130107 = Y.bLev
  rPar : c.nreg 130108 = Y.bPar
  rQ : c.nreg 130109 = Y.bQ
  rn : c.nreg 130110 = Y.nv
  rL : c.nreg 130111 = L
  rs : c.nreg 130112 = s

/-- The scratch registers of the search. -/
def Scr (r : ℕ) : Prop := 130120 ≤ r ∧ r ≤ 130130

/-- **The frame of the search** relative to its entry configuration `c0`: only the scratch
registers and the written arrays change. -/
def Fr (Y : Lay) (c0 c : Config) : Prop :=
  (∀ r, ¬ Scr r → c.nreg r = c0.nreg r) ∧ c.rreg = c0.rreg ∧ c.rmem = c0.rmem ∧
    c.output = c0.output ∧ ∀ a, ¬ Y.Written a → c.nmem a = c0.nmem a

/-- Changing only scratch registers keeps the frame. -/
theorem Fr.nreg {Y : Lay} {c0 c : Config} (hf : Fr Y c0 c) {f : ℕ → ℕ}
    (hfr : ∀ r, ¬ Scr r → f r = c.nreg r) : Fr Y c0 { c with nreg := f } :=
  ⟨fun r hr => (hfr r hr).trans ztoaq, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2⟩

/-- The layout registers survive the frame. -/
theorem Regs.fr {Y : Lay} {s L : ℕ} {c0 c : Config} (h : Regs Y s L c0) (hf : Fr Y c0 c) :
    Regs Y s L c := by
  zujab
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  refine ztzv <;>
    (rwa [k _ ztggo])

/-! ## The program -/

/-- Push `w` (address `lab + w` in `130126`): label, level, parent dart, queue entry `t`,
`t := t + 1`. -/
def pushB : Stmt := block [.storeN 130126 130111, .addN 130126 130107 130128,
  .storeN 130126 130129, .addN 130126 130108 130128, .storeN 130126 130124,
  .addN 130126 130109 130121, .storeN 130126 130128, .addN 130121 130121 130001]

/-- Visit `w`: push it unless it is labelled (`lab w < nv`). -/
def visitB : Stmt := .seq (block [.addN 130126 130106 130128, .loadN 130127 130126])
  (.ifLtN 130127 130110 .skip pushB)

/-- An unblocked dart `d`: `w := vert (opp d)`, visit `w` unless it is blocked. -/
def allowB : Stmt := .seq (block [.addN 130126 130100 130124, .loadN 130127 130126,
  .addN 130126 130102 130127, .loadN 130128 130126, .addN 130126 130105 130128,
  .loadN 130127 130126]) (ifNe1 130127 visitB)

/-- The current dart `d`: handle it unless it is blocked. -/
def dartB : Stmt := .seq (block [.addN 130126 130104 130124, .loadN 130127 130126])
  (ifNe1 130127 allowB)

/-- Advance: `d := rot d`, `j := j + 1`. -/
def advB : Stmt := block [.addN 130126 130101 130124, .loadN 130124 130126,
  .addN 130130 130130 130001]

/-- End of the orbit: `done := 1` if `d = first u`. -/
def testB : Stmt :=
  .ifLtN 130124 130123 .skip (.ifLtN 130123 130124 .skip (block [.constN 130125 1]))

/-- One dart of the inner loop. -/
def innerBody : Stmt := .seq dartB (.seq advB testB)

/-- The inner loop: the rotation orbit of `first u`. -/
def innerLoop : Stmt := .whileLtN 130125 130001 innerBody

/-- The head entry: `u := q h`, `lu := lev u + 1`, `d0 := d := first u`, `done := 0`,
`j := 0`. -/
def headB : Stmt := block [.addN 130126 130109 130120, .loadN 130122 130126,
  .addN 130126 130107 130122, .loadN 130129 130126, .addN 130129 130129 130001,
  .addN 130126 130103 130122, .loadN 130123 130126, .copyN 130124 130123, .constN 130125 0,
  .constN 130130 0]

/-- One entry of the queue. -/
def outerBody : Stmt := .seq headB (.seq innerLoop (.instr (.addN 130120 130120 130001)))

/-- The outer loop, while `h < t`. -/
def outerLoop : Stmt := .whileLtN 130120 130121 outerBody

/-- Start: `q 0 := s`, `lab s := L`, `lev s := 0`, `h := 0`, `t := 1`. -/
def initB : Stmt := block [.copyN 130126 130109, .storeN 130126 130112,
  .addN 130126 130106 130112, .storeN 130126 130111, .addN 130126 130107 130112,
  .constN 130127 0, .storeN 130126 130127, .constN 130120 0, .constN 130121 1]

/-- **Breadth-first search.** -/
def bfsStmt : Stmt := .seq initB outerLoop

/-! ## The straight-line pieces -/
section pieces
variable {P : Polygon} {W : ℕ} {Y : Lay} {s L : ℕ}
theorem pushB_exec (hY : Y.Good W) {c : Config} (hw : WordsBounded W c) (hR : Regs Y s L c)
    {w t e lu : ℕ} (hA : c.nreg 130126 = Y.bLab + w) (hW : c.nreg 130128 = w)
    (hT : c.nreg 130121 = t) (hE : c.nreg 130124 = e) (hLU : c.nreg 130129 = lu)
    (hwn : w < Y.nv) (htn : t < Y.nv) :
    ∃ c' k, Exec P W pushB c c' k ∧ k = 8 ∧
      c'.nmem = pushMem Y c.nmem w t L lu e ∧ c'.nreg 130121 = t + 1 ∧
      (∀ r, r ≠ 130126 → r ≠ 130121 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hY.wLev; have := hY.wPar; have := hY.wQ; have := hY.wn
  unfold pushB
  exec_block
  · config_simp; rw [hR.rLev, hW]; omega
  · config_simp; rw [hR.rPar, hW]; omega
  · config_simp; rw [hR.rQ, hT]; omega
  · config_simp; zuohs; omega
  · refine ⟨rfl, ?_, by config_simp; zuohs, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
    · simp only [pushMem, hA, hR.rL, hR.rLev, hW, hLU, hR.rPar, hE, hR.rQ, hT]
    simp_all
end pieces

/-! ## The inner loop -/

/-- **The configuration invariant of the inner loop**: the abstract invariant `InvIn` on the views
of memory, the head vertex `u = q h`, `lu = lev u + 1`, `d0 = first u`, the current dart
`d = rot^[j] d0`, and the flag `done` (`0` while `j < per`, `1` when `j = per`). -/
structure II (Y : Lay) (W s L : ℕ) (lab0 : ℕ → ℕ) (c0 c : Config) : Prop where
  wb : WordsBounded W c
  fr : Fr Y c0 c
  inv : (Y.env c0.nmem).InvIn s L lab0 ztkaa zttse zttvr
    zttxf ztboj ztvho ztjrt
  u : c.nreg 130122 = qV Y c.nmem ztboj
  lu : c.nreg 130129 = levV Y c.nmem zthuj + 1
  d0 : c.nreg 130123 = (Y.env c0.nmem).first zthuj
  d : c.nreg 130124 = (Y.env c0.nmem).rot^[c.nreg 130130] ztbzr
  dn : (c.nreg 130125 = 0 ∧ c.nreg 130130 < per (Y.env c0.nmem).rot Y.N ztbzr) ∨
    (c.nreg 130125 = 1 ∧ c.nreg 130130 = per (Y.env c0.nmem).rot Y.N ztbzr)

/-- The state after handling one dart (relative to the registers `R` and memory `m` at the start
of `dartB`, with head index `h`, dart counter `j` and head vertex `u`). -/
def DPost (Y : Lay) (W s L : ℕ) (lab0 : ℕ → ℕ) (c0 : Config) (h j u : ℕ) (R : ℕ → ℕ)
    (m : ℕ → ℕ) (c1 : Config) : Prop :=
  WordsBounded W c1 ∧ Fr Y c0 c1 ∧
    (Y.env c0.nmem).InvIn s L lab0 ztocr (levV Y c1.nmem) (parV Y c1.nmem)
      (qV Y c1.nmem) h (c1.nreg 130121) ztl ∧
    (∀ r, r ≠ 130121 → r ≠ 130126 → r ≠ 130127 → r ≠ 130128 → c1.nreg r = R r) ∧
    (∀ i, i < R 130121 → qV Y c1.nmem i = qV Y m i) ∧ R 130121 ≤ c1.nreg 130121 ∧
    levV Y c1.nmem u = levV Y m u
section inner
variable {P : Polygon} {W : ℕ} {Y : Lay} {s L : ℕ} {lab0 : ℕ → ℕ} {c0 : Config}

/-- Reading a read-only array of the entry memory through the frame. -/
theorem Fr.read {c : Config} (hY : Y.Good W) (hf : Fr Y c0 c) {b n i : ℕ}
    (hb : zteoz ∨ ztepa ∨ ztepb ∨
      zteoy ∨ zteox ∨ ztepc) (hi : i < n) :
    c.nmem ztbcn = view c0.nmem b n i := by
  zuccg

  unfold Lay.Written Disj at *
  omega

/-- Visiting `w = head e` for an unblocked dart `e` to an unblocked vertex: skip it if labelled,
push it otherwise. -/
theorem visitB_exec (hY : Y.Good W) (hR0 : Regs Y s L c0) (hp : (Y.env c0.nmem).Pre s L lab0)
    {c c' : Config} (hI : II Y W s L lab0 c0 c) (hjp : c.nreg 130130 <
      per (Y.env c0.nmem).rot Y.N ztbzr)
    (hw' : WordsBounded W c') (hf' : Fr Y c0 c') (hm' : c'.nmem = c.nmem)
    (hr' : ∀ r, r ≠ 130126 → r ≠ 130127 → r ≠ 130128 → c'.nreg r = c.nreg r)
    (hdb : (Y.env c0.nmem).db ztccs ≠ 1)
    (hW' : c'.nreg 130128 = (Y.env c0.nmem).head ztccs)
    (hvb : (Y.env c0.nmem).vb ztxcc ≠ 1) :
    ∃ c1 k, Exec P W visitB c' c1 k ∧ k ≤ 20 ∧
      DPost Y W s L lab0 c0 ztboj ztjrt zthuj c.nreg c.nmem c1 := by
  zulix
  have hIn := hI.inv
  have hht := hIn.hlt
  have hun : ztlxp := by rw [hI.u]; exact hIn.inv.qlt _ hht
  have he : (Y.env c0.nmem).rot^[c.nreg 130130] ((Y.env c0.nmem).first
      ztwsp) = c.nreg 130124 := by zunnq
  have hjp' : c.nreg 130130 < per (Y.env c0.nmem).rot (Y.env c0.nmem).N
      ztbaom := by
    zugxq
  have hfirst : ztdrd := hp.ok.first_lt _ hun
  have heN : ztlxq := by
    zubih
  have hve : (Y.env c0.nmem).vert ztccs = qV Y c.nmem ztboj := by
    rw [← he, hp.ok.vert_iterate _ (by zuoqq; tauto), hp.ok.vert_first _
      (by zuoqq; simp_all)]
  have hwn : ztoqc :=
    hp.ok.vert_lt _ (hp.ok.opp_lt _ heN)
  have hvis := hIn.visited_iff hp heN hdb hve hvb
  have := hY.wLab
  unfold visitB
  refine seqX (K₂ := 18) (R₁ := fun c2 => WordsBounded W c2 ∧ c2.nmem = c.nmem ∧
      c2.nreg 130126 = Y.bLab + (Y.env c0.nmem).head ztccs ∧
      c2.nreg 130127 = labV Y c.nmem ztxcc ∧
      ztcjl ∧
      c2.nreg 130128 = (Y.env c0.nmem).head ztccs ∧ c2.rreg = c'.rreg ∧
      c2.rmem = c'.rmem ∧ c2.output = c'.output) ?_ ?_
  · exec_block
    · zuoht; omega
    · refine ⟨by_omega, by_omega, hm', by config_simp; zuoht, ?_, fun r h1 h2 h3 => ?_,
        by simp_all, rfl, rfl, rfl⟩
      · config_simp; rw [hR'.rLab, hW', hm', labV, view_lt hwn]
      simp_all
  · rintro c2 ⟨hw2, hm2, hA2, hX2, hr2, hW2, hrr2, hrm2, ho2⟩
    have hf2 : Fr Y c0 c2 := by
      refine ⟨fun r hr => ?_, hrr2.trans hf'.2.1, hrm2.trans hf'.2.2.1, ho2.trans hf'.2.2.2.1,
        fun a ha => by rw [hm2]; exact hI.fr.2.2.2.2 a ha⟩
      have h6 : ztppp := fun h => hr ztya
      have h7 : r ≠ 130127 := fun h => hr ztya
      have h8 : r ≠ 130128 := fun h => hr ztya
      rw [hr2 r h6 h7 h8]; exact hI.fr.1 r hr
    have hR2 := hR0.fr hf2
    by_cases hv : c2.nreg 130127 < c2.nreg 130110
    · -- already labelled: skip
      refine ⟨c2, 0 + 1, .ifLtN_true hv ztgbs, by_omega, hw2, hf2, ?_,
        by simp_all, by_simp_all,
        by simp_all, by rw [hm2]⟩
      rw [hm2, hr2 _ by_decide by_decide by_decide]
      refine hIn.skip' hjp' he ztbaez
      zuijk
      simp_all
    · -- not labelled: push
      zuijk
      have hnot : ∀ i, i < c.nreg 130121 →
          qV Y c.nmem i ≠ (Y.env c0.nmem).head ztccs := by
        simp_all
      have htn := hIn.inv.t_lt_of_notMem hwn hnot
      obtain ⟨c1, k1, e1, hk1, hm1, hT1, hr1, hrr1, hrm1, ho1⟩ := pushB_exec hY hw2 hR2
        hA2 hW2 by_simp_all
        ztlib
        ztlib hwn htn
      refine ⟨c1, k1 + 2, .ifLtN_false (by rw [hX2, hR2.rn]; exact hv) e1, by_omega,
        e1.wb_right, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · refine ⟨fun r hr => ?_, hrr1.trans hf2.2.1, hrm1.trans hf2.2.2.1, ho1.trans hf2.2.2.2.1,
          fun a ha => ?_⟩
        · have h6 : ztppp := fun h => hr ztkth
          have h1 : r ≠ 130121 := fun h => hr ztkth
          rw [hr1 r h6 h1]; exact hf2.1 r hr
        · rw [hm1, pushMem_other _ hwn htn _ _ _ ha]; exact hf2.2.2.2.2 a ha
      · rw [hm1, hT1, hm2, labV_push hY _ hwn htn, levV_push hY _ hwn htn, parV_push hY _ hwn htn,
          qV_push hY _ hwn htn]
        refine hIn.push' hp hjp' he rfl ?_ hdb hvb hnot
        rw [hI.lu, hI.u]
      · grind
      · zug
        rw [hm1, hm2, qV_push hY _ hwn htn, Function.update_of_ne by_omega]
      · omega
      · rw [hm1, hm2, levV_push hY _ hwn htn, Function.update_of_ne]
        zudii
        exact hnot _ hht (by rw [← hI.u, heq])

/-- The frame of a configuration that differs from `c` only in the scratch registers `130126 …
130128`. -/
theorem fr_scratch {c c1 : Config} (hf : Fr Y c0 c) (hm : c1.nmem = c.nmem)
    (hr : ∀ r, r ≠ 130126 → r ≠ 130127 → r ≠ 130128 → c1.nreg r = c.nreg r)
    (hrr : c1.rreg = c.rreg) (hrm : c1.rmem = c.rmem) (ho : c1.output = c.output) :
    Fr Y c0 c1 := by
  refine ⟨fun r hr' => ?_, hrr.trans hf.2.1, hrm.trans hf.2.2.1, ho.trans hf.2.2.2.1,
    fun a ha => by zvmwi; exact hf.2.2.2.2 a ha⟩
  have h6 : ztppp := fun h => hr' ztya
  have h7 : r ≠ 130127 := fun h => hr' ztya
  have h8 : r ≠ 130128 := fun h => hr' ztya
  rw [hr r h6 h7 h8]; exact hf.1 r hr'

/-- A skipped dart: nothing but scratch registers changed. -/
theorem dpost_skip (_hp : (Y.env c0.nmem).Pre s L lab0) {c c1 : Config}
    (hI : II Y W s L lab0 c0 c)
    (hjp : c.nreg 130130 < per (Y.env c0.nmem).rot Y.N ztbzr)
    (hw1 : WordsBounded W c1) (hf1 : Fr Y c0 c1) (hm : c1.nmem = c.nmem)
    (hr : ∀ r, r ≠ 130126 → r ≠ 130127 → r ≠ 130128 → c1.nreg r = c.nreg r)
    (hcase : (Y.env c0.nmem).db ztccs = 1 ∨
      (Y.env c0.nmem).vb ztxcc = 1) :
    DPost Y W s L lab0 c0 ztboj ztjrt zthuj c.nreg c.nmem c1 := by
  have he : (Y.env c0.nmem).rot^[c.nreg 130130] ((Y.env c0.nmem).first
      ztwsp) = c.nreg 130124 := by zunnq
  have hjp' : c.nreg 130130 < per (Y.env c0.nmem).rot (Y.env c0.nmem).N
      ztbaom := by
    zugxq
  refine ⟨hw1, hf1, ?_, by_simp_all, by_simp_all,
    by simp_all, by zvmwi⟩
  rw [hm, hr _ by_decide by_decide by_decide]
  zuklb
  · exact hI.inv.skip' hjp' he zteg
  · exact hI.inv.skip' hjp' he by_omega

/-- An unblocked dart: read its head and its flag, visit the head unless it is blocked. -/
theorem allowB_exec (hY : Y.Good W) (hR0 : Regs Y s L c0) (hp : (Y.env c0.nmem).Pre s L lab0)
    {c c' : Config} (hI : II Y W s L lab0 c0 c) (hjp : c.nreg 130130 <
      per (Y.env c0.nmem).rot Y.N ztbzr)
    (hw' : WordsBounded W c') (hf' : Fr Y c0 c') (hm' : c'.nmem = c.nmem)
    (hr' : ∀ r, r ≠ 130126 → r ≠ 130127 → r ≠ 130128 → c'.nreg r = c.nreg r)
    (hdb : (Y.env c0.nmem).db ztccs ≠ 1) :
    ∃ c1 k, Exec P W allowB c' c1 k ∧ k ≤ 30 ∧
      DPost Y W s L lab0 c0 ztboj ztjrt zthuj c.nreg c.nmem c1 := by
  zulix
  zumg

  have heN : ztlxq := by
    zubih
  have hoN : (Y.env c0.nmem).opp _ < Y.N := hp.ok.opp_lt _ heN
  have hwn : ztoqc := hp.ok.vert_lt _ hoN
  have hD : c'.nreg 130124 = c.nreg 130124 := by_simp_all
  have r1 : c'.nmem _ = (Y.env c0.nmem).opp _ :=
    Fr.read hY hf' by_simp_all heN
  have r2 : c'.nmem _ =
      (Y.env c0.nmem).head _ :=
    Fr.read hY hf' by_omega hoN
  have r3 : c'.nmem _ =
      (Y.env c0.nmem).vb _ :=
    Fr.read hY hf' by_omega hwn
  have := hY.wO; have := hY.wV; have := hY.wVB
  unfold allowB
  refine seqX (K₂ := 24) (R₁ := fun c2 => WordsBounded W c2 ∧ c2.nmem = c.nmem ∧
      c2.nreg 130127 = (Y.env c0.nmem).vb ztxcc ∧
      c2.nreg 130128 = (Y.env c0.nmem).head ztccs ∧
      ztcjl ∧
      c2.rreg = c'.rreg ∧ c2.rmem = c'.rmem ∧ c2.output = c'.output) ?_ ?_
  · exec_block
    · rw [hR'.rO, hD]; omega
    · config_simp; rw [hR'.rV, hR'.rO, hD, r1]; omega
    · config_simp; rw [hR'.rVB, hR'.rV, hR'.rO, hD, r1, r2]; omega
    · refine ⟨by_omega, by_omega, hm', ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
      · config_simp; rw [hR'.rVB, hR'.rV, hR'.rO, hD, r1, r2, r3]
      · config_simp; rw [hR'.rV, hR'.rO, hD, r1, r2]
      simp_all
  · rintro c2 ⟨hw2, hm2, hX2, hW2, hr2, hrr2, hrm2, ho2⟩
    have hf2 := fr_scratch hI.fr hm2 hr2 (hrr2.trans (hf'.2.1.trans hI.fr.2.1.symm))
      (hrm2.trans (hf'.2.2.1.trans hI.fr.2.2.1.symm))
      (ho2.trans (hf'.2.2.2.1.trans hI.fr.2.2.2.1.symm))
    zuhzn
    refine weakenX (ifNe1_exec (K := 20) hw2 hone2 130127 ztefb ztcng)
      by_omega ztb
    · zuktk
      exact visitB_exec hY hR0 hp hI hjp hw2 hf2 hm2 hr2 hdb hW2 hne
    · zuktj
      exact dpost_skip hp hI hjp hw2 hf2 hm2 hr2 (Or.inr heq)

/-- **One dart** of the inner loop (before the advance): cost `≤ 36`. -/
theorem dartB_exec (hY : Y.Good W) (hR0 : Regs Y s L c0) (hp : (Y.env c0.nmem).Pre s L lab0)
    {c : Config} (hI : II Y W s L lab0 c0 c) (hjp : c.nreg 130130 <
      per (Y.env c0.nmem).rot Y.N ztbzr) :
    ∃ c1 k, Exec P W dartB c c1 k ∧ k ≤ 36 ∧
      DPost Y W s L lab0 c0 ztboj ztjrt zthuj c.nreg c.nmem c1 := by
  zuliv
  zumg

  have heN : ztlxq := by
    zubih
  have r1 : c.nmem _ = (Y.env c0.nmem).db _ :=
    Fr.read hY hI.fr by_omega heN
  have := hY.wDB
  zudpm
  unfold dartB
  refine seqX (K₂ := 34) (R₁ := fun c2 => WordsBounded W c2 ∧ c2.nmem = c.nmem ∧
      c2.nreg 130127 = (Y.env c0.nmem).db ztccs ∧
      ztcjl ∧
      c2.rreg = c.rreg ∧ c2.rmem = c.rmem ∧ c2.output = c.output) ?_ ?_
  · exec_block
    · rw [hR.rDB]; omega
    · refine ⟨by_omega, by_omega, rfl, by config_simp; rw [hR.rDB, r1], fun r h1 h2 h3 => ?_, rfl,
        rfl, rfl⟩
      simp_all
  · rintro c2 ⟨hw2, hm2, hX2, hr2, hrr2, hrm2, ho2⟩
    have hf2 := fr_scratch hI.fr hm2 hr2 hrr2 hrm2 ho2
    zuhzn
    refine weakenX (ifNe1_exec (K := 30) hw2 hone2 130127 ztefb ztcng)
      by_omega ztb
    · zuktk
      exact allowB_exec hY hR0 hp hI hjp hw2 hf2 hm2 hr2 hne
    · zuktj
      exact dpost_skip hp hI hjp hw2 hf2 hm2 hr2 (Or.inl heq)

/-- **One iteration of the inner loop**: handle the current dart, advance, test the end of the
orbit.  Cost `≤ 48`. -/
theorem innerBody_exec (hY : Y.Good W) (hR0 : Regs Y s L c0) (hp : (Y.env c0.nmem).Pre s L lab0)
    {c : Config} (hI : II Y W s L lab0 c0 c) (hdn : c.nreg 130125 = 0) :
    ∃ c' k, Exec P W innerBody c c' k ∧ k ≤ 48 ∧ II Y W s L lab0 c0 c' ∧
      c'.nreg 130120 = c.nreg 130120 ∧ c'.nreg 130122 = c.nreg 130122 ∧
      c'.nreg 130123 = c.nreg 130123 ∧ c'.nreg 130129 = c.nreg 130129 ∧
      c'.nreg 130130 = c.nreg 130130 + 1 ∧
      ztbtd ∧
      c.nreg 130121 ≤ c'.nreg 130121 ∧
      (c'.nreg 130125 = 0 ∨ c'.nreg 130130 = per (Y.env c0.nmem).rot Y.N ztbzr) := by
  have hjp : c.nreg 130130 < per (Y.env c0.nmem).rot Y.N ztbzr := by
    rcases hI.dn with h | h
    · omega
    · omega
  zumg

  have hd0N : c.nreg 130123 < Y.N := by rw [hI.d0]; omega
  have heN : ztlxq := by
    zubih
  have hperN : per (Y.env c0.nmem).rot Y.N _ ≤ Y.N := per_le hp.ok.injOn hd0N
  have := hY.wR; have := hY.wN
  unfold innerBody
  refine seqX (K₂ := 12) (dartB_exec hY hR0 hp hI hjp) ?_
  rintro c1 ⟨hw1, hf1, hIn1, hr1, hq1, ht1, hl1⟩
  have hR1 := hR0.fr hf1
  have hD1 : c1.nreg 130124 = c.nreg 130124 := by_simp_all
  have hJ1 : c1.nreg 130130 = c.nreg 130130 := by_simp_all
  have rd : c1.nmem _ = (Y.env c0.nmem).rot _ :=
    Fr.read hY hf1 by_simp_all heN
  have hrotN : (Y.env c0.nmem).rot _ < Y.N := hp.ok.rot_lt _ heN
  refine seqX (K₂ := 9) (R₁ := fun c2 => WordsBounded W c2 ∧ c2.nmem = c1.nmem ∧
      c2.nreg 130124 = (Y.env c0.nmem).rot ztccs ∧
      c2.nreg 130130 = c.nreg 130130 + 1 ∧
      (∀ r, r ≠ 130124 → r ≠ 130126 → r ≠ 130130 → c2.nreg r = c1.nreg r) ∧
      c2.rreg = c1.rreg ∧ c2.rmem = c1.rmem ∧ c2.output = c1.output) ?_ ?_
  · unfold advB
    exec_block
    · rw [hR1.rR, hD1]; omega
    · config_simp; zuohu; omega
    · refine ⟨by_omega, by_omega, rfl, by config_simp; rw [hR1.rR, hD1, rd],
        by config_simp; zuohu, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
      simp_all
  · rintro c2 ⟨hw2, hm2, hD2, hJ2, hr2, hrr2, hrm2, ho2⟩
    have hd02 : c2.nreg 130123 = c.nreg 130123 := by
      simp_all
    -- the facts common to both outcomes of the test
    have hiter : (Y.env c0.nmem).rot ztccs =
        (Y.env c0.nmem).rot^[c.nreg 130130 + 1] ztbzr := by
      rw [hI.d, Function.iterate_succ_apply']
    have key : ∀ c3 : Config, WordsBounded W c3 → c3.nmem = c2.nmem → c3.rreg = c2.rreg →
        c3.rmem = c2.rmem → c3.output = c2.output →
        (∀ r, r ≠ 130125 → c3.nreg r = c2.nreg r) →
        ((c3.nreg 130125 = 0 ∧ c.nreg 130130 + 1 < per (Y.env c0.nmem).rot Y.N ztbzr) ∨
          (c3.nreg 130125 = 1 ∧
            c.nreg 130130 + 1 = per (Y.env c0.nmem).rot Y.N ztbzr)) →
        II Y W s L lab0 c0 c3 ∧
        c3.nreg 130120 = c.nreg 130120 ∧ c3.nreg 130122 = c.nreg 130122 ∧
        c3.nreg 130123 = c.nreg 130123 ∧ c3.nreg 130129 = c.nreg 130129 ∧
        c3.nreg 130130 = c.nreg 130130 + 1 ∧
        (∀ i, i < c.nreg 130121 → qV Y c3.nmem i = qV Y c.nmem i) ∧
        c.nreg 130121 ≤ c3.nreg 130121 ∧
        (c3.nreg 130125 = 0 ∨ c3.nreg 130130 = per (Y.env c0.nmem).rot Y.N ztbzr) := by
      intro c3 hw3 hm3 hrr3 hrm3 ho3 hr3 hdn3
      have g : ∀ r, r ≠ 130124 → r ≠ 130125 → r ≠ 130126 → r ≠ 130127 → r ≠ 130128 →
          r ≠ 130130 → r ≠ 130121 → c3.nreg r = c.nreg r := by
        grind
      have e120 := g 130120 by_decide by_decide by_decide by_decide by_decide
        by_decide by_decide
      have e122 := g 130122 by_decide by_decide by_decide by_decide by_decide
        by_decide by_decide
      have e123 := g 130123 by_decide by_decide by_decide by_decide by_decide
        by_decide by_decide
      have e129 := g 130129 by_decide by_decide by_decide by_decide by_decide
        by_decide by_decide
      have e130 : c3.nreg 130130 = c.nreg 130130 + 1 := by_grind
      have e121 : c3.nreg 130121 = c1.nreg 130121 := by
        grind
      have hf3 : Fr Y c0 c3 := by
        refine ⟨fun r hr => ?_, hrr3.trans (hrr2.trans hf1.2.1), hrm3.trans (hrm2.trans hf1.2.2.1),
          ho3.trans (ho2.trans hf1.2.2.2.1), fun a ha => by zuohv; exact hf1.2.2.2.2 a ha⟩
        have a1 : r ≠ 130124 := fun h => hr ztya
        have a2 : r ≠ 130125 := fun h => hr ztya
        have a3 : ztppp := fun h => hr ztya
        have a6 : r ≠ 130130 := fun h => hr ztya
        rw [hr3 r a2, hr2 r a1 a3 a6]; exact hf1.1 r hr
      have hqh : qV Y c1.nmem _ = qV Y c.nmem _ := hq1 _ hht
      refine ⟨⟨hw3, hf3, ?_, ?_, ?_, ?_, ?_, ?_⟩, e120, e122, e123, e129, e130, ?_, ?_, ?_⟩
      · grind
      · rw [e122, hm3, hm2, e120, hqh]; exact hI.u
      · rw [e129, e122, hm3, hm2, hl1]; exact hI.lu
      · rw [e123, e122]; exact hI.d0
      · grind
      · grind
      · grind
      · omega
      omega
    have hdn2 : c2.nreg 130125 = 0 := by
      grind
    unfold testB
    by_cases hlt : c2.nreg 130124 < c2.nreg 130123
    · refine ⟨c2, 0 + 1, .ifLtN_true hlt ztgbs, by_omega, key c2 hw2 rfl rfl rfl rfl
        by_omega ztoxi⟩
      rcases Nat.lt_or_ge _ _
        with h | h
      · zubh
      · zqph
        rw [hD2, hd02, hiter, heq, iterate_per (N := Y.N) hp.ok.injOn hd0N] at hlt
        omega
    · by_cases hgt : c2.nreg 130123 < c2.nreg 130124
      · refine ⟨c2, 0 + 1 + 2, .ifLtN_false hlt (.ifLtN_true hgt ztgbs), by_omega,
          key c2 hw2 rfl rfl rfl rfl by_omega ztoxi⟩
        rcases Nat.lt_or_ge _ _
          with h | h
        · zubh
        · zqph
          rw [hD2, hd02, hiter, heq, iterate_per (N := Y.N) hp.ok.injOn hd0N] at hgt
          omega
      · have heqd : c2.nreg 130124 = c2.nreg 130123 := by_omega
        have hper : ztxte := by
          rw [hD2, hd02, hiter] at heqd
          zuct
          exact iterate_ne_of_lt_per (N := Y.N) hp.ok.injOn hd0N by_omega by_omega heqd
        have e3 := Exec.constN (P := P) hw2 130125 1 by_omega
        refine ⟨_, 1 + 2 + 2, .ifLtN_false hlt (.ifLtN_false hgt (Exec.block_cons e3
          (Exec.block_nil e3.wb_right))), by_omega, key _ e3.wb_right rfl rfl rfl rfl
          ztlou (Or.inr ⟨by_simp, hper⟩)⟩

/-- **The inner loop** over the rotation orbit of `first u`: cost `≤ 50 (deg u + 1) + 2`; at
the end the whole orbit is processed. -/
theorem innerLoop_exec (hY : Y.Good W) (hR0 : Regs Y s L c0)
    (hp : (Y.env c0.nmem).Pre s L lab0) {c : Config} (hI : II Y W s L lab0 c0 c)
    (hdn : c.nreg 130125 = 0) (hj : c.nreg 130130 = 0) :
    ∃ c' k, Exec P W innerLoop c c' k ∧
      k ≤ 50 * (per (Y.env c0.nmem).rot Y.N ztbzr + 1) + 2 ∧
      II Y W s L lab0 c0 c' ∧ c'.nreg 130125 = 1 ∧
      c'.nreg 130130 = per (Y.env c0.nmem).rot Y.N ztbzr ∧
      c'.nreg 130120 = c.nreg 130120 ∧ c'.nreg 130122 = c.nreg 130122 ∧
      c'.nreg 130123 = c.nreg 130123 ∧
      ztbtd ∧
      c.nreg 130121 ≤ c'.nreg 130121 := by
  set pr := per (Y.env c0.nmem).rot Y.N _ with hpr
  obtain ⟨c', k, e, ⟨hI', h120, h122, h123, hq', ht'⟩, htest, hk⟩ :=
    Exec.whileLtN_potential (P := P) (W := W) (a := 130125) (b := 130001) (body := innerBody)
    (fun c' => II Y W s L lab0 c0 c' ∧ c'.nreg 130120 = c.nreg 130120 ∧
      c'.nreg 130122 = c.nreg 130122 ∧ c'.nreg 130123 = c.nreg 130123 ∧
      ztbtd ∧
      c.nreg 130121 ≤ c'.nreg 130121)
    (fun c' => 50 * (pr + 1 - c'.nreg 130130 - c'.nreg 130125)) (fun c' h => h.1.wb)
    (fun c1 ⟨hI1, g120, g122, g123, gq, gt⟩ htest => by
      have hone := (hR0.fr hI1.fr).one
      have hdn1 : c1.nreg 130125 = 0 := by_omega
      have hjp1 : c1.nreg 130130 < pr := by
        rcases hI1.dn with h | h
        · simp_all
        · omega
      obtain ⟨c2, k2, e2, hk2, hI2, f120, f122, f123, f129, f130, fq, ft, fdn⟩ :=
        innerBody_exec hY hR0 hp hI1 hdn1
      refine ⟨c2, k2, e2, by_grind, ?_⟩
      omega) ⟨hI, rfl, rfl, rfl,
      fun _ _ => rfl, le_rfl⟩
  have hone := (hR0.fr hI'.fr).one
  have hdn' : c'.nreg 130125 = 1 ∧ c'.nreg 130130 = pr := by
    rcases hI'.dn with h | h
    · omega
    simp_all
  refine ⟨c', k, e, by_omega, hI', hdn'.1, hdn'.2, h120, h122, h123, hq', ht'⟩
end inner

/-! ## The outer loop -/

/-- **The configuration invariant of the outer loop.** -/
structure OI (Y : Lay) (W s L : ℕ) (lab0 : ℕ → ℕ) (c0 c : Config) : Prop where
  wb : WordsBounded W c
  fr : Fr Y c0 c
  inv : (Y.env c0.nmem).Inv s L lab0 ztkaa zttse zttvr
    zttxf ztboj ztvho
section outer
variable {P : Polygon} {W : ℕ} {Y : Lay} {s L : ℕ} {lab0 : ℕ → ℕ} {c0 : Config}

/-- The head entry: load `u = q h`, `lev u + 1`, `first u`; start the inner loop. -/
theorem headB_exec (hY : Y.Good W) (hR0 : Regs Y s L c0) (hp : (Y.env c0.nmem).Pre s L lab0)
    {c : Config} (hI : OI Y W s L lab0 c0 c) (hht : c.nreg 130120 < c.nreg 130121) :
    ∃ c1 k, Exec P W headB c c1 k ∧ k = 10 ∧ II Y W s L lab0 c0 c1 ∧ c1.nreg 130125 = 0 ∧
      c1.nreg 130130 = 0 ∧ c1.nreg 130120 = c.nreg 130120 ∧ c1.nreg 130121 = c.nreg 130121 ∧
      c1.nmem = c.nmem ∧
      c1.nreg 130123 = (Y.env c0.nmem).first ztwsp := by
  zuliv
  zudpm
  have htn : c.nreg 130121 ≤ Y.nv := hI.inv.tn
  zuiap
  have hlev := hI.inv.lev_le _ hht
  have rq : c.nmem (Y.bQ + c.nreg 130120) = qV Y c.nmem ztboj := by
    rw [qV, view_lt by_omega]
  have rl : c.nmem (Y.bLev + qV Y c.nmem ztboj) =
      levV Y c.nmem ztwsp := by rw [levV, view_lt hun]
  have rf : c.nmem _ =
      (Y.env c0.nmem).first _ :=
    Fr.read hY hI.fr by_omega hun
  have hfN : ztdrd := hp.ok.first_lt _ hun
  have := hY.wQ; have := hY.wLev; have := hY.wF; have := hY.wn
  unfold headB
  exec_block
  · simp only [hR.rQ]; omega
  · config_simp; simp only [hR.rQ, hR.rLev, rq]; omega
  · config_simp; zunjj; omega
  · config_simp; simp only [hR.rQ, hR.rF, rq]; omega
  · omega
  · omega
  · refine ⟨rfl, ztdix, by config_simp, by config_simp,
      by config_simp, by config_simp, rfl, by config_simp; zuncm⟩
    · exact Fr.nreg hI.fr (fun r hr => by
        unfold Scr at hr; zumwj; grind)
    · config_simp; exact hI.inv.start hht
    · config_simp; simp only [hR.rQ, rq]
    · config_simp; zunjj
    · config_simp; zuncm
    · simp
    · config_simp; left
      zuncm
      exact per_pos hp.ok.injOn hfN

/-- **One entry of the queue**: cost `≤ 50 deg u + 63`. -/
theorem outerBody_exec (hY : Y.Good W) (hR0 : Regs Y s L c0) (hp : (Y.env c0.nmem).Pre s L lab0)
    {c : Config} (hI : OI Y W s L lab0 c0 c) (hht : c.nreg 130120 < c.nreg 130121) :
    ∃ c' k, Exec P W outerBody c c' k ∧
      k ≤ 50 * (Y.env c0.nmem).deg ztwsp + 63 ∧
      OI Y W s L lab0 c0 c' ∧ c'.nreg 130120 = c.nreg 130120 + 1 ∧
      ztbtd := by
  obtain ⟨c1, k1, e1, hk1, hII1, hdn1, hj1, h120, h121, hm1, h123⟩ :=
    headB_exec (P := P) hY hR0 hp hI hht
  obtain ⟨c2, k2, e2, hk2, hII2, hdn2, hj2, g120, g122, g123, gq, gt⟩ :=
    innerLoop_exec (P := P) hY hR0 hp hII1 hdn1 hj1
  zuiap
  have hper : per (Y.env c0.nmem).rot Y.N (c1.nreg 130123) =
      (Y.env c0.nmem).deg ztwsp := by
    rw [h123]; exact hp.ok.per_first hun
  -- the inner invariant at the end of the orbit
  have hfin : (Y.env c0.nmem).Inv s L lab0 zttrs (levV Y c2.nmem) (parV Y c2.nmem)
      (qV Y c2.nmem) (c2.nreg 130120 + 1) (c2.nreg 130121) := by
    refine hII2.inv.finish hp ?_
    rw [hj2, ← hII2.u, g122, hII1.d0]
    rfl
  have hone := (hR0.fr hII2.fr).one
  have hw2 := hII2.wb
  have htn : c2.nreg 130121 ≤ Y.nv := hII2.inv.inv.tn
  have hht2 := hII2.inv.hlt
  have := hY.wn
  have e3 := Exec.addN (P := P) hw2 130120 130120 130001 by_omega
  refine ⟨_, k1 + ztcvw, .seq e1 ztbpc, ?_, ⟨e3.wb_right, ?_, ?_⟩, ?_, ?_⟩
  · omega
  · exact Fr.nreg hII2.fr (fun r hr => by
      unfold Scr at hr; zumwj; grind)
  · simp_all
  · simp_all
  simp_all

/-- **The outer loop**: from the invariant, the loop ends with `h = t`; the cost plus
`70 (nv - t) + 50 (N - Σ_{i<t} deg (q i))` at the end is at most the same quantity at the start
plus `2`. -/
theorem outerLoop_exec (hY : Y.Good W) (hR0 : Regs Y s L c0) (hp : (Y.env c0.nmem).Pre s L lab0)
    {c : Config} (hI : OI Y W s L lab0 c0 c) :
    ∃ c' k, Exec P W outerLoop c c' k ∧
      k + (70 * (Y.nv - c'.nreg 130120) + 50 * (Y.N - ∑ i ∈ Finset.range (c'.nreg 130120),
        (Y.env c0.nmem).deg ztrus)) ≤
      70 * ztrkl + 50 * (Y.N - ∑ i ∈ Finset.range ztboj,
        (Y.env c0.nmem).deg ztrut) + 2 ∧
      OI Y W s L lab0 c0 c' ∧ c'.nreg 130120 = c'.nreg 130121 := by
  obtain ⟨c', k, e, hI', htest, hk⟩ := whileLtN_pot (P := P) (W := W) (a := 130120)
    (b := 130121) (body := outerBody) (OI Y W s L lab0 c0)
    (fun c => 70 * ztrkl + 50 * (Y.N - ∑ i ∈ Finset.range ztboj,
      (Y.env c0.nmem).deg ztrut)) (fun c h => h.wb)
    (fun c1 hI1 htest => by
      obtain ⟨c2, k2, e2, hk2, hI2, h120, hq⟩ := outerBody_exec (P := P) hY hR0 hp hI1 htest
      refine ⟨c2, k2, e2, hI2, ?_⟩
      have htn : c1.nreg 130121 ≤ Y.nv := hI1.inv.tn
      have hsum : ∑ i ∈ Finset.range (c2.nreg 130120), (Y.env c0.nmem).deg (qV Y c2.nmem i) =
          ∑ i ∈ Finset.range ztvkf, (Y.env c0.nmem).deg (qV Y c1.nmem i) +
            (Y.env c0.nmem).deg (qV Y c1.nmem ztvkf) := by
        rw [h120, Finset.sum_range_succ, hq _ htest]
        zucr
        refine Finset.sum_congr rfl ztdp
        grind
      have hle := hI2.inv.sum_deg_le hp.ok hI2.inv.ht
      rw [hsum] at hle ⊢
      change _ ≤ Y.N at hle
      omega) hI
  refine ⟨c', k, e, hk, hI', ?_⟩
  have := hI'.inv.ht
  omega
end outer

/-! ## The whole search -/
section main
variable {P : Polygon} {W : ℕ} {Y : Lay} {s L : ℕ} {c0 : Config}

/-- **Breadth-first search on the RAM.**  From a configuration whose registers hold a good
layout, the label `L` and the source `s` (`Regs`), with the precondition `Pre` (a well-formed
rotation system, `s` unblocked, `L < nv`, the sentinel `nv` in `lab` at every vertex reachable
from `s`), `bfsStmt` runs in at most `70 t + 50 Σ_{i<t} deg (q i) + 11` steps (`t` the
number of reached vertices), changes only the scratch
registers and the arrays `lab`, `lev`, `par`, `q` (`Fr`), and ends with the invariant `Inv` at
`h = t`: the queue holds exactly the vertices reachable from `s` (`Env.Inv.reach_iff`), they are
labelled `L`, the other labels are unchanged, and the levels and parents form a breadth-first
tree (`Env.Inv.par`, `Env.Inv.lev_head_le`). -/
theorem bfs_exec (hY : Y.Good W) (hR0 : Regs Y s L c0)
    (hp : (Y.env c0.nmem).Pre s L ztkab) (hw : WordsBounded W c0) :
    ∃ c' k, Exec P W bfsStmt c0 c' k ∧
      k ≤ 70 * c'.nreg 130121 + 50 * ∑ i ∈ Finset.range (c'.nreg 130121),
        (Y.env c0.nmem).deg ztrus + 11 ∧
      OI Y W s L ztkab c0 c' ∧ c'.nreg 130120 = c'.nreg 130121 := by
  have hsn : s < Y.nv := hp.s_lt
  have := hY.wLab; have := hY.wLev; have := hY.wQ; have := hY.wn
  have hne1 : Y.bQ ≠ Y.bLab + s := by
    have := hY.d2.2.2.1; unfold Disj at this; omega
  have hne2 : Y.bQ ≠ Y.bLev + s := by
    have := hY.d2.2.2.2.2.1; unfold Disj at this; omega
  have hne3 : Y.bLab + s ≠ Y.bLev + s := by
    have := hY.d2.1; unfold Disj at this; omega
  unfold bfsStmt
  have hinit : ∃ c1 k1, Exec P W initB c0 c1 k1 ∧ k1 ≤ 9 ∧
      OI Y W s L ztkab c0 c1 ∧ c1.nreg 130120 = 0 := by
    unfold initB
    exec_block
    · config_simp; rw [hR0.rLab, hR0.rs]; omega
    · config_simp; rw [hR0.rLev, hR0.rs]; omega
    · omega
    · omega
    · omega
    · refine ⟨by_omega, ⟨by_omega, ztsu, ?_⟩, by config_simp⟩
      · unfold Scr at hr; zumwj; grind
      · simp only [Machine.upd_apply, hR0.rQ, hR0.rLab, hR0.rLev, hR0.rs]
        zumrc
        grind
      · simp only [Machine.upd_same, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
          Machine.upd_other, hR0.rQ, hR0.rLab, hR0.rLev, hR0.rs, hR0.rL]
        have hq : qV Y ztccb =
            Function.update (qV Y c0.nmem) 0 s := by
          unfold qV
          rw [view_upd_out _ _ _ _ _ (by have := hY.d2.2.2.2.2.1; unfold Disj at this; omega),
            view_upd_out _ _ _ _ _ (by have := hY.d2.2.2.1; unfold Disj at this; omega)]
          exact view_upd_in c0.nmem Y.bQ Y.nv 0 s by_omega
        have hl : labV Y ztccb =
            Function.update ztkab s L := by
          unfold labV
          rw [view_upd_out _ _ _ _ _ (by have := hY.d2.1; unfold Disj at this; omega),
            view_upd_in _ _ _ _ _ hsn,
            view_upd_out _ _ _ _ _ (by have := hY.d2.2.2.1; unfold Disj at this; omega)]
        have hv : levV Y ztccb s = 0 := by
          unfold levV
          rw [view_lt hsn, Machine.upd_same]
        refine Env.Inv.init hp by_simp_all (fun v hv' => ?_) hv
        zudug
        grind
  obtain ⟨c1, k1, e1, hk1, hI1, h0⟩ := hinit
  obtain ⟨c', k, e, hk, hI', ht⟩ := outerLoop_exec (P := P) hY hR0 hp hI1
  refine ⟨c', k1 + k, .seq e1 e, ?_, hI', ht⟩
  grind
end main
end
end Chazelle.Core.Cluster
end
section
set_option hygiene false
local macro "zqbih" : tactic => `(tactic| have hup : ztmtu := by zuncn)
local macro "zqbii" : tactic => `(tactic| (congr 1
                                           refine Finset.sum_congr (Finset.filter_true_of_mem ztesh) by_omega))
set_option hygiene true

/-!
# WP-I, part 8: preorder intervals of a tree in breadth-first order

A rooted tree on the nodes `[0, n)` given as a breadth-first search leaves it (`BTree`): the
queue `q` (a bijection of `[0, n)`, the root `q 0` first) and the parent `par h` of every other
node, which comes earlier in the queue.

* `BTree.Anc g h`: `g` is on the path from `h` to the root; `sub g` (the descendants),
  `sub_eq` (`sub g = {g} ⊔ ⋃ sub c` over the children), hence `card_sub` (the size recursion).
* **Sizes** (`SizeInv`): processing the queue backwards and adding the size of every node to its
  parent computes `|sub g|`.
* **Preorder** (`PreInv`): processing the queue forwards, every node takes the next free slot of
  its parent and advances it by its size.  At the end (`PreInv.final`) the preorder `pre` is
  injective and the descendants of `g` are exactly the nodes whose preorder lies in
  `[pre g, pre g + |sub g|)` (`PreInv.anc_iff`).
-/
namespace Chazelle.Core.Cluster
@[expose] public section
structure BTree where
  /-- number of nodes -/
  n : ℕ
  /-- the queue -/
  q : ℕ → ℕ
  /-- the parent of a non-root node -/
  par : ℕ → ℕ
namespace BTree
variable (R : BTree)

/-- Well-formedness: the queue is a bijection of `[0, n)` and parents come earlier. -/
structure OK : Prop where
  n_pos : 0 < R.n
  q_lt : ∀ i, i < R.n → R.q i < R.n
  q_inj : ∀ i, i < R.n → ∀ j, j < R.n → R.q i = R.q j → i = j
  par_lt : ∀ i, 0 < i → i < R.n → ∃ j, j < i ∧ R.q j = R.par ztbed

/-- The root. -/
def root : ℕ := R.q 0

/-- The parent, the root being its own parent. -/
def up (h : ℕ) : ℕ := if h = R.root then h else R.par h

/-- `g` is an ancestor of `h` (reflexive). -/
def Anc (g h : ℕ) : Prop := ∃ m : ℕ, R.up^[m] h = g

/-- The descendants of `g`. -/
noncomputable def sub (g : ℕ) : Finset ℕ :=
  haveI := Classical.decPred ztpbl
  (Finset.range R.n).filter ztpbl

/-- The children of `g`. -/
noncomputable def ch (g : ℕ) : Finset ℕ :=
  (Finset.range R.n).filter (fun h => h ≠ R.root ∧ R.par h = g)
variable {R}
theorem OK.surj (hR : R.OK) {h : ℕ} (hh : h < R.n) : ∃ i, i < R.n ∧ R.q i = h := by
  classical
  have hsub : (Finset.range R.n).image R.q ⊆ Finset.range R.n := by
    zuh
    zucny
    exact Finset.mem_range.mpr (hR.q_lt i ztmaz)
  have hcard : ((Finset.range R.n).image R.q).card = R.n := by
    zugbx
    zubgs
    exact hR.q_inj i ztmaz j ztuyn hij
  zukbw
  have : h ∈ (Finset.range R.n).image R.q := by_simp_all
  zufyk
  zubfo
open Classical in
/-- The position of a node in the queue. -/
noncomputable def pos (h : ℕ) : ℕ := if hh : ∃ i, i < R.n ∧ R.q i = h then Nat.find hh else 0
theorem OK.pos_spec (hR : R.OK) {h : ℕ} (hh : h < R.n) : R.pos h < R.n ∧ R.q ztqce = h := by
  classical
  have hex := hR.surj hh
  unfold pos
  zulpq
  exact Nat.find_spec hex
theorem OK.pos_q (hR : R.OK) {i : ℕ} (hi : i < R.n) : R.pos ztbed = i := by
  have := hR.pos_spec ztjxl
  exact hR.q_inj _ this.1 i hi this.2
theorem OK.root_lt (hR : R.OK) : R.root < R.n := hR.q_lt 0 hR.n_pos
theorem OK.pos_root (hR : R.OK) : R.pos R.root = 0 := hR.pos_q hR.n_pos

/-- The parent of a non-root node is a node earlier in the queue. -/
theorem OK.par_spec (hR : R.OK) {h : ℕ} (hh : h < R.n) (hr : h ≠ R.root) :
    R.par h < R.n ∧ R.pos ztqcd < R.pos h := by
  obtain ⟨hp, hq⟩ := hR.pos_spec hh
  have h0 : ztuju := by
    rcases Nat.eq_zero_or_pos ztqce with h0 | h0
    · exact absurd (by rw [← hq, h0]; rfl) hr
    omega
  obtain ⟨j, hj, hqj⟩ := hR.par_lt ztqce h0 hp
  zvnck at hqj
  rw [← hqj, hR.pos_q by_omega]
  exact ⟨hR.q_lt j by_omega, hj⟩
theorem OK.up_lt (hR : R.OK) {h : ℕ} (hh : h < R.n) : R.up h < R.n := by
  unfold up
  zulsu
  · exact hh
  · exact (hR.par_spec hh hr).1
theorem OK.iterate_up_lt (hR : R.OK) (m : ℕ) {h : ℕ} (hh : h < R.n) : R.up^[m] h < R.n := by
  induction m generalizing h with
  | zero => exact hh
  | succ m ih => rw [Function.iterate_succ_apply]; exact ih ztmku

/-- Ancestors come no later in the queue. -/
theorem OK.pos_le_of_anc (hR : R.OK) {g h : ℕ} (hh : h < R.n) (hgh : R.Anc g h) :
    R.pos g ≤ R.pos h := by
  zuicy
  induction m generalizing h with
  | zero => exact le_rfl
  | succ m ih =>
    zujgm
    refine (ih ztmku).trans ?_
    unfold up
    zulsu
    · omega
    · exact (hR.par_spec hh hr).2.le
theorem anc_refl (g : ℕ) : R.Anc g g := ztkil
theorem anc_up (h : ℕ) : R.Anc ztmcf h := ztufq
theorem Anc.trans {a b c : ℕ} (h1 : R.Anc a b) (h2 : R.Anc b c) : R.Anc a c := by
  obtain ⟨m1, rfl⟩ := h1
  obtain ⟨m2, rfl⟩ := h2
  exact ⟨m1 + m2, by zunri⟩

/-- Anti-symmetry of ancestry. -/
theorem OK.anc_antisymm (hR : R.OK) {g h : ℕ} (hh : h < R.n) (hg : g < R.n) (h1 : R.Anc g h)
    (h2 : R.Anc h g) : g = h := by
  have := hR.pos_le_of_anc hh h1
  have := hR.pos_le_of_anc hg h2
  have e1 := (hR.pos_spec hg).2
  have e2 := (hR.pos_spec hh).2
  grind

/-- The root is an ancestor of every node. -/
theorem OK.anc_root (hR : R.OK) {h : ℕ} (hh : h < R.n) : R.Anc R.root h := by
  induction hp : R.pos h using Nat.strong_induction_on generalizing h with
  | _ p ih =>
    zufrj
    · tauto
    · zugpp
      have := ih _ by_omega hpn rfl
      refine this.trans ?_
      have : ztmtu := by zuncn
      zvnnr; exact anc_up h

/-- Stepping up from a proper descendant. -/
theorem anc_iff_up {g h : ℕ} (hgh : g ≠ h) : R.Anc g h ↔ R.Anc g ztmcf := by
  constructor
  · zukon
    rcases m with _ | m
    · simp_all
    tauto
  · zukon
    exact ⟨m + 1, by_simp_all⟩

/-- **The descendants of `g`**: `g` and the descendants of its children, disjointly. -/
theorem OK.sub_eq (hR : R.OK) {g : ℕ} (hg : g < R.n) :
    R.sub g = insert g ((R.ch g).biUnion R.sub) := by
  classical
  ext h
  simp only [sub, ch, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hh, hgh⟩
    by_cases heq : h = g
    · omega
    · right
      -- the child of `g` on the path from `h`
      obtain ⟨m, hm⟩ := hgh
      have key : ∀ m h, h < R.n → R.up^[m] h = g → h ≠ g →
          ∃ c, (c < R.n ∧ c ≠ R.root ∧ R.par c = g) ∧ h < R.n ∧ R.Anc c h := by
        intro m
        induction m with
        | zero => intro h _ hm hne; exact absurd hm hne
        | succ m ih =>
          intro h hh hm hne
          rw [Function.iterate_succ_apply] at hm
          have hr : ztsiv := by
            zuibu
            have : R.up^[m] ztmcf = R.up h := by
              rw [show R.up h = h by simp [up, hr]]
              exact Function.iterate_fixed (by zuncn) m
            rw [this, show R.up h = h by simp [up, hr]] at hm
            omega
          zqbih
          by_cases hpg : R.par h = g
          · exact ⟨h, by_omega, hh, anc_refl h⟩
          · obtain ⟨c, hc, -, hch⟩ := ih ztmcf ztmku hm by_omega
            exact ⟨c, hc, hh, hch.trans (anc_up h)⟩
      grind
  · rintro (rfl | ⟨c, ⟨hc, hcr, hpc⟩, hh, hch⟩)
    · tauto
    · refine ⟨hh, Anc.trans ?_ hch⟩
      have : R.up c = g := by zunxn
      zvnnr; exact anc_up c

/-- Descendants of distinct children are disjoint. -/
theorem OK.sub_disjoint (hR : R.OK) {g c c' : ℕ} (hc : c ∈ R.ch g) (hc' : c' ∈ R.ch g)
    (hne : c ≠ c') : Disjoint (R.sub c) (R.sub c') := by
  classical
  zuzt
  intro h h1 h2
  simp only [sub, ch, Finset.mem_filter, Finset.mem_range] at h1 h2 hc hc'
  -- both `c` and `c'` are ancestors of `h`, so one is an ancestor of the other
  have key : ∀ m m' h, R.up^[m] h = c → R.up^[m'] h = c' → R.Anc c c' ∨ R.Anc c' c := by
    intro m m' h hm hm'
    zuiel
    · right; refine ⟨m' - m, ?_⟩
      zuezx
    · left; refine ⟨m - m', ?_⟩
      zuezx
  obtain ⟨m, hm⟩ := h1.2
  obtain ⟨m', hm'⟩ := h2.2
  -- a child of `g` that is an ancestor of another child of `g` is that child
  have hup : ∀ x, x < R.n → x ≠ R.root → R.par x = g → R.up x = g := fun x _ hxr hpx => by
    simp [up, hxr, hpx]
  have hchild : ∀ x y, x < R.n → y < R.n → x ≠ R.root → y ≠ R.root → R.par x = g →
      R.par y = g → R.Anc x y → x = y := by
    intro x y hx hy hxr hyr hpx hpy hxy
    by_contra hxy'
    have h1 := (anc_iff_up hxy').mp hxy
    rw [hup y hy hyr hpy] at h1
    have h2 : R.Anc g x := by rw [← hup x hx hxr hpx]; exact anc_up x
    have hgn : g < R.n := by rw [← hpx]; exact (hR.par_spec hx hxr).1
    have hxg := hR.anc_antisymm hgn hx h1 h2
    have hl := hR.par_spec hx hxr
    simp_all
  rcases key m m' h hm hm' with h3 | h3
  · grind
  · grind

/-- A child comes after its parent in the queue. -/
theorem OK.pos_ch (hR : R.OK) {g c : ℕ} (hc : c ∈ R.ch g) : R.pos g < R.pos c := by
  zughk
  have := hR.par_spec hc.1 hc.2.1
  simp_all

/-- A node is not a descendant of its own children. -/
theorem OK.notMem_sub_ch (hR : R.OK) {g c : ℕ} (hc : c ∈ R.ch g) : g ∉ R.sub c := by
  intro hg
  simp only [sub, Finset.mem_filter, Finset.mem_range] at hg
  have := hR.pos_le_of_anc hg.1 hg.2
  have := hR.pos_ch hc
  omega

/-- **The size recursion**: `|sub g| = 1 + Σ_{c child of g} |sub c|`. -/
theorem OK.card_sub (hR : R.OK) {g : ℕ} (hg : g < R.n) :
    (R.sub g).card = 1 + ∑ c ∈ R.ch g, (R.sub c).card := by
  classical
  rw [hR.sub_eq hg, Finset.card_insert_of_notMem, Finset.card_biUnion]
  · omega
  · zukjc
    exact hR.sub_disjoint hc hc' hne
  · simp only [Finset.mem_biUnion, not_exists, not_and]
    zung
    exact hR.notMem_sub_ch hc

/-- The root's subtree is everything. -/
theorem OK.card_sub_root (hR : R.OK) : (R.sub R.root).card = R.n := by
  classical
  have : R.sub R.root = Finset.range R.n := by
    ext h
    simp only [sub, Finset.mem_filter, Finset.mem_range, and_iff_left_iff_imp]
    exact hR.anc_root
  rw [this, Finset.card_range]

/-! ## Sizes -/

/-- **The invariant of the size loop** (queue entries from `i` on processed): the size array holds
`1 + Σ |sub c|` over the processed children. -/
def SizeInv (sz : ℕ → ℕ) (i : ℕ) : Prop :=
  ∀ g, g < R.n → sz g = 1 + ∑ c ∈ (R.ch g).filter ztesg, (R.sub c).card

/-- The start: all sizes `1`. -/
theorem SizeInv.init {sz : ℕ → ℕ} (h : ∀ g, g < R.n → sz g = 1) (hR : R.OK) :
    R.SizeInv sz R.n := by
  zubrf
  have hempty : (R.ch g).filter (fun c => R.n ≤ R.pos c) = ∅ := by
    refine Finset.filter_false_of_mem ztesh
    zughk
    have := (hR.pos_spec hc.1).1
    omega
  simp_all

/-- At an entry, the size array holds the true size. -/
theorem SizeInv.eq_card (hR : R.OK) {sz : ℕ → ℕ} {i : ℕ} (hS : R.SizeInv sz ztg)
    (hi : i < R.n) : sz ztbed = (R.sub ztbed).card := by
  rw [hS _ ztjxl, hR.card_sub ztjxl]
  zqbii
  have := hR.pos_ch hc
  rw [hR.pos_q hi] at this
  omega

/-- **One step of the size loop**: at the entry `i ≥ 1`, add its size to its parent. -/
theorem SizeInv.step (hR : R.OK) {sz : ℕ → ℕ} {i : ℕ} (hS : R.SizeInv sz ztg)
    (hi0 : 0 < i) (hi : i < R.n) :
    R.SizeInv (Function.update sz ztwxc (sz ztwxc + sz ztbed)) i := by
  classical
  have hq := hR.q_lt i hi
  have hr : ztplc := by
    intro h; have := hR.q_inj i hi 0 hR.n_pos h; omega
  have hpos : R.pos _ = i := hR.pos_q hi
  zubrf
  have hch : ∀ c, c ∈ (R.ch g).filter ztesg ↔
      c ∈ (R.ch g).filter ztlnx ∨ (c = R.q i ∧ R.par ztbed = g) := by
    intro c
    simp only [Finset.mem_filter, ch, Finset.mem_range]
    constructor
    · rintro ⟨⟨hc, hcr, hpc⟩, hic⟩
      by_cases hci : R.pos c = i
      · right
        have := (hR.pos_spec hc).2
        simp_all
      omega
    grind
  by_cases hpg : R.par ztbed = g
  · subst hpg
    rw [Function.update_self, hS _ hg, hS.eq_card hR hi]
    have hset : (R.ch ztwxc).filter ztesg =
        insert ztbed ((R.ch ztwxc).filter ztlnx) := by
      grind
    grind
  · rw [Function.update_of_ne (Ne.symm hpg), hS _ hg]
    simp_all

/-- At the end of the size loop, the sizes are the true sizes. -/
theorem SizeInv.final (hR : R.OK) {sz : ℕ → ℕ} (hS : R.SizeInv sz 1) {g : ℕ} (hg : g < R.n) :
    sz g = (R.sub g).card := by
  zuhll
  zqbii
  have := hR.pos_ch hc
  omega
theorem mem_ch {g x : ℕ} : x ∈ R.ch g ↔ x < R.n ∧ x ≠ R.root ∧ R.par x = g := by
  simp [ch]

/-- A subtree has at most `n` nodes. -/
theorem card_sub_le (g : ℕ) : (R.sub g).card ≤ R.n := by
  classical
  unfold sub
  zubfo

/-- During the size loop, sizes are at most the true sizes. -/
theorem SizeInv.le (hR : R.OK) {sz : ℕ → ℕ} {i : ℕ} (hS : R.SizeInv sz i) {g : ℕ}
    (hg : g < R.n) : sz g ≤ (R.sub g).card := by
  zuhll
  have := Finset.sum_le_sum_of_subset (f := fun c => (R.sub c).card)
    (Finset.filter_subset ztesg (R.ch g))
  omega

/-! ## Preorder -/

/-- **The invariant of the preorder loop** (queue entries before `i` processed): the next free
slot of a processed node follows its processed children; a processed non-root node has its
interval `[pre c, pre c + |sub c|)` inside the used part of its parent's; processed siblings have
disjoint intervals. -/
structure PreInv (pre slot : ℕ → ℕ) (i : ℕ) : Prop where
  i_pos : 0 < i
  i_le : i ≤ R.n
  root : pre R.root = 0
  slotEq : ∀ j, j < i → slot ztbkk =
    pre ztbkk + 1 + ∑ c ∈ (R.ch ztbkk).filter (fun c => R.pos c < i), (R.sub c).card
  nest : ∀ j, 0 < j → j < i →
    pre ztbafj + 1 ≤ pre ztbkk ∧
      pre ztbkk + (R.sub ztbkk).card ≤ slot ztbafj
  disj : ∀ j j', 0 < j → j < i → 0 < j' → j' < i → j ≠ j' → R.par ztbkk = R.par zthry →
    pre ztbkk + (R.sub ztbkk).card ≤ pre zthry ∨
      pre zthry + (R.sub zthry).card ≤ pre ztbkk
  bound : ∀ j, j < i → pre ztbkk + (R.sub ztbkk).card ≤ R.n

/-- The start: the root takes preorder `0` and next slot `1`. -/
theorem PreInv.init (hR : R.OK) {pre slot : ℕ → ℕ} (hp : pre R.root = 0) (hs : slot R.root = 1) :
    R.PreInv pre slot 1 := by
  classical
  refine ⟨by_omega, hR.n_pos, hp, fun j hj => ?_, by_grind,
    by simp_all, fun j hj => ?_⟩
  swap
  · zubkk

    show pre R.root + (R.sub R.root).card ≤ R.n
    rw [hp, hR.card_sub_root]; omega
  zubkk

  have hempty : (R.ch (R.q 0)).filter (fun c => R.pos c < 1) = ∅ := by
    refine Finset.filter_false_of_mem ztesh
    have := hR.pos_ch hc
    omega
  rw [hempty, Finset.sum_empty]
  show slot R.root = pre R.root + 1 + 0
  rw [hp, hs]

/-- **One step of the preorder loop**: the entry `i ≥ 1` takes the next free slot of its parent,
which advances by its size; its own next free slot follows it. -/
theorem PreInv.step (hR : R.OK) {pre slot : ℕ → ℕ} {i : ℕ} (hP : R.PreInv pre slot i)
    (hi : i < R.n) :
    R.PreInv (Function.update pre ztbed (slot ztwxc))
      (Function.update (Function.update slot ztwxc
        (slot ztwxc + (R.sub ztbed).card)) (R.q i) (slot (R.par (R.q i)) + 1))
      ztg := by
  classical
  set c := R.q i with hc_def
  set p := R.par c with hp_def
  have hcn : c < R.n := hR.q_lt i hi
  have hcr : c ≠ R.root := by
    intro h; have := hR.q_inj i hi 0 hR.n_pos h; have := hP.i_pos; omega
  have hposc : R.pos c = i := hR.pos_q hi
  obtain ⟨hpn, hpp⟩ := hR.par_spec hcn hcr
  rw [hposc, ← hp_def] at hpp
  rw [← hp_def] at hpn
  have hpq : R.q _ = p := (hR.pos_spec hpn).2
  have hpc : p ≠ c := by_grind
  -- facts about processed entries
  have hne : ∀ j, j < i → R.q j ≠ c := by
    intro j hj h; have := hR.q_inj j by_omega i hi h; omega
  have pre_old : ∀ j, j < i → Function.update pre c ztqwo _ = pre _ :=
    fun j hj => Function.update_of_ne (hne j hj) _ _
  have hchild_pos : ∀ x, x ∈ R.ch c → i < R.pos x := by
    intro x hx; have := hR.pos_ch hx; omega
  -- the slot of the parent covers the processed children
  have hslot_p := hP.slotEq _ hpp
  rw [hpq] at hslot_p
  refine ⟨by_omega, by_omega, ?_, fun j hj => ?_, fun j hj0 hj => ?_,
    fun j j' hj0 hj hj0' hj' hjj' hpar => ?_, fun j hj => ?_⟩
  rotate_right
  · -- the bound
    zuevf
    · rw [pre_old j hj]; exact hP.bound j hj
    · rw [hji, Function.update_self]
      have hb := hP.bound _ hpp
      rw [hpq] at hb
      have hcp : c ∈ R.ch p := mem_ch.mpr by_omega
      have hsub : insert c ((R.ch p).filter zthhg) ⊆ R.ch p := by
        grind
      have hsum := Finset.sum_le_sum_of_subset (f := fun x => (R.sub x).card) hsub
      rw [Finset.sum_insert by_simp_all] at hsum
      have hcs := hR.card_sub hpn
      grind
  · zuoqs; exact hP.root
  · -- slots
    zuevf
    · have hqc := hne j hj
      rw [pre_old j hj, Function.update_of_ne hqc]
      by_cases hjp : R.q j = p
      · have hset : (R.ch ztbkk).filter ztlox =
            insert c ((R.ch ztbkk).filter zthhg) := by
          zumx
          rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_filter, mem_ch]
          constructor
          · rintro ⟨⟨hx, hxr, hxp⟩, hxi⟩
            zujdl
            · omega
            · left
              have := (hR.pos_spec hx).2
              simp_all
          grind
        grind
      · have hset : (R.ch ztbkk).filter ztlox =
            (R.ch ztbkk).filter zthhg := by
          zumx
          rw [Finset.mem_filter, Finset.mem_filter]
          constructor
          · rintro ⟨hx, hxi⟩
            refine zthne
            zujdl
            · omega
            · exfalso
              obtain ⟨hxn, -, hxp⟩ := mem_ch.mp hx
              have := (hR.pos_spec hxn).2
              simp_all
          grind
        rw [hset, Function.update_of_ne hjp]
        exact hP.slotEq j hj
    simp_all
  · -- nesting
    zuevf
    · obtain ⟨n1, n2⟩ := hP.nest j hj0 hj
      have hqp : R.par ztbkk ≠ c := by
        zuq
        have := (hR.par_spec (hR.q_lt j by_omega) (fun h' => by
          have := hR.q_inj j by_omega 0 hR.n_pos h'; omega)).2
        rw [h, hposc, hR.pos_q by_omega] at this
        omega
      grind
    simp_all
  · -- disjointness
    have hcase : ∀ j j', 0 < j → j < i → j' = i → R.par ztbkk = R.par zthry →
        Function.update pre c ztqwo ztbkk + (R.sub ztbkk).card ≤
          Function.update pre c ztqwo zthry := by
      intro j j' hj0 hj hj' hpar
      subst hj'
      rw [pre_old j hj, Function.update_self]
      have := (hP.nest j hj0 hj).2
      simp_all
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hji <;>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj' | hji'
    · rw [pre_old j hj, pre_old j' hj']
      exact hP.disj j j' hj0 hj hj0' hj' hjj' hpar
    · grind
    · grind
    omega
section final
variable {pre slot : ℕ → ℕ}
theorem one_le_card_sub {g : ℕ} (hg : g < R.n) : 1 ≤ (R.sub g).card := by
  classical
  refine Finset.card_pos.mpr ⟨g, ?_⟩
  simp only [sub, Finset.mem_filter, Finset.mem_range]
  exact ⟨hg, anc_refl g⟩

/-- At the end, every next free slot is at the end of the interval. -/
theorem PreInv.slot_final (hR : R.OK) (hP : R.PreInv pre slot R.n) {g : ℕ} (hg : g < R.n) :
    slot g = pre g + (R.sub g).card := by
  obtain ⟨hpn, hpq⟩ := hR.pos_spec hg
  have := hP.slotEq _ hpn
  rw [hpq] at this
  rw [this, hR.card_sub hg]
  have : (R.ch g).filter (fun c => R.pos c < R.n) = R.ch g :=
    Finset.filter_true_of_mem (fun c hc => (hR.pos_spec (mem_ch.mp hc).1).1)
  grind

/-- At the end, the interval of a non-root node is inside its parent's, after the parent. -/
theorem PreInv.nest_final (hR : R.OK) (hP : R.PreInv pre slot R.n) {c : ℕ} (hc : c < R.n)
    (hcr : c ≠ R.root) :
    pre ztqcc + 1 ≤ pre c ∧ pre c + (R.sub c).card ≤ pre ztqcc + (R.sub ztqcc).card := by
  obtain ⟨hpn, hpq⟩ := hR.pos_spec hc
  have h0 : ztujt := by
    rcases Nat.eq_zero_or_pos ztvcy with h | h
    · exact absurd (by rw [← hpq, h]; rfl) hcr
    omega
  have := hP.nest _ h0 hpn
  rw [hpq, hP.slot_final hR (hR.par_spec hc hcr).1] at this
  omega

/-- Ancestors have enclosing intervals. -/
theorem PreInv.anc_le (hR : R.OK) (hP : R.PreInv pre slot R.n) {g h : ℕ} (hh : h < R.n)
    (hgh : R.Anc g h) :
    pre g ≤ pre h ∧ pre h + (R.sub h).card ≤ pre g + (R.sub g).card := by
  zuicy
  induction m generalizing h with
  | zero => exact by_simp_all
  | succ m ih =>
    zujgm
    obtain ⟨i1, i2⟩ := ih ztmku
    zufrj
    · rw [show R.up h = h by simp [up, hr]] at i1 i2 ⊢
      omega
    · zqbih
      rw [hup] at i1 i2 ⊢
      obtain ⟨n1, n2⟩ := hP.nest_final hR hh hr
      omega

/-- A proper ancestor comes strictly earlier in preorder. -/
theorem PreInv.anc_lt (hR : R.OK) (hP : R.PreInv pre slot R.n) {g h : ℕ} (hh : h < R.n)
    (hgh : R.Anc g h) (hne : g ≠ h) : pre g < pre h := by
  have hgn : g < R.n := by obtain ⟨m, rfl⟩ := hgh; exact hR.iterate_up_lt m hh
  have hr : ztsiv := by
    zuibu
    exact hne (hR.anc_antisymm hh hgn hgh (hr ▸ hR.anc_root hgn))
  have h1 := (anc_iff_up hne).mp hgh
  rw [show R.up h = R.par h by simp [up, hr]] at h1
  have := (hP.anc_le hR (hR.par_spec hh hr).1 h1).1
  have := (hP.nest_final hR hh hr).1
  omega

/-- The child of `p` on the path to a proper descendant `g`. -/
theorem OK.exists_ch_anc (hR : R.OK) {p g : ℕ} (hg : g < R.n) (hpg : R.Anc p g) (hne : p ≠ g) :
    ∃ c, c ∈ R.ch p ∧ R.Anc c g := by
  classical
  have hpn : p < R.n := by obtain ⟨m, rfl⟩ := hpg; exact hR.iterate_up_lt m hg
  have hmem : g ∈ R.sub p := by
    simp only [sub, Finset.mem_filter, Finset.mem_range]; simp_all
  rw [hR.sub_eq hpn, Finset.mem_insert, Finset.mem_biUnion] at hmem
  rcases hmem with h | ⟨c, hc, hgc⟩
  · omega
  · simp only [sub, Finset.mem_filter, Finset.mem_range] at hgc
    grind

/-- The key step of the disjointness of unrelated nodes (the later one's parent). -/
theorem PreInv.disj_step (hR : R.OK) (hP : R.PreInv pre slot R.n) {g h : ℕ} (hg : g < R.n)
    (hh : h < R.n) (hgh : ¬ R.Anc g h) (hhg : ¬ R.Anc h g) (hpos : R.pos g < R.pos h)
    (ih : ∀ g' h', g' < R.n → h' < R.n → R.pos g' + R.pos h' < R.pos g + R.pos h →
      ¬ R.Anc g' h' → ¬ R.Anc h' g' →
        pre g' + (R.sub g').card ≤ pre h' ∨ pre h' + (R.sub h').card ≤ pre g') :
    pre g + (R.sub g).card ≤ pre h ∨ pre h + (R.sub h).card ≤ pre g := by
  have hr : ztsiv := fun hr => hhg (hr ▸ hR.anc_root hg)
  zugpp
  zqbih
  have hph : R.Anc _ h := hup ▸ anc_up h
  obtain ⟨nh1, nh2⟩ := hP.nest_final hR hh hr
  zully
  have hσg := one_le_card_sub hg
  by_cases hgp : R.Anc g ztqcd
  · exact absurd (hgp.trans hph) hgh
  by_cases hpg : R.Anc ztqcd g
  · have hpne : R.par h ≠ g := by_grind
    obtain ⟨c, hc, hcg⟩ := hR.exists_ch_anc hg hpg hpne
    obtain ⟨hcn, hcr, hcp⟩ := mem_ch.mp hc
    have hch : c ≠ h := by_grind
    -- `c` and `h` are distinct children of `p`
    obtain ⟨pcn, pcq⟩ := hR.pos_spec hcn
    obtain ⟨phn, phq⟩ := hR.pos_spec hh
    have hc0 : ztujt := by
      rcases Nat.eq_zero_or_pos ztvcy with h0 | h0
      · exact absurd (by rw [← pcq, h0]; rfl) hcr
      omega
    have hh0 : ztuju := by_omega
    have hd := hP.disj _ _ hc0 pcn hh0 phn
      by_grind by_simp_all
    rw [pcq, phq] at hd
    obtain ⟨a1, a2⟩ := hP.anc_le hR hg hcg
    omega
  grind

/-- **Unrelated nodes have disjoint intervals.** -/
theorem PreInv.disj_unrel (hR : R.OK) (hP : R.PreInv pre slot R.n) :
    ∀ g h, g < R.n → h < R.n → ¬ R.Anc g h → ¬ R.Anc h g →
      pre g + (R.sub g).card ≤ pre h ∨ pre h + (R.sub h).card ≤ pre g := by
  intro g h
  induction hs : R.pos g + R.pos h using Nat.strong_induction_on generalizing g h with
  | _ s ih =>
    intro hg hh hgh hhg
    have ih' : ∀ g' h', g' < R.n → h' < R.n → R.pos g' + R.pos h' < R.pos g + R.pos h →
        ¬ R.Anc g' h' → ¬ R.Anc h' g' →
          pre g' + (R.sub g').card ≤ pre h' ∨ pre h' + (R.sub h').card ≤ pre g' :=
      by grind
    have hgne : g ≠ h := fun e => hgh (e ▸ anc_refl g)
    have hposne : R.pos g ≠ R.pos h := by
      zuchf
      exact hgne (by rw [← (hR.pos_spec hg).2, ← (hR.pos_spec hh).2, e])
    rcases Nat.lt_or_gt_of_ne hposne with hlt | hlt
    · exact hP.disj_step hR hg hh hgh hhg hlt ih'
    · have := hP.disj_step hR hh hg hhg hgh hlt by_grind
      omega

/-- **Preorder intervals**: at the end, `h` is a descendant of `g` iff `pre h` lies in
`[pre g, pre g + |sub g|)`; preorders are below `n`. -/
theorem PreInv.anc_iff (hR : R.OK) (hP : R.PreInv pre slot R.n) {g h : ℕ} (hg : g < R.n)
    (hh : h < R.n) : R.Anc g h ↔ pre g ≤ pre h ∧ pre h < pre g + (R.sub g).card := by
  zully
  constructor
  · intro hgh
    have := hP.anc_le hR hh hgh
    omega
  · zubf
    by_contra hgh
    by_cases hhg : R.Anc h g
    · have hne : h ≠ g := by_grind
      have := hP.anc_lt hR hg hhg hne
      omega
    · have := hP.disj_unrel hR g h hg hh hgh hhg
      omega

/-- Preorders are below `n`. -/
theorem PreInv.pre_lt (hR : R.OK) (hP : R.PreInv pre slot R.n) {h : ℕ} (hh : h < R.n) :
    pre h < R.n := by
  have := (hP.anc_iff hR hR.root_lt hh).mp (hR.anc_root hh)
  rw [hP.root, hR.card_sub_root] at this
  omega
end final
end BTree
end
end Chazelle.Core.Cluster
end
namespace Chazelle.Core.Cluster
open Machine Machine.Stmt Programs
@[expose] public section
def fillBody : Stmt := block [.addN 130141 130106 130140, .storeN 130141 130110,
  .addN 130140 130140 130001]

/-- Fill the label array with the sentinel. -/
def fillLoop : Stmt := .whileLtN 130140 130110 fillBody

/-- The search from `v` with label `v`. -/
def searchV : Stmt := .seq (block [.copyN 130111 130140, .copyN 130112 130140]) bfsStmt

/-- Search from `v` unless it is labelled. -/
def unlabB : Stmt := .seq ztjop
  (.ifLtN 130142 130110 .skip searchV)

/-- One vertex of the driver. -/
def drvBody : Stmt := .seq ztjoo
  (.seq (ifNe1 130142 unlabB) ztnam)

/-- The driver loop. -/
def drvLoop : Stmt := .whileLtN 130140 130110 drvBody

/-- **Component labelling.** -/
def labelStmt : Stmt :=
  .seq ztotl (.seq fillLoop (.seq ztotl drvLoop))

/-! ## Registers and frame -/

/-- The layout registers of the labelling (all those of `Regs` but the label and the source). -/
structure Regs0 (Y : Lay) (c : Config) : Prop where
  one : c.nreg 130001 = 1
  rO : c.nreg 130100 = Y.bO
  rR : c.nreg 130101 = Y.bR
  rV : c.nreg 130102 = Y.bV
  rF : c.nreg 130103 = Y.bF
  rDB : c.nreg 130104 = Y.bDB
  rVB : c.nreg 130105 = Y.bVB
  rLab : c.nreg 130106 = Y.bLab
  rLev : c.nreg 130107 = Y.bLev
  rPar : c.nreg 130108 = Y.bPar
  rQ : c.nreg 130109 = Y.bQ
  rn : c.nreg 130110 = Y.nv
theorem Regs0.regs {Y : Lay} {c : Config} (h : Regs0 Y c) {s L : ℕ} (hL : c.nreg 130111 = L)
    (hs : c.nreg 130112 = s) : Regs Y s L c :=
  ⟨h.one, h.rO, h.rR, h.rV, h.rF, h.rDB, h.rVB, h.rLab, h.rLev, h.rPar, h.rQ, h.rn, hL, hs⟩

/-- The registers written by the labelling. -/
def LScr (r : ℕ) : Prop := r = 130111 ∨ r = 130112 ∨ Scr r ∨ (130140 ≤ r ∧ r ≤ 130142)

/-- **The frame of the labelling**: only its registers and the written arrays change. -/
def LFr (Y : Lay) (c0 c : Config) : Prop :=
  (∀ r, ¬ LScr r → c.nreg r = c0.nreg r) ∧ c.rreg = c0.rreg ∧ c.rmem = c0.rmem ∧
    c.output = c0.output ∧ ∀ a, ¬ Y.Written a → c.nmem a = c0.nmem a
theorem LFr.trans {Y : Lay} {c0 c1 c2 : Config} (h1 : LFr Y c0 c1) (h2 : LFr Y c1 c2) :
    LFr Y c0 c2 :=
  ⟨fun r hr => (h2.1 r hr).trans zttlv, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
    h2.2.2.2.1.trans h1.2.2.2.1, fun a ha => (h2.2.2.2.2 a ha).trans zttlw⟩
theorem LFr.of_fr {Y : Lay} {c0 c : Config} (h : Fr Y c0 c) : LFr Y c0 c :=
  ⟨fun r hr => h.1 r (fun h' => hr ztcgy), h.2.1, h.2.2.1, h.2.2.2.1,
    h.2.2.2.2⟩
theorem LFr.nreg {Y : Lay} {c0 c : Config} (hf : LFr Y c0 c) {f : ℕ → ℕ}
    (hfr : ∀ r, ¬ LScr r → f r = c.nreg r) : LFr Y c0 { c with nreg := f } :=
  ⟨fun r hr => (hfr r hr).trans ztoaq, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2⟩
theorem Regs0.lfr {Y : Lay} {c0 c : Config} (h : Regs0 Y c0) (hf : LFr Y c0 c) : Regs0 Y c := by
  zujab
  zuboz
  refine ztexk <;>
    (rwa [k _ (by unfold LScr Scr; omega)])

/-! ## The fill -/
section fill
variable {P : Polygon} {W : ℕ} {Y : Lay}

/-- **The fill** of the label array with the sentinel `nv`: cost `≤ 5 nv + 2`. -/
theorem fillLoop_exec (hY : Y.Good W) {c : Config} (hw : WordsBounded W c) (hR : Regs0 Y c)
    (h0 : c.nreg 130140 = 0) :
    ∃ c' k, Exec P W fillLoop c c' k ∧ k ≤ 5 * Y.nv + 2 ∧ WordsBounded W c' ∧ LFr Y c c' ∧
      c'.nreg 130140 = Y.nv ∧ ∀ x, x < Y.nv → labV Y c'.nmem x = Y.nv := by
  have := hY.wLab; have := hY.wn
  obtain ⟨c', k, e, ⟨hw', hf', hle, hlab⟩, htest, hk⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := 130140) (b := 130110) (body := fillBody)
    (fun c' => WordsBounded W c' ∧ LFr Y c c' ∧ c'.nreg 130140 ≤ Y.nv ∧
      ∀ x, x < c'.nreg 130140 → labV Y c'.nmem x = Y.nv)
    (fun c' => 5 * (Y.nv - c'.nreg 130140)) ztbms
    (fun c1 ⟨hw1, hf1, hle1, hl1⟩ htest => by
      have hR1 := hR.lfr hf1
      rw [hR1.rn] at htest
      unfold fillBody
      exec_block
      · rw [hR1.rLab]; omega
      · config_simp; rw [hR1.one]; omega
      · refine ⟨⟨by_omega, ?_, ?_, fun x hx => ?_⟩, ?_⟩
        · refine ⟨fun r hr => ?_, hf1.2.1, hf1.2.2.1, hf1.2.2.2.1, fun a ha => ?_⟩
          · zudi
            zupi
            · exact absurd ztbh (h1 ▸ hr)
            · exact absurd ztbh (h2 ▸ hr)
            · zulyw
          · simp only [Machine.upd_apply, hR1.rLab]
            zumrc
            zudlu
            · omega
            · exact hf1.2.2.2.2 a ha
        · config_simp; rw [hR1.one]; omega
        · config_simp
          rw [hR1.one] at hx
          unfold labV
          rw [hR1.rLab, hR1.rn, view_upd_in _ _ _ _ _ htest]
          zujdk
          · zuoqs; tauto
          simp
        · config_simp; rw [hR1.one]; omega)
    ⟨hw, ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩, by_omega, fun x hx => by_omega⟩
  have hR' := hR.lfr hf'
  rw [hR'.rn] at htest
  refine ⟨c', k, e, by_omega, hw', hf', by_omega,
    by grind⟩
end fill

/-! ## The driver -/

/-- The unlabelled vertices of a label array. -/
def unlab (Y : Lay) (m : ℕ → ℕ) : Finset ℕ := (Finset.range Y.nv).filter (fun x => labV Y m x = Y.nv)

/-- The potential of the driver. -/
def drvPot (Y : Lay) (G : Env) (c : Config) : ℕ :=
  40 * (Y.nv - c.nreg 130140) + 70 * (unlab Y c.nmem).card + 50 * ∑ x ∈ unlab Y c.nmem, G.deg x

/-- **The invariant of the driver** (relative to the entry configuration `cE`). -/
structure DI (Y : Lay) (W : ℕ) (cE c : Config) : Prop where
  wb : WordsBounded W c
  fr : LFr Y cE c
  vle : c.nreg 130140 ≤ Y.nv
  inv : (Y.env cE.nmem).LInv ztkaa ztdzi
section drv
variable {P : Polygon} {W : ℕ} {Y : Lay} {cE : Config}

/-- The labelling frame keeps the rotation system. -/
theorem LFr.env (hY : Y.Good W) {c : Config} (hf : LFr Y cE c) : Y.env c.nmem = Y.env cE.nmem :=
  Lay.env_congr hY hf.2.2.2.2

/-- Reading a read-only array through the labelling frame. -/
theorem LFr.read (hY : Y.Good W) {c : Config} (hf : LFr Y cE c) {b n i : ℕ}
    (hb : zteoz ∨ ztepa ∨ ztepb ∨
      zteoy ∨ zteox ∨ ztepc) (hi : i < n) :
    c.nmem ztbcn = view cE.nmem b n i := by
  zuccg

  unfold Lay.Written Disj at *
  omega

/-- **One vertex of the driver**: skip it if blocked or labelled, otherwise search from it. -/
theorem drvBody_exec (hY : Y.Good W) (hR : Regs0 Y cE) (hok : (Y.env cE.nmem).OK)
    (hs : (Y.env cE.nmem).Sym) {c : Config} (hI : DI Y W cE c) (hlt : c.nreg 130140 < Y.nv) :
    ∃ c' k, Exec P W drvBody c c' k ∧ DI Y W cE c' ∧
      drvPot Y ztmcn c' + k + 2 ≤ drvPot Y ztmcn c := by
  have hRc := hR.lfr hI.fr
  zudpm
  have := hY.wVB; have := hY.wLab; have := hY.wn
  have rvb : c.nmem _ = (Y.env cE.nmem).vb _ :=
    LFr.read hY hI.fr by_omega hlt
  have rlab : c.nmem (Y.bLab + c.nreg 130140) = labV Y c.nmem ztdzi := by
    rw [labV, view_lt hlt]
  -- the final increment, common to all cases
  have fin : ∀ c2 : Config, WordsBounded W c2 → LFr Y cE c2 →
      c2.nreg 130140 = c.nreg 130140 →
      (Y.env cE.nmem).LInv zttrs (c.nreg 130140 + 1) →
      ∃ c3, Exec P W ztnam c2 c3 1 ∧ DI Y W cE c3 ∧
        c3.nreg 130140 = c.nreg 130140 + 1 ∧ c3.nmem = c2.nmem := by
    intro c2 hw2 hf2 hv2 hL2
    have hone := (hR.lfr hf2).one
    have e := Exec.addN (P := P) hw2 130140 130140 130001 by_omega
    refine ⟨_, e, ⟨e.wb_right, LFr.nreg hf2 ztez, ?_, ?_⟩, ?_, rfl⟩
    · rw [Machine.upd_other _ _ _ ztwkw]
    · simp_all
    · simp_all
    simp_all
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, hX1, hr1, hrr1, hrm1, ho1⟩ : ∃ c1 k1,
      Exec P W ztjoo c c1 k1 ∧ k1 = 2 ∧
      WordsBounded W c1 ∧ c1.nmem = c.nmem ∧
      c1.nreg 130142 = (Y.env cE.nmem).vb ztdzi ∧
      (∀ r, r ≠ 130141 → r ≠ 130142 → c1.nreg r = c.nreg r) ∧ c1.rreg = c.rreg ∧
      c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    · rw [hRc.rVB]; omega
    · refine ⟨rfl, by_omega, rfl, by config_simp; rw [hRc.rVB, rvb], fun r h1 h2 => ?_, rfl, rfl,
        rfl⟩
      simp_all
  have hf1 : LFr Y cE c1 := by
    refine ⟨fun r hr => ?_, hrr1.trans hI.fr.2.1, hrm1.trans hI.fr.2.2.1, ho1.trans hI.fr.2.2.2.1,
      fun a ha => by zvmxz; exact hI.fr.2.2.2.2 a ha⟩
    rw [hr1 r ztwkw
      ztwkw]
    exact hI.fr.1 r hr
  have hv1 : c1.nreg 130140 = c.nreg 130140 := by_simp_all
  have hone1 := (hR.lfr hf1).one
  have hpot : ∀ c3 : Config, c3.nreg 130140 = c.nreg 130140 + 1 → c3.nmem = c.nmem →
      drvPot Y ztmcn c3 + 40 = drvPot Y ztmcn c := by
    intro c3 hv3 hm3
    unfold drvPot
    grind
  by_cases hvb : (Y.env cE.nmem).vb ztdzi = 1
  · -- blocked: skip
    obtain ⟨c3, e3, hD3, hv3, hm3⟩ := fin c1 hw1 hf1 hv1 (by
      zvmxz; exact hI.inv.skip (Or.inl hvb))
    refine ⟨c3, 2 + ztstc, .seq by_simp_all (.seq (ifNe1_skip hw1 hone1 by_omega)
      e3), hD3, ?_⟩
    grind
  · have hX1' : c1.nreg 130142 ≠ 1 := by_omega
    -- load the label
    obtain ⟨c2, k2, e2, hk2, hw2, hm2, hX2, hr2, hrr2, hrm2, ho2⟩ : ∃ c2 k2,
        Exec P W ztjop c1 c2 k2 ∧ k2 = 2 ∧
        WordsBounded W c2 ∧ c2.nmem = c.nmem ∧
        c2.nreg 130142 = labV Y c.nmem _ ∧
        (∀ r, r ≠ 130141 → r ≠ 130142 → c2.nreg r = c1.nreg r) ∧ c2.rreg = c1.rreg ∧
        c2.rmem = c1.rmem ∧ c2.output = c1.output := by
      have hRc1 := hR.lfr hf1
      exec_block
      · rw [hRc1.rLab, hv1]; omega
      · refine ⟨rfl, by_omega, hm1, by config_simp; rw [hRc1.rLab, hv1, hm1, rlab], fun r h1 h2 => ?_,
          rfl, rfl, rfl⟩
        simp_all
    have hf2 : LFr Y cE c2 := by
      refine ⟨fun r hr => ?_, hrr2.trans hf1.2.1, hrm2.trans hf1.2.2.1, ho2.trans hf1.2.2.2.1,
        fun a ha => by rw [hm2]; exact hI.fr.2.2.2.2 a ha⟩
      rw [hr2 r ztwkw
        ztwkw]
      zulyw
    have hv2 : c2.nreg 130140 = c.nreg 130140 := by_simp_all
    have hRc2 := hR.lfr hf2
    by_cases hl : labV Y c.nmem ztdzi < Y.nv
    · -- labelled: skip
      obtain ⟨c3, e3, hD3, hv3, hm3⟩ := fin c2 hw2 hf2 hv2 (by
        rw [hm2]; exact hI.inv.skip (Or.inr (by simp only [Lay.env_nv]; omega)))
      have hlt2 : c2.nreg 130142 < c2.nreg 130110 := by zuoib; exact hl
      have eU : Exec P W unlabB c1 c2 _ :=
        Exec.seq e2 (.ifLtN_true hlt2 ztgbs)
      zueuk
      refine ⟨c3, 2 + ztjzg, .seq by_simp_all (.seq e' e3), hD3, ?_⟩
      grind
    · -- unlabelled: search
      have hlv : labV Y c.nmem ztdzi = Y.nv := by
        zuct
        exact hl (hI.inv.lbl _ hlt hne).1
      -- set the label and the source
      obtain ⟨c3, e3, hw3, hm3, h111, h112, hr3, hrr3, hrm3, ho3⟩ : ∃ c3,
          Exec P W _ c2 c3 2 ∧
          WordsBounded W c3 ∧ c3.nmem = c.nmem ∧ c3.nreg 130111 = c.nreg 130140 ∧
          c3.nreg 130112 = c.nreg 130140 ∧
          (∀ r, r ≠ 130111 → r ≠ 130112 → c3.nreg r = c2.nreg r) ∧ c3.rreg = c2.rreg ∧
          c3.rmem = c2.rmem ∧ c3.output = c2.output := by
        have := Exec.copyN (P := P) hw2 130111 130140
        have h2 := Exec.copyN (P := P) this.wb_right 130112 130140
        refine ⟨_, Exec.block_cons this (Exec.block_cons h2 (Exec.block_nil h2.wb_right)),
          h2.wb_right, hm2, ?_, ?_, fun r a b => ?_, rfl, rfl, rfl⟩
        · simp_all
        · simp_all
        simp_all
      have hf3 : LFr Y cE c3 := by
        refine ⟨fun r hr => ?_, hrr3.trans hf2.2.1, hrm3.trans hf2.2.2.1, ho3.trans hf2.2.2.2.1,
          fun a ha => by rw [hm3]; exact hI.fr.2.2.2.2 a ha⟩
        rw [hr3 r ztwnm ztbake]
        exact hf2.1 r hr
      have hR3 : Regs Y _ _ c3 := (hR.lfr hf3).regs h111 h112
      zuljz
      have hlab3 : labV Y c3.nmem = labV Y c.nmem := by rw [hm3]
      have hp : (Y.env c3.nmem).Pre ztdzi ztdzi (labV Y c3.nmem) := by
        rw [henv3, hlab3]
        exact ⟨hok, hlt, hvb, hlt, hI.inv.fresh hok hs hlt hlv⟩
      obtain ⟨c4, k4, e4, hk4, hOI, hht⟩ := bfs_exec hY hR3 hp hw3
      rw [henv3] at hk4
      have hB : (Y.env cE.nmem).Inv ztdzi ztdzi ztkaa
          (labV Y c4.nmem) (levV Y c4.nmem) (parV Y c4.nmem) (qV Y c4.nmem) ztvkn
          ztvkn := by
        have := hOI.inv
        grind
      have hf4 := hf3.trans (LFr.of_fr hOI.fr)
      have hv4 : c4.nreg 130140 = c.nreg 130140 := by
        rw [hOI.fr.1 _ ztggo, hr3 _ by_decide by_decide, hv2]
      have hL4 := hI.inv.bfs hok hs hlt hB
      obtain ⟨c5, e5, hD5, hv5, hm5⟩ := fin c4 hOI.wb hf4 hv4 hL4
      have hge2 : ¬ c2.nreg 130142 < c2.nreg 130110 := by zuoib; exact hl
      have eU : Exec P W unlabB c1 c4 _ :=
        Exec.seq e2 (.ifLtN_false hge2 (Exec.seq e3 e4))
      zueuk
      refine ⟨c5, 2 + ztjzg, .seq by_grind (.seq e' e5), hD5, ?_⟩
      -- the potential
      obtain ⟨hcard, hsum⟩ := hI.inv.unlab_split hok hs hlt hlv hB
      have hcard' : (unlab Y c4.nmem).card + c4.nreg 130121 = (unlab Y c.nmem).card := hcard
      have hsum' : ∑ x ∈ unlab Y c4.nmem, (Y.env cE.nmem).deg x +
          ∑ i ∈ Finset.range _, (Y.env cE.nmem).deg _ =
          ∑ x ∈ unlab Y c.nmem, (Y.env cE.nmem).deg x := hsum
      unfold drvPot
      grind
end drv

/-! ## The whole labelling -/
section main
variable {P : Polygon} {W : ℕ} {Y : Lay}

/-- **Component labelling on the RAM.**  On a good layout (`Regs0`) whose rotation system is
well formed and symmetric, `labelStmt` runs in at most `120 nv + 50 N + 10` steps, writes only its
registers and the arrays `lab`, `lev`, `par`, `q` (`LFr`), gives every unblocked vertex a label
`< nv`, and two unblocked vertices get the same label iff they are connected. -/
theorem labelStmt_exec (hY : Y.Good W) {c : Config} (hw : WordsBounded W c) (hR : Regs0 Y c)
    (hok : (Y.env c.nmem).OK) (hs : (Y.env c.nmem).Sym) :
    ∃ c' k, Exec P W labelStmt c c' k ∧ k ≤ 120 * Y.nv + 50 * Y.N + 10 ∧ WordsBounded W c' ∧
      LFr Y c c' ∧
      (∀ x, x < Y.nv → (Y.env c.nmem).vb x ≠ 1 → labV Y c'.nmem x < Y.nv) ∧
      ∀ x y, x < Y.nv → y < Y.nv → (Y.env c.nmem).vb x ≠ 1 → (Y.env c.nmem).vb y ≠ 1 →
        (labV Y c'.nmem x = labV Y c'.nmem y ↔ (Y.env c.nmem).Reach x y) := by
  have := hY.wn
  have e1 := Exec.constN (P := P) hw 130140 0 by_omega
  set c1 := { c with nreg := upd c.nreg 130140 0 }
  have hf1 : LFr Y c c1 := LFr.nreg ⟨by_omega, rfl, rfl, rfl, by_omega⟩
    ztbamw
  obtain ⟨c2, k2, e2, hk2, hw2, hf2, hv2, hlab2⟩ := fillLoop_exec (P := P) hY e1.wb_right
    (hR.lfr hf1) by_rfl
  zulkb
  have e3 := Exec.constN (P := P) hw2 130140 0 by_omega
  set c3 := { c2 with nreg := upd c2.nreg 130140 0 }
  have hf3 : LFr Y c c3 := LFr.nreg hf12
    ztbamw
  zuljz
  have hD3 : DI Y W c c3 := ⟨e3.wb_right, hf3, by_positivity, by
    simp only [c3, Machine.upd_same]
    exact Env.LInv.init by_simp_all⟩
  obtain ⟨c4, k4, e4, hD4, htest, hk4⟩ := whileLtN_pot (P := P) (W := W) (a := 130140)
    (b := 130110) (body := drvBody) (DI Y W c) (drvPot Y ztvef) (fun c h => h.wb)
    (fun c' hD htest => by
      have := (hR.lfr hD.fr).rn
      zvmwk at htest
      exact drvBody_exec hY hR hok hs hD htest) hD3
  have hv4 : c4.nreg 130140 = Y.nv := by
    have := (hR.lfr hD4.fr).rn
    have := hD4.vle
    omega
  have hL4 := hD4.inv
  rw [hv4] at hL4
  obtain ⟨hfin1, hfin2⟩ := hL4.final hok hs
  refine ⟨c4, 1 + (k2 + (1 + k4)), .seq e1 ztbal, ?_, hD4.wb, hD4.fr, hfin1,
    hfin2⟩
  -- the cost
  have hU3 : unlab Y c3.nmem = Finset.range Y.nv := by
    unfold unlab
    grind
  have hpot3 : drvPot Y ztvef c3 = 40 * Y.nv + 70 * Y.nv + 50 * Y.N := by
    unfold drvPot
    have hsd : ∑ x ∈ Finset.range Y.nv, (Y.env c.nmem).deg x = Y.N := hok.sum_deg
    rw [hU3, Finset.card_range, hsd]
    rfl
  omega
end main
def PFr (Rg Am : ℕ → Prop) (c0 c : Config) : Prop :=
  (∀ r, ¬ Rg r → c.nreg r = c0.nreg r) ∧ c.rreg = c0.rreg ∧ c.rmem = c0.rmem ∧
    c.output = c0.output ∧ ∀ a, ¬ Am a → c.nmem a = c0.nmem a
namespace PFr
variable {Rg Am : ℕ → Prop}
theorem refl (c : Config) : PFr Rg Am c c := ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
theorem trans {c0 c1 c2 : Config} (h1 : PFr Rg Am c0 c1) (h2 : PFr Rg Am c1 c2) :
    PFr Rg Am c0 c2 :=
  ⟨fun r hr => (h2.1 r hr).trans zttlv, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
    h2.2.2.2.1.trans h1.2.2.2.1, fun a ha => (h2.2.2.2.2 a ha).trans zttlw⟩
theorem mono {Rg' Am' : ℕ → Prop} {c0 c : Config} (h : PFr Rg Am c0 c)
    (hR : ∀ r, Rg r → Rg' r) (hA : ∀ a, Am a → Am' a) : PFr Rg' Am' c0 c :=
  ⟨fun r hr => h.1 r (fun h' => hr zttmq), h.2.1, h.2.2.1, h.2.2.2.1,
    fun a ha => h.2.2.2.2 a (fun h' => ha (hA a h'))⟩
variable {c0 c : Config}
theorem nreg (h : PFr Rg Am c0 c) {f : ℕ → ℕ}
    (hf : ∀ r, ¬ Rg r → f r = c.nreg r) : PFr Rg Am c0 { c with nreg := f } :=
  ⟨fun r hr => (hf r hr).trans ztoab, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
theorem nmem (h : PFr Rg Am c0 c) {a x : ℕ} (ha : Am a) :
    PFr Rg Am c0 { c with nmem := upd c.nmem a x } :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun b hb => by
    show upd c.nmem a x b = c0.nmem b
    zunxq; exact h.2.2.2.2 b hb⟩
theorem nreg_nmem (h : PFr Rg Am c0 c) {f : ℕ → ℕ}
    (hf : ∀ r, ¬ Rg r → f r = c.nreg r) {a x : ℕ} (ha : Am a) :
    PFr Rg Am c0 { c with nreg := f, nmem := upd c.nmem a x } :=
  ⟨fun r hr => (hf r hr).trans ztoab, h.2.1, h.2.2.1, h.2.2.2.1, fun b hb => by
    show upd c.nmem a x b = c0.nmem b
    zunxq; exact h.2.2.2.2 b hb⟩
theorem of_eq (h : PFr Rg Am c0 c) {f g : ℕ → ℕ}
    (hf : ∀ r, ¬ Rg r → f r = c.nreg r) (hg : ∀ a, ¬ Am a → g a = c.nmem a) :
    PFr Rg Am c0 { c with nreg := f, nmem := g } :=
  ⟨fun r hr => (hf r hr).trans ztoab, h.2.1, h.2.2.1, h.2.2.2.1,
    fun a ha => (hg a ha).trans (h.2.2.2.2 a ha)⟩
end PFr

/-! ## Filling an array -/

/-- One cell of the fill. -/
def fillCell : Stmt := block [.addN 130154 130150 130153, .storeN 130154 130152,
  .addN 130153 130153 130001]

/-- **Fill** `[b, b + n)` with `x`. -/
def fillStmt : Stmt := .seq (.instr (.constN 130153 0)) (.whileLtN 130153 130151 fillCell)

/-- The registers of the fill. -/
def FillScr (r : ℕ) : Prop := r = 130153 ∨ r = 130154
section fill
variable {P : Polygon} {W : ℕ}

/-- **The fill**: `[b, b + n)` holds `x` afterwards, nothing else changes but the scratch
registers `130153`, `130154`; cost `≤ 5 n + 3`. -/
theorem fillStmt_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    (hb : c.nreg 130150 + c.nreg 130151 ≤ W) (hn : c.nreg 130151 + 1 ≤ W) :
    ∃ c' k, Exec P W fillStmt c c' k ∧ k ≤ 5 * c.nreg 130151 + 3 ∧
      PFr FillScr zthgr c c' ∧
      ∀ i, i < c.nreg 130151 → c'.nmem ztrln = c.nreg 130152 := by
  have e0 := Exec.constN (P := P) hw 130153 0 by_omega
  set c1 := { c with nreg := upd c.nreg 130153 0 }
  obtain ⟨c', k, e, hk, hI⟩ := forN (P := P) (W := W) (ri := 130153) (rn := 130151)
    (body := fillCell)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130153 = j ∧ c'.nreg 130151 = c.nreg 130151 ∧
      PFr FillScr zthgr c c' ∧
      ∀ i, i < j → c'.nmem ztrln = c.nreg 130152)
    (c.nreg 130151) 3 zthd
    (fun j c2 hj ⟨hw2, hi2, hn2, hf2, hm2⟩ => by
      have r1 : c2.nreg 130150 = c.nreg 130150 := hf2.1 _ ztjqt
      have r2 : c2.nreg 130152 = c.nreg 130152 := hf2.1 _ ztjqt
      have r3 : zthoo := (hf2.1 _ ztjqt).trans hone
      unfold fillCell
      exec_block
      · omega
      · config_simp; omega
      · refine ⟨le_refl _, ‹_›, by_simp_all, by_simp_all, ?_,
          fun i hi => ?_⟩
        · refine PFr.nreg_nmem hf2 ztez ?_
          · zumwj; unfold FillScr at hr; simp_all
          omega
        · config_simp
          rw [r1, hi2, r2]
          zujgy
          grind)
    (j₀ := 0) ⟨e0.wb_right, by_rfl, by_rfl, PFr.nreg ztffw (fun r hr => by
      zumwj; unfold FillScr at hr; simp_all),
      fun i hi => by_omega⟩ (Nat.zero_le _)
  exact ⟨c', 1 + k, .seq e0 e, by_omega, hI.2.2.2.1, hI.2.2.2.2⟩
