module

public import HK.Vectors

/-!
# Definitions

The two dynamics, the stability assertions, and the data of the counterexamples.
-/

@[expose] public section

noncomputable section
-- Binder notations expand to open predicates on states and index sets.
set_option quotPrecheck false
namespace HK

open Filter

/-- Convergence as the discrete time parameter tends to infinity. -/
scoped notation "Converges" f:arg z:arg => Tendsto f atTop (nhds z)
scoped notation "State" n:arg => (Fin n → ℝ)

-- A data vector carries its dimension in the length of its literal.
local macro doc:(docComment)? "real_vector " n:ident args:bracketedBinder* " := " "[" xs:term,* "]" : command =>
  `($[$doc:docComment]? @[hk_data] def $n $args* : State $(Lean.quote xs.getElems.size) := ![$xs,*])

/-! ### The models (Mirtabatabaei–Bullo §2) -/

/-- The two models: synchronized bounded confidence and synchronized bounded influence. -/
inductive Model
  | sbc
  | sbi

section
variable (m : Model) {n : ℕ} (r y x₀ : State n) (x : ℕ → State n)

/-- The bound deciding whether `j` is an out-neighbour of `i`: `r i` (SBC) or `r j` (SBI). -/
def Model.bound (i j : Fin n) :=
  match m with
  | .sbc => r i
  | .sbi => r j

/-- `N_i(y)`: the out-neighbours of `i` at the opinion vector `y`, `{j : |y_i − y_j| ≤ r_i}` in the
SBC model and `{j : |y_i − y_j| ≤ r_j}` in the SBI model. -/
def neighbors (i : Fin n) :=
  Finset.univ.filter (fun j => |y i - y j| ≤ m.bound r i j)

/-- The proximity digraph `G_r(y)`: an arc from `i` to `j` iff `j ∈ N_i(y)`. -/
def proximityDigraph : Digraph (Fin n) :=
  ⟨fun i j => j ∈ neighbors m r y i⟩

/-- The equal weights assigned by an explicit neighborhood table. -/
scoped notation "weights" N:arg => Matrix.of fun i j => if j ∈ N i then (1 : ℝ) / (N i).card else 0

/-- The adjacency matrix `A(y)`: `a_ij = 1/|N_i(y)|` if `j ∈ N_i(y)`, else `0`. -/
def adjMatrix :=
  weights (neighbors m r y)

/-- One synchronous update, (2.1): `y ↦ A(y) y`. -/
def step :=
  (adjMatrix m r y).mulVec y

/-- The trajectory from the initial opinion vector `x₀`: `x(t) = stepᵗ x₀`. -/
def traj (t : ℕ) :=
  (step m r)^[t] x₀

/-- `x` is in a fixed state from `τ` on: `x(t) = x(τ)` for every `t ≥ τ`. -/
def FixedFrom (τ : ℕ) :=
  ∀ t, τ ≤ t → x t = x τ

/-- Pseudo-stable behaviour after `τ` towards `xinf` (Mirtabatabaei–Bullo (2.2)): `x` converges to
`xinf`, and the agents split into two non-empty classes `F` and `C` such that for every `t ≥ τ` the
agents of `F` sit at their limits and each agent of `C` moves strictly towards its limit from one
side: `x_i(t) < x_i(t+1) < xinf_i` or `x_i(t) > x_i(t+1) > xinf_i`. -/
def PseudoStableAfter (xinf : State n) (τ : ℕ) :=
  Converges x xinf ∧
    ∃ F C : Finset (Fin n), F.Nonempty ∧ C.Nonempty ∧ Disjoint F C ∧ F ∪ C = Finset.univ ∧
      ∀ t, τ ≤ t →
        (∀ i ∈ F, x t i = xinf i) ∧
        ∀ i ∈ C, (x t i < x (t + 1) i ∧ x (t + 1) i < xinf i) ∨
          (x t i > x (t + 1) i ∧ x (t + 1) i > xinf i)

/-! ### Final value and per-step factor -/

/-- Definition 3.1: the final value at constant topology, `fvct(y) = lim_{t→∞} A(y)ᵗ y` (the limit
of the trajectory from `y` whose topology is held fixed; `limUnder` is that limit when it exists). -/
def fvct :=
  limUnder atTop (fun t : ℕ => (adjMatrix m r y ^ t).mulVec y)

/-- Definition 6.1: the per-step convergence factor of agent `i` at time `t` along `x`,
`(x_i(t+1) − fvct_i(x(t))) / (x_i(t) − fvct_i(x(t)))`. -/
def perStepFactor (i : Fin n) (t : ℕ) :=
  (x (t + 1) i - fvct m r (x t) i) / (x t i - fvct m r (x t) i)

end

/-! ### The conjectures and the theorem, as statements about one model and about both -/

section
variable (m : Model) (n : ℕ)
scoped notation "PositiveRadii" r:arg => ∀ i, 0 < r i
local notation3 "AllSystems " r:arg _x:arg ", " p => ∀ (r _x : State n), PositiveRadii r → p
scoped notation "Settled" x:arg τ:arg => FixedFrom x τ ∨ ∃ z, PseudoStableAfter x z τ
/-- Neither of the eventual behaviours asserted by Conjecture 2.3 occurs. -/
scoped notation "Unstable" y:arg => (∀ t, ¬ FixedFrom y t) ∧ ∀ z t, ¬ PseudoStableAfter y z t

local notation "ConstantFrom" r:arg x:arg τ:arg => ∀ t, τ ≤ t →
  proximityDigraph m r (traj m r x t) = proximityDigraph m r (traj m r x τ)

local notation3 "OnceConstant " r:arg x:arg t:arg ", " p =>
  AllSystems r x, ∀ τ, (ConstantFrom r x τ) → ∃ t, τ ≤ t ∧ p

/-- Conjecture 2.2 (constant topology in finite time) for the model `m` and `n` agents: for every
positive bounds vector and every initial opinion vector there is a finite time after which the
proximity digraph is constant. -/
def Conjecture22ForAgents :=
  AllSystems r x₀, ∃ τ, ConstantFrom r x₀ τ

/-- Conjecture 2.2 for the model `m` and every number of agents. -/
def Conjecture22For := ∀ n, Conjecture22ForAgents m n

/-- Conjecture 2.2 for any SBC or SBI system. -/
def Conjecture22 := ∀ m, Conjecture22For m

/-- Conjecture 2.3 (pseudo-stable behaviour) for the model `m` and `n` agents: every trajectory
reaches a fixed state in finite time or is pseudo-stable after some finite time. -/
def Conjecture23ForAgents :=
  AllSystems r x₀, ∃ τ, Settled (traj m r x₀) τ

/-- Conjecture 2.3 for the model `m` and every number of agents. -/
def Conjecture23For := ∀ n, Conjecture23ForAgents m n

/-- Conjecture 2.3 for any SBC or SBI system. -/
def Conjecture23 := ∀ m, Conjecture23For m

/-- Theorem 6.4(iv) for the model `m` and `n` agents, read literally: if the proximity digraph of a
trajectory is constant from `τ` on, the trajectory is pseudo-stable from some `t₂ ≥ τ` on (already
false for a trajectory frozen from the start, since both classes of (2.2) must be non-empty). -/
def Theorem64ivLiteralForAgents :=
  OnceConstant r x₀ t₂, ∃ xinf, PseudoStableAfter (traj m r x₀) xinf t₂

/-- Theorem 6.4(iv) for the model `m` and every number of agents, read literally. -/
def Theorem64ivLiteralFor := ∀ n, Theorem64ivLiteralForAgents m n

/-- Theorem 6.4(iv) for the model `m` and `n` agents, the reading that also admits a trajectory in a
fixed state from `t₂` on. -/
def Theorem64ivForAgents :=
  OnceConstant r x₀ t₂, Settled (traj m r x₀) t₂

/-- Theorem 6.4(iv) for the model `m` and every number of agents, the reading admitting fixed states. -/
def Theorem64ivFor := ∀ n, Theorem64ivForAgents m n

/-- Theorem 6.4(iv), literal reading, for any SBC or SBI system. -/
def Theorem64ivLiteral := ∀ m, Theorem64ivLiteralFor m

/-- Theorem 6.4(iv), the reading admitting fixed states, for any SBC or SBI system. -/
def Theorem64iv := ∀ m, Theorem64ivFor m

end

scoped notation "gap" z:arg i:arg j:arg R:arg => |(|z i - z j|) - R|
scoped notation "gaps" r:arg z:arg i:arg =>
  {d : ℝ | ∃ j, j ≠ i ∧ (d = gap z i j (r i) ∨ d = gap z i j (r j))}

section
variable {n : ℕ} (r z y : State n)

/-- Definition 4.1(i): the equi-topology distance
`ε_i(z) = ½ · min {||z_i − z_j| − R| : j ≠ i, R ∈ {r_i, r_j}}` (for `n = 1` the set is empty and
`sInf ∅ = 0` on `ℝ`). -/
def equiTopologyDistance (i : Fin n) :=
  (1 / 2) * sInf (gaps r z i)

local notation "ε" => equiTopologyDistance r z

/-- `y` lies in the equi-topology neighbourhood of `z` (Definition 4.1(i)): `|y_i − z_i| < ε_i(z)`
where `ε_i(z) > 0`, and `|y_i − z_i| = ε_i(z)` where `ε_i(z) = 0`. -/
def EquiTopologyNbhd :=
  ∀ i, (0 < ε i → |y i - z i| < ε i) ∧
    (ε i = 0 → |y i - z i| = ε i)

end

/-! ### The four systems of Hegarty–Ognissanti–Wedin (their §2–§5) -/

/-- Their §2, SBC, seven agents: the initial opinions. -/
real_vector sbc7_x0 := [0, 38, 69, 84, 99, 130, 168]
/-- Their §2: the confidence bounds. -/
real_vector sbc7_r := [18, 42, 48, 12, 48, 42, 18]
/-- Their §2: the limit. -/
real_vector sbc7_lim := [0, 36, 72, 84, 96, 132, 168]
/-- Their §2: the offset direction, `x(t) = x_∞ + (−1/6)ᵗ v`. -/
real_vector sbc7_v := [0, 2, -3, 0, 3, -2, 0]

/-- Their §3: `λ = (1 − √5)/8`, the rate of the two SBI systems. -/
def sbiRate : ℝ := (1 - Real.sqrt 5) / 8

/-- Their §3, SBI, seven agents: the initial opinions, with `φ = (1 + √5)/2`. -/
real_vector sbi7_x0 := [0, 15 / 2, 10 - Real.goldenRatio / 2, 11, 12 + Real.goldenRatio / 2, 29 / 2, 22]
/-- Their §3: the influence bounds. -/
real_vector sbi7_r := [8, 4, 4, 8, 4, 4, 8]
/-- Their §3: the limit. -/
real_vector sbi7_lim := [0, 7, 10, 11, 12, 15, 22]
/-- Their §3 and §5: the offset direction, `x(t) = x_∞ + (λᵗ/2) v` in §3 and `x_∞ + λᵗ v` in §5. -/
real_vector sbi_v := [0, 1, -Real.goldenRatio, 0, Real.goldenRatio, -1, 0]

/-- Their §4, SBC, six agents: the initial opinions. -/
real_vector sbc6_x0 := [0, 22, 37, 103, 118, 140]
/-- Their §4: the confidence bounds. -/
real_vector sbc6_r := [10, 70, 70, 70, 70, 10]
/-- Their §4: the limit. -/
real_vector sbc6_lim := [0, 20, 40, 100, 120, 140]
/-- Their §4: the offset direction, `x(t) = x_∞ + (−1/6)ᵗ v`. -/
real_vector sbc6_v := [0, 2, -3, 3, -2, 0]

/-- Their §5, SBI, seven agents: the initial opinions. -/
real_vector sbi7b_x0 := [0, 71, 100 - Real.goldenRatio, 110, 120 + Real.goldenRatio, 149, 220]
/-- Their §5: the influence bounds. -/
real_vector sbi7b_r := [85, 35, 35, 75, 35, 35, 85]
/-- Their §5: the limit. -/
real_vector sbi7b_lim := [0, 70, 100, 110, 120, 150, 220]

/-! ### Two smaller constant-digraph systems (this development) -/

/-- Five SBC agents: the rate `(1 − √2)/3`. -/
def sbc5Rate : ℝ := (1 - Real.sqrt 2) / 3
/-- Five SBC agents: the initial opinions `(0, 7, 12 − √2, 19, 24)`. -/
real_vector sbc5_x0 := [0, 7, 12 - Real.sqrt 2, 19, 24]
/-- Five SBC agents: the confidence bounds. -/
real_vector sbc5_r := [3, 9, 9, 9, 3]
/-- Five SBC agents: the limit. -/
real_vector sbc5_lim := [0, 6, 12, 18, 24]
/-- Five SBC agents: the offset direction, `x(t) = x_∞ + ((1 − √2)/3)ᵗ v`. -/
real_vector sbc5_v := [0, 1, -Real.sqrt 2, 1, 0]

/-- Six SBI agents: the rate `(13 − √249)/40`. -/
def sbi6Rate : ℝ := (13 - Real.sqrt 249) / 40
/-- Six SBI agents: the initial opinions `x_∞ + v`. -/
real_vector sbi6_x0 := [0, 25 + 10 / 16, 31 + (-5 - Real.sqrt 249) / 16, 44 + 8 / 16, 55 + 10 / 16, 90]
/-- Six SBI agents: the influence bounds. -/
real_vector sbi6_r := [45, 18, 27, 45 / 2, 27, 54]
/-- Six SBI agents: the limit. -/
real_vector sbi6_lim := [0, 25, 31, 44, 55, 90]
/-- Six SBI agents: the offset direction, `x(t) = x_∞ + ((13 − √249)/40)ᵗ v`. -/
real_vector sbi6_v := [0, 10 / 16, (-5 - Real.sqrt 249) / 16, 8 / 16, 10 / 16, 0]

/-! ### The two spectator systems (their §4 and §5, against Theorem 6.4(iii)(b)) -/

/-- Their §4 with a spectator at `210` (`r = 100`) and two beacons at `280`, `300` (`r = 10`): the
initial opinions. -/
real_vector sbc9_x0 := [0, 22, 37, 103, 118, 140, 210, 280, 300]
/-- Their §4 with the spectator and the beacons: the confidence bounds. -/
real_vector sbc9_r := [10, 70, 70, 70, 70, 10, 100, 10, 10]
/-- Their §5 with a spectator at `60` (`r = 1`), which is index `1` when the opinions are listed
increasingly: the initial opinions. -/
real_vector sbi8_x0 := [0, 60, 71, 100 - Real.goldenRatio, 110, 120 + Real.goldenRatio, 149, 220]
/-- Their §5 with the spectator: the influence bounds. -/
real_vector sbi8_r := [85, 1, 35, 35, 75, 35, 35, 85]

/-! ### Five SBI agents with complex modes; the near-homogeneous SBC family (this development) -/

/-- Five SBI agents: the influence bounds. -/
real_vector sbi5_r := [31, 9, 5, 15, 28]

/-- Five SBI agents: the limit. -/
real_vector sbi5_lim := [0, 10, 18, 20, 42]

/-- Five SBI agents: the averaging map on the offsets of agents `1, 2, 3` under the table
`{0}, {0, 1, 3}, {0, 1, 2, 3, 4}, {0, 2, 3, 4}, {4}` (agents `0` and `4` have offset `0`). -/
real_vector sbi5LinearStep (z : State 3) := [(z 0 + z 2) / 3, (z 0 + z 1 + z 2) / 5, (z 1 + z 2) / 4]

/-- Five SBI agents: the offsets of agents `1, 2, 3` after `t` steps of `sbi5LinearStep` from
`(1/3 − ρ, 1/5, 0)`. -/
def sbi5Offset (ρ : ℝ) (t : ℕ) :=
  sbi5LinearStep^[t] ![1 / 3 - ρ, 1 / 5, 0]

/-- Five SBI agents: the offsets of agents `1, 2, 3` placed between the zero offsets of agents `0`
and `4`. -/
real_vector sbi5Lift (z : State 3) := [0, z 0, z 1, z 2, 0]

/-- Five SBI agents: the initial opinions `(0, 31/3 − ρ, 91/5, 20, 42)`; the construction takes `ρ`
to be the real root of `60ρ³ − 47ρ² + 9ρ − 1`, which lies in `(57/100, 29/50)`. -/
def sbi5_x0 (ρ : ℝ) := sbi5_lim + sbi5Lift (sbi5Offset ρ 0)

/-- The five-agent SBC family: the bounds `(6 − 3δ, 6 + 3δ, 6 + 3δ, 6 + 3δ, 6 − 3δ)`. -/
real_vector sbc5Family_r (δ : ℝ) := [6 - 3 * δ, 6 + 3 * δ, 6 + 3 * δ, 6 + 3 * δ, 6 - 3 * δ]

/-- The five-agent SBC family: the initial opinions `sbc5_lim + δ sbc5_v`; `δ = 1` is `sbc5_x0`. -/
def sbc5Family_x0 (δ : ℝ) :=
  fun i => sbc5_lim i + δ * sbc5_v i

attribute [hk_data] Model.bound neighbors sbc5Family_x0 sbc5Rate sbi6Rate sbiRate
  Real.goldenConj Real.goldenRatio Set.mem_Icc abs_le abs_lt Fin.exists_fin_succ Fin.forall_fin_succ

end HK
