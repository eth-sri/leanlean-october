module

public import HK.Defs

/-! # Heterogeneous HK dynamics: shared certificates, counterexamples, and topology lemmas -/

public section
noncomputable section
set_option maxHeartbeats 600000
namespace HK
open Filter Topology

/-- Pair certificates while keeping conjunctions explicit in the resulting statements. -/
infixr:30 " ⋏ " => And.intro

/-- A nonempty consecutive block of agent indices, expanded to the literal finite set. -/
macro:max "indices" a:num n:num : term =>
  `({$[$((Array.range' a.getNat n.getNat).map Lean.quote):term],*})

/-- Common seven-agent rows; `d` is the length of row one, and `c` is the central row. -/
macro "sevenTable" d:num c:term:max : term =>
  `(![{0}, indices 0 $d, indices 1 4, $c, indices 2 4,
      indices $(Lean.quote (7 - d.getNat)) $d, {6}])

/-- Rows shared by SBC6 and SBC9, optionally followed by spectator rows. -/
macro:max "sbcTable" xs:term,* : term =>
  `(![{0}, indices 0 3, indices 0 4, indices 2 4, indices 3 3, {5}, $xs,*])

notation "sbcRate" => (-1 / 6 : ℝ)

/-- The affine line through `L` in direction `v`. Expanding this notation retains the original
coordinate formulas in the public closed forms. -/
notation:max "affine" L:max v:max a:max => (fun i => L i + a * v i)

/-- A strictly negative, contractive geometric rate. -/
notation "negativeRate" q:max => (-1 < q ∧ q < 0)

section
variable (m : Model) {n : ℕ} (r z y x₀ xinf : Opinions n)

theorem neg_pow_facts (q : ℝ) (h : negativeRate q) (t) :
    q ^ t ∈ Set.Icc q 1 ∧ -1 ≤ q ^ t ∧ (if Even t then 0 < q ^ t else q ^ t < 0) := by
  induction t <;> simp_all [pow_succ, Nat.even_add_one, -Nat.not_even_iff_odd] <;>
    (try split_ifs at *) <;> and_intros <;> nlinarith

theorem sqrt_bounds : Real.sqrt 2 ∈ Set.Ioo 1.4 1.5 ∧
    Real.sqrt 249 ∈ Set.Ioo 15 16 ∧ Real.sqrt 5 ∈ Set.Ioo 2 3 := by norm_num [Real.lt_sqrt, Real.sqrt_lt']

/-- All four geometric rates are negative and contractive. -/

theorem rate_bounds :
    negativeRate sbiRate ∧ |sbiRate| < 1/4 ∧
    negativeRate sbc5Rate ∧ negativeRate sbi6Rate := by
  grind [sbiRate, sbc5Rate, sbi6Rate, sqrt_bounds]

/-- Exhaust the two finite agent indices and discharge each distance comparison. -/
macro "hk_table" : tactic =>
  `(tactic| (have := sqrt_bounds; simp_all +zetaDelta [-Nat.not_even_iff_odd, -inv_nonneg, one_div, inv_pow, sbiRate, Real.goldenRatio, Real.goldenConj, Fin.reduceSucc, pow_add]; simp [neighbors, Model.bound] <;>
    and_intros <;> intros <;> nlinarith))

/-- Compute finite averaging rows, using ring normalization modulo the algebraic rates. -/
macro "hk_mean" tab:Lean.Parser.Tactic.simpLemma : tactic =>
  `(tactic| (simp only [funext_iff, adjMatrix, Matrix.mulVec, dotProduct, $tab]; simp [sbc5Rate, sbi6Rate, sbiRate, pow_succ, sbi5Offset] <;>
    grind [Real.sq_sqrt]))

macro "hk_traj" t:ident tab:Lean.Parser.Tactic.simpLemma : tactic =>
  `(tactic| (induction $t:ident with
    | zero => norm_num [traj, sbi5_x0]
    | succ $t:ident ih => rw [traj, Function.iterate_succ_apply', ← traj, ih, step]; hk_mean $tab))

/-- Shared data and consequences of a nonzero negative geometric mode. -/
structure OscillatingMode where
  (L v : Opinions n)
  q : ℝ
  N : ℕ → _
  law : ∀ t, m.neighbors r (affine L v (q ^ t)) = N t ∧ ∀ a,
    (m.adjMatrix r (affine L v (q ^ t))).mulVec
      (affine L v a) = affine L v (q * a) := by
    intro t
    try split_ifs
    all_goals
      suffices h : neighbors _ _ _ = _ from h ⋏ by intro; hk_mean h
      let q : ℝ := ?_
      change neighbors _ _ (_ + q ^ t • _) = _
      have hp := neg_pow_facts q (by norm_num +zetaDelta) t
      try
        have := mul_le_mul_of_nonneg_right
          hp.2.1 (le_of_lt (by assumption))
      hk_table
  valid : negativeRate q ∧ x₀ = L + v ∧ v ≠ 0 ∧ ∀ i, 0 < r i := by
    norm_num [sbc5Family_x0] <;> grind

attribute [class] OscillatingMode

theorem digraph_constant_of_neighbors {m r x₀ N}
    (hN : ∀ t, @neighbors m n r (m.traj r x₀ t) = N) (t) :
    m.proximityDigraph r (m.traj r x₀ t) = m.proximityDigraph r x₀ := by
  simp only [proximityDigraph, hN, show m.neighbors r x₀ = N from hN 0]

namespace OscillatingMode

variable {m r x₀} [g : OscillatingMode m r x₀] (t τ : ℕ)
include g
local notation "x" => m.traj r x₀

theorem closed : x t = affine g.L g.v (g.q ^ t) := by
  induction t <;> simp_all [traj, Function.iterate_succ_apply', step, g.law,
    pow_succ', Pi.add_def, g.valid.2.1]

attribute [simp] closed law

theorem neighbors : m.neighbors r (x t) = g.N t := by simp

theorem tendsto : Tendsto x atTop (𝓝 g.L) := by
  simpa [funext g.closed, Pi.add_def] using
    ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one
      (by grind [g.valid.1])).smul_const g.v).const_add g.L

theorem fvct : m.fvct r (x t) = g.L := by
  apply Tendsto.limUnder_eq
  convert g.tendsto.comp (tendsto_add_atTop_nat t) using 1
  funext k
  induction k <;> simp_all [pow_succ', ← Matrix.mulVec_mulVec, Nat.succ_add]

/- Coordinatewise normal forms are enabled after the abstract vector identities above. -/
attribute [simp high] rate_bounds Real.inv_goldenRatio abs_le Function.iterate_succ_apply' funext_iff Finset.ext_iff Fin.forall_fin_succ Fin.exists_fin_succ
  Fin.sum_univ_succ Matrix.vecHead Matrix.vecTail

theorem not_fixedFrom : ¬ FixedFrom x τ := by
  have := g.valid.2.2.1
  simp_all [FixedFrom]
  grind [g.valid.1.2, pow_succ g.q τ, pow_eq_zero_iff]

theorem not_pseudoStableAfter (y) (τ) : ¬ PseudoStableAfter x y τ := by
  rintro ⟨hlim, F, C, -, ⟨i, hi⟩, -, -, h⟩
  cases tendsto_nhds_unique hlim g.tendsto
  rcases (h τ le_rfl).2 i hi with h | h <;>
    simp [pow_succ] at h <;> nlinarith [g.valid.1.2]

attribute [simp↓] not_fixedFrom not_pseudoStableAfter fvct

theorem perStepFactor (i)
    (hi : g.v i ≠ 0 := by
      fin_cases i <;> simp_all <;> grind [Real.sqrt_nonneg]) :
    m.perStepFactor r x i t = g.q := by
  simp [HK.perStepFactor, pow_succ,
    mul_div_mul_right, g.valid.1.2.ne, hi]

/-- A negative geometric mode cannot have a non-negative asymptotic per-step factor. -/
theorem factor_no_limit (i)
    (hi : g.v i ≠ 0 := by fin_cases i <;> simp_all <;> grind [Real.sqrt_nonneg]) (ρ) (hρ : 0 ≤ ρ) :
    ¬ Tendsto (fun t => m.perStepFactor r x i t) atTop (𝓝 ρ) := by
  simp_all [g.perStepFactor _ _ hi]
  linarith [g.valid.1.2]

theorem refute23 : ¬ m.Conjecture23ForAgents n := by
  intro h
  simpa using h r x₀ g.valid.2.2.2

theorem refute64 (hN : ∀ t, m.neighbors r (x t) = g.N 0 := by intro; apply OscillatingMode.neighbors) :
    ¬ m.Theorem64ivForAgents n := by
  intro h
  simpa using h r x₀ g.valid.2.2.2 0 (fun t _ => digraph_constant_of_neighbors hN t)

theorem flips (i j)
    (hN : ∀ t, j ∈ g.N (t + 1) i ↔ j ∉ g.N t i := by
      intro; simp [Nat.even_add_one, mem_ite, ← Nat.not_even_iff_odd]) :
    ∃ t, τ ≤ t ∧ m.proximityDigraph r (x t) ≠ m.proximityDigraph r (x τ) := by
  refine ⟨_, Nat.le_succ _, fun h => ?_⟩
  simpa [proximityDigraph, g.neighbors, hN] using congr($(h).Adj i j)

end OscillatingMode
/- Specialize a mode theorem, exposing just its certificate fields. Re-elaboration gives
canonical vector notation and instances; the kernel still checks the specialized proof. -/
open Lean Meta Elab Term in
elab "mode_type% " p:term : term => do
  let t ← transform (← inferType (← elabTerm p none) >>= instantiateMVars) (post := fun e => do
    if let some e' ← reduceProjOf? e (· == ``OscillatingMode) then
      return .visit e'
    if let some e' ← reduceProj? e then return .visit e'
    return .done e.headBeta)
  elabTerm (← Lean.PrettyPrinter.delab t) none
macro "specialization " n:ident bs:bracketedBinder* " := " p:term : command =>
  `(command| theorem $n $bs* : mode_type% $p := $p)


theorem proximityDigraph_eq_of_equiTopologyNbhd
    (h : EquiTopologyNbhd r z y) : m.proximityDigraph r y = m.proximityDigraph r z := by
  have bound {i j : Fin n} (hij : j ≠ i) :
      equiTopologyDistance r z i ∈ Set.Icc 0
        (1 / 2 * min |(|z i - z j|) - r i| |(|z i - z j|) - r j|) := by
    unfold equiTopologyDistance
    refine mul_nonneg one_half_pos.le (Real.sInf_nonneg (by aesop)) ⋏ ?_
    gcongr
    apply le_min <;> apply csInf_le ⟨0, by intro; aesop⟩ <;> aesop
  ext i j
  simp [proximityDigraph, neighbors]
  cases m <;> grind [EquiTopologyNbhd, Model.bound, @bound i j, @bound j i]

local notation "x" => m.traj r x₀
variable (hconv : Tendsto (m.traj r x₀) atTop (𝓝 xinf))
    (hε : ∀ i, 0 < equiTopologyDistance r xinf i)
include hconv hε

theorem eventually_constant_of_tendsto :
    ∃ T, ∀ t, T ≤ t → m.proximityDigraph r (x t) = m.proximityDigraph r xinf  := by
  apply Filter.eventually_atTop.1
  filter_upwards [Filter.eventually_all.2 fun i =>
    Metric.tendsto_nhds.mp ((tendsto_pi_nhds.mp hconv) i) _ (hε i)] with t ht
  apply proximityDigraph_eq_of_equiTopologyNbhd
  simpa [EquiTopologyNbhd, Real.dist_eq, hε, (hε _).ne'] using ht

theorem fvct_eq_and_equilibrium_of_tendsto :
    (∃ T, ∀ t, T ≤ t → m.fvct r (x t) = xinf) ∧ m.step r xinf = xinf := by
  obtain ⟨T, hT⟩ := eventually_constant_of_tendsto m r x₀ xinf hconv hε
  have hadj : ∀ t, T ≤ t → m.adjMatrix r (x t) = m.adjMatrix r xinf := by
    intro t ht
    simp only [adjMatrix, show m.neighbors r (x t) = m.neighbors r xinf from by
      simpa [proximityDigraph] using hT t ht]
  refine ⟨T, fun t ht => ?_⟩ ⋏ ?_
  · apply Tendsto.limUnder_eq
    rw [hadj t ht]
    convert hconv.comp (tendsto_add_atTop_nat t) using 1
    funext k
    induction k <;>
      simp only [traj] at * <;>
      simp (disch := omega) [*, pow_succ', ← Matrix.mulVec_mulVec, Nat.succ_add,
        traj, step]
  · exact tendsto_nhds_unique_of_eventuallyEq
      (((continuous_const.matrix_mulVec continuous_id).tendsto xinf).comp hconv)
      (hconv.comp (tendsto_add_atTop_nat 1))
      (Filter.eventually_atTop.2 ⟨T, fun t ht => by simp [← hadj t ht, traj, step]⟩)

end

section
variable (t τ : ℕ)

/-! ## SBC7 data -/

abbrev sbc7_mode : OscillatingMode .sbc sbc7_r sbc7_x0 :=
  .mk sbc7_lim sbc7_v sbcRate (fun t => sevenTable 3 (ite (Even t) {3} indices 2 3))

/-! ## SBI7 data -/

abbrev sbi7_mode : OscillatingMode .sbi sbi7_r sbi7_x0 :=
  .mk sbi7_lim (sbi_v / 2) sbiRate (fun t => sevenTable 4 (ite (Even t) indices 1 5 indices 2 3))

/-! ## SBC6 data -/

/-- §4: the closed form. -/
abbrev sbc6_mode : OscillatingMode .sbc sbc6_r sbc6_x0 :=
  .mk sbc6_lim sbc6_v sbcRate (fun _ => sbcTable)

/-! ## SBI7b data -/

/-- §5: the closed form. -/
abbrev sbi7b_mode : OscillatingMode .sbi sbi7b_r sbi7b_x0 :=
  .mk sbi7b_lim sbi_v sbiRate (fun _ => sevenTable 4 indices 2 3)

/-! ## SBC5 data -/

notation "sbc5_N" => ![{0}, indices 0 3, indices 1 3, indices 2 3, {4}]

/-- One certificate for the whole five-agent family; the original example is its unit-amplitude
specialization. -/
abbrev sbc5Family_mode (δ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    OscillatingMode .sbc (sbc5Family_r δ) (sbc5Family_x0 δ) :=
  .mk sbc5_lim (δ • sbc5_v) sbc5Rate (fun _ => sbc5_N)

abbrev sbc5_mode : OscillatingMode .sbc sbc5_r sbc5_x0 :=
  .mk sbc5_lim sbc5_v sbc5Rate (fun _ => sbc5_N)

/-! ## SBI6 data -/

/-- The six-agent SBI certificate. -/
abbrev sbi6_mode : OscillatingMode .sbi sbi6_r sbi6_x0 :=
  .mk sbi6_lim sbi6_v sbi6Rate (fun _ => ![{0}, indices 0 4, indices 0 5, insert 0 (indices 2 4), indices 2 4, {5}])

attribute [instance] sbc7_mode sbi7_mode sbc6_mode sbi7b_mode sbc5_mode sbi6_mode

/-! ## SBC7 consequences -/
specialization sbc7_closed_form := sbc7_mode.closed

specialization sbc7_neighbors := sbc7_mode.neighbors

specialization sbc7_digraph_not_eventually_constant := sbc7_mode.flips τ 3 2

/-! ## SBI7 consequences -/
theorem sbi7_closed_form :
    Model.sbi.traj sbi7_r sbi7_x0 t = affine sbi7_lim sbi_v (sbiRate ^ t / 2) := by simp [div_mul_eq_mul_div, ← mul_div_assoc]

specialization sbi7_neighbors := sbi7_mode.neighbors

specialization sbi7_digraph_not_eventually_constant := sbi7_mode.flips τ 3 1

/-! ## SBC6 consequences -/
specialization sbc6_closed_form := sbc6_mode.closed

/- §4: the neighbourhood table, the same at every `t`. -/
specialization sbc6_neighbors := sbc6_mode.neighbors

specialization sbc6_digraph_constant := digraph_constant_of_neighbors sbc6_neighbors

specialization sbc6_fvct := sbc6_mode.fvct

section
variable (i : Fin 6) (hi : i ∈ (indices 1 4 : Finset _))
include hi

specialization sbc6_perStepFactor := sbc6_mode.perStepFactor t i

specialization sbc6_perStepFactor_not_tendsto := sbc6_mode.factor_no_limit i

end

/-! ## SBI7b consequences -/
specialization sbi7b_closed_form := sbi7b_mode.closed

/- §5: the neighbourhood table, the same at every `t`. -/
specialization sbi7b_neighbors := sbi7b_mode.neighbors

specialization sbi7b_fvct := sbi7b_mode.fvct

specialization sbi7b_digraph_constant := digraph_constant_of_neighbors sbi7b_neighbors

section
variable (i : Fin 7) (hi : i ∈ ({1, 2, 4, 5} : Finset _))
include hi

specialization sbi7b_perStepFactor := sbi7b_mode.perStepFactor t i

specialization sbi7b_perStepFactor_not_tendsto := sbi7b_mode.factor_no_limit i

end

/-! ## SBC5 consequences -/
specialization sbc5_closed_form := sbc5_mode.closed

specialization sbc5_neighbors := sbc5_mode.neighbors

specialization not_conjecture23_sbc_five := sbc5_mode.refute23

specialization not_theorem64iv_sbc_five := sbc5_mode.refute64

/- The final value at constant topology along the trajectory is the limit at every `t`. -/
specialization sbc5_fvct := sbc5_mode.fvct

/- The per-step convergence factor of agents 1, 2, 3 is `λ` at every `t`. -/
specialization sbc5_perStepFactor (i) (hi : i ∈ (indices 1 3 : Finset _)) := sbc5_mode.perStepFactor t i

/-! ## SBI6 consequences -/
specialization sbi6_closed_form := sbi6_mode.closed

specialization sbi6_neighbors := sbi6_mode.neighbors

specialization not_conjecture23_sbi_six := sbi6_mode.refute23

specialization not_theorem64iv_sbi_six := sbi6_mode.refute64

/- The final value at constant topology (Definition 3.1) is the limit at every `t`. -/
specialization sbi6_fvct := sbi6_mode.fvct

/- The per-step convergence factor (Definition 6.1) of agents 1–4 is the rate at every `t`. -/
specialization sbi6_perStepFactor (i) (hi : i ∈ (indices 1 4 : Finset _)) := sbi6_mode.perStepFactor t i

/-! ## Refute -/

theorem not_conjecture22_sbc_seven : ¬ Model.sbc.Conjecture22ForAgents 7 := by
  unfold Conjecture22ForAgents
  push Not
  exact ⟨sbc7_r, sbc7_x0, sbc7_mode.valid.2.2.2,
    sbc7_digraph_not_eventually_constant⟩

theorem not_conjecture22_sbi_seven : ¬ Model.sbi.Conjecture22ForAgents 7 := by
  unfold Conjecture22ForAgents
  push Not
  exact ⟨sbi7_r, sbi7_x0, sbi7_mode.valid.2.2.2,
    sbi7_digraph_not_eventually_constant⟩

theorem not_conjecture22_sbc : ¬ Model.sbc.Conjecture22For := mt (· 7) not_conjecture22_sbc_seven

theorem not_conjecture23_sbc : ¬ Model.sbc.Conjecture23For := mt (· 5) not_conjecture23_sbc_five

theorem not_conjecture22_sbi : ¬ Model.sbi.Conjecture22For := mt (· 7) not_conjecture22_sbi_seven

theorem not_conjecture23_sbi : ¬ Model.sbi.Conjecture23For := mt (· 6) not_conjecture23_sbi_six

theorem not_theorem64iv_sbc : ¬ Model.sbc.Theorem64ivFor := mt (· 5) not_theorem64iv_sbc_five

theorem not_theorem64iv_sbi : ¬ Model.sbi.Theorem64ivFor := mt (· 6) not_theorem64iv_sbi_six

theorem not_conjecture22 : ¬ Conjecture22 := mt (· .sbc) not_conjecture22_sbc

theorem not_conjecture23 : ¬ Conjecture23 := mt (· .sbc) not_conjecture23_sbc

theorem not_theorem64iv : ¬ Theorem64iv := mt (· .sbc) not_theorem64iv_sbc

theorem literal_implies {m} (h : Theorem64ivLiteralFor m) : m.Theorem64ivFor := by
  intro n r x hr τ ht
  specialize h n r x hr τ
  aesop

theorem not_theorem64iv_literal_sbc : ¬ Model.sbc.Theorem64ivLiteralFor := mt literal_implies not_theorem64iv_sbc

theorem not_theorem64iv_literal_sbi : ¬ Model.sbi.Theorem64ivLiteralFor := mt literal_implies not_theorem64iv_sbi

theorem not_theorem64iv_literal : ¬ Theorem64ivLiteral :=
  mt (· .sbc) not_theorem64iv_literal_sbc

specialization tendsto_limits := sbc7_mode.tendsto ⋏ sbi7_mode.tendsto ⋏ sbc6_mode.tendsto ⋏ sbi7b_mode.tendsto

specialization not_fixedFrom := sbc7_mode.not_fixedFrom τ ⋏ sbi7_mode.not_fixedFrom τ ⋏ sbc6_mode.not_fixedFrom τ ⋏ sbi7b_mode.not_fixedFrom τ

specialization not_pseudoStableAfter (xinf) (yinf) (τ) :=
  sbc7_mode.not_pseudoStableAfter xinf τ ⋏ sbi7_mode.not_pseudoStableAfter xinf τ ⋏
    sbc6_mode.not_pseudoStableAfter yinf τ ⋏ sbi7b_mode.not_pseudoStableAfter xinf τ

specialization alternating_fvct := sbc7_mode.fvct t ⋏ sbi7_mode.fvct t

attribute [local simp] equiTopologyDistance Set.ofPred_or Set.ofPred_eq_eq_singleton csInf_insert

theorem equiTopologyDistance_pos :
    (∀ i, 0 < equiTopologyDistance sbc6_r sbc6_lim i) ∧
    (∀ i, 0 < equiTopologyDistance sbi7b_r sbi7b_lim i) := by
  norm_num

theorem equiTopologyDistance_eq_zero :
    (∀ i ∈ (indices 2 3 : Finset _), equiTopologyDistance sbc7_r sbc7_lim i = 0) ∧
    (∀ i ∈ ({1, 3, 5} : Finset _), equiTopologyDistance sbi7_r sbi7_lim i = 0) := by
  norm_num

specialization small_tendsto  := sbc5_mode.tendsto ⋏ sbi6_mode.tendsto

specialization small_digraph_constant := digraph_constant_of_neighbors sbc5_neighbors t ⋏ digraph_constant_of_neighbors sbi6_neighbors t

specialization small_not_fixedFrom := sbc5_mode.not_fixedFrom τ ⋏ sbi6_mode.not_fixedFrom τ

specialization small_not_pseudoStableAfter (xinf) (yinf) (τ) := sbc5_mode.not_pseudoStableAfter xinf τ ⋏ sbi6_mode.not_pseudoStableAfter yinf τ

/-! ## SpectatorSBC -/

/-- The SBC-9 opinion vector at the atoms `u` (the `(−1/6)ᵗ` offset) and `w` (the `(1/5)ᵗ` offset). -/
local notation:max "spe_sbc9_vec" u:max w:max =>
  ![0, 20 + 2 * u, 40 - 3 * u, 100 + 3 * u, 120 - 2 * u, 140, 210 + 12 / 11 * (u - w), 280, 300]

/-- The SBC-9 table along the two geometric modes. -/
local notation "sbc9_N" => sbcTable indices 4 5, {7}, {8}

theorem spe_sbc9_table :
    Model.sbc.neighbors sbc9_r (spe_sbc9_vec (sbcRate ^ t) ((1 / 5) ^ t)) = sbc9_N := by
  have := neg_pow_facts sbcRate (by norm_num) t
  have : (1 / 5 : ℝ) ^ t ∈ Set.Icc 0 1 := by constructor <;> bound
  hk_table

theorem sbc9_closed_form :
    Model.sbc.traj sbc9_r sbc9_x0 t =
      spe_sbc9_vec (sbcRate ^ t) ((1 / 5) ^ t) := by hk_traj t (spe_sbc9_table t)

specialization sbc9_neighbors := (congrArg (Model.sbc.neighbors sbc9_r) (sbc9_closed_form t)).trans (spe_sbc9_table t)

theorem sbc9_spectator_lt  (ht : 1 ≤ t) : Model.sbc.traj sbc9_r sbc9_x0 t 6 < 210 := by
  have h := pow_lt_pow_left₀ (by norm_num : |sbcRate| < 1 / 5) (abs_nonneg _)
    (ne_of_gt ht)
  rw [← abs_pow, abs_lt] at h
  norm_num [sbc9_closed_form]
  linarith

/-! ## SpectatorSBI -/

/-- The state on the box: `u = λᵗ`, `w = (1/4)ᵗ`. -/
local notation:max "spe_x" u:max w:max =>
  ![0, 60 + Real.goldenRatio⁻¹ * (w - u), 70 + u, 100 - Real.goldenRatio * u, 110,
    120 + Real.goldenRatio * u, 150 - u, 220]

/-- The table along the two geometric modes. -/
local notation "sbi8_N" => ![{0}, {0, 1, 2, 4}, insert 0 (indices 2 3), indices 2 4, indices 3 3, indices 3 4, indices 4 4, {7}]

theorem spe_table :
    Model.sbi.neighbors sbi8_r (spe_x (sbiRate ^ t) ((1 / 4) ^ t)) = sbi8_N := by
  have := neg_pow_facts sbiRate rate_bounds.1 t
  have : (1 / 4 : ℝ) ^ t ∈ Set.Icc 0 1 := by constructor <;> bound
  hk_table

theorem sbi8_closed_form :
    Model.sbi.traj sbi8_r sbi8_x0 t =
      spe_x (sbiRate ^ t) ((1 / 4) ^ t) := by hk_traj t (spe_table t)

specialization sbi8_neighbors := (congrArg (Model.sbi.neighbors sbi8_r) (sbi8_closed_form t)).trans (spe_table t)

theorem sbi8_spectator_gt  (ht : 1 ≤ t) : 60 < Model.sbi.traj sbi8_r sbi8_x0 t 1 := by
  have h := pow_lt_pow_left₀ rate_bounds.2.1 (abs_nonneg _) (ne_of_gt ht)
  rw [← abs_pow, abs_lt] at h
  norm_num [sbi8_closed_form]
  nlinarith [Real.goldenConj_neg]

/-! ## SBC5Family -/

section
variable (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (t : ℕ)

include hδ0 hδ1
theorem sbc5Family_closed_form :
    Model.sbc.traj (sbc5Family_r δ) (sbc5Family_x0 δ) t =
      affine sbc5_lim sbc5_v (sbc5Rate ^ t * δ) := by simpa [mul_assoc] using (sbc5Family_mode δ hδ0 hδ1).closed t

specialization sbc5Family_neighbors := (sbc5Family_mode δ hδ0 hδ1).neighbors

end

theorem sbc5_near_homogeneous (ε) (hε : 0 < ε) :
    ∃ r x₀,
      (∀ i, 0 < r i) ∧
      (∀ i j, r i < (1 + ε) * r j) ∧
      r 0 < r 1 ∧
      (∀ t, Model.sbc.proximityDigraph r (Model.sbc.traj r x₀ t) =
        Model.sbc.proximityDigraph r x₀) ∧
      Tendsto (Model.sbc.traj r x₀) atTop (𝓝 sbc5_lim) ∧
      (∀ τ, ¬ FixedFrom (Model.sbc.traj r x₀) τ) ∧
      (∀ xinf τ, ¬ PseudoStableAfter (Model.sbc.traj r x₀) xinf τ) := by
  let δ := ε / (2 + ε)
  let g := sbc5Family_mode δ (by positivity) (by bound)
  refine ⟨sbc5Family_r δ, sbc5Family_x0 δ, g.valid.2.2.2, ?_, ?_,
    digraph_constant_of_neighbors g.neighbors,
    g.tendsto, g.not_fixedFrom, g.not_pseudoStableAfter⟩
  all_goals
    norm_num [δ]
    and_intros <;> field_simp <;> nlinarith

end

local notation:max "cubic" z:max => 60 * z ^ 3 - 47 * z ^ 2 + 9 * z - 1

variable (ρ : ℝ) (hlo : 57 / 100 < ρ) (hhi : ρ < 29 / 50)
  (hp : cubic ρ = 0) (t : ℕ)

local notation "x" => Model.sbi.traj sbi5_r (sbi5_x0 ρ)
local notation "u" => sbi5Offset ρ
local notation "α" => (47 / 60 - ρ)
local notation "β" => (ρ ^ 2 - 47 / 60 * ρ + 3 / 20)

theorem sbi5_root_exists : ∃ ρ : ℝ, 57 / 100 < ρ ∧ ρ < 29 / 50 ∧
    cubic ρ = 0 := by
  simp only [← and_assoc]
  exact intermediate_value_Ioo (by norm_num) (by fun_prop) (by norm_num)

include hp in
theorem sbi5_offset_recurrence :
    u (t + 2) = fun i => α * u (t + 1) i - β * u t i := by
  induction t <;>
    simp_all [sbi5Offset] <;> and_intros <;> nlinarith

section
include hlo hhi

theorem sbi5_offset_bound : ∀ i, |u t i| ≤ (2 / 3 : ℝ) ^ (t + 2) := by
  induction t <;>
    simp_all [sbi5Offset, pow_succ] <;>
    grind

local notation "sbi5_N" => ![{0}, {0, 1, 3}, indices 0 5, insert 0 (indices 2 3), {4}]

theorem sbi5_table :
    Model.sbi.neighbors sbi5_r (sbi5_lim + sbi5Lift (u t)) =
      sbi5_N := by
  have := sbi5_offset_bound ρ hlo hhi t
  have : (2 / 3 : ℝ) ^ t ≤ 1 := by bound
  hk_table

@[simp] theorem sbi5_trajectory : x t = sbi5_lim + sbi5Lift (u t) := by hk_traj t (sbi5_table ρ hlo hhi t)

theorem sbi5_neighbors : Model.sbi.neighbors sbi5_r (x t) = sbi5_N := by
  simp_all only [sbi5_trajectory, sbi5_table]

theorem sbi5_tendsto :
    Tendsto x atTop (𝓝 sbi5_lim) := by
  rw [← tendsto_sub_nhds_zero_iff]
  simp_all [tendsto_pi_nhds]
  and_intros <;>
    exact squeeze_zero_norm (fun t => sbi5_offset_bound ρ hlo hhi t _)
      ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)).comp
        (tendsto_add_atTop_nat 2))

specialization sbi5_digraph_constant := digraph_constant_of_neighbors (sbi5_neighbors ρ hlo hhi)

set_option quotPrecheck false in
local notation:max "bothSides" f:max i:max a:max =>
  ((∃ k, t ≤ k ∧ k ≤ t + 4 ∧ f k i < a) ∧
    (∃ k, t ≤ k ∧ k ≤ t + 4 ∧ a < f k i))

include hp
theorem sbi5_oscillates_every_five (i) (hi : i ∈ (indices 1 3 : Finset _)) :
    bothSides x i (sbi5_lim i) := by
  have (i : Fin 3) :
      bothSides u i 0 := by
    have : β * (β - α ^ 2) < 0 := by nlinarith
    have hnz : ¬ (u t i = 0 ∧ u (t + 1) i = 0) := by
      induction t with
      | zero =>
        fin_cases i <;> simp [sbi5Offset]
        linarith
      | succ t ih => grind [sbi5_offset_recurrence ρ hp]
    have hrec := congrFun (sbi5_offset_recurrence ρ hp (t + 2)) i
    conv_rhs at hrec => simp only [sbi5_offset_recurrence ρ hp]
    constructor <;> by_contra! hn <;> apply hnz <;> constructor <;>
      (replace hn (k : Fin 5) := hn (t + k) (by omega) (by omega)
       simp_all
       nlinarith)
  fin_cases i <;> simp_all

@[simp↓] theorem sbi5_not_fixedFrom (τ) :
    ¬ FixedFrom x τ := by
  have := sbi5_oscillates_every_five ρ hlo hhi hp τ 1 (by simp)
  simp [FixedFrom]
  grind

@[simp↓] theorem sbi5_not_pseudoStableAfter (xinf) (τ) :
    ¬ PseudoStableAfter x xinf τ := by
  rintro ⟨hlim, F, C, -, -, -, hFC, h⟩
  cases tendsto_nhds_unique hlim (sbi5_tendsto ρ hlo hhi)
  obtain ⟨⟨k, hk0, -, hk⟩, ⟨l, hl0, -, hl⟩⟩ :=
    sbi5_oscillates_every_five ρ hlo hhi hp τ 1 (by simp)
  have := Finset.mem_univ (1 : Fin 5)
  have : ∀ t, τ ≤ t → (x t 1 < sbi5_lim 1 ↔ x τ 1 < sbi5_lim 1) :=
    Nat.le_induction Iff.rfl (by grind)
  grind

end

theorem not_conjecture23_sbi_five : ¬ Model.sbi.Conjecture23ForAgents 5 := by
  obtain ⟨ρ, hlo, hhi, hp⟩ := sbi5_root_exists
  intro h
  have := h sbi5_r (sbi5_x0 ρ) (by norm_num)
  simp_all

theorem not_theorem64iv_sbi_five : ¬ Model.sbi.Theorem64ivForAgents 5 := by
  obtain ⟨ρ, hlo, hhi, hp⟩ := sbi5_root_exists
  intro h
  have := h sbi5_r (sbi5_x0 ρ) (by norm_num) 0
    (fun t _ => sbi5_digraph_constant ρ hlo hhi t)
  simp_all

end HK
