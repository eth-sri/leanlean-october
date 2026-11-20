module

public import HK.Defs

@[expose] public section

namespace HK

open Filter Topology

variable {n : ℕ} {m : Model} {r x y L v : Fin n → ℝ} {X Y : ℕ → Fin n → ℝ}
  {q : ℝ} {N : Fin n → Finset (Fin n)} {T : ℕ → Fin n → Finset (Fin n)}

noncomputable def average (N : Fin n → Finset (Fin n)) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  (∑ j ∈ N i, x j) / (N i).card

theorem adj_mulVec (z : Fin n → ℝ) : (adjMatrix m r y).mulVec z = average (neighbors m r y) z := by
  funext i
  simp [adjMatrix, Matrix.mulVec, dotProduct, Finset.sum_ite_mem, average, div_eq_mul_inv,
    Finset.sum_mul, mul_comm]

theorem traj_succ (t : ℕ) : traj m r x (t + 1) = step m r (traj m r x t) :=
  Function.iterate_succ_apply' ..

theorem traj_of_average (hN : ∀ t, neighbors m r (Y t) = T t)
    (hs : ∀ t, average (T t) (Y t) = Y (t + 1)) (h0 : Y 0 = x) (t : ℕ) : traj m r x t = Y t := by
  induction t with
  | zero => exact h0.symm
  | succ t ih => rw [traj_succ, ih, step, adj_mulVec, hN, hs]

/-- The opinion profile with offset `u` along the direction `v` from `L`. -/
scoped notation "profile" L:max u:max v:max => (fun i => L i + u * v i)

/-- Evaluate a concrete vector equality, including the finite sums in an averaging step. -/
syntax "check_rows" Lean.Parser.Tactic.simpArgs : tactic
macro_rules
  | `(tactic| check_rows [$ds,*]) =>
    `(tactic| ((try split_ifs) <;> (funext i; fin_cases i <;>
      norm_num [average, Finset.sum_insert, $ds,*] <;>
      ring_nf <;> norm_num [Real.sq_sqrt, Real.goldenRatio_sq] <;> ring_nf)))

/-- A certificate for an affine orbit in a single, contracting negative mode.
The default row checks use the example data in the local simp set. -/
structure ModeOrbit (m : Model) (r x L v : Fin n → ℝ) (q : ℝ)
    (T : ℕ → Fin n → Finset (Fin n)) : Prop where
  rate : -1 < q ∧ q < 0 := by norm_num
  initial : L + v = x := by check_rows []
  table (t : ℕ) : neighbors m r (L + q ^ t • v) = T t
  mode (t : ℕ) (u : ℝ) : average (T t) (L + u • v) = L + (q * u) • v := by intro _ _; check_rows []

/-- If the frozen matrix acts like the actual update on a tail, both orbits have the same limit. -/
theorem fvct_of_tail (t : ℕ) (hc : Tendsto X atTop (𝓝 L))
    (hs : ∀ k ≥ t, (adjMatrix m r (X t)).mulVec (X k) = X (k + 1)) : fvct m r (X t) = L := by
  have h (k : ℕ) : (adjMatrix m r (X t) ^ k).mulVec (X t) = X (k + t) := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, hs _ (by omega), Nat.succ_add]
  exact ((hc.comp (tendsto_add_atTop_nat t)).congr fun k => (h k).symm).limUnder_eq

theorem digraph_eq_iff : proximityDigraph m r y = proximityDigraph m r x ↔
    neighbors m r y = neighbors m r x := by
  simp [proximityDigraph, funext_iff, Finset.ext_iff]

theorem digraph_constant (hN : ∀ t, neighbors m r (traj m r x t) = N) (t : ℕ) :
    proximityDigraph m r (traj m r x t) = proximityDigraph m r x :=
  digraph_eq_iff.mpr ((hN t).trans (hN 0).symm)

theorem neg_pow_bounds {a : ℝ} (hlo : -1 ≤ a) (ha : a ≤ q) (hq : q ≤ 0) (t : ℕ) :
    a ≤ q ^ t ∧ q ^ t ≤ 1 := by
  induction t with
  | zero => simp; linarith
  | succ t ih =>
    have := hlo.trans ih.1
    have := hlo.trans ha
    rw [pow_succ]
    and_intros <;> nlinarith [ih.2]

theorem sbiRate_eq : sbiRate = (1 - Real.goldenRatio) / 4 := by
  unfold sbiRate Real.goldenRatio
  ring

theorem sbiRate_neg : sbiRate < 0 := by
  rw [sbiRate_eq]
  linarith [Real.one_lt_goldenRatio]

theorem sbiRate_abs_lt_quarter : |sbiRate| < 1 / 4 := by
  rw [abs_of_neg sbiRate_neg, sbiRate_eq]
  linarith [Real.goldenRatio_lt_two]

theorem sbiRate_decay : -1 < sbiRate ∧ sbiRate < 0 :=
  ⟨by linarith [neg_le_abs sbiRate, sbiRate_abs_lt_quarter], sbiRate_neg⟩

theorem sbiRate_pow_bounds (t : ℕ) : -1 / 4 ≤ sbiRate ^ t ∧ sbiRate ^ t ≤ 1 :=
  neg_pow_bounds (by norm_num) (by linarith [neg_le_abs sbiRate, sbiRate_abs_lt_quarter]) sbiRate_neg.le t

theorem sixth_pow_bounds (t : ℕ) : -1 / 6 ≤ (-1 / 6 : ℝ) ^ t ∧ (-1 / 6 : ℝ) ^ t ≤ 1 :=
  neg_pow_bounds (by norm_num) le_rfl (by norm_num) t

/-- Absolute domination of the bases gives strict order at positive exponents. -/
theorem pow_lt_of_abs_lt {p : ℝ} (hq : |q| < p) {t : ℕ} (ht : 1 ≤ t) : q ^ t < p ^ t :=
  (le_abs_self _).trans_lt (by rw [abs_pow]; exact pow_lt_pow_left₀ hq (abs_nonneg _) (by omega))

def NeverStable (X : ℕ → Fin n → ℝ) : Prop :=
  (∀ τ, ¬ FixedFrom X τ) ∧ ∀ L τ, ¬ PseudoStableAfter X L τ

/-- A coordinate visiting both sides arbitrarily late rules out both forms of stabilization. -/
theorem neverStable_of_crossing {i : Fin n} (hc : Tendsto X atTop (𝓝 L))
    (ho : ∀ τ, (∃ k ≥ τ, X k i < L i) ∧ ∃ l ≥ τ, L i < X l i) : NeverStable X := by
  constructor
  · intro τ hf
    specialize ho τ
    grind [FixedFrom]
  · intro L' τ hp
    have e := tendsto_nhds_unique hp.1 hc
    subst L'
    obtain ⟨-, F, C, -, -, -, hFC, h⟩ := hp
    obtain ⟨⟨k, hk, hlt⟩, ⟨l, hl, hgt⟩⟩ := ho τ
    have hi : i ∈ F ∨ i ∈ C := by rw [← Finset.mem_union, hFC]; simp
    rcases hi with hi | hi
    · linarith [(h k hk).1 i hi]
    have side (t) (ht : τ ≤ t) : X τ i < L i ↔ X t i < L i := by
      induction t, ht using Nat.le_induction with
      | base => rfl
      | succ t ht ih =>
        have := (h t ht).2 i hi
        grind
    exact lt_asymm ((side l hl).mp ((side k hk).mpr hlt)) hgt

theorem abs_lt_one_of_rate (h : -1 < q ∧ q < 0) : |q| < 1 := by grind [abs_lt]

section

variable (h : ModeOrbit m r x L v q T)
include h

theorem ModeOrbit.form (t : ℕ) : traj m r x t = L + q ^ t • v :=
  traj_of_average h.table (fun t => by rw [h.mode t, pow_succ']) (by simpa using h.initial) t

theorem ModeOrbit.neighborhoods (t : ℕ) : neighbors m r (traj m r x t) = T t := by
  rw [h.form, h.table]

theorem ModeOrbit.tendsto : Tendsto (traj m r x) atTop (𝓝 L) := by
  rw [funext h.form]
  simpa using ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one (abs_lt_one_of_rate h.rate)).smul_const v).const_add L

theorem ModeOrbit.frozenLimit (t : ℕ) : fvct m r (traj m r x t) = L :=
  fvct_of_tail t h.tendsto fun k _ => by
    rw [h.form k, adj_mulVec, h.neighborhoods t, h.mode t, h.form (k + 1), pow_succ']

theorem ModeOrbit.facts (i : Fin n) (hi : v i ≠ 0) :
    Tendsto (traj m r x) atTop (𝓝 L) ∧ NeverStable (traj m r x) := by
  refine ⟨h.tendsto, neverStable_of_crossing (i := i) h.tendsto fun τ => ?_⟩
  have hn := mul_ne_zero (pow_ne_zero τ h.rate.2.ne) hi
  have hneg := mul_neg_of_neg_of_pos h.rate.2 (sq_pos_of_ne_zero hn)
  have hflip : (q ^ τ * v i) * (q ^ (τ + 1) * v i) < 0 := by
    rw [pow_succ']; nlinarith only [hneg]
  simp only [h.form, Pi.add_apply, Pi.smul_apply, smul_eq_mul, lt_add_iff_pos_right]
  have := mul_neg_iff.mp hflip
  have := Nat.le_succ τ
  grind

theorem ModeOrbit.factor (t : ℕ) (i : Fin n) (hi : v i ≠ 0) : perStepFactor m r (traj m r x) i t = q := by
  rw [perStepFactor, h.frozenLimit]
  simp [h.form, pow_succ]
  field_simp [pow_ne_zero _ h.rate.2.ne]

theorem ModeOrbit.factor_not_tendsto (i : Fin n) (hi : v i ≠ 0) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ¬ Tendsto (fun t => perStepFactor m r (traj m r x) i t) atTop (𝓝 ρ) := by
  simpa only [h.factor _ i hi, tendsto_const_nhds_iff] using (h.rate.2.trans_le hρ).ne

end

theorem refute22 (hr : ∀ i, 0 < r i)
    (h : ∀ τ, ∃ t ≥ τ, proximityDigraph m r (traj m r x t) ≠ proximityDigraph m r (traj m r x τ)) :
    ¬ Conjecture22ForAgents m n := by
  intro H
  obtain ⟨τ, H⟩ := H r x hr
  specialize h τ
  grind

theorem refute23 (hr : ∀ i, 0 < r i) (h : NeverStable (traj m r x)) : ¬ Conjecture23ForAgents m n := by
  intro H
  have := H r x hr
  grind [NeverStable]

theorem refute64 (hr : ∀ i, 0 < r i)
    (hG : ∀ t, proximityDigraph m r (traj m r x t) = proximityDigraph m r x)
    (h : NeverStable (traj m r x)) : ¬ Theorem64ivForAgents m n := by
  intro H
  have := H r x hr 0 (fun t _ => hG t)
  grind [NeverStable]

/-- Verify each pair of indices in a concrete neighbourhood table. Use nonlinear arithmetic
for the remaining comparisons when an offset involves a product of two bounded quantities. -/
syntax "check_neighbors" Lean.Parser.Tactic.simpArgs : tactic
macro_rules
  | `(tactic| check_neighbors [$ds,*]) =>
    `(tactic| (
      simp [funext_iff, Finset.ext_iff, Fin.forall_fin_succ, neighbors, Model.bound, abs_le, $ds,*]
      and_intros <;> first
        | grind
        | (intros; nlinarith)))

end HK
