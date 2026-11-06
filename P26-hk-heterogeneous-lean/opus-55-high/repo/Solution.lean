module

public import HK.Defs

@[expose] public section

namespace HK

open Filter Topology

set_option maxHeartbeats 0

variable {n : ℕ} {m : Model} {r x₀ L v y z : Fin n → ℝ} {q c δ α β ρ : ℝ} {a u : ℕ → ℝ} {N : ℕ → Fin n → Finset (Fin n)} {x : ℕ → Fin n → ℝ} (t : ℕ) (i : Fin n)

theorem traj_succ :
    traj m r x₀ (t + 1) = step m r (traj m r x₀ t) :=
  Function.iterate_succ_apply' _ _ _

theorem adj_mulVec :
    (adjMatrix m r y).mulVec z i = (∑ j ∈ neighbors m r y i, z j) / (neighbors m r y i).card := by
  simp [adjMatrix, Matrix.mulVec, dotProduct, div_eq_inv_mul, Finset.mul_sum]

theorem pow_bounds (h0 : -1 ≤ q) (h1 : q ≤ 0) : q ≤ q ^ t ∧ q ^ t ≤ 1 := by
  induction t <;> simp_all [pow_succ] <;> (try constructor) <;> nlinarith

def b6 t := @pow_bounds (-1 / 6) t (by norm_num) (by norm_num)

theorem sign_pow (hq : q < 0) (hc : 0 < c) :
    if Even t then 0 < q ^ t ∧ 0 < q ^ t * c else q ^ t < 0 ∧ q ^ t * c < 0 := by
  split_ifs <;> simp_all [mul_neg_iff, Even.pow_pos, Odd.pow_neg, hq.ne]

variable (x) in
abbrev NF : Prop := (∀ τ, ¬ FixedFrom x τ) ∧ ∀ y τ, ¬ PseudoStableAfter x y τ

variable (u c) in
abbrev Osc : Prop :=
  (∃ k, t ≤ k ∧ k ≤ t + 4 ∧ u k < c) ∧ ∃ k, t ≤ k ∧ k ≤ t + 4 ∧ c < u k

theorem osc_refute (hl : Tendsto x atTop (𝓝 L))
    (h : ∀ t, Osc (L i) (x · i) t) :
    NF x := by
  refine ⟨fun τ hf => ?_, fun y τ ⟨hy, F, C, _, _, _, hU, hc⟩ => ?_⟩ <;> have := h τ
  · grind [FixedFrom]
  have := hU ▸ Finset.mem_univ i
  have key : ∀ t ≥ τ, (x t i < y i ↔ x τ i < y i) := Nat.le_induction Iff.rfl fun t ht ih => by
    grind
  grind [tendsto_nhds_unique hy hl]

variable (m r x₀ L v q a N) in
structure Mode : Prop where
  h0 : x₀ = L + a 0 • v
  ha : ∀ t, a (t + 1) = q * a t
  hq : q < 0
  hq1 : |q| < 1
  ha0 : a 0 ≠ 0
  hv : ∃ i, v i ≠ 0
  nb : ∀ t, neighbors m r (L + a t • v) = N t
  adj : ∀ t y, neighbors m r y = N t → (adjMatrix m r y).mulVec L = L ∧
    (adjMatrix m r y).mulVec v = q • v

section

variable (h : Mode m r x₀ L v q a N)
include h

theorem Mode.eq : ∀ t, traj m r x₀ t = L + a t • v :=
  Nat.rec h.h0 fun t ih => by simp [traj_succ, ih, step, Matrix.mulVec_add, Matrix.mulVec_smul, h.adj t _ (h.nb t), h.ha,
    smul_smul, mul_comm]

theorem Mode.pow : a t = q ^ t * a 0 := by
  induction t <;> grind [h.ha, pow_succ]

theorem Mode.ne : a t ≠ 0 :=
  h.pow t ▸ mul_ne_zero (pow_ne_zero _ h.hq.ne) h.ha0

theorem Mode.lim :
    Tendsto (fun k : ℕ => L + (q ^ k * c) • v) atTop (𝓝 L) := by
  simpa using (((tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    h.hq1).mul_const c).smul_const v).const_add L

theorem Mode.tendsto : Tendsto (traj m r x₀) atTop (𝓝 L) :=
  h.lim.congr fun t => by rw [h.eq, h.pow t]

theorem Mode.fvct : fvct m r (traj m r x₀ t) = L := by
  have e : ∀ k, (adjMatrix m r (L + a t • v) ^ k).mulVec (L + a t • v) =
      L + (q ^ k * a t) • v := Nat.rec (by simp) fun k ih => by
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih]
    simp [Matrix.mulVec_add, Matrix.mulVec_smul, h.adj t _ (h.nb t), smul_smul]; ring_nf
  simp only [HK.fvct, h.eq, e]
  exact h.lim.limUnder_eq

theorem Mode.perStepFactor (hv : v i ≠ 0) :
    perStepFactor m r (traj m r x₀) i t = q := by
  rw [HK.perStepFactor, h.fvct, h.eq, h.eq, h.ha]; simp [h.ne t, hv, mul_assoc]

theorem Mode.nfp : NF (traj m r x₀) := by
  obtain ⟨i, hi⟩ := h.hv
  refine osc_refute i h.tendsto fun τ => ?_
  simp [h.eq]
  have := mul_self_pos.2 (mul_ne_zero (h.ne τ) hi)
  constructor <;> by_contra! hn <;>
    nlinarith [h.hq, hn τ le_rfl le_self_add, h.ha τ ▸ hn (τ + 1) le_self_add (by omega)]

end

/-- Conjecture 2.3 and Theorem 6.4(iv) fail for a trajectory never fixed nor pseudo-stable. -/
macro "pos" : tactic => `(tactic| (intro i; fin_cases i <;>
  norm_num [sbc7_r, sbi7_r, sbc6_r, sbi7b_r, sbc5_r, sbi6_r, sbi5_r]))

theorem refute (H : NF (traj m r x₀)) (hr : ∀ i, 0 < r i := by pos) :
    ¬ Conjecture23ForAgents m n ∧
      ((∀ t, proximityDigraph m r (traj m r x₀ t) = proximityDigraph m r x₀) →
        ¬ Theorem64ivForAgents m n ∧ ¬ Theorem64ivLiteralForAgents m n) :=
  ⟨fun h => by simpa [H.1, H.2] using h r x₀ hr, fun hd => by
    constructor <;> intro h <;> simpa [H.1, H.2] using h r x₀ hr 0 fun t _ => hd t⟩

theorem digraph_const {N : Fin n → Finset (Fin n)}
    (hN : ∀ t, neighbors m r (traj m r x₀ t) = N) (t : ℕ) :
    proximityDigraph m r (traj m r x₀ t) = proximityDigraph m r x₀ := by
  rw [proximityDigraph, hN t, ← hN 0]; rfl

open goldenRatio

theorem sbi_b : 1 < φ ∧ φ < 2 ∧ sbiRate = (1 - φ) / 4 ∧
    sbiRate ≤ sbiRate ^ t ∧ sbiRate ^ t ≤ 1 ∧ -1 / 4 ≤ sbiRate ^ t * φ ∧ sbiRate ^ t * φ ≤ 2 := by
  have := Real.sq_sqrt (Nat.ofNat_nonneg 5)
  have := Real.sqrt_nonneg 5
  unfold sbiRate Real.goldenRatio
  obtain ⟨_, _⟩ := pow_bounds (q := (1 - √5) / 8) t (by nlinarith) (by nlinarith)
  split_ands <;> nlinarith

macro "tab" : tactic => `(tactic| ((try split_ifs at *) <;> funext i <;> ext j <;>
      fin_cases i <;> fin_cases j <;>
      simp [neighbors, Model.bound, abs_le] <;> grind))

macro "mode" b:term:max c:term:max : tactic => `(tactic| (
  have := $b 0
  exact ⟨by norm_num [funext_iff, Fin.forall_fin_succ] <;> grind, fun t => by ring, by linarith,
    by grind [abs_lt], by grind, ⟨1, by simp⟩,
    fun t => by have := $b t; have := $c t; tab, fun t y h => by
      have := $b t; constructor <;> funext i <;> rw [adj_mulVec, h] <;>
      (try split_ifs) <;> fin_cases i <;> simp [Finset.sum_insert] <;> grind⟩))

section

attribute [local simp] sbc7_r sbc7_x0 sbc7_lim sbc7_v sbc6_r sbc6_x0 sbc6_lim sbc6_v sbi7b_r sbi7b_x0 sbi7b_lim sbi_v sbi7_r sbi7_x0 sbi7_lim sbc5Family_r sbc5Family_x0 sbc5_lim sbc5_v sbi6_r sbi6_x0 sbi6_lim sbi6_v

theorem sbc7 : Mode .sbc sbc7_r sbc7_x0 sbc7_lim sbc7_v (-1 / 6) (fun t => (-1 / 6 : ℝ) ^ t) fun t =>
    ![{0}, {0, 1, 2}, {1, 2, 3, 4}, if Even t then {3} else {2, 3, 4}, {2, 3, 4, 5}, {4, 5, 6}, {6}] := by
  mode b6 (sign_pow · (by norm_num : (-1 / 6 : ℝ) < 0) one_pos)
theorem sbc6 : Mode .sbc sbc6_r sbc6_x0 sbc6_lim sbc6_v (-1 / 6) (fun t => (-1 / 6 : ℝ) ^ t) fun _ =>
    ![{0}, {0, 1, 2}, {0, 1, 2, 3}, {2, 3, 4, 5}, {3, 4, 5}, {5}] := by
  mode b6 b6
theorem sbi7b : Mode .sbi sbi7b_r sbi7b_x0 sbi7b_lim sbi_v sbiRate (sbiRate ^ ·) fun _ =>
    ![{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, {2, 3, 4}, {2, 3, 4, 5}, {3, 4, 5, 6}, {6}] := by
  mode sbi_b sbi_b
theorem sbi7 : Mode .sbi sbi7_r sbi7_x0 sbi7_lim sbi_v sbiRate (sbiRate ^ · / 2) fun t =>
    ![{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, if Even t then {1, 2, 3, 4, 5} else {2, 3, 4},
      {2, 3, 4, 5}, {3, 4, 5, 6}, {6}] := by
  mode sbi_b (sign_pow · sbi7b.hq Real.goldenRatio_pos)
theorem sbc5_b : 1.4 < √2 ∧ √2 < 1.5 ∧
    sbc5Rate = (1 - √2) / 3 ∧ sbc5Rate ≤ sbc5Rate ^ t ∧ sbc5Rate ^ t ≤ 1 := by
  have := Real.sq_sqrt zero_le_two
  have := Real.sqrt_nonneg 2
  unfold sbc5Rate
  refine ⟨?_, ?_, ?_, pow_bounds t ?_ ?_⟩ <;> nlinarith

section

variable (h0 : 0 < δ) (h1 : δ ≤ 1)
include h0 h1

theorem fam_b : -δ ≤ sbc5Rate ^ t * δ ∧
    sbc5Rate ^ t * δ ≤ δ ∧ -(3 / 2) * δ ≤ sbc5Rate ^ t * δ * √2 ∧ sbc5Rate ^ t * δ * √2 ≤ 3 / 2 * δ := by
  obtain ⟨a, b, e, c, d⟩ := sbc5_b t
  split_ands <;> nlinarith [mul_le_mul_of_nonneg_right c h0.le,
    mul_le_mul_of_nonneg_right d h0.le]

theorem fam :
    Mode .sbc (sbc5Family_r δ) (sbc5Family_x0 δ) sbc5_lim sbc5_v sbc5Rate (sbc5Rate ^ · * δ) fun _ =>
      ![{0}, {0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {4}] :=
  by mode sbc5_b (fam_b · h0 h1)
end

theorem sbi6_b : 15 < √249 ∧
    sbi6Rate = (13 - √249) / 40 ∧ sbi6Rate ≤ sbi6Rate ^ t ∧ sbi6Rate ^ t ≤ 1 ∧
    -27 / 20 ≤ sbi6Rate ^ t * √249 ∧ sbi6Rate ^ t * √249 ≤ 16 := by
  have := Real.sq_sqrt (Nat.ofNat_nonneg 249)
  have := Real.sqrt_nonneg 249
  unfold sbi6Rate
  obtain ⟨_, _⟩ := pow_bounds (q := (13 - √249) / 40) t (by nlinarith) (by nlinarith)
  split_ands <;> nlinarith

theorem sbi6 : Mode .sbi sbi6_r sbi6_x0 sbi6_lim sbi6_v sbi6Rate (sbi6Rate ^ ·) fun _ =>
    ![{0}, {0, 1, 2, 3}, {0, 1, 2, 3, 4}, {0, 2, 3, 4, 5}, {2, 3, 4, 5}, {5}] := by
  mode sbi6_b sbi6_b

theorem sbc5_e : sbc5Family_r 1 = sbc5_r ∧ sbc5Family_x0 1 = sbc5_x0 := by
  norm_num [funext_iff, Fin.forall_fin_succ, sbc5_r, sbc5_x0, sub_eq_add_neg]

theorem sbc5 : Mode .sbc sbc5_r sbc5_x0 sbc5_lim sbc5_v sbc5Rate (sbc5Rate ^ ·) fun _ =>
    ![{0}, {0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {4}] := by
  simpa only [sbc5_e, mul_one] using fam one_pos le_rfl

theorem sbc6_perStepFactor (t : ℕ) (i : Fin 6) (hi : i ∈ ({1, 2, 3, 4} : Finset (Fin 6))) :
    perStepFactor .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0) i t = -1 / 6 :=
  sbc6.perStepFactor t i (by fin_cases hi <;> norm_num)

theorem sbi7b_perStepFactor (t : ℕ) (i : Fin 7) (hi : i ∈ ({1, 2, 4, 5} : Finset (Fin 7))) :
    perStepFactor .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0) i t = sbiRate :=
  sbi7b.perStepFactor t i (by fin_cases hi <;> simp <;> positivity)

theorem sbc5_perStepFactor (t : ℕ) (i : Fin 5) (hi : i ∈ ({1, 2, 3} : Finset (Fin 5))) :
    perStepFactor .sbc sbc5_r (traj .sbc sbc5_r sbc5_x0) i t = sbc5Rate :=
  sbc5.perStepFactor t i (by fin_cases hi <;> norm_num)

theorem sbi6_perStepFactor (t : ℕ) (i : Fin 6) (hi : i ∈ ({1, 2, 3, 4} : Finset (Fin 6))) :
    perStepFactor .sbi sbi6_r (traj .sbi sbi6_r sbi6_x0) i t = sbi6Rate :=
  sbi6.perStepFactor t i (by fin_cases hi <;> norm_num <;> grind [sbi6_b 0])

theorem equiTopologyDistance_pos :
    (∀ i, 0 < equiTopologyDistance sbc6_r sbc6_lim i) ∧
    (∀ i, 0 < equiTopologyDistance sbi7b_r sbi7b_lim i) := by
  constructor <;> intro i <;> refine mul_pos one_half_pos (four_pos.trans_le
    (le_csInf ⟨_, i + 1, by simp, .inl rfl⟩ ?_)) <;> rintro d ⟨k, hk, rfl | rfl⟩ <;>
    fin_cases i <;> fin_cases k <;> norm_num at *

theorem equiTopologyDistance_eq_zero :
    (∀ i ∈ ({2, 3, 4} : Finset (Fin 7)), equiTopologyDistance sbc7_r sbc7_lim i = 0) ∧
    (∀ i ∈ ({1, 3, 5} : Finset (Fin 7)), equiTopologyDistance sbi7_r sbi7_lim i = 0) := by
  constructor <;> intro i hi <;> fin_cases hi <;> refine mul_eq_zero_of_right _ (IsLeast.csInf_eq
    ⟨?_, by grind [mem_lowerBounds, abs_nonneg]⟩) <;>
    norm_num [Fin.exists_fin_succ]

end
theorem sbc7_closed_form (t : ℕ) :
    traj .sbc sbc7_r sbc7_x0 t = fun i => sbc7_lim i + (-1 / 6 : ℝ) ^ t * sbc7_v i :=
  sbc7.eq t

theorem sbc7_neighbors (t : ℕ) :
    neighbors .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 t) =
      ![{0}, {0, 1, 2}, {1, 2, 3, 4}, if Even t then {3} else {2, 3, 4}, {2, 3, 4, 5},
        {4, 5, 6}, {6}] :=
  sbc7.eq t ▸ sbc7.nb t

theorem sbi7_closed_form (t : ℕ) :
    traj .sbi sbi7_r sbi7_x0 t = fun i => sbi7_lim i + sbiRate ^ t / 2 * sbi_v i :=
  sbi7.eq t

theorem sbi7_neighbors (t : ℕ) :
    neighbors .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t) =
      ![{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, if Even t then {1, 2, 3, 4, 5} else {2, 3, 4},
        {2, 3, 4, 5}, {3, 4, 5, 6}, {6}] :=
  sbi7.eq t ▸ sbi7.nb t

theorem sbc6_closed_form (t : ℕ) :
    traj .sbc sbc6_r sbc6_x0 t = fun i => sbc6_lim i + (-1 / 6 : ℝ) ^ t * sbc6_v i :=
  sbc6.eq t

theorem sbc6_neighbors (t : ℕ) :
    neighbors .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0 t) =
      ![{0}, {0, 1, 2}, {0, 1, 2, 3}, {2, 3, 4, 5}, {3, 4, 5}, {5}] :=
  sbc6.eq t ▸ sbc6.nb t

theorem sbi7b_closed_form (t : ℕ) :
    traj .sbi sbi7b_r sbi7b_x0 t = fun i => sbi7b_lim i + sbiRate ^ t * sbi_v i :=
  sbi7b.eq t

theorem sbi7b_neighbors (t : ℕ) :
    neighbors .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0 t) =
      ![{0}, {0, 1, 2, 3}, {1, 2, 3, 4}, {2, 3, 4}, {2, 3, 4, 5}, {3, 4, 5, 6}, {6}] :=
  sbi7b.eq t ▸ sbi7b.nb t

theorem tendsto_limits :
    Tendsto (traj .sbc sbc7_r sbc7_x0) atTop (𝓝 sbc7_lim) ∧
    Tendsto (traj .sbi sbi7_r sbi7_x0) atTop (𝓝 sbi7_lim) ∧
    Tendsto (traj .sbc sbc6_r sbc6_x0) atTop (𝓝 sbc6_lim) ∧
    Tendsto (traj .sbi sbi7b_r sbi7b_x0) atTop (𝓝 sbi7b_lim) :=
  ⟨sbc7.tendsto, sbi7.tendsto, sbc6.tendsto, sbi7b.tendsto⟩

macro "ndc" nb:term:max j:term:max : term => `(⟨_ + 1, le_self_add, fun h => by
  have := congrArg (·.Adj 3 $j) h
  simp [proximityDigraph, $nb:term, Nat.even_add_one] at this
  grind⟩)

theorem sbc7_digraph_not_eventually_constant (τ : ℕ) :
    ∃ t, τ ≤ t ∧ proximityDigraph .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 t) ≠
      proximityDigraph .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 τ) :=
  ndc sbc7_neighbors 2

theorem sbi7_digraph_not_eventually_constant (τ : ℕ) :
    ∃ t, τ ≤ t ∧ proximityDigraph .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t) ≠
      proximityDigraph .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 τ) :=
  ndc sbi7_neighbors 1

theorem sbc6_digraph_constant (t : ℕ) :
    proximityDigraph .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0 t) =
      proximityDigraph .sbc sbc6_r sbc6_x0 :=
  digraph_const sbc6_neighbors t

theorem sbi7b_digraph_constant (t : ℕ) :
    proximityDigraph .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0 t) =
      proximityDigraph .sbi sbi7b_r sbi7b_x0 :=
  digraph_const sbi7b_neighbors t

theorem not_fixedFrom (τ : ℕ) :
    ¬ FixedFrom (traj .sbc sbc7_r sbc7_x0) τ ∧ ¬ FixedFrom (traj .sbi sbi7_r sbi7_x0) τ ∧
    ¬ FixedFrom (traj .sbc sbc6_r sbc6_x0) τ ∧ ¬ FixedFrom (traj .sbi sbi7b_r sbi7b_x0) τ :=
  ⟨sbc7.nfp.1 τ, sbi7.nfp.1 τ, sbc6.nfp.1 τ, sbi7b.nfp.1 τ⟩

theorem not_pseudoStableAfter (xinf : Fin 7 → ℝ) (yinf : Fin 6 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbc sbc7_r sbc7_x0) xinf τ ∧
    ¬ PseudoStableAfter (traj .sbi sbi7_r sbi7_x0) xinf τ ∧
    ¬ PseudoStableAfter (traj .sbc sbc6_r sbc6_x0) yinf τ ∧
    ¬ PseudoStableAfter (traj .sbi sbi7b_r sbi7b_x0) xinf τ :=
  ⟨sbc7.nfp.2 xinf τ, sbi7.nfp.2 xinf τ, sbc6.nfp.2 yinf τ, sbi7b.nfp.2 xinf τ⟩

theorem not_conjecture22_sbc_seven : ¬ Conjecture22ForAgents .sbc 7 :=
  fun h => (h sbc7_r sbc7_x0 (by pos)).elim fun τ hτ => by grind [sbc7_digraph_not_eventually_constant τ]

theorem not_conjecture22_sbi_seven : ¬ Conjecture22ForAgents .sbi 7 :=
  fun h => (h sbi7_r sbi7_x0 (by pos)).elim fun τ hτ => by grind [sbi7_digraph_not_eventually_constant τ]

theorem not_conjecture22_sbc : ¬ Conjecture22For .sbc :=
  fun h => not_conjecture22_sbc_seven (h 7)

theorem not_conjecture22_sbi : ¬ Conjecture22For .sbi :=
  fun h => not_conjecture22_sbi_seven (h 7)

theorem not_conjecture22 : ¬ Conjecture22 :=
  fun h => not_conjecture22_sbc (h .sbc)

theorem not_conjecture23_sbc : ¬ Conjecture23For .sbc :=
  fun h => (refute sbc7.nfp).1 (h 7)

theorem not_conjecture23_sbi : ¬ Conjecture23For .sbi :=
  fun h => (refute sbi7.nfp).1 (h 7)

theorem not_conjecture23 : ¬ Conjecture23 :=
  fun h => not_conjecture23_sbc (h .sbc)

def r6 := (refute sbc6.nfp).2 sbc6_digraph_constant
def r7 := (refute sbi7b.nfp).2 sbi7b_digraph_constant

theorem not_theorem64iv_sbc : ¬ Theorem64ivFor .sbc :=
  fun h => r6.1 (h 6)

theorem not_theorem64iv_sbi : ¬ Theorem64ivFor .sbi :=
  fun h => r7.1 (h 7)

theorem not_theorem64iv : ¬ Theorem64iv :=
  fun h => not_theorem64iv_sbc (h .sbc)

theorem not_theorem64iv_literal_sbc : ¬ Theorem64ivLiteralFor .sbc :=
  fun h => r6.2 (h 6)

theorem not_theorem64iv_literal_sbi : ¬ Theorem64ivLiteralFor .sbi :=
  fun h => r7.2 (h 7)

theorem not_theorem64iv_literal : ¬ Theorem64ivLiteral :=
  fun h => not_theorem64iv_literal_sbc (h .sbc)

theorem sbc5_closed_form (t : ℕ) :
    traj .sbc sbc5_r sbc5_x0 t = fun i => sbc5_lim i + sbc5Rate ^ t * sbc5_v i :=
  sbc5.eq t

theorem sbc5_neighbors (t : ℕ) :
    neighbors .sbc sbc5_r (traj .sbc sbc5_r sbc5_x0 t) =
      ![{0}, {0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {4}] :=
  sbc5.eq t ▸ sbc5.nb t

theorem sbi6_closed_form (t : ℕ) :
    traj .sbi sbi6_r sbi6_x0 t = fun i => sbi6_lim i + sbi6Rate ^ t * sbi6_v i :=
  sbi6.eq t

theorem sbi6_neighbors (t : ℕ) :
    neighbors .sbi sbi6_r (traj .sbi sbi6_r sbi6_x0 t) =
      ![{0}, {0, 1, 2, 3}, {0, 1, 2, 3, 4}, {0, 2, 3, 4, 5}, {2, 3, 4, 5}, {5}] :=
  sbi6.eq t ▸ sbi6.nb t

theorem small_tendsto :
    Tendsto (traj .sbc sbc5_r sbc5_x0) atTop (𝓝 sbc5_lim) ∧
    Tendsto (traj .sbi sbi6_r sbi6_x0) atTop (𝓝 sbi6_lim) :=
  ⟨sbc5.tendsto, sbi6.tendsto⟩

theorem small_digraph_constant (t : ℕ) :
    proximityDigraph .sbc sbc5_r (traj .sbc sbc5_r sbc5_x0 t) =
      proximityDigraph .sbc sbc5_r sbc5_x0 ∧
    proximityDigraph .sbi sbi6_r (traj .sbi sbi6_r sbi6_x0 t) =
      proximityDigraph .sbi sbi6_r sbi6_x0 :=
  ⟨digraph_const sbc5_neighbors t, digraph_const sbi6_neighbors t⟩

theorem small_not_fixedFrom (τ : ℕ) :
    ¬ FixedFrom (traj .sbc sbc5_r sbc5_x0) τ ∧ ¬ FixedFrom (traj .sbi sbi6_r sbi6_x0) τ :=
  ⟨sbc5.nfp.1 τ, sbi6.nfp.1 τ⟩

theorem small_not_pseudoStableAfter (xinf : Fin 5 → ℝ) (yinf : Fin 6 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbc sbc5_r sbc5_x0) xinf τ ∧
    ¬ PseudoStableAfter (traj .sbi sbi6_r sbi6_x0) yinf τ :=
  ⟨sbc5.nfp.2 xinf τ, sbi6.nfp.2 yinf τ⟩

theorem not_conjecture23_sbc_five : ¬ Conjecture23ForAgents .sbc 5 :=
  (refute sbc5.nfp).1

theorem not_conjecture23_sbi_six : ¬ Conjecture23ForAgents .sbi 6 :=
  (refute sbi6.nfp).1

theorem not_theorem64iv_sbc_five : ¬ Theorem64ivForAgents .sbc 5 :=
  ((refute sbc5.nfp).2 (digraph_const sbc5_neighbors)).1

theorem not_theorem64iv_sbi_six : ¬ Theorem64ivForAgents .sbi 6 :=
  ((refute sbi6.nfp).2 (digraph_const sbi6_neighbors)).1

theorem sbc5_fvct (t : ℕ) : fvct .sbc sbc5_r (traj .sbc sbc5_r sbc5_x0 t) = sbc5_lim :=
  sbc5.fvct t

theorem sbi6_fvct (t : ℕ) : fvct .sbi sbi6_r (traj .sbi sbi6_r sbi6_x0 t) = sbi6_lim :=
  sbi6.fvct t


mutual
theorem sbc9_closed_form (t : ℕ) :
    traj .sbc sbc9_r sbc9_x0 t =
      ![0, 20 + 2 * (-1 / 6 : ℝ) ^ t, 40 - 3 * (-1 / 6 : ℝ) ^ t, 100 + 3 * (-1 / 6 : ℝ) ^ t,
        120 - 2 * (-1 / 6 : ℝ) ^ t, 140, 210 + 12 / 11 * ((-1 / 6 : ℝ) ^ t - (1 / 5 : ℝ) ^ t),
        280, 300] := by
  cases t with
  | zero => norm_num [traj, sbc9_x0]
  | succ t =>
    ext i; rw [traj_succ, step, adj_mulVec, sbc9_neighbors t, sbc9_closed_form t]
    fin_cases i <;> simp [Finset.sum_insert, pow_succ] <;> ring
termination_by (t, 0)

theorem sbc9_neighbors (t : ℕ) :
    neighbors .sbc sbc9_r (traj .sbc sbc9_r sbc9_x0 t) =
      ![{0}, {0, 1, 2}, {0, 1, 2, 3}, {2, 3, 4, 5}, {3, 4, 5}, {5}, {4, 5, 6, 7, 8}, {7}, {8}] := by
  have := b6 t
  have : 0 ≤ ((5 : ℝ) ^ t)⁻¹ ∧ ((5 : ℝ) ^ t)⁻¹ ≤ 1 := by bound
  rw [sbc9_closed_form t, sbc9_r]
  tab
termination_by (t, 1)
end

theorem sbc9_spectator_lt (t : ℕ) (ht : 1 ≤ t) : traj .sbc sbc9_r sbc9_x0 t 6 < 210 := by
  have : (1 / 6 : ℝ) ^ t < (1 / 5) ^ t := by bound
  have := le_abs_self ((-1 / 6 : ℝ) ^ t)
  norm_num [abs_pow, sbc9_closed_form] at *
  linarith

mutual
theorem sbi8_closed_form (t : ℕ) :
    traj .sbi sbi8_r sbi8_x0 t =
      ![0, 60 + Real.goldenRatio⁻¹ * ((1 / 4 : ℝ) ^ t - sbiRate ^ t), 70 + sbiRate ^ t,
        100 - Real.goldenRatio * sbiRate ^ t, 110, 120 + Real.goldenRatio * sbiRate ^ t,
        150 - sbiRate ^ t, 220] := by
  cases t with
  | zero => norm_num [traj, sbi8_x0]
  | succ t =>
    have := sbi_b t
    ext i; rw [traj_succ, step, adj_mulVec, sbi8_neighbors t, sbi8_closed_form t]
    fin_cases i <;> simp [Finset.sum_insert, pow_succ] <;> grind
termination_by (t, 0)

theorem sbi8_neighbors (t : ℕ) :
    neighbors .sbi sbi8_r (traj .sbi sbi8_r sbi8_x0 t) =
      ![{0}, {0, 1, 2, 4}, {0, 2, 3, 4}, {2, 3, 4, 5}, {3, 4, 5}, {3, 4, 5, 6}, {4, 5, 6, 7}, {7}] := by
  have := sbi_b t
  have h : 0 ≤ ((4 : ℝ) ^ t)⁻¹ ∧ ((4 : ℝ) ^ t)⁻¹ ≤ 1 := by bound
  have := mul_le_mul_of_nonneg_right h.2 Real.goldenRatio_pos.le
  have := mul_nonneg h.1 Real.goldenRatio_pos.le
  rw [sbi8_closed_form t, Real.inv_goldenRatio, ← Real.one_sub_goldenConj, sbi8_r]
  tab
termination_by (t, 1)
end

theorem sbi8_spectator_gt (t : ℕ) (ht : 1 ≤ t) : 60 < traj .sbi sbi8_r sbi8_x0 t 1 := by
  obtain ⟨a, b, c, -⟩ := sbi_b t
  have := pow_lt_pow_left₀ (by grind [abs_lt] : |sbiRate| < 1 / 4) (abs_nonneg _) (Nat.one_le_iff_ne_zero.1 ht)
  have := le_abs_self (sbiRate ^ t)
  simp [abs_pow, sbi8_closed_form] at *
  exact mul_pos (by positivity) (by linarith)

theorem alternating_fvct (t : ℕ) :
    fvct .sbc sbc7_r (traj .sbc sbc7_r sbc7_x0 t) = sbc7_lim ∧
    fvct .sbi sbi7_r (traj .sbi sbi7_r sbi7_x0 t) = sbi7_lim :=
  ⟨sbc7.fvct t, sbi7.fvct t⟩

theorem sbc6_fvct (t : ℕ) : fvct .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0 t) = sbc6_lim :=
  sbc6.fvct t

theorem sbc6_perStepFactor_not_tendsto (i : Fin 6) (hi : i ∈ ({1, 2, 3, 4} : Finset (Fin 6)))
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ¬ Tendsto (fun t => perStepFactor .sbc sbc6_r (traj .sbc sbc6_r sbc6_x0) i t) atTop (𝓝 ρ) :=
  by simp [sbc6_perStepFactor _ i hi]; grind

theorem sbi7b_fvct (t : ℕ) : fvct .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0 t) = sbi7b_lim :=
  sbi7b.fvct t

theorem sbi7b_perStepFactor_not_tendsto (i : Fin 7) (hi : i ∈ ({1, 2, 4, 5} : Finset (Fin 7)))
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ¬ Tendsto (fun t => perStepFactor .sbi sbi7b_r (traj .sbi sbi7b_r sbi7b_x0) i t) atTop (𝓝 ρ) :=
  by simp [sbi7b_perStepFactor _ i hi]; grind [sbi7b.hq]

theorem proximityDigraph_eq_of_equiTopologyNbhd (m : Model) {n : ℕ} (r z y : Fin n → ℝ)
    (h : EquiTopologyNbhd r z y) : proximityDigraph m r y = proximityDigraph m r z := by
  have hle : ∀ i j, j ≠ i → ∀ R, R = r i ∨ R = r j →
      equiTopologyDistance r z i ≤ 1 / 2 * |(|z i - z j|) - R| := fun i j hij R hR =>
    mul_le_mul_of_nonneg_left (csInf_le ⟨0, by grind [mem_lowerBounds, abs_nonneg]⟩
      ⟨j, hij, by grind⟩) one_half_pos.le
  have h0 : ∀ i, 0 ≤ equiTopologyDistance r z i := fun i =>
    mul_nonneg one_half_pos.le (Real.sInf_nonneg (by grind [abs_nonneg]))
  ext i j
  simp [proximityDigraph, neighbors]
  rcases eq_or_ne j i with rfl | hij
  · simp
  have hR : m.bound r i j = r i ∨ m.bound r i j = r j := by cases m <;> simp [Model.bound]
  grind [abs_le, hle i j hij _ hR, hle j i hij.symm _ hR.symm, h i, h j]

theorem eventually_constant_of_tendsto (m : Model) {n : ℕ} (r x₀ xinf : Fin n → ℝ)
    (hconv : Tendsto (traj m r x₀) atTop (𝓝 xinf))
    (hε : ∀ i, 0 < equiTopologyDistance r xinf i) :
    ∃ T, ∀ t, T ≤ t → proximityDigraph m r (traj m r x₀ t) = proximityDigraph m r xinf :=
  (eventually_atTop.1 (eventually_all.2 fun i =>
    Metric.tendsto_nhds.1 (tendsto_pi_nhds.1 hconv i) _ (hε i))).imp fun _ hT t ht =>
      proximityDigraph_eq_of_equiTopologyNbhd m r xinf _ fun i =>
        ⟨fun _ => hT t ht i, (hε i).ne'.elim⟩

theorem fvct_eq_and_equilibrium_of_tendsto (m : Model) {n : ℕ} (r x₀ xinf : Fin n → ℝ)
    (hconv : Tendsto (traj m r x₀) atTop (𝓝 xinf))
    (hε : ∀ i, 0 < equiTopologyDistance r xinf i) :
    (∃ T, ∀ t, T ≤ t → fvct m r (traj m r x₀ t) = xinf) ∧ step m r xinf = xinf := by
  obtain ⟨T, hT⟩ := eventually_constant_of_tendsto m r x₀ xinf hconv hε
  have hA : ∀ t ≥ T, adjMatrix m r (traj m r x₀ t) = adjMatrix m r xinf := fun t ht => by
    simp_all [proximityDigraph, funext_iff, ← Finset.ext_iff, adjMatrix]
  have hs : ∀ t ≥ T, (adjMatrix m r xinf).mulVec (traj m r x₀ t) = traj m r x₀ (t + 1) :=
    fun t ht => by rw [traj_succ, step, hA t ht]
  refine ⟨⟨T, fun t ht => ?_⟩, tendsto_nhds_unique ((((continuous_const.matrix_mulVec
    continuous_id).tendsto xinf).comp hconv).congr' (eventually_atTop.2 ⟨T, hs⟩))
      (hconv.comp (tendsto_add_atTop_nat 1))⟩
  have : ∀ k, (adjMatrix m r xinf ^ k).mulVec (traj m r x₀ t) = traj m r x₀ (k + t) :=
    Nat.rec (by simp) fun k ih => by grind [pow_succ', Matrix.mulVec_mulVec]
  simp only [fvct, hA t ht, this]
  exact (hconv.comp (tendsto_add_atTop_nat t)).limUnder_eq

theorem sbi5_root_exists : ∃ ρ : ℝ, 57 / 100 < ρ ∧ ρ < 29 / 50 ∧
    60 * ρ ^ 3 - 47 * ρ ^ 2 + 9 * ρ - 1 = 0 := by
  simpa [and_assoc] using intermediate_value_Ioo (by norm_num : (57 / 100 : ℝ) ≤ 29 / 50)
    (f := fun ρ => 60 * ρ ^ 3 - 47 * ρ ^ 2 + 9 * ρ - 1) (by fun_prop) (show (0 : ℝ) ∈ _ by norm_num)

theorem osc (hA : α * (α ^ 2 - 2 * β) < 0) (hB : β * (β - α ^ 2) < 0)
    (hu : ∀ t, u (t + 2) = α * u (t + 1) - β * u t)
    (h0 : ¬ (u 0 = 0 ∧ u 1 = 0)) : Osc 0 u t := by
  have nz : ¬ (u t = 0 ∧ u (t + 1) = 0) := by
    induction t <;> grind [left_ne_zero_of_mul hB.ne]
  have e : u (t + 4) = α * (α ^ 2 - 2 * β) * u (t + 1) + β * (β - α ^ 2) * u t := by grind
  constructor <;> by_contra! hn <;> exact nz (by
    constructor <;> nlinarith [hn t le_rfl le_self_add, hn (t + 1) le_self_add (by omega), hn (t + 4) le_self_add le_rfl])

theorem sbi5_succ : sbi5Offset ρ (t + 1) = sbi5LinearStep (sbi5Offset ρ t) :=
  Function.iterate_succ_apply' _ _ _

theorem sbi5_bound (h1 : 57 / 100 < ρ) (h2 : ρ < 29 / 50) :
    ∀ i, ‖sbi5Offset ρ t i‖ ≤ (2 / 3 : ℝ) ^ t / 3 := by
  induction t <;> intro i <;> fin_cases i <;>
    simp_all [Real.norm_eq_abs, sbi5Offset, Function.iterate_succ_apply', pow_succ, sbi5LinearStep, abs_le] <;> grind

mutual
theorem sbi5_trajectory (ρ : ℝ) (hlo : 57 / 100 < ρ) (hhi : ρ < 29 / 50)
    (t : ℕ) : traj .sbi sbi5_r (sbi5_x0 ρ) t = sbi5_lim + sbi5Lift (sbi5Offset ρ t) := by
  cases t with
  | zero => rfl
  | succ t =>
    funext i
    rw [traj_succ, step, adj_mulVec, sbi5_neighbors ρ hlo hhi t, sbi5_trajectory ρ hlo hhi t, sbi5_succ]
    fin_cases i <;> simp [Finset.sum_insert, sbi5_lim, sbi5Lift, sbi5LinearStep] <;> ring
termination_by (t, 0)

theorem sbi5_neighbors (ρ : ℝ) (hlo : 57 / 100 < ρ) (hhi : ρ < 29 / 50)
    (t : ℕ) : neighbors .sbi sbi5_r (traj .sbi sbi5_r (sbi5_x0 ρ) t) =
      ![{0}, {0, 1, 3}, {0, 1, 2, 3, 4}, {0, 2, 3, 4}, {4}] := by
  have : (2 / 3 : ℝ) ^ t ≤ 1 := by bound
  have := fun i => abs_le.1 (sbi5_bound t hlo hhi i)
  rw [sbi5_trajectory ρ hlo hhi t, sbi5_r, sbi5_lim, sbi5Lift]
  tab
termination_by (t, 1)
end

theorem sbi5_tendsto (ρ : ℝ) (hlo : 57 / 100 < ρ) (hhi : ρ < 29 / 50) :
    Tendsto (traj .sbi sbi5_r (sbi5_x0 ρ)) atTop (𝓝 sbi5_lim) := by
  rw [funext (sbi5_trajectory ρ hlo hhi), tendsto_pi_nhds]
  intro i; fin_cases i <;> simpa [sbi5Lift] using tendsto_const_nhds.add (squeeze_zero_norm
    (sbi5_bound · hlo hhi _) (by simpa using (tendsto_pow_atTop_nhds_zero_iff.2 (by norm_num : |(2 / 3 : ℝ)| < 1)).div_const 3))

theorem sbi5_digraph_constant (ρ : ℝ) (hlo : 57 / 100 < ρ) (hhi : ρ < 29 / 50)
    (t : ℕ) : proximityDigraph .sbi sbi5_r (traj .sbi sbi5_r (sbi5_x0 ρ) t) =
      proximityDigraph .sbi sbi5_r (sbi5_x0 ρ) :=
  digraph_const (sbi5_neighbors ρ hlo hhi) t

theorem sbi5_oscillates_every_five (ρ : ℝ)
    (hlo : 57 / 100 < ρ) (hhi : ρ < 29 / 50)
    (hp : 60 * ρ ^ 3 - 47 * ρ ^ 2 + 9 * ρ - 1 = 0) (t : ℕ) (i : Fin 5)
    (hi : i ∈ ({1, 2, 3} : Finset (Fin 5))) :
    (∃ k, t ≤ k ∧ k ≤ t + 4 ∧ traj .sbi sbi5_r (sbi5_x0 ρ) k i < sbi5_lim i) ∧
    (∃ k, t ≤ k ∧ k ≤ t + 4 ∧ sbi5_lim i < traj .sbi sbi5_r (sbi5_x0 ρ) k i) := by
  have hr : ∀ t, sbi5Offset ρ (t + 2) = (47 / 60 - ρ) • sbi5Offset ρ (t + 1) -
      (ρ ^ 2 - 47 / 60 * ρ + 3 / 20) • sbi5Offset ρ t :=
    Nat.rec (by simp [funext_iff, Fin.forall_fin_succ, sbi5Offset, sbi5LinearStep]; grind) fun t ih => by
      simp only [sbi5_succ] at *; conv_lhs => rw [ih]
      simp [funext_iff, Fin.forall_fin_succ, sbi5LinearStep]; ring_nf; simp
  fin_cases hi <;> simp [sbi5Lift, sbi5_trajectory ρ hlo hhi] <;> exact osc t (by nlinarith) (by nlinarith) (fun t => congrFun (hr t) _) (by simp [sbi5Offset, sbi5LinearStep] <;> grind)

theorem sbi5_not_fixedFrom (ρ : ℝ) (hlo : 57 / 100 < ρ) (hhi : ρ < 29 / 50)
    (hp : 60 * ρ ^ 3 - 47 * ρ ^ 2 + 9 * ρ - 1 = 0) (τ : ℕ) :
    ¬ FixedFrom (traj .sbi sbi5_r (sbi5_x0 ρ)) τ :=
  (osc_refute 1 (sbi5_tendsto ρ hlo hhi) (sbi5_oscillates_every_five ρ hlo hhi hp · 1 (by simp))).1 τ

theorem sbi5_not_pseudoStableAfter (ρ : ℝ)
    (hlo : 57 / 100 < ρ) (hhi : ρ < 29 / 50)
    (hp : 60 * ρ ^ 3 - 47 * ρ ^ 2 + 9 * ρ - 1 = 0) (xinf : Fin 5 → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter (traj .sbi sbi5_r (sbi5_x0 ρ)) xinf τ :=
  (osc_refute 1 (sbi5_tendsto ρ hlo hhi) (sbi5_oscillates_every_five ρ hlo hhi hp · 1 (by simp))).2 xinf τ

theorem s5 : ¬ Conjecture23ForAgents .sbi 5 ∧ ¬ Theorem64ivForAgents .sbi 5 := by
  obtain ⟨ρ, a, b, c⟩ := sbi5_root_exists
  have := refute ⟨sbi5_not_fixedFrom ρ a b c, sbi5_not_pseudoStableAfter ρ a b c⟩
  exact ⟨this.1, (this.2 (sbi5_digraph_constant ρ a b)).1⟩

theorem not_conjecture23_sbi_five : ¬ Conjecture23ForAgents .sbi 5 :=
  s5.1

theorem not_theorem64iv_sbi_five : ¬ Theorem64ivForAgents .sbi 5 :=
  s5.2

theorem sbc5Family_closed_form (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (t : ℕ) :
    traj .sbc (sbc5Family_r δ) (sbc5Family_x0 δ) t =
      fun i => sbc5_lim i + (sbc5Rate ^ t * δ) * sbc5_v i :=
  (fam hδ0 hδ1).eq t

theorem sbc5Family_neighbors (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (t : ℕ) :
    neighbors .sbc (sbc5Family_r δ)
      (traj .sbc (sbc5Family_r δ) (sbc5Family_x0 δ) t) =
      ![{0}, {0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {4}] :=
  (fam hδ0 hδ1).eq t ▸ (fam hδ0 hδ1).nb t

theorem sbc5_near_homogeneous (ε : ℝ) (hε : 0 < ε) :
    ∃ r x₀ : Fin 5 → ℝ,
      (∀ i, 0 < r i) ∧
      (∀ i j, r i < (1 + ε) * r j) ∧
      r 0 < r 1 ∧
      (∀ t, proximityDigraph .sbc r (traj .sbc r x₀ t) =
        proximityDigraph .sbc r x₀) ∧
      Tendsto (traj .sbc r x₀) atTop (𝓝 sbc5_lim) ∧
      (∀ τ, ¬ FixedFrom (traj .sbc r x₀) τ) ∧
      (∀ xinf τ, ¬ PseudoStableAfter (traj .sbc r x₀) xinf τ) := by
  have h1 := min_le_left 1 (ε / 4)
  have h0 : 0 < min 1 (ε / 4) := by positivity
  have F := fam h0 h1
  have := mul_le_mul_of_nonneg_left h1 hε.le
  have := mul_pos hε h0
  refine ⟨_, _, ?_, ?_, ?_, digraph_const (sbc5Family_neighbors _ h0 h1),
    F.tendsto, F.nfp.1, F.nfp.2⟩ <;> simp [Fin.forall_fin_succ, sbc5Family_r] <;> grind

end HK
