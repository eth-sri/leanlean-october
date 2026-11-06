module

public import HK.Defs

/-!
# Generic lemmas about the models

The mean form of a step, the sign and size of the rates' powers, convergence of a geometric closed form
`L + a(t) v`, the two ways an alternating agent defeats a fixed state and pseudo-stability, the mean form of
`A(y) z`, neighbourhoods from digraphs, and the facts about `sbiRate = (1 − √5)/8`.
-/

@[expose] public section

namespace HK

open Filter Topology

variable {n : ℕ}

theorem adj_mulVec (m : Model) (r y z : Fin n → ℝ) (i : Fin n) :
    (adjMatrix m r y).mulVec z i = (∑ j ∈ neighbors m r y i, z j) / (neighbors m r y i).card := by
  simp only [adjMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_div]
  exact Finset.sum_congr rfl (fun j _ => by ring)

theorem step_apply (m : Model) (r y : Fin n → ℝ) (i : Fin n) :
    step m r y i = (∑ j ∈ neighbors m r y i, y j) / (neighbors m r y i).card :=
  adj_mulVec m r y y i

theorem traj_succ (m : Model) (r x₀ : Fin n → ℝ) (t : ℕ) :
    traj m r x₀ (t + 1) = step m r (traj m r x₀ t) :=
  Function.iterate_succ_apply' _ _ _

theorem pow_bounds_of_neg {q : ℝ} (hq : -1 ≤ q) (hq0 : q < 0) (t : ℕ) :
    q ≤ q ^ t ∧ q ^ t ≤ 1 := by
  induction t with
  | zero => simp; linarith
  | succ t ih =>
    rw [pow_succ]
    constructor <;> nlinarith [ih.1, ih.2]

theorem neg_pow_pos_even {q : ℝ} (hq : q < 0) {t : ℕ} (ht : Even t) : 0 < q ^ t := by
  rw [← neg_neg q, ht.neg_pow]
  exact pow_pos (neg_pos.mpr hq) t

theorem neg_pow_neg_odd {q : ℝ} (hq : q < 0) {t : ℕ} (ht : Odd t) : q ^ t < 0 := by
  rw [← neg_neg q, ht.neg_pow, neg_lt_zero]
  exact pow_pos (neg_pos.mpr hq) t

theorem pow_even {t : ℕ} (ht : Even t) : 0 < (-1 / 6 : ℝ) ^ t ∧ (-1 / 6 : ℝ) ^ t ≤ 1 :=
  ⟨neg_pow_pos_even (by norm_num) ht, (pow_bounds_of_neg (by norm_num) (by norm_num) t).2⟩

theorem pow_odd {t : ℕ} (ht : Odd t) : -1 / 6 ≤ (-1 / 6 : ℝ) ^ t ∧ (-1 / 6 : ℝ) ^ t < 0 :=
  ⟨(pow_bounds_of_neg (by norm_num) (by norm_num) t).1, neg_pow_neg_odd (by norm_num) ht⟩

theorem sbiRate_eq : sbiRate = (1 - Real.goldenRatio) / 4 := by
  unfold sbiRate Real.goldenRatio
  ring

theorem sbiRate_neg : sbiRate < 0 := by
  rw [sbiRate_eq]
  linarith [Real.one_lt_goldenRatio]

theorem sbiRate_abs_lt_one : |sbiRate| < 1 := by
  rw [sbiRate_eq, abs_lt]
  constructor <;> linarith [Real.one_lt_goldenRatio, Real.goldenRatio_lt_two]

theorem abs_negSixth : |(-1 / 6 : ℝ)| < 1 := by
  rw [abs_of_neg (by norm_num)]
  norm_num

theorem pow_bounds (t : ℕ) : -1 / 6 ≤ (-1 / 6 : ℝ) ^ t ∧ (-1 / 6 : ℝ) ^ t ≤ 1 :=
  pow_bounds_of_neg (by norm_num) (by norm_num) t

theorem sbiRate_pow_bounds (t : ℕ) :
    (1 - Real.goldenRatio) / 4 ≤ sbiRate ^ t ∧ sbiRate ^ t ≤ 1 := by
  rw [← sbiRate_eq]
  exact pow_bounds_of_neg
    (by rw [sbiRate_eq]; linarith [Real.one_lt_goldenRatio, Real.goldenRatio_lt_two]) sbiRate_neg t

theorem sbiRate_pow_even {t : ℕ} (ht : Even t) :
    0 < sbiRate ^ t / 2 ∧ sbiRate ^ t / 2 ≤ 1 / 2 :=
  ⟨div_pos (neg_pow_pos_even sbiRate_neg ht) (by norm_num), by linarith [(sbiRate_pow_bounds t).2]⟩

theorem sbiRate_pow_odd {t : ℕ} (ht : Odd t) :
    (1 - Real.goldenRatio) / 8 ≤ sbiRate ^ t / 2 ∧ sbiRate ^ t / 2 < 0 :=
  ⟨by linarith [(sbiRate_pow_bounds t).1],
    div_neg_of_neg_of_pos (neg_pow_neg_odd sbiRate_neg ht) (by norm_num)⟩

theorem tendsto_of_closed_form (x : ℕ → Fin n → ℝ) (lim v : Fin n → ℝ) (a : ℕ → ℝ)
    (ha : Tendsto a atTop (𝓝 0)) (hx : ∀ t, x t = fun i => lim i + a t * v i) :
    Tendsto x atTop (𝓝 lim) := by
  rw [tendsto_pi_nhds]
  intro i
  simpa [hx] using (ha.mul_const (v i)).const_add (lim i)

theorem not_pseudoStable_of_closed_form (x : ℕ → Fin n → ℝ) (lim v : Fin n → ℝ)
    (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0)) (hx : ∀ t, x t = fun i => lim i + a t * v i)
    (hab : ∀ t, a t * a (t + 1) < 0) (xinf : Fin n → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter x xinf τ := by
  rintro ⟨hlim, F, C, -, ⟨i, hi⟩, -, -, h⟩
  have hx' : xinf = lim := tendsto_nhds_unique hlim (tendsto_of_closed_form x lim v a ha hx)
  subst hx'
  have hc := (h τ le_rfl).2 i hi
  rw [hx, hx] at hc
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    nlinarith [hab τ, sq_nonneg (v i), sq_nonneg (a (τ + 1) * v i)]

theorem not_fixedFrom_of_closed_form (x : ℕ → Fin n → ℝ) (lim v : Fin n → ℝ)
    (a : ℕ → ℝ) (hx : ∀ t, x t = fun i => lim i + a t * v i)
    (hab : ∀ t, a t * a (t + 1) < 0) (i : Fin n) (hv : v i ≠ 0) (τ : ℕ) :
    ¬ FixedFrom x τ := by
  intro h
  have h1 := congrFun (h (τ + 1) (Nat.le_succ τ)) i
  rw [hx, hx] at h1
  have h2 : a (τ + 1) = a τ := mul_right_cancel₀ hv (by simpa using h1)
  have h3 := hab τ
  rw [h2] at h3
  nlinarith [sq_nonneg (a τ)]

/-- `a t · a (t+1) < 0` for `a t = q^t · c` with `q < 0`, `c ≠ 0`. -/
theorem alternating (q c : ℝ) (hq : q < 0) (hc : c ≠ 0) (t : ℕ) :
    q ^ t * c * (q ^ (t + 1) * c) < 0 := by
  rw [show q ^ t * c * (q ^ (t + 1) * c) = q * (q ^ t * c) ^ 2 by ring]
  exact mul_neg_of_neg_of_pos hq (sq_pos_of_ne_zero (mul_ne_zero (pow_ne_zero t hq.ne) hc))

theorem not_fixedFrom_of_pow (x : ℕ → Fin n → ℝ) (L v : Fin n → ℝ) (q : ℝ)
    (hx : ∀ t, x t = fun i => L i + q ^ t * v i) (hq : q < 0)
    (i : Fin n) (hv : v i ≠ 0) (τ : ℕ) : ¬ FixedFrom x τ :=
  not_fixedFrom_of_closed_form _ _ _ _ hx
    (by simpa using alternating q 1 hq one_ne_zero) i hv τ

theorem not_pseudoStable_of_pow (x : ℕ → Fin n → ℝ) (L v : Fin n → ℝ) (q : ℝ)
    (habs : |q| < 1) (hx : ∀ t, x t = fun i => L i + q ^ t * v i) (hq : q < 0)
    (xinf : Fin n → ℝ) (τ : ℕ) : ¬ PseudoStableAfter x xinf τ :=
  not_pseudoStable_of_closed_form _ _ _ _ (tendsto_pow_atTop_nhds_zero_of_abs_lt_one habs) hx
    (by simpa using alternating q 1 hq one_ne_zero) xinf τ

theorem tendsto_of_pow_closed_form (x : ℕ → Fin n → ℝ) (L v : Fin n → ℝ) (q : ℝ)
    (habs : |q| < 1) (hx : ∀ t, x t = fun i => L i + q ^ t * v i) : Tendsto x atTop (𝓝 L) :=
  tendsto_of_closed_form _ _ _ _ (tendsto_pow_atTop_nhds_zero_of_abs_lt_one habs) hx

theorem digraph_constant_of_neighbors (m : Model) (r x₀ : Fin n → ℝ)
    (N : Fin n → Finset (Fin n)) (h : ∀ t, neighbors m r (traj m r x₀ t) = N) (t : ℕ) :
    proximityDigraph m r (traj m r x₀ t) = proximityDigraph m r x₀ := by
  have h0 := h 0
  change neighbors m r x₀ = N at h0
  simp only [proximityDigraph, h, h0]

theorem fvct_of_eigen (m : Model) (r x L v : Fin n → ℝ) (q c : ℝ)
    (hx : x = L + c • v) (hL : (adjMatrix m r x).mulVec L = L)
    (hv : (adjMatrix m r x).mulVec v = q • v) (hq : |q| < 1) : fvct m r x = L := by
  have hpow : ∀ k, (adjMatrix m r x ^ k).mulVec x = L + (q ^ k * c) • v := by
    intro k
    induction k with
    | zero => simp [hx]
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_add, Matrix.mulVec_smul,
        hL, hv, smul_smul, pow_succ]
      congr 2
      ring
  unfold fvct
  simp only [hpow]
  have h := (((tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq).mul_const c).smul_const v).const_add L
  simpa using h.limUnder_eq

theorem perStepFactor_of_closed_form (m : Model) (r : Fin n → ℝ)
    (x : ℕ → Fin n → ℝ) (L v : Fin n → ℝ) (q : ℝ) (i : Fin n) (t : ℕ)
    (hfv : fvct m r (x t) = L) (hx : ∀ t, x t = fun i => L i + q ^ t * v i)
    (hq : q ≠ 0) (hv : v i ≠ 0) : perStepFactor m r x i t = q := by
  have hp := pow_ne_zero t hq
  rw [perStepFactor, hfv, hx, hx]
  simp only [add_sub_cancel_left, pow_succ]
  field_simp

theorem not_conjecture22_of (m : Model) (r x₀ : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (h : ∀ τ, ∃ t, τ ≤ t ∧ proximityDigraph m r (traj m r x₀ t) ≠
      proximityDigraph m r (traj m r x₀ τ)) : ¬ Conjecture22ForAgents m n := by
  intro hc
  obtain ⟨τ, hτ⟩ := hc r x₀ hr
  obtain ⟨t, ht, hne⟩ := h τ
  exact hne (hτ t ht)

theorem not_conjecture23_of (m : Model) (r x₀ : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hf : ∀ τ, ¬ FixedFrom (traj m r x₀) τ)
    (hp : ∀ xinf τ, ¬ PseudoStableAfter (traj m r x₀) xinf τ) :
    ¬ Conjecture23ForAgents m n := by
  intro hc
  obtain ⟨τ, hf' | ⟨xinf, hp'⟩⟩ := hc r x₀ hr
  · exact hf τ hf'
  · exact hp xinf τ hp'

theorem not_theorem64iv_of (m : Model) (r x₀ : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hd : ∀ t, proximityDigraph m r (traj m r x₀ t) = proximityDigraph m r x₀)
    (hf : ∀ τ, ¬ FixedFrom (traj m r x₀) τ)
    (hp : ∀ xinf τ, ¬ PseudoStableAfter (traj m r x₀) xinf τ) :
    ¬ Theorem64ivForAgents m n := by
  intro hc
  obtain ⟨t₂, -, hf' | ⟨xinf, hp'⟩⟩ := hc r x₀ hr 0 (fun t _ => by
    simpa only [traj, Function.iterate_zero, id_eq] using hd t)
  · exact hf t₂ hf'
  · exact hp xinf t₂ hp'

theorem not_theorem64iv_literal_of (m : Model) (h : ¬ Theorem64ivFor m) :
    ¬ Theorem64ivLiteralFor m := by
  intro hl
  apply h
  intro n r x₀ hr τ hτ
  obtain ⟨t₂, ht₂, hps⟩ := hl n r x₀ hr τ hτ
  exact ⟨t₂, ht₂, Or.inr hps⟩

end HK
