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

set_option hygiene false

notation "aff(" lim ", " u ", " v ")" => fun i => lim i + u * v i
notation "sbcRate" => (-1 / 6 : ℝ)
notation "~" s => (s : Finset _)
notation "tr7c" => traj .sbc sbc7_r sbc7_x0
notation "tr7i" => traj .sbi sbi7_r sbi7_x0
notation "tr6c" => traj .sbc sbc6_r sbc6_x0
notation "tr7b" => traj .sbi sbi7b_r sbi7b_x0
notation "tr5" => traj .sbc sbc5_r sbc5_x0
notation "tr6" => traj .sbi sbi6_r sbi6_x0
notation "tr9" => traj .sbc sbc9_r sbc9_x0
notation "tr8" => traj .sbi sbi8_r sbi8_x0

attribute [simp] Model.bound sbc7_x0 sbc7_r sbc7_lim sbc7_v sbi7_x0 sbi7_r sbi7_lim
  sbi7b_x0 sbi7b_r sbi7b_lim sbi_v sbc6_x0 sbc6_r sbc6_lim sbc6_v
  sbc5_x0 sbc5_r sbc5_lim sbc5_v sbc5Family_r sbc5Family_x0
  sbi6_x0 sbi6_r sbi6_lim sbi6_v sbc9_x0 sbc9_r sbi8_x0 sbi8_r
  sbi5_r sbi5_lim sbi5LinearStep sbi5Lift

theorem adj_mulVec m (r y z : V n) i :
    (adjMatrix m r y).mulVec z i = (∑ j ∈ neighbors m r y i, z j) / (neighbors m r y i).card := by
  simp [adjMatrix, Matrix.mulVec, dotProduct, Finset.mul_sum, div_eq_inv_mul]

macro "hk_table" : tactic =>
  `(tactic| (
    have := neg_pow_bounds sbcRate_lt t
    have := neg_pow_bounds sbiRate_lt t
    have := sbiRate_pow_bounds t
    ext i j; fin_cases i <;> fin_cases j <;>
    dsimp [neighbors] <;> (try split_ifs with ht <;> simp [ht, abs_le, -one_div] at *) <;>
    (try simp [abs_le, -one_div]) <;>
    (try constructor) <;> (try intro) <;> linarith))

macro "hk_traj" h0:Lean.Parser.Tactic.tacticSeq "=>" hs:Lean.Parser.Tactic.tacticSeq : tactic =>
  `(tactic| induction t with
    | zero => dsimp [traj]; ($h0)
    | succ t ih => rw [traj, Function.iterate_succ_apply', ← traj, ih, step]; funext i; rw [adj_mulVec]; ($hs))

macro "hk_avg" : tactic =>
  `(tactic| (
    have h1 := Real.goldenRatio_sq
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h3 : Real.sqrt 249 ^ 2 = 249 := Real.sq_sqrt (by norm_num)
    (try intro u i); fin_cases i <;> (try split_ifs) <;>
    simp [Finset.sum_insert, pow_succ, sbiRate_eq, sbc5Rate, sbi6Rate] <;>
    ring_nf <;> simp [h1, h2, h3] <;> ring))

variable {r lim v : V n} {N : ℕ → Fin n → Finset (Fin n)}

local notation "Eig" S:max q:max =>
  ∀ u i, (∑ j ∈ S i, (lim j + u * v j)) / (S i).card = lim i + (q * u) * v i

theorem neg_pow_bounds (hq : c < q ∧ q < %0) t (hc : -1 ≤ c := by norm_num) :
    (q ≤ q ^ t ∧ q ^ t ≤ 1) ∧ if Even t then 0 < q ^ t else q ^ t < 0 := by
  induction t with
  | zero => simp; linarith
  | succ t ih =>
    simp only [pow_succ, Nat.even_add_one]
    split_ifs at * <;> refine ⟨⟨?_, ?_⟩, ?_⟩ <;> nlinarith

theorem unit_pow c t (h : 0 ≤ c ∧ c ≤ %1 := by norm_num) : 0 ≤ c ^ t ∧ c ^ t ≤ 1 :=
  ⟨pow_nonneg h.1 t, pow_le_one₀ h.1 h.2⟩

theorem sbcRate_lt : -1 < sbcRate ∧ sbcRate < 0 := by norm_num

/-- `λ = (1 − φ)/4`. -/
theorem sbiRate_eq : sbiRate = (1 - Real.goldenRatio) / 4 := by
  unfold sbiRate Real.goldenRatio; ring

theorem sbiRate_lt : -1 / 4 < sbiRate ∧ sbiRate < 0 := by
  rw [sbiRate_eq]; constructor <;> linarith [Real.one_lt_goldenRatio, Real.goldenRatio_lt_two]

theorem pow_lt q c (ht : 1 ≤ t)
    (h : -c < q ∧ q < %c := by constructor <;> linarith [sbiRate_lt]) : q ^ t < c ^ t :=
  (le_abs_self _).trans_lt <| by rw [abs_pow]; exact pow_lt_pow_left₀ (abs_lt.2 h) (by positivity) (by omega)

theorem sbc_sqrt_two_bounds : 1.4 < Real.sqrt 2 ∧ Real.sqrt 2 < 1.5 := by
  rw [Real.lt_sqrt, Real.sqrt_lt'] <;> norm_num

theorem sbc5Rate_lt : -1 < sbc5Rate ∧ sbc5Rate < 0 := by
  unfold sbc5Rate; constructor <;> linarith [sbc_sqrt_two_bounds]

theorem sbi_sqrt249_bounds : 15 < Real.sqrt 249 ∧ Real.sqrt 249 < 16 := by
  rw [Real.lt_sqrt, Real.sqrt_lt'] <;> norm_num

theorem sbi6Rate_lt : -3 / 40 < sbi6Rate ∧ sbi6Rate < 0 := by
  unfold sbi6Rate; constructor <;> linarith [sbi_sqrt249_bounds]

theorem sbiRate_pow_bounds t :
    (1 < Real.goldenRatio ∧ Real.goldenRatio < 2) ∧
    (15 < Real.sqrt 249 ∧ Real.sqrt 249 < 16) ∧
    (1 - Real.goldenRatio) / 4 ≤ sbiRate ^ t ∧
    (-1 / 4 ≤ sbiRate ^ t * Real.goldenRatio ∧ sbiRate ^ t * Real.goldenRatio ≤ 2) ∧
    (-3 / 40 ≤ sbi6Rate ^ t ∧ sbi6Rate ^ t ≤ 1) ∧
    (-2 ≤ sbi6Rate ^ t * Real.sqrt 249 ∧ sbi6Rate ^ t * Real.sqrt 249 ≤ 16) := by
  have := (neg_pow_bounds sbiRate_lt t).1; have := (neg_pow_bounds sbi6Rate_lt t).1
  have := Real.one_lt_goldenRatio; have := Real.goldenRatio_lt_two; have := Real.goldenRatio_sq
  have := sbiRate_eq; have := sbi_sqrt249_bounds; have := sbi6Rate_lt
  exact ⟨⟨‹_›, ‹_›⟩, ‹_›, by linarith, ⟨by nlinarith, by nlinarith⟩, ⟨by linarith, by linarith⟩, by nlinarith, by nlinarith⟩

macro "rate_lt" : tactic =>
  `(tactic| constructor <;> linarith [sbiRate_lt, sbc5Rate_lt, sbi6Rate_lt])

theorem tendsto_geom
    (hx : ∀ t, x t = aff(lim, q ^ t, v)) (hq : -1 < q ∧ q < 0 := by rate_lt) :
    Tendsto x atTop (𝓝 lim) :=
  tendsto_pi_nhds.mpr fun i => by
    simpa [hx] using ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one
      (abs_lt.mpr ⟨hq.1, by linarith⟩)).mul_const (v i)).const_add (lim i)

theorem not_fixedFrom_geom {lim v : V (n + 2)}
    (hx : ∀ t, x t = aff(lim, q ^ t, v)) (hq : -1 < q ∧ q < 0 := by rate_lt)
    (hv : v 1 ≠ 0 := by simp) : ¬ FixedFrom x τ := fun h => by
  have h1 := congrFun (h (τ + 1) (Nat.le_succ _)) 1
  simp [hx, pow_succ, pow_ne_zero _ hq.2.ne, hv] at h1
  linarith

theorem not_pseudoStable_geom
    (hx : ∀ t, x t = aff(lim, q ^ t, v)) (hq : -1 < q ∧ q < 0 := by rate_lt) :
    ¬ PseudoStableAfter x xinf τ := by
  rintro ⟨hlim, F, C, -, ⟨i, hi⟩, -, -, h⟩
  obtain rfl := tendsto_nhds_unique hlim (tendsto_geom hx hq)
  have hc := (h τ le_rfl).2 i hi
  rw [hx, hx, pow_succ] at hc
  rcases hc with ⟨_, _⟩ | ⟨_, _⟩ <;> nlinarith [sq_nonneg (q ^ τ * v i)]

notation "tr" => traj m r x₀
notation "pd" => proximityDigraph m r
notation "nbc" => neighbors .sbc
notation "nbi" => neighbors .sbi
notation "pdc" => proximityDigraph .sbc
notation "pdi" => proximityDigraph .sbi
notation "nbh" f => by rw [f]; hk_table
notation "Nlim" m:max r:max x:max =>
  ∀ ρ, 0 ≤ ρ → ¬ Filter.Tendsto (fun t => perStepFactor m r x i t) Filter.atTop (nhds ρ)
notation "ntpsf" f =>
  fun _ hρ h => by simp only [f _ i hi, tendsto_const_nhds_iff] at h; linarith [sbiRate_lt.2]

theorem traj_eigen
    (hN : ∀ t, neighbors m r (aff(lim, q ^ t, v)) = N t := by intro t; hk_table)
    (havg : ∀ t, Eig (N t) q := by intro t; hk_avg)
    (h0 : x₀ = fun i => lim i + v i := by funext i; fin_cases i <;> simp <;> ring) :
    tr t = aff(lim, q ^ t, v) := by
  hk_traj simpa using h0 =>
    rw [hN, havg t, pow_succ]; ring

theorem digraph_const_of_neighbors
    (hN : ∀ t, neighbors m r (tr t) = S) t :
    pd (tr t) = pd x₀ := by
  rw [proximityDigraph, proximityDigraph, (hN t).trans (hN 0).symm]; rfl

notation "dnec" hN:max j:max =>
  ⟨τ + 1, Nat.le_succ _, fun h => by
    have := congrArg (·.Adj 3 j) h
    rw [proximityDigraph, proximityDigraph, hN, hN] at this
    by_cases ht : Even τ <;> simp [Nat.even_add_one, ht] at this⟩

theorem fvct_eigen
    (hx : ∀ t, tr t = aff(lim, q ^ t, v))
    (hN : ∀ t, neighbors m r (tr t) = N t)
    (hq : -1 < q ∧ q < 0 := by rate_lt)
    (havg : Eig (N t) q := by hk_avg) :
    fvct m r (tr t) = lim := by
  have hpow k : (adjMatrix m r (tr t) ^ k).mulVec (tr t) =
      aff(lim, q ^ k, fun i => q ^ t * v i) := by
    induction k with
    | zero => simp [hx]
    | succ k ih =>
      funext i
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, adj_mulVec, hN]
      simp only [← mul_assoc, havg, pow_succ]
      ring
  exact (tendsto_geom hpow hq).limUnder_eq

theorem perStepFactor_geom
    (hx : ∀ t, tr t = aff(lim, q ^ t, v))
    (hf : ∀ t, fvct m r (tr t) = lim)
    (hq : -1 < q ∧ q < 0 := by rate_lt)
    (hv : v i ≠ 0 := by
      fin_cases hi <;> simp [Real.goldenRatio_pos.ne'] <;> linarith [Real.sqrt_nonneg 249]) :
    perStepFactor m r tr i t = q := by
  have := pow_ne_zero t hq.2.ne
  rw [perStepFactor, hf, hx, hx]
  simp only [add_sub_cancel_left, pow_succ]
  field_simp

theorem refute_both
    (hd : ∀ t, pd (tr t) = pd x₀)
    (hf : ∀ τ, ¬ FixedFrom tr τ)
    (hps : ∀ xinf τ, ¬ PseudoStableAfter tr xinf τ)
    (hr : ∀ i, 0 < r i := by intro i; fin_cases i <;> norm_num) :
    ¬ Conjecture23ForAgents m n ∧ ¬ Theorem64ivForAgents m n := by
  have hn τ := not_or.2 ⟨hf τ, not_exists.2 (hps · τ)⟩
  exact ⟨fun h => let ⟨_, h⟩ := h r x₀ hr; hn _ h,
    fun h => let ⟨_, _, h⟩ := h r x₀ hr 0 fun t _ => hd t; hn _ h⟩

end HK
