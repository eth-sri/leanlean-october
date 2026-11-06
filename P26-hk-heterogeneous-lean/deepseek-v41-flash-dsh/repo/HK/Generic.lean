module

public import HK.Basic

/-!
# Mirtabatabaei–Bullo's Lemma 4.2 and Lemma 4.8

A point of the equi-topology neighbourhood of `z` has the proximity digraph of `z`; a convergent
trajectory whose limit has every equi-topology distance positive has, from some time on, the
proximity digraph of its limit, the limit as the final value at constant topology of `x(t)`, and the
limit is an equilibrium. No positivity of the bounds is assumed: the case `j = i` of Lemma 4.2
reduces, at `y` and at `z`, to the same condition `0 ≤ R`. Also: `ε_i(z) = 0` as soon as some
`j ≠ i` has `|z_i − z_j| = r_i`.
-/

@[expose] public section

namespace HK

open Filter Topology

/-- `ε_i(z) = 0` as soon as one `j ≠ i` has `|z_i − z_j| = r_i`. -/
theorem equiTopologyDistance_eq_zero_of {n : ℕ} (r z : Fin n → ℝ) (i j : Fin n) (hij : j ≠ i)
    (h : |z i - z j| = r i) : equiTopologyDistance r z i = 0 := by
  unfold equiTopologyDistance
  have hS : sInf {d : ℝ | ∃ j, j ≠ i ∧ (d = |(|z i - z j|) - r i| ∨ d = |(|z i - z j|) - r j|)} = 0 := by
    apply IsLeast.csInf_eq
    refine ⟨⟨j, hij, Or.inl (by rw [h, sub_self, abs_zero])⟩, ?_⟩
    rintro d ⟨k, -, rfl | rfl⟩ <;> exact abs_nonneg _
  rw [hS, mul_zero]

theorem abs_band_iff (a b c d R : ℝ) (h1 : |a - c| ≤ 1 / 2 * |(|c - d|) - R|)
    (h2 : |b - d| ≤ 1 / 2 * |(|c - d|) - R|)
    (h1' : |c - d| ≠ R → |a - c| < 1 / 2 * |(|c - d|) - R|)
    (h2' : |c - d| ≠ R → |b - d| < 1 / 2 * |(|c - d|) - R|) :
    |a - b| ≤ R ↔ |c - d| ≤ R := by
  have t1 := abs_sub_le a c b
  have t2 := abs_sub_le c d b
  have t3 := abs_sub_le c a d
  have t4 := abs_sub_le a b d
  have s1 := abs_sub_comm c a
  have s2 := abs_sub_comm d b
  rcases lt_trichotomy (|c - d|) R with hlt | heq | hgt
  · rw [abs_of_neg (by linarith : |c - d| - R < 0)] at h1 h2
    constructor <;> intro <;> linarith
  · rw [heq, sub_self, abs_zero, mul_zero] at h1 h2
    constructor <;> intro <;> linarith
  · rw [abs_of_pos (by linarith : 0 < |c - d| - R)] at h1' h2'
    have e1 := h1' hgt.ne'
    have e2 := h2' hgt.ne'
    constructor <;> intro <;> linarith

chall proximityDigraph_eq_of_equiTopologyNbhd "  have hS_bdd : ∀ i, BddBelow {d : ℝ | ∃ j, j ≠ i ∧
      (d = |(|z i - z j|) - r i| ∨ d = |(|z i - z j|) - r j|)} := fun i =>
    ⟨0, by rintro d ⟨k, -, rfl | rfl⟩ <;> exact abs_nonneg _⟩
  have hle : ∀ i j, j ≠ i → ∀ R, (R = r i ∨ R = r j) →
      equiTopologyDistance r z i ≤ 1 / 2 * |(|z i - z j|) - R| := by
    intro i j hij R hR
    unfold equiTopologyDistance
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply csInf_le (hS_bdd i)
    rcases hR with rfl | rfl
    · exact ⟨j, hij, Or.inl rfl⟩
    · exact ⟨j, hij, Or.inr rfl⟩
  have hnn : ∀ i, 0 ≤ equiTopologyDistance r z i := by
    intro i
    unfold equiTopologyDistance
    apply mul_nonneg (by norm_num)
    apply Real.sInf_nonneg
    rintro d ⟨k, -, rfl | rfl⟩ <;> exact abs_nonneg _
  have hdev : ∀ i, |y i - z i| ≤ equiTopologyDistance r z i ∧
      (|y i - z i| < equiTopologyDistance r z i ∨ y i = z i) := by
    intro i
    rcases (hnn i).lt_or_eq with hpos | hzero
    · have := (h i).1 hpos
      exact ⟨this.le, Or.inl this⟩
    · have := (h i).2 hzero.symm
      refine ⟨this.le, Or.inr ?_⟩
      rw [← hzero] at this
      exact sub_eq_zero.mp (abs_eq_zero.mp this)
  have key : ∀ i j, (j ∈ neighbors m r y i ↔ j ∈ neighbors m r z i) := by
    intro i j
    simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hij : j = i
    · subst hij; simp
    have hR : m.bound r i j = r i ∨ m.bound r i j = r j := by cases m <;> simp [Model.bound]
    have hi := hle i j hij _ hR
    have hj := hle j i (Ne.symm hij) _ hR.symm
    rw [abs_sub_comm (z j) (z i)] at hj
    obtain ⟨d1, d1'⟩ := hdev i
    obtain ⟨d2, d2'⟩ := hdev j
    apply abs_band_iff
    · exact d1.trans hi
    · exact d2.trans hj
    · intro hne
      rcases d1' with h' | h'
      · exact lt_of_lt_of_le h' hi
      · rw [h', sub_self, abs_zero]
        have := abs_pos.mpr (sub_ne_zero.mpr hne)
        linarith
    · intro hne
      rcases d2' with h' | h'
      · exact lt_of_lt_of_le h' hj
      · rw [h', sub_self, abs_zero]
        have := abs_pos.mpr (sub_ne_zero.mpr hne)
        linarith
  unfold proximityDigraph
  congr 1
  funext i j
  exact propext (key i j)"

chall eventually_constant_of_tendsto "  have hev : ∀ᶠ t in atTop, ∀ i, |traj m r x₀ t i - xinf i| < equiTopologyDistance r xinf i := by
    rw [Filter.eventually_all]
    intro i
    have hi := (tendsto_pi_nhds.mp hconv) i
    have := Metric.tendsto_nhds.mp hi _ (hε i)
    simpa [Real.dist_eq] using this
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hev
  refine ⟨T, fun t ht => proximityDigraph_eq_of_equiTopologyNbhd_internal m r xinf _ ?_⟩
  intro i
  exact ⟨fun _ => hT t ht i, fun h0 => absurd h0 (hε i).ne'⟩"

chall fvct_eq_and_equilibrium_of_tendsto "  obtain ⟨T, hT⟩ := eventually_constant_of_tendsto_internal m r x₀ xinf hconv hε
  set A := adjMatrix m r xinf with hA
  have hadj : ∀ t, T ≤ t → adjMatrix m r (traj m r x₀ t) = A := by
    intro t ht
    simp only [hA, adjMatrix, neighbors_eq_of_digraph_eq m r _ _ (hT t ht)]
  have hstep : ∀ t, T ≤ t → traj m r x₀ (t + 1) = A.mulVec (traj m r x₀ t) := by
    intro t ht
    rw [traj_succ, step, hadj t ht]
  refine ⟨⟨T, fun t ht => ?_⟩, ?_⟩
  · have hpow : ∀ k, (A ^ k).mulVec (traj m r x₀ t) = traj m r x₀ (k + t) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', ← Matrix.mulVec_mulVec, ih, ← hstep _ (by omega)]
        congr 1
        omega
    unfold fvct
    rw [hadj t ht]
    simp only [hpow]
    exact (hconv.comp (tendsto_add_atTop_nat t)).limUnder_eq
  · have hc : Continuous (fun v : Fin n → ℝ => A.mulVec v) :=
      continuous_const.matrix_mulVec continuous_id
    have h1 : Tendsto (fun t => traj m r x₀ (t + 1)) atTop (𝓝 xinf) :=
      hconv.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun t => A.mulVec (traj m r x₀ t)) atTop (𝓝 (A.mulVec xinf)) :=
      (hc.tendsto xinf).comp hconv
    have h3 : Tendsto (fun t => traj m r x₀ (t + 1)) atTop (𝓝 (A.mulVec xinf)) := by
      refine h2.congr' ?_
      rw [Filter.EventuallyEq, Filter.eventually_atTop]
      exact ⟨T, fun t ht => (hstep t ht).symm⟩
    rw [step]
    exact tendsto_nhds_unique h3 h1"

end HK
