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

section

variable {n : ℕ} {r z : Fin n → ℝ} {i j : Fin n}

private def gaps (r z : Fin n → ℝ) (i : Fin n) : Set ℝ :=
  {d | ∃ j, j ≠ i ∧ (d = abs (|z i - z j| - r i) ∨ d = abs (|z i - z j| - r j))}

private theorem gap_mem {R : ℝ} (hj : j ≠ i) (hR : R = r i ∨ R = r j) :
    abs (|z i - z j| - R) ∈ gaps r z i := by
  rcases hR with rfl | rfl <;> exact ⟨j, hj, by simp⟩

private theorem gap_nonneg : ∀ d ∈ gaps r z i, 0 ≤ d := by
  rintro d ⟨j, -, rfl | rfl⟩ <;> positivity

private theorem distance_nonneg : 0 ≤ equiTopologyDistance r z i :=
  mul_nonneg (by norm_num) (Real.sInf_nonneg gap_nonneg)

private theorem distance_le {R : ℝ} (hj : j ≠ i) (hR : R = r i ∨ R = r j) :
    equiTopologyDistance r z i ≤ (1 / 2) * abs (|z i - z j| - R) :=
  mul_le_mul_of_nonneg_left (csInf_le ⟨0, gap_nonneg⟩ (gap_mem hj hR)) (by norm_num)

theorem distance_zero {R : ℝ} (hj : j ≠ i) (hR : R = r i ∨ R = r j) (h : |z i - z j| = R) :
    equiTopologyDistance r z i = 0 :=
  le_antisymm (by simpa [h] using distance_le (z := z) hj hR) distance_nonneg

theorem distance_pos [Nontrivial (Fin n)] {B : ℝ} (hB : 0 < B)
    (h : ∀ k ≠ i, B ≤ abs (|z i - z k| - r i) ∧ B ≤ abs (|z i - z k| - r k)) :
    0 < equiTopologyDistance r z i := by
  obtain ⟨j, hj⟩ := exists_ne i
  refine mul_pos (by norm_num) (hB.trans_le (le_csInf ⟨_, gap_mem hj (.inl rfl)⟩ ?_))
  rintro d ⟨k, hk, rfl | rfl⟩ <;> grind

private theorem deviation {y : Fin n → ℝ} {b : ℝ} (h : EquiTopologyNbhd r z y)
    (hb : equiTopologyDistance r z i ≤ b) : |y i - z i| ≤ b ∧ (0 < b → |y i - z i| < b) := by
  have := h i
  have := distance_nonneg (r := r) (z := z) (i := i)
  grind

theorem proximityDigraph_eq_of_equiTopologyNbhd (m : Model) {n : ℕ} (r z y : Fin n → ℝ)
    (h : EquiTopologyNbhd r z y) : proximityDigraph m r y = proximityDigraph m r z := by
  apply digraph_eq_iff.mpr
  funext i
  ext j
  simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hj : j = i
  · subst j; simp
  have hR : m.bound r i j = r i ∨ m.bound r i j = r j := by cases m <;> simp [Model.bound]
  have hi := distance_le (z := z) hj hR
  have hj' := distance_le (z := z) (Ne.symm hj) hR.symm
  rw [abs_sub_comm (z j) (z i)] at hj'
  obtain ⟨di, di'⟩ := deviation h hi
  have dj := (deviation h hj').1
  have hb := dist_dist_dist_le (y i) (y j) (z i) (z j)
  simp only [Real.dist_eq, abs_le] at hb
  by_cases hz : |z i - z j| ≤ m.bound r i j
  · simp [hz]
    rw [abs_of_nonpos (sub_nonpos.mpr hz)] at di dj
    linarith
  · have hg := sub_pos.mpr (lt_of_not_ge hz)
    have ds := di' (by positivity)
    rw [abs_of_pos hg] at ds dj
    grind

end

section

variable (m : Model) {n : ℕ} (r x₀ xinf : Fin n → ℝ)
local notation "X" => traj m r x₀
local notation "G" => proximityDigraph m r
variable (hconv : Tendsto (traj m r x₀) atTop (𝓝 xinf)) (hε : ∀ i, 0 < equiTopologyDistance r xinf i)

include hconv hε

theorem eventually_constant_of_tendsto :
    ∃ T, ∀ t, T ≤ t → G (X t) = G xinf := by
  rw [← eventually_atTop]
  have h : ∀ᶠ t in atTop, ∀ i, |X t i - xinf i| < equiTopologyDistance r xinf i :=
    eventually_all.mpr fun i => by
      simpa [Real.dist_eq] using Metric.tendsto_nhds.mp (tendsto_pi_nhds.mp hconv i) _ (hε i)
  filter_upwards [h] with t ht
  exact proximityDigraph_eq_of_equiTopologyNbhd m r xinf _ fun i => ⟨fun _ => ht i, by grind⟩

theorem fvct_eq_and_equilibrium_of_tendsto :
    (∃ T, ∀ t, T ≤ t → fvct m r (X t) = xinf) ∧ step m r xinf = xinf := by
  obtain ⟨T, hT⟩ := eventually_constant_of_tendsto m r x₀ xinf hconv hε
  let A := adjMatrix m r xinf
  have hadj (t) (ht : T ≤ t) : adjMatrix m r (X t) = A := by
    simp only [A, adjMatrix, digraph_eq_iff.mp (hT t ht)]
  have hs (t) (ht : T ≤ t) : X (t + 1) = A.mulVec (X t) := by
    rw [traj_succ, step, hadj t ht]
  refine ⟨⟨T, fun t ht => ?_⟩, ?_⟩
  · exact fvct_of_tail t hconv fun k hk => by rw [hadj t ht, ← hs k (ht.trans hk)]
  · have hm : Continuous A.mulVec := by fun_prop
    exact tendsto_nhds_unique
      (((hm.tendsto xinf).comp hconv).congr' (eventually_atTop.mpr ⟨T, fun t ht => (hs t ht).symm⟩))
      (hconv.comp (tendsto_add_atTop_nat 1))

end

end HK
