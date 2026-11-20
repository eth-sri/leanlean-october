module

public import HK.Basic

/-!
# Mirtabatabaei–Bullo's Lemma 4.2 and Lemma 4.8

A point of the equi-topology neighbourhood of `z` has the proximity digraph of `z`; a convergent
trajectory whose limit has every equi-topology distance positive has, from some time on, the
proximity digraph of its limit, the limit as the final value at constant topology of `x(t)`, and the
limit is an equilibrium. No positivity of the bounds is assumed: the case `j = i` of Lemma 4.2
reduces, at `y` and at `z`, to the same condition `0 ≤ R`. The explicit limit gaps are checked for
the four source systems.
-/

public section

namespace HK

open Filter

/-- Reduce the finite set of threshold gaps to a minimum of explicit numbers. -/
local macro "gap_cases" : tactic => `(tactic| norm_num [equiTopologyDistance, hk_data, Set.ofPred_or,
    Set.singleton_union, csInf_insert])

theorem equiTopologyDistance_eq_zero :
    (∀ i ∈ (2⋯4 : Finset _), equiTopologyDistance sbc7_r sbc7_lim i = 0) ∧
    (∀ i ∈ ({1, 3, 5} : Finset _), equiTopologyDistance sbi7_r sbi7_lim i = 0) := by
  gap_cases

theorem equiTopologyDistance_pos :
    (∀ i, 0 < equiTopologyDistance sbc6_r sbc6_lim i) ∧
    (∀ i, 0 < equiTopologyDistance sbi7b_r sbi7b_lim i) := by
  gap_cases

variable (m : Model) {n : ℕ} (r : State n)
local notation "G" => proximityDigraph m r

theorem proximityDigraph_eq_of_equiTopologyNbhd (z y : State n)
    (h : EquiTopologyNbhd r z y) : G y = G z := by
  ext i j
  simp [proximityDigraph, neighbors]
  by_cases e : j = i
  · simp [e]
  -- Each endpoint moves by less than half the relevant gap, or not at all.
  have dev i {d} (hd : d ∈ gaps r z i) : |y i - z i| < 1 / 2 * d ∨ |y i - z i| = 0 := by
    have nn : 0 ∈ lowerBounds (gaps r z i) := by rintro _ ⟨j, -, rfl | rfl⟩ <;> positivity
    specialize h i
    unfold equiTopologyDistance at h
    grind [Real.sInf_nonneg nn, csInf_le ⟨0, nn⟩ hd]
  let d := gap z i j (m.bound r i j)
  have hi := dev i (d := d) ⟨j, e, by cases m <;> simp [d, Model.bound]⟩
  have hj := dev j (d := d) ⟨i, Ne.symm e, by
    cases m <;> simp [d, Model.bound, abs_sub_comm (z j) (z i)]⟩
  simp only [d, abs_eq_max_neg, max_def] at hi hj ⊢
  grind

variable (x₀ xinf : State n)
local notation "X" => traj m r x₀
variable (hconv : Converges (traj m r x₀) xinf) (hε : ∀ i, 0 < equiTopologyDistance r xinf i)
include hconv hε

theorem eventually_constant_of_tendsto :
    ∃ T, ∀ t, T ≤ t → G (X t) = G xinf := by
  apply eventually_atTop.mp
  have h i := Metric.tendsto_nhds.mp (tendsto_pi_nhds.mp hconv i) _ (hε i)
  filter_upwards [eventually_all.2 h] with t ht
  apply proximityDigraph_eq_of_equiTopologyNbhd
  intro i
  simpa [hε i, (hε i).ne', Real.dist_eq] using ht i

theorem fvct_eq_and_equilibrium_of_tendsto :
    (∃ T, ∀ t, T ≤ t → fvct m r (X t) = xinf) ∧ step m r xinf = xinf := by
  obtain ⟨T, H⟩ := eventually_constant_of_tendsto m r x₀ xinf hconv hε
  have rows t ht := graph_iff.1 (H t ht)
  have hf t (ht : T ≤ t) := frozen_tail m r t hconv fun s hs => by
    simp only [traj_succ, step, adjMatrix, rows t ht, rows s (le_trans ht hs)]
  refine ⟨⟨T, fun t ht => (hf t ht).1⟩, ?_⟩
  simpa only [step, adjMatrix, rows T le_rfl] using (hf T le_rfl).2

end HK
