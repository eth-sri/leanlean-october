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

set_option hygiene false
set_option quotPrecheck false

notation "lb0" => by rintro _ ⟨_, -, rfl | rfl⟩ <;> positivity

variable (m : Model) {n} (r z y x₀ xinf : V n)

theorem proximityDigraph_eq_of_equiTopologyNbhd
    (h : EquiTopologyNbhd r z y) : pd y = pd z := by
  simp only [proximityDigraph, neighbors, Finset.mem_filter, Finset.mem_univ, true_and]
  congr! 3 with i j
  by_cases hij : j = i
  · subst hij; simp
  let R := m.bound r i j
  have hb {a b} (hab : b ≠ a) (hR : R = r a ∨ R = r b := by cases m <;> simp [R]) :
      |y a - z a| = 0 ∨ |y a - z a| < 1 / 2 * |(|z a - z b|) - R| := by
    have hnn : 0 ≤ equiTopologyDistance r z a :=
      mul_nonneg (by norm_num) (Real.sInf_nonneg lb0)
    rcases hnn.lt_or_eq with hp | hz
    · exact .inr <| ((h a).1 hp).trans_le <| mul_le_mul_of_nonneg_left
        (csInf_le ⟨0, lb0⟩ ⟨b, by aesop⟩) (by norm_num)
    · exact .inl <| hz ▸ (h a).2 hz.symm
  have hj := hb (Ne.symm hij)
  rw [abs_sub_comm (z j) (z i)] at hj
  simp only [abs_lt, abs_eq_zero, sub_eq_zero] at hb hj
  cases hb hij <;> cases hj <;>
    cases abs_cases (y i - y j) <;>
    cases abs_cases (z i - z j) <;>
    cases abs_cases (|z i - z j| - R) <;>
    constructor <;> intro <;> linarith

variable (hconv : Tendsto tr atTop (𝓝 xinf))
  (hε : ∀ i, 0 < equiTopologyDistance r xinf i)
include hconv hε

theorem eventually_constant_of_tendsto :
    ∃ T, ∀ t, T ≤ t → pd (tr t) = pd xinf :=
  eventually_atTop.mp <| (eventually_all.mpr fun i => by
    simpa [Real.dist_eq] using Metric.tendsto_nhds.mp (tendsto_pi_nhds.mp hconv i) _ (hε i)).mono
    fun _ ht => proximityDigraph_eq_of_equiTopologyNbhd m r xinf _ fun i =>
      ⟨fun _ => ht i, fun h0 => absurd h0 (hε i).ne'⟩

theorem fvct_eq_and_equilibrium_of_tendsto :
    (∃ T, ∀ t, T ≤ t → fvct m r (tr t) = xinf) ∧ step m r xinf = xinf := by
  obtain ⟨T, hT⟩ := eventually_constant_of_tendsto m r x₀ xinf hconv hε
  let A := adjMatrix m r xinf
  have hadj t (ht : T ≤ t) : adjMatrix m r (tr t) = A := by
    simp [A, adjMatrix, show neighbors m r (tr t) = _ by
      ext i j; simpa [proximityDigraph] using congrArg (·.Adj i j) (hT t ht)]
  have hstep t (ht : T ≤ t) : tr (t + 1) = A.mulVec (tr t) := by
    rw [traj, Function.iterate_succ_apply', ← traj, step, hadj t ht]
  have hsh t : Tendsto (fun k => tr (k + t)) atTop (𝓝 xinf) :=
    hconv.comp (tendsto_add_atTop_nat t)
  refine ⟨⟨T, fun t ht => ?_⟩, tendsto_nhds_unique ?_ (hsh (T + 1))⟩
  · have hpow k : (A ^ k).mulVec (tr t) = tr (k + t) := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', ← Matrix.mulVec_mulVec, ih, ← hstep _ (by omega), Nat.succ_add]
    simpa [fvct, hadj t ht, hpow] using (hsh t).limUnder_eq
  · simpa [Function.comp_def, step, A, ← Nat.add_assoc, ← hstep _ (Nat.le_add_left T _)] using
      ((by fun_prop : Continuous A.mulVec).tendsto _).comp (hsh T)

end HK
