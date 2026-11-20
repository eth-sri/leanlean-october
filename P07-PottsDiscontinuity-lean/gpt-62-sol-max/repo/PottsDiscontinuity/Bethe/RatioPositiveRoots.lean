module

public import PottsDiscontinuity.Bethe.CountingAlignment

/-! The counting function quantizes the positive-root ranks. Its uniform derivative
bounds give both the spacing estimates and the central scaling of those ranks. -/

@[expose] public section

open Set Filter
open scoped Topology

namespace PottsDiscontinuity.Bethe

local notation "J" => Icc (-Real.pi) Real.pi

/-- The positive half of the full symmetric root tuple. -/
noncomputable def ratioPositiveRoot (N : ℕ) (h4 : 4 ∣ N) (p : Fin (N / 2) → ℝ)
    (j : Fin (N / 4)) : ℝ := p ⟨N / 4 + j.val, by omega⟩

theorem ratio_positiveRoot_pos {N : ℕ} (h4 : 4 ∣ N) {p : Fin (N / 2) → ℝ}
    (hp : p ∈ S_n (N / 2)) (j : Fin (N / 4)) : 0 < ratioPositiveRoot N h4 p j := by
  let i : Fin (N / 2) := ⟨N / 4 + j.val, by omega⟩
  have h := hp.2.1 (show Fin.rev i < i by grind)
  rw [hp.2.2 i] at h
  aesop

/-- The full-root family with the asymptotic estimates for its counting derivative. -/
structure FullRoots (Δ : ℝ) (N : ℕ → ℕ) (p : ∀ i, Fin (N i / 2) → ℝ) where
  hΔ : Δ < -1
  four : ∀ i, 4 ∣ N i
  pos : ∀ i, 0 < N i
  mem : ∀ i, p i ∈ S_n (N i / 2)
  bethe : ∀ i, DiscreteBetheEquation Δ (N i) (N i / 2) (p i)
  widthLimit : Tendsto (fun i => (N i : ℝ)) atTop atTop
  m : ℝ
  U : ℝ
  E : ℝ
  mpos : 0 < m
  bounds : ∀ᶠ i in atTop, ∀ x ∈ J,
    m ≤ betheCountingDerivative Δ (N i) (N i / 2) (p i) x ∧
    betheCountingDerivative Δ (N i) (N i / 2) (p i) x ≤ U
  approx : ∀ᶠ i in atTop, ∀ x ∈ J,
    |betheCountingDerivative Δ (N i) (N i / 2) (p i) x - rho Δ x| ≤ E / N i

namespace FullRoots

variable {Δ : ℝ} {N : ℕ → ℕ} {p : ∀ i, Fin (N i / 2) → ℝ} (R : FullRoots Δ N p)

local notation "F[" i "]" => betheCountingFunction Δ (N i) (N i / 2) (p i)
local notation "D[" i "]" => betheCountingDerivative Δ (N i) (N i / 2) (p i)

/-- Missing ranks in the finite initial segment may be filled by any value in `(0,π)`. -/
noncomputable def rank (k i : ℕ) : ℝ :=
  if h : k < N i / 4 then ratioPositiveRoot (N i) (R.four i) (p i) ⟨k, h⟩ else Real.pi / 2

theorem rank_eq {k i : ℕ} (h : k < N i / 4) :
    R.rank k i = ratioPositiveRoot (N i) (R.four i) (p i) ⟨k, h⟩ := dite_eq_left h

theorem rank_mem (k i : ℕ) : R.rank k i ∈ Ioo (-Real.pi) Real.pi := by
  unfold rank
  split_ifs
  · exact (R.mem i).1 _
  · constructor <;> linarith [Real.pi_pos]

theorem rank_pos (k i : ℕ) : 0 < R.rank k i := by
  unfold rank
  split_ifs
  · exact ratio_positiveRoot_pos (R.four i) (R.mem i) _
  · positivity

private theorem root_value {k i : ℕ} (hk : k < N i / 4) :
    F[i] (R.rank k i) = ((k : ℝ) + 1 / 2) / N i := by
  rw [R.rank_eq hk, ratioPositiveRoot, betheCountingFunction_root_value (R.pos i) (p i) (R.bethe i)]
  congr 1
  have h : N i / 2 = 2 * (N i / 4) := by obtain ⟨w, hw⟩ := R.four i; omega
  simp [discreteBetheIndex, h]
  ring

private theorem root_mean (k i : ℕ) : ∃ t ∈ Icc 0 (R.rank k i),
    F[i] (R.rank k i) = D[i] t * R.rank k i := by
  obtain ⟨t, ht, he⟩ := exists_mean_deriv (hasDerivAt_betheCountingFunction R.hΔ (N i) _ (p i)) 0 (R.rank k i)
  exact ⟨t, by rwa [uIcc_of_le (R.rank_pos k i).le] at ht, by simpa [betheCountingFunction_zero (R.mem i)] using he⟩

private theorem mean_mem {k i : ℕ} {t : ℝ} (ht : t ∈ Icc 0 (R.rank k i)) : t ∈ J :=
  ⟨(neg_nonpos.mpr Real.pi_pos.le).trans ht.1, ht.2.trans (R.rank_mem k i).2.le⟩

theorem rank_lower {i k : ℕ} (h : k < N i / 4) (hu : ∀ x ∈ J, D[i] x ≤ R.U) :
    (k : ℝ) + 1 / 2 ≤ (R.U * N i) * R.rank k i := by
  obtain ⟨t, ht, he⟩ := R.root_mean k i
  rw [R.root_value h, div_eq_iff ((Nat.cast_pos.mpr (R.pos i) : (0 : ℝ) < N i).ne')] at he
  rw [he]
  nlinarith only [mul_le_mul_of_nonneg_right (hu t (R.mean_mem ht))
    (mul_nonneg (R.rank_pos k i).le (Nat.cast_nonneg (α := ℝ) (N i)))]

theorem rank_gap {i k : ℕ} (h : k + 1 < N i / 4) (hl : ∀ x ∈ J, R.m ≤ D[i] x) :
    R.rank (k + 1) i - R.rank k i ≤ (1 / R.m) / N i := by
  have hk : k < N i / 4 := by omega
  have hxy : R.rank k i ≤ R.rank (k + 1) i := by
    rw [R.rank_eq hk, R.rank_eq h]
    exact (R.mem i).2.1.monotone (by change N i / 4 + k ≤ N i / 4 + (k + 1); omega)
  have hl' := counting_length_le R.mpos (hasDerivAt_betheCountingFunction R.hΔ (N i) _ (p i)) hl
    (Ioo_subset_Icc_self (R.rank_mem k i)) (Ioo_subset_Icc_self (R.rank_mem (k + 1) i)) hxy
  convert hl' using 1
  rw [R.root_value h, R.root_value hk]
  push_cast
  ring

include R in
theorem eventually_rank_exists (k : ℕ) : ∀ᶠ i in atTop, k < N i / 4 := by
  filter_upwards [R.widthLimit.eventually (eventually_ge_atTop (((4 * (k + 1) : ℕ) : ℝ)))] with i hi
  have : 4 * (k + 1) ≤ N i := by exact_mod_cast hi
  omega

/-- The central scale comes from the exact value of the counting function at a root. -/
theorem rank_limits (k : ℕ) : Tendsto (R.rank k) atTop (𝓝 0) ∧
    Tendsto (fun i => (N i : ℝ) * R.rank k i) atTop (𝓝 (((k : ℝ) + 1 / 2) / rho Δ 0)) := by
  classical
  choose t hmem hmean using R.root_mean k
  have hj (i : ℕ) := R.mean_mem (hmem i)
  have hN (i : ℕ) : (0 : ℝ) < N i := Nat.cast_pos.mpr (R.pos i)
  have he := (R.eventually_rank_exists k).mono fun i hi => (R.root_value hi).symm.trans (hmean i)
  have hx : Tendsto (R.rank k) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun i => (R.rank_pos k i).le) ?_
      (tendsto_const_nhds.div_atTop R.widthLimit :
        Tendsto (fun i => (((k : ℝ) + 1 / 2) / R.m) / N i) atTop (𝓝 0))
    filter_upwards [he, R.bounds] with i hi hb
    rw [div_div, le_div_iff₀ (mul_pos R.mpos (hN i))]
    have hh := mul_le_mul_of_nonneg_right ((hb _ (hj i)).1) (R.rank_pos k i).le
    rw [← hi] at hh
    nlinarith only [mul_le_mul_of_nonneg_right hh (hN i).le, div_mul_cancel₀ ((k : ℝ) + 1 / 2) (hN i).ne']
  have ht := squeeze_zero (fun i => (hmem i).1) (fun i => (hmem i).2) hx
  have hDρ := (continuous_rho R.hΔ).continuousAt.tendsto.comp ht
  have hD₀ : Tendsto (fun i => D[i] (t i) - rho Δ (t i)) atTop (𝓝 0) :=
    squeeze_zero_norm' (R.approx.mono fun i hi => by
      simpa using hi (t i) (hj i)) (tendsto_const_nhds.div_atTop R.widthLimit)
  have hD : Tendsto (fun i => D[i] (t i)) atTop (𝓝 (rho Δ 0)) := by
    simpa using hD₀.add hDρ
  refine ⟨hx, (tendsto_const_nhds.div hD (rho_pos R.hΔ 0).ne').congr' ?_⟩
  filter_upwards [he, R.bounds] with i hi hb
  have hd := R.mpos.trans_le (hb (t i) (hj i)).1
  change ((k : ℝ) + 1 / 2) / D[i] (t i) = (N i : ℝ) * R.rank k i
  rw [div_eq_iff hd.ne']
  rw [div_eq_iff (hN i).ne'] at hi
  linear_combination hi

end FullRoots

end PottsDiscontinuity.Bethe
