module

public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# Strongly continuous semigroups (Proposition 1.2)

* `C0Semigroup 𝕜 X` : strongly continuous semigroups `T` on `X` (first item of
  Definition 1.1): `T 0 = Id`, `T (t + s) = T t ∘ T s` for `t, s ≥ 0`, and `T t y → y`
  as `t → 0⁺` for every `y`.
* `C0Semigroup.exists_exp_bound` : `‖T t‖ ≤ M exp(ω t)` for `t ≥ 0`
  ([Pazy 1983, Chapter 1, Theorem 2.2], used in the proofs of Theorem 1.5 and
  Proposition 1.3); proved with the Banach–Steinhaus theorem.
* `C0Semigroup.continuousOn_orbit` : **Proposition 1.2**
  (`prop:pazy-semigroup-solution-continuous`), `t ↦ T t x°` is continuous on `ℝ₊`.

`T` is a function `ℝ → (X →L[𝕜] X)`; all axioms only involve nonnegative times, so the
values of `T t` for `t < 0` play no role. Completeness of `X` is assumed where needed.
-/

open Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- A strongly continuous semigroup on `X` (first item of Definition 1.1). -/
structure C0Semigroup (𝕜 : Type*) (X : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] where
  /-- the operators `T t` -/
  T : ℝ → X →L[𝕜] X
  /-- `T 0 = Id` -/
  T_zero : T 0 = ContinuousLinearMap.id 𝕜 X
  /-- `T (t + s) = T t ∘ T s` for `t, s ≥ 0` -/
  T_add : ∀ t s : ℝ, 0 ≤ t → 0 ≤ s → T (t + s) = (T t).comp (T s)
  /-- `T t y → y` as `t → 0⁺`, for every `y` -/
  T_cont : ∀ y : X, Tendsto (fun t => T t y) (nhdsWithin 0 (Set.Ici 0)) (𝓝 y)

namespace C0Semigroup

variable (S : C0Semigroup 𝕜 X)

/-! ## Exponential bound -/

/-- Banach–Steinhaus along a nonnegative null sequence. -/
theorem exists_bound_of_tendsto_zero [CompleteSpace X] (t : ℕ → ℝ)
    (ht0 : ∀ n, 0 ≤ t n) (ht : Tendsto t atTop (𝓝 0)) : ∃ C, ∀ n, ‖S.T (t n)‖ ≤ C := by
  have ht' : Tendsto t atTop (nhdsWithin 0 (Set.Ici 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨ht, .of_forall ht0⟩
  apply banach_steinhaus
  intro x
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1
    (Metric.isBounded_range_of_tendsto _ ((S.T_cont x).comp ht'))
  exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩

/-- First step: `‖T t‖ ≤ M` on some interval `[0, τ]` (Banach–Steinhaus). -/
theorem exists_bound_near_zero [CompleteSpace X] :
    ∃ τ > 0, ∃ M ≥ 1, ∀ t, 0 ≤ t → t ≤ τ → ‖S.T t‖ ≤ M := by
  by_contra h
  have key (n : ℕ) : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 / (n + 1) ∧ n + 1 < ‖S.T t‖ := by
    by_contra! hn
    exact h ⟨1 / (n + 1), by positivity, n + 1, le_add_of_nonneg_left (by positivity), hn⟩
  choose t ht0 htle htbig using key
  obtain ⟨C, hC⟩ := S.exists_bound_of_tendsto_zero t ht0
    (squeeze_zero ht0 htle tendsto_one_div_add_atTop_nhds_zero_nat)
  obtain ⟨n, hn⟩ := exists_nat_gt C
  linarith [hC n, htbig n]

/-- A uniform norm bound on every finite interval. -/
theorem exists_bound_upto [CompleteSpace X] (b : ℝ) :
    ∃ K > 0, ∀ t, 0 ≤ t → t ≤ b → ‖S.T t‖ ≤ K := by
  obtain ⟨τ, hτ, M, hM, hbound⟩ := S.exists_bound_near_zero
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hpow (k : ℕ) : ‖S.T (k * τ)‖ ≤ M ^ k := by
    induction k with
    | zero =>
      rw [Nat.cast_zero, zero_mul, S.T_zero, pow_zero]
      exact ContinuousLinearMap.norm_id_le
    | succ k ih =>
      rw [Nat.cast_succ, add_mul, one_mul,
        S.T_add _ _ (mul_nonneg (Nat.cast_nonneg _) hτ.le) hτ.le, pow_succ]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul ih (hbound τ hτ.le le_rfl) (norm_nonneg _) (pow_nonneg hM0.le k))
  refine ⟨M ^ (⌊b / τ⌋₊ + 1), pow_pos hM0 _, fun t ht htb => ?_⟩
  let k := ⌊t / τ⌋₊
  have hk : (k : ℝ) ≤ t / τ := Nat.floor_le (div_nonneg ht hτ.le)
  have hkt : t / τ < k + 1 := Nat.lt_floor_add_one _
  have h1 : (k : ℝ) * τ ≤ t := (le_div_iff₀ hτ).1 hk
  have h2 : t < (k + 1) * τ := (div_lt_iff₀ hτ).1 hkt
  calc
    ‖S.T t‖ ≤ M ^ k * M := by
      rw [← show (k : ℝ) * τ + (t - k * τ) = t by ring,
        S.T_add _ _ (mul_nonneg (Nat.cast_nonneg _) hτ.le) (by linarith)]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (hpow k) (hbound _ (by linarith) (by linarith)) (norm_nonneg _)
          (pow_nonneg hM0.le k))
    _ = M ^ (k + 1) := (pow_succ _ _).symm
    _ ≤ M ^ (⌊b / τ⌋₊ + 1) := pow_le_pow_right₀ hM <| Nat.succ_le_succ <|
      Nat.floor_mono (div_le_div_of_nonneg_right htb hτ.le)

/-! ## Proposition 1.2: continuity of the orbits -/

/-- **Proposition 1.2** (`prop:pazy-semigroup-solution-continuous`). -/
theorem continuousOn_orbit [CompleteSpace X] (y : X) :
    ContinuousOn (fun t => S.T t y) (Set.Ici 0) := by
  rw [Metric.continuousOn_iff]
  intro t₀ ht₀ ε hε
  obtain ⟨K, hK0, hK⟩ := S.exists_bound_upto t₀
  obtain ⟨δ, hδ, hc⟩ := Metric.tendsto_nhdsWithin_nhds.1 (S.T_cont y) (ε / K) (by positivity)
  have key (a h : ℝ) (ha : 0 ≤ a) (hat : a ≤ t₀) (hh : 0 ≤ h) (hhδ : h < δ) :
      ‖S.T (a + h) y - S.T a y‖ < ε := by
    have h1 : ‖S.T h y - y‖ < ε / K := by
      rw [← dist_eq_norm]
      exact hc hh (by simpa [Real.dist_eq, abs_of_nonneg hh] using hhδ)
    calc
      _ ≤ K * ‖S.T h y - y‖ := by
        rw [S.T_add a h ha hh, ContinuousLinearMap.comp_apply, ← map_sub]
        exact (S.T a).le_of_opNorm_le (hK a ha hat) _
      _ < ε := by rw [mul_comm]; exact (lt_div_iff₀ hK0).1 h1
  refine ⟨δ, hδ, fun t ht hd => ?_⟩
  rw [Real.dist_eq] at hd
  obtain ⟨hd1, hd2⟩ := abs_lt.1 hd
  rw [dist_eq_norm]
  rcases le_total t₀ t with htt | htt
  · have h := key t₀ (t - t₀) ht₀ le_rfl (by linarith) (by linarith)
    rwa [show t₀ + (t - t₀) = t by ring] at h
  · have h := key t (t₀ - t) ht htt (by linarith) (by linarith)
    rwa [show t + (t₀ - t) = t₀ by ring, norm_sub_rev] at h

end C0Semigroup
