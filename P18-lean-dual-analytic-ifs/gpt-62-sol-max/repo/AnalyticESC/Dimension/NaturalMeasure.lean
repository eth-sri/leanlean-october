module

public import AnalyticESC.Dimension.Pressure

@[expose] public section

/-!
# The natural measure

From Bowen's theorem (`BowenGibbsStatement`), the potential `s log|f'_{ω₀}(π(σω))|` has a Gibbs
measure `ν`. When `s = s(Φ)`, `ν` has the Gibbs property `ν[w] ≍ ‖f_w'‖^s` of `IFS.IsGibbs`, so the
results of `Main.LocalDimension` apply to the natural measure `ν ∘ π⁻¹`.
-/

namespace AnalyticESC

open Set Metric Filter Topology MeasureTheory
open Word (pref shift)

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- The Birkhoff sum of the potential: `∑_{k<m} φ_s(σ^k x) = s log |f_w'(π(σ^m x))|` with
`w = x₀ ⋯ x_{m-1}`. -/
private theorem nm_birkhoff (s : ℝ) (m : ℕ) (x : ℕ → Fin N) :
    ∑ k ∈ Finset.range m, Φ.potential s (fun i => x (i + k)) =
      s * Real.log ‖deriv (Φ.comp (pref x m))
        (Φ.natProj (shift x m))‖ := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    let y := shift x 1
    have hz := Φ.real_mem_closed (Φ.natProj_mem_I (shift y m))
    rw [Finset.sum_range_succ']
    change (∑ k ∈ Finset.range m, Φ.potential s (fun i => y (i + k))) +
        s * Real.log ‖deriv (Φ.f (x 0)) (Φ.natProj y)‖ =
      s * Real.log ‖deriv (Φ.comp (pref x (m+1))) (Φ.natProj (shift y m))‖
    rw [ih, Word.pref_succ, Φ.deriv_comp_cons _ _ hz,
      Φ.comp_ofReal _ (Φ.natProj_mem_I _), ← Φ.natProj_eq_comp_prefix y m, norm_mul,
      Real.log_mul (norm_ne_zero_iff.2 ((Φ.inClass _).deriv_ne_zero _
        (Φ.real_mem_closed (Φ.natProj_mem_I y))))
        (norm_ne_zero_iff.2 (Φ.deriv_comp_ne_zero _ hz)), mul_add, add_comm]

/-- At the pressure zero Bowen's existence theorem gives symbolic Gibbs measures, and
all of them satisfy the cylinder estimates used for the natural measure. -/
theorem gibbs_at_pressure_zero (hB : BowenGibbsStatement) (hN : 0 < N) :
    ∃ s : ℝ, 0 ≤ s ∧ Challenge.IsUniquePressureZero Φ.f s ∧
      (∃ ν : Measure (ℕ → Fin N), IsProbabilityMeasure ν ∧ IsGibbsMeasure (Φ.potential s) ν) ∧
      ∀ ν : Measure (ℕ → Fin N), IsProbabilityMeasure ν →
        IsGibbsMeasure (Φ.potential s) ν → Φ.IsGibbs s ν := by
  obtain ⟨s, hs₀, hs⟩ := Φ.exists_pressure_zero hN
  refine ⟨s, hs₀, hs, ?_, ?_⟩
  · -- The potential has exponentially decaying variations.
    obtain ⟨D, hD, hLip⟩ := Φ.exists_logNormDeriv_lip
    have hc := Φ.cmax_pos hN
    let B := max (|s| * D / Φ.cmax) (|s| * (-Real.log Φ.cmin)) + 1
    have h₁ : |s| * D / Φ.cmax ≤ B := by grind
    have h₂ : |s| * (-Real.log Φ.cmin) ≤ B := by grind
    have hB₀ : 0 < B := by positivity
    refine hB hN (Φ.potential s) hB₀ hc Φ.cmax_lt_one fun k x y hxy => ?_
    let x' := shift x 1
    let y' := shift y 1
    change |s * Φ.logNormDeriv [x 0] (Φ.natProj x') - s * Φ.logNormDeriv [y 0] (Φ.natProj y')| ≤ B * Φ.cmax ^ k
    rw [← mul_sub, abs_mul]
    cases k with
    | zero =>
      have hbd (i : Fin N) (t : ℝ) (ht : t ∈ I) :
          Real.log Φ.cmin ≤ Φ.logNormDeriv [i] t ∧ Φ.logNormDeriv [i] t ≤ 0 := by
        have hz := Φ.real_mem_closed ht
        exact ⟨Real.log_le_log (Φ.cmin_pos hN) (Φ.cmin_le_norm_deriv i hz),
          Real.log_nonpos (norm_nonneg _) ((Φ.inClass i).norm_deriv_lt_one _ hz).le⟩
      have he := hbd (x 0) _ (Φ.natProj_mem_I x')
      have hf := hbd (y 0) _ (Φ.natProj_mem_I y')
      rw [pow_zero, mul_one]
      apply le_trans _ h₂
      gcongr
      grind
    | succ k =>
      rw [hxy 0 (Nat.succ_pos k)]
      have he := (hLip [y 0] _ (Φ.natProj_mem_I x') _ (Φ.natProj_mem_I y')).trans
        (mul_le_mul_of_nonneg_left (Φ.abs_natProj_sub_le_of_prefix (x := x') (y := y') (n := k) (by bound)) hD)
      refine (mul_le_mul_of_nonneg_left he (abs_nonneg s)).trans ?_
      simpa only [pow_succ', mul_assoc] using
        mul_le_mul_of_nonneg_right ((div_le_iff₀ hc).1 h₁) (pow_nonneg hc.le k)
  · -- At the pressure zero the symbolic Gibbs bounds are uniform cylinder estimates.
    intro ν hν₀ hν
    let := hν₀
    have hs := (hs s).2 rfl
    obtain ⟨c₁, hc₁, c₂, hc₂, P, hG⟩ := hν
    obtain ⟨R, hR, hΔ⟩ := Φ.exists_distortion
    let K := c₁ / R ^ s
    have hK : 0 < K := by positivity
    let e (n : ℕ) := Real.exp (P * n)
    have he n : 0 < e n := Real.exp_pos _
    have key (n : ℕ) (v : Fin n → Fin N) :
        K * Φ.supDeriv (List.ofFn v) ^ s ≤ e n * ν.real (wordCylinder v) ∧
          e n * ν.real (wordCylinder v) ≤ c₂ * Φ.supDeriv (List.ofFn v) ^ s := by
      let x (i : ℕ) := if hi : i < n then v ⟨i, hi⟩ else ⟨0, hN⟩
      have hx : (fun j : Fin n => x j) = v := funext fun j => dite_eq_left j.isLt
      let y := Φ.natProj (shift x n)
      have hy : y ∈ I := Φ.natProj_mem_I _
      have hC : {y | ∀ i < n, y i = x i} = wordCylinder v := by
        rw [← hx]
        ext y
        simp [wordCylinder, funext_iff, Fin.forall_iff]
      have h := hG x n
      rw [hC, Φ.nm_birkhoff, show pref x n = List.ofFn v from congrArg List.ofFn hx,
        neg_mul, neg_add_eq_sub, Real.exp_sub, mul_comm s, ← Real.rpow_def_of_pos (norm_pos_iff.2 (Φ.deriv_comp_ne_zero (List.ofFn v) (Φ.real_mem_closed hy))), ← mul_div_assoc, ← mul_div_assoc] at h
      obtain ⟨hl, hu⟩ := hΔ (List.ofFn v) y hy s hs₀
      rw [mul_comm (e n)]
      refine ⟨?_, ((le_div_iff₀ (he n)).1 h.2).trans (mul_le_mul_of_nonneg_left hl hc₂.le)⟩
      refine le_trans ?_ ((div_le_iff₀ (he n)).1 h.1)
      dsimp [K]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < R ^ s), mul_assoc, mul_comm _ (R ^ s)]
      simp_all
    have hlog (n : ℕ) : P * n - Real.log (Φ.pressureSum s n) ∈ Icc (Real.log K) (Real.log c₂) := by
      have h := sum_mul_bounds Finset.univ (fun v _ => key n v)
      simp [← Finset.mul_sum, sum_measureReal_wordCylinder] at h
      simpa only [e, Real.log_exp] using
        log_sub_mem_Icc_of_mul_bounds (Φ.pressureSum_pos hN s n) hK hc₂ h
    have hlim := tendsto_bdd_div_atTop_nhds_zero (.of_forall fun n => (hlog (n+1)).1)
      (.of_forall fun n => (hlog (n+1)).2) (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    have hlim' := hlim.congr (f₂ := fun n => P - Φ.pressureRate s n) fun n => by
      simp [Challenge.pressureRatio, divide, sub_div, show (n : ℝ)+1 ≠ 0 by positivity]
    have hP : P = 0 := by simpa using tendsto_nhds_unique (hs.const_sub P) hlim'
    exact ⟨K, hK, c₂, hc₂, fun n v => by simpa [e, hP] using key n v⟩

end IFS

end AnalyticESC

namespace Challenge

open AnalyticESC Set Metric Filter Topology MeasureTheory

/-- The natural measure of the polynomial example in Section 1.2.2, from Bowen's theorem:
the pressure has a unique zero `s = s(Φ)`, the potential `s log|f'_{ω₀}(π(σω))|` has a Gibbs measure,
and for every such Gibbs measure `ν` the natural measure `μ = ν ∘ π⁻¹` has local dimension `s(Φ) - 1/3 < s(Φ)`
at `0`. -/
theorem audit_example_localDim (hB : BowenGibbsStatement) :
    ∃ s : ℝ,
      (∀ t, Tendsto (pressureRatio exampleMaps t) atTop (𝓝 0) ↔ t = s) ∧
      (∃ ν : Measure (ℕ → Fin 3), IsProbabilityMeasure ν ∧
        IsGibbsMeasure (potential exampleMaps s) ν) ∧
      ∀ ν : Measure (ℕ → Fin 3), IsProbabilityMeasure ν →
        IsGibbsMeasure (potential exampleMaps s) ν →
        Tendsto (fun r : Scale => logRatio ((ν.map (natProj exampleMaps)).real (closedBall 0 r)) r)
          scaleZero (𝓝 (s - 1 / 3)) := by
  obtain ⟨s, hs₀, hs, hG, h⟩ := exampleIFS.gibbs_at_pressure_zero hB (by norm_num)
  exact ⟨s, hs, hG, fun ν hν hGν => (scale_tendsto_iff _ _).2 (by simpa only [one_mul] using (example_localDim hs₀ (h ν hν hGν)).2 1 (by norm_num))⟩

end Challenge
