module
public import AnalyticESC.Dimension.Pressure
public import AnalyticESC.Main.LocalDimension

@[expose] public section
namespace AnalyticESC
open Set Metric Filter Topology MeasureTheory
namespace IFS
variable {N : ℕ} [NeZero N] (Φ : IFS N)

/-- The chain rule identifies a Birkhoff sum with the log derivative of a block. -/
private lemma birkhoff (s : ℝ) (m : ℕ) (x : Address N) :
    ∑ k ∈ Finset.range m, Φ.potential s (shift k x) = s * Real.log (Φ.weight (block m x) (Φ.natProj (shift m x))) := by
  induction m generalizing x with
  | zero => simpa [weight]
  | succ m ih =>
    let τ := shift 1 x
    have hz := Φ.pi_mem (shift m τ)
    rw [Finset.sum_range_succ']; change (∑ k ∈ Finset.range m, Φ.potential s (shift k τ)) + _ = _
    have e : block (m+1) x = [x 0] ++ block m τ := List.ofFn_succ
    rw [ih,e,show shift (m+1) x = shift m τ by rfl,Φ.weight_append _ _ hz,← Φ.natProj_eq_comp_prefix τ m,Real.log_mul (Φ.weight_pos [x 0] (Φ.pi_mem τ)).ne' (Φ.weight_pos _ hz).ne']
    change _ + s * Real.log (Φ.weight [x 0] (Φ.natProj τ)) = _
    ring

lemma exists_isGibbsMeasure (hB : BowenGibbsStatement) (s : ℝ) :
    ∃ ν : Measure (Address N), IsProbabilityMeasure ν ∧ IsGibbsMeasure (Φ.potential s) ν := by
  have hmin := Φ.cmin_pos
  have hmax := Φ.cmax_pos
  let B := max 1 (max (|s| * (-Real.log Φ.cmin)) (|s| * Φ.amp / Φ.cmax))
  have h0 : |s| * (-Real.log Φ.cmin) ≤ B := by grind
  have h1 : |s| * Φ.amp ≤ B*Φ.cmax := (div_le_iff₀ hmax).mp (by grind)
  refine hB (NeZero.pos N) _ (lt_max_of_lt_left zero_lt_one : 0 < B) hmax Φ.cmax_lt_one fun k x y h => ?_
  let X := Φ.natProj (shift 1 x)
  let Y := Φ.natProj (shift 1 y)
  change |s*Real.log (Φ.weight [x 0] X) - s*Real.log (Φ.weight [y 0] Y)| ≤ _
  rw [← mul_sub,abs_mul]
  cases k with
  | zero =>
    have bound (i : Fin N) z (hz : z ∈ I) : Real.log (Φ.weight [i] z) ∈ Icc (Real.log Φ.cmin) 0 :=
      ⟨Real.log_le_log hmin (Φ.cmin_le_norm_deriv i (Φ.closedReal hz)), Real.log_nonpos (norm_nonneg _) ((Φ.inClass i).norm_deriv_lt_one _ (Φ.closedReal hz)).le⟩
    simp only [pow_zero,mul_one]
    apply le_trans _ h0; gcongr
    grind [bound (x 0) X (Φ.pi_mem _), bound (y 0) Y (Φ.pi_mem _)]
  | succ k =>
    have d : |X-Y| ≤ Φ.cmax^k := Φ.close_prefix  (by grind)
    rw [← h 0 (by omega)]
    have hd := (Φ.distortion [x 0] (Φ.pi_mem _) (Φ.pi_mem _)).trans (mul_le_mul_of_nonneg_left d Φ.amp_nonneg)
    rw [pow_succ,mul_comm (Φ.cmax^k),← mul_assoc]
    calc _ ≤ |s| * Φ.amp * Φ.cmax^k := by rw [mul_assoc]; gcongr
      _ ≤ _ := by gcongr

/-- Summing the Gibbs bounds over all cylinders identifies the normalisation
constant `P` with the pressure. -/
private lemma normalization {S : ℕ → ℝ} {P A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hS : ∀ n, 0 < S n)
    (hs : Tendsto (fun n : ℕ => Real.log (S n) / n) atTop (𝓝 0))
    (h : ∀ n : ℕ, 1 ∈ Icc (A*Real.exp (-P*n)*S n) (B*Real.exp (-P*n)*S n)) : P = 0 := by
  apply tendsto_nhds_unique _ hs
  apply ratio_of_bounded (K := |Real.log A|+|Real.log B|)
  · simpa [tendsto_natCast_atTop_atTop]
  · apply Eventually.of_forall; intro n
    have e := log_gap hA hB (mul_pos (Real.exp_pos (-P*n)) (hS n)) (by simpa [mul_assoc] using h n)
    simp only [Real.log_one,zero_sub,abs_neg,Real.log_mul (Real.exp_pos _).ne' (hS n).ne',Real.log_exp] at e
    grind

theorem isGibbs_of_isGibbsMeasure {s : ℝ}
    (hs : Tendsto (fun n : ℕ => Real.log (Φ.pressureSum s n) / n) atTop (𝓝 0))
    {ν : Measure (Address N)} [IsProbabilityMeasure ν] (hν : IsGibbsMeasure (Φ.potential s) ν) :
    Φ.Gibbs s ν := by
  obtain ⟨a,ha,b,hb,P,G⟩ := hν
  let M := |s| * Φ.amp
  let A := a * Real.exp (-M)
  let B := b * Real.exp M
  have hA : 0 < A := by positivity
  have hB : 0 < B := by positivity
  have bounds {n} (v : Block N n) y (hy : y ∈ I) : ν.real (cyl v) ∈
      Icc (A * Real.exp (-P*n) * Φ.weight (.ofFn v) y ^ s) (B * Real.exp (-P*n) * Φ.weight (.ofFn v) y ^ s) := by
    let x (i : ℕ) := if hi : i < n then v ⟨i,hi⟩ else 0
    let z := Φ.natProj (shift n x)
    have hz := Φ.pi_mem (shift n x)
    have e : pref n x = v := by grind
    let E := -P*n + s*Real.log (Φ.weight (.ofFn v) z)
    obtain ⟨lo,hi⟩ : ν.real (cyl v) ∈ Icc (a*Real.exp E) (b*Real.exp E) := by
      dsimp only [E,z]; rw [←e,cyl_pref,← Φ.birkhoff]; exact G x n
    have d : |s*Real.log (Φ.weight (.ofFn v) z) - s*Real.log (Φ.weight (.ofFn v) y)| ≤ M := by
      rw [← mul_sub,abs_mul]; refine mul_le_mul_of_nonneg_left ((Φ.distortion _ hz hy).trans ?_) (abs_nonneg _)
      exact mul_le_of_le_one_right Φ.amp_nonneg (show |z-y| ≤ 1 by grind)
    have ex (K t : ℝ) : K * Real.exp t * Real.exp (-P*n) * Φ.weight (.ofFn v) y ^ s =
        K * Real.exp (-P*n + s*Real.log (Φ.weight (.ofFn v) y) + t) := by
      rw [Real.rpow_def_of_pos (Φ.weight_pos _ hy),mul_comm s,Real.exp_add,Real.exp_add]; ring
    obtain ⟨d₁,d₂⟩ := abs_le.mp d
    refine ⟨le_trans ?_ lo,hi.trans ?_⟩ <;> rw [ex] <;> apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity) <;> dsimp only [E] <;> linarith
  have H (n : ℕ) : 1 ∈ Icc (A*Real.exp (-P*n)*Φ.pressureSum s n) (B*Real.exp (-P*n)*Φ.pressureSum s n) := by
    choose z hz he using Φ.supDeriv_attained
    have h (v : Block N n) := he (.ofFn v) ▸ bounds v _ (hz _)
    simpa [sum_cyl,pressureSum,← Finset.mul_sum] using sum_bounds (S := Finset.univ) fun v _ => h v
  obtain rfl := normalization hA hB (Φ.pressureSum_pos s) hs H
  exact ⟨A,hA,B,hB,fun v x hx => by simpa using bounds v x hx⟩

end IFS

/-- At the pressure zero the Bowen estimates reduce to uniform cylinder estimates. -/
theorem example_gibbs (hB : BowenGibbsStatement) : ∃ s, exampleIFS.UniqueRoot s ∧
    (∃ ν : Measure (Address 3), IsProbabilityMeasure ν ∧ IsGibbsMeasure (exampleIFS.potential s) ν) ∧
    ∀ ν, IsProbabilityMeasure ν → IsGibbsMeasure (exampleIFS.potential s) ν → exampleIFS.Gibbs s ν := by
  obtain ⟨s, -, hs⟩ := exampleIFS.exists_pressure_zero
  exact ⟨s,hs,exampleIFS.exists_isGibbsMeasure hB s,fun ν _ =>
    exampleIFS.isGibbs_of_isGibbsMeasure ((exampleIFS.ratio_limit _).mp ((hs s).2 rfl))⟩

end AnalyticESC
