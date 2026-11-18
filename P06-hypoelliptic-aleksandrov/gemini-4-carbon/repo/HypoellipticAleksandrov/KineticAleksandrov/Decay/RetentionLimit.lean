module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceNotation
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonRadial
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
public import HypoellipticAleksandrov.Ambient.MatrixContraction
import Mathlib.Tactic.Ring
public import HypoellipticAleksandrov.Parabolic.KineticClassical
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MaxPrinciple
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierGeometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set Filter HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Matrix MeasureTheory HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped Topology MatrixOrder BigOperators


private def positivePower (N : ℕ) (x : ℝ) : ℝ := (max x 0) ^ N

private theorem positivePower_derivative {N : ℕ} (hN : 2 ≤ N) (x : ℝ) :
    HasDerivAt (positivePower N) ((N : ℝ) * positivePower (N - 1) x) x := by
  have hNm : N - 1 ≠ 0 := by omega
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have heq : positivePower N =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [gt_mem_nhds hx] with y hy
      simp [positivePower, max_eq_right hy.le, show N ≠ 0 by omega]
    have hd := (hasDerivAt_const x 0).congr_of_eventuallyEq heq
    simpa [positivePower, max_eq_right hx.le, hNm] using hd
  · have hp : HasDerivWithinAt (positivePower N) 0 (Ici 0) 0 := by
      have hd0 : HasDerivWithinAt (fun x : ℝ => x ^ N) 0 (Ici 0) 0 := by
        simpa [Pi.pow_apply, zero_pow hNm] using ((hasDerivAt_id (0 : ℝ)).fun_pow N).hasDerivWithinAt (s := Ici 0)
      exact hd0.congr (fun y hy => by simp [positivePower, max_eq_left hy])
        (by simp [positivePower])
    have hn : HasDerivWithinAt (positivePower N) 0 (Iic 0) 0 :=
      (hasDerivAt_const 0 0).hasDerivWithinAt.congr
        (fun y hy => by simp [positivePower, max_eq_right hy, show N ≠ 0 by omega])
        (by simp [positivePower, show N ≠ 0 by omega])
    have hu := hp.union hn
    rw [Ici_union_Iic] at hu
    simpa [positivePower, hNm] using hasDerivWithinAt_univ.mp hu
  · have heq : positivePower N =ᶠ[𝓝 x] fun y => y ^ N := by
      filter_upwards [lt_mem_nhds hx] with y hy
      simp [positivePower, max_eq_left hy.le]
    simpa [positivePower, max_eq_left hx.le] using
      ((hasDerivAt_id x).pow N).congr_of_eventuallyEq heq




private theorem positivePower_contDiff_two {N : ℕ} (hN : 3 ≤ N) :
    ContDiff ℝ 2 (positivePower N)   := by
  have positivePower_deriv {N : ℕ} (hN : 2 ≤ N) :
      deriv (positivePower N) = fun x => (N : ℝ) * positivePower (N - 1) x := by
    funext x
    exact (positivePower_derivative hN x).deriv
  have positivePower_contDiff_one {N : ℕ} (hN : 2 ≤ N) :
      ContDiff ℝ 1 (positivePower N) := by
    have positivePower_continuous (N : ℕ) :
        Continuous (positivePower N) := by
      unfold positivePower
      exact (continuous_id.max continuous_const).pow N
    rw [contDiff_one_iff_deriv, positivePower_deriv hN]
    exact ⟨fun x => (positivePower_derivative hN x).differentiableAt,
      continuous_const.mul (positivePower_continuous _)⟩
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x => (positivePower_derivative (by omega) x).differentiableAt, ?_, ?_⟩
  · norm_num
  · rw [positivePower_deriv (by omega)]
    exact contDiff_const.mul (positivePower_contDiff_one (by omega))


/-- A source-admissible integer gives a strictly positive barrier constant. -/
theorem exists_retention_barrier_order (d : ℕ) (hd : 1 ≤ d)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) :
    ∃ N : ℕ, 3 ≤ N ∧ 2 * (N - 1 : ℕ) * lam > (d : ℝ) * Lam ∧
      0 < barrierC d N lam Lam := by
  have _hlamLam := hlamLam
  obtain ⟨n, hn⟩ := exists_nat_gt (max 3 ((d : ℝ) * Lam / (2 * lam)))
  have hineq :=
    (div_lt_iff₀ (by positivity)).mp ((le_max_right _ _).trans_lt hn)
  refine ⟨n + 1, ?_, ?_, ?_⟩
  · have : 3 < n := by exact_mod_cast ((le_max_left _ _).trans_lt hn)
    omega
  · simpa using (by nlinarith :
      2 * (n : ℝ) * lam > (d : ℝ) * Lam)
  · unfold barrierC
    simp
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    nlinarith [mul_pos hpos (show 0 < 2 * (n : ℝ) * lam - (d : ℝ) * Lam by linarith)]

/-- The positive-part polynomial barrier is globally twice continuously differentiable. -/
theorem retention_barrier_contDiff {d N : ℕ} (hN : 3 ≤ N) (s : ℝ) :
    ContDiff ℝ 2 (barrier (d := d) N s) := by
  have hw : ContDiff ℝ 2 (fun Y : PDE.Vec d => 1 - PDE.vecNormSq Y / s ^ 2) :=
    contDiff_const.sub (PDE.contDiff_vecNormSq.of_le (by norm_num) |>.div_const _)
  exact (positivePower_contDiff_two hN).comp hw


private def radialProfile (N : ℕ) (s r : ℝ) : ℝ := positivePower N (1 - r / s ^ 2)

private theorem radialProfile_derivative {N : ℕ} (hN : 2 ≤ N) (s r : ℝ) :
    HasDerivAt (radialProfile N s)
      (-((N : ℝ) / s ^ 2) * positivePower (N - 1) (1 - r / s ^ 2)) r := by
  have h := (positivePower_derivative hN (1 - r / s ^ 2)).comp r (((hasDerivAt_id r).div_const (s ^ 2)).const_sub 1)
  exact h.congr_deriv (by ring)






/-- The source retention polynomial, including its boundary jets. -/
theorem retention_polynomial_barrier {d N : ℕ} (hN : 3 ≤ N)
    (s : ℝ) (hs : 0 < s) :
    ContDiff ℝ 2 (barrier (d := d) N s) ∧
    (∀ Y : PDE.Vec d, 0 ≤ barrier N s Y ∧ barrier N s Y ≤ 1) ∧ barrier (d := d) N s 0 = 1 ∧
    (∀ Y : PDE.Vec d, Y ∈ PDE.euclideanBall 0 s →
      PDE.classicalGradient (barrier N s) Y =
        (-2 * N / s ^ 2 * (1 - PDE.vecNormSq Y / s ^ 2) ^ (N - 1)) • Y ∧
      Hess (barrier N s) Y =
        (-2 * N / s ^ 2 * (1 - PDE.vecNormSq Y / s ^ 2) ^ (N - 1)) • (1 : PDE.Mat d) +
        ((4 * N * (N - 1 : ℕ) / s ^ 4 *
          (1 - PDE.vecNormSq Y / s ^ 2) ^ (N - 2)) •
            Matrix.of (fun i j => Y i * Y j) : PDE.Mat d)) ∧
    (∀ Y : PDE.Vec d, Y ∉ PDE.euclideanBall 0 s →
      barrier N s Y = 0 ∧ PDE.classicalGradient (barrier N s) Y = 0 ∧
        Hess (barrier N s) Y = 0)    := by
  have radialProfile_deriv {N : ℕ} (hN : 2 ≤ N) (s : ℝ) :
      deriv (radialProfile N s) =
      fun r => -((N : ℝ) / s ^ 2) * positivePower (N - 1) (1 - r / s ^ 2) := by
    funext r
    exact (radialProfile_derivative hN s r).deriv
  have retention_barrier_hessian {d : ℕ} (Y : PDE.Vec d) :
      Hess (barrier N s) Y =
      (-2 * N / s ^ 2 * (max (1 - PDE.vecNormSq Y / s ^ 2) 0) ^ (N - 1)) • 1 +
      ((4 * N * (N - 1 : ℕ) / s ^ 4 *
        (max (1 - PDE.vecNormSq Y / s ^ 2) 0) ^ (N - 2)) •
          Matrix.of (fun i j => Y i * Y j) : PDE.Mat d) := by
    have radialProfile_contDiff : ContDiff ℝ 2 (radialProfile N s) :=
      (positivePower_contDiff_two hN).comp
          (contDiff_const.sub (contDiff_id.div_const _))
    have radialProfile_second_deriv (s : ℝ) (r : ℝ) :
        deriv (deriv (radialProfile N s)) r =
        ((N : ℝ) / s ^ 2) * ((N - 1 : ℕ) / s ^ 2) *
          positivePower (N - 2) (1 - r / s ^ 2) := by
      rw [radialProfile_deriv (by omega)]
      have h := (radialProfile_derivative (N := N - 1) (by omega) s r).const_mul
        (-((N : ℝ) / s ^ 2))
      have heq : (fun r => -((N : ℝ) / s ^ 2) *
          positivePower (N - 1) (1 - r / s ^ 2)) =
          (fun r => -((N : ℝ) / s ^ 2) * radialProfile (N - 1) s r) := rfl
      rw [heq, h.deriv]
      rw [show N - 1 - 1 = N - 2 by omega]
      ring
    ext i j
    change sliceHessian (fun y => radialProfile N s (PDE.vecNormSq y)) Y i j = _
    have h := sliceHessian_comp_vecNormSq_sub
      (m := 0) (x := Y)
      (radialProfile_contDiff).contDiffAt i j
    simp at h
    rw [h, radialProfile_second_deriv, radialProfile_deriv (by omega)]
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, positivePower, Matrix.of_apply]
    generalize max (1 - PDE.vecNormSq Y / s ^ 2) 0 = w
    split_ifs <;> field_simp [hs.ne'] <;> ring
  have retention_barrier_gradient {d : ℕ} (Y : PDE.Vec d) :
      PDE.classicalGradient (barrier N s) Y =
      (-2 * N / s ^ 2 * (max (1 - PDE.vecNormSq Y / s ^ 2) 0) ^ (N - 1)) • Y := by
    have h := classicalGradient_comp_vecNormSq_sub
      (m := 0)
      ((radialProfile_derivative (by omega : 2 ≤ N) s
        (PDE.vecNormSq (Y - 0))).differentiableAt)
    simp at h
    change PDE.classicalGradient (fun y => radialProfile N s (PDE.vecNormSq y)) Y = _
    rw [h, radialProfile_deriv (by omega)]
    ext i
    simp [positivePower]
    ring
  have hs2 := sq_pos_of_pos hs
  have hpow1 : N - 1 ≠ 0 := by omega
  have hpow2 : N - 2 ≠ 0 := by omega
  refine ⟨retention_barrier_contDiff hN s, ?_, ?_, ?_, ?_⟩
  · intro Y
    have h0 : 0 ≤ max (1 - PDE.vecNormSq Y / s ^ 2) 0 := le_max_right _ _
    have h1 : max (1 - PDE.vecNormSq Y / s ^ 2) 0 ≤ 1 := by
      have hdiv := div_nonneg (PDE.vecNormSq_nonneg Y) hs2.le
      exact max_le (by linarith) zero_le_one
    exact ⟨pow_nonneg h0 _, pow_le_one₀ h0 h1⟩
  · simp [barrier, PDE.vecNormSq, PDE.vecDot]
  · intro Y hY
    have hY' : PDE.vecNormSq Y < s ^ 2 := by
      simpa [PDE.euclideanBall, PDE.euclideanSqDist] using hY
    have hw : 0 ≤ 1 - PDE.vecNormSq Y / s ^ 2 := by
      have := (div_lt_one hs2).mpr hY'
      linarith
    rw [retention_barrier_gradient Y, retention_barrier_hessian Y,
      max_eq_left hw]
    exact ⟨rfl, rfl⟩
  · intro Y hY
    have hY' : s ^ 2 ≤ PDE.vecNormSq Y := by
      simpa [PDE.euclideanBall, PDE.euclideanSqDist, not_lt] using hY
    have hw : 1 - PDE.vecNormSq Y / s ^ 2 ≤ 0 := by
      have := (one_le_div hs2).mpr hY'
      linarith
    rw [retention_barrier_gradient Y, retention_barrier_hessian Y]
    simp [barrier, max_eq_right hw, show N ≠ 0 by omega, hpow1, hpow2]








private theorem young_of_square {X U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hX : X ^ 2 ≤ 4 * U * V) : X ≤ U + V := by
  nlinarith [sq_nonneg (U - V)]


/-- Young absorption gives the source global drift inequality. -/
theorem retention_barrier_drift_inequality {d N : ℕ} (hN : 3 ≤ N)
    (lam Lam s H : ℝ) (hs : 0 < s) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hc : 0 < barrierC d N lam Lam) (A : PDE.Mat d) (hA : A.IsSymm)
    (hlo : lam • (1 : PDE.Mat d) ≤ A) (hhi : A ≤ Lam • (1 : PDE.Mat d))
    (a Y : PDE.Vec d) (ha : PDE.vecEuclideanNorm a ≤ H) :
    -barrierRate d N lam Lam s H * barrier N s Y ≤
      matrixContraction A (Hess (barrier N s) Y) -
        PDE.vecDot a (PDE.classicalGradient (barrier N s) Y)   := by
  have barrier_drift_absorption (hY : Y ∈ PDE.euclideanBall 0 s) :
      PDE.vecDot a (PDE.classicalGradient (barrier N s) Y) ≤
      (barrierC d N lam Lam / s ^ 4) *
        (1 - PDE.vecNormSq Y / s ^ 2) ^ (N - 2) * PDE.vecNormSq Y +
      ((N : ℝ) ^ 2 * H ^ 2 / barrierC d N lam Lam) * barrier N s Y := by
    have hs2 := sq_pos_of_pos hs
    have hR := PDE.vecNormSq_nonneg Y
    have hY' : PDE.vecNormSq Y < s ^ 2 := by
      simpa [PDE.euclideanBall, PDE.euclideanSqDist] using hY
    set w := 1 - PDE.vecNormSq Y / s ^ 2 with hw
    have hw0 : 0 ≤ w := by
      have := (div_lt_one hs2).mpr hY'
      dsimp [w]; linarith
    have hnorm : PDE.vecNormSq a ≤ H ^ 2 := by
      have hn := PDE.vecEuclideanNorm_nonneg a
      have heq := PDE.vecEuclideanNorm_sq a
      nlinarith
    have hCS :=
      (PDE.sq_vecDot_le_vecNormSq_mul_vecNormSq a Y).trans
        (mul_le_mul_of_nonneg_right hnorm hR)
    have hgrad := (retention_polynomial_barrier hN s hs).2.2.2.1 Y hY
    have hdot : PDE.vecDot a (PDE.classicalGradient (barrier N s) Y) =
        (-2 * N / s ^ 2 * w ^ (N - 1)) * PDE.vecDot a Y := by
      rw [hgrad.1]
      unfold PDE.vecDot
      simp [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hψ : barrier N s Y = w ^ N := by
      unfold barrier
      rw [max_eq_left hw0]
    have hpow : (w ^ (N - 1)) ^ 2 = w ^ (N - 2) * w ^ N := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    have hsq := mul_le_mul_of_nonneg_left hCS
      (sq_nonneg (-2 * (N : ℝ) / s ^ 2 * w ^ (N - 1)))
    have hid : (-2 * (N : ℝ) / s ^ 2 * w ^ (N - 1)) ^ 2 *
        (H ^ 2 * PDE.vecNormSq Y) =
        4 * ((barrierC d N lam Lam / s ^ 4) * w ^ (N - 2) * PDE.vecNormSq Y) *
          (((N : ℝ) ^ 2 * H ^ 2 / barrierC d N lam Lam) * w ^ N) := by
      rw [mul_pow, hpow]
      field_simp [hs.ne', hc.ne']
      ring
    rw [hdot, hψ]
    apply young_of_square (by positivity) (by positivity)
    rw [mul_pow, hid.symm]
    exact hsq
  have retention_barrier_second_order (hY : Y ∈ PDE.euclideanBall 0 s) :
      -(2 * N * d * Lam / s ^ 2) * barrier N s Y +
      (barrierC d N lam Lam / s ^ 4) *
        (1 - PDE.vecNormSq Y / s ^ 2) ^ (N - 2) * PDE.vecNormSq Y ≤
      matrixContraction A (Hess (barrier N s) Y) := by
    have contraction_outer {d : ℕ} (A : PDE.Mat d) (Y : PDE.Vec d) :
        matrixContraction A (Matrix.of (fun i j => Y i * Y j)) = PDE.vecDot Y (A *ᵥ Y) := by
      classical
      unfold matrixContraction PDE.vecDot Matrix.mulVec dotProduct
      simp
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have contraction_one {d : ℕ} (A : PDE.Mat d) :
        matrixContraction A 1 = A.trace := by
      classical
      simp [matrixContraction, Matrix.trace, Matrix.diag, Matrix.one_apply]
    have trace_upper :
        A.trace ≤ (d : ℝ) * Lam := by
      have htrace := (Matrix.le_iff.mp hhi).trace_nonneg
      simp [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin] at htrace
      linarith
    have _hA := hA
    have hLam := (hlam.trans_le hlamLam).le
    have hs2 := sq_pos_of_pos hs
    have hR := PDE.vecNormSq_nonneg Y
    have hY' : PDE.vecNormSq Y < s ^ 2 := by
      simpa [PDE.euclideanBall, PDE.euclideanSqDist] using hY
    set w := 1 - PDE.vecNormSq Y / s ^ 2 with hw
    have hw0 : 0 ≤ w := by
      have := (div_lt_one hs2).mpr hY'
      dsimp [w]; linarith
    have hw1 : w ≤ 1 := by
      have := div_nonneg hR hs2.le
      dsimp [w]; linarith
    rw [((retention_polynomial_barrier hN s hs).2.2.2.1 Y hY).2, matrixContraction_add_right, matrixContraction_smul_right,
      matrixContraction_smul_right, contraction_one, contraction_outer]
    change _ ≤ (-2 * N / s ^ 2 * w ^ (N - 1)) * A.trace +
      (4 * N * (N - 1 : ℕ) / s ^ 4 * w ^ (N - 2)) * PDE.vecDot Y (A *ᵥ Y)
    have hneg : -2 * (N : ℝ) / s ^ 2 * w ^ (N - 1) ≤ 0 := by
      have hnonneg : 0 ≤ 2 * (N : ℝ) / s ^ 2 * w ^ (N - 1) := by positivity
      convert neg_nonpos.mpr hnonneg using 1; ring
    have hpos : 0 ≤ 4 * (N : ℝ) * (N - 1 : ℕ) / s ^ 4 * w ^ (N - 2) := by
      positivity
    have ht := mul_le_mul_of_nonpos_left trace_upper hneg
    have hq := mul_le_mul_of_nonneg_left (vecDot_mulVec_lower_of_loewner hlo Y) hpos
    apply le_trans _ (add_le_add ht hq)
    have hpow1 : w ^ (N - 1) = w ^ (N - 2) * w := by
      rw [show N - 1 = (N - 2) + 1 by omega, pow_succ]
    have hpow2 : w ^ N = w ^ (N - 2) * w ^ 2 := by
      calc
        w ^ N = w ^ ((N - 2) + 2) := congrArg (fun k => w ^ k) (by omega)
        _ = w ^ (N - 2) * w ^ 2 := pow_add _ _ _
    have hrem : 0 ≤ (2 * (N : ℝ) * d * Lam / s ^ 4) *
        w ^ (N - 2) * PDE.vecNormSq Y * (1 - w) := by
      positivity
    have hid : PDE.vecNormSq Y = s ^ 2 * (1 - w) := by
      dsimp [w]
      field_simp [hs.ne']
      ring
    calc
      _ = (-2 * N / s ^ 2 * w ^ (N - 1)) * ((d : ℝ) * Lam) +
          (4 * N * (N - 1 : ℕ) / s ^ 4 * w ^ (N - 2)) * (lam * PDE.vecNormSq Y) -
          (2 * (N : ℝ) * d * Lam / s ^ 4) * w ^ (N - 2) *
            PDE.vecNormSq Y * (1 - w) := by
        unfold barrier barrierC
        rw [max_eq_left hw0, hpow1, hpow2, hid]
        field_simp [hs.ne']
        ring
      _ ≤ _ := sub_le_self _ hrem
  by_cases hY : Y ∈ PDE.euclideanBall 0 s
  · have hsecond := retention_barrier_second_order hY
    have hyoung := barrier_drift_absorption hY
    unfold barrierRate
    linarith
  · obtain ⟨hψ, hgrad, hHess⟩ := (retention_polynomial_barrier hN s hs).2.2.2.2 Y hY
    rw [hψ, hgrad, hHess]
    simp [matrixContraction, PDE.vecDot]



/-- The explicit retention rate has the stated structural upper bound. -/
theorem retention_rate_uniform {d N : ℕ} (hN : 3 ≤ N)
    (lam Lam ρ H : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hρ : 0 < ρ) (hc : 0 < barrierC d N lam Lam) :
    barrierRate d N lam Lam ρ H ≤
      (2 * N * d * Lam + (N : ℝ) ^ 2 / barrierC d N lam Lam) * (ρ⁻¹ ^ 2 + H ^ 2) := by
  have _hN := hN
  have _hρ := hρ
  have hLam := (hlam.trans_le hlamLam).le
  have hA : 0 ≤ 2 * (N : ℝ) * d * Lam := by positivity
  have hB : 0 ≤ (N : ℝ) ^ 2 / barrierC d N lam Lam := by positivity
  have h1 := mul_nonneg hA (sq_nonneg H)
  have h2 : 0 ≤ ((N : ℝ) ^ 2 / barrierC d N lam Lam) * ρ⁻¹ ^ 2 :=
    mul_nonneg hB (sq_nonneg _)
  unfold barrierRate
  simp only [div_eq_mul_inv, inv_pow] at h1 h2 ⊢
  nlinarith only [h1, h2]

end HypoellipticAleksandrov.KineticAleksandrov.Decay

