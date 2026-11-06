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
import Lean.Elab.Tactic.Grind



/-!
# Polynomial retention barriers

Positive-part powers have vanishing jets at their gluing point.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

open Set Filter
open scoped Topology

private def positivePower (N : ℕ) (x : ℝ) : ℝ := (max x 0) ^ N

section
variable {N : ℕ} (hN : 2 ≤ N)

include hN
private theorem positivePower_derivative  (x : ℝ) :
    HasDerivAt (positivePower N) ((N : ℝ) * positivePower (N - 1) x) x := by
  have hNm : N - 1 ≠ 0 := by omega
  rcases lt_trichotomy x 0 with hx | rfl | hx
  ·
    have hd := (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq (show positivePower N =ᶠ[𝓝 x] fun _ => (0 ) by
        filter_upwards [gt_mem_nhds hx] with y hy
        simp [positivePower, max_eq_right hy.le, show N ≠ 0 by omega])
    simpa [positivePower, max_eq_right hx.le, hNm] using hd
  ·
    have hn : HasDerivWithinAt (positivePower N) 0 (Iic 0) 0 :=
      (hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt.congr
        (fun y hy => by simp [positivePower, max_eq_right hy, show N ≠ 0 by omega])
        (by simp [positivePower, show N ≠ 0 by omega])
    have hu := (show HasDerivWithinAt (positivePower N) 0 (Ici 0) 0 by
        have hd := ((hasDerivAt_id (0 : ℝ)).fun_pow N).hasDerivWithinAt (s := Ici 0)

        exact (show HasDerivWithinAt (fun x : ℝ => x ^ N) 0 (Ici 0) 0 by
            simpa only [id_eq, zero_pow hNm, mul_zero, zero_mul] using hd).congr (fun y hy => by simp [positivePower, max_eq_left hy])
          (by simp [positivePower])).union hn
    rw [Ici_union_Iic] at hu
    simpa [positivePower, hNm] using hasDerivWithinAt_univ.mp hu
  ·
    simpa [positivePower, max_eq_left hx.le] using
      ((hasDerivAt_id x).pow N).congr_of_eventuallyEq (by
          filter_upwards [lt_mem_nhds hx] with y hy
          simp [positivePower, max_eq_left hy.le])

private theorem positivePower_deriv  :
    deriv (positivePower N) = fun x => (N : ℝ) * positivePower (N - 1) x := by
  funext x
  exact (positivePower_derivative hN x).deriv
end


private theorem positivePower_continuous (N : ℕ) : Continuous (positivePower N) := by
  unfold positivePower
  exact (continuous_id.max continuous_const).pow N

variable {N : ℕ}

private theorem positivePower_contDiff_one  (hN : 2 ≤ N) :
    ContDiff ℝ 1 (positivePower N) := by
  rw [contDiff_one_iff_deriv, positivePower_deriv hN]
  exact ⟨fun x => (positivePower_derivative hN x).differentiableAt,
    continuous_const.mul (positivePower_continuous _)⟩

private theorem positivePower_contDiff_two  (hN : 3 ≤ N) :
    ContDiff ℝ 2 (positivePower N) := by
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


  obtain ⟨n, hn⟩ := exists_nat_gt (max 3 ((d : ℝ) * Lam / (2 * lam)))


  have hineq  :=
    (div_lt_iff₀ (by positivity)).mp ((le_max_right _ _).trans_lt hn)
  refine ⟨n + 1, ?_, ?_, ?_⟩
  · have : 3 < n := by exact_mod_cast ((le_max_left _ _).trans_lt hn)
    omega
  · grind
  · unfold barrierC
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]

    nlinarith [mul_pos (by positivity) (show 0 < 2 * (n : ℝ) * lam - (d : ℝ) * Lam by linarith)]

/-- The positive-part polynomial barrier is globally twice continuously differentiable. -/
theorem retention_barrier_contDiff {d N : ℕ} (hN : 3 ≤ N) (s : ℝ) :
    ContDiff ℝ 2 (barrier (d := d) N s) := (positivePower_contDiff_two hN).comp (contDiff_const.sub (PDE.contDiff_vecNormSq.of_le (by norm_num) |>.div_const _))


private def radialProfile (N : ℕ) (s r : ℝ) : ℝ := positivePower N (1 - r / s ^ 2)

variable {N : ℕ}

private theorem radialProfile_derivative  (hN : 2 ≤ N) (s r : ℝ) :
    HasDerivAt (radialProfile N s)
      (-((N : ℝ) / s ^ 2) * positivePower (N - 1) (1 - r / s ^ 2)) r := ((positivePower_derivative hN (1 - r / s ^ 2)).comp r (((hasDerivAt_id r).div_const (s ^ 2)).const_sub 1)).congr_deriv (by ring)

private theorem radialProfile_deriv  (hN : 2 ≤ N) (s : ℝ) :
    deriv (radialProfile N s) =
      fun r => -((N : ℝ) / s ^ 2) * positivePower (N - 1) (1 - r / s ^ 2) := by
  funext r
  exact (radialProfile_derivative hN s r).deriv

private theorem radialProfile_second_deriv  (hN : 3 ≤ N) (s r : ℝ) :
    deriv (deriv (radialProfile N s)) r =
      ((N : ℝ) / s ^ 2) * ((N - 1 : ℕ) / s ^ 2) *
        positivePower (N - 2) (1 - r / s ^ 2) := by
  let sharedTerm_1c9c9c63da := ((-((N : ℝ) / s ^ 2)))
  rw [radialProfile_deriv (by omega)]
  have h := (radialProfile_derivative (N := N - 1) (by omega) s r).const_mul
    sharedTerm_1c9c9c63da
  have heq : (fun r => sharedTerm_1c9c9c63da *
      positivePower (N - 1) (1 - r / s ^ 2)) =
      (fun r => sharedTerm_1c9c9c63da * radialProfile (N - 1) s r) := rfl
  rw [heq, h.deriv]
  rw [show N - 1 - 1 = N - 2 by omega]
  ring

private theorem radialProfile_contDiff  (hN : 3 ≤ N) (s : ℝ) :
    ContDiff ℝ 2 (radialProfile N s) :=
  (positivePower_contDiff_two hN).comp
    (contDiff_const.sub (contDiff_id.div_const _))

variable {d N : ℕ} (hN : 3 ≤ N) (s : ℝ)

include hN in
/-- The global gradient formula uses the literal positive part, including the boundary. -/
theorem retention_barrier_gradient  (Y : PDE.Vec d) :
    PDE.classicalGradient (barrier N s) Y =
      (-2 * N / s ^ 2 * (max (1 - PDE.vecNormSq Y / s ^ 2) 0) ^ (N - 1)) • Y := by
  have h := classicalGradient_comp_vecNormSq_sub
    (m := (0 : PDE.Vec d)) (x := Y)
    ((radialProfile_derivative (by omega : 2 ≤ N) s
      (PDE.vecNormSq (Y - 0))).differentiableAt)
  simp only [sub_zero] at h
  change PDE.classicalGradient (fun y => radialProfile N s (PDE.vecNormSq y)) Y = _
  rw [h, radialProfile_deriv (by omega)]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_zero, positivePower]
  ring

variable (hs : 0 < s)

include hN hs
/-- The global Hessian formula uses the literal positive part through order two. -/
theorem retention_barrier_hessian   (Y : PDE.Vec d) :
    Hess (barrier N s) Y =
      (-2 * N / s ^ 2 * (max (1 - PDE.vecNormSq Y / s ^ 2) 0) ^ (N - 1)) • (1 : PDE.Mat d) +
      ((4 * N * (N - 1 : ℕ) / s ^ 4 *
        (max (1 - PDE.vecNormSq Y / s ^ 2) 0) ^ (N - 2)) •
          Matrix.of (fun i j => Y i * Y j) : PDE.Mat d) := by

  ext i j
  change sliceHessian (fun y => radialProfile N s (PDE.vecNormSq y)) Y i j = _
  have h := sliceHessian_comp_vecNormSq_sub
    (m := (0 : PDE.Vec d)) (x := Y)
    (radialProfile_contDiff hN s).contDiffAt i j
  simp only [sub_zero] at h
  rw [h, radialProfile_second_deriv hN, radialProfile_deriv (by omega)]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    positivePower, Pi.zero_apply, sub_zero, Matrix.of_apply]
  generalize max (1 - PDE.vecNormSq Y / s ^ 2) 0 = w
  split_ifs <;> field_simp [hs.ne'] <;> ring

/-- The source retention polynomial, including its boundary jets. -/
theorem retention_polynomial_barrier   :
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
        Hess (barrier N s) Y = 0) := by
  have hs2  := sq_pos_of_pos hs
  have hpow1 : N - 1 ≠ 0 := by omega
  have hpow2 : N - 2 ≠ 0 := by omega
  refine ⟨retention_barrier_contDiff hN s, ?_, ?_, ?_, ?_⟩
  · intro Y
    have h0 : 0 ≤ max (1 - PDE.vecNormSq Y / s ^ 2) 0 := le_max_right _ _

    exact ⟨pow_nonneg h0 _, pow_le_one₀ h0 (by

        have hdiv := div_nonneg (PDE.vecNormSq_nonneg Y) hs2.le
        exact max_le (by linarith) zero_le_one)⟩
  · simp [barrier, PDE.vecNormSq, PDE.vecDot]
  · intro Y hY

    have hw : 0 ≤ 1 - PDE.vecNormSq Y / s ^ 2 := by
      have := (div_lt_one hs2).mpr (by
          simpa only [PDE.euclideanBall, PDE.euclideanSqDist, mem_ofPred_eq, sub_zero] using hY)
      linarith
    rw [retention_barrier_gradient hN s Y, retention_barrier_hessian hN s hs Y,
      max_eq_left hw]
    exact ⟨rfl, rfl⟩
  · intro Y hY


    rw [retention_barrier_gradient hN s Y, retention_barrier_hessian hN s hs Y]
    simp [barrier, max_eq_right (show 1 - PDE.vecNormSq Y / s ^ 2 ≤ 0 by
        have := (one_le_div hs2).mpr (by
            simpa only [PDE.euclideanBall, PDE.euclideanSqDist, mem_ofPred_eq,
              sub_zero, not_lt] using hY)
        linarith), show N ≠ 0 by omega, hpow1, hpow2]

end HypoellipticAleksandrov.KineticAleksandrov.Decay
