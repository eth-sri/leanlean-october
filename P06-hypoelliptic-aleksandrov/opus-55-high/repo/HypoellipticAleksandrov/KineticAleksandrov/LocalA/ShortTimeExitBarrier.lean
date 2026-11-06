module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ShortTimeExitLinear
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ShortTimeExitGeometry

/-! # The explicit finite exponential barrier of the source

Time is physical backward time: elapsed time is `T - p.1`. The sum consists
of the positive and negative coordinate planes at the given starting velocity.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open HypoellipticAleksandrov Parabolic Set

/-- The source's two-sign coordinate barrier, without a coefficient derivative. -/
def ballExitBarrier {d : ℕ} (Lam α δ T : ℝ) (v : PDE.Vec d)
    (p : TimeVelocity d) : ℝ :=
  ∑ i : Fin d, (ballExitPlane i (-Lam * α ^ 2) α
    (Lam * α ^ 2 * T - α * v i - α * δ) p +
    ballExitPlane i (-Lam * α ^ 2) (-α)
      (Lam * α ^ 2 * T + α * v i - α * δ) p)

variable {d : ℕ} (Lam α δ T : ℝ) (v : PDE.Vec d)

/-- Every summand of the barrier is positive. -/
theorem ballExitBarrier_nonneg 
    (p : TimeVelocity d) : 0 ≤ ballExitBarrier Lam α δ T v p :=
  Finset.sum_nonneg (fun _ _ => add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)

/-- The barrier is smooth, including both time faces. -/
theorem ballExitBarrier_contDiff  :
    ContDiff ℝ (⊤ : ℕ∞) (ballExitBarrier Lam α δ T v) :=
  ContDiff.sum (fun i _ => (ballExitPlane_contDiff i _ _ _).add
    (ballExitPlane_contDiff i _ _ _))

/-- The barrier is a backward scalar supersolution under upper ellipticity. -/
theorem ballExitBarrier_operator_nonpos  {lam Lam : ℝ}
    (B : CoefficientField d) (hB : SectionTwo.IsSectionTwoCoefficient lam Lam B)
    (α δ T : ℝ) (v : PDE.Vec d) (p : TimeVelocity d) :
    scalarParabolicOperator B 0 (ballExitBarrier Lam α δ T v) p ≤ 0 := by
  unfold ballExitBarrier
  rw [ballExit_operator_sum B _ _ (fun i _ =>
    ((ballExitPlane_contDiff i _ _ _).add (ballExitPlane_contDiff i _ _ _)).of_le
      (by simp))]
  apply Finset.sum_nonpos
  intro i _
  rw [ballExit_operator_add B _ _ ((ballExitPlane_contDiff i _ _ _).of_le (by simp))
    ((ballExitPlane_contDiff i _ _ _).of_le (by simp))]
  have hn : -Lam * α ^ 2 = -Lam * (-α) ^ 2 := by ring
  exact add_nonpos (ballExitPlane_operator_nonpos B hB i α _ p)
    (hn ▸ ballExitPlane_operator_nonpos B hB i _ _ p)

/-- At the starting velocity, every coordinate plane has the same exponential value. -/
theorem ballExitBarrier_at_center  (Lam α δ T s : ℝ) (v : PDE.Vec d) :
    ballExitBarrier Lam α δ T v (s, v) =
      2 * (d : ℝ) * Real.exp (-α * δ + Lam * α ^ 2 * (T - s)) := by
  unfold ballExitBarrier ballExitPlane
  have hpos (i : Fin d) :
      -Lam * α ^ 2 * s + α * v i + (Lam * α ^ 2 * T - α * v i - α * δ) =
        -α * δ + Lam * α ^ 2 * (T - s) := by ring
  have hneg (i : Fin d) :
      -Lam * α ^ 2 * s + -α * v i + (Lam * α ^ 2 * T + α * v i - α * δ) =
        -α * δ + Lam * α ^ 2 * (T - s) := by ring
  simp only [hpos, hneg, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  ring

/-- A sufficiently distant signed coordinate makes a lateral summand at least one. -/
theorem ballExitBarrier_lateral  (hd : 1 ≤ d) {R Lam σ : ℝ}
    (hR : 0 < R) (hLam : 0 < Lam) (α T : ℝ) (hα : 0 ≤ α)
    (v₀ v : PDE.Vec d) (hv : v ∈ PDE.euclideanBall v₀ (3 * R / 4))
    (p : TimeVelocity d) (hp : p ∈ scalarParabolicLateralFace σ T
      (PDE.euclideanBall v₀ R)) :
    1 ≤ ballExitBarrier Lam α (R / (4 * Real.sqrt d)) T v p := by
  obtain ⟨i, hi⟩ := ballExit_lateral_coordinate hd hR v₀ v p.2 hv hp.2
  let δ := R / (4 * Real.sqrt d)
  let F  := fun j => ballExitPlane j (-Lam * α ^ 2) α
    (Lam * α ^ 2 * T - α * v j - α * δ) p +
      ballExitPlane j (-Lam * α ^ 2) (-α)
        (Lam * α ^ 2 * T + α * v j - α * δ) p
  have hterm : F i ≤ ballExitBarrier Lam α δ T v p := Finset.single_le_sum (f := F)
      (fun j _ => add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      (Finset.mem_univ i)
  have ht : 0 ≤ Lam * α ^ 2 * (T - p.1) :=
    mul_nonneg (mul_nonneg hLam.le (sq_nonneg α)) (sub_nonneg.mpr hp.1.2)
  have hpos : ballExitPlane i (-Lam * α ^ 2) α
      (Lam * α ^ 2 * T - α * v i - α * δ) p =
        Real.exp (α * (p.2 i - v i - δ) + Lam * α ^ 2 * (T - p.1)) := by
    unfold ballExitPlane
    ring
  have hneg : ballExitPlane i (-Lam * α ^ 2) (-α)
      (Lam * α ^ 2 * T + α * v i - α * δ) p =
        Real.exp (α * (-(p.2 i - v i) - δ) + Lam * α ^ 2 * (T - p.1)) := by
    unfold ballExitPlane
    ring
  have hone : 1 ≤ F i := by
    dsimp only [F]
    rw [hpos, hneg]
    by_cases hh : 0 ≤ p.2 i - v i
    · rw [abs_of_nonneg hh] at hi
      have he : 1 ≤ Real.exp
          (α * (p.2 i - v i - δ) + Lam * α ^ 2 * (T - p.1)) :=
        Real.one_le_exp_iff.mpr (add_nonneg
          (mul_nonneg hα (sub_nonneg.mpr hi)) ht)
      exact he.trans (le_add_of_nonneg_right (Real.exp_pos _).le)
    · rw [abs_of_neg (lt_of_not_ge hh)] at hi
      have he : 1 ≤ Real.exp
          (α * (-(p.2 i - v i) - δ) + Lam * α ^ 2 * (T - p.1)) :=
        Real.one_le_exp_iff.mpr (add_nonneg
          (mul_nonneg hα (sub_nonneg.mpr hi)) ht)
      exact he.trans (le_add_of_nonneg_left (Real.exp_pos _).le)
  linarith

/-- Optimizing the exponential parameter gives the exact source Gaussian exponent. -/
theorem ballExitBarrier_optimized  (hd : 1 ≤ d) {Lam R σ τ : ℝ}
    (hLam : 0 < Lam) (hR : 0 < R) (hστ : σ < τ) (v : PDE.Vec d) :
    let δ := R / (4 * Real.sqrt d)
    let α := δ / (2 * Lam * (τ - σ))
    ballExitBarrier Lam α δ τ v (σ, v) =
      2 * (d : ℝ) * Real.exp (-R ^ 2 / (64 * (d : ℝ) * Lam * (τ - σ))) := by
  dsimp only
  rw [ballExitBarrier_at_center]
  grind

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
