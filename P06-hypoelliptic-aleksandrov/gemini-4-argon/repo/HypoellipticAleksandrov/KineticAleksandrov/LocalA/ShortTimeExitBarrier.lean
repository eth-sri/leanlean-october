module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ShortTimeExitLinear
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ShortTimeExitGeometry
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.Geometry
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic

/-! # The explicit finite exponential barrier of the source

Time is physical backward time: elapsed time is `T - p.1`. The sum consists
of the positive and negative coordinate planes at the given starting velocity.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open HypoellipticAleksandrov Parabolic Set

/- The source's two-sign coordinate barrier, without a coefficient derivative. -/
def ballExitBarrier {d } (Lam α δ T : ℝ) (v : PDE.Vec d)
    (p : TimeVelocity d) : ℝ :=
  ∑ i : Fin d, (ballExitPlane i (-Lam * α ^ 2) α
    (Lam * α ^ 2 * T - α * v i - α * δ) p +
    ballExitPlane i (-Lam * α ^ 2) (-α)
      (Lam * α ^ 2 * T + α * v i - α * δ) p)

/- Every summand of the barrier is positive. -/
theorem ballExitBarrier_nonneg {d } (Lam α δ T : ℝ) (v : PDE.Vec d)
    (p : TimeVelocity d) : 0 ≤ ballExitBarrier Lam α δ T v p :=
  Finset.sum_nonneg (fun _ _ => add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)

/- The barrier is smooth, including both time faces. -/
theorem ballExitBarrier_contDiff {d } (Lam α δ T : ℝ) (v : PDE.Vec d) :
    ContDiff ℝ (⊤ : ℕ∞) (ballExitBarrier Lam α δ T v) :=
  ContDiff.sum (fun i _ => (ballExitPlane_contDiff i _ _ _).add
    (ballExitPlane_contDiff i _ _ _))

/- The barrier is a backward scalar supersolution under upper ellipticity. -/
theorem ballExitBarrier_operator_nonpos {d lam Lam}
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
    (hn ▸ ballExitPlane_operator_nonpos B hB i (-α) _ p)

/- At the starting velocity, every coordinate plane has the same exponential value. -/
theorem ballExitBarrier_lateral {d } (hd : 1 ≤ d) {R Lam σ }
    (hR : 0 < R) (hLam : 0 < Lam) (α T : ℝ) (hα : 0 ≤ α)
    (v₀ v : PDE.Vec d) (hv : v ∈ PDE.euclideanBall v₀ (3 * R / 4))
    (p ) (hp : p ∈ scalarParabolicLateralFace σ T
      (PDE.euclideanBall v₀ R)) :
    1 ≤ ballExitBarrier Lam α (R / (4 * Real.sqrt d)) T v p := by
  obtain ⟨i, hi⟩ : ∃ i : Fin d, R / (4 * Real.sqrt d) ≤ |p.2 i - v i| := by
    let w := p.2
    have hw := hp.2
    have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
    have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdR
    have hδ : 0 < R / (4 * Real.sqrt d) := div_pos hR (by positivity)
    by_contra h
    push Not at h
    have hn : ‖w - v‖ < R / (4 * Real.sqrt d) := by
      apply (pi_norm_lt_iff hδ).mpr
      intro i
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using h i
    have he := PDE.vecEuclideanNorm_le_sqrt_natCast_mul_norm (w - v)
    have hm := mul_lt_mul_of_pos_left hn hs
    have hc : Real.sqrt d * (R / (4 * Real.sqrt d)) = R / 4 := by
      field_simp
    rw [hc] at hm
    have _h_inl_8 : R / 4 ≤ PDE.vecEuclideanNorm (w - v) := by
        have hvn := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).mp hv
        have hwn : R ≤ PDE.vecEuclideanNorm (w - v₀) := by
          apply le_of_not_gt
          intro h
          rw [(PDE.isOpen_euclideanBall v₀ R).frontier_eq] at hw
          exact hw.2 ((PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mpr h)
        have ht := PDE.vecEuclideanNorm_add_le (w - v) (v - v₀)
        rw [sub_add_sub_cancel] at ht
        linarith only [hvn, hwn, ht]

      /- Some signed coordinate accounts for the Euclidean lateral distance. -/
    exact (not_lt_of_ge _h_inl_8) (he.trans_lt hm)
  let δ := R / (4 * Real.sqrt d)
  let F : Fin d → ℝ := fun j => ballExitPlane j (-Lam * α ^ 2) α
    (Lam * α ^ 2 * T - α * v j - α * δ) p +
      ballExitPlane j (-Lam * α ^ 2) (-α)
        (Lam * α ^ 2 * T + α * v j - α * δ) p
  have hterm : F i ≤ ballExitBarrier Lam α δ T v p := by
    change F i ≤ ∑ j, F j
    exact Finset.single_le_sum (f := F)
      (fun j _ => add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      (Finset.mem_univ i)
  have ht : 0 ≤ Lam * α ^ 2 * (T - p.1) :=
    mul_nonneg (mul_nonneg hLam.le (sq_nonneg α)) (sub_nonneg.mpr hp.1.2)
  have hpos : ballExitPlane i (-Lam * α ^ 2) α
      (Lam * α ^ 2 * T - α * v i - α * δ) p =
        Real.exp (α * (p.2 i - v i - δ) + Lam * α ^ 2 * (T - p.1)) := by
    unfold ballExitPlane
    congr 1
    ring
  have hneg : ballExitPlane i (-Lam * α ^ 2) (-α)
      (Lam * α ^ 2 * T + α * v i - α * δ) p =
        Real.exp (α * (-(p.2 i - v i) - δ) + Lam * α ^ 2 * (T - p.1)) := by
    unfold ballExitPlane
    congr 1
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
  exact hone.trans hterm

/- Optimizing the exponential parameter gives the exact source Gaussian exponent. -/
theorem ballExitBarrier_optimized {d } (hd : 1 ≤ d) {Lam R σ τ }
    (hLam : 0 < Lam) (hR : 0 < R) (hστ : σ < τ) (v : PDE.Vec d) :
    let δ := R / (4 * Real.sqrt d)
    let α := δ / (2 * Lam * (τ - σ))
    ballExitBarrier Lam α δ τ v (σ, v) =
      2 * (d : ℝ) * Real.exp (-R ^ 2 / (64 * (d : ℝ) * Lam * (τ - σ))) := by
  dsimp only
  have _h_inl_14 (Lam α δ T s : ℝ) (v : PDE.Vec d) : ballExitBarrier Lam α δ T v (s, v) = 2 * (d : ℝ) * Real.exp (-α * δ + Lam * α ^ 2 * (T - s)) := by
    unfold ballExitBarrier ballExitPlane
    have hpos (i : Fin d) :
        -Lam * α ^ 2 * s + α * v i + (Lam * α ^ 2 * T - α * v i - α * δ) =
          -α * δ + Lam * α ^ 2 * (T - s) := by ring
    have hneg (i : Fin d) :
        -Lam * α ^ 2 * s + -α * v i + (Lam * α ^ 2 * T + α * v i - α * δ) =
          -α * δ + Lam * α ^ 2 * (T - s) := by ring
    simp only [hpos, hneg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [_h_inl_14]
  congr 2
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hs : Real.sqrt (d : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hdR)
  have hs2 := Real.sq_sqrt hdR.le
  have ht : τ - σ ≠ 0 := ne_of_gt (sub_pos.mpr hστ)
  field_simp [hs, ht, hLam.ne']
  nlinarith only [hs2]

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
