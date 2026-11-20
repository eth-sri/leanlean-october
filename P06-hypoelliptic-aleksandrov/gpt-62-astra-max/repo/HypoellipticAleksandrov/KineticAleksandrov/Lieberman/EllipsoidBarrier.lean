module

public import HypoellipticAleksandrov.KineticAleksandrov.Lieberman.EllipsoidGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Lieberman.EllipsoidBarrierCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib

/-! # Smooth zero-boundary ellipsoid barriers absorbing bounded drift -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Lieberman
open HypoellipticAleksandrov Parabolic Set Filter Matrix
open scoped Matrix MatrixOrder Topology BigOperators

private theorem trace_mul_nonneg {d : ℕ} {A Q : PDE.Mat d}
    (hA : A.PosSemidef) (hQ : Q.PosSemidef) : 0 ≤ (A * Q).trace := by
  let S := CFC.sqrt Q
  calc
    0 ≤ (S * A * Sᴴ).trace := (hA.mul_mul_conjTranspose_same S).trace_nonneg
    _ = (S * A * S).trace := by rw [((CFC.sqrt_nonneg Q).posSemidef).isHermitian.eq]
    _ = (A * S * S).trace := (Matrix.trace_mul_cycle A S S).symm
    _ = (A * (S * S)).trace := by rw [Matrix.mul_assoc]
    _ = (A * Q).trace := by
      rw [CFC.sqrt_mul_sqrt_self Q hQ.nonneg]

/-- Lower Loewner ellipticity controls contraction with a positive-definite matrix. -/
theorem contraction_lower {d : ℕ} {A Q : PDE.Mat d} (hQ : Q.PosDef)
    {lam : ℝ} (hA : lam • (1 : PDE.Mat d) ≤ A) :
    lam * Q.trace ≤ matrixContraction A Q := by
  have hh := trace_mul_nonneg (Matrix.le_iff.mp hA) hQ.posSemidef
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sub,
    Matrix.trace_smul] at hh
  rw [matrixContraction_eq_trace_mul_of_isSymm _ _ hQ.isHermitian.isSymm]
  exact sub_nonneg.mp hh

private theorem drift_absorption {lam t B k s X Y D : ℝ}
    (hlam : 0 < lam) (ht : 0 < t) (hk : 0 < k)
    (hrel : k * lam ^ 2 * t = lam ^ 2 * t + B ^ 2)
    (hX : lam * t ≤ X) (hY : lam * s ^ 2 ≤ Y) (hD : -B * s ≤ D) :
    k * lam * t ≤ 2 * k * X + 4 * k ^ 2 * Y + 2 * k * D := by
  have hyoung : 2 * k * B * s ≤ 2 * k ^ 2 * lam * s ^ 2 + B ^ 2 / (2 * lam) := by
    have hd : 0 < 2 * lam := by positivity
    suffices hh : 2 * k * B * s - 2 * k ^ 2 * lam * s ^ 2 ≤ B ^ 2 / (2 * lam) by
      linarith only [hh]
    apply (le_div_iff₀ hd).mpr
    nlinarith only [(sq_nonneg (2 * k * lam * s - B))]
  have hmargin : B ^ 2 / (2 * lam) ≤ k * lam * t := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hrel, sq_nonneg B, hlam, ht]
  have hsquare : 0 ≤ 2 * k ^ 2 * lam * s ^ 2 := by positivity
  linarith only [(mul_le_mul_of_nonneg_left hX (show 0 ≤ 2 * k by positivity)), (mul_le_mul_of_nonneg_left hY (show 0 ≤ 4 * k ^ 2 by positivity)), (mul_le_mul_of_nonneg_left hD (show 0 ≤ 2 * k by positivity)), hyoung, hmargin, hsquare]

/-- One stationary profile works against *every* matrix and drift with these bounds.
The differential inequality is global, including outside the ellipsoid. -/
theorem universal_ellipsoid_barrier {d : ℕ} (hd : 0 < d) {Q : PDE.Mat d} (hQ : Q.PosDef)
    (lam M B : ℝ) (hlam : 0 < lam) (hM : 0 ≤ M) : ∃ q : PDE.Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) q ∧ (∀ y, PDE.vecDot y (Q *ᵥ y) ≤ 1 → 0 ≤ q y) ∧
      (∀ y, PDE.vecDot y (Q *ᵥ y) = 1 → q y = 0) ∧
      ∀ (A : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (z : TimeVelocity d),
        lam • (1 : PDE.Mat d) ≤ A z.1 z.2 → PDE.vecEuclideanNorm (b z.1 z.2) ≤ B →
        scalarParabolicZeroOrderOperator A b (fun _ _ => 0) (fun p => q p.2) z ≤ -M := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have ht : 0 < Q.trace := hQ.trace_pos
  let k := 1 + B ^ 2 / (lam ^ 2 * Q.trace)
  let C := M / (k * lam * Q.trace)
  let f := fun y => C *
    (Real.exp k - Real.exp (k * PDE.vecDot y (Q *ᵥ y)))
  have hk : 0 < k := by dsimp [k]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hrel : k * lam ^ 2 * Q.trace = lam ^ 2 * Q.trace + B ^ 2 := by
    dsimp [k]
    field_simp
  have hCM : C * (k * lam * Q.trace) = M := div_mul_cancel₀ M (by positivity)
  refine ⟨f,contDiff_const.mul (contDiff_const.sub (contDiff_scaled_quadratic Q k).exp),?_,?_,?_⟩
  · intro y hy; apply mul_nonneg hC
    exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by nlinarith only [hy,hk]))
  · intro y hy; simp [f,hy]
  · intro A b z hz hb
    let p := Q *ᵥ z.2
    let s := PDE.vecEuclideanNorm p
    have hs := PDE.vecEuclideanNorm_nonneg p
    have hy := vecDot_mulVec_lower_of_loewner (hz) p
    rw [← PDE.vecEuclideanNorm_sq] at hy
    have hd' : -B * s ≤ PDE.vecDot (b z.1 z.2) p := by
      linarith [PDE.abs_vecDot_le_vecEuclideanNorm_mul (b z.1 z.2) p, mul_le_mul_of_nonneg_right (hb) hs, neg_abs_le (PDE.vecDot (b z.1 z.2) p)]
    have hbr := drift_absorption hlam ht hk hrel (contraction_lower hQ (hz)) hy hd'
    have hq0 : 0 ≤ PDE.vecDot z.2 (Q *ᵥ z.2) := by
      exact hQ.posSemidef.dotProduct_mulVec_nonneg z.2
    have hprod := mul_le_mul_of_nonneg_left hbr (mul_nonneg hC (Real.exp_pos (k * PDE.vecDot z.2 (Q *ᵥ z.2))).le)
    have hex := mul_le_mul_of_nonneg_left (Real.one_le_exp (mul_nonneg hk.le hq0)) (mul_nonneg hC
      (by positivity : 0 ≤ k * lam * Q.trace))
    rw [show C * (k * lam * Q.trace) * 1 = M by rw [mul_one, hCM]] at hex
    rw [scalarOperator_exp_quadratic Q hQ.isHermitian.isSymm]
    nlinarith only [hprod, hex]

/-- A smooth ellipsoid barrier controls the backward operator with bounded drift. -/
theorem exists_ellipsoid_drift_barrier {d : ℕ} (hd : 0 < d)
    {Q : PDE.Mat d} (hQ : Q.PosDef) (a T lam M B : ℝ)
    (hlam : 0 < lam) (hM : 0 ≤ M)
    (A : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (hlo : ∀ z ∈ scalarParabolicClosedCylinder a T (openEllipsoid Q),
      lam • (1 : PDE.Mat d) ≤ A z.1 z.2)
    (hb : ∀ z ∈ scalarParabolicClosedCylinder a T (openEllipsoid Q),
      PDE.vecEuclideanNorm (b z.1 z.2) ≤ B) :
    ∃ q : PDE.Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) q ∧
      (∀ y ∈ closure (openEllipsoid Q), 0 ≤ q y) ∧
      (∀ y ∈ frontier (openEllipsoid Q), q y = 0) ∧
      ∀ z ∈ scalarParabolicClosedCylinder a T (openEllipsoid Q),
        scalarParabolicZeroOrderOperator A b (fun _ _ => 0)
          (fun p => q p.2) z ≤ -M := by
  obtain ⟨q,hq,hpos,hzero,hL⟩ := universal_ellipsoid_barrier hd hQ lam M B hlam hM
  obtain ⟨_,hcl,hfront⟩ := openEllipsoid_geometry hQ
  exact ⟨q,hq,fun y hy => hpos y (by rwa [hcl] at hy), fun y hy => hzero y (by rwa [hfront] at hy),
    fun z hz => hL A b z (hlo z hz) (hb z hz)⟩

end HypoellipticAleksandrov.KineticAleksandrov.Lieberman
