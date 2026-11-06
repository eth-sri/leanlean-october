module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.MassRepresentationApproximation

/-! # The compact approximation error fits the actual quadratic growth barrier -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set Parabolic

/- The growth barrier dominates the squared supremum norm used only for compact exhaustion. -/
theorem mass_trace_probe_weighted {d } (Lam a T : ℝ) (v₀ : PDE.Vec d) (R )
    (u φ : KineticPoint d → ℝ) (M L ε ) (hε : 0 ≤ ε)
    (hb : ∀ P ∈ localClosedStrip a T v₀ R, |u P| ≤ M)
    (hφ : ∀ P, |φ P| ≤ M + ε)
    (hclose : ∀ P ∈ localClosedStrip a T v₀ R, ‖P.position‖ ≤ L → |φ P - u P| ≤ ε)
    (hL : 0 ≤ L) (hsize : 2 * M + ε ≤ ε * L ^ 2) :
    ∀ P ∈ localClosedStrip a T v₀ R,
      |φ P - u P| ≤ ε * massGrowthBarrier Lam T P := by
  intro P hP
  by_cases hp : ‖P.position‖ ≤ L
  · exact (hclose P hP hp).trans (le_mul_of_one_le_right hε
      ((le_add_of_nonneg_right (PDE.vecNormSq_nonneg P.position)).trans
        (massGrowthBarrier_lower Lam T P hP.2.1)))
  · have hlp : L ^ 2 ≤ ‖P.position‖ ^ 2 :=
      (sq_le_sq₀ hL (norm_nonneg _)).mpr (not_le.mp hp).le
    have _h_inl_6 : ‖P.position‖ ^ 2 ≤ massGrowthBarrier Lam T P := by
      have hP := hP.2.1
      have hn := sq_le_sq₀ (norm_nonneg P.position) (PDE.vecEuclideanNorm_nonneg P.position)
        |>.mpr (PDE.norm_le_vecEuclideanNorm P.position)
      rw [PDE.vecEuclideanNorm_sq] at hn
      exact hn.trans ((le_add_of_nonneg_left zero_le_one).trans
        (massGrowthBarrier_lower Lam T P hP))
    exact ((abs_sub (φ P) (u P)).trans (add_le_add (hφ P) (hb P hP))).trans
      ((by linarith only [hsize] : M + ε + M ≤ ε * L ^ 2).trans
        (mul_le_mul_of_nonneg_left (hlp.trans _h_inl_6)
          hε))

/- A concrete growing aperture meets the weighted-error size requirement. -/
end HypoellipticAleksandrov.KineticAleksandrov.LocalA
