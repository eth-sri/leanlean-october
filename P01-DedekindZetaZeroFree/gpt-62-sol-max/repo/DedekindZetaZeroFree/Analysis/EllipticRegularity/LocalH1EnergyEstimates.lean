module

public import DedekindZetaZeroFree.Analysis.Sobolev.Restriction.IntegerOrderWeakDerivatives
public import DedekindZetaZeroFree.Analysis.Sobolev.WeakDerivatives.FirstOrderSmoothProducts
public import DedekindZetaZeroFree.Analysis.EllipticEquations.DivergenceForm.H1TestContinuity
public import DedekindZetaZeroFree.Analysis.EllipticEquations.EnergyEstimates.CutoffQuadraticForms
public import DedekindZetaZeroFree.Analysis.EllipticEquations.DivergenceForm.ClassicalToWeakSolutions
public import DedekindZetaZeroFree.Analysis.Sobolev.LocalEmbeddingAndSmoothRepresentatives

@[expose] public section

noncomputable section

set_option maxHeartbeats 800000

namespace DedekindZetaZeroFree.KPContLocalEnergy

open MeasureTheory
open KPContLocalNorm

open SobolevEnergyEstimates (restrictSobolev)

export SobolevEnergyEstimates.Raw (zeroIndex firstIndex value gradient Coefficients
  divergenceOperator WeakEquation Represents RepresentsClassicalDerivatives functionL2Norm)

def WeakEnergyEstimate {n : ℕ} (inner outer : LocalBall n)
    {cρ Cρ κ Λ : ℝ} (D : Coefficients outer cρ Cρ κ Λ) (M C : ℝ) : Prop :=
  ∀ (hsub : inner.carrier ⊆ outer.carrier) (z : ℂ), ‖z‖ ≤ M →
    ∀ (u : IntegerSobolev outer 1) (h : BallL2 outer), WeakEquation D z u h →
      (restrictSobolev hsub u).sobolevNorm ≤ C * (‖value u‖ + ‖h‖)

end DedekindZetaZeroFree.KPContLocalEnergy

namespace DedekindZetaZeroFree

open MeasureTheory KPContLocalNorm KPContLocalEnergy KPContLocalEnergy.SobolevEnergyEstimates

theorem kp_cont_local_energy_h1 (n : ℕ) (hn : 0 < n)
    (r R cρ Cρ κ Λ M : ℝ) (hr : 0 < r) (hrR : r < R)
    (hcρ : 0 < cρ) (hκ : 0 < κ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (inner outer : LocalBall n),
      inner.center = outer.center → inner.radius = r → outer.radius = R →
      ∀ D : Coefficients outer cρ Cρ κ Λ,
        WeakEnergyEstimate inner outer D M C := by
  obtain ⟨C, hC, hcutoff⟩ :=
    cutoff_quadratic_form_bound n hn r R cρ Cρ κ Λ M hr hrR hcρ hκ hM
  refine ⟨C, hC, ?_⟩
  intro inner outer hcenter hir hor D hsub z hz u h heq
  obtain ⟨η, _, hηenergy⟩ := hcutoff inner outer hcenter hir hor
  obtain ⟨w, hwvalue, hwgradient⟩ := multiply_smooth_compact outer η u
  have hwsupport : ∀ᵐ x ∂volume.restrict outer.carrier,
      x ∉ tsupport (fun y => η y) → value w x = 0 := by
    filter_upwards [hwvalue] with x hx
    intro hnot
    rw [hx, image_eq_zero_of_notMem_tsupport hnot]
    simp
  obtain ⟨φ, hφ⟩ := approximate_compact_integerSobolev outer w
    (tsupport (fun y => η y)) η.hasCompactSupport η.tsupport_subset hwsupport
  have htest := weakEquation_of_test_limit outer cρ Cρ κ Λ hcρ hκ D z u h heq w φ hφ
  have hbound := hηenergy D z hz u h w hwvalue hwgradient htest
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hC.le (by positivity))).mp
  change (restrictSobolev hsub u).sobolevNorm ^ 2 ≤ _
  rw [IntegerSobolev.sobolevNorm_sq, restrictSobolev_normSq_eq_integral]
  exact hbound

end DedekindZetaZeroFree

end
