module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarConstruction
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarPositionWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarVelocityWeak
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileHomogeneousBounds
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarCancellation
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarHessianScaling
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarJetFields
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarJetFormulas
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarNormalized
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarRescaled
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileWeak
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarContinuity
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarIntegrability
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.GeometryHomogeneity
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileBounds
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarClassical
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarNativeEquation
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarNegativeJets
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarMeasure
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarWeakSlice

/-!
# Full Appendix C scalar profile

The literal Kummer construction satisfies the complete native one-dimensional interface.
The connection and differentiated tail estimates are proved upstream; no analytic package
is assumed by the exported existence theorem.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set
open Filter Asymptotics
open scoped Topology ContDiff

/- The actual Appendix C scalar profile satisfies the complete branch interface. -/
theorem counterProfileOne_exists (alpha ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    CounterProfileOneStatement alpha := by
  let gamma : ScalarGamma := ⟨alpha / 3, by constructor <;> linarith⟩
  have hga : 3 * gamma.1 = alpha := by dsimp only [gamma]; ring
  obtain ⟨Lam, hLam, hmatch⟩ := exists_matching_ratio gamma.1 gamma.2.1 gamma.2.2
  have hp := lt_trans zero_lt_one hLam
  obtain ⟨c, C0, hc, hcC, hcomp⟩ := scalarProfile_comparison gamma Lam hp hmatch
  obtain ⟨Cg, hCg, hgrad⟩ : ∃ C : ℝ, 0 < C ∧ ∀ q : XV 1, q ≠ 0 → PDE.vecEuclideanNorm (scalarGv gamma Lam q) ≤
      C * Real.rpow (rho q) (3 * gamma.1 - 1) := by
    obtain ⟨C, hC, hbound⟩ := homogeneous_component_bound (fun q => scalarGv gamma Lam q 0)
      (3 * gamma.1 - 1)
      (fun r hr q => congrArg (fun w => w 0) (scalarGv_homogeneous gamma Lam r hp hr q))
      (by
        intro K hK hz
        obtain ⟨M, hM⟩ := scalarJets_compact_bound gamma Lam hp hmatch K hK hz
        exact ⟨M, fun q hq => by simpa only [scalar_vec_norm] using (hM q hq).2.1⟩)
    refine ⟨C, hC, ?_⟩
    intro q hq
    rw [scalar_vec_euclidean_norm]
    exact hbound q hq
  let C : ℝ := max C0 Cg
  have hC0 : C0 ≤ C := le_max_left _ _
  have hCgC : Cg ≤ C := le_max_right _ _
  have _h_xinl_0 : ∀ᵐ q ∂volume, matrixContraction (scalarProfileCoefficient Lam q) (scalarHess gamma Lam q) = PDE.vecDot q.2 (scalarGx gamma Lam q) := by
    have _h_xinl_0 : ∀ᵐ q ∂volume,
        matrixContraction (scalarProfileCoefficient Lam q) (dvv (scalarProfile gamma Lam) q) =
          PDE.vecDot q.2 (dx (scalarProfile gamma Lam) q) := by
      filter_upwards [coordinates_ne_zero_ae 1 (by omega)] with q hq
      apply scalarProfile_equation_off_axis gamma Lam hp q
      intro hz
      apply hq.1
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact hz
    filter_upwards [scalarJets_eq_ae gamma Lam, _h_xinl_0]
      with q hj he
    rw [hj.1, hj.2.2]
    exact he
  refine ⟨Lam, c, C, scalarProfile gamma Lam, scalarGx gamma Lam, scalarGv gamma Lam,
    scalarHess gamma Lam, hLam, hc, hCg.trans_le hCgC,
    scalarProfile_continuous gamma Lam hp hmatch, scalarProfile_zero gamma Lam, ?_, ?_,
    measurable_scalarGx gamma Lam, measurable_scalarGv gamma Lam,
    measurable_scalarHess gamma Lam, scalarJets_eq_ae gamma Lam,
    _h_xinl_0, ?_, scalarJets_compact_bound gamma Lam hp hmatch,
    ?_, ?_, ?_⟩
  · intro r hr q
    simpa only [hga] using scalarProfile_homogeneous gamma Lam r hr q
  · intro q
    have hh := hcomp q
    rw [hga] at hh
    exact ⟨hh.1, hh.2.trans (mul_le_mul_of_nonneg_right hC0
      (Real.rpow_nonneg (rho_nonneg q) alpha))⟩
  · intro q hq
    have hh := hgrad q hq
    rw [hga] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hCgC
      (Real.rpow_nonneg (rho_nonneg q) (alpha - 1)))
  · intro r hr q
    simpa only [hga] using And.intro (scalarGx_homogeneous gamma Lam r hp hr q)
      (And.intro (scalarGv_homogeneous gamma Lam r hp hr q)
        (scalarHess_homogeneous gamma Lam r hp hr q))
  · intro test ht hs _hz
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      have ht : ContDiff ℝ 1 test := (ht.of_le (by norm_num))
      apply scalar_position_ibp _ _ (scalarProfile_continuous gamma Lam hp hmatch)
        ((scalarJets_locallyIntegrable gamma Lam hp hmatch).1 0)
      · intro q hq
        exact (scalarProfile_contDiffAt_off_axis gamma Lam hp q hq).differentiableAt
          (by norm_num)
      · intro q hq
        simp only [scalarGx, hq, ↓reduceIte, dx]
      · exact ht
      · exact hs
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact scalarProfile_velocity_weak gamma Lam hp hmatch test
        (ht.of_le (by norm_num)) hs
    · intro i k
      have hi : i = 0 := Subsingleton.elim _ _
      have hk : k = 0 := Subsingleton.elim _ _
      subst i
      subst k
      have hjet := scalarJets_locallyIntegrable gamma Lam hp hmatch
      have hfirst := scalarProfile_velocity_weak gamma Lam hp hmatch
        (fun q => dv test q 0) (contDiff_dv_test test ht 0)
        (hs.fderiv_apply ℝ (0, Pi.single 0 1))
      have hsecond : (∫ q, scalarGv gamma Lam q 0 * dv test q 0) =
          -(∫ q, scalarHess gamma Lam q 0 0 * test q) := by
        apply scalar_velocity_ibp _ _ (hjet.2.1 0) (hjet.2.2 0 0)
        · intro q hq
          exact scalarGv_differentiableAt gamma Lam hp q hq 0
        · intro q hq
          exact (scalarHess_eq_velocity_derivative gamma Lam q hq 0 0).symm
        · exact ht.of_le (by norm_num)
        · exact hs
      change (∫ q, scalarProfile gamma Lam q * dvv test q 0 0) =
        -(∫ q, scalarGv gamma Lam q 0 * dv test q 0) at hfirst
      simpa only [hsecond, neg_neg] using hfirst
  · intro q hq
    exact (scalarProfile_contDiffAt_off_axis gamma Lam hp q hq).contDiffWithinAt

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
