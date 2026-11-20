module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarComparison
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarCancellation
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarPositionWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarVelocityWeak
import Mathlib.Tactic

/-!
# Full Appendix C scalar profile

The Kummer construction gives a whole-carrier weak profile in dimension one.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set
open scoped MatrixOrder

/-- Scalar multiples of the identity preserve the scalar order. -/
private theorem scalar_identity_le {d : ℕ} (a b : ℝ) (hab : a ≤ b) :
    a • (1 : PDE.Mat d) ≤ b • (1 : PDE.Mat d) := by
  apply Matrix.le_iff.mpr
  simpa only [sub_smul] using
    (Matrix.PosSemidef.one (n := Fin d) (R := ℝ)).smul (sub_nonneg.mpr hab)

/-- The literal scalar coefficient is entrywise measurable. -/
private theorem measurable_scalarProfileCoefficient (Lam : ℝ) (i k : Fin 1) :
    Measurable (fun q => scalarProfileCoefficient Lam q i k) := by
  have hm : Measurable (fun q : XV 1 => q.1 0 * q.2 0) :=
    ((measurable_pi_apply 0).comp measurable_fst).mul
      ((measurable_pi_apply 0).comp measurable_snd)
  have hs : MeasurableSet {q : XV 1 | q.1 0 * q.2 0 < 0} :=
    measurableSet_lt hm measurable_const
  exact (measurable_const.ite hs measurable_const).mul measurable_const

/-- The scalar coefficient has the source's uniform ellipticity bounds everywhere. -/
private theorem scalarProfileCoefficient_order (Lam : ℝ) (hLam : 1 < Lam) (q : XV 1) :
    (1 : ℝ) • (1 : PDE.Mat 1) ≤ scalarProfileCoefficient Lam q ∧
      scalarProfileCoefficient Lam q ≤ Lam • (1 : PDE.Mat 1) := by
  unfold scalarProfileCoefficient
  split_ifs
  · exact ⟨scalar_identity_le 1 Lam hLam.le, le_refl _⟩
  · exact ⟨le_refl _, scalar_identity_le 1 Lam hLam.le⟩


/-- The scalar profile satisfies the shared interface with its global weak jets. -/
theorem counterProfileOne_exists (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    CounterProfileStatement 1 alpha := by
  let gamma : ScalarGamma := ⟨alpha / 3, by constructor <;> linarith⟩
  have hga : 3 * gamma.1 = alpha := by dsimp only [gamma]; ring
  obtain ⟨Lam, hLam, hmatch⟩ := exists_matching_ratio gamma.1 gamma.2.1 gamma.2.2
  have hp : 0 < Lam := lt_trans zero_lt_one hLam
  obtain ⟨c, C0, hc, hcC, hcomp⟩ := scalarProfile_comparison gamma Lam hp hmatch
  obtain ⟨Cg, hCg, hgrad⟩ := scalarGv_gauge_bound gamma Lam hp hmatch
  let C : ℝ := max C0 Cg
  have hC0 : C0 ≤ C := le_max_left _ _
  have hCgC : Cg ≤ C := le_max_right _ _
  obtain ⟨hx, hv, hh⟩ := scalarJets_locallyIntegrable gamma Lam hp hmatch
  refine ⟨1, Lam, c, C, scalarProfileCoefficient Lam, scalarProfile gamma Lam, scalarGx gamma Lam,
    scalarGv gamma Lam, scalarHess gamma Lam, ⟨zero_lt_one, hLam.le, hc, hCg.trans_le hCgC,
    measurable_scalarProfileCoefficient Lam, scalarProfileCoefficient_order Lam hLam,
    scalarProfile_continuous gamma Lam hp hmatch, scalarProfile_zero gamma Lam, ?_, ?_,
    measurable_scalarGx gamma Lam, measurable_scalarGv gamma Lam,
    measurable_scalarHess gamma Lam, scalarJets_eq_ae gamma Lam, scalarJets_equation_ae gamma Lam hp,
    ?_, scalarJets_compact_bound gamma Lam hp hmatch, hx, hv, hh, ?_,
    scalar_off_axis_ae.mono (scalarProfile_contDiffAt_off_axis gamma Lam hp)⟩⟩
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
  · intro test ht hs
    have hi (i : Fin 1) : i = 0 := Subsingleton.elim _ _
    have ht1 : ContDiff ℝ 1 test := ht.of_le (by norm_num)
    refine ⟨?_, ?_, ?_⟩
    · intro i
      simpa only [hi i] using scalarProfile_position_weak gamma Lam hp hmatch test ht1 hs
    · intro i
      simpa only [hi i] using scalarProfile_velocity_weak gamma Lam hp hmatch test ht1 hs
    · intro i k
      simpa only [hi i, hi k] using scalarProfile_hessian_weak gamma Lam hp hmatch test ht hs

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
