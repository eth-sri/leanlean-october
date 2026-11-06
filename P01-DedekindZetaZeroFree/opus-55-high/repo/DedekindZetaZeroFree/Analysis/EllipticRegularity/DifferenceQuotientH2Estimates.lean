module

public import DedekindZetaZeroFree.Analysis.WeakH2.SecondWeakDerivatives

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalDifference

open KPContLocalNorm KPContLocalEnergy

def BoundedFirstDerivatives {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) (L : ℝ) : Prop :=
  ∀ x ∈ B.carrier, ∀ i j k : Fin n,
    ‖fderiv ℝ (fun y => D.density y * D.matrix y i j) x
      (EuclideanSpace.single k 1)‖ ≤ L

def WeakH2Estimate {n : ℕ} (inner outer : LocalBall n)
    {cρ Cρ κ Λ : ℝ} (D : Coefficients outer cρ Cρ κ Λ) (M C : ℝ) : Prop :=
  ∀ (z : ℂ), ‖z‖ ≤ M → ∀ (u : IntegerSobolev outer 1) (h : BallL2 outer),
    WeakEquation D z u h → ∃ v : IntegerSobolev inner 2,
      Represents v (fun x => value u x) ∧
      v.sobolevNorm ≤ C * (u.sobolevNorm + ‖h‖)

end DedekindZetaZeroFree.KPContLocalDifference

namespace DedekindZetaZeroFree

open KPContLocalNorm KPContLocalEnergy KPContLocalDifference

theorem kp_cont_local_difference_h2 (n : ℕ) (hn : 0 < n)
    (r R cρ Cρ κ Λ L M : ℝ) (hr : 0 < r) (hrR : r < R)
    (hcρ : 0 < cρ) (hκ : 0 < κ) (hL : 0 ≤ L) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (inner outer : LocalBall n),
      inner.center = outer.center → inner.radius = r → outer.radius = R →
      ∀ D : Coefficients outer cρ Cρ κ Λ,
        BoundedFirstDerivatives D L → WeakH2Estimate inner outer D M C := by
  classical
  obtain ⟨K, hK, hest⟩ := WeakH2.coercive_difference_estimate n hn
    r R cρ Cρ κ Λ L M hr hrR hcρ hκ hL hM
  refine ⟨Real.sqrt (1 + (n : ℝ) ^ 2 * K ^ 2), by positivity, ?_⟩
  intro inner outer hc hir hor D hD z hz u h heq
  let mid : LocalBall n := ⟨hn, outer.center, (r + R) / 2, by linarith⟩
  have hgap : inner.radius < outer.radius := by rw [hir, hor]; exact hrR
  have hsub : inner.carrier ⊆ outer.carrier := by
    rw [LocalBall.carrier, LocalBall.carrier, hc]
    exact Metric.ball_subset_ball hgap.le
  have hsm : inner.carrier ⊆ mid.carrier := by
    change Metric.ball inner.center inner.radius ⊆ Metric.ball outer.center ((r + R) / 2)
    rw [hc, hir]
    exact Metric.ball_subset_ball (by linarith)
  obtain ⟨η, hηone, hη⟩ := hest inner mid outer hc rfl hir rfl hor
  let Dr : KPContLocalEnergy.SobolevEnergyEstimates.Raw.Coefficients outer cρ Cρ κ Λ :=
    { density := D.density
      matrix := D.matrix
      density_smooth := D.density_smooth
      matrix_smooth := D.matrix_smooth
      density_bounds := D.density_bounds
      symmetric := D.symmetric
      ellipticity := D.ellipticity
      upper_bound := D.upper_bound }
  let A : ℝ := K * (u.sobolevNorm + ‖h‖)
  have hA : 0 ≤ A := by dsimp [A, IntegerSobolev.sobolevNorm]; positivity
  have hpair := fun j k => WeakH2.difference_bound_to_test_pairing inner outer hc hgap
    (gradient u j) k ((R - r) / 8) A (by linarith) hA
  have hbound : ∀ (j k : Fin n) (t : ℝ), t ≠ 0 → |t| < (R - r) / 8 →
      MeasureTheory.MemLp (WeakH2.differenceQuotient k t (WeakH2.zeroExtension (gradient u j)))
        2 (MeasureTheory.volume.restrict inner.carrier) ∧
      (∫ x in inner.carrier, ‖WeakH2.differenceQuotient k t
        (WeakH2.zeroExtension (gradient u j)) x‖ ^ 2) ≤ A ^ 2 := by
    intro j k t ht hts
    obtain ⟨hm, hb⟩ := hη Dr hD z hz u h heq k t ht hts
    change (∀ j : Fin n, MeasureTheory.MemLp (fun x => (η x : ℂ) *
      WeakH2.differenceQuotient k t (WeakH2.zeroExtension (gradient u j)) x)
      2 (MeasureTheory.volume.restrict mid.carrier)) at hm
    change (∑ j : Fin n, ∫ x in mid.carrier, ‖(η x : ℂ) *
      WeakH2.differenceQuotient k t (WeakH2.zeroExtension (gradient u j)) x‖ ^ 2)
      ≤ K ^ 2 * (u.sobolevNorm + ‖h‖) ^ 2 at hb
    let f := fun x => (η x : ℂ) * WeakH2.differenceQuotient k t
      (WeakH2.zeroExtension (gradient u j)) x
    have hfe : f =ᵐ[MeasureTheory.volume.restrict inner.carrier]
        WeakH2.differenceQuotient k t (WeakH2.zeroExtension (gradient u j)) := by
      filter_upwards [MeasureTheory.ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      simp [f, hηone x hx]
    refine ⟨((hm j).mono_measure (MeasureTheory.Measure.restrict_mono hsm le_rfl)).ae_eq hfe, ?_⟩
    have hfi : (∫ x in inner.carrier, ‖f x‖ ^ 2) =
        ∫ x in inner.carrier, ‖WeakH2.differenceQuotient k t
          (WeakH2.zeroExtension (gradient u j)) x‖ ^ 2 :=
      MeasureTheory.integral_congr_ae (hfe.fun_comp (fun z : ℂ => ‖z‖ ^ 2))
    rw [← hfi]
    calc
      _ ≤ ∫ x in mid.carrier, ‖f x‖ ^ 2 := by
        have hi : MeasureTheory.IntegrableOn (fun x => ‖f x‖ ^ 2) mid.carrier
            MeasureTheory.volume := (hm j).integrable_norm_pow (by decide)
        exact MeasureTheory.setIntegral_mono_set hi
          (Filter.Eventually.of_forall fun x => sq_nonneg _) (Filter.Eventually.of_forall hsm)
      _ ≤ ∑ i : Fin n, ∫ x in mid.carrier,
          ‖(η x : ℂ) * WeakH2.differenceQuotient k t
            (WeakH2.zeroExtension (gradient u i)) x‖ ^ 2 :=
        Finset.single_le_sum (f := fun i : Fin n => ∫ x in mid.carrier,
          ‖(η x : ℂ) * WeakH2.differenceQuotient k t
            (WeakH2.zeroExtension (gradient u i)) x‖ ^ 2)
          (fun i _ => MeasureTheory.integral_nonneg (fun x => sq_nonneg _))
          (Finset.mem_univ j)
      _ ≤ A ^ 2 := by simpa only [A, mul_pow] using hb
  obtain ⟨v, hv, hvn⟩ := WeakH2.assemble_second_weak_derivatives inner outer hsub u A hA
    (fun j k => hpair j k (hbound j k))
  refine ⟨v, hv, ?_⟩
  have hu0 : 0 ≤ u.sobolevNorm := Real.sqrt_nonneg _
  have hv0 : 0 ≤ v.sobolevNorm := Real.sqrt_nonneg _
  have hs : 0 ≤ 1 + (n : ℝ) ^ 2 * K ^ 2 := by positivity
  apply (sq_le_sq₀ hv0 (mul_nonneg (Real.sqrt_nonneg _) (by positivity))).mp
  rw [v.sobolevNorm_sq, mul_pow, Real.sq_sqrt hs]
  have hu := u.sobolevNorm_sq
  have hsq : u.normSq ≤ (u.sobolevNorm + ‖h‖) ^ 2 := by nlinarith [norm_nonneg h]
  calc
    v.normSq ≤ u.normSq + (n : ℝ) ^ 2 * A ^ 2 := hvn
    _ ≤ (u.sobolevNorm + ‖h‖) ^ 2 + (n : ℝ) ^ 2 * A ^ 2 := add_le_add hsq le_rfl
    _ = (1 + (n : ℝ) ^ 2 * K ^ 2) * (u.sobolevNorm + ‖h‖) ^ 2 := by dsimp [A]; ring

end DedekindZetaZeroFree

noncomputable section
open MeasureTheory
namespace DedekindZetaZeroFree.KPContLocalDifference.WeakRecovery
open KPContLocalNorm

end DedekindZetaZeroFree.KPContLocalDifference.WeakRecovery

noncomputable section
namespace DedekindZetaZeroFree.KPContLocalDifference.WeakRecovery
