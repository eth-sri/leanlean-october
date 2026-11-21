module

public import DedekindZetaZeroFree.Analysis.EllipticRegularity.IntegerSobolevEstimates

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPContActualLocalSolutionFamily.CoefficientRestriction
open MeasureTheory KPContLocalNorm KPContLocalEnergy KPContLocalRegularity
open SobolevIteration SobolevIteration.Iteration
open SobolevEnergyEstimates (coordinateDerivative_memLp_of_closedBall coordinateDerivative_zeroIndex)

lemma larger_ball {n : ℕ} (A B : LocalBall n)
    (hAB : Metric.closedBall A.center A.radius ⊆ B.carrier) :
    ∃ C : LocalBall n, C.center = A.center ∧ A.radius < C.radius ∧
      Metric.closedBall C.center C.radius ⊆ B.carrier := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall A.center A.radius).exists_cthickening_subset_open
    Metric.isOpen_ball hAB
  rw [cthickening_closedBall hδ.le A.radius_pos.le] at hsub
  exact ⟨⟨A.dimension_pos, A.center, δ + A.radius, add_pos hδ A.radius_pos⟩,
    rfl, by dsimp; linarith, hsub⟩

private lemma wsr_local_all_sobolev {n : ℕ} (A : LocalBall n) {cρ Cρ κ Λ : ℝ}
    (D : Coefficients A cρ Cρ κ Λ) (hcρ : 0 < cρ) (hκ : 0 < κ) (z : ℂ)
    (u : IntegerSobolev A 1) (g : BallL2 A)
    (hw : WeakEquation D z u g)
    (h : Space n → ℂ) (hh : ContDiffOn ℝ (⊤ : ℕ∞) h A.carrier)
    (hgh : h =ᵐ[volume.restrict A.carrier] (fun x => g x)) :
    KPContLocalCubeEmbedding.LocallyAllIntegerSobolev A.carrier (fun x => value u x) := by
  intro A' hA' k
  obtain ⟨C, hcen, hr, hC⟩ := larger_ball A' A hA'
  have hCA' : A'.center = C.center := hcen.symm
  have hsub : C.carrier ⊆ A.carrier := Metric.ball_subset_closedBall.trans hC
  let DC := restrictCoefficients hsub D
  have hDC := restrictCoefficients_smooth hsub hC D
  let uC := restrictSobolev hsub u
  have hm (α : MultiIndex n k) := coordinateDerivative_memLp_of_closedBall C
    Metric.isOpen_ball hC hh α
  obtain ⟨q, hq⟩ := smooth_has_integerSobolev_data C h (hh.mono hsub) hm
  have hval : value q = restrictBallL2 hsub g := by
    apply Lp.ext
    have heq : (fun x => value q x) =ᵐ[volume.restrict C.carrier] h := by
      rw [show value q = q.derivatives (zeroIndex n k) from rfl, hq]
      simpa only [coordinateDerivative_zeroIndex] using (hm (zeroIndex n k)).coeFn_toLp
    filter_upwards [heq, ae_restrict_of_ae_restrict_of_subset hsub hgh,
      restrictBallL2_ae hsub g] with x hx hy hz
    exact hx.trans (hy.trans hz.symm)
  obtain ⟨K, _, he⟩ := kp_cont_local_regularity_iterate_fixed_coefficients n A' C
    hCA' hr cρ Cρ κ Λ ‖z‖ hcρ hκ (norm_nonneg _) DC hDC k
  obtain ⟨w, hwu, _⟩ := he z le_rfl uC q (hval ▸ restrictWeakEquation hsub D z u g hw)
  refine ⟨lowerSobolev (Nat.le_add_right k 2) w, ?_⟩
  have hA'C : A'.carrier ⊆ C.carrier := by
    rw [LocalBall.carrier, LocalBall.carrier, hCA']
    exact Metric.ball_subset_ball hr.le
  have hval' : (fun x => value uC x) =ᵐ[volume.restrict A'.carrier] (fun x => value u x) :=
    ae_restrict_of_ae_restrict_of_subset hA'C (restrictSobolev_represents hsub u)
  change (fun x => value u x) =ᵐ[volume.restrict A'.carrier]
    (fun x => value (lowerSobolev (Nat.le_add_right k 2) w) x)
  rw [lower_value]
  exact (Filter.EventuallyEq.trans hwu hval').symm

theorem weighted_smooth_representative {n : ℕ} (A : LocalBall n)
    {cρ Cρ κ Λ : ℝ} (D : Coefficients A cρ Cρ κ Λ)
    (hcρ : 0 < cρ) (hκ : 0 < κ)
    (z : ℂ) (v : IntegerSobolev A 1) (g : BallL2 A)
    (h : Space n → ℂ) (hh : ContDiffOn ℝ (⊤ : ℕ∞) h A.carrier)
    (hg : h =ᵐ[volume.restrict A.carrier] (fun p => g p))
    (heq : WeakEquation D z v g) :
    ∃ f : Space n → ℂ,
      ContDiffOn ℝ (⊤ : ℕ∞) f A.carrier ∧
        (f =ᵐ[volume.restrict A.carrier] (fun p => value v p)) := by
  obtain ⟨f, hf, hfu, _⟩ :=
    KPContLocalCubeEmbedding.locally_all_orders_smooth_representative A.dimension_pos
      A.carrier Metric.isOpen_ball (fun x => value v x)
      (wsr_local_all_sobolev A D hcρ hκ z v g heq h hh hg)
  exact ⟨f, hf, hfu⟩

end DedekindZetaZeroFree.KPContActualLocalSolutionFamily.CoefficientRestriction

end
