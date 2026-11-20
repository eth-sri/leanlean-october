module
public import DedekindZetaZeroFree.Analysis.Sobolev.Embedding.CompactMixedDerivativeBound

public import DedekindZetaZeroFree.Analysis.EllipticEquations.DivergenceForm.WeakSolutions

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalEnergy.SobolevEnergyEstimates

open MeasureTheory KPContLocalNorm Raw

private alias coordinateDerivativeList_tsupport_subset := DedekindZetaZeroFree.KPLocalCubeSobolevJets.CompactMixedDerivativeBound.mixed_support

 section

variable {n : ℕ} {inner outer : LocalBall n} (hsub : inner.carrier ⊆ outer.carrier) (f : BallL2 outer)

def restrictBallL2 : BallL2 inner :=
  ((Lp.memLp f).mono_measure (Measure.restrict_mono hsub le_rfl)).toLp f

private theorem restrictBallL2_ae :
    ∀ᵐ x ∂volume.restrict inner.carrier, restrictBallL2 hsub f x = f x :=
  MemLp.coeFn_toLp _

end

alias IntegerOrderWeakDerivatives.restrictBallL2_ae := restrictBallL2_ae

private theorem integral_mul_test_restrict {n : ℕ} {inner outer : LocalBall n}
    (hsub : inner.carrier ⊆ outer.carrier) (f : Space n → ℂ)
    (φ : TestFunction inner.toOpens ℂ ⊤) (l : List (Fin n)) :
    (∫ x in outer.carrier, f x * coordinateDerivativeList l (fun y => φ y) x) =
      ∫ x in inner.carrier, f x * coordinateDerivativeList l (fun y => φ y) x := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Metric.isOpen_ball.measurableSet hsub
  intro x hx
  have hnot : x ∉ tsupport (coordinateDerivativeList l (fun y => φ y)) := fun hx' => hx.2 (φ.tsupport_subset (coordinateDerivativeList_tsupport_subset l _ hx'))
  rw [image_eq_zero_of_notMem_tsupport hnot, mul_zero]

alias IntegerOrderWeakDerivatives.integral_mul_test_restrict := integral_mul_test_restrict

 section

variable {n k : ℕ} {inner outer : LocalBall n} (hsub : inner.carrier ⊆ outer.carrier)

theorem isWeakDerivative_restrict (α : MultiIndex n k)
    (f g : BallL2 outer) (hfg : IsWeakDerivative outer α f g) :
    IsWeakDerivative inner α (restrictBallL2 hsub f) (restrictBallL2 hsub g) := by
  intro φ
  have heq := hfg (⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hsub⟩)
  have hleft : (∫ x in inner.carrier, restrictBallL2 hsub f x * coordinateDerivative α (fun y => φ y) x) =
      ∫ x in inner.carrier, f x * coordinateDerivative α (fun y => φ y) x := by
    apply integral_congr_ae
    filter_upwards [restrictBallL2_ae hsub f] with x hx
    rw [hx]
  have hright : (∫ x in inner.carrier, restrictBallL2 hsub g x * φ x) =
      ∫ x in inner.carrier, g x * φ x := by
    apply integral_congr_ae
    filter_upwards [restrictBallL2_ae hsub g] with x hx
    rw [hx]
  rw [hleft, hright]
  change (∫ x in outer.carrier, f x * coordinateDerivative α (fun y => φ y) x) =
    (-1 : ℂ) ^ α.degree * (∫ x in outer.carrier, g x * φ x) at heq
  rw [coordinateDerivative, integral_mul_test_restrict hsub f φ α.directions,
    ← coordinateDerivative] at heq
  have hzero := integral_mul_test_restrict hsub g φ []
  simp only [coordinateDerivativeList] at hzero
  rw [hzero] at heq
  exact heq

 def restrictSobolev (u : IntegerSobolev outer k) :
    IntegerSobolev inner k where
  derivatives α := restrictBallL2 hsub (u.derivatives α)
  weak_derivatives α := isWeakDerivative_restrict hsub α _ _ (u.weak_derivatives α)

end

theorem restrict_integerSobolev {n k : ℕ} (inner outer : LocalBall n)
    (hsub : inner.carrier ⊆ outer.carrier) (u : IntegerSobolev outer k) :
    ∃ v : IntegerSobolev inner k,
      (∀ α : MultiIndex n k,
        ∀ᵐ x ∂volume.restrict inner.carrier, v.derivatives α x = u.derivatives α x) ∧
      v.normSq = ∑ α : MultiIndex n k,
        ∫ x in inner.carrier, ‖u.derivatives α x‖ ^ 2 := by
  let v := restrictSobolev hsub u
  have hae : ∀ α : MultiIndex n k,
      ∀ᵐ x ∂volume.restrict inner.carrier, v.derivatives α x = u.derivatives α x :=
    fun α => restrictBallL2_ae hsub (u.derivatives α)
  refine ⟨v, hae, ?_⟩
  rw [← v.sobolevNorm_sq, v.sobolevNorm_sq_eq_integral]
  apply Finset.sum_congr rfl
  intro α _
  apply integral_congr_ae
  filter_upwards [hae α] with x hx
  rw [hx]

end DedekindZetaZeroFree.KPContLocalEnergy.SobolevEnergyEstimates

end
