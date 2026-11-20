module

public import DedekindZetaZeroFree.Analysis.EllipticRegularity.LocalH1EnergyEstimates

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalEnergy

open KPContLocalNorm MeasureTheory

alias coordinateDerivativeList_tsupport_subset := DedekindZetaZeroFree.WeakJets.Raw.list_tsupport_subset

section

variable {n : ℕ} {inner outer : LocalBall n} (hsub : inner.carrier ⊆ outer.carrier) (f : BallL2 outer)

def restrictBallL2 : BallL2 inner :=
  ((Lp.memLp f).mono_measure (Measure.restrict_mono hsub le_rfl)).toLp f

theorem restrictBallL2_ae :
    ∀ᵐ x ∂volume.restrict inner.carrier, restrictBallL2 hsub f x = f x :=
  MemLp.coeFn_toLp _

theorem norm_restrictBallL2_le :
    ‖restrictBallL2 hsub f‖ ≤ ‖f‖ := by
  rw [restrictBallL2, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top
    (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl))

end

private alias integral_mul_test_restrict := SobolevEnergyEstimates.IntegerOrderWeakDerivatives.integral_mul_test_restrict

variable {n k : ℕ} {inner outer : LocalBall n} (hsub : inner.carrier ⊆ outer.carrier)

theorem isWeakDerivative_restrict (α : MultiIndex n k)
    (f g : BallL2 outer) (hfg : IsWeakDerivative outer α f g) :
    IsWeakDerivative inner α (restrictBallL2 hsub f) (restrictBallL2 hsub g) := by apply @SobolevEnergyEstimates.isWeakDerivative_restrict <;> assumption

def restrictSobolev (u : IntegerSobolev outer k) :
    IntegerSobolev inner k where
  derivatives α := restrictBallL2 hsub (u.derivatives α)
  weak_derivatives α := isWeakDerivative_restrict hsub α _ _ (u.weak_derivatives α)

theorem restrictSobolev_represents (u : IntegerSobolev outer k) :
    Represents (restrictSobolev hsub u) (fun x => value u x) :=
  restrictBallL2_ae hsub _

theorem sobolevNorm_restrictSobolev_le (u : IntegerSobolev outer k) :
    (restrictSobolev hsub u).sobolevNorm ≤ u.sobolevNorm := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro α _
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_restrictBallL2_le hsub _) 2

end DedekindZetaZeroFree.KPContLocalEnergy

end
