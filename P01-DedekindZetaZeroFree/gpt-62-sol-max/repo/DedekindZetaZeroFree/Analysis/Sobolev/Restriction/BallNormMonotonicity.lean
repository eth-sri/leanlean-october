module

public import DedekindZetaZeroFree.Analysis.EllipticRegularity.LocalH1EnergyEstimates

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalEnergy

open KPContLocalNorm MeasureTheory

export SobolevEnergyEstimates (coordinateDerivativeList_tsupport_subset restrictBallL2
  restrictBallL2_ae isWeakDerivative_restrict restrictSobolev)

theorem norm_restrictBallL2_le {n : ℕ} {inner outer : LocalBall n}
    (hsub : inner.carrier ⊆ outer.carrier) (f : BallL2 outer) :
    ‖restrictBallL2 hsub f‖ ≤ ‖f‖ := by
  rw [restrictBallL2, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top
    (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl))

theorem restrictSobolev_represents {n k : ℕ} {inner outer : LocalBall n}
    (hsub : inner.carrier ⊆ outer.carrier) (u : IntegerSobolev outer k) :
    Represents (restrictSobolev hsub u) (fun x => value u x) :=
  restrictBallL2_ae hsub _

theorem sobolevNorm_restrictSobolev_le {n k : ℕ} {inner outer : LocalBall n}
    (hsub : inner.carrier ⊆ outer.carrier) (u : IntegerSobolev outer k) :
    (restrictSobolev hsub u).sobolevNorm ≤ u.sobolevNorm := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro α _
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_restrictBallL2_le hsub _) 2

end DedekindZetaZeroFree.KPContLocalEnergy

end
