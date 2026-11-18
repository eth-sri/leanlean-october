module
public import OAI.NumberTheory.DirichletL.Inversion.InitialLargeFourier
public import OAI.NumberTheory.DirichletL.Descent.CompleteMarkedPool

@[expose] public section

namespace OAI

noncomputable section

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialCompletePool
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialLargePool InverseInitialCommonTuples InverseInitialEnergyCallerWindow
local notation "Eis"=>ActualEisensteinCubic.O

theorem original_column_norm_bound (S:Finset (Ideal Eis)){P j c:Ideal Eis}
    (hP:Admissible P)(hj:j∣P)(hc:c∈columns S P j) :
    c.absNorm≤S.sup Ideal.absNorm*P.absNorm := by
  obtain ⟨hcs,hcj,hres,hnS⟩ := (mem_columns hP.2.1 hj).mp hc
  have hjpos := Nat.one_le_iff_ne_zero.mpr
    (fun h=>((admissible_of_dvd hP hj).1) (Ideal.absNorm_eq_zero_iff.mp h))
  have hPN := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (fun h=>hP.1 (Ideal.absNorm_eq_zero_iff.mp h)))
    (map_dvd Ideal.absNorm (idealQuotient_dvd hj))
  calc
    c.absNorm≤j.absNorm*c.absNorm := Nat.le_mul_of_pos_left _ hjpos
    _=(reconstruct P j c).absNorm*(residual P j).absNorm := (norm_reconstruct hres).symm
    _≤_ := Nat.mul_le_mul (Finset.le_sup hnS) hPN

end SevenEighths.InverseInitialCompletePool

end

end OAI
