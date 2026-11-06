module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Inversion.InitialLargeFourier
public import OAI.NumberTheory.DirichletL.Descent.CompleteMarkedPool

@[expose] public section

namespace OAI



open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open UniqueFactorizationMonoid
namespace SevenEighths.InverseInitialCompletePool
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialLargePool
open InverseInitialCommonTuples InverseInitialEnergyCallerWindow


theorem original_column_norm_bound (S:Finset (Ideal ActualEisensteinCubic.O)){P j c:Ideal ActualEisensteinCubic.O}
    (hP:Admissible P)(hj:j∣P)(hc:c∈columns S P j) :
    c.absNorm≤S.sup Ideal.absNorm*P.absNorm := And.casesOn ((OAI.SevenEighths.InverseInitialOverlap.mem_columns hP.right.left hj).mp hc) fun hcs right => And.casesOn right fun hcj right => And.casesOn right fun hres hnS => Nat.le_trans (Eq.symm (OAI.SevenEighths.InverseInitialOverlap.norm_reconstruct hres) ▸ Nat.le_mul_of_pos_left (Ideal.absNorm c) (Nat.one_le_iff_ne_zero.mpr fun h => (OAI.CanonicalQuadraticSieve.admissible_of_dvd hP hj).left (Ideal.absNorm_eq_zero_iff.mp h))) (Nat.mul_le_mul (Finset.le_sup hnS) (Nat.le_of_dvd (Nat.pos_of_ne_zero fun h => hP.left (Ideal.absNorm_eq_zero_iff.mp h)) (map_dvd Ideal.absNorm (OAI.CanonicalQuadraticSieve.idealQuotient_dvd hj))))

end SevenEighths.InverseInitialCompletePool



end OAI
