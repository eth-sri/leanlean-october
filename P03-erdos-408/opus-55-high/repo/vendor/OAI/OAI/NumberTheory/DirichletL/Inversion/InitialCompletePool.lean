module

public import OAI.NumberTheory.DirichletL.Inversion.InitialLargeFourier
public import OAI.NumberTheory.DirichletL.Descent.CompleteMarkedPool

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical
open CanonicalQuadraticSieve
namespace SevenEighths.InverseInitialCompletePool
open InverseInitialOverlap
local notation "Eis"=>ActualEisensteinCubic.O

theorem original_column_norm_bound (S:Finset (Ideal ActualEisensteinCubic.O)){P j c:Ideal ActualEisensteinCubic.O}
    (hP:Admissible P)(hj:j∣P)(hc:c∈columns S P j) :
    c.absNorm≤S.sup Ideal.absNorm*P.absNorm := by
  obtain ⟨hcs,hcj,hres,hnS⟩ := (mem_columns hP.2.1 hj).mp hc
  have hn := norm_reconstruct hres
  have hj0 := (admissible_of_dvd hP hj).1
  have hjpos : 1≤j.absNorm := Nat.one_le_iff_ne_zero.mpr
    (fun h=>hj0 (Ideal.absNorm_eq_zero_iff.mp h))
  have hnn : (reconstruct P j c).absNorm≤S.sup Ideal.absNorm := Finset.le_sup hnS
  have hPN : (residual P j).absNorm≤P.absNorm := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (fun h=>hP.1 (Ideal.absNorm_eq_zero_iff.mp h)))
    (map_dvd Ideal.absNorm (idealQuotient_dvd hj))
  nlinarith

end SevenEighths.InverseInitialCompletePool

end

end OAI
