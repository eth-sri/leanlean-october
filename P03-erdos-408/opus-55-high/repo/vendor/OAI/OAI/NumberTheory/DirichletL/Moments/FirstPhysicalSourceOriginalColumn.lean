module

public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceOriginalData
public import OAI.NumberTheory.DirichletL.Moments.SecondSectorColumns

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentFirstSectors CenteredMomentLiveDomain
open CenteredMomentGaussEnergy
local notation "O"=>ActualEisensteinCubic.O

theorem columns_gauss_polynomial_filter (Q C:Ideal ActualEisensteinCubic.O)(hC:Supported C)(S:Finset (Ideal ActualEisensteinCubic.O))
    (f:Ideal ActualEisensteinCubic.O→ℂ)(z:ActualEisensteinCubic.O):
    gaussPolynomial Finset.univ (element Q C hC.1 S) (element_supported Q C hC.1 S)
      (fun a=>f a) z=
    gaussPolynomial Finset.univ (sourceGenerator (residualPool C hC.1 S))
      (sourceGenerator_supported _) (fun I=>if IsCoprime Q (I:Ideal ActualEisensteinCubic.O) then f I else 0) z:=by
  rw [source_gaussPolynomial (residualPool C hC.1 S)
    (fun I=>if IsCoprime Q I then f I else 0) z,supported_residualPool C hC S]
  have he (a:columns Q C hC.1 S):
      gaussRow (element Q C hC.1 S a) (element_supported Q C hC.1 S a) z=
        primaryGaussRow a z:=by
    rw [primaryGaussRow,dite_eq_left (column_supported Q C hC.1 S a)]
    rfl
  simp only [gaussPolynomial,he]
  rw [Finset.sum_coe_sort (columns Q C hC.1 S) (fun I=>f I*primaryGaussRow I z)]
  unfold columns
  rw [Finset.sum_filter]
  simp

variable {ι:Type*}[Fintype ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
