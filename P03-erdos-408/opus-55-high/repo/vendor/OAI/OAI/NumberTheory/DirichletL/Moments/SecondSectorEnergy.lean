module

public import OAI.NumberTheory.DirichletL.Moments.SecondSectorChildren
public import OAI.NumberTheory.DirichletL.Moments.RestrictedSource

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentSecondSectorEnergy
open CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentSourceRow
open CenteredMomentSecondSectorColumns
open CenteredMomentRowNorm
open CenteredMomentRestrictedDomain
open CenteredMomentLiveDomain CenteredMomentFirstSectors

theorem sector_rowPolynomial (S : Finset (Ideal ActualEisensteinCubic.O)) (c : Ideal ActualEisensteinCubic.O → ℂ)
    (C : Ideal ActualEisensteinCubic.O) (hC : Supported C) (z : ActualEisensteinCubic.O) :
    rowPolynomial Finset.univ (sectorElement C hC.1 S)
      (fun I : sectorPool C hC.1 S => c I) z=
      rowPolynomial Finset.univ (sourceGenerator (residualPool C hC.1 S))
        (fun I : supportedColumns (residualPool C hC.1 S) => if IsCoprime C (I:Ideal ActualEisensteinCubic.O) then c I else 0) z := by
  rw [source_rowPolynomial (residualPool C hC.1 S)
    (fun I => if IsCoprime C I then c I else 0) z]
  unfold rowPolynomial
  simp only [sectorElement_span]
  rw [Finset.sum_coe_sort (sectorPool C hC.1 S) (fun I => c I*idealRowHom z I)]
  rw [sectorPool,Finset.sum_filter,supported_residualPool C hC S]
  simp

end SevenEighths.CenteredMomentSecondSectorEnergy

end

end OAI
