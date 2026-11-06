module
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceOriginalData
public import OAI.NumberTheory.DirichletL.Moments.SecondSectorColumns

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentSecondSectorColumns CenteredMomentFirstSectorTransform IdealMobiusDivisorSum CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors CenteredMomentLiveDomain CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentChildAssembly

theorem columns_gauss_polynomial_filter (Q C:Ideal O)(hC:Supported C)(S:Finset (Ideal O))
    (f:Ideal O→ℂ)(z:O):
    gaussPolynomial Finset.univ (element Q C hC.1 S) (element_supported Q C hC.1 S)
      (fun a=>f a) z=
    gaussPolynomial Finset.univ (sourceGenerator (residualPool C hC.1 S))
      (sourceGenerator_supported _) (fun I=>if IsCoprime Q (I:Ideal O) then f I else 0) z:=by
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
  apply Finset.sum_congr rfl
  intro I hI
  split_ifs <;> simp
