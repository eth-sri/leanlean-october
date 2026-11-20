module

public import DedekindZetaZeroFree.Eisenstein.Induction.ScalarCompactPicturesAndLocalQuotientTensors
public import DedekindZetaZeroFree.Metaplectic.Intertwining.ComplexStandardIntertwinerGerm

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPLiteralTensor
open KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues KPCplxActualImage
open KPLocalPrincipalSeries

noncomputable def harmonicQuotient :
    harmonicPlus →ₗ[ℂ] KPGlobalResidualConstruction.complexCore :=
  ((standardIntertwiner (1 : ℂˣ)).toLinearMap.domRestrict harmonicPlus).codRestrict
    KPGlobalResidualConstruction.complexCore (by
      intro x
      show (standardIntertwiner (1 : ℂˣ)) x ∈
        KPComplexStandardIntertwinerGerm.thetaCore (1 : ℂˣ)
      have hmem : (standardIntertwiner (1 : ℂˣ)) x ∈
          (KPComplexStandardIntertwinerGerm.ownedCore positiveParameter).map
            (standardIntertwiner (1 : ℂˣ)).toLinearMap := ⟨x, x.property, rfl⟩
      rw [(KPComplexStandardIntertwinerGerm.actual_harishChandra_image (1 : ℂˣ))] at hmem
      exact hmem)

theorem harmonicQuotient_surjective : Function.Surjective harmonicQuotient := by
  intro y
  have hy : (y : PrincipalSeries negativeParameter) ∈
      (KPComplexStandardIntertwinerGerm.ownedCore positiveParameter).map
        (standardIntertwiner (1 : ℂˣ)).toLinearMap := by
    rw [(KPComplexStandardIntertwinerGerm.actual_harishChandra_image (1 : ℂˣ))]
    exact y.property
  obtain ⟨f, hf, hfeq⟩ := hy
  exact ⟨⟨f, hf⟩, Subtype.ext hfeq⟩

theorem harmonicQuotient_val (x : harmonicPlus) :
    (harmonicQuotient x).val = standardIntertwiner (1 : ℂˣ) x.val := rfl

end DedekindZetaZeroFree.KPLiteralTensor

end
