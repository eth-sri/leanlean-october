module

public import DedekindZetaZeroFree.Eisenstein.Induction.Spherical.FlatSources

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory RootDerivatives
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

structure SphericalFlatPreimages (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (A : JointExteriorCoefficientSources R N) (D : SphericalTransportData R A)
    (P : NormalizedSphericalTensor R A D) where
  sources : AdmissibleFlatSources R
  dq_exact : sources.dq = A.sources.dq
  residue : ∀ v, FlatScalarResidue F R.A.zeta12 R.A.primitive_zeta12 (sources.flat v)
  residue_exact : ∀ v, (residue v).numerator 0 =
    tensorFunction R A.factorization D.tensor.stage P.entries
  source_nonzero : ∀ v, (sources.flat v).val 0 ≠ 0

theorem sphericalFlatPreimages_nonempty
    (R : PrincipalMellin.ActualRecipe S η) {N : TraceHaarTransport R}
    (A : JointExteriorCoefficientSources R N) (D : SphericalTransportData R A)
    (P : NormalizedSphericalTensor R A D) :
    Nonempty (SphericalFlatPreimages R A D P) := by
  obtain ⟨Q,hQ,C,hC,hf,hne,hper⟩ := normalized_spherical_flat_sources R A D P
  exact ⟨{
    sources := Q
    dq_exact := hQ
    residue := C
    residue_exact := hC
    source_nonzero := hf
     }⟩

end DedekindZetaZeroFree.ThetaExpansion

end
