module

public import DedekindZetaZeroFree.Adeles.Approximation.CompactReferenceTails
public import DedekindZetaZeroFree.Eisenstein.Induction.Chambers.ParameterEvaluation
public import DedekindZetaZeroFree.Eisenstein.Induction.ExteriorFactors.CompactParameterIntegrals
public import DedekindZetaZeroFree.Eisenstein.Continuation.Cofactors.HeightAndTailBounds

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
namespace DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding
open NumberField MomentSources KPGlobalTorusFiniteStages FaithfulSource.RepairedInducing
open KPLocalPrincipalSeries KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
open LiteralSource.CofactorChamber KPAdelicCoverRestrictedProduct KPLocalExceptionalConstruction
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
    (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
    (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem compact_split_tail (K : Set (FaithfulSource.RepairedInducing.Raw R)) (hK : IsCompact K)
    (E : Finset (KPFinitePlace F)) :
    ∃ Q : Finset (KPFinitePlace F), E ⊆ Q ∧ C.exceptional ⊆ Q ∧
      ∀ a ∈ K, ∀ q, q ∉ Q →
        KPPGLLocalCover.coverQuotient F ζ hζ (.inr q) (a (.inr q)) ∈
          (C.canonical q).iwasawa.compact.toOpenSubgroup := by
  obtain ⟨T,hT⟩ := LiteralSource.exists_uniform_compact_tail R.A K hK
  let Q := E ∪ C.exceptional ∪ T ∪ (bad_finite F).toFinset
  refine ⟨Q, ?_, ?_, ?_⟩
  · exact Finset.subset_union_left.trans (Finset.subset_union_left.trans Finset.subset_union_left)
  · exact Finset.subset_union_right.trans (Finset.subset_union_left.trans Finset.subset_union_left)
  · intro a ha q hq
    have hqB : ¬ Bad F q := fun h => hq (by simp [Q,h])
    have hk := hT a ha q (fun h => hq (by simp [Q,h]))
    simp only [finiteCompact, dite_eq_right hqB, MonoidHom.mem_range] at hk
    obtain ⟨k,hk⟩ := hk
    obtain ⟨ht,hc⟩ := C.actual_compact q (fun h => hq (by simp [Q,h]))
    change _ ∈ ((C.canonical q).iwasawa.compact.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q))
    rw [hc]
    refine ⟨k, ?_⟩
    rw [← hk]
    rfl

end DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding

end
