module
public import OAI.NumberTheory.DirichletL.Moments.FirstCommonFourierTransport
public import OAI.NumberTheory.DirichletL.Moments.FirstSectorTransform
public import OAI.NumberTheory.DirichletL.Moments.SecondSectorColumns

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstRetainedSector
open HeckeFamily CanonicalQuadraticSieve CompletedGauss CenteredMomentSourceRow CenteredMomentFirstSectorLocalization CenteredMomentFirstCommonFourierTransport CenteredMomentHeckeExpansion CenteredMomentCommonSectors CenteredMomentFirstSectors CenteredMomentCompleteCommon CenteredMomentSecondSectorColumns CenteredMomentHeckeColumnWindow CenteredMomentSupport CenteredMomentSectorLocalization

def retainedKernel (I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) : ℂ :=
  if hI : Supported I then if hJ : Supported J then CenteredMomentFirstSectorLocalization.retainedPair I J hI hJ W K X Z ξ else 0 else 0

theorem retainedKernel_eq (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    retainedKernel I J W K X Z ξ=CenteredMomentFirstSectorLocalization.retainedPair I J hI hJ W K X Z ξ := by
  simp only [retainedKernel,dite_eq_left hI,dite_eq_left hJ]

theorem retainedEnergy_common_sectors (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    CenteredMomentFirstSectorLocalization.retainedEnergy η m A t S β W K X Z ξ=
      ∑ p∈commonLabels (supportedColumns S) (supportedColumns S),
        ∑ q∈pairSector p.1 p.2 (supportedColumns S) (supportedColumns S),
          ((β q.1*rowWeight η m A 1 t q.1)*star (β q.2*rowWeight η m A 1 t q.2))*
            retainedKernel q.1 q.2 W K X Z ξ := by
  let F := fun I J : Ideal O=>((β I*rowWeight η m A 1 t I)*star (β J*rowWeight η m A 1 t J))*
    retainedKernel I J W K X Z ξ
  have he : CenteredMomentFirstSectorLocalization.retainedEnergy η m A t S β W K X Z ξ=
      ∑ I : supportedColumns S,∑ J : supportedColumns S,F I J := by
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro J hJ
    dsimp only [F]
    rw [retainedKernel_eq I J (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2]
  rw [he]
  have hj (I : Ideal O) : (∑ J : supportedColumns S,F I J)=∑ J∈supportedColumns S,F I J :=
    Finset.sum_coe_sort _ _
  simp_rw [hj]
  rw [Finset.sum_coe_sort (supportedColumns S) (fun I=>∑ J∈supportedColumns S,F I J)]
  exact sum_common_sectors _ _ F

theorem reconstructed_residualParts (C D I J:Ideal O)(hC:C≠0)(hD:D≠0)(hI:I≠0)(hJ:J≠0)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (hCI:IsCoprime C I)(hCJ:IsCoprime C J)(hIJ:IsCoprime I J):
    residualPart (C*I) (D*J)=I ∧ residualPart (D*J) (C*I)=J:=by
  obtain ⟨hc,hd⟩:=reconstructed_commonParts C D I J hC hD hI hJ hCD hCI hCJ hIJ
  constructor
  · have hh:=reconstruct (C*I) (D*J) (mul_ne_zero hC hI)
    rw [hc] at hh
    exact (mul_left_cancel₀ hC hh).symm
  · have hh:=reconstruct (D*J) (C*I) (mul_ne_zero hD hJ)
    rw [hd] at hh
    exact (mul_left_cancel₀ hD hh).symm

theorem canonicalRetainedPair_of_common (I J C D:Ideal O)(hI:Supported I)(hJ:Supported J)
    (hC:Supported C)(hc:commonPart I J=C)(hd:commonPart J I=D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    CenteredMomentFirstSectorLocalization.retainedPair I J hI hJ W K X Z ξ=
      ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
        fixedRetainedTerm C D hC (CenteredMomentCanonicalFirst.residualGenerator I J)
          (CenteredMomentCanonicalFirst.residualGenerator J I)
          (CenteredMomentCanonicalFirst.residualGenerator_supported I J hI)
          (CenteredMomentCanonicalFirst.residualGenerator_supported J I hJ) E W K X Z ξ:=by
  subst C
  subst D
  exact canonicalRetainedPair_fixed I J hI hJ W K X Z ξ

theorem retainedKernel_fixed (C D I J:Ideal O)(hC:Supported C)(hD:Supported D)
    (hI:Supported I)(hJ:Supported J)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (hCI:IsCoprime C I)(hCJ:IsCoprime C J)(hIJ:IsCoprime I J)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    retainedKernel (C*I) (D*J) W K X Z ξ=
      ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
        fixedRetainedTerm C D hC (primaryGenerator I) (primaryGenerator J)
          (by rw [primary_span_supported I hI];exact hI)
          (by rw [primary_span_supported J hJ];exact hJ) E W K X Z ξ:=by
  have hCI':Supported (C*I):=(supported_mul_iff C I).mpr ⟨hC,hI⟩
  have hDJ':Supported (D*J):=(supported_mul_iff D J).mpr ⟨hD,hJ⟩
  rw [retainedKernel_eq _ _ hCI' hDJ']
  obtain ⟨hc,hd⟩:=reconstructed_commonParts C D I J hC.1 hD.1 hI.1 hJ.1 hCD hCI hCJ hIJ
  obtain ⟨hi,hj⟩:=reconstructed_residualParts C D I J hC.1 hD.1 hI.1 hJ.1 hCD hCI hCJ hIJ
  have hh:=canonicalRetainedPair_of_common (C*I) (D*J) C D hCI' hDJ' hC hc hd W K X Z ξ
  simpa only [CenteredMomentCanonicalFirst.residualGenerator,hi,hj] using hh
