module

public import DedekindZetaZeroFree.Eisenstein.Residues.GlobalRefinedBoundaryCenters

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ContDiff
open MeasureTheory Filter
namespace DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters
open KPContActualSphericalRightFieldIdentification KPContActualCutoffPlusClearedGerm

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 120000
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]
    {SS : SArithmeticData F} {η : RayClassCharacter F SS.modulus}
    (AR : PrincipalMellin.ActualRecipe SS η)
    (AP : KPGlobalTorusFiniteStages.CompatibleModelData F AR.A.zeta12 AR.A.primitive_zeta12)
    (AC : KPGlobalTorusFiniteStages.LocalFiberData F AR.A.zeta12 AR.A.primitive_zeta12 AP)
    (D : KPGlobalTorusInducingPlan.ModelData F AR.A.zeta12 AR.A.primitive_zeta12)
    (Haar : KPSmoothLocalQuotientCharts.HaarRecipe F AR.A.zeta12 AR.A.primitive_zeta12)
    (Transport : KPMsFixedHaarDisintegration.SphericalTransport F AR.A.zeta12 AR.A.primitive_zeta12)
variable (H : KPMsFixedHaarDisintegration.AllLevels F AR.A.zeta12 AR.A.primitive_zeta12 Haar Transport)
    (U : KPMsRationalCompactCrossPairing.Level F AR.A.zeta12 AR.A.primitive_zeta12)
local notation "level" => KPContActualAllCuspSource.level F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U
local notation "Smooth" => KPContActualAllCuspSource.SmoothSections F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U
local notation "G" => KPContSectorCoveredQuotientVocabulary.ActualCover F AR.A.zeta12 AR.A.primitive_zeta12

open KPLiteralRaw
open scoped BigOperators

theorem finite_owned_refined_boundary_centers
    (Jaux : KPGlobalTorusFunctionData.FiniteLevel F AR.A.zeta12 AR.A.primitive_zeta12)
    (K : Subgroup G) (hK : IwasawaCompact F AR.A.zeta12 AR.A.primitive_zeta12 K) (f : Flat F AR.A.zeta12 AR.A.primitive_zeta12 K)
    (A : TensorActionSource.LiteralResidueFamily hK) :
    ∃ (n : ℕ) (U : Fin n → KPMsRationalCompactCrossPairing.Level F AR.A.zeta12 AR.A.primitive_zeta12)
      (m : Fin n → ℕ)
      (v : ∀ i, Fin (m i) → KPContActualSphericalFlatStage.Stage F AR.A.zeta12 AR.A.primitive_zeta12 (U i))
      (w : ∀ i, Fin (m i) → List (Fin (groupDimension F)))
      (B : ∀ i, Fin (m i) → ℂ → ℂ)
      (Z : ∀ i, Fin (m i) → KPContActualAllCuspSource.SmoothSections F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H (U i))
      (z : ∀ i, Fin (m i) → KPContActualAllCuspSource.Sector F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H (U i)),
      (∀ i, KPShift81CoherentLevel.level F AR.A.zeta12 AR.A.primitive_zeta12 (U i) = U i) ∧
      (∀ i, (U i).toOpenSubgroup.toSubgroup ≤ Jaux.toOpenSubgroup.toSubgroup) ∧
      (∀ i j, KPContActualSmoothLineGluing.Represents F AR.A.zeta12 AR.A.primitive_zeta12
        (KPContActualAllCuspSource.level F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H (U i)) Haar Transport H (Z i j).val (z i j)) ∧
      (∀ i j, LiteralSource.SphericalBoundaryProperty AR AP AC D Haar Transport H (U i) (v i j) (z i j)) ∧
      (∀ i j g, KPMsGreenFlux.casimir F AR.A.zeta12 AR.A.primitive_zeta12
        (groupScalar F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H (U i) (Z i j)) g =
        KPContinuation.spectralCoordinate (KPCuspLogShape.dimension F : ℤ) 0 *
          groupScalar F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H (U i) (Z i j) g) ∧
      (∀ g, f.val 0 g = ∑ i, ∑ j, B i j 0 * actualRightWord F AR.A.zeta12 AR.A.primitive_zeta12 (w i j)
        ((KPContFlatSourceRecipe.flatR F AR.A.zeta12 AR.A.primitive_zeta12 0 (v i j).val).val) g) ∧
      ∀ g, A.cleared f 0 g = ∑ i, ∑ j, B i j 0 * actualRightWord F AR.A.zeta12 AR.A.primitive_zeta12 (w i j)
        (groupScalar F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H (U i) (Z i j)) g := by
  obtain ⟨n, U, m, v, w, B, Z, z, hfix, haux, hz, heig, horth, hnative, hcus, hsource, q, J, T, r, hq, hq0, hJ, hch, hr, hT, hclear, hcenter⟩ := finite_literal_global_refined_boundary_centers AR AP AC D Haar Transport H Jaux K hK f
  refine ⟨n, U, m, v, w, B, Z, z, hfix, haux, hz, horth, hnative, hsource, ?_⟩
  intro g
  obtain ⟨O, u, hO, hc, hOc, hu, hub, hE, hAc, han⟩ := A.germ.2 f
  have he : (fun s => J s g) =ᶠ[𝓝[≠] (0 : ℂ)] (fun s => q s * A.E f s g) := by
    apply CompactPeriodAnalyticity.UpperPeriodContinuation.chamber_identity_germ (hJ g)
      (hq.meromorphicOn.mul ((A.normal f g).meromorphicOn))
      KPContinuation.spectralDomain_isConnected.isPreconnected
      KPContinuation.convergenceHalfPlane_subset_spectralDomain ?_ 0 ?_
    · intro s hs
      change J s g = q s * A.E f s g
      rw [hch s hs, A.germ.1 f s hs]
    · norm_num [KPContinuation.spectralDomain]
  have hnum : (fun s => T s g) =ᶠ[𝓝[≠] (0 : ℂ)] (fun s => q s * A.cleared f s g) := by
    filter_upwards [he, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr),
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hu), self_mem_nhdsWithin]
      with s hes hsr hsu hne
    rw [hclear s hsr hne]
    change s * J s g = q s * A.cleared f s g
    rw [hes, congrFun (hAc s hsu hne) g]
    change s * (q s * A.E f s g) = q s * (s * A.E f s g)
    ring
  have hqA : ContinuousAt (fun s => q s * A.cleared f s g) 0 :=
    (hq 0 (by norm_num [KPContinuation.spectralDomain])).continuousAt.mul
      ((han g) 0 (Metric.mem_ball_self hu)).continuousAt
  have he0 := (((hT g) 0 (Metric.mem_ball_self hr)).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    hqA).mp hnum |>.eq_of_nhds
  have hpin : T 0 g = A.cleared f 0 g := by simpa only [hq0, one_mul] using he0
  exact hpin.symm.trans (hcenter g)

end DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters

end
