module

public import RequestProject.Oriented

public import RequestProject.GenusNamedSurfaceCover
public import RequestProject.BarycentricTwoChains
public import RequestProject.OrderTwoMapPrism
public import RequestProject.OrderNervePositiveFillings

@[expose] public section

backwardOptions



/-!
Reverse comparison for the actual lifted attaching surface. The six-triangle
subdivision and the interval-lift carrier give an explicit old three-boundary
whenever the normalized last-vertex image of a two-cycle is zero. Equal
boundaries and equal polygon images therefore imply equality modulo genuine
old three-boundaries, with no subdivision-equivalence hypothesis.

Written proof terms; not compiled under the current workflow.
-/

noncomputable section
open scoped Classical

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {P X : Type u} [PartialOrder P] [DecidableEq P]
  [PartialOrder X] (g : P →o X)
  (a : Qpos (cmpRel P) X (nerveAtt g))
  (hc : IsConnected (orderCx (Qpos (cmpRel P) X (nerveAtt g))))

/-- Lift an actual simplex in the surface cover to its barycentric pullback.
The top vertex fixes the sheet and all other vertices remain in that sheet. -/
def surfaceBarycentricToSubdivision
    (σ : NeSpx (cmpRel (AttachingSurfaceCover g a))) : AttachingSurfaceSubdivision g a :=
  ⟨((chainMax σ).1.1,
      barycentricMap (attachingSurfaceProjection g a) (posetPullbackProjection_monotone _ _) σ), by
    change uOrderEnd (chainMax σ).1.1 =
      qNew (att := nerveAtt g) (g (chainMax
        (barycentricMap (attachingSurfaceProjection g a)
          (posetPullbackProjection_monotone _ _) σ)))
    erw [chainMax_barycentricMap]
    exact (chainMax σ).2⟩

theorem surfaceBarycentricToSubdivision_monotone :
    Monotone (surfaceBarycentricToSubdivision g a) := by
  intro σ τ h
  exact ⟨(chainMax_monotone h).1,
    barycentricMap_monotone _ (posetPullbackProjection_monotone _ _) h⟩

def surfaceBarycentricReverse : NeSpx (cmpRel (AttachingSurfaceCover g a)) →
    QLiftedAttaching a :=
  (surfaceSubdivisionToAttaching g a hc) ∘ (surfaceBarycentricToSubdivision g a)

theorem surfaceBarycentricReverse_monotone : Monotone (surfaceBarycentricReverse g a hc) :=
  (surfaceSubdivisionToAttaching_monotone g a hc).comp
    (surfaceBarycentricToSubdivision_monotone g a)

/-- The reverse subdivision of the last-vertex image is carried by the
original top simplex, inside the OLD attaching cover itself. -/
theorem surfaceBarycentricReverse_le_lastVertex
    (σ : NeSpx (cmpRel (QLiftedAttaching a))) :
    surfaceBarycentricReverse g a hc
      (barycentricMap (attachingToSurfaceCover g a hc)
        (attachingToSurfaceCover_monotone g a hc) σ) ≤ chainMax σ := by
  let F := attachingToSurfaceCover g a hc
  let hF := attachingToSurfaceCover_monotone g a hc
  let s := surfaceBarycentricToSubdivision g a (barycentricMap F hF σ)
  have hb : s.1.1 = attachingSurfaceLowerLift g a hc (chainMax σ) := by
    change (chainMax (barycentricMap F hF σ)).1.1 = _
    rwd [chainMax_barycentricMap]
    rfl
  have hs : s.1.2 ≤ qAttachingCoverEnd a (chainMax σ) := by
    intro p hp
    obtain ⟨d, hd, he⟩ := (@Finset.mem_image _ P (Classical.decEq P) _ _ _).mp hp
    obtain ⟨e, heσ, hed⟩ := Finset.mem_image.mp hd
    subst d
    rwd [← he]
    change chainMax (qAttachingCoverEnd a e) ∈ (qAttachingCoverEnd a (chainMax σ)).1
    exact (qAttachingCoverEnd_monotone g a (le_chainMax σ heσ))
      (chainMax_mem (qAttachingCoverEnd a e))
  have hsold : qOldIncl (att := nerveAtt g) (posQCube s.1.2) ≤
      uOrderEnd (chainMax σ).1 := by
    rwd [← qAttachingCoverEnd_oldPoint g a (chainMax σ)]
    exact qOldIncl_monotone ⟨hs, fun _ _ => rfl⟩
  have hlo : s.1.1 ≤ (chainMax σ).1 := by
    rwd [hb]
    exact (attachingSurfaceLowerLift_spec g a hc (chainMax σ)).1
  obtain ⟨v, hvlo, hvhi, hvend⟩ := (uOrderEnd_isPosetCover hc).exists_interval_lift hlo
    (qOldIncl (att := nerveAtt g) (posQCube s.1.2))
    (surfaceSubdivision_upper_comparison g a s) hsold
  have hu := surfaceSubdivisionUpperLift_spec g a hc s
  have heq : v = surfaceSubdivisionUpperLift g a hc s :=
    (uOrderEnd_isPosetCover hc).up_inj hvlo hu.1 (hvend.trans hu.2.symm)
  change surfaceSubdivisionUpperLift g a hc s ≤ (chainMax σ).1
  exact heq ▸ hvhi

/-- The only kernel of the normalized forward map on actual two-cycles is
made of actual old three-boundaries. All witnesses are finite cellular chains. -/
theorem attachingSurface_normalized_cycle_reflection
    (c : OrdTri (QLiftedAttaching a) →₀ ℤ)
    (hcycle : Comb.bdry2 (orderCx (QLiftedAttaching a)) c = 0)
    (hzero : normalizeOrdChain2 (chain2
      (orderCxMap (attachingToSurfaceCover g a hc)
        (attachingToSurfaceCover_monotone g a hc)) c) = 0) :
    ∃ b : OrdTet (QLiftedAttaching a) →₀ ℤ, ordBoundary3 b = c := by
  let F := attachingToSurfaceCover g a hc
  let hF := attachingToSurfaceCover_monotone g a hc
  let R := surfaceBarycentricReverse g a hc
  let hR := surfaceBarycentricReverse_monotone g a hc
  let H := R ∘ barycentricMap F hF
  have hH : Monotone H := hR.comp (barycentricMap_monotone F hF)
  have hle : ∀ σ, H σ ≤ chainMax σ := surfaceBarycentricReverse_le_lastVertex g a hc
  let s := barycentricChain2 c
  have hsc : Comb.bdry2 (orderCx (NeSpx (cmpRel (QLiftedAttaching a)))) s = 0 := by
    rwd [barycentricChain2_boundary, hcycle, map_zero]
  have hnatural : chain2 (orderCxMap H hH) s =
      chain2 (orderCxMap R hR) (barycentricChain2 (chain2 (orderCxMap F hF) c)) := by
    change Finsupp.mapDomain
      ((orderCxMap R hR).onF ∘
        (orderCxMap (barycentricMap F hF) (barycentricMap_monotone F hF)).onF) s = _
    rwd [Finsupp.mapDomain_comp]
    rwd [show Finsupp.mapDomain
        (orderCxMap (barycentricMap F hF) (barycentricMap_monotone F hF)).onF s =
      barycentricChain2 (chain2 (orderCxMap F hF) c) from
        barycentricChain2_natural F hF c]
    rfl
  have hz : barycentricChain2 (chain2 (orderCxMap F hF) c) = 0 := by
    rwd [barycentricChain2_normalization, hzero, map_zero]
  have hHz : chain2 (orderCxMap H hH) s = 0 := by rwd [hnatural, hz, map_zero]
  let l := chain2 (orderCxMap (chainMax (P := QLiftedAttaching a)) chainMax_monotone) s
  let p := ordMapPrism2 H chainMax hH chainMax_monotone hle s
  have hp : ordBoundary3 p = l := by
    have h := ordMapPrism_cycle H chainMax hH chainMax_monotone hle s hsc
    simpa only [hHz, sub_zero] using h
  have hlc : Comb.bdry2 (orderCx (QLiftedAttaching a)) l = 0 := by
    rwd [bdry2_chain2, hsc, map_zero]
  have hln : normalizeOrdChain2 l = normalizeOrdChain2 c := barycentricChain2_lastVertex c
  refine ⟨ordNormalizationHomotopy2 c - ordNormalizationHomotopy2 l + p, ?_⟩
  rwd [map_add, map_sub, ← ordNormalization_cycle_boundary c hcycle,
    ← ordNormalization_cycle_boundary l hlc, hp, hln]
  rwd [sub_sub_sub_cancel_right, sub_add_cancel]

/-- The reflection in exactly the homogeneous full-nerve interface used by
the old/star gluing theorem. -/
theorem attachingSurface_nerve_cycle_reflection
    (c : Nerve.Ch (QLiftedAttaching a)) (hinc : c ∈ Nerve.Inc (QLiftedAttaching a))
    (hdegree : Nerve.lengthProjection 3 c = c) (hcycle : Nerve.bdry c = 0)
    (hzero : normalizeOrdChain2 (chain2
      (orderCxMap (attachingToSurfaceCover g a hc)
        (attachingToSurfaceCover_monotone g a hc)) (decodeOrdNerve2 c)) = 0) :
    ∃ b ∈ Nerve.Inc (QLiftedAttaching a), Nerve.bdry b = c := by
  have he : ordNerveChain2 (decodeOrdNerve2 c) = c :=
    (ordNerveChain2_decode hinc).trans hdegree
  have hcell := (ordNerveChain2_cycle_iff (decodeOrdNerve2 c)).mp (by rwd [he, hcycle])
  obtain ⟨b, hb⟩ := attachingSurface_normalized_cycle_reflection g a hc
    (decodeOrdNerve2 c) hcell hzero
  refine ⟨ordNerveChain3 b, ordNerveChain3_mem_inc b, ?_⟩
  rwd [← ordNerveChain2_ordBoundary3, hb, he]

theorem attachingSurface_nerve_cycle_reflection_homogeneous
    (c : Nerve.Ch (QLiftedAttaching a)) (hinc : c ∈ Nerve.Inc (QLiftedAttaching a))
    (hdegree : Nerve.lengthProjection 3 c = c) (hcycle : Nerve.bdry c = 0)
    (hzero : normalizeOrdChain2 (chain2
      (orderCxMap (attachingToSurfaceCover g a hc)
        (attachingToSurfaceCover_monotone g a hc)) (decodeOrdNerve2 c)) = 0) :
    ∃ b ∈ Nerve.Inc (QLiftedAttaching a),
      Nerve.lengthProjection 4 b = b ∧ Nerve.bdry b = c := by
  obtain ⟨b, hb, hdb⟩ := attachingSurface_nerve_cycle_reflection g a hc
    c hinc hdegree hcycle hzero
  refine ⟨Nerve.lengthProjection 4 b, Nerve.lengthProjection_mem_inc _ hb,
    Nerve.lengthProjection_idempotent _ _, ?_⟩
  rwd [← Nerve.lengthProjection_bdry 3, hdb, hdegree]

/-- Exact homogeneous relative-chain comparison; the boundary itself is
retained, not merely its augmentation or its homology class. -/
theorem attachingSurface_nerve_relative_comparison
    (c d : Nerve.Ch (QLiftedAttaching a))
    (hcinc : c ∈ Nerve.Inc (QLiftedAttaching a))
    (hdinc : d ∈ Nerve.Inc (QLiftedAttaching a))
    (hcdegree : Nerve.lengthProjection 3 c = c)
    (hddegree : Nerve.lengthProjection 3 d = d)
    (hboundary : Nerve.bdry c = Nerve.bdry d)
    (himage : normalizeOrdChain2 (chain2
      (orderCxMap (attachingToSurfaceCover g a hc)
        (attachingToSurfaceCover_monotone g a hc)) (decodeOrdNerve2 c)) =
      normalizeOrdChain2 (chain2
        (orderCxMap (attachingToSurfaceCover g a hc)
          (attachingToSurfaceCover_monotone g a hc)) (decodeOrdNerve2 d))) :
    ∃ b ∈ Nerve.Inc (QLiftedAttaching a),
      Nerve.lengthProjection 4 b = b ∧ c - d = Nerve.bdry b := by
  obtain ⟨b, hb, hdeg, he⟩ := attachingSurface_nerve_cycle_reflection_homogeneous g a hc
    (c - d) (AddSubgroup.sub_mem _ hcinc hdinc)
    (by rwd [map_sub, hcdegree, hddegree])
    (by rwd [map_sub, hboundary, sub_self])
    (by rwd [map_sub, map_sub, map_sub, himage, sub_self])
  exact ⟨b, hb, hdeg, he.symm⟩

end FiniteChains.Davis

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily
variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)

end FiniteChains.Davis.Genus
