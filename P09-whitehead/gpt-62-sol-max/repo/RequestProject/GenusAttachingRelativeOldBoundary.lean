module

public import RequestProject.GenusNamedSurfaceSubdivision
public import RequestProject.GenusNamedPolygonCoefficients
public import RequestProject.GenusQuotientAttachingFilling
public import RequestProject.StrictOrderNormalizationMaps
public import RequestProject.OrderUniversalDeckChains
public import RequestProject.MonoidAlgebraCoefficients
public import RequestProject.GenusAllQuotientRelativeRigidity
public import RequestProject.GenusMarkedSpineInjection
public import RequestProject.GenusQuotientReceiver

@[expose] public section

/-! Polygon reconstruction yields a boundary supported on actual old cells.
All deck coefficients are retained in the actual quotient group.
 -/
noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency false


namespace FiniteChains.Comb
open Nerve
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

theorem decodeOrdNerve2_cmap_homogeneous (f : P → Q) (hf : Monotone f)
    (c : Ch P) (hc : c ∈ Inc P) (hd : lengthProjection 3 c = c) :
    decodeOrdNerve2 (cmap f c) = chain2 (orderCxMap f hf) (decodeOrdNerve2 c) := by
  have he  := (ordNerveChain2_decode hc).trans hd
  calc
    _ = decodeOrdNerve2 (cmap f (ordNerveChain2 (decodeOrdNerve2 c))) := by rw [he]
    _ = _ := by rw [← ordNerveChain2_chain2 f hf, decodeOrdNerve2_encode]

variable {a : P}

theorem universalNerveChain1_deck (g : Pi1 (orderCx P) a)
    (c : UE (orderCx P) a →₀ ℤ) :
    universalNerveChain1 (chain1 ((univDeck (orderCx P) a).cellHom g) c) =
      cmap (uOrderDeck g) (universalNerveChain1 c) := by
  change ordNerveChain1 (chain1 uOrderHomInv (chain1 ((univDeck (orderCx P) a).cellHom g) c)) = _
  rw [← chain1_comp_apply, uOrderHomInv_deck_square, chain1_comp_apply, ordNerveChain1_chain1]
  rfl

theorem universalNerveChain2_deck (g : Pi1 (orderCx P) a)
    (c : UF (orderCx P) a →₀ ℤ) :
    universalNerveChain2 ((univDeck (orderCx P) a).faceChains g c) =
      cmap (uOrderDeck g) (universalNerveChain2 c) := by
  change ordNerveChain2 (chain2 uOrderHomInv (chain2 ((univDeck (orderCx P) a).cellHom g) c)) = _
  rw [← chain2_comp_apply, uOrderHomInv_deck_square, chain2_comp_apply, ordNerveChain2_chain2]
  rfl

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve MonoidAlgebra
variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)

def namedAttachingDeck (g : NamedPolygonDeckGroup ρ q u) :
    namedAttachingCover q ρ u ≃o namedAttachingCover q ρ u where
  toFun p := ⟨uOrderDeck g p.1, by rw [uOrderDeck_end]; exact p.2⟩
  invFun p := ⟨uOrderDeck g⁻¹ p.1, by rw [uOrderDeck_end]; exact p.2⟩
  left_inv p := by
    apply Subtype.ext
    change deckV g⁻¹ (deckV g p.1) = p.1
    rw [← deckV_mul, inv_mul_cancel, deckV_one]
  right_inv p := by
    apply Subtype.ext
    change deckV g (deckV g⁻¹ p.1) = p.1
    rw [← deckV_mul, mul_inv_cancel, deckV_one]
  map_rel_iff' := (uOrderDeckOrderIso g).map_rel_iff

theorem namedAttachingIntoUniversal_deck_square (g : NamedPolygonDeckGroup ρ q u) :
    (namedAttachingIntoUniversal q ρ u).comp
      (orderCxMap (namedAttachingDeck ρ q u g) (namedAttachingDeck ρ q u g).monotone) =
      ((namedQuotientDeck ρ q u).cellHom g).comp (namedAttachingIntoUniversal q ρ u) :=
  congrArg (fun h => h.comp (orderCxMap (fun p : namedAttachingCover q ρ u => p.val)
    (fun _ _ h => h))) (uOrderHom_deck_square g)

theorem namedAttachingIntoUniversal_chain1_deck (g : NamedPolygonDeckGroup ρ q u)
    (c : OrdEdge (namedAttachingCover q ρ u) →₀ ℤ) :
    chain1 (namedAttachingIntoUniversal q ρ u)
      (chain1 (orderCxMap (namedAttachingDeck ρ q u g)
        (namedAttachingDeck ρ q u g).monotone) c) =
      chain1 ((namedQuotientDeck ρ q u).cellHom g)
          (chain1 (namedAttachingIntoUniversal q ρ u) c) := by
  rw [← chain1_comp_apply, namedAttachingIntoUniversal_deck_square, chain1_comp_apply]

theorem namedAttachingDeck_projection (g : NamedPolygonDeckGroup ρ q u)
    (p : namedAttachingCover q ρ u) :
    qAttachingCoverEnd (namedQuotientBase ρ q u) (namedAttachingDeck ρ q u g p) =
      qAttachingCoverEnd (namedQuotientBase ρ q u) p := by
  change qPositiveOldOrderIso ⟨uOrderEnd (uOrderDeck g p.1), _⟩ =
    qPositiveOldOrderIso ⟨uOrderEnd p.1, _⟩
  congr 1
  exact Subtype.ext (uOrderDeck_end g p.1)

theorem namedAttachingSurfaceLowerLift_deck (g : NamedPolygonDeckGroup ρ q u)
    (p : namedAttachingCover q ρ u) :
    attachingSurfaceLowerLift (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
      (namedQuotientPos_isConnected ρ q u) (namedAttachingDeck ρ q u g p) =
      uOrderDeck g (attachingSurfaceLowerLift (namedSurfaceLabel ρ q u)
        (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u) p) := by
  have h₁ := attachingSurfaceLowerLift_spec (namedSurfaceLabel ρ q u)
    (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u)
    (namedAttachingDeck ρ q u g p)
  have h₂ := attachingSurfaceLowerLift_spec (namedSurfaceLabel ρ q u)
    (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u) p
  apply (uOrderEnd_isPosetCover (namedQuotientPos_isConnected ρ q u)).down_inj
    h₁.1 ((uOrderDeckOrderIso g).monotone h₂.1)
  change uOrderEnd (attachingSurfaceLowerLift (namedSurfaceLabel ρ q u)
    (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u)
    (namedAttachingDeck ρ q u g p)) =
    uOrderEnd (uOrderDeck g (attachingSurfaceLowerLift (namedSurfaceLabel ρ q u)
      (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u) p))
  rw [h₁.2, uOrderDeck_end, h₂.2, namedAttachingDeck_projection]

theorem namedAttachingToSurface_deck (g : NamedPolygonDeckGroup ρ q u)
    (p : namedAttachingCover q ρ u) :
    attachingToSurfaceCover (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
      (namedQuotientPos_isConnected ρ q u) (namedAttachingDeck ρ q u g p) =
      namedSurfaceDeck ρ q u g
        (attachingToSurfaceCover (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
          (namedQuotientPos_isConnected ρ q u) p) := by
  apply Subtype.ext
  exact Prod.ext (namedAttachingSurfaceLowerLift_deck ρ q u g p)
    (congrArg chainMax (namedAttachingDeck_projection ρ q u g p))

section SurfaceForward
variable (n : ℕ) [NeZero n] (r : Jr ⊕ PUnit.{1} → FreeGroup α)
  (s : Fin n × Bool → FreeGroup α)

abbrev namedSurfaceForward : namedAttachingCover n r s → NamedSurfaceCover r n s :=
  attachingToSurfaceCover (namedSurfaceLabel r n s) (namedQuotientBase r n s)
    (namedQuotientPos_isConnected r n s)

theorem namedSurfaceForward_monotone : Monotone (namedSurfaceForward n r s) :=
  attachingToSurfaceCover_monotone (namedSurfaceLabel r n s)
    (namedQuotientBase r n s) (namedQuotientPos_isConnected r n s)

abbrev namedSurfaceForwardHom := orderCxMap (namedSurfaceForward n r s)
  (namedSurfaceForward_monotone n r s)

abbrev namedAttachingDeckHom (g : NamedPolygonDeckGroup r n s) :=
  orderCxMap (namedAttachingDeck r n s g) (namedAttachingDeck r n s g).monotone

theorem namedSurfaceForward_deck_square (g : NamedPolygonDeckGroup r n s) :
    (namedSurfaceForwardHom n r s).comp
        (namedAttachingDeckHom n r s g) =
      (orderCxMap (namedSurfaceDeck r n s g) (namedSurfaceDeck r n s g).monotone).comp
        (namedSurfaceForwardHom n r s) := by
  exact Hom.ext_orderCx (funext (namedAttachingToSurface_deck r n s g))

end SurfaceForward

def namedAttachingNerveSurfaceChain :
    Ch (namedAttachingCover q ρ u) →+
      (StrictOrdTri (NamedSurfaceCover ρ q u) →₀ ℤ) :=
  normalizeOrdChain2.toAddMonoidHom.comp
    ((chain2 (namedSurfaceForwardHom q ρ u)).toAddMonoidHom.comp decodeOrdNerve2)

theorem namedAttachingNerveSurfaceChain_deck (g : NamedPolygonDeckGroup ρ q u)
    (c : Ch (namedAttachingCover q ρ u)) (hc : c ∈ Inc _)
    (hd : lengthProjection 3 c = c) :
    namedAttachingNerveSurfaceChain ρ q u (cmap (namedAttachingDeck ρ q u g) c) =
      chain2 (strictOrderCxMap (namedSurfaceDeck ρ q u g)
        (namedSurfaceDeck ρ q u g).strictMono) (namedAttachingNerveSurfaceChain ρ q u c) := by
  change normalizeOrdChain2 (chain2 (namedSurfaceForwardHom q ρ u)
    (decodeOrdNerve2 (cmap (namedAttachingDeck ρ q u g) c))) = _
  rw [decodeOrdNerve2_cmap_homogeneous _ (namedAttachingDeck ρ q u g).monotone c hc hd,
    ← chain2_comp_apply, namedSurfaceForward_deck_square, chain2_comp_apply,
    normalizeOrdChain2_strict_map]
  rfl

def namedAttachingNerveMultiple (c : Ch (namedAttachingCover q ρ u)) :
    MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u) →ₗ[ℤ]
      Ch (namedAttachingCover q ρ u) :=
  coeffCombination (fun g => cmap (namedAttachingDeck ρ q u g) c)

def namedQuotientNerveMultiple
    (c : Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u))) :
    MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u) →ₗ[ℤ]
      Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)) :=
  coeffCombination (fun g => cmap (uOrderDeck g) c)

theorem namedAttachingNerveMultiple_mem_inc (c : Ch (namedAttachingCover q ρ u))
    (hc : c ∈ Inc _) (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    namedAttachingNerveMultiple ρ q u c w ∈ Inc _ :=
  coeffCombination_mem (fun g => cmap_mem_inc_of_monotone (namedAttachingDeck ρ q u g).monotone hc) w

theorem namedAttachingNerveMultiple_degree (c : Ch (namedAttachingCover q ρ u))
    (k : ℕ) (hc : lengthProjection k c = c)
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    lengthProjection k (namedAttachingNerveMultiple ρ q u c w) =
      namedAttachingNerveMultiple ρ q u c w :=
  coeffCombination_commutes (lengthProjection k).toIntLinearMap
    (fun g => (lengthProjection_cmap (namedAttachingDeck ρ q u g) k c).trans (congrArg _ hc)) w

theorem namedAttachingNerveSurfaceChain_multiple
    (c : Ch (namedAttachingCover q ρ u)) (hc : c ∈ Inc _)
    (hd : lengthProjection 3 c = c) (v : NamedPolygonPole ρ q u)
    (hv : namedAttachingNerveSurfaceChain ρ q u c = namedPolygonFillingAt ρ q u v)
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    namedAttachingNerveSurfaceChain ρ q u (namedAttachingNerveMultiple ρ q u c w) =
      namedPolygonMultipleAt ρ q u v w :=
  coeffCombination_commutes (namedAttachingNerveSurfaceChain ρ q u).toIntLinearMap
    (fun g => (namedAttachingNerveSurfaceChain_deck ρ q u g c hc hd).trans (congrArg _ hv)) w


theorem namedQuotientNerveMultiple_add (c d)
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    namedQuotientNerveMultiple ρ q u (c + d) w =
      namedQuotientNerveMultiple ρ q u c w + namedQuotientNerveMultiple ρ q u d w := by
  simpa only [namedQuotientNerveMultiple, map_add] using
    coeffCombination_add (fun g => cmap (uOrderDeck g) c) (fun g => cmap (uOrderDeck g) d) w

theorem namedQuotientNerveMultiple_bdry (c)
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    namedQuotientNerveMultiple ρ q u (Nerve.bdry c) w =
      Nerve.bdry (namedQuotientNerveMultiple ρ q u c w) :=
  (coeffCombination_commutes Nerve.bdry.toIntLinearMap (fun g => (cmap_bdry (uOrderDeck g) c).symm) w).symm

theorem namedQuotientNerveMultiple_attaching (c : Ch (namedAttachingCover q ρ u))
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    namedQuotientNerveMultiple ρ q u (cmap Subtype.val c) w =
      cmap Subtype.val (namedAttachingNerveMultiple ρ q u c w) :=
  (coeffCombination_commutes (cmap Subtype.val).toIntLinearMap (fun g => by
    change cmap Subtype.val (cmap (namedAttachingDeck ρ q u g) c) = _
    rw [cmap_comp, cmap_comp]
    rfl) w).symm

theorem namedQuotientNerveMultiple_old (c)
    (hc : c ∈ IncOn (fun p => InQOld (uOrderEnd p)))
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    namedQuotientNerveMultiple ρ q u c w ∈ IncOn (fun p => InQOld (uOrderEnd p)) :=
  coeffCombination_mem (fun g => cmap_mem_incOn (uOrderDeckOrderIso g).monotone
    (fun p hp => (uOrderDeck_end g p).symm ▸ hp) hc) w

theorem namedQuotientNerveMultiple_universal1
    (c : (namedQuotientCover ρ q u).E →₀ ℤ)
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    namedQuotientNerveMultiple ρ q u (universalNerveChain1 c) w =
      universalNerveChain1 (Finsupp.linearCombination ℤ (fun g => chain1
        ((namedQuotientDeck ρ q u).cellHom g)
          c) w.coeff) :=
  (coeffCombination_commutes universalNerveChain1 (fun g => universalNerveChain1_deck g c) w).symm

theorem namedQuotientNerveMultiple_universal2
    (c : (namedQuotientCover ρ q u).F →₀ ℤ)
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    namedQuotientNerveMultiple ρ q u (universalNerveChain2 c) w =
      universalNerveChain2 (Finsupp.linearCombination ℤ (fun g =>
        (namedQuotientDeck ρ q u).faceChains g
          c) w.coeff) :=
  (coeffCombination_commutes universalNerveChain2 (fun g => universalNerveChain2_deck g c) w).symm

/-- The reverse subdivision comparison supplies the missing old three-chain.
The reference is required to be the actual degree-one polygon filling. -/
theorem namedAttaching_polygon_multiple_old_boundary
    (hrho : IsSpineRelator ρ q u)
    (C D : Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)))
    (c d : Ch (namedAttachingCover q ρ u))
    (hc : c ∈ Inc _) (hd : d ∈ Inc _)
    (hcdegree : lengthProjection 3 c = c) (hddegree : lengthProjection 3 d = d)
    (yC yD : Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)))
    (hyC : yC ∈ IncOn (fun p => InQOld (uOrderEnd p)))
    (hyD : yD ∈ IncOn (fun p => InQOld (uOrderEnd p)))
    (hC : C = cmap Subtype.val c + Nerve.bdry yC)
    (hD : D = cmap Subtype.val d + Nerve.bdry yD)
    (v : NamedPolygonPole ρ q u)
    (hreference : namedAttachingNerveSurfaceChain ρ q u d = namedPolygonFillingAt ρ q u v)
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u))
    (hpolygon : namedAttachingNerveSurfaceChain ρ q u c = namedPolygonMultipleAt ρ q u v w)
    (hboundary : Nerve.bdry C = namedQuotientNerveMultiple ρ q u (Nerve.bdry D) w) :
    ∃ y ∈ IncOn (fun p => InQOld (uOrderEnd p)),
      Nerve.bdry y = C - namedQuotientNerveMultiple ρ q u D w := by
  let dw := namedAttachingNerveMultiple ρ q u d w
  have hdw  := namedAttachingNerveMultiple_mem_inc ρ q u d hd w
  have hdwdegree  :=
    namedAttachingNerveMultiple_degree ρ q u d 3 hddegree w
  have hD' : namedQuotientNerveMultiple ρ q u D w =
      cmap Subtype.val dw + Nerve.bdry (namedQuotientNerveMultiple ρ q u yD w) := by
    rw [hD, namedQuotientNerveMultiple_add, namedQuotientNerveMultiple_attaching,
      namedQuotientNerveMultiple_bdry]
  have hb : Nerve.bdry c = Nerve.bdry dw := by
    apply cmap_val_injective _
    have h := hboundary
    rw [namedQuotientNerveMultiple_bdry, hC, hD', map_add, map_add,
      Nerve.bdry_bdry, Nerve.bdry_bdry, add_zero, add_zero, ← cmap_bdry, ← cmap_bdry] at h
    exact h
  have himage : namedAttachingNerveSurfaceChain ρ q u c =
      namedAttachingNerveSurfaceChain ρ q u dw := by
    rw [hpolygon, namedAttachingNerveSurfaceChain_multiple ρ q u d hd hddegree v hreference w]
  obtain ⟨b, hbi, _, hbcd⟩ := attachingSurface_nerve_relative_comparison
    (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
    (namedQuotientPos_isConnected ρ q u) c dw hc hdw hcdegree hdwdegree hb himage
  have hbOld : cmap (Subtype.val : namedAttachingCover q ρ u → _) b ∈
      IncOn (fun p => InQOld (uOrderEnd p)) :=
    cmap_mem_incOn_of_maps
      (f := Subtype.val)
      (fun _ _ h => h) (·.2.1) hbi
  refine ⟨(cmap Subtype.val b :
      Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u))) +
      yC - namedQuotientNerveMultiple ρ q u yD w,
    AddSubgroup.sub_mem _ (AddSubgroup.add_mem _ hbOld hyC)
      (namedQuotientNerveMultiple_old ρ q u yD hyD w), ?_⟩
  rw [map_sub, map_add, ← cmap_bdry, ← hbcd, map_sub, hC, hD']
  let inc : namedAttachingCover q ρ u →
      UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u) := Subtype.val
  change (cmap inc c - cmap inc dw) + Nerve.bdry yC -
      Nerve.bdry (namedQuotientNerveMultiple ρ q u yD w) =
    (cmap inc c + Nerve.bdry yC) -
      (cmap inc dw + Nerve.bdry (namedQuotientNerveMultiple ρ q u yD w))
  abel

/-- The geometric comparison feeds the full coefficient-rigidity theorem.
Its scalar is the actual polygon coefficient at the specified reference pole. -/
theorem finiteSpine_polygon_reference_principal
    (hrho : IsSpineRelator ρ q u)
    (β γ : SpineCoefficients ρ q u)
    (hβ : SpineInternalCycle ρ q u β)
    (hγ : SpineInternalCycle ρ q u γ)
    (c d : Ch (namedAttachingCover q ρ u))
    (hc : c ∈ Inc _) (hd : d ∈ Inc _)
    (hcdegree : lengthProjection 3 c = c) (hddegree : lengthProjection 3 d = d)
    (yC yD : Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)))
    (hyC : yC ∈ IncOn (fun p => InQOld (uOrderEnd p)))
    (hyD : yD ∈ IncOn (fun p => InQOld (uOrderEnd p)))
    (hC : quotientCorrectedRelativeNerveChain q ρ u hrho β =
      cmap Subtype.val c + Nerve.bdry yC)
    (hD : quotientCorrectedRelativeNerveChain q ρ u hrho γ =
      cmap Subtype.val d + Nerve.bdry yD)
    (v : NamedPolygonPole ρ q u)
    (hreference : namedAttachingNerveSurfaceChain ρ q u d = namedPolygonFillingAt ρ q u v)
    (hrelative : PolygonRelativeChain (gc q) (namedSurfaceProjection ρ q u)
      (namedAttachingNerveSurfaceChain ρ q u c))
    (hmark : quotientSurfaceMarkingChains q ρ u hrho
        (singleReceivedSpineMarkingChain q ρ u β) =
      Finsupp.linearCombination ℤ (fun g => chain1
        ((namedQuotientDeck ρ q u).cellHom g)
        (quotientSurfaceMarkingChains q ρ u hrho
          (singleReceivedSpineMarkingChain q ρ u γ)))
        (namedPolygonCoefficientAt ρ q u v (namedAttachingNerveSurfaceChain ρ q u c)).coeff) :
    ∃ a : MonoidAlgebra ℤ (SpineReplacementGroup ρ q u),
      ∀ m, β m = a * γ m := by
  let w := namedPolygonCoefficientAt ρ q u v (namedAttachingNerveSurfaceChain ρ q u c)
  have hpolygon  :=
    namedPolygon_reconstruct_at_pole ρ q u v _ hrelative
  have hboundary : Nerve.bdry (quotientCorrectedRelativeNerveChain q ρ u hrho β) =
      namedQuotientNerveMultiple ρ q u
        (Nerve.bdry (quotientCorrectedRelativeNerveChain q ρ u hrho γ)) w := by
    rw [quotientCorrectedRelativeNerveChain_boundary q ρ u hrho β hβ,
      quotientCorrectedRelativeNerveChain_boundary q ρ u hrho γ hγ,
      namedQuotientNerveMultiple_universal1, hmark]
  obtain ⟨y, hy, hdy⟩ := namedAttaching_polygon_multiple_old_boundary ρ q u hrho
    (quotientCorrectedRelativeNerveChain q ρ u hrho β)
    (quotientCorrectedRelativeNerveChain q ρ u hrho γ)
    c d hc hd hcdegree hddegree yC yD hyC hyD hC hD v hreference w hpolygon hboundary
  apply finiteSpine_relative_class_principal q ρ u hrho β γ hβ hγ w hmark
  refine ⟨y, hy, ?_⟩
  rw [hdy, quotientCorrectedRelativeNerveChain, quotientCorrectedRelativeNerveChain,
    namedQuotientNerveMultiple_universal2, map_sub]

end FiniteChains.Davis.Genus
