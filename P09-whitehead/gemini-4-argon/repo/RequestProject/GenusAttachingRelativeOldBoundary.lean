module

public import RequestProject.GenusNamedSurfaceSubdivision
public import RequestProject.GenusNamedPolygonCoefficients
public import RequestProject.GenusQuotientAttachingFilling
public import RequestProject.StrictOrderNormalizationMaps
public import RequestProject.OrderUniversalDeckChains
public import RequestProject.GenusAllQuotientRelativeRigidity

@[expose] public section

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
  have he : ordNerveChain2 (decodeOrdNerve2 c) = c := (ordNerveChain2_decode hc).trans hd
  calc
    _ = decodeOrdNerve2 (cmap f (ordNerveChain2 (decodeOrdNerve2 c))) := by rw [he]
    _ = _ := by rw [← ordNerveChain2_chain2 f hf, decodeOrdNerve2_encode]

variable {a : P}

theorem uOrderEdge_deck (g : Pi1 (orderCx P) a) (e : OrdEdge (UOrder P a)) :
    uOrderEdge ((orderCxMap (uOrderDeckOrderIso g) (uOrderDeckOrderIso g).monotone).onE e) =
      deckE g (uOrderEdge e) := by
  refine Subtype.ext (Prod.ext rfl (Subtype.ext ?_))
  change (endV (deckV g e.1.1), endV (deckV g e.1.2)) = (endV e.1.1, endV e.1.2)
  simp only [endV_deckV]

theorem uOrderHomInv_deckE (g : Pi1 (orderCx P) a) (e : UE (orderCx P) a) :
    uOrderHomInv.onE (deckE g e) =
      (orderCxMap (uOrderDeckOrderIso g) (uOrderDeckOrderIso g).monotone).onE
        (uOrderHomInv.onE e) := by
  have hinv (e : UE (orderCx P) a) : uOrderEdge (uOrderHomInv.onE e) = e :=
    homInv_onE_apply uOrderHom Function.bijective_id
      ⟨uOrderEdge_injective, uOrderEdge_surjective⟩
      ⟨uOrderFace_injective, uOrderFace_surjective⟩ e
  apply uOrderEdge_injective
  rw [hinv, uOrderEdge_deck, hinv]

theorem uOrderHomInv_deckF (g : Pi1 (orderCx P) a) (t : UF (orderCx P) a) :
    uOrderHomInv.onF (deckF g t) =
      (orderCxMap (uOrderDeckOrderIso g) (uOrderDeckOrderIso g).monotone).onF
        (uOrderHomInv.onF t) := by
  have hinv (t : UF (orderCx P) a) : uOrderFace (uOrderHomInv.onF t) = t :=
    homInv_onF_apply uOrderHom Function.bijective_id
      ⟨uOrderEdge_injective, uOrderEdge_surjective⟩
      ⟨uOrderFace_injective, uOrderFace_surjective⟩ t
  apply uOrderFace_injective
  rw [hinv, uOrderFace_deck, hinv]

theorem universalNerveChain1_deck (g : Pi1 (orderCx P) a) (c : UE (orderCx P) a →₀ ℤ) :
    universalNerveChain1 (chain1 ((univDeck (orderCx P) a).cellHom g) c) =
      cmap (uOrderDeck g) (universalNerveChain1 c) := by
  have he : chain1 uOrderHomInv (chain1 ((univDeck (orderCx P) a).cellHom g) c) =
      chain1 (orderCxMap (uOrderDeckOrderIso g) (uOrderDeckOrderIso g).monotone)
        (chain1 uOrderHomInv c) := by
    change Finsupp.mapDomain uOrderHomInv.onE (Finsupp.mapDomain (deckE g) c) =
      Finsupp.mapDomain _ (Finsupp.mapDomain uOrderHomInv.onE c)
    rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    exact congrArg (Finsupp.mapDomain · c) (funext (uOrderHomInv_deckE g))
  change ordNerveChain1 (chain1 uOrderHomInv
    (chain1 ((univDeck (orderCx P) a).cellHom g) c)) = _
  rw [he, ordNerveChain1_chain1]; rfl

theorem universalNerveChain2_deck (g : Pi1 (orderCx P) a) (c : UF (orderCx P) a →₀ ℤ) :
    universalNerveChain2 ((univDeck (orderCx P) a).faceChains g c) =
      cmap (uOrderDeck g) (universalNerveChain2 c) := by
  have he : chain2 uOrderHomInv ((univDeck (orderCx P) a).faceChains g c) =
      chain2 (orderCxMap (uOrderDeckOrderIso g) (uOrderDeckOrderIso g).monotone)
        (chain2 uOrderHomInv c) := by
    change Finsupp.mapDomain uOrderHomInv.onF (Finsupp.mapDomain (deckF g) c) =
      Finsupp.mapDomain _ (Finsupp.mapDomain uOrderHomInv.onF c)
    rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    exact congrArg (Finsupp.mapDomain · c) (funext (uOrderHomInv_deckF g))
  change ordNerveChain2 (chain2 uOrderHomInv ((univDeck (orderCx P) a).faceChains g c)) = _
  rw [he, ordNerveChain2_chain2]; rfl

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)

def namedAttachingDeck (g : NamedPolygonDeckGroup ρ q u) :
    namedAttachingCover q ρ u ≃o namedAttachingCover q ρ u where
  toFun p := ⟨uOrderDeck g p.1, by rw [uOrderDeck_end]; exact p.2⟩
  invFun p := ⟨uOrderDeck g⁻¹ p.1, by rw [uOrderDeck_end]; exact p.2⟩
  left_inv p := Subtype.ext (by change deckV g⁻¹ (deckV g p.1) = p.1; rw [← deckV_mul, inv_mul_cancel, deckV_one])
  right_inv p := Subtype.ext (by change deckV g (deckV g⁻¹ p.1) = p.1; rw [← deckV_mul, mul_inv_cancel, deckV_one])
  map_rel_iff' := (uOrderDeckOrderIso g).map_rel_iff

theorem namedAttachingIntoUniversal_deck_square (g : NamedPolygonDeckGroup ρ q u) :
    (namedAttachingIntoUniversal q ρ u).comp
      (orderCxMap (namedAttachingDeck ρ q u g) (namedAttachingDeck ρ q u g).monotone) =
      ((univDeck (orderCx (namedQuotientPos ρ q u))
        (namedQuotientBase ρ q u)).cellHom g).comp (namedAttachingIntoUniversal q ρ u) :=
  Hom.ext' rfl
    (funext fun e => uOrderEdge_deck g ((orderCxMap Subtype.val (fun _ _ h => h)).onE e))
    (funext fun t => uOrderFace_deck g ((orderCxMap Subtype.val (fun _ _ h => h)).onF t))

theorem namedAttachingIntoUniversal_chain1_deck (g : NamedPolygonDeckGroup ρ q u)
    (c : OrdEdge (namedAttachingCover q ρ u) →₀ ℤ) :
    chain1 (namedAttachingIntoUniversal q ρ u)
      (chain1 (orderCxMap (namedAttachingDeck ρ q u g)
        (namedAttachingDeck ρ q u g).monotone) c) =
      chain1 ((univDeck (orderCx (namedQuotientPos ρ q u))
        (namedQuotientBase ρ q u)).cellHom g)
          (chain1 (namedAttachingIntoUniversal q ρ u) c) := by
  rw [← chain1_comp_apply, namedAttachingIntoUniversal_deck_square, chain1_comp_apply]

theorem namedAttachingDeck_projection (g : NamedPolygonDeckGroup ρ q u)
    (p : namedAttachingCover q ρ u) :
    qAttachingCoverEnd (namedQuotientBase ρ q u) (namedAttachingDeck ρ q u g p) =
      qAttachingCoverEnd (namedQuotientBase ρ q u) p := by
  change qPositiveOldOrderIso ⟨uOrderEnd (uOrderDeck g p.1), _⟩ =
    qPositiveOldOrderIso ⟨uOrderEnd p.1, _⟩
  exact congrArg qPositiveOldOrderIso (Subtype.ext (uOrderDeck_end g p.1))

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
  refine (uOrderEnd_isPosetCover (namedQuotientPos_isConnected ρ q u)).down_inj
    h₁.1 ((uOrderDeckOrderIso g).monotone h₂.1) ?_
  rw [h₁.2, uOrderDeck_end, h₂.2, namedAttachingDeck_projection]

theorem namedAttachingToSurface_deck (g : NamedPolygonDeckGroup ρ q u)
    (p : namedAttachingCover q ρ u) :
    attachingToSurfaceCover (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
      (namedQuotientPos_isConnected ρ q u) (namedAttachingDeck ρ q u g p) =
      namedSurfaceDeck ρ q u g
        (attachingToSurfaceCover (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
          (namedQuotientPos_isConnected ρ q u) p) :=
  Subtype.ext (Prod.ext (namedAttachingSurfaceLowerLift_deck ρ q u g p)
    (congrArg chainMax (namedAttachingDeck_projection ρ q u g p)))

def namedAttachingNerveSurfaceChain :
    Ch (namedAttachingCover q ρ u) →+
      (StrictOrdTri (NamedSurfaceCover ρ q u) →₀ ℤ) :=
  normalizeOrdChain2.toAddMonoidHom.comp
    ((chain2 (orderCxMap
      (attachingToSurfaceCover (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
        (namedQuotientPos_isConnected ρ q u))
      (attachingToSurfaceCover_monotone (namedSurfaceLabel ρ q u)
        (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u)))).toAddMonoidHom.comp
      decodeOrdNerve2)

theorem namedAttachingNerveSurfaceChain_deck (g : NamedPolygonDeckGroup ρ q u)
    (c : Ch (namedAttachingCover q ρ u)) (hc : c ∈ Inc _)
    (hd : lengthProjection 3 c = c) :
    namedAttachingNerveSurfaceChain ρ q u (cmap (namedAttachingDeck ρ q u g) c) =
      chain2 (strictOrderCxMap (namedSurfaceDeck ρ q u g)
        (namedSurfaceDeck ρ q u g).strictMono) (namedAttachingNerveSurfaceChain ρ q u c) := by
  let F : namedAttachingCover q ρ u → NamedSurfaceCover ρ q u :=
    attachingToSurfaceCover (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
      (namedQuotientPos_isConnected ρ q u)
  have hF : Monotone F := attachingToSurfaceCover_monotone (namedSurfaceLabel ρ q u)
    (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u)
  have hs : (orderCxMap F hF).comp
      (orderCxMap (namedAttachingDeck ρ q u g) (namedAttachingDeck ρ q u g).monotone) =
      (orderCxMap (namedSurfaceDeck ρ q u g) (namedSurfaceDeck ρ q u g).monotone).comp
        (orderCxMap F hF) :=
    Hom.ext' (funext (namedAttachingToSurface_deck ρ q u g))
      (funext fun _ => Subtype.ext (Prod.ext (namedAttachingToSurface_deck ρ q u g _)
        (namedAttachingToSurface_deck ρ q u g _)))
      (funext fun _ => Subtype.ext (Prod.ext (namedAttachingToSurface_deck ρ q u g _)
        (Prod.ext (namedAttachingToSurface_deck ρ q u g _)
          (namedAttachingToSurface_deck ρ q u g _))))
  change normalizeOrdChain2 (chain2 (orderCxMap F hF)
    (decodeOrdNerve2 (cmap (namedAttachingDeck ρ q u g) c))) = _
  rw [decodeOrdNerve2_cmap_homogeneous _ (namedAttachingDeck ρ q u g).monotone c hc hd,
    ← chain2_comp_apply, hs, chain2_comp_apply, normalizeOrdChain2_strict_map]
  rfl

theorem apply_linComb {M N G : Type*} [AddCommGroup M] [AddCommGroup N] {F : Type*}
    [FunLike F M N] [AddMonoidHomClass F M N] (φ : F) (f : G → M) (l : G →₀ ℤ) :
    φ (Finsupp.linearCombination ℤ f l) = Finsupp.linearCombination ℤ (fun g => φ (f g)) l := by
  induction l using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single g n => simp

def namedAttachingNerveMultiple (c : Ch (namedAttachingCover q ρ u))
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) : Ch (namedAttachingCover q ρ u) :=
  Finsupp.linearCombination ℤ (fun g => cmap (namedAttachingDeck ρ q u g) c) w.coeff

def namedQuotientNerveMultiple
    (c : Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)))
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)) :=
  Finsupp.linearCombination ℤ (fun g => cmap (uOrderDeck g) c) w.coeff

theorem namedAttachingNerveMultiple_mem_inc (c : Ch (namedAttachingCover q ρ u))
    (hc : c ∈ Inc _) (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    namedAttachingNerveMultiple ρ q u c w ∈ Inc _ := by
  unfold namedAttachingNerveMultiple
  induction w.coeff using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using AddSubgroup.add_mem _ hx hy
  | single g n =>
      simpa using AddSubgroup.zsmul_mem _
        (cmap_mem_inc_of_monotone (namedAttachingDeck ρ q u g).monotone hc) n

theorem namedQuotientNerveMultiple_old (c)
    (hc : c ∈ IncOn (fun p => InQOld (uOrderEnd p)))
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    namedQuotientNerveMultiple ρ q u c w ∈ IncOn (fun p => InQOld (uOrderEnd p)) := by
  obtain ⟨d, hd, rfl⟩ := exists_preimage_of_mem_incOn
    (fun p : UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u) =>
      InQOld (uOrderEnd p)) hc
  unfold namedQuotientNerveMultiple
  induction w.coeff using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using AddSubgroup.add_mem _ hx hy
  | single g n =>
      rw [Finsupp.linearCombination_single]
      refine AddSubgroup.zsmul_mem _ ?_ n
      rw [cmap_comp]
      exact cmap_mem_incOn_of_maps
        (f := fun p : {p : UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u) //
          InQOld (uOrderEnd p)} => uOrderDeck g p.1)
        ((uOrderDeckOrderIso g).monotone.comp fun _ _ h => h)
        (fun p => by change InQOld (uOrderEnd (uOrderDeck g p.1)); rw [uOrderDeck_end]; exact p.2) hd

theorem finiteSpine_polygon_reference_principal
    (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))
    (β γ : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))
    (hβ : ∀ z : SpinePresentationGen q,
      (∑ m, β m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0)
    (hγ : ∀ z : SpinePresentationGen q,
      (∑ m, γ m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0)
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
        ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i))) =
      Finsupp.linearCombination ℤ (fun g => chain1
        ((univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).cellHom g)
        (quotientSurfaceMarkingChains q ρ u hrho
          ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => γ (Sum.inr i)))))
        (namedPolygonCoefficientAt ρ q u v (namedAttachingNerveSurfaceChain ρ q u c)).coeff) :
    ∃ a : MonoidAlgebra ℤ (PresGroup (substPresF ρ (finiteSpineWordBlock q u))),
      ∀ m, β m = a * γ m := by
  let w := namedPolygonCoefficientAt ρ q u v (namedAttachingNerveSurfaceChain ρ q u c)
  let dw := namedAttachingNerveMultiple ρ q u d w
  have hpolygon : namedAttachingNerveSurfaceChain ρ q u c = namedPolygonMultipleAt ρ q u v w :=
    namedPolygon_reconstruct_at_pole ρ q u v _ hrelative
  have hboundary : Nerve.bdry (quotientCorrectedRelativeNerveChain q ρ u hrho β) =
      namedQuotientNerveMultiple ρ q u
        (Nerve.bdry (quotientCorrectedRelativeNerveChain q ρ u hrho γ)) w := by
    rw [quotientCorrectedRelativeNerveChain_boundary q ρ u hrho β hβ,
      quotientCorrectedRelativeNerveChain_boundary q ρ u hrho γ hγ, hmark]
    unfold namedQuotientNerveMultiple
    induction w.coeff using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | single g n => simp [universalNerveChain1_deck]
  have hdwdegree : lengthProjection 3 dw = dw := by
    change lengthProjection 3 (namedAttachingNerveMultiple ρ q u d w) = _
    rw [namedAttachingNerveMultiple, apply_linComb (lengthProjection 3)]
    simp only [lengthProjection_cmap, hddegree]; rfl
  have hD' : namedQuotientNerveMultiple ρ q u
      (quotientCorrectedRelativeNerveChain q ρ u hrho γ) w =
      cmap Subtype.val dw + Nerve.bdry (namedQuotientNerveMultiple ρ q u yD w) := by
    change namedQuotientNerveMultiple ρ q u _ w =
      cmap Subtype.val (namedAttachingNerveMultiple ρ q u d w) + _
    rw [hD, namedQuotientNerveMultiple, namedAttachingNerveMultiple,
      namedQuotientNerveMultiple, apply_linComb (cmap Subtype.val), apply_linComb Nerve.bdry]
    induction w.coeff using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]; abel
    | single g n => simp only [Finsupp.linearCombination_single, map_add, smul_add, cmap_comp, cmap_bdry]; rfl
  have hb : Nerve.bdry c = Nerve.bdry dw := by
    apply cmap_val_injective _
      ⟨(namedAttachingReference q ρ u hrho 1).1, (namedAttachingReference q ρ u hrho 1).2⟩
    have h : Nerve.bdry (quotientCorrectedRelativeNerveChain q ρ u hrho β) =
        Nerve.bdry (namedQuotientNerveMultiple ρ q u
          (quotientCorrectedRelativeNerveChain q ρ u hrho γ) w) := by
      rw [hboundary, namedQuotientNerveMultiple, namedQuotientNerveMultiple,
        apply_linComb Nerve.bdry]
      simp only [cmap_bdry]
    rw [hC, hD', map_add, map_add,
      Nerve.bdry_bdry, Nerve.bdry_bdry, add_zero, add_zero, ← cmap_bdry, ← cmap_bdry] at h
    exact h
  have himage : namedAttachingNerveSurfaceChain ρ q u c =
      namedAttachingNerveSurfaceChain ρ q u dw := by
    change _ = namedAttachingNerveSurfaceChain ρ q u (namedAttachingNerveMultiple ρ q u d w)
    rw [hpolygon, namedPolygonMultipleAt, namedAttachingNerveMultiple,
      apply_linComb (namedAttachingNerveSurfaceChain ρ q u)]
    simp only [namedAttachingNerveSurfaceChain_deck ρ q u _ d hd hddegree, hreference]; rfl
  obtain ⟨b, hbi, _, hbcd⟩ := attachingSurface_nerve_relative_comparison
    (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
    (namedQuotientPos_isConnected ρ q u) c dw hc
    (namedAttachingNerveMultiple_mem_inc ρ q u d hd w) hcdegree hdwdegree hb himage
  have hbOld : cmap (Subtype.val : namedAttachingCover q ρ u → _) b ∈
      IncOn (fun p => InQOld (uOrderEnd p)) :=
    cmap_mem_incOn_of_maps
      (f := (Subtype.val : namedAttachingCover q ρ u →
        UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)))
      (fun _ _ h => h) (fun p => p.2.1) hbi
  apply finiteSpine_relative_class_principal q ρ u hrho β γ hβ hγ w hmark
  let cb : Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)) := cmap Subtype.val b
  refine ⟨cb + yC - namedQuotientNerveMultiple ρ q u yD w,
    AddSubgroup.sub_mem _ (AddSubgroup.add_mem _ hbOld hyC)
      (namedQuotientNerveMultiple_old ρ q u yD hyD w), ?_⟩
  have hdy : Nerve.bdry (cb + yC - namedQuotientNerveMultiple ρ q u yD w) =
      quotientCorrectedRelativeNerveChain q ρ u hrho β -
        namedQuotientNerveMultiple ρ q u
          (quotientCorrectedRelativeNerveChain q ρ u hrho γ) w := by
    rw [map_sub, map_add, ← cmap_bdry, ← hbcd, map_sub, hC, hD']
    let inc : namedAttachingCover q ρ u →
      UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u) := Subtype.val
    change (cmap inc c - cmap inc dw) + Nerve.bdry yC -
        Nerve.bdry (namedQuotientNerveMultiple ρ q u yD w) =
      (cmap inc c + Nerve.bdry yC) -
        (cmap inc dw + Nerve.bdry (namedQuotientNerveMultiple ρ q u yD w))
    abel
  have hu2 (z : (uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).F →₀ ℤ) :
      namedQuotientNerveMultiple ρ q u (universalNerveChain2 z) w =
      universalNerveChain2 (Finsupp.linearCombination ℤ (fun g =>
        (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains g z) w.coeff) := by
    unfold namedQuotientNerveMultiple
    induction w.coeff using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | single g n => simp [universalNerveChain2_deck]
  rw [hdy, quotientCorrectedRelativeNerveChain, quotientCorrectedRelativeNerveChain, hu2, map_sub]
