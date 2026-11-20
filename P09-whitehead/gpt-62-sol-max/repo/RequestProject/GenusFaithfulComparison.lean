module

public import RequestProject.GenusQuotientReceiver
public import RequestProject.FinsuppBasis

@[expose] public section

/-! The forward comparison with the actual quotient and its reverse reading.

-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
theorem pi1Conj_empty_apply {K : Complex2} (a : K.V) (z : Pi1 K a) :
    pi1Conj (show IsPath K.src K.tgt [] a a from rfl) z = z := by
  refine Quotient.inductionOn z ?_
  intro p
  apply Quotient.sound
  simp [conjLoop]
end FiniteChains.Comb

namespace FiniteChains.Comb.OrdCocycle
universe v w
variable {P : Type} [Preorder P] {G : Type v} [Group G] {H : Type w} [Group H]

theorem monodromy_baseEq (c : OrdCocycle P G) {a b : P} (h : a = b)
    (z : Pi1 (orderCx P) a) :
    c.monodromy b (pi1BaseEqEquiv h z) = c.monodromy a z := by
  subst b
  rfl

theorem postcompose_monodromy (c : OrdCocycle P G) (φ : G →* H) (a : P) :
    (c.postcompose φ).monodromy a = φ.comp (c.monodromy a) := by
  apply MonoidHom.ext
  intro z
  refine Quotient.inductionOn z ?_
  intro p
  exact postcompose_readPath c φ p.1

end FiniteChains.Comb.OrdCocycle

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}
  {X : Type} [Preorder X] {att : NeSpx A →o X}

theorem quotientOldBasedInclusion_surface (s : NeSpx A)
    (p : Loop (orderCx (NeSpx A)) s) :
    quotientOldBasedInclusion (att := att) s
      (Pi1.mk ⟨mapPath (surfCx A) p.1, isPath_mapPath (surfCx A) p.2⟩) =
      pi1Map (orderCxMap (qNew (att := att)) qNew_monotone) (att s)
        (Pi1.mk ⟨mapPath (orderCxMap att att.monotone) p.1,
          isPath_mapPath _ p.2⟩) := by
  let i := orderCxMap (qNew (att := att)) qNew_monotone
  let j := orderCxMap (qOldIncl (att := att)) qOldIncl_monotone
  let a := orderCxMap att att.monotone
  let z := Pi1.mk p
  let h := qNew_att_le_qOldIncl (att := att)
  change pi1Conj (isPath_ordPos (h s)) (pi1Map j _ (pi1Map (surfCx A) s z)) =
    pi1Map i _ (pi1Map a s z)
  erw [← pi1Map_comp_apply (surfCx A) j s z, ← pi1Map_comp_apply a i s z,
    pi1Map_orderCx_le (qNew_monotone.comp att.monotone)
      (qOldIncl_monotone.comp posQCube_monotone) h z,
    pi1Conj_pi1Conj, pi1Conj_congr _ (isPath_nil' (qNew (att s))) (htpy_ordPos_ordNeg (h s))]
  exact pi1Conj_empty_apply _ _

end FiniteChains.Davis

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily
variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)
  (hrho : IsSpineRelator ρ q u)

noncomputable abbrev namedBasePos :=
  PresPos (genusNonemptyW (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q)

noncomputable abbrev namedAtt : NeSpx (cmpRel (GenusVertex q)) →o namedBasePos ρ q u :=
  genusNonemptyAtt (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q

theorem namedBasePos_isConnected : IsConnected (orderCx (namedBasePos ρ q u)) :=
  genusNonemptyW_isConnected (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q

noncomputable def namedBaseAlpha : PresGroup (namedPres ρ q u) →*
    Pi1 (orderCx (namedBasePos ρ q u)) (namedAtt ρ q u (gBase q)) :=
  (pi1BaseEqEquiv (genusNonemptyAtt_base (namedPres ρ q u)
    (namedA (α := α) q) (namedB (α := α) q) q).symm).toMonoidHom.comp
      (alphaHomW (namedPres ρ q u)
        (genusNonemptyW (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q)
        (mk_genusNonemptyW _ _ _ _ (namedPres_surface ρ q u)))

noncomputable def namedBaseIntoQuotient : PresGroup (namedPres ρ q u) →*
    NamedQuotientGroup ρ q u :=
  (pi1Map (orderCxMap (qNew (att := namedAtt ρ q u)) qNew_monotone)
    (namedAtt ρ q u (gBase q))).comp (namedBaseAlpha ρ q u)

noncomputable def sourceIntoNamedQuotient : PresGroup ρ →*
    NamedQuotientGroup ρ q u :=
  (namedBaseIntoQuotient ρ q u).comp
    (SurfaceWordExpansion.inclusion ρ u (finitePairs q) hrho)

theorem namedBaseAlpha_marked (x : Fin q × Bool) :
    namedBaseAlpha ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) =
      Pi1.mk ⟨mapPath (orderCxMap (namedAtt ρ q u) (namedAtt ρ q u).monotone)
        (gSig q (x.1.val, x.2)),
        isPath_mapPath _ (isPath_gSig q (x.1.val, x.2))⟩ := by
  let w := genusNonemptyW (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q
  let p : Loop (orderCx (namedBasePos ρ q u)) (namedAtt ρ q u (gBase q)) :=
    ⟨genLoop w (Sum.inr x), by
      erw [genusNonemptyAtt_base _ _ _ _]
      exact isPath_genLoop w (Sum.inr x)⟩
  have hp : namedBaseAlpha ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) =
      Pi1.mk p := by
    erw [namedBaseAlpha, MonoidHom.comp_apply, alphaHomW_gen]
    exact pi1BaseEqEquiv_mk _ ⟨genLoop w (Sum.inr x), isPath_genLoop w (Sum.inr x)⟩ p rfl
  erw [hp]
  apply Quotient.sound
  have hh := genusNonempty_hread (namedPres ρ q u) (namedA (α := α) q)
    (namedB (α := α) q) q PUnit.unit.{1} (x.1.val, x.2)
  simp only [List.nil_append, revPath_nil, List.append_nil] at hh
  have hl : genusLw (namedA (α := α) q) (namedB (α := α) q) q
      PUnit.unit.{1} (x.1.val, x.2) = [(Sum.inr x, true)] := namedLw_eq q PUnit.unit x
  erw [hl] at hh
  change Htpy (orderCx (namedBasePos ρ q u)) (namedAtt ρ q u (gBase q))
    (namedAtt ρ q u (gBase q)) (genLoop w (Sum.inr x))
    (mapPath (orderCxMap (namedAtt ρ q u) (namedAtt ρ q u).monotone)
      (gSig q (x.1.val, x.2)))
  simpa [namedAtt, genusNonemptyAtt_base, wordLoop, letterLoop] using hh.symm

theorem namedSpineIntoQuotient_marked (x : Fin q × Bool) :
    namedSpineIntoQuotient ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) =
      sourceIntoNamedQuotient ρ q u hrho (QuotientGroup.mk (u x)) := by
  change quotientOldBasedInclusion (att := namedAtt ρ q u) (gBase q)
    (namedSpineToOldEquiv q (QuotientGroup.mk (FreeGroup.of (Sum.inr x)))) = _
  erw [namedSpineToOld_marked, spineMarkedLoop_toOld_class,
    quotientOldBasedInclusion_surface (att := namedAtt ρ q u) (gBase q)
      ⟨gSig q (x.1.val, x.2), isPath_gSig q (x.1.val, x.2)⟩]
  erw [← namedBaseAlpha_marked]
  change namedBaseIntoQuotient ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) =
    namedBaseIntoQuotient ρ q u
      (SurfaceWordExpansion.inclusion ρ u (finitePairs q) hrho (QuotientGroup.mk (u x)))
  exact congrArg (namedBaseIntoQuotient ρ q u)
    (SurfaceWordExpansion.name_eq_word ρ u (finitePairs q) x)

theorem namedBaseCocycle_alpha {G : Type} [Group G] (j : PresGroup ρ →* G)
    (z : PresGroup (namedPres ρ q u)) :
    (namedBaseCocycle ρ q u hrho j).monodromy (namedAtt ρ q u (gBase q))
      (namedBaseAlpha ρ q u z) = namedBaseReceiver ρ q u hrho j z := by
  erw [namedBaseAlpha, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    OrdCocycle.monodromy_baseEq]
  erw [namedBaseCocycle, OrdCocycle.postcompose_monodromy,
    presGroupCocycle_monodromy, MonoidHom.comp_apply, readingPresW_alphaHomW]

/-- The reverse receiver constructed on Q is a left inverse on the whole
source presentation group, not just on its chosen generators. -/
theorem exists_namedQuotientReading_both {G : Type} [Group G]
    (j : PresGroup ρ →* G) (φ : PresGroup (namedSpinePresentation q) →* G)
    (hm : ∀ x : Fin q × Bool,
      φ (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) = j (QuotientGroup.mk (u x))) :
    ∃ ψ : NamedQuotientGroup ρ q u →* G,
      ψ.comp (namedSpineIntoQuotient ρ q u) = φ ∧
      ψ.comp (sourceIntoNamedQuotient ρ q u hrho) = j := by
  obtain ⟨ψ, ho, hb⟩ := exists_namedQuotientReading ρ q u hrho j φ hm
  refine ⟨ψ, ho, ?_⟩
  apply MonoidHom.ext
  intro z
  have hh := DFunLike.congr_fun hb
    (namedBaseAlpha ρ q u (SurfaceWordExpansion.inclusion ρ u (finitePairs q) hrho z))
  change ψ (sourceIntoNamedQuotient ρ q u hrho z) = j z
  erw [hh]
  erw [namedBaseCocycle_alpha]
  change j (SurfaceWordExpansion.elimination ρ u (finitePairs q) hrho
    (SurfaceWordExpansion.inclusion ρ u (finitePairs q) hrho z)) = j z
  erw [SurfaceWordExpansion.elimination_inclusion]

section ComparisonMaps
variable {H : Type} [Group H] (j : PresGroup ρ →* H)
  (φ : PresGroup (namedSpinePresentation q) →* H)
  (hm : ∀ x : Fin q × Bool,
    φ (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) = j (QuotientGroup.mk (u x)))

noncomputable def finiteSpineComparisonFree : FreeGroup (α ⊕ SpinePresentationGen q) →* H :=
  FreeGroup.lift (Sum.elim (fun a => j (QuotientGroup.mk (FreeGroup.of a)))
    (fun z => φ (QuotientGroup.mk (FreeGroup.of (Sum.inl z)))))

theorem finiteSpineComparisonFree_old (w : FreeGroup α) :
    finiteSpineComparisonFree ρ q j φ (FreeGroup.map Sum.inl w) =
      j (QuotientGroup.mk w) := by
  have h : (finiteSpineComparisonFree ρ q j φ).comp (FreeGroup.map Sum.inl) =
      j.comp (QuotientGroup.mk' (relSub ρ)) := by
    apply FreeGroup.ext_hom
    intro a
    simp [finiteSpineComparisonFree]
  exact DFunLike.congr_fun h w

include hm in
theorem finiteSpineComparisonFree_substitution (s : PUnit.{1}) :
    ((finiteSpineComparisonFree ρ q j φ).comp
      (blockSubst (Zt := fun _ : PUnit.{1} => SpinePresentationGen q) (fun _ => u) s)).comp
      (FreeGroup.map Sum.swap) = φ.comp (QuotientGroup.mk' (relSub (namedSpinePresentation q))) := by
  apply FreeGroup.ext_hom
  rintro (z | x)
  · simp [finiteSpineComparisonFree]
  · simp only [MonoidHom.comp_apply, FreeGroup.map.of, Sum.swap_inr,
      blockSubst_of_inl]
    erw [finiteSpineComparisonFree_old]
    exact (hm x).symm

noncomputable def finiteSpineComparisonMaps :
    BlockMaps ρ (finiteSpineWordBlock q u) j where
  b _ := finiteSpineComparisonFree ρ q j φ
  mark _ a := by simp [finiteSpineComparisonFree]
  rel s m := by
    have h := DFunLike.congr_fun
      (finiteSpineComparisonFree_substitution ρ q u j φ hm s) (namedSpinePresentation q m)
    change finiteSpineComparisonFree ρ q j φ
      (blockSubst (Zt := fun _  => SpinePresentationGen q) (fun _ => u) s
        (FreeGroup.map Sum.swap (namedSpinePresentation q m))) = 1
    simp only [MonoidHom.comp_apply] at h
    erw [h]
    have hz : (QuotientGroup.mk (namedSpinePresentation q m) :
        PresGroup (namedSpinePresentation q)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨m, rfl⟩)
    change φ (QuotientGroup.mk (namedSpinePresentation q m)) = 1
    erw [hz, map_one]

end ComparisonMaps

noncomputable def finiteSpineToQuotient :
    SpineReplacementGroup ρ q u →*
      NamedQuotientGroup ρ q u :=
  (finiteSpineComparisonMaps ρ q u (sourceIntoNamedQuotient ρ q u hrho)
    (namedSpineIntoQuotient ρ q u) (namedSpineIntoQuotient_marked ρ q u hrho)).psi

noncomputable def singleSpineNamedReceiver : PresGroup (namedSpinePresentation q) →*
    SpineReplacementGroup ρ q u :=
  familySpineHom ρ (fun _  => q) (fun _ => u) PUnit.unit

theorem singleSpineNamedReceiver_marked (x : Fin q × Bool) :
    singleSpineNamedReceiver ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) =
      substHomF ρ (finiteSpineWordBlock q u) (finiteSpineWordBlock_filled ρ q u hrho)
        (QuotientGroup.mk (u x)) := familySpineHom_marked ρ (fun _  => q) (fun _ => u) PUnit.unit x

theorem singleSpineNamedReceiver_internal (z : SpinePresentationGen q) :
    singleSpineNamedReceiver ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inl z))) =
      QuotientGroup.mk (FreeGroup.of (Sum.inr ⟨PUnit.unit, z⟩)) := by
  tauto

theorem finiteSpineToQuotient_source :
    (finiteSpineToQuotient ρ q u hrho).comp
      (substHomF ρ (finiteSpineWordBlock q u) (finiteSpineWordBlock_filled ρ q u hrho)) =
        sourceIntoNamedQuotient ρ q u hrho :=
  BlockMaps.psi_comp_substHomF _ (finiteSpineWordBlock_filled ρ q u hrho)

theorem finiteSpineToQuotient_internal (z : SpinePresentationGen q) :
    finiteSpineToQuotient ρ q u hrho
      (QuotientGroup.mk (FreeGroup.of (Sum.inr ⟨PUnit.unit, z⟩))) =
      namedSpineIntoQuotient ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inl z))) := by
  simp only [finiteSpineToQuotient, BlockMaps.psi_mk, FreeGroup.lift_apply_of,
    BlockMaps.gen_inr, finiteSpineComparisonMaps, finiteSpineComparisonFree, Sum.elim_inr]

/-- The same forward comparison transports the entire block receiver,
including its internal generators, to the genuine geometric block map. -/
theorem finiteSpineToQuotient_spine :
    (finiteSpineToQuotient ρ q u hrho).comp (singleSpineNamedReceiver ρ q u) =
      namedSpineIntoQuotient ρ q u := by
  have h : ((finiteSpineToQuotient ρ q u hrho).comp (singleSpineNamedReceiver ρ q u)).comp
      (QuotientGroup.mk' (relSub (namedSpinePresentation q))) =
      (namedSpineIntoQuotient ρ q u).comp
        (QuotientGroup.mk' (relSub (namedSpinePresentation q))) := by
    apply FreeGroup.ext_hom
    rintro (z | x)
    · change finiteSpineToQuotient ρ q u hrho
        (singleSpineNamedReceiver ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inl z)))) = _
      erw [singleSpineNamedReceiver_internal, finiteSpineToQuotient_internal]
      rfl
    · change finiteSpineToQuotient ρ q u hrho
        (singleSpineNamedReceiver ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inr x)))) = _
      erw [singleSpineNamedReceiver_marked ρ q u hrho]
      have hs := DFunLike.congr_fun (finiteSpineToQuotient_source ρ q u hrho)
        (QuotientGroup.mk (u x))
      exact hs.trans (namedSpineIntoQuotient_marked ρ q u hrho x).symm
  apply MonoidHom.ext
  intro z
  refine QuotientGroup.induction_on z ?_
  intro w
  exact DFunLike.congr_fun h w

/-- The actual single substituted group has a left inverse to its geometric
comparison. In particular no extra injectivity premise is needed for the map
used to transport the full group-ring coefficients into the universal cover. -/
theorem finiteSpineToQuotient_has_leftInverse :
    ∃ ψ : NamedQuotientGroup ρ q u →*
        SpineReplacementGroup ρ q u,
      ψ.comp (finiteSpineToQuotient ρ q u hrho) = MonoidHom.id _ := by
  let j := substHomF ρ (finiteSpineWordBlock q u) (finiteSpineWordBlock_filled ρ q u hrho)
  let φ := singleSpineNamedReceiver ρ q u
  obtain ⟨ψ, ho, hb⟩ := exists_namedQuotientReading_both ρ q u hrho j φ
    (singleSpineNamedReceiver_marked ρ q u hrho)
  refine ⟨ψ, ?_⟩
  have hfree : ((ψ.comp (finiteSpineToQuotient ρ q u hrho)).comp
      (QuotientGroup.mk' (relSub (spineReplacementPres ρ q u)))) =
      QuotientGroup.mk' (relSub (spineReplacementPres ρ q u)) := by
    apply FreeGroup.ext_hom
    rintro (a | ⟨s, z⟩)
    · have hs := DFunLike.congr_fun (finiteSpineToQuotient_source ρ q u hrho)
        (QuotientGroup.mk (FreeGroup.of a))
      change ψ (finiteSpineToQuotient ρ q u hrho
        (j (QuotientGroup.mk (FreeGroup.of a)))) = j (QuotientGroup.mk (FreeGroup.of a))
      erw [hs]
      exact DFunLike.congr_fun hb (QuotientGroup.mk (FreeGroup.of a))
    · cases s
      change ψ (finiteSpineToQuotient ρ q u hrho
        (QuotientGroup.mk (FreeGroup.of (Sum.inr ⟨PUnit.unit, z⟩)))) = _
      erw [finiteSpineToQuotient_internal]
      change ψ (namedSpineIntoQuotient ρ q u
        (QuotientGroup.mk (FreeGroup.of (Sum.inl z)))) =
          QuotientGroup.mk (FreeGroup.of (Sum.inr ⟨PUnit.unit, z⟩))
      calc
        _ = φ (QuotientGroup.mk (FreeGroup.of (Sum.inl z))) :=
          DFunLike.congr_fun ho _
        _ = _ := singleSpineNamedReceiver_internal ρ q u z
  apply MonoidHom.ext
  intro z
  refine QuotientGroup.induction_on z ?_
  intro w
  exact DFunLike.congr_fun hfree w

noncomputable def finiteSpineCoefficientMap :
    MonoidAlgebra ℤ (SpineReplacementGroup ρ q u) →+*
      MonoidAlgebra ℤ (NamedQuotientGroup ρ q u) :=
  MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineToQuotient ρ q u hrho)

/-- A polygon multiple found in the geometric group ring reflects back to
the original substituted group ring. The proved reverse group homomorphism
supplies the coefficient retraction; no flatness of coinvariants is assumed. -/
theorem finiteSpineCoefficientMap_reflect_multiple {I : Type}
    (β γ : I → MonoidAlgebra ℤ (SpineReplacementGroup ρ q u))
    (w : MonoidAlgebra ℤ
      (NamedQuotientGroup ρ q u))
    (hβ : ∀ i, finiteSpineCoefficientMap ρ q u hrho (β i) =
      w * finiteSpineCoefficientMap ρ q u hrho (γ i)) :
    ∃ a : MonoidAlgebra ℤ (SpineReplacementGroup ρ q u),
      ∀ i, β i = a * γ i := by
  obtain ⟨ψ, hψ⟩ := finiteSpineToQuotient_has_leftInverse ρ q u hrho
  let r := MonoidAlgebra.mapDomainRingHom ℤ ψ
  have hr : ∀ z, r (finiteSpineCoefficientMap ρ q u hrho z) = z := by
    intro z
    group_ring_singles z
    intro g n
    apply MonoidAlgebra.coeff_injective
    change Finsupp.mapDomain ψ
      (Finsupp.mapDomain (finiteSpineToQuotient ρ q u hrho) (Finsupp.single g n)) = _
    erw [Finsupp.mapDomain_single, Finsupp.mapDomain_single]
    have hg := DFunLike.congr_fun hψ g
    change ψ (finiteSpineToQuotient ρ q u hrho g) = g at hg
    erw [hg]
    rfl
  refine ⟨r w, ?_⟩
  intro i
  have h := congrArg r (hβ i)
  erw [hr, map_mul, hr] at h
  exact h

end FiniteChains.Davis.Genus
