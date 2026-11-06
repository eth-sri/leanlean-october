import RequestProject.GenusQuotientReceiver
import RequestProject.Tac
noncomputable section


/-! The forward comparison with the actual quotient and its reverse reading.

-/

bwd

namespace FiniteChains.Comb
theorem pi1Conj_empty_apply {K : Complex2} a z :
    pi1Conj (show IsPathX K [] a a from rfl) z = z := by
  refine Quotient.inductionOn z ?_
  intro p
  apply Quotient.sound
  simp [conjLoop]
end FiniteChains.Comb

namespace FiniteChains.Comb.OrdCocycle
universe v w
variable {P : Type} [Preorder P] {G : Type v} [Group G] {H : Type w} [Group H]

theorem monodromy_baseEq (c : OrdCocycle P G) {a b} (h : a = b)
    z :
    c.monodromy b (pi1BaseEqEquiv h z) = c.monodromy a z := by
  subst b
  rfl

theorem postcompose_monodromy (c : OrdCocycle P G) (φ : G →* H) a :
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
  let z := pi1Map (orderCxMap (qNew (att := att)) qNew_monotone) _
    (Pi1.mk ⟨mapPath (orderCxMap att att.monotone) p.1, isPath_mapPath _ p.2⟩)
  have hpos := isPath_ordPos (qNew_att_le_qOldIncl (att := att) s)
  have hneg := isPath_ordNeg (qNew_att_le_qOldIncl (att := att) s)
  have hnat := htpy_loop_mapPath_le
    (qNew_monotone.comp att.monotone)
    (qOldIncl_monotone.comp posQCube_monotone)
    (qNew_att_le_qOldIncl (att := att)) p.2
  have he : pi1Map (orderCxMap (qOldIncl (att := att)) qOldIncl_monotone) _
      (Pi1.mk ⟨mapPath (surfCx A) p.1, isPath_mapPath _ p.2⟩) =
        pi1Conj hneg z := by
    apply Quotient.sound
    change Htpy (orderCx (Qpos A X att)) (qOldIncl (att := att) (posQCube s))
      (qOldIncl (att := att) (posQCube s)) _ _
    convert hnat using 1 <;>
      simp [z, conjLoop, mapPath, surfCx, orderCxMap, List.map_map, Function.comp_def]
  have he' := congrArg (pi1Conj hpos) he
  rwd [he', pi1Conj_pi1Conj]
  calc
    pi1Conj (hpos.append hneg) z = pi1Conj (by simp) z :=
      pi1Conj_congr _ _ (htpy_ordPos_ordNeg _) z
    _ = z := pi1Conj_empty_apply _ z

end FiniteChains.Davis

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily
variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

abbrev namedBasePos :=
  PresPos (genusNonemptyW (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q)

abbrev namedAtt : NeSpx (cmpRel (GenusVertex q)) →o namedBasePos ρ q u :=
  genusNonemptyAtt _ _ _ q

theorem namedBasePos_isConnected : IsConnected (orderCx (namedBasePos ρ q u)) :=
  genusNonemptyW_isConnected _ _ _ q

def namedBaseAlpha : PresGroup (namedPres ρ q u) →*
    Pi1 (orderCx (namedBasePos ρ q u)) (namedAtt ρ q u (gBase q)) :=
  (pi1BaseEqEquiv (genusNonemptyAtt_base _
    _ _ q).symm).toMonoidHom.comp
      (alphaHomW _
        _
        (mk_genusNonemptyW _ _ _ _ (namedPres_surface ρ q u)))

def namedBaseIntoQuotient : PresGroup (namedPres ρ q u) →*
    Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u) :=
  (pi1Map (orderCxMap _ qNew_monotone)
    _).comp (namedBaseAlpha ρ q u)

def sourceIntoNamedQuotient :=
  (namedBaseIntoQuotient ρ q u).comp
    (SurfaceWordExpansion.inclusion ρ u _ hrho)

theorem namedBaseAlpha_marked x :
    namedBaseAlpha ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) =
      Pi1.mk ⟨mapPath (orderCxMap (namedAtt ρ q u) (namedAtt ρ q u).monotone)
        (gSig q (x.1.val, x.2)),
        isPath_mapPath _ (isPath_gSig q (x.1.val, x.2))⟩ := by
  let w := genusNonemptyW (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q
  let p : Loop (orderCx (namedBasePos ρ q u)) (namedAtt ρ q u (gBase q)) :=
    ⟨genLoop w (Sum.inr x), by
      rwd [show namedAtt ρ q u (gBase q) = ptBase w from genusNonemptyAtt_base _ _ _ _]
      trivial⟩
  have hp : namedBaseAlpha ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) =
      Pi1.mk p := pi1BaseEqEquiv_mk _ _ p rfl
  rwd [hp]
  apply Quotient.sound
  have hh := genusNonempty_hread (namedPres ρ q u) (namedA (α := α) q)
    (namedB (α := α) q) q PUnit.unit.{1} (x.1.val, x.2)
  have hl : genusLw (namedA (α := α) q) (namedB (α := α) q) q
      PUnit.unit.{1} (x.1.val, x.2) = [(Sum.inr x, true)] := namedLw_eq q PUnit.unit x
  rwd [hl] at hh
  change Htpy (orderCx (namedBasePos ρ q u)) (namedAtt ρ q u (gBase q))
    (namedAtt ρ q u (gBase q)) (genLoop w (Sum.inr x))
    (mapPath (orderCxMap (namedAtt ρ q u) (by grind))
      (gSig q (x.1.val, x.2)))
  simpa [namedAtt, genusNonemptyAtt_base, wordLoop, letterLoop] using hh.symm

theorem namedSpineIntoQuotient_marked x :
    namedSpineIntoQuotient ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) =
      sourceIntoNamedQuotient ρ q u hrho (QuotientGroup.mk (u x)) := by
  change quotientOldBasedInclusion (att := namedAtt ρ q u) _
    (namedSpineToOldEquiv q (QuotientGroup.mk (FreeGroup.of (Sum.inr x)))) = _
  rwd [namedSpineToOld_marked, spineMarkedLoop_toOld_class,
    quotientOldBasedInclusion_surface (att := namedAtt ρ q u) _
      ⟨gSig q (x.1.val, x.2), isPath_gSig q (x.1.val, x.2)⟩]
  rwd [← namedBaseAlpha_marked]
  exact congrArg (namedBaseIntoQuotient ρ q u)
    (SurfaceWordExpansion.name_eq_word ρ u _ x)

theorem namedBaseCocycle_alpha {G : Type} [Group G] (j : PresGroup ρ →* G)
    z :
    (namedBaseCocycle ρ q u hrho j).monodromy (namedAtt ρ q u (gBase q))
      (namedBaseAlpha ρ q u z) = namedBaseReceiver ρ q u hrho j z := by
  simp [namedBaseAlpha, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, OrdCocycle.monodromy_baseEq, namedBaseCocycle, OrdCocycle.postcompose_monodromy, presGroupCocycle_monodromy, readingPresW_alphaHomW]

/-- The reverse receiver constructed on Q is a left inverse on the whole
source presentation group, not just on its chosen generators. -/
theorem exists_namedQuotientReading_both {G : Type} [Group G]
    j φ
    (hm : ∀ x,
      φ (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) = j (QuotientGroup.mk (u x))) :
    ∃ ψ : Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u) →* G,
      ψ.comp (namedSpineIntoQuotient ρ q u) = φ ∧
      ψ.comp (sourceIntoNamedQuotient ρ q u hrho) = j := by
  obtain ⟨ψ, ho, hb⟩ := exists_namedQuotientReading ρ q u hrho j φ hm
  refine ⟨ψ, ho, ?_⟩
  apply MonoidHom.ext
  intro z
  have hh := DFunLike.congr_fun hb
    (namedBaseAlpha ρ q u (SurfaceWordExpansion.inclusion ρ u (finitePairs q) hrho z))
  rwd [show ψ (sourceIntoNamedQuotient ρ q u hrho z) =
    (namedBaseCocycle ρ q u hrho j).monodromy _
      (namedBaseAlpha ρ q u (SurfaceWordExpansion.inclusion ρ u _ hrho z))
      from hh]
  rwd [namedBaseCocycle_alpha]
  change j (SurfaceWordExpansion.elimination ρ u _ hrho
    (SurfaceWordExpansion.inclusion ρ u _ hrho z)) = j z
  simp [SurfaceWordExpansion.elimination_inclusion]

section ComparisonMaps
variable {H : Type} [Group H] (j : PresGroup ρ →* H)
  (φ : PresGroup (namedSpinePresentation q) →* H)
  (hm : ∀ x : Fin q × Bool,
    φ (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) = j (QuotientGroup.mk (u x)))

def finiteSpineComparisonFree :=
  FreeGroup.lift (Sum.elim (fun a => j (QuotientGroup.mk (FreeGroup.of a)))
    (fun z => φ (QuotientGroup.mk (FreeGroup.of (Sum.inl z)))))

theorem finiteSpineComparisonFree_old w :
    finiteSpineComparisonFree ρ q j φ (FreeGroup.map Sum.inl w) =
      j (QuotientGroup.mk w) := by
  have h : (finiteSpineComparisonFree ρ q j φ).comp (FreeGroup.map Sum.inl) =
      j.comp (QuotientGroup.mk' _) := by
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
  · simp [MonoidHom.comp_apply, FreeGroup.map.of, Sum.swap_inr,
      blockSubst_of_inl]
    grind [finiteSpineComparisonFree_old]

def finiteSpineComparisonMaps :
    BlockMaps ρ (finiteSpineWordBlock q u) j where
  b _ := finiteSpineComparisonFree ρ q j φ
  mark _ a := by simp [finiteSpineComparisonFree]
  rel s m := by
    have h := DFunLike.congr_fun
      (finiteSpineComparisonFree_substitution ρ q u j φ hm s) (namedSpinePresentation q m)
    rwd [h]
    have hz : (QuotientGroup.mk (namedSpinePresentation q m) :
        PresGroup (namedSpinePresentation q)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨m, rfl⟩)
    change φ (QuotientGroup.mk (namedSpinePresentation q m)) = 1
    grind

end ComparisonMaps

def finiteSpineToQuotient :=
  (finiteSpineComparisonMaps ρ q u _
    _ (namedSpineIntoQuotient_marked ρ q u hrho)).psi

def singleSpineNamedReceiver : PresGroup (namedSpinePresentation q) →*
    PresGroup (substPresF ρ (finiteSpineWordBlock q u)) :=
  familySpineHom ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit

theorem singleSpineNamedReceiver_marked x :
    singleSpineNamedReceiver ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) =
      substHomF ρ (finiteSpineWordBlock q u) (finiteSpineWordBlock_filled ρ q u hrho)
        (QuotientGroup.mk (u x)) := familySpineHom_marked ρ _ (fun _ => u) PUnit.unit x

theorem singleSpineNamedReceiver_internal z :
    singleSpineNamedReceiver ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inl z))) =
      QuotientGroup.mk (FreeGroup.of (Sum.inr ⟨PUnit.unit, z⟩)) := by
  rfl

theorem finiteSpineToQuotient_source :
    (finiteSpineToQuotient ρ q u hrho).comp
      (substHomF ρ (finiteSpineWordBlock q u) (finiteSpineWordBlock_filled ρ q u hrho)) =
        sourceIntoNamedQuotient ρ q u hrho :=
  BlockMaps.psi_comp_substHomF _ _

theorem finiteSpineToQuotient_internal z :
    finiteSpineToQuotient ρ q u hrho
      (QuotientGroup.mk (FreeGroup.of (Sum.inr ⟨PUnit.unit, z⟩))) =
      namedSpineIntoQuotient ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inl z))) := by
  simp [finiteSpineToQuotient, BlockMaps.psi_mk, FreeGroup.lift_apply_of,
    BlockMaps.gen_inr, finiteSpineComparisonMaps, finiteSpineComparisonFree, Sum.elim_inr]

/-- The same forward comparison transports the entire block receiver,
including its internal generators, to the genuine geometric block map. -/
theorem finiteSpineToQuotient_spine :
    (finiteSpineToQuotient ρ q u hrho).comp (singleSpineNamedReceiver ρ q u) =
      namedSpineIntoQuotient ρ q u := by
  have h : ((finiteSpineToQuotient ρ q u hrho).comp (singleSpineNamedReceiver ρ q u)).comp
      (QuotientGroup.mk' _) =
      (namedSpineIntoQuotient ρ q u).comp
        (QuotientGroup.mk' _) := by
    apply FreeGroup.ext_hom
    rintro (z | x)
    · simp [singleSpineNamedReceiver_internal, finiteSpineToQuotient_internal]
    · change finiteSpineToQuotient ρ q u hrho
        (singleSpineNamedReceiver ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inr x)))) = _
      rwd [singleSpineNamedReceiver_marked ρ q u hrho]
      have hs := DFunLike.congr_fun (finiteSpineToQuotient_source ρ q u hrho)
        (QuotientGroup.mk (u x))
      exact hs.trans (namedSpineIntoQuotient_marked ρ q u hrho x).symm
  aesop

/-- The actual single substituted group has a left inverse to its geometric
comparison. In particular no extra injectivity premise is needed for the map
used to transport the full group-ring coefficients into the universal cover. -/
theorem finiteSpineToQuotient_has_leftInverse :
    ∃ ψ : Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u) →*
        PresGroup (substPresF ρ (finiteSpineWordBlock q u)),
      ψ.comp (finiteSpineToQuotient ρ q u hrho) = MonoidHom.id _ := by
  let j := substHomF ρ _ (finiteSpineWordBlock_filled ρ q u hrho)
  let φ := singleSpineNamedReceiver ρ q u
  obtain ⟨ψ, ho, hb⟩ := exists_namedQuotientReading_both ρ q u hrho j φ
    (singleSpineNamedReceiver_marked ρ q u hrho)
  refine ⟨ψ, ?_⟩
  have hfree : ((ψ.comp (finiteSpineToQuotient ρ q u hrho)).comp
      (QuotientGroup.mk' _)) =
      QuotientGroup.mk' _ := by
    apply FreeGroup.ext_hom
    rintro (a | ⟨s, z⟩)
    · have hs := DFunLike.congr_fun (finiteSpineToQuotient_source ρ q u hrho)
        (QuotientGroup.mk (FreeGroup.of a))
      change ψ (finiteSpineToQuotient ρ q u hrho
        (j (QuotientGroup.mk (FreeGroup.of a)))) = j (QuotientGroup.mk (FreeGroup.of a))
      rwd [show finiteSpineToQuotient ρ q u hrho
        (j (QuotientGroup.mk (FreeGroup.of a))) =
        sourceIntoNamedQuotient ρ q u hrho (QuotientGroup.mk (FreeGroup.of a)) from hs]
      exact DFunLike.congr_fun hb _
    · cases s
      change ψ (finiteSpineToQuotient ρ q u hrho
        (QuotientGroup.mk (FreeGroup.of (Sum.inr ⟨PUnit.unit, z⟩)))) = _
      rwd [finiteSpineToQuotient_internal]
      calc
        _ = φ (QuotientGroup.mk (FreeGroup.of (Sum.inl z))) :=
          DFunLike.congr_fun ho _
        _ = _ := singleSpineNamedReceiver_internal ρ q u z
  aesop

def finiteSpineCoefficientMap :=
  MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineToQuotient ρ q u hrho)

/-- A polygon multiple found in the geometric group ring reflects back to
the original substituted group ring. The proved reverse group homomorphism
supplies the coefficient retraction; no flatness of coinvariants is assumed. -/
theorem finiteSpineCoefficientMap_reflect_multiple {I : Type}
    (β γ : I → MonoidAlgebra ℤ (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))
    w
    (hβ : ∀ i, finiteSpineCoefficientMap ρ q u hrho (β i) =
      w * finiteSpineCoefficientMap ρ q u hrho (γ i)) :
    ∃ a,
      ∀ i, β i = a * γ i := by
  obtain ⟨ψ, hψ⟩ := finiteSpineToQuotient_has_leftInverse ρ q u hrho
  let r := MonoidAlgebra.mapDomainRingHom ℤ ψ
  have hr : ∀ z, r (finiteSpineCoefficientMap ρ q u hrho z) = z := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp_all
    | single g n =>
      apply MonoidAlgebra.coeff_injective
      change Finsupp.mapDomain ψ
        (Finsupp.mapDomain (finiteSpineToQuotient ρ q u hrho) (Finsupp.single g n)) = _
      rwd [Finsupp.mapDomain_single, Finsupp.mapDomain_single]
      have hg := DFunLike.congr_fun hψ g
      tauto
  refine ⟨r w, ?_⟩
  grind
