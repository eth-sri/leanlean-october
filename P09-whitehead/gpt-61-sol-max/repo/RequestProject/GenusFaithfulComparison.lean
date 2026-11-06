import Mathlib.Tactic

import RequestProject.GenusQuotientReceiver

/-! The forward comparison with the actual quotient and its reverse reading.

-/

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
  let z := pi1Map (orderCxMap (qNew (att := att)) qNew_monotone) (att s)
    (Pi1.mk ⟨mapPath (orderCxMap att att.monotone) p.1, isPath_mapPath _ p.2⟩)
  have hpos := isPath_ordPos (qNew_att_le_qOldIncl (att := att) s)
  have hneg := isPath_ordNeg (qNew_att_le_qOldIncl (att := att) s)
  have hnat := htpy_loop_mapPath_le
    (qNew_monotone.comp att.monotone)
    (qOldIncl_monotone.comp posQCube_monotone)
    (fun t => qNew_att_le_qOldIncl (att := att) t) p.2
  have he : pi1Map (orderCxMap (qOldIncl (att := att)) qOldIncl_monotone) (posQCube s)
      (Pi1.mk ⟨mapPath (surfCx A) p.1, isPath_mapPath (surfCx A) p.2⟩) =
        pi1Conj hneg z := by
    apply Quotient.sound
    change Htpy (orderCx (Qpos A X att)) (qOldIncl (att := att) (posQCube s))
      (qOldIncl (att := att) (posQCube s)) _ _
    convert hnat using 1 <;>
      simp [z, conjLoop, mapPath, surfCx, orderCxMap, List.map_map, Function.comp_def]
  have he'  := congrArg (pi1Conj hpos) he
  rw (config := { transparency := .default }) [he', pi1Conj_pi1Conj]
  calc
    pi1Conj (hpos.append hneg) z = pi1Conj (isPath_nil' (qNew (att s))) z :=
      pi1Conj_congr _ _ (htpy_ordPos_ordNeg (qNew_att_le_qOldIncl (att := att) s)) z
    _ = z := pi1Conj_empty_apply _ z

end FiniteChains.Davis

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily
variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

noncomputable abbrev namedBasePos :=
  PresPos (genusNonemptyW (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q)

noncomputable abbrev namedAtt  :=
  genusNonemptyAtt (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q

abbrev namedBasePos_isConnected  :=
  FiniteChains.Davis.Genus.genusNonemptyW_isConnected (FiniteChains.Davis.Genus.namedPres ρ q u)
    (FiniteChains.Davis.Genus.namedA q) (FiniteChains.Davis.Genus.namedB q) q

noncomputable def namedBaseAlpha  :=
  (pi1BaseEqEquiv (genusNonemptyAtt_base (namedPres ρ q u)
    (namedA (α := α) q) (namedB (α := α) q) q).symm).toMonoidHom.comp
      (alphaHomW (namedPres ρ q u)
        (genusNonemptyW (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q)
        (mk_genusNonemptyW _ _ _ _ (namedPres_surface ρ q u)))

noncomputable def namedBaseIntoQuotient  :=
  (pi1Map (orderCxMap (qNew (att := namedAtt ρ q u)) qNew_monotone)
    (namedAtt ρ q u (gBase q))).comp (namedBaseAlpha ρ q u)

noncomputable def sourceIntoNamedQuotient : PresGroup ρ →*
    Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u) :=
  (namedBaseIntoQuotient ρ q u).comp
    (SurfaceWordExpansion.inclusion ρ u (finitePairs q) hrho)

variable (x : Fin q × Bool)
theorem namedBaseAlpha_marked  :
    namedBaseAlpha ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) =
      Pi1.mk ⟨mapPath (orderCxMap (namedAtt ρ q u) (namedAtt ρ q u).monotone)
        (gSig q (x.1.val, x.2)),
        isPath_mapPath _ (isPath_gSig q (x.1.val, x.2))⟩ := by
  let w := genusNonemptyW (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q
  let p : Loop (orderCx (namedBasePos ρ q u)) (namedAtt ρ q u (gBase q)) :=
    ⟨genLoop w (Sum.inr x), by
      aesop (add simp [FiniteChains.Davis.Genus.genusNonemptyAtt_base, FiniteChains.PresModel.isPath_genLoop])⟩
  have hp : namedBaseAlpha ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) =
      Pi1.mk p := by
    solve_by_elim [FiniteChains.Comb.pi1BaseEqEquiv_mk]
  rw  [hp]
  apply Quotient.sound
  have hh := genusNonempty_hread (namedPres ρ q u) (namedA (α := α) q)
    (namedB (α := α) q) q PUnit.unit.{1} (x.1.val, x.2)
  simp only [List.nil_append, revPath_nil, List.append_nil] at hh
  have hl : genusLw (namedA (α := α) q) (namedB (α := α) q) q
      PUnit.unit.{1} (x.1.val, x.2) = [(Sum.inr x, true)] := namedLw_eq q PUnit.unit x
  rw  [hl] at hh
  change Htpy (orderCx (namedBasePos ρ q u)) (namedAtt ρ q u (gBase q))
    (namedAtt ρ q u (gBase q)) (genLoop w (Sum.inr x))
    (mapPath (orderCxMap (namedAtt ρ q u) (namedAtt ρ q u).monotone)
      (gSig q (x.1.val, x.2)))
  simpa [namedAtt, genusNonemptyAtt_base, wordLoop, letterLoop] using hh.symm

theorem namedSpineIntoQuotient_marked  :
    namedSpineIntoQuotient ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) =
      sourceIntoNamedQuotient ρ q u hrho (QuotientGroup.mk (u x)) := by
  change quotientOldBasedInclusion (att := namedAtt ρ q u) (gBase q)
    (namedSpineToOldEquiv q (QuotientGroup.mk (FreeGroup.of (Sum.inr x)))) = _
  rw  [namedSpineToOld_marked, spineMarkedLoop_toOld_class,
    quotientOldBasedInclusion_surface (att := namedAtt ρ q u) (gBase q)
      ⟨gSig q (x.1.val, x.2), isPath_gSig q (x.1.val, x.2)⟩]
  rw  [← namedBaseAlpha_marked]
  
  exact congrArg (namedBaseIntoQuotient ρ q u)
    (SurfaceWordExpansion.name_eq_word ρ u (finitePairs q) x)

theorem namedBaseCocycle_alpha {G : Type} [Group G] (j : PresGroup ρ →* G)
    (z : PresGroup (namedPres ρ q u)) :
    (namedBaseCocycle ρ q u hrho j).monodromy (namedAtt ρ q u (gBase q))
      (namedBaseAlpha ρ q u z) = namedBaseReceiver ρ q u hrho j z := by
  rw  [namedBaseAlpha, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    OrdCocycle.monodromy_baseEq]
  rw  [namedBaseCocycle, OrdCocycle.postcompose_monodromy,
    presGroupCocycle_monodromy, MonoidHom.comp_apply, readingPresW_alphaHomW]

/-- The reverse receiver constructed on Q is a left inverse on the whole
source presentation group, not just on its chosen generators. -/
theorem exists_namedQuotientReading_both {G : Type} [Group G]
    (j : PresGroup ρ →* G) (φ : PresGroup (namedSpinePresentation q) →* G)
    (hm : ∀ x : Fin q × Bool,
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
  
  rw (config := { transparency := .default }) [show ψ (sourceIntoNamedQuotient ρ q u hrho z) =
    (namedBaseCocycle ρ q u hrho j).monodromy (namedAtt ρ q u (gBase q))
      (namedBaseAlpha ρ q u (SurfaceWordExpansion.inclusion ρ u (finitePairs q) hrho z))
      from hh]
  rw  [namedBaseCocycle_alpha]
  change j (SurfaceWordExpansion.elimination ρ u (finitePairs q) hrho
    (SurfaceWordExpansion.inclusion ρ u (finitePairs q) hrho z)) = j z
  rw  [SurfaceWordExpansion.elimination_inclusion]

section
variable {H : Type} [Group H] (j : PresGroup ρ →* H)
  (φ : PresGroup (namedSpinePresentation q) →* H)
  (hm : ∀ x : Fin q × Bool,
    φ (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) = j (QuotientGroup.mk (u x)))

noncomputable def finiteSpineComparisonFree  :=
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
  · simp 
    rw (config := { transparency := .default }) [finiteSpineComparisonFree_old]
    exact (hm x).symm

noncomputable def finiteSpineComparisonMaps :
    BlockMaps ρ (finiteSpineWordBlock q u) j where
  b _ := finiteSpineComparisonFree ρ q j φ
  mark _ a := by simp [finiteSpineComparisonFree]
  rel s m := by
    have h := DFunLike.congr_fun
      (finiteSpineComparisonFree_substitution ρ q u j φ hm s) (namedSpinePresentation q m)
    
    simp only [MonoidHom.comp_apply] at h
    rw (config := { transparency := .default }) [h]
    have hz : (QuotientGroup.mk (namedSpinePresentation q m) :
        PresGroup (namedSpinePresentation q)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨m, rfl⟩)
    dsimp
    rw (config := { transparency := .default }) [hz, map_one]

end

noncomputable def finiteSpineToQuotient  :=
  (finiteSpineComparisonMaps ρ q u (sourceIntoNamedQuotient ρ q u hrho)
    (namedSpineIntoQuotient ρ q u) (namedSpineIntoQuotient_marked ρ q u hrho)).psi

noncomputable def singleSpineNamedReceiver : PresGroup (namedSpinePresentation q) →*
    PresGroup (substPresF ρ (finiteSpineWordBlock q u)) :=
  familySpineHom ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit

theorem singleSpineNamedReceiver_marked  :
    singleSpineNamedReceiver ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) =
      substHomF ρ (finiteSpineWordBlock q u) (finiteSpineWordBlock_filled ρ q u hrho)
        (QuotientGroup.mk (u x)) := by
  classical solve_by_elim (transparency := .default) [FiniteChains.Davis.Genus.familySpineHom_marked]

theorem singleSpineNamedReceiver_internal (z : SpinePresentationGen q) :
    singleSpineNamedReceiver ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inl z))) =
      QuotientGroup.mk (FreeGroup.of (Sum.inr ⟨PUnit.unit, z⟩)) := rfl

abbrev finiteSpineToQuotient_source  :=
  FiniteChains.BlockFamily.BlockMaps.psi_comp_substHomF
    (FiniteChains.Davis.Genus.finiteSpineComparisonMaps ρ q u
      (FiniteChains.Davis.Genus.sourceIntoNamedQuotient ρ q u hrho)
      (FiniteChains.Davis.Genus.namedSpineIntoQuotient ρ q u)
      (FiniteChains.Davis.Genus.namedSpineIntoQuotient_marked ρ q u hrho))
    (FiniteChains.Davis.Genus.finiteSpineWordBlock_filled ρ q u hrho)

theorem finiteSpineToQuotient_internal (z : SpinePresentationGen q) :
    finiteSpineToQuotient ρ q u hrho
      (QuotientGroup.mk (FreeGroup.of (Sum.inr ⟨PUnit.unit, z⟩))) =
      namedSpineIntoQuotient ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inl z))) := by simp_all [finiteSpineToQuotient, finiteSpineComparisonMaps, finiteSpineComparisonFree]

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
    · simp_all [FiniteChains.Davis.Genus.singleSpineNamedReceiver_internal, FiniteChains.Davis.Genus.finiteSpineToQuotient_internal]
    · change finiteSpineToQuotient ρ q u hrho
        (singleSpineNamedReceiver ρ q u (QuotientGroup.mk (FreeGroup.of (Sum.inr x)))) = _
      rw  [singleSpineNamedReceiver_marked ρ q u hrho]
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
  let j := substHomF ρ (finiteSpineWordBlock q u) (finiteSpineWordBlock_filled ρ q u hrho)
  let φ := singleSpineNamedReceiver ρ q u
  obtain ⟨ψ, ho, hb⟩ := exists_namedQuotientReading_both ρ q u hrho j φ
    (singleSpineNamedReceiver_marked ρ q u hrho)
  refine ⟨ψ, ?_⟩
  have hfree : ((ψ.comp (finiteSpineToQuotient ρ q u hrho)).comp
      (QuotientGroup.mk' (relSub (substPresF ρ (finiteSpineWordBlock q u))))) =
      QuotientGroup.mk' (relSub (substPresF ρ (finiteSpineWordBlock q u))) := by
    apply FreeGroup.ext_hom
    rintro (a | ⟨s, z⟩)
    · have hs := DFunLike.congr_fun (finiteSpineToQuotient_source ρ q u hrho)
        (QuotientGroup.mk (FreeGroup.of a))
      change ψ (finiteSpineToQuotient ρ q u hrho
        (j (QuotientGroup.mk (FreeGroup.of a)))) = j (QuotientGroup.mk (FreeGroup.of a))
      rw  [show finiteSpineToQuotient ρ q u hrho
        (j (QuotientGroup.mk (FreeGroup.of a))) =
        sourceIntoNamedQuotient ρ q u hrho (QuotientGroup.mk (FreeGroup.of a)) from hs]
      exact DFunLike.congr_fun hb (QuotientGroup.mk (FreeGroup.of a))
    · cases s
      change ψ (finiteSpineToQuotient ρ q u hrho
        (QuotientGroup.mk (FreeGroup.of (Sum.inr ⟨PUnit.unit, z⟩)))) = _
      rw  [finiteSpineToQuotient_internal]
      change ψ (namedSpineIntoQuotient ρ q u
        (QuotientGroup.mk (FreeGroup.of (Sum.inl z)))) =
          QuotientGroup.mk (FreeGroup.of (Sum.inr ⟨PUnit.unit, z⟩))
      calc
        _ = φ (QuotientGroup.mk (FreeGroup.of (Sum.inl z))) :=
          DFunLike.congr_fun ho _
        _ = _ := singleSpineNamedReceiver_internal ρ q u z
  aesop

noncomputable def finiteSpineCoefficientMap  :=
  MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineToQuotient ρ q u hrho)

/-- A polygon multiple found in the geometric group ring reflects back to
the original substituted group ring. The proved reverse group homomorphism
supplies the coefficient retraction; no flatness of coinvariants is assumed. -/
theorem finiteSpineCoefficientMap_reflect_multiple {I : Type}
    (β γ : I → MonoidAlgebra ℤ (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))
    (w : MonoidAlgebra ℤ
      (Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)))
    (hβ : ∀ i, finiteSpineCoefficientMap ρ q u hrho (β i) =
      w * finiteSpineCoefficientMap ρ q u hrho (γ i)) :
    ∃ a : MonoidAlgebra ℤ (PresGroup (substPresF ρ (finiteSpineWordBlock q u))),
      ∀ i, β i = a * γ i := by
  obtain ⟨ψ, hψ⟩ := finiteSpineToQuotient_has_leftInverse ρ q u hrho
  let r := MonoidAlgebra.mapDomainRingHom ℤ ψ
  have hr : ∀ z, r (finiteSpineCoefficientMap ρ q u hrho z) = z := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | single g n =>
      apply MonoidAlgebra.coeff_injective
      change Finsupp.mapDomain ψ
        (Finsupp.mapDomain (finiteSpineToQuotient ρ q u hrho) (Finsupp.single g n)) = _
      rw  [Finsupp.mapDomain_single, Finsupp.mapDomain_single]
      have hg := DFunLike.congr_fun hψ g
      change ψ (finiteSpineToQuotient ρ q u hrho g) = g at hg
      rw  [hg]
      rfl
  refine ⟨r w, ?_⟩
  intro i
  have h := congrArg r (hβ i)
  rw  [hr, map_mul, hr] at h
  exact h

end FiniteChains.Davis.Genus
