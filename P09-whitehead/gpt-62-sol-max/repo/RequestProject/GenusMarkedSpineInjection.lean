module

public import RequestProject.GenusMarkedSpineBlock
public import RequestProject.GenusWordInjection

@[expose] public section

/-! Structural injectivity for substitution by the actual finite surviving spine. -/
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily

variable {α : Type}

/-- Substitute each block's old words into the relators of its marked genus spine. -/
noncomputable def familyFiniteSpineWordBlock {S : Type} (q : S → ℕ) [∀ s, NeZero (q s)]
    (u : ∀ s, Fin (q s) × Bool → FreeGroup α) (s : S) (m : NamedSpineRel (q s)) :
    FreeGroup (α ⊕ SpinePresentationGen (q s)) :=
  blockSubst (Zt := fun s => SpinePresentationGen (q s)) u s (markedSpineBeta (q s) m)

variable {Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)

noncomputable abbrev finiteSpineWordBlock :=
  familyFiniteSpineWordBlock (fun _ : PUnit.{1} => q) (fun _ => u)

/-- Replace the distinguished relator by the relators of its marked genus spine. -/
noncomputable abbrev spineReplacementPres := substPresF ρ (finiteSpineWordBlock q u)
noncomputable abbrev SpineReplacementGroup := PresGroup (spineReplacementPres ρ q u)

/-- The distinguished relator is the surface commutator word in the prescribed markings. -/
abbrev IsSpineRelator : Prop := ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q)

noncomputable abbrev SpineCoefficients := NamedSpineRel q → MonoidAlgebra ℤ (SpineReplacementGroup ρ q u)

variable (hrho : IsSpineRelator ρ q u)

include hrho in
theorem finiteSpineWordBlock_filled : FilledF ρ (finiteSpineWordBlock q u) :=
  markedSpine_filled q ρ (fun _ => u) (fun s => by cases s; exact hrho)

/-- The structural inclusion is injective for the actual finite spine and arbitrary words. -/
theorem finiteSpineWordBlock_injective :
    Function.Injective (substHomF ρ (finiteSpineWordBlock q u)
      (finiteSpineWordBlock_filled ρ q u hrho)) := by
  classical
  let ep := namedPres ρ q u
  let aa := namedA (α := α) q
  let bb := namedB (α := α) q
  have he  :=
    namedPres_surface ρ q u
  let ww := genusW ep aa bb q
  let att := genusAtt ep aa bb q
  let hh := mk_genusW ep aa bb q he
  let base := baseToQuotientW ep ww hh att
  let incl := SurfaceWordExpansion.inclusion ρ u (finitePairs q) hrho
  let j := base.comp incl
  have hj  :=
    (baseToQuotientW_injective ep ww hh att).comp
      (SurfaceWordExpansion.groupEquiv ρ u (finitePairs q) hrho).injective
  letI : Nonempty (GenusVertex q) := ⟨cV (gc q) (cyc (8 * q) 0)⟩
  obtain ⟨T, _⟩ := exists_spanningTree_qOld
    (A := cmpRel (GenusVertex q)) (posQCube (gBase q))
  let recv := (blockToQW ww att (gBase q) [] T (genus_hcb ep aa bb q)).comp
    (pi1Conj (T.treePath_isPath (posQCube (gBase q))))
  apply markedSpine_substitution_injective q ρ (fun _ => u)
    (fun s => by cases s; exact hrho) j hj (fun _ => recv)
  intro s x
  rw [spineMarkedLoop_toOld_class]
  change blockToQW ww att (gBase q) [] T (genus_hcb ep aa bb q)
    (SpanningTree.loopOf T (isPath_mapPath (surfCx _) (isPath_gSig q (x.1.val, x.2)))) = _
  rw [blockToQW_surfLoop ww att (gBase q) [] T (genus_hcb ep aa bb q)
    (isPath_gSig q (x.1.val, x.2))]
  let lw := finiteLw aa bb q PUnit.unit
  have hbase : pi1Conj (genus_hcb ep aa bb q)
      (Pi1.mk ⟨mapPath (orderCxMap att att.monotone) (gSig q (x.1.val, x.2)),
        isPath_mapPath _ (isPath_gSig q (x.1.val, x.2))⟩) =
      alphaHomW ep ww hh (QuotientGroup.mk (FreeGroup.mk (lw x))) := by
    rw [alphaHomW_mk, alphaFree_mk]
    exact Quotient.sound (genus_hread ep aa bb q PUnit.unit.{1} (x.1.val, x.2))
  rw [hbase]
  change base (QuotientGroup.mk (FreeGroup.mk (lw x))) =
    base (incl (QuotientGroup.mk (u x)))
  have hnames : FreeGroup.mk (lw x) = FreeGroup.of (Sum.inr x) := by
    rw [show lw x = [(Sum.inr x, true)] from namedLw_eq q PUnit.unit x]
    rfl
  rw [hnames]
  exact congrArg base (SurfaceWordExpansion.name_eq_word ρ u (finitePairs q) x)

end FiniteChains.Davis.Genus
