import RequestProject.GenusNamedSpineComparison
import RequestProject.BlockFamilyAmalgamation
import RequestProject.Tac
noncomputable section


/-! Genuine finite spine relators in the distinguished/internal order used by substitution. -/
bwd

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

abbrev MarkedSpineGen := (Fin q × Bool) ⊕ SpinePresentationGen q

def markedSpineBeta (m : NamedSpineRel q) : FreeGroup (MarkedSpineGen q) :=
  FreeGroup.map Sum.swap (namedSpinePresentation q m)

theorem freeGroup_map_swap_swap {α β : Type} (z : FreeGroup (α ⊕ β)) :
    FreeGroup.map Sum.swap (FreeGroup.map Sum.swap z) = z := by
  have h : (FreeGroup.map (Sum.swap : β ⊕ α → α ⊕ β)).comp
      (FreeGroup.map Sum.swap) = MonoidHom.id _ := by
    aesop
  exact DFunLike.congr_fun h z

def markedSpineToOldHom :
    FreeGroup (MarkedSpineGen q) →*
      Pi1 (orderCx (QOld (cmpRel (GenusVertex q))))
        ((genusSpineToOld q).onV (spineBase q)) :=
  (namedSpineToOldEquiv q).toMonoidHom.comp
    ((QuotientGroup.mk' _).comp (FreeGroup.map Sum.swap))

/-- All genuine marked block relators die under the constructed geometric block map. -/
theorem markedSpineToOldHom_rel m :
    markedSpineToOldHom q (markedSpineBeta q m) = 1 := by
  change (namedSpineToOldEquiv q).toMonoidHom
    (QuotientGroup.mk (FreeGroup.map Sum.swap
      (FreeGroup.map Sum.swap (namedSpinePresentation q m)))) = 1
  rw [freeGroup_map_swap_swap]
  have h : (QuotientGroup.mk (namedSpinePresentation q m) :
      PresGroup (namedSpinePresentation q)) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨m, rfl⟩)
  simp_all

/-- The distinguished generators have exactly the actual geometric marking. -/
theorem markedSpineToOldHom_mark x :
    markedSpineToOldHom q (FreeGroup.of (Sum.inl x)) =
      pi1Map (genusSpineToOld q) (spineBase q) (Pi1.mk (spineMarkedLoop q x)) := namedSpineToOld_marked q x

/-- The surface word is a consequence of the actual reordered finite spine relators. -/
theorem markedSpine_surface_mem :
    commWord (fun x => FreeGroup.of (Sum.inl x))
      (finitePairs q) ∈ relSub (markedSpineBeta q) := by
  have h : commWord (fun x =>
      FreeGroup.of (Sum.inr x)) (finitePairs q) ∈
      relSub (namedSpinePresentation q) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' _)
      (commWord (fun x => FreeGroup.of (Sum.inr x)) (finitePairs q)) = 1
    rw [map_commWord]
    exact namedSpine_surface_filling q
  have hm := map_mem_normalClosure _
    (N := Set.range (markedSpineBeta q)) (fun z hz => by
      obtain ⟨m, rfl⟩ := hz
      exact Subgroup.subset_normalClosure ⟨m, rfl⟩) h
  simp_all [relSub, map_commWord, FreeGroup.map.of, Sum.swap_inr]

/-- Simultaneous replacement by genuine finite spine relators fills each replaced word. -/
theorem markedSpine_filled {α Jr Sx}
    (ρ : Jr ⊕ Sx → FreeGroup α) (u : Sx → Fin q × Bool → FreeGroup α)
    (hrho : ∀ s, ρ (Sum.inr s) = commWord (u s) (finitePairs q)) :
    BlockFamily.FilledF ρ (fun s m =>
      BlockFamily.blockSubst (Zt := fun _ => SpinePresentationGen q) u s
        (markedSpineBeta q m)) := by
  apply BlockFamily.filledF_of_block_consequences
  intro s
  have h := map_mem_normalClosure
    _
    (N := Set.range (fun m => BlockFamily.blockSubst
      (Zt := fun _ => SpinePresentationGen q) u s (markedSpineBeta q m)))
    (fun z hz => by
      obtain ⟨m, rfl⟩ := hz
      exact Subgroup.subset_normalClosure ⟨m, rfl⟩) (markedSpine_surface_mem q)
  simp_all [map_commWord, BlockFamily.blockSubst_of_inl]

/-- The actual geometric block map supplies the relator checks for substitution.
Only the receiver inclusion and the reading of the prescribed words remain inputs. -/
theorem markedSpine_substitution_injective {α Jr Sx H : Type} [Group H]
    (ρ : Jr ⊕ Sx → FreeGroup α) (u : Sx → Fin q × Bool → FreeGroup α)
    (hrho : ∀ s, ρ (Sum.inr s) = commWord (u s) (finitePairs q))
    (j : PresGroup ρ →* H) (hj : Function.Injective j)
    (receiver : Sx → Pi1 (orderCx (QOld (cmpRel (GenusVertex q))))
      ((genusSpineToOld q).onV (spineBase q)) →* H)
    (hread : ∀ s x, receiver s
      (pi1Map (genusSpineToOld q) (spineBase q) (Pi1.mk (spineMarkedLoop q x))) =
        j (QuotientGroup.mk (u s x))) :
    Function.Injective (BlockFamily.substHomF ρ (fun s m =>
      BlockFamily.blockSubst (Zt := fun _ => SpinePresentationGen q) u s
        (markedSpineBeta q m)) (markedSpine_filled q ρ u hrho)) := by
  apply BlockFamily.injective_substHomF_of_markedBlock u
    _ _ j hj
    (fun s => (receiver s).comp (markedSpineToOldHom q))
  · simp_all [MonoidHom.comp_apply, markedSpineToOldHom_mark]
  · simp [MonoidHom.comp_apply, markedSpineToOldHom_rel, map_one]
