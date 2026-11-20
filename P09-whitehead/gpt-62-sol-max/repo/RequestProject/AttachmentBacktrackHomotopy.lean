module

public import RequestProject.HomeomorphContinuousMap
public import RequestProject.AttachmentBaseChange
public import RequestProject.CylinderBoundaryHomotopyCorrection

@[expose] public section

/-! Cancelling a homotopy of attaching maps followed by its reverse. The
boundary contraction is explicit; full-cylinder extension makes the disk
homotopy stationary on the attaching boundary. -/

noncomputable section
namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

universe u
variable {D P : Type u} [TopologicalSpace D] [TopologicalSpace P]

/-- The composite of the two actual collar maps is homotopic to the
identity. All map equations below are discharged by `desc` in the final
construction of the attaching-homotopy equivalence. -/
theorem attachingBacktrack_homotopic_id (S : Set D) (hS : IsClosed S)
    (hfull : HasHomotopyExtension (Subtype.val : FullCylinderBoundary S → I × D))
    (a₀ a₁ : C(S, P)) (H : a₀.Homotopy a₁)
    (C : C(Space a₁ Subtype.val, Space a₀ Subtype.val))
    (B : C(Space a₀ Subtype.val, Space a₁ Subtype.val))
    (hCold : ∀ p, C (old a₁ Subtype.val p) = old a₀ Subtype.val p)
    (hBold : ∀ p, B (old a₀ Subtype.val p) = old a₁ Subtype.val p)
    (L₀ : C(I × D, Space a₀ Subtype.val))
    (L₁ : C(I × D, Space a₁ Subtype.val))
    (hL₀zero : ∀ d, L₀ (0, d) = cell a₀ Subtype.val d)
    (hL₁zero : ∀ d, L₁ (0, d) = cell a₁ Subtype.val d)
    (hL₀side : ∀ t a, L₀ (t, a.val) = old a₀ Subtype.val (H (t, a)))
    (hL₁side : ∀ t a, L₁ (t, a.val) = old a₁ Subtype.val (H.symm (t, a)))
    (hCcell : ∀ d, C (cell a₁ Subtype.val d) = L₀ (1, d))
    (hBcell : ∀ d, B (cell a₀ Subtype.val d) = L₁ (1, d)) :
    (C.comp B).Homotopic (ContinuousMap.id (Space a₀ Subtype.val)) := by
  let f₀ : C(D, Space a₀ Subtype.val) := (Space.cellMap a₀ Subtype.val)
  let fm  :=
    C.comp (Space.cellMap a₁ Subtype.val)
  let f₁  := (C.comp B).comp f₀
  let F₀ : f₀.Homotopy fm := {
    toContinuousMap := L₀
    map_zero_left := hL₀zero
    map_one_left := fun d => (hCcell d).symm }
  let F₁ : fm.Homotopy f₁ := {
    toContinuousMap := C.comp L₁
    map_zero_left := fun d => congrArg C (hL₁zero d)
    map_one_left := fun d => congrArg C (hBcell d).symm }
  let F  := F₀.trans F₁
  let backtrack := Path.id.trans Path.id.symm
  have hFside (t : I) (a : S) :
      F (t, a.val) = old a₀ Subtype.val (H (backtrack t, a)) := by
    rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
    split_ifs
    · exact hL₀side _ _
    · exact (congrArg C (hL₁side _ _)).trans (hCold _)
  let J : C(I × (I × S), Space a₀ Subtype.val) := {
    toFun := fun st => old a₀ Subtype.val
      (H (unitInterval.symm st.1 * backtrack st.2.1, st.2.2))
    continuous_toFun := by
      apply (old_continuous _ _).comp (H.continuous.comp _)
      apply Continuous.prodMk _ (by fun_prop)
      apply Continuous.subtype_mk
      exact ((unitInterval.continuous_symm.comp continuous_fst).subtype_val).mul
        ((backtrack.continuous.comp (continuous_fst.comp continuous_snd)).subtype_val) }
  have hbd (a : S) := cell_boundary a₀ Subtype.val Subtype.val_injective a
  obtain ⟨G⟩ := homotopyRel_of_boundaryContraction S hS hfull F J
    (fun t a => by simpa [J] using (hFside t a).symm)
    (fun t a => by simp [J, f₀, hbd])
    (fun s a => by simp [J, f₀, backtrack.source, hbd])
    (fun s a => by simp [J, f₁, f₀, backtrack.target, hbd, hBold, hCold])
  let HOld : C(I × P, Space a₀ Subtype.val) :=
    ⟨fun tp => old a₀ Subtype.val tp.2, (old_continuous _ _).comp continuous_snd⟩
  have hg : ∀ t a, HOld (t, a₀ a) = G (t, a.val) := by
    intro t a
    change old a₀ Subtype.val (a₀ a) = G (t, a.val)
    rw [G.eq_fst t a.property]
    exact (cell_boundary a₀ Subtype.val Subtype.val_injective a).symm
  have Htotal : (ContinuousMap.id (Space a₀ Subtype.val)).Homotopy (C.comp B) :=
    attachmentHomotopy a₀ Subtype.val HOld G.toContinuousMap hg
      ⟨fun _ => rfl, G.apply_zero⟩
      ⟨fun p => ((congrArg C (hBold p)).trans (hCold p)).symm, G.apply_one⟩
  exact ⟨Htotal.symm⟩

end FiniteChains.RelativeAttachment
