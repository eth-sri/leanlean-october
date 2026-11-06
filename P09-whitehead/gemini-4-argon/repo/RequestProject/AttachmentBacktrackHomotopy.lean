module

public import RequestProject.HomeomorphContinuousMap
public import RequestProject.AttachmentBaseChange
public import RequestProject.CylinderBoundaryHomotopyCorrection

@[expose] public section

noncomputable section
namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

def backtrackTime (t : I) : I :=
  ⟨min (2 * (t : ℝ)) (2 - 2 * (t : ℝ)), by
    have := t.2.1; have := t.2.2
    refine ⟨by apply le_min <;> linarith, ?_⟩
    rcases le_total (t : ℝ) (1 / 2) with h | h
    · exact (min_le_left _ _).trans (by linarith)
    · exact (min_le_right _ _).trans (by linarith)⟩

universe u
variable {D P : Type u} [TopologicalSpace D] [TopologicalSpace P]

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
  let f₀ : C(D, Space a₀ Subtype.val) := ⟨cell a₀ Subtype.val, cell_continuous _ _⟩
  let fm : C(D, Space a₀ Subtype.val) := C.comp ⟨cell a₁ Subtype.val, cell_continuous _ _⟩
  let f₁ : C(D, Space a₀ Subtype.val) := (C.comp B).comp f₀
  let F₀ : f₀.Homotopy fm := ⟨L₀, hL₀zero, fun d => (hCcell d).symm⟩
  let F₁ : fm.Homotopy f₁ := ⟨C.comp L₁, fun d => congrArg C (hL₁zero d),
    fun d => congrArg C (hBcell d).symm⟩
  let F : f₀.Homotopy f₁ := F₀.trans F₁
  have hbt_cont : Continuous backtrackTime := by unfold backtrackTime; fun_prop
  have hbt0 : backtrackTime 0 = 0 := Subtype.ext (by norm_num [backtrackTime])
  have hbt1 : backtrackTime 1 = 0 := Subtype.ext (by norm_num [backtrackTime])
  have hcb (a : S) : old a₀ Subtype.val (a₀ a) = f₀ a.val :=
    (cell_boundary a₀ Subtype.val Subtype.val_injective a).symm
  have hFside (t : I) (a : S) :
      F (t, a.val) = old a₀ Subtype.val (H (backtrackTime t, a)) := by
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · change L₀ (_, a.val) = _; rw [hL₀side]
      refine congrArg (old a₀ Subtype.val ∘ H.toFun) (Prod.ext (Subtype.ext ?_) rfl)
      exact (min_eq_left (by linarith)).symm
    · change C (L₁ (_, a.val)) = _; rw [hL₁side, hCold]
      change old a₀ Subtype.val (H (unitInterval.symm _, a)) = _
      refine congrArg (old a₀ Subtype.val ∘ H.toFun) (Prod.ext (Subtype.ext ?_) rfl)
      change 1 - (2 * (t : ℝ) - 1) = min (2 * (t : ℝ)) (2 - 2 * (t : ℝ))
      rw [min_eq_right (by linarith)]; ring
  let J : C(I × (I × S), Space a₀ Subtype.val) :=
    ⟨fun sta => old a₀ Subtype.val (H (unitInterval.symm sta.1 * backtrackTime sta.2.1, sta.2.2)),
      (old_continuous _ _).comp (H.continuous.comp
        ((Continuous.subtype_mk ((continuous_subtype_val.comp
          (unitInterval.continuous_symm.comp continuous_fst)).mul
            (continuous_subtype_val.comp (hbt_cont.comp (continuous_fst.comp continuous_snd)))) _).prodMk
          (continuous_snd.comp continuous_snd)))⟩
  obtain ⟨G⟩ := homotopyRel_of_boundaryContraction S hS hfull F J
    (fun t a => by
      change old a₀ Subtype.val (H (unitInterval.symm 0 * backtrackTime t, a)) = _
      simpa using (hFside t a).symm)
    (fun t a => by
      change old a₀ Subtype.val (H (unitInterval.symm 1 * backtrackTime t, a)) = _
      simpa [unitInterval.symm_one] using hcb a)
    (fun s a => by
      change old a₀ Subtype.val (H (unitInterval.symm s * backtrackTime 0, a)) = _
      simpa [hbt0] using hcb a)
    (fun s a => by
      change old a₀ Subtype.val (H (unitInterval.symm s * backtrackTime 1, a)) = C (B _)
      rw [hbt1, mul_zero, H.apply_zero, ← hcb a, hBold, hCold])
  let HOld : C(I × P, Space a₀ Subtype.val) :=
    ⟨fun tp => old a₀ Subtype.val tp.2, (old_continuous _ _).comp continuous_snd⟩
  have hg (t : I) (a : S) : HOld (t, a₀ a) = G (t, a.val) :=
    (hcb a).trans (G.eq_fst t a.property).symm
  exact ⟨({
    toContinuousMap := attachmentHomotopyPasting a₀ Subtype.val HOld G.toContinuousMap hg
    map_zero_left := fun z => by
      obtain ⟨p | d, rfl⟩ := quotientMap_surjective a₀ Subtype.val z
      · rfl
      · exact (attachmentHomotopyPasting_cell a₀ Subtype.val HOld G.toContinuousMap hg 0 d).trans
          (G.apply_zero d)
    map_one_left := fun z => by
      obtain ⟨p | d, rfl⟩ := quotientMap_surjective a₀ Subtype.val z
      · exact ((congrArg C (hBold p)).trans (hCold p)).symm
      · exact (attachmentHomotopyPasting_cell a₀ Subtype.val HOld G.toContinuousMap hg 1 d).trans
          (G.apply_one d) } : ContinuousMap.Homotopy (.id _) (C.comp B)).symm⟩
