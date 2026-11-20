/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.HollowGrowthReference
public import VaughtConjecture.Knight.ReceivingContext
public import VaughtConjecture.Knight.GrowthTemplateInput

@[expose] public section

namespace VaughtConjecture.Knight.HollowGrowthTemplate

open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan CappedDonor

open CellScheme.restrictFace

noncomputable section

private theorem belowMap_val_of_heq {ιA ιB : Type*} [DecidableEq ιA] [DecidableEq ιB]
    {A : Finset ιA} {B : Finset ιB} {DA : CellScheme A} {DB : CellScheme B}
    {I J : Finset ιA × ℕ} {U V : Finset ιB × ℕ} (hIJ : I = J) (hUV : U = V)
    {f : DA.below I → DB.below U} {g : DA.below J → DB.below V}
    (hfg : HEq f g) (a : DA.below I) :
    (f a).1 = (g ⟨a.1, hIJ ▸ a.2⟩).1 := by aesop

universe w

variable {M : Type w} {α : LimitStage} {W : KnightRealization α M}
  {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n} (q : S α.1 (n + 1)) {Nmin : ℕ}
  (D : HollowGrowthReference.Data (W := W) t p (donorRequests q) (n + 1) Nmin)

def requests : Requests D.context.type.scheme.scheme q.scheme.scheme :=
  Requests.ofLabels D.cap ((le_max_right n (n + 1)).trans_lt
    ((le_max_left _ Nmin).trans_lt D.large)) D.marker D.ref q.label

private theorem ref_label_exists (d β) (h : q.label d = ofOrd β) :
    ∃ j < D.context.type.topGrade, D.context.type.label (D.ref (limitPart β)).1 =
      ofOrd (limitPart β + j) :=
  let hr := mem_donorRequests.mpr ⟨d, β, h, rfl⟩
  ⟨_, D.ref_off_lt _ hr, D.ref_label _ hr⟩

/-- The actual acquired references read the requested proper values exactly. -/
theorem actual_tOf {d : Cell q.scheme.scheme} (hd : d ∈ (requests q D).F) :
    (requests q D).tOf ((requests q D).sec D.context.type.label) d = q.label d :=
  (Requests.ofLabels_tOf _ (ref_label_exists q D) hd).trans (by rw [D.cap_top, min_top_right])

theorem actual_dOf :
    (requests q D).dOf ((requests q D).sec D.context.type.label) = ⊤ := by
  change min (extVisibilityReplace (D.context.type.label D.marker.1)
    D.context.type.topGrade (n + 1)) (D.context.type.label D.cap) = ⊤
  rw [D.marker_top, D.cap_top, extVisibilityReplace_top, min_self]

/-- The actual pair satisfies the request relation without a bottom-class
assumption. This does not assert physical readback or occurrence. -/
theorem actual_correct : (requests q D).Correct ((requests q D).sec D.context.type.label)
    q.label :=
  Requests.ofLabels_correct _ (ref_label_exists q D)

/-- Scalar correctness over the actual private face is exact donor readback.
The physical construction must still establish that correctness. -/
theorem correct_iff_eq_actual (v : Cell q.scheme.scheme → ExtOrd) :
    (requests q D).Correct ((requests q D).sec D.context.type.label) v ↔ v = q.label := by
  constructor
  · intro h
    funext d
    by_cases hb : q.label d = ⊥
    · have hz := h.1 d hb
      change min (v d) (D.context.type.label D.cap) = ⊥ at hz
      rw [D.cap_top, min_top_right] at hz
      exact hz.trans hb.symm
    by_cases ht : q.label d = ⊤
    · have htop := h.2.2 d ht
      rw [actual_dOf] at htop
      aesop
    have hp := h.2.1 d ⟨hb, ht⟩
    change min (v d) (D.context.type.label D.cap) = _ at hp
    rw [D.cap_top, min_top_right, actual_tOf q D ⟨hb, ht⟩] at hp
    exact hp
  · rintro rfl
    exact actual_correct q D

/-- Every proper donor label, every donor top, and every donor bottom is a
request; no donor coordinate is omitted by the coverage proof. -/
theorem exists_template (hn : 0 < n) (hq : IsCoface p q) :
    ∃ (hvP : Finset.univ.image Fin.castSuccEmb ∈ q.scheme.scheme.plan)
      (hP : q.scheme.restrictFace Fin.castSuccEmb hvP = p.scheme)
      (hvC : Finset.univ.image D.face ∈ D.context.type.scheme.scheme.plan)
      (hC : D.context.type.scheme.restrictFace D.face hvC = p.scheme)
      (X : RelativeData D.context.type.scheme.scheme D.context.type.scheme.rows
        q.scheme.scheme q.scheme.rows),
      X.req = requests q D ∧
      Nonempty (Growth.RootAttachment p.scheme Fin.castSuccEmb hvP hP D.face hvC hC X) ∧
      HEq X.ZA {d : D.context.type.scheme.scheme.below
        (D.context.type.scheme.scheme.cell D.cap) | D.context.type.label d.1 = ⊥} := by
  classical
  let C := D.context.type
  have hvP := hq.extendsDomain.visible
  have hP' : q.restrictFace Fin.castSuccEmb hvP = p :=
    restrictFace_eq_of_typeMap_eq_some hq
  have hP : q.scheme.restrictFace Fin.castSuccEmb hvP = p.scheme := congrArg scheme hP'
  have hvC := visible_of_typeMap_eq_some D.face_type
  have hC' : C.restrictFace D.face hvC = p := restrictFace_eq_of_typeMap_eq_some D.face_type
  have hC : C.scheme.restrictFace D.face hvC = p.scheme := congrArg scheme hC'
  have hc := Growth.root_below_cap D.face D.cap_scope
    (D.cap_grade ▸ (Nat.le_succ n).trans (requests q D).R_lt_N.le)
  let κ := Growth.literalKappa p.scheme Fin.castSuccEmb hvP hP D.face hvC hC D.cap hc
  have hlit (a : q.scheme.scheme.below (Growth.rootIndex n)) : q.label a.1 = C.label (κ a).1 :=
    Growth.literalKappa_label hP' hC' a
  have hroot : ∀ s, RespectsSemanticsBelow C.scheme.rows (C.scheme.scheme.cell D.cap) s →
      RespectsSemanticsBelow q.scheme.rows (Growth.rootIndex n) (fun a => s (κ a)) :=
    fun _ => Growth.literalKappa_lawful _ _ _ _ _ _ _ _ _
  have htoproot (a : q.scheme.scheme.below (Growth.rootIndex n)) (ha : C.label (κ a).1 = ⊤) :
      extVisibilityReplace (C.scheme.rows.E D.cap D.marker) C.topGrade (n + 1) ≤
        C.scheme.rows.E D.cap (κ a) := by
    let d : Cell p.scheme.scheme := SemScheme.castCell hP ((bP Fin.castSuccEmb hvP n).symm a).1
    have he : (κ a).1 = mapCell D.face_type d := by
      change (commonFace Fin.castSuccEmb hvP hP D.face hvC hC n a).1 = _
      rw [commonFace_val]
      rfl
    have hd : p.label d = ⊤ := by
      rwa [he, label_mapCell] at ha
    have he' : κ a = ⟨mapCell D.face_type d, D.root_below d⟩ := Subtype.ext he
    rw [he']
    exact D.top_root d hd
  have hmarker : C.scheme.rows.E D.cap D.marker ≠ ⊤ := by
    rcases C.scheme.rows_coded D.cap D.marker with h | ⟨i, j, _, h⟩
    · rw [h]; exact bot_ne_top
    · rw [h]; exact ofOrd_ne_top _
  have href (μ) (hμ : μ ∈ blocks q) :
      ∃ j < C.topGrade, C.label (D.ref μ).1 = ofOrd (μ + j) := by
    obtain ⟨r, hr, rfl⟩ := mem_blocks.mp hμ
    exact ⟨D.off r.block, D.ref_off_lt r hr, D.ref_label r hr⟩
  have hblocks (d) (β) (hd : q.label d = ofOrd β) :
      limitPart β ∈ blocks q ∧ finitePart β < C.topGrade := by
    have hr := mem_donorRequests.mpr ⟨d, β, hd, rfl⟩
    exact ⟨mem_blocks.mpr ⟨_, hr, rfl⟩, D.request_off_lt _ hr⟩
  have hF (d) (hd : d ∈ (requests q D).F) :
      ∃ β, q.label d = ofOrd β ∧ (requests q D).ρ d = D.ref (limitPart β) ∧
        (requests q D).off d = finitePart β := Requests.ofLabels_field hd
  obtain ⟨hrmem, htmem, hrt, hne, hbelow⟩ := Growth.successor_bounds hn hvP
  have hcover (d) : d ∈ (requests q D).Z ∨ d ∈ (requests q D).F ∨
      d ∈ (requests q D).T ∨ ∃ r : q.scheme.scheme.below (Growth.rootIndex n), r.1 = d :=
    Requests.ofLabels_cover d
  obtain ⟨X, hreq, hr, hk, hz⟩ :=
    exists_relativeData_of_context_with_root (requests q D) D.cap_grade
      (C.scheme.consistent D.cap) C.respects D.cap_top D.marker_top hmarker
      (blocks q) (blocks_limit q) D.ref href q.respects hrmem htmem hrt hne hbelow le_rfl κ hroot
      q.scheme.bountiful hcover hlit hblocks (fun _ h => h) (fun _ h => h) hF htoproot
  refine ⟨hvP, hP, hvC, hC, X, hreq, ?_, hz⟩
  refine ⟨⟨hr, ?_⟩⟩
  intro a
  exact belowMap_val_of_heq hr (congrArg (fun r => C.scheme.scheme.cell r.C) hreq) hk a

end

end VaughtConjecture.Knight.HollowGrowthTemplate
