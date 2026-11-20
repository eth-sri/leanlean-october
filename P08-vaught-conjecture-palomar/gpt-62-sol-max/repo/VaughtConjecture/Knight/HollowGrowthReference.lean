/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthMarkerCalibration
public import VaughtConjecture.Knight.ReferenceContextMargin

@[expose] public section

namespace VaughtConjecture.Knight.HollowGrowthReference

open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan

noncomputable section

universe w

variable {M : Type w} {α : LimitStage} {W : KnightRealization α M}

/-- All entries are occurrences of one actual labelled context. The threshold
is its maximal top grade, not its arity. -/
structure Data {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n)
    (reqs : List BlockRequest) (R Nmin : ℕ) where
  context : W.LabelledExt
  face : Fin n ↪ Fin context.arity
  face_tuple : face.trans context.tuple = t
  face_type : typeMap face context.type = some p
  cap : Cell context.type.scheme.scheme
  cap_scope : context.type.scheme.scheme.scope cap = Finset.univ
  cap_grade : context.type.scheme.scheme.grade cap = context.type.topGrade
  cap_top : context.type.label cap = ⊤
  large : max (max n R) Nmin < context.type.topGrade
  marker : context.type.scheme.scheme.below (context.type.scheme.scheme.cell cap)
  marker_top : context.type.label marker.1 = ⊤
  root_below : ∀ d : Cell p.scheme.scheme,
    GradedLe (context.type.scheme.scheme.cell (mapCell face_type d))
      (context.type.scheme.scheme.cell cap)
  ref : Ordinal.{0} → context.type.scheme.scheme.below (context.type.scheme.scheme.cell cap)
  off : Ordinal.{0} → ℕ
  ref_label : ∀ r ∈ reqs, context.type.label (ref r.block).1 = ofOrd (r.block + off r.block)
  ref_off_lt : ∀ r ∈ reqs, off r.block < context.type.topGrade
  request_off_lt : ∀ r ∈ reqs, r.offset < context.type.topGrade
  top_root : ∀ d : Cell p.scheme.scheme, p.label d = ⊤ →
    extVisibilityReplace (context.type.scheme.rows.E cap marker) context.type.topGrade R ≤
      context.type.scheme.rows.E cap ⟨mapCell face_type d, root_below d⟩

/-- The joint context is constructed, including empty roots and empty request
lists. The requested offset and threshold floor precede the final growth step. -/
theorem exists_data (hM : W.IsModel) (hg : W.HasTopGradeGrowth) (hh : W.IsHollow)
    {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n) (hp : W.eval t = some p)
    (reqs : List BlockRequest)
    (hreqs : ∀ r ∈ reqs, IsNonSuccessor r.block ∧ r.block < α.1) (R Nmin : ℕ) :
    Nonempty (Data (W := W) t p reqs R Nmin) := by
  obtain ⟨C, hCN, -, -⟩ := exists_referenceContext_margin hM p hp reqs hreqs
    (max (max n R) Nmin)
  have hpc : typeMap C.proj C.p₀ = some p := by
    have h := hM.consistent C.ctx C.p₀ C.proj C.eval_ctx
    rw [C.proj_ctx, hp, knightTower_pull] at h
    exact h.symm
  obtain ⟨y, f, hf, hcy, c, r, hN, hsc, hgr, hc, hr, -, hroot⟩ :=
    GrowthMarkerCalibration.exists_hollow_marker_context hM hg hh C.ctx C.p₀ C.eval_ctx
      C.m R
  have hNm := (le_max_left C.m R).trans_lt hN
  have hpy : typeMap (C.proj.trans f) y.type = some p := by
    rwa [← typeMap_trans C.proj f y.type C.p₀ hcy]
  have below (d : Cell C.p₀.scheme.scheme) :
      GradedLe (y.type.scheme.scheme.cell (mapCell hcy d)) (y.type.scheme.scheme.cell c) := by
    constructor
    · simp_all
    · change y.type.scheme.scheme.grade (mapCell hcy d) ≤ y.type.scheme.scheme.grade c
      rw [hgr, grade_mapCell hcy]
      have h := C.p₀.scheme.scheme.grade_le_card_scope d
      have hcard := Finset.card_le_univ (C.p₀.scheme.scheme.scope d)
      simp only [Fintype.card_fin] at hcard
      omega
  have rootBelow (d : Cell p.scheme.scheme) :
      GradedLe (y.type.scheme.scheme.cell (mapCell hpy d)) (y.type.scheme.scheme.cell c) := by
    rw [mapCell_trans hcy hpc hpy d]
    tauto
  refine ⟨{
    context := y
    face := C.proj.trans f
    face_tuple := by rw [Function.Embedding.trans_assoc, hf, C.proj_ctx]
    face_type := hpy
    cap := c
    cap_scope := hsc
    cap_grade := hgr
    cap_top := hc
    large := hCN.trans hNm
    marker := r
    marker_top := hr
    root_below := rootBelow
    ref := fun μ => ⟨mapCell hcy (C.repBase μ), below (C.repBase μ)⟩
    off := C.repOff
    ref_label := fun b hb => (label_mapCell hcy _).trans (C.rep_label b hb)
    ref_off_lt := fun b hb => (C.rep_off_lt b hb).trans hNm
    request_off_lt := fun b hb => (C.offset_lt b hb).trans hNm
    top_root := ?_
  }⟩
  intro d hd
  obtain ⟨hbelow, hle⟩ := hroot (mapCell hpc d) (by rw [label_mapCell hpc, hd])
  have heq : (⟨mapCell hpy d, rootBelow d⟩ :
      y.type.scheme.scheme.below (y.type.scheme.scheme.cell c)) =
      ⟨mapCell hcy (mapCell hpc d), hbelow⟩ :=
    Subtype.ext (mapCell_trans hcy hpc hpy d)
  rw [heq]
  exact hle

end

end VaughtConjecture.Knight.HollowGrowthReference
