/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalCodingSupport
public import VaughtConjecture.Knight.SourceCode
public import VaughtConjecture.Knight.Domain
public import VaughtConjecture.Knight.HighLayerBountiful

@[expose] public section

namespace VaughtConjecture.Knight
open AmalgamationPlan Transform Value ExtOrd

namespace HighGradeExtension
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {k : ℕ}

structure Data (D : CellScheme A) (k : ℕ) where
  base : Semantics D
  high : Cell D
  above : k < D.grade high
  full : D.scope high = A
  profile : D.below (A, k) → ExtOrd
  lawful : RespectsSemanticsBelow base (A, k) profile
  diagonal : ExtOrd
  visible : SelfVis (D.grade high) diagonal

namespace Data
variable (F : Data D k) {BJ CI : Finset ι × ℕ}

abbrev oldCell (d : Cell D) (hd : D.grade d ≤ k) : D.below (A, k) :=
  ⟨d, D.isPlan.subset_of_mem (D.scope_mem_plan d), hd⟩

def display (d : Cell D) : ExtOrd :=
  if hd : D.grade d ≤ k then F.profile (oldCell d hd) else if d = F.high then F.diagonal else ⊥

theorem display_old (d : Cell D) (hd : D.grade d ≤ k) :
    F.display d = F.profile (oldCell d hd) := dif_pos hd

theorem display_high : F.display F.high = F.diagonal := by
  simp only [display, not_le_of_gt F.above, ↓reduceDIte, ↓reduceIte]

theorem display_other (d : Cell D) (hd : ¬D.grade d ≤ k) (hne : d ≠ F.high) :
    F.display d = ⊥ := by simp only [display, hd, hne, ↓reduceDIte, ↓reduceIte]

theorem display_visible (d : Cell D) : SelfVis (D.grade d) (F.display d) := by
  by_cases hd : D.grade d ≤ k
  · rw [F.display_old d hd]; exact (F.lawful.orderly _).symm
  · by_cases he : d = F.high
    · subst d; rw [F.display_high]; exact F.visible
    · rw [F.display_other d hd he]; exact selfVis_bot _

def rows : Semantics D where
  E c d := if D.grade c ≤ k then F.base.E c d else if c = F.high then F.display d.1 else ⊥
  orderly c d := by
    split_ifs
    · exact F.base.orderly c d
    · exact (F.display_visible d.1).symm
    · exact (selfVis_bot _).symm

theorem row_old {c : Cell D} (hc : D.grade c ≤ k) : F.rows.E c = F.base.E c :=
  funext fun _ => if_pos hc

theorem rows_high : F.rows.E F.high = fun d => F.display d.1 :=
  funext fun _ => by simp only [rows, not_le_of_gt F.above, ↓reduceIte]

theorem row_mute {c : Cell D} (hc : ¬D.grade c ≤ k) (he : c ≠ F.high)
    (d : D.below (D.cell c)) : F.rows.E c d = ⊥ := by simp only [rows, hc, he, ↓reduceIte]

theorem old_respects_iff (hJ : BJ.2 ≤ k) {p : D.below BJ → ExtOrd} :
    RespectsSemanticsBelow F.rows BJ p ↔ RespectsSemanticsBelow F.base BJ p :=
  ⟨fun hp => ⟨hp.orderly, fun c => by simpa only [F.row_old (c.2.2.trans hJ)] using hp.locality c,
    hp.availability⟩,
   fun hp => ⟨hp.orderly, fun c => by rw [F.row_old (c.2.2.trans hJ)]; exact hp.locality c,
    hp.availability⟩⟩

theorem high_index {e : Cell D} (hs : D.scope F.high ⊆ D.scope e)
    (hg : D.grade F.high = D.grade e) : D.cell F.high = D.cell e :=
  Prod.ext (Finset.Subset.antisymm hs (by change D.scope e ⊆ D.scope F.high; rw [F.full]; exact D.isPlan.subset_of_mem (D.scope_mem_plan e))) hg

theorem consistent (hb : F.base.IsConsistent) : F.rows.IsConsistent := by
  intro c
  by_cases hc : D.grade c ≤ k
  · exact (F.old_respects_iff hc).mpr (by simpa only [F.row_old hc] using hb c)
  refine ⟨F.rows.orderly c, fun d => ?_, fun d e hs hg => ?_⟩
  · by_cases he : c = F.high
    · subst c
      by_cases hd : D.grade d.1 ≤ k
      · simpa only [F.row_old hd, F.rows_high, F.display_old d.1 hd,
          F.display_old _ ((_ : D.below (D.cell d.1)).2.2.trans hd),
          CellScheme.below.incl, oldCell] using F.lawful.locality (oldCell d.1 hd)
      · by_cases hdhi : d.1 = F.high
        · rcases d with ⟨d, hdle⟩; dsimp only at hdhi; subst d
          simpa only [F.rows_high, F.display_high, CellScheme.below.incl] using
            (TransformsTo.refl (grade := fun e : D.below (D.cell F.high) => D.grade e.1)
              (F.rows.E F.high)).cap (fun e => e.2.2) F.visible
        · simpa only [F.rows_high, F.display_other d.1 hd hdhi, min_bot_right] using
            (TransformsTo.to_bot (grade := fun e : D.below (D.cell d.1) => D.grade e.1) (F.rows.E d.1))
    · simpa only [rows, hc, he, ↓reduceIte, min_bot_right] using
        (TransformsTo.to_bot (grade := fun e : D.below (D.cell d.1) => D.grade e.1) (F.rows.E d.1))
  · by_cases he : c = F.high
    · subst c
      by_cases hd : D.grade d.1 ≤ k
      · obtain ⟨f, hf, hv⟩ := F.lawful.availability (oldCell d.1 hd) (oldCell e.1 (hg ▸ hd)) hs hg
        exact ⟨⟨f.1, by rw [hf]; exact e.2⟩, hf, by
          simpa only [F.rows_high, F.display_old d.1 hd, F.display_old f.1 f.2.2,
            show oldCell f.1 f.2.2 = f from Subtype.ext rfl] using hv⟩
      · by_cases hdhi : d.1 = F.high
        · exact ⟨d, by rw [hdhi]; exact F.high_index (by simpa only [hdhi] using hs) (by simpa only [hdhi] using hg), le_rfl⟩
        · exact ⟨e, rfl, by simp only [F.rows_high, F.display_other d.1 hd hdhi, bot_le]⟩
    · exact ⟨e, rfl, by simp only [F.row_mute hc he, le_refl]⟩

theorem mute_label {p : D.below BJ → ExtOrd} (hp : RespectsSemanticsBelow F.rows BJ p)
    (c : D.below BJ) (hc : ¬D.grade c.1 ≤ k) (hne : c.1 ≠ F.high) : p c = ⊥ := by
  rcases c with ⟨c, hcBJ⟩
  obtain ⟨g, σ, _, _, hbot, _, _, he⟩ := hp.locality ⟨c, hcBJ⟩
  have hh := he ⟨c, GradedLe.refl _⟩
  change min (p ⟨c, hcBJ⟩) (p ⟨c, hcBJ⟩) =
    min (σ (F.rows.E c ⟨c, GradedLe.refl _⟩)) (g (D.grade c)) at hh
  simpa only [rows, hc, hne, ↓reduceIte, hbot, min_bot_left, min_self] using hh

private theorem below_eta {J} (d : D.below J) (hd : GradedLe (D.cell d.1) J) :
    (⟨d.1, hd⟩ : D.below J) = d := Subtype.ext rfl

def cut (BJ : Finset ι × ℕ) (k : ℕ) : Finset ι × ℕ := (BJ.1, min BJ.2 k)

def fill (r : D.below (cut BJ k) → ExtOrd) (η : ExtOrd) (d : D.below BJ) : ExtOrd :=
  if hd : D.grade d.1 ≤ k then r ⟨d.1, d.2.1, le_min d.2.2 hd⟩ else
    if d.1 = F.high then η else ⊥

theorem bountiful (hk : 1 ≤ k) (hb : F.base.IsBountiful) : F.rows.IsBountiful := by
  classical
  intro CI BJ hCI hBJ hle _ p q γ hp hq hγ hag
  let i : GradedLe (cut CI k) CI := ⟨Finset.Subset.refl _, min_le_left _ _⟩
  let j : GradedLe (cut BJ k) BJ := ⟨Finset.Subset.refl _, min_le_left _ _⟩
  let ij : GradedLe (cut CI k) (cut BJ k) := ⟨hle.1, min_le_min hle.2 le_rfl⟩
  have hp1 := (F.old_respects_iff (min_le_right _ _)).mp (hp.mono i)
  have hq1 := (F.old_respects_iff (min_le_right _ _)).mp (hq.mono j)
  have hγJ : SelfVis BJ.2 γ := hγ
  have cmem {U} (hU : U ∈ Plan.gradedPlan D.plan) : cut U k ∈ Plan.gradedPlan D.plan := by
    obtain ⟨hB, hJ, hcard⟩ := Plan.mem_gradedPlan.mp hU
    exact Plan.mem_gradedPlan.mpr ⟨hB, lt_min hJ (Nat.lt_of_lt_of_le (by decide) hk), (min_le_left _ _).trans hcard⟩
  have base_lift {U V} (hU : U ∈ Plan.gradedPlan D.plan) (hV : V ∈ Plan.gradedPlan D.plan)
      (hUV : GradedLe U V) (p0 : D.below U → ExtOrd) (q0 : D.below V → ExtOrd)
      (hp0 : RespectsSemanticsBelow F.base U p0) (hq0 : RespectsSemanticsBelow F.base V q0)
      (hγ0 : SelfVis V.2 γ) (hag0 : ∀ d, min (q0 (CellScheme.below.mono hUV d)) γ = min (p0 d) γ) :
      ∃ out, RespectsSemanticsBelow F.base V out ∧
        (∀ d, min (out d) γ = min (q0 d) γ) ∧ ∀ d, out (CellScheme.below.mono hUV d) = p0 d := by
    by_cases he : U = V
    · subst he; exact ⟨p0, hp0, fun d => (hag0 d).symm, fun _ => rfl⟩
    · exact hb U V hU hV hUV he p0 q0 γ hp0 hq0 hγ0 hag0
  obtain ⟨r, hr, hcap, hpres⟩ := base_lift (cmem hCI) (cmem hBJ) ij
    _ _ hp1 hq1 (hγJ.mono (min_le_left _ _)) fun d => hag (CellScheme.below.mono i d)
  let η : ExtOrd := if hi : GradedLe (D.cell F.high) CI then p ⟨F.high, hi⟩
    else if hj : GradedLe (D.cell F.high) BJ then min (q ⟨F.high, hj⟩) γ else ⊥
  let out := F.fill r η
  have ηvis : SelfVis (D.grade F.high) η := by
    dsimp only [η]; split_ifs with hi hj
    · exact (hp.orderly ⟨F.high, hi⟩).symm
    · exact selfVis_min (hq.orderly ⟨F.high, hj⟩).symm (hγJ.mono hj.2)
    · exact selfVis_bot _
  have outcap (d : D.below BJ) : min (out d) γ = min (q d) γ := by
    by_cases hd : D.grade d.1 ≤ k
    · simpa only [out, fill, hd, ↓reduceDIte, CellScheme.below.mono, below_eta] using
        hcap ⟨d.1, d.2.1, le_min d.2.2 hd⟩
    · by_cases he : d.1 = F.high
      · rcases d with ⟨d, hdBJ⟩; dsimp only at he; subst d
        simp only [out, fill, not_le_of_gt F.above, ↓reduceDIte, ↓reduceIte, η]
        by_cases hi : GradedLe (D.cell F.high) CI
        · rw [dite_eq_left hi]; exact (hag ⟨F.high, hi⟩).symm
        · rw [dite_eq_right hi, dite_eq_left hdBJ, min_assoc, min_self]
      · simp only [out, fill, hd, he, ↓reduceDIte, ↓reduceIte, F.mute_label hq d hd he]
  have outpres (d : D.below CI) : out (CellScheme.below.mono hle d) = p d := by
    by_cases hd : D.grade d.1 ≤ k
    · simpa only [out, fill, hd, ↓reduceDIte, CellScheme.below.mono, below_eta] using
        hpres ⟨d.1, d.2.1, le_min d.2.2 hd⟩
    · by_cases he : d.1 = F.high
      · rcases d with ⟨d, hdCI⟩; dsimp only at he; subst d
        simp only [out, fill, CellScheme.below.mono, not_le_of_gt F.above, ↓reduceDIte, ↓reduceIte,
          η, dite_eq_left hdCI]
      · simp only [out, fill, CellScheme.below.mono, hd, he, ↓reduceDIte, ↓reduceIte,
          F.mute_label hp d hd he]
  refine ⟨out, ⟨fun d => ?_, fun c => ?_, fun d e hs hg => ?_⟩, outcap, outpres⟩
  · by_cases hd : D.grade d.1 ≤ k
    · simpa only [out, fill, hd, ↓reduceDIte] using hr.orderly ⟨d.1, d.2.1, le_min d.2.2 hd⟩
    · by_cases he : d.1 = F.high
      · rcases d with ⟨d, hdBJ⟩; dsimp only at he; subst d
        simpa only [out, fill, not_le_of_gt F.above, ↓reduceDIte, ↓reduceIte] using ηvis.symm
      · simpa only [out, fill, hd, he, ↓reduceDIte, ↓reduceIte] using (selfVis_bot (D.grade d.1)).symm
  · by_cases hc : D.grade c.1 ≤ k
    · rw [F.row_old hc]
      convert hr.locality ⟨c.1, c.2.1, le_min c.2.2 hc⟩ using 1
      funext d
      have hdc : D.grade d.1 ≤ k := d.2.2.trans hc
      simp only [out, fill, hc, hdc, ↓reduceDIte, CellScheme.below.incl]
    · by_cases he : c.1 = F.high
      · rcases c with ⟨c, hcBJ⟩; dsimp only at he; subst c
        by_cases hi : GradedLe (D.cell F.high) CI
        · convert hp.locality ⟨F.high, hi⟩ using 1
          funext e
          have h1 := outpres ⟨e.1, e.2.trans hi⟩
          have h2 := outpres ⟨F.high, hi⟩
          dsimp only [CellScheme.below.mono] at h1 h2
          change min (out ⟨e.1, e.2.trans hcBJ⟩) (out ⟨F.high, hcBJ⟩) = _
          rw [h1, h2]; rfl
        · have readc : out ⟨F.high, hcBJ⟩ = min (q ⟨F.high, hcBJ⟩) γ := by
            simp only [out, fill, not_le_of_gt F.above, ↓reduceDIte, ↓reduceIte, η,
              dite_eq_right hi, dite_eq_left hcBJ]
          convert (hq.locality ⟨F.high, hcBJ⟩).cap (fun e => e.2.2) (hγJ.mono hcBJ.2) using 1
          funext e
          change min (out ⟨e.1, e.2.trans hcBJ⟩) (out ⟨F.high, hcBJ⟩) = _
          rw [readc]
          calc _ = min (min (out ⟨e.1, e.2.trans hcBJ⟩) γ) (q ⟨F.high, hcBJ⟩) := by ac_rfl
            _ = min (min (q ⟨e.1, e.2.trans hcBJ⟩) γ) (q ⟨F.high, hcBJ⟩) :=
                congrArg (fun x => min x (q ⟨F.high, hcBJ⟩)) (outcap ⟨e.1, e.2.trans hcBJ⟩)
            _ = _ := by dsimp only [CellScheme.below.incl]; ac_rfl
      · simpa only [out, fill, hc, he, ↓reduceDIte, ↓reduceIte, min_bot_right] using
          (TransformsTo.to_bot (grade := fun d : D.below (D.cell c.1) => D.grade d.1) (F.rows.E c.1))
  · by_cases hd : D.grade d.1 ≤ k
    · obtain ⟨⟨f, hfc⟩, hf, hv⟩ := hr.availability
        ⟨d.1, d.2.1, le_min d.2.2 hd⟩ ⟨e.1, e.2.1, le_min e.2.2 (show D.grade e.1 ≤ k from hg ▸ hd)⟩ hs hg
      have hfk : D.grade f ≤ k := hfc.2.trans (min_le_right _ _)
      exact ⟨⟨f, hfc.trans j⟩, hf, by simpa only [out, fill, hd, hfk, ↓reduceDIte] using hv⟩
    · by_cases he : d.1 = F.high
      · exact ⟨d, by rw [he]; exact F.high_index (by simpa only [he] using hs) (by simpa only [he] using hg), le_rfl⟩
      · exact ⟨e, rfl, by simp only [out, fill, hd, he, ↓reduceDIte, ↓reduceIte, bot_le]⟩
end Data

theorem exists_extension {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {k : ℕ}
    (base : Semantics D) (h : Cell D) (hh : k < D.grade h) (hfull : D.scope h = A)
    (p : D.below (A, k) → ExtOrd) (hp : RespectsSemanticsBelow base (A, k) p)
    (N : ExtOrd) (hN : SelfVis (D.grade h) N) (hk : 1 ≤ k) (hc : base.IsConsistent)
    (hb : base.IsBountiful) (hcode : base.IsCoded) :
    ∃ (rows : Semantics D) (q : Cell D → ExtOrd),
      rows.IsConsistent ∧ rows.IsBountiful ∧ rows.IsCoded ∧ RespectsSemantics rows q ∧
      (∀ c, D.grade c ≤ k → rows.E c = base.E c) ∧
      (∀ d : D.below (A, k), q d.1 = p d) ∧ q h = N := by
  let _ : Fintype (D.below (A, k)) := Fintype.ofFinite _
  let sv : Finset Ordinal := primRange p ∪ primRange (fun _ : Unit => N)
  have hsold (d : D.below (A, k)) : SourceCode.Supported sv (p d) :=
    fun _ hv => Finset.mem_union_left _ (mem_primRange_of_eq hv)
  have hsnew : SourceCode.Supported sv N :=
    fun _ hv => Finset.mem_union_right _ (mem_primRange_of_eq (target := fun _ : Unit => N) (d := ()) hv)
  let F : Data D k :=
    { base := base, high := h, above := hh, full := hfull
      profile := fun d => SourceCode.encode (D.grade h) sv (p d)
      lawful := SourceCode.respectsBelow (D.grade h) sv hh.le hp hsold
      diagonal := SourceCode.encode (D.grade h) sv N
      visible := SourceCode.encode_selfVis _ _ le_rfl hN }
  let sel (d : Cell D) : ExtOrd :=
    if hd : D.grade d ≤ k then p (Data.oldCell d hd) else if d = h then N else ⊥
  have hsread (d : D.below (D.cell h)) :
      F.rows.E h d = SourceCode.encode (D.grade h) sv (sel d.1) := by
    simp only [Data.rows, F, not_le_of_gt hh, ↓reduceIte]
    by_cases hd : D.grade d.1 ≤ k
    · simp only [Data.display, sel, hd, ↓reduceDIte]
    · by_cases he : d.1 = h
      · simp only [Data.display, sel, he, not_le_of_gt hh, ↓reduceDIte, ↓reduceIte]
      · simp only [Data.display, sel, hd, he, ↓reduceDIte, ↓reduceIte, SourceCode.encode]
  refine ⟨F.rows, sel, F.consistent hc, F.bountiful hk hb, fun c d => ?_,
    ⟨fun d => ?_, fun c => ?_, fun d e hs hg => ?_⟩,
    fun _ hc' => F.row_old hc',
    fun d => (dif_pos d.2.2).trans (congrArg p (Subtype.ext rfl)),
    by simp only [sel, not_le_of_gt hh, ↓reduceDIte, ↓reduceIte]⟩
  · change IsCodedLabel (D.grade c) (F.rows.E c d)
    by_cases hc' : D.grade c ≤ k
    · rw [F.row_old hc']; exact hcode c d
    · by_cases he : c = h
      · subst c; rw [hsread d]; exact SourceCode.encode_coded _ _ _
      · exact Or.inl (F.row_mute hc' he d)
  · by_cases hd : D.grade d ≤ k
    · simpa only [sel, hd, ↓reduceDIte] using hp.orderly (Data.oldCell d hd)
    · by_cases he : d = h
      · subst d; simpa only [sel, not_le_of_gt hh, ↓reduceDIte, ↓reduceIte] using hN.symm
      · simpa only [sel, hd, he, ↓reduceDIte, ↓reduceIte] using (selfVis_bot (D.grade d)).symm
  · change TransformsTo _ (F.rows.E c) (fun d => min (sel d.1) (sel c))
    by_cases hc' : D.grade c ≤ k
    · rw [F.row_old hc']
      convert hp.locality (Data.oldCell c hc') using 1
      funext d; have hdc : D.grade d.1 ≤ k := d.2.2.trans hc'; simp only [sel, hc', hdc, ↓reduceDIte]; rfl
    · by_cases he : c = h
      · subst c
        rw [funext hsread, show sel h = N by simp only [sel, not_le_of_gt hh, ↓reduceDIte, ↓reduceIte]]
        refine SourceCode.outgoing (fun d : D.below (D.cell h) => D.grade d.1)
          (fun d => sel d.1) (D.grade h) sv (fun d => d.2.2) (fun d => ?_) hN
        by_cases hd : D.grade d.1 ≤ k
        · simpa only [sel, hd, ↓reduceDIte] using hsold _
        · by_cases he' : d.1 = h
          · simpa only [sel, he', not_le_of_gt hh, ↓reduceDIte, ↓reduceIte] using hsnew
          · simpa only [sel, hd, he', ↓reduceDIte, ↓reduceIte] using SourceCode.supported_bot sv
      · simpa only [sel, hc', he, ↓reduceDIte, ↓reduceIte, min_bot_right] using
          (TransformsTo.to_bot (grade := fun d : D.below (D.cell c) => D.grade d.1) (F.rows.E c))
  · by_cases hd : D.grade d ≤ k
    · obtain ⟨⟨f, hfc⟩, hf, hv⟩ := hp.availability (Data.oldCell d hd) (Data.oldCell e (hg ▸ hd)) hs hg
      have hfk : D.grade f ≤ k := hfc.2
      exact ⟨f, hf, by simpa only [sel, hd, hfk, ↓reduceDIte] using hv⟩
    · by_cases he : d = h
      · exact ⟨d, he ▸ F.high_index (by simpa only [F, he] using hs) (by simpa only [F, he] using hg), le_rfl⟩
      · exact ⟨e, rfl, by simp only [sel, hd, he, ↓reduceDIte, ↓reduceIte, bot_le]⟩
end
end HighGradeExtension

namespace MaximalFullLayer
open SourceLayerCarrier
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} (D : CellScheme A)
  (sem : Semantics D) (K l : ℕ) (hK : ∀ d : Cell D, D.grade d ≤ K)
  (hKl : K < l) (hlA : l ≤ A.card)

abbrev positive : 0 < l := (Nat.zero_le K).trans_lt hKl
abbrev separated := HighLayerBountiful.separated D l K hK hKl
abbrev scheme := SourceLayerCarrier.scheme D Unit l (positive K l hKl) hlA
abbrev old (d : Cell D) := toCell D Unit l (positive K l hKl) hlA (.inl d)
abbrev apex : Cell (scheme D K l hKl hlA) := toCell D Unit l (positive K l hKl) hlA (.inr ())
abbrev ownerEquiv := SeparatedSourceLayerCarrier.ownerEquiv D Unit l
  (positive K l hKl) hlA (separated D K l hK hKl)
abbrev base := SeparatedSourceLayerCarrier.base D Unit l
  (positive K l hKl) hlA (separated D K l hK hKl) sem

theorem old_index (d : Cell D) : (scheme D K l hKl hlA).cell (old D K l hKl hlA d) = D.cell d :=
  cell_toCell _ _ _ _ _ _
theorem apex_index : (scheme D K l hKl hlA).cell (apex D K l hKl hlA) = (A, l) :=
  cell_toCell _ _ _ _ _ _

theorem inherited_row (c : Cell D) (d : D.below (D.cell c)) :
    (base D sem K l hK hKl hlA).E (old D K l hKl hlA c)
      (ownerEquiv D K l hK hKl hlA c d) = sem.E c d :=
  SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ c d

theorem consistent (hs : sem.IsConsistent) : (base D sem K l hK hKl hlA).IsConsistent := by
  intro c
  obtain ⟨x, rfl⟩ := (enumeration D Unit l (positive K l hKl) hlA).surjective c
  change RespectsSemanticsBelow (base D sem K l hK hKl hlA)
    ((scheme D K l hKl hlA).cell (toCell D Unit l (positive K l hKl) hlA x))
    ((base D sem K l hK hKl hlA).E (toCell D Unit l (positive K l hKl) hlA x))
  cases x with
  | inl c =>
    apply (SeparatedSourceLayerCarrier.base_respects_iff D Unit l
      (positive K l hKl) hlA (separated D K l hK hKl) sem c _).mpr
    rw [show (base D sem K l hK hKl hlA).E (old D K l hKl hlA c) ∘
        ownerEquiv D K l hK hKl hlA c = sem.E c from funext (inherited_row D sem K l hK hKl hlA c)]
    exact hs c
  | inr u =>
    have he : (base D sem K l hK hKl hlA).E
        (toCell D Unit l (positive K l hKl) hlA (.inr u)) = fun _ => ⊥ := by
      funext d
      simp only [base, SeparatedSourceLayerCarrier.base, toOcc_toCell,
        SeparatedSourceLayerCarrier.oldTable]
    rw [he]
    exact ⟨fun _ => (extVisibilityReplace_bot _ _).symm,
      fun b => by simpa only [min_self] using TransformsTo.to_bot ((base D sem K l hK hKl hlA).E b.1),
      fun _ b _ _ => ⟨b, rfl, le_rfl⟩⟩

theorem bountiful (hpos : 0 < K) (hb : sem.IsBountiful) :
    (base D sem K l hK hKl hlA).IsBountiful :=
  HighLayerBountiful.bountiful D Unit l (positive K l hKl) hlA K hK hKl sem
    (base D sem K l hK hKl hlA) (inherited_row D sem K l hK hKl hlA) hpos hb

theorem coded (hc : sem.IsCoded) : (base D sem K l hK hKl hlA).IsCoded :=
  CanonicalCodingSupport.layer D Unit l (positive K l hKl) hlA
    (separated D K l hK hKl) sem _ hc (inherited_row D sem K l hK hKl hlA)
    fun _ _ => Or.inl (by simp only [base, SeparatedSourceLayerCarrier.base, toOcc_toCell,
      SeparatedSourceLayerCarrier.oldTable])

theorem complete (hc : ∀ J ∈ Plan.gradedPlan D.plan, J ≠ (A, l) → ∃ d, D.cell d = J) :
    (scheme D K l hKl hlA).IsComplete := fun J hJ => by
  by_cases he : J = (A, l)
  · exact ⟨apex D K l hKl hlA, (apex_index D K l hKl hlA).trans he.symm⟩
  · obtain ⟨d, hd⟩ := hc J hJ he
    exact ⟨old D K l hKl hlA d, (old_index D K l hKl hlA d).trans hd⟩

theorem exists_active (hk : 1 ≤ K) (hc : sem.IsConsistent) (hb : sem.IsBountiful)
    (hcode : sem.IsCoded) {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) :
    ∃ (out : Semantics (scheme D K l hKl hlA)) (q : Cell (scheme D K l hKl hlA) → ExtOrd),
      out.IsConsistent ∧ out.IsBountiful ∧ out.IsCoded ∧ RespectsSemantics out q ∧
      (∀ c d, out.E (old D K l hKl hlA c) (ownerEquiv D K l hK hKl hlA c d) = sem.E c d) ∧
      (∀ d, q (old D K l hKl hlA d) = p d) ∧ q (apex D K l hKl hlA) = ⊤ := by
  have hsep : ¬ GradedLe (A, l) (A, K) := fun h => (not_le_of_gt hKl) h.2
  let e := HighLayerBountiful.equiv D Unit l (positive K l hKl) hlA (A, K) hsep
  let low : (scheme D K l hKl hlA).below (A, K) → ExtOrd := fun d => p (e.symm d).1
  have hlaw : RespectsSemanticsBelow (base D sem K l hK hKl hlA) (A, K) low :=
    (HighLayerBountiful.respects_iff D Unit l (positive K l hKl) hlA K hK hKl sem
      (base D sem K l hK hKl hlA) (inherited_row D sem K l hK hKl hlA)
      (A, K) hsep (fun d => p d.1)).mp (hp.toBelow (A, K))
  have hg : (scheme D K l hKl hlA).grade (apex D K l hKl hlA) = l :=
    congrArg Prod.snd (apex_index D K l hKl hlA)
  obtain ⟨out, q, hoc, hob, hcod, hq, he, hread, htop⟩ :=
    HighGradeExtension.exists_extension (base D sem K l hK hKl hlA)
      (apex D K l hKl hlA) (by rw [hg]; exact hKl)
      (congrArg Prod.fst (apex_index D K l hKl hlA)) low hlaw ⊤
      (by simp only [SelfVis, extVisibilityReplace_top]) hk
      (consistent D sem K l hK hKl hlA hc)
      (bountiful D sem K l hK hKl hlA (Nat.zero_lt_of_lt hk) hb)
      (coded D sem K l hK hKl hlA hcode)
  refine ⟨out, q, hoc, hob, hcod, hq, fun c d => ?_, fun d => ?_, htop⟩
  · rw [he _ (by change ((scheme D K l hKl hlA).cell _).2 ≤ K; rw [old_index]; exact hK c)]
    exact inherited_row D sem K l hK hKl hlA c d
  · let dlow : D.below (A, K) := ⟨d, D.isPlan.subset_of_mem (D.scope_mem_plan d), hK d⟩
    have hh := hread (e dlow)
    dsimp only [low] at hh; rwa [e.symm_apply_apply] at hh

end
end MaximalFullLayer
end VaughtConjecture.Knight
