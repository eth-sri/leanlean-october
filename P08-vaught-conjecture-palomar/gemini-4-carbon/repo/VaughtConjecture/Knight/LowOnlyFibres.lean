/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorRetarget
public import VaughtConjecture.Knight.CappedDonorRelease
public import VaughtConjecture.Knight.PartialSections

@[expose] public section

namespace VaughtConjecture.Knight.LowOnly

open Transform Value ExtOrd SharpWitnessComposition AmalgamationPlan CappedDonor CappedDonor.Ref
open CappedDonor.Ref.LowRef

noncomputable section

section Retarget
variable {n : ℕ} {P : SemScheme n} {BJ : Finset (Fin n) × ℕ}
  {p : Cell P.scheme → ExtOrd} (hp : RespectsSemantics P.rows p)

include hp in
theorem srcP_nonTop_lt_top (o : P.scheme.below BJ) (ho : p o.1 = ⊤)
    (d t : P.scheme.below (P.scheme.cell o.1)) (hd : p d.1 ≠ ⊤) (ht : p t.1 = ⊤) :
    extVisibilityReplace (P.rows.E o.1 d) (P.scheme.grade o.1) (P.scheme.grade o.1) <
      P.rows.E o.1 t := by
  have hp := hp.toBelow BJ
  obtain ⟨τ, hτ, -, hread⟩ := exists_bounded_exact_capped_witness
    (grade := fun d : P.scheme.below (P.scheme.cell o.1) => P.scheme.grade d.1)
    (c := ⟨o.1, GradedLe.refl _⟩) (p := fun d => p d.1) (fun d => d.2.2)
    (hp.orderly o).symm (hp.locality o)
  have hd' : τ (P.rows.E o.1 d) = p d.1 := by
    rw [hread]; change min (p d.1) (p o.1) = _; rw [ho, min_top_right]
  have ht' : τ (P.rows.E o.1 t) = ⊤ := by
    rw [hread]; change min (p t.1) (p o.1) = _; rw [ho, ht, min_top_right]
  by_contra hle
  have h := hτ.mono (not_lt.mp hle)
  rw [ht', hτ.comm_gTop _ le_rfl, hd', top_le_iff] at h
  exact TopSupport.evr_ne_top hd _ _ h

open Classical in
def retargetTops (η : ExtOrd) (u : P.scheme.below BJ → ExtOrd)
    (d : P.scheme.below BJ) : ExtOrd :=
  if p d.1 = ⊤ then η else u d

theorem retargetTops_of_top (η : ExtOrd) (u : P.scheme.below BJ → ExtOrd)
    {d : P.scheme.below BJ} (h : p d.1 = ⊤) : retargetTops (p := p) η u d = η :=
  ite_eq_left h

theorem retargetTops_of_nonTop (η : ExtOrd) (u : P.scheme.below BJ → ExtOrd)
    {d : P.scheme.below BJ} (h : p d.1 ≠ ⊤) : retargetTops (p := p) η u d = u d :=
  ite_eq_right h

structure RetargetData {K : ℕ} (u : P.scheme.below BJ → ExtOrd) (b η : ExtOrd) : Prop where
  respects : RespectsSemanticsBelow P.rows BJ u
  b_vis : SelfVis K b
  b_pos : ⊥ < b
  nonTop_lt : ∀ d, p d.1 ≠ ⊤ → u d < b
  top_ge : ∀ d, p d.1 = ⊤ → b ≤ u d
  η_vis : SelfVis K η
  b_le_η : b ≤ η

def RetargetData.srcMax (o : P.scheme.below BJ) : ExtOrd :=
  letI := Fintype.ofFinite (P.scheme.below (P.scheme.cell o.1))
  (Finset.univ.filter fun d : P.scheme.below (P.scheme.cell o.1) => p d.1 ≠ ⊤).sup
    fun d => extVisibilityReplace (P.rows.E o.1 d) (P.scheme.grade o.1) (P.scheme.grade o.1)

include hp in
theorem RetargetData.retargetTops_respects {K : ℕ} {u : P.scheme.below BJ → ExtOrd} {b η : ExtOrd}
    (hu : RetargetData (p := p) (K := K) u b η)
    (htop : ∀ d, p d = ⊤ → P.scheme.grade d ≤ K) :
    RespectsSemanticsBelow P.rows BJ (retargetTops (p := p) η u) where
  orderly d := by
    by_cases h : p d.1 = ⊤
    · rw [retargetTops_of_top η u h]; exact (hu.η_vis.mono (htop d.1 h)).symm
    · rw [retargetTops_of_nonTop η u h]; exact hu.respects.orderly d
  locality o := by
    by_cases ho : p o.1 = ⊤
    · obtain ⟨τ, hτ, -, hread⟩ := exists_bounded_exact_capped_witness
        (grade := fun d : P.scheme.below (P.scheme.cell o.1) => P.scheme.grade d.1)
        (c := ⟨o.1, GradedLe.refl _⟩) (p := fun d => u (CellScheme.below.incl o d))
        (fun d => d.2.2) (hu.respects.orderly o).symm (hu.respects.locality o)
      have hko : P.scheme.grade o.1 ≤ K := htop o.1 ho
      have hτa : τ (RetargetData.srcMax (p := p) o) ≤ b := by
        let _ := Fintype.ofFinite (P.scheme.below (P.scheme.cell o.1))
        unfold RetargetData.srcMax
        rw [Finset.apply_sup_eq_sup_comp τ (fun _ _ => hτ.mono.map_max) hτ.bot]
        refine Finset.sup_le fun d hd => ?_
        simp only [Function.comp_apply, hτ.comm_gTop _ le_rfl, hread]
        exact evr_le_of_le_selfVis hu.b_vis hko le_rfl ((min_le_left _ _).trans
          (hu.nonTop_lt _ (Finset.mem_filter.mp hd).2).le)
      have hsmvis : SelfVis (P.scheme.grade o.1) (RetargetData.srcMax (p := p) o) :=
        TopSupport.selfVis_sup_evr _ _ _
      refine (retargetShifter_witness hτ hsmvis hτa
        hu.b_le_η (hu.η_vis.mono hko) (hu.b_pos.trans_le hu.b_le_η)).transformsTo fun d => ?_
      have hg : gTop (P.scheme.grade (⟨o.1, GradedLe.refl _⟩ :
          P.scheme.below (P.scheme.cell o.1)).1) (P.scheme.grade d.1) = ⊤ := gTop_of_le d.2.2
      rw [hg, min_top_right, retargetTops_of_top η u ho]
      by_cases hd : p d.1 = ⊤
      · rw [retargetTops_of_top η u (d := CellScheme.below.incl o d) hd, min_self]
        have hne : τ (P.rows.E o.1 d) ≠ ⊥ := by
          rw [hread]
          exact ne_bot_of_gt (lt_min (hu.b_pos.trans_le (hu.top_ge _ hd))
            (hu.b_pos.trans_le (hu.top_ge o ho)))
        have hpos : ⊥ < P.rows.E o.1 d := by
          have hp' := hp.toBelow BJ
          obtain ⟨τ', hτ', -, hread'⟩ := exists_bounded_exact_capped_witness
            (grade := fun e : P.scheme.below (P.scheme.cell o.1) => P.scheme.grade e.1)
            (c := ⟨o.1, GradedLe.refl _⟩) (p := fun e => p e.1) (fun e => e.2.2)
            (hp'.orderly o).symm (hp'.locality o)
          have h := hread' d
          change τ' (P.rows.E o.1 d) = min (p d.1) (p o.1) at h
          rw [hd, ho, min_top_right] at h
          exact bot_lt_iff_ne_bot.mpr fun hb => bot_ne_top (by rwa [hb, hτ'.bot] at h)
        have hlt : RetargetData.srcMax (p := p) o < P.rows.E o.1 d := by
          let _ := Fintype.ofFinite (P.scheme.below (P.scheme.cell o.1))
          unfold RetargetData.srcMax
          exact (Finset.sup_lt_iff hpos).mpr fun e he =>
            srcP_nonTop_lt_top hp o ho e d (Finset.mem_filter.mp he).2 hd
        rw [retargetShifter_of_lt hne hlt]
      · have hle : P.rows.E o.1 d ≤ RetargetData.srcMax (p := p) o := by
          let _ := Fintype.ofFinite (P.scheme.below (P.scheme.cell o.1))
          exact (TopSupport.le_evr_self _ _).trans (Finset.le_sup (f := fun e =>
            extVisibilityReplace (P.rows.E o.1 e) (P.scheme.grade o.1) (P.scheme.grade o.1))
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩))
        rw [retargetTops_of_nonTop η u (d := CellScheme.below.incl o d) hd,
          retargetShifter_of_le hle, hread]
        change min (u (CellScheme.below.incl o d)) η = min (u (CellScheme.below.incl o d)) (u o)
        rw [min_eq_left ((hu.nonTop_lt _ hd).le.trans hu.b_le_η),
          min_eq_left ((hu.nonTop_lt _ hd).le.trans (hu.top_ge o ho))]
    · have heq : (fun d : P.scheme.below (P.scheme.cell o.1) =>
          min (retargetTops (p := p) η u (CellScheme.below.incl o d))
            (retargetTops (p := p) η u o)) =
          fun d => min (u (CellScheme.below.incl o d)) (u o) := by
        funext d; rw [retargetTops_of_nonTop η u ho]
        by_cases hd : p d.1 = ⊤
        · rw [retargetTops_of_top η u (d := CellScheme.below.incl o d) hd,
            min_eq_right ((hu.nonTop_lt o ho).le.trans hu.b_le_η),
            min_eq_right ((hu.nonTop_lt o ho).le.trans (hu.top_ge _ hd))]
        · rw [retargetTops_of_nonTop η u (d := CellScheme.below.incl o d) hd]
      rw [heq]; exact hu.respects.locality o
  availability Sig Xi₀ hs hg := by
    by_cases hS : p Sig.1 = ⊤
    · obtain ⟨Xi, hcell, hle⟩ := (hp.toBelow BJ).availability Sig Xi₀ hs hg
      refine ⟨Xi, hcell, ?_⟩
      rw [retargetTops_of_top η u hS, retargetTops_of_top η u (top_le_iff.mp (hS ▸ hle))]
    · obtain ⟨Xi, hcell, hle⟩ := hu.respects.availability Sig Xi₀ hs hg
      refine ⟨Xi, hcell, ?_⟩
      rw [retargetTops_of_nonTop η u hS]
      by_cases hX : p Xi.1 = ⊤
      · rw [retargetTops_of_top η u hX]; exact (hu.nonTop_lt Sig hS).le.trans hu.b_le_η
      · rw [retargetTops_of_nonTop η u hX]; exact hle
end Retarget

def faceIndex {n : ℕ} (A : Finset (Fin n)) (j : ℕ) : Finset (Fin n) × ℕ :=
  (A, min A.card j)

theorem faceIndex_le {n : ℕ} (A : Finset (Fin n)) (j : ℕ) :
    GradedLe (faceIndex A j) (effC n j) :=
  ⟨Finset.subset_univ _, le_min (min_le_right _ _)
    ((min_le_left _ _).trans (by simpa using Finset.card_le_univ A))⟩

theorem faceIndex_mono {n : ℕ} (A : Finset (Fin n)) {i j : ℕ} (h : i ≤ j) :
    GradedLe (faceIndex A i) (faceIndex A j) := ⟨le_rfl, min_le_min_left _ h⟩

theorem faceIndex_mem {n : ℕ} {P : SemScheme n} {A : Finset (Fin n)} (hA : A ∈ P.scheme.plan)
    {j : ℕ} (hj : 0 < min A.card j) : faceIndex A j ∈ Plan.gradedPlan P.scheme.plan :=
  Plan.mem_gradedPlan.mpr ⟨hA, hj, min_le_left _ _⟩

theorem faceIndex_absent {n : ℕ} {P : SemScheme n} {A : Finset (Fin n)} {j : ℕ}
    (h : ¬ 0 < min A.card j) (d : P.scheme.below (faceIndex A j)) : False :=
  h ((P.scheme.grade_pos d.1).trans_le d.2.2)

theorem RetargetData.exists_retarget_restore {n : ℕ} {P : SemScheme n}
    {p : Cell P.scheme → ExtOrd} (hp : RespectsSemantics P.rows p)
    {K j : ℕ} (hK : 0 < K) (hn : 0 < n) (hj : K ≤ j)
    (ht : ∀ d, p d = ⊤ → P.scheme.grade d ≤ K)
    {u : P.scheme.below (effC n j) → ExtOrd} {b η : ExtOrd}
    (hu : RetargetData (p := p) (K := K) u b η)
    {A : Finset (Fin n)} (hA : A ∈ P.scheme.plan)
    {v : P.scheme.below (faceIndex A j) → ExtOrd}
    (hv : RespectsSemanticsBelow P.rows (faceIndex A j) v)
    (hnon : ∀ a, p a.1 ≠ ⊤ → v a = u (CellScheme.below.mono (faceIndex_le A j) a))
    (htop : ∀ a, p a.1 = ⊤ → η ≤ v a) :
    ∃ u' : P.scheme.below (effC n j) → ExtOrd,
      RespectsSemanticsBelow P.rows (effC n j) u' ∧
      (∀ d, p d.1 ≠ ⊤ → u' d = u d) ∧ (∀ d, p d.1 = ⊤ → η ≤ u' d) ∧
      ∀ a, u' (CellScheme.below.mono (faceIndex_le A j) a) = v a := by
  have hKj : GradedLe (effC n K) (effC n j) := ⟨le_rfl, min_le_min_right _ hj⟩
  have hwK := (hu.retargetTops_respects hp ht).mono hKj
  have hrest : ∃ w : P.scheme.below (effC n K) → ExtOrd,
      RespectsSemanticsBelow P.rows (effC n K) w ∧
      (∀ d, min (w d) η = min (retargetTops (p := p) η u (CellScheme.below.mono hKj d)) η) ∧
      ∀ a : P.scheme.below (faceIndex A K),
        w (CellScheme.below.mono (faceIndex_le A K) a) =
          v (CellScheme.below.mono (faceIndex_mono A hj) a) := by
    by_cases hk : 0 < min A.card K
    · refine P.bountiful.extend (faceIndex_mem hA hk) (effC_mem hK hn) (faceIndex_le A K)
        (hv.mono (faceIndex_mono A hj)) hwK (hu.η_vis.mono (min_le_left _ _)) fun a => ?_
      by_cases hat : p a.1 = ⊤
      · rw [retargetTops_of_top η u hat, min_self]; exact (min_eq_right (htop _ hat)).symm
      · rw [retargetTops_of_nonTop η u hat]
        exact congrArg (fun x => min x η)
          (hnon (CellScheme.below.mono (faceIndex_mono A hj) a) hat).symm
    · exact ⟨_, hwK, fun _ => rfl, fun a => (faceIndex_absent hk a).elim⟩
  obtain ⟨w, hw, hcap, hface⟩ := hrest
  have hlowNon (d : P.scheme.below (effC n K)) (hd : p d.1 ≠ ⊤) :
      w d = u (CellScheme.below.mono hKj d) := by
    have h := hcap d; rw [retargetTops_of_nonTop η u hd] at h
    exact eq_of_capAgree_of_lt h.symm ((hu.nonTop_lt _ hd).trans_le hu.b_le_η)
  have hlowTop (d : P.scheme.below (effC n K)) (hd : p d.1 = ⊤) : η ≤ w d := by
    have h := hcap d; rw [retargetTops_of_top η u hd, min_self] at h
    exact h.symm ▸ min_le_left _ _
  refine ⟨glueSection w u, hu.respects.glue hKj rfl hw ?_, ?_, ?_, ?_⟩
  · intro Sig hS d hd
    have hSn : p Sig.1 ≠ ⊤ := fun htop =>
      hS ⟨Finset.subset_univ _, le_min (ht Sig.1 htop) (gradeC_le Sig.1)⟩
    by_cases hdt : p d.1 = ⊤
    · rw [min_eq_right ((hu.nonTop_lt Sig hSn).le.trans (hu.b_le_η.trans (hlowTop ⟨d.1, hd⟩ hdt))),
        min_eq_right ((hu.nonTop_lt Sig hSn).le.trans (hu.top_ge _ hdt))]
    · rw [hlowNon ⟨d.1, hd⟩ hdt]; rfl
  · intro d hd
    by_cases h : GradedLe (P.scheme.cell d.1) (effC n K)
    · rw [glueSection_of_le w u h, hlowNon ⟨d.1, h⟩ hd]; rfl
    · rw [glueSection_of_not_le w u h]
  · intro d hd
    have h : GradedLe (P.scheme.cell d.1) (effC n K) :=
      ⟨Finset.subset_univ _, le_min (ht d.1 hd) (gradeC_le d.1)⟩
    rw [glueSection_of_le w u h]; exact hlowTop ⟨d.1, h⟩ hd
  · intro a
    by_cases hK : P.scheme.grade a.1 ≤ K
    · have hg : GradedLe (P.scheme.cell a.1) (effC n K) :=
        ⟨Finset.subset_univ _, le_min hK (gradeC_le a.1)⟩
      rw [glueSection_of_le w u hg]
      exact hface ⟨a.1, a.2.1, le_min (a.2.2.trans (min_le_left _ _)) hK⟩
    · have hg : ¬ GradedLe (P.scheme.cell a.1) (effC n K) := fun hg =>
        hK (hg.2.trans (min_le_left _ _))
      rw [glueSection_of_not_le w u hg]
      exact (hnon a fun ht' => hK (ht a.1 ht')).symm

structure SourceGap {n : ℕ} (C : SemScheme n) (K : ℕ) where
  c : Cell C.scheme
  c_grade : C.scheme.grade c = K
  r : C.scheme.below (C.scheme.cell c)
  gap_c : extVisibilityReplace (C.rows.E c r) K K < C.rows.E c ⟨c, GradedLe.refl _⟩

namespace SourceGap
variable {n K : ℕ} {C : SemScheme n} (L : SourceGap C K)

abbrev Dom := C.scheme.below (C.scheme.cell L.c)
def cL : L.Dom := ⟨L.c, GradedLe.refl _⟩

include L in
theorem K_pos : 0 < K := (C.scheme.grade_pos L.c).trans_eq L.c_grade

include L in
theorem K_le : K ≤ n := L.c_grade.symm.trans_le (gradeC_le L.c)

def h : ExtOrd := extVisibilityReplace (C.rows.E L.c L.r) K K

def e (v : L.Dom → ExtOrd) : ExtOrd :=
  min (v L.cL) (extVisibilityReplace (v L.r) K K)

theorem e_min {γ : ExtOrd} (hγ : SelfVis K γ) (v : L.Dom → ExtOrd) :
    L.e (fun d => min (v d) γ) = min (L.e v) γ := by
  unfold e; rw [evr_min_of_selfVis hγ le_rfl le_rfl, min_min_min_comm, min_self]

theorem c_selfVis {v : L.Dom → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (C.scheme.cell L.c) v) : SelfVis K (v L.cL) := by
  have h := (hv.orderly L.cL).symm
  change SelfVis (C.scheme.grade L.c) (v L.cL) at h
  rwa [L.c_grade] at h

theorem e_selfVis {v : L.Dom → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (C.scheme.cell L.c) v) : SelfVis K (L.e v) :=
  selfVis_min (L.c_selfVis hv) (TopSupport.selfVis_evr_self K _)

theorem exists_witness {v : L.Dom → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (C.scheme.cell L.c) v) :
    ∃ τ : ExtOrd → ExtOrd, Witness (gTop K) τ ∧ (∀ x, τ x ≤ v L.cL) ∧
      ∀ d : L.Dom, τ (C.rows.E L.c d) = min (v d) (v L.cL) := by
  have h := exists_bounded_exact_capped_witness (grade := fun d : L.Dom => C.scheme.grade d.1)
    (c := L.cL) (p := v) (fun d => d.2.2) (hv.orderly L.cL).symm (hv.locality L.cL)
  have hg : C.scheme.grade L.cL.1 = K := L.c_grade
  rwa [hg] at h

theorem e_le_of_gap {v : L.Dom → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (C.scheme.cell L.c) v)
    (d : L.Dom) (hd : L.h < C.rows.E L.c d) : L.e v ≤ v d := by
  obtain ⟨τ, hτ, -, hread⟩ := L.exists_witness hv
  have heq : L.e v = τ L.h := by
    unfold e h
    rw [hτ.comm_gTop _ le_rfl, hread, evr_min_of_selfVis (L.c_selfVis hv) le_rfl le_rfl, min_comm]
  rw [heq]; exact (hτ.mono hd.le).trans ((hread d).le.trans (min_le_left _ _))

theorem domLe {j : ℕ} (hj : K ≤ j) : GradedLe (C.scheme.cell L.c) (effC n j) :=
  ⟨Finset.subset_univ _, L.c_grade.trans_le (le_min hj L.K_le)⟩

def lowD {j : ℕ} (hj : K ≤ j) (v : C.scheme.below (effC n j) → ExtOrd)
    (d : L.Dom) : ExtOrd := v (CellScheme.below.mono (L.domLe hj) d)

theorem lowD_respects {j : ℕ} (hj : K ≤ j) {v : C.scheme.below (effC n j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v) :
    RespectsSemanticsBelow C.rows (C.scheme.cell L.c) (L.lowD hj v) := hv.mono (L.domLe hj)

def cC {j : ℕ} (hj : K ≤ j) : C.scheme.below (effC n j) :=
  CellScheme.below.mono (L.domLe hj) L.cL

def rC {j : ℕ} (hj : K ≤ j) : C.scheme.below (effC n j) :=
  CellScheme.below.mono (L.domLe hj) L.r

def eC {j : ℕ} (hj : K ≤ j) (v : C.scheme.below (effC n j) → ExtOrd) : ExtOrd :=
  L.e (L.lowD hj v)

theorem exists_release {j : ℕ} (hj : K ≤ j)
    {v : C.scheme.below (effC n j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v) {γ : ExtOrd}
    (hγ : SelfVis (effC n j).2 γ) (hγpos : γ ≠ ⊥) (he : γ < L.eC hj v)
    {A : Finset (Fin n)} (hA : A ∈ C.scheme.plan) (hAc : A ⊆ C.scheme.scope L.c)
    (T : Cell C.scheme → Prop)
    (htop : ∀ a : C.scheme.below (faceIndex A j), T a.1 → C.scheme.grade a.1 ≤ K)
    (hgap : ∀ (a : C.scheme.below (faceIndex A K))
      (ha : GradedLe (C.scheme.cell a.1) (C.scheme.cell L.c)),
      T a.1 → L.h < C.rows.E L.c ⟨a.1, ha⟩)
    (hshield : ∀ a : C.scheme.below (faceIndex A j), ¬ T a.1 →
      v (CellScheme.below.mono (faceIndex_le A j) a) < γ) :
    ∃ v' : C.scheme.below (effC n j) → ExtOrd,
      RespectsSemanticsBelow C.rows (effC n j) v' ∧
      (∀ a : C.scheme.below (faceIndex A j),
        v' (CellScheme.below.mono (faceIndex_le A j) a) =
          v (CellScheme.below.mono (faceIndex_le A j) a)) ∧
      (∀ d, min (v' d) γ = min (v d) γ) ∧ L.eC hj v' = γ := by
  have hγK : SelfVis K γ := hγ.mono (le_min hj L.K_le)
  set w₀ := L.lowD hj v
  have hw₀ := L.lowD_respects hj hv
  have hγL : γ < w₀ L.cL := he.trans_le (min_le_left _ _)
  have hγr : γ ≤ w₀ L.r := by
    by_contra hlt
    exact lt_irrefl _ ((he.trans_le (min_le_right _ _)).trans_le
      (evr_le_of_le_selfVis hγK le_rfl le_rfl (not_le.mp hlt).le))
  obtain ⟨τ, hτ, -, hread⟩ := L.exists_witness hw₀
  have hν : Witness (gTop K) (releaseShifter τ L.h γ) :=
    releaseShifter_witness hτ (TopSupport.selfVis_evr_self K _) hγK hγpos
  set w : L.Dom → ExtOrd := fun d => releaseShifter τ L.h γ (C.rows.E L.c d)
  have hcapL : SelfVis (C.scheme.cell L.c).2 (w₀ L.cL) := by
    change SelfVis (C.scheme.grade L.c) (w₀ L.cL); rw [L.c_grade]; exact L.c_selfVis hw₀
  have ht : RespectsSemanticsBelow C.rows (C.scheme.cell L.c) (fun d => τ (C.rows.E L.c d)) := by
    rw [show (fun d : L.Dom => τ (C.rows.E L.c d)) = fun d => min (w₀ d) (w₀ L.cL) from funext hread]
    exact hw₀.cap hcapL
  have hw : RespectsSemanticsBelow C.rows (C.scheme.cell L.c) w :=
    (map_respects_iff_rowBlockBottom (C.consistent L.c) (fun d => d.2.2.trans_eq L.c_grade)
      (boundedMap_of_witness hν)).mpr
      (rowBlockBottom_of_same_pattern (rowBlockBottom_of_respects ht)
        fun _ => releaseShifter_eq_bot_iff hγpos _)
  have hwc : w L.cL = w₀ L.cL :=
    (releaseShifter_of_lt L.gap_c).trans ((hread L.cL).trans (min_self _))
  have hwr : w L.r = γ :=
    (releaseShifter_of_le (TopSupport.le_evr_self _ K)).trans
      ((congrArg (fun x => min x γ) (hread L.r)).trans (min_eq_right (le_min hγr hγL.le)))
  have hwcap (d : L.Dom) : min (w d) γ = min (w₀ d) γ := by
    change min (releaseShifter τ L.h γ (C.rows.E L.c d)) γ = _
    unfold releaseShifter; split_ifs
    · rw [hread, min_assoc, min_self, min_assoc, min_eq_right hγL.le]
    · rw [hread, min_assoc, min_eq_right hγL.le]
  have hfaceLe : GradedLe (faceIndex A K) (C.scheme.cell L.c) :=
    ⟨hAc, (min_le_right _ _).trans_eq L.c_grade.symm⟩
  have hrest : ∃ w' : L.Dom → ExtOrd,
      RespectsSemanticsBelow C.rows (C.scheme.cell L.c) w' ∧
      (∀ d, min (w' d) (w₀ L.cL) = min (w d) (w₀ L.cL)) ∧
      ∀ a : C.scheme.below (faceIndex A K),
        w' (CellScheme.below.mono hfaceLe a) = w₀ (CellScheme.below.mono hfaceLe a) := by
    by_cases hk : 0 < min A.card K
    · refine C.bountiful.extend (faceIndex_mem hA hk) (C.scheme.cell_mem L.c)
        hfaceLe (hw₀.mono hfaceLe) hw hcapL fun a => ?_
      have hwface : w (CellScheme.below.mono hfaceLe a) =
          min (w₀ (CellScheme.below.mono hfaceLe a)) (w₀ L.cL) := by
        by_cases hat : T a.1
        · exact (releaseShifter_of_lt (hgap a (a.2.trans hfaceLe) hat)).trans (hread _)
        · have hlt : w₀ (CellScheme.below.mono hfaceLe a) < γ :=
            hshield (CellScheme.below.mono (faceIndex_mono A hj) a) hat
          change releaseShifter τ L.h γ _ = _
          unfold releaseShifter; split_ifs
          · rw [hread, min_eq_left ((min_le_left _ _).trans hlt.le)]
          · rw [hread]
      rw [hwface, min_assoc, min_self]
    · exact ⟨w, hw, fun _ => rfl, fun a => (faceIndex_absent hk a).elim⟩
  obtain ⟨w', hw', hcap', hface'⟩ := hrest
  have hw'r : w' L.r = γ := by
    have h := hcap' L.r; rw [hwr, min_eq_left hγL.le] at h
    exact eq_of_capAgree_of_lt (x := γ) (by rw [min_eq_left hγL.le]; exact h.symm) hγL
  have hw'c : w₀ L.cL ≤ w' L.cL := by
    have h := hcap' L.cL; rw [hwc, min_self] at h
    exact h.symm ▸ min_le_left _ _
  obtain ⟨v', hv', hcap, hlow⟩ := C.bountiful.extend (C.scheme.cell_mem L.c)
    (effC_mem (L.K_pos.trans_le hj) (L.K_pos.trans_le L.K_le))
    (L.domLe hj) hw' hv hγ fun d => by
      change min (w₀ d) γ = min (w' d) γ
      rw [← hwcap d, ← min_eq_right hγL.le, ← min_assoc, ← hcap' d, min_assoc, min_eq_right hγL.le]
  have hlowD : L.lowD hj v' = w' := funext hlow
  refine ⟨v', hv', ?_, hcap, ?_⟩
  · intro a
    by_cases hK : C.scheme.grade a.1 ≤ K
    · let aK : C.scheme.below (faceIndex A K) :=
        ⟨a.1, a.2.1, le_min (a.2.2.trans (min_le_left _ _)) hK⟩
      change L.lowD hj v' (CellScheme.below.mono hfaceLe aK) =
        L.lowD hj v (CellScheme.below.mono hfaceLe aK)
      rw [hlowD]; exact hface' aK
    · exact eq_of_capAgree_of_lt (hcap _).symm (hshield a fun ht => hK (htop a ht))
  · unfold eC e; rw [hlowD, hw'r, evr_eq_self_of_selfVis hγK, min_eq_right (hγL.le.trans hw'c)]

end SourceGap

open Classical in
def completeAt {n : ℕ} {P : SemScheme n} {j : ℕ} (a : Cell P.scheme → ExtOrd)
    (u : P.scheme.below (effC n j) → ExtOrd) (d : Cell P.scheme) : ExtOrd :=
  if hd : GradedLe (P.scheme.cell d) (effC n j) then u ⟨d, hd⟩ else a d

theorem completeAt_present {n : ℕ} {P : SemScheme n} {j : ℕ} (a : Cell P.scheme → ExtOrd)
    (u : P.scheme.below (effC n j) → ExtOrd) (d : P.scheme.below (effC n j)) :
    completeAt a u d.1 = u d := dite_eq_left d.2

theorem completeAt_future {n : ℕ} {P : SemScheme n} {j : ℕ} (a : Cell P.scheme → ExtOrd)
    (u : P.scheme.below (effC n j) → ExtOrd) (d : Cell P.scheme)
    (hd : j < P.scheme.grade d) : completeAt a u d = a d :=
  dite_eq_right fun h => (not_le.mpr hd) (h.2.trans (min_le_left _ _))

theorem completeAt_respects {n : ℕ} {P : SemScheme n} {j : ℕ} (a : Cell P.scheme → ExtOrd)
    {u : P.scheme.below (effC n j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effC n j) u) :
    RespectsSemanticsBelow P.rows (effC n j) (fun d => completeAt a u d.1) := by
  rw [show (fun d : P.scheme.below (effC n j) => completeAt a u d.1) = u from
    funext (completeAt_present a u)]
  exact hu

theorem completeAt_cap {n : ℕ} {P : SemScheme n} {j : ℕ} (a : Cell P.scheme → ExtOrd)
    {u : P.scheme.below (effC n j) → ExtOrd} {γ : ExtOrd}
    (hcap : ∀ d, min (u d) γ = min (a d.1) γ) (d : Cell P.scheme) :
    min (completeAt a u d) γ = min (a d) γ := by
  unfold completeAt; split_ifs with hd
  · exact hcap ⟨d, hd⟩
  · rfl

open Classical in
def nonTopMax {F : Type*} [Fintype F] (T : F → Prop) (a : F → ExtOrd) : ExtOrd :=
  (Finset.univ.filter fun d => ¬ T d).sup a

theorem le_nonTopMax {F : Type*} [Fintype F] {T : F → Prop} (a : F → ExtOrd) {d : F}
    (hd : ¬ T d) : a d ≤ nonTopMax T a := by
  classical exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩)

theorem clipped_activation {F : Type*} [Fintype F] {T : F → Prop} {a a' : F → ExtOrd}
    {b γ : ExtOrd} (hcap : ∀ d, min (a' d) γ = min (a d) γ)
    (hactive : nonTopMax T a' < min b γ) :
    (∀ d, ¬ T d → a' d = a d) ∧ nonTopMax T a' = nonTopMax T a ∧ nonTopMax T a < b := by
  classical
  have hfix (d : F) (hd : ¬ T d) : a' d = a d :=
    (eq_of_capAgree_of_lt (hcap d)
      (((le_nonTopMax a' hd).trans_lt hactive).trans_le (min_le_right _ _))).symm
  have hM : nonTopMax T a' = nonTopMax T a :=
    Finset.sup_congr rfl fun d hd => hfix d (Finset.mem_filter.mp hd).2
  exact ⟨hfix, hM, hM ▸ hactive.trans_le (min_le_left _ _)⟩

theorem clipped_cutoff_cap (b γ : ExtOrd) : min (min b γ) γ = min b γ := by
  rw [min_assoc, min_self]

structure CommonRoot {n : ℕ} (P C : SemScheme n) where
  A : Finset (Fin n)
  B : Finset (Fin n)
  A_mem : A ∈ P.scheme.plan
  B_mem : B ∈ C.scheme.plan
  card : A.card = B.card
  face : P.scheme.below (A, A.card) ≃ C.scheme.below (B, B.card)
  grade : ∀ a, P.scheme.grade a.1 = C.scheme.grade (face a).1
  scope : ∀ a b, P.scheme.scope a.1 ⊆ P.scheme.scope b.1 ↔
    C.scheme.scope (face a).1 ⊆ C.scheme.scope (face b).1
  row : ∀ (a : P.scheme.below (A, A.card))
    (d : P.scheme.below (P.scheme.cell a.1))
    (hd : GradedLe (C.scheme.cell (face ⟨d.1, d.2.trans a.2⟩).1)
      (C.scheme.cell (face a).1)),
    P.rows.E a.1 d = C.rows.E (face a).1 ⟨(face ⟨d.1, d.2.trans a.2⟩).1, hd⟩

namespace CommonRoot
variable {n : ℕ} {P C : SemScheme n} (R : CommonRoot P C)

def fullP {j : ℕ} (a : P.scheme.below (faceIndex R.A j)) : P.scheme.below (R.A, R.A.card) :=
  ⟨a.1, a.2.1, a.2.2.trans (min_le_left _ _)⟩

def fullC {j : ℕ} (a : C.scheme.below (faceIndex R.B j)) : C.scheme.below (R.B, R.B.card) :=
  ⟨a.1, a.2.1, a.2.2.trans (min_le_left _ _)⟩

def faceAt (j : ℕ) : P.scheme.below (faceIndex R.A j) ≃ C.scheme.below (faceIndex R.B j) where
  toFun a := ⟨(R.face (R.fullP a)).1, (R.face (R.fullP a)).2.1,
    le_min (R.face (R.fullP a)).2.2
      ((R.grade (R.fullP a)).symm.trans_le (a.2.2.trans (min_le_right _ _)))⟩
  invFun a := ⟨(R.face.symm (R.fullC a)).1, (R.face.symm (R.fullC a)).2.1,
    le_min (R.face.symm (R.fullC a)).2.2 (by
      have hg := R.grade (R.face.symm (R.fullC a))
      rw [Equiv.apply_symm_apply] at hg
      exact hg.trans_le (a.2.2.trans (min_le_right _ _)))⟩
  left_inv a := by
    apply Subtype.ext; change (R.face.symm (R.face (R.fullP a))).1 = a.1
    exact congrArg Subtype.val (R.face.symm_apply_apply (R.fullP a))
  right_inv a := by
    apply Subtype.ext; change (R.face (R.face.symm (R.fullC a))).1 = a.1
    exact congrArg Subtype.val (R.face.apply_symm_apply (R.fullC a))

theorem respects_iff {j : ℕ} (v : C.scheme.below (faceIndex R.B j) → ExtOrd) :
    RespectsSemanticsBelow C.rows (faceIndex R.B j) v ↔
      RespectsSemanticsBelow P.rows (faceIndex R.A j) (fun a => v (R.faceAt j a)) := by
  have h := respects_iff_of_equiv (sem' := P.rows) (sem := C.rows) (R.faceAt j)
    (fun a => R.grade (R.fullP a)) (fun a b => R.scope (R.fullP a) (R.fullP b))
    (fun a d hd => R.row (R.fullP a) d hd) (fun a => v (R.faceAt j a))
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using h.symm

def Shared (u : Cell P.scheme → ExtOrd) (v : Cell C.scheme → ExtOrd) : Prop :=
  ∀ a, u a.1 = v (R.face a).1

theorem shared_at {u : Cell P.scheme → ExtOrd} {v : Cell C.scheme → ExtOrd}
    (h : R.Shared u v) {j : ℕ} (a : P.scheme.below (faceIndex R.A j)) :
    u a.1 = v (R.faceAt j a).1 := h (R.fullP a)

theorem shared_complete {j : ℕ} {u : Cell P.scheme → ExtOrd} {v : Cell C.scheme → ExtOrd}
    (h : R.Shared u v) (u' : P.scheme.below (effC n j) → ExtOrd)
    (v' : C.scheme.below (effC n j) → ExtOrd)
    (hface : ∀ a : P.scheme.below (faceIndex R.A j),
      u' (CellScheme.below.mono (faceIndex_le R.A j) a) =
        v' (CellScheme.below.mono (faceIndex_le R.B j) (R.faceAt j a))) :
    R.Shared (completeAt u u') (completeAt v v') := fun a => by
  by_cases hj : P.scheme.grade a.1 ≤ j
  · let a' : P.scheme.below (faceIndex R.A j) := ⟨a.1, a.2.1, le_min a.2.2 hj⟩
    exact (completeAt_present u u' (CellScheme.below.mono (faceIndex_le R.A j) a')).trans
      ((hface a').trans (completeAt_present v v'
        (CellScheme.below.mono (faceIndex_le R.B j) (R.faceAt j a'))).symm)
  · rw [completeAt_future u u' a.1 (not_le.mp hj),
      completeAt_future v v' (R.face a).1 (by rw [← R.grade]; exact not_le.mp hj)]
    exact h a

theorem installP {j : ℕ} {u : P.scheme.below (effC n j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effC n j) u)
    {v : C.scheme.below (effC n j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v)
    {γ : ExtOrd} (hγ : SelfVis (effC n j).2 γ)
    (hag : ∀ a : P.scheme.below (faceIndex R.A j),
      min (u (CellScheme.below.mono (faceIndex_le R.A j) a)) γ =
        min (v (CellScheme.below.mono (faceIndex_le R.B j) (R.faceAt j a))) γ) :
    ∃ u', RespectsSemanticsBelow P.rows (effC n j) u' ∧
      (∀ d, min (u' d) γ = min (u d) γ) ∧
      ∀ a : P.scheme.below (faceIndex R.A j),
        u' (CellScheme.below.mono (faceIndex_le R.A j) a) =
          v (CellScheme.below.mono (faceIndex_le R.B j) (R.faceAt j a)) := by
  by_cases hk : 0 < min R.A.card j
  · exact P.bountiful.extend (faceIndex_mem R.A_mem hk)
      (effC_mem (hk.trans_le (min_le_right _ _))
        ((hk.trans_le (min_le_left _ _)).trans_le (by simpa using Finset.card_le_univ R.A)))
      (faceIndex_le R.A j) ((R.respects_iff _).mp (hv.mono (faceIndex_le R.B j))) hu hγ hag
  · exact ⟨u, hu, fun _ => rfl, fun a => (faceIndex_absent hk a).elim⟩

theorem installC {j : ℕ} {v : C.scheme.below (effC n j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v)
    {u : P.scheme.below (effC n j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effC n j) u)
    {γ : ExtOrd} (hγ : SelfVis (effC n j).2 γ)
    (hag : ∀ a : P.scheme.below (faceIndex R.A j),
      min (v (CellScheme.below.mono (faceIndex_le R.B j) (R.faceAt j a))) γ =
        min (u (CellScheme.below.mono (faceIndex_le R.A j) a)) γ) :
    ∃ v', RespectsSemanticsBelow C.rows (effC n j) v' ∧
      (∀ d, min (v' d) γ = min (v d) γ) ∧
      ∀ a : P.scheme.below (faceIndex R.A j),
        v' (CellScheme.below.mono (faceIndex_le R.B j) (R.faceAt j a)) =
          u (CellScheme.below.mono (faceIndex_le R.A j) a) := by
  by_cases hk : 0 < min R.B.card j
  · have hlaw : RespectsSemanticsBelow C.rows (faceIndex R.B j)
        (fun a => u (CellScheme.below.mono (faceIndex_le R.A j) ((R.faceAt j).symm a))) := by
      apply (R.respects_iff _).mpr
      simpa only [Equiv.symm_apply_apply] using hu.mono (faceIndex_le R.A j)
    obtain ⟨v', hv', hcap, hface⟩ := C.bountiful.extend (faceIndex_mem R.B_mem hk)
      (effC_mem (hk.trans_le (min_le_right _ _))
        ((hk.trans_le (min_le_left _ _)).trans_le (by simpa using Finset.card_le_univ R.B)))
      (faceIndex_le R.B j) hlaw hv hγ
      (fun a => by simpa only [Equiv.apply_symm_apply] using hag ((R.faceAt j).symm a))
    exact ⟨v', hv', hcap, fun a => by simpa using hface (R.faceAt j a)⟩
  · exact ⟨v, hv, fun _ => rfl, fun a => (faceIndex_absent hk (R.faceAt j a)).elim⟩

end CommonRoot

structure Family {n : ℕ} (P C : SemScheme n) (K : ℕ) where
  root : CommonRoot P C
  gap : SourceGap C K
  p : Cell P.scheme → ExtOrd
  p_lawful : RespectsSemantics P.rows p
  top_grade : ∀ d, p d = ⊤ → P.scheme.grade d ≤ K
  root_sub : root.B ⊆ C.scheme.scope gap.c
  root_gap : ∀ (a : P.scheme.below (root.A, root.A.card)) (ht : p a.1 = ⊤),
    gap.h < C.rows.E gap.c ⟨(root.face a).1,
      ⟨(root.face a).2.1.trans root_sub,
        (root.grade a).symm.trans_le ((top_grade a.1 ht).trans_eq gap.c_grade.symm)⟩⟩

structure State {n : ℕ} (P C : SemScheme n) where
  u : Cell P.scheme → ExtOrd
  v : Cell C.scheme → ExtOrd
  b : ExtOrd

namespace State
variable {n : ℕ} {P C : SemScheme n}

def lowerP (S : State P C) (j : ℕ) (d : P.scheme.below (effC n j)) : ExtOrd := S.u d.1
def lowerC (S : State P C) (j : ℕ) (d : C.scheme.below (effC n j)) : ExtOrd := S.v d.1

def replace (S : State P C) {j : ℕ} (u : P.scheme.below (effC n j) → ExtOrd)
    (v : C.scheme.below (effC n j) → ExtOrd) (b : ExtOrd) : State P C :=
  ⟨completeAt S.u u, completeAt S.v v, b⟩

theorem replace_lowerP (S : State P C) {j : ℕ}
    (u : P.scheme.below (effC n j) → ExtOrd) (v : C.scheme.below (effC n j) → ExtOrd)
    (b : ExtOrd) : (S.replace u v b).lowerP j = u := funext (completeAt_present S.u u)

theorem replace_lowerC (S : State P C) {j : ℕ}
    (u : P.scheme.below (effC n j) → ExtOrd) (v : C.scheme.below (effC n j) → ExtOrd)
    (b : ExtOrd) : (S.replace u v b).lowerC j = v := funext (completeAt_present S.v v)

def CapEq (γ : ExtOrd) (S S' : State P C) : Prop :=
  (∀ d, min (S'.u d) γ = min (S.u d) γ) ∧
  (∀ d, min (S'.v d) γ = min (S.v d) γ) ∧ min S'.b γ = min S.b γ

def FutureEq (j : ℕ) (S S' : State P C) : Prop :=
  (∀ d, j < P.scheme.grade d → S'.u d = S.u d) ∧
  (∀ d, j < C.scheme.grade d → S'.v d = S.v d)

theorem replace_future (S : State P C) {j : ℕ}
    (u : P.scheme.below (effC n j) → ExtOrd) (v : C.scheme.below (effC n j) → ExtOrd)
    (b : ExtOrd) : S.FutureEq j (S.replace u v b) :=
  ⟨completeAt_future S.u u, completeAt_future S.v v⟩

theorem replace_caps (S : State P C) {j : ℕ}
    {u : P.scheme.below (effC n j) → ExtOrd} {v : C.scheme.below (effC n j) → ExtOrd}
    {b γ : ExtOrd} (hu : ∀ d, min (u d) γ = min (S.lowerP j d) γ)
    (hv : ∀ d, min (v d) γ = min (S.lowerC j d) γ) (hb : min b γ = min S.b γ) :
    S.CapEq γ (S.replace u v b) :=
  ⟨completeAt_cap S.u hu, completeAt_cap S.v hv, hb⟩
end State

namespace Family
variable {n K : ℕ} {P C : SemScheme n} (F : Family P C K)

def maximum (S : State P C) : ExtOrd := nonTopMax (fun d => F.p d = ⊤) S.u

structure Source (j : ℕ) (S : State P C) : Prop where
  lawfulP : RespectsSemanticsBelow P.rows (effC n j) (S.lowerP j)
  lawfulC : RespectsSemanticsBelow C.rows (effC n j) (S.lowerC j)
  shared : F.root.Shared S.u S.v
  futureP : ∀ d, j < P.scheme.grade d → SelfVis 1 (S.u d)
  futureC : ∀ d, j < C.scheme.grade d → SelfVis 1 (S.v d)

structure Admissible (j : ℕ) (S : State P C) : Prop extends F.Source j S where
  cutoff : SelfVis (min j K) S.b
  low : ∀ hj : K ≤ j, F.maximum S < S.b → ∀ d, F.p d = ⊤ →
    max S.b (F.gap.eC hj (S.lowerC j)) ≤ S.u d

theorem Source.replace {j : ℕ} {S : State P C} (hS : F.Source j S)
    {u : P.scheme.below (effC n j) → ExtOrd} {v : C.scheme.below (effC n j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effC n j) u)
    (hv : RespectsSemanticsBelow C.rows (effC n j) v) (b : ExtOrd)
    (hface : ∀ a : P.scheme.below (faceIndex F.root.A j),
      u (CellScheme.below.mono (faceIndex_le F.root.A j) a) =
        v (CellScheme.below.mono (faceIndex_le F.root.B j) (F.root.faceAt j a))) :
    F.Source j (S.replace u v b) where
  lawfulP := completeAt_respects S.u hu
  lawfulC := completeAt_respects S.v hv
  shared := F.root.shared_complete hS.shared u v hface
  futureP d hd := by
    rw [show (S.replace u v b).u d = S.u d from completeAt_future _ _ _ hd]; exact hS.futureP d hd
  futureC d hd := by
    rw [show (S.replace u v b).v d = S.v d from completeAt_future _ _ _ hd]; exact hS.futureC d hd

theorem Source.install_private {j : ℕ} {S : State P C} (hS : F.Source j S)
    {v : C.scheme.below (effC n j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v) {γ : ExtOrd}
    (hγ : SelfVis (effC n j).2 γ)
    (hag : ∀ d, min (v d) γ = min (S.lowerC j d) γ) :
    ∃ u, F.Source j (S.replace u v (min S.b γ)) ∧
      (∀ d, min (u d) γ = min (S.lowerP j d) γ) := by
  obtain ⟨u, hu, hcap, hface⟩ := F.root.installP hS.lawfulP hv hγ fun a => by
    rw [hag]; exact congrArg (fun x => min x γ) (F.root.shared_at hS.shared a)
  exact ⟨u, hS.replace F hu hv _ hface, hcap⟩

theorem Source.install_donor {j : ℕ} {S : State P C} (hS : F.Source j S)
    {u : P.scheme.below (effC n j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effC n j) u) {γ : ExtOrd}
    (hγ : SelfVis (effC n j).2 γ)
    (hag : ∀ d, min (u d) γ = min (S.lowerP j d) γ) :
    ∃ v, F.Source j (S.replace u v (min S.b γ)) ∧
      (∀ d, min (v d) γ = min (S.lowerC j d) γ) := by
  obtain ⟨v, hv, hcap, hface⟩ := F.root.installC hS.lawfulC hu hγ fun a => by
    rw [hag]; exact congrArg (fun x => min x γ) (F.root.shared_at hS.shared a).symm
  exact ⟨v, hS.replace F hu hv _ (fun a => (hface a).symm), hcap⟩

theorem frontier_cap {j : ℕ} (hj : K ≤ j) {v v' : C.scheme.below (effC n j) → ExtOrd}
    {γ : ExtOrd} (hγ : SelfVis K γ) (hag : ∀ d, min (v' d) γ = min (v d) γ) :
    min (F.gap.eC hj v') γ = min (F.gap.eC hj v) γ := by
  unfold SourceGap.eC; rw [← F.gap.e_min hγ, ← F.gap.e_min hγ]
  exact congrArg _ (funext fun d => hag (CellScheme.below.mono (F.gap.domLe hj) d))

include F in
theorem cap_visible {j : ℕ} (hj : K ≤ j) {γ : ExtOrd}
    (hγ : SelfVis (effC n j).2 γ) : SelfVis K γ := hγ.mono (le_min hj F.gap.K_le)

theorem top_present {j : ℕ} (hj : K ≤ j) {d : Cell P.scheme} (hd : F.p d = ⊤) :
    GradedLe (P.scheme.cell d) (effC n j) :=
  ⟨Finset.subset_univ _, le_min ((F.top_grade d hd).trans hj) (gradeC_le d)⟩

private theorem inactive_admissible {j : ℕ} (hj : K ≤ j) {S : State P C}
    (hS : F.Admissible j S) {u : P.scheme.below (effC n j) → ExtOrd}
    {v : C.scheme.below (effC n j) → ExtOrd} {γ : ExtOrd}
    (hQ : F.Source j (S.replace u v (min S.b γ)))
    (hbvis : SelfVis K (min S.b γ)) (hcap : S.CapEq γ (S.replace u v (min S.b γ)))
    (hfloor : min (max (min S.b γ) (F.gap.eC hj v)) γ =
      min (max S.b (F.gap.eC hj (S.lowerC j))) γ)
    (hη : F.maximum (S.replace u v (min S.b γ)) < min S.b γ →
      max (min S.b γ) (F.gap.eC hj v) ≤ γ) :
    F.Admissible j (S.replace u v (min S.b γ)) :=
  ⟨hQ, by change SelfVis (min j K) (min S.b γ); simpa only [min_eq_right hj] using hbvis,
    fun _ hm d hd => by
      obtain ⟨-, -, hmold⟩ := clipped_activation hcap.1 hm
      change max (min S.b γ) (F.gap.eC _ ((S.replace u v _).lowerC j)) ≤ _
      rw [State.replace_lowerC]
      exact (min_eq_left (hη hm)).symm.trans_le (hfloor.trans_le
        ((min_le_min_right _ (hS.low hj hmold d hd)).trans
          ((hcap.1 d).symm.trans_le (min_le_left _ _))))⟩

theorem private_active {j : ℕ} (hj : K ≤ j) {S : State P C}
    (hS : F.Admissible j S) {v : C.scheme.below (effC n j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v) {γ : ExtOrd}
    (hγ : SelfVis (effC n j).2 γ)
    (hag : ∀ d, min (v d) γ = min (S.lowerC j d) γ) :
    ∃ S', F.Admissible j S' ∧ S'.lowerC j = v ∧ S.CapEq γ S' ∧ S.FutureEq j S' := by
  obtain ⟨u, hQ, hucap⟩ := hS.toSource.install_private F hv hγ hag
  have hface0 (a : P.scheme.below (faceIndex F.root.A j)) :
      u (CellScheme.below.mono (faceIndex_le F.root.A j) a) =
        v (CellScheme.below.mono (faceIndex_le F.root.B j) (F.root.faceAt j a)) := by
    have h := F.root.shared_at hQ.shared a
    change (S.replace u v _).lowerP j (CellScheme.below.mono (faceIndex_le F.root.A j) a) =
      (S.replace u v _).lowerC j
        (CellScheme.below.mono (faceIndex_le F.root.B j) (F.root.faceAt j a)) at h
    simpa only [State.replace_lowerP, State.replace_lowerC] using h
  let Q := S.replace u v (min S.b γ)
  have hcap : S.CapEq γ Q := S.replace_caps hucap hag (clipped_cutoff_cap _ _)
  have hbvis : SelfVis K (min S.b γ) :=
    selfVis_min (by simpa only [min_eq_right hj] using hS.cutoff) (F.cap_visible hj hγ)
  have hfloor : min (max (min S.b γ) (F.gap.eC hj v)) γ =
      min (max S.b (F.gap.eC hj (S.lowerC j))) γ :=
    floor_min (clipped_cutoff_cap _ _) (F.frontier_cap hj (F.cap_visible hj hγ) hag)
  by_cases hact : F.maximum Q < min S.b γ ∧ γ < max (min S.b γ) (F.gap.eC hj v)
  · obtain ⟨hm, hη⟩ := hact
    obtain ⟨-, -, hmold⟩ := clipped_activation hcap.1 hm
    have hlow := hS.low hj hmold
    have hγfloor : γ ≤ max S.b (F.gap.eC hj (S.lowerC j)) := by
      rw [min_eq_right hη.le] at hfloor; exact min_eq_right_iff.mp hfloor.symm
    have htopγ (d : P.scheme.below (effC n j)) (hd : F.p d.1 = ⊤) : γ ≤ u d :=
      le_of_capAgree_of_le (hucap d).symm (hγfloor.trans (hlow d.1 hd))
    have hRD : RetargetData (p := F.p) (K := K) u (min S.b γ)
        (max (min S.b γ) (F.gap.eC hj v)) :=
      ⟨by simpa only [State.replace_lowerP] using hQ.lawfulP,
        hbvis, bot_lt_iff_ne_bot.mpr (fun h => not_lt_bot (h ▸ hm)),
        fun d hd => by
          simpa only [Q, State.replace, completeAt_present] using (le_nonTopMax Q.u hd).trans_lt hm,
        fun d hd => (min_le_right _ _).trans (htopγ d hd),
        TopSupport.selfVis_max_of hbvis (F.gap.e_selfVis (F.gap.lowD_respects hj hv)),
        le_max_left _ _⟩
    obtain ⟨u', hu', hnon, htop, hface⟩ := hRD.exists_retarget_restore
      F.p_lawful F.gap.K_pos (F.gap.K_pos.trans_le F.gap.K_le) hj F.top_grade
      F.root.A_mem ((F.root.respects_iff _).mp (hv.mono (faceIndex_le F.root.B j)))
      (fun a _ => (hface0 a).symm)
      (fun a ha => max_le
        ((min_le_right _ _).trans
          ((htopγ (CellScheme.below.mono (faceIndex_le F.root.A j) a) ha).trans_eq (hface0 a)))
        (F.gap.e_le_of_gap (F.gap.lowD_respects hj hv) _ (F.root_gap (F.root.fullP a) ha)))
    have hcap' (d : P.scheme.below (effC n j)) : min (u' d) γ = min (S.lowerP j d) γ := by
      by_cases hd : F.p d.1 = ⊤
      · change min (u' d) γ = min (S.u d.1) γ
        rw [min_eq_right (hη.le.trans (htop d hd)), min_eq_right (hγfloor.trans (hlow d.1 hd))]
      · rw [hnon d hd, hucap d]
    refine ⟨S.replace u' v (min S.b γ), ⟨hS.toSource.replace F hu' hv _ hface,
      by change SelfVis (min j K) (min S.b γ); simpa only [min_eq_right hj] using hbvis,
      fun _ _ d hd => ?_⟩,
      S.replace_lowerC _ _ _, S.replace_caps hcap' hag (clipped_cutoff_cap _ _),
      S.replace_future _ _ _⟩
    change max (min S.b γ) (F.gap.eC _ ((S.replace u' v _).lowerC j)) ≤ completeAt S.u u' d
    rw [State.replace_lowerC, completeAt_present S.u u' ⟨d, F.top_present hj hd⟩]
    exact htop _ hd
  · exact ⟨Q, F.inactive_admissible hj hS hQ hbvis hcap hfloor (fun hm =>
      not_lt.mp fun h => hact ⟨hm, h⟩), S.replace_lowerC _ _ _, hcap, S.replace_future _ _ _⟩

theorem release_root {j : ℕ} (hj : K ≤ j)
    {v : C.scheme.below (effC n j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v) {γ : ExtOrd}
    (hγ : SelfVis (effC n j).2 γ) (hbot : γ ≠ ⊥) (he : γ < F.gap.eC hj v)
    (hshield : ∀ a : P.scheme.below (faceIndex F.root.A j), F.p a.1 ≠ ⊤ →
      v (CellScheme.below.mono (faceIndex_le F.root.B j) (F.root.faceAt j a)) < γ) :
    ∃ v', RespectsSemanticsBelow C.rows (effC n j) v' ∧
      (∀ d, min (v' d) γ = min (v d) γ) ∧
      (∀ a : P.scheme.below (faceIndex F.root.A j),
        v' (CellScheme.below.mono (faceIndex_le F.root.B j) (F.root.faceAt j a)) =
          v (CellScheme.below.mono (faceIndex_le F.root.B j) (F.root.faceAt j a))) ∧
      F.gap.eC hj v' = γ := by
  let T (d : Cell C.scheme) : Prop :=
    ∃ a : P.scheme.below (F.root.A, F.root.A.card), (F.root.face a).1 = d ∧ F.p a.1 = ⊤
  obtain ⟨v', hv', hface, hcap, he'⟩ := F.gap.exists_release hj hv hγ hbot he
    F.root.B_mem F.root_sub T
    (by rintro a ⟨b, hb, ht⟩; rw [← hb, ← F.root.grade]; exact F.top_grade b.1 ht)
    (by rintro a ha ⟨b, hb, ht⟩
        rw [show (⟨a.1, ha⟩ : F.gap.Dom) = ⟨(F.root.face b).1, _⟩ from Subtype.ext hb.symm]
        exact F.root_gap b ht)
    (fun a ha => by
      have hn : F.p ((F.root.faceAt j).symm a).1 ≠ ⊤ := fun ht => ha
        ⟨F.root.fullP ((F.root.faceAt j).symm a),
          congrArg Subtype.val ((F.root.faceAt j).apply_symm_apply a), ht⟩
      simpa only [Equiv.apply_symm_apply] using hshield ((F.root.faceAt j).symm a) hn)
  exact ⟨v', hv', hcap, fun a => hface (F.root.faceAt j a), he'⟩

theorem donor_active {j : ℕ} (hj : K ≤ j) {S : State P C}
    (hS : F.Admissible j S) {u : P.scheme.below (effC n j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effC n j) u) {γ : ExtOrd}
    (hγ : SelfVis (effC n j).2 γ)
    (hag : ∀ d, min (u d) γ = min (S.lowerP j d) γ) :
    ∃ S', F.Admissible j S' ∧ S'.lowerP j = u ∧ S.CapEq γ S' ∧ S.FutureEq j S' := by
  obtain ⟨v, hQ, hvcap⟩ := hS.toSource.install_donor F hu hγ hag
  have hface0 (a : P.scheme.below (faceIndex F.root.A j)) :
      u (CellScheme.below.mono (faceIndex_le F.root.A j) a) =
        v (CellScheme.below.mono (faceIndex_le F.root.B j) (F.root.faceAt j a)) := by
    have h := F.root.shared_at hQ.shared a
    change (S.replace u v _).lowerP j (CellScheme.below.mono (faceIndex_le F.root.A j) a) =
      (S.replace u v _).lowerC j
        (CellScheme.below.mono (faceIndex_le F.root.B j) (F.root.faceAt j a)) at h
    simpa only [State.replace_lowerP, State.replace_lowerC] using h
  let Q := S.replace u v (min S.b γ)
  have hcap : S.CapEq γ Q := S.replace_caps hag hvcap (clipped_cutoff_cap _ _)
  have hbvis : SelfVis K (min S.b γ) :=
    selfVis_min (by simpa only [min_eq_right hj] using hS.cutoff) (F.cap_visible hj hγ)
  have hfloor : min (max (min S.b γ) (F.gap.eC hj v)) γ =
      min (max S.b (F.gap.eC hj (S.lowerC j))) γ :=
    floor_min (clipped_cutoff_cap _ _) (F.frontier_cap hj (F.cap_visible hj hγ) hvcap)
  by_cases hact : F.maximum Q < min S.b γ ∧ γ < F.gap.eC hj v
  · obtain ⟨hm, he⟩ := hact
    obtain ⟨-, -, hmold⟩ := clipped_activation hcap.1 hm
    have hγfloor : γ ≤ max S.b (F.gap.eC hj (S.lowerC j)) := by
      rw [min_eq_right (he.le.trans (le_max_right _ _))] at hfloor
      exact min_eq_right_iff.mp hfloor.symm
    obtain ⟨v', hv', hv'cap, hface', he'⟩ := F.release_root hj
      (by simpa only [State.replace_lowerC] using hQ.lawfulC) hγ
      (ne_bot_of_gt ((bot_le.trans_lt hm).trans_le (min_le_right _ _))) he fun a ha => by
        rw [← hface0]
        have h := ((le_nonTopMax Q.u ha).trans_lt hm).trans_le (min_le_right _ _)
        change Q.lowerP j (CellScheme.below.mono (faceIndex_le F.root.A j) a) < γ at h
        simpa only [Q, State.replace_lowerP] using h
    refine ⟨S.replace u v' (min S.b γ),
      ⟨hS.toSource.replace F hu hv' _ (fun a => (hface0 a).trans (hface' a).symm),
        by change SelfVis (min j K) (min S.b γ); simpa only [min_eq_right hj] using hbvis,
        fun _ _ d hd => ?_⟩,
      S.replace_lowerP _ _ _,
      S.replace_caps hag (fun d => (hv'cap d).trans (hvcap d)) (clipped_cutoff_cap _ _),
      S.replace_future _ _ _⟩
    change max (min S.b γ) (F.gap.eC _ ((S.replace u v' _).lowerC j)) ≤ completeAt S.u u d
    rw [State.replace_lowerC, he', max_eq_right (min_le_right _ _),
      completeAt_present S.u u ⟨d, F.top_present hj hd⟩]
    exact le_of_capAgree_of_le (hag _).symm (hγfloor.trans (hS.low hj hmold d hd))
  · exact ⟨Q, F.inactive_admissible hj hS hQ hbvis hcap hfloor (fun hm =>
      max_le (min_le_right _ _) (not_lt.mp fun h => hact ⟨hm, h⟩)),
      S.replace_lowerP _ _ _, hcap, S.replace_future _ _ _⟩

theorem private_lift {j : ℕ} {S : State P C} (hS : F.Admissible j S)
    {v : C.scheme.below (effC n j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v) {γ : ExtOrd}
    (hγ : SelfVis (effC n j).2 γ)
    (hag : ∀ d, min (v d) γ = min (S.lowerC j d) γ) :
    ∃ S', F.Admissible j S' ∧ S'.lowerC j = v ∧ S.CapEq γ S' ∧ S.FutureEq j S' := by
  by_cases hj : K ≤ j
  · exact F.private_active hj hS hv hγ hag
  obtain ⟨u, hQ, hucap⟩ := hS.toSource.install_private F hv hγ hag
  exact ⟨S.replace u v (min S.b γ), ⟨hQ, selfVis_min hS.cutoff (hγ.mono
    (le_min (min_le_left _ _) ((min_le_right _ _).trans F.gap.K_le))), fun h => (hj h).elim⟩,
    S.replace_lowerC _ _ _, S.replace_caps hucap hag (clipped_cutoff_cap _ _),
    S.replace_future _ _ _⟩

theorem donor_lift {j : ℕ} {S : State P C} (hS : F.Admissible j S)
    {u : P.scheme.below (effC n j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effC n j) u) {γ : ExtOrd}
    (hγ : SelfVis (effC n j).2 γ)
    (hag : ∀ d, min (u d) γ = min (S.lowerP j d) γ) :
    ∃ S', F.Admissible j S' ∧ S'.lowerP j = u ∧ S.CapEq γ S' ∧ S.FutureEq j S' := by
  by_cases hj : K ≤ j
  · exact F.donor_active hj hS hu hγ hag
  obtain ⟨v, hQ, hvcap⟩ := hS.toSource.install_donor F hu hγ hag
  exact ⟨S.replace u v (min S.b γ), ⟨hQ, selfVis_min hS.cutoff (hγ.mono
    (le_min (min_le_left _ _) ((min_le_right _ _).trans F.gap.K_le))), fun h => (hj h).elim⟩,
    S.replace_lowerP _ _ _, S.replace_caps hag hvcap (clipped_cutoff_cap _ _),
    S.replace_future _ _ _⟩

def zero : State P C := ⟨fun _ => ⊥, fun _ => ⊥, ⊥⟩

theorem zero_admissible (j : ℕ) : F.Admissible j (zero : State P C) :=
  ⟨⟨RespectsSemanticsBelow.bot _ _, RespectsSemanticsBelow.bot _ _, fun _ => rfl,
    fun _ _ => selfVis_bot _, fun _ _ => selfVis_bot _⟩, selfVis_bot _,
    fun _ h => (not_lt_bot h).elim⟩

theorem private_bottom_supply {j : ℕ} {v : C.scheme.below (effC n j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v) :
    ∃ S : State P C, F.Admissible j S ∧ S.lowerC j = v ∧ S.b = ⊥ ∧
      (zero : State P C).FutureEq j S := by
  obtain ⟨u, hQ, -⟩ := (F.zero_admissible j).toSource.install_private F hv
    (selfVis_bot _) (fun _ => by simp only [min_bot_right])
  exact ⟨(zero : State P C).replace u v ⊥,
    ⟨hQ, selfVis_bot _, fun _ hm => (not_lt_bot hm).elim⟩,
    State.replace_lowerC _ _ _ _, rfl, State.replace_future _ _ _ _⟩

theorem donor_bottom_supply {j : ℕ} {u : P.scheme.below (effC n j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effC n j) u) :
    ∃ S : State P C, F.Admissible j S ∧ S.lowerP j = u ∧ S.b = ⊥ ∧
      (zero : State P C).FutureEq j S := by
  obtain ⟨v, hQ, -⟩ := (F.zero_admissible j).toSource.install_donor F hu
    (selfVis_bot _) (fun _ => by simp only [min_bot_right])
  exact ⟨(zero : State P C).replace u v ⊥,
    ⟨hQ, selfVis_bot _, fun _ hm => (not_lt_bot hm).elim⟩,
    State.replace_lowerP _ _ _ _, rfl, State.replace_future _ _ _ _⟩

end Family
end
end VaughtConjecture.Knight.LowOnly
