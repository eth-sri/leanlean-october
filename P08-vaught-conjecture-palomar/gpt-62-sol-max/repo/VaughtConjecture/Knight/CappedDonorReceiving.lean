/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorSelector
public import VaughtConjecture.Knight.SectionExtension
public import VaughtConjecture.Knight.CountedRecoding
public import VaughtConjecture.Knight.CappedLocalityRecoding
public import VaughtConjecture.Knight.Semantics
public import VaughtConjecture.Knight.Reduction
public import VaughtConjecture.Knight.VisibilityAlgebra
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import VaughtConjecture.Knight.FullScopeZeroExtension
public import VaughtConjecture.Knight.RowCorrectness
public import VaughtConjecture.Knight.RowReadback
public import VaughtConjecture.Knight.PositiveNormalization

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd SharpWitnessComposition AmalgamationPlan

namespace CappedDonor

/-- The present request fields at cutoff `j`. -/
def effP (nP j : ℕ) : Finset (Fin (nP + 1)) × ℕ := (Finset.univ, min j (nP + 1))

/-- The present private fields at cutoff `j`. -/
def effC (J j : ℕ) : Finset (Fin J) × ℕ := (Finset.univ, min j J)

section Cutoffs

variable {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}

theorem gradeC_le (d : Cell C.scheme) : C.scheme.grade d ≤ J :=
  (C.scheme.grade_le_card_scope d).trans (by simpa using Finset.card_le_univ (C.scheme.scope d))

theorem grade_le_effC {j : ℕ} (d : Cell C.scheme) : C.scheme.grade d ≤ (effC J j).2 ↔ C.scheme.grade d ≤ j :=
  le_min_iff.trans (and_iff_left (gradeC_le d))

end Cutoffs

namespace Ref

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  (R : Ref I nP N J P C)

include R in
theorem effP_snd_le_N (j : ℕ) : (effP nP j).2 ≤ N := (min_le_right _ _).trans R.arity_lt.le

include R in
theorem effP_snd_le_effC (j : ℕ) : (effP nP j).2 ≤ (effC J j).2 :=
  min_le_min_left j (R.arity_lt.le.trans R.N_le)

/-- Once the cap is present, its whole lower domain is present. -/
theorem capLe {j : ℕ} (hj : N ≤ j) : GradedLe (C.scheme.cell R.cap) (effC J j) := by
  rw [R.cap_cell]
  exact ⟨Finset.subset_univ _, le_min hj R.N_le⟩

/-- The cap as a present field. -/
def capC {j : ℕ} (hj : N ≤ j) : C.scheme.below (effC J j) :=
  CellScheme.below.mono (R.capLe hj) R.capL

/-- The restriction of a present private section to the cap's lower domain. -/
def lowC {j : ℕ} (hj : N ≤ j) (v : C.scheme.below (effC J j) → ExtOrd) (d : R.Low) : ExtOrd :=
  v (CellScheme.below.mono (R.capLe hj) d)

theorem lowC_respects {j : ℕ} (hj : N ≤ j) {v : C.scheme.below (effC J j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC J j) v) :
    RespectsSemanticsBelow C.rows (C.scheme.cell R.cap) (R.lowC hj v) :=
  hv.mono (R.capLe hj)

include R in
theorem selfVis_N_of_effC {j : ℕ} (hj : N ≤ j) {γ : ExtOrd} (hγ : SelfVis (effC J j).2 γ) :
    SelfVis N γ := hγ.mono (le_min hj R.N_le)

include R in
theorem selfVis_effP_of_effC {j : ℕ} {γ : ExtOrd} (hγ : SelfVis (effC J j).2 γ) :
    SelfVis (effP nP j).2 γ := hγ.mono (R.effP_snd_le_effC j)

include R in
/-- An `N`-visible cut is permissible at the request scheme's own effective grade. -/
theorem selfVis_effP_of_N (j : ℕ) {β : ExtOrd} (hβ : SelfVis N β) : SelfVis (effP nP j).2 β :=
  hβ.mono (R.effP_snd_le_N j)

/-- A face cell present at cutoff `j` as a present request field. -/
def reqFace {j : ℕ} (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j) :
    P.scheme.below (effP nP j) :=
  ⟨a.1, ⟨Finset.subset_univ _, le_min h (gradeP_le a.1)⟩⟩

/-- The private copy of a face cell present at cutoff `j` as a present private field. -/
def privFace {j : ℕ} (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j) :
    C.scheme.below (effC J j) :=
  ⟨(R.face a).1, ⟨Finset.subset_univ _, le_min ((R.face_grade a).trans_le h) (gradeC_le _)⟩⟩

/-- Every face cell is present once the cap is. -/
theorem face_grade_le_of_N {j : ℕ} (hj : N ≤ j) (a : P.scheme.below (R.A, R.KA)) :
    P.scheme.grade a.1 ≤ j := a.2.2.trans (R.KA_lt_N.le.trans hj)

/-- The present portion `(A, min KA j)` of the face at cutoff `j`. -/
theorem face_le_effP {j : ℕ} : GradedLe (R.A, min R.KA j) (effP nP j) :=
  ⟨Finset.subset_univ _, le_min (min_le_right _ _) ((min_le_left _ _).trans R.KA_le)⟩

theorem face_le_effC {j : ℕ} : GradedLe (R.A', min R.KA j) (effC J j) :=
  ⟨Finset.subset_univ _, le_min (min_le_right _ _)
    ((min_le_left _ _).trans (R.KA_lt_N.le.trans R.N_le))⟩



/-- A private section read on the present portion of the request copy of the face. -/
def faceSec {j : ℕ} (v : C.scheme.below (effC J j) → ExtOrd)
    (a : P.scheme.below (R.A, min R.KA j)) : ExtOrd :=
  v (R.privFace (R.faceLift (min_le_left _ _) a) (a.2.2.trans (min_le_right _ _)))

theorem faceSec_respects {j : ℕ} {v : C.scheme.below (effC J j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC J j) v) :
    RespectsSemanticsBelow P.rows (R.A, min R.KA j) (R.faceSec v) :=
  (R.faceAt_respects (min_le_left _ _) _).mp (hv.mono R.face_le_effC)

theorem lowC_face {j : ℕ} (hj : N ≤ j) (v : C.scheme.below (effC J j) → ExtOrd)
    (a : P.scheme.below (R.A, R.KA)) :
    R.lowC hj v (R.lowFace a) = v (R.privFace a (R.face_grade_le_of_N hj a)) := rfl

/-- A state at cutoff `j`: the present numerical sections, the gate, and the numerical
persistent shadows of every field (present or future). -/
structure State (R : Ref I nP N J P C) (j : ℕ) where
  /-- The current request section. -/
  u : P.scheme.below (effP nP j) → ExtOrd
  /-- The current private section. -/
  v : C.scheme.below (effC J j) → ExtOrd
  /-- The free grade-one gate. -/
  gate : ExtOrd
  /-- The persistent grade-one shadow of every request field. -/
  shadowP : Cell P.scheme → ExtOrd
  /-- The persistent grade-one shadow of every private field. -/
  shadowC : Cell C.scheme → ExtOrd

/-- **Admissibility** (notes32 §4): lawful sections, the literal common face on its present
portion (at every cutoff), `1`-visible gate and shadows, shadows carrying the present numerical
supports, the support guard (11), and the numerical relation (10) whenever the cap is present,
the gate is positive and the cap is positive. -/
structure Admissible {j : ℕ} (st : R.State j) : Prop where
  u_respects : RespectsSemanticsBelow P.rows (effP nP j) st.u
  v_respects : RespectsSemanticsBelow C.rows (effC J j) st.v
  face : ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j),
    st.u (R.reqFace a h) = st.v (R.privFace a h)
  gate_vis : SelfVis 1 st.gate
  shadowP_vis : ∀ d, SelfVis 1 (st.shadowP d)
  shadowC_vis : ∀ d, SelfVis 1 (st.shadowC d)
  shadowP_iff : ∀ d : P.scheme.below (effP nP j), st.shadowP d.1 ≠ ⊥ ↔ st.u d ≠ ⊥
  shadowC_iff : ∀ d : C.scheme.below (effC J j), st.shadowC d.1 ≠ ⊥ ↔ st.v d ≠ ⊥
  support : st.gate ≠ ⊥ → st.shadowC R.cap ≠ ⊥ →
    (∀ i, st.shadowC (R.ref i) ≠ ⊥) ∧ ∀ d, st.shadowP d ≠ ⊥ ↔ R.p d ≠ ⊥
  relation : ∀ (hj : N ≤ j), st.gate ≠ ⊥ → st.v (R.capC hj) ≠ ⊥ →
    ∀ d : P.scheme.below (effP nP j),
      min (st.u d) (R.cut (R.lowC hj st.v)) = R.sel (R.lowC hj st.v) d.1

/-- In an active admissible state the restricted private section is active for the selector. -/
theorem Admissible.active {j : ℕ} {st : R.State j} (hst : R.Admissible st) (hj : N ≤ j)
    (hg : st.gate ≠ ⊥) (hc : st.v (R.capC hj) ≠ ⊥) : R.Active (R.lowC hj st.v) := by
  obtain ⟨href, hsupp⟩ := hst.support hg ((hst.shadowC_iff (R.capC hj)).mpr hc)
  refine ⟨R.lowC_respects hj hst.v_respects, hc, fun i => ?_, ?_⟩
  · exact (hst.shadowC_iff (CellScheme.below.mono (R.capLe hj) (R.lowRef i))).mp (href i)
  · intro a ha
    have hu : st.u (R.reqFace a (R.face_grade_le_of_N hj a)) = ⊥ := by
      by_contra hne
      exact (hsupp a.1).mp ((hst.shadowP_iff _).mpr hne) ha
    rw [R.lowC_face, ← hst.face a (R.face_grade_le_of_N hj a), hu]

/-- **Cap receipts**: the gate and every shadow of the new state agree with the old ones below
the comparison cap `γ`. -/
def CapReceipts {j : ℕ} (γ : ExtOrd) (st st₁ : R.State j) : Prop :=
  min st₁.gate γ = min st.gate γ ∧ (∀ d, min (st₁.shadowP d) γ = min (st.shadowP d) γ) ∧
    ∀ d, min (st₁.shadowC d) γ = min (st.shadowC d) γ

theorem capReceipts_bot {j : ℕ} (st st₁ : R.State j) : R.CapReceipts ⊥ st st₁ :=
  ⟨by simp, fun _ => by simp,
    fun _ => by simp⟩

theorem capReceipts_of_eq {j : ℕ} (γ : ExtOrd) {st st₁ : R.State j} (hg : st₁.gate = st.gate)
    (hP : st₁.shadowP = st.shadowP) (hC : st₁.shadowC = st.shadowC) : R.CapReceipts γ st st₁ :=
  ⟨by tauto, fun _ => by tauto, fun _ => by tauto⟩

/-- **Persistence**: at a positive cap the gate and every shadow are retained; new lawful
sections agreeing with the old ones below the cap, with the literal face and the relation, form
an admissible state. -/
theorem admissible_persist {j : ℕ} {st : R.State j} (hst : R.Admissible st) {γ : ExtOrd}
    (hγ : γ ≠ ⊥) {u₁ : P.scheme.below (effP nP j) → ExtOrd}
    {v₁ : C.scheme.below (effC J j) → ExtOrd}
    (hu₁ : RespectsSemanticsBelow P.rows (effP nP j) u₁)
    (hv₁ : RespectsSemanticsBelow C.rows (effC J j) v₁)
    (hu : ∀ d, min (u₁ d) γ = min (st.u d) γ) (hv : ∀ d, min (v₁ d) γ = min (st.v d) γ)
    (hface : ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j),
      u₁ (R.reqFace a h) = v₁ (R.privFace a h))
    (hrel : ∀ (hj : N ≤ j), st.gate ≠ ⊥ → v₁ (R.capC hj) ≠ ⊥ →
      ∀ d : P.scheme.below (effP nP j),
        min (u₁ d) (R.cut (R.lowC hj v₁)) = R.sel (R.lowC hj v₁) d.1) :
    R.Admissible ⟨u₁, v₁, st.gate, st.shadowP, st.shadowC⟩ where
  u_respects := hu₁
  v_respects := hv₁
  face := hface
  gate_vis := hst.gate_vis
  shadowP_vis := hst.shadowP_vis
  shadowC_vis := hst.shadowC_vis
  shadowP_iff d := by
    rw [hst.shadowP_iff d]
    grind
  shadowC_iff d := by
    rw [hst.shadowC_iff d]
    grind
  support := hst.support
  relation := hrel

section Shadow

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {BJ : Finset ι × ℕ}

/-- Present shadows read the incoming section; future shadows are retained. -/
noncomputable def completeShadow (a : Cell D → ExtOrd) (p : D.below BJ → ExtOrd) : Cell D → ExtOrd :=
  CellScheme.complete a (fun d => extVisibilityReplace (p d) 1 1)

theorem completeShadow_present (a : Cell D → ExtOrd) (p : D.below BJ → ExtOrd) (d : D.below BJ) :
    completeShadow a p d.1 = extVisibilityReplace (p d) 1 1 := CellScheme.complete_present _ _ d

theorem completeShadow_visible {a : Cell D → ExtOrd} (ha : ∀ d, SelfVis 1 (a d))
    (p : D.below BJ → ExtOrd) (d : Cell D) : SelfVis 1 (completeShadow a p d) :=
  CellScheme.complete_cases (P := fun _ x => SelfVis 1 x)
    (fun c => TopSupport.selfVis_evr_self 1 (p c)) (fun c _ => ha c) d

theorem completeShadow_ne_bot (a : Cell D → ExtOrd) (p : D.below BJ → ExtOrd) (d : D.below BJ) :
    completeShadow a p d.1 ≠ ⊥ ↔ p d ≠ ⊥ := by
  rw [completeShadow_present]
  exact not_congr (evr_eq_bot_iff 1 1)

end Shadow

variable {R} in
/-- Update the sections and the gate; refresh the present shadows without touching future cells. -/
noncomputable def State.replace {j : ℕ} (st : R.State j) (u : P.scheme.below (effP nP j) → ExtOrd)
    (v : C.scheme.below (effC J j) → ExtOrd) (g : ExtOrd) : R.State j :=
  ⟨u, v, g, completeShadow st.shadowP u, completeShadow st.shadowC v⟩

/-- At the bottom cap the gate can be turned off. -/
noncomputable abbrev offState {j : ℕ} (st : R.State j) (u : P.scheme.below (effP nP j) → ExtOrd)
    (v : C.scheme.below (effC J j) → ExtOrd) : R.State j := st.replace u v ⊥

theorem admissible_off {j : ℕ} {st : R.State j} (hst : R.Admissible st)
    {u₁ : P.scheme.below (effP nP j) → ExtOrd} {v₁ : C.scheme.below (effC J j) → ExtOrd}
    (hu₁ : RespectsSemanticsBelow P.rows (effP nP j) u₁)
    (hv₁ : RespectsSemanticsBelow C.rows (effC J j) v₁)
    (hface : ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j),
      u₁ (R.reqFace a h) = v₁ (R.privFace a h)) :
    R.Admissible (R.offState st u₁ v₁) where
  u_respects := hu₁
  v_respects := hv₁
  face := hface
  gate_vis := selfVis_bot 1
  shadowP_vis := completeShadow_visible hst.shadowP_vis u₁
  shadowC_vis := completeShadow_visible hst.shadowC_vis v₁
  shadowP_iff := completeShadow_ne_bot _ u₁
  shadowC_iff := completeShadow_ne_bot _ v₁
  support h := (h rfl).elim
  relation _ h := (h rfl).elim

/-- Old `P`-bountifulness installs a lawful private face prescription into a request section at
a permissible cap, on the present portion of the face; nothing is done when that portion is
empty. -/
theorem exists_installP {j : ℕ} {u : P.scheme.below (effP nP j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effP nP j) u)
    {v₁ : C.scheme.below (effC J j) → ExtOrd} (hv₁ : RespectsSemanticsBelow C.rows (effC J j) v₁)
    {γ : ExtOrd} (hγ : SelfVis (effP nP j).2 γ)
    (hcompat : ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j),
      min (u (R.reqFace a h)) γ = min (v₁ (R.privFace a h)) γ) :
    ∃ u₁ : P.scheme.below (effP nP j) → ExtOrd, RespectsSemanticsBelow P.rows (effP nP j) u₁ ∧
      (∀ d, min (u₁ d) γ = min (u d) γ) ∧
      ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j),
        u₁ (R.reqFace a h) = v₁ (R.privFace a h) := by
  obtain ⟨u₁, hu₁, hcap, hface⟩ := P.bountiful.extend R.A_mem P.scheme.isPlan.domain_mem
    R.face_le_effP (R.faceSec_respects hv₁) hu hγ
    (fun a => hcompat (R.faceLift (min_le_left _ _) a) (a.2.2.trans (min_le_right _ _)))
  exact ⟨u₁, hu₁, hcap, fun a h => hface ⟨a.1, a.2.1, le_min a.2.2 h⟩⟩

/-- **The private fibre**: an independently lawful private prescription `v₁` agreeing with the
current private section below a permissible cap `γ` lifts to an admissible state retaining `v₁`
literally, the whole request cap vector `u ∧ γ`, the entire common face, the cap receipts of the
gate and of every shadow — and, at a positive cap, the gate and every shadow literally.  The only
extension operation is old `P`-bountifulness. -/
theorem exists_private_lift {j : ℕ} {st : R.State j} (hst : R.Admissible st)
    {v₁ : C.scheme.below (effC J j) → ExtOrd} (hv₁ : RespectsSemanticsBelow C.rows (effC J j) v₁)
    {γ : ExtOrd} (hγ : SelfVis (effC J j).2 γ) (hagree : ∀ d, min (v₁ d) γ = min (st.v d) γ) :
    ∃ st₁ : R.State j, R.Admissible st₁ ∧ st₁.v = v₁ ∧ (∀ d, min (st₁.u d) γ = min (st.u d) γ) ∧
      R.CapReceipts γ st st₁ ∧
      (γ ≠ ⊥ → st₁.gate = st.gate ∧ st₁.shadowP = st.shadowP ∧ st₁.shadowC = st.shadowC) := by
  have hcompat : ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j),
      min (st.u (R.reqFace a h)) γ = min (v₁ (R.privFace a h)) γ := by
    intro a h
    rw [hst.face a h]
    simp_all
  by_cases hbot : γ = ⊥
  · -- bottom cap: switch the gate off
    subst hbot
    obtain ⟨u₁, hu₁, hcap, hface⟩ := R.exists_installP hst.u_respects hv₁ (selfVis_bot _) hcompat
    exact ⟨R.offState st u₁ v₁, R.admissible_off hst hu₁ hv₁ hface, rfl, hcap,
      R.capReceipts_bot _ _, fun h => absurd rfl h⟩
  have hγP : SelfVis (effP nP j).2 γ := R.selfVis_effP_of_effC hγ
  have hpat := bottom_pattern_of_cap_agreement hbot hagree
  by_cases hact : ∃ hj : N ≤ j, st.gate ≠ ⊥ ∧ st.v (R.capC hj) ≠ ⊥
  · obtain ⟨hj, hg, hc⟩ := hact
    have hγN : SelfVis N γ := R.selfVis_N_of_effC hj hγ
    have hA₀ := Admissible.active R hst hj hg hc
    have hrel₀ := hst.relation hj hg hc
    have hA₁ : R.Active (R.lowC hj v₁) :=
      ⟨R.lowC_respects hj hv₁, fun h => hc ((hpat _).mp h),
        fun i h => hA₀.ref_pos i ((hpat _).mp h), fun a ha => (hpat _).mpr (hA₀.face_bot a ha)⟩
    have hVγ : (fun d => min (R.lowC hj v₁ d) γ) = fun d => min (R.lowC hj st.v d) γ :=
      funext fun d => hagree _
    have hcutγ : min (R.cut (R.lowC hj v₁)) γ = min (R.cut (R.lowC hj st.v)) γ := by
      rw [← R.cut_min hγN, ← R.cut_min hγN, hVγ]
    have hselγ : ∀ e, min (R.sel (R.lowC hj v₁) e) γ = min (R.sel (R.lowC hj st.v) e) γ := by
      intro e
      rw [← R.sel_min hγN, ← R.sel_min hγN, hVγ]
    have hcutvis : SelfVis N (R.cut (R.lowC hj v₁)) :=
      R.selfVis_cut (Active.selfVis_cap R hA₁)
    by_cases hβ : R.cut (R.lowC hj v₁) ≤ γ
    · -- the cut is at most the cap: extend from the old ambient at `γ`
      obtain ⟨u₁, hu₁, hcap, hface⟩ := R.exists_installP hst.u_respects hv₁ hγP hcompat
      refine ⟨⟨u₁, v₁, st.gate, st.shadowP, st.shadowC⟩,
        R.admissible_persist hst hbot hu₁ hv₁ hcap hagree hface ?_, rfl, hcap,
        R.capReceipts_of_eq γ rfl rfl rfl, by lia⟩
      intro hj' _ _ d
      change min (u₁ d) (R.cut (R.lowC hj v₁)) = R.sel (R.lowC hj v₁) d.1
      have hβ' : R.cut (R.lowC hj v₁) = min (R.cut (R.lowC hj st.v)) γ := by
        grind
      calc min (u₁ d) (R.cut (R.lowC hj v₁))
          = min (min (u₁ d) γ) (R.cut (R.lowC hj v₁)) := by grind
        _ = min (min (st.u d) γ) (R.cut (R.lowC hj v₁)) := by tauto
        _ = min (st.u d) (R.cut (R.lowC hj v₁)) := by grind
        _ = min (min (st.u d) (R.cut (R.lowC hj st.v))) γ := by grind
        _ = min (R.sel (R.lowC hj st.v) d.1) γ := by tauto
        _ = min (R.sel (R.lowC hj v₁) d.1) γ := by grind
        _ = R.sel (R.lowC hj v₁) d.1 := min_eq_left ((R.sel_le_cut _ d.1).trans hβ)
    · -- the cap is below the cut: extend from the lawful selector at the cut
      obtain ⟨u₁, hu₁, hcap₁, hface₁⟩ := R.exists_installP
        (u := fun d => R.sel (R.lowC hj v₁) d.1) ((Active.sel_respects R hA₁).toBelow _) hv₁
        (R.selfVis_effP_of_N j hcutvis) (by
          intro a h
          change min (R.sel (R.lowC hj v₁) a.1) (R.cut (R.lowC hj v₁)) =
            min (v₁ (R.privFace a h)) (R.cut (R.lowC hj v₁))
          rw [Active.sel_face R hA₁ a, R.lowC_face, min_assoc, min_self])
      have hrel₁ : ∀ d, min (u₁ d) (R.cut (R.lowC hj v₁)) = R.sel (R.lowC hj v₁) d.1 := by
        intro d
        rw [hcap₁ d]
        exact min_eq_left (R.sel_le_cut _ d.1)
      have hcap : ∀ d, min (u₁ d) γ = min (st.u d) γ := by
        grind
      refine ⟨⟨u₁, v₁, st.gate, st.shadowP, st.shadowC⟩,
        R.admissible_persist hst hbot hu₁ hv₁ hcap hagree hface₁ ?_, rfl, hcap,
        R.capReceipts_of_eq γ rfl rfl rfl, by simp⟩
      solve_by_elim
  · -- inactive: plain matching-face bountifulness; the relation stays vacuous
    obtain ⟨u₁, hu₁, hcap, hface⟩ := R.exists_installP hst.u_respects hv₁ hγP hcompat
    refine ⟨⟨u₁, v₁, st.gate, st.shadowP, st.shadowC⟩,
      R.admissible_persist hst hbot hu₁ hv₁ hcap hagree hface ?_, rfl, hcap,
      R.capReceipts_of_eq γ rfl rfl rfl, by lia⟩
    grind

/-- The actual pair — the donor on the request scheme and the actual private labelling — with
the gate on and the shadows the `1`-visible roundings of the actual values, at any cutoff. -/
noncomputable def actualState (j : ℕ) : R.State j where
  u d := R.p d.1
  v d := R.vact d.1
  gate := ⊤
  shadowP d := extVisibilityReplace (R.p d) 1 1
  shadowC d := extVisibilityReplace (R.vact d) 1 1

/-- The actual pair is admissible with a positive gate (notes32 §8, first step): it matches on
the face and satisfies the relation by `sel_actual`. -/
theorem actual_admissible (j : ℕ) : R.Admissible (R.actualState j) where
  u_respects := R.p_respects.toBelow _
  v_respects := R.vact_respects.toBelow _
  face a _ := (R.face_actual a).symm
  gate_vis := TopSupport.selfVis_top_ext 1
  shadowP_vis _ := TopSupport.selfVis_evr_self 1 _
  shadowC_vis _ := TopSupport.selfVis_evr_self 1 _
  shadowP_iff _ := not_congr (evr_eq_bot_iff 1 1)
  shadowC_iff _ := not_congr (evr_eq_bot_iff 1 1)
  support _ _ := ⟨fun i => by
    change extVisibilityReplace (R.vact (R.ref i)) 1 1 ≠ ⊥
    rw [R.vact_ref, ne_eq, evr_eq_bot_iff]
    simp, fun _ => not_congr (evr_eq_bot_iff 1 1)⟩
  relation _ _ _ d := by
    change min (R.p d.1) (R.cut R.vactL) = R.sel R.vactL d.1
    exact (R.sel_actual d.1).symm

end Ref

end CappedDonor

end VaughtConjecture.Knight
