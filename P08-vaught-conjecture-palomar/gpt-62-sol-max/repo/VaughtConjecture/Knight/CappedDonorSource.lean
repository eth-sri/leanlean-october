/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorFields
public import VaughtConjecture.Knight.PositiveNormalization

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd AmalgamationPlan

namespace CappedDonor

namespace Ref

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  {R : Ref I nP N J P C}

/-- A present request cell as a present field. -/
def reqCell {j : ℕ} (d : Cell P.scheme) (h : P.scheme.grade d ≤ j) : P.scheme.below (effP nP j) :=
  ⟨d, (present_req_iff j d).mpr h⟩

/-- A present private cell as a present field. -/
def privCell {j : ℕ} (d : Cell C.scheme) (h : C.scheme.grade d ≤ j) : C.scheme.below (effC J j) :=
  ⟨d, (present_priv_iff j d).mpr h⟩

/-- The single source field vector: numerical values at present fields, persistent values at
future fields. -/
noncomputable def State.sourceProfile {j : ℕ} (st : R.State j) (f : Field P C) : ExtOrd :=
  if h : f.grade ≤ j then st.numeric f h else st.persistent f

theorem State.sourceProfile_of_present {j : ℕ} (st : R.State j) {f : Field P C}
    (h : f.grade ≤ j) : st.sourceProfile f = st.numeric f h := by
  unfold State.sourceProfile; simp_all

theorem State.sourceProfile_of_future {j : ℕ} (st : R.State j) {f : Field P C}
    (h : ¬ f.grade ≤ j) : st.sourceProfile f = st.persistent f := by
  unfold State.sourceProfile; simp_all

/-- **Synchronized**: every persistent value is the `1`-visible rounding of the source vector. -/
def Synchronized {j : ℕ} (st : R.State j) : Prop :=
  ∀ f : Field P C, st.persistent f = extVisibilityReplace (st.sourceProfile f) 1 1

theorem Synchronized.shadowP {j : ℕ} {st : R.State j} (hs : Synchronized st)
    (d : P.scheme.below (effP nP j)) : st.shadowP d.1 = extVisibilityReplace (st.u d) 1 1 := by
  have h := hs (.req d.1)
  rwa [st.sourceProfile_of_present (f := .req d.1) ((present_req_iff j d.1).mp d.2)] at h

theorem Synchronized.shadowC {j : ℕ} {st : R.State j} (hs : Synchronized st)
    (d : C.scheme.below (effC J j)) : st.shadowC d.1 = extVisibilityReplace (st.v d) 1 1 := by
  have h := hs (.priv d.1)
  rwa [st.sourceProfile_of_present (f := .priv d.1) ((present_priv_iff j d.1).mp d.2)] at h

/-- Synchronization of an admissible state is the synchronization of its present cells. -/
theorem synchronized_iff {j : ℕ} {st : R.State j} (hst : R.Admissible st) :
    Synchronized st ↔
      (∀ d : P.scheme.below (effP nP j), st.shadowP d.1 = extVisibilityReplace (st.u d) 1 1) ∧
      ∀ d : C.scheme.below (effC J j), st.shadowC d.1 = extVisibilityReplace (st.v d) 1 1 := by
  refine ⟨fun hs => ⟨hs.shadowP, hs.shadowC⟩, fun ⟨hP, hC⟩ f => ?_⟩
  by_cases h : f.grade ≤ j
  · rw [st.sourceProfile_of_present h]
    cases f with
    | req d => exact hP ⟨d, (present_req_iff j d).mpr h⟩
    | priv d => exact hC ⟨d, (present_priv_iff j d).mpr h⟩
    | gate => exact hst.gate_vis.symm
  · rw [st.sourceProfile_of_future h]
    exact (hst.persistent_selfVis f).symm

/-- Recompute the present persistent fields from the numerical values; retain the future ones. -/
noncomputable abbrev resync {j : ℕ} (st : R.State j) : R.State j := st.replace st.u st.v st.gate

section Shadow

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {BJ : Finset ι × ℕ}

private theorem completeShadow_support {a : Cell D → ExtOrd} {p : D.below BJ → ExtOrd}
    (h : ∀ d, a d.1 ≠ ⊥ ↔ p d ≠ ⊥) (d : Cell D) :
    completeShadow a p d ≠ ⊥ ↔ a d ≠ ⊥ :=
  CellScheme.complete_cases (P := fun c x => x ≠ ⊥ ↔ a c ≠ ⊥)
    (fun c => (not_congr (evr_eq_bot_iff 1 1)).trans (h c).symm) (fun _ _ => Iff.rfl) d

private theorem completeShadow_cap {a b : Cell D → ExtOrd} {p q : D.below BJ → ExtOrd}
    {γ : ExtOrd} (hγ : Nonempty (D.below BJ) → SelfVis 1 γ)
    (ha : ∀ d, a d.1 = extVisibilityReplace (p d) 1 1)
    (hpq : ∀ d, min (q d) γ = min (p d) γ)
    (hab : ∀ d, min (b d) γ = min (a d) γ) (d : Cell D) :
    min (completeShadow b q d) γ = min (a d) γ := by
  apply CellScheme.complete_cases (P := fun c x => min x γ = min (a c) γ) _ (fun c _ => hab c) d
  intro c
  have hv := hγ ⟨c⟩
  simp only [ha c, ← evr_min_of_selfVis hv le_rfl le_rfl, hpq c]

end Shadow

/-- Resynchronization preserves admissibility. -/
theorem Admissible.resync {j : ℕ} {st : R.State j} (hst : R.Admissible st) :
    R.Admissible (resync st) where
  u_respects := hst.u_respects
  v_respects := hst.v_respects
  face := hst.face
  gate_vis := hst.gate_vis
  shadowP_vis := completeShadow_visible hst.shadowP_vis st.u
  shadowC_vis := completeShadow_visible hst.shadowC_vis st.v
  shadowP_iff := completeShadow_ne_bot _ _
  shadowC_iff := completeShadow_ne_bot _ _
  support hg hc := by
    have hp := completeShadow_support hst.shadowP_iff
    have hv := completeShadow_support hst.shadowC_iff
    obtain ⟨href, hsupp⟩ := hst.support hg ((hv R.cap).mp hc)
    exact ⟨fun i => (hv _).mpr (href i), fun d => (hp d).trans (hsupp d)⟩
  relation := hst.relation

/-- The resynchronized state of an admissible state is synchronized. -/
theorem resync_synchronized {j : ℕ} {st : R.State j} (hst : R.Admissible st) :
    Synchronized (resync st) :=
  (synchronized_iff hst.resync).mpr ⟨completeShadow_present _ _, completeShadow_present _ _⟩

include R in
/-- The comparison cap of a nonempty cutoff is `1`-visible. -/
theorem selfVis_one_of_effC {j : ℕ} (hj : 1 ≤ j) {γ : ExtOrd} (hγ : SelfVis (effC J j).2 γ) :
    SelfVis 1 γ := by
  have hJ : 1 ≤ J := (Nat.succ_pos _).trans_le (R.arity_lt.le.trans R.N_le)
  exact hγ.mono (le_min hj hJ)

include R in
/-- **Cap receipts survive resynchronization**: if the numerical fields of a new admissible state
agree below a permissible cap with those of a synchronized state, and the persistent fields carry
receipts, then the resynchronized new state carries receipts for every persistent field. -/
theorem resync_capReceipts {j : ℕ} {st st₁ : R.State j} (hs : Synchronized st) {γ : ExtOrd}
    (hγ : SelfVis (effC J j).2 γ) (hu : ∀ d, min (st₁.u d) γ = min (st.u d) γ)
    (hv : ∀ d, min (st₁.v d) γ = min (st.v d) γ) (hrec : R.CapReceipts γ st st₁) :
    R.CapReceipts γ st (resync st₁) := by
  obtain ⟨hg, hP, hC⟩ := hrec
  refine ⟨hg, completeShadow_cap (fun ⟨d⟩ => ?_) hs.shadowP hu hP,
    completeShadow_cap (fun ⟨d⟩ => ?_) hs.shadowC hv hC⟩
  · exact selfVis_one_of_effC (R := R) ((P.scheme.grade_pos d.1).trans_le
      ((present_req_iff j d.1).mp d.2)) hγ
  · exact hγ.mono ((C.scheme.grade_pos d.1).trans_le d.2.2)

/-- Apply a scalar map to every field of a state. -/
def mapState {j : ℕ} (σ : ExtOrd → ExtOrd) (st : R.State j) : R.State j where
  u d := σ (st.u d)
  v d := σ (st.v d)
  gate := σ st.gate
  shadowP d := σ (st.shadowP d)
  shadowC d := σ (st.shadowC d)

theorem sourceProfile_map (σ : ExtOrd → ExtOrd) {j : ℕ} (st : R.State j) (f : Field P C) :
    (mapState σ st).sourceProfile f = σ (st.sourceProfile f) := by
  by_cases h : f.grade ≤ j
  · rw [State.sourceProfile_of_present _ h, State.sourceProfile_of_present _ h]
    cases f <;> rfl
  · rw [State.sourceProfile_of_future _ h, State.sourceProfile_of_future _ h]
    cases f <;> rfl

section Map

variable {K : ℕ} {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop K) σ)

include hσ

theorem map_comm {k : ℕ} (hk : k ≤ K) (x : ExtOrd) {i : ℕ} (hi : i ≤ k) :
    σ (extVisibilityReplace x k i) = extVisibilityReplace (σ x) k i :=
  hσ.comm x hk hi

theorem selfVis_map {k : ℕ} (hk : k ≤ K) {x : ExtOrd} (h : SelfVis k x) : SelfVis k (σ x) := by grind [extVisibilityReplace, map_comm]

theorem map_ne_bot_iff (hbot : ∀ x, σ x = ⊥ → x = ⊥) (x : ExtOrd) : σ x ≠ ⊥ ↔ x ≠ ⊥ :=
  not_congr ⟨hbot x, fun h => by rw [h, hσ.bot]⟩

theorem map_sup (f : I → ExtOrd) :
    σ (Finset.univ.sup f) = Finset.univ.sup fun i => σ (f i) :=
  Finset.apply_sup_eq_sup_comp σ (fun _ _ => hσ.mono.map_max) hσ.bot

/-- The cut commutes with a normalized witness through `N`. -/
theorem cut_map (hN : N ≤ K) (v : R.Low → ExtOrd) : R.cut (fun d => σ (v d)) = σ (R.cut v) := by
  unfold cut
  rw [hσ.mono.map_min, map_sup hσ]
  grind [map_comm]

/-- The selector commutes with a normalized witness through `N`. -/
theorem sel_map (hN : N ≤ K) (v : R.Low → ExtOrd) (d : Cell P.scheme) :
    R.sel (fun d => σ (v d)) d = σ (R.sel v d) := by
  by_cases h : R.p d ≠ ⊥ ∧ R.p d ≠ ⊤
  · rw [R.sel_of_proper h, R.sel_of_proper h, cut_map hσ hN, hσ.mono.map_min,
      map_comm hσ hN _ (R.poff_lt d h).le]
  by_cases hb : R.p d = ⊥
  · rw [R.sel_of_bot hb, R.sel_of_bot hb, hσ.bot]
  · have ht := not_not.mp fun ht => h ⟨hb, ht⟩
    rw [R.sel_of_top ht, R.sel_of_top ht, cut_map hσ hN]

/-- **Admissibility is preserved by every bottom-reflecting normalized witness through the grades
currently present** (and grade one, for the gate and the persistent fields): lawfulness by
`RespectsSemanticsBelow.map_bottom_reflecting`, visibility and supports by commutation and bottom reflection,
the relation by `cut_map`/`sel_map` — which needs commutation through `N` only when the cap is
present, i.e. when `N` is among the present grades. -/
theorem Admissible.map {j : ℕ} (hK : (effC J j).2 ≤ K) (h1 : 1 ≤ K)
    (hbot : ∀ x, σ x = ⊥ → x = ⊥) {st : R.State j} (hst : R.Admissible st) :
    R.Admissible (mapState σ st) where
  u_respects := RespectsSemanticsBelow.map_bottom_reflecting hst.u_respects
    (fun d => d.2.2.trans ((R.effP_snd_le_effC j).trans hK)) hσ hbot
  v_respects := RespectsSemanticsBelow.map_bottom_reflecting hst.v_respects (fun d => d.2.2.trans hK) hσ hbot
  face a h := congrArg σ (hst.face a h)
  gate_vis := selfVis_map hσ h1 hst.gate_vis
  shadowP_vis d := selfVis_map hσ h1 (hst.shadowP_vis d)
  shadowC_vis d := selfVis_map hσ h1 (hst.shadowC_vis d)
  shadowP_iff d := (map_ne_bot_iff hσ hbot _).trans ((hst.shadowP_iff d).trans
    (map_ne_bot_iff hσ hbot _).symm)
  shadowC_iff d := (map_ne_bot_iff hσ hbot _).trans ((hst.shadowC_iff d).trans
    (map_ne_bot_iff hσ hbot _).symm)
  support hg hc := by
    obtain ⟨href, hsupp⟩ := hst.support ((map_ne_bot_iff hσ hbot _).mp hg)
      ((map_ne_bot_iff hσ hbot _).mp hc)
    exact ⟨by tauto,
      fun d => (map_ne_bot_iff hσ hbot _).trans (hsupp d)⟩
  relation hj hg hc d := by
    have hN : N ≤ K := (le_min hj R.N_le).trans hK
    have h := hst.relation hj ((map_ne_bot_iff hσ hbot _).mp hg)
      ((map_ne_bot_iff hσ hbot _).mp hc) d
    change min (σ (st.u d)) (R.cut (fun e => σ (R.lowC hj st.v e))) =
      R.sel (fun e => σ (R.lowC hj st.v e)) d.1
    rw [cut_map hσ hN, sel_map hσ hN, ← hσ.mono.map_min, h]

/-- Synchronization is preserved by every normalized witness through a grade at least `1`. -/
theorem Synchronized.map (hK : 1 ≤ K) {j : ℕ} {st : R.State j} (hs : Synchronized st) :
    Synchronized (mapState σ st) := by
  intro f
  rw [sourceProfile_map σ, ← map_comm hσ hK _ le_rfl, ← hs f]
  cases f <;> rfl

end Map

end Ref

end CappedDonor

end VaughtConjecture.Knight
