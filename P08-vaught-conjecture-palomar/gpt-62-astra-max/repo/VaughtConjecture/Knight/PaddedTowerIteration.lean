/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PaddedTowerRows

/-! # Normalization, decoding and iteration from the rank-table base -/

@[expose] public section

namespace VaughtConjecture.Knight.PaddedTower
open Transform Value ExtOrd SourcePrefixRows SharpWitnessComposition PairedSlotComparison
open RecursiveRungRendering (grid ceiling)
noncomputable section
variable {ι X : Type*} [DecidableEq ι] [Fintype X] {A : Finset ι} {D : CellScheme A}
  {Q : ℕ → Type*} [∀ j, Fintype (Q j)]
variable {F : System D X Q} {k : ℕ}

namespace System
variable (F : System D X Q)

abbrev project (a : Q (k+2)) := F.lower (Nat.succ_pos k) a
abbrev decoder (a : Q (k+2)) := PairedSlotDecoder.decode (k+1) (PairedSlotEncoding.values (F.values a))
  (grid X (k+2)) (ceiling X (k+2))

private theorem vis {h} (hh : h ∈ grid X (k+2)) : SelfVis (k+1) h :=
  (sourceGrid_visible hh).mono (Nat.le_succ _)

theorem decode_witness (a : Q (k+2)) : Witness (gTop (k+1)) (F.decoder a) :=
  PairedSlotDecoder.decode_witness (fun _ => vis) (vis (sourceGrid_endpoint le_rfl))

theorem decode_ceiling (a : Q (k+2)) : F.decoder a (ceiling X (k+1)) = ceiling X (k+2) :=
  decode_reserved_ceiling (vis (sourceGrid_endpoint le_rfl)) (F.bounded a)

theorem decode_project (a : Q (k+2)) (x : X) : F.decoder a (F.values (F.project a) x) = F.values a x := by
  rw [project, F.restricts]
  exact PairedSlotDecoder.decode_normalize (fun _ => vis) (vis (sourceGrid_endpoint le_rfl)) (F.canonical a).2 x
end System

namespace Step
variable (P : Layer F k) (hk : 1 ≤ k) (hnext : k + 1 ≤ A.card)

abbrev render (a : Q (k+2)) (d : Cell (carrier P hnext)) := F.decoder a (source P hk hnext (F.project a) d)

theorem base_table (a : Q (k+2)) (d : Cell F.base) :
    render P hk hnext a (baseMap P hnext d) = F.table (P.birth (F.project a)) a d := by
  rw [render, source_base]
  unfold System.table
  generalize hb : P.birth (F.project a) = b
  rw [System.project, F.restricts]
  exact RelativeLadderLayer.renderWith_decode_normalized _ _ _ _ _ _ _ (F.canonical a).2
    (fun _ => System.vis) (System.vis (sourceGrid_endpoint le_rfl)) (F.decode_ceiling a) d

theorem ranks (a : Q (k+2)) (x : X) : F.ranks (P.birth (F.project a)) x =
    LadderScalarRendering.fieldRank (F.values a) x := by
  rw [P.birth_ranks, System.project, F.restricts]
  exact ReceivingCatalogueRanks.fieldRank_normalize _ _ (F.canonical a).2 x

theorem agrees (a b : Q (k+2)) {h : ExtOrd} (hh : h ∈ RecursiveRungRendering.grid X (k+2))
    (hab : Agree (F.values a) (F.values b) h) : Agree (render P hk hnext a) (render P hk hnext b) h := by
  have hv : SelfVis (k+1) (RecursiveRungRendering.ceiling X (k+2)) := System.vis (sourceGrid_endpoint le_rfl)
  have hle := CanonicalFieldLayer.grid_bound _ _ hh
  obtain ⟨e, heG, he, ha, hb, hc⟩ := exists_common_cut (fun _ => System.vis) hv hv hh hle hle
    (F.canonical a).2 (F.canonical b).2 hab
  apply Agree.decode (s := e) _ (F.decode_witness a).mono (F.decode_witness b).mono ha hb (fun _ _ => hc _)
  apply source_agreement P hk hnext _ _ heG
  simp only [System.project, F.restricts]
  exact he
end Step

section
open Step
variable (P : Layer F k) (hk : 1 ≤ k) (hnext : k + 1 ≤ A.card)

/-- A single successor works at every height, including immediately above
one. The outer grid and ceiling are always those of the incoming grade. -/
def successor : Layer F (k + 1) where
  carrier := carrier P hnext
  rows := rows P hk hnext
  consistent := consistent P hk hnext
  baseMap := baseMap P hnext
  base_mono := (SourceLayerCarrier.old_order _ _ _ _ _).comp P.base_mono
  base_index := base_index P hnext
  base_row := base_row P hk hnext
  base_respects := base_respects P hk hnext
  cases := cell_cases P hk hnext
  higher_short := higher_short P hk hnext
  selected := render P hk hnext
  birth a := P.birth (F.project a)
  birth_ranks := ranks P
  render_base := base_table P hk hnext
  lawful a := by
    apply decoded P hk hnext (Nat.le_succ _) _ (F.decode_witness a)
    change RespectsSemanticsBelow _ _ (fun d => render P hk hnext a (baseMap P hnext d.1))
    simpa only [base_table] using F.table_lawful (by omega) _ a (ranks P a)
  bound a _ := by
    apply PairedSlotDecoder.decode_le (System.vis (sourceGrid_endpoint le_rfl))
    intro v hv
    obtain ⟨x, hx⟩ := PairedSlotEncoding.mem_values.mp hv
    exact hx ▸ F.bounded a x
  supported a _ := PairedSlotDecoder.decode_supported (Nat.le_succ _) (sourceGrid_endpoint le_rfl) _
  agreement := agrees P hk hnext
  ceiling_at a i hi hik := by
    by_cases he : i = k+1
    · subst i
      refine ⟨_, (controller P hnext (F.project a)).2, ?_⟩
      exact (congrArg (F.decoder a) ((data P hk hnext).profile_diagonal _)).trans (F.decode_ceiling a)
    · obtain ⟨c, hc, hv⟩ := P.ceiling_at (F.project a) i hi (by omega)
      refine ⟨old P hnext c, (SourceLayerCarrier.cell_toCell _ _ _ _ _ _).trans hc, ?_⟩
      rw [render, source_old, hv, F.decode_ceiling]

end

variable (F) in
def build : (t : ℕ) → t + 1 ≤ A.card → Layer F (t + 1)
  | 0, _ => seed F
  | t+1, ht => successor (build t (by omega)) (Nat.succ_pos _) ht

theorem build_plan (t : ℕ) (ht : t+1 ≤ A.card) : (build F t ht).carrier.plan = D.plan := by
  induction t with
  | zero => rfl
  | succ _ ih => exact ih (by omega)

end
end VaughtConjecture.Knight.PaddedTower
