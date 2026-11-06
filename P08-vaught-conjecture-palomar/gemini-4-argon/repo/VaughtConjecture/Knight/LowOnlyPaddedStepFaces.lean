/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedStepDecode
public import VaughtConjecture.Knight.LowOnlyPaddedLiftingReady

/-! # Literal original faces through the padded tower

Each original face retains its entire old domain and rows. Lower target-grade
lifting transports through the actual installation, without a global grade
bound on retained proper owners.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.LowOnlyPaddedStepFaces
open Transform Value ExtOrd CappedDonor LowOnly CanonicalPairedInverse LowOnlyPaddedContract LowOnlyPaddedStepRows LowOnlyOrderedLadder
open LowOnlyPaddedDecode (grid_fixed_below)

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  {hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I F hroot hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

/-- Literal faces survive the entire installed tower, not just its field readings. -/
def layerFace {T : Finset ι} {E : CellScheme T} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows I.rows) (hT : ¬ A ⊆ T) :
    ExactSemanticFace oldRows P.rows := by
  let L := SeparatedLayerFace.face I.boundary
    (RelativeLadderLayer.Point (X := Field I.left I.right) (Q := F.Anchor 1))
    1 Nat.one_pos (by omega) (RelativeLadderLayer.separated I.boundary
      (LowOnlyOrderedLadder.proper I hB hC)) I.rows (baseRows I F hroot hA hB hC)
    (RelativeLadderLayer.inherited_row I.boundary I.rows (by omega)
      (field I) (F.fields 1) (LowOnlyOrderedLadder.proper I hB hC)) G hT
  exact {
    map := L.map.trans ⟨P.baseMap, P.base_mono.injective⟩
    index := fun d => (P.base_index _).trans (L.index d)
    exhaustive := fun z hz => by
      rcases P.cases z with ⟨d, rfl⟩ | ⟨hs, _, _⟩
      · obtain ⟨c, rfl⟩ := L.exhaustive d (by
          change (P.carrier.cell (P.baseMap d)).1 ⊆ T at hz
          rwa [P.base_index] at hz)
        exact ⟨c, rfl⟩
      · exact False.elim (hT (hs ▸ hz))
    row := fun c d => (P.base_row (L.map c)
      ⟨L.map d.1, by rw [L.index, L.index]; exact d.2⟩).trans (L.row c d) }

def face {T : Finset ι} {E : CellScheme T} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows I.rows) (hT : ¬ A ⊆ T) :
    ExactSemanticFace oldRows (rows P hk hnext) :=
  SeparatedLayerFace.face P.carrier (F.Anchor (k + 1)) (k + 1) (Nat.succ_pos k) hnext
    (P.separated I F hroot hA hB hC (by omega)) P.rows (rows P hk hnext)
    (inherited_row P hk hnext) (layerFace P G hT) hT

def privateFace : ExactSemanticFace I.rightRows (rows P hk hnext) :=
  face P hk hnext I.rightFace hC.not_ge

def donorFace : ExactSemanticFace I.leftRows (rows P hk hnext) :=
  face P hk hnext I.leftFace hB.not_ge

theorem lower_lifting (hprev : TargetGradeLifting.Through P.rows k) :
    TargetGradeLifting.Through (rows P hk hnext) k :=
  TargetGradeLifting.through_separated P.rows (F.Anchor (k + 1)) (k + 1)
    (Nat.succ_pos k) hnext (P.separated I F hroot hA hB hC (by omega))
    (rows P hk hnext) (inherited_row P hk hnext) (Nat.lt_succ_self k) hprev

open LowOnlyPaddedFaces (fullEquiv full_respects_iff) in
open AmalgamationPlan in
theorem active_step_lift (hplan : P.carrier.plan = R) (hprev : TargetGradeLifting.Through P.rows k)
    {D : Finset ι} (hD : D ⊂ A) (hDR : D ∈ R) {S : SemScheme n} {place : Fin n ↪ ι}
    (himg : Finset.image place Finset.univ = D)
    (Fface : ExactSemanticFace (PointImageSemantics.rows S.scheme place himg S.rows)
      (rows P hk hnext))
    {faceAt : S.scheme.below (effC n (k + 1)) → (carrier P hnext).below (A, k + 1)}
    {p : S.scheme.below (effC n (k + 1)) → ExtOrd}
    {q : (carrier P hnext).below (A, k + 1) → ExtOrd}
    (hp : RespectsSemanticsBelow S.rows (effC n (k + 1)) p)
    (hq : RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) q)
    {γ : ExtOrd} (hpos : ⊥ < γ)
    (hactive : ∃ d, S.scheme.grade d.1 = k + 1 ∧ γ < p d)
    (hcapped : ∀ c : S.scheme.below (effC n (k + 1)),
      S.scheme.cell c.1 = effC n (k + 1) → S.scheme.grade c.1 = k + 1 → γ < p c →
      ∃ u, RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) u ∧
        (∀ d, u (faceAt d) = min (p d) (p c)) ∧
        (∀ d, min (u d) γ = min (q d) γ) ∧ (∀ d, u d ≤ p c))
    (hid : ∀ d, CellScheme.below.mono
      (show GradedLe (D, k + 1) (A, k + 1) from ⟨hD.subset, le_rfl⟩)
      (fullEquiv S place himg Fface (k + 1) d) = faceAt d :=
      by intro; apply Subtype.ext; rfl) :
    ∃ r, RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) r ∧
      (∀ d, r (faceAt d) = p d) ∧ ∀ d, min (r d) γ = min (q d) γ := by
  obtain ⟨d, hd, hpd⟩ := hactive
  have hn : k + 1 ≤ n := by simpa only [hd] using gradeC_le d.1
  obtain ⟨c₀, hc₀⟩ := S.complete (effC n (k + 1)) (CappedDonor.effC_mem (by omega) (by omega))
  obtain ⟨c, hc, hmax⟩ := AmbientGradeCharts.exists_maximizer hp
    ⟨⟨c₀, by rw [hc₀]; exact GradedLe.refl _⟩, by simpa only [effC, min_eq_left hn] using hc₀⟩
  have hg : S.scheme.grade c.1 = k + 1 := congrArg Prod.snd hc
  have hpc : γ < p c := hpd.trans_le (hmax d hd)
  obtain ⟨u, hu, hread, hcap, _⟩ :=
    hcapped c (by simpa only [effC, min_eq_left hn] using hc) hg hpc
  let e := fullEquiv S place himg Fface (k + 1)
  let p' := p ∘ e.symm
  have hp' : RespectsSemanticsBelow (rows P hk hnext) (D, k + 1) p' := by
    apply (full_respects_iff S place himg Fface (k + 1) p').mpr
    simpa only [p', e, Function.comp_def, Equiv.symm_apply_apply] using hp
  have hcard : D.card = n := by
    rw [← himg, Finset.card_image_of_injective _ place.injective]
    simp only [Finset.card_univ, Fintype.card_fin]
  have hDmem : (D, k) ∈ Plan.gradedPlan (carrier P hnext).plan := by
    change (D, k) ∈ Plan.gradedPlan P.carrier.plan; rw [hplan]
    exact Plan.mem_gradedPlan.mpr ⟨hDR, by omega, by change k ≤ D.card; omega⟩
  have hAmem : (A, k) ∈ Plan.gradedPlan (carrier P hnext).plan :=
    Plan.mem_gradedPlan.mpr
      ⟨(carrier P hnext).isPlan.domain_mem, by omega, by change k ≤ A.card; omega⟩
  obtain ⟨r, hr, hrc, hrr⟩ := TargetGradeLifting.restore (rows P hk hnext)
    (lower_lifting P hk hnext hprev) hDmem hAmem hD.subset hp' hu
    (by simpa only [hg] using (hp.orderly c).symm) hpc.le
    (fun d => by
      obtain ⟨x, rfl⟩ := e.surjective d
      simpa only [p', e, Function.comp_apply, Equiv.symm_apply_apply, hid] using hread x)
    (fun d hd' => by
      obtain ⟨x, rfl⟩ := e.surjective d
      simpa only [p', Function.comp_apply, Equiv.symm_apply_apply] using
        hmax x ((congrArg Prod.snd (Fface.index x.1)).symm.trans hd'))
    hcap
  exact ⟨r, hr, fun d => by
    simpa only [p', e, Function.comp_apply, Equiv.symm_apply_apply, hid] using hrr (e d), hrc⟩
