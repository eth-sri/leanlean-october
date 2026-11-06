/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthFilteredRoot
public import VaughtConjecture.Knight.StableLiftCore
public import VaughtConjecture.Knight.ReceivingTemplate

/-! # Stable-root compatibility for selected growth donors

The donor extends the stable root, not the actual root. The stable labelling
of an actual private cover supplies a lawful compatible complete vector. This
uses the original model only, not modelhood of its stable lift. Admission is
proved below activation; calibrated request correctness above activation is
deliberately not assumed or asserted here.

The proper-field bound is at the next block. A proper stable value of an
actual top prevents replacing that bound by the original stage bound.
-/

@[expose] public section

namespace VaughtConjecture.Knight.GrowthStableSelectedInput
open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan CappedDonor
open CellScheme.restrictFace
open SharpWitnessComposition
noncomputable section
universe w
variable {M : Type w} {α : LimitStage} {W : KnightRealization α M}
  (hM : W.IsModel) {n J : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
  (hp : W.eval t = some p) {u : Fin J ↪ M} {C : S α.1 J}
  (hC : W.eval u = some C) {f : Fin n ↪ Fin J} (hfu : f.trans u = t)
  (hf : typeMap f C = some p)
  {q : S α.nextBlock.1 (n + 1)} (hq : IsCoface (stableLiftType hM t p hp) q)

include hfu in
/-- Stable face compatibility follows from consistency of the original model;
no occurrence of the chosen donor is assumed. -/
theorem stable_face :
    typeMap f (stableLiftType hM u C hC) = some (stableLiftType hM t p hp) := by
  have h := stableLift_consistent hM u (stableLiftType hM u C hC) f
    (stableLift_eval_some hM hC)
  rw [hfu, stableLift_eval_some hM hp] at h
  exact h.symm

/-- All fields are stored, including those beyond a later physical cutoff. -/
def state : Growth.State C.scheme.scheme q.scheme.scheme :=
  ⟨W.stableValue u C, q.label⟩

include hf hq in
/-- Both ordered schemes have the literal original root scheme. Only their
labellings have moved to the next block. -/
theorem common_faces :
    ∃ (hvP : Finset.univ.image Fin.castSuccEmb ∈ q.scheme.scheme.plan)
      (hvC : Finset.univ.image f ∈ C.scheme.scheme.plan),
      q.scheme.restrictFace Fin.castSuccEmb hvP = p.scheme ∧
      C.scheme.restrictFace f hvC = p.scheme := by
  refine ⟨visible_of_typeMap_eq_some hq, visible_of_typeMap_eq_some hf, ?_, ?_⟩
  · exact congrArg scheme (restrictFace_eq_of_typeMap_eq_some hq)
  · exact congrArg scheme (restrictFace_eq_of_typeMap_eq_some hf)

include hM hC in
/-- Stable private labels have the actual private bottom pattern, even where
they do not have the actual private values. -/
theorem private_bottom (d : Cell C.scheme.scheme) :
    W.stableValue u C d = ⊥ ↔ C.label d = ⊥ := by
  have h := truncExt_stableValue hM.consistent hM.covering hC d
  rw [← h]
  exact truncExt_eq_bot_iff.symm

include hM hC in
/-- Cleaning uses the actual top cap; decoding uses its independently lawful
stable labelling. Consequently a proper stable cap is no obstruction to
constructing the lawful cleaned source and its bounded reading chart. -/
theorem exists_cleaned_source_chart (c : Cell C.scheme.scheme) (hc : C.label c = ⊤) :
    ∃ e : C.scheme.scheme.below (C.scheme.scheme.cell c) → ExtOrd,
      RespectsSemanticsBelow C.scheme.rows (C.scheme.scheme.cell c) e ∧
      (∀ d, e d = ⊥ ↔ C.label d.1 = ⊥) ∧
      (∀ d, C.label d.1 ≠ ⊥ → e d = C.scheme.rows.E c d) ∧
      ∃ θ : ExtOrd → ExtOrd, BoundedMap (C.scheme.scheme.grade c) θ ∧
        (∀ x, θ x ≤ W.stableValue u C c) ∧
        ∀ d, θ (e d) = min (W.stableValue u C d.1) (W.stableValue u C c) := by
  have hl := stableLiftRespects hM hC
  have hvis : SelfVis (C.scheme.scheme.grade c) (W.stableValue u C c) :=
    (hl.orderly c).symm
  obtain ⟨τ, hbot, hmono, hread, hcomm, -⟩ := exists_exact_capped_shifter
    (D := C.scheme.scheme.below (C.scheme.scheme.cell c))
    (grade := fun d => C.scheme.scheme.grade d.1) (p := fun d => W.stableValue u C d.1)
    (c := ⟨c, GradedLe.refl _⟩) (fun d => d.2.2) hvis (hl.locality c)
  have hcb : W.stableValue u C c ≠ ⊥ := by
    intro h
    exact top_ne_bot (hc.symm.trans ((private_bottom hM hC c).mp h))
  have hbottom (d : C.scheme.scheme.below (C.scheme.scheme.cell c)) :
      τ (C.scheme.rows.E c d) = ⊥ ↔ W.stableValue u C d.1 = ⊥ := by
    rw [hread d]
    exact ⟨fun h => (min_eq_bot.mp h).resolve_right hcb,
      fun h => by rw [h, min_eq_left bot_le]⟩
  let e : C.scheme.scheme.below (C.scheme.scheme.cell c) → ExtOrd :=
    fun d => if C.label d.1 = ⊥ then ⊥ else C.scheme.rows.E c d
  have he : RespectsSemanticsBelow C.scheme.rows (C.scheme.scheme.cell c) e := by
    have h := cleaned_respects_of_bottom_agreement (C.scheme.consistent c) (hl.toBelow _)
      (fun d => d.2.2) ⟨hbot, hmono, hcomm⟩ hbottom
    simpa only [private_bottom hM hC] using h
  have heq (d) (hd : C.label d.1 ≠ ⊥) : e d = C.scheme.rows.E c d := ite_eq_right hd
  have heb (d) : e d = ⊥ ↔ C.label d.1 = ⊥ := by
    by_cases hd : C.label d.1 = ⊥
    · simp only [e, hd, ite_true]
    · rw [heq d hd]
      exact ⟨fun h => (hd ((private_bottom hM hC d.1).mp
        ((hbottom d).mp (by rw [h, hbot])))).elim, fun h => (hd h).elim⟩
  refine ⟨e, he, heb, heq, fun x => min (τ x) (W.stableValue u C c),
    ⟨?_, ?_, ?_⟩, fun x => min_le_right _ _, ?_⟩
  · rw [hbot, min_eq_left bot_le]
  · intro x y hxy
    exact min_le_min_right _ (hmono hxy)
  · intro x k i hk hi
    rw [hcomm x k i hk hi, evr_min_of_selfVis hvis hk hi]
  · intro d
    change min (τ (e d)) (W.stableValue u C c) =
      min (W.stableValue u C d.1) (W.stableValue u C c)
    by_cases hd : C.label d.1 = ⊥
    · rw [(heb d).mpr hd, hbot, (private_bottom hM hC d.1).mpr hd]
    · rw [heq d hd, hread d, min_assoc, min_self]

end
end VaughtConjecture.Knight.GrowthStableSelectedInput
