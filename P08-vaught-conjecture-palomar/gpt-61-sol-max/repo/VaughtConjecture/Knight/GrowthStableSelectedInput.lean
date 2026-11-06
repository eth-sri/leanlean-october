/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.GrowthFilteredRoot
import VaughtConjecture.Knight.StableLiftCore
import VaughtConjecture.Knight.ReceivingTemplate

/-! # Stable-root compatibility for selected growth donors

The donor extends the stable root, not the actual root. The stable labelling
of an actual private cover supplies a lawful compatible complete vector. This
uses the original model only, not modelhood of its stable lift. Admission is
proved below activation; calibrated request correctness above activation is
deliberately not assumed or asserted here.

The proper-field bound is at the next block. A proper stable value of an
actual top prevents replacing that bound by the original stage bound.
-/

namespace VaughtConjecture.Knight.GrowthStableSelectedInput
open TypeTower StageType KnightRealization Value   

open SharpWitnessComposition
noncomputable section
universe w
variable {M : Type w} {α : LimitStage} {W : KnightRealization α M}
  (hM : W.IsModel) {n J : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
  (hp : W.eval t = some p) {u : Fin J ↪ M} {C : S α.1 J}
  (hC : W.eval u = some C) {f : Fin n ↪ Fin J} (hfu : f.trans u = t)
  (hf : typeMap f C = some p)
  {q : S α.nextBlock.1 (n + 1)} (hq : IsCoface (stableLiftType hM hp) q)

include hfu in
/-- Stable face compatibility follows from consistency of the original model;
no occurrence of the chosen donor is assumed. -/
theorem stable_face :
    typeMap f (stableLiftType hM hC) = some (stableLiftType hM hp) := by
  have h := stableLift_consistent hM u (stableLiftType hM hC) f
    (stableLift_eval_some hM hC)
  rw [hfu, stableLift_eval_some hM hp] at h
  exact h.symm

local notation "stableValue₀" => W.stableValue u C

/-- All fields are stored, including those beyond a later physical cutoff. -/
def state : Growth.State C.scheme.scheme q.scheme.scheme :=
  ⟨stableValue₀, q.label⟩

include hf hq in
/-- Both ordered schemes have the literal original root scheme. Only their
labellings have moved to the next block. -/
theorem common_faces :
    ∃ hvP
      hvC,
      q.scheme.restrictFace Fin.castSuccEmb hvP = p.scheme ∧
      C.scheme.restrictFace f hvC = p.scheme := by
  refine ⟨visible_of_typeMap_eq_some hq, visible_of_typeMap_eq_some hf, ?_, ?_⟩
  · exact congrArg scheme (restrictFace_eq_of_typeMap_eq_some hq)
  · exact congrArg scheme (restrictFace_eq_of_typeMap_eq_some hf)

include hM hC in
/-- Stable private labels have the actual private bottom pattern, even where
they do not have the actual private values. -/
theorem private_bottom d :
    stableValue₀ d = ⊥ ↔ C.label d = ⊥ := by
  have h := truncExt_stableValue hM.consistent hM.covering hC d
  rw [← h]
  exact truncExt_eq_bot_iff.symm

include hM hC in
/-- Cleaning uses the actual top cap; decoding uses its independently lawful
stable labelling. Consequently a proper stable cap is no obstruction to
constructing the lawful cleaned source and its bounded reading chart. -/
theorem exists_cleaned_source_chart c (hc : C.label c = ⊤) :
    ∃ e ,
      Semantics.RowLawful C.scheme.rows c e ∧
      (∀ d, e d = ⊥ ↔ C.label d.1 = ⊥) ∧
      (∀ d, C.label d.1 ≠ ⊥ → e d = C.scheme.rows.E c d) ∧
      ∃ θ , BoundedMap (C.scheme.scheme.grade c) θ ∧
        (∀ x, θ x ≤ stableValue₀ c) ∧
        ∀ d, θ (e d) = min (stableValue₀ d.1) (stableValue₀ c) := by
  have hl := stableLiftRespects hM hC
  have hvis : SelfVis (C.scheme.scheme.grade c) (stableValue₀ c) :=
    (hl.orderly c).symm
  obtain ⟨τ, hbot, hmono, hread, hcomm, -⟩ := exists_exact_capped_shifter
    (D := C.scheme.scheme.belowCell c)
    (grade := fun d => C.scheme.scheme.grade d.1) (p := fun d => stableValue₀ d.1)
    (c := ⟨c, GradedLe.refl _⟩) (fun d => d.2.2) hvis (hl.locality c)
  have hcb : stableValue₀ c ≠ ⊥ := by
    intro h
    exact top_ne_bot (hc.symm.trans ((private_bottom hM hC c).mp h))
  have hbottom (d : C.scheme.scheme.belowCell c) :
      τ (C.scheme.rows.E c d) = ⊥ ↔ stableValue₀ d.1 = ⊥ := by
    grind
  let e  :=
    fun d => if C.label d.1 = ⊥ then ⊥ else C.scheme.rows.E c d
  have he : Semantics.RowLawful C.scheme.rows c e := by
    have h := cleaned_respects_of_bottom_agreement (C.scheme.consistent c) (hl.toBelow _)
      (fun d => d.2.2) ⟨hbot, hmono, hcomm⟩ hbottom
    simpa only [private_bottom hM hC] using h
  have heq (d) (hd : C.label d.1 ≠ ⊥) : e d = C.scheme.rows.E c d := ite_eq_right hd
  have heb d : e d = ⊥ ↔ C.label d.1 = ⊥ := by
    grind [private_bottom]
  refine ⟨e, he, heb, heq, fun x => min (τ x) (stableValue₀ c),
    ⟨?_, ?_, ?_⟩, fun x => min_le_right _ _, ?_⟩
  · rw [hbot, min_eq_left bot_le]
  · intro x y hxy
    exact min_le_min_right _ (hmono hxy)
  · intro x k i hk hi
    rw [hcomm x k i hk hi, evr_min_of_selfVis hvis hk hi]
  · grind [private_bottom]


