/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorContext
public import VaughtConjecture.Knight.GrowthFilteredRoot

@[expose] public section

namespace VaughtConjecture.Knight

open Value ExtOrd AmalgamationPlan CellScheme.restrictFace TypeTower StageType

namespace Requests

variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
  {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}

/-- All labels are requested, classified as bottom, a block and offset, or high. -/
noncomputable abbrev ofLabels (c : Cell DA) {N R : ℕ} (hR : R < N)
    (a : DA.below (DA.cell c)) (ref : Ordinal.{0} → DA.below (DA.cell c))
    (p : Cell DQ → ExtOrd) : Requests DA DQ where
  C := c
  N := N
  R := R
  R_lt_N := hR
  Z := {d | p d = ⊥}
  F := {d | p d ≠ ⊥ ∧ p d ≠ ⊤}
  T := {d | p d = ⊤}
  ρ d := ref (limitPart (ordOf (p d)))
  off d := finitePart (ordOf (p d))
  a := a

variable {c : Cell DA} {N R : ℕ} {hR : R < N}
  {a : DA.below (DA.cell c)} {ref : Ordinal.{0} → DA.below (DA.cell c)}
  {p : Cell DQ → ExtOrd}

lemma ofLabels_cover {X : Prop} (d : Cell DQ) :
    d ∈ (ofLabels c hR a ref p).Z ∨ d ∈ (ofLabels c hR a ref p).F ∨
    d ∈ (ofLabels c hR a ref p).T ∨ X := by
  change p d = ⊥ ∨ (p d ≠ ⊥ ∧ p d ≠ ⊤) ∨ p d = ⊤ ∨ X
  tauto

lemma ofLabels_field {d : Cell DQ} (hd : d ∈ (ofLabels c hR a ref p).F) :
    ∃ β, p d = ofOrd β ∧ (ofLabels c hR a ref p).ρ d = ref (limitPart β) ∧
      (ofLabels c hR a ref p).off d = finitePart β := by
  change p d ≠ ⊥ ∧ p d ≠ ⊤ at hd
  rcases ExtOrd.cases (p d) with hb | ht | ⟨β, hβ⟩
  · tauto
  · tauto
  exact ⟨β, hβ, by simp only [ofLabels, hβ, ordOf_ofOrd], by simp only [ofLabels, hβ, ordOf_ofOrd]⟩

lemma ofLabels_tOf (w : Cell DA → ExtOrd)
    (href : ∀ d β, p d = ofOrd β → ∃ j < N, w (ref (limitPart β)).1 = ofOrd (limitPart β + j))
    {d : Cell DQ} (hd : d ∈ (ofLabels c hR a ref p).F) :
    (ofLabels c hR a ref p).tOf ((ofLabels c hR a ref p).sec w) d = min (p d) (w c) := by
  obtain ⟨β, hβ, -, -⟩ := ofLabels_field hd
  obtain ⟨j, hj, he⟩ := href d β hβ
  change min (extVisibilityReplace (w (ref (limitPart (ordOf (p d)))).1) N
    (finitePart (ordOf (p d)))) (w c) = _
  rw [hβ, ordOf_ofOrd, he,
    extVisibilityReplace_of_finitePart_lt (finitePart_limitPart_add_nat _ _ ▸ hj),
    limitPart_limitPart_add_nat, limitPart_add_finitePart]

lemma ofLabels_correct (w : Cell DA → ExtOrd)
    (href : ∀ d β, p d = ofOrd β → ∃ j < N, w (ref (limitPart β)).1 = ofOrd (limitPart β + j)) :
    (ofLabels c hR a ref p).Correct ((ofLabels c hR a ref p).sec w) p := by
  refine ⟨fun d hd => ?_, fun d hd => (ofLabels_tOf w href hd).symm, fun d hd => ?_⟩
  · change p d = ⊥ at hd
    simp [hd]
  · change p d = ⊤ at hd
    simpa [hd, dOf] using min_le_right (extVisibilityReplace (w a.1) N R) (w c)

end Requests

namespace CappedDonor

variable {α : LimitStage} {n : ℕ} {q : S α.1 (n + 1)}

lemma block_of_label {d : Cell q.scheme.scheme} {β : Ordinal.{0}} (h : q.label d = ofOrd β) :
    limitPart β ∈ blocks q :=
  mem_blocks.mpr ⟨_, mem_donorRequests.mpr ⟨d, β, h, rfl⟩, rfl⟩

lemma blocks_limit (q : S α.1 (n + 1)) (μ : Ordinal.{0}) (hμ : μ ∈ blocks q) : limitPart μ = μ := by
  obtain ⟨r, hr, rfl⟩ := mem_blocks.mp hμ
  exact limitPart_eq_self_of_isNonSuccessor (donorRequests_ok q r hr).1

end CappedDonor

namespace Growth

open CappedDonor

variable {n J : ℕ} {P : SemScheme (n + 1)}

abbrev rootIndex (n : ℕ) : Finset (Fin (n + 1)) × ℕ := (Finset.univ.image Fin.castSuccEmb, n)

abbrev topIndex (n : ℕ) : Finset (Fin (n + 1)) × ℕ := (Finset.univ, n + 1)

theorem successor_bounds (hn : 0 < n) (hv : (rootIndex n).1 ∈ P.scheme.plan) :
    rootIndex n ∈ Plan.gradedPlan P.scheme.plan ∧ topIndex n ∈ Plan.gradedPlan P.scheme.plan ∧
    GradedLe (rootIndex n) (topIndex n) ∧ rootIndex n ≠ topIndex n ∧
    ∀ d, GradedLe (P.scheme.cell d) (topIndex n) := by
  refine ⟨Plan.mem_gradedPlan.mpr ⟨hv, hn, ?_⟩,
    Plan.mem_gradedPlan.mpr ⟨P.scheme.isPlan.domain_mem, Nat.succ_pos n, by simp [topIndex]⟩,
    ⟨Finset.subset_univ _, Nat.le_succ _⟩, ?_, fun d => ⟨Finset.subset_univ _, ?_⟩⟩
  · change n ≤ (Finset.univ.image Fin.castSuccEmb).card
    simp only [Finset.card_image_of_injective _ Fin.castSuccEmb.injective,
      Finset.card_univ, Fintype.card_fin, le_refl]
  · exact fun h => Nat.ne_add_one n (congrArg Prod.snd h)
  · exact (P.scheme.grade_le_card_scope d).trans (by
      simpa using (Finset.card_le_univ (P.scheme.scope d)))

theorem root_below_cap {C : SemScheme J} (f : Fin n ↪ Fin J) {c : Cell C.scheme}
    (hsc : C.scheme.scope c = Finset.univ) (hg : n ≤ C.scheme.grade c) :
    GradedLe (Finset.univ.image f, n) (C.scheme.cell c) :=
  ⟨by change Finset.univ.image f ⊆ C.scheme.scope c; rw [hsc]; exact Finset.subset_univ _, hg⟩

theorem literalKappa_label {β : Ordinal.{0}} {q : S β (n + 1)} {p : S β n} {C : S β J}
    {f : Fin n ↪ Fin J} {hvP : (rootIndex n).1 ∈ q.scheme.scheme.plan}
    {hvC : Finset.univ.image f ∈ C.scheme.scheme.plan}
    (hP : q.restrictFace Fin.castSuccEmb hvP = p) (hC : C.restrictFace f hvC = p)
    {c : Cell C.scheme.scheme} {hc : GradedLe (Finset.univ.image f, n) (C.scheme.scheme.cell c)}
    (d : q.scheme.scheme.below (rootIndex n)) :
    q.label d.1 = C.label (literalKappa p.scheme Fin.castSuccEmb hvP (congrArg scheme hP)
      f hvC (congrArg scheme hC) c hc d).1 := by
  change q.label d.1 = C.label (commonFace Fin.castSuccEmb hvP (congrArg scheme hP)
    f hvC (congrArg scheme hC) n d).1
  erw [commonFace_val]
  exact ((StageType.label_castCell hC.symm _).trans ((StageType.label_castCell hP _).trans
    (congrArg q.label (toCell_belowEquiv_symm_val _ _ _ _ d)))).symm

end Growth

end VaughtConjecture.Knight
