/- Transport of full-face lifting through point placements and literal installations. -/
module

public import VaughtConjecture.Knight.WholeDonorBoundary
public import VaughtConjecture.Knight.PaddedFaceLift
public import VaughtConjecture.Knight.CappedLiftComposition

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd AmalgamationPlan CoatomBoundaryExtension

noncomputable section

namespace PaddedFaceLift

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {A B : Finset ι} {C : Finset κ}
  {D : CellScheme C} {E E₀ : CellScheme A} {J : Finset κ × ℕ} {j : ℕ}
  {rd : Semantics D} {re : Semantics E} {re₀ : Semantics E₀}
  {emb : D.below J → E₀.below (A, j)} {h : GradedLe (B, j) (A, j)}

theorem to_capped_transport (s : D.below J ≃ E.below (B, j))
    (hs : ∀ p, RespectsSemanticsBelow re (B, j) p → RespectsSemanticsBelow rd J (p ∘ s))
    (t : E₀.below (A, j) ≃ E.below (A, j))
    (ht : ∀ q, RespectsSemanticsBelow re₀ (A, j) q ↔ RespectsSemanticsBelow re (A, j) (q ∘ t.symm))
    (comm : ∀ d, t (emb d) = CellScheme.below.mono h (s d)) (hl : Lift rd re₀ emb) :
    CappedLift re h := by
  intro p q γ hp hq hγ hag
  have hq₀ : RespectsSemanticsBelow re₀ (A, j) (q ∘ t) := (ht _).mpr (by simpa only [Function.comp_def, Equiv.apply_symm_apply] using hq)
  obtain ⟨r, hr, hread, hcap⟩ := hl (hs p hp) hq₀ hγ (fun d => by
    simpa only [Function.comp_apply, comm] using hag (s d))
  refine ⟨r ∘ t.symm, (ht _).mp hr, ?_, ?_⟩
  · aesop
  · rintro d
    obtain ⟨d, rfl⟩ := s.surjective d
    grind

theorem to_capped {emb : D.below J → E.below (A, j)}
    (s : D.below J ≃ E.below (B, j))
    (hs : ∀ p, RespectsSemanticsBelow re (B, j) p → RespectsSemanticsBelow rd J (p ∘ s))
    (comm : ∀ d, emb d = CellScheme.below.mono h (s d)) (hl : Lift rd re emb) : CappedLift re h :=
  to_capped_transport s hs (Equiv.refl _) (fun _ => Iff.rfl) comm hl

end PaddedFaceLift

namespace WholeDonorBoundary.Input

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)} {m l r : ℕ}
  (I : Input A B C R m l r) {D : CellScheme A} {sem : Semantics D}
  (L : ExactSemanticFace I.leftRows sem) (G : ExactSemanticFace I.rightRows sem)

include I L G

/-- Lift through either full face before extending to the installed ambient. -/
theorem subface_lift {S T : Finset ι} {i j : ℕ} (hS : (S, i) ∈ Plan.gradedPlan R)
    (hT : T ∈ R) (hST : S ⊆ T) (hTA : T ⊆ A) (hij : i ≤ j) (hv : T ⊆ B ∨ T ⊆ C)
    (hl : (T, i) ∈ Plan.gradedPlan R → CappedLift sem (show GradedLe (T, i) (A, i) from ⟨hTA, le_rfl⟩)) :
    CappedLift sem (show GradedLe (S, i) (A, j) from ⟨hST.trans hTA, hij⟩) := by
  have hTi : (T, i) ∈ Plan.gradedPlan R := Plan.mem_gradedPlan.mpr
    ⟨hT, (Plan.mem_gradedPlan.mp hS).2.1, (Plan.mem_gradedPlan.mp hS).2.2.trans (Finset.card_le_card hST)⟩
  exact ((I.installed_lift L G hS hTi ⟨hST, le_rfl⟩ hv).comp (hl hTi)).raise_target
    (h := hST.trans hTA) hij

/-- Either original face supplies the subface-to-full lift, with the same cap. -/
theorem subface_to_full {S : Finset ι} {i j : ℕ} (hB : B ⊆ A) (hC : C ⊆ A)
    (hS : (S, i) ∈ Plan.gradedPlan R) (hside : S ⊆ B ∨ S ⊆ C) (hij : i ≤ j)
    (hl : (B, i) ∈ Plan.gradedPlan R → CappedLift sem (show GradedLe (B, i) (A, i) from ⟨hB, le_rfl⟩))
    (hr : (C, i) ∈ Plan.gradedPlan R → CappedLift sem (show GradedLe (C, i) (A, i) from ⟨hC, le_rfl⟩)) :
    CappedLift sem (show GradedLe (S, i) (A, j) from
      ⟨I.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hS).1, hij⟩) := by
  rcases hside with hb | hc
  · exact I.subface_lift L G hS (I.leftPlan_le I.leftScheme.isPlan.domain_mem) hb hB hij (Or.inl le_rfl) hl
  · exact I.subface_lift L G hS (I.rightPlan_le I.rightScheme.isPlan.domain_mem) hc hC hij (Or.inr le_rfl) hr

theorem same_grade_of_faces {S T : Finset ι} {j : ℕ}
    (hB : B ⊆ A) (hC : C ⊆ A) (hcover : ∀ S ∈ R, S ≠ A → S ⊆ B ∨ S ⊆ C)
    (hl : (B, j) ∈ Plan.gradedPlan R → CappedLift sem (show GradedLe (B, j) (A, j) from ⟨hB, le_rfl⟩))
    (hr : (C, j) ∈ Plan.gradedPlan R → CappedLift sem (show GradedLe (C, j) (A, j) from ⟨hC, le_rfl⟩))
    (hS : (S, j) ∈ Plan.gradedPlan R) (hT : (T, j) ∈ Plan.gradedPlan R) (hST : S ⊆ T) :
    CappedLift sem (show GradedLe (S, j) (T, j) from ⟨hST, le_rfl⟩) := by
  by_cases ht : T = A
  · subst T
    by_cases hs : S = A
    · subst S; exact lift_refl
    exact I.subface_to_full L G hB hC hS (hcover S (Plan.mem_gradedPlan.mp hS).1 hs) le_rfl hl hr
  · exact I.installed_lift L G hS hT ⟨hST, le_rfl⟩ (hcover T (Plan.mem_gradedPlan.mp hT).1 ht)

end WholeDonorBoundary.Input

end

end VaughtConjecture.Knight
