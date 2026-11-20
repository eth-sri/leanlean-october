/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalPairBoundary
public import VaughtConjecture.Knight.ScopedSourcePrefixLayer

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalPairLocalSections

open Transform Value ExtOrd SourcePrefixRows PairedSlotEncoding PairedSlotComparison

open CanonicalPairBoundary

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable (sem : Semantics D) (hA : 2 ≤ A.card) (hp : ∀ d : Cell D, D.scope d ≠ A)

abbrev one_le := (by decide : 1 ≤ 2).trans hA

abbrev carrier := scheme sem 1 2 (by decide) (one_le hA) (by decide) hA

abbrev semantics := rows sem 1 2 (by decide) (one_le hA) (by decide) hA hp (by decide)

abbrev original := old sem 1 2 (by decide) (one_le hA) (by decide) hA

abbrev small := lower sem 1 2 (by decide) (one_le hA) (by decide) hA

local notation "M" => CanonicalPairBoundary.frame sem 1 2 (by decide) hA hp (by decide)

abbrev smallRows := CanonicalMixedGradeLayers.rows M

local notation "Γ" => GradeCutPairRows.assembly D (firstProfiles sem 1 2) (secondProfiles sem 2)
  1 2 (by decide) (one_le hA) (by decide) hA hp (by decide)

variable {K : ℕ} (hK : 2 ≤ K) {p : Cell D → ExtOrd}

variable (hpr : RespectsSemanticsBelow sem (A, K) (fun d => p d.1)) (ht : ∀ d, p d ≠ ⊤)

include hK hpr in
theorem cut_lawful : RespectsSemantics (GradeCutBoundary.rows D 2 sem)
    (fun d => p (GradeCutBoundary.toCell D 2 d)) := by
  have hr := GradeCutBoundary.pullback_respects D 2 sem le_rfl
    (hpr.mono (show GradedLe (A, 2) (A, K) from ⟨Finset.Subset.refl _, hK⟩))
  exact hr.toRespects (fun d =>
    ⟨D.scope_subset _, GradeCutBoundary.grade_bound D 2 d⟩)

def smallSection (G : Finset ExtOrd) (C : ExtOrd) : Cell (small sem hA) → ExtOrd :=
  CanonicalMixedGradeLayers.sectionOf M (cut_lawful sem hK hpr)
    (fun d => ht (GradeCutBoundary.toCell D 2 d)) G C

def sectionOf (G : Finset ExtOrd) (C : ExtOrd) : Cell (carrier sem hA) → ExtOrd :=
  (Γ).union.paste p
    (smallSection sem hA hp hK hpr ht G C)

theorem section_old {G : Finset ExtOrd} {C : ExtOrd} (d : Cell D) :
    sectionOf sem hA hp hK hpr ht G C (original sem hA d) = p d :=
  (Γ).union.paste_old p _ d

variable {G : Finset ExtOrd} {C : ExtOrd}

theorem small_readback (hG : ∀ z ∈ G, SelfVis 2 z) (hC : SelfVis 2 C)
    (d : Cell (GradeCutBoundary.scheme D 2)) :
    smallSection sem hA hp hK hpr ht G C
      (GradeCutPairCarrier.old (GradeCutBoundary.scheme D 2) _ _ 1 2
        (by decide) (one_le hA) (by decide) hA d) = p (GradeCutBoundary.toCell D 2 d) :=
  CanonicalMixedGradeLayers.section_boundary M (cut_lawful sem hK hpr) _ hG hC d

theorem section_lawful (hG : ∀ z ∈ G, SelfVis 2 z) (hC : SelfVis 2 C) :
    RespectsSemanticsBelow (semantics sem hA hp) (A, K)
      (fun d => sectionOf sem hA hp hK hpr ht G C d.1) := by
  exact (Γ).paste_respectsBelow (overlap sem 1 2 (by decide) (one_le hA) (by decide) hA hp (by decide))
    hpr (CanonicalMixedGradeLayers.section_lawful M
      (cut_lawful sem hK hpr) (fun d => ht (GradeCutBoundary.toCell D 2 d)) hG hC)
    (small_readback sem hA hp hK hpr ht hG hC)

theorem section_bound (hC : SelfVis 2 C) (hb : ∀ d, p d ≤ C)
    (d : Cell (carrier sem hA)) : sectionOf sem hA hp hK hpr ht G C d ≤ C :=
  (Γ).union.paste_pred (P := (· ≤ C)) hb (CanonicalMixedGradeLayers.section_bound M
    (cut_lawful sem hK hpr) _ hC (fun a => hb (GradeCutBoundary.toCell D 2 a))) d

theorem section_supported {L : ℕ} (hL : 2 ≤ L) (hCG : C ∈ G)
    (d : Cell (carrier sem hA)) :
    OrbitPrefixSupport.Supported L (G : Set ExtOrd) p
      (sectionOf sem hA hp hK hpr ht G C d) := by
  have hl (a : Cell (small sem hA)) : OrbitPrefixSupport.Supported L (G : Set ExtOrd) p
      (smallSection sem hA hp hK hpr ht G C a) := by
    rcases CanonicalMixedGradeLayers.section_supported M hL hCG
      (cut_lawful sem hK hpr) (fun d => ht (GradeCutBoundary.toCell D 2 d)) a with
      hb | hm | ⟨e, i, hi, he⟩
    · exact Or.inl hb
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr ⟨GradeCutBoundary.toCell D 2 e, i, hi, he⟩)
  exact (Γ).union.paste_pred (OrbitPrefixSupport.supported_field _ _ _) hl d

theorem section_agreement {q : Cell D → ExtOrd}
    (hqr : RespectsSemanticsBelow sem (A, K) (fun d => q d.1)) (htq : ∀ d, q d ≠ ⊤)
    {h : ExtOrd} (hG : ∀ z ∈ G, SelfVis 2 z) (hC : SelfVis 2 C)
    (hh : h ∈ G) (hhC : h ≤ C) (hag : Agree p q h) :
    Agree (sectionOf sem hA hp hK hpr ht G C) (sectionOf sem hA hp hK hqr htq G C) h := by
  have hl := CanonicalMixedGradeLayers.section_agreement M
    (cut_lawful sem hK hpr) (cut_lawful sem hK hqr)
    (fun d => ht (GradeCutBoundary.toCell D 2 d))
    (fun d => htq (GradeCutBoundary.toCell D 2 d)) hG hC hh hhC
    (fun d => hag (GradeCutBoundary.toCell D 2 d))
  exact (Γ).union.paste_rel (R := fun x y => min x h = min y h) hag hl

open SharpWitnessComposition

theorem full_source_short (c : Cell (carrier sem hA))
    (hc : (carrier sem hA).scope c = A)
    (d : (carrier sem hA).below ((carrier sem hA).cell c)) :
    Short ((carrier sem hA).grade c) ((semantics sem hA hp).E c d) := by
  have hc2 : (carrier sem hA).grade c ≤ 2 := by
    obtain ⟨x, rfl⟩ := (GradeCutPairCarrier.occEquiv D _ _ 1 2 (by decide)
      (one_le hA) (by decide) hA).surjective c
    change (carrier sem hA).grade (GradeCutPairCarrier.cell _ _ _ _ _ _ _ _ _ x) ≤ 2
    change ((carrier sem hA).cell
      (GradeCutPairCarrier.cell _ _ _ _ _ _ _ _ _ x)).1 = A at hc
    rw [GradeCutPairCarrier.cell_idx] at hc
    rw [CellScheme.grade, GradeCutPairCarrier.cell_idx]
    rcases x with (c | q) | q
    · exact (hp c hc).elim
    · exact (by decide : 1 ≤ 2)
    · exact le_rfl
  obtain ⟨a, rfl⟩ := GradeCutPairCarrier.exhaustive D _ _ 1 2 (by decide)
    (one_le hA) (by decide) hA c hc2
  obtain ⟨e, rfl⟩ := (GradeCutPairCarrier.belowEquiv D _ _ 1 2 (by decide)
    (one_le hA) (by decide) hA _ hc2).surjective d
  have hi := GradeCutPairCarrier.embed_index D _ _ 1 2 (by decide) (one_le hA)
    (by decide) hA a
  let f : (small sem hA).below ((small sem hA).cell a) := ⟨e.1, hi ▸ e.2⟩
  have he := CanonicalPairBoundary.lower_row sem 1 2 (by decide) (one_le hA)
    (by decide) hA hp (by decide) a f
  have hv := CanonicalMixedGradeLayers.full_source_short M a
    ((congrArg Prod.fst hi).symm.trans hc) f
  rw [← he] at hv
  exact (congrArg (fun i => Short i _) (congrArg Prod.snd hi)).mpr hv

end

end VaughtConjecture.Knight.CanonicalPairLocalSections
