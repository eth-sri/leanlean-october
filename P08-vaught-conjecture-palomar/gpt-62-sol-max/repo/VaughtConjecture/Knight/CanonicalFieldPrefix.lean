/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalFieldLayer
public import VaughtConjecture.Knight.CanonicalPrefixDecoding

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalFieldPrefix

open Transform Value ExtOrd SourcePrefixRows CanonicalFieldLayer

open CanonicalPairedInverse PairedSlotEncoding

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable (sem : Semantics D) (j : ℕ) (X : Type*) [Fintype X] (occ : Cell D → X)

variable (hj : 0 < j) (hA : j ≤ A.card)

variable (hproper : ∀ d : Cell D, D.scope d ≠ A) (hg : ∀ d : Cell D, D.grade d ≤ j)

theorem exists_section (a : Profile sem j X occ)
    {p : X → ExtOrd} (hp : RespectsSemantics sem (p ∘ occ)) (ht : ∀ x, p x ≠ ⊤)
    {B : ℕ} (hB : B ≤ 2 * Fintype.card X + 1)
    (hag : ∀ x, min (a.val x) (grid j B) = min (p x) (grid j B)) :
    ∃ r : Cell (scheme sem j X occ hj hA) → ExtOrd,
      RespectsSemantics (rows sem j X occ hj hA hproper hg) r ∧
      (∀ d, r (old sem j X occ hj hA d) = p (occ d)) ∧
      ∀ d, min (r d) (grid j B) =
        min (source sem j X occ hj hA hproper hg a d) (grid j B) := by
  let F := data sem j X occ hj hA hproper hg
  let b := encode sem j X occ hg hp ht
  obtain ⟨δ, hr, hread, hc⟩ := CanonicalPrefixDecoding.exists_decoder a.property.2 ht hB hag
    (source sem j X occ hj hA hproper hg a) (source sem j X occ hj hA hproper hg b)
    (F.profile_respects (controller sem j X occ hj hA a)) (F.profile_respects (controller sem j X occ hj hA b))
    (source_supported sem j X occ hj hA hproper hg a) (source_prefix sem j X occ hj hA hproper hg b a)
  refine ⟨_, hr.toRespects (fun d => ⟨(scheme sem j X occ hj hA).scope_subset d, max_grade sem j X occ hj hA hg d⟩), fun d => ?_, hc⟩
  exact (congrArg δ (source_old sem j X occ hj hA hproper hg b d)).trans (hread (occ d))

/-- Completion of physical occurrences, with all other fields retained before
normalization. Injectivity is occurrence injectivity, not label injectivity. -/
theorem exists_boundary_section (hinj : Function.Injective occ) (a : Profile sem j X occ)
    {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
    {B : ℕ} (hB : B ≤ 2 * Fintype.card X + 1)
    (hag : ∀ d, min (a.val (occ d)) (grid j B) = min (p d) (grid j B)) :
    ∃ r : Cell (scheme sem j X occ hj hA) → ExtOrd,
      RespectsSemantics (rows sem j X occ hj hA hproper hg) r ∧
      (∀ d, r (old sem j X occ hj hA d) = p d) ∧
      ∀ d, min (r d) (grid j B) =
        min (source sem j X occ hj hA hproper hg a d) (grid j B) := by
  classical
  let v := Function.extend occ p a.val
  have hv (d : Cell D) : v (occ d) = p d := hinj.extend_apply p a.val d
  have hvp : RespectsSemantics sem (v ∘ occ) := by
    aesop
  have hvt : ∀ x, v x ≠ ⊤ := by
    intro x
    by_cases hx : ∃ d, occ d = x
    · grind
    · rw [show v x = a.val x from Function.extend_apply' p a.val x hx]
      apply a.property.2.2
  have hva : ∀ x, min (a.val x) (grid j B) = min (v x) (grid j B) := by
    intro x
    by_cases hx : ∃ d, occ d = x
    · grind
    · rw [show v x = a.val x from Function.extend_apply' p a.val x hx]
  obtain ⟨r, hr, hread, hcap⟩ := exists_section sem j X occ hj hA hproper hg
    a hvp hvt hB hva
  grind

end

end VaughtConjecture.Knight.CanonicalFieldPrefix
