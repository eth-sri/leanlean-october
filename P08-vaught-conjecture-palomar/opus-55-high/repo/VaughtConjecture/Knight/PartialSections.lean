/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PullbackSemantics

/-! # Pullbacks along retractions with partial sections; transport along bijections

`Semantics.pullback_isConsistent` and `RespectsSemanticsBelow.pullback_of_sect` demand a section
over **every** graded index.  Two different faces glued along a shared pair have no total section
(a face carries only its own level-three cells).  Availability is trivial when the request already
has the index of the larger cell (`Xi := Sig`), so sections are needed only for pairs of
**distinct** graded indices — `PartialSections` — and both theorems go through
(`Semantics.pullback_isConsistent'`, `RespectsSemanticsBelow.pullback_of_sect'`).  A labelling of
the extension that is constant on the fibres of the retraction (rigidity) descends along a
section to a respecting labelling of the base (`RespectsSemanticsBelow.descend`).

Respect and bountifulness transport along a bijection of lower sets preserving scopes and grades
with agreeing rows (`RespectsSemanticsBelow.of_equiv`, `respects_iff_of_equiv`,
`bountiful_of_equiv`).  Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

section Transport
variable {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι'] {A : Finset ι} {A' : Finset ι'}
  {D : CellScheme A} {D' : CellScheme A'} {sem : Semantics D} {sem' : Semantics D'}

section
variable {BJ : Finset ι' × ℕ} {BJ' : Finset ι × ℕ} (e : D'.below BJ ≃ D.below BJ')

/-- The graded order is reflected and preserved by a bijection preserving scopes and grades. -/
theorem gradedLe_iff_of_equiv (hgrade : ∀ a, D'.grade a.1 = D.grade (e a).1)
    (hscope : ∀ a b, D'.scope a.1 ⊆ D'.scope b.1 ↔ D.scope (e a).1 ⊆ D.scope (e b).1)
    (a b : D'.below BJ) :
    GradedLe (D'.cell a.1) (D'.cell b.1) ↔ GradedLe (D.cell (e a).1) (D.cell (e b).1) := by
  constructor
  · rintro ⟨hs, hg⟩
    refine ⟨(hscope a b).mp hs, ?_⟩
    simp_all
  · rintro ⟨hs, hg⟩
    refine ⟨(hscope a b).mpr hs, ?_⟩
    simp_all

/-- **Respect transports along a bijection of lower sets with agreeing rows.** -/
theorem RespectsSemanticsBelow.of_equiv (hgrade : ∀ a, D'.grade a.1 = D.grade (e a).1)
    (hscope : ∀ a b, D'.scope a.1 ⊆ D'.scope b.1 ↔ D.scope (e a).1 ⊆ D.scope (e b).1)
    (hrows : ∀ (Sig : D'.below BJ) (d : D'.below (D'.cell Sig.1))
      (hd : GradedLe (D.cell (e ⟨d.1, d.2.trans Sig.2⟩).1) (D.cell (e Sig).1)),
      sem'.E Sig.1 d = sem.E (e Sig).1 ⟨(e ⟨d.1, d.2.trans Sig.2⟩).1, hd⟩)
    {q : D.below BJ' → ExtOrd} (hq : RespectsSemanticsBelow sem BJ' q) :
    RespectsSemanticsBelow sem' BJ (fun a => q (e a)) where
  orderly a := by
    have := hq.orderly (e a)
    grind
  locality Sig := by
    let φ : D'.below (D'.cell Sig.1) → D.below (D.cell (e Sig).1) := fun d =>
      ⟨(e ⟨d.1, d.2.trans Sig.2⟩).1, (gradedLe_iff_of_equiv e hgrade hscope _ _).mp d.2⟩
    have key := (hq.locality (e Sig)).reindex φ
    refine transformsTo_congr ?_ ?_ ?_ key
    · funext d
      exact (hgrade ⟨d.1, d.2.trans Sig.2⟩).symm
    · funext d
      exact (hrows Sig d _).symm
    · funext d
      rfl
  availability Sig Xi₀ hs hg := by
    obtain ⟨Xi, hcell, hle⟩ := hq.availability (e Sig) (e Xi₀) ((hscope _ _).mp hs)
      (by grind)
    refine ⟨e.symm Xi, ?_, ?_⟩
    · apply GradedLe.antisymm'
      · rw [gradedLe_iff_of_equiv e hgrade hscope, e.apply_symm_apply, hcell]
        exact ⟨Finset.Subset.refl _, le_rfl⟩
      · rw [gradedLe_iff_of_equiv e hgrade hscope, e.apply_symm_apply, hcell]
        exact ⟨Finset.Subset.refl _, le_rfl⟩
    · rw [e.apply_symm_apply]; exact hle

end

/-- **Bountifulness transports along compatible bijections of the two lower sets.** -/
theorem bountiful_of_equiv {CI BJ} {CI' BJ'}
    h h'
    (eB : D'.below BJ ≃ D.below BJ') (eC : D'.below CI ≃ D.below CI')
    (hmonoE : ∀ d, eB (CellScheme.below.mono h d) = CellScheme.below.mono h' (eC d))
    (hRB : ∀ q,
      RespectsSemanticsBelow sem' BJ q ↔ RespectsSemanticsBelow sem BJ' (q ∘ eB.symm))
    (hRC : ∀ p : D'.below CI → ExtOrd,
      RespectsSemanticsBelow sem' CI p ↔ RespectsSemanticsBelow sem CI' (p ∘ eC.symm))
    (hb : ∀ (p : D.below CI' → ExtOrd) (q : D.below BJ' → ExtOrd) (γ : ExtOrd),
      RespectsSemanticsBelow sem CI' p → RespectsSemanticsBelow sem BJ' q →
      extVisibilityReplace γ BJ'.2 BJ'.2 = γ →
      (∀ d : D.below CI', min (q (CellScheme.below.mono h' d)) γ = min (p d) γ) →
      ∃ q' : D.below BJ' → ExtOrd, RespectsSemanticsBelow sem BJ' q' ∧
        (∀ d : D.below BJ', min (q' d) γ = min (q d) γ) ∧
        (∀ d : D.below CI', q' (CellScheme.below.mono h' d) = p d))
    (hgradeBJ : BJ.2 = BJ'.2)
    p q γ
    (hp : RespectsSemanticsBelow sem' CI p) (hq : RespectsSemanticsBelow sem' BJ q)
    (hγ : extVisibilityReplace γ BJ.2 BJ.2 = γ)
    (hagree : ∀ d : D'.below CI, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) :
    ∃ q' : D'.below BJ → ExtOrd, RespectsSemanticsBelow sem' BJ q' ∧
      (∀ d : D'.below BJ, min (q' d) γ = min (q d) γ) ∧
      (∀ d : D'.below CI, q' (CellScheme.below.mono h d) = p d) := by
  obtain ⟨q₀, hq₀, hq₀γ, hq₀p⟩ := hb (p ∘ eC.symm) (q ∘ eB.symm) γ ((hRC p).mp hp) ((hRB q).mp hq)
    (by rw [← hgradeBJ]; exact hγ)
    (by grind)
  refine ⟨q₀ ∘ eB, ?_, ?_, ?_⟩
  · rw [hRB]
    have : (q₀ ∘ eB) ∘ eB.symm = q₀ := by funext d; simp
    rw [this]; exact hq₀
  · grind
  · grind

end Transport

theorem Semantics.E_congr' {ι} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    (sem : Semantics D) {x y : Cell D} (h : x = y) {d}
    {d'} (hd : d.1 = d'.1) : sem.E x d = sem.E y d' := by
  subst h
  rw [Subtype.ext hd]

section Transport2
variable {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι'] {A : Finset ι} {A' : Finset ι'}
  {D : CellScheme A} {D' : CellScheme A'} {sem : Semantics D} {sem' : Semantics D'}

/-- **Respect transports both ways** along a bijection with agreeing rows. -/
theorem respects_iff_of_equiv {BJ} {BJ' : Finset ι × ℕ}
    (e : D'.below BJ ≃ D.below BJ') (hgrade : ∀ a, D'.grade a.1 = D.grade (e a).1)
    (hscope : ∀ a b, D'.scope a.1 ⊆ D'.scope b.1 ↔ D.scope (e a).1 ⊆ D.scope (e b).1)
    (hrows : ∀ Sig d
      hd,
      sem'.E Sig.1 d = sem.E (e Sig).1 ⟨(e ⟨d.1, d.2.trans Sig.2⟩).1, hd⟩)
    (q : D'.below BJ → ExtOrd) :
    RespectsSemanticsBelow sem' BJ q ↔ RespectsSemanticsBelow sem BJ' (q ∘ e.symm) := by
  constructor
  · intro hq
    refine RespectsSemanticsBelow.of_equiv (sem := sem') (sem' := sem) e.symm
      (fun b => by rw [hgrade (e.symm b), e.apply_symm_apply])
      (fun a b => by rw [hscope (e.symm a) (e.symm b), e.apply_symm_apply, e.apply_symm_apply])
      ?_ hq
    intro Sig d hd
    have hv1 : (e (e.symm ⟨d.1, d.2.trans Sig.2⟩)).1 = d.1 :=
      congrArg Subtype.val (e.apply_symm_apply ⟨d.1, d.2.trans Sig.2⟩)
    have hv2 : (e (e.symm Sig)).1 = Sig.1 := congrArg Subtype.val (e.apply_symm_apply Sig)
    have hd0 : GradedLe (D.cell (e (e.symm ⟨d.1, d.2.trans Sig.2⟩)).1)
        (D.cell (e (e.symm Sig)).1) := by
      rw [hv1, hv2]; exact d.2
    have h1 := hrows (e.symm Sig) ⟨(e.symm ⟨d.1, d.2.trans Sig.2⟩).1, hd⟩ hd0
    have h2 : sem.E Sig.1 d =
        sem.E (e (e.symm Sig)).1 ⟨(e (e.symm ⟨d.1, d.2.trans Sig.2⟩)).1, hd0⟩ :=
      sem.E_congr' hv2.symm hv1.symm
    exact h2.trans h1.symm
  · intro hq
    have := RespectsSemanticsBelow.of_equiv e hgrade hscope hrows hq
    simp_all

end Transport2

end VaughtConjecture.Knight
