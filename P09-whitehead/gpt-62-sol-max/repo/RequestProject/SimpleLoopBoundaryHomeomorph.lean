module

public import RequestProject.SquareBoundaryLoopQuotient
public import RequestProject.SquareBoundaryNormHomeomorph

@[expose] public section

/-! Elementary simple-arc gluing and an explicit homeomorphism from the
actual normed-circle boundary onto a once-traversed Hausdorff simple loop.
The proof uses the concrete interval quotient, not a classification theorem.
Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval
open Set Topology

namespace FiniteChains.RelativeAttachment

variable {X : Type} [TopologicalSpace X]

private theorem path_trans_fiber_le {a b c : X} (p : Path a b) (q : Path b c)
    (hp : Function.Injective p) (hq : Function.Injective q) {allowEnds : Prop}
    (hmeet : ∀ u v : I, p u = q v → p u = b ∨ allowEnds ∧ p u = a ∧ q v = c)
    {s t : I} (hst : (s : ℝ) ≤ t) (h : (p.trans q) s = (p.trans q) t) :
    s = t ∨ allowEnds ∧ s = 0 ∧ t = 1 := by
  simp only [Path.trans_apply] at h
  split_ifs at h with hs ht
  · have hv := congrArg Subtype.val (hp h)
    exact Or.inl (Subtype.ext (by dsimp at hv; linarith))
  · rcases hmeet _ _ h with hb | ⟨ha, hs, ht⟩
    · have hv := congrArg Subtype.val (hp (hb.trans p.target.symm))
      have hw := congrArg Subtype.val (hq (h.symm.trans (hb.trans q.source.symm)))
      exact Or.inl (Subtype.ext (by dsimp at hv hw; linarith))
    · have hv := congrArg Subtype.val (hp (hs.trans p.source.symm))
      have hw := congrArg Subtype.val (hq (ht.trans q.target.symm))
      exact Or.inr ⟨ha, Subtype.ext (by change (s : ℝ) = 0; dsimp at hv; linarith),
        Subtype.ext (by change (t : ℝ) = 1; dsimp at hw; linarith)⟩
  · linarith
  · have hv := congrArg Subtype.val (hq h)
    exact Or.inl (Subtype.ext (by dsimp at hv; linarith))

theorem path_trans_injective {a b c : X} (p : Path a b) (q : Path b c)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hmeet : ∀ s t : I, p s = q t → p s = b) : Function.Injective (p.trans q) := by
  intro s t h
  let core {s t : I} := path_trans_fiber_le p q hp hq (allowEnds := False)
    (fun s t h => Or.inl (hmeet s t h)) (s := s) (t := t)
  grind

/-- Two arcs meeting only at their endpoints identify only the ends of the interval. -/
theorem path_trans_loop_fiber {a b : X} (p : Path a b) (q : Path b a)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hmeet : ∀ s t : I, p s = q t → p s = a ∨ p s = b)
    {s t : I} (h : (p.trans q) s = (p.trans q) t) :
    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  let core {s t : I} := path_trans_fiber_le p q hp hq (allowEnds := True) (by
    grind) (s := s) (t := t)
  grind

theorem squareLoopDesc_bijective {a : X} (p : Path a a)
    (hsur : Function.Surjective p)
    (hfiber : ∀ s t : I, p s = p t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) :
    Function.Bijective (squareLoopDesc p) := by
  constructor
  · intro x y h
    obtain ⟨s, rfl⟩ := squareBoundaryTraversal_surjective x
    obtain ⟨t, rfl⟩ := squareBoundaryTraversal_surjective y
    grind [squareLoopDesc_traversal]
  · intro x
    obtain ⟨t, rfl⟩ := hsur x
    exact ⟨squareBoundaryTraversal t, squareLoopDesc_traversal p t⟩

def simpleLoopSquareHomeomorph [T2Space X] {a : X} (p : Path a a)
    (hsur : Function.Surjective p)
    (hfiber : ∀ s t : I, p s = p t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) :
    SquareBoundary ≃ₜ X := by
  letI : CompactSpace SquareBoundary := ⟨by
    simpa only [Set.range_eq_univ.mpr squareBoundaryTraversal_surjective] using
      (isCompact_range squareBoundaryTraversal.continuous)⟩
  exact Continuous.homeoOfEquivCompactToT2 (f :=
    Equiv.ofBijective (squareLoopDesc p) (squareLoopDesc_bijective p hsur hfiber))
    (squareLoopDesc p).continuous

def simpleLoopBoundaryHomeomorph [T2Space X] {a : X} (p : Path a a)
    (hsur : Function.Surjective p)
    (hfiber : ∀ s t : I, p s = p t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) :
    UnitBoundary (Fin 2 → ℝ) ≃ₜ X :=
  unitBoundarySquareHomeomorph.trans (simpleLoopSquareHomeomorph p hsur hfiber)

@[simp] theorem simpleLoopSquareHomeomorph_traversal [T2Space X] {a : X} (p : Path a a)
    (hsur : Function.Surjective p)
    (hfiber : ∀ s t : I, p s = p t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) (t : I) :
    simpleLoopSquareHomeomorph p hsur hfiber (squareBoundaryTraversal t) = p t :=
  squareLoopDesc_traversal p t

end FiniteChains.RelativeAttachment
