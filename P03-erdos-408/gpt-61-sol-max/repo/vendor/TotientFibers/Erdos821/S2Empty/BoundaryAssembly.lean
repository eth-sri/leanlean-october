module
public import Mathlib.Tactic

public import Erdos821.S2Empty.BigAsymptotic

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Empty

open Erdos821.Blueprint.Graph

/-- Split a full label family according to the small and big group partition. -/
def labelSplitEquiv (P ) (M ) :
    P.Labels M ≃ SmallLabels P M × BigLabels P M := by
  classical
  let splitInv : SmallLabels P M × BigLabels P M → P.Labels M := fun z g =>
    if h : P.big g = false then z.1 ⟨g, h⟩ else
      z.2 ⟨g, by
        simp_all⟩
  refine
    { toFun := fun a => (fun g => a g.val, fun g => a g.val)
      invFun := splitInv
      left_inv := ?_
      right_inv := ?_ }
  · grind
  · rintro ⟨s, b⟩
    apply Prod.ext
    · aesop
    aesop



def bigLabelWeight (F : FixedData) (P ) (n M : ℕ)
    (a : BigLabels P M)  :=
  ∏ g : P.BigGroup, ∏ j : Fin M, tiltedMu F P n g.val (a g j)

theorem full_label_sum_factor  F   P   n M 
     y  :
    (∑ a : P.Labels M,
      if P.smallPhysical y a then
        bigLabelWeight F P n M ((labelSplitEquiv P M a).2) else 0) =
      (∑ s : SmallLabels P M,
        if ∀ g : P.SmallGroup, smallLocalGood g (y g) (s g) then (1 : ℝ) else 0) *
      ∑ b : BigLabels P M, bigLabelWeight F P n M b := by
  classical
  let E := labelSplitEquiv P M
  have hphys (a : P.Labels M) :
      P.smallPhysical y a ↔
        ∀ g : P.SmallGroup, smallLocalGood g (y g) ((E a).1 g) := by
    rfl
  calc
    _ = ∑ z : SmallLabels P M × BigLabels P M,
        if ∀ g : P.SmallGroup, smallLocalGood g (y g) (z.1 g) then
          bigLabelWeight F P n M z.2 else 0 := Fintype.sum_equiv E
        (fun a => if P.smallPhysical y a then bigLabelWeight F P n M (E a).2 else 0)
        (fun z => if ∀ g : P.SmallGroup, smallLocalGood g (y g) (z.1 g) then
          bigLabelWeight F P n M z.2 else 0)
        (by intro a; simp [hphys a])
    _ = ∑ s : SmallLabels P M, ∑ b : BigLabels P M,
        if ∀ g : P.SmallGroup, smallLocalGood g (y g) (s g) then
          bigLabelWeight F P n M b else 0 := Fintype.sum_prod_type'
        (fun (s : SmallLabels P M) b => if ∀ g : P.SmallGroup, smallLocalGood g (y g) (s g) then
          bigLabelWeight F P n M b else 0)
    _ = (∑ s : SmallLabels P M,
          if ∀ g : P.SmallGroup, smallLocalGood g (y g) (s g) then (1 : ℝ) else 0) *
        ∑ b : BigLabels P M, bigLabelWeight F P n M b := by
      calc
        _ = ∑ s : SmallLabels P M,
            if ∀ g : P.SmallGroup, smallLocalGood g (y g) (s g) then
              ∑ b : BigLabels P M, bigLabelWeight F P n M b else 0 := by
          apply Finset.sum_congr rfl
          intro s _
          by_cases hs : ∀ g : P.SmallGroup, smallLocalGood g (y g) (s g) <;> simp [hs]
        _ = _ := by
          rw [Finset.sum_mul]
          grind


end Erdos821.S2Empty
