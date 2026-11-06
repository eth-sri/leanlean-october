module

public import proofs.HordijkSteelThreshold.BasicSourceEdges

@[expose] public section

namespace HordijkSteelThreshold

open RAF.Polymer RAF.Concrete

variable {n : ℕ} (x : Molecule n)

/-- Arbitrary literal split, retaining its product and split-position identity. -/
def sourceSplitReaction  (k : ℕ)
    (hk : 0 < k) (hkm : k < molLength x) : Reaction n :=
  ⟨x.1, x.2, ⟨k - 1, by unfold molLength at hkm; omega⟩⟩

@[simp] theorem sourceSplitReaction_product  (k : ℕ)
    (hk : 0 < k) (hkm : k < molLength x) :
    reactionProduct (sourceSplitReaction x k hk hkm) = x := rfl

@[simp] theorem sourceSplitReaction_leftLength  (k : ℕ)
    (hk : 0 < k) (hkm : k < molLength x) :
    reactionLeftLength (sourceSplitReaction x k hk hkm) = k := by
  change k - 1 + 1 = k
  omega

variable (side : Bool) (k : ℕ)

/-- The side indicates deletion of a short suffix (true) or prefix (false). -/
def sourceShortSplit   : ℕ :=
  if side then molLength x - k else k

def sourceShortReaction
    (hk : 0 < k) (hkm : k < molLength x) : Reaction n :=
  sourceSplitReaction x (sourceShortSplit x side k)
    (by cases side <;> simp only [sourceShortSplit, Bool.false_eq_true, ↓reduceIte] <;> omega)
    (by cases side <;> simp only [sourceShortSplit, Bool.false_eq_true, ↓reduceIte] <;> omega)

variable (hk : 0 < k) (hkm : k < molLength x)

theorem sourceShortReaction_product
      :
    reactionProduct (sourceShortReaction x side k hk hkm) = x := rfl

@[simp] theorem sourceShortReaction_leftLength
      :
    reactionLeftLength (sourceShortReaction x side k hk hkm) =
      sourceShortSplit x side k := sourceSplitReaction_leftLength _ _ _ _

end HordijkSteelThreshold
