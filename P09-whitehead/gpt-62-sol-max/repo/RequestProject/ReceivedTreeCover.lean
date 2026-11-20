module

public import RequestProject.ReceivedTreePaths

@[expose] public section

/-! A genuine regular cover on all sheets of the receiving group. -/
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
universe u
variable {K : Complex2.{u}} (T : SpanningTree K) {G : Type u} [Group G]
  (φ : PresGroup (treeRel T) →* G)

/-- This cover has precisely the coefficient group's sheets. It can be
disconnected when the receiver is not surjective; no connectedness is asserted. -/
noncomputable def cover : Complex2.{u} :=
  TreeVoltage.cover T (freeReceiver T φ) (wordValue_att T φ)

noncomputable def projection : Hom (cover T φ) K :=
  TreeVoltage.projection T (freeReceiver T φ) (wordValue_att T φ)

noncomputable def deck : DeckAction (cover T φ) G where
  smulV h x := (h * x.1, x.2)
  smulE h x := (h * x.1, x.2)
  smulF h x := (h * x.1, x.2)
  one_smulV _ := by simp
  mul_smulV _ _ _ := by simp [mul_assoc]
  one_smulE _ := by simp
  mul_smulE _ _ _ := by simp [mul_assoc]
  one_smulF _ := by simp
  mul_smulF _ _ _ := by simp [mul_assoc]
  src_smul _ _ := rfl
  tgt_smul h x := by
    change (h * x.1 * germValue T φ (x.2, true), K.tgt x.2) =
      (h * (x.1 * germValue T φ (x.2, true)), K.tgt x.2)
    rw [mul_assoc]
  base_smul _ _ := rfl
  att_smul h f := liftPath_translate T φ (K.att f.2) h f.1

end FiniteChains.Comb.ReceivedTree
