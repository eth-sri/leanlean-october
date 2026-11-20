module

public import QPBT.Games.DistributionMarginals

/-! Reordering the independent draws of finite product distributions. -/

@[expose] public section

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

namespace Distribution

section

variable {α β γ δ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
include α β γ δ

/-- Push forward two independent draws coordinatewise. -/
theorem prod_map_prodMap
    (μ : Distribution α) (ν : Distribution β) (f : α → γ) (g : β → δ) :
    prod (μ.map f) (ν.map g) = (prod μ ν).map (Prod.map f g) := by
  rw [prod_map_left, prod_map_right, map_map]
  rfl

/-- Move the first and last draws of a four-factor product into a pair. -/
theorem prod_map_shuffleAssoc
    (A : Distribution α) (B : Distribution β) (C : Distribution γ) (D : Distribution δ) :
    prod (prod (prod A B) C) D = (prod (prod B C) (prod A D)).map
      (fun w => (((w.2.1, w.1.1), w.1.2), w.2.2)) := by
  symm
  refine map_bijective_eq _ _ _ (fun w => ((w.1.1.2, w.1.2), (w.1.1.1, w.2)))
    (fun _ => rfl) (fun _ => rfl) (fun _ => ?_) (fun _ => ?_)
  · simp only [prod_support, Finset.mem_product]
    tauto
  · simp only [prod_weight]
    ring

end

/-- Transpose three independent pairs to two independent triples. -/
theorem prod_map_transposeTriple {A B C D E F : Type*}
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] [DecidableEq E] [DecidableEq F]
    (a : Distribution A) (b : Distribution B) (c : Distribution C)
    (d : Distribution D) (e : Distribution E) (f : Distribution F) :
    (prod (prod (prod a b) (prod c d)) (prod e f)).map
      (fun w => ((w.2.1, w.1.2.1, w.1.1.1), (w.2.2, w.1.2.2, w.1.1.2))) =
      prod (prod e (prod c a)) (prod f (prod d b)) := by
  refine map_bijective_eq _ _ _ (fun w => (((w.1.2.2, w.2.2.2), (w.1.2.1, w.2.2.1)), w.1.1, w.2.1))
    (fun _ => rfl) (fun _ => rfl) (fun _ => ?_) (fun _ => ?_)
  · simp only [prod_support, Finset.mem_product]
    tauto
  · simp only [prod_weight]
    ring

end Distribution

end MIPStarRE.QPBT
