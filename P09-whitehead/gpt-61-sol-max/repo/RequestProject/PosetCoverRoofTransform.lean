import Mathlib.Tactic

import RequestProject.PosetCoverDownTransform

/-! The two legs of a contraction lift into the same sheet of a poset cover. -/
namespace FiniteChains.Comb.IsPosetCover
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}
variable (hf : IsPosetCover f) (g : Q → Q) (hg : ∀ q, g q ≤ q)
  (b : Q) (hb : ∀ q, g q ≤ b)

/-- Lift the upper leg from the canonical lower lift, rather than independently
choosing a lift of the endpoint. -/
noncomputable def roofTransform (a : P)  :=
  Classical.choose (hf.up (hf.downTransform g hg a) b
    ((hf.downTransform_spec g hg a).2 ▸ hb (f a)))

abbrev roofTransform_spec (a : P)  :=
  (Classical.choose_spec (hf.up (hf.downTransform g hg a) b
    ((hf.downTransform_spec g hg a).2 ▸ hb (f a)))).1

/-- Comparable vertices have exactly the same lifted endpoint. -/
abbrev roofTransform_comparable_equal (hmono : Monotone g)
    {a a' : P} (haa' : a ≤ a')  :=
  have ha := FiniteChains.Comb.IsPosetCover.roofTransform_spec hf g hg b hb a;
  have ha' := FiniteChains.Comb.IsPosetCover.roofTransform_spec hf g hg b hb a';
  FiniteChains.Comb.IsPosetCover.up_inj hf ha.left
    (LE.le.trans (FiniteChains.Comb.IsPosetCover.downTransform_monotone hf g hmono hg haa') ha'.left)
    (Eq.trans ha.right (Eq.symm ha'.right))

theorem roofTransform_monotone (hmono : Monotone g) :
    Monotone (hf.roofTransform g hg b hb) := by
  intro a a' haa'
  exact le_of_eq (hf.roofTransform_comparable_equal g hg b hb hmono haa')

end FiniteChains.Comb.IsPosetCover
