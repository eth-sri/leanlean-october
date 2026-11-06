import Mathlib.Tactic

import RequestProject.OrderPosetCovering

/-! Lifting an actual downward monotone homotopy through a poset covering. -/
namespace FiniteChains.Comb
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}

namespace IsPosetCover
variable (hf : IsPosetCover f)
include hf

/-- A comparability interval lifts inside the specified interval upstairs. -/
theorem exists_interval_lift {a b : P} (hab : a ≤ b) (q : Q)
    (haq : f a ≤ q) (hqb : q ≤ f b) :
    ∃ c : P, a ≤ c ∧ c ≤ b ∧ f c = q := by
  obtain ⟨c, ⟨hac, hfc⟩, _⟩ := hf.up a q haq
  obtain ⟨d, ⟨hcd, hfd⟩, _⟩ := hf.up c (f b) (hfc ▸ hqb)
  have hd  := hf.up_inj (hac.trans hcd) hab hfd
  exact ⟨c, hac, hd ▸ hcd, hfc⟩

variable (g : Q → Q)
  (hg : ∀ q, g q ≤ q)
noncomputable def downTransform   (a : P)  :=
  Classical.choose (hf.down a (g (f a)) (hg (f a)))

theorem downTransform_spec   (a : P) :
    hf.downTransform g hg a ≤ a ∧ f (hf.downTransform g hg a) = g (f a) :=
  (Classical.choose_spec (hf.down a (g (f a)) (hg (f a)))).1

/-- The canonical downward lift is monotone; uniqueness of interval lifts supplies
the comparison between its values, without any choice-coherence hypothesis. -/
theorem downTransform_monotone  (hmono : Monotone g) (hg : ∀ q, g q ≤ q) :
    Monotone (hf.downTransform g hg) := by
  intro a b hab
  have ha := hf.downTransform_spec g hg a
  have hb := hf.downTransform_spec g hg b
  obtain ⟨c, hxc, hcb, hfc⟩ := hf.exists_interval_lift (ha.1.trans hab) (g (f b))
    (ha.2 ▸ hmono (hf.mono hab)) (hg (f b))
  have he  := hf.down_inj hcb hb.1 (hfc.trans hb.2.symm)
  exact he ▸ hxc

/-- The lifted transformation lies below the identity, exactly as its original does. -/
abbrev downTransform_le   (a : P)  := (hf.downTransform_spec g hg a).1

end FiniteChains.Comb.IsPosetCover

