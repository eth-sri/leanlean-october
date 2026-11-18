module

public import RequestProject.OrderPosetCovering

@[expose] public section

/-! Lifting an actual downward monotone homotopy through a poset covering. -/
namespace FiniteChains.Comb
universe u
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
  have hd : d = b := hf.up_inj (hac.trans hcd) hab hfd
  exact ⟨c, hac, hd ▸ hcd, hfc⟩

noncomputable def downTransform (g : Q → Q) (hg : ∀ q, g q ≤ q) (a : P) : P :=
  Classical.choose (hf.down a (g (f a)) (hg (f a)))

theorem downTransform_spec (g : Q → Q) (hg : ∀ q, g q ≤ q) (a : P) :
    hf.downTransform g hg a ≤ a ∧ f (hf.downTransform g hg a) = g (f a) :=
  (Classical.choose_spec (hf.down a (g (f a)) (hg (f a)))).1

/-- The canonical downward lift is monotone; uniqueness of interval lifts supplies
the comparison between its values, without any choice-coherence hypothesis. -/
theorem downTransform_monotone (g : Q → Q) (hmono : Monotone g) (hg : ∀ q, g q ≤ q) :
    Monotone (hf.downTransform g hg) := by
  intro a b hab
  have ha := hf.downTransform_spec g hg a
  have hb := hf.downTransform_spec g hg b
  obtain ⟨c, hxc, hcb, hfc⟩ := hf.exists_interval_lift (ha.1.trans hab) (g (f b))
    (ha.2 ▸ hmono (hf.mono hab)) (hg (f b))
  have he : c = hf.downTransform g hg b := hf.down_inj hcb hb.1 (hfc.trans hb.2.symm)
  exact he ▸ hxc

/-- The lifted transformation lies below the identity, exactly as its original does. -/
theorem downTransform_le (g : Q → Q) (hg : ∀ q, g q ≤ q) (a : P) :
    hf.downTransform g hg a ≤ a := (hf.downTransform_spec g hg a).1

end IsPosetCover
end FiniteChains.Comb
