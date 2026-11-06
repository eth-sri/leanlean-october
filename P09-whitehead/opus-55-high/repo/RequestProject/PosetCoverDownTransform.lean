import RequestProject.OrderPosetCovering


/-! Lifting an actual downward monotone homotopy through a poset covering. -/
namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}

namespace IsPosetCover
variable (hf : IsPosetCover f)
include hf

/-- A comparability interval lifts inside the specified interval upstairs. -/
theorem exists_interval_lift (hab : a ≤ b) q
    (haq : f a ≤ q) (hqb : q ≤ f b) :
    ∃ c, a ≤ c ∧ c ≤ b ∧ f c = q := by
  obtain ⟨c, ⟨hac, hfc⟩, _⟩ := hf.up a q haq
  obtain ⟨d, ⟨hcd, hfd⟩, _⟩ := hf.up c _ (hfc ▸ hqb)
  have hd := hf.up_inj (hac.trans hcd) hab hfd
  grind

noncomputable def downTransform (g : Q → Q) (hg : ∀ q, g q ≤ q) (a : P) :=
  Classical.choose (hf.down a (g (f a)) (by simp_all))

theorem downTransform_spec g hg a :
    hf.downTransform g hg a ≤ a ∧ f (hf.downTransform g hg a) = g (f a) :=
  (Classical.choose_spec (hf.down a _ (by simp_all))).1

/-- The canonical downward lift is monotone; uniqueness of interval lifts supplies
the comparison between its values, without any choice-coherence hypothesis. -/
theorem downTransform_monotone g (hmono : Monotone g) hg :
    Monotone (hf.downTransform g hg) := by
  intro a b hab
  have ha := hf.downTransform_spec g hg a
  have hb := hf.downTransform_spec g hg b
  obtain ⟨c, hxc, hcb, hfc⟩ := hf.exists_interval_lift (ha.1.trans hab) _
    (ha.2 ▸ hmono (hf.mono hab)) (by simp_all)
  have he := hf.down_inj hcb hb.1 (hfc.trans hb.2.symm)
  simp_all

/-- The lifted transformation lies below the identity, exactly as its original does. -/
theorem downTransform_le g hg a :
    hf.downTransform g hg a ≤ a := (hf.downTransform_spec g hg a).1
