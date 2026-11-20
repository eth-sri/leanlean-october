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

/-- Within one sheet above a fixed vertex, the projection reflects the order. -/
theorem le_of_le_above {a b v : P} (ha : v ≤ a) (hb : v ≤ b) (h : f a ≤ f b) : a ≤ b := by
  obtain ⟨c, ⟨hac, hfc⟩, _⟩ := hf.up a (f b) h
  exact hf.up_inj (ha.trans hac) hb hfc ▸ hac

theorem le_of_le_below {a b v : P} (ha : a ≤ v) (hb : b ≤ v) (h : f a ≤ f b) : a ≤ b :=
  hf.dual.le_of_le_above hb ha h

/-- A comparability interval lifts inside the specified interval upstairs. -/
theorem exists_interval_lift {a b : P} (hab : a ≤ b) (q : Q)
    (haq : f a ≤ q) (hqb : q ≤ f b) :
    ∃ c : P, a ≤ c ∧ c ≤ b ∧ f c = q := by
  obtain ⟨c, ⟨hac, hfc⟩, _⟩ := hf.up a q haq
  exact ⟨c, hac, hf.le_of_le_above hac hab (hfc.symm ▸ hqb), hfc⟩

section Maps
variable {R : Type*}

noncomputable def lowerMapLift (a : R → P) (b : R → Q)
    (hab : ∀ x, b x ≤ f (a x)) (x : R) : P :=
  (hf.dual.liftUp (a x) (b x) (hab x)).1

theorem lowerMapLift_spec (a : R → P) (b : R → Q)
    (hab : ∀ x, b x ≤ f (a x)) (x : R) :
    hf.lowerMapLift a b hab x ≤ a x ∧ f (hf.lowerMapLift a b hab x) = b x :=
  (hf.dual.liftUp (a x) (b x) (hab x)).2

theorem lowerMapLift_monotone [Preorder R] (a : R → P) (b : R → Q)
    (ha : Monotone a) (hb : Monotone b) (hab : ∀ x, b x ≤ f (a x)) :
    Monotone (hf.lowerMapLift a b hab) := by
  intro x y hxy
  obtain ⟨hx, hfx⟩ := hf.lowerMapLift_spec a b hab x
  obtain ⟨hy, hfy⟩ := hf.lowerMapLift_spec a b hab y
  exact hf.le_of_le_below (hx.trans (ha hxy)) hy (hfx.symm ▸ hfy.symm ▸ hb hxy)

noncomputable def upperMapLift (a : R → P) (b : R → Q)
    (hab : ∀ x, f (a x) ≤ b x) : R → P := hf.dual.lowerMapLift a b hab

theorem upperMapLift_spec (a : R → P) (b : R → Q) (hab : ∀ x, f (a x) ≤ b x) (x : R) :
    a x ≤ hf.upperMapLift a b hab x ∧ f (hf.upperMapLift a b hab x) = b x :=
  hf.dual.lowerMapLift_spec a b hab x

theorem upperMapLift_monotone [Preorder R] (a : R → P) (b : R → Q)
    (ha : Monotone a) (hb : Monotone b) (hab : ∀ x, f (a x) ≤ b x) :
    Monotone (hf.upperMapLift a b hab) :=
  (hf.dual.lowerMapLift_monotone (R := Rᵒᵈ) a b ha.dual hb.dual hab).dual

end Maps

noncomputable def downTransform (g : Q → Q) (hg : ∀ q, g q ≤ q) : P → P :=
  hf.lowerMapLift id (g ∘ f) (fun a => hg (f a))

theorem downTransform_spec (g : Q → Q) (hg : ∀ q, g q ≤ q) (a : P) :
    hf.downTransform g hg a ≤ a ∧ f (hf.downTransform g hg a) = g (f a) :=
  hf.lowerMapLift_spec _ _ _ a

theorem downTransform_monotone (g : Q → Q) (hm : Monotone g) (hg : ∀ q, g q ≤ q) :
    Monotone (hf.downTransform g hg) :=
  hf.lowerMapLift_monotone _ _ monotone_id (hm.comp hf.mono) _

theorem downTransform_le (g : Q → Q) (hg : ∀ q, g q ≤ q) (a : P) :
    hf.downTransform g hg a ≤ a := (hf.downTransform_spec g hg a).1

end IsPosetCover
end FiniteChains.Comb
