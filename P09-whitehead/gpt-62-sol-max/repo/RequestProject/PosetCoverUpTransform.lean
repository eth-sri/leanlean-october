module

public import RequestProject.PosetCoverDownTransform

@[expose] public section

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}
namespace IsPosetCover
variable (hf : IsPosetCover f)
include hf

/-- The upward analogue of a downward order homotopy. -/
noncomputable def upTransform (g : Q → Q) (hg : ∀ q, q ≤ g q) : P → P :=
  hf.dual.downTransform g hg

theorem upTransform_spec (g : Q → Q) (hg : ∀ q, q ≤ g q) (a : P) :
    a ≤ hf.upTransform g hg a ∧ f (hf.upTransform g hg a) = g (f a) :=
  hf.dual.downTransform_spec g hg a

theorem upTransform_monotone (g : Q → Q) (hm : Monotone g) (hg : ∀ q, q ≤ g q) :
    Monotone (hf.upTransform g hg) := (hf.dual.downTransform_monotone g hm.dual hg).dual

theorem le_upTransform (g : Q → Q) (hg : ∀ q, q ≤ g q) (a : P) :
    a ≤ hf.upTransform g hg a := (hf.upTransform_spec g hg a).1

theorem upTransform_fixed (g : Q → Q) (hg : ∀ q, q ≤ g q) (a : P)
    (ha : g (f a) = f a) : hf.upTransform g hg a = a :=
  hf.up_inj (hf.le_upTransform g hg a) (le_refl a)
    ((hf.upTransform_spec g hg a).2.trans ha)

theorem strictMono : StrictMono f := by
  intro a b h
  apply lt_of_le_of_ne (hf.mono h.le)
  intro he
  have hb  := hf.up_inj h.le (le_refl a) he.symm
  exact (ne_of_lt h) hb.symm

end IsPosetCover
end FiniteChains.Comb
