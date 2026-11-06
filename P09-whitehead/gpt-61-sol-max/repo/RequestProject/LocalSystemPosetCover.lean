import Mathlib.Tactic

import RequestProject.OrderPosetCovering

/-! An actual set-valued local system on a poset gives a poset covering.
The construction retains the whole fibre; no choice of group coordinates
or covering classification theorem is needed. Unverified source. -/

noncomputable section

namespace FiniteChains.Comb.LocalSystem
open CategoryTheory
variable {P : Type u} [PartialOrder P] (F : P ⥤ Type u)

def Cover := Σ p : P, F.obj p

instance coverPartialOrder : PartialOrder (Cover F) where
  le x y := ∃ h : x.1 ≤ y.1, F.map (homOfLE h) x.2 = y.2
  le_refl x := ⟨le_rfl, by simp⟩
  le_trans x y z hxy hyz := by
    obtain ⟨hxy, hfx⟩ := hxy
    obtain ⟨hyz, hfy⟩ := hyz
    refine ⟨hxy.trans hyz, ?_⟩
    have hh := ConcreteCategory.congr_hom (F.map_comp (homOfLE hxy) (homOfLE hyz)) x.2
    dsimp at *
    rw [hh, hfx, hfy]
  le_antisymm x y hxy hyx := by
    rcases x with ⟨p, x⟩
    rcases y with ⟨q, y⟩
    obtain ⟨hpq, hx⟩ := hxy
    obtain ⟨hqp, _⟩ := hyx
    obtain rfl := le_antisymm hpq hqp
    have hxy : x = y := by simpa using hx
    cases hxy
    rfl

def projection : Cover F → P := Sigma.fst

theorem projection_monotone : Monotone (projection F) := fun _ _ h => h.choose

theorem projection_isPosetCover
    (hF : ∀ {p q : P} (h : p ≤ q), Function.Bijective (F.map (homOfLE h)))
    (hne : ∀ p, Nonempty (F.obj p)) : IsPosetCover (projection F) := by
  refine ⟨projection_monotone F, fun p => ⟨⟨p, Classical.choice (hne p)⟩, rfl⟩, ?_, ?_⟩
  · intro x q hxq
    refine ⟨⟨q, F.map (homOfLE hxq) x.2⟩, ⟨⟨hxq, rfl⟩, rfl⟩, ?_⟩
    rintro ⟨r, y⟩ ⟨⟨hxy, hy⟩, hr⟩
    change r = q at hr
    subst r
    exact congrArg (Sigma.mk q) hy.symm
  · intro x q hqx
    obtain ⟨v, hv⟩ := (hF hqx).2 x.2
    refine ⟨⟨q, v⟩, ⟨⟨hqx, hv⟩, rfl⟩, ?_⟩
    rintro ⟨r, y⟩ ⟨⟨hyx, hy⟩, hr⟩
    change r = q at hr
    subst r
    exact congrArg (Sigma.mk q) ((hF hqx).1 (hy.trans hv.symm))

end FiniteChains.Comb.LocalSystem
