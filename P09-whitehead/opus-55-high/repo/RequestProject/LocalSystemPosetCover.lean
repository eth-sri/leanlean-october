import RequestProject.OrderPosetCovering
import RequestProject.Tac


/-! An actual set-valued local system on a poset gives a poset covering.
The construction retains the whole fibre; no choice of group coordinates
or covering classification theorem is needed. Unverified source. -/

noncomputable section
bwd

namespace FiniteChains.Comb.LocalSystem
open CategoryTheory
universe u
variable {P : Type u} [PartialOrder P] (F : P ⥤ Type u)

def Cover := Σ p : P, F.obj p

instance coverPartialOrder : PartialOrder (Cover F) where
  le x y := ∃ h : x.1 ≤ y.1, F.map (homOfLE h) x.2 = y.2
  le_refl x := ⟨le_rfl, by simp⟩
  le_trans x y z hxy hyz := by
    cases' hxy with hxy hfx
    cases' hyz with hyz hfy
    refine ⟨hxy.trans hyz, ?_⟩
    have hh := ConcreteCategory.congr_hom (F.map_comp (homOfLE hxy) (homOfLE hyz)) x.2
    simp_all
  le_antisymm x y hxy hyx := by
    cases' x with p x
    cases' hxy with hpq hx
    cases' hyx with hqp _
    obtain rfl := le_antisymm hpq hqp
    simp_all

def projection : Cover F → P := Sigma.fst

theorem projection_monotone : Monotone (projection F) := fun _ _ h => h.choose

theorem projection_isPosetCover
    (hF : ∀ {p q} (h : p ≤ q), Function.Bijective (F.map (homOfLE h)))
    (hne : ∀ p, Nonempty (F.obj p)) : IsPosetCover (projection F) := by
  classical
  refine ⟨projection_monotone F, fun p => ⟨⟨p, Classical.choice (hne p)⟩, rfl⟩, ?_, ?_⟩
  · intro x q hxq
    refine ⟨⟨q, F.map (homOfLE hxq) x.2⟩, by tauto, ?_⟩
    rintro ⟨r, y⟩ ⟨⟨hxy, hy⟩, hr⟩
    change r = q at hr
    subst r
    tauto
  · intro x q hqx
    cases' (hF hqx).2 x.2 with v hv
    refine ⟨⟨q, v⟩, by tauto, ?_⟩
    rintro ⟨r, y⟩ ⟨⟨hyx, hy⟩, hr⟩
    change r = q at hr
    subst r
    exact congrArg _ ((hF hqx).1 (hy.trans hv.symm))
