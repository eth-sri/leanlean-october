import Mathlib.Tactic

import RequestProject.PresPosetPartialOrder
import RequestProject.OrderThreeNormalization

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel

variable {α J : Type u}

def roseDimension : Rose α → ℕ
  | Rose.base => 1
  | Rose.mid _ => 1
  | Rose.edg _ _ => 2

theorem roseDimension_monotone : Monotone (roseDimension (α := α)) := by
  intro x y h
  change Rose.le x y at h
  cases x <;> cases y <;> simp_all [Rose.le, roseDimension]

theorem roseDimension_strictMono : StrictMono (roseDimension (α := α)) := by
  intro x y h
  
  have hl := le_of_lt h
  change Rose.le x y at hl
  cases x <;> cases y <;> simp_all [Rose.le, roseDimension]

variable (w : J → List (α × Bool))
  (x : TCirc w)
noncomputable def circleDimension   : ℕ := if x.2.1 < (w x.1).length ∧
    (x.2.2 = CPos.cedgL ∨ x.2.2 = CPos.cedgR) then 1 else 0

theorem circleDimension_le_one   :
    circleDimension w x ≤ 1 := by
  unfold circleDimension
  split <;> omega

theorem circleDimension_strictMono  :
    StrictMono (circleDimension w) := by
  intro x y h
  have hn := ne_of_lt h
  have hl := le_of_lt h
  
  rcases hl with he | hl
  · exact (hn he).elim
  obtain ⟨j, k, t⟩ := x
  obtain ⟨j', k', t'⟩ := y
  obtain ⟨hj, hk, htags⟩ := hl
  subst j'
  rcases htags with ⟨ht, ht', _⟩ | ⟨ht, ht', _⟩ | ⟨ht, ht', _⟩ | ⟨ht, ht', _⟩ <;>
    subst t <;> subst t' <;> simp [circleDimension, hk]

theorem circleDimension_lt_aFun   :
    circleDimension w x < roseDimension (aFun w x) := by
  classical
  obtain ⟨j, k, t⟩ := x
  by_cases hk : k < (w j).length
  · aesop (add simp [circleDimension, aFun, roseDimension])
  · 
    cases t <;> simp_all [circleDimension, aFun, roseDimension]

noncomputable def cylinderDimension  : CylBase w → ℕ :=
  Sum.elim roseDimension (circleDimension w)

theorem cylinderDimension_strictMono  :
    StrictMono (cylinderDimension w) := by
  intro p q h
  have hn := ne_of_lt h
  have hl := le_of_lt h
  cases p with
  | inl p =>
    cases q with
    | inl q =>
      solve_by_elim [FiniteChains.PresModel.roseDimension_strictMono]
    | inr q => exact hl.elim
  | inr p =>
    cases q with
    | inl q =>
      exact (circleDimension_lt_aFun w p).trans_le (roseDimension_monotone hl)
    | inr q =>
      solve_by_elim [FiniteChains.PresModel.circleDimension_strictMono]

noncomputable def presPosDimension  : PresPos w → ℕ :=
  Sum.elim (cylinderDimension w) (fun _ => 2)

theorem presPosDimension_le_two  (p : PresPos w) :
    presPosDimension w p ≤ 2 := by
  cases p with
  | inl p =>
    cases p with
    | inl r => cases r <;> simp [presPosDimension, cylinderDimension, roseDimension]
    | inr c => solve_by_elim [FiniteChains.PresModel.circleDimension_le_one]
  | inr j => exact le_refl _

theorem presPosDimension_strictMono  :
    StrictMono (presPosDimension w) := by
  intro p q h
  have hn := ne_of_lt h
  have hl := le_of_lt h
  cases p with
  | inl p =>
    cases q with
    | inl q =>
      solve_by_elim [FiniteChains.PresModel.cylinderDimension_strictMono]
    | inr j =>
      obtain ⟨r, hr, hpr⟩ := hl
      obtain ⟨k, t, _, he⟩ := hr
      subst r
      have hm := (cylinderDimension_strictMono w).monotone hpr
      have hb := circleDimension_le_one w (TCirc.pt w j k t)
      change cylinderDimension w p < 2
      change cylinderDimension w p ≤ circleDimension w (TCirc.pt w j k t) at hm
      omega
  | inr j =>
    cases q with
    | inl q => exact hl.elim
    | inr k => exact (hn (congrArg Sum.inr hl)).elim

end FiniteChains.PresModel
