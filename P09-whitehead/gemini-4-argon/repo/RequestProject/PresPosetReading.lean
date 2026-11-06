module

public import RequestProject.PresPosetAlpha

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.PresModel

open Comb

universe u v

variable {α J : Type u} (w : J → List (α × Bool)) {G : Type v} [Group G] (gen : α → G)

def letterVal (p : α × Bool) : G := if p.2 then gen p.1 else (gen p.1)⁻¹

def wordVal (l : List (α × Bool)) : G := FreeGroup.lift gen (FreeGroup.mk l)

def roseVal : Rose α → Rose α → G
  | Rose.base, Rose.edg i b => if b then (gen i)⁻¹ else 1
  | _, _ => 1

@[simp] theorem roseVal_base_edg (i : α) (b : Bool) :
    roseVal gen Rose.base (Rose.edg i b) = if b then (gen i)⁻¹ else 1 := rfl

@[simp] theorem roseVal_mid_edg (i i' : α) (b : Bool) :
    roseVal gen (Rose.mid i) (Rose.edg i' b) = 1 := rfl

@[simp] theorem roseVal_self (x : Rose α) : roseVal gen x x = 1 := by
  cases x <;> rfl

def roseCoc : OrdCocycle (Rose α) G where
  val := roseVal gen
  comp := by
    intro a b c hab hbc
    cases b with
    | base => cases a <;> [rw [roseVal_self, one_mul]; exact hab.elim; exact hab.elim]
    | mid i =>
        cases a with
        | base | edg _ _ => exact hab.elim
        | mid i' => cases (hab : i' = i); rw [roseVal_self, one_mul]
    | edg i bb =>
        cases c with
        | base | mid _ => exact hbc.elim
        | edg i' b' => rcases hbc with ⟨rfl, rfl⟩; rw [roseVal_self, mul_one]

def prefixVal (j : J) (k : ℕ) : G := wordVal gen ((w j).take k)

def trivVal (j : J) (k : ℕ) (t : CPos) : G :=
  match t with
  | CPos.cor => (prefixVal w gen j k)⁻¹
  | _ => (roseVal gen Rose.base (aFun w (j, k, CPos.cedgL)))⁻¹ * (prefixVal w gen j k)⁻¹

def trivFun (_j : J) : CylBase w → G :=
  Sum.elim (fun _ => 1) (fun x => trivVal w gen x.1 x.2.1 x.2.2)

theorem trivVal_step (hrel : ∀ j : J, wordVal gen (w j) = 1) {x y : TCirc w} (h : x ≤ y) :
    roseVal gen (aFun w x) (aFun w y) * trivVal w gen y.1 y.2.1 y.2.2
      = trivVal w gen x.1 x.2.1 x.2.2 := by
  rcases h with rfl | hlt
  · rw [roseVal_self, one_mul]
  rcases x with ⟨j, k, t⟩; rcases y with ⟨j', k', t'⟩
  rcases hlt with ⟨rfl, hk', hcase⟩
  obtain ⟨p, hp⟩ := exists_get_of_lt w hk'
  have hL := aFun_cedgL_of_get w hp
  have hR := aFun_cedgR_of_get w hp
  have hM := aFun_cmid_of_get w hp
  rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · show roseVal gen Rose.base (aFun w (j, k, CPos.cedgL))
        * ((roseVal gen Rose.base (aFun w (j, k, CPos.cedgL)))⁻¹
          * (prefixVal w gen j k)⁻¹) = (prefixVal w gen j k)⁻¹
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  · show roseVal gen (aFun w (j, k, CPos.cmid)) (aFun w (j, k, CPos.cedgL))
        * trivVal w gen j k CPos.cedgL = trivVal w gen j k CPos.cmid
    rw [hM, hL, roseVal_mid_edg, one_mul]; rfl
  · show roseVal gen (aFun w (j, k, CPos.cmid)) (aFun w (j, k, CPos.cedgR))
        * trivVal w gen j k CPos.cedgR = trivVal w gen j k CPos.cmid
    rw [hM, hR, roseVal_mid_edg, one_mul]; rfl
  · show roseVal gen Rose.base (aFun w (j, k', CPos.cedgR))
        * ((roseVal gen Rose.base (aFun w (j, k', CPos.cedgL)))⁻¹
          * (prefixVal w gen j k')⁻¹) = (prefixVal w gen j (TCirc.csucc w j k'))⁻¹
    have hcsucc : prefixVal w gen j (TCirc.csucc w j k') = prefixVal w gen j (k' + 1) := by
      rcases lt_or_eq_of_le (Nat.succ_le_of_lt hk') with hlt | heq
      · rw [TCirc.csucc, Nat.mod_eq_of_lt hlt]
      · have hlen : (w j).length = k' + 1 := heq.symm
        rw [show TCirc.csucc w j k' = 0 by rw [TCirc.csucc, hlen, Nat.mod_self],
          show prefixVal w gen j 0 = 1 by simp [prefixVal, wordVal],
          prefixVal, ← hlen, List.take_length, hrel j]
    have hsucc : prefixVal w gen j (k' + 1) = prefixVal w gen j k' * letterVal gen (w j)[k'] := by
      rw [prefixVal, prefixVal, show (w j).take (k' + 1) = (w j).take k' ++ [(w j)[k']] by
        rw [List.take_add_one, List.getElem?_eq_getElem hk']; rfl,
        wordVal, wordVal, ← FreeGroup.mul_mk, map_mul]
      congr 1
      rcases (w j)[k'] with ⟨i, _ | _⟩ <;> simp [letterVal, FreeGroup.lift_mk]
    have hpk : (w j)[k'] = p := Option.some.inj ((List.getElem?_eq_getElem hk').symm.trans hp)
    rw [hcsucc, hsucc, hL, hR, roseVal_base_edg, roseVal_base_edg, hpk, letterVal]
    cases p.2 <;> simp [mul_inv_rev]

def presCoc (hrel : ∀ j : J, wordVal gen (w j) = 1) : OrdCocycle (PresPos w) G :=
  ((roseCoc gen).comap (cylRetr (aHom w)) (cylRetr_monotone (aHom w))).coneAdj (trivFun w gen)
    fun _ p q hpq ⟨_, ⟨_, _, _, rfl⟩, hqr⟩ => by
      cases q with
      | inl _ => exact hqr.elim
      | inr _ =>
          cases p with
          | inl _ => exact hpq.elim
          | inr _ => exact trivVal_step w gen hrel hpq

def reading (hrel : ∀ j : J, wordVal gen (w j) = 1) :
    Pi1 (orderCx (PresPos w)) (ptBase w) →* G :=
  (presCoc w gen hrel).monodromy (ptBase w)

theorem reading_genClass (hrel : ∀ j : J, wordVal gen (w j) = 1) (i : α) :
    reading w gen hrel (genClass w i) = gen i := by
  show roseVal gen Rose.base (Rose.edg i false) *
      ((roseVal gen (Rose.mid i) (Rose.edg i false))⁻¹ *
        (roseVal gen (Rose.mid i) (Rose.edg i true) *
          ((roseVal gen Rose.base (Rose.edg i true))⁻¹ * 1))) = gen i
  simp

end FiniteChains.PresModel
