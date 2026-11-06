import RequestProject.PresPosetAlpha


/-!
# The reading homomorphism of the poset model, and injectivity of the comparison

This file constructs the second half of the marked comparison of a presentation with the poset
model of its presentation complex: a **reading homomorphism**

    `reading : π₁(orderCx (PresPos w), ptBase) →* G`

for any group `G` with a chosen image `gen i` of every generator, provided every relator word
evaluates to `1` in `G`.  It is the monodromy (`FiniteChains.Comb.OrdCocycle.monodromy`) of an
explicit cocycle on the model:

* on the rose, the cocycle reads the generator off the second half of its subdivided loop;
* on the mapping cylinder it is pulled back along the retraction onto the rose;
* over the cone point of a relator it is trivialised by the prefix products of the relator word,
  which is consistent exactly because the whole word evaluates to `1`.

Composed with the comparison homomorphism of `RequestProject/PresPosetAlpha.lean` for
`G = PresGroup ρ` this gives a left inverse of `alphaHom`, hence **`alphaHom` is injective**:
the presentation group embeds in the fundamental group of the model, marked by the generators.
-/

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel

open Comb


variable {α J : Type u} (w : J → List (α × Bool)) {G : Type v} [Group G] (gen : α → G)

/-! ### The values of letters and words -/

/-- The value of a letter. -/
def letterVal (p : α × Bool) := if p.2 then gen p.1 else (gen p.1)⁻¹

/-- The value of a word. -/
def wordVal (l : List (α × Bool)) := FreeGroup.lift gen (FreeGroup.mk l)

@[simp] theorem wordVal_nil : wordVal (gen := gen) [] = 1 := by
  rfl

theorem wordVal_append l l' :
    wordVal gen (l ++ l') = wordVal gen l * wordVal gen l' := by
  simp [wordVal, map_mul]

theorem wordVal_single p : wordVal gen [p] = letterVal gen p := by
  simp [wordVal, letterVal, FreeGroup.lift_mk]

/-! ### The cocycle of the rose -/

/-- The cocycle of the subdivided rose: the generator is read off the second half of its loop. -/
def roseVal : Rose α → Rose α → G
  | Rose.base, Rose.edg i b => if b then (gen i)⁻¹ else 1
  | _, _ => 1

@[simp] theorem roseVal_base_edg i b :
    roseVal gen Rose.base (Rose.edg i b) = if b then (gen i)⁻¹ else 1 := rfl

@[simp] theorem roseVal_mid_edg i i' b :
    roseVal gen (Rose.mid i) (Rose.edg i' b) = 1 := rfl

@[simp] theorem roseVal_self x : roseVal gen x x = 1 := by
  cases x <;> rfl

/-- The cocycle of the rose. -/
def roseCoc : OrdCocycle (Rose α) G where
  val := roseVal gen
  comp := by
    intro a b c hab hbc
    cases b with
    | base =>
        cases a with
        | base => simp
        | mid i => exact hab.elim
        | edg i b => exact hab.elim
    | mid i =>
        cases a with
        | base => exact hab.elim
        | mid i' =>
            have hii : i' = i := hab
            simp_all
        | edg i' b => exact hab.elim
    | edg i bb =>
        cases c with
        | base => exact hbc.elim
        | mid i' => exact hbc.elim
        | edg i' b' =>
            cases' hbc with hi hb
            simp_all

/-- The cocycle of the mapping cylinder: the cocycle of the rose read through the retraction. -/
def cylCoc : OrdCocycle (CylBase w) G :=
  (roseCoc gen).comap _ (cylRetr_monotone _)

/-! ### The trivialisation over a two-cell -/

/-- The prefix product of the first `k` letters of the relator `j`. -/
def prefixVal (j : J) (k : ℕ) := wordVal gen ((w j).take k)

@[simp] theorem prefixVal_zero j : prefixVal w gen j 0 = 1 := by
  rfl

theorem prefixVal_succ j {k} hk :
    prefixVal w gen j (k + 1) = prefixVal w gen j k * letterVal gen (w j)[k] := by
  have hsplit : (w j).take (k + 1) = (w j).take k ++ [(w j)[k]] := by
    simp
  rw [prefixVal, prefixVal, hsplit, wordVal_append, wordVal_single]

/-- The value of the trivialisation at a point of a circle. -/
def trivVal (j : J) (k : ℕ) (t : CPos) : G :=
  match t with
  | CPos.cor => (prefixVal w gen j k)⁻¹
  | _ => (roseVal gen Rose.base (aFun w (j, k, CPos.cedgL)))⁻¹ * (prefixVal w gen j k)⁻¹

/-- The trivialisation of the cocycle under the cone point of the relator `j`. -/
def trivFun (_j : J) : CylBase w → G :=
  Sum.elim (fun _ => 1) (fun x => trivVal w gen x.1 x.2.1 x.2.2)

/-- The prefix product at the cyclic successor of a position: the relator word closes up
because it evaluates to `1`. -/
theorem prefixVal_csucc (hrel : ∀ j, wordVal gen (w j) = 1) j {k}
    (hk : k < (w j).length) :
    prefixVal w gen j (TCirc.csucc w j k) = prefixVal w gen j (k + 1) := by
  rcases lt_or_eq_of_le (Nat.succ_le_of_lt hk) with hlt | heq
  · rw [TCirc.csucc, Nat.mod_eq_of_lt hlt]
  · have hlen : (w j).length = k + 1 := heq.symm
    have h0 : TCirc.csucc w j k = 0 := by rw [TCirc.csucc, hlen, Nat.mod_self]
    rw [h0, prefixVal_zero, prefixVal, ← hlen, List.take_length, hrel j]

/-- **The trivialisation is parallel for the cocycle**: this is the cocycle identity for a
comparability of the attaching circle and the cone point over it. -/
theorem trivVal_step (hrel : ∀ j, wordVal gen (w j) = 1) {x y} (h : x ≤ y) :
    roseVal gen (aFun w x) (aFun w y) * trivVal w gen y.1 y.2.1 y.2.2
      = trivVal w gen x.1 x.2.1 x.2.2 := by
  rcases h with rfl | hlt
  · simp
  obtain ⟨j, k, t⟩ := x
  obtain ⟨j', k', t'⟩ := y
  obtain ⟨hj, hk', hcase⟩ := hlt
  subst hj
  cases' exists_get_of_lt w hk' with p hp
  have hL := aFun_cedgL_of_get w hp
  have hR := aFun_cedgR_of_get w hp
  have hM := aFun_cmid_of_get w hp
  rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · -- corner ≤ left half
    show roseVal gen Rose.base (aFun w (j, k, CPos.cedgL))
        * ((roseVal gen Rose.base (aFun w (j, k, CPos.cedgL)))⁻¹
          * (prefixVal w gen j k)⁻¹) = (prefixVal w gen j k)⁻¹
    simp
  · -- midpoint ≤ left half
    aesop
  · -- midpoint ≤ right half
    aesop
  · -- the corner in front of the next letter ≤ right half: here the letter is read
    show roseVal gen Rose.base (aFun w (j, k', CPos.cedgR))
        * ((roseVal gen Rose.base (aFun w (j, k', CPos.cedgL)))⁻¹
          * (prefixVal w gen j k')⁻¹) = (prefixVal w gen j (TCirc.csucc w j k'))⁻¹
    rw [prefixVal_csucc w gen hrel j hk', prefixVal_succ w gen j hk', hL, hR,
      roseVal_base_edg, roseVal_base_edg]
    have hpk : (w j)[k'] = p := by
      simp_all
    rw [hpk, letterVal]
    aesop

/-- **The cocycle of the model.**  The hypothesis is that every relator word evaluates to `1`,
which is what makes the trivialisation over a two-cell consistent. -/
def presCoc (hrel : ∀ j, wordVal gen (w j) = 1) : OrdCocycle (PresPos w) G :=
  (cylCoc w gen).coneAdj (trivFun w gen) (by
    intro t p q hpq hq
    obtain ⟨r, hr, hqr⟩ := hq
    obtain ⟨k0, t0, hk0, rfl⟩ := hr
    -- the elements under a cone point are the points of its circle
    cases q with
    | inl y => exact hqr.elim
    | inr y =>
        cases p with
        | inl x => exact hpq.elim
        | inr x => exact trivVal_step w gen hrel hpq)

/-! ### The reading homomorphism -/

/-- **The reading homomorphism** of the model: the monodromy of the cocycle. -/
def reading (hrel : ∀ j, wordVal gen (w j) = 1) :=
  (presCoc w gen hrel).monodromy (ptBase w)

/-- **The reading homomorphism reads the generators.** -/
theorem reading_genClass hrel i :
    reading w gen hrel (genClass w i) = gen i := by
  show roseVal gen Rose.base (Rose.edg i false) *
      ((roseVal gen (Rose.mid i) (Rose.edg i false))⁻¹ *
        (roseVal gen (Rose.mid i) (Rose.edg i true) *
          ((roseVal gen Rose.base (Rose.edg i true))⁻¹ * 1))) = gen i
  simp

/-! ### Injectivity of the comparison -/
