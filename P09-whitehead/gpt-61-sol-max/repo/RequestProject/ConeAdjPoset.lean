import Mathlib.Tactic

import RequestProject.OrderCxMonodromy

/-!
# Adjoining cone points over prescribed subsets of a poset

The poset model of a presentation complex is obtained from the mapping cylinder of the
attaching circles by coning off each circle.  This file provides that last step in general
form: given a preorder `P`, an index type `T` of new points and, for every `t : T`, a set
`S t ⊆ P` of elements it is to dominate, the preorder

    `ConeAdj P T S = P ⊕ T`

puts `t` above the *down-closure* of `S t` and adds no other relation.  Taking the down-closure
is what makes transitivity automatic; on a down-closed `S t` — the only case used — it changes
nothing.

Also provided:

* `FiniteChains.Comb.OrdCocycle.comap` — a cocycle pulls back along a monotone map;
* `FiniteChains.Comb.OrdCocycle.coneAdj` — a cocycle on `P` extends to `ConeAdj P T S` as soon
  as for every cone point `t` a *trivialisation* `h t : P → G` of the cocycle on the elements
  under `t` is given; this is the exact point at which a relator of the presentation has to die
  in the receiving group;
* `FiniteChains.Comb.htpy_nil_of_pathIn_le` — the cone lemma in the form used later: a loop all
  of whose edges lie under a fixed element is null-homotopic.
-/

namespace FiniteChains.Comb



/-! ### Pullback of a cocycle -/

section

variable {P Q : Type u} [Preorder P] [Preorder Q] {G : Type v} [Group G]

/-- A cocycle pulls back along a monotone map. -/
def OrdCocycle.comap (f : P → Q) (hf : Monotone f) (c : OrdCocycle Q G) : OrdCocycle P G where
  val a b := c.val (f a) (f b)
  comp hab hbc := c.comp (hf hab) (hf hbc)



end

/-! ### The poset with adjoined cone points -/

variable {P : Type u} [Preorder P] {T : Type u}

/-- The preorder `P` with a new point above the down-closure of `S t` for every `t : T`. -/
def ConeAdj (_S : T → P → Prop)  := P ⊕ T

namespace ConeAdj

variable {S : T → P → Prop}

/-- The inclusion of the original poset. -/
def inc (p : P) : ConeAdj S := Sum.inl p

/-- The cone point attached to `t`. -/
def apex (t : T) : ConeAdj S := Sum.inr t

/-- The order of `ConeAdj`: the old order on `P`, a new point above everything below some
element of `S t`, and no relation between two distinct new points. -/
protected def le (S : T → P → Prop) : ConeAdj S → ConeAdj S → Prop
  | Sum.inl p, Sum.inl q => p ≤ q
  | Sum.inl p, Sum.inr t => ∃ r, S t r ∧ p ≤ r
  | Sum.inr _, Sum.inl _ => False
  | Sum.inr t, Sum.inr t' => t = t'

instance : Preorder (ConeAdj S) where
  le := ConeAdj.le S
  le_refl p := by
    aesop (add simp [FiniteChains.Comb.ConeAdj.le])
  le_trans p q r hpq hqr := by
    cases p with
    | inl x =>
        cases q with
        | inl y =>
            cases r <;> grind [FiniteChains.Comb.ConeAdj.le]
        | inr t =>
            aesop (add simp [FiniteChains.Comb.ConeAdj.le])
    | inr t =>
        aesop (add simp [FiniteChains.Comb.ConeAdj.le])







theorem inc_monotone : Monotone (inc : P → ConeAdj S) := fun _ _ h => h

/-- The defining relation: an element of `S t` lies under the cone point `t`. -/
theorem inc_le_apex_of_mem {p : P} {t : T} (h : S t p) : (inc p : ConeAdj S) ≤ apex t :=
  ⟨p, h, le_refl p⟩

omit [Preorder P] in
theorem inc_injective : Function.Injective (inc : P → ConeAdj S) := fun _ _ h => Sum.inl_injective h

end ConeAdj

/-! ### Extending a cocycle over the cone points -/

variable {G : Type v} [Group G] {S : T → P → Prop}

/-- The extension of a cocycle over the adjoined cone points, given a trivialisation `h t` of
the cocycle under each cone point. -/
def OrdCocycle.coneAdjVal (c : OrdCocycle P G) (h : T → P → G) :
    ConeAdj S → ConeAdj S → G
  | Sum.inl p, Sum.inl q => c.val p q
  | Sum.inl p, Sum.inr t => h t p
  | Sum.inr _, Sum.inl _ => 1
  | Sum.inr _, Sum.inr _ => 1

/-- **Extension of a cocycle over the cone points.**  The hypothesis is that `h t` trivialises
the cocycle on the elements lying under the cone point `t`. -/
def OrdCocycle.coneAdj (c : OrdCocycle P G) (h : T → P → G)
    (hh : ∀ (t : T) {p q : P}, p ≤ q → (ConeAdj.inc q : ConeAdj S) ≤ ConeAdj.apex t →
      c.val p q * h t q = h t p) :
    OrdCocycle (ConeAdj S) G where
  val := c.coneAdjVal h
  comp := by
    rintro (p | t) (q | t') (r | t'') hpq hqr
    · exact c.comp hpq hqr
    · exact hh t'' hpq hqr
    · exact absurd hqr (fun x => x)
    · cases (hqr : t' = t'') <;> aesop (add simp [mul_one])
    · exact absurd hpq (fun x => x)
    · exact absurd hpq (fun x => x)
    · exact absurd hqr (fun x => x)
    · show (1 : G) * 1 = 1
      rw [mul_one]





/-! ### The cone lemma in the form used below -/

/-- **A loop all of whose edges lie under a fixed element is null-homotopic.** -/
abbrev htpy_nil_of_pathIn_le.{eta_u0} :=
  fun {Pp : Type eta_u0} [inst : Preorder.{eta_u0} Pp] (d : Pp) =>
    @FiniteChains.Comb.htpy_nil_of_pathIn_le_top.{eta_u0} Pp inst
      (fun (x : Pp) => @LE.le.{eta_u0} Pp (@Preorder.toLE.{eta_u0} Pp inst) x d) d (@le_refl.{eta_u0} Pp inst d)
      fun (x : Pp) (hx : @LE.le.{eta_u0} Pp (@Preorder.toLE.{eta_u0} Pp inst) x d) => hx

end FiniteChains.Comb

