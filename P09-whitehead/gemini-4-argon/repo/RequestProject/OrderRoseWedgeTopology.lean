module

public import RequestProject.PresValidFinite
public import RequestProject.OrderNerveFiniteCoordinates
public import RequestProject.OrderNerveRealizationMapCoordinates

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.PresModel
open Comb CategoryTheory Simplicial
open scoped Classical

variable {α : Type}

def roseCopy (a : α) : Rose PUnit.{1} ↪o Rose α where
  toFun
    | .base => .base
    | .mid _ => .mid a
    | .edg _ b => .edg a b
  inj' p q h := by cases p <;> cases q <;> simp_all
  map_rel_iff' := fun {p q} => by
    change Rose.le _ _ ↔ Rose.le p q
    cases p <;> cases q <;> simp [Rose.le, RelEmbedding.coe_mk]

def roseCopyRealization (a : α) : C(orderNerveRealization (Rose PUnit),
    orderNerveRealization (Rose α)) :=
  (orderNerveRealizationMap (roseCopy a) (roseCopy a).monotone).hom

def orderRoseBase (α : Type) : orderNerveRealization (Rose α) :=
  orderNerveRealizationVertex Rose.base

theorem realizedMap_vertex {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (f : P → Q) (hf : Monotone f) (p : P) :
    orderNerveRealizationMap f hf (orderNerveRealizationVertex p) =
      orderNerveRealizationVertex (f p) :=
  congrArg (fun k : TopCat.of (SimplexCategory.toTop.obj ⦋0⦌) ⟶ orderNerveRealization Q => k default)
    (orderNerveRealizationSimplex_natural f hf (ComposableArrows.mk₀ p))

@[simp] theorem roseCopyRealization_base (a : α) :
    roseCopyRealization a (orderRoseBase PUnit) = orderRoseBase α :=
  realizedMap_vertex (roseCopy a) (roseCopy a).monotone Rose.base

theorem roseCopyRealization_injective (a : α) : Function.Injective (roseCopyRealization a) :=
  orderNerveRealizationMap_injective (roseCopy a) (roseCopy a).monotone (roseCopy a).injective

theorem roseSimplex_cases {n : SimplexCategory}
    (s : (nerve (Rose α)).obj (Opposite.op n)) :
    (∀ i, s.obj i = .base) ∨
      ∃ (a : α) (t : (nerve (Rose PUnit)).obj (Opposite.op n)),
        (nerveMap (roseCopy a).monotone.functor).app _ t = s := by
  have hlift (a : α) (hs : ∀ i, ∃ p, roseCopy a p = s.obj i) :
      ∃ t : (nerve (Rose PUnit)).obj (Opposite.op n),
        (nerveMap (roseCopy a).monotone.functor).app _ t = s := by
    choose p hp using hs
    exact ⟨(show Monotone p from fun i j hij =>
      (roseCopy a).le_iff_le.mp (by rw [hp i, hp j]; exact leOfHom (s.map (homOfLE hij)))).functor,
      CategoryTheory.Functor.ext hp⟩
  let last : Fin (n.len + 1) := Fin.last n.len
  have hle (i : Fin (n.len + 1)) : s.obj i ≤ s.obj last :=
    leOfHom (s.map (homOfLE (Fin.le_last i)))
  cases he : s.obj last with
  | base =>
      refine .inl fun i => ?_
      have hi := he ▸ hle i
      generalize s.obj i = p at hi
      cases p <;> [rfl; exact hi.elim; exact hi.elim]
  | mid a =>
      refine .inr ⟨a, hlift a fun i => ?_⟩
      have hi := he ▸ hle i
      generalize s.obj i = p at hi
      cases p with
      | base | edg _ _ => exact hi.elim
      | mid b => exact ⟨.mid PUnit.unit, congrArg Rose.mid hi.symm⟩
  | edg a b =>
      refine .inr ⟨a, hlift a fun i => ?_⟩
      have hi := he ▸ hle i
      generalize s.obj i = p at hi
      cases p with
      | base => exact ⟨.base, rfl⟩
      | mid c => exact ⟨.mid PUnit.unit, congrArg Rose.mid hi.symm⟩
      | edg c d => exact ⟨.edg PUnit.unit d, congrArg (Rose.edg · d) hi.1.symm⟩

theorem constantSimplex_vertex {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n)) (p : P)
    (hs : ∀ i, s.obj i = p) (z : SimplexCategory.toTop.obj n) :
    orderNerveRealizationSimplex P s z = orderNerveRealizationVertex p := by
  apply orderNerveRealizationCoordinates_injective P; funext q
  rw [orderNerveRealizationCoordinates_simplex, orderNerveRealizationCoordinates_vertex]
  change (∑ i, z.down.weights i * (if s.obj i = q then 1 else 0)) = _
  simp only [hs, ← Finset.sum_mul, z.down.total_of_fintype, one_mul]

theorem orderRoseRealization_continuous_iff {X : Type*} [TopologicalSpace X]
    (f : orderNerveRealization (Rose α) → X) :
    Continuous f ↔ ∀ a, Continuous (f ∘ roseCopyRealization a) :=
  ⟨fun hf a => hf.comp (roseCopyRealization a).continuous, fun hf =>
    (orderNerveRealization_continuous_iff (Rose α) f).mpr fun n s => by
      rcases roseSimplex_cases s with hs | ⟨a, t, ht⟩
      · rw [show f ∘ orderNerveRealizationSimplex (Rose α) s = fun _ => f (orderRoseBase α) from
          funext fun z => congrArg f (constantSimplex_vertex s .base hs z)]
        exact continuous_const
      · rw [← show roseCopyRealization a ∘ orderNerveRealizationSimplex (Rose PUnit) t =
            orderNerveRealizationSimplex (Rose α) s from
          funext fun z => by
            simpa only [ht, roseCopyRealization, TopCat.comp_app, Function.comp_apply] using
              congrArg (· z) (orderNerveRealizationSimplex_natural (roseCopy a) (roseCopy a).monotone t)]
        exact (hf a).comp (orderNerveRealizationSimplex (Rose PUnit) t).hom.continuous⟩

theorem orderRoseRealization_cases (x : orderNerveRealization (Rose α)) :
    x = orderRoseBase α ∨ ∃ a u, roseCopyRealization a u = x := by
  obtain ⟨n, s, z, rfl⟩ := orderNerveRealizationSimplex_jointly_surjective (Rose α) x
  rcases roseSimplex_cases s with hs | ⟨a, t, ht⟩
  · exact .inl (constantSimplex_vertex s .base hs z)
  · exact .inr ⟨a, orderNerveRealizationSimplex (Rose PUnit) t z, by
      simpa only [ht, roseCopyRealization, TopCat.comp_app, Function.comp_apply] using
        congrArg (· z) (orderNerveRealizationSimplex_natural (roseCopy a) (roseCopy a).monotone t)⟩

theorem roseCopyRealization_intersection {a b : α} (hab : a ≠ b)
    (x y : orderNerveRealization (Rose PUnit))
    (h : roseCopyRealization a x = roseCopyRealization b y) :
    x = orderRoseBase PUnit ∧ y = orderRoseBase PUnit := by
  have oneSide {a b : α} (hab : a ≠ b) (x y : orderNerveRealization (Rose PUnit))
      (h : roseCopyRealization a x = roseCopyRealization b y) :
      x = orderRoseBase PUnit := by
    have hx (q : Rose PUnit) (hq : q ≠ .base) :
        orderNerveRealizationCoordinates (Rose PUnit) x q = 0 := by
      have hc := congrArg (fun z => orderNerveRealizationCoordinates (Rose α) z (roseCopy a q)) h
      dsimp only [roseCopyRealization] at hc
      rw [orderNerveRealizationCoordinates_map_injective (roseCopy a)
        (roseCopy a).monotone (roseCopy a).injective] at hc
      exact hc.trans (orderNerveRealizationCoordinates_map_outside
        (roseCopy b) (roseCopy b).monotone y (roseCopy a q) fun ⟨p, hp⟩ => by
          cases q <;> cases p <;> simp_all [roseCopy, RelEmbedding.coe_mk])
    letI : Fintype (Rose PUnit) := Fintype.ofFinite _
    have hb : orderNerveRealizationCoordinates (Rose PUnit) x .base = 1 :=
      (Fintype.sum_eq_single Rose.base hx).symm.trans (orderNerveRealizationCoordinates_sum x)
    apply orderNerveRealizationCoordinates_injective (Rose PUnit); funext q
    rw [orderRoseBase, orderNerveRealizationCoordinates_vertex]
    by_cases hq : q = .base
    · subst q; simpa using hb
    · simp only [if_neg (Ne.symm hq), hx q hq]
  exact ⟨oneSide hab x y h, oneSide hab.symm y x h.symm⟩

end FiniteChains.PresModel
