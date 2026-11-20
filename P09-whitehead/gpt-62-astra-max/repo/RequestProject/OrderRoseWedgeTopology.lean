module

public import RequestProject.PresValidFinite
public import RequestProject.OrderNerveFiniteCoordinates


@[expose] public section

/-! The weak topology and exact intersection rule of an arbitrary realized
rose. Every simplex lies in one four-vertex circle or at the common vertex.
There is no finiteness assumption on the set of generators. -/

noncomputable section

namespace FiniteChains.PresModel
open Comb CategoryTheory Simplicial
open scoped Classical

variable {α : Type}

variable (a : α)

def roseCopy : Rose PUnit.{1} ↪o Rose α where
  toFun
    | .base => .base
    | .mid _ => .mid a
    | .edg _ b => .edg a b
  inj' := by
    intro p q h
    grind
  map_rel_iff' := by
    intro p q
    change Rose.le _ _ ↔ Rose.le p q
    cases p <;> cases q <;> simp [Rose.le, RelEmbedding.coe_mk]

def roseCopyRealization :=
  (orderNerveRealizationMap (roseCopy a) (roseCopy a).monotone).hom

def orderRoseBase (α : Type) : orderNerveRealization (Rose α) :=
  orderNerveRealizationVertex Rose.base

theorem realizedMap_vertex {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (f : P → Q) (hf : Monotone f) (p : P) :
    orderNerveRealizationMap f hf (orderNerveRealizationVertex p) =
      orderNerveRealizationVertex (f p) := by
  have h := congrArg (fun k : TopCat.of (SimplexCategory.toTop.obj ⦋0⦌) ⟶
      orderNerveRealization Q => k default)
    (orderNerveRealizationSimplex_natural f hf (ComposableArrows.mk₀ p))
  exact h

variable (a : α)

@[simp] theorem roseCopyRealization_base :
    roseCopyRealization a (orderRoseBase PUnit) = orderRoseBase α :=
  realizedMap_vertex (roseCopy a) (roseCopy a).monotone Rose.base

theorem roseCopyRealization_injective : Function.Injective (roseCopyRealization a) :=
  orderNerveRealizationMap_injective (roseCopy a) (roseCopy a).monotone (roseCopy a).injective

theorem rose_le_base (p : Rose α) (hp : p ≤ .base) : p = .base := by
  cases p with
  | base => rfl
  | mid a => exact hp.elim
  | edg a b => exact hp.elim

variable (a : α)

theorem rose_le_mid_has_copy (p : Rose α) (hp : p ≤ .mid a) :
    ∃ q, roseCopy a q = p := by
  cases p with
  | base => exact hp.elim
  | mid b => exact ⟨.mid PUnit.unit, congrArg Rose.mid hp.symm⟩
  | edg b s => exact hp.elim

theorem rose_le_edg_has_copy (b : Bool) (p : Rose α)
    (hp : p ≤ .edg a b) : ∃ q, roseCopy a q = p := by
  cases p with
  | base => solve_by_elim
  | mid c => exact ⟨.mid PUnit.unit, congrArg Rose.mid hp.symm⟩
  | edg c s =>
      exact ⟨.edg PUnit.unit s, congrArg (fun c => Rose.edg c s) hp.1.symm⟩

variable {n : SimplexCategory} (s : (nerve (Rose α)).obj (Opposite.op n))

theorem roseSimplex_copy_lift (a : α)
    (hs : ∀ i, ∃ p, roseCopy a p = s.obj i) :
    ∃ t : (nerve (Rose PUnit)).obj (Opposite.op n),
      (nerveMap (roseCopy a).monotone.functor).app _ t = s := by
  choose p hp using hs
  let t :=
    (show Monotone p from fun i j hij =>
      (roseCopy a).le_iff_le.mp (by
        rw [hp i, hp j]
        exact leOfHom (s.map (homOfLE hij)))).functor
  exact ⟨t, CategoryTheory.Functor.ext hp⟩

theorem roseSimplex_cases :
    (∀ i, s.obj i = .base) ∨
      ∃ (a : α) (t : (nerve (Rose PUnit)).obj (Opposite.op n)),
        (nerveMap (roseCopy a).monotone.functor).app _ t = s := by
  let last := Fin.last n.len
  have hle (i : Fin (n.len + 1)) : s.obj i ≤ s.obj last :=
    leOfHom (s.map (homOfLE (Fin.le_last i)))
  cases he : s.obj last with
  | base => simp_all [rose_le_base]
  | mid a =>
      obtain ⟨t, ht⟩ := roseSimplex_copy_lift s a
        (fun i => rose_le_mid_has_copy a _ (he ▸ hle i)) <;> grind
  | edg a b =>
      obtain ⟨t, ht⟩ := roseSimplex_copy_lift s a
        (fun i => rose_le_edg_has_copy a b _ (he ▸ hle i)) <;> grind

theorem constantSimplex_vertex {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n)) (p : P)
    (hs : ∀ i, s.obj i = p) (z : SimplexCategory.toTop.obj n) :
    orderNerveRealizationSimplex P s z = orderNerveRealizationVertex p := by
  apply orderNerveRealizationCoordinates_injective P
  funext q
  rw [orderNerveRealizationCoordinates_simplex, orderNerveRealizationCoordinates_vertex]
  change (∑ i, z.down.weights i * (if s.obj i = q then 1 else 0)) = _
  simp_all

theorem orderRoseRealization_continuous_iff {X : Type*} [TopologicalSpace X]
    (f : orderNerveRealization (Rose α) → X) :
    Continuous f ↔ ∀ a, Continuous (f ∘ roseCopyRealization a) := by
  constructor
  · fun_prop
  · intro hf
    apply (orderNerveRealization_continuous_iff (Rose α) f).mpr
    intro n s
    rcases roseSimplex_cases s with hs | ⟨a, t, ht⟩
    · have he : f ∘ orderNerveRealizationSimplex (Rose α) s =
          fun _ => f (orderRoseBase α) :=
        funext (fun z => congrArg f (constantSimplex_vertex s .base hs z))
      rw [he]
      exact continuous_const
    · have he : roseCopyRealization a ∘ orderNerveRealizationSimplex (Rose PUnit) t =
          orderNerveRealizationSimplex (Rose α) s := by
        funext z
        have h := congrArg (fun k => k z)
          (orderNerveRealizationSimplex_natural (roseCopy a) (roseCopy a).monotone t)
        aesop
      rw [← he]
      exact (hf a).comp (orderNerveRealizationSimplex (Rose PUnit) t).hom.continuous

theorem orderRoseRealization_cases (x : orderNerveRealization (Rose α)) :
    x = orderRoseBase α ∨ ∃ a u, roseCopyRealization a u = x := by
  obtain ⟨n, s, z, rfl⟩ := orderNerveRealizationSimplex_jointly_surjective (Rose α) x
  rcases roseSimplex_cases s with hs | ⟨a, t, ht⟩
  · solve_by_elim [constantSimplex_vertex]
  · right
    refine ⟨a, orderNerveRealizationSimplex (Rose PUnit) t z, ?_⟩
    have h := congrArg (fun k => k z)
      (orderNerveRealizationSimplex_natural (roseCopy a) (roseCopy a).monotone t)
    aesop

theorem roseCopy_outside {a b : α} (hab : a ≠ b) (q : Rose PUnit)
    (hq : q ≠ .base) : roseCopy a q ∉ Set.range (roseCopy b) := by
  rintro ⟨p, hp⟩
  cases q <;> cases p <;> simp_all [roseCopy, RelEmbedding.coe_mk]

theorem smallRose_eq_base (x : orderNerveRealization (Rose PUnit))
    (hx : ∀ q, q ≠ .base → orderNerveRealizationCoordinates (Rose PUnit) x q = 0) :
    x = orderRoseBase PUnit := by
  letI : Fintype (Rose PUnit) := Fintype.ofFinite _
  have hb : orderNerveRealizationCoordinates (Rose PUnit) x .base = 1 := by
    calc
      orderNerveRealizationCoordinates (Rose PUnit) x .base =
          ∑ q : Rose PUnit, orderNerveRealizationCoordinates (Rose PUnit) x q :=
        (Fintype.sum_eq_single Rose.base hx).symm
      _ = 1 := orderNerveRealizationCoordinates_sum x
  apply orderNerveRealizationCoordinates_injective (Rose PUnit)
  funext q
  rw [orderRoseBase, orderNerveRealizationCoordinates_vertex] <;> grind

theorem roseCopyRealization_intersection {a b : α} (hab : a ≠ b)
    (x y : orderNerveRealization (Rose PUnit))
    (h : roseCopyRealization a x = roseCopyRealization b y) :
    x = orderRoseBase PUnit ∧ y = orderRoseBase PUnit := by
  have oneSide {a b : α} (hab : a ≠ b) (x y : orderNerveRealization (Rose PUnit))
      (h : roseCopyRealization a x = roseCopyRealization b y) :
      x = orderRoseBase PUnit := by
    apply smallRose_eq_base
    intro q hq
    have hc := congrArg (fun z => orderNerveRealizationCoordinates (Rose α) z (roseCopy a q)) h
    dsimp only [roseCopyRealization] at hc
    rw [orderNerveRealizationCoordinates_map_injective (roseCopy a)
      (roseCopy a).monotone (roseCopy a).injective] at hc
    grind [orderNerveRealizationCoordinates_map_outside, roseCopy_outside]
  grind

end FiniteChains.PresModel
