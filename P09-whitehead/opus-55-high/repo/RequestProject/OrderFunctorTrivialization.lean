import RequestProject.OrderCocyclePotential
import Mathlib.CategoryTheory.Endomorphism


namespace FiniteChains.Comb
open CategoryTheory
open scoped Classical
universe u v w

variable {P : Type u} [Preorder P] {C : Type v} [Groupoid.{w} C]

/-- A choice of arrows from a base object turns a groupoid-valued order functor
into a cocycle. The opposite group makes multiplication follow path order. -/
noncomputable def orderFunctorCocycle (F : P ⥤ C) a
    (d : ∀ p, F.obj a ⟶ F.obj p) : OrdCocycle P (End (F.obj a))ᵐᵒᵖ where
  val p q := if h : p ≤ q then
    MulOpposite.op (d p ≫ F.map (homOfLE h) ≫ Groupoid.inv (d q)) else 1
  comp {p q r} hpq hqr := by
    simp [dif_pos hpq, dif_pos hqr, dif_pos (hpq.trans hqr)]
    apply MulOpposite.unop_injective
    have hc : homOfLE (hpq.trans hqr) = homOfLE hpq ≫ homOfLE hqr := rfl
    rw [hc, F.map_comp]
    simp

/-- Combinatorial simple connectivity makes the arrows to all vertices coherent
with every order morphism, in an arbitrary target groupoid. -/
theorem orderFunctor_exists_coherent_arrows (F : P ⥤ C) a
    (d : ∀ p, F.obj a ⟶ F.obj p)
    (hconn : IsConnected (orderCx P)) (hsc : SimplyConnected (orderCx P)) :
    ∃ k : ∀ p, F.obj a ⟶ F.obj p,
      ∀ {p q : P} (h : p ⟶ q), k p ≫ F.map h = k q := by
  obtain ⟨k, _, hk⟩ := (orderFunctorCocycle F a d).exists_potential_of_simplyConnected
    hconn hsc a
  refine ⟨fun p => (k p).unop ≫ d p, ?_⟩
  intro p q h
  have he : homOfLE (leOfHom h) = h := Subsingleton.elim _ _
  have h₁ := congrArg MulOpposite.unop (hk (leOfHom h))
  simp [orderFunctorCocycle, dif_pos (leOfHom h), MulOpposite.unop_mul,
    MulOpposite.unop_op, End.mul_def, he] at h₁
  grind [Category.assoc, Groupoid.inv_eq_inv, IsIso.inv_hom_id, Category.comp_id]
