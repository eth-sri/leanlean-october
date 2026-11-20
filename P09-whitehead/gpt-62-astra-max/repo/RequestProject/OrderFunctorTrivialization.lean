module

public import RequestProject.OrderCocyclePotential
public import Mathlib.CategoryTheory.Endomorphism

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory
open scoped Classical
universe u v w

variable {P : Type u} [Preorder P] {C : Type v} [Groupoid.{w} C]

variable (F : P ⥤ C) (a : P) (d : ∀ p : P, F.obj a ⟶ F.obj p)
include d

/-- A choice of arrows from a base object turns a groupoid-valued order functor
into a cocycle. The opposite group makes multiplication follow path order. -/
noncomputable def orderFunctorCocycle : OrdCocycle P (End (F.obj a))ᵐᵒᵖ where
  val p q := if h : p ≤ q then
    MulOpposite.op (d p ≫ F.map (homOfLE h) ≫ Groupoid.inv (d q)) else 1
  comp {p q r} hpq hqr := by
    simp only [dif_pos hpq, dif_pos hqr, dif_pos (hpq.trans hqr)]
    apply MulOpposite.unop_injective
    have hc : homOfLE (hpq.trans hqr) = homOfLE hpq ≫ homOfLE hqr := rfl
    rw [hc, F.map_comp] <;> simp_all

/-- Combinatorial simple connectivity makes the arrows to all vertices coherent
with every order morphism, in an arbitrary target groupoid. -/
theorem orderFunctor_exists_coherent_arrows
    (hconn : IsConnected (orderCx P)) (hsc : SimplyConnected (orderCx P)) :
    ∃ k : ∀ p : P, F.obj a ⟶ F.obj p,
      ∀ {p q : P} (h : p ⟶ q), k p ≫ F.map h = k q := by
  obtain ⟨k, _, hk⟩ := (orderFunctorCocycle F a d).exists_potential_of_simplyConnected
    hconn hsc a
  refine ⟨fun p => (k p).unop ≫ d p, ?_⟩
  intro p q h
  have he : homOfLE (leOfHom h) = h := Subsingleton.elim _ _
  have h₁ := congrArg MulOpposite.unop (hk (leOfHom h))
  simp only [orderFunctorCocycle, dif_pos (leOfHom h), MulOpposite.unop_mul,
    MulOpposite.unop_op, End.mul_def, he] at h₁
  simpa only [Category.assoc, Groupoid.inv_eq_inv, IsIso.inv_hom_id, Category.comp_id] using (congrArg (fun e : End (F.obj a) => e ≫ d q) h₁)

end FiniteChains.Comb
