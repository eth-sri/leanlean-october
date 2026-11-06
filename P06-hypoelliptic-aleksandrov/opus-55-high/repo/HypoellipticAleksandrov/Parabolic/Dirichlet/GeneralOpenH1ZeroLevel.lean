module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.GeneralOpenH1PositivePart
public import PDEFoundation.Sobolev.H1.Algebra

/-!
# Vanishing of an H¹ gradient on the zero set of its representative

The two strict one-sided truncations reconstruct the original representative.
Uniqueness of weak partial derivatives on an open set then identifies their
difference gradient with the selected gradient of the original function.
-/

@[expose] public section

namespace PDE.H1Function

open Filter MeasureTheory Set

/-- On an arbitrary open set, the selected weak gradient of an `H¹`
representative vanishes almost everywhere on its zero set. -/
theorem grad_ae_zero_on_zero_set_of_isOpen
    {d : ℕ} {U : Set (PDE.Vec d)} (hU : IsOpen U)
    (u : PDE.H1Function U) :
    ∀ᵐ x ∂(PDE.volumeOn U), u.toFun x = 0 → u.grad x = 0 := by
  obtain ⟨v₁, hv₁Fun, hv₁Grad⟩ :=
    exists_h1PositivePartSubConst_of_isOpen hU u 0 (by norm_num)
  obtain ⟨v₂, hv₂Fun, hv₂Grad⟩ :=
    exists_h1PositivePartSubConst_of_isOpen hU (-u) 0 (by norm_num)
  let v  := v₁ - v₂
  have hvFun : v.toFun = u.toFun := by
    aesop
  have hgradAE : ∀ᵐ x ∂(PDE.volumeOn U), v.grad x = u.grad x := by
    have hcoord : ∀ i : Fin d,
        (fun x => v.grad x i) =ᵐ[PDE.volumeOn U] (fun x => u.grad x i) := by
      intro i
      refine PDE.HasWeakPartialDerivOn.ae_eq hU
        (locallyIntegrableOn_of_locallyIntegrable_restrict
          ((v.gradMemL2 i).locallyIntegrable (by norm_num)))
        (locallyIntegrableOn_of_locallyIntegrable_restrict
          ((u.gradMemL2 i).locallyIntegrable (by norm_num)))
        (v.hasWeakGradient i) ?_
      rw [hvFun]
      exact u.hasWeakGradient i
    have hall : ∀ᵐ x ∂(PDE.volumeOn U), ∀ i, v.grad x i = u.grad x i :=
      ae_all_iff.mpr hcoord
    grind
  filter_upwards [hgradAE] with x hx hux
  aesop

end PDE.H1Function
