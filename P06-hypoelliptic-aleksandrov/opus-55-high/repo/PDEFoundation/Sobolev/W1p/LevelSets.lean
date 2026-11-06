module

public import PDEFoundation.Sobolev.W1p.Mean
public import PDEFoundation.Sobolev.W1p.Truncation

/-!
# Vanishing of weak gradients on individual level sets

For a representative-level finite-exponent `W^{1,p}` function on a bounded
open convex domain, this module proves that its selected weak gradient
vanishes almost everywhere on each individual level set.  The proof compares
the two one-sided positive-part truncations of `u` and `-u`; it does not use a
general Lipschitz Sobolev chain rule.

The result concerns one fixed level only.  The stronger null-preimage theorem
needed for an arbitrary Lipschitz scalar composition remains a separate
later result.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open Filter MeasureTheory

namespace W1pFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}

/-- The selected weak gradient of a finite-exponent `W^{1,p}` representative
vanishes almost everywhere on each individual level set. -/
theorem grad_ae_zero_on_level_set
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (c : ℝ) :
    ∀ᵐ x ∂(volumeOn U), u.toFun x = c → u.grad x = 0 := by
  let : Fact _ := ⟨hp⟩
  let  :=
    hU.isSobolevRegularDomain.isFiniteMeasure_volumeOn
  let v₁  :=
    u.positivePartSubConst hU hp hpTop c
  let v₂  :=
    (-u).positivePartSubConst hU hp hpTop (-c)
  let v  := v₁ - v₂
  let w  := u.addConst (-c)
  have htoFun_eq : v.toFun = w.toFun := by
    funext x
    have hneg : (-u).toFun x - -c = c - u.toFun x := by
      simp only [neg_toFun]
      ring
    change max _ 0 - max _ 0 =
      u.toFun x + -c
    grind
  have hgrad_ae : ∀ᵐ x ∂(volumeOn U), v.grad x = w.grad x := by
    have hcoord : ∀ i : Fin d,
        (fun x => v.grad x i) =ᵐ[volumeOn U] (fun x => w.grad x i) := by
      intro i
      refine HasWeakPartialDerivOn.ae_eq hU.isOpen
        (MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
          (v.locallyIntegrable_grad i))
        (MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
          (w.locallyIntegrable_grad i))
        (v.hasWeakGradient i) ?_
      rw [htoFun_eq]
      exact w.hasWeakGradient i
    have hall : ∀ᵐ x ∂(volumeOn U), ∀ i, v.grad x i = w.grad x i :=
      ae_all_iff.mpr hcoord
    grind
  filter_upwards [hgrad_ae] with x hx hxc
  aesop

end W1pFunction

end PDE
