module

public import PDEFoundation.Sobolev.W1p.Mean
public import PDEFoundation.Sobolev.W1p.Truncation
public import PDEFoundation.Sobolev.H1.Basic

@[expose] public noncomputable section

namespace PDE
section
open scoped ENNReal

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
  let : Fact (1 ≤ p) := ⟨hp⟩
  let : IsFiniteMeasure (volumeOn U) :=
    hU.isSobolevRegularDomain.isFiniteMeasure_volumeOn
  let v₁ : W1pFunction U p :=
    u.positivePartSubConst hU hp hpTop c
  let v₂ : W1pFunction U p :=
    (-u).positivePartSubConst hU hp hpTop (-c)
  let v := v₁ - v₂
  let w := u.addConst (-c)
  have htoFun_eq : v.toFun = w.toFun := by
    funext x
    have hneg : (-u).toFun x - -c = c - u.toFun x := by
      simp
      ring
    change max (u.toFun x - c) 0 - max ((-u).toFun x - -c) 0 =
      u.toFun x + -c
    rw [hneg]
    rcases le_total (u.toFun x - c) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]
      ring
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
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
    filter_upwards [(ae_all_iff.mpr hcoord)] with x hx
    funext i
    exact hx i
  filter_upwards [hgrad_ae] with x hx hxc
  have hvgrad : v.grad x = v₁.grad x - v₂.grad x := rfl
  have hwgrad : w.grad x = u.grad x := by
    simp only [w, addConst_grad]
  have hv₁zero : v₁.grad x = 0 := by
    change {y | c < u.toFun y}.indicator u.grad x = 0
    rw [Set.indicator_of_notMem (by
      simp [not_lt, hxc, le_refl])]
  have hv₂zero : v₂.grad x = 0 := by
    change {y | -c < (-u).toFun y}.indicator (-u).grad x = 0
    rw [Set.indicator_of_notMem (by
      simp only [Set.mem_ofPred_eq, neg_toFun, not_lt, hxc]
      exact le_rfl)]
  rw [← hwgrad, ← hx, hvgrad, hv₁zero, hv₂zero, sub_zero]

end W1pFunction

end

open Filter MeasureTheory

namespace H1Function

variable {d : ℕ} {U : Set (Vec d)}

/-- The selected `H¹` weak gradient vanishes almost everywhere on each fixed
level set. -/
theorem grad_ae_zero_on_level_set
    (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (c : ℝ) :
    ∀ᵐ x ∂(volumeOn U), u.toFun x = c → u.grad x = 0 := by
  simpa using
    W1pFunction.grad_ae_zero_on_level_set
      hU (by norm_num) (by norm_num) u.toW1pFunction c

end H1Function

end PDE

