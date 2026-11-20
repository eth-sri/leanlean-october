module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeCoord

/-! # Slice regularity in packed evolution coordinates -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Evolution Parabolic Set

section
variable {n : ℕ} {u : KineticPoint n → ℝ}

/-- A second order jet in packed coordinates supplies the native slice jets. -/
theorem IsSliceRegularAt.of_packed_contDiffAt
    (p : KineticPoint n)
    (h : ContDiffAt ℝ 2 (u ∘ evolutionHomeomorph n) ((evolutionHomeomorph n).symm p)) :
    IsSliceRegularAt u p := by
  apply IsSliceRegularAt.of_contDiffAt
  have he : (u ∘ evolutionHomeomorph n) ∘ (evolutionProdCLE n).symm = rawLift u := by
    funext q
    change u (evolutionHomeomorph n ((evolutionProdCLE n).symm q)) =
      u ((KineticPoint.equivProd n).symm q)
    congr 1
    apply (KineticPoint.equivProd n).injective
    rw [equivProd_evolutionHomeomorph, ContinuousLinearEquiv.apply_symm_apply, Equiv.apply_symm_apply]
  rw [← he]
  exact h.comp (p.time, p.position, p.velocity) (evolutionProdCLE n).symm.contDiff.contDiffAt

/-- Slice regularity at each interior point of an open set of packed smoothness. -/
theorem IsSliceRegularAt.of_packed_smooth
    {D : Set (KineticPoint n)} (hD : IsOpen D)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ evolutionHomeomorph n) (evolutionHomeomorph n ⁻¹' D))
    (p : KineticPoint n) (hp : p ∈ D) : IsSliceRegularAt u p := by
  have hm : (evolutionHomeomorph n).symm p ∈ evolutionHomeomorph n ⁻¹' D := by simpa using hp
  exact .of_packed_contDiffAt p ((hu.contDiffAt
    ((hD.preimage (evolutionHomeomorph n).continuous).mem_nhds hm)).of_le (by simp))

end

end HypoellipticAleksandrov.KineticAleksandrov
