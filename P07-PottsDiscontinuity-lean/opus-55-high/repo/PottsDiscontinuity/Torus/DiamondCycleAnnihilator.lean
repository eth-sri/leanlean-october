module

public import PottsDiscontinuity.Torus.DiamondChains

/-!
# Potentials characterize the annihilator of conserved flows

An edge coefficient vanishing on every actual cycle is an endpoint potential
difference. This is finite linear duality for the indexed incidence map.
-/

public section

open Finset Matrix

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

section
variable (A : RCConfig N M) (c : OpenDiamondEdge A → ℚ)
/-- Pairing an indexed coefficient vector with indexed one-chains. -/
def edgePairFunctional  :
    (OpenDiamondEdge A → ℚ) →ₗ[ℚ] ℚ where
  toFun f := ∑ e, c e * f e
  map_add' f g := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    grind

@[simp] theorem edgePairFunctional_single (e : OpenDiamondEdge A) : edgePairFunctional A c (Pi.single e 1) = c e := by
  simp [edgePairFunctional, Pi.single_apply, mul_ite]
end

section
variable (hN : Even N) (hM : Even M) (A : RCConfig N M)
theorem diamondBoundary_single (e : OpenDiamondEdge A) :
    diamondBoundary hN hM A (Pi.single e 1) =
      Pi.single (faceEndpoint hN hM true e.val true) 1 -
        Pi.single (faceEndpoint hN hM true e.val false) 1 := by
  funext u
  change ((diamondIncidence hN hM A) *ᵥ Pi.single e 1) u = _
  simp
  simp only [diamondIncidence, Pi.single_apply]
  grind

/-- Every coefficient annihilating conserved indexed flows is an actual vertex coboundary. -/
theorem exists_diamondPotential_of_cycle_annihilator (c : OpenDiamondEdge A → ℚ)
    (h : ∀ f : diamondCycleSpace hN hM A, ∑ e, c e * f.val e = 0) :
    ∃ g : FaceVertex N M true → ℚ, diamondCoboundary hN hM A g = c := by
  have ht : edgePairFunctional A c ∈ (LinearMap.ker (diamondBoundary hN hM A)).dualAnnihilator := by
    simp
    intro f hf
    exact h ⟨f, hf⟩
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at ht
  obtain ⟨H, hH⟩ := ht
  refine ⟨fun u => H (Pi.single u 1), ?_⟩
  funext e
  have he := LinearMap.congr_fun hH (Pi.single e 1)
  change H (diamondBoundary hN hM A (Pi.single e 1)) =
    edgePairFunctional A c (Pi.single e 1) at he
  rw [diamondBoundary_single, map_sub, edgePairFunctional_single] at he
  tauto
end

end PottsDiscontinuity.Torus
