module

public import PottsDiscontinuity.Torus.DiamondCycleExtension
public import PottsDiscontinuity.Torus.FullDisplacement

/-! Vanishing displacement gives a face potential on the full torus. Across
an absent ribbon the potential has no jump, so it descends to the subgraph.
The capped homology has even dimension, so at most one remaining winding
coordinate already implies that every cycle is a boundary. -/

@[expose] public section

open Module Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

section

variable (hN : Even N) (hM : Even M) (A : RCConfig N M)

private theorem boundary_of_full_boundary (f : diamondCycleSpace hN hM A)
    (hf : fullDiamondCycleExtension hN hM A f ∈ ribbonBoundarySpace hN hM (openRCConfig N M)) :
    f ∈ ribbonBoundarySpace hN hM A := by
  obtain ⟨F, hF⟩ := hf
  have hF' := congrArg Subtype.val hF
  let H := fun d => F (ribbonBoundaryOf hN hM (openRCConfig N M) d)
  let e := ribbonEndEquiv hN hM
  have hzero (v : Fin N × Fin M) (hv : A v = false) : H (e (v, true)) = H (e (v, false)) := by
    apply sub_eq_zero.mp
    exact (congrFun hF' ⟨v, rfl⟩).trans (extendDiamondChain_closed A f.val v hv)
  have hs (d : DirectedDart (checkerArrows N M)) :
      H (ribbonEdgePairing hN hM A d) = H (ribbonEdgePairing hN hM (openRCConfig N M) d) := by
    obtain ⟨⟨v,b⟩,rfl⟩ := e.surjective d
    dsimp [e] at *
    rw [ribbonEdgePairing_end, ribbonEdgePairing_end]
    cases hv : A v
    · cases b
      · exact (hzero v hv).symm
      · exact hzero v hv
    · rfl
  have hinv (d : DirectedDart (checkerArrows N M)) : H (ribbonBoundary hN hM A d) = H d :=
    (hs (faceRotation hN hM d)).trans (congrArg F (ribbonBoundaryOf_step hN hM _ d))
  refine ⟨Quotient.lift H (fun _ _ h => sameCycle_invariant _ H hinv h), ?_⟩
  apply Subtype.ext
  funext u
  exact (congrFun hF' ⟨u.val, rfl⟩).trans (extendDiamondChain_open A f.val u.val u.property)

theorem mem_boundary_of_displacement_zero (hNp : 0 < N) (hMp : 0 < M)
    (f : diamondCycleSpace hN hM A) (hf : diamondDisplacementMap hN hM A f = 0) :
    f ∈ ribbonBoundarySpace hN hM A := by
  apply boundary_of_full_boundary
  apply (fullDiamondDisplacement_eq_zero_iff hN hM hNp hMp _).mp
  rw [diamondDisplacementMap_apply, diamondHorizontalDisplacement_fullExtension,
    diamondVerticalDisplacement_fullExtension]
  exact hf

private theorem all_mem_boundary_of_scalar_ker (L : diamondCycleSpace hN hM A →ₗ[ℚ] ℚ)
    (hL : LinearMap.ker L ≤ ribbonBoundarySpace hN hM A) (f : diamondCycleSpace hN hM A) :
    f ∈ ribbonBoundarySpace hN hM A := by
  have hb := LinearMap.finrank_le_finrank_of_surjective (Submodule.factor_surjective hL)
  rw [L.quotKerEquivRange.finrank_eq] at hb
  have hr := Submodule.finrank_le (LinearMap.range L)
  rw [finrank_self] at hr
  have he := finrank_cappedRibbonHomology hN hM A
  have hzero : finrank ℚ (CappedRibbonHomology hN hM A) = 0 := by
    change finrank ℚ (CappedRibbonHomology hN hM A) ≤ _ at hb
    omega
  exact (Submodule.Quotient.mk_eq_zero _).mp ((finrank_zero_iff.mp hzero).elim _ 0)
end

theorem mem_boundary_of_horizontal_displacement_zero
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M) (A : RCConfig N M)
    (hX : ∀ f : diamondCycleSpace hN hM A, diamondHorizontalDisplacement A f.val = 0)
    (f : diamondCycleSpace hN hM A) : f ∈ ribbonBoundarySpace hN hM A := by
  apply all_mem_boundary_of_scalar_ker hN hM A
    ((LinearMap.snd ℚ ℚ ℚ).comp (diamondDisplacementMap hN hM A)) _ f
  intro g hg
  exact mem_boundary_of_displacement_zero hN hM A hNp hMp g
    (Prod.ext (hX g) (LinearMap.mem_ker.mp hg))

theorem mem_boundary_of_boundary_winds_vertically
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M) (A : RCConfig N M)
    (b : diamondCycleSpace hN hM A) (hb : b ∈ ribbonBoundarySpace hN hM A)
    (hy : diamondVerticalDisplacement A b.val ≠ 0) (f : diamondCycleSpace hN hM A) :
    f ∈ ribbonBoundarySpace hN hM A := by
  let D := diamondDisplacementMap hN hM A
  let L := (D b).2 • (LinearMap.fst ℚ ℚ ℚ).comp D - (D b).1 • (LinearMap.snd ℚ ℚ ℚ).comp D
  have hY : (D b).2 ≠ 0 := hy
  apply all_mem_boundary_of_scalar_ker hN hM A L _ f
  intro g hg
  let c := (D g).2 / (D b).2
  have hz := LinearMap.mem_ker.mp hg
  change (D b).2 * (D g).1 - (D b).1 * (D g).2 = 0 at hz
  have h : D (g - c • b) = 0 := by
    simp only [map_sub, map_smul]
    apply Prod.ext <;> dsimp [c] <;> field_simp <;> linarith
  have hg' := mem_boundary_of_displacement_zero hN hM A hNp hMp _ h
  simpa using (ribbonBoundarySpace hN hM A).add_mem hg' ((ribbonBoundarySpace hN hM A).smul_mem c hb)

end PottsDiscontinuity.Torus
