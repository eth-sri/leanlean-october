import RequestProject.OrderNerveSmallHomotopyOne


namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision

/-- Fill the comparison discrepancy on a two-simplex after correcting its edges. -/
theorem orderSmallHomotopyTwoFill_exists {P} [PartialOrder P]
    σ :
    ∃ b, b ∈ orderSingularCarrierChains σ.val 3 ∧
      boundary 2 b = Finsupp.single σ.val 1 -
        orderSmallSingularApproximation2 (orderSmallSingle σ 1) -
        orderSmallHomotopy1 (smallBoundary (orderNerveRealizationOpenStar P) 1 (orderSmallSingle σ 1)) := by
  apply orderSingularCarrierChains_cycle_bounds σ.val σ.property 1
  · exact Submodule.sub_mem _
      (Submodule.sub_mem _ (orderSingularCarrierChains_single σ.val 1)
        (orderSmallSingularApproximation2_carrier σ))
      (orderSmallBoundary_map_carrier orderSmallHomotopy1 orderSmallHomotopy1_carrier σ)
  · rw [map_sub, map_sub, orderSmallSingularApproximation2_boundary, orderSmallHomotopy1_boundary]
    have hd : smallBoundary _ 0
        (smallBoundary _ 1 (orderSmallSingle σ 1)) = 0 :=
      DFunLike.congr_fun (smallBoundary_squared _ 0)
        _
    rw [hd, map_zero, sub_zero]
    exact sub_self _

noncomputable def orderSmallHomotopy2 {P} [PartialOrder P] :
    smallChains (orderNerveRealizationOpenStar P) 2 →ₗ[ℤ] Chain (orderNerveRealization P) 3 :=
  (Finsupp.linearCombination ℤ (fun σ => (orderSmallHomotopyTwoFill_exists σ).choose)).comp
    (orderSmallChainEquiv P 2).toLinearMap

theorem orderSmallHomotopy2_single {P} [PartialOrder P]
    (σ : OrderSmallSimplex P 2) :
    orderSmallHomotopy2 (orderSmallSingle σ 1) = (orderSmallHomotopyTwoFill_exists σ).choose := by
  have he := (orderSmallChainEquiv P 2).apply_symm_apply (Finsupp.single σ 1)
  rw [orderSmallChainEquiv_symm_single] at he
  change (Finsupp.linearCombination ℤ (fun τ : OrderSmallSimplex P 2 =>
    (orderSmallHomotopyTwoFill_exists τ).choose))
      ((orderSmallChainEquiv P 2) (orderSmallSingle σ 1)) = _
  simp_all

theorem orderSmallHomotopy2_boundary {P} [PartialOrder P]
    c :
    boundary 2 (orderSmallHomotopy2 c) = c.val - orderSmallSingularApproximation2 c -
      orderSmallHomotopy1 (smallBoundary (orderNerveRealizationOpenStar P) 1 c) := by
  have he : (boundary 2).comp orderSmallHomotopy2 =
      (smallChains (orderNerveRealizationOpenStar P) 2).subtype - orderSmallSingularApproximation2 -
        orderSmallHomotopy1.comp (smallBoundary _ 1) := by
    apply orderSmallSingle_spans
    intro σ
    simp [LinearMap.comp_apply, LinearMap.sub_apply, orderSmallHomotopy2_single]
    exact (orderSmallHomotopyTwoFill_exists σ).choose_spec.2
  exact DFunLike.congr_fun he c

/-- Realizing the cellular approximation preserves the actual singular class
of every star-small two-cycle. -/
theorem orderSmallCellularApproximation2_homologous {P} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 2)
    (hc : smallBoundary (orderNerveRealizationOpenStar P) 1 c = 0) :
    ∃ b : Chain (orderNerveRealization P) 3,
      boundary 2 b = c.val - orderCellSingularChain2 (orderSmallCellularApproximation2 c) := by
  refine ⟨orderSmallHomotopy2 c, ?_⟩
  rw [orderSmallHomotopy2_boundary, hc, map_zero, sub_zero]
  rfl
