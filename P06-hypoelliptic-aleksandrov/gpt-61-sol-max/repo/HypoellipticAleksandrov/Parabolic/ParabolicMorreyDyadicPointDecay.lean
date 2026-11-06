module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicClosedTail
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicPointSelector
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyProjectionRecovery

/-!
# Pointwise decay along selected parabolic Morrey dyadic cells

This module passes the finite closed dyadic Morrey tail to the smooth value at
the point used to select the cells.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open Filter

/-- Along the canonical dyadic cells containing a reference point, the
canonical affine projection at level `m` differs from the smooth value at
that point by the finite closed Morrey tail. -/
theorem exists_parabolicMorreyDyadicContainingProjectionValueDecayConst
    (d : Nat) (hd : 1 <= d) :
    ∃ C : Real, 0 < C ∧
      ∀ (z : TimeVelocity d)
        (hz : z ∈ parabolicDyadicReferenceCell d)
        (u : HypoellipticAleksandrov.Parabolic.ScalarField d),
        ContDiff Real 2 u ->
        HasCompactSupport u ->
        ∀ m : Nat,
          |u z -
              parabolicMorreyBoxAffineProjection
                (parabolicDyadicSourceBox
                  (parabolicDyadicAddressContaining d z hz m).2).baseTime
                (parabolicDyadicSourceBox
                  (parabolicDyadicAddressContaining d z hz m).2).center
                (parabolicDyadicSourceBox
                  (parabolicDyadicAddressContaining d z hz m).2).radius
                u z| <=
            C *
              (parabolicDyadicSourceBox
                (parabolicDyadicAddressContaining d z hz m).2).radius ^
                parabolicMorreyExponent d *
              (1 - (2 : Real) ^ (-parabolicMorreyExponent d))⁻¹ *
              parabolicMorreyDerivativeLpNorm d u := by
  obtain ⟨C, hCpos, htail⟩ :=
    exists_parabolicMorreyDyadicAddressPrefixProjectionClosedTailConst d hd
  refine ⟨C, hCpos, ?_⟩
  intro z hz u hu huc m
  let A  :=
    fun n => parabolicDyadicAddressContaining d z hz n
  let P  := fun n =>
    parabolicMorreyBoxAffineProjection
      (parabolicDyadicSourceBox (A n).2).baseTime
      (parabolicDyadicSourceBox (A n).2).center
      (parabolicDyadicSourceBox (A n).2).radius u z
  let R : Real :=
    C * (parabolicDyadicSourceBox (A m).2).radius ^ parabolicMorreyExponent d *
      (1 - (2 : Real) ^ (-parabolicMorreyExponent d))⁻¹ *
      parabolicMorreyDerivativeLpNorm d u


  have hprojection : Tendsto P atTop (nhds (u z)) := by
    dsimp only [P]
    exact tendsto_parabolicMorreyBoxAffineProjection_apply_of_contDiff u hu z
      (fun n => (parabolicDyadicSourceBox (A n).2).baseTime)
      (fun n => (parabolicDyadicSourceBox (A n).2).center)
      (fun n => (parabolicDyadicSourceBox (A n).2).radius)
      (fun n => parabolicDyadicSourceBox_radius_pos (A n).2)
      (fun n => parabolicDyadicAddressContaining_mem_closedForwardBox d z hz n)
      (by


          rw [show (fun n => (parabolicDyadicSourceBox (A n).2).radius) =
              fun n => (2 : Real)⁻¹ *
                (2 * (parabolicDyadicSourceBox
                  (parabolicDyadicIndexContaining d z hz n)).radius) by
            funext n
            dsimp only [A, parabolicDyadicAddressContaining]
            ring]
          simpa only [mul_zero] using ((tendsto_two_mul_parabolicDyadicIndexContaining_radius_atTop d z hz).const_mul ((2 : Real)⁻¹)))

  simpa only [P, R, A] using le_of_tendsto ((hprojection.sub tendsto_const_nhds).abs) (by
      refine Filter.eventually_atTop.2 ⟨m, fun n hmn => ?_⟩
      exact htail (A m) (A n) u
        (parabolicDyadicAddressContaining_prefix d z hz hmn) hu huc z
        (parabolicDyadicAddressContaining_mem_closedForwardBox d z hz n))

end HypoellipticAleksandrov.Parabolic
