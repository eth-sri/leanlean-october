module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyBoxCoefficientBound
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyMeanNormRestriction
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyProjectionMoments
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Measurability
import all HypoellipticAleksandrov.Parabolic.ParabolicMollifierJetCauchy
import all HypoellipticAleksandrov.Parabolic.ParabolicPoincareMoments

open private HypoellipticAleksandrov.Parabolic.coeff_velocity_affine from HypoellipticAleksandrov.Parabolic.ParabolicPoincareMoments
open private HypoellipticAleksandrov.Parabolic.average_velocity_affine from HypoellipticAleksandrov.Parabolic.ParabolicPoincareMoments
open private HypoellipticAleksandrov.Parabolic.ParabolicW12Function.parabolicExponent_one_le from HypoellipticAleksandrov.Parabolic.ParabolicMollifierJetCauchy


/-!
# Nested parabolic Morrey affine projections

This module compares the canonical affine moment projections on nested forward
parabolic boxes.  The comparison is relative to the residual from the larger
projection and is valid in every spatial dimension, including dimension zero.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators ENNReal




variable {d : Nat}

variable (t_b : Real) (v_b : PDE.Vec d) (r_b : Real) (t_s : Real) (v_s : PDE.Vec d)

private theorem physicalProjection_recenter
      (u : TimeVelocity d -> Real)
    (z : TimeVelocity d) :
    parabolicMorreyBoxAffineProjection t_b v_b r_b u z =
      parabolicMorreyBoxAffineProjection t_b v_b r_b u (t_s, v_s) +
        ∑ i : Fin d, parabolicMorreyBoxVelocitySlope t_b v_b r_b u i *
          (z.2 i - v_s i) := by
  simp only [parabolicMorreyBoxAffineProjection]

  rw [Finset.sum_congr rfl fun i _ => (show ∀ i : Fin d,
      parabolicMorreyBoxVelocitySlope t_b v_b r_b u i * (z.2 i - v_b i) =
        parabolicMorreyBoxVelocitySlope t_b v_b r_b u i * (v_s i - v_b i) +
          parabolicMorreyBoxVelocitySlope t_b v_b r_b u i * (z.2 i - v_s i) by
      intro i
      ring) i, Finset.sum_add_distrib]
  ring

private theorem physicalProjection_pullback_recenter
      {r_s : Real} (_hr_s : 0 < r_s)
    (u : TimeVelocity d -> Real) :
    pullbackScalar (parabolicMorreyBoxAffineProjection t_b v_b r_b u)
      t_s v_s r_s =
      fun z => parabolicMorreyBoxAffineProjection t_b v_b r_b u (t_s, v_s) +
        ∑ i : Fin d, (r_s *
          parabolicMorreyBoxVelocitySlope t_b v_b r_b u i) * z.2 i := by
  funext z
  rw [pullbackScalar_apply, physicalProjection_recenter]
  simp only [parabolicAffine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem unit_raw_integrable_of_physical_mean_memLp
     (t_s : Real) (v_s : PDE.Vec d) {r_s : Real} (hr_s : 0 < r_s)
    (f : TimeVelocity d -> Real)
    (hf : MemLp f (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 r_s t_s v_s))) :
    Integrable (pullbackScalar f t_s v_s r_s)
      (volume.restrict (parabolicMorreyUnitBox d)) := by
  have hmean := (memLp_parabolicNormalizedVolumeOn_parabolicBox_iff
    t_s v_s hr_s f).mp hf

  have hUtop  :=
    lt_top_iff_ne_top.mpr (volume_parabolicMorreyUnitBox_ne_top d)
  have hraw := memLp_restrict_of_memLp_parabolicNormalizedVolumeOn
    ((ENNReal.toReal_pos_iff.mp (volume_parabolicMorreyUnitBox_toReal_pos d)).1) hUtop hmean
  letI : Fact (volume (parabolicMorreyUnitBox d) < ∞) := ⟨hUtop⟩
  exact hraw.integrable (_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.parabolicExponent_one_le d)

variable (a : Real) (b : Fin d -> Real)

private theorem unit_raw_integrable_affine
      :
    Integrable (fun z : TimeVelocity d => a + ∑ i : Fin d, b i * z.2 i)
      (volume.restrict (parabolicMorreyUnitBox d)) := by
  letI : Fact (volume (parabolicMorreyUnitBox d) < ∞) :=
    ⟨lt_top_iff_ne_top.mpr (volume_parabolicMorreyUnitBox_ne_top d)⟩
  exact (Continuous.memLp_parabolicMorreyUnitBox (by fun_prop)).integrable
    (_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.parabolicExponent_one_le d)







private theorem unit_raw_integrable_mul_velocity
     {f : TimeVelocity d -> Real}
    (hf : Integrable f (volume.restrict (parabolicMorreyUnitBox d)))
    (i : Fin d) :
    Integrable (fun z => f z * z.2 i)
      (volume.restrict (parabolicMorreyUnitBox d)) := by
  refine hf.mul_bdd (c := 1) ?_ ?_
  · measurability
  · filter_upwards [ae_restrict_mem
      (measurableSet_parabolicBox 1 1 0 (0 : PDE.Vec d))] with z hz
    change z ∈ parabolicBox 1 1 0 (0 : PDE.Vec d) at hz
    rw [mem_parabolicBox_iff] at hz
    change |z.2 i| ≤ 1
    simpa only [Pi.zero_apply, sub_zero] using (hz.2.2 i).le

variable (t_b : Real) (v_b : PDE.Vec d)

variable (r_b : Real) (t_s : Real) (v_s : PDE.Vec d) {r_s : Real}

section
variable (hr_s : 0 < r_s) (u : TimeVelocity d -> Real)

include hr_s
private theorem parabolicMorreyBoxAverage_sub_projection

    (hf : MemLp (fun z => u z -
      parabolicMorreyBoxAffineProjection t_b v_b r_b u z)
      (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 r_s t_s v_s))) :
    parabolicMorreyBoxAverage t_s v_s r_s
      (fun z => u z - parabolicMorreyBoxAffineProjection t_b v_b r_b u z) =
      parabolicMorreyBoxAverage t_s v_s r_s u -
        parabolicMorreyBoxAffineProjection t_b v_b r_b u (t_s, v_s) := by
  let B  :=
    parabolicMorreyBoxAffineProjection t_b v_b r_b u
  let f  := fun z => u z - B z
  let fhat  := pullbackScalar f t_s v_s r_s
  let bhat  := pullbackScalar B t_s v_s r_s

  have hbhat_shape : bhat = fun z => B (t_s, v_s) + ∑ i : Fin d,
      (r_s * parabolicMorreyBoxVelocitySlope t_b v_b r_b u i) * z.2 i := by
    dsimp only [bhat, B]
    exact physicalProjection_pullback_recenter t_b v_b r_b t_s v_s hr_s u

  have hsum : pullbackScalar u t_s v_s r_s = fhat + bhat := by
    funext z
    simp only [fhat, bhat, f, B, pullbackScalar_apply, Pi.add_apply]
    ring
  have havg := parabolicMorreyUnitAverage_add fhat bhat (by
      dsimp only [fhat, f]
      exact unit_raw_integrable_of_physical_mean_memLp t_s v_s hr_s _ hf) (by
      rw [hbhat_shape]
      exact unit_raw_integrable_affine _ _)
  rw [← hsum] at havg
  have hBavg : parabolicMorreyUnitAverage bhat = B (t_s, v_s) := by
    rw [hbhat_shape]
    exact _root_.HypoellipticAleksandrov.Parabolic.average_velocity_affine _ _
  change parabolicMorreyUnitAverage fhat =
    parabolicMorreyUnitAverage (pullbackScalar u t_s v_s r_s) - B (t_s, v_s)
  rw [hBavg] at havg
  linarith

private theorem parabolicMorreyBoxVelocitySlope_sub_projection
        (i : Fin d)
    (hf : MemLp (fun z => u z -
      parabolicMorreyBoxAffineProjection t_b v_b r_b u z)
      (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 r_s t_s v_s))) :
    parabolicMorreyBoxVelocitySlope t_s v_s r_s
      (fun z => u z - parabolicMorreyBoxAffineProjection t_b v_b r_b u z) i =
      parabolicMorreyBoxVelocitySlope t_s v_s r_s u i -
        parabolicMorreyBoxVelocitySlope t_b v_b r_b u i := by
  let B  :=
    parabolicMorreyBoxAffineProjection t_b v_b r_b u
  let f  := fun z => u z - B z
  let fhat  := pullbackScalar f t_s v_s r_s
  let bhat  := pullbackScalar B t_s v_s r_s

  have hbhat_shape : bhat = fun z => B (t_s, v_s) + ∑ j : Fin d,
      (r_s * parabolicMorreyBoxVelocitySlope t_b v_b r_b u j) * z.2 j := by
    dsimp only [bhat, B]
    exact physicalProjection_pullback_recenter t_b v_b r_b t_s v_s hr_s u



  have hsum : pullbackScalar u t_s v_s r_s = fhat + bhat := by
    funext z
    simp only [fhat, bhat, f, B, pullbackScalar_apply, Pi.add_apply]
    ring
  have hcoeff := parabolicMorreyUnitVelocityCoeff_add fhat bhat i (unit_raw_integrable_mul_velocity (show Integrable fhat (volume.restrict (parabolicMorreyUnitBox d)) by
      dsimp only [fhat, f]
      exact unit_raw_integrable_of_physical_mean_memLp t_s v_s hr_s _ hf) i) (unit_raw_integrable_mul_velocity (show Integrable bhat (volume.restrict (parabolicMorreyUnitBox d)) by
      rw [hbhat_shape]
      exact unit_raw_integrable_affine _ _) i)
  rw [← hsum] at hcoeff
  have hBcoeff : parabolicMorreyUnitVelocityCoeff bhat i =
      r_s * parabolicMorreyBoxVelocitySlope t_b v_b r_b u i := by
    rw [hbhat_shape]
    exact _root_.HypoellipticAleksandrov.Parabolic.coeff_velocity_affine _ _ i
  change r_s⁻¹ * parabolicMorreyUnitVelocityCoeff fhat i =
    r_s⁻¹ * parabolicMorreyUnitVelocityCoeff (pullbackScalar u t_s v_s r_s) i -
      parabolicMorreyBoxVelocitySlope t_b v_b r_b u i
  rw [hBcoeff] at hcoeff
  rw [hcoeff]
  field_simp [hr_s.ne']
  ring
end


private theorem parabolicMorreyNestedProjection_abs_sub_le_discrepancy
       (_hr_s : 0 < r_s)
    (u : TimeVelocity d -> Real) (z : TimeVelocity d)
    (hz : z ∈ parabolicBox 1 r_s t_s v_s) :
    |parabolicMorreyBoxAffineProjection t_s v_s r_s u z -
      parabolicMorreyBoxAffineProjection t_b v_b r_b u z| ≤
      |parabolicMorreyBoxAverage t_s v_s r_s u -
        parabolicMorreyBoxAffineProjection t_b v_b r_b u (t_s, v_s)| +
      r_s * ∑ i : Fin d,
        |parabolicMorreyBoxVelocitySlope t_s v_s r_s u i -
          parabolicMorreyBoxVelocitySlope t_b v_b r_b u i| := by
  let sharedTerm_556b04d11c := (∑ i : Fin d,
    (parabolicMorreyBoxVelocitySlope t_s v_s r_s u i - parabolicMorreyBoxVelocitySlope t_b v_b r_b u i) * (z.2 i - v_s i))
  have hcoord : ∀ i : Fin d, |z.2 i - v_s i| ≤ r_s := by
    intro i
    rw [mem_parabolicBox_iff] at hz
    exact (hz.2.2 i).le
  have hdiff :
      parabolicMorreyBoxAffineProjection t_s v_s r_s u z -
        parabolicMorreyBoxAffineProjection t_b v_b r_b u z =
        (parabolicMorreyBoxAverage t_s v_s r_s u -
          parabolicMorreyBoxAffineProjection t_b v_b r_b u (t_s, v_s)) +
        sharedTerm_556b04d11c := by
    rw [physicalProjection_recenter t_b v_b r_b t_s v_s u z]
    simp only [parabolicMorreyBoxAffineProjection]
    have hsumdiff :
        (sharedTerm_556b04d11c) =
          (∑ i : Fin d, parabolicMorreyBoxVelocitySlope t_s v_s r_s u i *
            (z.2 i - v_s i)) -
          ∑ i : Fin d, parabolicMorreyBoxVelocitySlope t_b v_b r_b u i *
            (z.2 i - v_s i) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsumdiff]
    ring

  rw [hdiff]
  calc
    |(parabolicMorreyBoxAverage t_s v_s r_s u -
          parabolicMorreyBoxAffineProjection t_b v_b r_b u (t_s, v_s)) +
        sharedTerm_556b04d11c| ≤
        |parabolicMorreyBoxAverage t_s v_s r_s u -
          parabolicMorreyBoxAffineProjection t_b v_b r_b u (t_s, v_s)| +
        |sharedTerm_556b04d11c| := abs_add_le _ _
    _ ≤ _ := add_le_add (le_refl _) (by
        calc
          |sharedTerm_556b04d11c| ≤
              ∑ i : Fin d,
                |(parabolicMorreyBoxVelocitySlope t_s v_s r_s u i -
                  parabolicMorreyBoxVelocitySlope t_b v_b r_b u i) *
                    (z.2 i - v_s i)| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ i : Fin d,
              |parabolicMorreyBoxVelocitySlope t_s v_s r_s u i -
                parabolicMorreyBoxVelocitySlope t_b v_b r_b u i| *
                  |z.2 i - v_s i| := by
            simp_rw [abs_mul]
          _ ≤ ∑ i : Fin d,
              |parabolicMorreyBoxVelocitySlope t_s v_s r_s u i -
                parabolicMorreyBoxVelocitySlope t_b v_b r_b u i| * r_s := by
            bound
          _ = r_s * ∑ i : Fin d,
              |parabolicMorreyBoxVelocitySlope t_s v_s r_s u i -
                parabolicMorreyBoxVelocitySlope t_b v_b r_b u i| := by
            rw [Finset.mul_sum]
            ac_rfl)

/-- The small-box projection discrepancy is controlled by the normalized
residual from an arbitrary reference affine projection. -/
theorem parabolicMorreyNestedProjection_discrepancy_le_smallResidual
       (hr_s : 0 < r_s)
    (u : TimeVelocity d -> Real)
    (hsmall : MemLp (fun z => u z - parabolicMorreyBoxAffineProjection t_b v_b r_b u z)
      (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 r_s t_s v_s))) :
    |parabolicMorreyBoxAverage t_s v_s r_s u -
        parabolicMorreyBoxAffineProjection t_b v_b r_b u (t_s, v_s)| +
      r_s * ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope t_s v_s r_s u i -
        parabolicMorreyBoxVelocitySlope t_b v_b r_b u i| ≤
      (1 + 3 * (d : Real)) * parabolicLpMeanNormOn d
        (fun z => u z - parabolicMorreyBoxAffineProjection t_b v_b r_b u z)
        _ hsmall := by
  let sharedTerm_a19eeaa2bd := ((fun z => u z - parabolicMorreyBoxAffineProjection t_b v_b r_b u z))
  have hbound := parabolicMorreyBoxCoefficientBound_le_parabolicLpMeanNormOn
    t_s v_s hr_s
      sharedTerm_a19eeaa2bd hsmall
  rw [parabolicMorreyBoxAverage_sub_projection t_b v_b r_b t_s v_s hr_s u hsmall]
    at hbound
  have hslope : ∀ i : Fin d,
      parabolicMorreyBoxVelocitySlope t_s v_s r_s
        sharedTerm_a19eeaa2bd i =
        parabolicMorreyBoxVelocitySlope t_s v_s r_s u i -
          parabolicMorreyBoxVelocitySlope t_b v_b r_b u i := by
    intro i
    exact parabolicMorreyBoxVelocitySlope_sub_projection
      t_b v_b r_b t_s v_s hr_s u i hsmall
  simp_rw [hslope] at hbound
  exact hbound

variable {r_b : Real} (hr_b : 0 < r_b) (t_s : Real) (v_s : PDE.Vec d) {r_s : Real} (hr_s : 0 < r_s) (hsub : parabolicBox 1 r_s t_s v_s ⊆ parabolicBox 1 r_b t_b v_b) (u : TimeVelocity d -> Real)

include hr_b hr_s hsub
/-- A nested small-box discrepancy is controlled by the normalized residual
on the containing large box with the exact parabolic radius factor. -/
theorem parabolicMorreyNestedProjection_discrepancy_le_largeResidual

    (hbig : MemLp (fun z => u z - parabolicMorreyBoxAffineProjection t_b v_b r_b u z)
      (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 r_b t_b v_b))) :
    |parabolicMorreyBoxAverage t_s v_s r_s u -
        parabolicMorreyBoxAffineProjection t_b v_b r_b u (t_s, v_s)| +
      r_s * ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope t_s v_s r_s u i -
        parabolicMorreyBoxVelocitySlope t_b v_b r_b u i| ≤
      (1 + 3 * (d : Real)) *
        (r_b / r_s) ^ (((d : Real) + 2) / ((d : Real) + 1)) *
        parabolicLpMeanNormOn d
          (fun z => u z - parabolicMorreyBoxAffineProjection t_b v_b r_b u z)
          _ hbig := by
  let sharedTerm_38056a6300 := ((r_b / r_s) ^ (((d : Real) + 2) / ((d : Real) + 1)))
  let sharedTerm_b37901e401 := (1 + 3 * (d : Real))
  let f  := fun z =>
    u z - parabolicMorreyBoxAffineProjection t_b v_b r_b u z
  have hsmall  :=
    memLp_parabolicNormalizedVolumeOn_mono_parabolicBox
      t_b v_b hr_b t_s v_s hr_s hsub hbig
  have hsmallbound :=
    parabolicMorreyNestedProjection_discrepancy_le_smallResidual
      t_b v_b r_b t_s v_s hr_s u hsmall
  have hnorm := parabolicLpMeanNormOn_mono_parabolicBox
    t_b v_b hr_b t_s v_s hr_s hsub f hsmall hbig
  calc
    |parabolicMorreyBoxAverage t_s v_s r_s u -
        parabolicMorreyBoxAffineProjection t_b v_b r_b u (t_s, v_s)| +
      r_s * ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope t_s v_s r_s u i -
        parabolicMorreyBoxVelocitySlope t_b v_b r_b u i| ≤
        (sharedTerm_b37901e401) *
          parabolicLpMeanNormOn d f _ hsmall := hsmallbound
    _ ≤ (sharedTerm_b37901e401) *
        (sharedTerm_38056a6300 *
          parabolicLpMeanNormOn d f _ hbig) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = (sharedTerm_b37901e401) *
        sharedTerm_38056a6300 *
        parabolicLpMeanNormOn d f _ hbig := by
      ring

/-- Two nested canonical affine projections differ pointwise by the same
large-box residual bound on the small forward box. -/
theorem parabolicMorreyNestedProjection_abs_sub_le_largeResidual
       (z : TimeVelocity d)
    (hz : z ∈ parabolicBox 1 r_s t_s v_s)
    (hbig : MemLp (fun w => u w - parabolicMorreyBoxAffineProjection t_b v_b r_b u w)
      (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 r_b t_b v_b))) :
    |parabolicMorreyBoxAffineProjection t_s v_s r_s u z -
      parabolicMorreyBoxAffineProjection t_b v_b r_b u z| ≤
      (1 + 3 * (d : Real)) *
        (r_b / r_s) ^ (((d : Real) + 2) / ((d : Real) + 1)) *
        parabolicLpMeanNormOn d
          (fun w => u w - parabolicMorreyBoxAffineProjection t_b v_b r_b u w)
          _ hbig := (parabolicMorreyNestedProjection_abs_sub_le_discrepancy
    t_b v_b r_b t_s v_s hr_s u z hz).trans
      (parabolicMorreyNestedProjection_discrepancy_le_largeResidual
        t_b v_b hr_b t_s v_s hr_s hsub u hbig)

end HypoellipticAleksandrov.Parabolic
