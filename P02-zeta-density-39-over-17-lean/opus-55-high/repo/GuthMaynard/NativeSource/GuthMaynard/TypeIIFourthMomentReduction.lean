module
public import GuthMaynard.NativeSource.GuthMaynard.ClassicalDensity
public import GuthMaynard.NativeSource.GuthMaynard.ExtractSeparated
public import GuthMaynard.NativeSource.GuthMaynard.ScaledSeparated
public import GuthMaynard.NativeSource.GuthMaynard.TypeIIContour
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Asymptotics Filter MeasureTheory Topology
open Complex Finset
open scoped BigOperators Interval
open Classical

namespace GuthMaynard.NativeMoment

/-!
# Native Type-II fourth-moment reduction

This module implements Maynard--Pratt Lemma 24 for the concrete finite zeta
zero family.  The first layer below performs the multiplicity-preserving
selection of separated ordinates.
-/

set_option maxHeartbeats 800000 in
set_option hygiene false in
macro "pb_2004" : tactic => `(tactic| (
  have hCompl : (Set.Icc (-H) H)ᶜ = Set.Iio (-H) ∪ Set.Ioi H := by
    ext u
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
    constructor
    grind
    grind))
section
variable {a H : ℝ} (ha : a < -1) (hH : 0 < H)
include a H ha hH
set_option maxHeartbeats 800000 in
set_option maxHeartbeats 800000 in
/-- Exact symmetric tail integral for a negative real power. -/
theorem integral_abs_rpow_compl_Icc :
    ∫ u : ℝ in (Set.Icc (-H) H)ᶜ, |u| ^ a =
      -2 * H ^ (a + 1) / (a + 1) := by
  pm_1596
  have hNegInt : IntegrableOn (fun u : ℝ => |u| ^ a) (Set.Iio (-H)) := by
    pm_954
    have h : IntegrableOn (fun u : ℝ => (-u) ^ a) (Set.Iio (-H)) := by
      exact hPosInt'.comp_neg_Iio (c := -H)
    pm_5884
  have hPosAbs : IntegrableOn (fun u : ℝ => |u| ^ a) (Set.Ioi H) := by
    apply hPosInt.congr_fun
    intro u hu
    pm_8130
    exact measurableSet_Ioi
  pm_7571 hDisjoint H u huNeg huPos
  pb_2004
  rw [hCompl, setIntegral_union hDisjoint measurableSet_Ioi hNegInt hPosAbs]
  have hNegEq :
      ∫ u : ℝ in Set.Iio (-H), |u| ^ a = ∫ u : ℝ in Set.Ioi H, u ^ a := by
    rw [← integral_Iic_eq_integral_Iio]
    rw [← integral_comp_neg_Ioi H (fun u : ℝ => |u| ^ a)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    change |-u| ^ a = u ^ a
    rw [abs_neg, abs_of_pos (hH.trans hu)]
  have hPosEq :
      ∫ u : ℝ in Set.Ioi H, |u| ^ a = ∫ u : ℝ in Set.Ioi H, u ^ a := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    change |u| ^ a = u ^ a
    grind
  rw [hNegEq, hPosEq, integral_Ioi_rpow_of_lt ha hH]
  ring

theorem integrableOn_abs_rpow_compl_Icc :
    IntegrableOn (fun u : ℝ => |u| ^ a) (Set.Icc (-H) H)ᶜ := by
  pm_1596
  have hPosAbs : IntegrableOn (fun u : ℝ => |u| ^ a) (Set.Ioi H) := by
    apply hPosInt.congr_fun
    · intro u hu
      pm_8130
    simp_all
  have hNegAbs : IntegrableOn (fun u : ℝ => |u| ^ a) (Set.Iio (-H)) := by
    pm_954
    have h : IntegrableOn (fun u : ℝ => (-u) ^ a) (Set.Iio (-H)) :=
      hPosInt'.comp_neg_Iio (c := -H)
    pm_5884
  pb_2004
  rw [hCompl]
  simp_all
end

end GuthMaynard.NativeMoment
