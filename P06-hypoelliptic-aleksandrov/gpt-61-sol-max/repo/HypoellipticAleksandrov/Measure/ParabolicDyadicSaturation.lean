module

public import HypoellipticAleksandrov.Measure.ParabolicDyadicOpenCover
public import HypoellipticAleksandrov.Measure.ParabolicDyadicInkSpotsBridge
import Lean.Elab.Tactic.Grind



/-!
# Parabolic dyadic saturation of the first ink-spots union

This file proves the measure part of the crawling-of-ink-spots lemma for the
actual clipped first enlargement union.  The proof separates the root cell
from the first-entry cover and performs the resulting countable sum in
extended nonnegative reals.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- The non-root dyadic cells which first enter the actual source D1 union. -/
def parabolicDyadicD1Entry {d : Nat} (Gamma : HypoellipticAleksandrov.Parabolic.Region d) (xi : Real) :
    Set (ParabolicDyadicAddress d) :=
  parabolicDyadicFirstEntry (inkSpotsD1 Gamma xi)

variable (d : Nat)

private theorem parabolicDyadicD1_subset_unit
     (Gamma : HypoellipticAleksandrov.Parabolic.Region d) (xi : Real) :
    inkSpotsD1 Gamma xi ⊆ inkSpotsUnitBox d := by
  intro z hz
  simp only [inkSpotsD1, Set.mem_iUnion] at hz
  obtain ⟨q, hqDense, hzq⟩ := hz
  exact hzq.2

private theorem parabolicDyadicRoot_openCell_eq_inkSpotsUnitBox  :
    parabolicDyadicOpenCell (Fin.elim0 : ParabolicDyadicIndex d 0) =
      inkSpotsUnitBox d := by
  ext z
  rcases z with ⟨time, velocity⟩
  rw [mem_parabolicDyadicOpenCell_iff, inkSpotsUnitBox, mem_parabolicBox_iff,
    mem_velocityCube_iff]
  simp [parabolicDyadicTimeCode, parabolicDyadicVelocityCode, abs_lt]
  intro _ _
  constructor <;> intro hvelocity <;> intro coordinate
  · grind
  · grind

private theorem volume_inkSpotsUnitBox_ne_top  :
    volume (inkSpotsUnitBox d) ≠ ∞ := by
  intro htop
  have hformula : (volume (inkSpotsUnitBox d)).toReal =
      ((1 : Real) * 1 ^ 2) * (2 * 1) ^ d := by
    simpa only [inkSpotsUnitBox] using
      (volume_parabolicBox_toReal (d := d) (vartheta := (1 )) (r := (1 ))
        (t₀ := (0 )) (v₀ := (0 )) (by norm_num) (by norm_num))
  rw [htop] at hformula
  norm_num at hformula
  exact (ne_of_gt (pow_pos (by norm_num : (0 : Real) < 2) d)) hformula.symm

variable {d : Nat} (Gamma : HypoellipticAleksandrov.Parabolic.Region d) (xi : Real) (a : {a : ParabolicDyadicAddress d // a ∈ parabolicDyadicD1Entry Gamma xi})

private theorem parabolicDyadicD1Entry_openCell_subset
     :
    parabolicDyadicOpenCell a.1.2 ⊆ inkSpotsD1 Gamma xi := by
  rcases a with ⟨⟨n, index⟩, ha⟩
  cases n with
  | zero => exact False.elim ha
  | succ n => exact ha.1

private theorem parabolicDyadicD1_entry_density_le
     :
    (volume (Gamma ∩ parabolicDyadicOpenCell a.1.2)).toReal ≤
      xi * (volume (parabolicDyadicOpenCell a.1.2)).toReal := by
  rcases a with ⟨⟨n, index⟩, ha⟩
  cases n with
  | zero => exact False.elim ha
  | succ n =>
      change parabolicDyadicOpenCell index ⊆ inkSpotsD1 Gamma xi ∧
        ¬ parabolicDyadicOpenCell (parabolicDyadicParent index) ⊆ inkSpotsD1 Gamma xi at ha
      by_contra hle

      exact ha.2
        (parabolicDyadicOpenCell_parent_subset_inkSpotsD1_of_density_gt Gamma xi index (lt_of_not_ge hle))

theorem volume_Gamma_le_xi_volume_inkSpotsD1
    (d : Nat) (Gamma : HypoellipticAleksandrov.Parabolic.Region d) (xi : Real)
    (hGamma : MeasurableSet Gamma) (hGammaUnit : Gamma ⊆ inkSpotsUnitBox d)
    (hxi : xi ∈ Set.Ioo (0 : Real) 1)
    (hsubcritical : (volume Gamma).toReal <
      xi * (volume (inkSpotsUnitBox d)).toReal) :
    Gamma ≤ᵐ[volume] inkSpotsD1 Gamma xi ∧
      (volume Gamma).toReal ≤ xi * (volume (inkSpotsD1 Gamma xi)).toReal := by
  let U  := inkSpotsD1 Gamma xi
  let root : ParabolicDyadicIndex d 0 := Fin.elim0
  have hGammaAE : Gamma ≤ᵐ[volume] U := by
    exact (ae_le_inkSpotsD1_of_parabolicDyadicDensity d Gamma xi hGamma hGammaUnit hxi)
  have hUUnit : U ⊆ inkSpotsUnitBox d := by
    exact parabolicDyadicD1_subset_unit d Gamma xi
  have hrootEq : parabolicDyadicOpenCell root = inkSpotsUnitBox d := by
    exact parabolicDyadicRoot_openCell_eq_inkSpotsUnitBox d

  refine ⟨hGammaAE, ?_⟩
  by_cases hroot : parabolicDyadicOpenCell root ⊆ U
  · grind
  · let E := {a : ParabolicDyadicAddress d | a ∈ parabolicDyadicD1Entry Gamma xi}
    let C : E → HypoellipticAleksandrov.Parabolic.Region d := fun a => parabolicDyadicOpenCell a.1.2
    let V  := ⋃ a : E, C a
    have hV : V = ⋃ a ∈ parabolicDyadicD1Entry Gamma xi,
        parabolicDyadicOpenCell a.2 := by
      change (⋃ a : {a : ParabolicDyadicAddress d //
        a ∈ parabolicDyadicD1Entry Gamma xi}, parabolicDyadicOpenCell a.1.2) = _
      rw [Set.iUnion_subtype]
    have hcover : U =ᵐ[volume] V := by
      rw [hV]
      exact (ae_eq_iUnion_parabolicDyadicFirstEntry_openCell d U
          (isOpen_inkSpotsD1 Gamma xi) (by
              rw [hrootEq]
              exact hUUnit) hroot)
    have hdisjointC : Pairwise (Function.onFun Disjoint C) := by
      intro a b hab
      simp only [C]
      apply pairwiseDisjoint_parabolicDyadicFirstEntry_openCell U
      · exact a.2
      · exact b.2
      · exact Subtype.coe_ne_coe.mpr hab
    have hmeasC : ∀ a : E, MeasurableSet (C a) := by
      intro a
      exact measurableSet_parabolicDyadicOpenCell a.1.2


    have hunit_ne_top  :=
      volume_inkSpotsUnitBox_ne_top d


    have hC_ne_top : ∀ a : E, volume (C a) ≠ ∞ := by
      intro a
      apply measure_ne_top_of_subset
      exact (parabolicDyadicD1Entry_openCell_subset Gamma xi a).trans hUUnit
      exact hunit_ne_top

    let xie  := ENNReal.ofReal xi



    have hGammaV : Gamma ∩ V = ⋃ a : E, Gamma ∩ C a := by
      simp only [V, inter_iUnion]
    have hmeasure : volume Gamma ≤ xie * volume U := by
      calc
        volume Gamma = volume (Gamma ∩ U) := measure_congr (by
            filter_upwards [hGammaAE] with z hz
            apply propext
            constructor
            · intro hzGamma
              exact ⟨hzGamma, hz hzGamma⟩
            · exact fun hzGamma => hzGamma.1)
        _ = volume (Gamma ∩ V) := measure_congr (ae_eq_set_inter (EventuallyEq.rfl) hcover)
        _ = volume (⋃ a : E, Gamma ∩ C a) := by rw [hGammaV]
        _ = ∑' a : E, volume (Gamma ∩ C a) :=
          measure_iUnion (by
              intro a b hab
              exact (hdisjointC hab).mono inter_subset_right inter_subset_right) (by
              intro a
              exact hGamma.inter (hmeasC a))
        _ ≤ ∑' a : E, xie * volume (C a) := ENNReal.tsum_le_tsum (by
            intro a
            apply (ENNReal.toReal_le_toReal ((show ∀ a : E, volume (Gamma ∩ C a) ≠ ∞ by
                intro a
                exact measure_ne_top_of_subset inter_subset_right (hC_ne_top a)) a)
              (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hC_ne_top a))).mp
            simpa only [xie, ENNReal.toReal_mul, ENNReal.toReal_ofReal hxi.1.le] using
              (parabolicDyadicD1_entry_density_le Gamma xi a))
        _ = xie * ∑' a : E, volume (C a) := ENNReal.tsum_mul_left
        _ = xie * volume V := by rw [← measure_iUnion hdisjointC hmeasC]
        _ = xie * volume U := by rw [measure_congr hcover]


    simpa only [U, xie, ENNReal.toReal_mul, ENNReal.toReal_ofReal hxi.1.le] using (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top_of_subset hUUnit hunit_ne_top)) hmeasure)

end

end HypoellipticAleksandrov.Parabolic
