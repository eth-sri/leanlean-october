module

public import ADR11.Identifiability.FiveTaxa.Classes
public import ADR11.Identifiability.FiveTaxa.Common
public import ADR11.Nonbinary.AppendixC

/-!
# Appendix C: the classes of gene trees of the rootings of `U5 0` and `U5 1`

The proof of Proposition 11 (Appendix C of the paper) reads the shape and the labelling of a
nonbinary 5-taxon species tree off its classes of equiprobable gene trees: the least probable class
`𝒞`, the class with the second smallest probability, and the most probable gene trees. This module
computes these classes, from the gene tree distributions of Table 7 (`rootingDist5_k_j`, the
formulas of Table 7 for each labelling), for the rootings of the star `U5 0` and of `U5 1 = AB|CDE`
whose labelling rules use them (the shapes `P₃`, `P₇` and `P₉`), and for the representatives `P₂`,
`P₃` of Table 6 (used by the rule telling them apart, `sh_P2_P3_rule`).

## Main results

* `ac1_leastClass_eq`, `ac1_secondClass_eq`, `ac1_mostProbable_eq`, `ac1_classes_two`: the
  classes of a distribution that takes one value on a set of gene trees and larger (smaller)
  values elsewhere.
* `ac1_classes_0_j` (`j = 1, …, 5`, the rootings of shape `P₃`) and `ac1_classes_1_j`
  (`j = 3, …, 7`, the rootings of shapes `P₉` and `P₇`): the least probable class of the `j`-th
  rooting of `U5 0` (resp. `U5 1`), with the class of the second smallest probability or the most
  probable gene tree.
* `ac1_classes_P2`, `ac1_classes_P3`: the same for the representatives `P₂ = (a,b,c,(d,e))` and
  `P₃ = ((a,b,c,d),e)`, from Table 7.
-/

@[expose] public section

namespace ADR11

open Finset Real

/-! ### The classes of a distribution with a given least (or greatest) value -/

/-- If `u τ` takes the value `v` on a nonempty set `S` of gene trees and larger values on the other
gene trees, then `S` is the least probable class. -/
theorem ac1_leastClass_eq {τ : SpeciesTree (Fin 5)} (S : Finset ℕ) (v : ℝ) (hS : S ⊆ Icc 1 15)
    (hne : S.Nonempty) (hu : ∀ i ∈ Icc 1 15, (i ∈ S → u τ i = v) ∧ (i ∉ S → v < u τ i)) :
    cls_leastClass τ = S := five_leastClass_eq S v hS hne hu

/-- If the least probable class is `S₁`, and `u τ` takes the value `w` on a nonempty set `S₂` of
gene trees outside `S₁` and larger values on the gene trees outside `S₁ ∪ S₂`, then `S₂` is the
class with the second smallest probability. -/
theorem ac1_secondClass_eq {τ : SpeciesTree (Fin 5)} {S₁ : Finset ℕ} (h₁ : cls_leastClass τ = S₁)
    (S₂ : Finset ℕ) (w : ℝ) (hS₂ : S₂ ⊆ Icc 1 15) (hd : Disjoint S₁ S₂) (hne : S₂.Nonempty)
    (hu : ∀ i ∈ Icc 1 15, (i ∈ S₂ → u τ i = w) ∧ (i ∉ S₁ → i ∉ S₂ → w < u τ i)) :
    cls_secondClass τ = S₂ := five_secondClass_eq h₁ S₂ w hS₂ hd hne hu

/-- If `u τ` takes the value `m` on a nonempty set `S` of gene trees and smaller values on the
other gene trees, then `S` is the set of the most probable gene trees. -/
theorem ac1_mostProbable_eq {τ : SpeciesTree (Fin 5)} (S : Finset ℕ) (m : ℝ) (hS : S ⊆ Icc 1 15)
    (hne : S.Nonempty) (hu : ∀ i ∈ Icc 1 15, (i ∈ S → u τ i = m) ∧ (i ∉ S → u τ i < m)) :
    cls_mostProbable τ = S := five_mostProbable_eq S m hS hne hu

/-- A distribution with two classes: if `u τ` takes the value `a` on a nonempty set `C` of gene
trees and a smaller value `b` on the others (at least one), then the least probable class is the
complement of `C`, and `C` is the class with the second smallest probability. -/
theorem ac1_classes_two {τ : SpeciesTree (Fin 5)} (C : Finset ℕ) (a b : ℝ) (hC : C ⊆ Icc 1 15)
    (hne : C.Nonempty) (hne' : (Icc 1 15 \ C).Nonempty)
    (hu : ∀ i ∈ Icc 1 15, u τ i = if i ∈ C then a else b) (hba : b < a) :
    cls_leastClass τ = Icc 1 15 \ C ∧ cls_secondClass τ = C := by
  have h₁ : cls_leastClass τ = Icc 1 15 \ C := by
    refine ac1_leastClass_eq _ b sdiff_subset hne' fun i hi => ⟨fun h => ?_, fun h => ?_⟩
    · rw [hu i hi, ite_eq_right (mem_sdiff.1 h).2]
    · have hiC : i ∈ C := by
        by_contra hiC
        exact h (mem_sdiff.2 ⟨hi, hiC⟩)
      rw [hu i hi, ite_eq_left hiC]
      exact hba
  refine ⟨h₁, ac1_secondClass_eq h₁ C a hC sdiff_disjoint hne fun i hi => ⟨fun h => ?_, ?_⟩⟩
  · rw [hu i hi, ite_eq_left h]
  · intro h1 h2
    exact absurd (mem_sdiff.2 ⟨hi, h2⟩) h1

private theorem ac1_classes_two_eq {τ : SpeciesTree (Fin 5)} (C L : Finset ℕ) (a b : ℝ)
    (hC : C ⊆ Icc 1 15) (hne : C.Nonempty) (hne' : (Icc 1 15 \ C).Nonempty)
    (hL : L = Icc 1 15 \ C)
    (hu : ∀ i ∈ Icc 1 15, u τ i = if i ∈ C then a else b) (hba : b < a) :
    cls_leastClass τ = L ∧ cls_secondClass τ = C := by
  subst L
  exact ac1_classes_two C a b hC hne hne' hu hba

macro "ac1_interval" i:ident hi:ident : tactic => `(tactic| (
  obtain ⟨hi1, hi2⟩ := mem_Icc.1 $hi
  interval_cases $i <;> simp_all))

macro "ac1_p3" τ:ident h:ident r:term:max A:term:max : tactic => `(tactic| (
  have hd := $r $τ $h
  have h1 := hd 1 (by decide)
  have h2 := hd 2 (by decide)
  have h3 := hd 3 (by decide)
  have h4 := hd 4 (by decide)
  have h5 := hd 5 (by decide)
  have h6 := hd 6 (by decide)
  have h7 := hd 7 (by decide)
  have h8 := hd 8 (by decide)
  have h9 := hd 9 (by decide)
  have h10 := hd 10 (by decide)
  have h11 := hd 11 (by decide)
  have h12 := hd 12 (by decide)
  have h13 := hd 13 (by decide)
  have h14 := hd 14 (by decide)
  have h15 := hd 15 (by decide)
  clear hd
  obtain ⟨z0, z1⟩ := five_exp_bounds $τ (A := $A) (by rw [show _ from $h]; decide) (by decide)
  generalize exp (-($τ).length $A) = Z at *
  have f : Z ^ 6 < 1 := pow_lt_one₀ z0.le z1 (by norm_num)
  have i_ba : 1 / 90 * Z ^ 6 + 1 / 18 < -2 / 45 * Z ^ 6 + 1 / 9 := by linarith only [f]
  generalize 1 / 90 * Z ^ 6 + 1 / 18 = b at *
  generalize -2 / 45 * Z ^ 6 + 1 / 9 = a at *
  refine ac1_classes_two_eq _ _ a b (by decide) (by decide) (by decide) (by decide) ?_ i_ba
  intro i hi
  ac1_interval i hi))

macro "ac1_p9" τ:ident h:ident r:term:max A:term:max B:term:max L:term:max S:term:max : tactic => `(tactic| (
  have hd := $r $τ $h
  have h1 := hd 1 (by decide)
  have h2 := hd 2 (by decide)
  have h3 := hd 3 (by decide)
  have h4 := hd 4 (by decide)
  have h5 := hd 5 (by decide)
  have h6 := hd 6 (by decide)
  have h7 := hd 7 (by decide)
  have h8 := hd 8 (by decide)
  have h9 := hd 9 (by decide)
  have h10 := hd 10 (by decide)
  have h11 := hd 11 (by decide)
  have h12 := hd 12 (by decide)
  have h13 := hd 13 (by decide)
  have h14 := hd 14 (by decide)
  have h15 := hd 15 (by decide)
  clear hd
  obtain ⟨y0, y1⟩ := five_exp_bounds $τ (A := $A) (by rw [show _ from $h]; decide) (by decide)
  obtain ⟨z0, z1⟩ := five_exp_bounds $τ (A := $B) (by rw [show _ from $h]; decide) (by decide)
  generalize exp (-($τ).length $A) = Y at *
  generalize exp (-($τ).length $B) = Z at *
  have f1 : 0 < Y * ((1 - Y) * (1 + Y)) :=
    mul_pos y0 (mul_pos (sub_pos.2 y1) (by linarith only [y0]))
  have f2 : 0 < (1 - Y) ^ 2 * (2 + Y) := mul_pos (pow_pos (sub_pos.2 y1) 2) (by linarith only [y0])
  have f3 : Y ^ 3 * Z ^ 6 < Y ^ 3 :=
    mul_lt_of_lt_one_right (pow_pos y0 3) (pow_lt_one₀ z0.le z1 (by norm_num))
  have i_vw : 1 / 90 * Y ^ 3 * Z ^ 6 + 1 / 18 * Y ^ 3 <
      1 / 90 * Y ^ 3 * Z ^ 6 - 1 / 9 * Y ^ 3 + 1 / 6 * Y := by linarith only [y1, f1, f2, f3]
  have i_vs : 1 / 90 * Y ^ 3 * Z ^ 6 + 1 / 18 * Y ^ 3 <
      -2 / 45 * Y ^ 3 * Z ^ 6 - 1 / 18 * Y ^ 3 + 1 / 6 * Y := by linarith only [y1, f1, f2, f3]
  have i_vt : 1 / 90 * Y ^ 3 * Z ^ 6 + 1 / 18 * Y ^ 3 <
      1 / 90 * Y ^ 3 * Z ^ 6 + 1 / 18 * Y ^ 3 - 1 / 3 * Y + 1 / 3 := by
    linarith only [y1, f1, f2, f3]
  have i_wt : 1 / 90 * Y ^ 3 * Z ^ 6 - 1 / 9 * Y ^ 3 + 1 / 6 * Y <
      1 / 90 * Y ^ 3 * Z ^ 6 + 1 / 18 * Y ^ 3 - 1 / 3 * Y + 1 / 3 := by
    linarith only [y1, f1, f2, f3]
  have i_ws : 1 / 90 * Y ^ 3 * Z ^ 6 - 1 / 9 * Y ^ 3 + 1 / 6 * Y <
      -2 / 45 * Y ^ 3 * Z ^ 6 - 1 / 18 * Y ^ 3 + 1 / 6 * Y := by
    linarith only [y1, f1, f2, f3]
  generalize 1 / 90 * Y ^ 3 * Z ^ 6 + 1 / 18 * Y ^ 3 - 1 / 3 * Y + 1 / 3 = t at *
  generalize -2 / 45 * Y ^ 3 * Z ^ 6 - 1 / 18 * Y ^ 3 + 1 / 6 * Y = s at *
  generalize 1 / 90 * Y ^ 3 * Z ^ 6 - 1 / 9 * Y ^ 3 + 1 / 6 * Y = w at *
  generalize 1 / 90 * Y ^ 3 * Z ^ 6 + 1 / 18 * Y ^ 3 = v at *
  have hC := ac1_leastClass_eq (τ := $τ) $L v (by decide) (by decide) (by
    intro i hi
    ac1_interval i hi)
  refine ⟨hC, ac1_secondClass_eq hC $S w (by decide) (by decide) (by decide) (by
    intro i hi
    ac1_interval i hi)⟩))

macro "ac1_p7" τ:ident h:ident r:term:max A:term:max B:term:max L:term:max M:term:max : tactic => `(tactic| (
  have hd := $r $τ $h
  have h1 := hd 1 (by decide)
  have h2 := hd 2 (by decide)
  have h3 := hd 3 (by decide)
  have h4 := hd 4 (by decide)
  have h5 := hd 5 (by decide)
  have h6 := hd 6 (by decide)
  have h7 := hd 7 (by decide)
  have h8 := hd 8 (by decide)
  have h9 := hd 9 (by decide)
  have h10 := hd 10 (by decide)
  have h11 := hd 11 (by decide)
  have h12 := hd 12 (by decide)
  have h13 := hd 13 (by decide)
  have h14 := hd 14 (by decide)
  have h15 := hd 15 (by decide)
  clear hd
  obtain ⟨x0, x1⟩ := five_exp_bounds $τ (A := $A) (by rw [show _ from $h]; decide) (by decide)
  obtain ⟨z0, z1⟩ := five_exp_bounds $τ (A := $B) (by rw [show _ from $h]; decide) (by decide)
  generalize exp (-($τ).length $A) = X at *
  generalize exp (-($τ).length $B) = Z at *
  have f : X * Z ^ 6 < X := mul_lt_of_lt_one_right x0 (pow_lt_one₀ z0.le z1 (by norm_num))
  have i_vp : 1 / 90 * X * Z ^ 6 + 1 / 18 * X <
      1 / 90 * X * Z ^ 6 - 5 / 18 * X + 1 / 3 := by linarith only [x1, f]
  have i_vq : 1 / 90 * X * Z ^ 6 + 1 / 18 * X <
      -2 / 45 * X * Z ^ 6 + 1 / 9 * X := by linarith only [x1, f]
  have i_vm : 1 / 90 * X * Z ^ 6 + 1 / 18 * X <
      -2 / 45 * X * Z ^ 6 - 2 / 9 * X + 1 / 3 := by linarith only [x1, f]
  have i_pm : 1 / 90 * X * Z ^ 6 - 5 / 18 * X + 1 / 3 <
      -2 / 45 * X * Z ^ 6 - 2 / 9 * X + 1 / 3 := by linarith only [x1, f]
  have i_qm : -2 / 45 * X * Z ^ 6 + 1 / 9 * X <
      -2 / 45 * X * Z ^ 6 - 2 / 9 * X + 1 / 3 := by linarith only [x1, f]
  generalize -2 / 45 * X * Z ^ 6 - 2 / 9 * X + 1 / 3 = m at *
  generalize 1 / 90 * X * Z ^ 6 - 5 / 18 * X + 1 / 3 = p at *
  generalize 1 / 90 * X * Z ^ 6 + 1 / 18 * X = v at *
  generalize -2 / 45 * X * Z ^ 6 + 1 / 9 * X = q at *
  have hC := ac1_leastClass_eq (τ := $τ) $L v (by decide) (by decide) (by
    intro i hi
    ac1_interval i hi)
  refine ⟨hC, ac1_mostProbable_eq $M m (by decide) (by decide) (by
    intro i hi
    ac1_interval i hi)⟩))

/-! ### The rootings of `U5 0` and `U5 1` -/

/-- The classes of gene trees of the rooting `hierarchyOf {{1, 2, 3, 4}}` of `U5 0`
(`P₃ = ((b,c,d,e),a)`), read off its gene tree distribution `rootingDist5_0_1`. -/
theorem ac1_classes_0_1 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{1, 2, 3, 4}}) :
    cls_leastClass τ = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} ∧
      cls_secondClass τ = {13, 14, 15} := by
  ac1_p3 τ h rootingDist5_0_1 {1, 2, 3, 4}

/-- The classes of gene trees of the rooting `hierarchyOf {{0, 2, 3, 4}}` of `U5 0`
(`P₃ = ((a,c,d,e),b)`), read off its gene tree distribution `rootingDist5_0_2`. -/
theorem ac1_classes_0_2 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 2, 3, 4}}) :
    cls_leastClass τ = {1, 2, 3, 5, 6, 8, 9, 11, 12, 13, 14, 15} ∧
      cls_secondClass τ = {4, 7, 10} := by
  ac1_p3 τ h rootingDist5_0_2 {0, 2, 3, 4}

/-- The classes of gene trees of the rooting `hierarchyOf {{0, 1, 3, 4}}` of `U5 0`
(`P₃ = ((a,b,d,e),c)`), read off its gene tree distribution `rootingDist5_0_3`. -/
theorem ac1_classes_0_3 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1, 3, 4}}) :
    cls_leastClass τ = {2, 3, 4, 5, 6, 7, 9, 10, 12, 13, 14, 15} ∧
      cls_secondClass τ = {1, 8, 11} := by
  ac1_p3 τ h rootingDist5_0_3 {0, 1, 3, 4}

/-- The classes of gene trees of the rooting `hierarchyOf {{0, 1, 2, 4}}` of `U5 0`
(`P₃ = ((a,b,c,e),d)`), read off its gene tree distribution `rootingDist5_0_4`. -/
theorem ac1_classes_0_4 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1, 2, 4}}) :
    cls_leastClass τ = {1, 3, 4, 6, 7, 8, 9, 10, 11, 13, 14, 15} ∧
      cls_secondClass τ = {2, 5, 12} := by
  ac1_p3 τ h rootingDist5_0_4 {0, 1, 2, 4}

/-- The classes of gene trees of the rooting `hierarchyOf {{0, 1, 2, 3}}` of `U5 0`
(`P₃ = ((a,b,c,d),e)`), read off its gene tree distribution `rootingDist5_0_5`. -/
theorem ac1_classes_0_5 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1, 2, 3}}) :
    cls_leastClass τ = {1, 2, 4, 5, 7, 8, 10, 11, 12, 13, 14, 15} ∧
      cls_secondClass τ = {3, 6, 9} := by
  ac1_p3 τ h rootingDist5_0_5 {0, 1, 2, 3}

/-- The classes of gene trees of the rooting `hierarchyOf {{2, 3, 4}, {1, 2, 3, 4}}` of `U5 1`
(`P₉ = (((c,d,e),b),a)`), read off its gene tree distribution `rootingDist5_1_3`. -/
theorem ac1_classes_1_3 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{2, 3, 4}, {1, 2, 3, 4}}) :
    cls_leastClass τ = {5, 6, 8, 9, 11, 12} ∧ cls_secondClass τ = {4, 7, 10} := by
  ac1_p9 τ h rootingDist5_1_3 {2, 3, 4} {1, 2, 3, 4} {5, 6, 8, 9, 11, 12} {4, 7, 10}

/-- The classes of gene trees of the rooting `hierarchyOf {{2, 3, 4}, {0, 2, 3, 4}}` of `U5 1`
(`P₉ = (((c,d,e),a),b)`), read off its gene tree distribution `rootingDist5_1_4`. -/
theorem ac1_classes_1_4 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{2, 3, 4}, {0, 2, 3, 4}}) :
    cls_leastClass τ = {5, 6, 8, 9, 11, 12} ∧ cls_secondClass τ = {13, 14, 15} := by
  ac1_p9 τ h rootingDist5_1_4 {2, 3, 4} {0, 2, 3, 4} {5, 6, 8, 9, 11, 12} {13, 14, 15}

/-- The classes of gene trees of the rooting `hierarchyOf {{0, 1}, {0, 1, 3, 4}}` of `U5 1`
(`P₇ = (((a,b),d,e),c)`), read off its gene tree distribution `rootingDist5_1_5`. -/
theorem ac1_classes_1_5 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1}, {0, 1, 3, 4}}) :
    cls_leastClass τ = {4, 5, 6, 7, 9, 10, 12, 13, 14, 15} ∧
      cls_mostProbable τ = {1} := by
  ac1_p7 τ h rootingDist5_1_5 {0, 1} {0, 1, 3, 4} {4, 5, 6, 7, 9, 10, 12, 13, 14, 15} {1}

/-- The classes of gene trees of the rooting `hierarchyOf {{0, 1}, {0, 1, 2, 4}}` of `U5 1`
(`P₇ = (((a,b),c,e),d)`), read off its gene tree distribution `rootingDist5_1_6`. -/
theorem ac1_classes_1_6 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2, 4}}) :
    cls_leastClass τ = {4, 6, 7, 8, 9, 10, 11, 13, 14, 15} ∧
      cls_mostProbable τ = {2} := by
  ac1_p7 τ h rootingDist5_1_6 {0, 1} {0, 1, 2, 4} {4, 6, 7, 8, 9, 10, 11, 13, 14, 15} {2}

/-- The classes of gene trees of the rooting `hierarchyOf {{0, 1}, {0, 1, 2, 3}}` of `U5 1`
(`P₇ = (((a,b),c,d),e)`), read off its gene tree distribution `rootingDist5_1_7`. -/
theorem ac1_classes_1_7 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2, 3}}) :
    cls_leastClass τ = {4, 5, 7, 8, 10, 11, 12, 13, 14, 15} ∧
      cls_mostProbable τ = {3} := by
  ac1_p7 τ h rootingDist5_1_7 {0, 1} {0, 1, 2, 3} {4, 5, 7, 8, 10, 11, 12, 13, 14, 15} {3}

/-! ### The representatives `P₂` and `P₃` (Table 7) -/

/-- Table 7 for `P₂ = (a,b,c,(d,e):z)`: the least probable class is the complement of
`{T₁, T₄, T₁₃}`, the class with the second smallest probability. -/
theorem ac1_classes_P2 (σ : SpeciesTree (Fin 5)) (h : σ.clusters = polytomy5 2) :
    cls_leastClass σ = Icc 1 15 \ {1, 4, 13} ∧ cls_secondClass σ = {1, 4, 13} := by
  obtain ⟨z0, z1⟩ := five_exp_bounds σ (A := {3, 4}) (by rw [h]; decide) (by decide)
  exact ac1_classes_two {1, 4, 13} (1 / 3 - 4 / 15 * exp (-σ.length {3, 4}))
    (1 / 15 * exp (-σ.length {3, 4})) (by decide) (by decide) (by decide)
    (fun i hi => (table7 σ i hi).2.1 h) (by linarith)

/-- Table 7 for `P₃ = ((a,b,c,d):z,e)`: the least probable class is the complement of
`{T₃, T₆, T₉}`, the class with the second smallest probability. -/
theorem ac1_classes_P3 (σ : SpeciesTree (Fin 5)) (h : σ.clusters = polytomy5 3) :
    cls_leastClass σ = Icc 1 15 \ {3, 6, 9} ∧ cls_secondClass σ = {3, 6, 9} := by
  obtain ⟨z0, z1⟩ := five_exp_bounds σ (A := {0, 1, 2, 3}) (by rw [h]; decide) (by decide)
  have hz : exp (-σ.length {0, 1, 2, 3}) ^ 6 < 1 := pow_lt_one₀ z0.le z1 (by norm_num)
  exact ac1_classes_two {3, 6, 9} (1 / 9 - 2 / 45 * exp (-σ.length {0, 1, 2, 3}) ^ 6)
    (1 / 18 + 1 / 90 * exp (-σ.length {0, 1, 2, 3}) ^ 6) (by decide) (by decide) (by decide)
    (fun i hi => (table7 σ i hi).2.2.1 h) (by linarith)

end ADR11
