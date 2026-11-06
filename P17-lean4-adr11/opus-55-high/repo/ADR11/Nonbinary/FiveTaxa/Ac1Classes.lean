module

public import ADR11.Identifiability.FiveTaxa.Classes
public import ADR11.Identifiability.FiveTaxa.Common
public meta import ADR11.Rootings.Proofs

/-!
# Appendix C: the classes of gene trees of the nonbinary rootings

The proof of Proposition 11 (Appendix C of the paper) tells the rootings of an unrooted five-taxon
species tree apart by their classes of equiprobable gene trees: the least probable class `𝒞` and
the class with the second smallest probability. This module computes these classes from the gene
tree distributions of Table 7 (`msc_have`, the formulas of Table 7 for each labelling), or by
permuting labels (`cls_classes_of`).

## Main results

* `ac1_classes_0_j` (`j = 1, …, 5`, the rootings of shape `P₃` of the star `U5 0`) and
  `ac1_classes_1_j` (`j = 3, …, 7`, the rootings of shapes `P₉` and `P₇` of `U5 1 = AB|CDE`).
* `ac1_classes_P1`, `ac1_classes_P2`, `ac1_classes_P4`, `ac1_classes_P8` (the other rootings of
  `U5 0` and `U5 1`), `ac1_classes_P5`, `ac1_classes_P6` (rootings of `U5 2`).
-/

@[expose] public section

namespace ADR11

open Finset Real

/-- The classes of gene trees of the rooting `hierarchyOf {{0, 1, 2, 3}}` of `U5 0`
(`P₃ = ((a,b,c,d),e)`). -/
theorem ac1_classes_0_5 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1, 2, 3}}) :
    cls_leastClass τ = {1, 2, 4, 5, 7, 8, 10, 11, 12, 13, 14, 15} ∧
      cls_secondClass τ = {3, 6, 9} := by
  msc_have h
  obtain ⟨z0, z1⟩ := five_exp_bounds h {0, 1, 2, 3}
  have := pow_lt_one₀ z0.le z1 (by norm_num : 6 ≠ 0)
  ac1_cases ac1_least_second (u τ 1) (u τ 3) using this

/-- The classes of gene trees of the rooting `hierarchyOf {{1, 2, 3, 4}}` of `U5 0`
(`P₃ = ((b,c,d,e),a)`). -/
theorem ac1_classes_0_1 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{1, 2, 3, 4}}) :
    cls_leastClass τ = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} ∧
      cls_secondClass τ = {13, 14, 15} :=
  cls_classes_of (Equiv.swap 0 4) (ac1_classes_0_5 _ ·) h

/-- The classes of gene trees of the rooting `hierarchyOf {{0, 2, 3, 4}}` of `U5 0`
(`P₃ = ((a,c,d,e),b)`). -/
theorem ac1_classes_0_2 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 2, 3, 4}}) :
    cls_leastClass τ = {1, 2, 3, 5, 6, 8, 9, 11, 12, 13, 14, 15} ∧
      cls_secondClass τ = {4, 7, 10} :=
  cls_classes_of (Equiv.swap 1 4) (ac1_classes_0_5 _ ·) h

/-- The classes of gene trees of the rooting `hierarchyOf {{0, 1, 3, 4}}` of `U5 0`
(`P₃ = ((a,b,d,e),c)`). -/
theorem ac1_classes_0_3 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1, 3, 4}}) :
    cls_leastClass τ = {2, 3, 4, 5, 6, 7, 9, 10, 12, 13, 14, 15} ∧
      cls_secondClass τ = {1, 8, 11} :=
  cls_classes_of (Equiv.swap 2 4) (ac1_classes_0_5 _ ·) h

/-- The classes of gene trees of the rooting `hierarchyOf {{0, 1, 2, 4}}` of `U5 0`
(`P₃ = ((a,b,c,e),d)`). -/
theorem ac1_classes_0_4 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1, 2, 4}}) :
    cls_leastClass τ = {1, 3, 4, 6, 7, 8, 9, 10, 11, 13, 14, 15} ∧
      cls_secondClass τ = {2, 5, 12} :=
  cls_classes_of (Equiv.swap 3 4) (ac1_classes_0_5 _ ·) h

/-- The classes of gene trees of the rooting `hierarchyOf {{2, 3, 4}, {1, 2, 3, 4}}` of `U5 1`
(`P₉ = (((c,d,e),b),a)`). -/
theorem ac1_classes_1_3 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{2, 3, 4}, {1, 2, 3, 4}}) :
    cls_leastClass τ = {5, 6, 8, 9, 11, 12} ∧ cls_secondClass τ = {4, 7, 10} := by
  msc_have h
  obtain ⟨y0, y1⟩ := five_exp_bounds h {2, 3, 4}
  obtain ⟨z0, z1⟩ := five_exp_bounds h {1, 2, 3, 4}
  generalize exp (-τ.length {2, 3, 4}) = Y at *
  have := sub_pos.2 y1
  generalize exp (-τ.length {1, 2, 3, 4}) = Z at *
  have f1 : 0 < Y * ((1 - Y) * (1 + Y)) := by positivity
  have f2 : 0 < (1 - Y) ^ 2 * (2 + Y) := by positivity
  have f3 : Y ^ 3 * Z ^ 6 < Y ^ 3 :=
    mul_lt_of_lt_one_right (pow_pos y0 3) (pow_lt_one₀ z0.le z1 (by norm_num))
  ac1_cases ac1_least_second (u τ 5) (u τ 4) using y1, f1, f2, f3

/-- The classes of gene trees of the rooting `hierarchyOf {{2, 3, 4}, {0, 2, 3, 4}}` of `U5 1`
(`P₉ = (((c,d,e),a),b)`). -/
theorem ac1_classes_1_4 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{2, 3, 4}, {0, 2, 3, 4}}) :
    cls_leastClass τ = {5, 6, 8, 9, 11, 12} ∧ cls_secondClass τ = {13, 14, 15} :=
  cls_classes_of (Equiv.swap 0 1) (ac1_classes_1_3 _ ·) h

/-- The least probable class of the rooting `hierarchyOf {{0, 1}, {0, 1, 2, 3}}` of `U5 1`
(`P₇ = (((a,b),c,d),e)`). -/
theorem ac1_classes_1_7 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2, 3}}) :
    cls_leastClass τ = {4, 5, 7, 8, 10, 11, 12, 13, 14, 15} := by
  msc_have h
  obtain ⟨x0, x1⟩ := five_exp_bounds h {0, 1}
  obtain ⟨z0, z1⟩ := five_exp_bounds h {0, 1, 2, 3}
  have := mul_lt_of_lt_one_right x0 (pow_lt_one₀ z0.le z1 (by norm_num : 6 ≠ 0))
  ac1_cases ac1_least (u τ 4) using x1, this

/-- The least probable class of the rooting `hierarchyOf {{0, 1}, {0, 1, 3, 4}}` of `U5 1`
(`P₇ = (((a,b),d,e),c)`). -/
theorem ac1_classes_1_5 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1}, {0, 1, 3, 4}}) :
    cls_leastClass τ = {4, 5, 6, 7, 9, 10, 12, 13, 14, 15} :=
  cls_least_of (Equiv.swap 2 4) (ac1_classes_1_7 _ ·) h

/-- The least probable class of the rooting `hierarchyOf {{0, 1}, {0, 1, 2, 4}}` of `U5 1`
(`P₇ = (((a,b),c,e),d)`). -/
theorem ac1_classes_1_6 (τ : SpeciesTree (Fin 5))
    (h : τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2, 4}}) :
    cls_leastClass τ = {4, 6, 7, 8, 9, 10, 11, 13, 14, 15} :=
  cls_least_of (Equiv.swap 3 4) (ac1_classes_1_7 _ ·) h

/-! ### The other rootings (Table 7) -/

/-- Table 7 for `P₂ = ((a,b):z,c,d,e)`: the least probable class is the complement of
`{T₁, T₂, T₃}`, the class with the second smallest probability. -/
theorem ac1_classes_P2 (σ : SpeciesTree (Fin 5)) (h : σ.clusters = hierarchyOf {{0, 1}}) :
    cls_leastClass σ = Icc 1 15 \ {1, 2, 3} ∧ cls_secondClass σ = {1, 2, 3} := by
  msc_have h
  obtain ⟨z0, z1⟩ := five_exp_bounds h {0, 1}
  ac1_cases ac1_least_second (u σ 4) (u σ 1) using z1

/-- Table 7 for `P₁ = (a,b,c,d,e)`: all gene trees are equiprobable. -/
theorem ac1_classes_P1 (σ : SpeciesTree (Fin 5)) (h : σ.clusters = hierarchyOf ∅) :
    cls_leastClass σ = Icc 1 15 := by
  msc_have h
  ac1_cases ac1_least (1 / 15) using h

/-- Table 7 for `P₄ = ((c,d,e):y,a,b)`. -/
theorem ac1_classes_P4 (σ : SpeciesTree (Fin 5)) (h : σ.clusters = hierarchyOf {{2, 3, 4}}) :
    cls_leastClass σ = {5, 6, 8, 9, 11, 12} ∧ cls_secondClass σ = {4, 7, 10, 13, 14, 15} := by
  msc_have h
  obtain ⟨y0, y1⟩ := five_exp_bounds h {2, 3, 4}
  generalize exp (-σ.length {2, 3, 4}) = Y at *
  have := sub_pos.2 y1
  have f1 : 0 < Y * ((1 - Y) * (1 + Y)) := by positivity
  have f2 : 0 < (1 - Y) ^ 2 * (2 + Y) := by positivity
  ac1_cases ac1_least_second (u σ 5) (u σ 4) using f1, f2

/-- Table 7 for `P₅ = ((a,b):x,(d,e):y,c)`. -/
theorem ac1_classes_P5 (σ : SpeciesTree (Fin 5)) (h : σ.clusters = hierarchyOf {{0, 1}, {3, 4}}) :
    cls_leastClass σ = {5, 6, 7, 8, 9, 10, 11, 12, 14, 15} := by
  msc_have h
  obtain ⟨x0, x1⟩ := five_exp_bounds h {0, 1}
  obtain ⟨y0, y1⟩ := five_exp_bounds h {3, 4}
  ac1_cases ac1_least (u σ 5) using x1, y1, mul_lt_mul_of_pos_left x1 y0, mul_lt_mul_of_pos_left y1 x0, mul_pos (sub_pos.2 x1) (sub_pos.2 y1)

/-- Table 7 for `P₆ = (((a,b):x,c):y,d,e)`. -/
theorem ac1_classes_P6 (σ : SpeciesTree (Fin 5)) (h : σ.clusters = hierarchyOf {{0, 1}, {0, 1, 2}}) :
    cls_leastClass σ = {7, 8, 10, 11, 14, 15} ∧ cls_secondClass σ = {5, 6, 9, 12} := by
  msc_have h
  obtain ⟨x0, x1⟩ := five_exp_bounds h {0, 1}
  obtain ⟨y0, y1⟩ := five_exp_bounds h {0, 1, 2}
  generalize exp (-σ.length {0, 1}) = X at *
  generalize exp (-σ.length {0, 1, 2}) = Y at *
  have := sub_pos.2 y1
  have f1 : 0 < X * Y * ((1 - Y) * (1 + Y)) := by positivity
  have f2 : 0 < X * ((1 - Y) ^ 2 * (2 + Y)) := by positivity
  have f5 : 0 < (1 - X) * (3 - 2 * Y) := mul_pos (sub_pos.2 x1) (by linarith)
  ac1_cases ac1_least_second (u σ 7) (u σ 5) using x1, y1, f1, f2, mul_lt_mul_of_pos_left x1 y0, mul_lt_mul_of_pos_left y1 x0, f5

/-- Table 7 for `P₈ = ((c,d,e):y,(a,b):z)`. -/
theorem ac1_classes_P8 (σ : SpeciesTree (Fin 5)) (h : σ.clusters = hierarchyOf {{0, 1}, {2, 3, 4}}) :
    cls_leastClass σ = {5, 6, 8, 9, 11, 12} ∧ cls_secondClass σ = {4, 7, 10, 13, 14, 15} := by
  msc_have h
  obtain ⟨y0, y1⟩ := five_exp_bounds h {2, 3, 4}
  obtain ⟨z0, z1⟩ := five_exp_bounds h {0, 1}
  generalize exp (-σ.length {2, 3, 4}) = Y at *
  have := sub_pos.2 y1
  generalize exp (-σ.length {0, 1}) = Z at *
  have f1 : 0 < Y * Z * ((1 - Y) * (1 + Y)) := by positivity
  have f2 : 0 < Z * ((1 - Y) ^ 2 * (2 + Y)) := by positivity
  ac1_cases ac1_least_second (u σ 5) (u σ 4) using z1, f1, f2

end ADR11
