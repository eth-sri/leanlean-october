module

public import PottsDiscontinuity.SixVertex.InfinityDefectMotion
public import PottsDiscontinuity.SixVertex.InfinityMoves

/-! # Admissible labelled defect choices and their upper row -/

@[expose] public section

open Finset Matrix

namespace PottsDiscontinuity.SixVertex

variable {N n : ℕ}

section
variable (x : Finset (Fin N))
/-- Defects indexed by their actual cyclic sites. -/
abbrev DefectSite  := {i : Fin N // i ∈ defects x}

/-- `true` chooses a left unit move and `false` a right unit move. -/
abbrev DefectChoice  := DefectSite x → Bool

/-- A right-then-left choice at adjacent defects would exchange them and is forbidden. -/
def AdmissibleDefectChoice (d : DefectChoice x) : Prop :=
  ∀ i : DefectSite x, ∀ hj : nxt i.1 ∈ defects x,
    d i = false → d ⟨nxt i.1, hj⟩ = false
end

instance (x : Finset (Fin N)) (d : DefectChoice x) : Decidable (AdmissibleDefectChoice x d) := by
  unfold AdmissibleDefectChoice
  infer_instance

/-- Horizontal arrows are reconstructed from the defect choices and the forced up switches. -/
def horizontalOfDefectChoice (x : Finset (Fin N)) (d : DefectChoice x) : Fin N → Bool :=
  fun i => if hd : nxt i ∈ defects x then d ⟨nxt i, hd⟩ else decide (i ∈ x)

section
variable (h : Fin N → Bool)
/-- The upper up arrows are exactly the down switches of the horizontal arrows. -/
def upperOfHorizontal  : Finset (Fin N) :=
  univ.filter fun i => h (prv i) = true ∧ h i = false

@[simp] theorem mem_upperOfHorizontal (i : Fin N) :
    i ∈ upperOfHorizontal h ↔ h (prv i) = true ∧ h i = false := by
  simp only [upperOfHorizontal, mem_filter, mem_univ, true_and]
end

/-- A choice is recovered exactly at the predecessor of its defect. -/
theorem horizontalOfDefectChoice_prv (x : Finset (Fin N)) (d : DefectChoice x)
    (i : DefectSite x) : horizontalOfDefectChoice x d (prv i.1) = d i := by
  unfold horizontalOfDefectChoice
  grind

section
variable {x : Finset (Fin N)} (hx : NoConsecutiveUp x) (d : DefectChoice x)
include hx
theorem horizontalOfDefectChoice_up {i : Fin N} (hi : i ∈ x) :
    horizontalOfDefectChoice x d (prv i) = false ∧ horizontalOfDefectChoice x d i = true := by
  have hn : nxt i ∉ defects x := by
    rw [mem_defects_iff]
    grind
  have hd : i ∉ defects x := by simp_all
  have hp : prv i ∉ x := by
    intro hp
    exact hx (prv i) hp (by grind)
  simp only [horizontalOfDefectChoice, nxt, prv, Equiv.apply_symm_apply,
    dite_eq_right hd, dite_eq_right hn, decide_eq_false hp, decide_eq_true hi, and_self]

/-- Admissibility excludes every additional up switch. -/
theorem horizontalOfDefectChoice_up_iff (ha : AdmissibleDefectChoice x d) (i : Fin N) :
    i ∈ x ↔ horizontalOfDefectChoice x d (prv i) = false ∧
      horizontalOfDefectChoice x d i = true := by
  constructor
  · exact horizontalOfDefectChoice_up hx d
  · rintro ⟨hp, hi⟩
    by_contra hix
    by_cases hdi : i ∈ defects x
    · have hp' :=
        (horizontalOfDefectChoice_prv x d ⟨i, hdi⟩).symm.trans hp
      by_cases hdn : nxt i ∈ defects x
      · have hdnext := ha ⟨i, hdi⟩ hdn hp'
        grind [horizontalOfDefectChoice]
      grind [horizontalOfDefectChoice]
    simp_all [prv, horizontalOfDefectChoice_up]

/-- Every admissible choice realizes an ice-rule row. -/
theorem flux_horizontalOfDefectChoice (ha : AdmissibleDefectChoice x d) :
    Flux x (upperOfHorizontal (horizontalOfDefectChoice x d)) (horizontalOfDefectChoice x d) := by
  intro i
  simp only [mem_upperOfHorizontal, (horizontalOfDefectChoice_up_iff hx d ha i)]
  cases hp : horizontalOfDefectChoice x d (prv i) <;>
    cases hi : horizontalOfDefectChoice x d i <;> norm_num [toInt]

theorem disjoint_upperOfDefectChoice  : Disjoint x (upperOfHorizontal (horizontalOfDefectChoice x d)) := by
  apply disjoint_left.mpr
  simp_all [horizontalOfDefectChoice_up, mem_upperOfHorizontal]
end

/-- Cardinality conservation for the generic cyclic flux equation. -/
theorem Flux.card_eq_generic {x y : Finset (Fin N)} {h : Fin N → Bool} (hf : Flux x y h) :
    x.card = y.card := by
  cases N with
  | zero => exact congrArg Finset.card (Subsingleton.elim _ _)
  | succ k => exact hf.card_eq

/-- The actual independent upper state associated to an admissible choice. -/
def defectChoiceUpperState (x : IndependentState N n)
    (d : {d : DefectChoice x.1.1 // AdmissibleDefectChoice x.1.1 d}) : IndependentState N n :=
  let y := upperOfHorizontal (horizontalOfDefectChoice x.1.1 d.1)
  have hf := flux_horizontalOfDefectChoice x.2 d.1 d.2
  have hd := disjoint_upperOfDefectChoice x.2 d.1
  ⟨⟨y, hf.card_eq_generic.symm.trans x.1.2⟩,
    noConsecutiveUp_of_interlaced_disjoint (interlaced_of_flux hf).symm hd.symm⟩

/-- Admissible choices produce genuine limiting-matrix edges. -/
theorem infinityRestriction_defectChoiceUpperState (hn : 0 < n) (x : IndependentState N n)
    (d : {d : DefectChoice x.1.1 // AdmissibleDefectChoice x.1.1 d}) :
    infinityRestriction N n x (defectChoiceUpperState x d) = 1 := by
  apply (infinityBlock_eq_one_iff hn _ _).mpr
  exact ⟨interlaced_of_flux (flux_horizontalOfDefectChoice x.2 d.1 d.2),
    disjoint_upperOfDefectChoice x.2 d.1⟩

/-- The labelled choice read from an ice-rule row. -/
def defectChoiceOfHorizontal (x : Finset (Fin N)) (h : Fin N → Bool) : DefectChoice x :=
  fun i => h (prv i.1)

section
variable {x y : Finset (Fin N)} {h : Fin N → Bool} (hf : Flux x y h) (hd : Disjoint x y)
include x y hf hd
/-- Every disjoint transfer row is recovered from its choices at the defects. -/
theorem Flux.horizontalOfDefectChoice_inverse  :
    horizontalOfDefectChoice x (defectChoiceOfHorizontal x h) = h := by
  funext i
  by_cases hi : nxt i ∈ defects x
  · simp only [horizontalOfDefectChoice, dite_eq_left hi, defectChoiceOfHorizontal,
      prv, nxt, Equiv.symm_apply_apply]
  · have hdi : i ∈ x ∨ nxt i ∈ x := by
      rw [mem_defects_iff] at hi
      grind
    simp only [horizontalOfDefectChoice, dite_eq_right hi]
    rcases hdi with hx | hx
    · have hh := (hf.local_disjoint hd i).1.mp hx
      simp_all
    · have hh := (hf.local_disjoint hd (nxt i)).1.mp hx |>.1
      simp only [prv, nxt, Equiv.symm_apply_apply] at hh
      have hix : i ∉ x := by
        intro hix
        have hi' := (hf.local_disjoint hd i).1.mp hix |>.2
        simp_all
      simp_all

/-- The choices of a disjoint transfer row cannot exchange adjacent defects. -/
theorem Flux.admissibleDefectChoice  :
    AdmissibleDefectChoice x (defectChoiceOfHorizontal x h) := by
  intro i hj hi
  change h (prv i.1) = false at hi
  change h (prv (nxt i.1)) = false
  rw [show prv (nxt i.1) = i.1 from (finRotate N).symm_apply_apply i.1]
  have hix := (mem_defects_iff x i.1).mp i.2 |>.1
  have hup := (hf.local_disjoint hd i.1).1
  simp_all

/-- The upper row of a disjoint flux configuration is its set of horizontal down switches. -/
theorem Flux.upperOfHorizontal_eq  : upperOfHorizontal h = y := by
  ext i
  exact (mem_upperOfHorizontal h i).trans (hf.local_disjoint hd i).2.symm
end

/-- Nonempty disjoint vertical states admit at most one horizontal flux solution. -/
theorem Flux.unique_of_disjoint {x y : Finset (Fin N)} {h g : Fin N → Bool}
    (hf : Flux x y h) (hg : Flux x y g) (hd : Disjoint x y) (hx : x.Nonempty) : h = g := by
  have hxy : x ≠ y := by
    grind
  cases N with
  | zero =>
    obtain ⟨i, _⟩ := hx
    exact Fin.elim0 i
  | succ k =>
    have hc := card_flux x y
    rw [ite_eq_right hxy, ite_eq_left (interlaced_of_flux hf)] at hc
    obtain ⟨a, ha⟩ := card_eq_one.mp hc
    have hh : h ∈ (univ.filter fun h : Fin (k + 1) → Bool => Flux x y h) := by grind
    have hh' : g ∈ (univ.filter fun h : Fin (k + 1) → Bool => Flux x y h) := by grind
    simp_all

section
variable (hn : 0 < n)
include hn
/-- Distinct admissible labelled choices give distinct neighboring row states. -/
theorem defectChoiceUpperState_injective (x : IndependentState N n) :
    Function.Injective (defectChoiceUpperState x) := by
  intro d e he
  have hd := flux_horizontalOfDefectChoice x.2 d.1 d.2
  have he' := flux_horizontalOfDefectChoice x.2 e.1 e.2
  have hval := congrArg (fun y : IndependentState N n => y.1.1) he
  change upperOfHorizontal (horizontalOfDefectChoice x.1.1 d.1) =
    upperOfHorizontal (horizontalOfDefectChoice x.1.1 e.1) at hval
  rw [← hval] at he'
  have hx : x.1.1.Nonempty := by grind
  apply Subtype.ext
  funext i
  have hh' := congrFun (hd.unique_of_disjoint he' (disjoint_upperOfDefectChoice x.2 d.1) hx) (prv i.1)
  grind [horizontalOfDefectChoice_prv]

/-- Every genuine neighbor comes from an admissible labelled choice. -/
theorem exists_defectChoiceUpperState (x y : IndependentState N n)
    (hxy : infinityRestriction N n x y = 1) :
    ∃ d : {d : DefectChoice x.1.1 // AdmissibleDefectChoice x.1.1 d},
      defectChoiceUpperState x d = y := by
  obtain ⟨hi, hd⟩ := (infinityBlock_eq_one_iff hn x.1 y.1).mp hxy
  obtain ⟨h, hf⟩ := exists_flux_of_interlaced hi
  let d : {d : DefectChoice x.1.1 // AdmissibleDefectChoice x.1.1 d} :=
    ⟨defectChoiceOfHorizontal x.1.1 h, hf.admissibleDefectChoice hd⟩
  refine ⟨d, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change upperOfHorizontal (horizontalOfDefectChoice x.1.1 (defectChoiceOfHorizontal x.1.1 h)) = y.1.1
  rw [hf.horizontalOfDefectChoice_inverse hd, hf.upperOfHorizontal_eq hd]

/-- Exact finite-state row summation over the admissible labelled choices. -/
theorem infinityRestriction_mulVec_eq_sum_choices (x : IndependentState N n)
    (v : IndependentState N n → ℝ) :
    (infinityRestriction N n *ᵥ v) x =
      ∑ d : {d : DefectChoice x.1.1 // AdmissibleDefectChoice x.1.1 d}, v (defectChoiceUpperState x d) := by
  have hs : (∑ d : {d : DefectChoice x.1.1 // AdmissibleDefectChoice x.1.1 d},
      v (defectChoiceUpperState x d)) =
      ∑ y ∈ univ.filter (fun y => infinityRestriction N n x y = 1), v y := by
    apply sum_bij (fun d _ => defectChoiceUpperState x d)
    · simp_all [infinityRestriction_defectChoiceUpperState]
    · grind [defectChoiceUpperState_injective]
    · grind [exists_defectChoiceUpperState]
    simp
  rw [hs, Matrix.mulVec, dotProduct, sum_filter]
  apply sum_congr rfl
  intro y _
  change infinityBlock N n x.1 y.1 * v y =
    if infinityBlock N n x.1 y.1 = 1 then v y else 0
  unfold infinityBlock
  split_ifs <;> simp_all [Nat.ne_of_gt hn]
end

end PottsDiscontinuity.SixVertex
