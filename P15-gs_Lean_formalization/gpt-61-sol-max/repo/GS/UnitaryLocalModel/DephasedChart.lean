import Mathlib.Tactic

import GS.UnitaryLocalModel.DephasedDifferential


set_option backward.isDefEq.respectTransparency false
/-!
# An actual local chart on the dephased unitary slice

The real implicit function theorem is applied to the proved surjective anchor
constraint derivative. Positivity is an open restriction. All unitary and
slice spaces retain their inherited matrix topology.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS.UnitaryManifold
namespace GS.UnitaryLocalModel
variable (Q A : CMat q) (o : Fin q)

/-- The strict inequalities defining the positive branch of the anchor slice. -/
def AnchorPositive  : Prop :=
  (∀ i, 0 < (A i o / Q i o).re) ∧ (∀ j, 0 < (A o j / Q o j).re)

theorem anchorPositive_open  :
    IsOpen {A : CMat q | AnchorPositive Q A o} := by
  have h (i j : Fin q) : IsOpen {A : CMat q | 0 < (A i j / Q i j).re} :=
    isOpen_lt continuous_const (by fun_prop)
  simpa [AnchorPositive, Set.ofPred_and, Set.ofPred_forall] using
    (isOpen_iInter_of_finite fun i => h i o).inter (isOpen_iInter_of_finite fun j => h o j)

theorem anchorPositive_self 
    (hQ : AnchorNonzero Q Q o) : AnchorPositive Q Q o := by
  constructor
  · intro i; simp [div_self (hQ.1 i).1]
  · intro j; simp [div_self (hQ.2 j).1]

theorem anchorImag_eq_zero_iff  :
    anchorImag Q o A = 0 ↔
      (∀ i, (A i o / Q i o).im = 0) ∧ (∀ j, (A o j / Q o j).im = 0) := by
  constructor
  · intro h
    have hc : ∀ i, (A i o / Q i o).im = 0 := fun i =>
      congrArg (fun p : AnchorCoordinates o => p.1 i) h
    refine ⟨hc, ?_⟩
    intro j
    by_cases hj : j = o
    · aesop
    · exact congrArg (fun p : AnchorCoordinates o => p.2 ⟨j,hj⟩) h
  · aesop

theorem complex_positive_real_iff (z : ℂ) :
    (∃ r : ℝ, 0 < r ∧ z = r) ↔ z.im = 0 ∧ 0 < z.re := by
  constructor
  · aesop
  · rintro ⟨hi,hr⟩
    refine ⟨z.re,hr,?_⟩
    apply Complex.ext
    · rfl
    · exact hi

theorem dephased_constraints_iff  :
    anchorImag Q o A = 0 ∧ AnchorPositive Q A o ↔
      (∀ i, ∃ r : ℝ, 0 < r ∧ A i o / Q i o = r) ∧
      (∀ j, ∃ r : ℝ, 0 < r ∧ A o j / Q o j = r) := by
  simp only [complex_positive_real_iff, anchorImag_eq_zero_iff, AnchorPositive, forall_and]
  tauto

variable (Q : FullUnitary q) (o : Fin q)

/-- An iterated matrix subtype; no topology is transported to this space. -/
abbrev DephasedUnitary  :=
  {A : FullUnitary q // anchorImag Q.val o A.val = 0 ∧ AnchorPositive Q.val A.val o}

abbrev DephasedModel  :=
  ↥(LinearMap.ker (anchorDerivative Q o : FullSkewModel q →ₗ[ℝ] AnchorCoordinates o))

variable (hQ : AnchorNonzero Q.val Q.val o)

/-- The actual implicit-function chart of the Cayley constraint map. -/
def constraintChart 
 :
    OpenPartialHomeomorph (FullSkewModel q) (AnchorCoordinates o × DephasedModel Q o) :=
  (anchorConstraints_hasStrictFDerivAt Q o).implicitToOpenPartialHomeomorph
    (anchorConstraints Q o) (anchorDerivative Q o) (anchorDerivative_range Q o hQ)

@[simp] theorem constraintChart_fst 
 (x : FullSkewModel q) :
    (constraintChart Q o hQ x).1 = anchorConstraints Q o x :=
  rfl

@[simp] theorem constraintChart_zero 
 : constraintChart Q o hQ 0 = (0,0) := by simp_all [constraintChart,anchorConstraints_zero,HasStrictFDerivAt.implicitToOpenPartialHomeomorph_self]

theorem zero_mem_constraintChart_source 
 : (0 : FullSkewModel q) ∈ (constraintChart Q o hQ).source :=
  (anchorConstraints_hasStrictFDerivAt Q o).mem_implicitToOpenPartialHomeomorph_source
    (anchorDerivative_range Q o hQ)

/-- First pass to Cayley coordinates, then straighten the constraints, and
restrict to the open positive branch. -/
def unitaryConstraintChart 
 :
    OpenPartialHomeomorph (FullUnitary q) (AnchorCoordinates o × DephasedModel Q o) :=
  ((blockPartialChart Q).trans (constraintChart Q o hQ)).restrOpen
    {A | AnchorPositive Q.val A.val o}
    ((anchorPositive_open Q.val o).preimage continuous_subtype_val)

theorem unitaryConstraintChart_source_iff 
 (A : FullUnitary q) :
    A ∈ (unitaryConstraintChart Q o hQ).source ↔
      A ∈ chartSource Q ∧ chartMap Q A.val ∈ (constraintChart Q o hQ).source ∧
        AnchorPositive Q.val A.val o := and_assoc

theorem base_mem_unitaryConstraintChart_source 
 : Q ∈ (unitaryConstraintChart Q o hQ).source := by simp_all [anchorPositive_self,unitaryConstraintChart_source_iff,zero_mem_constraintChart_source,base_mem_chartSource]

@[simp] theorem unitaryConstraintChart_base 
 : unitaryConstraintChart Q o hQ Q = (0,0) := by
  change constraintChart Q o hQ (chartMap Q Q.val) = _
  rw [chartMap_base, constraintChart_zero]

theorem unitaryConstraintChart_fst 
 (A : FullUnitary q)
    (hA : A ∈ (unitaryConstraintChart Q o hQ).source) :
    (unitaryConstraintChart Q o hQ A).1 = anchorImag Q.val o A.val := by
  change (constraintChart Q o hQ (chartMap Q A.val)).1 = _
  rw [constraintChart_fst]
  unfold anchorConstraints
  rw [chartInv_chartMap Q A ((unitaryConstraintChart_source_iff Q o hQ A).mp hA).1]

/-- Open coordinates on the zero constraint level. -/
def dephasedChartDomain 
 : Set (DephasedModel Q o) :=
  {y | (0,y) ∈ (unitaryConstraintChart Q o hQ).target}

def dephasedParametrization 
 (y : DephasedModel Q o) : CMat q :=
  ((unitaryConstraintChart Q o hQ).symm (0,y)).val

theorem dephasedChartDomain_open 
 : IsOpen (dephasedChartDomain Q o hQ) :=
  (unitaryConstraintChart Q o hQ).open_target.preimage (continuous_const.prodMk continuous_id)

theorem zero_mem_dephasedChartDomain 
 : (0 : DephasedModel Q o) ∈ dephasedChartDomain Q o hQ := by
  change (0, 0) ∈ (unitaryConstraintChart Q o hQ).target
  simpa only [unitaryConstraintChart_base] using (unitaryConstraintChart Q o hQ).map_source
    (base_mem_unitaryConstraintChart_source Q o hQ)

@[simp] theorem dephasedParametrization_zero 
 : dephasedParametrization Q o hQ 0 = Q.val := by
  simpa only [dephasedParametrization, unitaryConstraintChart_base] using
    congrArg Subtype.val ((unitaryConstraintChart Q o hQ).left_inv
      (base_mem_unitaryConstraintChart_source Q o hQ))

theorem dephasedParametrization_unitary 
 (y : DephasedModel Q o) :
    Unitary (dephasedParametrization Q o hQ y) :=
  ((unitaryConstraintChart Q o hQ).symm (0,y)).property.2

theorem dephasedParametrization_constraints 
 (y : DephasedModel Q o)
    (hy : y ∈ dephasedChartDomain Q o hQ) :
    anchorImag Q.val o (dephasedParametrization Q o hQ y) = 0 ∧
      AnchorPositive Q.val (dephasedParametrization Q o hQ y) o := by
  have hs := (unitaryConstraintChart Q o hQ).map_target hy
  refine ⟨?_, ((unitaryConstraintChart_source_iff Q o hQ _).mp hs).2.2⟩
  unfold dephasedParametrization
  rw [← unitaryConstraintChart_fst Q o hQ _ hs]
  exact congrArg Prod.fst ((unitaryConstraintChart Q o hQ).right_inv hy)

theorem dephasedParametrization_continuousOn 
 :
    ContinuousOn (dephasedParametrization Q o hQ) (dephasedChartDomain Q o hQ) := continuous_subtype_val.continuousOn.comp
    ((unitaryConstraintChart Q o hQ).continuousOn_symm.comp
      (continuous_const.prodMk continuous_id).continuousOn (fun _ h => h))
    (fun _ _ => Set.mem_univ _)

theorem dephasedParametrization_injectiveOn 
 :
    Set.InjOn (dephasedParametrization Q o hQ) (dephasedChartDomain Q o hQ) := by
  intro y hy z hz he
  exact congrArg Prod.snd ((unitaryConstraintChart Q o hQ).symm.injOn hy hz (Subtype.ext he))

end GS.UnitaryLocalModel
