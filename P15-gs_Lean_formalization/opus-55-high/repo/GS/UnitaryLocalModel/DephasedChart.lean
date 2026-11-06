module

public import GS.UnitaryLocalModel.DephasedDifferential

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# An actual local chart on the dephased unitary slice

The real implicit function theorem is applied to the proved surjective anchor
constraint derivative. Positivity is an open restriction. All unitary and
slice spaces retain their inherited matrix topology.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryManifold Set
namespace GS.UnitaryLocalModel
variable {q : ℕ}

/-- The strict inequalities defining the positive branch of the anchor slice. -/
def AnchorPositive (Q A : CMat q) (o : Fin q) : Prop :=
  (∀ i, 0 < (A i o / Q i o).re) ∧ (∀ j, 0 < (A o j / Q o j).re)

section
variable (Q : CMat q) (o : Fin q)
theorem anchorPositive_self (hQ : AnchorNonzero Q Q o) : AnchorPositive Q Q o :=
  ⟨fun i => by simp [(hQ.1 i).1], fun j => by simp [(hQ.2 j).1]⟩

end

theorem anchorImag_eq_zero_iff (Q A : CMat q) (o : Fin q) :
    anchorImag Q o A = 0 ↔
      (∀ i, (A i o / Q i o).im = 0) ∧ (∀ j, (A o j / Q o j).im = 0) := by
  constructor
  · intro h
    have hc : ∀ i, (A i o / Q i o).im = 0 := fun i =>
      congrArg (fun p : AnchorCoordinates o => p.1 i) h
    refine ⟨hc, ?_⟩
    intro j
    by_cases hj : j = o
    · grind
    · exact congrArg (fun p : AnchorCoordinates o => p.2 ⟨j,hj⟩) h
  aesop

theorem complex_positive_real_iff (z : ℂ) :
    (∃ r : ℝ, 0 < r ∧ z = r) ↔ z.im = 0 ∧ 0 < z.re := by
  constructor <;> [simp_all; exact fun h => ⟨z.re, h.2, Complex.ext rfl (by simp [h.1])⟩]

theorem dephased_constraints_iff (Q A : CMat q) (o : Fin q) :
    anchorImag Q o A = 0 ∧ AnchorPositive Q A o ↔
      (∀ i, ∃ r : ℝ, 0 < r ∧ A i o / Q i o = r) ∧
      (∀ j, ∃ r : ℝ, 0 < r ∧ A o j / Q o j = r) := by
  simp only [anchorImag_eq_zero_iff, complex_positive_real_iff, AnchorPositive, forall_and]
  tauto

section
variable (Q : FullUnitary q) (o : Fin q)
/-- An iterated matrix subtype; no topology is transported to this space. -/
abbrev DephasedUnitary :=
  {A : FullUnitary q // anchorImag Q.val o A.val = 0 ∧ AnchorPositive Q.val A.val o}

abbrev DephasedModel :=
  ↥(LinearMap.ker (anchorDerivative Q o : FullSkewModel q →ₗ[ℝ] AnchorCoordinates o))

end

section
variable (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o)
/-- The actual implicit-function chart of the Cayley constraint map. -/
def constraintChart :
    OpenPartialHomeomorph (FullSkewModel q) (AnchorCoordinates o × DephasedModel Q o) :=
  (anchorConstraints_hasStrictFDerivAt Q o).implicitToOpenPartialHomeomorph
    (anchorConstraints Q o) (anchorDerivative Q o) (anchorDerivative_range Q o hQ)

@[simp] theorem constraintChart_fst (x : FullSkewModel q) :
    (constraintChart Q o hQ x).1 = anchorConstraints Q o x :=
  (anchorConstraints_hasStrictFDerivAt Q o).implicitToOpenPartialHomeomorph_fst
    (anchorDerivative_range Q o hQ) x

@[simp] theorem constraintChart_zero : constraintChart Q o hQ 0 = (0,0) := by
  unfold constraintChart
  simp_all

theorem zero_mem_constraintChart_source : (0 : FullSkewModel q) ∈ (constraintChart Q o hQ).source :=
  (anchorConstraints_hasStrictFDerivAt Q o).mem_implicitToOpenPartialHomeomorph_source
    (anchorDerivative_range Q o hQ)

/-- First pass to Cayley coordinates, then straighten the constraints, and
restrict to the open positive branch. -/
def unitaryConstraintChart :
    OpenPartialHomeomorph (FullUnitary q) (AnchorCoordinates o × DephasedModel Q o) :=
  ((blockPartialChart Q).trans (constraintChart Q o hQ)).restrOpen
    {A | AnchorPositive Q.val A.val o}
    (by apply IsOpen.and <;> simp only [Set.setOf_forall] <;>
      exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (by fun_prop))

theorem unitaryConstraintChart_source_iff (A : FullUnitary q) :
    A ∈ (unitaryConstraintChart Q o hQ).source ↔
      A ∈ chartSource Q ∧ chartMap Q A.val ∈ (constraintChart Q o hQ).source ∧
        AnchorPositive Q.val A.val o := and_assoc

theorem base_mem_unitaryConstraintChart_source : Q ∈ (unitaryConstraintChart Q o hQ).source :=
  (unitaryConstraintChart_source_iff Q o hQ Q).mpr ⟨base_mem_chartSource Q, by simpa using zero_mem_constraintChart_source Q o hQ,
    anchorPositive_self Q.val o hQ⟩

@[simp] theorem unitaryConstraintChart_base : unitaryConstraintChart Q o hQ Q = (0,0) := by
  change constraintChart Q o hQ (chartMap Q Q.val) = _
  simp

theorem unitaryConstraintChart_fst (A : FullUnitary q)
    (hA : A ∈ (unitaryConstraintChart Q o hQ).source) :
    (unitaryConstraintChart Q o hQ A).1 = anchorImag Q.val o A.val := by
  change (constraintChart Q o hQ (chartMap Q A.val)).1 = _
  rw [constraintChart_fst, anchorConstraints, chartInv_chartMap Q A ((unitaryConstraintChart_source_iff Q o hQ A).mp hA).1]

/-- Open coordinates on the zero constraint level. -/
def dephasedChartDomain : Set (DephasedModel Q o) :=
  {y | (0,y) ∈ (unitaryConstraintChart Q o hQ).target}

def dephasedParametrization (y : DephasedModel Q o) : CMat q :=
  ((unitaryConstraintChart Q o hQ).symm (0,y)).val

theorem dephasedChartDomain_open : IsOpen (dephasedChartDomain Q o hQ) :=
  (unitaryConstraintChart Q o hQ).open_target.preimage (continuous_const.prodMk continuous_id)

theorem zero_mem_dephasedChartDomain : (0 : DephasedModel Q o) ∈ dephasedChartDomain Q o hQ := by
  change (0, 0) ∈ (unitaryConstraintChart Q o hQ).target
  simpa only [unitaryConstraintChart_base] using (unitaryConstraintChart Q o hQ).map_source
    (base_mem_unitaryConstraintChart_source Q o hQ)

@[simp] theorem dephasedParametrization_zero : dephasedParametrization Q o hQ 0 = Q.val := by
  have h := (unitaryConstraintChart Q o hQ).left_inv
    (base_mem_unitaryConstraintChart_source Q o hQ)
  rw [unitaryConstraintChart_base] at h
  exact congrArg Subtype.val h

section
variable (y : DephasedModel Q o)
theorem dephasedParametrization_unitary :
    Unitary (dephasedParametrization Q o hQ y) :=
  ((unitaryConstraintChart Q o hQ).symm (0,y)).property.2

theorem dephasedParametrization_constraints (hy : y ∈ dephasedChartDomain Q o hQ) :
    anchorImag Q.val o (dephasedParametrization Q o hQ y) = 0 ∧
      AnchorPositive Q.val (dephasedParametrization Q o hQ y) o := by
  have hs := (unitaryConstraintChart Q o hQ).map_target hy
  refine ⟨?_, ((unitaryConstraintChart_source_iff Q o hQ _).mp hs).2.2⟩
  unfold dephasedParametrization
  rw [← unitaryConstraintChart_fst Q o hQ _ hs]
  exact congrArg Prod.fst ((unitaryConstraintChart Q o hQ).right_inv hy)

end

theorem dephasedParametrization_continuousOn :
    ContinuousOn (dephasedParametrization Q o hQ) (dephasedChartDomain Q o hQ) :=
  continuous_subtype_val.continuousOn.comp
    ((unitaryConstraintChart Q o hQ).continuousOn_symm.comp
      (by fun_prop) (by tauto))
    (fun _ _ => Set.mem_univ _)

theorem dephasedParametrization_injectiveOn :
    Set.InjOn (dephasedParametrization Q o hQ) (dephasedChartDomain Q o hQ) := by
  intro y hy z hz he
  have hh := congrArg (unitaryConstraintChart Q o hQ) (Subtype.ext he)
  rw [(unitaryConstraintChart Q o hQ).right_inv hy,
    (unitaryConstraintChart Q o hQ).right_inv hz] at hh
  grind

end

end GS.UnitaryLocalModel
