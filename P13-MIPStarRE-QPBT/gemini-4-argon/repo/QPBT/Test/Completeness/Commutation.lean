module

public import QPBT.Test.Completeness.HonestStrategy.MeasurementFamily

/-!
# Commutation of the honest Pauli measurements

This module proves that the honest measurement family of
`MIPStarRE.QPBT.Test.Completeness.HonestStrategy.MeasurementFamily` has commuting effects
on every question pair of positive weight for the Pauli question sampler.  The
argument first characterises the supported question pairs as the typed
conditionally linear images of a single ambient coefficient vector along an edge
of the Pauli type graph, and then treats the five edge families of that graph.

## References

This is the commutation obligation in the proof of `lem:pauli-completeness`,
blueprint `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1382`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

set_option maxRecDepth 8000

/-! ### The supported question pairs -/

/-- The ordered incidence forms of the Pauli type graph: an ordered pair of
distinct types listed in `def:pauli-question-distribution` outside the Magic
Square block. Blueprint `def:pauli-question-distribution`. -/
def PauliEdgeOriented (t₁ t₂ : PauliType) : Prop :=
  (∃ W : PauliKind, t₁ = .point W ∧
      (t₂ = .aline W ∨ t₂ = .dline W ∨ t₂ = .pauli W ∨ t₂ = .pairW W)) ∨
    (∃ W : PauliKind, t₁ = .pairW W ∧ t₂ = .pair) ∨
    (t₁ = .point .X ∧ t₂ = .ms (.var 0)) ∨
    (t₁ = .point .Z ∧ t₂ = .ms (.var 4))

/-- Every edge of the Pauli type graph is a self-loop, an edge of the Magic
Square graph, or one of the listed incidence forms in one of the two
orders. -/
theorem pauliEdges_cases {t₁ t₂ : PauliType} (h : Sym2.mk t₁ t₂ ∈ pauliEdges) :
    t₁ = t₂ ∨
      (∃ s₁ s₂ : MsType, t₁ = .ms s₁ ∧ t₂ = .ms s₂ ∧ Sym2.mk s₁ s₂ ∈ msEdges) ∨
      PauliEdgeOriented t₁ t₂ ∨ PauliEdgeOriented t₂ t₁ := by
  classical
  simp only [pauliEdges, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton,
    Prod.exists] at h
  rcases h with (((⟨a, hEq⟩ | ((⟨W, hEq⟩ | ⟨W, hEq⟩) | ⟨W, hEq⟩)) |
    (⟨W, hEq⟩ | hEq | hEq)) | ⟨W, hEq⟩) | ⟨s₁, s₂, hms, hEq⟩ <;>
    rcases Sym2.eq_iff.mp hEq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [PauliEdgeOriented, Sym2.eq_swap, *]

theorem pauliQuestionDistribution_pos_incidence (P : AdmissibleParams)
    (x y : PauliQuestion P) (hxy : 0 < (pauliQuestionDistribution P).weight (x, y)) :
    ∃ z : PauliSpace P, Sym2.mk x.1 y.1 ∈ pauliEdges ∧
      x.2 = pauliCL P x.1 z ∧ y.2 = pauliCL P y.1 z := by
  classical
  let _ : Nonempty PauliEdge := pauliEdge_nonempty
  set F : PauliEdge × PauliSpace P → PauliQuestion P × PauliQuestion P :=
    fun q => ((q.1.val.1, pauliCL P q.1.val.1 q.2),
      (q.1.val.2, pauliCL P q.1.val.2 q.2))
  have hmem : (x, y) ∈
      ((uniformDistribution (PauliEdge × PauliSpace P)).map F).support := by
    by_contra hnot
    exact lt_irrefl 0 (((uniformDistribution (PauliEdge × PauliSpace P)).map F).outsideSupport _ hnot ▸ hxy)
  rw [Distribution.map_support, uniformDistribution_support] at hmem
  obtain ⟨q, -, hq⟩ := Finset.mem_image.mp hmem
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hq.symm
  exact ⟨q.2, q.1.2, rfl, rfl⟩

/-! ### Coarse-graining and tensor placement -/

theorem postprocess_commute_of_commute {α β γ δ V : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    [Fintype V] [DecidableEq V]
    (M : Measurement α V) (N : Measurement β V)
    (h : ∀ x y, Commute (M.effect x) (N.effect y))
    (f : α → γ) (g : β → δ) (a : γ) (b : δ) :
    Commute ((M.postprocess f).effect a) ((N.postprocess g).effect b) := by
  rw [Measurement.postprocess_effect, Measurement.postprocess_effect]
  exact Commute.sum_left _ _ _ fun x _ => Commute.sum_right _ _ _ fun y _ => h x y

theorem placedPauliMeasurement_effect_eq {P : AdmissibleParams}
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : Measurement α (PauliRegister P)) (f : α → PauliAnswer P)
    (a : PauliAnswer P) :
    (placedPauliMeasurement M f).effect a =
      heteroKron ((M.postprocess f).effect a) (1 : Op (ZMod 2)) := by
  rw [placedPauliMeasurement, Measurement.postprocess_effect, Measurement.postprocess_effect]
  exact leftTensor_finset_sum _ _

theorem placedPauliMeasurement_postprocess_eq {P : AdmissibleParams}
    {ζ α : Type*} [Fintype ζ] [DecidableEq ζ] [Fintype α] [DecidableEq α]
    (M : Measurement ζ (PauliRegister P)) (g : ζ → α) (u : α → PauliAnswer P) :
    placedPauliMeasurement (M.postprocess g) u =
      placedPauliMeasurement M (fun h => u (g h)) := by
  have hplace :
      DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2) (M.postprocess g) =
        (DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2) M).postprocess g := by
    refine Measurement.ext fun b => ?_
    change heteroKron ((M.postprocess g).effect b) (1 : Op (ZMod 2)) = _
    rw [Measurement.postprocess_effect, Measurement.postprocess_effect]
    exact (leftTensor_finset_sum _ _).symm
  change (DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2)
      (M.postprocess g)).postprocess u = _
  rw [hplace, Measurement.postprocess_comp]; rfl

theorem placedPauliMeasurement_commute_of_commute {P : AdmissibleParams}
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (M : Measurement α (PauliRegister P)) (N : Measurement β (PauliRegister P))
    (h : ∀ x y, Commute (M.effect x) (N.effect y))
    (f : α → PauliAnswer P) (g : β → PauliAnswer P) (a b : PauliAnswer P) :
    Commute ((placedPauliMeasurement M f).effect a)
      ((placedPauliMeasurement N g).effect b) := by
  rw [placedPauliMeasurement_effect_eq, placedPauliMeasurement_effect_eq]
  refine leftPlaced_commute ?_
  rw [Measurement.postprocess_effect, Measurement.postprocess_effect]
  exact Commute.sum_left _ _ _ fun x _ => Commute.sum_right _ _ _ fun y _ => h x y

theorem deterministicMeasurement_effect_self {α V : Type*}
    [Fintype α] [DecidableEq α] [Fintype V] [DecidableEq V] (a₀ : α) :
    (deterministicMeasurement (V := V) a₀).effect a₀ = 1 := by
  change ((unitMeasurement V).postprocess (fun _ => a₀)).effect a₀ = 1
  rw [Measurement.postprocess_effect]
  simp [unitMeasurement, Measurement.ofSumEqOne]

theorem deterministicMeasurement_effect_commute {α V : Type*}
    [Fintype α] [DecidableEq α] [Fintype V] [DecidableEq V]
    (a₀ a : α) (A : Op V) :
    Commute ((deterministicMeasurement (V := V) a₀).effect a) A := by
  by_cases h : a = a₀
  · subst h; rw [deterministicMeasurement_effect_self]; exact Commute.one_left A
  · rw [deterministicMeasurement_effect_eq_zero_of_ne h]; exact Commute.zero_left A

/-! ### Honest measurements sharing a Pauli basis -/

theorem exists_placedBasis_of_basisType (P : AdmissibleParams) (t : PauliType)
    (W : PauliKind) (z : PauliSpace P)
    (ht : t = .point W ∨ t = .aline W ∨ t = .dline W ∨ t = .pauli W ∨
      t = .pairW W) :
    ∃ f : PauliRegister P → PauliAnswer P,
      honestMeasurement P t z = placedPauliMeasurement (pauliBasisMeasurement W) f := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, placedPauliMeasurement_postprocess_eq _ _ _⟩
  · exact ⟨_, placedPauliMeasurement_postprocess_eq _ _ _⟩
  · exact ⟨_, placedPauliMeasurement_postprocess_eq _ _ _⟩
  · exact ⟨fun a => PauliAnswer.pauliOutcome a, rfl⟩
  · exact ⟨_, placedPauliMeasurement_postprocess_eq _ _ _⟩

theorem honestMeasurement_basis_commute (P : AdmissibleParams) {t₁ t₂ : PauliType}
    (W : PauliKind) (z₁ z₂ : PauliSpace P)
    (h₁ : t₁ = .point W ∨ t₁ = .aline W ∨ t₁ = .dline W ∨ t₁ = .pauli W ∨
      t₁ = .pairW W)
    (h₂ : t₂ = .point W ∨ t₂ = .aline W ∨ t₂ = .dline W ∨ t₂ = .pauli W ∨
      t₂ = .pairW W)
    (a b : PauliAnswer P) :
    Commute ((honestMeasurement P t₁ z₁).effect a)
      ((honestMeasurement P t₂ z₂).effect b) := by
  obtain ⟨f₁, hf₁⟩ := exists_placedBasis_of_basisType P t₁ W z₁ h₁
  obtain ⟨f₂, hf₂⟩ := exists_placedBasis_of_basisType P t₂ W z₂ h₂
  rw [hf₁, hf₂]
  exact placedPauliMeasurement_commute (pauliBasisMeasurement W)
    (fun h => pauliProj_isProj W h) f₁ f₂ a b

/-! ### The Pair and Magic Square measurements -/

theorem honestMagicMeasurement_var_eq_placedBasis (P : AdmissibleParams)
    (z : PauliSpace P) (hg : pauliPairGamma P z ≠ 0) :
    honestMagicMeasurement P (.var 0) z =
        placedPauliMeasurement (pauliBasisMeasurement .X)
          (fun h => .bit (pauliTraceBit P (pauliXBlock z) (pauliRXBlock z) h)) ∧
      honestMagicMeasurement P (.var 4) z =
        placedPauliMeasurement (pauliBasisMeasurement .Z)
          (fun h => .bit (pauliTraceBit P (pauliZBlock z) (pauliRZBlock z) h)) := by
  classical
  have hcell (j : Fin 9) (W : PauliKind) (u : Fin P.m → PauliScalar P) (r : PauliScalar P)
      (hj : ∀ b, (pauliMagicMeasurement P z hg (.var j)).effect (.bit b) =
        heteroKron ((pauliTraceMeasurement P W u r).effect b) (1 : Op (ZMod 2))) :
      honestMagicMeasurement P (.var j) z =
        placedPauliMeasurement (pauliBasisMeasurement W)
          (fun h => .bit (pauliTraceBit P u r h)) := by
    rw [show honestMagicMeasurement P (.var j) z =
        (pauliMagicCellMeasurement P z hg j).postprocess PauliAnswer.bit by
      simp [honestMagicMeasurement, hg, pauliMagicMeasurement, msStrategyMeasurement,
        Measurement.postprocess_comp]; rfl,
      ← show DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2)
        (pauliTraceMeasurement P W u r) = pauliMagicCellMeasurement P z hg j from
        Measurement.ext fun b => ((msStrategyMeasurement_var_bit _
          (pauliMagicCellMeasurement_projective P z hg)
          (pauliMagicCellMeasurement_commute P z hg) j b).symm.trans (hj b)).symm]
    exact placedPauliMeasurement_postprocess_eq _ _ _
  exact ⟨hcell 0 .X _ _ fun b => (pauliMagicMeasurement_var_effect P z hg b).1,
    hcell 4 .Z _ _ fun b => (pauliMagicMeasurement_var_effect P z hg b).2⟩

theorem honestPairW_pair_commute (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (a b : PauliAnswer P) :
    Commute ((honestPairWMeasurement P W z).effect a)
      ((honestPairMeasurement P z).effect b) := by
  classical
  by_cases hg : pauliPairGamma P z = 0
  · rw [show honestPairMeasurement P z =
      placedPauliMeasurement (pauliPairMeasurement P z hg) PauliAnswer.pairBits by
      simp [honestPairMeasurement, hg]]
    refine placedPauliMeasurement_commute_of_commute _ _ (fun x c => ?_) _ _ a b
    cases W
    · exact Commute.mul_right
        (postprocess_effect_commute (pauliBasisMeasurement .X) (pauliProj_isProj .X) _ _ x c.1)
        (pauliTraceMeasurement_effect_commute P z hg x c.2)
    · exact Commute.mul_right
        (pauliTraceMeasurement_effect_commute P z hg c.1 x).symm
        (postprocess_effect_commute (pauliBasisMeasurement .Z) (pauliProj_isProj .Z) _ _ x c.2)
  · rw [show honestPairMeasurement P z =
      deterministicMeasurement (V := HonestIndex P) (.pairBits (0, 0)) by
      simp [honestPairMeasurement, hg]]
    exact (deterministicMeasurement_effect_commute _ _ _).symm

theorem honestMagicMeasurement_ms_commute (P : AdmissibleParams)
    (z : PauliSpace P) {s₁ s₂ : MsType} (hms : Sym2.mk s₁ s₂ ∈ msEdges)
    (a b : PauliAnswer P) :
    Commute ((honestMagicMeasurement P s₁ z).effect a)
      ((honestMagicMeasurement P s₂ z).effect b) := by
  classical
  by_cases hg : pauliPairGamma P z = 0
  · cases s₁ <;> {
      simp only [honestMagicMeasurement, hg, dite_true]
      exact deterministicMeasurement_effect_commute _ _ _ }
  · have h₁ (s : MsType) : honestMagicMeasurement P s z =
        (pauliMagicMeasurement P z hg s).postprocess (pauliAnswerOfMs (P := P)) := by
      simp [honestMagicMeasurement, hg]
    have hsupp : (s₁, s₂) ∈ msGameSymm.μ.support :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hms⟩
    rcases msGame_support_incidence s₁ s₂ hsupp with
      ⟨i, k, rfl, rfl⟩ | ⟨i, k, rfl, rfl⟩ <;> rw [h₁ _, h₁ _]
    · exact postprocess_commute_of_commute _ _
        (fun x y => pauliMagicMeasurement_incident_commute P z hg i k x y) _ _ a b
    · exact postprocess_commute_of_commute _ _
        (fun x y => (pauliMagicMeasurement_incident_commute P z hg i k y x).symm) _ _ a b

/-! ### Commutation along the Pauli type graph -/

theorem honestMeasurement_commute_of_oriented (P : AdmissibleParams)
    {t₁ t₂ : PauliType} (h : PauliEdgeOriented t₁ t₂) (z : PauliSpace P)
    (a b : PauliAnswer P) :
    Commute ((honestMeasurement P t₁ (pauliCL P t₁ z)).effect a)
      ((honestMeasurement P t₂ (pauliCL P t₂ z)).effect b) := by
  classical
  rcases h with ⟨W, rfl, hW⟩ | ⟨W, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine honestMeasurement_basis_commute P W _ _ (Or.inl rfl) ?_ a b
    rcases hW with rfl | rfl | rfl | rfl <;> tauto
  · exact honestPairW_pair_commute P W (pauliSharedProjection z) a b
  · by_cases hg : pauliPairGamma P (pauliSharedProjection z) = 0
    · change Commute _ ((honestMagicMeasurement P _ (pauliSharedProjection z)).effect b)
      simp only [honestMagicMeasurement, hg, dite_true]
      exact (deterministicMeasurement_effect_commute _ _ _).symm
    · obtain ⟨f₁, hf₁⟩ := exists_placedBasis_of_basisType P (.point .X) .X
        (pauliCL P (.point .X) z) (Or.inl rfl)
      change Commute _ ((honestMagicMeasurement P _ (pauliSharedProjection z)).effect b)
      rw [hf₁, (honestMagicMeasurement_var_eq_placedBasis P (pauliSharedProjection z) hg).1]
      exact placedPauliMeasurement_commute (pauliBasisMeasurement .X) (pauliProj_isProj .X) f₁ _ a b
  · by_cases hg : pauliPairGamma P (pauliSharedProjection z) = 0
    · change Commute _ ((honestMagicMeasurement P _ (pauliSharedProjection z)).effect b)
      simp only [honestMagicMeasurement, hg, dite_true]
      exact (deterministicMeasurement_effect_commute _ _ _).symm
    · obtain ⟨f₁, hf₁⟩ := exists_placedBasis_of_basisType P (.point .Z) .Z
        (pauliCL P (.point .Z) z) (Or.inl rfl)
      change Commute _ ((honestMagicMeasurement P _ (pauliSharedProjection z)).effect b)
      rw [hf₁, (honestMagicMeasurement_var_eq_placedBasis P (pauliSharedProjection z) hg).2]
      exact placedPauliMeasurement_commute (pauliBasisMeasurement .Z) (pauliProj_isProj .Z) f₁ _ a b

/-- The honest measurement family has commuting effects on every question pair
of positive weight for the Pauli question sampler.  This is the commutation
obligation of the honest strategy in `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1382`. -/
theorem honestMeasurement_commuting (P : AdmissibleParams) :
    IsCommutingOn (pauliQuestionDistribution P)
      (fun q : PauliQuestion P => honestMeasurement P q.1 q.2)
      (fun q : PauliQuestion P => honestMeasurement P q.1 q.2) := by
  intro x y hxy a b
  obtain ⟨z, hedge, hx, hy⟩ := pauliQuestionDistribution_pos_incidence P x y hxy
  change Commute ((honestMeasurement P x.1 x.2).effect a)
    ((honestMeasurement P y.1 y.2).effect b)
  rw [hx, hy]
  rcases pauliEdges_cases hedge with heq | ⟨s₁, s₂, hs₁, hs₂, hms⟩ | hor | hor
  · rw [heq]
    exact honestMeasurement_self_commute P y.1 _ a b
  · rw [hs₁, hs₂]
    exact honestMagicMeasurement_ms_commute P (pauliSharedProjection z) hms a b
  · exact honestMeasurement_commute_of_oriented P hor z a b
  · exact (honestMeasurement_commute_of_oriented P hor z b a).symm

end

end MIPStarRE.QPBT
