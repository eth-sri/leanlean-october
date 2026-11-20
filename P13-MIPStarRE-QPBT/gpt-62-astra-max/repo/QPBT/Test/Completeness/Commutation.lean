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
    Prod.exists, Sym2.eq_iff] at h
  unfold PauliEdgeOriented
  rcases h with (((h | ((h | h) | h)) | (h | h | h)) | h) | h <;>
    grind [Sym2.eq_swap]

/-- Every question pair of positive weight in the Pauli question distribution
consists of the typed conditionally linear images of a single ambient
coefficient vector along an edge of the Pauli type graph. -/
theorem pauliQuestionDistribution_pos_incidence {P : AdmissibleParams}
    {x y : PauliQuestion P} (hxy : 0 < (pauliQuestionDistribution P).weight (x, y)) :
    ∃ z : PauliSpace P, Sym2.mk x.1 y.1 ∈ pauliEdges ∧
      x.2 = pauliCL P x.1 z ∧ y.2 = pauliCL P y.1 z := by
  classical
  letI := pauliEdge_nonempty
  set F : PauliEdge × PauliSpace P → PauliQuestion P × PauliQuestion P :=
    fun q => ((q.1.val.1, pauliCL P q.1.val.1 q.2),
      (q.1.val.2, pauliCL P q.1.val.2 q.2)) with hF
  have hEq : pauliQuestionDistribution P =
      (uniformDistribution (PauliEdge × PauliSpace P)).map F := rfl
  rw [hEq] at hxy
  have hmem : (x, y) ∈
      ((uniformDistribution (PauliEdge × PauliSpace P)).map F).support := by
    by_contra hnot
    rw [((uniformDistribution (PauliEdge × PauliSpace P)).map F).outsideSupport _ hnot]
      at hxy
    exact lt_irrefl 0 hxy
  obtain ⟨q, -, hq⟩ := Finset.mem_image.mp hmem
  have hx := (congrArg Prod.fst hq).symm
  have hy := (congrArg Prod.snd hq).symm
  subst hx
  subst hy
  exact ⟨q.2, q.1.2, rfl, rfl⟩

/-! ### Coarse-graining and tensor placement -/

section

variable {P : AdmissibleParams} {ζ α β γ : Type*} [Fintype ζ] {δ V : Type*} [DecidableEq ζ]
  [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (M : Measurement α (PauliRegister P))
  [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ] [Fintype V] [DecidableEq V] (a₀ : α)
  (f : α → PauliAnswer P) (a : PauliAnswer P)

/-- Pairwise commuting effects stay commuting under coarse-graining. -/
theorem postprocess_commute_of_commute
    {M : Measurement α V} {N : Measurement β V}
    (h : ∀ x y, Commute (M.effect x) (N.effect y))
    (f : α → γ) (g : β → δ) (a : γ) (b : δ) :
    Commute ((M.postprocess f).effect a) ((N.postprocess g).effect b) := by
  exact Commute.sum_left _ _ _ fun x _ => Commute.sum_right _ _ _ fun y _ => h x y

/-- The effect of a placed and relabelled measurement of the Pauli register. -/
theorem placedPauliMeasurement_effect_eq :
    (placedPauliMeasurement M f).effect a =
      heteroKron ((M.postprocess f).effect a) (1 : Op (ZMod 2)) := by
  apply leftTensor_finset_sum

/-- Placing a coarse-grained measurement of the Pauli register and relabelling
its outcomes is the placement of the original measurement relabelled along the
composite; this is the composition identity for successive coarse-grainings. -/
theorem placedPauliMeasurement_postprocess_eq
    (M : Measurement ζ (PauliRegister P)) (g : ζ → α) (u : α → PauliAnswer P) :
    placedPauliMeasurement (M.postprocess g) u =
      placedPauliMeasurement M (fun h => u (g h)) := by
  have hplace :
      DistanceCalculus.leftPlacedMeasurement (M.postprocess g) =
        (DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2) M).postprocess g := by
    refine Measurement.ext fun b => ?_
    exact (leftTensor_finset_sum _ _).symm
  change (DistanceCalculus.leftPlacedMeasurement
      (M.postprocess g)).postprocess u = _
  rw [hplace, Measurement.postprocess_comp]
  rfl

/-- Placed measurements of the Pauli register with pairwise commuting effects
have commuting effects. -/
theorem placedPauliMeasurement_commute_of_commute (N : Measurement β (PauliRegister P))
    (h : ∀ x y, Commute (M.effect x) (N.effect y))
    (f : α → PauliAnswer P) (g : β → PauliAnswer P) (a b : PauliAnswer P) :
    Commute ((placedPauliMeasurement M f).effect a)
      ((placedPauliMeasurement N g).effect b) := by
  simp [placedPauliMeasurement_effect_eq]
  apply leftPlaced_commute
  exact Commute.sum_left _ _ _ fun x _ => Commute.sum_right _ _ _ fun y _ => h x y

/-- The deterministic measurement reports its prescribed outcome with the
identity effect. -/
theorem deterministicMeasurement_effect_self :
    (deterministicMeasurement (V := V) a₀).effect a₀ = 1 := by
  change ((unitMeasurement V).postprocess _).effect a₀ = 1
  rw [Measurement.postprocess_effect]
  simp [unitMeasurement, Measurement.ofSumEqOne]

/-- Every effect of a deterministic measurement commutes with every
operator. -/
theorem deterministicMeasurement_effect_commute
    (a₀ a : α) (A : Op V) :
    Commute ((deterministicMeasurement (V := V) a₀).effect a) A := by
  by_cases h : a = a₀
  · subst h
    simp [deterministicMeasurement_effect_self]
  · simp [deterministicMeasurement_effect_eq_zero_of_ne h]

end

/-! ### Honest measurements sharing a Pauli basis -/

variable (P : AdmissibleParams) (t : PauliType) {t₁ t₂ : PauliType} (W : PauliKind)
  (h : PauliEdgeOriented t₁ t₂) (z : PauliSpace P) {s₁ s₂ : MsType}
  (hms : Sym2.mk s₁ s₂ ∈ msEdges) (a b : PauliAnswer P)

/-- Every honest measurement at a question type reading a single Pauli basis is
a relabelled coarse-graining of that basis measurement. -/
theorem exists_placedBasis_of_basisType
    (ht : t = .point W ∨ t = .aline W ∨ t = .dline W ∨ t = .pauli W ∨
      t = .pairW W) :
    ∃ f : PauliRegister P → PauliAnswer P,
      honestMeasurement t z = placedPauliMeasurement (pauliBasisMeasurement W) f := by
  rcases ht with rfl | rfl | rfl | rfl | rfl <;>
    first | exact ⟨_, rfl⟩ | exact ⟨_, placedPauliMeasurement_postprocess_eq (pauliBasisMeasurement W) _ _⟩

/-- Honest measurements reading one and the same Pauli basis have commuting
effects, whatever the coefficient vectors carried by their questions. -/
theorem honestMeasurement_basis_commute (z₁ z₂ : PauliSpace P)
    (h₁ : t₁ = .point W ∨ t₁ = .aline W ∨ t₁ = .dline W ∨ t₁ = .pauli W ∨
      t₁ = .pairW W)
    (h₂ : t₂ = .point W ∨ t₂ = .aline W ∨ t₂ = .dline W ∨ t₂ = .pauli W ∨
      t₂ = .pairW W)
    (a b : PauliAnswer P) :
    Commute ((honestMeasurement t₁ z₁).effect a)
      ((honestMeasurement t₂ z₂).effect b) := by
  obtain ⟨f₁, hf₁⟩ := exists_placedBasis_of_basisType P t₁ W z₁ h₁
  obtain ⟨f₂, hf₂⟩ := exists_placedBasis_of_basisType P t₂ W z₂ h₂
  simp_all
  solve_by_elim [placedPauliMeasurement_commute, pauliProj_isProj]

/-! ### The Pair and Magic Square measurements -/

variable {z} in
/-- With a nonzero phase bit the honest measurements at the first and the fifth
Magic Square variables are the honest Pair/X and Pair/Z measurements, hence
relabelled coarse-grainings of the Pauli basis measurements. -/
theorem honestMagicMeasurement_var_eq_placedBasis (hg : pauliPairGamma P z ≠ 0) :
    honestMagicMeasurement (.var 0) z =
        placedPauliMeasurement (pauliBasisMeasurement .X)
          (fun h => .bit (pauliTraceBit (pauliXBlock z) (pauliRXBlock z) h)) ∧
      honestMagicMeasurement (.var 4) z =
        placedPauliMeasurement (pauliBasisMeasurement .Z)
          (fun h => .bit (pauliTraceBit (pauliZBlock z) (pauliRZBlock z) h)) := by
  classical
  have hcell : ∀ (j : Fin 9) (W : PauliKind) (u : PauliPoint P)
      (r : PauliScalar P),
      (∀ b, (pauliMagicCellMeasurement z hg j).effect b =
        heteroKron ((pauliTraceMeasurement W u r).effect b) 1) →
      honestMagicMeasurement (.var j) z =
        placedPauliMeasurement (pauliBasisMeasurement W)
          (fun h => .bit (pauliTraceBit u r h)) := by
    intro j W u r hj
    have hstep : honestMagicMeasurement (.var j) z =
        (pauliMagicCellMeasurement z hg j).postprocess
          (fun b : ZMod 2 => (PauliAnswer.bit b)) := by
      have hunfold : honestMagicMeasurement (.var j) z =
          (pauliMagicMeasurement z hg (.var j)).postprocess
            (pauliAnswerOfMs) := by
        simp [honestMagicMeasurement, hg]
      rw [hunfold, show pauliMagicMeasurement z hg (.var j) =
        (pauliMagicCellMeasurement z hg j).postprocess MsAnswer.bit from rfl,
        Measurement.postprocess_comp]
      rfl
    have hplaced : DistanceCalculus.leftPlacedMeasurement
        (pauliTraceMeasurement W u r) = pauliMagicCellMeasurement z hg j :=
      Measurement.ext fun b => (hj b).symm
    rw [hstep, ← hplaced]
    apply placedPauliMeasurement_postprocess_eq
  have hB : ∀ b, (pauliMagicCellMeasurement z hg 4).effect b =
      heteroKron
        ((pauliTraceMeasurement .Z (pauliZBlock z) (pauliRZBlock z)).effect b)
        1 := by
    intro b
    rw [← msStrategyMeasurement_var_bit]
    exact (pauliMagicMeasurement_var_effect hg b).2
  refine ⟨hcell 0 .X _ _ ?_,
    hcell 4 .Z _ _ hB⟩
  intro b
  rw [← msStrategyMeasurement_var_bit (pauliMagicCellMeasurement z hg)
    (pauliMagicCellMeasurement_projective hg)
    (pauliMagicCellMeasurement_commute hg) 0 b]
  exact (pauliMagicMeasurement_var_effect hg b).1

/-- The honest Pair/W and Pair measurements have commuting effects. -/
theorem honestPairW_pair_commute :
    Commute ((honestPairWMeasurement P W z).effect a)
      ((honestPairMeasurement P z).effect b) := by
  classical
  by_cases hg : pauliPairGamma P z = 0
  · have hpair : honestPairMeasurement P z =
        placedPauliMeasurement (pauliPairMeasurement z hg)
          (PauliAnswer.pairBits) := by
      simp [honestPairMeasurement, hg]
    rw [hpair]
    apply placedPauliMeasurement_commute_of_commute
    intro x c
    cases W with
    | X =>
        exact Commute.mul_right
          (postprocess_effect_commute (pauliBasisMeasurement .X)
            (pauliProj_isProj .X)
            _
            _ x c.1)
          (pauliTraceMeasurement_effect_commute hg x c.2)
    | Z =>
        exact Commute.mul_right
          ((pauliTraceMeasurement_effect_commute hg c.1 x).symm)
          (postprocess_effect_commute (pauliBasisMeasurement .Z)
            (pauliProj_isProj .Z)
            _
            _ x c.2)
  · have hpair : honestPairMeasurement P z =
        deterministicMeasurement
          (PauliAnswer.pairBits (0, 0)) := by
      simp [honestPairMeasurement, hg]
    rw [hpair]
    exact (deterministicMeasurement_effect_commute _ _ _).symm

include hms in
/-- The honest Magic Square measurements have commuting effects along every
edge of the Magic Square type graph. -/
theorem honestMagicMeasurement_ms_commute :
    Commute ((honestMagicMeasurement s₁ z).effect a)
      ((honestMagicMeasurement s₂ z).effect b) := by
  classical
  by_cases hg : pauliPairGamma P z = 0
  · simp only [honestMagicMeasurement, dif_pos hg]
    apply deterministicMeasurement_effect_commute
  · have h₁ : ∀ s : MsType, honestMagicMeasurement s z =
        (pauliMagicMeasurement z hg s).postprocess (pauliAnswerOfMs) := by
      simp [honestMagicMeasurement, hg]
    rcases msGame_support_incidence s₁ s₂ (by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hms⟩) with
      ⟨i, k, rfl, rfl⟩ | ⟨i, k, rfl, rfl⟩
    · simp_all
      exact postprocess_commute_of_commute
        (pauliMagicMeasurement_incident_commute hg i k) _ _ a b
    · simp_all
      exact postprocess_commute_of_commute
        (fun x y => (pauliMagicMeasurement_incident_commute hg i k y x).symm)
        _ _ a b

/-! ### Commutation along the Pauli type graph -/

include h in
/-- The honest measurements at the two ends of an ordered incidence form of the
Pauli type graph have commuting effects. -/
theorem honestMeasurement_commute_of_oriented :
    Commute ((honestMeasurement t₁ (pauliCL P t₁ z)).effect a)
      ((honestMeasurement t₂ (pauliCL P t₂ z)).effect b) := by
  classical
  rcases h with ⟨W, rfl, hW⟩ | ⟨W, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine honestMeasurement_basis_commute P W _ _ (Or.inl rfl) ?_ a b
    rcases hW with rfl | rfl | rfl | rfl
    · solve_by_elim [Or.inr]
    · solve_by_elim [Or.inr]
    · solve_by_elim [Or.inr]
    · solve_by_elim [Or.inr]
  · apply honestPairW_pair_commute
  · by_cases hg : pauliPairGamma P (pauliSharedProjection z) = 0
    · have hdet : honestMagicMeasurement (.var 0) (pauliSharedProjection z) =
          deterministicMeasurement
            (PauliAnswer.bit 0) := by
        simp [honestMagicMeasurement, hg]
      change Commute _
        ((honestMagicMeasurement (.var 0) (pauliSharedProjection z)).effect b)
      rw [hdet]
      exact (deterministicMeasurement_effect_commute _ _ _).symm
    · obtain ⟨f₁, hf₁⟩ := exists_placedBasis_of_basisType P _ .X
        (pauliCL P (.point .X) z) (Or.inl rfl)
      change Commute _
        ((honestMagicMeasurement (.var 0) (pauliSharedProjection z)).effect b)
      rw [hf₁, ((honestMagicMeasurement_var_eq_placedBasis P hg).1)]
      solve_by_elim [placedPauliMeasurement_commute, pauliProj_isProj]
  · by_cases hg : pauliPairGamma P (pauliSharedProjection z) = 0
    · have hdet : honestMagicMeasurement (.var 4) (pauliSharedProjection z) =
          deterministicMeasurement
            (PauliAnswer.bit 0) := by
        simp [honestMagicMeasurement, hg]
      change Commute _
        ((honestMagicMeasurement (.var 4) (pauliSharedProjection z)).effect b)
      rw [hdet]
      exact (deterministicMeasurement_effect_commute _ _ _).symm
    · obtain ⟨f₁, hf₁⟩ := exists_placedBasis_of_basisType P _ .Z
        (pauliCL P (.point .Z) z) (Or.inl rfl)
      change Commute _
        ((honestMagicMeasurement (.var 4) (pauliSharedProjection z)).effect b)
      rw [hf₁, ((honestMagicMeasurement_var_eq_placedBasis P hg).2)]
      solve_by_elim [placedPauliMeasurement_commute, pauliProj_isProj]

/-- The honest measurement family has commuting effects on every question pair
of positive weight for the Pauli question sampler.  This is the commutation
obligation of the honest strategy in `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1382`. -/
theorem honestMeasurement_commuting :
    IsCommutingOn (pauliQuestionDistribution P)
      (fun q : PauliQuestion P => honestMeasurement q.1 q.2)
      (fun q : PauliQuestion P => honestMeasurement q.1 q.2) := by
  intro x y hxy a b
  obtain ⟨z, hedge, hx, hy⟩ := pauliQuestionDistribution_pos_incidence hxy
  simp_all
  rcases pauliEdges_cases hedge with heq | ⟨s₁, s₂, hs₁, hs₂, hms⟩ | hor | hor
  · rw [heq]
    by_cases hab : a = b
    · subst hab
      exact Commute.refl _
    · rw [commute_iff_eq,
        DistanceCalculus.projective_effect_mul_effect_eq_zero _
          (honestMeasurement_projective P y.1 _) hab,
        DistanceCalculus.projective_effect_mul_effect_eq_zero _
          (honestMeasurement_projective P y.1 _) (Ne.symm hab)]
  · simp_all
    exact honestMagicMeasurement_ms_commute P _ hms a b
  · solve_by_elim [honestMeasurement_commute_of_oriented]
  · exact (honestMeasurement_commute_of_oriented P hor z b a).symm

end

end MIPStarRE.QPBT
