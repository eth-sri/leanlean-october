module

public import QPBT.Test.Completeness.HonestStrategy

/-!
# The honest Pauli measurement family

This module collects the measurements of
`MIPStarRE.QPBT.Test.Completeness.HonestStrategy` into a single measurement
family indexed by the question type of the Pauli basis test.  Each honest
measurement acts on the tensor product of the Pauli register with the qubit
supplied to the Magic Square construction, and every outcome is relabelled into
the common answer alphabet of the test.  The results recorded here are the
projectivity and the symmetry of every effect of that family.

## References

The measurement family described here is the one displayed in the proof of
`lem:pauli-completeness`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1237-1360`;
blueprint `lem:pauli-completeness`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-! ### Tensor placement and relabeling -/

/-- The one-outcome measurement, used to make the harmless branches of the
honest strategy total on questions outside the sampler support. -/
noncomputable def unitMeasurement (V : Type*) [Fintype V] [DecidableEq V] :
    Measurement Unit V :=
  Measurement.ofSumEqOne (fun _ => 1)
    (fun _ => Matrix.PosSemidef.one.nonneg) (by simp)

section

variable {α V : Type*} [Fintype α] [DecidableEq α] [Fintype V] [DecidableEq V]

/-- A deterministic measurement with prescribed outcome. -/
noncomputable def deterministicMeasurement
    (a : α) : Measurement α V :=
  (unitMeasurement V).postprocess fun _ => a

/-- A deterministic measurement is projective. -/
theorem deterministicMeasurement_projective
    (a : α) :
    MIPStarRE.QPBT.Measurement.IsProjective
      (deterministicMeasurement (V := V) a) := by
  apply SandwichProduct.postprocess_isProjective
  solve_by_elim [IsStarProjection.one]

/-- Every effect of a deterministic measurement is symmetric. -/
theorem deterministicMeasurement_effect_transpose
    (a b : α) :
    ((deterministicMeasurement (V := V) a).effect b)ᵀ =
      (deterministicMeasurement (V := V) a).effect b := by
  apply postprocess_effect_transpose
  intro u
  cases u
  exact Matrix.transpose_one

/-- A deterministic measurement has zero effect away from its prescribed
outcome. -/
theorem deterministicMeasurement_effect_eq_zero_of_ne
    {a₀ a : α} (ha : a ≠ a₀) :
    (deterministicMeasurement (V := V) a₀).effect a = 0 := by
  apply postprocess_effect_eq_zero_of_notMem
  simp_all

end

section

variable {α V W : Type*} [Fintype α] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  (M : Measurement α V)

/-- Placing a projective measurement on the first tensor factor preserves
projectivity. -/
theorem leftPlacedMeasurement_projective (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    MIPStarRE.QPBT.Measurement.IsProjective
      (DistanceCalculus.leftPlacedMeasurement (ιB := W) M) := by
  solve_by_elim [MIPStarRE.LDT.MakingMeasurementsProjective.isProj_kronecker, IsStarProjection.one]

end

/-- Two coarse-grainings of one projective measurement commute. -/
theorem postprocess_effect_commute {ζ α β V : Type*}
    [Fintype ζ] [DecidableEq ζ] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype V] [DecidableEq V]
    (M : Measurement ζ V) (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (f : ζ → α) (g : ζ → β) (a : α) (b : β) :
    Commute ((M.postprocess f).effect a) ((M.postprocess g).effect b) := by
  apply Commute.sum_left
  intro x _
  apply Commute.sum_right
  intro y _
  by_cases hxy : x = y
  · subst y
    exact Commute.refl _
  · rw [commute_iff_eq,
      DistanceCalculus.projective_effect_mul_effect_eq_zero M hM hxy,
      DistanceCalculus.projective_effect_mul_effect_eq_zero M hM (Ne.symm hxy)]

section

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W] {A B : Op V}

/-- Commutation is preserved when both operators are placed on the first
tensor factor. -/
theorem leftPlaced_commute (h : Commute A B) :
    Commute (heteroKron A (1 : Op W)) (heteroKron B (1 : Op W)) := by
  simp [commute_iff_eq, heteroKron_mul, h.eq]

/-- A zero product remains zero after placement on the first tensor factor. -/
theorem leftPlaced_mul_eq_zero (h : A * B = 0) :
    heteroKron A (1 : Op W) * heteroKron B (1 : Op W) = 0 := by
  rw [heteroKron_mul, h]
  simp [heteroKron]

end

/-- The local Hilbert-space index used by the honest Pauli strategy.  The
second factor is the qubit supplied to the Magic Square construction. -/
abbrev HonestIndex (P : AdmissibleParams) := PauliRegister P × ZMod 2

/-- Place a Pauli-register measurement on the first factor of the honest local
space and relabel its outcomes with a global answer embedding. -/
noncomputable def placedPauliMeasurement {P : AdmissibleParams}
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : Measurement α (PauliRegister P)) (f : α → PauliAnswer P) :
    Measurement (PauliAnswer P) (HonestIndex P) :=
  (DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2) M).postprocess f

/-- Incompatible coarse-grained outcomes of two measurements on the Pauli
register have zero product after tensor placement. -/
theorem placedPauliMeasurement_mul_eq_zero_of_incompatible {P : AdmissibleParams}
    {ζ : Type*} [Fintype ζ] [DecidableEq ζ]
    (M : Measurement ζ (PauliRegister P))
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (f g : ζ → PauliAnswer P)
    (a b : PauliAnswer P)
    (hbad : ∀ h, f h = a → g h = b → False) :
    (placedPauliMeasurement M f).effect a *
        (placedPauliMeasurement M g).effect b = 0 := by
  change ((DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2) M).postprocess f).effect a *
      ((DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2) M).postprocess g).effect b = 0
  classical
  rw [Measurement.postprocess_effect, Measurement.postprocess_effect,
    Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro y hy
  by_cases hxy : x = y
  · subst y
    exact (hbad x (Finset.mem_filter.mp hx).2
      (Finset.mem_filter.mp hy).2).elim
  · solve_by_elim [DistanceCalculus.projective_effect_mul_effect_eq_zero, leftPlacedMeasurement_projective]

/-- Coarse-grainings of one Pauli basis measurement commute after tensor
placement. -/
theorem placedPauliMeasurement_commute {P : AdmissibleParams}
    {ζ : Type*} [Fintype ζ] [DecidableEq ζ]
    (M : Measurement ζ (PauliRegister P))
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (f g : ζ → PauliAnswer P)
    (a b : PauliAnswer P) :
    Commute ((placedPauliMeasurement M f).effect a)
      ((placedPauliMeasurement M g).effect b) := by
  solve_by_elim [postprocess_effect_commute, leftPlacedMeasurement_projective]

/-- An answer outside a placed coarse-graining's relabelling range has zero
effect. -/
theorem placedPauliMeasurement_effect_eq_zero_of_notMem {P : AdmissibleParams}
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : Measurement α (PauliRegister P)) (f : α → PauliAnswer P)
    {a : PauliAnswer P} (ha : a ∉ Set.range f) :
    (placedPauliMeasurement M f).effect a = 0 := by
  solve_by_elim [postprocess_effect_eq_zero_of_notMem]

/-! ### The total honest measurement family -/

/-- Embed a Magic Square answer into the global Pauli-test answer alphabet. -/
def pauliAnswerOfMs {P : AdmissibleParams} : MsAnswer → PauliAnswer P
  | .triple a => .msTriple a
  | .bit a => .bit a

/-- The embedding of Magic Square answers is injective. -/
theorem pauliAnswerOfMs_injective {P : AdmissibleParams} :
    Function.Injective (@pauliAnswerOfMs P) := by
  intro a b h
  cases a <;> cases b <;> simp only [pauliAnswerOfMs] at h <;> cases h <;> rfl

section

variable (P : AdmissibleParams)

section

variable (W : PauliKind)

/-- The honest point measurement at a typed Pauli question. -/
noncomputable def honestPointMeasurement
    (z : PauliSpace P) : Measurement (PauliAnswer P) (HonestIndex P) :=
  placedPauliMeasurement (pauliPointMeasurement P W (pauliPointBlock W z))
    (fun a => .value a)

/-- The honest axis-line measurement at a typed Pauli question. -/
noncomputable def honestALineMeasurement
    (z : PauliSpace P) : Measurement (PauliAnswer P) (HonestIndex P) :=
  placedPauliMeasurement (pauliALineMeasurement P W z) (fun a => .alinePoly a)

/-- The honest diagonal-line measurement at a typed Pauli question. -/
noncomputable def honestDLineMeasurement
    (z : PauliSpace P) : Measurement (PauliAnswer P) (HonestIndex P) :=
  placedPauliMeasurement (pauliDLineMeasurement P W z) (fun a => .dlinePoly a)

/-- The honest Pauli/W measurement at a typed Pauli question. -/
noncomputable def honestPauliMeasurement :
    Measurement (PauliAnswer P) (HonestIndex P) :=
  placedPauliMeasurement (pauliBasisMeasurement W) (fun a => .pauliOutcome a)

/-- The honest Pair/W measurement at a typed Pauli question. The trace
measurement is retained when the phase is nonzero, whereas the proof of
`lem:pauli-completeness` chooses a trivial measurement in that inactive case.
The corresponding Pair checks then accept automatically. The present choice
remains projective, consistent, and commuting along the question graph, so it
gives the same existential completeness conclusion. -/
noncomputable def honestPairWMeasurement
    (z : PauliSpace P) : Measurement (PauliAnswer P) (HonestIndex P) :=
  placedPauliMeasurement
    (pauliTraceMeasurement W
      (pauliPointBlock W z)
      (match W with | .X => pauliRXBlock z | .Z => pauliRZBlock z))
    (fun a => .bit a)

end

/-- The honest Pair measurement, with a deterministic harmless branch when the
two Pair/W observables anticommute. -/
noncomputable def honestPairMeasurement
    (z : PauliSpace P) : Measurement (PauliAnswer P) (HonestIndex P) := by
  classical
  by_cases hgamma : pauliPairGamma P z = 0
  · exact placedPauliMeasurement (pauliPairMeasurement z hgamma)
      (fun a => .pairBits a)
  · exact deterministicMeasurement (V := HonestIndex P) (.pairBits (0, 0))

variable {P} in
/-- The honest Magic Square measurement at a typed Pauli question. -/
noncomputable def honestMagicMeasurement (t : MsType)
    (z : PauliSpace P) : Measurement (PauliAnswer P) (HonestIndex P) := by
  classical
  by_cases hgamma : pauliPairGamma P z = 0
  · exact deterministicMeasurement (V := HonestIndex P)
      (match t with
      | .constraint _ => (.msTriple 0 : PauliAnswer P)
      | .var _ => (.bit 0 : PauliAnswer P))
  · exact (pauliMagicMeasurement z hgamma t).postprocess pauliAnswerOfMs

variable {P} in
/-- The total honest measurement family, defined on all 26 Pauli question
types and all ambient coefficient vectors. -/
noncomputable def honestMeasurement
    (t : PauliType) (z : PauliSpace P) :
    Measurement (PauliAnswer P) (HonestIndex P) :=
  match t with
  | .point W => honestPointMeasurement P W z
  | .aline W => honestALineMeasurement P W z
  | .dline W => honestDLineMeasurement P W z
  | .pauli W => honestPauliMeasurement P W
  | .pairW W => honestPairWMeasurement P W z
  | .pair => honestPairMeasurement P z
  | .ms t => honestMagicMeasurement t z

end

section

variable {P : AdmissibleParams} {α : Type*} [Fintype α] [DecidableEq α]
  (M : Measurement α (PauliRegister P))

/-- Injective answer relabelling preserves projectivity of a placed Pauli
measurement. -/
theorem placedPauliMeasurement_projective
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (f : α → PauliAnswer P) (hf : Function.Injective f) :
    MIPStarRE.QPBT.Measurement.IsProjective (placedPauliMeasurement M f) := by
  intro a
  by_cases ha : a ∈ Set.range f
  · rcases ha with ⟨b, rfl⟩
    change IsProj (((DistanceCalculus.leftPlacedMeasurement M).postprocess f).effect
      (f b))
    rw [SandwichProduct.postprocess_effect_of_injective _ f hf b]
    solve_by_elim [MIPStarRE.LDT.MakingMeasurementsProjective.isProj_kronecker, IsStarProjection.one]
  · change IsProj
      (((DistanceCalculus.leftPlacedMeasurement M).postprocess f).effect a)
    rw [postprocess_effect_eq_zero_of_notMem _ _ ha]
    exact IsStarProjection.zero _

/-- Injective answer relabelling preserves symmetry of a placed Pauli
measurement. -/
theorem placedPauliMeasurement_effect_transpose
    (hM : ∀ a, (M.effect a)ᵀ = M.effect a)
    (f : α → PauliAnswer P) (a : PauliAnswer P) :
    ((placedPauliMeasurement M f).effect a)ᵀ =
      (placedPauliMeasurement M f).effect a := by
  apply postprocess_effect_transpose
  intro b
  change (heteroKron (M.effect b) _)ᵀ =
    heteroKron (M.effect b) (1 : Op _)
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [heteroKron]
  rw [show M.effect b j i = M.effect b i j by
    exact congrFun (congrFun (hM b) i) j]
  by_cases hkl : k = l
  · subst l
    simp
  · simp [hkl, Ne.symm hkl]

end

variable (P : AdmissibleParams)

/-- The global honest measurement is projective at every question. -/
theorem honestMeasurement_projective (t : PauliType)
    (z : PauliSpace P) :
    MIPStarRE.QPBT.Measurement.IsProjective (honestMeasurement t z) := by
  cases t with
  | point W =>
      simpa [honestMeasurement, honestPointMeasurement] using
        (placedPauliMeasurement_projective
          (pauliPointMeasurement P W (pauliPointBlock W z))
          ((pauliBasisMeasurement_postprocess_projective W _))
          (PauliAnswer.value) (by intro; simp))
  | aline W =>
      simpa [honestMeasurement, honestALineMeasurement] using
        (placedPauliMeasurement_projective (pauliALineMeasurement P W z)
          ((pauliBasisMeasurement_postprocess_projective W _))
          (PauliAnswer.alinePoly) (by intro; simp))
  | dline W =>
      simpa [honestMeasurement, honestDLineMeasurement] using
        (placedPauliMeasurement_projective (pauliDLineMeasurement P W z)
          ((pauliBasisMeasurement_postprocess_projective W _))
          (PauliAnswer.dlinePoly) (by intro; simp))
  | pauli W =>
      simpa [honestMeasurement, honestPauliMeasurement] using
        (placedPauliMeasurement_projective (pauliBasisMeasurement W)
          (pauliProj_isProj W)
          (PauliAnswer.pauliOutcome) (by intro; simp))
  | pairW W =>
      simpa [honestMeasurement, honestPairWMeasurement] using
        (placedPauliMeasurement_projective
          (pauliTraceMeasurement W (pauliPointBlock W z)
            (match W with | .X => pauliRXBlock z | .Z => pauliRZBlock z))
          (pauliTraceMeasurement_projective P W _ _)
          (PauliAnswer.bit) (by intro; simp))
  | pair =>
      classical
      by_cases hg : pauliPairGamma P z = 0
      · simpa [honestMeasurement, honestPairMeasurement, hg] using
          (placedPauliMeasurement_projective (pauliPairMeasurement z hg)
            ((pauliPairEffect_isProj hg))
            (PauliAnswer.pairBits) (by intro; simp))
      · simpa [honestMeasurement, honestPairMeasurement, hg] using
          (deterministicMeasurement_projective (α := PauliAnswer P) (.pairBits (0, 0)))
  | ms t =>
      classical
      by_cases hg : pauliPairGamma P z = 0
      · simpa [honestMeasurement, honestMagicMeasurement, hg] using
          (deterministicMeasurement_projective (α := PauliAnswer P)
            (match t with
            | .constraint _ => (.msTriple 0)
            | .var _ => (.bit 0)))
      · simpa [honestMeasurement, honestMagicMeasurement, hg] using
          (SandwichProduct.postprocess_isProjective (pauliMagicMeasurement z hg t)
            ((msStrategyMeasurement_projective _ _ _ t)) pauliAnswerOfMs)

section

variable (t : PauliType) (z : PauliSpace P)

/-- The global honest measurement has symmetric effects. -/
theorem honestMeasurement_effect_transpose (a : PauliAnswer P) :
    ((honestMeasurement t z).effect a)ᵀ =
      (honestMeasurement t z).effect a := by
  cases t with
  | point W =>
      exact placedPauliMeasurement_effect_transpose _
        ((by
           apply postprocess_effect_transpose
           intro h
           apply pauliProj_transpose)) _ _
  | aline W =>
      exact placedPauliMeasurement_effect_transpose _
        ((by
           apply postprocess_effect_transpose
           intro h
           apply pauliProj_transpose)) _ _
  | dline W =>
      exact placedPauliMeasurement_effect_transpose _
        ((by
           apply postprocess_effect_transpose
           intro h
           apply pauliProj_transpose)) _ _
  | pauli W =>
      solve_by_elim [placedPauliMeasurement_effect_transpose, pauliProj_transpose]
  | pairW W =>
      solve_by_elim [placedPauliMeasurement_effect_transpose, pauliTraceMeasurement_effect_transpose]
  | pair =>
      classical
      by_cases hg : pauliPairGamma P z = 0
      · simpa [honestMeasurement, honestPairMeasurement, hg] using
          (placedPauliMeasurement_effect_transpose (pauliPairMeasurement z hg)
            (fun β => by
              change (pauliPairEffect z β)ᵀ = _
              simp [pauliPairEffect, Matrix.transpose_mul, pauliTraceMeasurement_effect_transpose]
              exact (pauliTraceMeasurement_effect_commute hg β.1 β.2).eq.symm)
            (PauliAnswer.pairBits) a)
      · simpa [honestMeasurement, honestPairMeasurement, hg] using
          (deterministicMeasurement_effect_transpose (.pairBits (0, 0)) a)
  | ms t =>
      classical
      by_cases hg : pauliPairGamma P z = 0
      · simpa [honestMeasurement, honestMagicMeasurement, hg] using
          (deterministicMeasurement_effect_transpose
            (match t with
            | .constraint _ => (.msTriple 0)
            | .var _ => (.bit 0)) a)
      · simpa [honestMeasurement, honestMagicMeasurement, hg] using
          (postprocess_effect_transpose _
            pauliAnswerOfMs
            (pauliMagicMeasurement_effect_transpose P z hg t) a)

/-- The global honest measurement is consistent on the maximally entangled
state of the honest local space, every effect being symmetric. -/
theorem honestMeasurement_isConsistentOn :
    MIPStarRE.QPBT.Measurement.IsConsistentOn (honestMeasurement t z)
      (eprState (HonestIndex P)) := fun a =>
  epr_action_eq_of_transpose (honestMeasurement_effect_transpose P t z a)

end

end

end MIPStarRE.QPBT
