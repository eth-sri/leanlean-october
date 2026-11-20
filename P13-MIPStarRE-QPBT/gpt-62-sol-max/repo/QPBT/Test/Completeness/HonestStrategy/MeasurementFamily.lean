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

variable {α V : Type*}
    [Fintype α] [DecidableEq α] [Fintype V] [DecidableEq V]
include α V

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
  intro u
  cases u
  exact IsStarProjection.one _

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
  rw [show deterministicMeasurement (V := V) a₀ =
      (unitMeasurement V).postprocess (fun _ => a₀) by rfl]
  apply SandwichProduct.postprocess_effect_eq_zero_of_notMem
  rintro ⟨u, hu⟩
  exact ha hu.symm

end

section

variable {α V W : Type*}
    [Fintype α] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (M : Measurement α V)
include α V W M

/-- Placing a projective measurement on the first tensor factor preserves
projectivity. -/
theorem leftPlacedMeasurement_projective (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    MIPStarRE.QPBT.Measurement.IsProjective
      (DistanceCalculus.leftPlacedMeasurement (ιB := W) M) := by
  intro a
  exact MIPStarRE.LDT.MakingMeasurementsProjective.isProj_kronecker
    (hM a) (IsStarProjection.one _)

/-- Tensor placement on the first factor preserves symmetry of effects. -/
theorem leftPlacedMeasurement_effect_transpose (hM : ∀ a, (M.effect a)ᵀ = M.effect a) (a : α) :
    ((DistanceCalculus.leftPlacedMeasurement (ιB := W) M).effect a)ᵀ =
      (DistanceCalculus.leftPlacedMeasurement (ιB := W) M).effect a := by
  change (heteroKron (M.effect a) (1 : Op W))ᵀ =
    heteroKron (M.effect a) (1 : Op W)
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [Matrix.transpose_apply, heteroKron, Matrix.kronecker,
    Matrix.kroneckerMap_apply]
  rw [show M.effect a j i = M.effect a i j by
    exact congrFun (congrFun (hM a) i) j]
  by_cases hkl : k = l
  · subst l
    simp
  · simp [hkl, Ne.symm hkl]

end

section

variable {ζ α β V : Type*}
    [Fintype ζ] [DecidableEq ζ] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype V] [DecidableEq V]
    (M : Measurement ζ V) (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (f : ζ → α) (g : ζ → β) (a : α) (b : β)
include ζ α β V M hM f g a b

/-- Two coarse-grainings of one projective measurement commute. -/
theorem postprocess_effect_commute :
    Commute ((M.postprocess f).effect a) ((M.postprocess g).effect b) := by
  refine postprocess_commute_of_commute M M (fun x y => ?_) f g a b
  by_cases h : x = y
  · subst y
    exact Commute.refl _
  · rw [commute_iff_eq, DistanceCalculus.projective_effect_mul_effect_eq_zero M hM h,
      DistanceCalculus.projective_effect_mul_effect_eq_zero M hM (Ne.symm h)]

/-- Incompatible fibers of two coarse-grainings of one projective measurement
have zero product. -/
theorem postprocess_effect_mul_eq_zero_of_incompatible
    (hbad : ∀ z, f z = a → g z = b → False) :
    (M.postprocess f).effect a * (M.postprocess g).effect b = 0 := by
  refine postprocess_effect_mul_eq_zero M M f g a b fun x y hx hy => ?_
  by_cases h : x = y
  · subst y
    exact (hbad x hx hy).elim
  · exact DistanceCalculus.projective_effect_mul_effect_eq_zero M hM h

end

section

variable {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    {A B : Op V}
include V W A B

/-- Commutation is preserved when both operators are placed on the first
tensor factor. -/
theorem leftPlaced_commute (h : Commute A B) :
    Commute (heteroKron A (1 : Op W)) (heteroKron B (1 : Op W)) := by
  rw [commute_iff_eq, heteroKron_mul, heteroKron_mul, h.eq]

/-- A zero product remains zero after placement on the first tensor factor. -/
theorem leftPlaced_mul_eq_zero (h : A * B = 0) :
    heteroKron A (1 : Op W) * heteroKron B (1 : Op W) = 0 := by
  rw [heteroKron_mul, h]
  simp_all [heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply]

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
  DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2) (M.postprocess f)

section

variable {P : AdmissibleParams}
    {ζ : Type*} [Fintype ζ] [DecidableEq ζ]
    (M : Measurement ζ (PauliRegister P))
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (f g : ζ → PauliAnswer P)
    (a b : PauliAnswer P)
include P ζ M hM f g a b

/-- Incompatible coarse-grained outcomes of two measurements on the Pauli
register have zero product after tensor placement. -/
theorem placedPauliMeasurement_mul_eq_zero_of_incompatible
    (hbad : ∀ h, f h = a → g h = b → False) :
    (placedPauliMeasurement M f).effect a *
        (placedPauliMeasurement M g).effect b = 0 := by
  exact leftPlaced_mul_eq_zero (postprocess_effect_mul_eq_zero_of_incompatible M hM f g a b hbad)

/-- Coarse-grainings of one Pauli basis measurement commute after tensor
placement. -/
theorem placedPauliMeasurement_commute :
    Commute ((placedPauliMeasurement M f).effect a)
      ((placedPauliMeasurement M g).effect b) := by
  exact leftPlaced_commute (postprocess_effect_commute M hM f g a b)

end

/-- An answer outside a placed coarse-graining's relabelling range has zero
effect. -/
theorem placedPauliMeasurement_effect_eq_zero_of_notMem {P : AdmissibleParams}
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : Measurement α (PauliRegister P)) (f : α → PauliAnswer P)
    {a : PauliAnswer P} (ha : a ∉ Set.range f) :
    (placedPauliMeasurement M f).effect a = 0 := by
  change heteroKron ((M.postprocess f).effect a) (1 : Op (ZMod 2)) = 0
  rw [SandwichProduct.postprocess_effect_eq_zero_of_notMem _ _ ha]
  exact Matrix.zero_kronecker _

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
include P

section

variable (W : PauliKind)
    (z : PauliSpace P)
include W z

/-- The honest point measurement at a typed Pauli question. -/
noncomputable def honestPointMeasurement : Measurement (PauliAnswer P) (HonestIndex P) :=
  placedPauliMeasurement (pauliBasisMeasurement W) (fun h => .value (lowDegreeEnc h (pauliPointBlock W z)))

/-- The honest axis-line measurement at a typed Pauli question. -/
noncomputable def honestALineMeasurement : Measurement (PauliAnswer P) (HonestIndex P) :=
  placedPauliMeasurement (pauliBasisMeasurement W) (fun h => .alinePoly
    (restrictToAxisLine P.toLdParams
      (aLineDescOf P.toLdParams (ldALineCL P.toLdParams (pauliToLd P W z))) (lowDegreeEncoding h)))

/-- The honest diagonal-line measurement at a typed Pauli question. -/
noncomputable def honestDLineMeasurement : Measurement (PauliAnswer P) (HonestIndex P) :=
  placedPauliMeasurement (pauliBasisMeasurement W) (fun h => .dlinePoly
    (restrictToLine P.toLdParams
      (dLineDescOf P.toLdParams (ldDLineCL P.toLdParams (pauliToLd P W z))) (lowDegreeEncoding h)))

end

/-- The honest Pauli/W measurement at a typed Pauli question. -/
noncomputable def honestPauliMeasurement (W : PauliKind) :
    Measurement (PauliAnswer P) (HonestIndex P) :=
  placedPauliMeasurement (pauliBasisMeasurement W) (fun a => .pauliOutcome a)

/-- The honest Pair/W measurement at a typed Pauli question. The trace
measurement is retained when the phase is nonzero, whereas the proof of
`lem:pauli-completeness` chooses a trivial measurement in that inactive case.
The corresponding Pair checks then accept automatically. The present choice
remains projective, consistent, and commuting along the question graph, so it
gives the same existential completeness conclusion. -/
noncomputable def honestPairWMeasurement (W : PauliKind)
    (z : PauliSpace P) : Measurement (PauliAnswer P) (HonestIndex P) :=
  placedPauliMeasurement
    (pauliTraceMeasurement P W
      (pauliPointBlock W z)
      (match W with | .X => pauliRXBlock z | .Z => pauliRZBlock z))
    (fun a => .bit a)

/-- The honest Pair measurement, with a deterministic harmless branch when the
two Pair/W observables anticommute. -/
noncomputable def honestPairMeasurement
    (z : PauliSpace P) : Measurement (PauliAnswer P) (HonestIndex P) := by
  classical
  by_cases hgamma : pauliPairGamma P z = 0
  · exact placedPauliMeasurement (pauliPairMeasurement P z hgamma)
      (fun a => .pairBits a)
  · exact deterministicMeasurement (V := HonestIndex P) (.pairBits (0, 0))

/-- The honest Magic Square measurement at a typed Pauli question. -/
noncomputable def honestMagicMeasurement (t : MsType)
    (z : PauliSpace P) : Measurement (PauliAnswer P) (HonestIndex P) := by
  classical
  by_cases hgamma : pauliPairGamma P z = 0
  · exact deterministicMeasurement (V := HonestIndex P)
      (match t with
      | .constraint _ => (.msTriple 0 : PauliAnswer P)
      | .var _ => (.bit 0 : PauliAnswer P))
  · exact (pauliMagicMeasurement P z hgamma t).postprocess pauliAnswerOfMs

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
  | .ms t => honestMagicMeasurement P t z

/-- The honest measurement on the typed image of a common sample. -/
noncomputable abbrev honestSampleMeasurement
    (t : PauliType) (z : PauliSpace P) := honestMeasurement P t (pauliCL P t z)

end

/-- The two properties needed for the honest strategy on an EPR state. -/
private abbrev SymmetricProjective {α V : Type*} [Fintype α] [DecidableEq α]
    [Fintype V] [DecidableEq V] (M : Measurement α V) : Prop :=
  Measurement.IsProjective M ∧ ∀ a, (M.effect a)ᵀ = M.effect a

private theorem symmetricProjective_postprocess {α β V : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype V] [DecidableEq V]
    (M : Measurement α V) (h : SymmetricProjective M) (f : α → β) :
    SymmetricProjective (M.postprocess f) :=
  ⟨SandwichProduct.postprocess_isProjective M h.1 f, postprocess_effect_transpose M f h.2⟩

private theorem placedPauliMeasurement_symmetricProjective {P : AdmissibleParams}
    {α : Type*} [Fintype α] [DecidableEq α] (M : Measurement α (PauliRegister P))
    (h : SymmetricProjective M) (f : α → PauliAnswer P) :
    SymmetricProjective (placedPauliMeasurement M f) :=
  let H := symmetricProjective_postprocess M h f
  ⟨leftPlacedMeasurement_projective _ H.1, leftPlacedMeasurement_effect_transpose _ H.2⟩

private theorem deterministic_symmetricProjective {α V : Type*}
    [Fintype α] [DecidableEq α] [Fintype V] [DecidableEq V] (a : α) :
    SymmetricProjective (deterministicMeasurement (V := V) a) :=
  ⟨deterministicMeasurement_projective a, deterministicMeasurement_effect_transpose a⟩

private theorem pauli_readout_symmetricProjective {P : AdmissibleParams}
    {α : Type*} [Fintype α] [DecidableEq α] (W : PauliKind) (f : PauliRegister P → α) :
    SymmetricProjective ((pauliBasisMeasurement W).postprocess f) :=
  symmetricProjective_postprocess (pauliBasisMeasurement W)
    ⟨fun a => pauliProj_isProj W a, pauliProj_transpose W⟩ f

section

variable (P : AdmissibleParams) (t : PauliType)
    (z : PauliSpace P)
include P t z

/-- The honest measurement is projective with symmetric matrix effects. -/
private theorem honestMeasurement_symmetricProjective : SymmetricProjective (honestMeasurement P t z) := by
  cases t with
  | point W | aline W | dline W | pauli W =>
    exact placedPauliMeasurement_symmetricProjective (pauliBasisMeasurement W)
      ⟨fun a => pauliProj_isProj W a, pauliProj_transpose W⟩ _
  | pairW W =>
    exact placedPauliMeasurement_symmetricProjective _ (pauli_readout_symmetricProjective W _) _
  | pair =>
    classical
    change SymmetricProjective (honestPairMeasurement P z)
    unfold honestPairMeasurement
    split
    · rename_i hg
      apply placedPauliMeasurement_symmetricProjective
      refine ⟨pauliPairMeasurement_projective P z hg, fun β => ?_⟩
      change (pauliPairEffect P z β)ᵀ = pauliPairEffect P z β
      rw [pauliPairEffect, Matrix.transpose_mul,
        pauliTraceMeasurement_effect_transpose, pauliTraceMeasurement_effect_transpose]
      exact (pauliTraceMeasurement_effect_commute P z hg β.1 β.2).eq.symm
    · exact deterministic_symmetricProjective _
  | ms t =>
    classical
    change SymmetricProjective (honestMagicMeasurement P t z)
    unfold honestMagicMeasurement
    split
    · exact deterministic_symmetricProjective _
    · exact symmetricProjective_postprocess _
        ⟨pauliMagicMeasurement_projective P z _ t, pauliMagicMeasurement_effect_transpose P z _ t⟩ _

/-- The global honest measurement is projective at every question. -/
theorem honestMeasurement_projective :
    Measurement.IsProjective (honestMeasurement P t z) :=
  (honestMeasurement_symmetricProjective P t z).1

/-- The global honest measurement has symmetric effects. -/
theorem honestMeasurement_effect_transpose (a : PauliAnswer P) :
    ((honestMeasurement P t z).effect a)ᵀ = (honestMeasurement P t z).effect a :=
  (honestMeasurement_symmetricProjective P t z).2 a

/-- The global honest measurement is consistent on the maximally entangled
state of the honest local space, every effect being symmetric. -/
theorem honestMeasurement_isConsistentOn :
    MIPStarRE.QPBT.Measurement.IsConsistentOn (honestMeasurement P t z)
      (eprState (HonestIndex P)) := fun a =>
  epr_action_eq_of_transpose _ (honestMeasurement_effect_transpose P t z a)

/-- The effects of one honest measurement commute with one another; this is the
commutation along the self-loops of the Pauli question graph in
`lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1372`. -/
theorem honestMeasurement_self_commute (a b : PauliAnswer P) :
    Commute ((honestMeasurement P t z).effect a)
      ((honestMeasurement P t z).effect b) := by
  by_cases hab : a = b
  · subst hab
    exact Commute.refl _
  · rw [commute_iff_eq,
      DistanceCalculus.projective_effect_mul_effect_eq_zero _
        (honestMeasurement_projective P t z) hab,
      DistanceCalculus.projective_effect_mul_effect_eq_zero _
        (honestMeasurement_projective P t z) (Ne.symm hab)]

end

end

end MIPStarRE.QPBT
