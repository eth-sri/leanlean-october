module

public import QPBT.Observables.ExpandedPlacement
public import QPBT.Observables.IdealPointConsistency
public import QPBT.Games.DistanceTheorems.TensorConsistency

/-! Joint readouts on the opposite register pairs of the expanded strategy. -/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-- The four directed cross-party placement pairs asserted by the source's
“symmetric equivalents” clause. The relation lists the two orientations of
each of the `AA'`--`BA''` and `BB'`--`AB''` pairs; paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`, blueprint
`def:symmetric-equivalents`. -/
def Placement.IsOpposite : Placement → Placement → Prop
  | .AA', .BA'' => True
  | .BA'', .AA' => True
  | .BB', .AB'' => True
  | .AB'', .BB' => True
  | _, _ => False

namespace Placement

open ProjectiveSetting (overlapPartner)

theorem eq_overlapPartner {p q : Placement} (h : p.IsOpposite q) : q = overlapPartner p := by
  cases p <;> cases q <;> simp_all [IsOpposite, overlapPartner]

theorem opposite_partner (p : Placement) : p.IsOpposite (overlapPartner p) := by cases p <;> trivial

theorem IsOpposite.symm {p q : Placement} (h : p.IsOpposite q) : q.IsOpposite p := by
  obtain rfl := eq_overlapPartner h
  cases p <;> trivial

end Placement

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-- A register placement respects finite sums of operators.
Formalization-only auxiliary for the register placements of
`def:symmetric-equivalents`; the source uses this additivity without stating
it. -/
theorem place_finset_sum (S : ProjectiveSetting P ε) (p : Placement)
    {γ : Type*} (s : Finset γ) (O : γ → Op (S.ExpandedLocalSpace p.side)) :
    S.place p (∑ g ∈ s, O g) = ∑ g ∈ s, S.place p (O g) := map_sum (S.placeLinear p) O s

/-- A register placement of the zero operator is zero. -/
theorem place_zero (S : ProjectiveSetting P ε) (p : Placement) :
    S.place p (0 : Op (S.ExpandedLocalSpace p.side)) = 0 := map_zero (S.placeLinear p)

/-- Reindexing an operator along an equivalence preserves positivity. -/
theorem reindexOp_nonneg {ι κ : Type*} [Finite ι] [Finite κ]
    (e : ι ≃ κ) {M : Op κ} (hM : 0 ≤ M) :
    0 ≤ reindexOp e M := by
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite κ
  rw [Matrix.nonneg_iff_posSemidef] at hM ⊢
  exact hM.submatrix e.symm.symm

set_option synthInstance.maxSize 400 in
/-- A placement preserves positivity. -/
theorem place_nonneg (S : ProjectiveSetting P ε) :
    ∀ (p : Placement) {A : Op (S.ExpandedLocalSpace p.side)}, 0 ≤ A →
      0 ≤ S.place p A := by
  intro p A hA
  rw [place_eq_reindex]
  exact reindexOp_nonneg _ (MIPStarRE.Quantum.kronecker_nonneg hA Matrix.PosSemidef.one.nonneg)

/-- A complete measurement on a local expanded space, placed on one of the
four register pairs, is a complete measurement on the six-register space. -/
def placedMeasurement (S : ProjectiveSetting P ε) (p : Placement) {α : Type*}
    [Fintype α] (M : Measurement α (S.ExpandedLocalSpace p.side)) :
    Measurement α (S.ExpandedSpace) :=
  M.mapEffects (S.placeLinear p).toAddMonoidHom (S.place_one p) (fun {_} h => S.place_nonneg p h)

/-- The effects of a placed measurement are the placed effects. -/
@[simp] theorem placedMeasurement_effect (S : ProjectiveSetting P ε)
    (p : Placement) {α : Type*} [Fintype α]
    (M : Measurement α (S.ExpandedLocalSpace p.side)) (a : α) :
    (S.placedMeasurement p M).effect a = S.place p (M.effect a) := rfl

/-- Placing a measurement does not change its classical postprocessing. -/
@[simp] theorem placedMeasurement_postprocess (S : ProjectiveSetting P ε) (p : Placement)
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (M : Measurement α (S.ExpandedLocalSpace p.side)) (f : α → β) :
    (S.placedMeasurement p M).postprocess f = S.placedMeasurement p (M.postprocess f) := by
  apply Quantum.Measurement.ext
  intro b
  simp only [Measurement.postprocess_effect, placedMeasurement_effect, place_finset_sum]

/-- Postprocessing the left measurement groups, but does not alter, its overlap
with a family indexed by the postprocessed answer. -/
theorem placed_overlap_postprocess
    {Answer Output : Type*} [Fintype Answer] [DecidableEq Answer]
    [Fintype Output] [DecidableEq Output]
    (setting : ProjectiveSetting P ε) (first second : Placement)
    (measurement : Quantum.Measurement Answer (setting.ExpandedLocalSpace first.side))
    (mapping : Answer → Output) (right : Output → Op (setting.ExpandedLocalSpace second.side)) :
    (∑ output, setting.placedCorrelation first second
      ((measurement.postprocess mapping).effect output) (right output)) =
      ∑ answer, setting.placedCorrelation first second (measurement.effect answer) (right (mapping answer)) := by
  simp only [placedCorrelation, Quantum.Measurement.postprocess_effect, place_finset_sum,
    Finset.sum_mul, stateQForm_finset_sum, Finset.sum_fiberwise_apply]

/-- The mismatch mass of local measurement families on the expanded state. -/
abbrev placedDefect (S : ProjectiveSetting P ε) {X α : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    (p q : Placement) (μ : Distribution X)
    (A : X → Measurement α (S.ExpandedLocalSpace p.side))
    (B : X → Measurement α (S.ExpandedLocalSpace q.side)) :=
  measurementDefect μ (fun x => S.placedMeasurement p (A x))
    (fun x => S.placedMeasurement q (B x)) S.psiHat

/-- For a normalized state, mismatch is one minus the diagonal overlap. -/
theorem placedDefect_eq_one_sub (S : ProjectiveSetting P ε) {X α : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    (p q : Placement) (μ : Distribution X)
    (A : X → Measurement α (S.ExpandedLocalSpace p.side))
    (B : X → Measurement α (S.ExpandedLocalSpace q.side)) (hμ : μ.IsProbability) :
    S.placedDefect p q μ A B =
      1 - avgOver μ (fun x => ∑ a, S.placedCorrelation p q ((A x).effect a) ((B x).effect a)) :=
  consistencyDefect_eq_one_sub_overlap _ _ _ _ hμ S.psiHat_norm

/-- Reversing both operands does not change the real mismatch mass. -/
theorem placedDefect_symm (S : ProjectiveSetting P ε) {X α : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    (p q : Placement) (μ : Distribution X)
    (A : X → Measurement α (S.ExpandedLocalSpace p.side))
    (B : X → Measurement α (S.ExpandedLocalSpace q.side)) :
    S.placedDefect p q μ A B = S.placedDefect q p μ B A :=
  DistanceCalculus.measurementDefect_symm _ _ _ _

set_option synthInstance.maxSize 400 in
/-- Operators on the two sides of this register partition commute. -/
theorem place_AA'_mul_place_BA''_comm (S : ProjectiveSetting P ε)
    (X : Op (S.ExpandedLocalSpace .alice)) (Y : Op (S.ExpandedLocalSpace .bob)) :
    S.place .AA' X * S.place .BA'' Y = S.place .BA'' Y * S.place .AA' X := by
  rw [← reindexOp_aaBaBipartition_left, ← reindexOp_aaBaBipartition_right,
    ← reindexOp_mul, ← reindexOp_mul]
  congr 1
  exact WinImplications.heteroKron_left_right_comm _ _

set_option synthInstance.maxSize 400 in
/-- Operators on the two sides of this register partition commute. -/
theorem place_AB''_mul_place_BB'_comm (S : ProjectiveSetting P ε)
    (X : Op (S.ExpandedLocalSpace .alice)) (Y : Op (S.ExpandedLocalSpace .bob)) :
    S.place .AB'' X * S.place .BB' Y = S.place .BB' Y * S.place .AB'' X := by
  rw [← reindexOp_abBbBipartition_left, ← reindexOp_abBbBipartition_right,
    ← reindexOp_mul, ← reindexOp_mul]
  congr 1
  exact WinImplications.heteroKron_left_right_comm _ _

/-! ## The four placement pairs -/

set_option synthInstance.maxSize 400

section

variable (S : ProjectiveSetting P ε) (p : Placement)
include S p

def strategyOverlap :
    Op (S.LocalSpace p.side) → Op (S.LocalSpace (overlapPartner p).side) → ℝ :=
  match p with
  | .AA' | .AB'' => fun A B => stateQForm S.toStrategy.ψ (heteroKron A B)
  | .BA'' | .BB' => fun B A => stateQForm S.toStrategy.ψ (heteroKron A B)

private theorem placed_overlap_factor
    (A : Op (S.LocalSpace p.side)) (B : Op (S.LocalSpace (overlapPartner p).side))
    (L R : Op (PauliRegister P))
    (hL : L.IsHermitian) (hR : R.IsHermitian) :
    S.placedCorrelation p (overlapPartner p) (heteroKron A L) (heteroKron B R) =
    strategyOverlap S p A B * stateQForm (eprState (PauliRegister P)) (heteroKron L R) := by
  unfold placedCorrelation
  cases p
  · exact S.stateQForm_placeOnEpr_mul true A B L R hL hR
  · rw [← place_AA'_mul_place_BA''_comm S, stateQForm_eprState_swap L R]
    exact S.stateQForm_placeOnEpr_mul true B A R L hR hL
  · rw [← place_AB''_mul_place_BB'_comm S]
    exact S.stateQForm_placeOnEpr_mul false B A R L hR hL
  · rw [stateQForm_eprState_swap L R]
    exact S.stateQForm_placeOnEpr_mul false A B L R hL hR

private theorem placed_overlap_match
    {A B X : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype X] [DecidableEq X]
    (M : Measurement A (S.ExpandedLocalSpace p.side))
    (N : Measurement B (S.ExpandedLocalSpace (overlapPartner p).side))
    (f : A → X) (g : B → X) :
    (∑ x, S.placedCorrelation p (overlapPartner p) ((M.postprocess f).effect x) ((N.postprocess g).effect x)) =
    ∑ a, ∑ b, if f a = g b then S.placedCorrelation p (overlapPartner p) (M.effect a) (N.effect b) else 0 := by
  let w a b := S.placedCorrelation p (overlapPartner p) (M.effect a) (N.effect b)
  change (∑ x, S.placedCorrelation p (overlapPartner p) (∑ a ∈ Finset.univ.filter (fun a => f a = x), M.effect a) (∑ b ∈ Finset.univ.filter (fun b => g b = x), N.effect b)) = _
  simp_rw [placedCorrelation, place_finset_sum, Finset.sum_mul, Finset.mul_sum, stateQForm_finset_sum]
  exact sum_matching_fibers f g w


/-- A common injective shift controlled by the EPR readout preserves the
strategy overlap on every directed opposite placement pair. -/
theorem placed_shift_overlap
    (W : PauliKind) (u : PauliPoint P)
    {G Y : Type*} [Fintype G] [DecidableEq G] [Fintype Y] [DecidableEq Y]
    (A : Measurement G (S.LocalSpace p.side))
    (B : Measurement G (S.LocalSpace (overlapPartner p).side))
    (shift : G → PauliScalar P → Y) (hinj : ∀ c, Function.Injective (shift · c)) :
    let T := tauPointMeas W u
    let M := (tensorMeasurement A T).postprocess (fun a => shift a.1 a.2)
    let N := (tensorMeasurement B T).postprocess (fun a => shift a.1 a.2)
    (∑ y, S.placedCorrelation p (overlapPartner p) (M.effect y) (N.effect y)) =
      ∑ a, S.strategyOverlap p (A.effect a) (B.effect a) := by
  classical
  dsimp only
  let T := tauPointMeas W u
  let w a b := S.strategyOverlap p (A.effect a) (B.effect b)
  let q c d := stateQForm (eprState (PauliRegister P)) (heteroKron (T.effect c) (T.effect d))
  have hK (a b : G × PauliScalar P) : S.placedCorrelation p (overlapPartner p) ((tensorMeasurement A T).effect a) ((tensorMeasurement B T).effect b) = w a.1 b.1 * q a.2 b.2 :=
    placed_overlap_factor S p _ _ _ _
      (Matrix.nonneg_iff_posSemidef.mp (T.pos a.2)).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp (T.pos b.2)).isHermitian
  refine (placed_overlap_match S p (tensorMeasurement A T) (tensorMeasurement B T)
    (fun a => shift a.1 a.2) (fun a => shift a.1 a.2)).trans ?_
  simp_rw [hK]
  exact sum_matched_shift shift hinj w q
    (fun _ _ => tauPointProj_epr_joint_eq_zero_of_ne W u)
    (sum_tauPointProj_pair_stateQForm_eprState W u)

end

end ProjectiveSetting

end

end MIPStarRE.QPBT
