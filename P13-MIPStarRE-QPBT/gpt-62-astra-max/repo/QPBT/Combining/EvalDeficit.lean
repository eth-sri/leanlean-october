module

public import QPBT.Combining.Lines
public import QPBT.Combining.OrderedPoints
public import QPBT.Combining.OverlapGap

/-! # Point deficits of the evaluated pair-line measurement

Complete the point-pair measurement at the two undefined scalar outcomes and
bound the overlap deficit for either component over a product of restricted
line-point laws. For each basis, the distance comparison uses the corresponding
order of the expanded point projections. This is the common estimate for
`lem:claim-17-2` and `lem:claim-17-3` in the Pauli basis test analysis.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

/-! ## Completed point pairs -/

/-- A sum over completed outcome pairs of a function vanishing on both `none`
classes is the sum over the uncompleted pairs. -/
theorem sum_option_prod_eq_of_none {β γ : Type*} [Fintype β] [Fintype γ]
    (F : Option β × Option γ → ℝ) (h1 : ∀ o2, F (none, o2) = 0)
    (h2 : ∀ o1, F (o1, none) = 0) :
    (∑ o, F o) = ∑ bc : β × γ, F (some bc.1, some bc.2) := by
  calc _
      = _ := Fintype.sum_prod_type (f := F)
    _ = _ := Fintype.sum_option _
    _ = ∑ b : β, ∑ o2 : Option γ, F (some b, o2) := by
        simp_all
    _ = _ :=
        Finset.sum_congr rfl fun b _ => Fintype.sum_option _
    _ = ∑ b : β, ∑ c : γ, F (some b, some c) := by
        grind
    _ = _ :=
        (Fintype.sum_prod_type (f := fun bc : β × γ => F (some bc.1, some bc.2))).symm

section

variable {β γ d : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ] [Fintype d]
  [DecidableEq d] (Q : Measurement (β × γ) d)

/-- The completed joint measurement has the joint effect on a pair of
evaluations. -/
theorem completedPair_effect_some (bc : β × γ) :
    (Q.postprocess fun ab => (some ab.1, some ab.2)).effect (some bc.1, some bc.2) =
      Q.effect bc := by
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect,
    show (Finset.univ.filter fun cd : β × γ =>
        (some cd.1, some cd.2) = (some bc.1, some bc.2)) = {bc} by
      grind]
  simp

/-- The completed joint measurement vanishes on outcomes outside the image of
the completion. -/
theorem completedPair_effect_eq_zero (o : Option β × Option γ)
    (ho : ∀ bc : β × γ, (some bc.1, some bc.2) ≠ o) :
    (Q.postprocess fun ab => (some ab.1, some ab.2)).effect o = 0 := by
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  simp [*]

/-- The completion of a projective joint measurement is projective. -/
theorem completedPair_isProjective (hQ : Measurement.IsProjective Q) :
    Measurement.IsProjective (Q.postprocess fun ab => (some ab.1, some ab.2)) := by
  intro o
  by_cases h : ∃ bc : β × γ, (some bc.1, some bc.2) = o
  · obtain ⟨bc, rfl⟩ := h
    rw [completedPair_effect_some]
    exact hQ bc
  · push Not at h
    rw [completedPair_effect_eq_zero Q o h]
    exact IsStarProjection.zero _

end

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

variable (S : ProjectiveSetting P ε) {δ : ℝ} (points : CombinedPointsWitness S δ)
  (p : Placement)

/-- A placed projection is a projection. -/
theorem place_isProj
    {E : Op (S.ExpandedLocalSpace p.side)} (hE : IsProj E) :
    IsProj (S.place p E) := by
  refine isStarProjection_iff'.2 ⟨?_, ?_⟩
  · rw [← place_mul, hE.isIdempotentElem.eq]
  · rw [Matrix.star_eq_conjTranspose, ← place_conjTranspose,
      hE.isSelfAdjoint.isHermitian.eq]

/-- Every effect of the completed expanded point measurement is a projection,
the `none` effect being zero. -/
theorem pointMeasExpOption_isProj
    (side : PlayerSide) (W : PauliKind) (u : PauliPoint P)
    (o : Option (PauliScalar P)) :
    IsProj ((S.pointMeasExpOption side W u).effect o) := by
  cases o with
  | none =>
    simp [S.pointMeasExpOption_effect_none]
  | some a =>
    rw [S.pointMeasExpOption_effect_some]
    apply S.pointMeasExp_isProjective

/-- The completed joint point measurement and a completed point product differ
only on outcome pairs with two evaluations, so their placed state-dependent
squared distance is the one of the joint point measurement and the point
product.  Blueprint `ch15_qpbt_combining.tex:2651-2698`. -/
theorem sum_norm_place_completedPair_sub_sq
    (Q : Measurement (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace p.side))
    (Gc : Option (PauliScalar P) × Option (PauliScalar P) →
      Op (S.ExpandedLocalSpace p.side))
    (G : PauliScalar P × PauliScalar P → Op (S.ExpandedLocalSpace p.side))
    (hsome : ∀ ab : PauliScalar P × PauliScalar P, Gc (some ab.1, some ab.2) = G ab)
    (hnone1 : ∀ o2, Gc (none, o2) = 0) (hnone2 : ∀ o1, Gc (o1, none) = 0) :
    (∑ o : Option (PauliScalar P) × Option (PauliScalar P),
        ‖applyOperatorToState
          (S.place p ((Q.postprocess fun ab => (some ab.1, some ab.2)).effect o) -
            S.place p (Gc o)) S.psiHat‖ ^ 2) =
      ∑ ab : PauliScalar P × PauliScalar P,
        ‖applyOperatorToState (S.place p (Q.effect ab) - S.place p (G ab))
          S.psiHat‖ ^ 2 := by
  refine Eq.trans (sum_option_prod_eq_of_none _ ?_ ?_) ?_
  · intro o2
    rw [completedPair_effect_eq_zero Q (none, o2) (fun ab => by simp), hnone1,
      place_zero, sub_self]
    simp [applyOperatorToState]
  · intro o1
    rw [completedPair_effect_eq_zero Q (o1, none) (fun ab => by simp), hnone2,
      place_zero, sub_self]
    simp [applyOperatorToState]
  · congr 1 with ab
    rw [completedPair_effect_some, hsome]

end ProjectiveSetting

/-! ## The abstract one-point deficit -/

/-- Let `A` be a complete measurement, `Q` a projective measurement, `R` a
family of projections and `W` a family of operators, all indexed by the same
outcomes, with `Q`, `R` and `W` commuting with the effects of `A` and with
`W R = W`.  If `A` and `Q` are consistent with defect at most `η` and `Q` is
within squared distance `ζ` of `Wᴴ`, then the deficit of the overlap of `A`
with `R` is at most `2 √η + 2 √ζ`.  The proof inserts `Q` before `R`, replaces
`Q R` by `W R = W`, and compares `W` with `Q`; each of the three steps is a
Cauchy--Schwarz estimate weighted by `A`.  This is the common estimate behind
the deficits in the proofs of `lem:claim-17-2` and `lem:claim-17-3`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1168-1239`. -/
theorem one_sub_overlap_le_of_consistencyDefect {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A Q : X → Measurement α ι) (R W : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1)
    (hQ : ∀ x, Measurement.IsProjective (Q x)) (hR : ∀ x a, IsProj (R x a))
    (hAQ : ∀ x a, Commute ((A x).effect a) ((Q x).effect a))
    (hAR : ∀ x a, Commute ((A x).effect a) (R x a))
    (hAW : ∀ x a, Commute ((A x).effect a) (W x a))
    (hWR : ∀ x a, W x a * R x a = W x a)
    (hnonneg : ∀ x a, 0 ≤ stateQForm ψ ((A x).effect a * (Q x).effect a))
    (η ζ : ℝ)
    (hcons : consistencyDefect μ (fun x a => (A x).effect a)
      (fun x a => (Q x).effect a) ψ ≤ η)
    (hdist : opFamilyDistSq μ (fun x a => (Q x).effect a)
      (fun x a => (W x a)ᴴ) ψ ≤ ζ) :
    1 - avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * R x a)) ≤
      2 * Real.sqrt η + 2 * Real.sqrt ζ := by
  set ovQ := avgOver μ (fun x =>
    ∑ a, stateQForm ψ ((A x).effect a * (Q x).effect a)) with hovQ
  have h1 : 1 - ovQ ≤ η := by
    rw [← consistencyDefect_eq_one_sub_overlap A Q hμ hψ]
    exact hcons
  have hovQ_nonneg : 0 ≤ ovQ :=
    avgOver_nonneg μ _ fun x => Finset.sum_nonneg fun a _ => hnonneg x a
  have hovQ_le :=
    avgOver_sum_stateQForm_mul_le_one μ A _ ψ hμ hψ
      (hQ) hAQ
  have h1' : 1 - ovQ ≤ Real.sqrt η := by
    have h0 : 0 ≤ 1 - ovQ := by linarith
    calc 1 - ovQ = _ := (Real.sqrt_sq h0).symm
      _ ≤ Real.sqrt η := Real.sqrt_le_sqrt (by nlinarith)
  -- comparing `Q` with `W` under the weight `A`
  have hWconj : ∀ x a, stateQForm ψ ((A x).effect a * W x a) =
      stateQForm ψ ((A x).effect a * (W x a)ᴴ) := by
    intro x a
    rw [← stateQForm_conjTranspose,
      Matrix.conjTranspose_mul, measurement_effect_hermitian]
    congr 1
    have h := congrArg Matrix.conjTranspose (hAW x a).eq
    simp [Matrix.conjTranspose_mul, measurement_effect_hermitian] at h
    exact h
  have h2 : |ovQ - avgOver μ (fun x =>
      ∑ a, stateQForm ψ ((A x).effect a * W x a))| ≤ Real.sqrt ζ := by
    simp [*]
    solve_by_elim [abs_overlap_gap_le_sqrt_of_opFamilyDistSq]
  -- replacing `Q R` by `W R = W`
  have h4 : |avgOver μ (fun x =>
      ∑ a, stateQForm ψ ((A x).effect a * ((Q x).effect a * R x a))) -
        avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * W x a))| ≤
      Real.sqrt ζ := by
    have hpt : ∀ x,
        (∑ a, stateQForm ψ ((A x).effect a * ((Q x).effect a * R x a))) -
          (∑ a, stateQForm ψ ((A x).effect a * W x a)) =
        ∑ a, stateQForm ψ ((A x).effect a * (((Q x).effect a - W x a) * R x a)) := by
      intro x
      rw [← Finset.sum_sub_distrib]
      congr 1 with a
      rw [sub_mul, hWR]
      simp [stateQForm, applyOperatorToState]
    rw [← avgOver_sub, avgOver_congr μ _ _ hpt]
    refine (abs_avgOver_sum_stateQForm_mul_le_sqrt_of_isProj' μ A
      _ R ψ hμ hψ hR hAR
      (fun x a => (hAQ x a).sub_right (hAW x a))).trans (Real.sqrt_le_sqrt ?_)
    refine le_of_eq_of_le ?_ hdist
    apply avgOver_congr
    simp [measurement_effect_hermitian]
  -- inserting `Q` before `R`
  have h5 : |avgOver μ (fun x =>
      ∑ a, stateQForm ψ ((A x).effect a * ((Q x).effect a * R x a))) -
        avgOver μ (fun x => ∑ a, stateQForm ψ ((A x).effect a * R x a))| ≤
      Real.sqrt η := by
    have hpt : ∀ x,
        (∑ a, stateQForm ψ ((A x).effect a * R x a)) -
          (∑ a, stateQForm ψ ((A x).effect a * ((Q x).effect a * R x a))) =
        ∑ a, stateQForm ψ ((A x).effect a * ((1 - (Q x).effect a) * R x a)) := by
      simp [stateQForm, applyOperatorToState]
    rw [abs_sub_comm, ← avgOver_sub, avgOver_congr μ _ _ hpt]
    have hcs := abs_avgOver_sum_stateQForm_mul_mul_le_sqrt_mul_sqrt μ A
      (fun x a => 1 - (Q x).effect a) R ψ (fun x a => (hQ x a).one_sub)
      (fun x a => (Commute.one_right _).sub_right (hAQ x a))
    have hfirst : avgOver μ (fun x =>
        ∑ a, stateQForm ψ ((A x).effect a * (1 - (Q x).effect a))) = 1 - ovQ := by
      have hx : ∀ x,
          (∑ a, stateQForm ψ ((A x).effect a * (1 - (Q x).effect a))) =
            1 - ∑ a, stateQForm ψ ((A x).effect a * (Q x).effect a) := by
        intro x
        simp [← sum_stateQForm_effect_eq_one (A x) hψ]
        simp [stateQForm, applyOperatorToState]
      rw [avgOver_congr μ _ _ hx, avgOver_sub, avgOver_const_of_isProbability μ hμ]
    rw [hfirst] at hcs
    calc
      _ ≤ _ := hcs
      _ ≤ Real.sqrt (1 - ovQ) * 1 := by
        gcongr
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by
          rw [avgOver_congr μ _ _ fun x => Finset.sum_congr rfl fun a _ =>
            stateQForm_applyOperatorToState_eq_of_isProj ψ (hR x a) (hAR x a)]
          apply avgOver_sum_stateQForm_mul_le_one <;> assumption)
      _ = _ := mul_one _
      _ ≤ Real.sqrt η := Real.sqrt_le_sqrt h1
  have h2' := abs_le.mp h2
  have h4' := abs_le.mp h4
  have h5' := abs_le.mp h5
  linarith

/-! ## The two placed deficits -/

/-- A pair of line-point pairs of the source space: the sample type of the
consistency display of `lem:qld-xz-lines`. -/
abbrev LinePointPairSample (P : AdmissibleParams) :=
  (LineDesc P.toLdParams × (PauliPoint P)) ×
    (LineDesc P.toLdParams × (PauliPoint P))

/-- The selected component and its complementary basis. -/
def PauliKind.component {α : Type*} : PauliKind → α × α → α | .X => Prod.fst | .Z => Prod.snd

def PauliKind.other : PauliKind → PauliKind | .X => .Z | .Z => .X

section

variable {P : AdmissibleParams} {ε δQ δP : ℝ} {S : ProjectiveSetting P ε}
  {points : CombinedPointsWitness S δQ}

/-- Completing both coordinates of the joint point POVM. -/
abbrev CombinedPointsWitness.completed (points : CombinedPointsWitness S δQ) (side : PlayerSide)
    (xz : PauliPoint P × PauliPoint P) :=
  (points.Q side xz.1 xz.2).postprocess fun ab => (some ab.1, some ab.2)

/-- Joint evaluation of the two line answers at their sampled points. -/
abbrev CombinedLinesWitness.evaluated (lines : CombinedLinesWitness S points δP) (side : PlayerSide)
    (s : LinePointPairSample P) :=
  (lines.T side s.1.1 s.2.1).postprocess fun fs =>
    (evalOpt s.1.1 s.1.2 fs.1, evalOpt s.2.1 s.2.2 fs.2)

/-- The effect selected from the expanded point measurement of either basis. -/
abbrev ProjectiveSetting.componentEffect (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (xz : PauliPoint P × PauliPoint P) (o : Option (PauliScalar P) × Option (PauliScalar P)) :=
  (S.pointMeasExpOption side W (W.component xz)).effect (W.component o)

/-- Adding the `none` outcomes changes neither of the ordered-product distances. -/
theorem ProjectiveSetting.completedPair_norm_sq_sum (S : ProjectiveSetting P ε)
    (points : CombinedPointsWitness S δQ) (p : Placement) (W : PauliKind) (xz : PauliPoint P × PauliPoint P) :
    (∑ o, ‖applyOperatorToState (S.place p ((points.completed p.side xz).effect o) -
      S.place p (S.componentEffect p.side W xz o * S.componentEffect p.side W.other xz o)) S.psiHat‖ ^ 2) =
    ∑ ab : PauliScalar P × PauliScalar P, ‖applyOperatorToState
      (S.place p ((points.Q p.side xz.1 xz.2).effect ab) - S.place p
        ((S.pointMeasExp p.side W (W.component xz)).effect (W.component ab) *
         (S.pointMeasExp p.side W.other (W.other.component xz)).effect (W.other.component ab))) S.psiHat‖ ^ 2 := by
  cases W <;> apply S.sum_norm_place_completedPair_sub_sq <;>
    simp [componentEffect, PauliKind.component, PauliKind.other,
      S.pointMeasExpOption_effect_some, S.pointMeasExpOption_effect_none]

end

/-! ## The two deficits over a product of restricted line-point laws -/

section

variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι] (P : AdmissibleParams)
  (kind kindX kindZ : LineKind) (i j : Fin P.m)

/-- Every restricted line-point law has total mass one. -/
theorem restrictedLinePointDist_isProbability :
    (restrictedLinePointDist kind i).IsProbability := by
  cases kind
  · change (restrictedALineDist P.toLdParams i).IsProbability
    unfold restrictedALineDist restrictedALinePreDist
    exact (Distribution.restrict_isProbability
      (clDistribution (ldALineCL P.toLdParams) (ldPointCL P.toLdParams))
      (restrictedLineSeedEvent P.toLdParams i) (restrictedALineSeedEvent_positive P.toLdParams i)).map _
  · change (restrictedDLineDist P.toLdParams i).IsProbability
    unfold restrictedDLineDist restrictedDLinePreDist
    exact (Distribution.restrict_isProbability
      (clDistribution (ldDLineCL P.toLdParams) (ldPointCL P.toLdParams))
      (restrictedLineSeedEvent P.toLdParams i) (restrictedDLineSeedEvent_positive P.toLdParams i)).map _

/-- The point marginal of a restricted line-point law is uniform. -/
theorem restrictedLinePointDist_map_snd :
    (restrictedLinePointDist kind i).map Prod.snd =
      uniformDistribution (PauliPoint P) := by
  rw [restrictedLinePointDist_eq_map_prod, Distribution.map_map]
  exact Distribution.prod_map_fst _ (Distribution.prod_isProbability
    (subLineSeedDist_isProbability P i) (uniformDistribution_isProbability _))

/-- The pair of points of a product of two restricted line-point laws is a
uniform pair. -/
theorem prod_restrictedLinePointDist_map_points :
    (Distribution.prod (restrictedLinePointDist kindX i)
        (restrictedLinePointDist kindZ j)).map (fun s => (s.1.2, s.2.2)) =
      uniformDistribution
        ((PauliPoint P) × (PauliPoint P)) := by
  have h : Distribution.prod ((restrictedLinePointDist kindX i).map Prod.snd)
      ((restrictedLinePointDist kindZ j).map Prod.snd) =
      uniformDistribution
        ((PauliPoint P) × (PauliPoint P)) := by
    simp [restrictedLinePointDist_map_snd, uniformDistribution_prod]
  rw [← h, Distribution.prod_map_left, Distribution.prod_map_right,
    Distribution.map_map]

/-- A state-dependent distance between two families depending on the pair of
points only, averaged over a product of two restricted line-point laws, is the
distance averaged over a uniform pair of points. -/
theorem opFamilyDistSq_prod_restricted_points
    (F G : (PauliPoint P) × (PauliPoint P) → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    opFamilyDistSq
        (Distribution.prod (restrictedLinePointDist kindX i)
          (restrictedLinePointDist kindZ j))
        (fun s a => F (s.1.2, s.2.2) a) (fun s a => G (s.1.2, s.2.2) a) ψ =
      opFamilyDistSq
        (uniformDistribution
          ((PauliPoint P) × (PauliPoint P))) F G ψ := by
  unfold opFamilyDistSq
  rw [← prod_restrictedLinePointDist_map_points,
    Distribution.avgOver_map]

end

section Restricted

variable {P : AdmissibleParams} {ε δQ δP : ℝ} {S : ProjectiveSetting P ε}
  {points : CombinedPointsWitness S δQ}

/-- Either point deficit over a pair of restricted line-point laws. The basis
selects the first factor of the ordered product; the reversed product used in
the overlap estimate is its adjoint. -/
theorem CombinedLinesWitness.one_sub_overlap_restricted_le (lines : CombinedLinesWitness S points δP)
    (first second : Placement) (hopposite : first.IsOpposite second) (W : PauliKind)
    (kindX kindZ : LineKind) (i j : Fin P.m) :
    1 - avgOver (Distribution.prod (restrictedLinePointDist kindX i) (restrictedLinePointDist kindZ j))
      (fun s => ∑ o, stateQForm S.psiHat (S.place first ((lines.evaluated first.side s).effect o) *
        S.place second (S.componentEffect second.side W (s.1.2, s.2.2) o))) ≤
      2 * Real.sqrt (4 * (P.m : ℝ) ^ 2 * δP) + 2 * Real.sqrt (4 * δQ) := by
  let ν := Distribution.prod (restrictedLinePointDist kindX i) (restrictedLinePointDist kindZ j)
  let A := lines.evaluated first.side
  let Q := points.completed second.side
  let E := S.componentEffect second.side
  let xz (s : LinePointPairSample P) := (s.1.2, s.2.2)
  have hE (V : PauliKind) v o : IsProj (E V v o) := S.pointMeasExpOption_isProj _ _ _ _
  have hstar (v o) : (S.place second (E W.other v o * E W v o))ᴴ =
      S.place second (E W v o * E W.other v o) := by
    rw [← S.place_conjTranspose, Matrix.conjTranspose_mul,
      (hE W _ _).isSelfAdjoint.isHermitian.eq, (hE W.other _ _).isSelfAdjoint.isHermitian.eq]
  refine one_sub_overlap_le_of_consistencyDefect ν (fun s => S.placedMeasurement first (A s))
    (fun s => S.placedMeasurement second (Q (xz s))) (fun s o => S.place second (E W (xz s) o))
    (fun s o => S.place second (E W.other (xz s) o * E W (xz s) o)) S.psiHat
    (Distribution.prod_isProbability (restrictedLinePointDist_isProbability P kindX i)
      (restrictedLinePointDist_isProbability P kindZ j)) S.psiHat_norm
    (fun s => S.placedMeasurement_isProjective _ _ (completedPair_isProjective _ (points.projective _ _ _)))
    (fun s o => S.place_isProj _ (hE _ _ _))
    (fun _ _ => S.place_comm _ _ hopposite _ _) (fun _ _ => S.place_comm _ _ hopposite _ _)
    (fun _ _ => S.place_comm _ _ hopposite _ _) ?_
    (fun s o => stateQForm_nonneg _ (S.place_mul_place_nonneg _ _ hopposite ((A s).pos o) ((Q (xz s)).pos o)))
    _ _ ?_ ?_
  · intro s o
    rw [← S.place_mul, mul_assoc, (hE W _ _).isIdempotentElem.eq]
  · refine (avgOver_prod_restrictedLinePointDist_le _ ?_ kindX kindZ i j).trans ?_
    · solve_by_elim [consistencyDefect_integrand_nonneg]
    · exact mul_le_mul_of_nonneg_left (lines.consistent first second hopposite) (by positivity)
  · simp only [hstar]
    refine (opFamilyDistSq_prod_restricted_points P kindX kindZ i j
      (fun v o => S.place second ((Q v).effect o)) (fun v o => S.place second (E W v o * E W.other v o)) _).le.trans ?_
    unfold opFamilyDistSq
    rw [avgOver_congr _ _ _ fun v => S.completedPair_norm_sq_sum points second W v]
    cases W
    · exact points.orderedXZ_dist_le second
    · exact points.orderedZX_dist_le second

end Restricted

end

end MIPStarRE.QPBT
