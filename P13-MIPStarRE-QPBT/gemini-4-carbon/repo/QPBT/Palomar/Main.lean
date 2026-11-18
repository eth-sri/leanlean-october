module

public import QPBT.Palomar.Definitions
public import QPBT.Test.Completeness
public import QPBT.Combining.DirectLowDegree
public import QPBT.Games.Sandwich.Support
public import QPBT.Test.Soundness
public import QPBT.Algebra.PauliTheorems
public import MIPStarRE.LDT.Basic.DistributionPMF

/-! # Compact Palomar bridges, completeness, low-degree soundness, and Pauli soundness -/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder

namespace MIPStarRE.QPBT.Palomar

open MIPStarRE.LDT hiding Measurement
open MIPStarRE MIPStarRE.Quantum

noncomputable section

theorem LowDegreeParams.is_admissible_size (P : LowDegreeParams) :
    QPBT.IsAdmissibleSize P.q := P.hq

theorem PauliParams.is_admissible_size (P : PauliParams) :
    QPBT.IsAdmissibleSize P.q := P.hq

def POVM.ofMeasurement {A I : Type*} [Fintype A] [Fintype I] [DecidableEq I]
    (M : Measurement A I) : POVM A I :=
  ⟨M.effect, fun a => Matrix.nonneg_iff_posSemidef.mp (M.pos a), M.sum_eq_one⟩

def POVM.toMeasurement {A I : Type*} [Fintype A] [Fintype I] [DecidableEq I]
    (M : POVM A I) : Measurement A I :=
  Measurement.ofSumEqOne M.effect
    (fun a => Matrix.nonneg_iff_posSemidef.mpr (M.pos a)) M.sum_eq_one

def POVM.relabel {A B I : Type*} [Fintype A] [Fintype B] [Fintype I] [DecidableEq I]
    (e : A ≃ B) (M : POVM A I) : POVM B I :=
  ⟨fun b => M.effect (e.symm b), fun b => M.pos (e.symm b),
    (Equiv.sum_comp e.symm M.effect).trans M.sum_eq_one⟩

def Strategy.toLibrary {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (H : QPBT.Game) (eX : X ≃ H.QuestionA) (eY : Y ≃ H.QuestionB)
    (eA : A ≃ H.AnswerA) (eB : B ≃ H.AnswerB) (S : Strategy X Y A B) :
    QPBT.Strategy H where
  ιA := S.ιA
  ιB := S.ιB
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  A x := (POVM.relabel eA (S.alice (eX.symm x))).toMeasurement
  B y := (POVM.relabel eB (S.bob (eY.symm y))).toMeasurement

theorem Strategy.toLibrary_value {X Y A B : Type} [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (H : QPBT.Game)
    (eX : X ≃ H.QuestionA) (eY : Y ≃ H.QuestionB)
    (eA : A ≃ H.AnswerA) (eB : B ≃ H.AnswerB) (S : Strategy X Y A B)
    (hμ : G.μ.map (eX.prodCongr eY) = H.μ.toPMF H.μ_prob)
    (hdec : ∀ x y a b, G.decide x y a b = H.decide (eX x) (eY y) (eA a) (eB b)) :
    (S.toLibrary H eX eY eA eB).value = S.value G := by
  unfold QPBT.Strategy.value Strategy.value
  rw [avgOver_eq_toPMF_realWeightedSum H.μ H.μ_prob, ← hμ, PMF.realWeightedSum_map]
  refine congrArg (PMF.realWeightedSum G.μ) (funext fun xy => ?_)
  simp only [toLibrary, QPBT.outcomeWeight, Strategy.outcomeWeight,
    QPBT.applyOperatorToState, QPBT.heteroKron,
    POVM.toMeasurement, POVM.relabel, Measurement.ofSumEqOne,
    Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]
  rw [← eA.sum_comp, ← Finset.sum_congr rfl fun _ _ => eB.sum_comp _]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hd : H.decide (eX xy.1) (eY xy.2) (eA a) (eB b) <;>
    simp [hdec, hd, eA.symm_apply_apply, eB.symm_apply_apply] <;> rfl

/-! ### Low-degree bridge and soundness -/

@[reducible] def LowDegreeParams.ofLdParams (P : QPBT.LdParams) : LowDegreeParams :=
  ⟨P.q, P.m, P.d, P.k, P.hm, P.hd, P.hk, P.hq, P.hdvd⟩

def lowDegreeTypeEquiv : LowDegreeType ≃ QPBT.LdType where
  toFun | .point => .point | .aline => .aline | .dline => .dline
  invFun | .point => .point | .aline => .aline | .dline => .dline
  left_inv t := by cases t <;> rfl
  right_inv t := by cases t <;> rfl

def lowDegreeQuestionEquiv (P : QPBT.LdParams) :
    LowDegreeQuestion (.ofLdParams P) (QPBT.ScalarQ P) ≃
      QPBT.LdQuestion P :=
  lowDegreeTypeEquiv.prodCongr (QPBT.ldSpaceSplit P).symm

theorem lowDegreeLineRep_eq_lineRepMap {K : Type} [Field K] [DecidableEq K]
    {m : ℕ} (u v : Fin m → K) :
    lowDegreeLineRep u v = QPBT.lineRepMap v u := by
  rw [QPBT.lineRepMap_apply_eq_explicitLineRep]
  simp only [lowDegreeLineRep, QPBT.explicitLineRep]
  split_ifs with hv; · rfl
  have hp_ne : v (lowDegreePivot v hv) ≠ 0 :=
    (Finset.mem_filter.mp (Finset.min'_mem (Finset.univ.filter fun j => v j ≠ 0) _)).2
  have hp_le (i : Fin m) (hi : v i ≠ 0) : lowDegreePivot v hv ≤ i :=
    Finset.min'_le _ i (by simp [hi])
  have hEq : lowDegreePivot v hv = QPBT.linePivotIndex v hv :=
    le_antisymm (hp_le _ (QPBT.linePivotIndex_ne_zero v hv))
      (le_of_not_gt fun hlt => hp_ne (QPBT.linePivotIndex_zero_before v hv _ hlt))
  rw [hEq]

theorem lowDegreeMap_equiv (P : QPBT.LdParams) (t : LowDegreeType)
    (z : LowDegreeSpace (.ofLdParams P) (QPBT.ScalarQ P)) :
    (QPBT.ldSpaceSplit P).symm
        (lowDegreeMap (.ofLdParams P) (QPBT.binaryRepresentation P.model) t z) =
      QPBT.ldCL P (lowDegreeTypeEquiv t) ((QPBT.ldSpaceSplit P).symm z) := by
  cases t with
  | point => rfl
  | aline | dline =>
      funext i; rcases i with (j | ⟨⟩) | j
      · exact congrFun (lowDegreeLineRep_eq_lineRepMap _ _) j
      · rfl
      · rfl

theorem lowDegreeQuestionPMF_map (P : QPBT.LdParams) :
    (lowDegreeQuestionPMF (.ofLdParams P) (QPBT.binaryRepresentation P.model)).map
        ((lowDegreeQuestionEquiv P).prodCongr (lowDegreeQuestionEquiv P)) =
      (QPBT.ldGame P).μ.toPMF (QPBT.ldGame P).μ_prob := by
  let eS := (lowDegreeTypeEquiv.prodCongr lowDegreeTypeEquiv).prodCongr
    (QPBT.ldSpaceSplit P).symm
  let f := fun z : (LowDegreeType × LowDegreeType) ×
      LowDegreeSpace (.ofLdParams P) (QPBT.ScalarQ P) =>
    ((z.1.1, lowDegreeMap (.ofLdParams P) (QPBT.binaryRepresentation P.model) z.1.1 z.2),
      (z.1.2, lowDegreeMap (.ofLdParams P) (QPBT.binaryRepresentation P.model) z.1.2 z.2))
  let g := fun z : (QPBT.LdType × QPBT.LdType) × QPBT.LdSpace P =>
    ((z.1.1, QPBT.ldCL P z.1.1 z.2), (z.1.2, QPBT.ldCL P z.1.2 z.2))
  have hf : ((lowDegreeQuestionEquiv P).prodCongr (lowDegreeQuestionEquiv P)) ∘ f = g ∘ eS :=
    funext fun z => Prod.ext (Prod.ext rfl (lowDegreeMap_equiv P z.1.1 z.2))
      (Prod.ext rfl (lowDegreeMap_equiv P z.1.2 z.2))
  change (PMF.map _ (PMF.map f _)) = _
  rw [PMF.map_comp, hf, ← PMF.map_comp, PMF.uniformOfFintype_map_equiv eS, ← uniformDistribution_toPMF]
  exact (Distribution.toPMF_map _ (uniformDistribution_isProbability _) g).symm

set_option maxHeartbeats 800000 in
-- Checks all 81 type/answer constructor combinations explicitly.
theorem lowDegreeWin_equiv (P : QPBT.LdParams)
    (x y : LowDegreeQuestion (.ofLdParams P) (QPBT.ScalarQ P))
    (a b : LowDegreeAnswer (.ofLdParams P) (QPBT.ScalarQ P)) :
    lowDegreeWin (.ofLdParams P) (QPBT.binaryRepresentation P.model) x y a b =
      QPBT.ldWinPredicate P (lowDegreeQuestionEquiv P x)
        (lowDegreeQuestionEquiv P y) ((QPBT.ldAnswerEquiv P).symm a)
        ((QPBT.ldAnswerEquiv P).symm b) := by
  rcases x with ⟨tA, xA⟩; rcases y with ⟨tB, xB⟩
  rcases a with a | (a | a) <;> rcases b with b | (b | b) <;>
    cases tA <;> cases tB <;>
    simp [lowDegreeWin, validLowDegreeAnswer, QPBT.ldWinPredicate,
      QPBT.validLdAnswer, lowDegreeQuestionEquiv,
      QPBT.ldAnswerEquiv, lowDegreeTypeEquiv,
      QPBT.alinePointCondition, QPBT.dlinePointCondition,
      QPBT.coordinateDirection, lowDegreeEval, QPBT.evalCoefficient,
      lowDegreeChiIndex, QPBT.chiIndex] <;> rfl

theorem consistencyDefect_toPMF {X O I J : Type*}
    [Fintype X] [DecidableEq X] [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (μ : Distribution X) (hμ : μ.IsProbability)
    (A : X → O → Matrix I I ℂ) (B : X → O → Matrix J J ℂ)
    (ψ : EuclideanSpace ℂ (I × J)) :
    consistencyDefect (μ.toPMF hμ) A B ψ =
      QPBT.consistencyDefect μ
        (fun x a => QPBT.heteroKron (A x a) 1)
        (fun x a => QPBT.heteroKron 1 (B x a)) ψ := by
  unfold consistencyDefect QPBT.consistencyDefect
  rw [avgOver_eq_toPMF_realWeightedSum μ hμ]
  simp only [PMF.realWeightedSum, smul_eq_mul, QPBT.heteroKron]

theorem relabel_postprocess_effect {A B C I : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    [Fintype I] [DecidableEq I] (e : A ≃ B) (M : POVM A I) (f : B → C) (c : C) :
    (((POVM.relabel e M).toMeasurement).postprocess f).effect c =
      postprocessEffect M (fun a => f (e a)) c := by
  change (∑ b ∈ Finset.univ.filter (fun b => f b = c), M.effect (e.symm b)) = _
  simp only [postprocessEffect, Finset.sum_filter]
  rw [← Equiv.sum_comp e.symm (fun a => if f (e a) = c then M.effect a else 0)]
  simp

theorem lowDegreeQuestionEquiv_symm_point (L : QPBT.LdParams)
    (u : Fin L.m → QPBT.ScalarQ L) :
    (lowDegreeQuestionEquiv L).symm (QPBT.ldPointQuestionOf L u) =
      lowDegreePointQuestion (.ofLdParams L) u := rfl

set_option maxHeartbeats 800000 in
-- Seed-fiber compression and Schwartz--Zippel transport for simultaneous low-degree soundness.
theorem ld_soundness_lib :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (L : QPBT.LdParams) (ε : ℝ), 0 < ε →
        ∀ S : QPBT.Strategy (QPBT.ldGame L), S.IsProjective → 1 - ε ≤ S.value →
          ∃ GA : QPBT.PolyMeasTuple L S.ιA, ∃ GB : QPBT.PolyMeasTuple L S.ιB,
            QPBT.consistencyDefect (uniformDistribution (Fin L.m → QPBT.ScalarQ L))
                (fun u o => QPBT.heteroKron
                  (((S.A (QPBT.ldPointQuestionOf L u)).postprocess
                    (QPBT.ldPointValuesOrZero L)).effect o) 1)
                (fun u o => QPBT.heteroKron 1 ((GB.postprocess (QPBT.evalPolyTupleAt u)).effect o))
                S.ψ ≤ QPBT.deltaLd a b ε L.q L.m L.d L.k ∧
            QPBT.consistencyDefect (uniformDistribution (Fin L.m → QPBT.ScalarQ L))
                (fun u o => QPBT.heteroKron ((GA.postprocess (QPBT.evalPolyTupleAt u)).effect o) 1)
                (fun u o => QPBT.heteroKron 1
                  (((S.B (QPBT.ldPointQuestionOf L u)).postprocess
                    (QPBT.ldPointValuesOrZero L)).effect o))
                S.ψ ≤ QPBT.deltaLd a b ε L.q L.m L.d L.k ∧
            QPBT.consistencyDefect (uniformDistribution Unit)
                (fun _ g => QPBT.heteroKron (GA.effect g) 1)
                (fun _ g => QPBT.heteroKron 1 (GB.effect g))
                S.ψ ≤ QPBT.deltaLd a b ε L.q L.m L.d L.k := by
  classical
  obtain ⟨a, b, ha, hb, hb1, hs⟩ := QPBT.exists_direct_ld_soundness
  refine ⟨10 * a, b / 2, by linarith, by positivity, by linarith, fun L ε hε S hS hwin => ?_⟩
  let D := L.toDirectLdParams
  let E := QPBT.deltaLd a b ε L.q L.m L.d L.k
  let F := QPBT.deltaLd (10 * a) (b / 2) ε L.q L.m L.d L.k
  obtain ⟨GA₀, GB₀, h1, h2, _⟩ := hs L.toDirectLdParams ε hε (QPBT.ldStrategyToDirect L S)
    (QPBT.ldStrategyToDirect_isProjective L S hS)
    (by simpa only [QPBT.ldStrategyToDirect_value_eq] using hwin)
  let GA := QPBT.seedFiberCompressPolyMeasTuple L GA₀
  let GB := QPBT.seedFiberCompressPolyMeasTuple L GB₀
  have c1 : QPBT.consistencyDefect (uniformDistribution (Fin L.m → QPBT.ScalarQ L))
      (fun u o => QPBT.heteroKron
        (((S.A (QPBT.ldPointQuestionOf L u)).postprocess (QPBT.ldPointValuesOrZero L)).effect o) 1)
      (fun u o => QPBT.heteroKron 1 ((GB.postprocess (QPBT.evalPolyTupleAt u)).effect o)) S.ψ ≤ E := by
    rw [show GB = QPBT.seedFiberCompressPolyMeasTuple L GB₀ from rfl,
      ← QPBT.ldStrategyToDirect_pointPolynomial_compression L S GB₀]; exact h1
  have c2 : QPBT.consistencyDefect (uniformDistribution (Fin L.m → QPBT.ScalarQ L))
      (fun u o => QPBT.heteroKron ((GA.postprocess (QPBT.evalPolyTupleAt u)).effect o) 1)
      (fun u o => QPBT.heteroKron 1
        (((S.B (QPBT.ldPointQuestionOf L u)).postprocess (QPBT.ldPointValuesOrZero L)).effect o)) S.ψ ≤ E := by
    rw [show GA = QPBT.seedFiberCompressPolyMeasTuple L GA₀ from rfl,
      ← QPBT.ldStrategyToDirect_polynomialPoint_compression L S GA₀]; exact h2
  have c3 := QPBT.ldPointPair_consistencyDefect_le L S hS ε hwin
  have ctrans := QPBT.consistencyDefect_trans_le (uniformDistribution (Fin L.m → QPBT.ScalarQ L))
    (fun u => QPBT.DistanceCalculus.leftPlacedMeasurement (GA.postprocess (QPBT.evalPolyTupleAt u)))
    (fun u => QPBT.DistanceCalculus.rightPlacedMeasurement
      ((S.B (QPBT.ldPointQuestionOf L u)).postprocess (QPBT.ldPointValuesOrZero L)))
    (fun u => QPBT.DistanceCalculus.leftPlacedMeasurement
      ((S.A (QPBT.ldPointQuestionOf L u)).postprocess (QPBT.ldPointValuesOrZero L)))
    (fun u => QPBT.DistanceCalculus.rightPlacedMeasurement (GB.postprocess (QPBT.evalPolyTupleAt u)))
    S.ψ E (9 * ε) E (uniformDistribution_isProbability _) S.ψ_norm c2 c3 c1
  have ccode : QPBT.consistencyDefect (uniformDistribution Unit)
      (fun _ g => QPBT.heteroKron (GA.effect g) 1)
      (fun _ g => QPBT.heteroKron 1 (GB.effect g)) S.ψ ≤
      E + 2 * Real.sqrt (9 * ε + E) + (L.m : ℝ) * L.d / L.q := by
    have hstep := QPBT.SandwichProduct.consistencyDefect_codewords_le_evaluated_add
      (uniformDistribution Unit) (fun _ => GA) (fun _ => GB) S.ψ
      (fun g u => QPBT.evalPolyTupleAt u g) ((L.m : ℝ) * L.d / L.q)
      (uniformDistribution_isProbability _) S.ψ_norm (by positivity) fun g g' hne => by
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
        refine (avgOver_mono _ _ _ fun u => ?_).trans
          (QPBT.directPolynomialAgreement_avg_le_mdq D (g i) (g' i) hi)
        split_ifs with h h'
        · exact le_rfl
        · exact False.elim (h' (congrFun h i))
        · norm_num
        · exact le_rfl
    have hprod (A B : Unit × (Fin L.m → QPBT.ScalarQ L) →
        (Fin L.k → QPBT.ScalarQ L) → Op (S.ιA × S.ιB)) :
        QPBT.consistencyDefect (Distribution.prod (uniformDistribution Unit)
          (uniformDistribution (Fin L.m → QPBT.ScalarQ L))) A B S.ψ =
        QPBT.consistencyDefect (uniformDistribution (Fin L.m → QPBT.ScalarQ L))
          (fun u => A ((), u)) (fun u => B ((), u)) S.ψ := by
      unfold QPBT.consistencyDefect
      rw [QPBT.SandwichProduct.avgOver_distribution_prod, avgOver_uniform_eq_inv_card_mul_sum]
      simp
    rw [hprod] at hstep; exact hstep.trans (add_le_add ctrans le_rfl)
  have hsqrt : 10 * Real.sqrt E ≤ F := QPBT.ten_sqrt_deltaLd_le D ha hε.le
  have hEnn : 0 ≤ E := by dsimp [E, QPBT.deltaLd]; positivity
  have hbound {X α : Type} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype α] [DecidableEq α]
      (A : X → Measurement α S.ιA) (B : X → Measurement α S.ιB)
      (hc : QPBT.consistencyDefect (uniformDistribution X)
        (fun x o => QPBT.heteroKron ((A x).effect o) 1)
        (fun x o => QPBT.heteroKron 1 ((B x).effect o)) S.ψ ≤
        E + 2 * Real.sqrt (9 * ε + E) + (L.m : ℝ) * L.d / L.q) :
      QPBT.consistencyDefect (uniformDistribution X)
        (fun x o => QPBT.heteroKron ((A x).effect o) 1)
        (fun x o => QPBT.heteroKron 1 ((B x).effect o)) S.ψ ≤ F := by
    have hone := QPBT.consistencyDefect_heteroKron_le_one (uniformDistribution X)
      (uniformDistribution_isProbability _) A B S.ψ S.ψ_norm
    by_cases hε1 : ε ≤ 1
    · by_cases hE1 : E ≤ 1
      · obtain ⟨he, hm⟩ := QPBT.error_and_collision_le_deltaLd D ha hb1 hε hε1
        change ε ≤ E at he; change (L.m : ℝ) * L.d / L.q ≤ E at hm
        have hEs := QPBT.le_sqrt_of_le_of_le_one le_rfl hE1
        have hrt : Real.sqrt (9 * ε + E) ≤ 4 * Real.sqrt E :=
          Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [Real.sq_sqrt hEnn]⟩
        exact hc.trans (by linarith)
      · exact hone.trans (by linarith [show 1 ≤ Real.sqrt E by simpa using Real.sqrt_le_sqrt (not_le.mp hE1).le])
    · exact hone.trans (QPBT.one_le_deltaLd_of_one_le_error (by linarith) (by positivity)
        (not_le.mp hε1).le L.hm L.hd L.hk)
  have : 0 ≤ 2 * Real.sqrt (9 * ε + E) + (L.m : ℝ) * L.d / L.q := by positivity
  exact ⟨GA, GB,
    hbound (fun u => (S.A (QPBT.ldPointQuestionOf L u)).postprocess (QPBT.ldPointValuesOrZero L))
      (fun u => GB.postprocess (QPBT.evalPolyTupleAt u)) (c1.trans (by linarith)),
    hbound (fun u => GA.postprocess (QPBT.evalPolyTupleAt u))
      (fun u => (S.B (QPBT.ldPointQuestionOf L u)).postprocess (QPBT.ldPointValuesOrZero L))
      (c2.trans (by linarith)),
    hbound (fun _ : Unit => GA) (fun _ : Unit => GB) ccode⟩

theorem exists_ld_soundness :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (P : LowDegreeParams) (ε : ℝ), 0 < ε →
        ∀ S : LowDegreeStrategy P (QPBT.fixedFieldModel P.q
            P.is_admissible_size).K,
          S.IsProjective →
          1 - ε ≤ S.value (lowDegreeGame P
            (QPBT.binaryRepresentation
              (QPBT.fixedFieldModel P.q
                P.is_admissible_size))) →
          ∃ GA : LowDegreePolynomialPOVM P
              (QPBT.fixedFieldModel P.q
                P.is_admissible_size).K S.ιA,
            ∃ GB : LowDegreePolynomialPOVM P
                (QPBT.fixedFieldModel P.q
                  P.is_admissible_size).K S.ιB,
              ldPointPolynomialDefect P S GB ≤
                  deltaLd a b ε P.q P.m P.d P.k ∧
                ldPolynomialPointDefect P S GA ≤
                  deltaLd a b ε P.q P.m P.d P.k ∧
                ldPolynomialPolynomialDefect P S GA GB ≤
                  deltaLd a b ε P.q P.m P.d P.k := by
  obtain ⟨a, b, ha, hb, hb1, hsound⟩ := ld_soundness_lib
  refine ⟨a, b, ha, hb, hb1, ?_⟩
  rintro ⟨q, m, d, k, hm, hd, hk, hq, hdvd⟩ ε hε S hproj hval
  let L : QPBT.LdParams := ⟨q, m, d, k, hm, hd, hk, hq, hdvd⟩
  let eQ := lowDegreeQuestionEquiv L
  let eA := (QPBT.ldAnswerEquiv L).symm
  let S' := S.toLibrary (QPBT.ldGame L) eQ eQ eA eA
  have hval' : 1 - ε ≤ S'.value :=
    hval.trans_eq (Strategy.toLibrary_value
      (lowDegreeGame (.ofLdParams L) (QPBT.binaryRepresentation L.model))
      (QPBT.ldGame L) eQ eQ eA eA S
      (lowDegreeQuestionPMF_map L) (lowDegreeWin_equiv L)).symm
  obtain ⟨GA, GB, h1, h2, h3⟩ := hsound L ε hε S'
    ⟨fun x c => hproj.1 (eQ.symm x) (eA.symm c), fun y c => hproj.2 (eQ.symm y) (eA.symm c)⟩ hval'
  have hpt (c : LowDegreeAnswer (.ofLdParams L) (QPBT.ScalarQ L)) :
      QPBT.ldPointValuesOrZero L (eA c) = lowDegreePointValuesOrZero c := by
    rcases c with c | c | c <;> rfl
  have h_eff {I : Type} [Fintype I] [DecidableEq I]
      (M : POVM (LowDegreeAnswer (.ofLdParams L) (QPBT.ScalarQ L)) I) (o) :
      (((POVM.relabel eA M).toMeasurement).postprocess (QPBT.ldPointValuesOrZero L)).effect o =
        postprocessEffect M lowDegreePointValuesOrZero o := by
    rw [relabel_postprocess_effect]
    exact Finset.sum_congr (by ext c; simp [hpt]) fun _ _ => rfl
  refine ⟨POVM.ofMeasurement GA, POVM.ofMeasurement GB, ?_, ?_, ?_⟩
  · refine (le_of_eq ?_).trans h1
    unfold ldPointPolynomialDefect
    rw [← uniformDistribution_toPMF, consistencyDefect_toPMF]
    refine QPBT.consistencyDefect_congr _ _ _ _ _ S.ψ (fun u o => ?_) fun _ _ => rfl
    exact congrArg (QPBT.heteroKron · 1) ((congrArg (fun q =>
      (((POVM.relabel eA (S.alice q)).toMeasurement).postprocess
        (QPBT.ldPointValuesOrZero L)).effect o) (lowDegreeQuestionEquiv_symm_point L u)).trans
      (h_eff _ o)).symm
  · refine (le_of_eq ?_).trans h2
    unfold ldPolynomialPointDefect
    rw [← uniformDistribution_toPMF, consistencyDefect_toPMF]
    refine QPBT.consistencyDefect_congr _ _ _ _ _ S.ψ (fun _ _ => rfl) fun u o => ?_
    exact congrArg (QPBT.heteroKron 1 ·) ((congrArg (fun q =>
      (((POVM.relabel eA (S.bob q)).toMeasurement).postprocess
        (QPBT.ldPointValuesOrZero L)).effect o) (lowDegreeQuestionEquiv_symm_point L u)).trans
      (h_eff _ o)).symm
  · refine (le_of_eq ?_).trans h3
    unfold ldPolynomialPolynomialDefect
    rw [← uniformDistribution_toPMF, consistencyDefect_toPMF]
    rfl

/-! ### Pauli bridge, completeness, qudit soundness, and qubit soundness -/

@[reducible] def PauliParams.ofAdmissibleParams (P : QPBT.AdmissibleParams) :
    PauliParams := ⟨P.q, P.m, P.d, P.one_le_m, P.hd, P.hq, P.hdvd⟩

local instance compactPauliQuestionDecidableEq (P : QPBT.AdmissibleParams) :
    DecidableEq (PauliQuestion (.ofAdmissibleParams P) (QPBT.PauliScalar P)) :=
  instDecidableEqPauliQuestion

def pauliKindEquiv : PauliKind ≃ QPBT.PauliKind where
  toFun | .X => .X | .Z => .Z
  invFun | .X => .X | .Z => .Z
  left_inv W := by cases W <;> rfl
  right_inv W := by cases W <;> rfl

def pauliTypeEquiv : PauliType ≃ QPBT.PauliType where
  toFun
    | .point W => .point (pauliKindEquiv W)
    | .aline W => .aline (pauliKindEquiv W)
    | .dline W => .dline (pauliKindEquiv W)
    | .pauli W => .pauli (pauliKindEquiv W)
    | .pairW W => .pairW (pauliKindEquiv W)
    | .pair => .pair
    | .constraint i => .ms (.constraint i)
    | .variable j => .ms (.var j)
  invFun
    | .point W => .point (pauliKindEquiv.symm W)
    | .aline W => .aline (pauliKindEquiv.symm W)
    | .dline W => .dline (pauliKindEquiv.symm W)
    | .pauli W => .pauli (pauliKindEquiv.symm W)
    | .pairW W => .pairW (pauliKindEquiv.symm W)
    | .pair => .pair
    | .ms (.constraint i) => .constraint i
    | .ms (.var j) => .variable j
  left_inv
    | .point W | .aline W | .dline W | .pauli W | .pairW W => by cases W <;> rfl
    | .pair | .constraint _ | .variable _ => rfl
  right_inv
    | .point W | .aline W | .dline W | .pauli W | .pairW W => by cases W <;> rfl
    | .pair => rfl
    | .ms t => by cases t <;> rfl

def pauliSpaceEquiv (P : QPBT.AdmissibleParams) :
    PauliSpace (.ofAdmissibleParams P) (QPBT.PauliScalar P) ≃
      QPBT.PauliSpace P where
  toFun z
    | .inl (.inl (.inl (.inl (.inl i)))) => z.1 i
    | .inl (.inl (.inl (.inl (.inr i)))) => z.2.1 i
    | .inl (.inl (.inl (.inr _))) => z.2.2.1
    | .inl (.inl (.inr i)) => z.2.2.2.1 i
    | .inl (.inr _) => z.2.2.2.2.1
    | .inr _ => z.2.2.2.2.2
  invFun z := (QPBT.pauliXBlock z, QPBT.pauliZBlock z,
    QPBT.pauliScalarBlock z, QPBT.pauliDirectionBlock z,
    QPBT.pauliRXBlock z, QPBT.pauliRZBlock z)
  left_inv z := by rcases z with ⟨_, _, _, _, _, _⟩; rfl
  right_inv z := by funext i; rcases i with ((((i | i) | _) | i) | _) | _ <;> rfl

def pauliQuestionEquiv (P : QPBT.AdmissibleParams) :
    PauliQuestion (.ofAdmissibleParams P) (QPBT.PauliScalar P) ≃
      QPBT.PauliQuestion P :=
  pauliTypeEquiv.prodCongr (pauliSpaceEquiv P)

def pauliAnswerEquivCompact (P : QPBT.AdmissibleParams) :
    PauliAnswer (.ofAdmissibleParams P) (QPBT.PauliScalar P) ≃
      QPBT.PauliAnswer P where
  toFun
    | .value a => .value a | .alinePoly a => .alinePoly a | .dlinePoly a => .dlinePoly a
    | .pairBits a => .pairBits a | .bit a => .bit a | .msTriple a => .msTriple a
    | .pauliOutcome a => .pauliOutcome a
  invFun
    | .value a => .value a | .alinePoly a => .alinePoly a | .dlinePoly a => .dlinePoly a
    | .pairBits a => .pairBits a | .bit a => .bit a | .msTriple a => .msTriple a
    | .pauliOutcome a => .pauliOutcome a
  left_inv a := by cases a <;> rfl
  right_inv a := by cases a <;> rfl

theorem pauliEdges_mem_equiv (e : PauliType × PauliType) :
    Sym2.mk e.1 e.2 ∈ pauliEdges ↔
      Sym2.mk (pauliTypeEquiv e.1) (pauliTypeEquiv e.2) ∈ QPBT.pauliEdges := by
  have hms : ((Finset.univ : Finset (QPBT.MsType × QPBT.MsType)).filter
      (fun xy => Sym2.mk xy.1 xy.2 ∈ QPBT.msEdges) |>.image
      (fun xy => Sym2.mk (QPBT.PauliType.ms xy.1)
        (QPBT.PauliType.ms xy.2))) =
    (Finset.univ : Finset (Fin 6 × Fin 3)).image (fun ij =>
      Sym2.mk (.ms (.constraint ij.1))
        (.ms (.var (QPBT.msConstraintVars ij.1 ij.2)))) := by
    ext s; simp only [QPBT.msEdges, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and, Prod.exists, Sym2.eq_iff]
    exact ⟨fun ⟨_, _, ⟨i, j, h⟩, hs⟩ => h.elim
        (fun ⟨rfl, rfl⟩ => ⟨i, j, hs⟩) (fun ⟨rfl, rfl⟩ => ⟨i, j, Sym2.eq_swap.trans hs⟩),
      fun ⟨i, j, hs⟩ => ⟨_, _, ⟨i, j, Or.inl ⟨rfl, rfl⟩⟩, hs⟩⟩
  have hfwd {s : Sym2 PauliType} (h : s ∈ pauliEdges) :
      Sym2.map pauliTypeEquiv s ∈ QPBT.pauliEdges := by
    unfold QPBT.pauliEdges; rw [hms]
    simp only [pauliEdges, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      true_and, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with ((((⟨t, rfl⟩ | ((⟨W, rfl⟩ | ⟨W, rfl⟩) | ⟨W, rfl⟩)) |
      (⟨W, rfl⟩ | rfl | rfl)) | ⟨W, rfl⟩) | ⟨⟨i, j⟩, rfl⟩) <;>
      simp [pauliTypeEquiv, pauliKindEquiv, magicVariable, QPBT.msConstraintVars]
  have hbwd {s : Sym2 QPBT.PauliType} (h : s ∈ QPBT.pauliEdges) :
      Sym2.map pauliTypeEquiv.symm s ∈ pauliEdges := by
    unfold QPBT.pauliEdges at h; rw [hms] at h
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      true_and, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with ((((⟨t, rfl⟩ | ((⟨W, rfl⟩ | ⟨W, rfl⟩) | ⟨W, rfl⟩)) |
      (⟨W, rfl⟩ | rfl | rfl)) | ⟨W, rfl⟩) | ⟨⟨i, j⟩, rfl⟩) <;>
      simp [pauliEdges, pauliTypeEquiv, pauliKindEquiv, magicVariable, QPBT.msConstraintVars]
  exact ⟨fun h => by simpa using hfwd h, fun h => by simpa using hbwd h⟩

theorem pauliMap_equiv (P : QPBT.AdmissibleParams) (t : PauliType)
    (z : PauliSpace (.ofAdmissibleParams P) (QPBT.PauliScalar P)) :
    pauliSpaceEquiv P (pauliMap (.ofAdmissibleParams P)
        (QPBT.binaryRepresentation P.model) t z) =
      QPBT.pauliCL P (pauliTypeEquiv t) (pauliSpaceEquiv P z) := by
  have hemb (W : PauliKind) (tL : LowDegreeType) :
      pauliSpaceEquiv P (pauliEmbedLowDegree W
        (lowDegreeMap (PauliParams.ofAdmissibleParams P).toLowDegreeParams
          (QPBT.binaryRepresentation P.model) tL (pauliLowDegreeSpace W z))) =
      QPBT.embedLd P (pauliKindEquiv W)
        (QPBT.ldCL P.toLdParams (lowDegreeTypeEquiv tL)
          (QPBT.pauliToLd P (pauliKindEquiv W) (pauliSpaceEquiv P z))) := by
    have h1 : (QPBT.ldSpaceSplit P.toLdParams).symm (pauliLowDegreeSpace W z) =
        QPBT.pauliToLd P (pauliKindEquiv W) (pauliSpaceEquiv P z) := by
      funext i; rcases i with (i | _) | i <;> cases W <;> rfl
    have h2 (u) : pauliSpaceEquiv P (pauliEmbedLowDegree W u) =
        QPBT.embedLd P (pauliKindEquiv W)
          ((QPBT.ldSpaceSplit P.toLdParams).symm u) := by
      funext i; rcases i with ((((i | i) | _) | i) | _) | _ <;> cases W <;> rfl
    rw [h2]; congr 1
    exact (lowDegreeMap_equiv P.toLdParams tL (pauliLowDegreeSpace W z)).trans (by rw [h1])
  cases t with
  | point W => exact hemb W .point
  | aline W => exact hemb W .aline
  | dline W => exact hemb W .dline
  | pauli _ | pairW _ | pair | constraint _ | _ =>
      funext i; rcases i with ((((i | i) | _) | i) | _) | _ <;> rfl

theorem pauliQuestionPMF_map (P : QPBT.AdmissibleParams) :
    (pauliQuestionPMF (.ofAdmissibleParams P) (QPBT.binaryRepresentation P.model)).map
        ((pauliQuestionEquiv P).prodCongr (pauliQuestionEquiv P)) =
      (QPBT.pauliBasisTest P).μ.toPMF (QPBT.pauliBasisTest P).μ_prob := by
  classical
  let _ : Nonempty QPBT.PauliEdge := QPBT.pauliEdge_nonempty
  let eE : PauliEdge ≃ QPBT.PauliEdge :=
    (pauliTypeEquiv.prodCongr pauliTypeEquiv).subtypeEquiv pauliEdges_mem_equiv
  let eS := eE.prodCongr (pauliSpaceEquiv P)
  let f := fun s : PauliEdge × PauliSpace (.ofAdmissibleParams P) (QPBT.PauliScalar P) =>
    ((s.1.1.1, pauliMap (.ofAdmissibleParams P) (QPBT.binaryRepresentation P.model) s.1.1.1 s.2),
      (s.1.1.2, pauliMap (.ofAdmissibleParams P) (QPBT.binaryRepresentation P.model) s.1.1.2 s.2))
  let g := fun s : QPBT.PauliEdge × QPBT.PauliSpace P =>
    ((s.1.1.1, QPBT.pauliCL P s.1.1.1 s.2),
      (s.1.1.2, QPBT.pauliCL P s.1.1.2 s.2))
  have hf : ((pauliQuestionEquiv P).prodCongr (pauliQuestionEquiv P)) ∘ f = g ∘ eS :=
    funext fun s => Prod.ext (Prod.ext rfl (pauliMap_equiv P s.1.1.1 s.2))
      (Prod.ext rfl (pauliMap_equiv P s.1.1.2 s.2))
  change (PMF.map _ (PMF.map f _)) = _
  rw [PMF.map_comp, hf, ← PMF.map_comp, PMF.uniformOfFintype_map_equiv eS, ← uniformDistribution_toPMF]
  exact (Distribution.toPMF_map _ (uniformDistribution_isProbability _) g).symm

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Checks all well-formed question/answer constructor pairs explicitly.
theorem pauliWin_equiv (P : QPBT.AdmissibleParams)
    (x y : PauliQuestion (.ofAdmissibleParams P) (QPBT.PauliScalar P))
    (a b : PauliAnswer (.ofAdmissibleParams P) (QPBT.PauliScalar P)) :
    pauliWin (.ofAdmissibleParams P)
        (QPBT.binaryRepresentation P.model)
        (QPBT.fixedBinTrace P.model) x y a b =
      QPBT.pauliWinPredicate P (pauliQuestionEquiv P x)
        (pauliQuestionEquiv P y) (pauliAnswerEquivCompact P a)
        (pauliAnswerEquivCompact P b) := by
  have hind (u : Fin P.m → QPBT.PauliScalar P) :
      pauliIndicator (P := .ofAdmissibleParams P) u = QPBT.indicatorVec u :=
    funext fun y => (QPBT.indicatorVec_apply_eq_prod u y).symm
  have henc (h : (Fin P.m → Bool) → QPBT.PauliScalar P) (u) :
      pauliEncoded (P := .ofAdmissibleParams P) h u = QPBT.lowDegreeEnc h u := by
    rw [QPBT.lowDegreeEnc_eq_dotProduct, pauliEncoded, hind]
  have hgam (z : PauliSpace (.ofAdmissibleParams P) (QPBT.PauliScalar P)) :
      pauliGamma (QPBT.fixedBinTrace P.model) z =
        QPBT.pauliPairGamma P (pauliSpaceEquiv P z) := by
    simp only [pauliGamma, QPBT.pauliPairGamma, QPBT.gammaValue, hind]; rfl
  have hs (z) : QPBT.pauliScalarBlock (pauliSpaceEquiv P z) = z.2.2.1 := rfl
  have hd (z) : QPBT.pauliDirectionBlock (pauliSpaceEquiv P z) = z.2.2.2.1 := rfl
  have hrx (z) : QPBT.pauliRXBlock (pauliSpaceEquiv P z) = z.2.2.2.2.1 := rfl
  have hrz (z) : QPBT.pauliRZBlock (pauliSpaceEquiv P z) = z.2.2.2.2.2 := rfl
  have hptX (z) : QPBT.pauliPointBlock .X (pauliSpaceEquiv P z) = pauliPointBlock .X z := rfl
  have hptZ (z) : QPBT.pauliPointBlock .Z (pauliSpaceEquiv P z) = pauliPointBlock .Z z := rfl
  have hval (t : PauliType) (c : PauliAnswer (.ofAdmissibleParams P) _) :
      validPauliAnswer t c =
        QPBT.validPauliAnswer (pauliTypeEquiv t) (pauliAnswerEquivCompact P c) := by
    cases t <;> cases c <;> simp [validPauliAnswer, QPBT.validPauliAnswer,
      pauliTypeEquiv, pauliAnswerEquivCompact]
  rcases x with ⟨tA, xA⟩; rcases y with ⟨tB, xB⟩
  unfold pauliWin QPBT.pauliWinPredicate
  simp only [pauliQuestionEquiv, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, ← hval]
  by_cases hv : (validPauliAnswer tA a && validPauliAnswer tB b) = true
  · rw [ite_eq_left_iff.mpr fun h => absurd hv h, ite_eq_left_iff.mpr fun h => absurd hv h]
    by_cases ht : tA = tB
    · have ht' : pauliTypeEquiv tA = pauliTypeEquiv tB := congrArg _ ht
      rw [ite_eq_left_iff.mpr fun h => absurd ht h, ite_eq_left_iff.mpr fun h => absurd ht' h]
      simp [(pauliAnswerEquivCompact P).injective.eq_iff]
    · have ht' : pauliTypeEquiv tA ≠ pauliTypeEquiv tB := fun h => ht (pauliTypeEquiv.injective h)
      simp only [ht, ht', ↓reduceIte]
      obtain ⟨hvA, hvB⟩ := Bool.and_eq_true_iff.mp hv
      rcases tA with (_ | _) | (_ | _) | (_ | _) | (_ | _) | (_ | _) | _ | i | j <;>
        rcases a with uA | fA | gA | bitsA | bitA | tripleA | outcomeA <;>
        (try exact Bool.noConfusion hvA) <;>
        rcases tB with (_ | _) | (_ | _) | (_ | _) | (_ | _) | (_ | _) | _ | i' | j' <;>
        rcases b with uB | fB | gB | bitsB | bitB | tripleB | outcomeB <;>
        (try exact Bool.noConfusion hvB) <;>
        simp [pauliTypeEquiv, pauliKindEquiv, pauliAnswerEquivCompact,
          QPBT.pauliAlinePointCondition, QPBT.pauliDlinePointCondition,
          QPBT.pauliPointPauliCondition, QPBT.pauliPairCondition,
          QPBT.pauliPointPairCondition, QPBT.pauliPointVariableCondition,
          QPBT.msWinPredicate, QPBT.coordinateDirection,
          lowDegreeEval, QPBT.evalCoefficient, magicVariable,
          QPBT.msConstraintVars, magicParity, QPBT.msParity,
          pauliChiIndex, QPBT.chiIndex, henc, hgam, hs, hd, hrx, hrz, hptX, hptZ] <;>
        (try (split_ifs <;> simp)) <;>
        (try exact decide_eq_decide.mpr ⟨fun h => h, fun h => h⟩)
  · simp [hv]

def pauliStrategyToLibrary (P : QPBT.AdmissibleParams)
    (S : PauliStrategy (.ofAdmissibleParams P) (QPBT.PauliScalar P)) :
    QPBT.Strategy (QPBT.pauliBasisTest P) :=
  S.toLibrary (QPBT.pauliBasisTest P)
    (pauliQuestionEquiv P) (pauliQuestionEquiv P)
    (pauliAnswerEquivCompact P) (pauliAnswerEquivCompact P)

theorem pauliStrategyToLibrary_value (P : QPBT.AdmissibleParams)
    (S : PauliStrategy (.ofAdmissibleParams P) (QPBT.PauliScalar P)) :
    (pauliStrategyToLibrary P S).value =
      S.value (pauliGame (.ofAdmissibleParams P)
        (QPBT.binaryRepresentation P.model)
        (QPBT.fixedBinTrace P.model)) :=
  Strategy.toLibrary_value _ _ _ _ _ _ S
    (by simpa [pauliGame] using pauliQuestionPMF_map P)
    (fun x y a b => by simpa [pauliGame] using pauliWin_equiv P x y a b)

theorem exists_spcc_value_one (P : PauliParams) :
    ∃ S : SymmetricPauliStrategy P
        (QPBT.fixedFieldModel P.q P.is_admissible_size).K,
      S.IsPauliSPCC P
          (QPBT.binaryRepresentation
            (QPBT.fixedFieldModel P.q P.is_admissible_size)) ∧
      S.toStrategy.value
          (pauliGame P
            (QPBT.binaryRepresentation
              (QPBT.fixedFieldModel P.q P.is_admissible_size))
            (QPBT.fixedBinTrace
              (QPBT.fixedFieldModel P.q P.is_admissible_size))) = 1 := by
  classical
  rcases P with ⟨q, m, d, hm, hd, hq, hdvd⟩
  let Q : QPBT.AdmissibleParams := ⟨q, m, d, hd, hq, hdvd⟩
  obtain ⟨T, ⟨hproj, hcons, hcomm⟩, hval⟩ := QPBT.exists_spcc_value_one Q
  let eQ := pauliQuestionEquiv Q
  let eA := pauliAnswerEquivCompact Q
  let S : SymmetricPauliStrategy (.ofAdmissibleParams Q) (QPBT.PauliScalar Q) :=
    ⟨T.ι, T.ψ, T.ψ_norm, T.ψ_swap, fun x => POVM.relabel eA.symm (POVM.ofMeasurement (T.M (eQ x)))⟩
  refine ⟨S, ⟨fun x a => hproj (eQ x) (eA a), fun x a => hcons (eQ x) (eA a),
    fun x y hxy a b => ?_⟩, ?_⟩
  · have hpos : 0 < ((QPBT.pauliBasisTest Q).μ.toPMF
        (QPBT.pauliBasisTest Q).μ_prob) (eQ x, eQ y) := by
      rw [← pauliQuestionPMF_map Q]
      have hmap : ((pauliQuestionPMF (.ofAdmissibleParams Q)
          (QPBT.binaryRepresentation Q.model)).map (eQ.prodCongr eQ)) (eQ x, eQ y) =
        pauliQuestionPMF (.ofAdmissibleParams Q)
          (QPBT.binaryRepresentation Q.model) (x, y) := by
        change (PMF.map (eQ.prodCongr eQ) _) ((eQ.prodCongr eQ) (x, y)) = _
        rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_single (x, y)]
        · simp
        · intro z _ hz
          have hne : (eQ.prodCongr eQ) (x, y) ≠ (eQ.prodCongr eQ) z :=
            fun h => hz ((eQ.prodCongr eQ).injective h).symm
          simp only [hne, ↓reduceIte]
        · simp
      exact hmap.symm ▸ hxy
    rw [Distribution.toPMF_apply, ENNReal.ofReal_pos] at hpos
    exact hcomm (eQ x) (eQ y) hpos (eA a) (eA b)
  · rw [← pauliStrategyToLibrary_value Q S.toStrategy]
    have hM : (fun x : QPBT.PauliQuestion Q =>
        (POVM.relabel eA (S.meas (eQ.symm x))).toMeasurement) = T.M := by
      funext x; apply Quantum.Measurement.ext; intro a
      simp [S, POVM.toMeasurement, POVM.ofMeasurement, POVM.relabel, Measurement.ofSumEqOne]
    have hEq : pauliStrategyToLibrary Q S.toStrategy = T.toStrategy := by
      change QPBT.Strategy.mk (G := QPBT.pauliBasisTest Q) T.ι T.ι T.ψ T.ψ_norm
          (fun x : QPBT.PauliQuestion Q => (POVM.relabel eA (S.meas (eQ.symm x))).toMeasurement)
          (fun x : QPBT.PauliQuestion Q => (POVM.relabel eA (S.meas (eQ.symm x))).toMeasurement) =
        T.toStrategy
      rw [hM]; rfl
    rw [hEq]; exact hval

theorem pauli_soundness :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : PauliParams) (epsilon : ℝ), 0 ≤ epsilon →
        ∀ S : PauliStrategy P
            (QPBT.fixedFieldModel P.q P.is_admissible_size).K,
          1 - epsilon ≤ S.value
            (pauliGame P
              (QPBT.binaryRepresentation
                (QPBT.fixedFieldModel P.q P.is_admissible_size))
              (QPBT.fixedBinTrace
                (QPBT.fixedFieldModel P.q P.is_admissible_size))) →
          ∃ w : ExtractionWitness
              (R := PauliRegister P
                (QPBT.fixedFieldModel P.q P.is_admissible_size).K) S,
            stateError w ≤ deltaQld a b epsilon P.m P.d P.q ∧
            (∀ W : PauliKind,
              rawPauliAliceError P S w
                  (QPBT.fixedBinTrace
                    (QPBT.fixedFieldModel P.q P.is_admissible_size)) W ≤
                deltaQld a b epsilon P.m P.d P.q) ∧
            ∀ W : PauliKind,
              rawPauliBobError P S w
                  (QPBT.fixedBinTrace
                    (QPBT.fixedFieldModel P.q P.is_admissible_size)) W ≤
                deltaQld a b epsilon P.m P.d P.q := by
  obtain ⟨a, b, ha, hb, hb1, hsound⟩ := QPBT.pauli_soundness
  refine ⟨a, b, ha, hb, hb1, ?_⟩
  rintro ⟨q, m, d, hm, hd, hq, hdvd⟩ ε hε S hval
  let Q : QPBT.AdmissibleParams := ⟨q, m, d, hd, hq, hdvd⟩
  obtain ⟨w, hst, hA, hB⟩ := hsound Q ε hε (pauliStrategyToLibrary Q S)
    (hval.trans_eq (pauliStrategyToLibrary_value Q S).symm)
  let w' : ExtractionWitness (R := PauliRegister (.ofAdmissibleParams Q) (QPBT.PauliScalar Q)) S :=
    ⟨w.ιA', w.ιB', w.φA, w.φB, w.aux, w.aux_norm⟩
  have hA' (W : PauliKind) : rawPauliAliceError _ S w' (QPBT.fixedBinTrace Q.model) W =
      QPBT.rawPauliOperatorDistanceA Q (pauliStrategyToLibrary Q S) w (pauliKindEquiv W) := by
    cases W <;> rfl
  have hB' (W : PauliKind) : rawPauliBobError _ S w' (QPBT.fixedBinTrace Q.model) W =
      QPBT.rawPauliOperatorDistanceB Q (pauliStrategyToLibrary Q S) w (pauliKindEquiv W) := by
    cases W <;> rfl
  exact ⟨w', hst, fun W => (hA' W).trans_le (hA _), fun W => (hB' W).trans_le (hB _)⟩

theorem pauli_soundness_qubit :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : PauliParams) (epsilon : ℝ), 0 ≤ epsilon →
        ∀ S : PauliStrategy P
            (QPBT.fixedFieldModel P.q P.is_admissible_size).K,
          1 - epsilon ≤ S.value
            (pauliGame P
              (QPBT.binaryRepresentation
                (QPBT.fixedFieldModel P.q P.is_admissible_size))
              (QPBT.fixedBinTrace
                (QPBT.fixedFieldModel P.q P.is_admissible_size))) →
          ∃ w : ExtractionWitness
              (R := QubitRegister P
                (QPBT.fixedFieldModel P.q
                  P.is_admissible_size).basisDim) S,
            stateError w ≤ deltaQld a b epsilon P.m P.d P.q ∧
            (∀ W : PauliKind,
              rawQubitAliceError P S w
                  (QPBT.fixedFieldModel P.q
                    P.is_admissible_size).binaryCoordinates W ≤
                deltaQld a b epsilon P.m P.d P.q) ∧
            ∀ W : PauliKind,
              rawQubitBobError P S w
                  (QPBT.fixedFieldModel P.q
                    P.is_admissible_size).binaryCoordinates W ≤
                deltaQld a b epsilon P.m P.d P.q := by
  classical
  obtain ⟨a, b, ha, hb, hb1, hsound⟩ := pauli_soundness
  refine ⟨a, b, ha, hb, hb1, ?_⟩
  intro P ε hε S hval
  let F := QPBT.fixedFieldModel P.q P.is_admissible_size
  obtain ⟨w, hst, hA, hB⟩ := hsound P ε hε S hval
  let eR : PauliRegister P F.K ≃ QubitRegister P F.basisDim :=
    QPBT.quditQubitLabelEquiv F
  let eA := (Equiv.refl w.ιA').prodCongr eR
  let eB := (Equiv.refl w.ιB').prodCongr eR
  let eJ := eA.prodCongr eB
  let iso {κ ν : Type} [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν] (e : κ ≃ ν) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
  let wQ : ExtractionWitness (R := QubitRegister P F.basisDim) S :=
    ⟨w.ιA', w.ιB', (iso eA).toLinearIsometry.comp w.φA,
      (iso eB).toLinearIsometry.comp w.φB, w.aux, w.aux_norm⟩
  have hid : idealExtractionState wQ = iso eJ (idealExtractionState w) := by
    ext p
    dsimp [wQ]
    simp [idealExtractionState, normalizedEPRState, iso, eJ, eA, eB, Fintype.card_congr eR]
  have hnorm (M N : Matrix _ _ ℂ) :
      ‖Matrix.toEuclideanLin (Matrix.reindex eJ eJ M - Matrix.reindex eJ eJ N)
        (idealExtractionState wQ)‖ =
      ‖Matrix.toEuclideanLin (M - N) (idealExtractionState w)‖ := by
    have hact (X : Matrix _ _ ℂ) :
        Matrix.toEuclideanLin (Matrix.reindex eJ eJ X) (iso eJ (idealExtractionState w)) =
          iso eJ (Matrix.toEuclideanLin X (idealExtractionState w)) := by
      ext p
      change (X.submatrix eJ.symm eJ.symm *ᵥ fun i => idealExtractionState w (eJ.symm i)) p =
        (X *ᵥ fun i => idealExtractionState w i) (eJ.symm p)
      rw [Matrix.submatrix_mulVec_equiv]
      simp [Function.comp_def]
    rw [hid, show Matrix.reindex eJ eJ M - Matrix.reindex eJ eJ N =
      Matrix.reindex eJ eJ (M - N) from rfl, hact, LinearIsometryEquiv.norm_map]
  have hproj (W : PauliKind) (u : PauliRegister P F.K) :
      Matrix.reindex eR eR (pauliProj (QPBT.fixedBinTrace F) W u) =
        qubitPauliProj W (binaryRegisterLabel F.binaryCoordinates u) := by
    have h := QPBT.pauliProj_reindex_quditQubitLabelEquiv F (pauliKindEquiv W) u
    ext r c
    have hrc := congrFun (congrFun h (eR.symm r)) (eR.symm c)
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm] at hrc ⊢
    dsimp only [eR] at hrc
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hrc
    cases W <;> exact hrc
  refine ⟨wQ, ?_, fun W => ?_, fun W => ?_⟩
  · refine (le_of_eq ?_).trans hst
    unfold stateError
    rw [show localIsometryTensor wQ.φA wQ.φB S.ψ = iso eJ (localIsometryTensor w.φA w.φB S.ψ)
      from rfl, hid, ← map_sub, LinearIsometryEquiv.norm_map]
  · refine (le_of_eq ?_).trans (hA W)
    refine Finset.sum_congr rfl fun u _ => congrArg (· ^ 2) ?_
    dsimp only
    have hM : liftedQubitAliceEffect (J' := wQ.ιB') wQ.φA
        ((S.alice (pauliMeasurementQuestion P W)).effect (.pauliOutcome u)) =
      Matrix.reindex eJ eJ (liftedPauliAliceEffect (J' := w.ιB') w.φA
        ((S.alice (pauliMeasurementQuestion P W)).effect (.pauliOutcome u))) := by
      ext r c
      have hconj : conjIsometry wQ.φA
          ((S.alice (pauliMeasurementQuestion P W)).effect (.pauliOutcome u)) =
        Matrix.reindex eA eA (conjIsometry w.φA
          ((S.alice (pauliMeasurementQuestion P W)).effect (.pauliOutcome u))) := rfl
      simp [liftedQubitAliceEffect, liftedPauliAliceEffect, hconj, Matrix.kronecker,
        Matrix.one_apply, mul_ite, eJ]
    have hN : idealProjectorAlice (J' := wQ.ιB')
        (qubitPauliProj W (binaryRegisterLabel F.binaryCoordinates u)) =
      Matrix.reindex eJ eJ (idealProjectorAlice (J' := w.ιB')
        (pauliProj (QPBT.fixedBinTrace F) W u)) := by
      ext r c; rw [← hproj W u]
      change _ = if (eA.symm r.1).1 = (eA.symm c.1).1 ∧ eB.symm r.2 = eB.symm c.2 then
        pauliProj (QPBT.fixedBinTrace F) W u (eA.symm r.1).2 (eA.symm c.1).2 else 0
      simp only [idealProjectorAlice, Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.apply_eq_iff_eq]
      rfl
    rw [hM, hN, hnorm]
  · refine (le_of_eq ?_).trans (hB W)
    refine Finset.sum_congr rfl fun u _ => congrArg (· ^ 2) ?_
    dsimp only
    have hM : liftedQubitBobEffect (I' := wQ.ιA') wQ.φB
        ((S.bob (pauliMeasurementQuestion P W)).effect (.pauliOutcome u)) =
      Matrix.reindex eJ eJ (liftedPauliBobEffect (I' := w.ιA') w.φB
        ((S.bob (pauliMeasurementQuestion P W)).effect (.pauliOutcome u))) := by
      ext r c
      have hconj : conjIsometry wQ.φB
          ((S.bob (pauliMeasurementQuestion P W)).effect (.pauliOutcome u)) =
        Matrix.reindex eB eB (conjIsometry w.φB
          ((S.bob (pauliMeasurementQuestion P W)).effect (.pauliOutcome u))) := rfl
      simp [liftedQubitBobEffect, liftedPauliBobEffect, hconj, Matrix.kronecker,
        Matrix.one_apply, ite_mul, eJ]
    have hN : idealProjectorBob (I' := wQ.ιA')
        (qubitPauliProj W (binaryRegisterLabel F.binaryCoordinates u)) =
      Matrix.reindex eJ eJ (idealProjectorBob (I' := w.ιA')
        (pauliProj (QPBT.fixedBinTrace F) W u)) := by
      ext r c; rw [← hproj W u]
      change _ = if eA.symm r.1 = eA.symm c.1 ∧ (eB.symm r.2).1 = (eB.symm c.2).1 then
        pauliProj (QPBT.fixedBinTrace F) W u (eB.symm r.2).2 (eB.symm c.2).2 else 0
      simp only [idealProjectorBob, Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.apply_eq_iff_eq]
      rfl
    rw [hM, hN, hnorm]

end

end MIPStarRE.QPBT.Palomar
