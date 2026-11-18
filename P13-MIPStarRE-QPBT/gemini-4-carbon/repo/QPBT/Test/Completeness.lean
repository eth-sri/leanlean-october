module

public import QPBT.Algebra.PauliTheorems
public import QPBT.Games.DistanceTheorems.TensorSupport
public import QPBT.Observables.ExpandedCommutation
public import QPBT.Observables.LineMeasurement.Restriction
public import QPBT.Test.MagicSquareTheorems.Basic
public import QPBT.Test.MagicSquareTheorems.PerfectStrategy
public import QPBT.Test.LowDegreeGameMeasurements
public import QPBT.Test.PauliBasisTest
public import QPBT.Games.StrategyClasses

/-! # Completeness of the Pauli basis test -/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

set_option maxRecDepth 8000

/-! ### Generalized Pauli basis and honest Pair/Magic-Square measurements -/

section Basis
variable {K ι : Type*} [Field K] [Fintype K] [DecidableEq K] [Algebra (ZMod 2) K]
  [Fintype ι] [DecidableEq ι]

noncomputable def pauliBasisMeasurement (W : PauliKind) : Measurement (ι → K) (ι → K) :=
  Measurement.ofSumEqOne (pauliProj W)
    (fun e => Matrix.nonneg_iff_posSemidef.mpr (posSemidef_pauliProj W e)) (sum_pauliProj_eq_one W)

theorem pauliProj_isProj (W : PauliKind) (e : ι → K) : IsProj (pauliProj W e) :=
  isStarProjection_iff'.2 ⟨by simpa using pauliProj_mul_pauliProj W e e,
    by rw [Matrix.star_eq_conjTranspose, (posSemidef_pauliProj W e).isHermitian.eq]⟩

omit [Fintype K] in
theorem tauObservable_transpose (W : PauliKind) (a : ι → K) :
    (tauObservable W a)ᵀ = tauObservable W a := by
  have : CharP K 2 := (Algebra.charP_iff (ZMod 2) K 2).mp (ZMod.charP 2)
  have hsw (x y c : K) : (x = y + c) ↔ (y = x + c) :=
    ⟨by rintro rfl; rw [add_assoc, CharTwo.add_self_eq_zero, add_zero],
     by rintro rfl; rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]⟩
  ext x y; rw [Matrix.transpose_apply]
  cases W <;> refine Finset.prod_congr rfl fun i _ => ?_
  · change (if y i = x i + a i then (1 : ℂ) else 0) = if x i = y i + a i then 1 else 0
    by_cases h : x i = y i + a i
    · rw [ite_eq_left_iff.mpr fun hc => absurd ((hsw _ _ _).mp h) hc,
        ite_eq_left_iff.mpr fun hc => absurd h hc]
    · rw [ite_eq_right_iff.mpr fun hc => absurd ((hsw _ _ _).mp hc) h,
        ite_eq_right_iff.mpr fun hc => absurd hc h]
  · change (if y i = x i then phaseSign (binTrace K (a i * x i)) else 0) =
      if x i = y i then phaseSign (binTrace K (a i * y i)) else 0
    by_cases h : x i = y i <;> simp [h, eq_comm]
end Basis

def pauliTraceBit (P : AdmissibleParams)
    (u : Fin P.m → PauliScalar P) (r : PauliScalar P) (h : PauliRegister P) : ZMod 2 :=
  fixedBinTrace P.model (lowDegreeEnc h u * r)

def pauliTraceMeasurement (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (r : PauliScalar P) :
    Measurement (ZMod 2) (PauliRegister P) :=
  (pauliBasisMeasurement W).postprocess (pauliTraceBit P u r)

theorem pauliTraceMeasurement_projective (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (r : PauliScalar P) :
    Measurement.IsProjective (pauliTraceMeasurement P W u r) :=
  SandwichProduct.postprocess_isProjective _ (fun e => pauliProj_isProj W e) _

theorem pauliTraceMeasurement_effect_transpose (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (r : PauliScalar P) (b : ZMod 2) :
    ((pauliTraceMeasurement P W u r).effect b)ᵀ = (pauliTraceMeasurement P W u r).effect b :=
  postprocess_effect_transpose _ _ (pauliProj_transpose W) b

theorem obsOf_pauliTraceMeasurement (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (r : PauliScalar P) :
    obsOf (pauliTraceMeasurement P W u r) = tauObservable W (r • indicatorVec u) := by
  classical
  have hp (e : PauliRegister P) :
      phaseSign (binTrace (PauliScalar P) (dotProduct (r • indicatorVec u) e)) =
        phaseSign (pauliTraceBit P u r e) := by
    congr 2; rw [lowDegreeEnc_eq_dotProduct]
    simp only [dotProduct, Finset.sum_mul, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [tauObservable_eq_sum_pauliProj, Finset.sum_congr rfl fun e _ => by rw [hp e],
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun e => pauliTraceBit P u r e = 0)]
  have hf : (Finset.univ.filter fun e => ¬ pauliTraceBit P u r e = 0) =
      Finset.univ.filter fun e => pauliTraceBit P u r e = 1 := by
    ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases zmod_two_eq_zero_or_one (pauliTraceBit P u r e) with h | h <;> simp [h]
  have h0 : ∑ e ∈ Finset.univ.filter (fun e => pauliTraceBit P u r e = 0),
      phaseSign (pauliTraceBit P u r e) • pauliProj W e =
      (pauliTraceMeasurement P W u r).effect 0 :=
    Finset.sum_congr rfl fun e he => by
      rw [(Finset.mem_filter.mp he).2]; simp [phaseSign]; rfl
  have h1 : ∑ e ∈ Finset.univ.filter (fun e => ¬ pauliTraceBit P u r e = 0),
      phaseSign (pauliTraceBit P u r e) • pauliProj W e =
      -(pauliTraceMeasurement P W u r).effect 1 := by
    rw [hf, ← neg_one_smul ℂ ((pauliTraceMeasurement P W u r).effect 1)]
    change _ = (-1 : ℂ) • ∑ e ∈ _, pauliProj W e
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun e he => by rw [(Finset.mem_filter.mp he).2]; norm_num [phaseSign]
  rw [h0, h1, ← sub_eq_add_neg]; rfl

theorem obsOf_pauliTraceMeasurement_anticommute (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z ≠ 0) :
    obsOf (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)) *
        obsOf (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)) =
      -(obsOf (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)) *
        obsOf (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z))) := by
  rw [obsOf_pauliTraceMeasurement, obsOf_pauliTraceMeasurement, tauObservable_X_mul_Z]
  change phaseSign (pauliPairGamma P z) • _ = _
  rcases zmod_two_eq_zero_or_one (pauliPairGamma P z) with h | h
  · exact absurd h hgamma
  · rw [h]; simp [phaseSign]

theorem pauliTraceMeasurement_effect_commute (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z = 0) (a b : ZMod 2) :
    Commute ((pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)).effect a)
      ((pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)).effect b) := by
  rw [← reflectionEffect_obsOf_measurement (pauliTraceMeasurement P .X _ _) a,
    ← reflectionEffect_obsOf_measurement (pauliTraceMeasurement P .Z _ _) b]
  refine reflectionEffect_commute ?_ a b
  rw [commute_iff_eq, obsOf_pauliTraceMeasurement, obsOf_pauliTraceMeasurement,
    tauObservable_X_mul_Z]
  change phaseSign (pauliPairGamma P z) • _ = _
  simp [hgamma, phaseSign]

def restrictToAxisLine (L : LdParams) (line : LineDesc L)
    (g : MvPolynomial (Fin L.m) (ScalarQ L)) : DegPoly L L.d :=
  fun i => (polynomialOnLine L line g).coeff i.val

theorem evalCoefficient_restrictToAxisLine_lowDegreeEncoding
    (L : LdParams) (line : LineDesc L) (hline : line.kind = .axis)
    (h : Cube L.m → ScalarQ L) (t : ScalarQ L) :
    evalCoefficient (restrictToAxisLine L line (lowDegreeEncoding h)) t =
      MvPolynomial.eval (line.base + t • line.direction) (lowDegreeEncoding h) := by
  unfold evalCoefficient restrictToAxisLine
  rw [Fin.sum_univ_eq_sum_range (fun i => (polynomialOnLine L line (lowDegreeEncoding h)).coeff i * t ^ i),
    ← Polynomial.eval_eq_sum_range'
      (Nat.lt_succ_of_le ((polynomialOnLine_lowDegreeEncoding_natDegree_le_one_of_axis L line hline h).trans L.hd)),
    eval_polynomialOnLine]

def pauliMagicCellMeasurement (P : AdmissibleParams)
    (z : PauliSpace P) (hg : pauliPairGamma P z ≠ 0) :
    Fin 9 → Measurement (ZMod 2) (PauliRegister P × ZMod 2) :=
  let A := pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)
  let B := pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)
  msCellMeasurement (obsOf A) (obsOf B)
    (obsOf_conjTranspose A (pauliTraceMeasurement_projective P .X _ _))
    (obsOf_conjTranspose B (pauliTraceMeasurement_projective P .Z _ _))
    (obsOf_sq A (pauliTraceMeasurement_projective P .X _ _))
    (obsOf_sq B (pauliTraceMeasurement_projective P .Z _ _))
    (obsOf_pauliTraceMeasurement_anticommute P z hg)

theorem pauliMagicCellMeasurement_projective (P : AdmissibleParams)
    (z : PauliSpace P) (hg : pauliPairGamma P z ≠ 0) (j : Fin 9) :
    Measurement.IsProjective (pauliMagicCellMeasurement P z hg j) :=
  msCellMeasurement_projective _ _
    (obsOf_conjTranspose _ (pauliTraceMeasurement_projective P .X _ _))
    (obsOf_conjTranspose _ (pauliTraceMeasurement_projective P .Z _ _))
    (obsOf_sq _ (pauliTraceMeasurement_projective P .X _ _))
    (obsOf_sq _ (pauliTraceMeasurement_projective P .Z _ _))
    (obsOf_pauliTraceMeasurement_anticommute P z hg) j

theorem pauliMagicCellMeasurement_commute (P : AdmissibleParams)
    (z : PauliSpace P) (hg : pauliPairGamma P z ≠ 0)
    (i : Fin 6) (k l : Fin 3) (a b : ZMod 2) :
    Commute ((pauliMagicCellMeasurement P z hg (msConstraintVars i k)).effect a)
      ((pauliMagicCellMeasurement P z hg (msConstraintVars i l)).effect b) :=
  reflectionEffect_commute (msConstraintObservable_commute _ _
    (obsOf_sq _ (pauliTraceMeasurement_projective P .X _ _))
    (obsOf_sq _ (pauliTraceMeasurement_projective P .Z _ _))
    (obsOf_pauliTraceMeasurement_anticommute P z hg) i k l) a b

def pauliMagicMeasurement (P : AdmissibleParams)
    (z : PauliSpace P) (hg : pauliPairGamma P z ≠ 0) :
    MsType → Measurement MsAnswer (PauliRegister P × ZMod 2) :=
  msStrategyMeasurement (pauliMagicCellMeasurement P z hg)
    (pauliMagicCellMeasurement_projective P z hg)
    (pauliMagicCellMeasurement_commute P z hg)

def msBasisVar : PauliKind → Fin 9 | .X => 0 | .Z => 4

def pauliPairScalar (P : AdmissibleParams) (W : PauliKind) (z : PauliSpace P) : PauliScalar P :=
  match W with | .X => pauliRXBlock z | .Z => pauliRZBlock z

theorem pauliMagicMeasurement_var_effect (P : AdmissibleParams)
    (z : PauliSpace P) (hg : pauliPairGamma P z ≠ 0) (W : PauliKind) (b : ZMod 2) :
    (pauliMagicMeasurement P z hg (.var (msBasisVar W))).effect (.bit b) =
      heteroKron ((pauliTraceMeasurement P W (pauliPointBlock W z) (pauliPairScalar P W z)).effect b)
        (1 : Op (ZMod 2)) := by
  have h (Z : Op (PauliRegister P)) :
      reflectionEffect (heteroKron Z (1 : Op (ZMod 2))) b = heteroKron (reflectionEffect Z b) 1 := by
    ext i j; rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
      simp [reflectionEffect, heteroKron, Matrix.kronecker, Matrix.one_apply, Prod.ext_iff] <;>
      split_ifs <;> simp_all [mul_add]
  cases W <;> unfold pauliMagicMeasurement msBasisVar pauliPointBlock pauliPairScalar <;>
    rw [msStrategyMeasurement_var_bit] <;>
    exact (h _).trans (by rw [reflectionEffect_obsOf_measurement])

def pauliPairEffect (P : AdmissibleParams) (z : PauliSpace P) (β : ZMod 2 × ZMod 2) :
    Op (PauliRegister P) :=
  (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)).effect β.1 *
    (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)).effect β.2

theorem pauliPairEffect_isProj (P : AdmissibleParams) (z : PauliSpace P)
    (hg : pauliPairGamma P z = 0) (β : ZMod 2 × ZMod 2) : IsProj (pauliPairEffect P z β) :=
  IsStarProjection.mul (pauliTraceMeasurement_projective P .X _ _ β.1)
    (pauliTraceMeasurement_projective P .Z _ _ β.2)
    (pauliTraceMeasurement_effect_commute P z hg β.1 β.2)

def pauliPairMeasurement (P : AdmissibleParams) (z : PauliSpace P)
    (hg : pauliPairGamma P z = 0) : Measurement (ZMod 2 × ZMod 2) (PauliRegister P) :=
  Measurement.ofSumEqOne (pauliPairEffect P z) (fun β => (pauliPairEffect_isProj P z hg β).nonneg) <| by
    rw [Fintype.sum_prod_type]
    simp_rw [pauliPairEffect, ← Finset.mul_sum,
      (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)).sum_eq_one, mul_one,
      (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)).sum_eq_one]

/-! ### Total honest measurement family -/

abbrev HonestIndex (P : AdmissibleParams) := PauliRegister P × ZMod 2

def deterministicMeasurement {α V : Type*} [Fintype α] [DecidableEq α] [Fintype V] [DecidableEq V]
    (a : α) : Measurement α V :=
  (Measurement.ofSumEqOne (fun _ : Unit => (1 : Op V))
    (fun _ => Matrix.PosSemidef.one.nonneg) (by simp)).postprocess fun _ => a

theorem deterministicMeasurement_effect_eq_zero_of_ne {α V : Type*}
    [Fintype α] [DecidableEq α] [Fintype V] [DecidableEq V] {a₀ a : α} (ha : a ≠ a₀) :
    (deterministicMeasurement (V := V) a₀).effect a = 0 :=
  postprocess_effect_eq_zero_of_notMem _ _ fun ⟨_, hu⟩ => ha hu.symm

theorem deterministicMeasurement_effect_commute {α V : Type*}
    [Fintype α] [DecidableEq α] [Fintype V] [DecidableEq V] (a₀ a : α) (A : Op V) :
    Commute ((deterministicMeasurement (V := V) a₀).effect a) A := by
  by_cases h : a = a₀
  · subst h
    have hs : (deterministicMeasurement (V := V) a).effect a = 1 := by
      rw [deterministicMeasurement, Measurement.postprocess_effect]; simp [Measurement.ofSumEqOne]
    rw [hs]; exact Commute.one_left A
  · rw [deterministicMeasurement_effect_eq_zero_of_ne h]; exact Commute.zero_left A

def placedPauliMeasurement {P : AdmissibleParams} {α : Type*} [Fintype α] [DecidableEq α]
    (M : Measurement α (PauliRegister P)) (f : α → PauliAnswer P) :
    Measurement (PauliAnswer P) (HonestIndex P) :=
  (DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2) M).postprocess f

theorem placedPauliMeasurement_effect_eq {P : AdmissibleParams} {α : Type*} [Fintype α] [DecidableEq α]
    (M : Measurement α (PauliRegister P)) (f : α → PauliAnswer P) (a : PauliAnswer P) :
    (placedPauliMeasurement M f).effect a =
      heteroKron ((M.postprocess f).effect a) (1 : Op (ZMod 2)) := by
  rw [placedPauliMeasurement, Measurement.postprocess_effect, Measurement.postprocess_effect]
  exact leftTensor_finset_sum _ _

theorem placedPauliMeasurement_projective {P : AdmissibleParams} {α : Type*} [Fintype α] [DecidableEq α]
    (M : Measurement α (PauliRegister P)) (hM : Measurement.IsProjective M) (f : α → PauliAnswer P) :
    Measurement.IsProjective (placedPauliMeasurement M f) :=
  SandwichProduct.postprocess_isProjective _
    (fun a => MakingMeasurementsProjective.isProj_kronecker (hM a) (.one _)) f

theorem placedPauliMeasurement_effect_transpose {P : AdmissibleParams} {α : Type*} [Fintype α] [DecidableEq α]
    (M : Measurement α (PauliRegister P)) (hM : ∀ a, (M.effect a)ᵀ = M.effect a)
    (f : α → PauliAnswer P) (a : PauliAnswer P) :
    ((placedPauliMeasurement M f).effect a)ᵀ = (placedPauliMeasurement M f).effect a := by
  refine postprocess_effect_transpose _ f (fun b => ?_) a
  change (heteroKron (M.effect b) (1 : Op (ZMod 2)))ᵀ = heteroKron (M.effect b) 1
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [Matrix.transpose_apply, heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [show M.effect b j i = M.effect b i j from congrFun (congrFun (hM b) i) j]
  by_cases hkl : k = l
  · subst l; simp
  · simp [hkl, Ne.symm hkl]

theorem placedPauliMeasurement_commute {P : AdmissibleParams} {ζ : Type*} [Fintype ζ] [DecidableEq ζ]
    (M : Measurement ζ (PauliRegister P)) (hM : Measurement.IsProjective M)
    (f g : ζ → PauliAnswer P) (a b : PauliAnswer P) :
    Commute ((placedPauliMeasurement M f).effect a) ((placedPauliMeasurement M g).effect b) := by
  rw [placedPauliMeasurement_effect_eq, placedPauliMeasurement_effect_eq,
    commute_iff_eq, heteroKron_mul, heteroKron_mul]
  congr 1; rw [ ← commute_iff_eq, Measurement.postprocess_effect, Measurement.postprocess_effect]
  refine Commute.sum_left _ _ _ fun x _ => Commute.sum_right _ _ _ fun y _ => ?_
  by_cases hxy : x = y
  · exact hxy ▸ Commute.refl _
  · rw [commute_iff_eq, DistanceCalculus.projective_effect_mul_effect_eq_zero M hM hxy,
      DistanceCalculus.projective_effect_mul_effect_eq_zero M hM (Ne.symm hxy)]

def pauliAnswerOfMs {P : AdmissibleParams} : MsAnswer → PauliAnswer P
  | .triple a => .msTriple a
  | .bit a => .bit a

theorem pauliAnswerOfMs_injective {P : AdmissibleParams} :
    Function.Injective (@pauliAnswerOfMs P) := by
  intro a b h; cases a <;> cases b <;> simp only [pauliAnswerOfMs] at h <;> cases h <;> rfl

def honestPairMeasurement (P : AdmissibleParams) (z : PauliSpace P) :
    Measurement (PauliAnswer P) (HonestIndex P) := by
  classical
  exact if hg : pauliPairGamma P z = 0 then
    placedPauliMeasurement (pauliPairMeasurement P z hg) .pairBits
  else deterministicMeasurement (V := HonestIndex P) (.pairBits (0, 0))

def honestMagicMeasurement (P : AdmissibleParams) (t : MsType) (z : PauliSpace P) :
    Measurement (PauliAnswer P) (HonestIndex P) := by
  classical
  exact if hg : pauliPairGamma P z = 0 then
    deterministicMeasurement (V := HonestIndex P)
      (match t with | .constraint _ => .msTriple 0 | .var _ => .bit 0)
  else (pauliMagicMeasurement P z hg t).postprocess pauliAnswerOfMs

def honestMeasurement (P : AdmissibleParams) :
    PauliType → PauliSpace P → Measurement (PauliAnswer P) (HonestIndex P)
  | .point W, z => placedPauliMeasurement (pauliBasisMeasurement W)
      (fun h => .value (lowDegreeEnc h (pauliPointBlock W z)))
  | .aline W, z => placedPauliMeasurement (pauliBasisMeasurement W)
      (fun h => .alinePoly (restrictToAxisLine P.toLdParams
        (aLineDescOf P.toLdParams (ldALineCL P.toLdParams (pauliToLd P W z))) (lowDegreeEncoding h)))
  | .dline W, z => placedPauliMeasurement (pauliBasisMeasurement W)
      (fun h => .dlinePoly (restrictToLine P.toLdParams
        (dLineDescOf P.toLdParams (ldDLineCL P.toLdParams (pauliToLd P W z))) (lowDegreeEncoding h)))
  | .pauli W, _ => placedPauliMeasurement (pauliBasisMeasurement W) .pauliOutcome
  | .pairW W, z => placedPauliMeasurement (pauliBasisMeasurement W)
      (fun h => .bit (pauliTraceBit P (pauliPointBlock W z) (pauliPairScalar P W z) h))
  | .pair, z => honestPairMeasurement P z
  | .ms t, z => honestMagicMeasurement P t z

theorem honestMeasurement_projective (P : AdmissibleParams) (t : PauliType) (z : PauliSpace P) :
    Measurement.IsProjective (honestMeasurement P t z) := by
  classical
  cases t with
  | point W | aline W | dline W | pauli W | pairW W =>
      exact placedPauliMeasurement_projective _ (fun e => pauliProj_isProj W e) _
  | pair =>
      dsimp only [honestMeasurement, honestPairMeasurement]; split_ifs with hg
      · exact placedPauliMeasurement_projective _ (fun β => pauliPairEffect_isProj P z hg β) _
      · exact SandwichProduct.postprocess_isProjective _ (fun _ => .one _) _
  | ms t =>
      dsimp only [honestMeasurement, honestMagicMeasurement]; split_ifs with hg
      · exact SandwichProduct.postprocess_isProjective _ (fun _ => .one _) _
      · exact SandwichProduct.postprocess_isProjective _
          (msStrategyMeasurement_projective _ _ _ t) _

theorem honestMeasurement_effect_transpose (P : AdmissibleParams) (t : PauliType)
    (z : PauliSpace P) (a : PauliAnswer P) :
    ((honestMeasurement P t z).effect a)ᵀ = (honestMeasurement P t z).effect a := by
  classical
  cases t with
  | point W | aline W | dline W | pauli W | pairW W =>
      exact placedPauliMeasurement_effect_transpose _ (pauliProj_transpose W) _ a
  | pair =>
      dsimp only [honestMeasurement, honestPairMeasurement]; split_ifs with hg
      · refine placedPauliMeasurement_effect_transpose _ (fun β => ?_) _ a
        change (pauliPairEffect P z β)ᵀ = pauliPairEffect P z β
        rw [pauliPairEffect, Matrix.transpose_mul, pauliTraceMeasurement_effect_transpose,
          pauliTraceMeasurement_effect_transpose,
          (pauliTraceMeasurement_effect_commute P z hg β.1 β.2).eq]
      · exact postprocess_effect_transpose _ _ (fun _ => Matrix.transpose_one) a
  | ms t =>
      dsimp only [honestMeasurement, honestMagicMeasurement]; split_ifs with hg
      · exact postprocess_effect_transpose _ _ (fun _ => Matrix.transpose_one) a
      · refine postprocess_effect_transpose _ _ (fun b => ?_) a
        dsimp only [pauliMagicMeasurement]
        refine msStrategyMeasurement_effect_transpose _ _ _ (fun j c => ?_) t b
        dsimp only [pauliMagicCellMeasurement]
        apply msCellMeasurement_transpose
        · rw [obsOf_pauliTraceMeasurement]; exact tauObservable_transpose _ _
        · rw [obsOf_pauliTraceMeasurement]; exact tauObservable_transpose _ _

/-! ### Commutation and rejection on the Pauli type graph -/

def PauliEdgeOriented (t₁ t₂ : PauliType) : Prop :=
  (∃ W, t₁ = .point W ∧ (t₂ = .aline W ∨ t₂ = .dline W ∨ t₂ = .pauli W ∨ t₂ = .pairW W)) ∨
    (∃ W, t₁ = .pairW W ∧ t₂ = .pair) ∨
    ∃ W, t₁ = .point W ∧ t₂ = .ms (.var (msBasisVar W))

theorem pauliEdges_cases {t₁ t₂ : PauliType} (h : Sym2.mk t₁ t₂ ∈ pauliEdges) :
    t₁ = t₂ ∨ (∃ s₁ s₂, t₁ = .ms s₁ ∧ t₂ = .ms s₂ ∧ Sym2.mk s₁ s₂ ∈ msEdges) ∨
      PauliEdgeOriented t₁ t₂ ∨ PauliEdgeOriented t₂ t₁ := by
  classical
  simp only [pauliEdges, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, Prod.exists] at h
  rcases h with (((⟨a, h⟩ | ((⟨W, h⟩ | ⟨W, h⟩) | ⟨W, h⟩)) | (⟨W, h⟩ | h | h)) | ⟨W, h⟩) | ⟨s₁, s₂, hm, h⟩
  · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact Or.inl rfl
  · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨W, rfl, Or.inl rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W, rfl, Or.inl rfl⟩)))
  · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨W, rfl, Or.inr (Or.inl rfl)⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W, rfl, Or.inr (Or.inl rfl)⟩)))
  · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨W, rfl, Or.inr (Or.inr (Or.inl rfl))⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W, rfl, Or.inr (Or.inr (Or.inl rfl))⟩)))
  · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨W, rfl, Or.inr (Or.inr (Or.inr rfl))⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W, rfl, Or.inr (Or.inr (Or.inr rfl))⟩)))
  · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr ⟨.X, rfl, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨.X, rfl, rfl⟩))))
  · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr ⟨.Z, rfl, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨.Z, rfl, rfl⟩))))
  · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl ⟨W, rfl, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨W, rfl, rfl⟩))))
  · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨s₁, s₂, rfl, rfl, hm⟩)
    · exact Or.inr (Or.inl ⟨s₂, s₁, rfl, rfl, by rwa [Sym2.eq_swap]⟩)

theorem pauliQuestionDistribution_pos_incidence (P : AdmissibleParams)
    (x y : PauliQuestion P) (hxy : 0 < (pauliQuestionDistribution P).weight (x, y)) :
    ∃ z : PauliSpace P, Sym2.mk x.1 y.1 ∈ pauliEdges ∧
      x.2 = pauliCL P x.1 z ∧ y.2 = pauliCL P y.1 z := by
  classical
  let _ : Nonempty PauliEdge := pauliEdge_nonempty
  have hmem : (x, y) ∈ (pauliQuestionDistribution P).support := by
    by_contra hnot
    exact lt_irrefl 0 (((pauliQuestionDistribution P).outsideSupport _ hnot) ▸ hxy)
  unfold pauliQuestionDistribution at hmem
  rw [Distribution.map_support, uniformDistribution_support] at hmem
  obtain ⟨q, -, hq⟩ := Finset.mem_image.mp hmem
  rcases Prod.mk.inj hq.symm with ⟨rfl, rfl⟩
  exact ⟨q.2, q.1.2, rfl, rfl⟩

theorem honestMagicMeasurement_var_eq_placedBasis (P : AdmissibleParams)
    (z : PauliSpace P) (hg : pauliPairGamma P z ≠ 0) (W : PauliKind) :
    honestMagicMeasurement P (.var (msBasisVar W)) z =
      placedPauliMeasurement (pauliBasisMeasurement W)
        (fun h => .bit (pauliTraceBit P (pauliPointBlock W z) (pauliPairScalar P W z) h)) := by
  classical
  dsimp only [honestMagicMeasurement]; rw [dif_neg hg]
  change ((pauliMagicCellMeasurement P z hg (msBasisVar W)).postprocess MsAnswer.bit).postprocess
    pauliAnswerOfMs = _
  rw [Measurement.postprocess_comp]
  have hpl : DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2)
      (pauliTraceMeasurement P W (pauliPointBlock W z) (pauliPairScalar P W z)) =
      pauliMagicCellMeasurement P z hg (msBasisVar W) := by
    refine Measurement.ext fun b => ?_
    rw [← msStrategyMeasurement_var_bit (pauliMagicCellMeasurement P z hg)
      (pauliMagicCellMeasurement_projective P z hg) (pauliMagicCellMeasurement_commute P z hg)]
    exact (pauliMagicMeasurement_var_effect P z hg W b).symm
  rw [← hpl]
  have hp : DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2)
      (pauliTraceMeasurement P W (pauliPointBlock W z) (pauliPairScalar P W z)) =
      (DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2) (pauliBasisMeasurement W)).postprocess
        (pauliTraceBit P (pauliPointBlock W z) (pauliPairScalar P W z)) :=
    Measurement.ext fun b => by
      change heteroKron (((pauliBasisMeasurement W).postprocess _).effect b) _ = _
      rw [Measurement.postprocess_effect, Measurement.postprocess_effect]
      exact (leftTensor_finset_sum _ _).symm
  rw [hp, Measurement.postprocess_comp]; rfl

theorem honestMeasurement_commute_of_oriented (P : AdmissibleParams)
    {t₁ t₂ : PauliType} (h : PauliEdgeOriented t₁ t₂) (z : PauliSpace P) (a b : PauliAnswer P) :
    Commute ((honestMeasurement P t₁ (pauliCL P t₁ z)).effect a)
      ((honestMeasurement P t₂ (pauliCL P t₂ z)).effect b) := by
  classical
  rcases h with ⟨W, rfl, rfl | rfl | rfl | rfl⟩ | ⟨W, rfl, rfl⟩ | ⟨W, rfl, rfl⟩
  · exact placedPauliMeasurement_commute _ (fun e => pauliProj_isProj W e) _ _ a b
  · exact placedPauliMeasurement_commute _ (fun e => pauliProj_isProj W e) _ _ a b
  · exact placedPauliMeasurement_commute _ (fun e => pauliProj_isProj W e) _ _ a b
  · exact placedPauliMeasurement_commute _ (fun e => pauliProj_isProj W e) _ _ a b
  · change Commute ((honestMeasurement P (.pairW W) (pauliSharedProjection z)).effect a)
      ((honestPairMeasurement P (pauliSharedProjection z)).effect b)
    dsimp only [honestPairMeasurement]; split_ifs with hg
    · have hp : honestMeasurement P (.pairW W) (pauliSharedProjection z) =
          placedPauliMeasurement (pauliTraceMeasurement P W
            (pauliPointBlock W (pauliSharedProjection z))
            (pauliPairScalar P W (pauliSharedProjection z))) .bit := by
        refine Measurement.ext fun c => ?_
        rw [honestMeasurement, placedPauliMeasurement_effect_eq, placedPauliMeasurement_effect_eq,
          pauliTraceMeasurement, Measurement.postprocess_comp]
      rw [hp, placedPauliMeasurement_effect_eq, placedPauliMeasurement_effect_eq,
        commute_iff_eq, heteroKron_mul, heteroKron_mul]
      congr 1; rw [← commute_iff_eq, Measurement.postprocess_effect, Measurement.postprocess_effect]
      refine Commute.sum_left _ _ _ fun x _ => Commute.sum_right _ _ _ fun c _ => ?_
      have hself {u r} (x₁ x₂ : ZMod 2) :
          Commute ((pauliTraceMeasurement P W u r).effect x₁)
            ((pauliTraceMeasurement P W u r).effect x₂) := by
        by_cases hx : x₁ = x₂
        · exact hx ▸ Commute.refl _
        · rw [commute_iff_eq, DistanceCalculus.projective_effect_mul_effect_eq_zero _
            (pauliTraceMeasurement_projective P W _ _) hx,
            DistanceCalculus.projective_effect_mul_effect_eq_zero _
            (pauliTraceMeasurement_projective P W _ _) (Ne.symm hx)]
      cases W
      · exact Commute.mul_right (hself x c.1)
          (pauliTraceMeasurement_effect_commute P (pauliSharedProjection z) hg x c.2)
      · exact Commute.mul_right
          (pauliTraceMeasurement_effect_commute P (pauliSharedProjection z) hg c.1 x).symm
          (hself x c.2)
    · exact (deterministicMeasurement_effect_commute _ _ _).symm
  · change Commute _ ((honestMagicMeasurement P _ (pauliSharedProjection z)).effect b)
    by_cases hg : pauliPairGamma P (pauliSharedProjection z) = 0
    · dsimp only [honestMagicMeasurement]; rw [dif_pos hg]
      exact (deterministicMeasurement_effect_commute _ _ _).symm
    · rw [honestMagicMeasurement_var_eq_placedBasis P (pauliSharedProjection z) hg W]
      exact placedPauliMeasurement_commute _ (fun e => pauliProj_isProj W e) _ _ a b

theorem honestMeasurement_commuting (P : AdmissibleParams) :
    IsCommutingOn (pauliQuestionDistribution P)
      (fun q : PauliQuestion P => honestMeasurement P q.1 q.2)
      (fun q : PauliQuestion P => honestMeasurement P q.1 q.2) := by
  classical
  intro x y hxy a b
  obtain ⟨z, hedge, hx, hy⟩ := pauliQuestionDistribution_pos_incidence P x y hxy
  change Commute ((honestMeasurement P x.1 x.2).effect a) ((honestMeasurement P y.1 y.2).effect b)
  rw [hx, hy]
  rcases pauliEdges_cases hedge with heq | ⟨s₁, s₂, hs₁, hs₂, hms⟩ | hor | hor
  · rw [heq]
    by_cases hab : a = b
    · exact hab ▸ Commute.refl _
    · rw [commute_iff_eq, DistanceCalculus.projective_effect_mul_effect_eq_zero _
        (honestMeasurement_projective P _ _) hab,
        DistanceCalculus.projective_effect_mul_effect_eq_zero _
        (honestMeasurement_projective P _ _) (Ne.symm hab)]
  · rw [hs₁, hs₂]
    change Commute ((honestMagicMeasurement P s₁ (pauliSharedProjection z)).effect a)
      ((honestMagicMeasurement P s₂ (pauliSharedProjection z)).effect b)
    dsimp only [honestMagicMeasurement]; split_ifs with hg
    · exact deterministicMeasurement_effect_commute _ _ _
    · have hsupp : (s₁, s₂) ∈ msGameSymm.μ.support :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hms⟩
      rw [Measurement.postprocess_effect, Measurement.postprocess_effect]
      rcases msGame_support_incidence s₁ s₂ hsupp with ⟨i, k, rfl, rfl⟩ | ⟨i, k, rfl, rfl⟩
      · exact Commute.sum_left _ _ _ fun u _ => Commute.sum_right _ _ _ fun v _ =>
          msStrategyMeasurement_incident_commute _ _ _ i k u v
      · exact Commute.sum_left _ _ _ fun u _ => Commute.sum_right _ _ _ fun v _ =>
          (msStrategyMeasurement_incident_commute _ _ _ i k v u).symm
  · exact honestMeasurement_commute_of_oriented P hor z a b
  · exact (honestMeasurement_commute_of_oriented P hor z b a).symm

/-! ### Rejection of wrong answers -/

theorem honestMeasurement_effect_eq_zero_of_invalid (P : AdmissibleParams)
    (t : PauliType) (z : PauliSpace P) {a : PauliAnswer P} (ha : validPauliAnswer t a = false) :
    (honestMeasurement P t z).effect a = 0 := by
  classical
  cases t with
  | point W | aline W | dline W | pauli W | pairW W =>
      exact postprocess_effect_eq_zero_of_notMem _ _ (by rintro ⟨_, rfl⟩; simp [validPauliAnswer] at ha)
  | pair =>
      dsimp only [honestMeasurement, honestPairMeasurement]; split_ifs with hg
      · exact postprocess_effect_eq_zero_of_notMem _ _ (by rintro ⟨_, rfl⟩; simp [validPauliAnswer] at ha)
      · exact deterministicMeasurement_effect_eq_zero_of_ne (by rintro rfl; simp [validPauliAnswer] at ha)
  | ms s =>
      dsimp only [honestMeasurement, honestMagicMeasurement]; split_ifs with hg
      · cases s <;> exact deterministicMeasurement_effect_eq_zero_of_ne
          (by rintro rfl; simp [validPauliAnswer] at ha)
      · rw [Measurement.postprocess_effect]
        refine Finset.sum_eq_zero fun c hc => ?_
        have hca := (Finset.mem_filter.mp hc).2
        cases s <;> cases c
        · exact absurd ha (by rw [← hca]; simp [pauliAnswerOfMs, validPauliAnswer])
        · exact msStrategyMeasurement_constraint_zero _ _ _ _ fun ⟨_, h⟩ => MsAnswer.noConfusion h
        · exact msStrategyMeasurement_var_zero _ _ _ _ fun ⟨_, h⟩ => MsAnswer.noConfusion h
        · exact absurd ha (by rw [← hca]; simp [pauliAnswerOfMs, validPauliAnswer])

private theorem placedBasis_rejected_mul (P : AdmissibleParams) (W : PauliKind)
    (x y : PauliQuestion P) (f g : PauliRegister P → PauliAnswer P)
    (hacc : ∀ h, pauliWinPredicate P x y (f h) (g h) = true)
    (a b : PauliAnswer P) (hrej : pauliWinPredicate P x y a b = false) :
    (placedPauliMeasurement (pauliBasisMeasurement W) f).effect a *
      (placedPauliMeasurement (pauliBasisMeasurement W) g).effect b = 0 := by
  classical
  change ((DistanceCalculus.leftPlacedMeasurement (pauliBasisMeasurement W)).postprocess f).effect a *
    ((DistanceCalculus.leftPlacedMeasurement (pauliBasisMeasurement W)).postprocess g).effect b = 0
  rw [Measurement.postprocess_effect, Measurement.postprocess_effect, Finset.sum_mul]
  refine Finset.sum_eq_zero fun u hu => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero fun v hv => ?_
  by_cases huv : u = v
  · subst v; rw [← (Finset.mem_filter.mp hu).2, ← (Finset.mem_filter.mp hv).2, hacc u] at hrej
    exact Bool.noConfusion hrej
  · exact DistanceCalculus.projective_effect_mul_effect_eq_zero _
      (fun e => MakingMeasurementsProjective.isProj_kronecker (pauliProj_isProj W e) (.one _)) huv

theorem honest_oriented_rejected_mul (P : AdmissibleParams) {t₁ t₂ : PauliType}
    (h : PauliEdgeOriented t₁ t₂) (z : PauliSpace P) (a b : PauliAnswer P)
    (hrej : pauliWinPredicate P (t₁, pauliCL P t₁ z) (t₂, pauliCL P t₂ z) a b = false) :
    (honestMeasurement P t₁ (pauliCL P t₁ z)).effect a *
      (honestMeasurement P t₂ (pauliCL P t₂ z)).effect b = 0 := by
  classical
  have hpt (W) : pauliPointBlock W (pauliCL P (.point W) z) = pauliPointBlock W z := by cases W <;> rfl
  have hemb (W) (u) : pauliToLd P W (embedLd P W u) = u := by
    funext i; cases W <;> rcases i with (j | ⟨⟩) | j <;> rfl
  rcases h with ⟨W, rfl, rfl | rfl | rfl | rfl⟩ | ⟨W, rfl, rfl⟩ | ⟨W, rfl, rfl⟩
  · have hidem : ldALineCL P.toLdParams (pauliToLd P W (pauliCL P (.aline W) z)) =
        ldALineCL P.toLdParams (pauliToLd P W z) := by
      rw [show pauliToLd P W (pauliCL P (.aline W) z) = _ from hemb W _]
      funext i; rcases i with (j | ⟨⟩) | j
      · exact congrFun (lineRepMap_apply_self _ _) j
      · rfl
      · rfl
    change (placedPauliMeasurement _ _).effect a * (placedPauliMeasurement _ _).effect b = 0
    rw [hpt W, hidem]
    refine placedBasis_rejected_mul P W _ _ _ _ (fun h => ?_) a b hrej
    have hcond : pauliAlinePointCondition P W (pauliCL P (.aline W) z) (pauliCL P (.point W) z)
        (restrictToAxisLine P.toLdParams (aLineDescOf P.toLdParams (ldALineCL P.toLdParams (pauliToLd P W z)))
          (lowDegreeEncoding h)) (lowDegreeEnc h (pauliPointBlock W z)) := by
      intro t ht; rw [hpt W] at ht
      have hk := evalCoefficient_restrictToAxisLine_lowDegreeEncoding P.toLdParams
        (aLineDescOf P.toLdParams (ldALineCL P.toLdParams (pauliToLd P W z))) rfl h t
      have hb : (aLineDescOf P.toLdParams (ldALineCL P.toLdParams (pauliToLd P W z))).base =
          pauliPointBlock W (pauliCL P (.aline W) z) := by cases W <;> exact lineRepMap_apply_self _ _
      have hd : (aLineDescOf P.toLdParams (ldALineCL P.toLdParams (pauliToLd P W z))).direction =
          coordinateDirection (chiIndex P.toLdParams (pauliScalarBlock (pauliCL P (.aline W) z))) := by
        cases W <;> rfl
      rw [hb, hd] at hk; exact ht ▸ hk
    simpa [pauliWinPredicate, validPauliAnswer] using hcond
  · have hidem : ldDLineCL P.toLdParams (pauliToLd P W (pauliCL P (.dline W) z)) =
        ldDLineCL P.toLdParams (pauliToLd P W z) := by
      rw [show pauliToLd P W (pauliCL P (.dline W) z) = _ from hemb W _]
      funext i; rcases i with (j | ⟨⟩) | j
      · change lineRepMap (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
          (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed) (pauliToLd P W z).direction))
          (lineRepMap _ _) j = _
        rw [prefixProjection_idempotent]; exact congrFun (lineRepMap_apply_self _ _) j
      · rfl
      · change prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
          (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed) (pauliToLd P W z).direction) j = _
        rw [prefixProjection_idempotent]; rfl
    change (placedPauliMeasurement _ _).effect a * (placedPauliMeasurement _ _).effect b = 0
    rw [hpt W, hidem]
    refine placedBasis_rejected_mul P W _ _ _ _ (fun h => ?_) a b hrej
    have hcond : pauliDlinePointCondition P W (pauliCL P (.dline W) z) (pauliCL P (.point W) z)
        (restrictToLine P.toLdParams (dLineDescOf P.toLdParams (ldDLineCL P.toLdParams (pauliToLd P W z)))
          (lowDegreeEncoding h)) (lowDegreeEnc h (pauliPointBlock W z)) := by
      intro t ht; rw [hpt W] at ht
      have hk1 := evalCoefficient_restrictToLine P.toLdParams
        (dLineDescOf P.toLdParams (ldDLineCL P.toLdParams (pauliToLd P W z)))
        (lowDegreeEncoding h) (polynomialOnLine_lowDegreeEncoding_natDegree_le P.toLdParams _ h) t
      have hk2 := eval_polynomialOnLine P.toLdParams
        (dLineDescOf P.toLdParams (ldDLineCL P.toLdParams (pauliToLd P W z))) (lowDegreeEncoding h) t
      have hb : (dLineDescOf P.toLdParams (ldDLineCL P.toLdParams (pauliToLd P W z))).base =
          pauliPointBlock W (pauliCL P (.dline W) z) := by
        have hp' : pauliPointBlock W (pauliCL P (.dline W) z) =
            (ldDLineCL P.toLdParams (pauliToLd P W z)).point := by cases W <;> rfl
        rw [hp']
        change lineRepMap (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
          (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed) (pauliToLd P W z).direction))
          (lineRepMap _ _) = _
        rw [prefixProjection_idempotent]; exact lineRepMap_apply_self _ _
      have hd : (dLineDescOf P.toLdParams (ldDLineCL P.toLdParams (pauliToLd P W z))).direction =
          pauliDirectionBlock (pauliCL P (.dline W) z) := prefixProjection_idempotent _ _
      rw [hb, hd] at hk2; exact ht ▸ hk1.trans hk2
    simpa [pauliWinPredicate, validPauliAnswer] using hcond
  · change (placedPauliMeasurement _ _).effect a * (placedPauliMeasurement _ _).effect b = 0
    rw [hpt W]
    refine placedBasis_rejected_mul P W _ _ _ _ (fun h => ?_) a b hrej
    have hc : pauliPointPauliCondition P W (pauliCL P (.point W) z) h
        (lowDegreeEnc h (pauliPointBlock W z)) := hpt W ▸ rfl
    simpa [pauliWinPredicate, validPauliAnswer] using hc
  · change (placedPauliMeasurement _ _).effect a * (placedPauliMeasurement _ _).effect b = 0
    rw [hpt W]
    refine placedBasis_rejected_mul P W _ _ _ _ (fun h => ?_) a b hrej
    have hc : pauliPointPairCondition P W (pauliCL P (.pairW W) z)
        (lowDegreeEnc h (pauliPointBlock W z))
        (pauliTraceBit P (pauliPointBlock W (pauliCL P (.pairW W) z))
          (pauliPairScalar P W (pauliCL P (.pairW W) z)) h) := by
      cases W <;> exact Or.inr rfl
    cases W <;> simpa [pauliWinPredicate, validPauliAnswer] using hc
  · rcases (Bool.eq_false_or_eq_true (validPauliAnswer (.pairW W) a)).symm with hva | hva
    · rw [honestMeasurement_effect_eq_zero_of_invalid P _ _ hva, zero_mul]
    rcases (Bool.eq_false_or_eq_true (validPauliAnswer .pair b)).symm with hvb | hvb
    · rw [honestMeasurement_effect_eq_zero_of_invalid P _ _ hvb, mul_zero]
    obtain ⟨β, rfl⟩ : ∃ c, a = .bit c := by
      cases a <;> first | exact ⟨_, rfl⟩ | exact absurd hva (by simp [validPauliAnswer])
    obtain ⟨bits, rfl⟩ : ∃ c, b = .pairBits c := by
      cases b <;> first | exact ⟨_, rfl⟩ | exact absurd hvb (by simp [validPauliAnswer])
    by_cases hg : pauliPairGamma P (pauliSharedProjection z) = 0
    · have hcond : ¬ pauliPairCondition P W (pauliCL P (.pairW W) z) β bits := fun hc =>
        Bool.noConfusion ((by simpa [pauliWinPredicate, validPauliAnswer] using hc :
          pauliWinPredicate P _ _ _ _ = true).symm.trans hrej)
      have h1 : (honestMeasurement P (.pairW W) (pauliCL P (.pairW W) z)).effect (.bit β) =
          heteroKron ((pauliTraceMeasurement P W (pauliPointBlock W (pauliSharedProjection z))
            (pauliPairScalar P W (pauliSharedProjection z))).effect β) 1 := by
        rw [honestMeasurement, placedPauliMeasurement_effect_eq]
        congr 1
        have hcomp : ((pauliBasisMeasurement W).postprocess
            (fun h => PauliAnswer.bit (P := P) (pauliTraceBit P (pauliPointBlock W (pauliSharedProjection z))
              (pauliPairScalar P W (pauliSharedProjection z)) h))) =
            (pauliTraceMeasurement P W (pauliPointBlock W (pauliSharedProjection z))
              (pauliPairScalar P W (pauliSharedProjection z))).postprocess (PauliAnswer.bit (P := P)) :=
          (Measurement.postprocess_comp _ _ _).symm
        dsimp only [pauliCL]
        rw [hcomp, SandwichProduct.postprocess_effect_of_injective _ _ (by intro _ _; simp)]
      have h2 : (honestMeasurement P .pair (pauliCL P .pair z)).effect (.pairBits bits) =
          heteroKron (pauliPairEffect P (pauliSharedProjection z) bits) 1 := by
        change (honestPairMeasurement P (pauliSharedProjection z)).effect _ = _
        dsimp only [honestPairMeasurement]; rw [dif_pos hg, placedPauliMeasurement_effect_eq,
          SandwichProduct.postprocess_effect_of_injective _ _ (by intro _ _; simp)]; rfl
      rw [h1, h2, heteroKron_mul, one_mul]
      have hz0 {A : Op (PauliRegister P)} (hA : A = 0) : heteroKron A (1 : Op (ZMod 2)) = 0 := by
        rw [hA]; ext; simp [heteroKron, Matrix.kronecker]
      apply hz0
      cases W
      · have hne : β ≠ bits.1 := fun h => hcond (Or.inr h.symm)
        dsimp [pauliPairEffect, pauliPointBlock, pauliPairScalar]
        rw [← mul_assoc, DistanceCalculus.projective_effect_mul_effect_eq_zero _
          (pauliTraceMeasurement_projective P .X _ _) hne, zero_mul]
      · have hne : β ≠ bits.2 := fun h => hcond (Or.inr h.symm)
        dsimp [pauliPairEffect, pauliPointBlock, pauliPairScalar]
        rw [← mul_assoc, ← (pauliTraceMeasurement_effect_commute P (pauliSharedProjection z) hg bits.1 β).eq,
          mul_assoc, DistanceCalculus.projective_effect_mul_effect_eq_zero _
          (pauliTraceMeasurement_projective P .Z _ _) hne, mul_zero]
    · have hc : pauliPairCondition P W (pauliCL P (.pairW W) z) β bits := Or.inl hg
      exact Bool.noConfusion ((by simpa [pauliWinPredicate, validPauliAnswer] using hc :
        pauliWinPredicate P _ _ _ _ = true).symm.trans hrej)
  · rcases (Bool.eq_false_or_eq_true (validPauliAnswer (.point W) a)).symm with hva | hva
    · rw [honestMeasurement_effect_eq_zero_of_invalid P _ _ hva, zero_mul]
    rcases (Bool.eq_false_or_eq_true (validPauliAnswer (.ms (.var (msBasisVar W))) b)).symm with hvb | hvb
    · rw [honestMeasurement_effect_eq_zero_of_invalid P _ _ hvb, mul_zero]
    obtain ⟨u, rfl⟩ : ∃ u, a = .value u := by
      cases a <;> first | exact ⟨_, rfl⟩ | exact absurd hva (by simp [validPauliAnswer])
    obtain ⟨β, rfl⟩ : ∃ c, b = .bit c := by
      cases b <;> first | exact ⟨_, rfl⟩ | exact absurd hvb (by simp [validPauliAnswer])
    by_cases hg : pauliPairGamma P (pauliSharedProjection z) = 0
    · have hc : pauliPointVariableCondition P W (pauliCL P (.ms (.var (msBasisVar W))) z)
          (msBasisVar W) u β := Or.inl hg
      exact Bool.noConfusion ((by simpa [pauliWinPredicate, validPauliAnswer] using hc :
        pauliWinPredicate P _ _ _ _ = true).symm.trans hrej)
    · change (placedPauliMeasurement _ _).effect _ *
        (honestMagicMeasurement P (.var (msBasisVar W)) (pauliSharedProjection z)).effect _ = 0
      rw [hpt W, honestMagicMeasurement_var_eq_placedBasis P (pauliSharedProjection z) hg W]
      refine placedBasis_rejected_mul P W _ _ _ _ (fun h => ?_) _ _ hrej
      have hc : pauliPointVariableCondition P W (pauliCL P (.ms (.var (msBasisVar W))) z)
          (msBasisVar W) (lowDegreeEnc h (pauliPointBlock W z))
          (pauliTraceBit P (pauliPointBlock W (pauliSharedProjection z))
            (pauliPairScalar P W (pauliSharedProjection z)) h) := by
        cases W
        · exact Or.inr (Or.inl ⟨by decide, rfl, rfl⟩)
        · exact Or.inr (Or.inr ⟨by decide, rfl, rfl⟩)
      simpa [pauliWinPredicate, validPauliAnswer] using hc

theorem honest_ms_rejected_mul (P : AdmissibleParams) (z : PauliSpace P)
    {s₁ s₂ : MsType} (hms : Sym2.mk s₁ s₂ ∈ msEdges) (a b : PauliAnswer P)
    (hrej : pauliWinPredicate P (.ms s₁, pauliCL P (.ms s₁) z)
      (.ms s₂, pauliCL P (.ms s₂) z) a b = false) :
    (honestMeasurement P (.ms s₁) (pauliCL P (.ms s₁) z)).effect a *
      (honestMeasurement P (.ms s₂) (pauliCL P (.ms s₂) z)).effect b = 0 := by
  classical
  have hcl (s) : pauliCL P (.ms s) z = pauliSharedProjection z := rfl
  simp only [hcl] at hrej ⊢
  have hsupp : (s₁, s₂) ∈ msGameSymm.μ.support := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hms⟩
  rcases (Bool.eq_false_or_eq_true (validPauliAnswer (.ms s₁) a)).symm with hva | hva
  · rw [honestMeasurement_effect_eq_zero_of_invalid P _ _ hva, zero_mul]
  rcases (Bool.eq_false_or_eq_true (validPauliAnswer (.ms s₂) b)).symm with hvb | hvb
  · rw [honestMeasurement_effect_eq_zero_of_invalid P _ _ hvb, mul_zero]
  obtain ⟨a', rfl⟩ : ∃ c, a = pauliAnswerOfMs c := by
    cases a with
    | msTriple β => exact ⟨.triple β, rfl⟩
    | bit c => exact ⟨.bit c, rfl⟩
    | _ => exact absurd hva (by cases s₁ <;> simp [validPauliAnswer])
  obtain ⟨b', rfl⟩ : ∃ c, b = pauliAnswerOfMs c := by
    cases b with
    | msTriple β => exact ⟨.triple β, rfl⟩
    | bit c => exact ⟨.bit c, rfl⟩
    | _ => exact absurd hvb (by cases s₂ <;> simp [validPauliAnswer])
  by_cases hg : pauliPairGamma P (pauliSharedProjection z) = 0
  · exfalso
    have hpos : pauliWinPredicate P (.ms s₁, pauliSharedProjection z)
        (.ms s₂, pauliSharedProjection z) (pauliAnswerOfMs a') (pauliAnswerOfMs b') = true := by
      clear hrej
      rcases msGame_support_incidence s₁ s₂ hsupp with ⟨i, k, rfl, rfl⟩ | ⟨i, k, rfl, rfl⟩ <;>
        cases a' <;> cases b' <;>
        simp_all [pauliWinPredicate, validPauliAnswer, pauliAnswerOfMs, msWinPredicate]
    exact Bool.noConfusion (hpos.symm.trans hrej)
  · have hmsrej : msWinPredicate s₁ s₂ a' b' = false := by
      rcases Bool.eq_false_or_eq_true (msWinPredicate s₁ s₂ a' b') with hmsw | hmsw
      · exfalso
        have hpos : pauliWinPredicate P (.ms s₁, pauliSharedProjection z)
            (.ms s₂, pauliSharedProjection z) (pauliAnswerOfMs a') (pauliAnswerOfMs b') = true := by
          clear hrej
          rcases msGame_support_incidence s₁ s₂ hsupp with ⟨i, k, rfl, rfl⟩ | ⟨i, k, rfl, rfl⟩ <;>
            cases a' <;> cases b' <;>
            simp_all [pauliWinPredicate, validPauliAnswer, pauliAnswerOfMs, msWinPredicate]
        exact Bool.noConfusion (hpos.symm.trans hrej)
      · exact hmsw
    change (honestMagicMeasurement P s₁ _).effect _ * (honestMagicMeasurement P s₂ _).effect _ = 0
    dsimp only [honestMagicMeasurement]; rw [dif_neg hg, dif_neg hg,
      SandwichProduct.postprocess_effect_of_injective _ _ pauliAnswerOfMs_injective a',
      SandwichProduct.postprocess_effect_of_injective _ _ pauliAnswerOfMs_injective b']
    exact msStrategyMeasurement_rejected_mul_on_support _ _ _
      (fun i k ab c => msCellConstraintJoint_mul _ _
        (obsOf_conjTranspose _ (pauliTraceMeasurement_projective P .X _ _))
        (obsOf_conjTranspose _ (pauliTraceMeasurement_projective P .Z _ _))
        (obsOf_sq _ (pauliTraceMeasurement_projective P .X _ _))
        (obsOf_sq _ (pauliTraceMeasurement_projective P .Z _ _))
        (obsOf_pauliTraceMeasurement_anticommute P _ hg) i k ab c)
      s₁ s₂ hsupp a' b' hmsrej

/-! ### Symmetry of the Pauli basis test and value-one SPCC strategy -/

theorem pauliQuestionDistribution_symm (P : AdmissibleParams) (x y : PauliQuestion P) :
    (pauliQuestionDistribution P).weight (x, y) =
      (pauliQuestionDistribution P).weight (y, x) := by
  classical
  let _ : Nonempty PauliEdge := pauliEdge_nonempty
  let swapE : PauliEdge ≃ PauliEdge :=
    { toFun := fun e => ⟨e.1.swap, by simpa [Sym2.eq_swap] using e.2⟩
      invFun := fun e => ⟨e.1.swap, by simpa [Sym2.eq_swap] using e.2⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
  let eS := swapE.prodCongr (Equiv.refl (PauliSpace P))
  let f : PauliEdge × PauliSpace P → PauliQuestion P × PauliQuestion P :=
    fun s => ((s.1.1.1, pauliCL P s.1.1.1 s.2), (s.1.1.2, pauliCL P s.1.1.2 s.2))
  change ((uniformDistribution _).map f).weight (x, y) =
    ((uniformDistribution _).map f).weight (y, x)
  rw [uniformDistribution_map_weight, uniformDistribution_map_weight]
  refine congrArg (fun n : ℕ => (n : ℝ) * _) (Finset.card_bij (fun s _ => eS s) ?_ ?_ ?_)
  · intro s hs
    have hf : f s = (x, y) := (Finset.mem_filter.mp hs).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Prod.ext (congrArg Prod.snd hf) (congrArg Prod.fst hf)⟩
  · intro _ _ _ _ h; exact eS.injective h
  · intro s hs
    have hf : f s = (y, x) := (Finset.mem_filter.mp hs).2
    exact ⟨eS s, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Prod.ext (congrArg Prod.snd hf) (congrArg Prod.fst hf)⟩, eS.symm_apply_apply s⟩

theorem pauliWinPredicate_symm (P : AdmissibleParams)
    (x y : PauliQuestion P) (a b : PauliAnswer P) :
    pauliWinPredicate P x y a b = pauliWinPredicate P y x b a := by
  obtain ⟨tA, xA⟩ := x; obtain ⟨tB, xB⟩ := y
  dsimp only [pauliWinPredicate]
  by_cases hT : tA = tB
  · subst hT
    rw [ite_eq_left_iff.mpr fun h => absurd rfl h, ite_eq_left_iff.mpr fun h => absurd rfl h,
      Bool.and_comm (validPauliAnswer tA b) (validPauliAnswer tA a)]
    exact congrArg (fun c => if validPauliAnswer tA a && validPauliAnswer tA b then c else false)
      (decide_eq_decide.mpr eq_comm)
  · cases hvA : validPauliAnswer tA a
    · cases validPauliAnswer tB b <;> rfl
    · cases hvB : validPauliAnswer tB b
      · rfl
      · rw [Bool.true_and, ite_eq_left_iff.mpr fun h => absurd rfl h,
          ite_eq_left_iff.mpr fun h => absurd rfl h,
          ite_eq_right_iff.mpr fun h => absurd h hT,
          ite_eq_right_iff.mpr fun h => absurd h.symm hT]
        rcases tA with (_|_)|(_|_)|(_|_)|(_|_)|(_|_)|_|(iA|jA) <;>
          rcases a with uA|fA|gA|bitsA|bitA|trA|hhA <;>
          (try exact Bool.noConfusion hvA) <;>
          rcases tB with (_|_)|(_|_)|(_|_)|(_|_)|(_|_)|_|(iB|jB) <;>
          rcases b with uB|fB|gB|bitsB|bitB|trB|hhB <;>
          (try exact Bool.noConfusion hvB) <;> rfl

@[reducible] def pauliBasisTestSymm (P : AdmissibleParams) : SymmetricGame where
  Question := PauliQuestion P
  Answer := PauliAnswer P
  μ := pauliQuestionDistribution P
  μ_prob := (pauliBasisTest P).μ_prob
  μ_symm := pauliQuestionDistribution_symm P
  decide := pauliWinPredicate P
  decide_symm := pauliWinPredicate_symm P

@[reducible] def honestStrategy (P : AdmissibleParams) : SymmetricStrategy (pauliBasisTestSymm P) where
  ι := HonestIndex P
  ψ := eprState (HonestIndex P)
  ψ_norm := eprState_norm (HonestIndex P)
  ψ_swap := reindexState_prodComm_eprState (HonestIndex P)
  M q := honestMeasurement P q.1 q.2

theorem honestMeasurement_rejected_mul (P : AdmissibleParams)
    (x y : PauliQuestion P) (hxy : 0 < (pauliQuestionDistribution P).weight (x, y))
    (a b : PauliAnswer P) (hrej : pauliWinPredicate P x y a b = false) :
    (honestMeasurement P x.1 x.2).effect a * (honestMeasurement P y.1 y.2).effect b = 0 := by
  classical
  obtain ⟨z, hedge, hx, hy⟩ := pauliQuestionDistribution_pos_incidence P x y hxy
  obtain ⟨t₁, x₁⟩ := x; obtain ⟨t₂, x₂⟩ := y
  dsimp only at hx hy hedge ⊢; subst hx hy
  rcases pauliEdges_cases hedge with rfl | ⟨s₁, s₂, rfl, rfl, hms⟩ | hor | hor
  · rcases (Bool.eq_false_or_eq_true (validPauliAnswer (P := P) t₁ a)).symm with hva | hva
    · rw [honestMeasurement_effect_eq_zero_of_invalid P _ _ hva, zero_mul]
    have hab : a ≠ b := by
      rintro rfl; simp [pauliWinPredicate, hva] at hrej
    exact DistanceCalculus.projective_effect_mul_effect_eq_zero _
      (honestMeasurement_projective P t₁ _) hab
  · exact honest_ms_rejected_mul P z hms a b hrej
  · exact honest_oriented_rejected_mul P hor z a b hrej
  · rw [← (honestMeasurement_commute_of_oriented P hor z b a).eq]
    exact honest_oriented_rejected_mul P hor z b a (by rwa [pauliWinPredicate_symm])

theorem exists_spcc_value_one (P : AdmissibleParams) :
    ∃ S : SymmetricStrategy (pauliBasisTestSymm P),
      S.IsSPCC ∧ S.toStrategy.value = 1 := by
  classical
  refine ⟨honestStrategy P, ⟨fun x => honestMeasurement_projective P x.1 x.2,
    fun x a => epr_action_eq_of_transpose _ (honestMeasurement_effect_transpose P x.1 x.2 a),
    honestMeasurement_commuting P⟩, ?_⟩
  have hborn (x y) (hxy : 0 < (pauliQuestionDistribution P).weight (x, y)) (a b)
      (hrej : pauliWinPredicate P x y a b = false) :
      outcomeWeight (honestStrategy P).toStrategy x y a b = 0 := by
    have hzero := heteroKron_mulVec_epr_eq_zero_of_mul_eq_zero _ _
      (honestMeasurement_effect_transpose P y.1 y.2 b)
      (honestMeasurement_rejected_mul P x y hxy a b hrej)
    have hact : applyOperatorToState
        (heteroKron ((honestMeasurement P x.1 x.2).effect a) ((honestMeasurement P y.1 y.2).effect b))
        (eprState (HonestIndex P)) = 0 := by
      rw [applyOperatorToState, Matrix.toLpLin_apply, hzero]; rfl
    change (inner ℂ (eprState (HonestIndex P))
      (applyOperatorToState
        (heteroKron ((honestMeasurement P x.1 x.2).effect a) ((honestMeasurement P y.1 y.2).effect b))
        (eprState (HonestIndex P)))).re = 0
    rw [hact]; simp
  change avgOver (pauliQuestionDistribution P) (fun xy =>
    ∑ a : PauliAnswer P, ∑ b : PauliAnswer P,
      if pauliWinPredicate P xy.1 xy.2 a b then
        outcomeWeight (honestStrategy P).toStrategy xy.1 xy.2 a b else 0) = 1
  have hcongr : avgOver (pauliQuestionDistribution P) (fun xy =>
      ∑ a : PauliAnswer P, ∑ b : PauliAnswer P,
        if pauliWinPredicate P xy.1 xy.2 a b then
          outcomeWeight (honestStrategy P).toStrategy xy.1 xy.2 a b else 0) =
      avgOver (pauliQuestionDistribution P) (fun _ => 1) := by
    simp only [avgOver]; refine Finset.sum_congr rfl fun xy _ => ?_
    rcases lt_or_eq_of_le ((pauliQuestionDistribution P).nonnegative xy) with hpos | hzero
    · rw [← outcomeWeight_sum_eq_one (honestStrategy P).toStrategy xy.1 xy.2]
      congr 1; refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      by_cases hab : pauliWinPredicate P xy.1 xy.2 a b = true
      · simp [hab]
      · have hab' := Bool.eq_false_of_not_eq_true hab
        rw [hborn xy.1 xy.2 hpos a b hab']; simp [hab']
    · rw [← hzero, zero_mul, zero_mul]
  rw [hcongr]
  exact avgOver_const_of_isProbability _ (pauliBasisTestSymm P).μ_prob 1

end

end MIPStarRE.QPBT
