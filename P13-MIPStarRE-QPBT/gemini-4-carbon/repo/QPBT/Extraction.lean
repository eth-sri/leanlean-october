module

public import QPBT.Algebra.Decoding
public import QPBT.Combining.Apply
public import QPBT.Combining.Points
public import QPBT.Combining.Lines
public import QPBT.Observables.IdealPointConsistency
public import QPBT.Games.SupportMass
public import QPBT.Games.DistanceTheorems.TensorConsistency
public import QPBT.Games.Sandwich.Support
public import QPBT.Test.MagicSquareTheorems.Rigidity.Reflections
public import QPBT.Test.MagicSquareTheorems.Rigidity.JointState
public import QPBT.Test.MagicSquareTheorems.Rigidity.GroundSlice
public import QPBT.Test.MagicSquareTheorems.Rigidity.Transfer
public import QPBT.Quantum.ControlledUnitary
public import QPBT.ExplicitConstants
public import QPBT.Test.SoundnessDefs

/-! # Consolidated Pauli extraction and swap unitaries -/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.LDT.Preliminaries MIPStarRE.Quantum DistanceCalculus ProjectiveSetting WinImplications

noncomputable section

@[simp] theorem reindexOp_apply_extr {ι ι' : Type*} (e : ι ≃ ι') (M : Op ι') (i j : ι) :
    reindexOp e M i j = M (e i) (e j) := rfl

/-! ## Heterogeneous extraction registers and coarse-grained projectors -/

abbrev ExtractionBlock (P : AdmissibleParams) (ι : Type*) :=
  (ι × PauliRegister P) × PauliRegister P

abbrev ExtractionRegisters (P : AdmissibleParams) (ιA ιB : Type*) :=
  ExtractionBlock P ιA × ExtractionBlock P ιB

abbrev ExtractionAuxRegisters (P : AdmissibleParams) (ιA ιB : Type*) :=
  (ιA × PauliRegister P) × (ιB × PauliRegister P)

def sixRegExtractionEquiv (P : AdmissibleParams) (ιA ιB : Type*) :
    SixReg P ιA ιB ≃ ExtractionRegisters P ιA ιB where
  toFun p := (((p.1.1, p.1.2.1), p.1.2.2), ((p.2.1, p.2.2.1), p.2.2.2))
  invFun p := ((p.1.1.1, (p.1.1.2, p.1.2)), (p.2.1.1, (p.2.1.2, p.2.2)))
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

def extractionIdealShuffle (P : AdmissibleParams) (ιA ιB : Type*) :
    (ExtractionAuxRegisters P ιA ιB × (PauliRegister P × PauliRegister P)) ≃ SixReg P ιA ιB where
  toFun p := ((p.1.1.1, (p.1.1.2, p.2.1)), (p.1.2.1, (p.1.2.2, p.2.2)))
  invFun p := (((p.1.1, p.1.2.1), (p.2.1, p.2.2.1)), (p.1.2.2, p.2.2.2))
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

def extractionEprFirstEquiv (P : AdmissibleParams) (ιA ιB : Type*) :
    SixReg P ιA ιB ≃
      (PauliRegister P × (ιA × PauliRegister P)) × (PauliRegister P × (ιB × PauliRegister P)) :=
  (sixRegExtractionEquiv P ιA ιB).trans
    (Equiv.prodCongr (Equiv.prodComm _ _) (Equiv.prodComm _ _))

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

def placeSide (S : ProjectiveSetting P ε) (side : PlayerSide)
    (O : Op (ExtractionBlock P (S.LocalSpace side))) :
    Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
  match side with
  | .alice => reindexOp (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB) (heteroKron O 1)
  | .bob => reindexOp (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB) (heteroKron 1 O)

def onPlayer (S : ProjectiveSetting P ε) (side : PlayerSide)
    (O : Op (S.LocalSpace side)) : Op (ExtractionBlock P (S.LocalSpace side)) :=
  heteroKron (heteroKron O 1) 1

def placePlayer (S : ProjectiveSetting P ε) (side : PlayerSide)
    (O : Op (S.LocalSpace side)) : Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
  match side with
  | .alice => S.place .AA' (heteroKron O 1)
  | .bob => S.place .BB' (heteroKron O 1)

def placeExtractedRegister (S : ProjectiveSetting P ε) (side : PlayerSide)
    (O : Op (PauliRegister P)) : Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
  match side with
  | .alice => S.place .BA'' (heteroKron (1 : Op S.toStrategy.ιB) O)
  | .bob => S.place .AB'' (heteroKron (1 : Op S.toStrategy.ιA) O)

def placeBoth (S : ProjectiveSetting P ε)
    (VA : Op (ExtractionBlock P S.toStrategy.ιA))
    (VB : Op (ExtractionBlock P S.toStrategy.ιB)) :
    Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
  reindexOp (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB) (heteroKron VA VB)

def applyBoth (S : ProjectiveSetting P ε)
    (VA : Op (ExtractionBlock P S.toStrategy.ιA))
    (VB : Op (ExtractionBlock P S.toStrategy.ιB))
    (ψ : EuclideanSpace ℂ (SixReg P S.toStrategy.ιA S.toStrategy.ιB)) :
    EuclideanSpace ℂ (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
  applyOperatorToState (S.placeBoth VA VB) ψ

def idealExpState (S : ProjectiveSetting P ε)
    (aux : EuclideanSpace ℂ (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB)) :
    EuclideanSpace ℂ (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
  open Classical in
  reindexState (extractionIdealShuffle P S.toStrategy.ιA S.toStrategy.ιB)
    (vecTensor aux (eprState (PauliRegister P)))

end ProjectiveSetting

def bracketOp {α β ι : Type*} [Fintype α] [DecidableEq β]
    (N : α → Op ι) (f : α → β) (b : β) : Op ι :=
  ∑ a ∈ Finset.univ.filter (fun a => f a = b), N a

def tauDotProj {P : AdmissibleParams} (W : PauliKind)
    (u : PauliRegister P) (a : PauliScalar P) : Op (PauliRegister P) :=
  bracketOp (pauliProj W) (fun h => dotProduct h u) a

theorem tauDotProj_isProj {P : AdmissibleParams} (W : PauliKind)
    (u : PauliRegister P) (a : PauliScalar P) : IsProj (tauDotProj W u a) := by
  classical
  let U : Op (PauliRegister P) := fun r l => pauliVec W l r
  have hUt (l r : PauliRegister P) : Uᴴ l r = star (pauliVec W l r) := rfl
  have hU : U * Uᴴ = 1 := by
    rw [← sum_pauliProj_eq_one W]; ext r c; rw [Matrix.mul_apply]
    simp only [U, hUt, pauliProj, Matrix.sum_apply, Matrix.vecMulVec_apply]
  let D : Op (PauliRegister P) := Matrix.diagonal fun l => if dotProduct l u = a then (1 : ℂ) else 0
  have hD : IsProj D := ⟨by
    change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal]; congr 1; funext l; split_ifs <;> simp,
    by change Dᴴ = D; simp [D, Matrix.diagonal_conjTranspose]⟩
  have hc : tauDotProj W u a = U * D * Uᴴ := by
    ext r c; simp only [tauDotProj, bracketOp, Matrix.sum_apply, pauliProj, Matrix.vecMulVec_apply]
    rw [Matrix.mul_apply]; simp only [D, Matrix.mul_diagonal]
    simp [U, hUt, Finset.sum_filter, mul_ite, ite_mul]
  rw [hc]
  exact hD.map (Unitary.conjStarAlgAut ℂ (Op (PauliRegister P)) ⟨U, Matrix.mem_unitaryGroup_iff.mpr hU⟩)

theorem sum_tauDotProj_eq_one {P : AdmissibleParams} (W : PauliKind) (u : PauliRegister P) :
    ∑ a : PauliScalar P, tauDotProj W u a = 1 := by
  classical
  unfold tauDotProj bracketOp
  exact (Finset.sum_fiberwise _ _ _).trans (sum_pauliProj_eq_one W)

def conjBy {ι : Type*} [Fintype ι] (V N : Op ι) : Op ι := V * N * Vᴴ

def deltaConstructPaulis (C epsilon deltaG : ℝ) (m d q : ℕ) : ℝ :=
  C * (deltaG + Real.sqrt epsilon + ((m * d : ℕ) : ℝ) / (q : ℝ))

def deltaExtract (C deltaS : ℝ) (m d q : ℕ) : ℝ :=
  C * (Real.rpow deltaS (1 / 4 : ℝ) + ((m * d : ℕ) : ℝ) / (q : ℝ))

/-! ## Pulled-apart observables and swap conjugation -/

def PauliKind.selectPoly {P : AdmissibleParams} : PauliKind → PolyPair P → Poly P
  | .X, p => p.1
  | .Z, p => p.2

namespace GlobalPairWitness

def marginalPoly {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta)
    (side : PlayerSide) (W : PauliKind) : Measurement (Poly P) (S.ExpandedLocalSpace side) :=
  (w.Smeas side).postprocess W.selectPoly

theorem marginalPoly_isProjective {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta)
    (side : PlayerSide) (W : PauliKind) : Measurement.IsProjective (w.marginalPoly side W) :=
  SandwichProduct.postprocess_isProjective (w.Smeas side) (w.projective side) W.selectPoly

theorem marginalPoly_postprocess_eval {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (side : PlayerSide) (W : PauliKind) (point : Fin P.m → PauliScalar P) :
    (w.marginalPoly side W).postprocess (fun poly => MvPolynomial.eval point poly.1) =
      (w.Smeas side).postprocess (evalAt W point) := by
  rw [marginalPoly, Measurement.postprocess_comp]; cases W <;> rfl

end GlobalPairWitness

def tildeM {P : AdmissibleParams} {epsilon delta : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S delta) (side : PlayerSide) (W : PauliKind)
    (u : PauliRegister P) (a : PauliScalar P) : Op (ExtractionBlock P (S.LocalSpace side)) :=
  ∑ g : Poly P, heteroKron ((w.marginalPoly side W).effect g)
    (tauDotProj W u (dotProduct (decodeFq g) u - a))

theorem tildeM_isProj {P : AdmissibleParams} {epsilon delta : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S delta) (side : PlayerSide) (W : PauliKind)
    (u : PauliRegister P) (a : PauliScalar P) : IsProj (tildeM w side W u a) := by
  classical
  have hp (g : Poly P) := MakingMeasurementsProjective.isProj_kronecker
    (w.marginalPoly_isProjective side W g) (tauDotProj_isProj W u (dotProduct (decodeFq g) u - a))
  refine ⟨?_, ?_⟩
  · change (∑ g, _) * (∑ g, _) = _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Matrix.mul_sum, Finset.sum_eq_single g]
    · exact (hp g).isIdempotentElem
    · intro g' _ hg'
      rw [heteroKron_mul, MagicSquareRigidity.mul_eq_zero_of_isProj_family
        (w.marginalPoly_isProjective side W) (w.marginalPoly side W).sum_le_one hg'.symm]
      simp [heteroKron]
    · intro hg; exact (hg (Finset.mem_univ g)).elim
  · change (∑ g, _)ᴴ = _; rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun g _ => (hp g).isSelfAdjoint

theorem sum_tildeM_eq_one {P : AdmissibleParams} {epsilon delta : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S delta) (side : PlayerSide) (W : PauliKind) (u : PauliRegister P) :
    ∑ a : PauliScalar P, tildeM w side W u a = 1 := by
  classical
  simp only [tildeM]; rw [Finset.sum_comm]
  have hs (g : Poly P) : ∑ a, tauDotProj W u (dotProduct (decodeFq g) u - a) = 1 :=
    ((Equiv.subLeft _).sum_comp (tauDotProj W u)).trans (sum_tauDotProj_eq_one W u)
  simp_rw [← DistanceCalculus.heteroKron_finset_sum_right, hs,
    ← DistanceCalculus.heteroKron_finset_sum_left, (w.marginalPoly side W).sum_eq_one,
    heteroKron_one_one]

def tildeObs {P : AdmissibleParams} {epsilon delta : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S delta) (side : PlayerSide) (W : PauliKind)
    (u : PauliRegister P) (j : Fin P.model.basisDim) :
    Op (ExtractionBlock P (S.LocalSpace side)) :=
  ∑ a : PauliScalar P, phaseSign (fixedBinTrace P.model (P.model.basis j * a)) • tildeM w side W u a

theorem sum_phaseSign_tauDotProj_sub {P : AdmissibleParams} (W : PauliKind)
    (v : PauliRegister P) (c o : PauliScalar P) :
    (∑ a : PauliScalar P, phaseSign (fixedBinTrace P.model (c * a)) • tauDotProj W v (o - a)) =
      phaseSign (fixedBinTrace P.model (c * o)) • tauObservable W (c • v) := by
  classical
  have h1 : (∑ a : PauliScalar P, phaseSign (fixedBinTrace P.model (c * a)) • tauDotProj W v (o - a)) =
      ∑ a, phaseSign (fixedBinTrace P.model (c * (o - a))) • tauDotProj W v a := by
    simpa using ((Equiv.subLeft o).sum_comp
      (fun a => phaseSign (fixedBinTrace P.model (c * a)) • tauDotProj W v (o - a))).symm
  rw [h1]; simp only [tauDotProj, bracketOp, Finset.smul_sum]
  have h2 : (∑ a, ∑ x ∈ Finset.univ.filter (fun l => dotProduct l v = a),
      phaseSign (fixedBinTrace P.model (c * (o - a))) • pauliProj W x) =
      ∑ l, phaseSign (fixedBinTrace P.model (c * (o - dotProduct l v))) • pauliProj W l :=
    (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l hl => by
      rw [(Finset.mem_filter.mp hl).2]).trans (Finset.sum_fiberwise _ _ _)
  rw [h2, tauObservable_eq_sum_pauliProj, Finset.smul_sum]
  have hps (x y : ZMod 2) : phaseSign (x - y) = phaseSign x * phaseSign y := by
    rw [sub_eq_add_neg, ZMod.neg_eq_self_mod_two, phaseSign_add]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_smul, smul_dotProduct, smul_eq_mul, dotProduct_comm v l]
  congr 1
  rw [mul_sub, fixedBinTrace, map_sub]
  exact hps _ _

theorem tildeObs_eq_heteroKron {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta)
    (side : PlayerSide) (W : PauliKind) (u : PauliRegister P) (j : Fin P.model.basisDim) :
    tildeObs w side W u j =
      heteroKron (∑ p : PolyPair P,
        phaseSign (fixedBinTrace P.model (P.model.basis j * dotProduct (decodeFq (W.selectPoly p)) u)) •
          (w.Smeas side).effect p) (tauObservable W (P.model.basis j • u)) := by
  classical
  simp only [tildeObs, tildeM, Finset.smul_sum]; rw [Finset.sum_comm]
  have h1 (g : Poly P) : (∑ a, phaseSign (fixedBinTrace P.model (P.model.basis j * a)) •
      heteroKron ((w.marginalPoly side W).effect g) (tauDotProj W u (dotProduct (decodeFq g) u - a))) =
      heteroKron (phaseSign (fixedBinTrace P.model (P.model.basis j * dotProduct (decodeFq g) u)) •
        (w.marginalPoly side W).effect g) (tauObservable W (P.model.basis j • u)) := by
    simp_rw [← MagicSquareRigidity.heteroKron_smul_right]
    rw [← DistanceCalculus.heteroKron_finset_sum_right, sum_phaseSign_tauDotProj_sub]
    simp [heteroKron, Matrix.kronecker, Matrix.kronecker_smul, Matrix.smul_kronecker]
  simp_rw [h1, ← DistanceCalculus.heteroKron_finset_sum_left]; congr 1
  simp only [GlobalPairWitness.marginalPoly, Measurement.postprocess_effect, Finset.smul_sum]
  rw [← Finset.sum_fiberwise Finset.univ W.selectPoly
    (fun p => phaseSign (fixedBinTrace P.model
      (P.model.basis j * dotProduct (decodeFq (W.selectPoly p)) u)) • (w.Smeas side).effect p)]
  exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun p hp => by
    rw [(Finset.mem_filter.mp hp).2]

theorem swapPauli_mul_conjTranspose {P : AdmissibleParams} (p : PolyPair P) :
    (tauObservable .X (decodeFq p.2) * tauObservable .Z (decodeFq p.1)) *
      (tauObservable .X (decodeFq p.2) * tauObservable .Z (decodeFq p.1))ᴴ = 1 := by
  rw [Matrix.conjTranspose_mul, tauObservable_conjTranspose, tauObservable_conjTranspose,
    ← Matrix.mul_assoc, Matrix.mul_assoc (tauObservable .X (decodeFq p.2)), tauObservable_sq,
    Matrix.mul_one, tauObservable_sq]

theorem swapPauli_conj_tauObservable {P : AdmissibleParams}
    (p : PolyPair P) (W : PauliKind) (u : PauliRegister P) :
    conjBy (tauObservable .X (decodeFq p.2) * tauObservable .Z (decodeFq p.1)) (tauObservable W u) =
      phaseSign (fixedBinTrace P.model (dotProduct (decodeFq (W.selectPoly p)) u)) •
        tauObservable W u := by
  have hm : (tauObservable .X (decodeFq p.2) * tauObservable .Z (decodeFq p.1)) * tauObservable W u =
      phaseSign (fixedBinTrace P.model (dotProduct (decodeFq (W.selectPoly p)) u)) •
        (tauObservable W u * (tauObservable .X (decodeFq p.2) * tauObservable .Z (decodeFq p.1))) := by
    cases W
    · have hc : tauObservable .X (decodeFq p.2) * tauObservable .X u =
          tauObservable .X u * tauObservable .X (decodeFq p.2) := by
        rw [tauObservable_mul, tauObservable_mul, add_comm]
      have hx := congrArg (fun A : Op (PauliRegister P) =>
        phaseSign (binTrace (PauliScalar P) (dotProduct u (decodeFq p.1))) • A)
        (tauObservable_X_mul_Z u (decodeFq p.1))
      simp only [smul_smul, phaseSign_mul_self, one_smul] at hx
      simp only [PauliKind.selectPoly, fixedBinTrace]; rw [dotProduct_comm (decodeFq p.1) u]
      rw [Matrix.mul_assoc, ← hx, Matrix.mul_smul, ← Matrix.mul_assoc, hc, Matrix.mul_assoc]
    · have hc : tauObservable .Z (decodeFq p.1) * tauObservable .Z u =
          tauObservable .Z u * tauObservable .Z (decodeFq p.1) := by
        rw [tauObservable_mul, tauObservable_mul, add_comm]
      simp only [PauliKind.selectPoly, fixedBinTrace]
      rw [Matrix.mul_assoc, hc, ← Matrix.mul_assoc, tauObservable_X_mul_Z, Matrix.smul_mul,
        Matrix.mul_assoc]
  rw [conjBy, hm, Matrix.smul_mul, Matrix.mul_assoc, swapPauli_mul_conjTranspose, Matrix.mul_one]

theorem swapPauli_conj_tauDotProj {P : AdmissibleParams}
    (p : PolyPair P) (W : PauliKind) (u : PauliRegister P) (a : PauliScalar P) :
    conjBy (tauObservable .X (decodeFq p.2) * tauObservable .Z (decodeFq p.1)) (tauDotProj W u a) =
      tauDotProj W u (a + dotProduct (decodeFq (W.selectPoly p)) u) := by
  classical
  have hp (h : PauliRegister P) :
      conjBy (tauObservable .X (decodeFq p.2) * tauObservable .Z (decodeFq p.1)) (pauliProj W h) =
        pauliProj W (h + decodeFq (W.selectPoly p)) := by
    rw [pauliProj_eq_avg_tauObservable, conjBy, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_sum, Finset.sum_mul, pauliProj_eq_avg_tauObservable]; congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul]
    change _ • conjBy _ _ = _
    rw [swapPauli_conj_tauObservable, smul_smul]; congr 1
    rw [fixedBinTrace, ← phaseSign_add, ← map_add, dotProduct_comm (decodeFq (W.selectPoly p)) v,
      dotProduct_add]
  simp only [tauDotProj, bracketOp, conjBy, Matrix.mul_sum, Finset.sum_mul]
  change (∑ h ∈ Finset.univ.filter (fun h => dotProduct h u = a), conjBy _ (pauliProj W h)) = _
  simp_rw [hp]
  exact Finset.sum_equiv (Equiv.addRight (decodeFq (W.selectPoly p)))
    (fun h => by simp [add_dotProduct]) fun _ _ => rfl

def swapUnitary {P : AdmissibleParams} {epsilon delta : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S delta) (side : PlayerSide) :
    Op (ExtractionBlock P (S.LocalSpace side)) :=
  ∑ p : PolyPair P, heteroKron ((w.Smeas side).effect p)
    (tauObservable .X (decodeFq p.2) * tauObservable .Z (decodeFq p.1))

theorem swapUnitary_mul_conjTranspose {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta) (side : PlayerSide) :
    swapUnitary w side * (swapUnitary w side)ᴴ = 1 := by
  classical
  apply sum_heteroKron_mul_conjTranspose (w.Smeas side) (w.projective side)
  exact swapPauli_mul_conjTranspose

theorem conjTranspose_mul_swapUnitary {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta) (side : PlayerSide) :
    (swapUnitary w side)ᴴ * swapUnitary w side = 1 :=
  mul_eq_one_comm.mp (swapUnitary_mul_conjTranspose w side)

theorem swapUnitary_conj_controlled {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta) (side : PlayerSide)
    (R : PolyPair P → Op (PauliRegister P)) :
    conjBy (swapUnitary w side) (∑ p, heteroKron ((w.Smeas side).effect p) (R p)) =
      ∑ p, heteroKron ((w.Smeas side).effect p)
        (conjBy (tauObservable .X (decodeFq p.2) * tauObservable .Z (decodeFq p.1)) (R p)) := by
  have hs (p : PolyPair P) : ((w.Smeas side).effect p)ᴴ = (w.Smeas side).effect p :=
    (w.projective side p).isSelfAdjoint
  simp only [conjBy, swapUnitary, Matrix.conjTranspose_sum,
    MagicSquareRigidity.heteroKron_conjTranspose, hs]
  rw [sum_heteroKron_mul_sum_heteroKron (w.Smeas side) (w.projective side),
    sum_heteroKron_mul_sum_heteroKron (w.Smeas side) (w.projective side)]

theorem swapUnitary_conj_tildeObs {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta) (side : PlayerSide)
    (W : PauliKind) (u : PauliRegister P) (j : Fin P.model.basisDim) :
    conjBy (swapUnitary w side) (tildeObs w side W u j) =
      heteroKron (1 : Op (S.ExpandedLocalSpace side)) (tauObservable W (P.model.basis j • u)) := by
  classical
  rw [tildeObs_eq_heteroKron, DistanceCalculus.heteroKron_finset_sum_left]
  simp_rw [MagicSquareRigidity.heteroKron_smul_left, ← MagicSquareRigidity.heteroKron_smul_right]
  rw [swapUnitary_conj_controlled]
  have hc (p : PolyPair P) :
      conjBy (tauObservable .X (decodeFq p.2) * tauObservable .Z (decodeFq p.1))
        (phaseSign (fixedBinTrace P.model (P.model.basis j * dotProduct (decodeFq (W.selectPoly p)) u)) •
          tauObservable W (P.model.basis j • u)) =
        tauObservable W (P.model.basis j • u) := by
    rw [conjBy, Matrix.mul_smul, Matrix.smul_mul]
    change _ • conjBy _ _ = _
    rw [swapPauli_conj_tauObservable, smul_smul, dotProduct_smul, smul_eq_mul,
      phaseSign_mul_self, one_smul]
  simp_rw [hc]; rw [← DistanceCalculus.heteroKron_finset_sum_left, (w.Smeas side).sum_eq_one]

theorem swapUnitary_conj_tildeM {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta) (side : PlayerSide)
    (W : PauliKind) (u : Fin P.m → PauliScalar P) (a : PauliScalar P) :
    conjBy (swapUnitary w side) (tildeM w side W (indicatorVec u) a) =
      heteroKron (1 : Op (S.ExpandedLocalSpace side))
        (bracketOp (pauliProj W) (fun h => lowDegreeEnc h u) a) := by
  classical
  have hM : tildeM w side W (indicatorVec u) a =
      ∑ p : PolyPair P, heteroKron ((w.Smeas side).effect p)
        (tauDotProj W (indicatorVec u) (dotProduct (decodeFq (W.selectPoly p)) (indicatorVec u) - a)) := by
    simp only [tildeM, GlobalPairWitness.marginalPoly, Measurement.postprocess_effect]
    simp_rw [DistanceCalculus.heteroKron_finset_sum_left]
    rw [← Finset.sum_fiberwise Finset.univ W.selectPoly (fun p => heteroKron ((w.Smeas side).effect p)
      (tauDotProj W (indicatorVec u) (dotProduct (decodeFq (W.selectPoly p)) (indicatorVec u) - a)))]
    exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun p hp => by
      rw [(Finset.mem_filter.mp hp).2]
  have hc (b : PauliScalar P) : b - a + b = a := by
    letI : CharP (PauliScalar P) 2 :=
      (Algebra.charP_iff (ZMod 2) (PauliScalar P) 2).mp (ZMod.charP 2)
    rw [sub_eq_add_neg, CharTwo.neg_eq, add_right_comm, CharTwo.add_self_eq_zero, zero_add]
  rw [hM, swapUnitary_conj_controlled]; simp_rw [swapPauli_conj_tauDotProj, hc]
  rw [← DistanceCalculus.heteroKron_finset_sum_left, (w.Smeas side).sum_eq_one]
  simp only [tauDotProj, bracketOp, lowDegreeEnc_eq_dotProduct]

/-! ## EPR correlation projection, auxiliary state, and uniform bounds -/

namespace Extraction

section Correlation
variable {K ι : Type*} [Field K] [Fintype K] [DecidableEq K] [Algebra (ZMod 2) K]
  [Fintype ι] [DecidableEq ι]

def pauliCorrelation (W : PauliKind) : Op ((ι → K) × (ι → K)) :=
  (Fintype.card (ι → K) : ℂ)⁻¹ • ∑ u : ι → K, heteroKron (tauObservable W u) (tauObservable W u)

theorem pauliCorrelation_Z_apply (x y : (ι → K) × (ι → K)) :
    pauliCorrelation .Z x y = if x = y ∧ y.1 = y.2 then 1 else 0 := by
  have havg (v : ι → K) : (Fintype.card (ι → K) : ℂ)⁻¹ *
      ∑ u : ι → K, phaseSign (binTrace K (dotProduct u v)) = if v = 0 then 1 else 0 := by
    have h := congrArg (fun A : Op (ι → K) => A v v) (pauliProj_eq_avg_tauObservable .Z (0 : ι → K))
    have hv : pauliProj .Z (0 : ι → K) v v = if v = 0 then 1 else 0 := by
      change (∏ i, if v i = 0 then (1 : ℂ) else 0) * star (∏ i, if v i = 0 then (1 : ℂ) else 0) = _
      simp only [Fintype.prod_boole, ← funext_iff]
      change (if v = 0 then (1 : ℂ) else 0) * star (if v = 0 then 1 else 0) = _
      split <;> simp
    simp only [dotProduct_zero, map_zero, phaseSign, ite_true, one_smul] at h
    rw [hv] at h; simpa only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
      tauObservable_Z_apply, ite_true, one_mul] using h.symm
  simp only [pauliCorrelation, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply]
  simp_rw [tauObservable_Z_apply]
  by_cases hxy : x = y
  · subst x; simp only [ite_true, true_and]
    simp_rw [show ∀ u : ι → K, phaseSign (binTrace K (dotProduct u y.1)) *
      phaseSign (binTrace K (dotProduct u y.2)) =
      phaseSign (binTrace K (dotProduct u (y.1 + y.2))) from fun u => by
        rw [← phaseSign_add, dotProduct_add, map_add]]
    rw [havg]
    letI : CharP K 2 := (Algebra.charP_iff (ZMod 2) K 2).mp (ZMod.charP 2)
    simp only [funext_iff, Pi.add_apply, Pi.zero_apply, CharTwo.add_eq_zero]
  · have h : x.1 ≠ y.1 ∨ x.2 ≠ y.2 := by
      by_contra hc; push Not at hc; exact hxy (Prod.ext hc.1 hc.2)
    rcases h with h | h <;> simp [h, hxy]

theorem pauliCorrelation_mul_eq_epr :
    pauliCorrelation (K := K) (ι := ι) .X * pauliCorrelation .Z =
      Matrix.vecMulVec (fun x => eprState (ι → K) x) (fun y => star (eprState (ι → K) y)) := by
  have hX (x : (ι → K) × (ι → K)) (a : ι → K) :
      pauliCorrelation .X x (a, a) = if x.1 = x.2 then (Fintype.card (ι → K) : ℂ)⁻¹ else 0 := by
    simp only [pauliCorrelation, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
      heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply]
    simp_rw [tauObservable_X_apply]
    rw [Finset.sum_eq_single (x.1 - a)]
    · simp [add_sub_cancel, eq_comm]
    · intro u _ hu; simp [show x.1 ≠ a + u from fun h => hu (by rw [h, add_sub_cancel_left])]
    · simp
  ext x y; rw [Matrix.mul_apply]; simp_rw [pauliCorrelation_Z_apply]
  rw [Finset.sum_eq_single y]
  · by_cases hy : y.1 = y.2
    · rcases y with ⟨a, b⟩; dsimp only at hy; subst b
      rw [if_pos ⟨rfl, rfl⟩, mul_one, hX]
      change (if x.1 = x.2 then (Fintype.card (ι → K) : ℂ)⁻¹ else 0) =
        (if x.1 = x.2 then (Real.sqrt (Fintype.card (ι → K) : ℝ) : ℂ)⁻¹ else 0) *
          star (if a = a then (Real.sqrt (Fintype.card (ι → K) : ℝ) : ℂ)⁻¹ else 0)
      by_cases hx : x.1 = x.2
      · rw [if_pos hx, if_pos hx, if_pos rfl]; exact (inv_sqrt_natCast_mul_conj _).symm
      · simp [hx]
    · simp [hy, Matrix.vecMulVec_apply, eprState]
  · intro z _ hz; simp [hz]
  · simp

theorem norm_heteroKron_pauliCorrelation_apply_le {R : Type*} [Fintype R] [DecidableEq R]
    (W : PauliKind) (ψ : EuclideanSpace ℂ (R × ((ι → K) × (ι → K)))) :
    ‖applyOperatorToState (heteroKron (1 : Op R) (pauliCorrelation W)) ψ‖ ≤ ‖ψ‖ := by
  let U (u : ι → K) := heteroKron (1 : Op R) (heteroKron (tauObservable W u) (tauObservable W u))
  have hn (u : ι → K) : ‖applyOperatorToState (U u) ψ‖ = ‖ψ‖ := by
    apply MagicSquareRigidity.norm_toEuclideanLin_of_conjTranspose_mul_eq_one
    simp only [U, heteroKron, Matrix.kronecker, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
    change heteroKron 1 (heteroKron (tauObservable W u)ᴴ (tauObservable W u)ᴴ) *
      heteroKron 1 (heteroKron (tauObservable W u) (tauObservable W u)) = 1
    rw [heteroKron_mul, heteroKron_mul, tauObservable_conjTranspose_mul_self,
      heteroKron_one_one, Matrix.one_mul, heteroKron_one_one]
  have ha : applyOperatorToState (heteroKron (1 : Op R) (pauliCorrelation W)) ψ =
      (Fintype.card (ι → K) : ℂ)⁻¹ • ∑ u : ι → K, applyOperatorToState (U u) ψ := by
    change applyOperatorToState ((Matrix.kroneckerBilinear (R := ℂ) (α := ℂ) (1 : Op R))
      ((Fintype.card (ι → K) : ℂ)⁻¹ • ∑ u, heteroKron (tauObservable W u) (tauObservable W u))) ψ = _
    simp only [map_smul, map_sum, applyOperatorToState, LinearMap.sum_apply, LinearMap.smul_apply]
    rfl
  rw [ha, norm_smul]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)).trans_eq ?_
  simp only [hn, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [norm_inv, Complex.norm_natCast, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

end Correlation

theorem norm_sub_eprProjection_le_of_pauli_dist {K I R : Type} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod 2) K] [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
    (psi : EuclideanSpace ℂ (R × ((I → K) × (I → K)))) (delta : ℝ) (hdelta : 0 ≤ delta)
    (hdist : ∀ W : PauliKind, opDistSq (uniformDistribution (I → K))
      (fun u => heteroKron (1 : Op R) (heteroKron (tauObservable W u) 1))
      (fun u => heteroKron (1 : Op R) (heteroKron 1 (tauObservable W u))) psi ≤ delta) :
    ‖psi - applyOperatorToState (heteroKron (1 : Op R)
      (Matrix.vecMulVec (fun x => eprState (I → K) x) (fun y => star (eprState (I → K) y)))) psi‖ ≤
      2 * Real.sqrt delta := by
  let H (W : PauliKind) := heteroKron (1 : Op R) (pauliCorrelation (K := K) (ι := I) W)
  have hstep (W : PauliKind) : ‖psi - applyOperatorToState (H W) psi‖ ≤ Real.sqrt delta := by
    refine (Real.le_sqrt (norm_nonneg _) hdelta).mpr ((?_ : _ ^ 2 ≤ _).trans (hdist W))
    let L (u : I → K) := heteroKron (1 : Op R) (heteroKron (tauObservable W u) (1 : Op (I → K)))
    let B (u : I → K) := heteroKron (1 : Op R) (heteroKron (1 : Op (I → K)) (tauObservable W u))
    let C (u : I → K) := heteroKron (1 : Op R) (heteroKron (tauObservable W u) (tauObservable W u))
    have hL (u) : (L u)ᴴ * L u = 1 := by
      simp only [L, MagicSquareRigidity.heteroKron_conjTranspose, Matrix.conjTranspose_one,
        heteroKron_mul, Matrix.one_mul, tauObservable_conjTranspose_mul_self, heteroKron_one_one]
    have halg (u) : L u * (L u - B u) = 1 - C u := by
      simp only [L, B, C, Matrix.mul_sub, heteroKron_mul, Matrix.one_mul,
        Matrix.mul_one, tauObservable_sq, heteroKron_one_one]
    have hd : opDistSq (uniformDistribution (I → K)) (fun _ => 1) C psi =
        opDistSq (uniformDistribution (I → K)) L B psi := by
      unfold opDistSq opFamilyDistSq; simp only [Fintype.sum_unique]
      refine avgOver_congr _ _ _ fun u => ?_
      rw [← halg, MagicSquareRigidity.norm_applyOperatorToState_isometry_mul (hL u)]
    have havg : averageOperatorOverDistribution (uniformDistribution (I → K))
        (fun u => (1 : ℂ) • ((1 : Op (R × ((I → K) × (I → K)))) - C u)) = 1 - H W := by
      simp only [one_smul]
      have hs : averageOperatorOverDistribution (uniformDistribution (I → K))
          (fun u => (1 : Op _) - C u) =
          averageOperatorOverDistribution (uniformDistribution (I → K)) (fun _ => 1) -
            averageOperatorOverDistribution (uniformDistribution (I → K)) C := by
        simp [averageOperatorOverDistribution, smul_sub, Finset.sum_sub_distrib]
      rw [hs, averageOperatorOverDistribution_const_of_isProbability _
        (uniformDistribution_isProbability _)]; congr 1
      rw [averageOperatorOverDistribution_uniform_eq_inv_card_smul_sum]
      change _ = (Matrix.kroneckerBilinear (R := ℂ) (α := ℂ) (1 : Op R)) _
      simp only [pauliCorrelation, map_smul, map_sum, C]; rfl
    have h := avg_closeness (uniformDistribution (I → K)) (uniformDistribution_isProbability _)
      (fun _ => 1) C (fun _ => 1) (fun _ => by simp) psi
    rw [havg, hd] at h
    simpa only [MagicSquareRigidity.applyOperatorToState_sub_op,
      MagicSquareRigidity.applyOperatorToState_one] using h
  have hp : H .X * H .Z = heteroKron (1 : Op R)
      (Matrix.vecMulVec (fun x => eprState (I → K) x) (fun y => star (eprState (I → K) y))) := by
    dsimp only [H]; rw [heteroKron_mul, Matrix.one_mul, pauliCorrelation_mul_eq_epr]
  rw [← hp, applyOperatorToState_mul]
  refine (norm_sub_le_norm_sub_add_norm_sub _ (applyOperatorToState (H .X) psi) _).trans ?_
  rw [← MagicSquareRigidity.applyOperatorToState_sub]
  linarith [hstep .X, (norm_heteroKron_pauliCorrelation_apply_le .X _).trans (hstep .Z)]

def eprPartialInner {R V : Type*} [Fintype R] [DecidableEq R] [Fintype V] [DecidableEq V]
    [Nonempty V] (ψ : EuclideanSpace ℂ (R × (V × V))) : EuclideanSpace ℂ R :=
  (EuclideanSpace.equiv R ℂ).symm fun r => ∑ p : V × V, star (eprState V p) * ψ (r, p)

theorem vecTensor_eprPartialInner {R V : Type*} [Fintype R] [DecidableEq R]
    [Fintype V] [DecidableEq V] [Nonempty V] (ψ : EuclideanSpace ℂ (R × (V × V))) :
    vecTensor (eprPartialInner ψ) (eprState V) =
      applyOperatorToState (heteroKron (1 : Op R)
        (Matrix.vecMulVec (fun x => eprState V x) (fun y => star (eprState V y)))) ψ := by
  ext x
  change (∑ p : V × V, star (eprState V p) * ψ (x.1, p)) * eprState V x.2 =
    ∑ j : R × (V × V), ((1 : Op R) x.1 j.1 * (eprState V x.2 * star (eprState V j.2))) * ψ j
  conv_rhs => rw [Fintype.sum_prod_type]
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul]
  conv_rhs => rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring

end Extraction

namespace ProjectiveSetting

section EPRBounds
variable {P : AdmissibleParams} {ε deltaG : ℝ} (S : ProjectiveSetting P ε)

open scoped Classical

theorem idealExpState_norm
    (aux : EuclideanSpace ℂ (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB)) :
    ‖S.idealExpState aux‖ = ‖aux‖ := by
  rw [idealExpState, reindexState_norm_eq, vecTensor_norm_eq, eprState_norm, mul_one]

def extractionAuxReference :
    EuclideanSpace ℂ (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB) :=
  reindexState prodShuffle (vecTensor S.toStrategy.ψ (eprState (PauliRegister P)))

theorem extractionAuxReference_norm : ‖S.extractionAuxReference‖ = 1 := by
  rw [extractionAuxReference, reindexState_norm_eq, vecTensor_norm_eq, eprState_norm,
    S.toStrategy.ψ_norm, one_mul]

def extractionEprProjection : Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
  reindexOp (extractionIdealShuffle P S.toStrategy.ιA S.toStrategy.ιB).symm
    (heteroKron (1 : Op (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB))
      (Matrix.vecMulVec (fun x => eprState (PauliRegister P) x)
        (fun y => star (eprState (PauliRegister P) y))))

theorem exists_unit_aux_near_eprProjection
    (θ : EuclideanSpace ℂ (SixReg P S.toStrategy.ιA S.toStrategy.ιB)) (hθ : ‖θ‖ = 1) :
    ∃ aux : EuclideanSpace ℂ (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB),
      ‖aux‖ = 1 ∧ ‖θ - S.idealExpState aux‖ ≤
        2 * ‖θ - applyOperatorToState S.extractionEprProjection θ‖ := by
  let e := extractionEprFirstEquiv P S.toStrategy.ιA S.toStrategy.ιB
  have hre (aux) : reindexState e (S.idealExpState aux) =
      reindexState prodShuffle (vecTensor (eprState (PauliRegister P)) aux) := by
    ext idx; exact mul_comm _ _
  have hdist (aux) : ‖reindexState e θ - reindexState prodShuffle
      (vecTensor (eprState (PauliRegister P)) aux)‖ = ‖θ - S.idealExpState aux‖ := by
    rw [← hre]; exact (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).norm_map (θ - S.idealExpState aux)
  let aux0 := Extraction.eprPartialInner
    (reindexState (extractionIdealShuffle P S.toStrategy.ιA S.toStrategy.ιB).symm θ)
  have hid0 : S.idealExpState aux0 = applyOperatorToState S.extractionEprProjection θ := by
    unfold idealExpState; rw [Extraction.vecTensor_eprPartialInner]; ext x
    let eI := (extractionIdealShuffle P S.toStrategy.ιA S.toStrategy.ιB).symm
    exact (congrFun (Matrix.submatrix_mulVec_equiv _ (fun j => θ j) eI eI) x).symm
  obtain ⟨aux, haux, hclose⟩ := MagicSquareRigidity.exists_unit_residual
    (reindexState e θ) (by rwa [reindexState_norm_eq])
    S.extractionAuxReference S.extractionAuxReference_norm
    ‖θ - applyOperatorToState S.extractionEprProjection θ‖ aux0
    (((hdist aux0).trans (congrArg (‖θ - ·‖) hid0)).le)
  exact ⟨aux, haux, (hdist aux).symm.trans_le hclose⟩

theorem placeBoth_swap_left_unitary (w : GlobalPairWitness S deltaG) :
    (S.placeBoth (swapUnitary w .alice) (swapUnitary w .bob))ᴴ *
      S.placeBoth (swapUnitary w .alice) (swapUnitary w .bob) = 1 := by
  rw [placeBoth, ← reindexOp_conjTranspose, ← WinImplications.reindexOp_mul,
    MagicSquareRigidity.heteroKron_conjTranspose, heteroKron_mul]
  erw [conjTranspose_mul_swapUnitary, conjTranspose_mul_swapUnitary, heteroKron_one_one]
  ext x y; simp [Matrix.one_apply]

theorem applyBoth_swap_norm (w : GlobalPairWitness S deltaG) :
    ‖S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat‖ = 1 := by
  rw [applyBoth, MagicSquareRigidity.norm_applyOperatorToState_of_isometry
    (S.placeBoth_swap_left_unitary w), S.psiHat_norm]

theorem extraction_pauli_dist_le_four (w : GlobalPairWitness S deltaG)
    (aux : EuclideanSpace ℂ (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB))
    (haux : ‖aux‖ = 1) (side : PlayerSide) (W : PauliKind) :
    opFamilyDistSq (uniformDistribution Unit)
      (fun _ h => conjBy (S.placeSide side (swapUnitary w side))
        (S.placePlayer side ((S.pauliMeas side W).effect h)))
      (fun _ h => S.placeExtractedRegister side (pauliProj W h)) (S.idealExpState aux) ≤ 4 := by
  have hps (p : Placement) (A : PauliRegister P → Op (S.ExpandedLocalSpace p.side))
      (hA : ∑ a, (A a)ᴴ * A a = 1) : ∑ a, (S.place p (A a))ᴴ * S.place p (A a) = 1 := by
    simp only [← S.place_conjTranspose, ← S.place_mul]
    rw [← S.place_finsetSum, hA, S.place_one]
  have hU : (S.placeSide side (swapUnitary w side))ᴴ * S.placeSide side (swapUnitary w side) = 1 := by
    cases side <;>
      simp only [placeSide, ← reindexOp_conjTranspose, ← WinImplications.reindexOp_mul,
        MagicSquareRigidity.heteroKron_conjTranspose, Matrix.conjTranspose_one,
        heteroKron_mul, Matrix.mul_one] <;>
      erw [conjTranspose_mul_swapUnitary, heteroKron_one_one] <;>
      ext x y <;> simp [Matrix.one_apply]
  have hpl : ∑ h, (S.placePlayer side ((S.pauliMeas side W).effect h))ᴴ *
      S.placePlayer side ((S.pauliMeas side W).effect h) = 1 := by
    have hpr : Measurement.IsProjective (S.pauliMeas side W) :=
      SandwichProduct.postprocess_isProjective _
        (by cases side; exact S.isProjective.1 _; exact S.isProjective.2 _) _
    have hl : ∑ h, ((S.pauliMeas side W).effect h)ᴴ * (S.pauliMeas side W).effect h = 1 := by
      simp only [fun h => (hpr h).isSelfAdjoint.isHermitian.eq, fun h => (hpr h).isIdempotentElem.eq]
      exact (S.pauliMeas side W).sum_eq_one
    cases side <;> dsimp [placePlayer] <;> apply hps <;>
      simp only [MagicSquareRigidity.heteroKron_conjTranspose, Matrix.conjTranspose_one,
        heteroKron_mul, Matrix.one_mul, ← heteroKron_finset_sum_left] <;>
      erw [hl] <;> exact heteroKron_one_one
  refine opFamilyDistSq_uniform_le_four _ _ _ (by rw [S.idealExpState_norm, haux]) (fun _ => ?_)
    fun _ => ?_
  · let U := S.placeSide side (swapUnitary w side)
    have ht (A : Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB)) :
        (conjBy U A)ᴴ * conjBy U A = U * (Aᴴ * A) * Uᴴ := by
      simp only [conjBy, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      calc _ = U * (Aᴴ * (Uᴴ * U) * A) * Uᴴ := by noncomm_ring
        _ = _ := by rw [hU, Matrix.mul_one]
    change (∑ h, (conjBy U _)ᴴ * conjBy U _) ≤ 1
    simp_rw [ht]
    rw [← Finset.sum_mul, ← Matrix.mul_sum, hpl, Matrix.mul_one, mul_eq_one_comm.mp hU]
  · have hl : ∑ h : PauliRegister P, (pauliProj W h)ᴴ * pauliProj W h = 1 := by
      simp only [fun h => (posSemidef_pauliProj W h).isHermitian.eq, pauliProj_mul_pauliProj, ite_true]
      exact sum_pauliProj_eq_one W
    have ht {R : Type} [Fintype R] [DecidableEq R] :
        ∑ h : PauliRegister P, (heteroKron (1 : Op R) (pauliProj W h))ᴴ *
          heteroKron (1 : Op R) (pauliProj W h) = 1 := by
      simp only [MagicSquareRigidity.heteroKron_conjTranspose, Matrix.conjTranspose_one,
        heteroKron_mul, Matrix.one_mul, ← heteroKron_finset_sum_right, hl, heteroKron_one_one]
    cases side <;> exact (hps _ _ ht).le

end EPRBounds
end ProjectiveSetting

/-! ## Polynomial collision, encoding support, and non-encoding mass -/

theorem poly_eval_collision_le {P : AdmissibleParams} (f g : Poly P) (hne : f ≠ g) :
    avgOver (uniformDistribution (Fin P.m → PauliScalar P))
      (fun u => if evalPoly f u = evalPoly g u then (1 : ℝ) else 0) ≤ (P.m * P.d : ℝ) / P.q := by
  have hcard : Fintype.card (PauliScalar P) = P.q := @FieldModel.card P.q P.model.toFieldModel
  conv_rhs => rw [← hcard]
  unfold evalPoly
  have havg : avgOver (uniformDistribution (Fin P.m → PauliScalar P))
      (fun u => if MvPolynomial.eval u f.1 = MvPolynomial.eval u g.1 then (1 : ℝ) else 0) =
      (polynomialAgreementProbability P.m (PauliScalar P) f.1 g.1 : ℝ) := by
    rw [avgOver_uniform_eq_inv_card_mul_sum, ← Finset.sum_filter]
    simp [polynomialAgreementProbability, div_eq_mul_inv, mul_comm]
  rw [havg]
  simpa using (by exact_mod_cast schwartzZippel_individualDegree f g hne :
    (polynomialAgreementProbability P.m (PauliScalar P) f.1 g.1 : ℝ) ≤
      ((((P.m * P.d : ℕ) : ℚ≥0) / Fintype.card (PauliScalar P)) : ℝ))

def pauliRegisterMeas {P : AdmissibleParams} (W : PauliKind) :
    Measurement (PauliRegister P) (PauliRegister P) :=
  Measurement.ofSumEqOne (pauliProj W)
    (fun a => Matrix.nonneg_iff_posSemidef.mpr (posSemidef_pauliProj W a)) (sum_pauliProj_eq_one W)

@[simp] theorem isEncoding_encodingPoly {P : AdmissibleParams} (a : PauliRegister P) :
    IsEncoding (encodingPoly a) := by
  unfold IsEncoding; rw [decodeFq_lowDegreeEncoding]; rfl

namespace ProjectiveSetting

def encodingPauliMeas {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) : Measurement (Poly P) (S.ExpandedLocalSpace side) :=
  (tensorMeasurement (S.pauliMeas side W) (pauliRegisterMeas W)).postprocess
    fun a => encodingPoly (a.1 + a.2)

theorem encodingPauliMeas_effect_eq_zero_of_not_isEncoding {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (side : PlayerSide) (W : PauliKind)
    (g : Poly P) (hg : ¬ IsEncoding g) : (S.encodingPauliMeas side W).effect g = 0 := by
  classical
  exact Finset.sum_eq_zero fun a ha => False.elim
    (hg ((Finset.mem_filter.mp ha).2 ▸ isEncoding_encodingPoly (a.1 + a.2)))

theorem encodingPauliMeas_eval_effect_eq_convolution {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (side : PlayerSide) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (v : PauliScalar P) :
    ((S.encodingPauliMeas side W).postprocess (fun g => evalPoly g u)).effect v =
      ∑ ab ∈ Finset.univ.filter (fun ab : PauliScalar P × PauliScalar P => ab.1 + ab.2 = v),
        heteroKron ((S.pauliEvalMeas side W u).effect ab.1) (tauPointProj W u ab.2) := by
  have hp : (S.encodingPauliMeas side W).postprocess (fun g => evalPoly g u) =
      (tensorMeasurement (S.pauliEvalMeas side W u)
        ((pauliRegisterMeas W).postprocess (fun a => lowDegreeEnc a u))).postprocess
        (fun ab => ab.1 + ab.2) := by
    unfold encodingPauliMeas pauliEvalMeas
    rw [Measurement.postprocess_comp, tensorMeasurement_postprocess, Measurement.postprocess_comp]
    refine congrArg ((tensorMeasurement (S.pauliMeas side W) (pauliRegisterMeas W)).postprocess) ?_
    funext a; change lowDegreeEnc (a.1 + a.2) u = lowDegreeEnc a.1 u + lowDegreeEnc a.2 u
    simp only [lowDegreeEnc_eq_dotProduct, add_dotProduct]
  rw [hp, Measurement.postprocess_effect]
  refine Finset.sum_congr rfl fun ab _ => ?_
  change heteroKron _ (((pauliRegisterMeas W).postprocess _).effect ab.2) = _
  simp only [Measurement.postprocess_effect, lowDegreeEnc_eq_dotProduct]; rfl

end ProjectiveSetting

theorem consistencyDefect_comm_of_commute {X A I : Type*}
    [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (mu : Distribution X) (f g : X → A → Op I) (psi : EuclideanSpace ℂ I)
    (hc : ∀ x a b, f x a * g x b = g x b * f x a) :
    consistencyDefect mu f g psi = consistencyDefect mu g f psi := by
  unfold consistencyDefect
  refine avgOver_congr _ _ _ fun x => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [hc x a b, eq_comm]

theorem mass_outside_encoding_le_evaluated_defect {P : AdmissibleParams} {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (meas : Measurement (Poly P) I) (ref : Measurement (Poly P) J)
    (psi : EuclideanSpace ℂ (I × J)) (hpsi : ‖psi‖ = 1)
    (hsupp : ∀ g, ¬ IsEncoding g → ref.effect g = 0) :
    (∑ g ∈ Finset.univ.filter (fun g : Poly P => ¬ IsEncoding g),
      stateQForm psi (heteroKron (meas.effect g) 1)) ≤
      consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron ((meas.postprocess (fun g => evalPoly g u)).effect a) 1)
        (fun u a => heteroKron 1 ((ref.postprocess (fun g => evalPoly g u)).effect a)) psi +
        (P.m * P.d : ℝ) / P.q := by
  classical
  have hm := mass_outside_support_le_point_defect meas ref psi
    (Finset.univ.filter IsEncoding) (by simpa using hsupp)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
  refine hm.trans ((SandwichProduct.point_codeword_defect_le_avg_evaluated_add meas ref psi
    evalPoly ((P.m * P.d : ℝ) / P.q) hpsi (by positivity) poly_eval_collision_le).trans_eq ?_)
  rw [SandwichProduct.consistencyDefect_placed_eq_avg_point]

theorem right_mass_outside_encoding_le_evaluated_defect {P : AdmissibleParams} {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (ref : Measurement (Poly P) I) (meas : Measurement (Poly P) J)
    (psi : EuclideanSpace ℂ (I × J)) (hpsi : ‖psi‖ = 1)
    (hsupp : ∀ g, ¬ IsEncoding g → ref.effect g = 0) :
    (∑ g ∈ Finset.univ.filter (fun g : Poly P => ¬ IsEncoding g),
      stateQForm psi (heteroKron 1 (meas.effect g))) ≤
      consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron ((ref.postprocess (fun g => evalPoly g u)).effect a) 1)
        (fun u a => heteroKron 1 ((meas.postprocess (fun g => evalPoly g u)).effect a)) psi +
        (P.m * P.d : ℝ) / P.q := by
  simpa only [WinImplications.stateQForm_reindexState,
    WinImplications.reindexOp_prodComm_heteroKron,
    WinImplications.consistencyDefect_swappedState] using
    mass_outside_encoding_le_evaluated_defect meas ref
      (reindexState (Equiv.prodComm I J) psi) (by rw [reindexState_norm_eq, hpsi]) hsupp

theorem consistencyDefect_measurement_symm {X α I : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I]
    (mu : Distribution X) (A B : X → Measurement α I) (psi : EuclideanSpace ℂ I) :
    consistencyDefect mu (fun x a => (A x).effect a) (fun x a => (B x).effect a) psi =
      consistencyDefect mu (fun x a => (B x).effect a) (fun x a => (A x).effect a) psi := by
  unfold consistencyDefect
  refine avgOver_congr _ _ _ fun x => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  by_cases hab : a = b; · simp [hab]
  simp only [if_neg hab, if_neg (Ne.symm hab), consistency_term_eq_stateQForm]
  have hs : ((A x).effect a * (B x).effect b)ᴴ = (B x).effect b * (A x).effect a := by
    simp only [Matrix.conjTranspose_mul, measurement_effect_hermitian]
  rw [← hs]; unfold stateQForm applyOperatorToState
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]
  exact inner_re_symm (𝕜 := ℂ) _ _

theorem global_marginal_encoding_consistency {P : AdmissibleParams} {epsilon deltaG : ℝ}
    (hepsilon : 0 ≤ epsilon) (S : ProjectiveSetting P epsilon)
    (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron (((w.marginalPoly .alice W).postprocess (fun g => evalPoly g u)).effect a) 1)
        (fun u a => heteroKron 1 (((S.encodingPauliMeas .bob W).postprocess (fun g => evalPoly g u)).effect a))
        (ExtendedLineGame.pairState S) ≤ deltaG + (1 + 2 * Real.sqrt 172) * Real.sqrt epsilon ∧
      consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron (((S.encodingPauliMeas .alice W).postprocess (fun g => evalPoly g u)).effect a) 1)
        (fun u a => heteroKron 1 (((w.marginalPoly .bob W).postprocess (fun g => evalPoly g u)).effect a))
        (ExtendedLineGame.pairState S) ≤ deltaG + (1 + 2 * Real.sqrt 172) * Real.sqrt epsilon := by
  let mu := uniformDistribution (Fin P.m → PauliScalar P)
  let psi := ExtendedLineGame.pairState S
  let pA := fun u => leftPlacedMeasurement (ιB := S.ExpandedLocalSpace .bob) (S.pointMeasExp .alice W u)
  let pB := fun u => rightPlacedMeasurement (ιA := S.ExpandedLocalSpace .alice) (S.pointMeasExp .bob W u)
  let rA := fun u => leftPlacedMeasurement (ιB := S.ExpandedLocalSpace .bob)
    ((S.encodingPauliMeas .alice W).postprocess (fun g => evalPoly g u))
  let rB := fun u => rightPlacedMeasurement (ιA := S.ExpandedLocalSpace .alice)
    ((S.encodingPauliMeas .bob W).postprocess (fun g => evalPoly g u))
  let mA := fun u => leftPlacedMeasurement (ιB := S.ExpandedLocalSpace .bob)
    ((w.marginalPoly .alice W).postprocess (fun g => evalPoly g u))
  let mB := fun u => rightPlacedMeasurement (ιA := S.ExpandedLocalSpace .alice)
    ((w.marginalPoly .bob W).postprocess (fun g => evalPoly g u))
  have hab : consistencyDefect mu (fun u a => (mA u).effect a) (fun u a => (pB u).effect a) psi ≤ deltaG := by
    change consistencyDefect mu (fun u a => heteroKron _ 1) (fun u a => heteroKron 1 _) psi ≤ _
    rw [S.consistencyDefect_pairState_eq_AA'_BA'']
    simpa only [evalPoly, w.marginalPoly_postprocess_eval] using w.point_consistent_alice W
  have hba : consistencyDefect mu (fun u a => (mB u).effect a) (fun u a => (pA u).effect a) psi ≤ deltaG := by
    rw [consistencyDefect_measurement_symm]
    change consistencyDefect mu (fun u a => heteroKron _ 1) (fun u a => heteroKron 1 _) psi ≤ _
    rw [S.consistencyDefect_pairState_eq_AB''_BB',
      consistencyDefect_comm_of_commute _ _ _ _ (fun _ _ _ => S.place_comm .AB'' .BB' trivial _ _)]
    simpa only [evalPoly, w.marginalPoly_postprocess_eval] using w.point_consistent_bob W
  have hconv (MA : (Fin P.m → PauliScalar P) → Measurement (PauliScalar P) S.toStrategy.ιA)
      (MB : (Fin P.m → PauliScalar P) → Measurement (PauliScalar P) S.toStrategy.ιB) :=
    consistencyDefect_convolution_eq_of_perfect mu MA MB (tauPointMeas W) (tauPointMeas W)
      S.toStrategy.ψ (eprState (PauliRegister P)) (eprState_norm _)
      (tauPointProj_epr_offDiagonal_eq_zero W)
  have hpts : consistencyDefect mu (fun u a => (pA u).effect a) (fun u a => (pB u).effect a) psi ≤
      86 * epsilon := by
    change consistencyDefect mu (fun u a => heteroKron ((S.pointMeasExp .alice W u).effect a) 1)
      (fun u a => heteroKron 1 ((S.pointMeasExp .bob W u).effect a)) (ExtendedLineGame.pairState S) ≤ _
    have he := hconv (S.pointMeas .alice W) (S.pointMeas .bob W)
    simp only [pointMeasExp, Measurement.ofSumEqOne, expPointOp_eq_convolution, tauPointMeas,
      ExtendedLineGame.pairState] at he ⊢
    rw [he]; simpa only [pauli_edge_card, Nat.cast_ofNat] using point_self_consistency_le S W
  have hpts' : consistencyDefect mu (fun u a => (pB u).effect a) (fun u a => (pA u).effect a) psi ≤
      86 * epsilon := by rw [consistencyDefect_measurement_symm]; exact hpts
  have hpb : consistencyDefect mu (fun u a => (pA u).effect a) (fun u a => (rB u).effect a) psi ≤
      86 * epsilon := by
    change consistencyDefect mu (fun u a => heteroKron ((S.pointMeasExp .alice W u).effect a) 1)
      (fun u a => heteroKron 1 (((S.encodingPauliMeas .bob W).postprocess (fun g => evalPoly g u)).effect a))
      (ExtendedLineGame.pairState S) ≤ _
    have he := hconv (S.pointMeas .alice W) (S.pauliEvalMeas .bob W)
    simp_rw [S.encodingPauliMeas_eval_effect_eq_convolution .bob W]
    simp only [pointMeasExp, Measurement.ofSumEqOne, expPointOp_eq_convolution, tauPointMeas,
      ExtendedLineGame.pairState] at he ⊢
    rw [he]; exact win_pauli_basis_cons_explicit P epsilon S hepsilon W
  have hpa : consistencyDefect mu (fun u a => (pB u).effect a) (fun u a => (rA u).effect a) psi ≤
      86 * epsilon := by
    rw [consistencyDefect_measurement_symm]
    change consistencyDefect mu
      (fun u a => heteroKron (((S.encodingPauliMeas .alice W).postprocess (fun g => evalPoly g u)).effect a) 1)
      (fun u a => heteroKron 1 ((S.pointMeasExp .bob W u).effect a))
      (ExtendedLineGame.pairState S) ≤ _
    have he := hconv (S.pauliEvalMeas .alice W) (S.pointMeas .bob W)
    simp_rw [S.encodingPauliMeas_eval_effect_eq_convolution .alice W]
    simp only [pointMeasExp, Measurement.ofSumEqOne, expPointOp_eq_convolution, tauPointMeas,
      ExtendedLineGame.pairState] at he ⊢
    rw [he]; exact win_pauli_basis_cons_interchanged_explicit P epsilon S hepsilon W
  have hsc : deltaG + 2 * Real.sqrt (86 * epsilon + 86 * epsilon) ≤
      deltaG + (1 + 2 * Real.sqrt 172) * Real.sqrt epsilon := by
    rw [← add_mul, show (86 : ℝ) + 86 = 172 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 172)]
    nlinarith [Real.sqrt_nonneg epsilon]
  refine ⟨(consistencyDefect_trans_le mu mA pB pA rB psi _ _ _
    (uniformDistribution_isProbability _) (ExtendedLineGame.pairState_norm S) hab hpts hpb).trans hsc,
    ?_⟩
  have h := (consistencyDefect_trans_le mu mB pA pB rA psi _ _ _
    (uniformDistribution_isProbability _) (ExtendedLineGame.pairState_norm S) hba hpts' hpa).trans hsc
  change consistencyDefect mu (fun u a => (rA u).effect a) (fun u a => (mB u).effect a) psi ≤ _
  rwa [consistencyDefect_measurement_symm]

/-! ## Block measurements, point overlaps, and supplied-witness consistency -/

namespace ProjectiveSetting

section BlockPlacement
variable {P : AdmissibleParams} {epsilon : ℝ} (S : ProjectiveSetting P epsilon)

theorem placeSide_alice_tensor_one (A : Op (S.ExpandedLocalSpace .alice)) :
    S.placeSide .alice (heteroKron A (1 : Op (PauliRegister P))) = S.place .AA' A := by
  ext r c; simp [placeSide, sixRegExtractionEquiv, heteroKron, Matrix.kronecker, place,
    Matrix.one_apply, Prod.ext_iff, ite_and, mul_ite]; split_ifs <;> rfl

theorem placeSide_bob_tensor_one (B : Op (S.ExpandedLocalSpace .bob)) :
    S.placeSide .bob (heteroKron B (1 : Op (PauliRegister P))) = S.place .BB' B := by
  ext r c; simp [placeSide, sixRegExtractionEquiv, heteroKron, Matrix.kronecker, place,
    Matrix.one_apply, Prod.ext_iff, ite_and, mul_ite, ite_mul]; split_ifs <;> rfl

theorem placeSide_finset_sum (side : PlayerSide) {I : Type*} (s : Finset I)
    (B : I → Op (ExtractionBlock P (S.LocalSpace side))) :
    S.placeSide side (∑ i ∈ s, B i) = ∑ i ∈ s, S.placeSide side (B i) := by
  classical
  cases side
  · change reindexOp _ (heteroKron (∑ i ∈ s, B i) (1 : Op _)) = _
    rw [heteroKron_finset_sum_left]; ext r c; simp [placeSide, Matrix.sum_apply]
  · change reindexOp _ (heteroKron (1 : Op _) (∑ i ∈ s, B i)) = _
    rw [heteroKron_finset_sum_right]; ext r c; simp [placeSide, Matrix.sum_apply]

theorem placePlayer_alice_mul_placeSide_bob_tensor (A : Op S.toStrategy.ιA)
    (B : Op (S.ExpandedLocalSpace .bob)) (T : Op (PauliRegister P)) :
    S.placePlayer .alice A * S.placeSide .bob (heteroKron B T) =
      S.place .BB' B * S.place .AB'' (heteroKron A T) := by
  classical
  ext r c; simp [placePlayer, placeSide, sixRegExtractionEquiv, heteroKron, Matrix.kronecker,
    place, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, Prod.ext_iff,
    ite_and, mul_ite, ite_mul]; split_ifs <;> ac_rfl

theorem placeSide_alice_tensor_mul_placePlayer_bob (B : Op (S.ExpandedLocalSpace .alice))
    (T : Op (PauliRegister P)) (A : Op S.toStrategy.ιB) :
    S.placeSide .alice (heteroKron B T) * S.placePlayer .bob A =
      S.place .AA' B * S.place .BA'' (heteroKron A T) := by
  classical
  ext r c; simp [placePlayer, placeSide, sixRegExtractionEquiv, heteroKron, Matrix.kronecker,
    place, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, Prod.ext_iff,
    ite_and, mul_ite, ite_mul]; split_ifs <;> ac_rfl

theorem pointMeasExp_effect_eq_sum_sub (side : PlayerSide) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (a : PauliScalar P) :
    (S.pointMeasExp side W u).effect a =
      ∑ b : PauliScalar P, heteroKron ((S.pointMeas side W u).effect b)
        (tauDotProj W (indicatorVec u) (a - b)) := by
  classical
  change S.expPointOp side W u a = _; rw [S.expPointOp_eq_convolution]
  simp only [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h (c : PauliScalar P) : b + c = a ↔ c = a - b := by rw [eq_sub_iff_add_eq, add_comm]
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, if_true]; rfl

def blockMeasurement (side : PlayerSide) {α : Type*} [Fintype α]
    (A : Measurement α (ExtractionBlock P (S.LocalSpace side))) :
    Measurement α (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
  Measurement.ofSumEqOne (fun a => S.placeSide side (A.effect a))
    (fun a => by
      cases side
      · exact reindexOp_nonneg _ (kronecker_nonneg (A.pos a) Matrix.PosSemidef.one.nonneg)
      · exact reindexOp_nonneg _ (kronecker_nonneg Matrix.PosSemidef.one.nonneg (A.pos a)))
    (by
      rw [← S.placeSide_finset_sum, A.sum_eq_one]
      cases side <;>
        (change reindexOp _ (heteroKron (1 : Op _) (1 : Op _)) = 1;
         rw [heteroKron_one_one]; ext r c; simp [Matrix.one_apply]))

@[simp] theorem blockMeasurement_effect (side : PlayerSide) {α : Type*} [Fintype α]
    (A : Measurement α (ExtractionBlock P (S.LocalSpace side))) (a : α) :
    (S.blockMeasurement side A).effect a = S.placeSide side (A.effect a) := rfl

theorem blockMeasurement_isProjective (side : PlayerSide) {α : Type*} [Fintype α]
    (A : Measurement α (ExtractionBlock P (S.LocalSpace side))) (hA : Measurement.IsProjective A) :
    Measurement.IsProjective (S.blockMeasurement side A) := by
  classical
  let e := sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB
  letI : DecidableEq (ExtractionRegisters P S.toStrategy.ιA S.toStrategy.ιB) := instDecidableEqProd
  cases side
  · convert reindexMeasurement_isProjective e (leftPlacedMeasurement A)
      (fun a => MakingMeasurementsProjective.isProj_kronecker (hA a) (.one _)) using 1; rfl
  · convert reindexMeasurement_isProjective e (rightPlacedMeasurement A)
      (fun a => MakingMeasurementsProjective.isProj_kronecker (.one _) (hA a)) using 1; rfl

theorem consistencyDefect_placePlayers {X α : Type*} [Fintype α] [DecidableEq α]
    [Fintype X] [DecidableEq X] (mu : Distribution X)
    (A : X → Measurement α S.toStrategy.ιA) (B : X → Measurement α S.toStrategy.ιB) :
    consistencyDefect mu (fun x a => S.placePlayer .alice ((A x).effect a))
        (fun x a => S.placePlayer .bob ((B x).effect a)) S.psiHat =
      consistencyDefect mu (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 ((B x).effect a)) S.toStrategy.ψ := by
  letI : DecidableEq (((S.toStrategy.ιA × S.toStrategy.ιB) ×
    (PauliRegister P × PauliRegister P)) × (PauliRegister P × PauliRegister P)) := instDecidableEqProd
  unfold consistencyDefect
  refine avgOver_congr _ _ _ fun x => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : a = b; · simp [hab]
  simp only [if_neg hab, consistency_term_eq_stateQForm]
  have hA := (Matrix.nonneg_iff_posSemidef.mp ((A x).pos a)).isHermitian
  have hB := (Matrix.nonneg_iff_posSemidef.mp ((B x).pos b)).isHermitian
  have hAB := heteroKron_isHermitian _ _ hA hB
  rw [placed_product_stateQForm_eq]
  change stateQForm S.psiHat (S.place .AA' (heteroKron _ 1) * S.place .BB' (heteroKron _ 1)) = _
  rw [S.psiHat_eq_reindexState, WinImplications.stateQForm_reindexState,
    WinImplications.reindexOp_mul, S.reindexOp_sixRegShuffle_place_AA'_heteroKron,
    S.reindexOp_sixRegShuffle_place_BB'_heteroKron]
  simp only [heteroKron_mul, Matrix.one_mul, Matrix.mul_one, heteroKron_one_one]
  rw [stateQForm_vecTensor_heteroKron _ _ _ _
    (heteroKron_isHermitian _ _ hAB Matrix.isHermitian_one) Matrix.isHermitian_one,
    stateQForm_vecTensor_heteroKron _ _ _ _ hAB Matrix.isHermitian_one,
    stateQForm_one_eq_norm_sq, eprState_norm]; ring

end BlockPlacement
end ProjectiveSetting

theorem sum_marginalPoly_eval_mul {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (p : Placement) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (fam : PauliScalar P → Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB)) :
    (∑ a, S.place p (((w.marginalPoly p.side W).postprocess (fun g => MvPolynomial.eval u g.1)).effect a) *
      fam a) =
      ∑ g : Poly P, S.place p ((w.marginalPoly p.side W).effect g) * fam (MvPolynomial.eval u g.1) := by
  classical
  simp only [Measurement.postprocess_effect, ProjectiveSetting.place_finsetSum, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun g hg => ?_).trans
    (Finset.sum_fiberwise _ _ _)
  rw [(Finset.mem_filter.mp hg).2]

theorem marginal_eval_overlap_le_decoded_add {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (p₁ p₂ : Placement) (hp : p₁.IsOpposite p₂) (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    (∑ g : Poly P, stateQForm S.psiHat (S.place p₁ ((w.marginalPoly p₁.side W).effect g) *
        S.place p₂ ((S.pointMeasExp p₂.side W u).effect (MvPolynomial.eval u g.1)))) ≤
      (∑ g : Poly P, stateQForm S.psiHat (S.place p₁ ((w.marginalPoly p₁.side W).effect g) *
        S.place p₂ ((S.pointMeasExp p₂.side W u).effect (dotProduct (decodeFq g) (indicatorVec u))))) +
      ∑ g ∈ (Finset.univ.filter fun g : Poly P => ¬ IsEncoding g),
        stateQForm S.psiHat (S.place p₁ ((w.marginalPoly p₁.side W).effect g)) := by
  classical
  have hpos (g : Poly P) (a : PauliScalar P) := stateQForm_nonneg S.psiHat
    (S.place_mul_place_nonneg p₁ p₂ hp ((w.marginalPoly p₁.side W).pos g)
      ((S.pointMeasExp p₂.side W u).pos a))
  have hsum (g : Poly P) : (∑ a, stateQForm S.psiHat
      (S.place p₁ ((w.marginalPoly p₁.side W).effect g) *
        S.place p₂ ((S.pointMeasExp p₂.side W u).effect a))) =
      stateQForm S.psiHat (S.place p₁ ((w.marginalPoly p₁.side W).effect g)) := by
    have hc : (∑ a, S.place p₂ ((S.pointMeasExp p₂.side W u).effect a)) = 1 :=
      (S.placedMeasurement p₂ (S.pointMeasExp p₂.side W u)).sum_eq_one
    rw [← stateQForm_finset_sum, ← Finset.mul_sum, hc, mul_one]
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun g _ => ?_
  by_cases hg : IsEncoding g
  · simp only [hg, not_true_eq_false, if_false, add_zero, decodeFq_dotProduct_indicatorVec hg u]; rfl
  · simp only [hg, not_false_eq_true, if_true]
    exact ((Finset.single_le_sum (fun a _ => hpos g a) (Finset.mem_univ _)).trans_eq (hsum g)).trans
      (le_add_of_nonneg_left (hpos g _))

theorem tilde_m_consistent_point_meas_both {P : AdmissibleParams} {epsilon deltaG : ℝ}
    (hepsilon : 0 ≤ epsilon) (hdeltaG : 0 ≤ deltaG) (S : ProjectiveSetting P epsilon)
    (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => S.placePlayer .alice ((S.pointMeas .alice W u).effect a))
        (fun u a => S.placeSide .bob (tildeM w .bob W (indicatorVec u) a)) S.psiHat ≤
      deltaConstructPaulis (2 + 2 * Real.sqrt 172) epsilon deltaG P.m P.d P.q ∧
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => S.placeSide .alice (tildeM w .alice W (indicatorVec u) a))
        (fun u a => S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) S.psiHat ≤
      deltaConstructPaulis (2 + 2 * Real.sqrt 172) epsilon deltaG P.m P.d P.q := by
  classical
  let mu := uniformDistribution (Fin P.m → PauliScalar P)
  have hpr := uniformDistribution_isProbability (Fin P.m → PauliScalar P)
  let T (side : PlayerSide) (u : Fin P.m → PauliScalar P) :=
    S.blockMeasurement side (Measurement.ofSumEqOne (tildeM w side W (indicatorVec u))
      (fun a => (tildeM_isProj w side W (indicatorVec u) a).nonneg)
      (sum_tildeM_eq_one w side W (indicatorVec u)))
  obtain ⟨hrefA, hrefB⟩ := global_marginal_encoding_consistency hepsilon S w W
  have hsc {x m : ℝ} (hd : x ≤ deltaG + m)
      (hm : m ≤ deltaG + (1 + 2 * Real.sqrt 172) * Real.sqrt epsilon + (P.m * P.d : ℝ) / P.q) :
      x ≤ deltaConstructPaulis (2 + 2 * Real.sqrt 172) epsilon deltaG P.m P.d P.q := by
    unfold deltaConstructPaulis; rw [Nat.cast_mul]
    have : 0 ≤ (P.m * P.d : ℝ) / P.q := by positivity
    nlinarith [Real.sqrt_nonneg epsilon, Real.sqrt_nonneg (172 : ℝ)]
  constructor
  · have hd : consistencyDefect mu (fun u a => S.placePlayer .alice ((S.pointMeas .alice W u).effect a))
        (fun u a => S.placeSide .bob (tildeM w .bob W (indicatorVec u) a)) S.psiHat ≤
        deltaG + ∑ g ∈ Finset.univ.filter (fun g : Poly P => ¬ IsEncoding g),
          stateQForm S.psiHat (S.place .BB' ((w.marginalPoly .bob W).effect g)) := by
      have h1 := consistencyDefect_eq_one_sub_overlap mu
        (fun u => S.placedMeasurement .AA' (leftPlacedMeasurement (S.pointMeas .alice W u)))
        (T .bob) S.psiHat hpr S.psiHat_norm
      change consistencyDefect mu _ _ _ = 1 - avgOver mu (fun u => ∑ a, stateQForm S.psiHat
        (S.placePlayer .alice ((S.pointMeas .alice W u).effect a) *
          S.placeSide .bob (tildeM w .bob W (indicatorVec u) a))) at h1
      have hov (u) : (∑ a, S.placePlayer .alice ((S.pointMeas .alice W u).effect a) *
          S.placeSide .bob (tildeM w .bob W (indicatorVec u) a)) =
          ∑ g, S.place .BB' ((w.marginalPoly .bob W).effect g) *
            S.place .AB'' ((S.pointMeasExp .alice W u).effect (dotProduct (decodeFq g) (indicatorVec u))) := by
        simp only [tildeM, S.placeSide_finset_sum .bob, Finset.mul_sum]; rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun g _ => ?_
        simp only [S.placePlayer_alice_mul_placeSide_bob_tensor]
        rw [← Finset.mul_sum, ← S.place_finset_sum, S.pointMeasExp_effect_eq_sum_sub .alice W u]
      have h2 := consistencyDefect_eq_one_sub_overlap mu
        (fun u => S.placedMeasurement .BB' ((w.marginalPoly .bob W).postprocess (fun g => MvPolynomial.eval u g.1)))
        (fun u => S.placedMeasurement .AB'' (S.pointMeasExp .alice W u)) S.psiHat hpr S.psiHat_norm
      have hw : consistencyDefect mu
          (fun u a => (S.placedMeasurement .BB' ((w.marginalPoly .bob W).postprocess (fun g => MvPolynomial.eval u g.1))).effect a)
          (fun u a => (S.placedMeasurement .AB'' (S.pointMeasExp .alice W u)).effect a) S.psiHat ≤ deltaG := by
        simpa only [ProjectiveSetting.placedMeasurement_effect, w.marginalPoly_postprocess_eval]
          using w.point_consistent_bob W
      rw [h2] at hw
      have hrg (u) : (∑ a, stateQForm S.psiHat
          (S.place .BB' (((w.marginalPoly .bob W).postprocess (fun g => MvPolynomial.eval u g.1)).effect a) *
            S.place .AB'' ((S.pointMeasExp .alice W u).effect a))) =
          ∑ g, stateQForm S.psiHat (S.place .BB' ((w.marginalPoly .bob W).effect g) *
            S.place .AB'' ((S.pointMeasExp .alice W u).effect (MvPolynomial.eval u g.1))) := by
        rw [← stateQForm_finset_sum, sum_marginalPoly_eval_mul w .BB' W u, stateQForm_finset_sum]
      simp only [ProjectiveSetting.placedMeasurement_effect, hrg] at hw
      have hcmp := avgOver_mono mu _ _ fun u =>
        marginal_eval_overlap_le_decoded_add w .BB' .AB'' trivial W u
      rw [avgOver_add, avgOver_const_of_isProbability mu hpr] at hcmp
      have h1' : consistencyDefect mu (fun u a => S.placePlayer .alice ((S.pointMeas .alice W u).effect a))
          (fun u a => S.placeSide .bob (tildeM w .bob W (indicatorVec u) a)) S.psiHat =
          1 - avgOver mu fun u => ∑ g, stateQForm S.psiHat (S.place .BB' ((w.marginalPoly .bob W).effect g) *
            S.place .AB'' ((S.pointMeasExp .alice W u).effect (dotProduct (decodeFq g) (indicatorVec u)))) := by
        refine h1.trans (congrArg (1 - ·) (avgOver_congr _ _ _ fun u => ?_))
        rw [← stateQForm_finset_sum, hov, stateQForm_finset_sum]
      rw [h1']; dsimp only [mu] at hw hcmp ⊢; linarith
    refine hsc hd ?_
    have hst (g : Poly P) : stateQForm S.psiHat (S.place .BB' ((w.marginalPoly .bob W).effect g)) =
        stateQForm (ExtendedLineGame.pairState S) (heteroKron 1 ((w.marginalPoly .bob W).effect g)) := by
      have h := ExtendedLineGame.stateQForm_pairState_eq_AB''_BB' S 1 ((w.marginalPoly .bob W).effect g)
        Matrix.isHermitian_one (Matrix.nonneg_iff_posSemidef.mp ((w.marginalPoly .bob W).pos g)).isHermitian
      have ho : S.place .AB'' (1 : Op (S.ExpandedLocalSpace .alice)) = 1 := S.place_one .AB''
      rw [ho, Matrix.one_mul] at h; exact h.symm
    simp_rw [hst]
    exact (right_mass_outside_encoding_le_evaluated_defect (S.encodingPauliMeas .alice W)
      (w.marginalPoly .bob W) _ (ExtendedLineGame.pairState_norm S)
      (S.encodingPauliMeas_effect_eq_zero_of_not_isEncoding .alice W)).trans (add_le_add hrefB le_rfl)
  · have hd : consistencyDefect mu (fun u a => S.placeSide .alice (tildeM w .alice W (indicatorVec u) a))
        (fun u a => S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) S.psiHat ≤
        deltaG + ∑ g ∈ Finset.univ.filter (fun g : Poly P => ¬ IsEncoding g),
          stateQForm S.psiHat (S.place .AA' ((w.marginalPoly .alice W).effect g)) := by
      have h1 := consistencyDefect_eq_one_sub_overlap mu (T .alice)
        (fun u => S.placedMeasurement .BB' (leftPlacedMeasurement (S.pointMeas .bob W u)))
        S.psiHat hpr S.psiHat_norm
      change consistencyDefect mu _ _ _ = 1 - avgOver mu (fun u => ∑ a, stateQForm S.psiHat
        (S.placeSide .alice (tildeM w .alice W (indicatorVec u) a) *
          S.placePlayer .bob ((S.pointMeas .bob W u).effect a))) at h1
      have hov (u) : (∑ a, S.placeSide .alice (tildeM w .alice W (indicatorVec u) a) *
          S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) =
          ∑ g, S.place .AA' ((w.marginalPoly .alice W).effect g) *
            S.place .BA'' ((S.pointMeasExp .bob W u).effect (dotProduct (decodeFq g) (indicatorVec u))) := by
        simp only [tildeM, S.placeSide_finset_sum .alice, Finset.sum_mul]; rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun g _ => ?_
        simp only [S.placeSide_alice_tensor_mul_placePlayer_bob]
        rw [← Finset.mul_sum, ← S.place_finset_sum, S.pointMeasExp_effect_eq_sum_sub .bob W u]
      have h2 := consistencyDefect_eq_one_sub_overlap mu
        (fun u => S.placedMeasurement .AA' ((w.marginalPoly .alice W).postprocess (fun g => MvPolynomial.eval u g.1)))
        (fun u => S.placedMeasurement .BA'' (S.pointMeasExp .bob W u)) S.psiHat hpr S.psiHat_norm
      have hw : consistencyDefect mu
          (fun u a => (S.placedMeasurement .AA' ((w.marginalPoly .alice W).postprocess (fun g => MvPolynomial.eval u g.1))).effect a)
          (fun u a => (S.placedMeasurement .BA'' (S.pointMeasExp .bob W u)).effect a) S.psiHat ≤ deltaG := by
        simpa only [ProjectiveSetting.placedMeasurement_effect, w.marginalPoly_postprocess_eval]
          using w.point_consistent_alice W
      rw [h2] at hw
      have hrg (u) : (∑ a, stateQForm S.psiHat
          (S.place .AA' (((w.marginalPoly .alice W).postprocess (fun g => MvPolynomial.eval u g.1)).effect a) *
            S.place .BA'' ((S.pointMeasExp .bob W u).effect a))) =
          ∑ g, stateQForm S.psiHat (S.place .AA' ((w.marginalPoly .alice W).effect g) *
            S.place .BA'' ((S.pointMeasExp .bob W u).effect (MvPolynomial.eval u g.1))) := by
        rw [← stateQForm_finset_sum, sum_marginalPoly_eval_mul w .AA' W u, stateQForm_finset_sum]
      simp only [ProjectiveSetting.placedMeasurement_effect, hrg] at hw
      have hcmp := avgOver_mono mu _ _ fun u =>
        marginal_eval_overlap_le_decoded_add w .AA' .BA'' trivial W u
      rw [avgOver_add, avgOver_const_of_isProbability mu hpr] at hcmp
      have h1' : consistencyDefect mu (fun u a => S.placeSide .alice (tildeM w .alice W (indicatorVec u) a))
          (fun u a => S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) S.psiHat =
          1 - avgOver mu fun u => ∑ g, stateQForm S.psiHat (S.place .AA' ((w.marginalPoly .alice W).effect g) *
            S.place .BA'' ((S.pointMeasExp .bob W u).effect (dotProduct (decodeFq g) (indicatorVec u)))) := by
        refine h1.trans (congrArg (1 - ·) (avgOver_congr _ _ _ fun u => ?_))
        rw [← stateQForm_finset_sum, hov, stateQForm_finset_sum]
      rw [h1']; dsimp only [mu] at hw hcmp ⊢; linarith
    refine hsc hd ?_
    have hst (g : Poly P) : stateQForm S.psiHat (S.place .AA' ((w.marginalPoly .alice W).effect g)) =
        stateQForm (ExtendedLineGame.pairState S) (heteroKron ((w.marginalPoly .alice W).effect g) 1) := by
      have h := ExtendedLineGame.stateQForm_pairState_eq_AA'_BA'' S ((w.marginalPoly .alice W).effect g) 1
        (Matrix.nonneg_iff_posSemidef.mp ((w.marginalPoly .alice W).pos g)).isHermitian Matrix.isHermitian_one
      have ho : S.place .BA'' (1 : Op (S.ExpandedLocalSpace .bob)) = 1 := S.place_one .BA''
      rw [ho, Matrix.mul_one] at h; exact h.symm
    simp_rw [hst]
    exact (mass_outside_encoding_le_evaluated_defect (w.marginalPoly .alice W)
      (S.encodingPauliMeas .bob W) _ (ExtendedLineGame.pairState_norm S)
      (S.encodingPauliMeas_effect_eq_zero_of_not_isEncoding .bob W)).trans (add_le_add hrefA le_rfl)

/-! ## Character consistency, pulling argument, and state extraction -/

def pullingPoly {P : AdmissibleParams} (o : Poly P × PauliRegister P) : Poly P :=
  o.1 - encodingPoly o.2

def pullingMeas {P : AdmissibleParams} {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (side : PlayerSide) (W : PauliKind) :
    Measurement (Poly P) (ExtractionBlock P (S.LocalSpace side)) :=
  open Classical in
  (tensorMeasurement (w.marginalPoly side W) (pauliRegisterMeas W)).postprocess pullingPoly

theorem pullingMeas_isProjective {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (side : PlayerSide) (W : PauliKind) : Measurement.IsProjective (pullingMeas w side W) := by
  classical
  refine SandwichProduct.postprocess_isProjective _ (fun o => ?_) _
  exact MakingMeasurementsProjective.isProj_kronecker (w.marginalPoly_isProjective side W o.1)
    ⟨by simp [IsIdempotentElem, pauliRegisterMeas, Measurement.ofSumEqOne, pauliProj_mul_pauliProj],
      (posSemidef_pauliProj W o.2).isHermitian⟩

theorem pullingMeas_postprocess_effect {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG) (side : PlayerSide)
    (W : PauliKind) (u : PauliRegister P) (a : PauliScalar P) :
    (open Classical in
      ((pullingMeas w side W).postprocess (fun g => dotProduct (decodeFq g) u)).effect a) =
      tildeM w side W u a := by
  classical
  have hd (o : Poly P × PauliRegister P) : decodeFq (pullingPoly o) = decodeFq o.1 - o.2 := by
    have hs (g h : Poly P) : decodeFq (g - h) = decodeFq g - decodeFq h := by
      funext y; simp [decodeOn, decodeAt, evalPoly, MvPolynomial.eval_sub]
    rw [pullingPoly, hs, decodeFq_lowDegreeEncoding]
  rw [pullingMeas, Measurement.postprocess_comp]
  simp only [Measurement.postprocess_effect, Finset.sum_filter, hd,
    tensorMeasurement, Measurement.ofSumEqOne, pauliRegisterMeas]
  rw [Fintype.sum_prod_type]; unfold tildeM tauDotProj bracketOp
  simp_rw [heteroKron_finset_sum_right, Finset.sum_filter]
  refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun h _ => ?_
  have hl : dotProduct (decodeFq g - h) u = a ↔ dotProduct h u = dotProduct (decodeFq g) u - a := by
    rw [sub_dotProduct]; constructor <;> intro he <;> linear_combination -he
  simp only [hl]

theorem pullingMeas_eval_effect {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG) (side : PlayerSide)
    (W : PauliKind) (u : Fin P.m → PauliScalar P) (a : PauliScalar P) :
    ((pullingMeas w side W).postprocess (fun g => evalPoly g u)).effect a =
      ∑ g : Poly P, heteroKron ((w.marginalPoly side W).effect g)
        (tauDotProj W (indicatorVec u) (evalPoly g u - a)) := by
  classical
  rw [pullingMeas, Measurement.postprocess_comp]
  have he (o : Poly P × PauliRegister P) :
      evalPoly (pullingPoly o) u = evalPoly o.1 u - dotProduct o.2 (indicatorVec u) := by
    change MvPolynomial.eval u (o.1.1 - lowDegreeEncoding o.2) = _
    rw [MvPolynomial.eval_sub]; exact congrArg (evalPoly o.1 u - ·) (lowDegreeEnc_eq_dotProduct o.2 u)
  simp only [Measurement.postprocess_effect, Finset.sum_filter, he, tensorMeasurement,
    Measurement.ofSumEqOne, pauliRegisterMeas]
  rw [Fintype.sum_prod_type]; unfold tauDotProj bracketOp
  simp_rw [heteroKron_finset_sum_right, Finset.sum_filter]
  refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun h _ => ?_
  have hl : evalPoly g u - dotProduct h (indicatorVec u) = a ↔
      dotProduct h (indicatorVec u) = evalPoly g u - a := by
    constructor <;> intro hq <;> linear_combination -hq
  simp only [hl]

theorem polynomial_decoding_defect_le_evaluated_add {P : AdmissibleParams}
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Measurement (Poly P) I) (B : Measurement (Poly P) J)
    (psi : EuclideanSpace ℂ (I × J)) (hpsi : ‖psi‖ = 1) :
    consistencyDefect (uniformDistribution (PauliRegister P))
        (fun u a => heteroKron ((A.postprocess (fun g => dotProduct (decodeFq g) u)).effect a) 1)
        (fun u a => heteroKron 1 ((B.postprocess (fun g => dotProduct (decodeFq g) u)).effect a)) psi ≤
      consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron ((A.postprocess (fun g => evalPoly g u)).effect a) 1)
        (fun u a => heteroKron 1 ((B.postprocess (fun g => evalPoly g u)).effect a)) psi +
        (P.m * P.d : ℝ) / P.q := by
  have hcol := SandwichProduct.point_codeword_defect_le_avg_evaluated_add A B psi evalPoly
    ((P.m * P.d : ℝ) / P.q) hpsi (by positivity) poly_eval_collision_le
  have hp (u : PauliRegister P) := consistencyDefect_postprocess_le
    (uniformDistribution Unit) (fun _ => A) (fun _ => B) psi (fun g => dotProduct (decodeFq g) u)
  simp only [consistencyDefect, avgOver_uniform_const, consistency_term_eq_stateQForm,
    placed_product_stateQForm_eq] at hp
  simp only [consistencyDefect, consistency_term_eq_stateQForm, placed_product_stateQForm_eq]
  exact (avgOver_mono _ _ _ hp).trans ((avgOver_uniform_const _).le.trans hcol)

theorem tildeObs_opDistSq_le {P : AdmissibleParams} {epsilon deltaG : ℝ}
    (hepsilon : 0 ≤ epsilon) (hepsilon_one : epsilon ≤ 1) (hdeltaG : 0 ≤ deltaG)
    (S : ProjectiveSetting P epsilon) (w : GlobalPairWitness S deltaG)
    (W : PauliKind) (j : Fin P.model.basisDim) :
    opDistSq (uniformDistribution (PauliRegister P))
      (fun u => S.placeSide .alice (tildeObs w .alice W u j))
      (fun u => S.placeSide .bob (tildeObs w .bob W u j)) S.psiHat ≤
      deltaConstructPaulis pauliBaselineExtractionConstant epsilon deltaG P.m P.d P.q := by
  classical
  let e := sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB
  let f := fun a : PauliScalar P => fixedBinTrace P.model (P.model.basis j * a)
  have hchar {X ιA ιB : Type} [Fintype X] [DecidableEq X] [Fintype ιA] [DecidableEq ιA]
      [Fintype ιB] [DecidableEq ιB] (μ : Distribution X)
      (A : X → Measurement (PauliScalar P) ιA) (B : X → Measurement (PauliScalar P) ιB)
      (ψ : EuclideanSpace ℂ (ιA × ιB)) :
      opDistSq μ (fun x => heteroKron (∑ a, phaseSign (f a) • (A x).effect a) 1)
        (fun x => heteroKron 1 (∑ a, phaseSign (f a) • (B x).effect a)) ψ ≤
        4 * consistencyDefect μ (fun x a => heteroKron ((A x).effect a) 1)
          (fun x a => heteroKron 1 ((B x).effect a)) ψ := by
    have hsb {ι : Type} [Fintype ι] [DecidableEq ι] (M : Measurement (PauliScalar P) ι) :
        (∑ a, phaseSign (f a) • M.effect a) = ∑ b : ZMod 2, phaseSign b • (M.postprocess f).effect b := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := f) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Measurement.postprocess_effect, Finset.smul_sum]
      exact Finset.sum_congr rfl fun a ha => by rw [(Finset.mem_filter.mp ha).2]
    have hfam := (opFamilyDistSq_le_two_mul_consistencyDefect μ
      (fun x => leftPlacedMeasurement ((A x).postprocess f))
      (fun x => rightPlacedMeasurement ((B x).postprocess f)) ψ).trans
        (mul_le_mul_of_nonneg_left (consistencyDefect_postprocess_le μ A B ψ f) (by norm_num))
    have hobs := povm_to_obs_of_measurements μ
      (fun x => leftPlacedMeasurement ((A x).postprocess f))
      (fun x => rightPlacedMeasurement ((B x).postprocess f)) phaseSign norm_phaseSign ψ
    simp only [ZMod.card, Nat.cast_ofNat] at hobs
    simpa only [hsb, WinImplications.heteroKron_left_sum_smul,
      WinImplications.heteroKron_right_sum_smul, leftPlacedMeasurement, rightPlacedMeasurement,
      Measurement.ofSumEqOne, ← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num] using
      hobs.trans (mul_le_mul_of_nonneg_left hfam (by norm_num))
  let M (side : PlayerSide) (u : PauliRegister P) :=
    Measurement.ofSumEqOne (tildeM w side W u)
      (fun a => (tildeM_isProj w side W u a).nonneg) (sum_tildeM_eq_one w side W u)
  have h1 := hchar (uniformDistribution (PauliRegister P)) (M .alice) (M .bob) (reindexState e S.psiHat)
  have hd_eq : opDistSq (uniformDistribution (PauliRegister P))
      (fun u => heteroKron (tildeObs w .alice W u j) 1)
      (fun u => heteroKron 1 (tildeObs w .bob W u j)) (reindexState e S.psiHat) =
      opDistSq (uniformDistribution (PauliRegister P))
        (fun u => S.placeSide .alice (tildeObs w .alice W u j))
        (fun u => S.placeSide .bob (tildeObs w .bob W u j)) S.psiHat := by
    unfold opDistSq opFamilyDistSq; simp only [Fintype.sum_unique]
    refine avgOver_congr _ _ _ fun u => ?_
    rw [WinImplications.norm_applyOperatorToState_reindexState, WinImplications.reindexOp_sub]; rfl
  have hc_ps {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A]
      (mu : Distribution X) (L : X → A → Op (ExtractionBlock P (S.LocalSpace .alice)))
      (R : X → A → Op (ExtractionBlock P (S.LocalSpace .bob))) :
      consistencyDefect mu (fun x a => S.placeSide .alice (L x a))
        (fun x a => S.placeSide .bob (R x a)) S.psiHat =
      consistencyDefect mu (fun x a => heteroKron (L x a) 1) (fun x a => heteroKron 1 (R x a))
        (reindexState e S.psiHat) := by
    unfold consistencyDefect
    refine avgOver_congr _ _ _ fun x => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases hab : a = b; · simp [hab]
    simp only [if_neg hab, consistency_term_eq_stateQForm]
    rw [WinImplications.stateQForm_reindexState, WinImplications.reindexOp_mul]; rfl
  change opDistSq _ (fun u => heteroKron (tildeObs w .alice W u j) 1)
    (fun u => heteroKron 1 (tildeObs w .bob W u j)) _ ≤
    4 * consistencyDefect _ (fun u a => heteroKron (tildeM w .alice W u a) 1)
      (fun u a => heteroKron 1 (tildeM w .bob W u a)) _ at h1
  rw [hd_eq, ← hc_ps] at h1
  have h2 : consistencyDefect (uniformDistribution (PauliRegister P))
      (fun u a => S.placeSide .alice (tildeM w .alice W u a))
      (fun u a => S.placeSide .bob (tildeM w .bob W u a)) S.psiHat ≤
      consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => S.placeSide .alice (((pullingMeas w .alice W).postprocess (fun g => evalPoly g u)).effect a))
        (fun u a => S.placeSide .bob (((pullingMeas w .bob W).postprocess (fun g => evalPoly g u)).effect a))
        S.psiHat + (P.m * P.d : ℝ) / P.q := by
    rw [hc_ps, hc_ps]
    have h := polynomial_decoding_defect_le_evaluated_add (pullingMeas w .alice W)
      (pullingMeas w .bob W) (reindexState e S.psiHat) (by rw [reindexState_norm_eq, S.psiHat_norm])
    have hA : (fun u a => heteroKron (tildeM w .alice W u a)
        (1 : Op (ExtractionBlock P S.toStrategy.ιB))) =
        fun u a => heteroKron
          (((pullingMeas w .alice W).postprocess (fun g => dotProduct (decodeFq g) u)).effect a) 1 := by
      funext u a; rw [pullingMeas_postprocess_effect]
    have hB : (fun u a => heteroKron (1 : Op (ExtractionBlock P S.toStrategy.ιA))
        (tildeM w .bob W u a)) =
        fun u a => heteroKron 1
          (((pullingMeas w .bob W).postprocess (fun g => dotProduct (decodeFq g) u)).effect a) := by
      funext u a; rw [pullingMeas_postprocess_effect]
    rwa [hA, hB]
  let mu := uniformDistribution (Fin P.m → PauliScalar P)
  have hpr := uniformDistribution_isProbability (Fin P.m → PauliScalar P)
  let PA := fun u => S.placedMeasurement .AA' (leftPlacedMeasurement (S.pointMeas .alice W u))
  let PB := fun u => S.placedMeasurement .BB' (leftPlacedMeasurement (S.pointMeas .bob W u))
  let QA := fun u => S.blockMeasurement .alice ((pullingMeas w .alice W).postprocess (fun g => evalPoly g u))
  let QB := fun u => S.blockMeasurement .bob ((pullingMeas w .bob W).postprocess (fun g => evalPoly g u))
  have hpA : consistencyDefect mu (fun u a => (QA u).effect a) (fun u a => (PB u).effect a) S.psiHat ≤ deltaG := by
    have h_ov (u) : (∑ a, S.placeSide .alice (((pullingMeas w .alice W).postprocess (fun g => evalPoly g u)).effect a) *
        S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) =
        ∑ g, S.place .AA' ((w.marginalPoly .alice W).effect g) *
          S.place .BA'' ((S.pointMeasExp .bob W u).effect (evalPoly g u)) := by
      simp_rw [pullingMeas_eval_effect (S := S) w .alice W u]
      simp only [S.placeSide_finset_sum .alice, Finset.sum_mul]; rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [S.placeSide_alice_tensor_mul_placePlayer_bob]
      rw [← Finset.mul_sum, ← S.place_finset_sum, S.pointMeasExp_effect_eq_sum_sub .bob W u]
    let MA := fun u => S.placedMeasurement .AA' ((w.marginalPoly .alice W).postprocess (fun g => evalPoly g u))
    let EA := fun u => S.placedMeasurement .BA'' (S.pointMeasExp .bob W u)
    have ha1 := consistencyDefect_eq_one_sub_overlap mu QA PB S.psiHat hpr S.psiHat_norm
    have ha2 := consistencyDefect_eq_one_sub_overlap mu MA EA S.psiHat hpr S.psiHat_norm
    have hbd : consistencyDefect mu (fun u a => (MA u).effect a) (fun u a => (EA u).effect a) S.psiHat ≤ deltaG := by
      simpa only [MA, EA, ProjectiveSetting.placedMeasurement_effect, evalPoly,
        w.marginalPoly_postprocess_eval] using w.point_consistent_alice W
    refine (le_of_eq ?_).trans hbd
    rw [ha1, ha2]; refine congrArg (1 - ·) (avgOver_congr _ _ _ fun u => ?_)
    simp only [QA, PB, MA, EA, ProjectiveSetting.blockMeasurement_effect, ProjectiveSetting.placedMeasurement_effect]
    change (∑ a, stateQForm S.psiHat (S.placeSide .alice _ * S.placePlayer .bob _)) = _
    rw [← stateQForm_finset_sum, h_ov, ← stateQForm_finset_sum]
    exact congrArg (stateQForm S.psiHat)
      (sum_marginalPoly_eval_mul w .AA' W u fun a => S.place .BA'' ((S.pointMeasExp .bob W u).effect a)).symm
  have hpB : consistencyDefect mu (fun u a => (PA u).effect a) (fun u a => (QB u).effect a) S.psiHat ≤ deltaG := by
    have h_ov (u) : (∑ a, S.placePlayer .alice ((S.pointMeas .alice W u).effect a) *
        S.placeSide .bob (((pullingMeas w .bob W).postprocess (fun g => evalPoly g u)).effect a)) =
        ∑ g, S.place .BB' ((w.marginalPoly .bob W).effect g) *
          S.place .AB'' ((S.pointMeasExp .alice W u).effect (evalPoly g u)) := by
      simp_rw [pullingMeas_eval_effect (S := S) w .bob W u]
      simp only [S.placeSide_finset_sum .bob, Finset.mul_sum]; rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [S.placePlayer_alice_mul_placeSide_bob_tensor]
      rw [← Finset.mul_sum, ← S.place_finset_sum, S.pointMeasExp_effect_eq_sum_sub .alice W u]
    let MB := fun u => S.placedMeasurement .BB' ((w.marginalPoly .bob W).postprocess (fun g => evalPoly g u))
    let EB := fun u => S.placedMeasurement .AB'' (S.pointMeasExp .alice W u)
    have ha1 := consistencyDefect_eq_one_sub_overlap mu PA QB S.psiHat hpr S.psiHat_norm
    have ha2 := consistencyDefect_eq_one_sub_overlap mu MB EB S.psiHat hpr S.psiHat_norm
    have hbd : consistencyDefect mu (fun u a => (MB u).effect a) (fun u a => (EB u).effect a) S.psiHat ≤ deltaG := by
      simpa only [MB, EB, ProjectiveSetting.placedMeasurement_effect, evalPoly,
        w.marginalPoly_postprocess_eval] using w.point_consistent_bob W
    refine (le_of_eq ?_).trans hbd
    rw [ha1, ha2]; refine congrArg (1 - ·) (avgOver_congr _ _ _ fun u => ?_)
    simp only [QB, PA, MB, EB, ProjectiveSetting.blockMeasurement_effect, ProjectiveSetting.placedMeasurement_effect]
    change (∑ a, stateQForm S.psiHat (S.placePlayer .alice _ * S.placeSide .bob _)) = _
    rw [← stateQForm_finset_sum, h_ov, ← stateQForm_finset_sum]
    exact congrArg (stateQForm S.psiHat)
      (sum_marginalPoly_eval_mul w .BB' W u fun a => S.place .AB'' ((S.pointMeasExp .alice W u).effect a)).symm
  have hpt : consistencyDefect mu (fun u a => (PA u).effect a) (fun u a => (PB u).effect a) S.psiHat ≤
      (Fintype.card PauliEdge : ℝ) * epsilon := by
    change consistencyDefect mu (fun u a => S.placePlayer .alice _) (fun u a => S.placePlayer .bob _) _ ≤ _
    rw [S.consistencyDefect_placePlayers]; exact point_self_consistency_le S W
  have hP := (opFamilyDistSq_le_two_mul_consistencyDefect mu PA PB S.psiHat).trans
    (mul_le_mul_of_nonneg_left hpt (by norm_num))
  rw [opFamilyDistSq_symm] at hP
  have hAB := opFamilyDistSq_le_of_le_of_le mu _ _ _ S.psiHat _ _
    (opFamilyDistSq_le_of_le_of_le mu _ _ _ S.psiHat _ _
      ((opFamilyDistSq_le_two_mul_consistencyDefect mu QA PB S.psiHat).trans
        (mul_le_mul_of_nonneg_left hpA (by norm_num))) hP)
    ((opFamilyDistSq_le_two_mul_consistencyDefect mu PA QB S.psiHat).trans
      (mul_le_mul_of_nonneg_left hpB (by norm_num)))
  have h3 : consistencyDefect mu (fun u a => (QA u).effect a) (fun u a => (QB u).effect a) S.psiHat ≤
      12 * deltaG + 8 * (Fintype.card PauliEdge : ℝ) * epsilon :=
    (consistencyDefect_le_opFamilyDistSq_of_projective mu QA QB S.psiHat
      (fun u => S.blockMeasurement_isProjective .alice _
        (SandwichProduct.postprocess_isProjective _ (pullingMeas_isProjective w .alice W) _))
      (fun u => S.blockMeasurement_isProjective .bob _
        (SandwichProduct.postprocess_isProjective _ (pullingMeas_isProjective w .bob W) _))).trans
      (hAB.trans (by ring_nf; rfl))
  have h4 := h1.trans (mul_le_mul_of_nonneg_left (h2.trans (add_le_add h3 le_rfl)) (by norm_num))
  have heps : epsilon ≤ Real.sqrt epsilon := Real.le_sqrt_self_iff.mpr hepsilon_one
  have hr : 0 ≤ (P.m * P.d : ℝ) / P.q :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  refine h4.trans ?_
  unfold deltaConstructPaulis pauliBaselineExtractionConstant
  rw [pauli_edge_card, Nat.cast_ofNat, Nat.cast_mul]
  nlinarith [Real.sqrt_nonneg epsilon]

theorem ProjectiveSetting.conjBy_placeBoth_swap_placeSide {P : AdmissibleParams}
    {epsilon deltaG : ℝ} (S : ProjectiveSetting P epsilon) (w : GlobalPairWitness S deltaG)
    (side : PlayerSide) (A : Op (ExtractionBlock P (S.LocalSpace side))) :
    conjBy (S.placeBoth (swapUnitary w .alice) (swapUnitary w .bob)) (S.placeSide side A) =
      S.placeSide side (conjBy (swapUnitary w side) A) := by
  have hcr {I J : Type} [Fintype I] [Fintype J] (e : I ≃ J) (U M : Op J) :
      conjBy (reindexOp e U) (reindexOp e M) = reindexOp e (conjBy U M) := by
    rw [conjBy, ← reindexOp_conjTranspose, ← WinImplications.reindexOp_mul,
      ← WinImplications.reindexOp_mul, conjBy]
  have hck {I J : Type} [Fintype I] [Fintype J] (U M : Op I) (V N : Op J) :
      conjBy (heteroKron U V) (heteroKron M N) = heteroKron (conjBy U M) (conjBy V N) := by
    simp only [conjBy, MagicSquareRigidity.heteroKron_conjTranspose, heteroKron_mul]
  cases side <;> simp only [ProjectiveSetting.placeBoth, ProjectiveSetting.placeSide, hcr, hck] <;>
    congr 2 <;> dsimp only [conjBy] <;>
    rw [Matrix.mul_one, swapUnitary_mul_conjTranspose]

theorem exists_extraction_aux_of_global_pair_witness {P : AdmissibleParams} {epsilon deltaG : ℝ}
    (hepsilon : 0 ≤ epsilon) (hepsilon_one : epsilon ≤ 1) (hdeltaG : 0 ≤ deltaG)
    (S : ProjectiveSetting P epsilon) (w : GlobalPairWitness S deltaG) :
    ∃ aux : EuclideanSpace ℂ (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB),
      ‖aux‖ = 1 ∧ ‖S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat -
        S.idealExpState aux‖ ^ 2 ≤
        16 * deltaConstructPaulis pauliBaselineExtractionConstant epsilon deltaG P.m P.d P.q := by
  classical
  let theta := S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat
  let e := (extractionIdealShuffle P S.toStrategy.ιA S.toStrategy.ιB).symm
  let delta := deltaConstructPaulis pauliBaselineExtractionConstant epsilon deltaG P.m P.d P.q
  have hdelta : 0 ≤ delta := by dsimp [delta, deltaConstructPaulis, pauliBaselineExtractionConstant]; positivity
  let j : Fin P.model.basisDim := ⟨0, P.model.basisDimOdd.pos⟩
  have hdist := Extraction.norm_sub_eprProjection_le_of_pauli_dist (reindexState e theta) delta hdelta
    fun W => by
      have hrl (T : Op (PauliRegister P)) : reindexOp e
          (heteroKron (1 : Op (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB))
            (heteroKron T (1 : Op (PauliRegister P)))) =
          S.placeSide .alice (heteroKron (1 : Op (S.ExpandedLocalSpace .alice)) T) := by
        ext r c; change (if ((r.1.1, r.1.2.1), (r.2.1, r.2.2.1)) =
            ((c.1.1, c.1.2.1), (c.2.1, c.2.2.1)) then (1 : ℂ) else 0) *
            (T r.1.2.2 c.1.2.2 * if r.2.2.2 = c.2.2.2 then 1 else 0) =
          ((if (r.1.1, r.1.2.1) = (c.1.1, c.1.2.1) then 1 else 0) * T r.1.2.2 c.1.2.2) *
            (if ((r.2.1, r.2.2.1), r.2.2.2) = ((c.2.1, c.2.2.1), c.2.2.2) then 1 else 0)
        simp only [Prod.mk.injEq, ite_and, ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero]
        split_ifs <;> rfl
      have hrr (T : Op (PauliRegister P)) : reindexOp e
          (heteroKron (1 : Op (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB))
            (heteroKron (1 : Op (PauliRegister P)) T)) =
          S.placeSide .bob (heteroKron (1 : Op (S.ExpandedLocalSpace .bob)) T) := by
        ext r c; change (if ((r.1.1, r.1.2.1), (r.2.1, r.2.2.1)) =
            ((c.1.1, c.1.2.1), (c.2.1, c.2.2.1)) then (1 : ℂ) else 0) *
            ((if r.1.2.2 = c.1.2.2 then 1 else 0) * T r.2.2.2 c.2.2.2) =
          (if ((r.1.1, r.1.2.1), r.1.2.2) = ((c.1.1, c.1.2.1), c.1.2.2) then 1 else 0) *
            ((if (r.2.1, r.2.2.1) = (c.2.1, c.2.2.1) then 1 else 0) * T r.2.2.2 c.2.2.2)
        simp only [Prod.mk.injEq, ite_and, ite_mul, mul_ite, one_mul, zero_mul, mul_zero]
        split_ifs <;> rfl
      have hre : opDistSq (uniformDistribution (PauliRegister P))
          (fun u => heteroKron (1 : Op _) (heteroKron (tauObservable W u) 1))
          (fun u => heteroKron (1 : Op _) (heteroKron 1 (tauObservable W u))) (reindexState e theta) =
        opDistSq (uniformDistribution (PauliRegister P))
          (fun u => S.placeSide .alice (heteroKron 1 (tauObservable W (P.model.basis j • u))))
          (fun u => S.placeSide .bob (heteroKron 1 (tauObservable W (P.model.basis j • u)))) theta := by
        unfold opDistSq opFamilyDistSq; simp only [Fintype.sum_unique]
        simp_rw [WinImplications.norm_applyOperatorToState_reindexState,
          WinImplications.reindexOp_sub, hrl, hrr]
        let em : PauliRegister P ≃ PauliRegister P :=
          Equiv.piCongrRight fun _ => Equiv.mulLeft₀ (P.model.basis j) (P.model.basis.ne_zero j)
        simpa only [Equiv.symm_symm, show ∀ u, em u = P.model.basis j • u from fun _ => rfl] using
          avgOver_uniform_equiv em.symm (fun u => ‖applyOperatorToState
            (S.placeSide .alice (heteroKron 1 (tauObservable W u)) -
              S.placeSide .bob (heteroKron 1 (tauObservable W u))) theta‖ ^ 2)
      have hsw : opDistSq (uniformDistribution (PauliRegister P))
          (fun u => S.placeSide .alice (heteroKron 1 (tauObservable W (P.model.basis j • u))))
          (fun u => S.placeSide .bob (heteroKron 1 (tauObservable W (P.model.basis j • u)))) theta =
        opDistSq (uniformDistribution (PauliRegister P))
          (fun u => S.placeSide .alice (tildeObs w .alice W u j))
          (fun u => S.placeSide .bob (tildeObs w .bob W u j)) S.psiHat := by
        let U := S.placeBoth (swapUnitary w .alice) (swapUnitary w .bob)
        have hU := S.placeBoth_swap_left_unitary w
        have ht (M N : Op _) : (conjBy U M - conjBy U N) * U = U * (M - N) := by
          simp only [conjBy]
          calc _ = U * (M - N) * (Uᴴ * U) := by noncomm_ring
            _ = _ := by rw [hU, Matrix.mul_one]
        have hc : opDistSq (uniformDistribution (PauliRegister P))
            (fun u => conjBy U (S.placeSide .alice (tildeObs w .alice W u j)))
            (fun u => conjBy U (S.placeSide .bob (tildeObs w .bob W u j))) theta =
            opDistSq (uniformDistribution (PauliRegister P))
              (fun u => S.placeSide .alice (tildeObs w .alice W u j))
              (fun u => S.placeSide .bob (tildeObs w .bob W u j)) S.psiHat := by
          unfold opDistSq opFamilyDistSq; simp only [Fintype.sum_unique]
          refine avgOver_congr _ _ _ fun u => ?_
          change ‖applyOperatorToState (_ - _) (applyOperatorToState U S.psiHat)‖ ^ 2 = _
          rw [← applyOperatorToState_mul, ht, MagicSquareRigidity.norm_applyOperatorToState_isometry_mul hU]
        dsimp only [U] at hc
        simp_rw [S.conjBy_placeBoth_swap_placeSide w .alice,
          S.conjBy_placeBoth_swap_placeSide w .bob, swapUnitary_conj_tildeObs w .alice W,
          swapUnitary_conj_tildeObs w .bob W] at hc
        exact hc
      exact (hre.trans hsw).trans_le (tildeObs_opDistSq_le hepsilon hepsilon_one hdeltaG S w W j)
  have htr : ‖reindexState e theta - applyOperatorToState
      (heteroKron 1 (Matrix.vecMulVec (fun x => eprState (PauliRegister P) x)
        (fun y => star (eprState (PauliRegister P) y)))) (reindexState e theta)‖ =
      ‖theta - applyOperatorToState S.extractionEprProjection theta‖ := by
    have h := WinImplications.norm_applyOperatorToState_reindexState e
      (1 - heteroKron 1 (Matrix.vecMulVec (fun x => eprState (PauliRegister P) x)
        (fun y => star (eprState (PauliRegister P) y)))) theta
    rw [WinImplications.reindexOp_sub, show reindexOp e (1 : Op _) = 1 by ext x y; simp [Matrix.one_apply]] at h
    simpa only [MagicSquareRigidity.applyOperatorToState_sub_op,
      MagicSquareRigidity.applyOperatorToState_one, ProjectiveSetting.extractionEprProjection] using h
  obtain ⟨aux, haux, hclose⟩ := S.exists_unit_aux_near_eprProjection theta (S.applyBoth_swap_norm w)
  refine ⟨aux, haux, ?_⟩
  have hpr := htr.symm.trans_le hdist
  change ‖theta - S.idealExpState aux‖ ^ 2 ≤ 16 * delta
  nlinarith [norm_nonneg (theta - S.idealExpState aux), Real.sqrt_nonneg delta, Real.sq_sqrt hdelta]

/-! ## Evaluated total-Pauli consistency, overlap transfer, and concrete Pauli comparison -/

theorem evaluated_pauli_tilde_consistency {P : AdmissibleParams} {epsilon deltaG : ℝ}
    (he : 0 ≤ epsilon) (hd : 0 ≤ deltaG) (S : ProjectiveSetting P epsilon)
    (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => S.placePlayer .alice ((S.pauliEvalMeas .alice W u).effect a))
        (fun u a => S.placeSide .bob (tildeM w .bob W (indicatorVec u) a)) S.psiHat ≤
      deltaConstructPaulis (2 + 4 * Real.sqrt 172) epsilon deltaG P.m P.d P.q ∧
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => S.placeSide .alice (tildeM w .alice W (indicatorVec u) a))
        (fun u a => S.placePlayer .bob ((S.pauliEvalMeas .bob W u).effect a)) S.psiHat ≤
      deltaConstructPaulis (2 + 4 * Real.sqrt 172) epsilon deltaG P.m P.d P.q := by
  classical
  let mu := uniformDistribution (Fin P.m → PauliScalar P)
  let PA := fun u => S.placedMeasurement .AA' (leftPlacedMeasurement (S.pointMeas .alice W u))
  let PB := fun u => S.placedMeasurement .BB' (leftPlacedMeasurement (S.pointMeas .bob W u))
  let QA := fun u => S.placedMeasurement .AA' (leftPlacedMeasurement (S.pauliEvalMeas .alice W u))
  let QB := fun u => S.placedMeasurement .BB' (leftPlacedMeasurement (S.pauliEvalMeas .bob W u))
  let T (side : PlayerSide) (u : Fin P.m → PauliScalar P) :=
    S.blockMeasurement side (Measurement.ofSumEqOne (tildeM w side W (indicatorVec u))
      (fun a => (tildeM_isProj w side W (indicatorVec u) a).nonneg)
      (sum_tildeM_eq_one w side W (indicatorVec u)))
  have hpts : consistencyDefect mu (fun u a => (PA u).effect a) (fun u a => (PB u).effect a) S.psiHat ≤
      86 * epsilon := by
    change consistencyDefect mu (fun u a => S.placePlayer .alice _) (fun u a => S.placePlayer .bob _) _ ≤ _
    rw [S.consistencyDefect_placePlayers]
    simpa only [pauli_edge_card, Nat.cast_ofNat] using point_self_consistency_le S W
  have hfw : consistencyDefect mu (fun u a => (PA u).effect a) (fun u a => (QB u).effect a) S.psiHat ≤
      86 * epsilon := by
    change consistencyDefect mu (fun u a => S.placePlayer .alice _) (fun u a => S.placePlayer .bob _) _ ≤ _
    rw [S.consistencyDefect_placePlayers]
    exact WinImplications.win_pauli_basis_cons_explicit P epsilon S he W
  have hrv : consistencyDefect mu (fun u a => (QA u).effect a) (fun u a => (PB u).effect a) S.psiHat ≤
      86 * epsilon := by
    change consistencyDefect mu (fun u a => S.placePlayer .alice _) (fun u a => S.placePlayer .bob _) _ ≤ _
    rw [S.consistencyDefect_placePlayers]
    exact WinImplications.win_pauli_basis_cons_interchanged_explicit P epsilon S he W
  obtain ⟨hr, hl⟩ := tilde_m_consistent_point_meas_both he hd S w W
  have hsc : deltaConstructPaulis (2 + 2 * Real.sqrt 172) epsilon deltaG P.m P.d P.q +
      2 * Real.sqrt (86 * epsilon + 86 * epsilon) ≤
      deltaConstructPaulis (2 + 4 * Real.sqrt 172) epsilon deltaG P.m P.d P.q := by
    rw [← add_mul, show (86 : ℝ) + 86 = 172 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 172)]
    unfold deltaConstructPaulis
    have : 0 ≤ ((P.m * P.d : ℕ) : ℝ) / P.q := by positivity
    nlinarith [Real.sqrt_nonneg (172 : ℝ), Real.sqrt_nonneg epsilon]
  constructor
  · change consistencyDefect mu (fun u a => (QA u).effect a) (fun u a => (T .bob u).effect a) S.psiHat ≤ _
    rw [consistencyDefect_measurement_symm]
    exact (consistencyDefect_trans_le mu (T .bob) PA PB QA S.psiHat _ _ _
      (uniformDistribution_isProbability _) S.psiHat_norm
      (by rw [consistencyDefect_measurement_symm]; exact hr)
      (by rw [consistencyDefect_measurement_symm]; exact hpts)
      (by rw [consistencyDefect_measurement_symm]; exact hrv)).trans hsc
  · exact (consistencyDefect_trans_le mu (T .alice) PB PA QB S.psiHat _ _ _
      (uniformDistribution_isProbability _) S.psiHat_norm hl hpts hfw).trans hsc

theorem pauli_distance_on_ideal_le {P : AdmissibleParams} {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Measurement (PauliRegister P) (I × PauliRegister P)) (W : PauliKind)
    (aux : EuclideanSpace ℂ (I × J)) (haux : ‖aux‖ = 1)
    (theta : EuclideanSpace ℂ ((I × PauliRegister P) × (J × PauliRegister P)))
    (htheta : ‖theta‖ = 1) :
    let ideal := reindexState prodShuffle (vecTensor aux (eprState (PauliRegister P)))
    let B := rightPlacedMeasurement (ιA := J) (pauliRegisterMeas (P := P) W)
    (∑ h : PauliRegister P, ‖applyOperatorToState
      (heteroKron (A.effect h - heteroKron (1 : Op I) (pauliProj W h))
        (1 : Op (J × PauliRegister P))) ideal‖ ^ 2) ≤
      2 * (1 - avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun u =>
        ∑ a : PauliScalar P, stateQForm theta
          (heteroKron ((A.postprocess (fun h => evalPoly (encodingPoly h) u)).effect a)
            ((B.postprocess (fun h => evalPoly (encodingPoly h) u)).effect a)))) +
        2 * ((P.m * P.d : ℝ) / P.q) + 4 * ‖theta - ideal‖ := by
  dsimp only
  let ideal := reindexState prodShuffle (vecTensor aux (eprState (PauliRegister P)))
  let B := rightPlacedMeasurement (ιA := J) (pauliRegisterMeas (P := P) W)
  have hideal : ‖ideal‖ = 1 := by
    rw [reindexState_norm_eq, vecTensor_norm_eq, haux, eprState_norm, one_mul]
  have hd := point_distance_le_two_defect (leftPlacedMeasurement (ιB := J × PauliRegister P) A)
    (rightPlacedMeasurement (ιA := I × PauliRegister P) B) ideal
  rw [point_defect_eq, hideal, one_pow] at hd
  have hact (h : PauliRegister P) :
      applyOperatorToState (heteroKron (A.effect h - heteroKron (1 : Op I) (pauliProj W h))
        (1 : Op (J × PauliRegister P))) ideal =
      applyOperatorToState ((leftPlacedMeasurement (ιB := J × PauliRegister P) A).effect h -
        (rightPlacedMeasurement (ιA := I × PauliRegister P) B).effect h) ideal := by
    have hepr : applyOperatorToState (heteroKron (heteroKron (1 : Op I) (pauliProj W h)) (1 : Op (J × _))) ideal =
        applyOperatorToState (heteroKron (1 : Op (I × _)) (heteroKron (1 : Op J) (pauliProj W h))) ideal := by
      ext p; simp only [applyOperatorToState, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
        Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
      simp [heteroKron, Matrix.kronecker, Matrix.one_apply, reindexState, vecTensor, eprState,
        prodShuffle, mul_ite, ite_mul, Prod.ext_iff, ite_and, ideal]
      rw [show pauliProj W h p.2.2 p.1.2 = pauliProj W h p.1.2 p.2.2 from
        congrFun (congrFun (pauliProj_transpose W h) p.1.2) p.2.2]; simp
    change applyOperatorToState (heteroKron (A.effect h - _) _) ideal =
      applyOperatorToState (heteroKron (A.effect h) _ - heteroKron _ (heteroKron _ (pauliProj W h))) ideal
    rw [heteroKron_sub_left, MagicSquareRigidity.applyOperatorToState_sub_op,
      MagicSquareRigidity.applyOperatorToState_sub_op, hepr]
  rw [Finset.sum_congr rfl fun h _ => congrArg (‖·‖ ^ 2) (hact h)]
  have hov : avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun u =>
      ∑ a, stateQForm theta (heteroKron ((A.postprocess (fun h => evalPoly (encodingPoly h) u)).effect a)
        ((B.postprocess (fun h => evalPoly (encodingPoly h) u)).effect a))) ≤
      (∑ h, stateQForm ideal (heteroKron (A.effect h) (B.effect h))) +
        (P.m * P.d : ℝ) / P.q + 2 * ‖theta - ideal‖ := by
    have hst : ∀ u, (∑ a, stateQForm theta (heteroKron
        ((A.postprocess (fun h => evalPoly (encodingPoly h) u)).effect a)
        ((B.postprocess (fun h => evalPoly (encodingPoly h) u)).effect a))) -
        (∑ a, stateQForm ideal (heteroKron
        ((A.postprocess (fun h => evalPoly (encodingPoly h) u)).effect a)
        ((B.postprocess (fun h => evalPoly (encodingPoly h) u)).effect a))) ≤ 2 * ‖theta - ideal‖ := by
      intro u
      let MA := A.postprocess (fun h => evalPoly (encodingPoly h) u)
      let MB := B.postprocess (fun h => evalPoly (encodingPoly h) u)
      let s := Finset.univ.filter fun ab : PauliScalar P × PauliScalar P => ab.1 = ab.2
      let T := ∑ ab ∈ s, (tensorMeasurement MA MB).effect ab
      have hT (v) : ‖applyOperatorToState T v‖ ≤ ‖v‖ := by
        have hp : 0 ≤ T := Finset.sum_nonneg fun a _ => (tensorMeasurement MA MB).pos a
        have hl : T ≤ 1 := (tensorMeasurement MA MB).sum_eq_one ▸
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
            fun a _ _ => (tensorMeasurement MA MB).pos a
        apply MagicSquareRigidity.norm_applyOperatorToState_le
        rw [(Matrix.nonneg_iff_posSemidef.mp hp).isHermitian.eq]
        exact (MIPStarRE.Quantum.sq_le_self hp hl).trans hl
      have heq (φ) : stateQForm φ T = ∑ a, stateQForm φ (heteroKron (MA.effect a) (MB.effect a)) := by
        rw [← stateQForm_finset_sum]
        congr 1; simp [T, s, Finset.sum_filter, Fintype.sum_prod_type, tensorMeasurement, Measurement.ofSumEqOne]
      rw [← heq theta, ← heq ideal]
      have hsp : stateQForm theta T - stateQForm ideal T =
          (inner ℂ (theta - ideal) (applyOperatorToState T theta)).re +
            (inner ℂ ideal (applyOperatorToState T (theta - ideal))).re := by
        simp [stateQForm, applyOperatorToState]
      rw [hsp]
      have h1 := ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm (theta - ideal) _)).trans
        (mul_le_mul_of_nonneg_left (hT theta) (norm_nonneg _))
      have h2 := ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm ideal _)).trans
        (mul_le_mul_of_nonneg_left (hT (theta - ideal)) (norm_nonneg _))
      rw [htheta] at h1; rw [hideal] at h2
      linarith [le_abs_self (inner ℂ (theta - ideal) (applyOperatorToState T theta)).re,
        le_abs_self (inner ℂ ideal (applyOperatorToState T (theta - ideal))).re]
    have ht := avgOver_mono (uniformDistribution (Fin P.m → PauliScalar P)) _ _ hst
    rw [avgOver_sub, avgOver_const_of_isProbability _ (uniformDistribution_isProbability _)] at ht
    have hc := SandwichProduct.avg_diagonal_postprocess_stateQForm_le A B ideal
      (fun h u => evalPoly (encodingPoly h) u) ((P.m * P.d : ℝ) / P.q) hideal (by positivity)
      fun h k hne => poly_eval_collision_le _ _ fun heq => hne <| by
        simpa only [decodeFq_lowDegreeEncoding] using congrArg decodeFq heq
    linarith
  simp only [leftPlacedMeasurement, rightPlacedMeasurement, Measurement.ofSumEqOne,
    placed_product_stateQForm_eq] at hd
  exact hd.trans (by dsimp [B] at hov ⊢; linarith)

theorem norm_reindexState_sub_eq {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (psi phi : EuclideanSpace ℂ I) :
    ‖reindexState e psi - reindexState e phi‖ = ‖psi - phi‖ :=
  reindexState_norm_eq e (psi - phi)

theorem pauli_distance_on_ideal_right_le {P : AdmissibleParams} {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Measurement (PauliRegister P) (J × PauliRegister P)) (W : PauliKind)
    (aux : EuclideanSpace ℂ (I × J)) (haux : ‖aux‖ = 1)
    (theta : EuclideanSpace ℂ ((I × PauliRegister P) × (J × PauliRegister P)))
    (htheta : ‖theta‖ = 1) :
    let ideal := reindexState prodShuffle (vecTensor aux (eprState (PauliRegister P)))
    let B := rightPlacedMeasurement (ιA := I) (pauliRegisterMeas (P := P) W)
    (∑ h : PauliRegister P, ‖applyOperatorToState
      (heteroKron (1 : Op (I × PauliRegister P))
        (A.effect h - heteroKron (1 : Op J) (pauliProj W h))) ideal‖ ^ 2) ≤
      2 * (1 - avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun u =>
        ∑ a : PauliScalar P, stateQForm theta
          (heteroKron ((B.postprocess (fun h => evalPoly (encodingPoly h) u)).effect a)
            ((A.postprocess (fun h => evalPoly (encodingPoly h) u)).effect a)))) +
        2 * ((P.m * P.d : ℝ) / P.q) + 4 * ‖theta - ideal‖ := by
  let e := Equiv.prodComm (I × PauliRegister P) (J × PauliRegister P)
  let ideal := reindexState prodShuffle (vecTensor aux (eprState (PauliRegister P)))
  have hideal : reindexState prodShuffle
      (vecTensor (reindexState (Equiv.prodComm I J) aux) (eprState (PauliRegister P))) =
      reindexState e ideal := by
    ext p; simp [reindexState, vecTensor, prodShuffle, eprState, e, ideal, eq_comm]
  have h := pauli_distance_on_ideal_le A W (reindexState (Equiv.prodComm I J) aux)
    (by rw [reindexState_norm_eq, haux]) (reindexState e theta) (by rw [reindexState_norm_eq, htheta])
  dsimp only at h ⊢
  rw [hideal, norm_reindexState_sub_eq] at h
  dsimp only [e] at h
  simp_rw [WinImplications.norm_applyOperatorToState_reindexState,
    WinImplications.stateQForm_reindexState, WinImplications.reindexOp_prodComm_heteroKron] at h
  exact h

namespace ProjectiveSetting

section PauliTransport
variable {P : AdmissibleParams} {epsilon deltaG : ℝ} (S : ProjectiveSetting P epsilon)

open scoped Classical

def swappedPauliMeas (w : GlobalPairWitness S deltaG) (side : PlayerSide)
    (W : PauliKind) : Measurement (PauliRegister P) (ExtractionBlock P (S.LocalSpace side)) :=
  Measurement.ofSumEqOne
    (fun h => conjBy (swapUnitary w side) (S.onPlayer side ((S.pauliMeas side W).effect h)))
    (fun h => by
      apply star_right_conjugate_nonneg
      exact kronecker_nonneg
        (kronecker_nonneg ((S.pauliMeas side W).pos h) Matrix.PosSemidef.one.nonneg)
        Matrix.PosSemidef.one.nonneg)
    (by simp only [conjBy, onPlayer, ← Finset.sum_mul, ← Matrix.mul_sum,
      ← heteroKron_finset_sum_left, (S.pauliMeas side W).sum_eq_one,
      heteroKron_one_one, Matrix.mul_one, swapUnitary_mul_conjTranspose])

theorem placeSide_onPlayer (side : PlayerSide) (A : Op (S.LocalSpace side)) :
    S.placeSide side (S.onPlayer side A) = S.placePlayer side A := by
  cases side
  · exact S.placeSide_alice_tensor_one _
  · exact S.placeSide_bob_tensor_one _

theorem placeSide_swappedPauliMeas (w : GlobalPairWitness S deltaG)
    (side : PlayerSide) (W : PauliKind) (h : PauliRegister P) :
    S.placeSide side ((S.swappedPauliMeas w side W).effect h) =
      conjBy (S.placeSide side (swapUnitary w side)) (S.placePlayer side ((S.pauliMeas side W).effect h)) := by
  have hcb (U A : Op (ExtractionBlock P (S.LocalSpace side))) :
      S.placeSide side (conjBy U A) = conjBy (S.placeSide side U) (S.placeSide side A) := by
    cases side <;>
      simp only [placeSide, conjBy, ← reindexOp_conjTranspose, ← WinImplications.reindexOp_mul,
        MagicSquareRigidity.heteroKron_conjTranspose, heteroKron_mul,
        Matrix.conjTranspose_one, Matrix.mul_one] <;> rfl
  exact (hcb _ _).trans (congrArg _ (S.placeSide_onPlayer side _))

set_option maxHeartbeats 800000 in
theorem extraction_pauli_dist_le (w : GlobalPairWitness S deltaG)
    (aux : EuclideanSpace ℂ (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB))
    (haux : ‖aux‖ = 1) (side : PlayerSide) (W : PauliKind) :
    opFamilyDistSq (uniformDistribution Unit)
      (fun _ h => conjBy (S.placeSide side (swapUnitary w side))
        (S.placePlayer side ((S.pauliMeas side W).effect h)))
      (fun _ h => S.placeExtractedRegister side (pauliProj W h)) (S.idealExpState aux) ≤
      2 * (match side with
        | .alice => consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
            (fun u a => S.placePlayer .alice ((S.pauliEvalMeas .alice W u).effect a))
            (fun u a => S.placeSide .bob (tildeM w .bob W (indicatorVec u) a)) S.psiHat
        | .bob => consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
            (fun u a => S.placeSide .alice (tildeM w .alice W (indicatorVec u) a))
            (fun u a => S.placePlayer .bob ((S.pauliEvalMeas .bob W u).effect a)) S.psiHat) +
      2 * ((P.m * P.d : ℝ) / P.q) +
      4 * ‖S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat - S.idealExpState aux‖ := by
  let e := sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB
  let theta := S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat
  have htheta : ‖reindexState e theta‖ = 1 := (reindexState_norm_eq e theta).trans (S.applyBoth_swap_norm w)
  have hsub (A B : Op (ExtractionBlock P (S.LocalSpace side))) :
      S.placeSide side (A - B) = S.placeSide side A - S.placeSide side B := by
    cases side <;> ext r c <;> [exact sub_mul _ _ _; exact mul_sub _ _ _]
  have hext (T : Op (PauliRegister P)) :
      S.placeSide side (heteroKron (1 : Op (S.ExpandedLocalSpace side)) T) =
        S.placeExtractedRegister side T := by
    cases side
    · ext r c; change ((if (r.1.1, r.1.2.1) = (c.1.1, c.1.2.1) then (1 : ℂ) else 0) * T r.1.2.2 c.1.2.2) *
          (if ((r.2.1, r.2.2.1), r.2.2.2) = ((c.2.1, c.2.2.1), c.2.2.2) then 1 else 0) =
        (if r.1.1 = c.1.1 then 1 else 0) * (if r.1.2.1 = c.1.2.1 then 1 else 0) *
          ((if r.2.1 = c.2.1 then 1 else 0) * T r.1.2.2 c.1.2.2) *
          (if r.2.2.1 = c.2.2.1 then 1 else 0) * (if r.2.2.2 = c.2.2.2 then 1 else 0)
      simp only [Prod.mk.injEq, ite_and, ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero]
      split_ifs <;> rfl
    · ext r c; change (if ((r.1.1, r.1.2.1), r.1.2.2) = ((c.1.1, c.1.2.1), c.1.2.2) then (1 : ℂ) else 0) *
          ((if (r.2.1, r.2.2.1) = (c.2.1, c.2.2.1) then 1 else 0) * T r.2.2.2 c.2.2.2) =
        ((if r.1.1 = c.1.1 then 1 else 0) * T r.2.2.2 c.2.2.2) *
          (if r.1.2.1 = c.1.2.1 then 1 else 0) * (if r.1.2.2 = c.1.2.2 then 1 else 0) *
          (if r.2.1 = c.2.1 then 1 else 0) * (if r.2.2.1 = c.2.2.1 then 1 else 0)
      simp only [Prod.mk.injEq, ite_and, ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero]
      split_ifs <;> rfl
  have hsum : opFamilyDistSq (uniformDistribution Unit)
      (fun _ h => conjBy (S.placeSide side (swapUnitary w side))
        (S.placePlayer side ((S.pauliMeas side W).effect h)))
      (fun _ h => S.placeExtractedRegister side (pauliProj W h)) (S.idealExpState aux) =
      ∑ h, ‖applyOperatorToState (S.placeSide side
        ((S.swappedPauliMeas w side W).effect h - heteroKron 1 (pauliProj W h)))
        (S.idealExpState aux)‖ ^ 2 := by
    simp_rw [hsub, S.placeSide_swappedPauliMeas, hext]; exact avgOver_uniform_const _
  rw [hsum]
  have hsw_ev (sd : PlayerSide) (u : Fin P.m → PauliScalar P) (a : PauliScalar P) :
      ((S.swappedPauliMeas w sd W).postprocess (fun h => evalPoly (encodingPoly h) u)).effect a =
        conjBy (swapUnitary w sd) (S.onPlayer sd ((S.pauliEvalMeas sd W u).effect a)) := by
    simp only [swappedPauliMeas, Measurement.postprocess_effect, Measurement.ofSumEqOne,
      pauliEvalMeas, conjBy, onPlayer, ← Finset.sum_mul, ← Matrix.mul_sum,
      ← heteroKron_finset_sum_left]; rfl
  have hcan_ev (sd : PlayerSide) (u : Fin P.m → PauliScalar P) (a : PauliScalar P) :
      ((rightPlacedMeasurement (ιA := S.ExpandedLocalSpace sd) (pauliRegisterMeas (P := P) W)).postprocess
        (fun h => evalPoly (encodingPoly h) u)).effect a =
        conjBy (swapUnitary w sd) (tildeM w sd W (indicatorVec u) a) := by
    rw [swapUnitary_conj_tildeM]
    simp only [Measurement.postprocess_effect, rightPlacedMeasurement, Measurement.ofSumEqOne,
      pauliRegisterMeas, bracketOp, ← heteroKron_finset_sum_right]; rfl
  have hbl_ov (A : (Fin P.m → PauliScalar P) → Measurement (PauliScalar P) (ExtractionBlock P S.toStrategy.ιA))
      (B : (Fin P.m → PauliScalar P) → Measurement (PauliScalar P) (ExtractionBlock P S.toStrategy.ιB)) :
      avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun u => ∑ a, stateQForm (reindexState e theta)
        (heteroKron (conjBy (swapUnitary w .alice) ((A u).effect a))
          (conjBy (swapUnitary w .bob) ((B u).effect a)))) =
      1 - consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => S.placeSide .alice ((A u).effect a))
        (fun u a => S.placeSide .bob ((B u).effect a)) S.psiHat := by
    have hc := consistencyDefect_eq_one_sub_overlap _
      (fun u => S.blockMeasurement .alice (A u)) (fun u => S.blockMeasurement .bob (B u))
      S.psiHat (uniformDistribution_isProbability _) S.psiHat_norm
    simp only [blockMeasurement_effect] at hc
    rw [hc, sub_sub_cancel]
    refine avgOver_congr _ _ _ fun u => Finset.sum_congr rfl fun a _ => ?_
    have hrk (M : Op (ExtractionBlock P S.toStrategy.ιA))
        (N : Op (ExtractionBlock P S.toStrategy.ιB)) :
        reindexOp e (heteroKron M N) = S.placeSide .alice M * S.placeSide .bob N := by
      simp only [e, placeSide, ← WinImplications.reindexOp_mul, heteroKron_mul,
        Matrix.mul_one, Matrix.one_mul]
    rw [WinImplications.stateQForm_reindexState, hrk]
    erw [← S.conjBy_placeBoth_swap_placeSide w .alice, ← S.conjBy_placeBoth_swap_placeSide w .bob]
    let U := S.placeBoth (swapUnitary w .alice) (swapUnitary w .bob)
    have hU := S.placeBoth_swap_left_unitary w
    let X := S.placeSide .alice ((A u).effect a)
    let Y := S.placeSide .bob ((B u).effect a)
    change stateQForm (applyOperatorToState U S.psiHat) (conjBy U X * conjBy U Y) = stateQForm S.psiHat (X * Y)
    rw [← stateQForm_conjTranspose_mul_mul]; congr 1; simp only [conjBy]
    calc Uᴴ * (U * X * Uᴴ * (U * Y * Uᴴ)) * U = (Uᴴ * U) * X * (Uᴴ * U) * Y * (Uᴴ * U) := by noncomm_ring
      _ = X * Y := by rw [hU]; simp
  cases side
  · have h := pauli_distance_on_ideal_le (S.swappedPauliMeas w .alice W) W aux haux
      (reindexState e theta) htheta
    dsimp only at h
    have hov : avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun u => ∑ a,
        stateQForm (reindexState e theta)
          (heteroKron (((S.swappedPauliMeas w .alice W).postprocess (fun h => evalPoly (encodingPoly h) u)).effect a)
            (((rightPlacedMeasurement (ιA := S.ExpandedLocalSpace .bob) (pauliRegisterMeas (P := P) W)).postprocess
              (fun h => evalPoly (encodingPoly h) u)).effect a))) =
        1 - consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
          (fun u a => S.placePlayer .alice ((S.pauliEvalMeas .alice W u).effect a))
          (fun u a => S.placeSide .bob (tildeM w .bob W (indicatorVec u) a)) S.psiHat := by
      simp only [hsw_ev .alice]; simp_rw [hcan_ev .bob]
      have hb := hbl_ov
        (fun u => leftPlacedMeasurement (leftPlacedMeasurement (S.pauliEvalMeas .alice W u)))
        (fun u => Measurement.ofSumEqOne (tildeM w .bob W (indicatorVec u))
          (fun a => (tildeM_isProj w .bob W (indicatorVec u) a).nonneg)
          (sum_tildeM_eq_one w .bob W (indicatorVec u)))
      convert hb.trans (congrArg (fun f => 1 - consistencyDefect _ f _ S.psiHat)
        (funext fun u => funext fun a => S.placeSide_onPlayer .alice _)) using 1 <;> rfl
    erw [hov, sub_sub_cancel, show reindexState prodShuffle (vecTensor aux (eprState (PauliRegister P))) =
      reindexState e (S.idealExpState aux) from rfl, norm_reindexState_sub_eq] at h
    convert h using 1
    exact Finset.sum_congr rfl fun l _ => congrArg (· ^ 2)
      (WinImplications.norm_applyOperatorToState_reindexState e _ _).symm
  · have h := pauli_distance_on_ideal_right_le (S.swappedPauliMeas w .bob W) W aux haux
      (reindexState e theta) htheta
    dsimp only at h
    have hov : avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun u => ∑ a,
        stateQForm (reindexState e theta)
          (heteroKron (((rightPlacedMeasurement (ιA := S.ExpandedLocalSpace .alice) (pauliRegisterMeas (P := P) W)).postprocess
              (fun h => evalPoly (encodingPoly h) u)).effect a)
            (((S.swappedPauliMeas w .bob W).postprocess (fun h => evalPoly (encodingPoly h) u)).effect a))) =
        1 - consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
          (fun u a => S.placeSide .alice (tildeM w .alice W (indicatorVec u) a))
          (fun u a => S.placePlayer .bob ((S.pauliEvalMeas .bob W u).effect a)) S.psiHat := by
      simp only [hsw_ev .bob]; simp_rw [hcan_ev .alice]
      have hb := hbl_ov
        (fun u => Measurement.ofSumEqOne (tildeM w .alice W (indicatorVec u))
          (fun a => (tildeM_isProj w .alice W (indicatorVec u) a).nonneg)
          (sum_tildeM_eq_one w .alice W (indicatorVec u)))
        (fun u => leftPlacedMeasurement (leftPlacedMeasurement (S.pauliEvalMeas .bob W u)))
      convert hb.trans (congrArg (fun f => 1 - consistencyDefect _ _ f S.psiHat)
        (funext fun u => funext fun a => S.placeSide_onPlayer .bob _)) using 1 <;> rfl
    erw [hov, sub_sub_cancel, show reindexState prodShuffle (vecTensor aux (eprState (PauliRegister P))) =
      reindexState e (S.idealExpState aux) from rfl, norm_reindexState_sub_eq] at h
    convert h using 1
    exact Finset.sum_congr rfl fun l _ => congrArg (· ^ 2)
      (WinImplications.norm_applyOperatorToState_reindexState e _ _).symm

end PauliTransport
end ProjectiveSetting

/-! ## Extraction witness and error-scale absorption -/

structure ExtractionWitness {P : AdmissibleParams} {epsilon deltaS : ℝ}
    (S : ProjectiveSetting P epsilon) (w : GlobalPairWitness S deltaS) (delta : ℝ) where
  swap_right_unitary : ∀ side : PlayerSide, swapUnitary w side * (swapUnitary w side)ᴴ = 1
  swap_left_unitary : ∀ side : PlayerSide, (swapUnitary w side)ᴴ * swapUnitary w side = 1
  aux : EuclideanSpace ℂ (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB)
  aux_norm : ‖aux‖ = 1
  state_close :
    ‖S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat - S.idealExpState aux‖ ^ 2 ≤ delta
  pauli_close : ∀ (side : PlayerSide) (W : PauliKind),
    opFamilyDistSq (uniformDistribution Unit)
      (fun _ h => conjBy (S.placeSide side (swapUnitary w side))
        (S.placePlayer side ((S.pauliMeas side W).effect h)))
      (fun _ h => S.placeExtractedRegister side (pauliProj W h)) (S.idealExpState aux) ≤ delta

theorem exists_extractionWitness :
    ∃ a b C : ℝ, 1 < a ∧ 0 < b ∧ b < 1 ∧ 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (epsilon : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → ∀ S : ProjectiveSetting P epsilon,
          ∃ w : GlobalPairWitness S (deltaQld a b epsilon P.m P.d P.q),
            Nonempty (ExtractionWitness S w
              (deltaExtract C (deltaConstructPaulis C epsilon
                (deltaQld a b epsilon P.m P.d P.q) P.m P.d P.q) P.m P.d P.q)) := by
  obtain ⟨a, b, ha, hb, hb1, hglobal⟩ := exists_globalPairWitness
  let C : ℝ := pauliBaselineExtractionConstant
  refine ⟨a, b, C, ha, hb, hb1, by unfold C pauliBaselineExtractionConstant; norm_num, ?_⟩
  intro P epsilon heps0 heps1 S
  obtain ⟨w⟩ := hglobal P epsilon S
  refine ⟨w, ?_⟩
  have hdeltaG : 0 ≤ deltaQld a b epsilon P.m P.d P.q := by
    simp only [deltaQld, Real.rpow_eq_pow]; positivity
  let delta := deltaConstructPaulis C epsilon (deltaQld a b epsilon P.m P.d P.q) P.m P.d P.q
  have hdelta : 0 ≤ delta := by
    dsimp [delta, C, deltaConstructPaulis, pauliBaselineExtractionConstant]; positivity
  by_cases hd1 : delta ≤ 1
  · obtain ⟨aux, haux, hclose⟩ :=
      exists_extraction_aux_of_global_pair_witness heps0 heps1 hdeltaG S w
    have hnorm : ‖S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat -
        S.idealExpState aux‖ ≤ 4 * Real.sqrt delta := by
      nlinarith [Real.sq_sqrt hdelta, Real.sqrt_nonneg delta, norm_nonneg
        (S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat - S.idealExpState aux)]
    have hrt := Real.self_le_rpow_of_le_one hdelta hd1 (by norm_num : (1 / 4 : ℝ) ≤ 1)
    have hsq : Real.sqrt delta ≤ delta ^ (1 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_ge' hdelta hd1 (by norm_num) (by norm_num)
    have hr : 0 ≤ (((P.m * P.d : ℕ) : ℝ) / P.q) := by positivity
    have hC18 : 18 ≤ C := by dsimp [C, pauliBaselineExtractionConstant]; norm_num
    have hp := mul_le_mul_of_nonneg_right hC18 (add_nonneg (Real.rpow_nonneg hdelta (1 / 4)) hr)
    refine ⟨⟨swapUnitary_mul_conjTranspose w, conjTranspose_mul_swapUnitary w, aux, haux,
      hclose.trans ((by nlinarith : 16 * delta ≤ 18 * _).trans hp), fun side W => ?_⟩⟩
    have he := evaluated_pauli_tilde_consistency heps0 hdeltaG S w W
    have hCE : 2 + 4 * Real.sqrt 172 ≤ C := by
      dsimp [C, pauliBaselineExtractionConstant]
      nlinarith [Real.sqrt_nonneg (172 : ℝ), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 172)]
    have hm := mul_le_mul_of_nonneg_right hCE
      (show 0 ≤ deltaQld a b epsilon P.m P.d P.q + Real.sqrt epsilon + ((P.m * P.d : ℕ) : ℝ) / P.q
        by positivity)
    have h1 : consistencyDefect _ _ _ S.psiHat ≤ delta := he.1.trans hm
    have h2 : consistencyDefect _ _ _ S.psiHat ≤ delta := he.2.trans hm
    have hub := ((by nlinarith :
      2 * delta + 2 * (((P.m * P.d : ℕ) : ℝ) / P.q) + 16 * Real.sqrt delta ≤ 18 * _).trans hp)
    cases side <;> refine (S.extraction_pauli_dist_le w aux haux _ W).trans (le_trans ?_ hub) <;>
      (dsimp only; push_cast at hub ⊢; linarith)
  · have h4 : 4 ≤ deltaExtract C delta P.m P.d P.q := by
      have hrt := Real.one_le_rpow (le_of_not_ge hd1) (by norm_num : (0 : ℝ) ≤ 1 / 4)
      have hr : 0 ≤ ((P.m * P.d : ℕ) : ℝ) / P.q := by positivity
      have hC4 : 4 ≤ C := by dsimp [C, pauliBaselineExtractionConstant]; norm_num
      exact hC4.trans (le_mul_of_one_le_right (by linarith) (hrt.trans (le_add_of_nonneg_right hr)))
    refine ⟨⟨swapUnitary_mul_conjTranspose w, conjTranspose_mul_swapUnitary w,
      S.extractionAuxReference, S.extractionAuxReference_norm, ?_, fun side W =>
        (S.extraction_pauli_dist_le_four w _ S.extractionAuxReference_norm side W).trans h4⟩⟩
    have hn := norm_sub_le (S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat)
      (S.idealExpState S.extractionAuxReference)
    rw [S.applyBoth_swap_norm w, S.idealExpState_norm, S.extractionAuxReference_norm] at hn
    nlinarith [norm_nonneg (S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat -
      S.idealExpState S.extractionAuxReference)]

theorem deltaExtract_le_deltaQld (C a b : ℝ) (hC : 1 ≤ C) (ha : 1 < a)
    (hb : 0 < b) (hb1 : b < 1) :
    ∃ a' b' : ℝ, 1 ≤ a' ∧ 0 < b' ∧ b' < 1 ∧
      ∀ (P : AdmissibleParams) (epsilon : ℝ), 0 ≤ epsilon → epsilon ≤ 1 →
        deltaExtract C (deltaConstructPaulis C epsilon
          (deltaQld a b epsilon P.m P.d P.q) P.m P.d P.q) P.m P.d P.q ≤
        deltaQld a' b' epsilon P.m P.d P.q := by
  have hC0 : 0 ≤ C := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hconst : a ≤ 4 * C ^ 2 * a := by
    nlinarith [mul_le_mul_of_nonneg_right (show 1 ≤ C ^ 2 by nlinarith) ha0]
  refine ⟨4 * C ^ 2 * a, b / 8, ha.le.trans hconst, by positivity, by linarith, ?_⟩
  intro P eps he0 he1
  let deg : ℝ := ((P.m * P.d : ℕ) : ℝ)
  have hd1 : 1 ≤ deg := Nat.one_le_cast.mpr (Nat.mul_pos P.one_le_m P.hd)
  have hd0 : 0 ≤ deg := by linarith
  have hq1 : (1 : ℝ) ≤ P.q := by
    obtain ⟨s, -, hs⟩ := P.hq; rw [hs]; exact_mod_cast Nat.one_le_pow _ _ (by norm_num)
  have hq0 : (0 : ℝ) ≤ P.q := by positivity
  let amp : ℝ := a * deg ^ a
  let rt : ℝ := eps ^ (b / 8) + (P.q : ℝ) ^ (-(b / 8)) + (2 : ℝ) ^ (-((b / 8) * deg))
  have hamp1 : 1 ≤ amp := one_le_mul_of_one_le_of_one_le ha.le (Real.one_le_rpow hd1 ha0)
  have hamp0 : 0 ≤ amp := by linarith
  have hdeg_amp : deg ≤ amp :=
    (Real.self_le_rpow_of_one_le hd1 ha.le).trans (le_mul_of_one_le_left (Real.rpow_nonneg hd0 a) ha.le)
  have hrt0 : 0 ≤ rt := by dsimp [rt]; positivity
  have he_rt : eps ^ (b / 8) ≤ rt := by
    dsimp [rt]; linarith [Real.rpow_nonneg hq0 (-(b / 8)),
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-((b / 8) * deg))]
  have hq_rt : (P.q : ℝ) ^ (-(b / 8)) ≤ rt := by
    dsimp [rt]; linarith [Real.rpow_nonneg he0 (b / 8),
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-((b / 8) * deg))]
  have hrs {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
      (x + y + z) ^ (1 / 4 : ℝ) ≤ x ^ (1 / 4 : ℝ) + y ^ (1 / 4 : ℝ) + z ^ (1 / 4 : ℝ) :=
    (Real.rpow_add_le_add_rpow (add_nonneg hx hy) hz (by norm_num) (by norm_num)).trans
      (add_le_add (Real.rpow_add_le_add_rpow hx hy (by norm_num) (by norm_num)) le_rfl)
  have hrt_root : (eps ^ b + (P.q : ℝ) ^ (-b) + (2 : ℝ) ^ (-(b * deg))) ^ (1 / 4 : ℝ) ≤ rt := by
    refine (hrs (by positivity) (by positivity) (by positivity)).trans ?_
    rw [← Real.rpow_mul he0, ← Real.rpow_mul hq0, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact add_le_add (add_le_add
      (Real.rpow_le_rpow_of_exponent_ge' he0 he1 (by positivity) (by linarith))
      (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)))
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [mul_nonneg hb.le hd0]))
  have hg0 : 0 ≤ deltaQld a b eps P.m P.d P.q := by simp only [deltaQld, Real.rpow_eq_pow]; positivity
  have hg_rt : (deltaQld a b eps P.m P.d P.q) ^ (1 / 4 : ℝ) ≤ amp * rt := by
    change (amp * (eps ^ b + (P.q : ℝ) ^ (-b) + (2 : ℝ) ^ (-(b * deg)))) ^ (1 / 4 : ℝ) ≤ amp * rt
    rw [Real.mul_rpow hamp0 (by positivity)]
    exact mul_le_mul (Real.rpow_le_self_of_one_le hamp1 (by norm_num)) hrt_root (by positivity) hamp0
  have hsq_rt : (Real.sqrt eps) ^ (1 / 4 : ℝ) ≤ amp * rt := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul he0]
    exact ((Real.rpow_le_rpow_of_exponent_ge' he0 he1 (by positivity) (by linarith)).trans he_rt).trans
      (le_mul_of_one_le_left hrt0 hamp1)
  have hrat_rt : (deg / (P.q : ℝ)) ^ (1 / 4 : ℝ) ≤ amp * rt := by
    rw [Real.div_rpow hd0 hq0, div_eq_mul_inv, ← Real.rpow_neg hq0]
    exact mul_le_mul ((Real.rpow_le_self_of_one_le hd1 (by norm_num)).trans hdeg_amp)
      ((Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)).trans hq_rt) (by positivity) hamp0
  have hrat : deg / (P.q : ℝ) ≤ amp * rt := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one]
    exact mul_le_mul hdeg_amp ((Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)).trans hq_rt)
      (by positivity) hamp0
  have hc_rt : (deltaConstructPaulis C eps (deltaQld a b eps P.m P.d P.q) P.m P.d P.q) ^ (1 / 4 : ℝ) ≤
      3 * C * amp * rt := by
    unfold deltaConstructPaulis; rw [Real.mul_rpow hC0 (by positivity)]
    refine (mul_le_mul (Real.rpow_le_self_of_one_le hC (by norm_num))
      (hrs hg0 (by positivity) (by positivity)) (by positivity) hC0).trans ?_
    exact (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hg_rt hsq_rt) hrat_rt) hC0).trans_eq
      (by ring)
  calc deltaExtract C (deltaConstructPaulis C eps (deltaQld a b eps P.m P.d P.q) P.m P.d P.q)
        P.m P.d P.q ≤ C * (3 * C * amp * rt + amp * rt) :=
        mul_le_mul_of_nonneg_left (add_le_add hc_rt hrat) hC0
    _ = (C * (3 * C + 1)) * (amp * rt) := by ring
    _ ≤ 4 * C ^ 2 * (amp * rt) :=
        mul_le_mul_of_nonneg_right (by nlinarith) (mul_nonneg hamp0 hrt0)
    _ = (4 * C ^ 2 * a) * deg ^ a * rt := by dsimp [amp]; ring
    _ ≤ deltaQld (4 * C ^ 2 * a) (b / 8) eps P.m P.d P.q :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hd1 hconst) (by positivity))
          hrt0

end

end MIPStarRE.QPBT
