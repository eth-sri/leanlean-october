module

public import QPBT.Combining.Witnesses
public import QPBT.Observables.PointConsistency
public import QPBT.Observables.LineMeasurement
public import QPBT.ExplicitConstants
public import QPBT.Test.MagicSquareTheorems.Rigidity.Consistency
public import QPBT.Games.DistanceTheorems
public import QPBT.Games.DistanceTheorems.Calculus

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus MIPStarRE.LDT.Preliminaries

noncomputable section

/-! ## Section 1: Placement calculus on the expanded state -/

def baAaBipartition (P : AdmissibleParams) (ιA ιB : Type*) :
    SixReg P ιA ιB ≃
      (ιB × PauliRegister P) ×
        ((ιA × PauliRegister P) × (PauliRegister P × PauliRegister P)) where
  toFun := fun ⟨⟨a, a', a''⟩, b, b', b''⟩ => ((b, a''), ((a, a'), (b', b'')))
  invFun := fun ⟨⟨b, a''⟩, ⟨a, a'⟩, b', b''⟩ => ((a, (a', a'')), (b, (b', b'')))
  left_inv := by rintro ⟨⟨a, a', a''⟩, b, b', b''⟩; rfl
  right_inv := by rintro ⟨⟨b, a''⟩, ⟨a, a'⟩, b', b''⟩; rfl

namespace ProjectiveSetting

section
variable {P : AdmissibleParams} {ε : ℝ}

theorem place_AA'_eq (S : ProjectiveSetting P ε)
    (O : Op (S.ExpandedLocalSpace Placement.AA'.side)) :
    S.place .AA' O =
      reindexOp (aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
        (heteroKron O (1 : Op ((S.toStrategy.ιB × PauliRegister P) × (PauliRegister P × PauliRegister P)))) :=
  (reindexOp_aaBaBipartition_left S O).symm

theorem place_BA''_eq (S : ProjectiveSetting P ε)
    (O : Op (S.ExpandedLocalSpace Placement.BA''.side)) :
    S.place .BA'' O =
      reindexOp (aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
        (heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
          (heteroKron O (1 : Op (PauliRegister P × PauliRegister P)))) :=
  (reindexOp_aaBaBipartition_right S O).symm

theorem place_AB''_eq (S : ProjectiveSetting P ε)
    (O : Op (S.ExpandedLocalSpace Placement.AB''.side)) :
    S.place .AB'' O =
      reindexOp (abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB)
        (heteroKron O (1 : Op ((S.toStrategy.ιB × PauliRegister P) × (PauliRegister P × PauliRegister P)))) :=
  (reindexOp_abBbBipartition_left S O).symm

theorem place_BB'_eq (S : ProjectiveSetting P ε)
    (O : Op (S.ExpandedLocalSpace Placement.BB'.side)) :
    S.place .BB' O =
      reindexOp (abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB)
        (heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
          (heteroKron O (1 : Op (PauliRegister P × PauliRegister P)))) :=
  (reindexOp_abBbBipartition_right S O).symm

theorem reindexOp_baAaBipartition_left (S : ProjectiveSetting P ε)
    (O : Op (S.ExpandedLocalSpace Placement.BA''.side)) :
    reindexOp (baAaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
        (heteroKron O (1 : Op ((S.toStrategy.ιA × PauliRegister P) × (PauliRegister P × PauliRegister P)))) =
      S.place .BA'' O := by
  ext ⟨⟨a, a', a''⟩, b, b', b''⟩ ⟨⟨c, c', c''⟩, d, d', d''⟩
  simp only [reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    place, baAaBipartition, Equiv.coe_fn_mk, heteroKron, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

theorem reindexOp_baAaBipartition_right (S : ProjectiveSetting P ε)
    (O : Op (S.ExpandedLocalSpace Placement.AA'.side)) :
    reindexOp (baAaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
        (heteroKron (1 : Op (S.toStrategy.ιB × PauliRegister P))
          (heteroKron O (1 : Op (PauliRegister P × PauliRegister P)))) =
      S.place .AA' O := by
  ext ⟨⟨a, a', a''⟩, b, b', b''⟩ ⟨⟨c, c', c''⟩, d, d', d''⟩
  simp only [reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    place, baAaBipartition, Equiv.coe_fn_mk, heteroKron, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

theorem reindexOp_conjTranspose {ι κ : Type*} (e : ι ≃ κ) (M : Op κ) :
    reindexOp e Mᴴ = (reindexOp e M)ᴴ := by ext; rfl

theorem reindexOp_nonneg {ι κ : Type*} [Finite ι] [Finite κ]
    (e : ι ≃ κ) {M : Op κ} (hM : 0 ≤ M) : 0 ≤ reindexOp e M := by
  letI := Fintype.ofFinite ι; letI := Fintype.ofFinite κ
  rw [Matrix.nonneg_iff_posSemidef] at hM ⊢
  exact hM.submatrix e.symm.symm

set_option synthInstance.maxSize 400 in
theorem place_mul (S : ProjectiveSetting P ε) :
    ∀ (p : Placement) (A B : Op (S.ExpandedLocalSpace p.side)),
      S.place p (A * B) = S.place p A * S.place p B
  | .AA', A, B => by
      classical
      rw [place_AA'_eq, place_AA'_eq, place_AA'_eq, ← WinImplications.reindexOp_mul, heteroKron_mul, mul_one]
  | .BA'', A, B => by
      classical
      rw [place_BA''_eq, place_BA''_eq, place_BA''_eq, ← WinImplications.reindexOp_mul, heteroKron_mul, heteroKron_mul, mul_one, mul_one]
  | .BB', A, B => by
      classical
      rw [place_BB'_eq, place_BB'_eq, place_BB'_eq, ← WinImplications.reindexOp_mul, heteroKron_mul, heteroKron_mul, mul_one, mul_one]
  | .AB'', A, B => by
      classical
      rw [place_AB''_eq, place_AB''_eq, place_AB''_eq, ← WinImplications.reindexOp_mul, heteroKron_mul, mul_one]

theorem place_one (S : ProjectiveSetting P ε) (p : Placement) :
    S.place p (1 : Op (S.ExpandedLocalSpace p.side)) = 1 := by
  ext i j; cases p <;> (simp only [ProjectiveSetting.place, Matrix.one_apply, Prod.ext_iff]; split_ifs <;> simp_all)

theorem place_finsetSum (S : ProjectiveSetting P ε) (p : Placement) {γ : Type*}
    (s : Finset γ) (O : γ → Op (S.ExpandedLocalSpace p.side)) :
    S.place p (∑ x ∈ s, O x) = ∑ x ∈ s, S.place p (O x) :=
  S.place_finset_sum p s O

theorem place_conjTranspose (S : ProjectiveSetting P ε) :
    ∀ (p : Placement) (A : Op (S.ExpandedLocalSpace p.side)), S.place p Aᴴ = (S.place p A)ᴴ
  | .AA', A => by rw [place_AA'_eq, place_AA'_eq, ← reindexOp_conjTranspose, WinImplications.heteroKron_conjTranspose, Matrix.conjTranspose_one]
  | .BA'', A => by rw [place_BA''_eq, place_BA''_eq, ← reindexOp_conjTranspose, WinImplications.heteroKron_conjTranspose, WinImplications.heteroKron_conjTranspose, Matrix.conjTranspose_one, Matrix.conjTranspose_one]
  | .BB', A => by rw [place_BB'_eq, place_BB'_eq, ← reindexOp_conjTranspose, WinImplications.heteroKron_conjTranspose, WinImplications.heteroKron_conjTranspose, Matrix.conjTranspose_one, Matrix.conjTranspose_one]
  | .AB'', A => by rw [place_AB''_eq, place_AB''_eq, ← reindexOp_conjTranspose, WinImplications.heteroKron_conjTranspose, Matrix.conjTranspose_one]

set_option synthInstance.maxSize 400 in
theorem place_nonneg (S : ProjectiveSetting P ε) :
    ∀ (p : Placement) {A : Op (S.ExpandedLocalSpace p.side)}, 0 ≤ A → 0 ≤ S.place p A
  | .AA', _, hA => by classical rw [place_AA'_eq]; exact reindexOp_nonneg _ (kronecker_nonneg hA Matrix.PosSemidef.one.nonneg)
  | .BA'', _, hA => by classical rw [place_BA''_eq]; exact reindexOp_nonneg _ (kronecker_nonneg Matrix.PosSemidef.one.nonneg (kronecker_nonneg hA Matrix.PosSemidef.one.nonneg))
  | .BB', _, hA => by classical rw [place_BB'_eq]; exact reindexOp_nonneg _ (kronecker_nonneg Matrix.PosSemidef.one.nonneg (kronecker_nonneg hA Matrix.PosSemidef.one.nonneg))
  | .AB'', _, hA => by classical rw [place_AB''_eq]; exact reindexOp_nonneg _ (kronecker_nonneg hA Matrix.PosSemidef.one.nonneg)

theorem place_le_one (S : ProjectiveSetting P ε) (p : Placement)
    {A : Op (S.ExpandedLocalSpace p.side)} (hA : A ≤ 1) : S.place p A ≤ 1 := by
  have h := S.place_nonneg p (sub_nonneg.mpr hA)
  rw [place_sub, place_one] at h; exact sub_nonneg.mp h

theorem place_conjTranspose_mul_self_le_one (S : ProjectiveSetting P ε)
    (p : Placement) {E : Op (S.ExpandedLocalSpace p.side)} (hE : IsProj E) :
    (S.place p E)ᴴ * S.place p E ≤ 1 := by
  rw [← place_conjTranspose, ← place_mul, hE.isSelfAdjoint.isHermitian.eq, hE.isIdempotentElem.eq]
  exact S.place_le_one p (sub_nonneg.mp hE.one_sub.nonneg)

set_option synthInstance.maxSize 400 in
theorem place_comm (S : ProjectiveSetting P ε) (p₁ p₂ : Placement) (hopp : p₁.IsOpposite p₂)
    (A : Op (S.ExpandedLocalSpace p₁.side)) (B : Op (S.ExpandedLocalSpace p₂.side)) :
    S.place p₁ A * S.place p₂ B = S.place p₂ B * S.place p₁ A := by
  classical
  cases p₁ <;> cases p₂ <;> try exact False.elim hopp
  · rw [place_AA'_eq, place_BA''_eq, ← WinImplications.reindexOp_mul, ← WinImplications.reindexOp_mul]
    simp only [heteroKron_mul, one_mul, mul_one]
  · rw [place_AA'_eq, place_BA''_eq, ← WinImplications.reindexOp_mul, ← WinImplications.reindexOp_mul]
    simp only [heteroKron_mul, one_mul, mul_one]
  · rw [place_AB''_eq, place_BB'_eq, ← WinImplications.reindexOp_mul, ← WinImplications.reindexOp_mul]
    simp only [heteroKron_mul, one_mul, mul_one]
  · rw [place_AB''_eq, place_BB'_eq, ← WinImplications.reindexOp_mul, ← WinImplications.reindexOp_mul]
    simp only [heteroKron_mul, one_mul, mul_one]

def placedMeasurement (S : ProjectiveSetting P ε) (p : Placement) {α : Type*}
    [Fintype α] (M : Measurement α (S.ExpandedLocalSpace p.side)) :
    Measurement α (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
  Measurement.ofSumEqOne (fun a => S.place p (M.effect a))
    (fun a => S.place_nonneg p (M.pos a))
    (by rw [← place_finsetSum, M.sum_eq_one, place_one])

@[simp] theorem placedMeasurement_effect (S : ProjectiveSetting P ε)
    (p : Placement) {α : Type*} [Fintype α]
    (M : Measurement α (S.ExpandedLocalSpace p.side)) (a : α) :
    (S.placedMeasurement p M).effect a = S.place p (M.effect a) := rfl

theorem placedMeasurement_isProjective (S : ProjectiveSetting P ε)
    (p : Placement) {α : Type*} [Fintype α]
    (M : Measurement α (S.ExpandedLocalSpace p.side))
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    MIPStarRE.QPBT.Measurement.IsProjective (S.placedMeasurement p M) := fun a =>
  isStarProjection_iff'.2 ⟨by
    change S.place p (M.effect a) * S.place p (M.effect a) = S.place p (M.effect a)
    rw [← place_mul, (hM a).isIdempotentElem.eq], by
    change star (S.place p (M.effect a)) = S.place p (M.effect a)
    rw [Matrix.star_eq_conjTranspose, ← place_conjTranspose, (hM a).isSelfAdjoint.isHermitian.eq]⟩

def eprCrossSwap (P : AdmissibleParams) (ιA ιB : Type*) :
    SixReg P ιA ιB ≃ SixReg P ιA ιB where
  toFun := fun ⟨⟨a, a', a''⟩, b, b', b''⟩ => ((a, (b'', b')), (b, (a'', a')))
  invFun := fun ⟨⟨a, a', a''⟩, b, b', b''⟩ => ((a, (b'', b')), (b, (a'', a')))
  left_inv := by rintro ⟨⟨a, a', a''⟩, b, b', b''⟩; rfl
  right_inv := by rintro ⟨⟨a, a', a''⟩, b, b', b''⟩; rfl

theorem reindexState_eprCrossSwap_psiHat (S : ProjectiveSetting P ε) :
    reindexState (eprCrossSwap P S.toStrategy.ιA S.toStrategy.ιB) S.psiHat = S.psiHat := by
  have hepr {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (x y : V) :
      (eprState V).ofLp (x, y) = (eprState V).ofLp (y, x) := by
    change (if x = y then (Real.sqrt (Fintype.card V : ℝ) : ℂ)⁻¹ else 0) =
      (if y = x then (Real.sqrt (Fintype.card V : ℝ) : ℂ)⁻¹ else 0)
    by_cases h : x = y <;> simp [h, eq_comm]
  ext ⟨⟨a, a', a''⟩, b, b', b''⟩
  change S.toStrategy.ψ.ofLp (a, b) * (eprState (PauliRegister P)).ofLp (b'', b') *
      (eprState (PauliRegister P)).ofLp (a'', a') =
    S.toStrategy.ψ.ofLp (a, b) * (eprState (PauliRegister P)).ofLp (a', a'') *
      (eprState (PauliRegister P)).ofLp (b', b'')
  rw [hepr b'' b', hepr a'' a']; ring

theorem opFamilyDistSq_place_AB''_eq_AA' {X α : Type*} [Fintype α]
    (S : ProjectiveSetting P ε) (μ : Distribution X)
    (A B : X → α → Op (S.ExpandedLocalSpace .alice)) :
    opFamilyDistSq μ (fun x a => S.place .AB'' (A x a)) (fun x a => S.place .AB'' (B x a)) S.psiHat =
      opFamilyDistSq μ (fun x a => S.place .AA' (A x a)) (fun x a => S.place .AA' (B x a)) S.psiHat := by
  have hop (O : Op (S.ExpandedLocalSpace .alice)) :
      reindexOp (eprCrossSwap P S.toStrategy.ιA S.toStrategy.ιB) (S.place .AB'' O) = S.place .AA' O := by
    ext ⟨⟨a, a', a''⟩, b, b', b''⟩ ⟨⟨c, c', c''⟩, d, d', d''⟩
    simp only [reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      place, eprCrossSwap, Equiv.coe_fn_mk, Matrix.one_apply]
    ring!
  unfold opFamilyDistSq
  refine avgOver_congr _ _ _ fun x => Finset.sum_congr rfl fun a _ => ?_
  rw [← place_sub, ← place_sub]
  conv_lhs => rw [← reindexState_eprCrossSwap_psiHat S]
  rw [WinImplications.norm_applyOperatorToState_reindexState, hop]

theorem opFamilyDistSq_place_BB'_eq_BA'' {X α : Type*} [Fintype α]
    (S : ProjectiveSetting P ε) (μ : Distribution X)
    (A B : X → α → Op (S.ExpandedLocalSpace .bob)) :
    opFamilyDistSq μ (fun x a => S.place .BB' (A x a)) (fun x a => S.place .BB' (B x a)) S.psiHat =
      opFamilyDistSq μ (fun x a => S.place .BA'' (A x a)) (fun x a => S.place .BA'' (B x a)) S.psiHat := by
  have hop (O : Op (S.ExpandedLocalSpace .bob)) :
      reindexOp (eprCrossSwap P S.toStrategy.ιA S.toStrategy.ιB) (S.place .BB' O) = S.place .BA'' O := by
    ext ⟨⟨a, a', a''⟩, b, b', b''⟩ ⟨⟨c, c', c''⟩, d, d', d''⟩
    simp only [reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      place, eprCrossSwap, Equiv.coe_fn_mk, Matrix.one_apply]
    ring!
  unfold opFamilyDistSq
  refine avgOver_congr _ _ _ fun x => Finset.sum_congr rfl fun a _ => ?_
  rw [← place_sub, ← place_sub]
  conv_lhs => rw [← reindexState_eprCrossSwap_psiHat S]
  rw [WinImplications.norm_applyOperatorToState_reindexState, hop]

end
end ProjectiveSetting

/-! ## Section 2: Approximate commutation, sandwich POVM, and combined points witness -/

abbrev PointPair (P : AdmissibleParams) :=
  (Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)

theorem averageOperatorOverDistribution_uniform_eq_inv_card_smul_sum
    {α ι : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype ι] [DecidableEq ι] (f : α → Op ι) :
    averageOperatorOverDistribution (uniformDistribution α) f =
      (Fintype.card α : ℂ)⁻¹ • ∑ a, f a := by
  ext i j
  simp only [averageOperatorOverDistribution, uniformDistribution,
    Distribution.uniformOnFinset, Finset.mem_univ, if_true, Matrix.sum_apply,
    Matrix.smul_apply, Complex.real_smul, smul_eq_mul,
    Finset.card_univ, one_div, Complex.ofReal_inv, Complex.ofReal_natCast, Finset.mul_sum]

theorem opFamilyDistSq_uniform_le_four {X α ι : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] [Fintype α] [Fintype ι] [DecidableEq ι]
    (A B : X → α → Op ι) (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1)
    (hA : ∀ x, ∑ a, (A x a)ᴴ * A x a ≤ 1) (hB : ∀ x, ∑ a, (B x a)ᴴ * B x a ≤ 1) :
    opFamilyDistSq (uniformDistribution X) A B ψ ≤ 4 := by
  unfold opFamilyDistSq
  exact (avgOver_mono _ _ (fun _ => 4) fun x =>
    sum_norm_sub_apply_sq_le_four (A x) (B x) ψ hψ (hA x) (hB x)).trans_eq (avgOver_uniform_const _)

theorem sum_mul_conjTranspose_mul_self_eq_one {α β ι : Type*} [Fintype α]
    [Fintype β] [Fintype ι] [DecidableEq ι]
    (A : Measurement α ι) (B : Measurement β ι)
    (hA : MIPStarRE.QPBT.Measurement.IsProjective A)
    (hB : MIPStarRE.QPBT.Measurement.IsProjective B) :
    ∑ ab : α × β, (A.effect ab.1 * B.effect ab.2)ᴴ * (A.effect ab.1 * B.effect ab.2) = 1 := by
  rw [Fintype.sum_prod_type_right]
  calc _ = ∑ b : β, B.effect b * (∑ a : α, A.effect a) * B.effect b := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Matrix.conjTranspose_mul, (hA a).isSelfAdjoint.isHermitian.eq,
          (hB b).isSelfAdjoint.isHermitian.eq, Matrix.mul_assoc _ _ (A.effect a * B.effect b),
          ← Matrix.mul_assoc (A.effect a) (A.effect a), (hA a).isIdempotentElem.eq, ← Matrix.mul_assoc]
    _ = 1 := by
        simp_rw [A.sum_eq_one, mul_one]
        rw [Finset.sum_congr rfl fun b _ => (hB b).isIdempotentElem.eq]
        exact B.sum_eq_one

namespace ProjectiveSetting

section
variable {P : AdmissibleParams} {ε : ℝ}

theorem exp_point_comm_explicit (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
    (p : Placement) :
    opFamilyDistSq (uniformDistribution (PointPair P))
      (fun xz (ab : PauliScalar P × PauliScalar P) => S.place p
        ((S.pointMeasExp p.side .X xz.1).effect ab.1 * (S.pointMeasExp p.side .Z xz.2).effect ab.2))
      (fun xz ab => S.place p
        ((S.pointMeasExp p.side .Z xz.2).effect ab.2 * (S.pointMeasExp p.side .X xz.1).effect ab.1))
      S.psiHat ≤ pauliBaselineTwistedConstant * Real.sqrt ε := by
  have hε : (0 : ℝ) ≤ ε := by
    have := WinImplications.strategy_value_le_one S.toStrategy; have := S.win; linarith
  have horth_sum {I J E : Type} [Fintype I] [DecidableEq I] [Fintype J]
      [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      (c : J → I → ℂ) (N : ℝ)
      (horth : ∀ i i', ∑ j, (starRingEnd ℂ) (c j i) * c j i' = if i = i' then (N : ℂ) else 0)
      (v : I → E) : ∑ j, ‖∑ i, c j i • v i‖ ^ 2 = N * ∑ i, ‖v i‖ ^ 2 := by
    have hnorm (x : E) : ‖x‖ ^ 2 = (inner ℂ x x).re := by simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) x).symm
    have hj (j : J) : ‖∑ i, c j i • v i‖ ^ 2 =
        (∑ i, ∑ i', ((starRingEnd ℂ) (c j i) * c j i') * inner ℂ (v i) (v i')).re := by
      rw [hnorm, sum_inner]; simp only [inner_sum, inner_smul_left, inner_smul_right]
      congr 1; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have hsum : ∑ j, ∑ i, ∑ i', ((starRingEnd ℂ) (c j i) * c j i') * inner ℂ (v i) (v i') =
        ∑ i, (N : ℂ) * inner ℂ (v i) (v i) := by
      rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      calc _ = ∑ i', (∑ j, (starRingEnd ℂ) (c j i) * c j i') * inner ℂ (v i) (v i') :=
            Finset.sum_congr rfl fun _ _ => (Finset.sum_mul _ _ _).symm
        _ = ∑ i', (if i = i' then (N : ℂ) else 0) * inner ℂ (v i) (v i') :=
            Finset.sum_congr rfl fun _ _ => by rw [horth]
        _ = _ := by simp [ite_mul]
    rw [Finset.sum_congr rfl fun j _ => hj j, ← Complex.re_sum, hsum, Complex.re_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Complex.re_ofReal_mul, ← hnorm]
  have hchar_orth (r r' : PauliScalar P) :
      ∑ a : PauliScalar P, phaseSign (fixedBinTrace P.model (a * r)) *
          phaseSign (fixedBinTrace P.model (a * r')) =
        if r = r' then (Fintype.card (PauliScalar P) : ℂ) else 0 := by
    have hsum1 (c : PauliScalar P) :
        ∑ a : PauliScalar P, phaseSign (fixedBinTrace P.model (a * c)) =
          if c = 0 then (Fintype.card (PauliScalar P) : ℂ) else 0 := by
      have h : (𝔼 r : PauliScalar P, phaseSign (fixedBinTrace P.model (r * c))) =
          if c = 0 then (1 : ℂ) else 0 := by
        simpa only [fixedBinTrace, phaseSign_eq_ffChar, ffChar_apply] using
          fourier_fact_scalar (p := 2) (F := PauliScalar P) c
      rw [Finset.expect_eq_sum_div_card, Finset.card_univ,
        div_eq_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)] at h
      rw [h]; split_ifs <;> simp
    have hfmul (x y : PauliScalar P) : phaseSign (fixedBinTrace P.model x) *
        phaseSign (fixedBinTrace P.model y) = phaseSign (fixedBinTrace P.model (x + y)) := by
      rw [fixedBinTrace, map_add, phaseSign_eq_ffChar, phaseSign_eq_ffChar, phaseSign_eq_ffChar]
      exact ((ZMod.stdAddChar (N := 2)).map_add_eq_mul _ _).symm
    have hterm (a : PauliScalar P) : phaseSign (fixedBinTrace P.model (a * r)) *
        phaseSign (fixedBinTrace P.model (a * r')) =
        phaseSign (fixedBinTrace P.model (a * (r' - r))) := by
      have hneg : phaseSign (fixedBinTrace P.model (-(a * r))) = phaseSign (fixedBinTrace P.model (a * r)) := by
        rw [fixedBinTrace, map_neg]; exact congrArg phaseSign (ZMod.neg_eq_self_mod_two _)
      rw [← hneg, hfmul]; congr 2; ring
    simp_rw [hterm, hsum1]
    by_cases h : r = r'
    · simp [h]
    · rw [if_neg h, if_neg fun h' => h (sub_eq_zero.mp h').symm]
  have hpair_orth (rs rs' : PauliScalar P × PauliScalar P) :
      ∑ ab : PauliScalar P × PauliScalar P,
          (starRingEnd ℂ) (phaseSign (fixedBinTrace P.model (ab.1 * rs.1)) *
              phaseSign (fixedBinTrace P.model (ab.2 * rs.2))) *
            (phaseSign (fixedBinTrace P.model (ab.1 * rs'.1)) *
              phaseSign (fixedBinTrace P.model (ab.2 * rs'.2))) =
        if rs = rs' then (((Fintype.card (PauliScalar P) : ℝ) ^ 2 : ℝ) : ℂ) else 0 := by
    have hst (t : ZMod 2) : (starRingEnd ℂ) (phaseSign t) = phaseSign t := by
      rw [← Complex.star_def]; exact star_phaseSign t
    simp_rw [map_mul, hst]
    rw [Fintype.sum_prod_type]
    calc _ = (∑ a : PauliScalar P, phaseSign (fixedBinTrace P.model (a * rs.1)) *
            phaseSign (fixedBinTrace P.model (a * rs'.1))) *
          ∑ b : PauliScalar P, phaseSign (fixedBinTrace P.model (b * rs.2)) *
            phaseSign (fixedBinTrace P.model (b * rs'.2)) := by
          rw [Finset.sum_mul_sum]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      _ = _ := by
          rw [hchar_orth, hchar_orth]
          by_cases h1 : rs.1 = rs'.1 <;> by_cases h2 : rs.2 = rs'.2
          · rw [if_pos h1, if_pos h2, if_pos (Prod.ext h1 h2)]; push_cast; ring
          · rw [if_pos h1, if_neg h2, if_neg fun h => h2 (congrArg Prod.snd h)]; simp
          · rw [if_neg h1, if_pos h2, if_neg fun h => h1 (congrArg Prod.fst h)]; simp
          · rw [if_neg h1, if_neg h2, if_neg fun h => h1 (congrArg Prod.fst h)]; simp
  have hpt_sum (x z : Fin P.m → PauliScalar P) :
      ∑ ab : PauliScalar P × PauliScalar P,
          ‖applyOperatorToState (S.place p
            (S.expPointOp p.side .X x ab.1 * S.expPointOp p.side .Z z ab.2 -
              S.expPointOp p.side .Z z ab.2 * S.expPointOp p.side .X x ab.1)) S.psiHat‖ ^ 2 =
        avgOver (uniformDistribution (PauliScalar P × PauliScalar P))
          (fun rs => ‖applyOperatorToState (S.place p
            (S.expObs p.side .X rs.1 x * S.expObs p.side .Z rs.2 z -
              S.expObs p.side .Z rs.2 z * S.expObs p.side .X rs.1 x)) S.psiHat‖ ^ 2) := by
    let v : PauliScalar P × PauliScalar P →
        EuclideanSpace ℂ (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
      fun rs => applyOperatorToState (S.place p
        (S.expObs p.side .X rs.1 x * S.expObs p.side .Z rs.2 z -
          S.expObs p.side .Z rs.2 z * S.expObs p.side .X rs.1 x)) S.psiHat
    let c : ℂ := (Fintype.card (PauliScalar P) : ℂ)⁻¹
    have hcomm_eq (a b : PauliScalar P) :
        S.expPointOp p.side .X x a * S.expPointOp p.side .Z z b -
            S.expPointOp p.side .Z z b * S.expPointOp p.side .X x a =
          (c * c) • ∑ rs : PauliScalar P × PauliScalar P,
            (phaseSign (fixedBinTrace P.model (a * rs.1)) *
                phaseSign (fixedBinTrace P.model (b * rs.2))) •
              (S.expObs p.side .X rs.1 x * S.expObs p.side .Z rs.2 z -
                S.expObs p.side .Z rs.2 z * S.expObs p.side .X rs.1 x) := by
      unfold expPointOp
      rw [averageOperatorOverDistribution_uniform_eq_inv_card_smul_sum,
        averageOperatorOverDistribution_uniform_eq_inv_card_smul_sum]
      change (c • ∑ r, _) * (c • ∑ s, _) - (c • ∑ s, _) * (c • ∑ r, _) = _
      rw [smul_mul_smul_comm, smul_mul_smul_comm, ← smul_sub, Finset.sum_mul_sum, Finset.sum_mul_sum,
        Fintype.sum_prod_type]
      congr 1
      rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun s r => (phaseSign (fixedBinTrace P.model (b * s)) • S.expObs p.side .Z s z) *
          (phaseSign (fixedBinTrace P.model (a * r)) • S.expObs p.side .X r x)),
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (phaseSign (fixedBinTrace P.model (b * s))), smul_sub]
    have hpt (ab : PauliScalar P × PauliScalar P) :
        applyOperatorToState (S.place p
            (S.expPointOp p.side .X x ab.1 * S.expPointOp p.side .Z z ab.2 -
              S.expPointOp p.side .Z z ab.2 * S.expPointOp p.side .X x ab.1)) S.psiHat =
          (c * c) • ∑ rs : PauliScalar P × PauliScalar P,
            (phaseSign (fixedBinTrace P.model (ab.1 * rs.1)) *
                phaseSign (fixedBinTrace P.model (ab.2 * rs.2))) • v rs := by
      rw [hcomm_eq, place_smul, place_finsetSum, WinImplications.applyOperatorToState_smul_op,
        applyOperatorToState_finset_sum]
      congr 1; refine Finset.sum_congr rfl fun rs _ => ?_
      rw [place_smul, WinImplications.applyOperatorToState_smul_op]
    have hpars := horth_sum
      (fun (ab rs : PauliScalar P × PauliScalar P) =>
        phaseSign (fixedBinTrace P.model (ab.1 * rs.1)) * phaseSign (fixedBinTrace P.model (ab.2 * rs.2)))
      ((Fintype.card (PauliScalar P) : ℝ) ^ 2) hpair_orth v
    have hq : (0 : ℝ) < (Fintype.card (PauliScalar P) : ℝ) := by exact_mod_cast Fintype.card_pos
    have hcn : ‖c * c‖ = ((Fintype.card (PauliScalar P) : ℝ) ^ 2)⁻¹ := by
      simp only [c, norm_mul, norm_inv, Complex.norm_natCast]; rw [sq, mul_inv]
    calc _ = ∑ ab : PauliScalar P × PauliScalar P,
            ‖c * c‖ ^ 2 * ‖∑ rs : PauliScalar P × PauliScalar P,
              (phaseSign (fixedBinTrace P.model (ab.1 * rs.1)) *
                phaseSign (fixedBinTrace P.model (ab.2 * rs.2))) • v rs‖ ^ 2 :=
            Finset.sum_congr rfl fun ab _ => by rw [hpt, norm_smul, mul_pow]
      _ = ‖c * c‖ ^ 2 * (((Fintype.card (PauliScalar P) : ℝ) ^ 2) * ∑ rs, ‖v rs‖ ^ 2) := by
            rw [← Finset.mul_sum, hpars]
      _ = _ := by
            rw [avgOver_uniform_eq_inv_card_mul_sum, Fintype.card_prod, hcn]
            dsimp [v]; push_cast; field_simp
  have hfam : opFamilyDistSq (uniformDistribution (PointPair P))
      (fun xz (ab : PauliScalar P × PauliScalar P) => S.place p
        ((S.pointMeasExp p.side .X xz.1).effect ab.1 * (S.pointMeasExp p.side .Z xz.2).effect ab.2))
      (fun xz ab => S.place p
        ((S.pointMeasExp p.side .Z xz.2).effect ab.2 * (S.pointMeasExp p.side .X xz.1).effect ab.1))
      S.psiHat =
      avgOver (uniformDistribution (PauliTuple P)) (fun ω =>
        ‖applyOperatorToState (S.placeStrategySide p.side (S.twistedCommutator p.side ω))
          S.toStrategy.ψ‖ ^ 2) := by
    unfold opFamilyDistSq
    have hnorm (x z : Fin P.m → PauliScalar P) (rs : PauliScalar P × PauliScalar P) :
        ‖applyOperatorToState (S.place p
            (S.expObs p.side .X rs.1 x * S.expObs p.side .Z rs.2 z -
              S.expObs p.side .Z rs.2 z * S.expObs p.side .X rs.1 x)) S.psiHat‖ ^ 2 =
          ‖applyOperatorToState
            (S.placeStrategySide p.side (S.twistedCommutator p.side (x, z, rs.1, rs.2)))
            S.toStrategy.ψ‖ ^ 2 := by
      rw [expObs_commutator S p.side (x, z, rs.1, rs.2),
        norm_place_heteroKron_psiHat S p _ _ (tauX_mul_tauZ_isometry P (x, z, rs.1, rs.2))]
    calc avgOver (uniformDistribution (PointPair P)) (fun xz =>
          ∑ ab : PauliScalar P × PauliScalar P, ‖applyOperatorToState
            (S.place p ((S.pointMeasExp p.side .X xz.1).effect ab.1 * (S.pointMeasExp p.side .Z xz.2).effect ab.2) -
              S.place p ((S.pointMeasExp p.side .Z xz.2).effect ab.2 * (S.pointMeasExp p.side .X xz.1).effect ab.1))
            S.psiHat‖ ^ 2)
      _ = avgOver (uniformDistribution (PointPair P)) (fun xz =>
          avgOver (uniformDistribution (PauliScalar P × PauliScalar P)) (fun rs =>
            ‖applyOperatorToState (S.placeStrategySide p.side
              (S.twistedCommutator p.side (xz.1, xz.2, rs.1, rs.2))) S.toStrategy.ψ‖ ^ 2)) :=
        avgOver_congr _ _ _ fun xz => by
          rw [← avgOver_congr _ _ _ (hnorm xz.1 xz.2), ← hpt_sum xz.1 xz.2]
          exact Finset.sum_congr rfl fun ab _ => by rw [place_sub]; rfl
      _ = _ := by
        rw [← avgOver_uniform_prod (fun (xz : PointPair P) (rs : PauliScalar P × PauliScalar P) =>
            ‖applyOperatorToState (S.placeStrategySide p.side
              (S.twistedCommutator p.side (xz.1, xz.2, rs.1, rs.2))) S.toStrategy.ψ‖ ^ 2),
          avgOver_uniform_equiv (Equiv.prodAssoc (Fin P.m → PauliScalar P)
            (Fin P.m → PauliScalar P) (PauliScalar P × PauliScalar P))]
        rfl
  rw [hfam]
  have h := twisted_commutator_avg_le_explicit P ε S p.side hε
  rw [pauli_edge_card] at h
  convert h using 1 <;>
    simp only [pauliBaselineTwistedConstant, pauliBaselineCommutatorConstant, Nat.cast_ofNat] <;> ring

def sandwichPoint (S : ProjectiveSetting P ε) (side : PlayerSide)
    (x z : Fin P.m → PauliScalar P) :
    Measurement (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace side) :=
  Measurement.ofSumEqOne
    (fun ab => (S.pointMeasExp side .Z z).effect ab.2 *
      (S.pointMeasExp side .X x).effect ab.1 * (S.pointMeasExp side .Z z).effect ab.2)
    (fun ab => (pastedMeasurement_isMeasurement
      (S.pointMeasExp side .X x) (S.pointMeasExp side .Z z)
      (S.pointMeasExp_isProjective side .Z z)).1 ab)
    (pastedMeasurement_isMeasurement
      (S.pointMeasExp side .X x) (S.pointMeasExp side .Z z)
      (S.pointMeasExp_isProjective side .Z z)).2

@[simp] theorem sandwichPoint_effect (S : ProjectiveSetting P ε)
    (side : PlayerSide) (x z : Fin P.m → PauliScalar P)
    (ab : PauliScalar P × PauliScalar P) :
    (S.sandwichPoint side x z).effect ab =
      (S.pointMeasExp side .Z z).effect ab.2 *
        (S.pointMeasExp side .X x).effect ab.1 * (S.pointMeasExp side .Z z).effect ab.2 := rfl

def sandwichDefectBound (S : ProjectiveSetting P ε) (p₁ p₂ : Placement) (xz : PointPair P) : ℝ :=
  (1 / 2) * ∑ b : PauliScalar P, ‖applyOperatorToState
      (S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect b) -
        S.place p₂ ((S.pointMeasExp p₂.side .Z xz.2).effect b)) S.psiHat‖ ^ 2 +
    (3 / 2) * ((∑ a : PauliScalar P, ‖applyOperatorToState
        (S.place p₁ ((S.pointMeasExp p₁.side .X xz.1).effect a) -
          S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect a)) S.psiHat‖ ^ 2) +
      (∑ ab : PauliScalar P × PauliScalar P, ‖applyOperatorToState
        (S.place p₁ ((S.pointMeasExp p₁.side .X xz.1).effect ab.1 *
            (S.pointMeasExp p₁.side .Z xz.2).effect ab.2) -
          S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2 *
            (S.pointMeasExp p₁.side .X xz.1).effect ab.1)) S.psiHat‖ ^ 2) +
      ∑ ab : PauliScalar P × PauliScalar P, ‖applyOperatorToState
        (S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect ab.1 *
            (S.pointMeasExp p₂.side .Z xz.2).effect ab.2) -
          S.place p₂ ((S.pointMeasExp p₂.side .Z xz.2).effect ab.2 *
            (S.pointMeasExp p₂.side .X xz.1).effect ab.1)) S.psiHat‖ ^ 2)

theorem sandwich_defect_abstract {α β ι : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Fintype ι] [DecidableEq ι]
    (X₁ X₂ : Measurement α ι) (Z₁ Z₂ : Measurement β ι)
    (w : EuclideanSpace ℂ ι) (hw : ‖w‖ = 1)
    (hX₁ : MIPStarRE.QPBT.Measurement.IsProjective X₁)
    (hX₂ : MIPStarRE.QPBT.Measurement.IsProjective X₂)
    (hZ₁ : MIPStarRE.QPBT.Measurement.IsProjective Z₁)
    (hZ₂ : MIPStarRE.QPBT.Measurement.IsProjective Z₂)
    (hXZ : ∀ a b, X₁.effect a * Z₂.effect b = Z₂.effect b * X₁.effect a)
    (hZX : ∀ a b, Z₁.effect b * X₂.effect a = X₂.effect a * Z₁.effect b)
    (hZZ : ∀ b, Z₁.effect b * Z₂.effect b = Z₂.effect b * Z₁.effect b) :
    1 - (∑ ab : α × β, stateQForm w
      ((Z₁.effect ab.2 * X₁.effect ab.1 * Z₁.effect ab.2) *
        (Z₂.effect ab.2 * X₂.effect ab.1 * Z₂.effect ab.2))) ≤
      (1 / 2) * (∑ b, ‖applyOperatorToState (Z₁.effect b - Z₂.effect b) w‖ ^ 2) +
      (3 / 2) * ((∑ a, ‖applyOperatorToState (X₁.effect a - X₂.effect a) w‖ ^ 2) +
        (∑ ab : α × β, ‖applyOperatorToState
          (X₁.effect ab.1 * Z₁.effect ab.2 - Z₁.effect ab.2 * X₁.effect ab.1) w‖ ^ 2) +
        ∑ ab : α × β, ‖applyOperatorToState
          (X₂.effect ab.1 * Z₂.effect ab.2 - Z₂.effect ab.2 * X₂.effect ab.1) w‖ ^ 2) := by
  have hsqf {γ : Type} [Fintype γ] [DecidableEq γ] (A B : Measurement γ ι)
      (u : EuclideanSpace ℂ ι)
      (hA : MIPStarRE.QPBT.Measurement.IsProjective A)
      (hB : MIPStarRE.QPBT.Measurement.IsProjective B) :
      ∑ c, stateQForm u (A.effect c * B.effect c) =
        ‖u‖ ^ 2 - (1 / 2) * ∑ c, ‖applyOperatorToState (A.effect c - B.effect c) u‖ ^ 2 := by
    rw [point_distance_eq_two_defect_of_projective A B u hA hB, point_defect_eq]; ring
  have hov : ∑ ab : α × β, stateQForm w
      ((Z₁.effect ab.2 * X₁.effect ab.1 * Z₁.effect ab.2) *
        (Z₂.effect ab.2 * X₂.effect ab.1 * Z₂.effect ab.2)) =
      1 - (1 / 2) * ∑ b, ‖applyOperatorToState (Z₁.effect b - Z₂.effect b) w‖ ^ 2 -
        (1 / 2) * ∑ ab : α × β,
          ‖applyOperatorToState (X₁.effect ab.1 - X₂.effect ab.1)
            (applyOperatorToState (Z₁.effect ab.2 * Z₂.effect ab.2) w)‖ ^ 2 := by
    have hstep (ab : α × β) :
        stateQForm w ((Z₁.effect ab.2 * X₁.effect ab.1 * Z₁.effect ab.2) *
          (Z₂.effect ab.2 * X₂.effect ab.1 * Z₂.effect ab.2)) =
        stateQForm (applyOperatorToState (Z₁.effect ab.2 * Z₂.effect ab.2) w)
          (X₁.effect ab.1 * X₂.effect ab.1) := by
      rw [← stateQForm_conjTranspose_mul_mul, Matrix.conjTranspose_mul,
        measurement_effect_hermitian, measurement_effect_hermitian]
      congr 1
      simp only [Matrix.mul_assoc]
      rw [(show Commute (Z₁.effect ab.2) (Z₂.effect ab.2) from hZZ ab.2).left_comm (X₂.effect ab.1 * Z₂.effect ab.2),
        (show Commute (X₁.effect ab.1) (Z₂.effect ab.2) from hXZ ab.1 ab.2).left_comm,
        (show Commute (Z₁.effect ab.2) (Z₂.effect ab.2) from hZZ ab.2).left_comm,
        (show Commute (Z₁.effect ab.2) (X₂.effect ab.1) from hZX ab.1 ab.2).left_comm]
    have hW (b) : ‖applyOperatorToState (Z₁.effect b * Z₂.effect b) w‖ ^ 2 =
        stateQForm w (Z₁.effect b * Z₂.effect b) := by
      rw [MagicSquareRigidity.norm_applyOperatorToState_sq, Matrix.conjTranspose_mul,
        measurement_effect_hermitian, measurement_effect_hermitian]
      congr 1
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Z₁.effect b) (Z₁.effect b),
        (hZ₁ b).isIdempotentElem.eq, hZZ b, ← Matrix.mul_assoc, (hZ₂ b).isIdempotentElem.eq]
    simp_rw [hstep]
    rw [Fintype.sum_prod_type_right]
    dsimp only
    rw [Finset.sum_congr rfl fun b _ => hsqf X₁ X₂ _ hX₁ hX₂,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp_rw [hW]
    rw [hsqf Z₁ Z₂ w hZ₁ hZ₂, hw, one_pow, Fintype.sum_prod_type_right]
  have hpt (ab : α × β) :
      ‖applyOperatorToState (X₁.effect ab.1 - X₂.effect ab.1)
          (applyOperatorToState (Z₁.effect ab.2 * Z₂.effect ab.2) w)‖ ^ 2 ≤
        3 * (‖applyOperatorToState (Z₂.effect ab.2 * (X₁.effect ab.1 - X₂.effect ab.1)) w‖ ^ 2 +
          ‖applyOperatorToState (X₁.effect ab.1 * Z₁.effect ab.2 - Z₁.effect ab.2 * X₁.effect ab.1) w‖ ^ 2 +
          ‖applyOperatorToState (X₂.effect ab.1 * Z₂.effect ab.2 - Z₂.effect ab.2 * X₂.effect ab.1) w‖ ^ 2) := by
    obtain ⟨a, b⟩ := ab
    have halg : (X₁.effect a - X₂.effect a) * (Z₁.effect b * Z₂.effect b) =
        Z₁.effect b * Z₂.effect b * (X₁.effect a - X₂.effect a) +
          Z₂.effect b * (X₁.effect a * Z₁.effect b - Z₁.effect b * X₁.effect a) -
          Z₁.effect b * (X₂.effect a * Z₂.effect b - Z₂.effect b * X₂.effect a) := by
      simp only [sub_mul, mul_sub, Matrix.mul_assoc]
      rw [(show Commute (Z₂.effect b) (X₁.effect a) from (hXZ a b).symm).left_comm (Z₁.effect b), ← hZZ b,
        (show Commute (Z₂.effect b) (Z₁.effect b) from (hZZ b).symm).left_comm (X₁.effect a),
        (show Commute (Z₁.effect b) (X₂.effect a) from hZX a b).left_comm (Z₂.effect b)]
      abel
    rw [← applyOperatorToState_mul, halg]
    have hlin : applyOperatorToState
        (Z₁.effect b * Z₂.effect b * (X₁.effect a - X₂.effect a) +
          Z₂.effect b * (X₁.effect a * Z₁.effect b - Z₁.effect b * X₁.effect a) -
          Z₁.effect b * (X₂.effect a * Z₂.effect b - Z₂.effect b * X₂.effect a)) w =
        applyOperatorToState (Z₁.effect b)
            (applyOperatorToState (Z₂.effect b * (X₁.effect a - X₂.effect a)) w) +
          applyOperatorToState (Z₂.effect b)
            (applyOperatorToState (X₁.effect a * Z₁.effect b - Z₁.effect b * X₁.effect a) w) -
          applyOperatorToState (Z₁.effect b)
            (applyOperatorToState (X₂.effect a * Z₂.effect b - Z₂.effect b * X₂.effect a) w) := by
      rw [← applyOperatorToState_mul, ← applyOperatorToState_mul, ← applyOperatorToState_mul, Matrix.mul_assoc]
      simp only [applyOperatorToState, map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
    rw [hlin]
    have hpr {M : Measurement β ι}
        (hM : MIPStarRE.QPBT.Measurement.IsProjective M) (c) (v) :
        ‖applyOperatorToState (M.effect c) v‖ ^ 2 ≤ ‖v‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (MagicSquareRigidity.norm_applyOperatorToState_le
        (by rw [(hM c).isSelfAdjoint.isHermitian.eq, (hM c).isIdempotentElem.eq]; exact measurement_effect_le_one M c) v) 2
    let v₁ := applyOperatorToState (Z₂.effect b * (X₁.effect a - X₂.effect a)) w
    let v₂ := applyOperatorToState (X₁.effect a * Z₁.effect b - Z₁.effect b * X₁.effect a) w
    let v₃ := applyOperatorToState (X₂.effect a * Z₂.effect b - Z₂.effect b * X₂.effect a) w
    let u₁ := applyOperatorToState (Z₁.effect b) v₁
    let u₂ := applyOperatorToState (Z₂.effect b) v₂
    let u₃ := applyOperatorToState (Z₁.effect b) v₃
    have htri : ‖u₁ + u₂ - u₃‖ ≤ ‖u₁‖ + ‖u₂‖ + ‖u₃‖ :=
      (norm_sub_le (u₁ + u₂) u₃).trans (add_le_add (norm_add_le u₁ u₂) le_rfl)
    have hsq : ‖u₁ + u₂ - u₃‖ ^ 2 ≤ 3 * (‖u₁‖ ^ 2 + ‖u₂‖ ^ 2 + ‖u₃‖ ^ 2) := by
      nlinarith [sq_nonneg (‖u₁‖ - ‖u₂‖), sq_nonneg (‖u₂‖ - ‖u₃‖), sq_nonneg (‖u₁‖ - ‖u₃‖),
        norm_nonneg (u₁ + u₂ - u₃), norm_nonneg u₁, norm_nonneg u₂, norm_nonneg u₃]
    have hu1 := hpr hZ₁ b v₁
    have hu2 := hpr hZ₂ b v₂
    have hu3 := hpr hZ₁ b v₃
    dsimp [u₁, u₂, u₃, v₁, v₂, v₃] at hsq hu1 hu2 hu3; linarith
  have hcontr : ∑ ab : α × β,
      ‖applyOperatorToState (Z₂.effect ab.2 * (X₁.effect ab.1 - X₂.effect ab.1)) w‖ ^ 2 ≤
      ∑ a, ‖applyOperatorToState (X₁.effect a - X₂.effect a) w‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_le_sum fun a _ =>
      sum_norm_mul_apply_le Z₂.effect (X₁.effect a - X₂.effect a) w (measurement_sum_adjoint_mul_le_one Z₂)
  have hsum := Finset.sum_le_sum fun ab (_ : ab ∈ Finset.univ) => hpt ab
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  linarith

theorem sandwich_offDiagonal_le_sandwichDefectBound (S : ProjectiveSetting P ε)
    (p₁ p₂ : Placement) (hopp : p₁.IsOpposite p₂) (xz : PointPair P) :
    (∑ ab : PauliScalar P × PauliScalar P, ∑ ab' : PauliScalar P × PauliScalar P,
      if ab = ab' then 0 else stateQForm S.psiHat
        (S.place p₁ ((S.sandwichPoint p₁.side xz.1 xz.2).effect ab) *
          S.place p₂ ((S.sandwichPoint p₂.side xz.1 xz.2).effect ab'))) ≤
      S.sandwichDefectBound p₁ p₂ xz := by
  have hdef := point_defect_eq
    (S.placedMeasurement p₁ (S.sandwichPoint p₁.side xz.1 xz.2))
    (S.placedMeasurement p₂ (S.sandwichPoint p₂.side xz.1 xz.2)) S.psiHat
  simp only [placedMeasurement_effect, psiHat_norm, one_pow] at hdef
  rw [hdef]
  have habs := sandwich_defect_abstract
    (S.placedMeasurement p₁ (S.pointMeasExp p₁.side .X xz.1))
    (S.placedMeasurement p₂ (S.pointMeasExp p₂.side .X xz.1))
    (S.placedMeasurement p₁ (S.pointMeasExp p₁.side .Z xz.2))
    (S.placedMeasurement p₂ (S.pointMeasExp p₂.side .Z xz.2))
    S.psiHat S.psiHat_norm
    (S.placedMeasurement_isProjective p₁ _ (S.pointMeasExp_isProjective p₁.side .X xz.1))
    (S.placedMeasurement_isProjective p₂ _ (S.pointMeasExp_isProjective p₂.side .X xz.1))
    (S.placedMeasurement_isProjective p₁ _ (S.pointMeasExp_isProjective p₁.side .Z xz.2))
    (S.placedMeasurement_isProjective p₂ _ (S.pointMeasExp_isProjective p₂.side .Z xz.2))
    (fun _ _ => S.place_comm p₁ p₂ hopp _ _)
    (fun _ _ => S.place_comm p₁ p₂ hopp _ _)
    (fun _ => S.place_comm p₁ p₂ hopp _ _)
  simp only [placedMeasurement_effect] at habs
  simp only [sandwichPoint_effect, place_mul]
  unfold sandwichDefectBound
  simp only [place_mul]
  exact habs

set_option synthInstance.maxSize 400 in
theorem exists_projective_close_sandwich (S : ProjectiveSetting P ε)
    (p₁ p₂ : Placement) (hopp : p₁.IsOpposite p₂)
    (e : SixReg P S.toStrategy.ιA S.toStrategy.ιB ≃
      S.ExpandedLocalSpace p₁.side ×
        (S.ExpandedLocalSpace p₂.side × (PauliRegister P × PauliRegister P)))
    (he₁ : ∀ O : Op (S.ExpandedLocalSpace p₁.side),
      reindexOp e (heteroKron O (1 : Op (S.ExpandedLocalSpace p₂.side × (PauliRegister P × PauliRegister P)))) =
        S.place p₁ O)
    (he₂ : ∀ O : Op (S.ExpandedLocalSpace p₂.side),
      reindexOp e (heteroKron (1 : Op (S.ExpandedLocalSpace p₁.side))
        (heteroKron O (1 : Op (PauliRegister P × PauliRegister P)))) = S.place p₂ O) :
    ∃ Q : PointPair P →
        Measurement (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace p₁.side),
      (∀ xz, MIPStarRE.QPBT.Measurement.IsProjective (Q xz)) ∧
        opFamilyDistSq (uniformDistribution (PointPair P))
          (fun xz (ab : PauliScalar P × PauliScalar P) => S.place p₁ ((Q xz).effect ab))
          (fun xz ab => S.place p₁ ((S.sandwichPoint p₁.side xz.1 xz.2).effect ab))
          S.psiHat ≤
          220 * Real.rpow (avgOver (uniformDistribution (PointPair P))
            (S.sandwichDefectBound p₁ p₂)) (1 / 4 : ℝ) := by
  classical
  have hψ : ‖reindexState e S.psiHat‖ = 1 := by rw [reindexState_norm_eq, psiHat_norm]
  have hdb_nn (xz) : 0 ≤ S.sandwichDefectBound p₁ p₂ xz := by unfold sandwichDefectBound; positivity
  have hxz (xz : PointPair P) :
      ∃ Pm : Measurement (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace p₁.side),
        MIPStarRE.QPBT.Measurement.IsProjective Pm ∧
          ∑ ab : PauliScalar P × PauliScalar P, ‖applyOperatorToState
            (S.place p₁ (Pm.effect ab) - S.place p₁ ((S.sandwichPoint p₁.side xz.1 xz.2).effect ab))
            S.psiHat‖ ^ 2 ≤ 220 * Real.rpow (S.sandwichDefectBound p₁ p₂ xz) (1 / 4 : ℝ) := by
    have hcons : consistencyDefect (uniformDistribution Unit)
        (fun _ ab => heteroKron ((S.sandwichPoint p₁.side xz.1 xz.2).effect ab) 1)
        (fun _ ab => heteroKron 1
          ((leftPlacedMeasurement (ιB := PauliRegister P × PauliRegister P)
            (S.sandwichPoint p₂.side xz.1 xz.2)).effect ab))
        (reindexState e S.psiHat) ≤ S.sandwichDefectBound p₁ p₂ xz := by
      refine le_trans (le_of_eq ?_) (S.sandwich_offDiagonal_le_sandwichDefectBound p₁ p₂ hopp xz)
      unfold consistencyDefect
      rw [avgOver_uniform_const]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      by_cases hab : a = b
      · simp [hab]
      · rw [if_neg hab, if_neg hab, consistency_term_eq_stateQForm,
          WinImplications.stateQForm_reindexState, WinImplications.reindexOp_mul, he₁]
        change stateQForm S.psiHat (S.place p₁ _ * reindexOp e (heteroKron 1 (heteroKron _ 1))) = _
        rw [he₂]
    obtain ⟨Pm, hPm, hdist⟩ := projective_rounding_with_explicit_constant
      (reindexState e S.psiHat) hψ (S.sandwichPoint p₁.side xz.1 xz.2)
      (leftPlacedMeasurement (ιB := PauliRegister P × PauliRegister P) (S.sandwichPoint p₂.side xz.1 xz.2))
      (S.sandwichDefectBound p₁ p₂ xz) (hdb_nn xz) hcons
    refine ⟨Pm, hPm, (le_of_eq ?_).trans hdist⟩
    unfold opFamilyDistSq
    rw [avgOver_uniform_const]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [WinImplications.norm_applyOperatorToState_reindexState, WinImplications.reindexOp_sub, he₁, he₁]
  choose Q hQ using hxz
  refine ⟨Q, fun xz => (hQ xz).1, ?_⟩
  have hqeq {t : ℝ} (ht : 0 ≤ t) : Real.rpow t (1 / 4 : ℝ) = Real.sqrt (Real.sqrt t) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul ht]; norm_num
  have hjensen : avgOver (uniformDistribution (PointPair P))
      (fun xz => Real.rpow (S.sandwichDefectBound p₁ p₂ xz) (1 / 4 : ℝ)) ≤
      Real.rpow (avgOver (uniformDistribution (PointPair P)) (S.sandwichDefectBound p₁ p₂)) (1 / 4 : ℝ) := by
    have hw1 := uniformDistribution_weight_sum_le_one (PointPair P)
    have h1 : |avgOver (uniformDistribution (PointPair P))
        (fun xz => Real.sqrt (Real.sqrt (S.sandwichDefectBound p₁ p₂ xz)))| ≤
        Real.sqrt (avgOver (uniformDistribution (PointPair P))
          (fun xz => Real.sqrt (S.sandwichDefectBound p₁ p₂ xz))) :=
      avgOver_abs_le_sqrt_of_pointwise (uniformDistribution (PointPair P)) _ _
        (fun xz => by rw [abs_of_nonneg (Real.sqrt_nonneg _)]) (fun _ => Real.sqrt_nonneg _) hw1
    have h2 : |avgOver (uniformDistribution (PointPair P))
        (fun xz => Real.sqrt (S.sandwichDefectBound p₁ p₂ xz))| ≤
        Real.sqrt (avgOver (uniformDistribution (PointPair P)) (S.sandwichDefectBound p₁ p₂)) :=
      avgOver_abs_le_sqrt_of_pointwise (uniformDistribution (PointPair P)) _ _
        (fun xz => by rw [abs_of_nonneg (Real.sqrt_nonneg _)]) hdb_nn hw1
    rw [hqeq (avgOver_nonneg _ _ hdb_nn)]
    exact (avgOver_congr _ _ _ fun xz => hqeq (hdb_nn xz)).trans_le
      ((le_abs_self _).trans (h1.trans (Real.sqrt_le_sqrt ((le_abs_self _).trans h2))))
  unfold opFamilyDistSq
  exact (avgOver_mono _ _ _ fun xz => (hQ xz).2).trans
    ((avgOver_const_mul _ _ _).trans_le (mul_le_mul_of_nonneg_left hjensen (by norm_num)))

end
end ProjectiveSetting

theorem exists_combinedPointsWitness :
    ∃ deltaQ : ℝ → ℝ, IsPolyErr deltaQ ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
        Nonempty (CombinedPointsWitness S (deltaQ ε)) := by
  have hQ : (1 : ℝ) ≤ pauliBaselinePointConstant := by
    simp only [pauliBaselinePointConstant, pauliBaselineTwistedConstant, pauliBaselineCommutatorConstant]
    nlinarith [Real.sqrt_nonneg (344 : ℝ)]
  refine ⟨fun ε => pauliBaselinePointConstant * Real.rpow ε (1 / 8 : ℝ),
    ⟨pauliBaselinePointConstant, 1 / 8, hQ, by norm_num, fun ε hε =>
      ⟨mul_nonneg (by linarith) (Real.rpow_nonneg hε _), le_rfl⟩⟩, ?_⟩
  intro P ε S
  let C₀ : ℝ := 344 + 3 * pauliBaselineTwistedConstant
  let C₁ : ℝ := pauliBaselineTwistedConstant
  let C₃ : ℝ := 688
  have hC₁ : (1 : ℝ) ≤ C₁ := by
    dsimp [C₁, pauliBaselineTwistedConstant, pauliBaselineCommutatorConstant]
    nlinarith [Real.sqrt_nonneg (344 : ℝ)]
  have hC₀ : (1 : ℝ) ≤ C₀ := by dsimp [C₀]; linarith
  have hε := S.eps_nonneg
  have h₀ (p₁ p₂ : Placement) (hopp : p₁.IsOpposite p₂) :
      avgOver (uniformDistribution (PointPair P)) (S.sandwichDefectBound p₁ p₂) ≤
        C₀ * (ε + Real.sqrt ε) := by
    have hZ : avgOver (uniformDistribution (PointPair P)) (fun xz =>
        ∑ b : PauliScalar P, ‖applyOperatorToState
          (S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect b) -
            S.place p₂ ((S.pointMeasExp p₂.side .Z xz.2).effect b)) S.psiHat‖ ^ 2) ≤ 172 * ε := by
      rw [avgOver_uniform_snd (α := Fin P.m → PauliScalar P) (fun z => ∑ b, ‖applyOperatorToState
        (S.place p₁ ((S.pointMeasExp p₁.side .Z z).effect b) -
          S.place p₂ ((S.pointMeasExp p₂.side .Z z).effect b)) S.psiHat‖ ^ 2)]
      exact exp_point_self_cons_explicit P ε S p₁ p₂ hopp .Z
    have hX : avgOver (uniformDistribution (PointPair P)) (fun xz =>
        ∑ a : PauliScalar P, ‖applyOperatorToState
          (S.place p₁ ((S.pointMeasExp p₁.side .X xz.1).effect a) -
            S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect a)) S.psiHat‖ ^ 2) ≤ 172 * ε := by
      rw [avgOver_uniform_fst (β := Fin P.m → PauliScalar P) (fun x => ∑ a, ‖applyOperatorToState
        (S.place p₁ ((S.pointMeasExp p₁.side .X x).effect a) -
          S.place p₂ ((S.pointMeasExp p₂.side .X x).effect a)) S.psiHat‖ ^ 2)]
      exact exp_point_self_cons_explicit P ε S p₁ p₂ hopp .X
    have hK₁ := ProjectiveSetting.exp_point_comm_explicit P ε S p₁
    have hK₂ := ProjectiveSetting.exp_point_comm_explicit P ε S p₂
    unfold opFamilyDistSq at hK₁ hK₂
    unfold ProjectiveSetting.sandwichDefectBound
    rw [avgOver_add, avgOver_const_mul, avgOver_const_mul, avgOver_add, avgOver_add]
    dsimp [C₀, C₁] at hC₁ ⊢
    nlinarith [Real.sqrt_nonneg ε]
  have h₁ (p : Placement) :
      opFamilyDistSq (uniformDistribution (PointPair P))
        (fun xz (ab : PauliScalar P × PauliScalar P) => S.place p ((S.sandwichPoint p.side xz.1 xz.2).effect ab))
        (fun xz ab => S.place p
          ((S.pointMeasExp p.side .Z xz.2).effect ab.2 * (S.pointMeasExp p.side .X xz.1).effect ab.1))
        S.psiHat ≤ C₁ * Real.sqrt ε := by
    refine le_trans ?_ (ProjectiveSetting.exp_point_comm_explicit P ε S p)
    unfold opFamilyDistSq
    refine avgOver_mono _ _ _ fun xz => Finset.sum_le_sum fun ab _ => ?_
    have hsub : (S.sandwichPoint p.side xz.1 xz.2).effect ab -
        (S.pointMeasExp p.side .Z xz.2).effect ab.2 * (S.pointMeasExp p.side .X xz.1).effect ab.1 =
      (S.pointMeasExp p.side .Z xz.2).effect ab.2 *
        ((S.pointMeasExp p.side .X xz.1).effect ab.1 * (S.pointMeasExp p.side .Z xz.2).effect ab.2 -
          (S.pointMeasExp p.side .Z xz.2).effect ab.2 * (S.pointMeasExp p.side .X xz.1).effect ab.1) := by
      rw [ProjectiveSetting.sandwichPoint_effect, mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        (S.pointMeasExp_isProjective p.side .Z xz.2 ab.2).isIdempotentElem.eq]
    rw [← ProjectiveSetting.place_sub, hsub, ProjectiveSetting.place_mul, applyOperatorToState_mul,
      ← ProjectiveSetting.place_sub]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (MagicSquareRigidity.norm_applyOperatorToState_le
        (S.place_conjTranspose_mul_self_le_one p (S.pointMeasExp_isProjective p.side .Z xz.2 ab.2)) _) 2
  have h₂ := ProjectiveSetting.exp_point_comm_explicit P ε S
  have h₃ (p₁ p₂ : Placement) (hopp : p₁.IsOpposite p₂) :
      opFamilyDistSq (uniformDistribution (PointPair P))
        (fun xz (ab : PauliScalar P × PauliScalar P) => S.place p₁
          ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2 * (S.pointMeasExp p₁.side .X xz.1).effect ab.1))
        (fun xz ab => S.place p₂
          ((S.pointMeasExp p₂.side .X xz.1).effect ab.1 * (S.pointMeasExp p₂.side .Z xz.2).effect ab.2))
        S.psiHat ≤ C₃ * ε := by
    have hA : opFamilyDistSq (uniformDistribution (PointPair P))
        (fun xz (ab : PauliScalar P × PauliScalar P) => S.place p₁
          ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2 * (S.pointMeasExp p₁.side .X xz.1).effect ab.1))
        (fun xz ab => S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2) *
          S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect ab.1))
        S.psiHat ≤ 172 * ε := by
      refine le_trans ?_ ((avgOver_uniform_fst (β := Fin P.m → PauliScalar P)
        (fun x => ∑ a : PauliScalar P, ‖applyOperatorToState
          (S.place p₁ ((S.pointMeasExp p₁.side .X x).effect a) -
            S.place p₂ ((S.pointMeasExp p₂.side .X x).effect a)) S.psiHat‖ ^ 2)).trans_le
        (exp_point_self_cons_explicit P ε S p₁ p₂ hopp .X))
      unfold opFamilyDistSq
      refine avgOver_mono _ _ _ fun xz => ?_
      simp_rw [S.place_mul p₁, ← mul_sub]
      rw [Fintype.sum_prod_type]
      exact Finset.sum_le_sum fun a _ => sum_norm_mul_apply_le
        (fun b => S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect b))
        (S.place p₁ ((S.pointMeasExp p₁.side .X xz.1).effect a) -
          S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect a)) S.psiHat
        (measurement_sum_adjoint_mul_le_one (S.placedMeasurement p₁ (S.pointMeasExp p₁.side .Z xz.2)))
    have hB : opFamilyDistSq (uniformDistribution (PointPair P))
        (fun xz (ab : PauliScalar P × PauliScalar P) =>
          S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2) *
            S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect ab.1))
        (fun xz ab => S.place p₂
          ((S.pointMeasExp p₂.side .X xz.1).effect ab.1 * (S.pointMeasExp p₂.side .Z xz.2).effect ab.2))
        S.psiHat ≤ 172 * ε := by
      refine le_trans ?_ ((avgOver_uniform_snd (α := Fin P.m → PauliScalar P)
        (fun z => ∑ b : PauliScalar P, ‖applyOperatorToState
          (S.place p₁ ((S.pointMeasExp p₁.side .Z z).effect b) -
            S.place p₂ ((S.pointMeasExp p₂.side .Z z).effect b)) S.psiHat‖ ^ 2)).trans_le
        (exp_point_self_cons_explicit P ε S p₁ p₂ hopp .Z))
      unfold opFamilyDistSq
      refine avgOver_mono _ _ _ fun xz => ?_
      have hpt (ab : PauliScalar P × PauliScalar P) :
          S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2) *
            S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect ab.1) -
          S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect ab.1 *
            (S.pointMeasExp p₂.side .Z xz.2).effect ab.2) =
          S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect ab.1) *
            (S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2) -
              S.place p₂ ((S.pointMeasExp p₂.side .Z xz.2).effect ab.2)) := by
        rw [S.place_mul p₂, S.place_comm p₁ p₂ hopp, ← mul_sub]
      simp only [hpt, Fintype.sum_prod_type_right]
      exact Finset.sum_le_sum fun b _ => sum_norm_mul_apply_le
        (fun a => S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect a))
        (S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect b) -
          S.place p₂ ((S.pointMeasExp p₂.side .Z xz.2).effect b)) S.psiHat
        (measurement_sum_adjoint_mul_le_one (S.placedMeasurement p₂ (S.pointMeasExp p₂.side .X xz.1)))
    have htri := opFamilyDistSq_le_of_le_of_le (uniformDistribution (PointPair P)) _ _ _ S.psiHat _ _ hA hB
    dsimp [C₃]; linarith
  obtain ⟨Qa, hQa, hQaR⟩ := S.exists_projective_close_sandwich .AA' .BA'' trivial
    (ProjectiveSetting.aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
    (fun O => S.reindexOp_aaBaBipartition_left O) (fun O => S.reindexOp_aaBaBipartition_right O)
  obtain ⟨Qb, hQb, hQbR⟩ := S.exists_projective_close_sandwich .BA'' .AA' trivial
    (baAaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
    (fun O => S.reindexOp_baAaBipartition_left O) (fun O => S.reindexOp_baAaBipartition_right O)
  let Q : (side : PlayerSide) → PointPair P →
      Measurement (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace side) :=
    fun side => match side with | .alice => Qa | .bob => Qb
  let η : ℝ := 440 * Real.rpow (C₀ * (ε + Real.sqrt ε)) (1 / 4 : ℝ)
  have hQR (p : Placement) : opFamilyDistSq (uniformDistribution (PointPair P))
      (fun xz (ab : PauliScalar P × PauliScalar P) => S.place p ((Q p.side xz).effect ab))
      (fun xz ab => S.place p ((S.sandwichPoint p.side xz.1 xz.2).effect ab)) S.psiHat ≤ η := by
    have hb (p₁ p₂ : Placement) (hopp : p₁.IsOpposite p₂) :
        220 * Real.rpow (avgOver (uniformDistribution (PointPair P)) (S.sandwichDefectBound p₁ p₂)) (1 / 4 : ℝ) ≤ η := by
      have hnn : 0 ≤ avgOver (uniformDistribution (PointPair P)) (S.sandwichDefectBound p₁ p₂) :=
        avgOver_nonneg _ _ fun _ => by unfold ProjectiveSetting.sandwichDefectBound; positivity
      have hr := Real.rpow_le_rpow hnn (h₀ p₁ p₂ hopp) (by norm_num : (0 : ℝ) ≤ 1 / 4)
      have hr0 : 0 ≤ (C₀ * (ε + Real.sqrt ε)) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (by positivity) _
      dsimp [η]; linarith
    cases p
    · exact hQaR.trans (hb .AA' .BA'' trivial)
    · exact hQbR.trans (hb .BA'' .AA' trivial)
    · rw [ProjectiveSetting.opFamilyDistSq_place_BB'_eq_BA'']; exact hQbR.trans (hb .BA'' .AA' trivial)
    · rw [ProjectiveSetting.opFamilyDistSq_place_AB''_eq_AA']; exact hQaR.trans (hb .AA' .BA'' trivial)
  have hchain (p₁ p₂ : Placement) (hopp : p₁.IsOpposite p₂) :
      opFamilyDistSq (uniformDistribution (PointPair P))
          (fun xz ab => S.place p₁ ((Q p₁.side xz).effect ab))
          (fun xz ab => S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect ab.1 *
            (S.pointMeasExp p₂.side .Z xz.2).effect ab.2)) S.psiHat ≤
        2 * η + 4 * (C₁ * Real.sqrt ε) + 4 * (C₃ * ε) ∧
      opFamilyDistSq (uniformDistribution (PointPair P))
          (fun xz ab => S.place p₁ ((Q p₁.side xz).effect ab))
          (fun xz ab => S.place p₂ ((S.pointMeasExp p₂.side .Z xz.2).effect ab.2 *
            (S.pointMeasExp p₂.side .X xz.1).effect ab.1)) S.psiHat ≤
        4 * η + 8 * (C₁ * Real.sqrt ε) + 8 * (C₃ * ε) + 2 * (C₁ * Real.sqrt ε) ∧
      opFamilyDistSq (uniformDistribution (PointPair P))
          (fun xz ab => S.place p₁ ((Q p₁.side xz).effect ab))
          (fun xz ab => S.place p₂ ((Q p₂.side xz).effect ab)) S.psiHat ≤
        12 * η + 20 * (C₁ * Real.sqrt ε) + 16 * (C₃ * ε) + 4 * (C₁ * Real.sqrt ε) := by
    have hRXZ := opFamilyDistSq_le_of_le_of_le _ _ _ _ S.psiHat _ _ (h₁ p₁) (h₃ p₁ p₂ hopp)
    have hQXZ := opFamilyDistSq_le_of_le_of_le _ _ _ _ S.psiHat _ _ (hQR p₁) hRXZ
    have hQZX := opFamilyDistSq_le_of_le_of_le _ _ _ _ S.psiHat _ _ hQXZ (h₂ p₂)
    have hZXQ : opFamilyDistSq (uniformDistribution (PointPair P))
        (fun xz ab => S.place p₂ ((S.pointMeasExp p₂.side .Z xz.2).effect ab.2 *
          (S.pointMeasExp p₂.side .X xz.1).effect ab.1))
        (fun xz ab => S.place p₂ ((Q p₂.side xz).effect ab)) S.psiHat ≤
        2 * η + 2 * (C₁ * Real.sqrt ε) := by
      rw [opFamilyDistSq_symm]
      exact opFamilyDistSq_le_of_le_of_le _ _ _ _ S.psiHat _ _ (hQR p₂) (h₁ p₂)
    have hQQ := opFamilyDistSq_le_of_le_of_le _ _ _ _ S.psiHat _ _ hQZX hZXQ
    exact ⟨by linarith, by linarith, by linarith⟩
  let K : ℝ := pauliBaselinePointConstant
  have hKf : K = 12 * (440 * (2 * C₀)) + 20 * C₁ + 16 * C₃ + 4 * C₁ := by
    dsimp [K, C₀, C₁, C₃]; unfold pauliBaselinePointConstant; ring
  have hK4 : (4 : ℝ) ≤ K := by rw [hKf]; nlinarith
  have hη0 : 0 ≤ η := by dsimp [η]; positivity
  have hs0 : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have htot : 12 * η + 20 * (C₁ * Real.sqrt ε) + 16 * (C₃ * ε) + 4 * (C₁ * Real.sqrt ε) ≤
      K * Real.rpow ε (1 / 8 : ℝ) ∨ 1 < ε := by
    by_cases hε1 : ε ≤ 1
    · left
      have h8 : ε ≤ Real.rpow ε (1 / 8 : ℝ) ∧ Real.sqrt ε ≤ Real.rpow ε (1 / 8 : ℝ) ∧
          Real.rpow (C₀ * (ε + Real.sqrt ε)) (1 / 4 : ℝ) ≤ 2 * C₀ * Real.rpow ε (1 / 8 : ℝ) := by
        rcases eq_or_lt_of_le hε with rfl | hpos
        · simp [Real.zero_rpow (by norm_num : (1 / 8 : ℝ) ≠ 0),
            Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0)]
        · have hm (y z : ℝ) (hyz : z ≤ y) : Real.rpow ε y ≤ Real.rpow ε z :=
            Real.rpow_le_rpow_of_exponent_ge hpos hε1 hyz
          have h12 : ε ≤ Real.sqrt ε := by
            rw [Real.sqrt_eq_rpow]; exact (Real.rpow_one ε).symm.trans_le (hm 1 (1 / 2) (by norm_num))
          refine ⟨(Real.rpow_one ε).symm.trans_le (hm 1 (1 / 8) (by norm_num)),
            by rw [Real.sqrt_eq_rpow]; exact hm (1 / 2) (1 / 8) (by norm_num), ?_⟩
          calc _ ≤ Real.rpow (2 * C₀ * Real.sqrt ε) (1 / 4 : ℝ) :=
                Real.rpow_le_rpow (by positivity) (by nlinarith) (by norm_num)
            _ = Real.rpow (2 * C₀) (1 / 4 : ℝ) * Real.rpow ε (1 / 8 : ℝ) := by
                change (2 * C₀ * Real.sqrt ε) ^ (1 / 4 : ℝ) = (2 * C₀) ^ (1 / 4 : ℝ) * ε ^ (1 / 8 : ℝ)
                rw [Real.mul_rpow (by linarith) hs0, Real.sqrt_eq_rpow, ← Real.rpow_mul hε]; norm_num
            _ ≤ _ := mul_le_mul_of_nonneg_right
                ((Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num : (1 / 4 : ℝ) ≤ 1)).trans_eq
                  (Real.rpow_one _)) (Real.rpow_nonneg hε _)
      rw [hKf]; dsimp [η]; simp only [Real.rpow_eq_pow] at h8 ⊢
      nlinarith [mul_le_mul_of_nonneg_left h8.2.2 (by norm_num : (0 : ℝ) ≤ 440),
        mul_le_mul_of_nonneg_left h8.2.1 (by linarith : (0 : ℝ) ≤ C₁),
        mul_le_mul_of_nonneg_left h8.1 (by norm_num : (0 : ℝ) ≤ C₃)]
    · exact Or.inr (lt_of_not_ge hε1)
  have hK8 (hε1 : 1 < ε) : (4 : ℝ) ≤ K * Real.rpow ε (1 / 8 : ℝ) := by
    have : (1 : ℝ) ≤ Real.rpow ε (1 / 8 : ℝ) := Real.one_le_rpow hε1.le (by norm_num)
    nlinarith
  have hsqQ (p : Placement) (xz : PointPair P) :
      (∑ ab, (S.place p ((Q p.side xz).effect ab))ᴴ * S.place p ((Q p.side xz).effect ab)) ≤ 1 :=
    measurement_sum_adjoint_mul_le_one (S.placedMeasurement p (Q p.side xz))
  have hsqXZ (p : Placement) (xz : PointPair P) :
      (∑ ab : PauliScalar P × PauliScalar P,
        (S.place p ((S.pointMeasExp p.side .X xz.1).effect ab.1 *
          (S.pointMeasExp p.side .Z xz.2).effect ab.2))ᴴ *
        S.place p ((S.pointMeasExp p.side .X xz.1).effect ab.1 *
          (S.pointMeasExp p.side .Z xz.2).effect ab.2)) ≤ 1 := by
    simp only [ProjectiveSetting.place_mul]
    exact (sum_mul_conjTranspose_mul_self_eq_one
      (S.placedMeasurement p (S.pointMeasExp p.side .X xz.1))
      (S.placedMeasurement p (S.pointMeasExp p.side .Z xz.2))
      (S.placedMeasurement_isProjective p _ (S.pointMeasExp_isProjective _ _ _))
      (S.placedMeasurement_isProjective p _ (S.pointMeasExp_isProjective _ _ _))).le
  have hsqZX (p : Placement) (xz : PointPair P) :
      (∑ ab : PauliScalar P × PauliScalar P,
        (S.place p ((S.pointMeasExp p.side .Z xz.2).effect ab.2 *
          (S.pointMeasExp p.side .X xz.1).effect ab.1))ᴴ *
        S.place p ((S.pointMeasExp p.side .Z xz.2).effect ab.2 *
          (S.pointMeasExp p.side .X xz.1).effect ab.1)) ≤ 1 := by
    simp only [ProjectiveSetting.place_mul]
    rw [Fintype.sum_prod_type_right]
    have h := sum_mul_conjTranspose_mul_self_eq_one
      (S.placedMeasurement p (S.pointMeasExp p.side .Z xz.2))
      (S.placedMeasurement p (S.pointMeasExp p.side .X xz.1))
      (S.placedMeasurement_isProjective p _ (S.pointMeasExp_isProjective _ _ _))
      (S.placedMeasurement_isProjective p _ (S.pointMeasExp_isProjective _ _ _))
    rw [Fintype.sum_prod_type] at h
    exact h.le
  refine ⟨{
    Q := fun side x z => Q side (x, z)
    projective := fun side x z => by cases side; exact hQa (x, z); exact hQb (x, z)
    self_consistent := fun p₁ p₂ hopp => by
      rcases htot with ht | h1
      · exact (hchain p₁ p₂ hopp).2.2.trans ht
      · exact (opFamilyDistSq_uniform_le_four _ _ S.psiHat S.psiHat_norm (hsqQ p₁) (hsqQ p₂)).trans (hK8 h1)
    consistent_XZ := fun p₁ p₂ hopp => by
      rcases htot with ht | h1
      · exact (hchain p₁ p₂ hopp).1.trans (by dsimp [C₃] at ht ⊢; nlinarith)
      · exact (opFamilyDistSq_uniform_le_four _ _ S.psiHat S.psiHat_norm (hsqQ p₁) (hsqXZ p₂)).trans (hK8 h1)
    consistent_ZX := fun p₁ p₂ hopp => by
      rcases htot with ht | h1
      · exact (hchain p₁ p₂ hopp).2.1.trans (by dsimp [C₃] at ht ⊢; nlinarith)
      · exact (opFamilyDistSq_uniform_le_four _ _ S.psiHat S.psiHat_norm (hsqQ p₁) (hsqZX p₂)).trans (hK8 h1) }⟩

/-! ## Section 3: Marginal distances, affine coarse-graining, and ordered estimates -/

theorem norm_marginal_sub_sq_le {β ι : Type*} [Fintype β]
    [Fintype ι] [DecidableEq ι] (Q : β → Op ι)
    (hQ : ∀ b, IsProj (Q b)) (horth : ∀ {b c}, b ≠ c → Q b * Q c = 0)
    (B : Quantum.Measurement β ι) (hB : Measurement.IsProjective B)
    (hcomm : ∀ b, Q b * B.effect b = B.effect b * Q b)
    (D : Op ι) (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState ((∑ b, Q b) - D) ψ‖ ^ 2 ≤
      4 * ∑ b, ‖applyOperatorToState (Q b - B.effect b * D) ψ‖ ^ 2 := by
  classical
  let U : Op ι := ∑ b, Q b * (Q b - B.effect b * Q b)
  let V : Op ι := ∑ b, B.effect b * (Q b - B.effect b * D)
  have hU : ‖applyOperatorToState U ψ‖ ^ 2 ≤
      ∑ b, ‖applyOperatorToState (Q b - B.effect b * D) ψ‖ ^ 2 := by
    refine (norm_finset_sum_projector_mul_sq_le Q (fun b => Q b - B.effect b * Q b) hQ horth Finset.univ ψ).trans
      (Finset.sum_le_sum fun b _ => ?_)
    have hidem := (hB b).isIdempotentElem.eq
    have hgram : (1 - B.effect b)ᴴ * (1 - B.effect b) ≤ 1 := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, (hB b).isSelfAdjoint.isHermitian.eq,
        show (1 - B.effect b) * (1 - B.effect b) = 1 - B.effect b by simp only [sub_mul, mul_sub, one_mul, mul_one, hidem]; abel]
      exact sub_le_self _ (B.pos b)
    rw [show Q b - B.effect b * Q b = (1 - B.effect b) * (Q b - B.effect b * D) by
      simp only [sub_mul, mul_sub, one_mul, ← mul_assoc, hidem]; abel, applyOperatorToState_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) (MagicSquareRigidity.norm_applyOperatorToState_le hgram _) 2
  have hV : ‖applyOperatorToState V ψ‖ ^ 2 ≤
      ∑ b, ‖applyOperatorToState (Q b - B.effect b * D) ψ‖ ^ 2 :=
    norm_finset_sum_projector_mul_sq_le B.effect (fun b => Q b - B.effect b * D) hB
      (fun hbc => projective_effect_mul_effect_eq_zero B hB hbc) Finset.univ ψ
  have hsum : (∑ b, Q b) - D = U + V := by
    have h1 : U = ∑ b, (Q b - B.effect b * Q b) := Finset.sum_congr rfl fun b _ => by
      rw [mul_sub, ← mul_assoc, hcomm b, mul_assoc, (hQ b).isIdempotentElem.eq]
    have h2 : V = (∑ b, B.effect b * Q b) - D := by
      dsimp [V]; simp only [mul_sub, ← mul_assoc, (hB _).isIdempotentElem.eq,
        Finset.sum_sub_distrib, ← Finset.sum_mul, B.sum_eq_one, one_mul]
    rw [h1, h2, Finset.sum_sub_distrib]; abel
  rw [hsum]
  have htri : ‖applyOperatorToState (U + V) ψ‖ ≤ ‖applyOperatorToState U ψ‖ + ‖applyOperatorToState V ψ‖ := by
    simpa only [applyOperatorToState, map_add, LinearMap.add_apply] using
      norm_add_le (applyOperatorToState U ψ) (applyOperatorToState V ψ)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
  nlinarith [sq_nonneg (‖applyOperatorToState U ψ‖ - ‖applyOperatorToState V ψ‖)]

set_option maxHeartbeats 800000 in
theorem CombinedPointsWitness.marginal_X_distance_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq (uniformDistribution ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
      (fun xz a => ∑ b, S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b)))
      (fun xz a => S.place p2 ((S.pointMeasExp p2.side .X xz.1).effect a))
      S.psiHat ≤ 4 * δQ := by
  classical
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (points.consistent_ZX p1 p2 hopp) (by norm_num))
  unfold opFamilyDistSq
  rw [← avgOver_const_mul]
  refine avgOver_mono _ _ _ fun xz => ?_
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  simpa only [ProjectiveSetting.placedMeasurement_effect, ProjectiveSetting.place_mul] using
    norm_marginal_sub_sq_le
      (fun b => S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b)))
      (fun b => S.placedMeasurement_isProjective p1 _ (points.projective _ _ _) (a, b))
      (fun hbc => projective_effect_mul_effect_eq_zero
        (S.placedMeasurement p1 (points.Q p1.side xz.1 xz.2))
        (S.placedMeasurement_isProjective p1 _ (points.projective _ _ _))
        (fun hp => hbc (congrArg Prod.snd hp)))
      (S.placedMeasurement p2 (S.pointMeasExp p2.side .Z xz.2))
      (S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _))
      (fun b => S.place_comm p1 p2 hopp _ _)
      (S.place p2 ((S.pointMeasExp p2.side .X xz.1).effect a)) S.psiHat

set_option maxHeartbeats 800000 in
theorem CombinedPointsWitness.marginal_Z_distance_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq (uniformDistribution ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
      (fun xz b => ∑ a, S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b)))
      (fun xz b => S.place p2 ((S.pointMeasExp p2.side .Z xz.2).effect b))
      S.psiHat ≤ 4 * δQ := by
  classical
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (points.consistent_XZ p1 p2 hopp) (by norm_num))
  unfold opFamilyDistSq
  rw [← avgOver_const_mul]
  refine avgOver_mono _ _ _ fun xz => ?_
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  simpa only [ProjectiveSetting.placedMeasurement_effect, ProjectiveSetting.place_mul] using
    norm_marginal_sub_sq_le
      (fun a => S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b)))
      (fun a => S.placedMeasurement_isProjective p1 _ (points.projective _ _ _) (a, b))
      (fun hac => projective_effect_mul_effect_eq_zero
        (S.placedMeasurement p1 (points.Q p1.side xz.1 xz.2))
        (S.placedMeasurement_isProjective p1 _ (points.projective _ _ _))
        (fun hp => hac (congrArg Prod.fst hp)))
      (S.placedMeasurement p2 (S.pointMeasExp p2.side .X xz.1))
      (S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _))
      (fun a => S.place_comm p1 p2 hopp _ _)
      (S.place p2 ((S.pointMeasExp p2.side .Z xz.2).effect b)) S.psiHat

theorem affine_collision_average {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p p' : K × K) :
    avgOver (uniformDistribution (K × K)) (fun c =>
      if c.1 * p.1 + c.2 * p.2 = c.1 * p'.1 + c.2 * p'.2 then (1 : ℝ) else 0) =
      if p = p' then 1 else (Fintype.card K : ℝ)⁻¹ := by
  classical
  have hind (x : K) : avgOver (uniformDistribution K) (fun y => if y = x then (1 : ℝ) else 0) =
      (Fintype.card K : ℝ)⁻¹ := by rw [avgOver_uniform_eq_inv_card_mul_sum]; simp
  rw [avgOver_uniform_prod (α := K) (β := K) (fun a b =>
    if a * p.1 + b * p.2 = a * p'.1 + b * p'.2 then (1 : ℝ) else 0)]
  by_cases hp : p = p'
  · subst p'; simp [avgOver_uniform_const]
  · rw [if_neg hp]
    by_cases hf : p.1 = p'.1
    · have hd : p.2 - p'.2 ≠ 0 := sub_ne_zero.mpr fun h => hp (Prod.ext hf h)
      have hc : (avgOver (uniformDistribution K) fun a =>
          avgOver (uniformDistribution K) fun b =>
            if a * p.1 + b * p.2 = a * p'.1 + b * p'.2 then (1 : ℝ) else 0) =
        avgOver (uniformDistribution K) fun _ =>
          avgOver (uniformDistribution K) fun b => if b = 0 then (1 : ℝ) else 0 :=
        avgOver_congr _ _ _ fun a => avgOver_congr _ _ _ fun b => if_congr
          ⟨fun h => (mul_eq_zero.mp (by rw [hf] at h; linear_combination h)).resolve_right hd,
            fun h => by subst b; simp [hf]⟩ rfl rfl
      rw [hc, hind, avgOver_uniform_const]
    · have hd : p.1 - p'.1 ≠ 0 := sub_ne_zero.mpr hf
      rw [avgOver_uniform_comm]
      refine (avgOver_congr _ _ _ fun b => (avgOver_congr _ _ _ fun a => ?_).trans
        (hind (b * (p'.2 - p.2) / (p.1 - p'.1)))).trans (avgOver_uniform_const _)
      exact if_congr ⟨fun h => (eq_div_iff hd).mpr (by linear_combination h),
        fun h => by have := (eq_div_iff hd).mp h; linear_combination this⟩ rfl rfl

theorem opFamilyDistSq_uniform_affine_postprocess_le
    {X K ι : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [Field K] [Fintype K] [DecidableEq K] [Fintype ι] [DecidableEq ι]
    (A B : X → K × K → Op ι) (ψ : EuclideanSpace ℂ ι)
    (hsum : ∀ x, ∑ p, A x p = ∑ p, B x p) :
    opFamilyDistSq (uniformDistribution (X × (K × K)))
        (fun q c => ∑ p ∈ Finset.univ.filter (fun p => q.2.1 * p.1 + q.2.2 * p.2 = c), A q.1 p)
        (fun q c => ∑ p ∈ Finset.univ.filter (fun p => q.2.1 * p.1 + q.2.2 * p.2 = c), B q.1 p)
        ψ ≤ opFamilyDistSq (uniformDistribution X) A B ψ := by
  classical
  have hfib_pair {Γ R : Type} [Fintype Γ] [Fintype R] [DecidableEq R]
      (f : Γ → R) (v : Γ → EuclideanSpace ℂ ι) :
      (∑ r : R, ‖∑ g ∈ Finset.univ.filter (fun g => f g = r), v g‖ ^ 2) =
        ∑ g : Γ, ∑ g' : Γ, if f g = f g' then (inner ℂ (v g) (v g')).re else 0 := by
    calc _ = ∑ r : R, ∑ g ∈ Finset.univ.filter (fun g => f g = r),
          ∑ g' ∈ Finset.univ.filter (fun g' => f g' = r), (inner ℂ (v g) (v g')).re :=
          Finset.sum_congr rfl fun r _ => by
            simp only [@norm_sq_eq_re_inner ℂ, sum_inner, inner_sum, map_sum]
            exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => inner_re_symm _ _
      _ = ∑ r : R, ∑ g : Γ, ∑ g' : Γ, if f g = r ∧ f g' = r then (inner ℂ (v g) (v g')).re else 0 :=
          Finset.sum_congr rfl fun r _ => by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun g _ => ?_
            by_cases hg : f g = r
            · rw [if_pos hg, Finset.sum_filter]
              exact Finset.sum_congr rfl fun g' _ => by by_cases hg' : f g' = r <;> simp [hg, hg']
            · simp [hg]
      _ = ∑ g : Γ, ∑ g' : Γ, ∑ r : R, if f g = r ∧ f g' = r then (inner ℂ (v g) (v g')).re else 0 := by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun g' _ => by
          by_cases hgg' : f g = f g'
          · rw [if_pos hgg', Fintype.sum_eq_single (f g)]
            · simp [hgg']
            · intro r hr; simp [Ne.symm hr]
          · rw [if_neg hgg']
            exact Finset.sum_eq_zero fun r _ => by
              simp only [ite_eq_right_iff]; exact fun h => (hgg' (h.1.trans h.2.symm)).elim
  have haff (v : K × K → EuclideanSpace ℂ ι) (hv0 : ∑ p, v p = 0) :
      avgOver (uniformDistribution (K × K)) (fun c =>
        ∑ r : K, ‖∑ p ∈ Finset.univ.filter (fun p => c.1 * p.1 + c.2 * p.2 = r), v p‖ ^ 2) ≤
        ∑ p, ‖v p‖ ^ 2 := by
    let w (p p' : K × K) : ℝ := (inner ℂ (v p) (v p')).re
    let qinv : ℝ := (Fintype.card K : ℝ)⁻¹
    have hall : (∑ p, ∑ p', w p p') = 0 := by
      simpa [w, hv0] using (hfib_pair (fun _ : K × K => ()) v).symm
    have hdiag : (∑ p, w p p) = ∑ p, ‖v p‖ ^ 2 :=
      Finset.sum_congr rfl fun p _ => (@norm_sq_eq_re_inner ℂ _ _ _ _ (v p)).symm
    have hnn : 0 ≤ ∑ p, ‖v p‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hq0 : 0 ≤ qinv := by positivity
    calc _ = avgOver (uniformDistribution (K × K)) (fun c =>
            ∑ p, ∑ p', if c.1 * p.1 + c.2 * p.2 = c.1 * p'.1 + c.2 * p'.2 then w p p' else 0) :=
            avgOver_congr _ _ _ fun c => hfib_pair _ v
      _ = ∑ p, ∑ p', if p = p' then w p p' else qinv * w p p' := by
            rw [avgOver_sum]
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [avgOver_sum]
            refine Finset.sum_congr rfl fun p' _ => ?_
            rw [show (fun c : K × K => if c.1 * p.1 + c.2 * p.2 = c.1 * p'.1 + c.2 * p'.2 then w p p' else 0) =
              fun c => (if c.1 * p.1 + c.2 * p.2 = c.1 * p'.1 + c.2 * p'.2 then (1 : ℝ) else 0) * w p p'
              by funext c; split_ifs <;> simp, avgOver_mul_const, affine_collision_average]
            dsimp [qinv]; split_ifs <;> simp
      _ = (1 - qinv) * ∑ p, ‖v p‖ ^ 2 := by
            have hsp : (∑ p, ∑ p', if p = p' then w p p' else qinv * w p p') =
                qinv * (∑ p, ∑ p', w p p') + (1 - qinv) * ∑ p, w p p := by
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun p _ => ?_
              calc _ = ∑ p', (qinv * w p p' + if p = p' then (1 - qinv) * w p p' else 0) :=
                    Finset.sum_congr rfl fun p' _ => by by_cases h : p = p' <;> simp [h]; ring
                _ = _ := by
                    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
                    congr 1; rw [Fintype.sum_eq_single p]; simp; intro _ hp'; simp [Ne.symm hp']
            rw [hsp, hall, hdiag]; ring
      _ ≤ _ := by nlinarith
  unfold opFamilyDistSq
  rw [avgOver_uniform_prod (α := X) (β := K × K) (fun x c =>
    ∑ r : K, ‖applyOperatorToState
      ((∑ p ∈ Finset.univ.filter (fun p => c.1 * p.1 + c.2 * p.2 = r), A x p) -
        ∑ p ∈ Finset.univ.filter (fun p => c.1 * p.1 + c.2 * p.2 = r), B x p) ψ‖ ^ 2)]
  refine avgOver_mono _ _ _ fun x => ?_
  let v : K × K → EuclideanSpace ℂ ι := fun p => applyOperatorToState (A x p - B x p) ψ
  have hv0 : ∑ p, v p = 0 := by
    simp only [v, ← MagicSquareRigidity.applyOperatorToState_sum, Finset.sum_sub_distrib, hsum x, sub_self]
    simp [applyOperatorToState]
  refine (avgOver_congr _ _ _ fun c => Finset.sum_congr rfl fun r _ => ?_).trans_le (haff v hv0)
  congr 2
  simp only [v, applyOperatorToState, map_sub, LinearMap.sub_apply, map_sum, LinearMap.sum_apply, Finset.sum_sub_distrib]

abbrev ExtendedPointQuestion (P : AdmissibleParams) :=
  ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)) × (PauliScalar P × PauliScalar P)

theorem projective_refinement_ordered_dist_le {X Γ α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Γ] [DecidableEq Γ]
    [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (R : Measurement Γ ι) (hR : Measurement.IsProjective R)
    (ev : X → Γ → α) (A B : X → Measurement α ι) (T : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) (eta deltaSelf deltaOrder : ℝ)
    (hpoint : consistencyDefect μ (fun x a => (R.postprocess (ev x)).effect a)
      (fun x a => (B x).effect a) ψ ≤ eta)
    (hself : opFamilyDistSq μ (fun x a => (B x).effect a) (fun x a => (A x).effect a) ψ ≤ deltaSelf)
    (horder : opFamilyDistSq μ (fun x a => (A x).effect a) T ψ ≤ deltaOrder) :
    opFamilyDistSq μ (fun _ g => R.effect g) (fun x g => R.effect g * T x (ev x g)) ψ ≤
      4 * eta + 4 * deltaSelf + 4 * deltaOrder := by
  have hlift (U V : X → α → Op ι) :
      opFamilyDistSq μ (fun x g => R.effect g * U x (ev x g))
        (fun x g => R.effect g * V x (ev x g)) ψ ≤ opFamilyDistSq μ U V ψ := by
    unfold opFamilyDistSq
    refine avgOver_mono _ _ _ fun x => ?_
    simpa only [mul_sub] using sum_norm_mul_funIndexed_apply_le (ev x) R.effect
      (fun a => U x a - V x a) ψ (measurement_sum_adjoint_mul_le_one R)
  have hins : opFamilyDistSq μ (fun _ g => R.effect g)
      (fun x g => R.effect g * (B x).effect (ev x g)) ψ ≤ 2 * eta := by
    have h := hlift (fun x a => (R.postprocess (ev x)).effect a) (fun x a => (B x).effect a)
    simp only [effect_mul_postprocess_effect_self R hR] at h
    exact h.trans ((opFamilyDistSq_le_two_mul_consistencyDefect μ _ B ψ).trans
      (mul_le_mul_of_nonneg_left hpoint (by norm_num)))
  have htail := (hlift (fun x a => (B x).effect a) T).trans
    (opFamilyDistSq_le_of_le_of_le μ _ (fun x a => (A x).effect a) T ψ deltaSelf deltaOrder hself horder)
  have h := opFamilyDistSq_le_of_le_of_le μ _ (fun x g => R.effect g * (B x).effect (ev x g)) _
    ψ (2 * eta) (2 * deltaSelf + 2 * deltaOrder) hins htail
  linarith

namespace CombinedPointsWitness

noncomputable def extendedQ {P : AdmissibleParams} {ε δ : ℝ}
    {S : ProjectiveSetting P ε} (points : CombinedPointsWitness S δ)
    (side : PlayerSide) (x z : Fin P.m → PauliScalar P)
    (alpha beta : PauliScalar P) :
    Measurement (PauliScalar P) (S.ExpandedLocalSpace side) :=
  (points.Q side x z).postprocess fun ab => alpha * ab.1 + beta * ab.2

theorem orderedZX_dist_le {P : AdmissibleParams} {ε δ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δ) (p : Placement) :
    opFamilyDistSq (uniformDistribution ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
        (fun xz ab => S.place p ((points.Q p.side xz.1 xz.2).effect ab))
        (fun xz ab => S.place p
          ((S.pointMeasExp p.side .Z xz.2).effect ab.2 * (S.pointMeasExp p.side .X xz.1).effect ab.1))
        S.psiHat ≤ 4 * δ := by
  have hop : ∃ q : Placement, p.IsOpposite q ∧ q.IsOpposite p := by
    cases p with
    | AA' => exact ⟨.BA'', trivial, trivial⟩
    | BA'' => exact ⟨.AA', trivial, trivial⟩
    | BB' => exact ⟨.AB'', trivial, trivial⟩
    | AB'' => exact ⟨.BB', trivial, trivial⟩
  obtain ⟨q, hpq, hqp⟩ := hop
  have h := opFamilyDistSq_le_of_le_of_le
    (uniformDistribution ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
    (fun xz ab => S.place p ((points.Q p.side xz.1 xz.2).effect ab))
    (fun xz ab => S.place q ((points.Q q.side xz.1 xz.2).effect ab))
    (fun xz ab => S.place p
      ((S.pointMeasExp p.side .Z xz.2).effect ab.2 * (S.pointMeasExp p.side .X xz.1).effect ab.1))
    S.psiHat δ δ (points.self_consistent p q hpq) (points.consistent_ZX q p hqp)
  linarith

theorem orderedXZ_dist_le {P : AdmissibleParams} {ε δ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δ) (p : Placement) :
    opFamilyDistSq (uniformDistribution ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
        (fun xz ab => S.place p ((points.Q p.side xz.1 xz.2).effect ab))
        (fun xz ab => S.place p
          ((S.pointMeasExp p.side .X xz.1).effect ab.1 * (S.pointMeasExp p.side .Z xz.2).effect ab.2))
        S.psiHat ≤ 4 * δ := by
  have hop : ∃ q : Placement, p.IsOpposite q ∧ q.IsOpposite p := by
    cases p with
    | AA' => exact ⟨.BA'', trivial, trivial⟩
    | BA'' => exact ⟨.AA', trivial, trivial⟩
    | BB' => exact ⟨.AB'', trivial, trivial⟩
    | AB'' => exact ⟨.BB', trivial, trivial⟩
  obtain ⟨q, hpq, hqp⟩ := hop
  have h := opFamilyDistSq_le_of_le_of_le
    (uniformDistribution ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
    (fun xz ab => S.place p ((points.Q p.side xz.1 xz.2).effect ab))
    (fun xz ab => S.place q ((points.Q q.side xz.1 xz.2).effect ab))
    (fun xz ab => S.place p
      ((S.pointMeasExp p.side .X xz.1).effect ab.1 * (S.pointMeasExp p.side .Z xz.2).effect ab.2))
    S.psiHat δ δ (points.self_consistent p q hpq) (points.consistent_XZ q p hqp)
  linarith

set_option maxHeartbeats 1600000 in
-- Coarse-graining the joint point POVM expands three finite consistency sums.
theorem ordered_dist_le {P : AdmissibleParams} {ε δQ : ℝ}
    {S : ProjectiveSetting P ε} (points : CombinedPointsWitness S δQ)
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (p1 p2 : Placement) (hopposite : p1.IsOpposite p2)
    (R : Measurement Γ (S.ExpandedLocalSpace p1.side))
    (hR : Measurement.IsProjective R) (ev : ExtendedPointQuestion P → Γ → PauliScalar P)
    (eta : ℝ)
    (hpoint : consistencyDefect (uniformDistribution (ExtendedPointQuestion P))
      (fun x a => S.place p1 ((R.postprocess (ev x)).effect a))
      (fun x a => S.place p2 ((points.extendedQ p2.side x.1.1 x.1.2 x.2.1 x.2.2).effect a)) S.psiHat ≤ eta) :
    (opFamilyDistSq (uniformDistribution (ExtendedPointQuestion P))
      (fun _ g => S.place p1 (R.effect g))
      (fun x g => S.place p1 (R.effect g) * S.place p2
        (∑ ab ∈ Finset.univ.filter (fun ab : PauliScalar P × PauliScalar P =>
            x.2.1 * ab.1 + x.2.2 * ab.2 = ev x g),
          (S.pointMeasExp p2.side .X x.1.1).effect ab.1 *
            (S.pointMeasExp p2.side .Z x.1.2).effect ab.2)) S.psiHat ≤
        4 * eta + 8 * δQ) ∧
    (opFamilyDistSq (uniformDistribution (ExtendedPointQuestion P))
      (fun _ g => S.place p1 (R.effect g))
      (fun x g => S.place p1 (R.effect g) * S.place p2
        (∑ ab ∈ Finset.univ.filter (fun ab : PauliScalar P × PauliScalar P =>
            x.2.1 * ab.1 + x.2.2 * ab.2 = ev x g),
          (S.pointMeasExp p2.side .Z x.1.2).effect ab.2 *
            (S.pointMeasExp p2.side .X x.1.1).effect ab.1)) S.psiHat ≤
        4 * eta + 8 * δQ) := by
  have hsum_meas (p : Placement) {α : Type} [Fintype α] (M : Measurement α (S.ExpandedLocalSpace p.side)) :
      (∑ a, S.place p (M.effect a)) = 1 := by
    rw [← S.place_finsetSum, M.sum_eq_one, S.place_one]
  have hsum_prod (p : Placement) {α β : Type} [Fintype α] [Fintype β]
      (M : Measurement α (S.ExpandedLocalSpace p.side)) (N : Measurement β (S.ExpandedLocalSpace p.side)) :
      (∑ ab : α × β, S.place p (M.effect ab.1 * N.effect ab.2)) = 1 := by
    rw [← S.place_finsetSum, Fintype.sum_prod_type]
    have hl : (∑ a : α, ∑ b : β, M.effect a * N.effect b) = 1 := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul, M.sum_eq_one, N.sum_eq_one, one_mul]
    rw [hl, S.place_one]
  have hself : opFamilyDistSq (uniformDistribution (ExtendedPointQuestion P))
      (fun x a => S.place p2 ((points.extendedQ p2.side x.1.1 x.1.2 x.2.1 x.2.2).effect a))
      (fun x a => S.place p1 ((points.extendedQ p1.side x.1.1 x.1.2 x.2.1 x.2.2).effect a)) S.psiHat ≤ δQ := by
    rw [opFamilyDistSq_symm]
    have h1 := opFamilyDistSq_uniform_affine_postprocess_le (X := PointPair P) (K := PauliScalar P)
      (fun xz ab => S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab))
      (fun xz ab => S.place p2 ((points.Q p2.side xz.1 xz.2).effect ab)) S.psiHat
      (fun _ => by rw [hsum_meas, hsum_meas])
    have heq : opFamilyDistSq (uniformDistribution (ExtendedPointQuestion P))
        (fun x a => S.place p1 ((points.extendedQ p1.side x.1.1 x.1.2 x.2.1 x.2.2).effect a))
        (fun x a => S.place p2 ((points.extendedQ p2.side x.1.1 x.1.2 x.2.1 x.2.2).effect a)) S.psiHat = _ :=
      opFamilyDistSq_congr _ _ _ _ _ _ (fun _ _ => S.place_finsetSum p1 _ _) (fun _ _ => S.place_finsetSum p2 _ _)
    exact (heq.trans_le h1).trans (points.self_consistent p1 p2 hopposite)
  have hXZ : opFamilyDistSq (uniformDistribution (ExtendedPointQuestion P))
      (fun x a => S.place p1 ((points.extendedQ p1.side x.1.1 x.1.2 x.2.1 x.2.2).effect a))
      (fun x a => S.place p2 (∑ ab ∈ Finset.univ.filter (fun ab : PauliScalar P × PauliScalar P =>
          x.2.1 * ab.1 + x.2.2 * ab.2 = a),
        (S.pointMeasExp p2.side .X x.1.1).effect ab.1 * (S.pointMeasExp p2.side .Z x.1.2).effect ab.2))
      S.psiHat ≤ δQ := by
    have h1 := opFamilyDistSq_uniform_affine_postprocess_le (X := PointPair P) (K := PauliScalar P)
      (fun xz ab => S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab))
      (fun xz ab => S.place p2 ((S.pointMeasExp p2.side .X xz.1).effect ab.1 *
        (S.pointMeasExp p2.side .Z xz.2).effect ab.2)) S.psiHat
      (fun _ => by rw [hsum_meas, hsum_prod])
    have heq : opFamilyDistSq (uniformDistribution (ExtendedPointQuestion P))
        (fun x a => S.place p1 ((points.extendedQ p1.side x.1.1 x.1.2 x.2.1 x.2.2).effect a))
        (fun x a => S.place p2 (∑ ab ∈ Finset.univ.filter (fun ab : PauliScalar P × PauliScalar P =>
            x.2.1 * ab.1 + x.2.2 * ab.2 = a),
          (S.pointMeasExp p2.side .X x.1.1).effect ab.1 * (S.pointMeasExp p2.side .Z x.1.2).effect ab.2))
        S.psiHat = _ :=
      opFamilyDistSq_congr _ _ _ _ _ _ (fun _ _ => S.place_finsetSum p1 _ _) (fun _ _ => S.place_finsetSum p2 _ _)
    exact (heq.trans_le h1).trans (points.consistent_XZ p1 p2 hopposite)
  have hZX : opFamilyDistSq (uniformDistribution (ExtendedPointQuestion P))
      (fun x a => S.place p1 ((points.extendedQ p1.side x.1.1 x.1.2 x.2.1 x.2.2).effect a))
      (fun x a => S.place p2 (∑ ab ∈ Finset.univ.filter (fun ab : PauliScalar P × PauliScalar P =>
          x.2.1 * ab.1 + x.2.2 * ab.2 = a),
        (S.pointMeasExp p2.side .Z x.1.2).effect ab.2 * (S.pointMeasExp p2.side .X x.1.1).effect ab.1))
      S.psiHat ≤ δQ := by
    have h1 := opFamilyDistSq_uniform_affine_postprocess_le (X := PointPair P) (K := PauliScalar P)
      (fun xz ab => S.place p1 ((points.Q p1.side xz.1 xz.2).effect ab))
      (fun xz ab => S.place p2 ((S.pointMeasExp p2.side .Z xz.2).effect ab.2 *
        (S.pointMeasExp p2.side .X xz.1).effect ab.1)) S.psiHat
      (fun xz => by
        rw [hsum_meas, Fintype.sum_prod_type_right]
        have ht := hsum_prod p2 (S.pointMeasExp p2.side .Z xz.2) (S.pointMeasExp p2.side .X xz.1)
        rw [Fintype.sum_prod_type] at ht
        exact ht.symm)
    have heq : opFamilyDistSq (uniformDistribution (ExtendedPointQuestion P))
        (fun x a => S.place p1 ((points.extendedQ p1.side x.1.1 x.1.2 x.2.1 x.2.2).effect a))
        (fun x a => S.place p2 (∑ ab ∈ Finset.univ.filter (fun ab : PauliScalar P × PauliScalar P =>
            x.2.1 * ab.1 + x.2.2 * ab.2 = a),
          (S.pointMeasExp p2.side .Z x.1.2).effect ab.2 * (S.pointMeasExp p2.side .X x.1.1).effect ab.1))
        S.psiHat = _ :=
      opFamilyDistSq_congr _ _ _ _ _ _ (fun _ _ => S.place_finsetSum p1 _ _) (fun _ _ => S.place_finsetSum p2 _ _)
    exact (heq.trans_le h1).trans (points.consistent_ZX p1 p2 hopposite)
  let A (x : ExtendedPointQuestion P) := S.placedMeasurement p1 (points.extendedQ p1.side x.1.1 x.1.2 x.2.1 x.2.2)
  let B (x : ExtendedPointQuestion P) := S.placedMeasurement p2 (points.extendedQ p2.side x.1.1 x.1.2 x.2.1 x.2.2)
  have hpt' : consistencyDefect (uniformDistribution (ExtendedPointQuestion P))
      (fun x a => ((S.placedMeasurement p1 R).postprocess (ev x)).effect a)
      (fun x a => (B x).effect a) S.psiHat ≤ eta := by
    refine (le_of_eq ?_).trans hpoint
    apply consistencyDefect_congr <;> intro x a
    · exact (S.place_finsetSum p1 _ _).symm
    · rfl
  have hb := projective_refinement_ordered_dist_le
    (uniformDistribution (ExtendedPointQuestion P)) (S.placedMeasurement p1 R)
    (S.placedMeasurement_isProjective p1 R hR) ev A B
  refine ⟨?_, ?_⟩
  · have h := hb _ S.psiHat eta δQ δQ hpt' hself hXZ
    dsimp only [ProjectiveSetting.placedMeasurement_effect] at h; linarith
  · have h := hb _ S.psiHat eta δQ δQ hpt' hself hZX
    dsimp only [ProjectiveSetting.placedMeasurement_effect] at h; linarith

end CombinedPointsWitness

end

end MIPStarRE.QPBT
