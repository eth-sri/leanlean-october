module

public import GS.NonmanifoldClosure.TopologicalClosure
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Diagonal
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Calculus.Implicit
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Topology.Order.Compact

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.SharedGeometry GS.UnitaryNonmanifold Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology

namespace GS.UnitaryManifold
variable {n : ℕ}

abbrev FullUnitary (n : ℕ) := BlockK ℂ (fun _ : Fin n => 0)
abbrev FullSkewModel (n : ℕ) := ↥(supportedSkewSpace (fun _ : Fin n => 0))

def fullUnitary (Q : CMat n) (hQ : Unitary Q) : FullUnitary n :=
  ⟨Q, fun _ _ h => (h rfl).elim, hQ⟩

theorem continuous_matrix_product {X : Type*} [TopologicalSpace X]
    {A B : X → CMat n} (hA : Continuous A) (hB : Continuous B) :
    Continuous (fun x => A x * B x) := kcontinuous_matrix_product hA hB

def skewPart : CMat n →L[ℝ] FullSkewModel n :=
  ({ toFun := fun M => ⟨(1 / 2 : ℝ) • (M - Mᴴ), fun _ _ h => (h rfl).elim, by
       ext i j; simp [Matrix.conjTranspose_apply, Complex.real_smul]; ring⟩
     map_add' := fun _ _ => by ext i j; simp [Matrix.add_apply, Complex.real_smul]; ring
     map_smul' := fun _ _ => by ext i j; simp [Matrix.smul_apply, Complex.real_smul]; ring } :
    CMat n →ₗ[ℝ] FullSkewModel n).toContinuousLinearMap

@[simp] theorem skewPart_val (M : CMat n) : (skewPart M).val = (1 / 2 : ℝ) • (M - Mᴴ) := rfl

theorem skewPart_val_of_isSkew {A : CMat n} (hA : IsSkewHermitian A) : (skewPart A).val = A := by
  rw [skewPart_val, hA]; ext i j; simp [Complex.real_smul]; ring

def chartSource (Q : FullUnitary n) : Set (FullUnitary n) :=
  {U | kadmissible (Q.valᴴ * U.val)}
def chartMap (Q : FullUnitary n) (X : CMat n) : FullSkewModel n :=
  skewPart (kcayley (Q.valᴴ * X))
def chartInv (Q : FullUnitary n) (x : FullSkewModel n) : CMat n :=
  Q.val * kcayley x.val

@[simp] theorem base_mem_chartSource (Q : FullUnitary n) : Q ∈ chartSource Q := by
  change kadmissible (Q.valᴴ * Q.val); rw [Q.property.2.1]; exact admissible_one

theorem chartMap_val (Q U : FullUnitary n) (hU : U ∈ chartSource Q) :
    (chartMap Q U.val).val = kcayley (Q.valᴴ * U.val) :=
  skewPart_val_of_isSkew (cayley_isSkew _ (Q.property.2.conjTranspose.mul U.property.2) hU)

theorem centered_chartInv (Q : FullUnitary n) (x : FullSkewModel n) :
    Q.valᴴ * chartInv Q x = kcayley x.val := by
  simp only [chartInv, ← Matrix.mul_assoc, Q.property.2.1, Matrix.one_mul]

theorem chartMap_chartInv (Q : FullUnitary n) (x : FullSkewModel n) :
    chartMap Q (chartInv Q x) = x := by
  unfold chartMap; rw [centered_chartInv, cayley_involutive x.val (admissible_of_isSkew x.val x.property.2)]
  exact Subtype.ext (skewPart_val_of_isSkew x.property.2)

theorem chartInv_chartMap (Q U : FullUnitary n) (hU : U ∈ chartSource Q) :
    chartInv Q (chartMap Q U.val) = U.val := by
  unfold chartInv; rw [chartMap_val Q U hU, cayley_involutive _ hU]
  simp only [← Matrix.mul_assoc, Q.property.2.2, Matrix.one_mul]

@[simp] theorem chartInv_zero (Q : FullUnitary n) : chartInv Q 0 = Q.val := by simp [chartInv]
@[simp] theorem chartMap_base (Q : FullUnitary n) : chartMap Q Q.val = 0 := by
  rw [← chartInv_zero Q, chartMap_chartInv Q 0]

theorem chartMap_smooth_at (Q : FullUnitary n) (X : CMat n)
    (hX : kadmissible (Q.valᴴ * X)) : ContDiffAt ℝ ⊤ (chartMap Q) X :=
  skewPart.contDiff.contDiffAt.comp X
    (smooth_cayley_comp_at (ksmooth_mul_at contDiffAt_const contDiffAt_id) hX)

theorem chartInv_smooth (Q : FullUnitary n) : ContDiff ℝ ⊤ (chartInv Q) :=
  contDiff_iff_contDiffAt.mpr fun x =>
    ksmooth_mul_at contDiffAt_const
      (smooth_cayley_comp_at (supportedSkewSpace _).subtypeL.contDiff.contDiffAt
        (admissible_of_isSkew x.val x.property.2))

def blockPartialChart (Q : FullUnitary n) :
    OpenPartialHomeomorph (FullUnitary n) (FullSkewModel n) where
  toFun U := chartMap Q U.val
  invFun x := ⟨chartInv Q x, fun _ _ h => (h rfl).elim,
    Q.property.2.mul (cayley_unitary x.val x.property.2 (admissible_of_isSkew x.val x.property.2))⟩
  source := chartSource Q
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' x _ := by change kadmissible (Q.valᴴ * chartInv Q x); rw [centered_chartInv]; exact admissible_cayley x.val (admissible_of_isSkew x.val x.property.2)
  left_inv' U hU := Subtype.ext (chartInv_chartMap Q U hU)
  right_inv' x _ := chartMap_chartInv Q x
  open_source := admissible_open.preimage (continuous_matrix_product continuous_const continuous_subtype_val)
  open_target := isOpen_univ
  continuousOn_toFun U hU := ((chartMap_smooth_at Q U.val hU).continuousAt.comp
    continuous_subtype_val.continuousAt).continuousWithinAt
  continuousOn_invFun := ((chartInv_smooth Q).continuous.subtype_mk _).continuousOn

theorem chartInv_fderiv_zero (Q : FullUnitary n) (v : FullSkewModel n) :
    fderiv ℝ (chartInv Q) 0 v = (-2 : ℝ) • (Q.val * v.val) := by
  have hi := ((chartInv_smooth Q).differentiable (by simp) 0).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => t • v) v 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  exact (hi.comp_hasDerivAt_of_eq 0 hl (by simp)).unique (chartInv_line_hasDerivAt_zero Q v)

def fullSkewPairEquiv (q : ℕ) :
    (FullSkewModel q × FullSkewModel q) ≃ₗ[ℝ] CMat q where
  toFun p := p.1.val + Complex.I • p.2.val
  invFun M := (skewPart M, skewPart (-(Complex.I • M)))
  left_inv := fun ⟨A, B⟩ => by
    have hA (i j) : (starRingEnd ℂ) (A.val j i) = -A.val i j := congrFun (congrFun A.property.2 i) j
    have hB (i j) : (starRingEnd ℂ) (B.val j i) = -B.val i j := congrFun (congrFun B.property.2 i) j
    apply Prod.ext <;> apply Subtype.ext <;> simp only [skewPart_val] <;> ext i j : 2 <;>
      { simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
          Matrix.conjTranspose_apply, map_add, map_neg, smul_eq_mul, map_mul, Complex.star_def,
          Complex.conj_I, hA, hB, Complex.real_smul]
        push_cast; ring_nf; try { simp only [Complex.I_sq]; ring } }
  right_inv M := by
    simp only [skewPart_val]; ext i j : 2
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
      Matrix.conjTranspose_apply, map_neg, smul_eq_mul, map_mul, Complex.star_def, Complex.conj_I, Complex.real_smul]
    push_cast; ring_nf; simp only [Complex.I_sq]; ring
  map_add' _ _ := by ext i j; simp [Matrix.add_apply, Matrix.smul_apply]; ring
  map_smul' _ _ := by ext i j; simp [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]; ring

theorem finrank_fullModel (q : ℕ) :
    Module.finrank ℝ (FullSkewModel q) = q * q := by
  have h := (fullSkewPairEquiv q).finrank_eq
  simp [CMat, Module.finrank_prod, Module.finrank_matrix, Complex.basisOneI.equivFun.finrank_eq] at h
  omega

end GS.UnitaryManifold

open GS.UnitaryManifold
namespace GS.UnitaryLocalModel

def phase (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

theorem norm_phase {z : ℂ} (hz : z ≠ 0) : ‖phase z‖ = 1 := by
  simp [phase, norm_div, Complex.norm_real, abs_of_nonneg (norm_nonneg z), hz]

theorem conj_phase_mul_phase {z : ℂ} (hz : z ≠ 0) :
    star (phase z) * phase z = 1 := by
  change (starRingEnd ℂ) (phase z) * phase z = 1
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, norm_phase hz]; norm_num

theorem norm_mul_phase (z : ℂ) : (‖z‖ : ℂ) * phase z = z := by
  by_cases hz : z = 0
  · simp [hz, phase]
  · exact mul_div_cancel₀ z (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))

theorem conj_phase_mul (z : ℂ) : star (phase z) * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [hz, phase]
  · calc star (phase z) * z = star (phase z) * ((‖z‖ : ℂ) * phase z) :=
          congrArg (star (phase z) * ·) (norm_mul_phase z).symm
      _ = (‖z‖ : ℂ) * (star (phase z) * phase z) := by ring
      _ = (‖z‖ : ℂ) := by rw [conj_phase_mul_phase hz, mul_one]

variable {q : ℕ}

def AnchorNonzero (Q A : CMat q) (o : Fin q) : Prop :=
  (∀ i, Q i o ≠ 0 ∧ A i o ≠ 0) ∧ (∀ j, Q o j ≠ 0 ∧ A o j ≠ 0)

def rowPhase (Q A : CMat q) (o i : Fin q) : ℂ := phase (A i o / Q i o)
def colPhase (Q A : CMat q) (o j : Fin q) : ℂ := phase (A o j / Q o j)

def dephase (Q A : CMat q) (o : Fin q) : CMat q := fun i j =>
  star (rowPhase Q A o i) * A i j * star (colPhase Q A o j) * rowPhase Q A o o

theorem diagonal_unitary_of_norm_one (u : Fin q → ℂ) (hu : ∀ i, ‖u i‖ = 1) :
    GS.Unitary (Matrix.diagonal u) := by
  have h : (Matrix.diagonal u)ᴴ * Matrix.diagonal u = 1 := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    ext i j; by_cases hij : i = j
    · subst j; simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      change (starRingEnd ℂ) (u i) * u i = 1
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hu i]; norm_num
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply, hij]
  exact ⟨h, mul_eq_one_comm.mp h⟩

theorem dephase_unitary {Q A : CMat q} {o : Fin q}
    (hA : GS.Unitary A) (ha : AnchorNonzero Q A o) : GS.Unitary (dephase Q A o) := by
  have hr (i) : ‖rowPhase Q A o i‖ = 1 := norm_phase (div_ne_zero (ha.1 i).2 (ha.1 i).1)
  have hc (j) : ‖colPhase Q A o j‖ = 1 := norm_phase (div_ne_zero (ha.2 j).2 (ha.2 j).1)
  have h_eq : dephase Q A o = Matrix.diagonal (fun i => star (rowPhase Q A o i)) * A *
      Matrix.diagonal (fun j => star (colPhase Q A o j) * rowPhase Q A o o) := by
    ext i j; simp [dephase, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_assoc]
  rw [h_eq]
  exact ((diagonal_unitary_of_norm_one _ fun i => by simpa using hr i).mul hA).mul
    (diagonal_unitary_of_norm_one _ fun j => by rw [norm_mul, norm_star, hc j, hr o, mul_one])

theorem dephase_anchor_column_positive {Q A : CMat q} {o : Fin q}
    (ha : AnchorNonzero Q A o) (i : Fin q) :
    ∃ r : ℝ, 0 < r ∧ dephase Q A o i o / Q i o = r := by
  refine ⟨‖A i o / Q i o‖, norm_pos_iff.mpr (div_ne_zero (ha.1 i).2 (ha.1 i).1), ?_⟩
  calc dephase Q A o i o / Q i o
    _ = (star (rowPhase Q A o i) * (A i o / Q i o)) *
        (star (phase (A o o / Q o o)) * phase (A o o / Q o o)) := by
      simp only [dephase, rowPhase, colPhase]; ring
    _ = (‖A i o / Q i o‖ : ℂ) := by
      rw [conj_phase_mul_phase (div_ne_zero (ha.1 o).2 (ha.1 o).1), mul_one]
      exact conj_phase_mul _

theorem dephase_anchor_row_positive {Q A : CMat q} {o : Fin q}
    (ha : AnchorNonzero Q A o) (j : Fin q) :
    ∃ r : ℝ, 0 < r ∧ dephase Q A o o j / Q o j = r := by
  refine ⟨‖A o j / Q o j‖, norm_pos_iff.mpr (div_ne_zero (ha.2 j).2 (ha.2 j).1), ?_⟩
  calc dephase Q A o o j / Q o j
    _ = (star (colPhase Q A o j) * (A o j / Q o j)) *
        (star (phase (A o o / Q o o)) * phase (A o o / Q o o)) := by
      simp only [dephase, rowPhase, colPhase]; ring
    _ = (‖A o j / Q o j‖ : ℂ) := by
      rw [conj_phase_mul_phase (div_ne_zero (ha.1 o).2 (ha.1 o).1), mul_one]
      exact conj_phase_mul _

def rowPhaseDiagonal (Q A B : CMat q) (o i : Fin q) : CMat 2 :=
  diagTwo (rowPhase Q A o i) (rowPhase Q B o i)

def colPhaseDiagonal (Q A B : CMat q) (o j : Fin q) : CMat 2 :=
  diagTwo (colPhase Q A o j) (colPhase Q B o j)

theorem rowPhaseDiagonal_unitary {Q A B : CMat q} {o : Fin q}
    (ha : AnchorNonzero Q A o) (hb : AnchorNonzero Q B o) (i : Fin q) :
    GS.Unitary (rowPhaseDiagonal Q A B o i) := by
  apply diagonal_unitary_of_norm_one; intro k; fin_cases k
  · exact norm_phase (div_ne_zero (ha.1 i).2 (ha.1 i).1)
  · exact norm_phase (div_ne_zero (hb.1 i).2 (hb.1 i).1)

theorem colPhaseDiagonal_unitary {Q A B : CMat q} {o : Fin q}
    (ha : AnchorNonzero Q A o) (hb : AnchorNonzero Q B o) (j : Fin q) :
    GS.Unitary (colPhaseDiagonal Q A B o j) := by
  apply diagonal_unitary_of_norm_one; intro k; fin_cases k
  · exact norm_phase (div_ne_zero (ha.2 j).2 (ha.2 j).1)
  · exact norm_phase (div_ne_zero (hb.2 j).2 (hb.2 j).1)

def phaseGaugeLeft (U V : Fin q → CMat 2) (Q A B : CMat q)
    (o i : Fin q) : CMat 2 := U i * rowPhaseDiagonal Q A B o i * V o

def phaseGaugeRight (V : Fin q → CMat 2) (Q A B : CMat q)
    (o j : Fin q) : CMat 2 :=
  (V o)ᴴ * (rowPhaseDiagonal Q A B o o)ᴴ * colPhaseDiagonal Q A B o j * V j

theorem phaseGaugeLeft_unitary (U V : Fin q → CMat 2) (Q A B : CMat q) (o : Fin q)
    (hU : ∀ i, GS.Unitary (U i)) (hV : ∀ j, GS.Unitary (V j))
    (ha : AnchorNonzero Q A o) (hb : AnchorNonzero Q B o) (i : Fin q) :
    GS.Unitary (phaseGaugeLeft U V Q A B o i) :=
  ((hU i).mul (rowPhaseDiagonal_unitary ha hb i)).mul (hV o)

theorem phaseGaugeRight_unitary (V : Fin q → CMat 2) (Q A B : CMat q) (o : Fin q)
    (hV : ∀ j, GS.Unitary (V j))
    (ha : AnchorNonzero Q A o) (hb : AnchorNonzero Q B o) (j : Fin q) :
    GS.Unitary (phaseGaugeRight V Q A B o j) :=
  ((((hV o).conjTranspose).mul (rowPhaseDiagonal_unitary ha hb o).conjTranspose).mul
    (colPhaseDiagonal_unitary ha hb j)).mul (hV j)

theorem phaseGaugeRight_anchor (V : Fin q → CMat 2) (Q A B : CMat q) (o : Fin q)
    (hV : GS.Unitary (V o)) (ha : AnchorNonzero Q A o) (hb : AnchorNonzero Q B o) :
    phaseGaugeRight V Q A B o o = 1 := by
  unfold phaseGaugeRight
  change (V o)ᴴ * (rowPhaseDiagonal Q A B o o)ᴴ * rowPhaseDiagonal Q A B o o * V o = 1
  have hE := rowPhaseDiagonal_unitary ha hb o
  calc _ = (V o)ᴴ * ((rowPhaseDiagonal Q A B o o)ᴴ * rowPhaseDiagonal Q A B o o) * V o := by
          simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hE.1, Matrix.mul_one, hV.1]

theorem phase_normalization_block (U V : Fin q → CMat 2) (Q A B : CMat q)
    (o i j : Fin q) (hU : GS.Unitary (U i)) (hV : GS.Unitary (V j)) :
    (phaseGaugeLeft U V Q A B o i)ᴴ * (U i * diagTwo (A i j) (B i j) * V j) *
      (phaseGaugeRight V Q A B o j)ᴴ =
      (V o)ᴴ * diagTwo (dephase Q A o i j) (dephase Q B o i j) * V o := by
  have h_diag : (rowPhaseDiagonal Q A B o i)ᴴ * diagTwo (A i j) (B i j) *
      (colPhaseDiagonal Q A B o j)ᴴ * rowPhaseDiagonal Q A B o o =
      diagTwo (dephase Q A o i j) (dephase Q B o i j) := by
    ext a b; fin_cases a <;> fin_cases b <;>
      simp [rowPhaseDiagonal, colPhaseDiagonal, diagTwo, dephase, Matrix.mul_apply, Fin.sum_univ_two]
  unfold phaseGaugeLeft phaseGaugeRight
  calc _ = (V o)ᴴ * (rowPhaseDiagonal Q A B o i)ᴴ * ((U i)ᴴ * U i) * diagTwo (A i j) (B i j) *
          (V j * (V j)ᴴ) * (colPhaseDiagonal Q A B o j)ᴴ * rowPhaseDiagonal Q A B o o * V o := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = (V o)ᴴ * ((rowPhaseDiagonal Q A B o i)ᴴ * diagTwo (A i j) (B i j) *
          (colPhaseDiagonal Q A B o j)ᴴ * rowPhaseDiagonal Q A B o o) * V o := by
        rw [hU.1, hV.2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by rw [h_diag]

theorem sandwich_scalar_props (U V : CMat 2) (a b c : ℂ)
    (hU : GS.Unitary U) (hV : GS.Unitary V) (hc : c ≠ 0)
    (he : U * diagTwo a b * V = c • (1 : CMat 2)) :
    (a ≠ 0 ∧ b ≠ 0) ∧ U * diagTwo (phase (a / c)) (phase (b / c)) * V = 1 := by
  have hs : U * diagTwo (a / c) (b / c) * V = 1 := by
    have hdiv : diagTwo (a / c) (b / c) = c⁻¹ • diagTwo a b := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [diagTwo, div_eq_mul_inv, mul_comm]
    rw [hdiv, Matrix.mul_smul, Matrix.smul_mul, he, smul_smul]; simp [hc]
  have hd_u : GS.Unitary (diagTwo (a / c) (b / c)) := by
    have hd : diagTwo (a / c) (b / c) = Uᴴ * Vᴴ := by
      calc _ = Uᴴ * (U * diagTwo (a / c) (b / c) * V) * Vᴴ := by
              simp only [← Matrix.mul_assoc, hU.1, Matrix.one_mul]; rw [Matrix.mul_assoc, hV.2, Matrix.mul_one]
        _ = _ := by rw [hs, Matrix.mul_one]
    exact hd ▸ hU.conjTranspose.mul hV.conjTranspose
  have h0 : star (a / c) * (a / c) = 1 := by
    simpa [diagTwo, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] using
      congrFun (congrFun hd_u.1 0) 0
  have h1 : star (b / c) * (b / c) = 1 := by
    simpa [diagTwo, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] using
      congrFun (congrFun hd_u.1 1) 1
  have hn0 := congrArg norm h0; have hn1 := congrArg norm h1
  simp only [norm_mul, norm_star, norm_one] at hn0 hn1
  have ha : ‖a / c‖ = 1 := by nlinarith [norm_nonneg (a / c)]
  have hb : ‖b / c‖ = 1 := by nlinarith [norm_nonneg (b / c)]
  have hp0 (x : ℂ) (hx : ‖x‖ = 1) : phase x = x := by simp [phase, hx]
  refine ⟨⟨fun h => by simp [h] at ha, fun h => by simp [h] at hb⟩, ?_⟩
  rwa [hp0 _ ha, hp0 _ hb]

theorem base_fibre_dephased (U V : Fin q → CMat 2) (Q A B : CMat q)
    (o : Fin q) (hU : ∀ i, GS.Unitary (U i)) (hV : ∀ j, GS.Unitary (V j))
    (hQ : AnchorNonzero Q Q o)
    (he : ∀ i j, U i * diagTwo (A i j) (B i j) * V j = Q i j • (1 : CMat 2)) :
    (AnchorNonzero Q A o ∧ AnchorNonzero Q B o) ∧ dephase Q A o = Q ∧ dephase Q B o = Q := by
  have hc (i) := sandwich_scalar_props (U i) (V o) (A i o) (B i o) (Q i o) (hU i) (hV o) (hQ.1 i).1 (he i o)
  have hr (j) := sandwich_scalar_props (U o) (V j) (A o j) (B o j) (Q o j) (hU o) (hV j) (hQ.2 j).1 (he o j)
  have hl (i) : phaseGaugeLeft U V Q A B o i = 1 := (hc i).2
  have hrg (j) : phaseGaugeRight V Q A B o j = 1 := by
    have h_anch : phaseGaugeRight V Q A B o j =
        (phaseGaugeLeft U V Q A B o o)ᴴ * (U o * colPhaseDiagonal Q A B o j * V j) := by
      unfold phaseGaugeLeft phaseGaugeRight
      calc _ = (V o)ᴴ * (rowPhaseDiagonal Q A B o o)ᴴ * ((U o)ᴴ * U o) * colPhaseDiagonal Q A B o j * V j := by
              rw [(hU o).1, Matrix.mul_one]
        _ = _ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [h_anch, hl o, Matrix.conjTranspose_one, Matrix.one_mul]
    exact (hr j).2
  have hd (i j : Fin q) : diagTwo (dephase Q A o i j) (dephase Q B o i j) = Q i j • (1 : CMat 2) := by
    have hn := phase_normalization_block U V Q A B o i j (hU i) (hV j)
    rw [hl i, hrg j, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, he i j] at hn
    calc _ = V o * ((V o)ᴴ * diagTwo (dephase Q A o i j) (dephase Q B o i j) * V o) * (V o)ᴴ := by
            simp only [← Matrix.mul_assoc, (hV o).2, Matrix.one_mul]
            rw [Matrix.mul_assoc, (hV o).2, Matrix.mul_one]
      _ = _ := by rw [← hn, Matrix.mul_smul, Matrix.smul_mul]; simp only [Matrix.mul_one, (hV o).2]
  exact ⟨⟨⟨fun i => ⟨(hQ.1 i).1, (hc i).1.1⟩, fun j => ⟨(hQ.2 j).1, (hr j).1.1⟩⟩,
    ⟨fun i => ⟨(hQ.1 i).1, (hc i).1.2⟩, fun j => ⟨(hQ.2 j).1, (hr j).1.2⟩⟩⟩,
    by ext i j; simpa [diagTwo] using congrFun (congrFun (hd i j) 0) 0,
    by ext i j; simpa [diagTwo] using congrFun (congrFun (hd i j) 1) 1⟩

theorem continuousAt_phase {z : ℂ} (hz : z ≠ 0) : ContinuousAt phase z :=
  continuousAt_id.div (Complex.continuous_ofReal.continuousAt.comp continuous_norm.continuousAt)
    (by exact_mod_cast norm_ne_zero_iff.mpr hz)

theorem isOpen_anchorNonzero (Q : CMat q) (o : Fin q) :
    IsOpen {A : CMat q | AnchorNonzero Q A o} := by
  unfold AnchorNonzero
  refine IsOpen.and ?_ ?_ <;> simp only [Set.setOf_forall] <;>
    exact isOpen_iInter_of_finite fun _ => isOpen_const.and
      (isOpen_ne_fun (by fun_prop) continuous_const)

theorem continuousAt_dephase {Q A : CMat q} {o : Fin q}
    (ha : AnchorNonzero Q A o) :
    ContinuousAt (fun M : CMat q => dephase Q M o) A := by
  have hrow (i : Fin q) : ContinuousAt (fun M : CMat q => rowPhase Q M o i) A :=
    ContinuousAt.comp (f := fun M : CMat q => M i o / Q i o)
      (continuousAt_phase (div_ne_zero (ha.1 i).2 (ha.1 i).1))
      ((show Continuous (fun M : CMat q => M i o) from by fun_prop).continuousAt.div_const _)
  have hcol (j : Fin q) : ContinuousAt (fun M : CMat q => colPhase Q M o j) A :=
    ContinuousAt.comp (f := fun M : CMat q => M o j / Q o j)
      (continuousAt_phase (div_ne_zero (ha.2 j).2 (ha.2 j).1))
      ((show Continuous (fun M : CMat q => M o j) from by fun_prop).continuousAt.div_const _)
  refine continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j => ?_
  exact (((hrow i).star.mul (continuous_apply_apply i j).continuousAt).mul (hcol j).star).mul (hrow o)

abbrev AnchorCoordinates (o : Fin q) :=
  (Fin q → ℝ) × ({j : Fin q // j ≠ o} → ℝ)

def anchorImag (Q : CMat q) (o : Fin q) : CMat q →L[ℝ] AnchorCoordinates o :=
  ({ toFun := fun A => (fun i => (A i o / Q i o).im, fun j => (A o j.val / Q o j.val).im)
     map_add' := fun _ _ => by apply Prod.ext <;> funext i <;> simp [add_div, Complex.add_im]
     map_smul' := fun _ _ => by apply Prod.ext <;> funext i <;> simp [Complex.real_smul, mul_div_assoc, Complex.mul_im] } :
    CMat q →ₗ[ℝ] AnchorCoordinates o).toContinuousLinearMap

@[simp] theorem anchorImag_apply (Q A : CMat q) (o : Fin q) :
    anchorImag Q o A =
      (fun i => (A i o / Q i o).im, fun j => (A o j.val / Q o j.val).im) := rfl

def anchorConstraints (Q : FullUnitary q) (o : Fin q) (x : FullSkewModel q) :
    AnchorCoordinates o := anchorImag Q.val o (chartInv Q x)

@[simp] theorem anchorConstraints_zero (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : anchorConstraints Q o 0 = 0 := by
  rw [anchorConstraints, chartInv_zero]
  exact Prod.ext (funext fun i => by simp [anchorImag_apply, div_self (hQ.1 i).1])
    (funext fun j => by simp [anchorImag_apply, div_self (hQ.2 j.val).1])

def anchorDerivative (Q : FullUnitary q) (o : Fin q) :
    FullSkewModel q →L[ℝ] AnchorCoordinates o :=
  (anchorImag Q.val o).comp (fderiv ℝ (chartInv Q) 0)

theorem anchorConstraints_hasStrictFDerivAt (Q : FullUnitary q) (o : Fin q) :
    HasStrictFDerivAt (anchorConstraints Q o) (anchorDerivative Q o) 0 := by
  have hs : ContDiff ℝ ⊤ (anchorConstraints Q o) :=
    (anchorImag Q.val o).contDiff.comp (chartInv_smooth Q)
  exact hs.contDiffAt.hasStrictFDerivAt'
    (((anchorImag Q.val o).hasFDerivAt).comp 0
      ((chartInv_smooth Q).differentiable (by simp) 0).hasFDerivAt) (by simp)

def phaseDiagonal (a : Fin q → ℝ) : CMat q :=
  Matrix.diagonal (fun i => (a i : ℂ) * Complex.I)

theorem phaseDiagonal_skew (a : Fin q → ℝ) : IsSkewHermitian (phaseDiagonal a) := by
  unfold IsSkewHermitian phaseDiagonal
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_neg]
  exact congrArg Matrix.diagonal (funext fun i => by simp)

def phaseCoordinate (Q : FullUnitary q) (a b : Fin q → ℝ) : FullSkewModel q :=
  ⟨(-1 / 2 : ℝ) • (Q.valᴴ * phaseDiagonal a * Q.val + phaseDiagonal b),
    (by intro i j hij; exact (hij rfl).elim),
    skewHermitian_real_smul _ (skewHermitian_add
      (by simpa using conjugate_skewHermitian Q.valᴴ (phaseDiagonal a) (phaseDiagonal_skew a))
      (phaseDiagonal_skew b))⟩

theorem anchorDerivative_range (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    LinearMap.range (anchorDerivative Q o : FullSkewModel q →ₗ[ℝ] AnchorCoordinates o) = ⊤ := by
  refine LinearMap.range_eq_top.mpr fun ⟨a, b⟩ => ?_
  let β : Fin q → ℝ := fun j => if hj : j = o then 0 else b ⟨j, hj⟩ - a o
  use phaseCoordinate Q a β
  change anchorImag Q.val o (fderiv ℝ (chartInv Q) 0 (phaseCoordinate Q a β)) = (a, b)
  have h_vel : fderiv ℝ (chartInv Q) 0 (phaseCoordinate Q a β) =
      phaseDiagonal a * Q.val + Q.val * phaseDiagonal β := by
    rw [chartInv_fderiv_zero]
    change (-2 : ℝ) • (Q.val * ((-1 / 2 : ℝ) • (Q.valᴴ * phaseDiagonal a * Q.val + phaseDiagonal β))) = _
    rw [Matrix.mul_smul, smul_smul]; norm_num; rw [Matrix.mul_add]
    congr 1; simp only [← Matrix.mul_assoc, Q.property.2.2, Matrix.one_mul]
  rw [h_vel]
  have hβ0 : β o = 0 := by simp [β]
  apply Prod.ext
  · funext i
    change (((phaseDiagonal a * Q.val + Q.val * phaseDiagonal β) i o) / Q.val i o).im = a i
    simp only [Matrix.add_apply, phaseDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal, hβ0,
      Complex.ofReal_zero, zero_mul, mul_zero, add_zero]
    rw [mul_div_cancel_right₀ _ (hQ.1 i).1]; simp
  · funext j
    change (((phaseDiagonal a * Q.val + Q.val * phaseDiagonal β) o j.val) / Q.val o j.val).im = b j
    simp only [Matrix.add_apply, phaseDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [add_div, mul_div_cancel_right₀ _ (hQ.2 j.val).1, mul_div_cancel_left₀ _ (hQ.2 j.val).1]
    simp [β, j.property]

def AnchorPositive (Q A : CMat q) (o : Fin q) : Prop :=
  (∀ i, 0 < (A i o / Q i o).re) ∧ (∀ j, 0 < (A o j / Q o j).re)

theorem anchorPositive_open (Q : CMat q) (o : Fin q) :
    IsOpen {A : CMat q | AnchorPositive Q A o} := by
  have hc (i : Fin q) : IsOpen {A : CMat q | 0 < (A i o / Q i o).re} :=
    isOpen_lt continuous_const ((Complex.continuous_re).comp (((continuous_apply o).comp (continuous_apply i)).div_const _))
  have hr (j : Fin q) : IsOpen {A : CMat q | 0 < (A o j / Q o j).re} :=
    isOpen_lt continuous_const ((Complex.continuous_re).comp (((continuous_apply j).comp (continuous_apply o)).div_const _))
  convert (isOpen_iInter_of_finite hc).inter (isOpen_iInter_of_finite hr) using 1
  ext A; simp [AnchorPositive]

theorem anchorPositive_self (Q : CMat q) (o : Fin q)
    (hQ : AnchorNonzero Q Q o) : AnchorPositive Q Q o :=
  ⟨fun i => by simp [div_self (hQ.1 i).1], fun j => by simp [div_self (hQ.2 j).1]⟩

theorem dephased_constraints_iff (Q A : CMat q) (o : Fin q) :
    anchorImag Q o A = 0 ∧ AnchorPositive Q A o ↔
      (∀ i, ∃ r : ℝ, 0 < r ∧ A i o / Q i o = r) ∧
      (∀ j, ∃ r : ℝ, 0 < r ∧ A o j / Q o j = r) := by
  have h_re (z : ℂ) : (∃ r : ℝ, 0 < r ∧ z = r) ↔ z.im = 0 ∧ 0 < z.re :=
    ⟨fun ⟨r, hr, h⟩ => h ▸ ⟨rfl, hr⟩, fun ⟨hi, hr⟩ => ⟨z.re, hr, Complex.ext rfl hi⟩⟩
  have h_im : anchorImag Q o A = 0 ↔
      (∀ i, (A i o / Q i o).im = 0) ∧ (∀ j, (A o j / Q o j).im = 0) := by
    refine ⟨fun h => ?_, fun ⟨hc, hr⟩ => Prod.ext (funext hc) (funext fun j => hr j.val)⟩
    have hc (i) : (A i o / Q i o).im = 0 := congrArg (fun p : AnchorCoordinates o => p.1 i) h
    exact ⟨hc, fun j => if hj : j = o then hj ▸ hc o else congrArg (fun p : AnchorCoordinates o => p.2 ⟨j, hj⟩) h⟩
  rw [h_im]
  exact ⟨fun ⟨⟨hic, hir⟩, hpc, hpr⟩ =>
      ⟨fun i => (h_re _).mpr ⟨hic i, hpc i⟩, fun j => (h_re _).mpr ⟨hir j, hpr j⟩⟩,
    fun ⟨hc, hr⟩ => ⟨⟨fun i => ((h_re _).mp (hc i)).1, fun j => ((h_re _).mp (hr j)).1⟩,
      fun i => ((h_re _).mp (hc i)).2, fun j => ((h_re _).mp (hr j)).2⟩⟩

abbrev DephasedModel (Q : FullUnitary q) (o : Fin q) :=
  ↥(LinearMap.ker (anchorDerivative Q o : FullSkewModel q →ₗ[ℝ] AnchorCoordinates o))

theorem finrank_dephasedModel (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    Module.finrank ℝ (DephasedModel Q o) = (q - 1) ^ 2 := by
  classical
  have h_anc : Module.finrank ℝ (AnchorCoordinates o) = q + (q - 1) := by
    dsimp only [AnchorCoordinates]
    rw [Module.finrank_prod, Module.finrank_pi, Module.finrank_pi]
    simp only [Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  have hd := LinearMap.finrank_range_add_finrank_ker
    (anchorDerivative Q o : FullSkewModel q →ₗ[ℝ] AnchorCoordinates o)
  rw [anchorDerivative_range Q o hQ, finrank_top, h_anc, finrank_fullModel q] at hd
  have hq : q - 1 + 1 = q := by have ho := o.isLt; omega
  change Module.finrank ℝ (LinearMap.ker
    (anchorDerivative Q o : FullSkewModel q →ₗ[ℝ] AnchorCoordinates o)) = (q - 1) ^ 2
  nlinarith

def dephasedCoordinateEquiv (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    DephasedModel Q o ≃L[ℝ] (Fin ((q - 1) ^ 2) → ℝ) := by
  letI : Module.Free ℝ (DephasedModel Q o) :=
    Module.Free.of_basis (Module.Basis.ofVectorSpace ℝ (DephasedModel Q o))
  let b : Module.Basis (Fin ((q - 1) ^ 2)) ℝ (DephasedModel Q o) :=
    Module.finBasisOfFinrankEq ℝ (DephasedModel Q o) (finrank_dephasedModel Q o hQ)
  let e : DephasedModel Q o ≃ₗ[ℝ] (Fin ((q - 1) ^ 2) → ℝ) := b.equivFun
  exact LinearEquiv.toContinuousLinearEquiv (𝕜 := ℝ) (E := DephasedModel Q o) (F := Fin ((q - 1) ^ 2) → ℝ) e

def constraintChart (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    OpenPartialHomeomorph (FullSkewModel q) (AnchorCoordinates o × DephasedModel Q o) :=
  (anchorConstraints_hasStrictFDerivAt Q o).implicitToOpenPartialHomeomorph
    (anchorConstraints Q o) (anchorDerivative Q o) (anchorDerivative_range Q o hQ)

@[simp] theorem constraintChart_fst (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (x : FullSkewModel q) :
    (constraintChart Q o hQ x).1 = anchorConstraints Q o x :=
  (anchorConstraints_hasStrictFDerivAt Q o).implicitToOpenPartialHomeomorph_fst
    (anchorDerivative_range Q o hQ) x

@[simp] theorem constraintChart_zero (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : constraintChart Q o hQ 0 = (0, 0) := by
  unfold constraintChart
  rw [HasStrictFDerivAt.implicitToOpenPartialHomeomorph_self, anchorConstraints_zero Q o hQ]

theorem zero_mem_constraintChart_source (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : (0 : FullSkewModel q) ∈ (constraintChart Q o hQ).source :=
  (anchorConstraints_hasStrictFDerivAt Q o).mem_implicitToOpenPartialHomeomorph_source
    (anchorDerivative_range Q o hQ)

def unitaryConstraintChart (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    OpenPartialHomeomorph (FullUnitary q) (AnchorCoordinates o × (Fin ((q - 1) ^ 2) → ℝ)) :=
  (((blockPartialChart Q).trans (constraintChart Q o hQ)).trans
    ((ContinuousLinearEquiv.refl ℝ (AnchorCoordinates o)).prodCongr
      (dephasedCoordinateEquiv Q o hQ)).toHomeomorph.toOpenPartialHomeomorph).restrOpen
    {A | AnchorPositive Q.val A.val o}
    ((anchorPositive_open Q.val o).preimage continuous_subtype_val)

theorem unitaryConstraintChart_source_iff (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (A : FullUnitary q) :
    A ∈ (unitaryConstraintChart Q o hQ).source ↔
      A ∈ chartSource Q ∧ chartMap Q A.val ∈ (constraintChart Q o hQ).source ∧
        AnchorPositive Q.val A.val o := by
  change ((A ∈ chartSource Q ∧ chartMap Q A.val ∈ (constraintChart Q o hQ).source) ∧ True) ∧
    AnchorPositive Q.val A.val o ↔ _; tauto

theorem base_mem_unitaryConstraintChart_source (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : Q ∈ (unitaryConstraintChart Q o hQ).source :=
  (unitaryConstraintChart_source_iff Q o hQ Q).mpr
    ⟨base_mem_chartSource Q, by simpa using zero_mem_constraintChart_source Q o hQ,
      anchorPositive_self Q.val o hQ⟩

@[simp] theorem unitaryConstraintChart_base (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : unitaryConstraintChart Q o hQ Q = (0, 0) := by
  simp [unitaryConstraintChart, blockPartialChart]

theorem unitaryConstraintChart_fst (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (A : FullUnitary q)
    (hA : A ∈ (unitaryConstraintChart Q o hQ).source) :
    (unitaryConstraintChart Q o hQ A).1 = anchorImag Q.val o A.val := by
  change (constraintChart Q o hQ (chartMap Q A.val)).1 = _
  rw [constraintChart_fst]; unfold anchorConstraints
  rw [chartInv_chartMap Q A ((unitaryConstraintChart_source_iff Q o hQ A).mp hA).1]

def euclideanDephasedDomain (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : Set (Fin ((q - 1) ^ 2) → ℝ) :=
  {x | (0, x) ∈ (unitaryConstraintChart Q o hQ).target}

def euclideanDephasedParametrization (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (x : Fin ((q - 1) ^ 2) → ℝ) : CMat q :=
  ((unitaryConstraintChart Q o hQ).symm (0, x)).val

theorem euclideanDephasedDomain_open (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : IsOpen (euclideanDephasedDomain Q o hQ) :=
  (unitaryConstraintChart Q o hQ).open_target.preimage (continuous_const.prodMk continuous_id)

theorem zero_mem_euclideanDephasedDomain (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    (0 : Fin ((q - 1) ^ 2) → ℝ) ∈ euclideanDephasedDomain Q o hQ := by
  change (0, 0) ∈ (unitaryConstraintChart Q o hQ).target
  simpa only [unitaryConstraintChart_base] using (unitaryConstraintChart Q o hQ).map_source
    (base_mem_unitaryConstraintChart_source Q o hQ)

@[simp] theorem euclideanDephasedParametrization_zero (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : euclideanDephasedParametrization Q o hQ 0 = Q.val := by
  have h := (unitaryConstraintChart Q o hQ).left_inv (base_mem_unitaryConstraintChart_source Q o hQ)
  rw [unitaryConstraintChart_base] at h
  exact congrArg Subtype.val h

theorem dephasedParametrization_unitary (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (x : Fin ((q - 1) ^ 2) → ℝ) :
    Unitary (euclideanDephasedParametrization Q o hQ x) :=
  ((unitaryConstraintChart Q o hQ).symm (0, x)).property.2

theorem dephasedParametrization_constraints (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (x : Fin ((q - 1) ^ 2) → ℝ)
    (hx : x ∈ euclideanDephasedDomain Q o hQ) :
    anchorImag Q.val o (euclideanDephasedParametrization Q o hQ x) = 0 ∧
      AnchorPositive Q.val (euclideanDephasedParametrization Q o hQ x) o := by
  have hs := (unitaryConstraintChart Q o hQ).map_target hx
  refine ⟨?_, ((unitaryConstraintChart_source_iff Q o hQ _).mp hs).2.2⟩
  unfold euclideanDephasedParametrization
  rw [← unitaryConstraintChart_fst Q o hQ _ hs]
  exact congrArg Prod.fst ((unitaryConstraintChart Q o hQ).right_inv hx)

theorem euclideanDephasedParametrization_continuousOn (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    ContinuousOn (euclideanDephasedParametrization Q o hQ) (euclideanDephasedDomain Q o hQ) :=
  continuous_subtype_val.continuousOn.comp
    ((unitaryConstraintChart Q o hQ).continuousOn_symm.comp
      (continuous_const.prodMk continuous_id).continuousOn fun _ h => h)
    fun _ _ => Set.mem_univ _

theorem euclideanDephasedParametrization_injectiveOn (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    Set.InjOn (euclideanDephasedParametrization Q o hQ) (euclideanDephasedDomain Q o hQ) := by
  intro x hx y hy he
  have hh := congrArg (unitaryConstraintChart Q o hQ)
    (Subtype.ext he : (unitaryConstraintChart Q o hQ).symm (0, x) = (unitaryConstraintChart Q o hQ).symm (0, y))
  rw [(unitaryConstraintChart Q o hQ).right_inv hx, (unitaryConstraintChart Q o hQ).right_inv hy] at hh
  exact congrArg Prod.snd hh

theorem euclideanDephasedParametrization_coordinates (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (A : FullUnitary q)
    (hA : A ∈ (unitaryConstraintChart Q o hQ).source) (him : anchorImag Q.val o A.val = 0) :
    euclideanDephasedParametrization Q o hQ (unitaryConstraintChart Q o hQ A).2 = A.val := by
  have h_eq : unitaryConstraintChart Q o hQ A = (0, (unitaryConstraintChart Q o hQ A).2) :=
    Prod.ext ((unitaryConstraintChart_fst Q o hQ A hA).trans him) rfl
  simp only [euclideanDephasedParametrization, ← h_eq, (unitaryConstraintChart Q o hQ).left_inv hA]

def anchorFactorSet (Q : FullUnitary q) (o : Fin q) : Set (SmallFactorSpace q) :=
  {p | AnchorNonzero Q.val p.val.2.1 o ∧ AnchorNonzero Q.val p.val.2.2.1 o}

theorem anchorFactorSet_open (Q : FullUnitary q) (o : Fin q) :
    IsOpen (anchorFactorSet Q o) :=
  ((isOpen_anchorNonzero Q.val o).preimage (by fun_prop)).inter
    ((isOpen_anchorNonzero Q.val o).preimage (by fun_prop))

theorem dephase_anchorImag_zero {Q A : CMat q} {o : Fin q} (ha : AnchorNonzero Q A o) :
    anchorImag Q o (dephase Q A o) = 0 :=
  ((dephased_constraints_iff Q (dephase Q A o) o).mpr
    ⟨dephase_anchor_column_positive ha, dephase_anchor_row_positive ha⟩).1

def dephasedFirst (Q : FullUnitary q) (o : Fin q)
    (p : anchorFactorSet Q o) : FullUnitary q :=
  fullUnitary (dephase Q.val p.val.val.2.1 o)
    (dephase_unitary p.val.property.2.1 p.property.1)

def dephasedSecond (Q : FullUnitary q) (o : Fin q)
    (p : anchorFactorSet Q o) : FullUnitary q :=
  fullUnitary (dephase Q.val p.val.val.2.2.1 o)
    (dephase_unitary p.val.property.2.2.1 p.property.2)

theorem continuous_dephasedFirst (Q : FullUnitary q) (o : Fin q) :
    Continuous (dephasedFirst Q o) :=
  (continuous_iff_continuousAt.mpr fun p =>
    ContinuousAt.comp (f := fun p : anchorFactorSet Q o => p.val.val.2.1)
      (continuousAt_dephase p.property.1) (by fun_prop)).subtype_mk _

theorem continuous_dephasedSecond (Q : FullUnitary q) (o : Fin q) :
    Continuous (dephasedSecond Q o) :=
  (continuous_iff_continuousAt.mpr fun p =>
    ContinuousAt.comp (f := fun p : anchorFactorSet Q o => p.val.val.2.2.1)
      (continuousAt_dephase p.property.2) (by fun_prop)).subtype_mk _

end GS.UnitaryLocalModel

namespace GS.UnitaryLocalModel

abbrev AxisVector := Fin 3 → ℝ

def OnSphere (u : AxisVector) : Prop := u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1

def pauli (u : AxisVector) : CMat 2 :=
  !![(u 0 : ℂ), (u 1 : ℂ) - Complex.I * (u 2 : ℂ);
      (u 1 : ℂ) + Complex.I * (u 2 : ℂ), -(u 0 : ℂ)]

theorem continuous_pauli : Continuous pauli := by
  apply continuous_pi; intro i; apply continuous_pi; intro j
  fin_cases i <;> fin_cases j <;> simp [pauli] <;> fun_prop

theorem pauli_conjTranspose (u : AxisVector) : (pauli u)ᴴ = pauli u := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauli, Matrix.conjTranspose_apply] <;> ring

theorem pauli_square (u : AxisVector) :
    pauli u * pauli u = ((u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 : ℝ) : ℂ) • (1 : CMat 2) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauli, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem pauli_neg (u : AxisVector) : pauli (-u) = -pauli u := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauli] <;> ring

theorem exists_sphere_pauli (H : CMat 2)
    (hH : Hᴴ = H) (ht : Matrix.trace H = 0) (hs : H * H = 1) :
    ∃ u : AxisVector, OnSphere u ∧ pauli u = H := by
  let u : AxisVector := ![(H 0 0).re, (H 1 0).re, (H 1 0).im]
  have hdiag : (H 0 0).im = 0 := by
    have hh := congrArg Complex.im (congrFun (congrFun hH 0) 0)
    simp [Matrix.conjTranspose_apply] at hh; linarith
  have htrace : H 1 1 = -H 0 0 := by
    simpa [Matrix.trace, Fin.sum_univ_two, eq_neg_iff_add_eq_zero, add_comm] using ht
  have hu_eq : pauli u = H := by
    ext i j; fin_cases i <;> fin_cases j
    · apply Complex.ext <;> simp [pauli, u, hdiag]
    · change pauli u 0 1 = H 0 1; rw [(congrFun (congrFun hH 0) 1).symm]; apply Complex.ext <;> simp [pauli, u]
    · apply Complex.ext <;> simp [pauli, u]
    · change pauli u 1 1 = H 1 1; rw [htrace]; apply Complex.ext <;> simp [pauli, u, hdiag]
  refine ⟨u, ?_, hu_eq⟩
  rw [← hu_eq, pauli_square] at hs
  change u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1
  simpa only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
    Complex.ofReal_re, Complex.one_re] using congrArg Complex.re (congrFun (congrFun hs 0) 0)

def middleBlock (a b : ℂ) (u : AxisVector) : CMat 2 :=
  ((a + b) / 2) • (1 : CMat 2) + ((a - b) / 2) • pauli u

theorem middleBlock_simultaneous_swap (a b : ℂ) (u : AxisVector) :
    middleBlock b a (-u) = middleBlock a b u := by
  rw [middleBlock, pauli_neg]; ext i j; simp [middleBlock]; ring

theorem middleBlock_equal (a : ℂ) (u : AxisVector) :
    middleBlock a a u = a • (1 : CMat 2) := by
  simp [middleBlock]

theorem OnSphere.unitSq {u : AxisVector} (hu : OnSphere u) : UnitSq u := by
  simpa [OnSphere, UnitSq, Fin.sum_univ_three, ← add_assoc] using hu

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem exists_sphereOuter_of_rank_le_one (W : Matrix (Fin 3) κ ℝ)
    (hW : W.rank ≤ 1) :
    ∃ u : AxisVector, OnSphere u ∧ ∃ z : κ → ℝ, outer u z = W := by
  obtain ⟨u, hu, z, hz⟩ := GS.GlobalGeometry.exists_unitSq_outer_of_rank_le_one W hW
  exact ⟨u, by simpa [OnSphere, UnitSq, Fin.sum_univ_three, ← add_assoc] using hu, z, hz⟩

def axisDiagonal : CMat 2 := diagTwo 1 (-1)

@[simp] theorem axisDiagonal_conjTranspose : axisDiagonalᴴ = axisDiagonal := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [axisDiagonal, diagTwo, Matrix.conjTranspose_apply]

@[simp] theorem axisDiagonal_square : axisDiagonal * axisDiagonal = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [axisDiagonal, diagTwo, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem axisDiagonal_trace : Matrix.trace axisDiagonal = 0 := by
  simp [axisDiagonal, diagTwo, Matrix.trace, Fin.sum_univ_two]

theorem conjugated_diagTwo_eq_middle (S : CMat 2) (hS : GS.Unitary S)
    (u : AxisVector) (he : Sᴴ * axisDiagonal * S = pauli u) (a b : ℂ) :
    Sᴴ * diagTwo a b * S = middleBlock a b u := by
  have h_form : diagTwo a b = ((a + b) / 2) • (1 : CMat 2) + ((a - b) / 2) • axisDiagonal := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [axisDiagonal, diagTwo] <;> ring
  rw [h_form]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hS.1, he, middleBlock]

theorem exists_axis_of_unitary (S : CMat 2) (hS : GS.Unitary S) :
    ∃ u : AxisVector, OnSphere u ∧
      ∀ a b : ℂ, Sᴴ * diagTwo a b * S = middleBlock a b u := by
  let H := Sᴴ * axisDiagonal * S
  have hh : Hᴴ = H := by
    simp only [H, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      axisDiagonal_conjTranspose, Matrix.mul_assoc]
  have ht : Matrix.trace H = 0 := by
    change Matrix.trace (Sᴴ * axisDiagonal * S) = 0
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hS.2, Matrix.one_mul, axisDiagonal_trace]
  have hs : H * H = 1 := by
    calc H * H = Sᴴ * axisDiagonal * (S * Sᴴ) * axisDiagonal * S := by simp only [H, Matrix.mul_assoc]
      _ = 1 := by rw [hS.2, Matrix.mul_one, Matrix.mul_assoc Sᴴ, axisDiagonal_square, Matrix.mul_one, hS.1]
  obtain ⟨u, hu, he⟩ := exists_sphere_pauli H hh ht hs
  exact ⟨u, hu, conjugated_diagTwo_eq_middle S hS u he.symm⟩

theorem middleBlock_unitary_diagonalization (u : AxisVector) (hu : OnSphere u) :
    ∃ S : CMat 2, GS.Unitary S ∧
      ∀ a b : ℂ, Sᴴ * diagTwo a b * S = middleBlock a b u := by
  have hH : pauli u * pauli u = 1 := by rw [pauli_square, hu]; simp
  have hu0 : -1 ≤ u 0 := by
    dsimp [OnSphere] at hu; nlinarith [sq_nonneg (u 1), sq_nonneg (u 2), sq_nonneg (u 0 + 1)]
  suffices ∃ S : CMat 2, GS.Unitary S ∧ Sᴴ * axisDiagonal * S = pauli u by
    obtain ⟨S, hS, he⟩ := this
    exact ⟨S, hS, conjugated_diagTwo_eq_middle S hS u he⟩
  by_cases hp : u 0 = -1
  · have h1 : u 1 = 0 := by dsimp [OnSphere] at hu; rw [hp] at hu; nlinarith [sq_nonneg (u 2)]
    have h2 : u 2 = 0 := by dsimp [OnSphere] at hu; rw [hp] at hu; nlinarith [sq_nonneg (u 1)]
    refine ⟨!![0, 1; 1, 0], ?_, ?_⟩
    · constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
    · ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [axisDiagonal, diagTwo, pauli, hp, h1, h2, Matrix.mul_apply,
          Fin.sum_univ_two, Matrix.conjTranspose_apply]
  · let A := (1 : CMat 2) + pauli u * axisDiagonal
    let r := Real.sqrt (2 * (1 + u 0))
    have hpos : 0 < 2 * (1 + u 0) := by have : -1 < u 0 := lt_of_le_of_ne hu0 (Ne.symm hp); linarith
    have hr0 : r ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
    have hrs : r ^ 2 = 2 * (1 + u 0) := Real.sq_sqrt hpos.le
    have h_anti : pauli u * axisDiagonal + axisDiagonal * pauli u = (2 * u 0 : ℝ) • (1 : CMat 2) := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
          Fin.sum_univ_two, pauli, axisDiagonal, diagTwo, Matrix.diagonal_apply,
          Matrix.one_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
        norm_num [Complex.real_smul] <;> ring
    have hAA : Aᴴ * A = (2 * (1 + u 0) : ℝ) • (1 : CMat 2) := by
      calc Aᴴ * A = (1 : CMat 2) + 1 + (pauli u * axisDiagonal + axisDiagonal * pauli u) := by
            simp only [A, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
              Matrix.conjTranspose_mul, axisDiagonal_conjTranspose, pauli_conjTranspose,
              Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
            have ht : axisDiagonal * pauli u * (pauli u * axisDiagonal) = (1 : CMat 2) := by
              rw [Matrix.mul_assoc, ← Matrix.mul_assoc (pauli u), hH, Matrix.one_mul, axisDiagonal_square]
            rw [ht]; abel
        _ = _ := by
            rw [h_anti]; ext i j
            simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]; push_cast; ring
    let U := (r⁻¹ : ℝ) • A
    have hUleft : Uᴴ * U = 1 := by
      simp only [U, Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul,
        smul_smul, hAA]
      have he : r⁻¹ * (r⁻¹ * (2 * (1 + u 0))) = 1 := by rw [← hrs]; field_simp [hr0]
      rw [he, one_smul]
    have hU : GS.Unitary U := ⟨hUleft, mul_eq_one_comm.mp hUleft⟩
    have hHU : pauli u * U = U * axisDiagonal := by
      simp only [U, Matrix.mul_smul, Matrix.smul_mul]; congr 1
      dsimp [A]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
      rw [← Matrix.mul_assoc, hH, Matrix.one_mul, Matrix.mul_assoc, axisDiagonal_square, Matrix.mul_one]
      abel
    refine ⟨Uᴴ, hU.conjTranspose, ?_⟩
    rw [Matrix.conjTranspose_conjTranspose, ← hHU, Matrix.mul_assoc, hU.2, Matrix.mul_one]

def realify {κ : Type*} (z : κ → ℂ) : κ × Fin 2 → ℝ :=
  fun p => if p.2 = 0 then (z p.1).re else (z p.1).im

theorem realify_injective {κ : Type*} : Function.Injective (@realify κ) := fun _ _ h =>
  funext fun j => Complex.ext (by simpa [realify] using congrFun h (j, 0))
    (by simpa [realify] using congrFun h (j, 1))

def complexOuter {κ : Type*} (u : AxisVector) (z : κ → ℂ) : Matrix (Fin 3) κ ℂ :=
  fun i j => (u i : ℂ) * z j

theorem complexOuter_fibres {κ : Type*} {u v : AxisVector} {z w : κ → ℂ}
    (hu : OnSphere u) (hv : OnSphere v) :
    complexOuter u z = complexOuter v w ↔
      (z = 0 ∧ w = 0) ∨ (u = v ∧ z = w) ∨ (u = -v ∧ z = -w) := by
  have h_eq : complexOuter u z = complexOuter v w ↔
      outer u (realify z) = outer v (realify w) := by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · ext i p; have hh := congrFun (congrFun h i) p.1
      by_cases hp : p.2 = 0 <;> [simpa [outer, realify, hp, complexOuter] using congrArg Complex.re hh;
        simpa [outer, realify, hp, complexOuter] using congrArg Complex.im hh]
    · ext i j
      exact Complex.ext (by simpa [outer, realify, complexOuter] using congrFun (congrFun h i) (j, 0))
        (by simpa [outer, realify, complexOuter] using congrFun (congrFun h i) (j, 1))
  rw [h_eq, outer_fibres_unitSq hu.unitSq hv.unitSq]
  have hr0 (x : κ → ℂ) : realify x = 0 ↔ x = 0 := by
    rw [show (0 : κ × Fin 2 → ℝ) = realify 0 by funext p; simp [realify], realify_injective.eq_iff]
  have hrn : realify z = -realify w ↔ z = -w := by
    rw [show -realify w = realify (-w) by funext p; by_cases h : p.2 = 0 <;> simp [realify, h], realify_injective.eq_iff]
  rw [hr0, hr0, realify_injective.eq_iff, hrn]

def axisCoefficient (H : CMat 2) : Fin 3 → ℂ :=
  ![H 0 0 - H 1 1, H 0 1 + H 1 0, Complex.I * (H 0 1 - H 1 0)]

theorem middleBlock_family_fibres {κ : Type*} (a b c d : κ → ℂ)
    {u v : AxisVector} (hu : OnSphere u) (hv : OnSphere v) :
    (∀ j, middleBlock (a j) (b j) u = middleBlock (c j) (d j) v) ↔
      (a = b ∧ c = d ∧ a = c) ∨
      (u = v ∧ a = c ∧ b = d) ∨ (u = -v ∧ a = d ∧ b = c) := by
  have h_tr (x y : ℂ) (w : AxisVector) : Matrix.trace (middleBlock x y w) = x + y := by
    simp [Matrix.trace, Fin.sum_univ_two, middleBlock, pauli]; ring
  have h_ax (x y : ℂ) (w : AxisVector) :
      axisCoefficient (middleBlock x y w) = fun i => (w i : ℂ) * (x - y) := by
    funext i; fin_cases i <;> simp [axisCoefficient, middleBlock, pauli] <;>
      ring_nf <;> simp [Complex.I_sq] <;> ring
  refine ⟨fun h => ?_, ?_⟩
  · have hsum (j : κ) : a j + b j = c j + d j := by
      simpa only [h_tr] using congrArg Matrix.trace (h j)
    have ho : complexOuter u (a - b) = complexOuter v (c - d) := by
      ext i j; simpa only [h_ax, complexOuter, Pi.sub_apply] using congrFun (congrArg axisCoefficient (h j)) i
    rcases (complexOuter_fibres hu hv).mp ho with ⟨hab, hcd⟩ | ⟨huv, hdiff⟩ | ⟨huv, hdiff⟩
    · have hab' : a = b := sub_eq_zero.mp hab
      have hcd' : c = d := sub_eq_zero.mp hcd
      refine Or.inl ⟨hab', hcd', funext fun j => ?_⟩
      have hs := hsum j; rw [hab', hcd'] at hs
      simpa [hab', hcd'] using (by linear_combination (1 / 2 : ℂ) * hs : b j = d j)
    · have ha : a = c := funext fun j => by
        have hd : a j - b j = c j - d j := congrFun hdiff j
        linear_combination (1 / 2 : ℂ) * hsum j + (1 / 2 : ℂ) * hd
      exact Or.inr (Or.inl ⟨huv, ha, funext fun j => add_left_cancel (ha ▸ hsum j)⟩)
    · have ha : a = d := funext fun j => by
        have hd : a j - b j = -(c j - d j) := congrFun hdiff j
        linear_combination (1 / 2 : ℂ) * hsum j + (1 / 2 : ℂ) * hd
      exact Or.inr (Or.inr ⟨huv, ha, funext fun j => by have hs := ha ▸ hsum j; linear_combination hs⟩)
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · intro j; rw [middleBlock_equal, middleBlock_equal]
    · intro _; rfl
    · intro _; exact middleBlock_simultaneous_swap _ _ _

theorem positive_polar_unique {n : ℕ} (U V P Q : CMat n)
    (hU : GS.Unitary U) (hV : GS.Unitary V)
    (hP : P.PosDef) (hQ : Q.PosDef) (he : U * P = V * Q) :
    U = V ∧ P = Q := by
  have hs : P ^ 2 = Q ^ 2 := by
    simpa only [Matrix.conjTranspose_mul, hP.isHermitian.eq, hQ.isHermitian.eq,
      Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, ← Matrix.mul_assoc Vᴴ V,
      hU.1, hV.1, Matrix.one_mul, pow_two] using congrArg (fun T : CMat n => Tᴴ * T) he
  have hPQ : P = Q := (CFC.sq_eq_sq_iff P Q hP.posSemidef.nonneg hQ.posSemidef.nonneg).mp hs
  subst Q
  exact ⟨hP.isUnit.mul_right_cancel he, rfl⟩

theorem positive_polar_unique_right {n : ℕ} (U V P Q : CMat n)
    (hU : GS.Unitary U) (hV : GS.Unitary V)
    (hP : P.PosDef) (hQ : Q.PosDef) (he : P * U = Q * V) :
    U = V ∧ P = Q := by
  have ht : Uᴴ * P = Vᴴ * Q := by
    simpa only [Matrix.conjTranspose_mul, hP.isHermitian.eq, hQ.isHermitian.eq] using
      congrArg Matrix.conjTranspose he
  obtain ⟨hUV, hPQ⟩ := positive_polar_unique Uᴴ Vᴴ P Q hU.conjTranspose hV.conjTranspose hP hQ ht
  exact ⟨Matrix.conjTranspose_injective hUV, hPQ⟩

variable {q : ℕ}

theorem middleBlock_mul (a b c d : ℂ) (u : AxisVector) (hu : OnSphere u) :
    middleBlock a b u * middleBlock c d u = middleBlock (a * c) (b * d) u := by
  have hh : pauli u * pauli u = (1 : CMat 2) := by rw [pauli_square, hu]; simp
  unfold middleBlock
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, hh, smul_smul]
  ext i j; simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring

theorem middleBlock_ratio_posDef (a b c : ℂ) (u : AxisVector) (hu : OnSphere u)
    (ha : ∃ r : ℝ, 0 < r ∧ a / c = r)
    (hb : ∃ s : ℝ, 0 < s ∧ b / c = s) :
    (c⁻¹ • middleBlock a b u).PosDef := by
  obtain ⟨r, hr, ha⟩ := ha
  obtain ⟨s, hs, hb⟩ := hb
  have h_smul : c⁻¹ • middleBlock a b u = middleBlock (r : ℂ) (s : ℂ) u := by
    rw [show c⁻¹ • middleBlock a b u = middleBlock (c⁻¹ * a) (c⁻¹ * b) u by
      ext i j; simp only [middleBlock, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]; ring]
    rw [show c⁻¹ * a = (r : ℂ) by simpa only [div_eq_mul_inv, mul_comm] using ha,
        show c⁻¹ * b = (s : ℂ) by simpa only [div_eq_mul_inv, mul_comm] using hb]
  rw [h_smul]
  let B := middleBlock (Real.sqrt r : ℂ) (Real.sqrt s : ℂ) u
  let C := middleBlock ((Real.sqrt r : ℂ)⁻¹) ((Real.sqrt s : ℂ)⁻¹) u
  have hbr : (Real.sqrt r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hr))
  have hbs : (Real.sqrt s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hs))
  have hinv : C * B = 1 := by
    rw [show C * B = middleBlock ((Real.sqrt r : ℂ)⁻¹ * (Real.sqrt r : ℂ))
      ((Real.sqrt s : ℂ)⁻¹ * (Real.sqrt s : ℂ)) u from middleBlock_mul _ _ _ _ u hu]
    simp [hbr, hbs, middleBlock_equal]
  have hinj : Function.Injective B.mulVec := fun x y hxy => by
    simpa only [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] using congrArg (C *ᵥ ·) hxy
  have h_herm : Bᴴ = B := by
    simp [B, middleBlock, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, pauli_conjTranspose]
  have hsq : Bᴴ * B = middleBlock (r : ℂ) (s : ℂ) u := by
    rw [h_herm]; change B * B = _
    rw [middleBlock_mul _ _ _ _ u hu]
    simp only [← Complex.ofReal_mul, Real.mul_self_sqrt hr.le, Real.mul_self_sqrt hs.le]
  simpa only [Matrix.mul_one, hsq] using
    (Matrix.PosDef.one : (1 : CMat 2).PosDef).conjTranspose_mul_mul_same hinj

def localEnergy {d : ℕ} (x : Fin d → ℝ) : ℝ := ∑ i, x i ^ 2

theorem continuous_localEnergy (d : ℕ) : Continuous (@localEnergy d) := by
  unfold localEnergy; fun_prop

abbrev LocalParameters (d : ℕ) := (Fin d → ℝ) × (Fin d → ℝ) × AxisVector

def localParameterBox (d : ℕ) (r : ℝ) : Set (LocalParameters d) :=
  {p | localEnergy p.1 ≤ r ^ 2 ∧ localEnergy p.2.1 ≤ r ^ 2 ∧ OnSphere p.2.2}

theorem localEnergy_coordinate_bound {d : ℕ} (x : Fin d → ℝ) (r : ℝ)
    (hx : localEnergy x ≤ r ^ 2) (i : Fin d) : |x i| ≤ |r| := by
  have hi : x i ^ 2 ≤ localEnergy x :=
    Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  nlinarith [sq_abs (x i), sq_abs r, abs_nonneg (x i), abs_nonneg r]

theorem isCompact_localParameterBox (d : ℕ) (r : ℝ) :
    IsCompact (localParameterBox d r) := by
  have h_closed : IsClosed (localParameterBox d r) := by
    have hc : IsClosed {p : LocalParameters d | localEnergy p.1 ≤ r ^ 2} :=
      isClosed_le ((continuous_localEnergy d).comp continuous_fst) continuous_const
    have hz : IsClosed {p : LocalParameters d | localEnergy p.2.1 ≤ r ^ 2} :=
      isClosed_le ((continuous_localEnergy d).comp (by fun_prop)) continuous_const
    have hu : IsClosed {p : LocalParameters d | OnSphere p.2.2} :=
      isClosed_eq (show Continuous fun p : LocalParameters d => p.2.2 0 ^ 2 + p.2.2 1 ^ 2 + p.2.2 2 ^ 2 by fun_prop)
        continuous_const
    exact hc.inter (hz.inter hu)
  let lo : LocalParameters d := (fun _ => -|r|, fun _ => -|r|, fun _ => -1)
  let hi : LocalParameters d := (fun _ => |r|, fun _ => |r|, fun _ => 1)
  refine (show IsCompact (Set.Icc lo hi) from isCompact_Icc).of_isClosed_subset h_closed fun p hp => ?_
  have hc (i) := abs_le.mp (localEnergy_coordinate_bound p.1 r hp.1 i)
  have hz (i) := abs_le.mp (localEnergy_coordinate_bound p.2.1 r hp.2.1 i)
  have hu (i : Fin 3) : -1 ≤ p.2.2 i ∧ p.2.2 i ≤ 1 := by
    apply abs_le.mp
    have h_sph : OnSphere p.2.2 := hp.2.2
    have hs : p.2.2 i ^ 2 ≤ 1 := by
      fin_cases i <;> dsimp [OnSphere] at h_sph ⊢ <;>
        nlinarith [sq_nonneg (p.2.2 0), sq_nonneg (p.2.2 1), sq_nonneg (p.2.2 2)]
    nlinarith [sq_abs (p.2.2 i), abs_nonneg (p.2.2 i)]
  exact ⟨⟨fun i => (hc i).1, fun i => (hz i).1, fun i => (hu i).1⟩,
    ⟨fun i => (hc i).2, fun i => (hz i).2, fun i => (hu i).2⟩⟩

abbrev ConeCoordinates (d : ℕ) :=
  (Fin d → ℝ) × {W : Matrix (Fin 3) (Fin d) ℝ // W.rank ≤ 1}

def parameterCone {d : ℕ} (p : LocalParameters d) : ConeCoordinates d :=
  (p.1, ⟨outer p.2.2 p.2.1, rank_outer_le_one _ _⟩)

theorem continuous_parameterCone (d : ℕ) : Continuous (@parameterCone d) :=
  continuous_fst.prodMk (((show Continuous fun p : AxisVector × (Fin d → ℝ) => outer p.1 p.2 by
    unfold outer; fun_prop).comp (continuous_snd.snd.prodMk continuous_snd.fst)).subtype_mk _)

def boundedConeCoordinates (d : ℕ) (r : ℝ) : Set (ConeCoordinates d) :=
  {p | localEnergy p.1 ≤ r ^ 2 ∧ frobSq p.2.val ≤ r ^ 2}

def coneCoordinatesZero (d : ℕ) : ConeCoordinates d := (0, ⟨0, by simp⟩)

theorem boundedConeCoordinates_mem_nhds (d : ℕ) {r : ℝ} (hr : 0 < r) :
    boundedConeCoordinates d r ∈ 𝓝 (coneCoordinatesZero d) := by
  have hc : Continuous (fun p : ConeCoordinates d => localEnergy p.1) :=
    (continuous_localEnergy d).comp continuous_fst
  have hW : Continuous (fun p : ConeCoordinates d => frobSq p.2.val) := by
    unfold frobSq frobInner
    have hv : Continuous (fun p : ConeCoordinates d => p.2.val) := continuous_subtype_val.comp continuous_snd
    exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (((continuous_apply j).comp ((continuous_apply i).comp hv))).mul
        (((continuous_apply j).comp ((continuous_apply i).comp hv)))
  refine Filter.mem_of_superset
    (((isOpen_lt hc continuous_const).inter (isOpen_lt hW continuous_const)).mem_nhds ?_)
    fun _ hp => ⟨hp.1.le, hp.2.le⟩
  simp [coneCoordinatesZero, localEnergy, frobSq, frobInner, sq_pos_of_pos hr]

theorem exists_parameterBox_in_chart {d : ℕ} (U : Set (Fin d → ℝ))
    (hU : IsOpen U) (h0 : 0 ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∀ p ∈ localParameterBox d r,
      p.1 + p.2.1 ∈ U ∧ p.1 - p.2.1 ∈ U := by
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  refine ⟨ε / 3, by positivity, fun p hp => ?_⟩
  have h_norm {x : Fin d → ℝ} (hx : localEnergy x ≤ (ε / 3) ^ 2) : ‖x‖ ≤ ε / 3 :=
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ε / 3)] using
        localEnergy_coordinate_bound x (ε / 3) hx i
  have hc := h_norm hp.1
  have hz := h_norm hp.2.1
  exact ⟨hsub (by change dist (p.1 + p.2.1) 0 < ε; rw [dist_zero_right]; exact lt_of_le_of_lt (norm_add_le _ _) (by linarith)),
    hsub (by change dist (p.1 - p.2.1) 0 < ε; rw [dist_zero_right]; exact lt_of_le_of_lt (norm_sub_le _ _) (by linarith))⟩

abbrev BlockFamily (q : ℕ) := Fin q → Fin q → CMat 2

def flattenBlockFamily {q : ℕ} (N : BlockFamily q) : CMat (q * 2) :=
  fun i j => N (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1
    (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2

def extractBlockFamily {q : ℕ} (M : CMat (q * 2)) : BlockFamily q :=
  fun i j a b => M (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b))

@[simp] theorem extract_flattenBlockFamily {q : ℕ} (N : BlockFamily q) :
    extractBlockFamily (flattenBlockFamily N) = N := by
  funext i j a b; simp [extractBlockFamily, flattenBlockFamily]

@[simp] theorem flatten_extractBlockFamily {q : ℕ} (M : CMat (q * 2)) :
    flattenBlockFamily (extractBlockFamily M) = M := by
  ext i j
  change M (finProdFinEquiv (finProdFinEquiv.symm i)) (finProdFinEquiv (finProdFinEquiv.symm j)) = M i j
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

def blockFamilyHomeomorph (q : ℕ) : BlockFamily q ≃ₜ CMat (q * 2) where
  toFun := flattenBlockFamily
  invFun := extractBlockFamily
  left_inv := extract_flattenBlockFamily
  right_inv := flatten_extractBlockFamily
  continuous_toFun := by unfold flattenBlockFamily; fun_prop
  continuous_invFun := by unfold extractBlockFamily; fun_prop

abbrev OuterFactors (q : ℕ) (o : Fin q) :=
  (Fin q → FullUnitary 2) × ({j : Fin q // j ≠ o} → FullUnitary 2)

def outerLeft {q : ℕ} {o : Fin q} (g : OuterFactors q o) (i : Fin q) : CMat 2 := (g.1 i).val

def outerRight {q : ℕ} {o : Fin q} (g : OuterFactors q o) (j : Fin q) : CMat 2 :=
  if h : j = o then 1 else (g.2 ⟨j, h⟩).val

theorem outerLeft_unitary {q : ℕ} {o : Fin q} (g : OuterFactors q o) (i : Fin q) :
    GS.Unitary (outerLeft g i) := (g.1 i).property.2

theorem outerRight_unitary {q : ℕ} {o : Fin q} (g : OuterFactors q o) (j : Fin q) :
    GS.Unitary (outerRight g j) := by
  unfold outerRight; split <;> [exact GS.Unitary.one; exact (g.2 _).property.2]

@[simp] theorem outerRight_anchor {q : ℕ} {o : Fin q} (g : OuterFactors q o) :
    outerRight g o = 1 := by simp [outerRight]

def outerOfMatrices {q : ℕ} {o : Fin q} (L R : Fin q → CMat 2)
    (hL : ∀ i, GS.Unitary (L i)) (hR : ∀ j, GS.Unitary (R j)) : OuterFactors q o :=
  (fun i => fullUnitary (L i) (hL i), fun j => fullUnitary (R j.val) (hR j.val))

theorem outerRight_ofMatrices {q : ℕ} {o : Fin q} (L R : Fin q → CMat 2)
    (hL : ∀ i, GS.Unitary (L i)) (hR : ∀ j, GS.Unitary (R j)) (ho : R o = 1) :
    outerRight (outerOfMatrices (o := o) L R hL hR) = R := by
  funext j; by_cases hj : j = o
  · subst j; simp [outerRight, ho]
  · simp [outerRight, hj, outerOfMatrices, fullUnitary]

theorem outerFactors_ext {q : ℕ} {o : Fin q} {g h : OuterFactors q o}
    (hL : outerLeft g = outerLeft h) (hR : outerRight g = outerRight h) : g = h :=
  Prod.ext (funext fun i => Subtype.ext (congrFun hL i))
    (funext fun j => Subtype.ext (by simpa [outerRight, j.property] using congrFun hR j.val))

def chartBlockFamily {q d : ℕ} (ψ : (Fin d → ℝ) → CMat q)
    (p : LocalParameters d) : BlockFamily q :=
  fun i j => middleBlock (ψ (p.1 + p.2.1) i j) (ψ (p.1 - p.2.1) i j) p.2.2

def fullBlockImage {q d : ℕ} {o : Fin q} (ψ : (Fin d → ℝ) → CMat q)
    (g : OuterFactors q o) (p : LocalParameters d) : CMat (q * 2) :=
  flattenBlockFamily (fun i j => outerLeft g i * chartBlockFamily ψ p i j * outerRight g j)

abbrev FullCompactParameters (q : ℕ) (o : Fin q) (d : ℕ) (r : ℝ) :=
  OuterFactors q o × localParameterBox d r

def fullCompactMiddle {q d : ℕ} (ψ : (Fin d → ℝ) → CMat q) (o : Fin q) (r : ℝ)
    (p : FullCompactParameters q o d r) : CMat (q * 2) :=
  fullBlockImage ψ p.1 p.2.val

abbrev FullCompactImage {q d : ℕ} (ψ : (Fin d → ℝ) → CMat q) (o : Fin q) (r : ℝ) :=
  Set.range (fullCompactMiddle ψ o r)

instance fullCompactParameters_compactSpace (q : ℕ) (o : Fin q) (d : ℕ) (r : ℝ) :
    CompactSpace (FullCompactParameters q o d r) := by
  letI : CompactSpace (localParameterBox d r) :=
    isCompact_iff_compactSpace.mp (isCompact_localParameterBox d r)
  exact inferInstance

theorem continuous_fullCompactMiddle {q d : ℕ}
    (ψ : (Fin d → ℝ) → CMat q) (U : Set (Fin d → ℝ)) (o : Fin q) (r : ℝ)
    (hψ : ContinuousOn ψ U)
    (hargs : ∀ p ∈ localParameterBox d r, p.1 + p.2.1 ∈ U ∧ p.1 - p.2.1 ∈ U) :
    Continuous (fullCompactMiddle ψ o r) := by
  have hp : Continuous (fun p : FullCompactParameters q o d r => ψ (p.2.val.1 + p.2.val.2.1)) :=
    hψ.comp_continuous (by fun_prop) fun p => (hargs p.2.val p.2.property).1
  have hm : Continuous (fun p : FullCompactParameters q o d r => ψ (p.2.val.1 - p.2.val.2.1)) :=
    hψ.comp_continuous (by fun_prop) fun p => (hargs p.2.val p.2.property).2
  have hL : Continuous (@outerLeft q o) := by unfold outerLeft; fun_prop
  have hR : Continuous (@outerRight q o) :=
    continuous_pi fun j => by
      by_cases hj : j = o
      · simp only [outerRight, dif_pos hj]; exact continuous_const
      · simp only [outerRight, dif_neg hj]; fun_prop
  refine (show Continuous (@flattenBlockFamily q) by unfold flattenBlockFamily; fun_prop).comp ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have hpi := (continuous_apply j).comp ((continuous_apply i).comp hp)
  have hmi := (continuous_apply j).comp ((continuous_apply i).comp hm)
  refine continuous_matrix_product (continuous_matrix_product (((continuous_apply i).comp hL).comp continuous_fst) ?_)
    (((continuous_apply j).comp hR).comp continuous_fst)
  exact (((hpi.add hmi).div_const 2).smul continuous_const).add
    (((hpi.sub hmi).div_const 2).smul (continuous_pauli.comp (by fun_prop)))

def PositiveChartAnchors {q d : ℕ} (Q : CMat q) (o : Fin q)
    (ψ : (Fin d → ℝ) → CMat q) (U : Set (Fin d → ℝ)) : Prop :=
  ∀ x ∈ U, (∀ i, ∃ a : ℝ, 0 < a ∧ ψ x i o / Q i o = a) ∧
    (∀ j, ∃ a : ℝ, 0 < a ∧ ψ x o j / Q o j = a)

theorem chartBlockFamily_fibres {q d : ℕ}
    (ψ : (Fin d → ℝ) → CMat q) (U : Set (Fin d → ℝ)) (hψ : Set.InjOn ψ U)
    {p p' : LocalParameters d}
    (hcp : p.1 + p.2.1 ∈ U) (hcm : p.1 - p.2.1 ∈ U)
    (hcp' : p'.1 + p'.2.1 ∈ U) (hcm' : p'.1 - p'.2.1 ∈ U)
    (hu : OnSphere p.2.2) (hv : OnSphere p'.2.2) :
    chartBlockFamily ψ p = chartBlockFamily ψ p' ↔
      parameterCone p = parameterCone p' := by
  rcases p with ⟨c, z, u⟩; rcases p' with ⟨c', z', v⟩
  have hψ' {x y : Fin d → ℝ} (hx : x ∈ U) (hy : y ∈ U)
      (h : (fun ij : Fin q × Fin q => ψ x ij.1 ij.2) = fun ij => ψ y ij.1 ij.2) : x = y :=
    hψ hx hy (funext fun i => funext fun j => congrFun h (i, j))
  have h_cd (x y x' y' : Fin d → ℝ) (hp : x + y = x' + y') (hm : x - y = x' - y') : x = x' ∧ y = y' :=
    ⟨funext fun j => by have := congrFun hp j; have := congrFun hm j; dsimp at *; linarith,
     funext fun j => by have := congrFun hp j; have := congrFun hm j; dsimp at *; linarith⟩
  simp only [parameterCone, Prod.mk.injEq, Subtype.mk.injEq, outer_fibres_unitSq hu.unitSq hv.unitSq]
  refine ⟨fun h => ?_, ?_⟩
  · have he (ij : Fin q × Fin q) := congrFun (congrFun h ij.1) ij.2
    rcases (middleBlock_family_fibres _ _ _ _ hu hv).mp he with ⟨hzz, hzz', hcc⟩ | ⟨huv, hplus, hminus⟩ | ⟨huv, hplus, hminus⟩
    · have hz0 : z = 0 := funext fun j => by have := congrFun (hψ' hcp hcm hzz) j; dsimp at *; linarith
      have hz'0 : z' = 0 := funext fun j => by have := congrFun (hψ' hcp' hcm' hzz') j; dsimp at *; linarith
      subst z z'
      exact ⟨by simpa using hψ' hcp hcp' hcc, Or.inl ⟨rfl, rfl⟩⟩
    · obtain ⟨hc, hz⟩ := h_cd c z c' z' (hψ' hcp hcp' hplus) (hψ' hcm hcm' hminus)
      exact ⟨hc, Or.inr (Or.inl ⟨huv, hz⟩)⟩
    · obtain ⟨hc, hz⟩ := h_cd c z c' (-z')
        (by simpa only [sub_eq_add_neg] using hψ' hcp hcm' hplus)
        (by simpa using hψ' hcm hcp' hminus)
      exact ⟨hc, Or.inr (Or.inr ⟨huv, hz⟩)⟩
  · rintro ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · funext i j; simp [chartBlockFamily, middleBlock_equal]
    · rfl
    · funext i j; simp only [chartBlockFamily, ← sub_eq_add_neg, sub_neg_eq_add]
      exact middleBlock_simultaneous_swap _ _ _

theorem fullCompactMiddle_fibres {q d : ℕ} (Q : CMat q) (o : Fin q)
    (ψ : (Fin d → ℝ) → CMat q) (U : Set (Fin d → ℝ))
    (hψ : Set.InjOn ψ U) (hpos : PositiveChartAnchors Q o ψ U) (r : ℝ)
    (hargs : ∀ p ∈ localParameterBox d r, p.1 + p.2.1 ∈ U ∧ p.1 - p.2.1 ∈ U)
    (p p' : FullCompactParameters q o d r) :
    fullCompactMiddle ψ o r p = fullCompactMiddle ψ o r p' ↔
      p.1 = p'.1 ∧ parameterCone p.2.val = parameterCone p'.2.val := by
  have cancel_l (W A B : CMat 2) (hW : GS.Unitary W) (he : W * A = W * B) : A = B := by
    simpa only [← Matrix.mul_assoc, hW.1, Matrix.one_mul] using congrArg (Wᴴ * ·) he
  have cancel_r (W A B : CMat 2) (hW : GS.Unitary W) (he : A * W = B * W) : A = B := by
    simpa only [Matrix.mul_assoc, hW.2, Matrix.mul_one] using congrArg (· * Wᴴ) he
  have h_pos_l (t : localParameterBox d r) (i : Fin q) :
      ((Q i o)⁻¹ • chartBlockFamily ψ t.val i o).PosDef :=
    middleBlock_ratio_posDef _ _ _ _ t.property.2.2
      ((hpos _ (hargs _ t.property).1).1 i) ((hpos _ (hargs _ t.property).2).1 i)
  have h_pos_r (t : localParameterBox d r) (j : Fin q) :
      ((Q o j)⁻¹ • chartBlockFamily ψ t.val o j).PosDef :=
    middleBlock_ratio_posDef _ _ _ _ t.property.2.2
      ((hpos _ (hargs _ t.property).1).2 j) ((hpos _ (hargs _ t.property).2).2 j)
  rw [← chartBlockFamily_fibres ψ U hψ (hargs _ p.2.property).1 (hargs _ p.2.property).2
    (hargs _ p'.2.property).1 (hargs _ p'.2.property).2 p.2.property.2.2 p'.2.property.2.2]
  refine ⟨fun he => ?_, fun ⟨hg, hN⟩ => by simp only [fullCompactMiddle, fullBlockImage, hg, hN]⟩
  have hblocks (i j : Fin q) :
      outerLeft p.1 i * chartBlockFamily ψ p.2.val i j * outerRight p.1 j =
      outerLeft p'.1 i * chartBlockFamily ψ p'.2.val i j * outerRight p'.1 j := by
    simpa only [fullCompactMiddle, fullBlockImage, extract_flattenBlockFamily] using
      congrFun (congrFun (congrArg (@extractBlockFamily q) he) i) j
  have hLL : outerLeft p.1 = outerLeft p'.1 := funext fun i => by
    have hi := by simpa only [outerRight_anchor, Matrix.mul_one] using hblocks i o
    exact (positive_polar_unique _ _ _ _ (outerLeft_unitary p.1 i) (outerLeft_unitary p'.1 i)
      (h_pos_l p.2 i) (h_pos_l p'.2 i)
      (by simpa only [Matrix.mul_smul] using congrArg ((Q i o)⁻¹ • ·) hi)).1
  have hRR : outerRight p.1 = outerRight p'.1 := funext fun j => by
    have hj := cancel_l (outerLeft p.1 o) _ _ (outerLeft_unitary p.1 o)
      (by simpa only [Matrix.mul_assoc, hLL] using hblocks o j)
    exact (positive_polar_unique_right _ _ _ _ (outerRight_unitary p.1 j) (outerRight_unitary p'.1 j)
      (h_pos_r p.2 j) (h_pos_r p'.2 j)
      (by simpa only [Matrix.smul_mul] using congrArg ((Q o j)⁻¹ • ·) hj)).1
  refine ⟨outerFactors_ext hLL hRR, funext fun i => funext fun j => ?_⟩
  exact cancel_r _ _ _ (outerRight_unitary p.1 j) (cancel_l _ _ _ (outerLeft_unitary p.1 i)
    (by simpa only [Matrix.mul_assoc, hLL, hRR] using hblocks i j))

def fullCompactCone {q d : ℕ} {o : Fin q} {r : ℝ}
    (p : FullCompactParameters q o d r) : OuterFactors q o × ConeCoordinates d :=
  (p.1, parameterCone p.2.val)

def fullCompactSource {q d : ℕ} (F : Set (CMat (q * 2)))
    (ψ : (Fin d → ℝ) → CMat q) (o : Fin q) (r : ℝ) : Set F :=
  {M | M.val ∈ FullCompactImage ψ o r}

theorem full_compact_pointed_neighbourhood_model {q d : ℕ}
    (F : Set (CMat (q * 2))) (x : F) (Q : CMat q) (o : Fin q)
    (ψ : (Fin d → ℝ) → CMat q) (U : Set (Fin d → ℝ))
    (hψc : ContinuousOn ψ U) (hψi : Set.InjOn ψ U)
    (hpos : PositiveChartAnchors Q o ψ U) (r : ℝ) (hr : 0 < r)
    (hargs : ∀ p ∈ localParameterBox d r, p.1 + p.2.1 ∈ U ∧ p.1 - p.2.1 ∈ U)
    (hsub : FullCompactImage ψ o r ⊆ F)
    (hcover : fullCompactSource F ψ o r ∈ 𝓝 x)
    (p₀ : FullCompactParameters q o d r)
    (hbase : fullCompactMiddle ψ o r p₀ = x.val)
    (hzero : parameterCone p₀.2.val = coneCoordinatesZero d) :
    Nonempty (GS.NonmanifoldCompletion.PointedNeighbourhoodModel F
      (OuterFactors q o × ConeCoordinates d) x (p₀.1, coneCoordinatesZero d)) := by
  let h_src : fullCompactSource F ψ o r ≃ₜ FullCompactImage ψ o r :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      invFun := fun y => ⟨⟨y.val, hsub y.property⟩, y.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have h_cont_cone : Continuous (@fullCompactCone q d o r) :=
    continuous_fst.prodMk ((continuous_parameterCone d).comp (continuous_subtype_val.comp continuous_snd))
  obtain ⟨h, hh⟩ := exists_homeomorph_ranges_of_same_fibres
    (fullCompactMiddle ψ o r) (@fullCompactCone q d o r)
    (continuous_fullCompactMiddle ψ U o r hψc hargs) h_cont_cone
    (fun p p' => by
      rw [fullCompactMiddle_fibres Q o ψ U hψi hpos r hargs p p']
      simp only [fullCompactCone, Prod.mk.injEq])
  refine ⟨{
    source := fullCompactSource F ψ o r
    target := Set.range (@fullCompactCone q d o r)
    source_nhds := hcover
    target_nhds := Filter.mem_of_superset
      (continuous_snd.continuousAt.preimage_mem_nhds (boundedConeCoordinates_mem_nhds d hr))
      fun ⟨g, w⟩ ⟨hc, hW⟩ => by
        obtain ⟨u, hu, z, hz⟩ := exists_sphereOuter_of_rank_le_one w.2.val w.2.property
        have he : localEnergy z = frobSq w.2.val := by rw [← hz, frobSq_outer_unitSq hu.unitSq]; rfl
        exact ⟨(g, ⟨(w.1, z, u), hc, he ▸ hW, hu⟩), Prod.ext rfl (Prod.ext rfl (Subtype.ext hz))⟩
    chart := h_src.trans h
    map_point := fun hx => by
      have he : h_src ⟨x, hx⟩ = ⟨fullCompactMiddle ψ o r p₀, ⟨p₀, rfl⟩⟩ := Subtype.ext hbase.symm
      change (h (h_src ⟨x, hx⟩)).val = _
      rw [he, hh p₀]; exact Prod.ext rfl hzero }⟩

def scalarBlockBase {q : ℕ} (Q : CMat q) : CMat (q * 2) :=
  flattenBlockFamily (fun i j => Q i j • (1 : CMat 2))

def identityOuter (q : ℕ) (o : Fin q) : OuterFactors q o := (fun _ => 1, fun _ => 1)

def parameterZero (d : ℕ) : LocalParameters d := (0, 0, ![1, 0, 0])

theorem parameterZero_mem (d : ℕ) (r : ℝ) : parameterZero d ∈ localParameterBox d r := by
  simp [parameterZero, localParameterBox, localEnergy, OnSphere, sq_nonneg]

@[simp] theorem parameterCone_zero (d : ℕ) :
    parameterCone (parameterZero d) = coneCoordinatesZero d :=
  Prod.ext rfl (Subtype.ext (by ext i j; simp [parameterCone, parameterZero, coneCoordinatesZero, outer]))

def fullParameterZero (q d : ℕ) (o : Fin q) (r : ℝ) : FullCompactParameters q o d r :=
  (identityOuter q o, ⟨parameterZero d, parameterZero_mem d r⟩)

@[simp] theorem fullCompactMiddle_zero {q d : ℕ}
    (ψ : (Fin d → ℝ) → CMat q) (o : Fin q) (r : ℝ) :
    fullCompactMiddle ψ o r (fullParameterZero q d o r) = scalarBlockBase (ψ 0) := by
  unfold fullCompactMiddle fullBlockImage scalarBlockBase
  apply congrArg (@flattenBlockFamily q)
  funext i j
  have hl : outerLeft (identityOuter q o) i = 1 := rfl
  have hr : outerRight (identityOuter q o) j = 1 := by unfold outerRight identityOuter; split <;> rfl
  simp [fullParameterZero, hl, hr, chartBlockFamily, parameterZero, middleBlock_equal]

theorem fullBlockImage_mem_localFamily {q d : ℕ} {o : Fin q}
    (ψ : (Fin d → ℝ) → CMat q) (g : OuterFactors q o) (p : LocalParameters d)
    (hp : GS.Unitary (ψ (p.1 + p.2.1))) (hm : GS.Unitary (ψ (p.1 - p.2.1)))
    (hu : OnSphere p.2.2) :
    fullBlockImage ψ g p ∈ GS.UnitaryNonmanifold.localFamily q := by
  obtain ⟨S, hS, hdiag⟩ := middleBlock_unitary_diagonalization p.2.2 hu
  let v : SmallBlockParameters q :=
    (fun i => outerLeft g i * Sᴴ, ψ (p.1 + p.2.1), ψ (p.1 - p.2.1), fun j => S * outerRight g j)
  have hv : v ∈ smallFactorSet q :=
    ⟨fun i => (outerLeft_unitary g i).mul hS.conjTranspose, hp, hm, fun j => hS.mul (outerRight_unitary g j)⟩
  have he : smallFactorMap v = fullBlockImage ψ g p := by
    apply (blockFamilyHomeomorph q).symm.injective
    change extractBlockFamily (smallFactorMap v) = extractBlockFamily (fullBlockImage ψ g p)
    unfold fullBlockImage; rw [extract_flattenBlockFamily]
    funext i j a b
    change smallFactorMap v (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) = _
    rw [smallFactorMap_block]
    change ((outerLeft g i * Sᴴ) * diagTwo (ψ (p.1 + p.2.1) i j) (ψ (p.1 - p.2.1) i j) *
      (S * outerRight g j)) a b =
      (outerLeft g i * middleBlock (ψ (p.1 + p.2.1) i j) (ψ (p.1 - p.2.1) i j) p.2.2 * outerRight g j) a b
    rw [← hdiag]; simp only [Matrix.mul_assoc]
  rw [← he, ← image_smallFactorMap]
  exact ⟨v, hv, rfl⟩

theorem fullCompactImage_subset_localFamily {q d : ℕ}
    (ψ : (Fin d → ℝ) → CMat q) (o : Fin q) (U : Set (Fin d → ℝ))
    (hψ : ∀ x ∈ U, GS.Unitary (ψ x)) (r : ℝ)
    (hargs : ∀ p ∈ localParameterBox d r, p.1 + p.2.1 ∈ U ∧ p.1 - p.2.1 ∈ U) :
    FullCompactImage ψ o r ⊆ GS.UnitaryNonmanifold.localFamily q := by
  rintro _ ⟨p, rfl⟩
  exact fullBlockImage_mem_localFamily ψ p.1 p.2.val
    (hψ _ (hargs _ p.2.property).1) (hψ _ (hargs _ p.2.property).2) p.2.property.2.2

theorem scalarBlockBase_mem_localFamily {q : ℕ} (Q : CMat q) (hQ : GS.Unitary Q)
    (o : Fin q) : scalarBlockBase Q ∈ GS.UnitaryNonmanifold.localFamily q := by
  have h := fullBlockImage_mem_localFamily (d := 0) (fun _ => Q)
    (identityOuter q o) (parameterZero 0) hQ hQ (by simp [parameterZero, OnSphere])
  have he := fullCompactMiddle_zero (d := 0) (fun _ => Q) o 0
  change fullBlockImage (fun _ => Q) (identityOuter q o) (parameterZero 0) = _ at he
  exact he ▸ h

def smallDephasedSource (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (r : ℝ) : Set (FullUnitary q) :=
  {A | A ∈ (unitaryConstraintChart Q o hQ).source ∧
    localEnergy (unitaryConstraintChart Q o hQ A).2 < r ^ 2}

theorem smallDephasedSource_open (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (r : ℝ) : IsOpen (smallDephasedSource Q o hQ r) :=
  (((continuous_localEnergy _).comp continuous_snd).comp_continuousOn
    (unitaryConstraintChart Q o hQ).continuousOn).isOpen_inter_preimage
    (unitaryConstraintChart Q o hQ).open_source isOpen_Iio

theorem base_mem_smallDephasedSource (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (r : ℝ) (hr : 0 < r) :
    Q ∈ smallDephasedSource Q o hQ r :=
  ⟨base_mem_unitaryConstraintChart_source Q o hQ,
    by simpa [unitaryConstraintChart_base, localEnergy] using sq_pos_of_pos hr⟩

def smallFullFactors (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (r : ℝ) : Set (SmallFactorSpace q) :=
  Subtype.val '' {p : anchorFactorSet Q o |
    dephasedFirst Q o p ∈ smallDephasedSource Q o hQ r ∧
    dephasedSecond Q o p ∈ smallDephasedSource Q o hQ r}

theorem smallFullFactors_open (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (r : ℝ) : IsOpen (smallFullFactors Q o hQ r) :=
  (anchorFactorSet_open Q o).isOpenMap_subtype_val _
    (((smallDephasedSource_open Q o hQ r).preimage (continuous_dephasedFirst Q o)).inter
      ((smallDephasedSource_open Q o hQ r).preimage (continuous_dephasedSecond Q o)))

theorem smallFullFactors_map_mem (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (r : ℝ) (p : SmallFactorSpace q)
    (hp : p ∈ smallFullFactors Q o hQ r) :
    smallFactorValue q p ∈ FullCompactImage (euclideanDephasedParametrization Q o hQ) o r := by
  obtain ⟨p, hp, rfl⟩ := hp
  let a := (unitaryConstraintChart Q o hQ (dephasedFirst Q o p)).2
  let b := (unitaryConstraintChart Q o hQ (dephasedSecond Q o p)).2
  let c : Fin ((q - 1) ^ 2) → ℝ := fun i => (a i + b i) / 2
  let z : Fin ((q - 1) ^ 2) → ℝ := fun i => (a i - b i) / 2
  have hca : c + z = a := by ext i; dsimp [c, z]; ring
  have hcb : c - z = b := by ext i; dsimp [c, z]; ring
  have h_avg (w : Fin ((q - 1) ^ 2) → ℝ) (hw : ∀ i, w i ^ 2 ≤ (a i ^ 2 + b i ^ 2) / 2) : localEnergy w ≤ r ^ 2 := by
    have h2 : localEnergy w ≤ (localEnergy a + localEnergy b) / 2 := by
      simpa only [localEnergy, ← Finset.sum_div, Finset.sum_add_distrib] using
        Finset.sum_le_sum (s := Finset.univ) fun i _ => hw i
    linarith [hp.1.2, hp.2.2]
  have hc : localEnergy c ≤ r ^ 2 := h_avg c fun i => by dsimp [c]; nlinarith [sq_nonneg (a i - b i)]
  have hz : localEnergy z ≤ r ^ 2 := h_avg z fun i => by dsimp [z]; nlinarith [sq_nonneg (a i + b i)]
  have hea := euclideanDephasedParametrization_coordinates Q o hQ (dephasedFirst Q o p) hp.1.1
    (dephase_anchorImag_zero p.property.1)
  have heb := euclideanDephasedParametrization_coordinates Q o hQ (dephasedSecond Q o p) hp.2.1
    (dephase_anchorImag_zero p.property.2)
  let U := p.val.val.1; let V := p.val.val.2.2.2; let A := p.val.val.2.1; let B := p.val.val.2.2.1
  have hU : ∀ i, Unitary (U i) := p.val.property.1
  have hV : ∀ j, Unitary (V j) := p.val.property.2.2.2
  let L := phaseGaugeLeft U V Q.val A B o
  let R := phaseGaugeRight V Q.val A B o
  have hL : ∀ i, Unitary (L i) := phaseGaugeLeft_unitary U V Q.val A B o hU hV p.property.1 p.property.2
  have hR : ∀ j, Unitary (R j) := phaseGaugeRight_unitary V Q.val A B o hV p.property.1 p.property.2
  have hRo : R o = 1 := phaseGaugeRight_anchor V Q.val A B o (hV o) p.property.1 p.property.2
  obtain ⟨u, hu, hdiag⟩ := exists_axis_of_unitary (V o) (hV o)
  let g : OuterFactors q o := outerOfMatrices L R hL hR
  let t : localParameterBox ((q - 1) ^ 2) r := ⟨(c, z, u), hc, hz, hu⟩
  refine ⟨(g, t), ?_⟩
  apply (blockFamilyHomeomorph q).symm.injective
  change extractBlockFamily (fullCompactMiddle _ o r (g, t)) = extractBlockFamily (smallFactorValue q p.val)
  rw [fullCompactMiddle, fullBlockImage, extract_flattenBlockFamily]
  funext i j
  have hn := phase_normalization_block U V Q.val A B o i j (hU i) (hV j)
  have he : L i * middleBlock (dephase Q.val A o i j) (dephase Q.val B o i j) u * R j =
      U i * diagTwo (A i j) (B i j) * V j := by
    rw [← hdiag, ← hn]
    calc _ = (L i * (L i)ᴴ) * (U i * diagTwo (A i j) (B i j) * V j) * ((R j)ᴴ * R j) := by
            dsimp only [L, R]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [(hL i).2, (hR j).1]; simp
  rw [show outerLeft g = L from rfl, outerRight_ofMatrices L R hL hR hRo]
  have hmiddle : chartBlockFamily (euclideanDephasedParametrization Q o hQ) t.val i j =
      middleBlock (dephase Q.val A o i j) (dephase Q.val B o i j) u := by
    change middleBlock (euclideanDephasedParametrization Q o hQ (c + z) i j)
      (euclideanDephasedParametrization Q o hQ (c - z) i j) u = _
    rw [hca, hcb, hea, heb]; rfl
  rw [hmiddle, he]
  ext k l; exact (smallFactorMap_block p.val.val i j k l).symm

theorem exists_open_full_compact_coverage (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (r : ℝ) (hr : 0 < r) :
    ∃ W : Set (CMat (q * 2)), IsOpen W ∧ scalarBlockBase Q.val ∈ W ∧
      ∀ M ∈ GS.UnitaryNonmanifold.localFamily q, M ∈ W →
        M ∈ FullCompactImage (euclideanDephasedParametrization Q o hQ) o r := by
  have h_base (p : SmallFactorSpace q) (he : smallFactorValue q p = scalarBlockBase Q.val) :
      p ∈ smallFullFactors Q o hQ r := by
    have hv : extractBlockFamily (smallFactorValue q p) = fun i j =>
        p.val.1 i * diagTwo (p.val.2.1 i j) (p.val.2.2.1 i j) * p.val.2.2.2 j :=
      funext fun i => funext fun j => funext fun a => funext fun b => smallFactorMap_block p.val i j a b
    have hh := congrArg (@extractBlockFamily q) he
    rw [hv, scalarBlockBase, extract_flattenBlockFamily] at hh
    obtain ⟨ha, hd1, hd2⟩ := base_fibre_dephased p.val.1 p.val.2.2.2 Q.val p.val.2.1 p.val.2.2.1 o
      p.property.1 p.property.2.2.2 hQ (fun i j => congrFun (congrFun hh i) j)
    refine ⟨⟨p, ha⟩, ⟨?_, ?_⟩, rfl⟩
    · rw [show dephasedFirst Q o ⟨p, ha⟩ = Q from Subtype.ext hd1]
      exact base_mem_smallDephasedSource Q o hQ r hr
    · rw [show dephasedSecond Q o ⟨p, ha⟩ = Q from Subtype.ext hd2]
      exact base_mem_smallDephasedSource Q o hQ r hr
  obtain ⟨W, hW, hbase, hcover⟩ := GS.Continuation.compact_full_fibre_neighbourhood
    (smallFactorValue q) (continuous_smallFactorValue q) Set.univ isCompact_univ
    (smallFullFactors Q o hQ r) (smallFullFactors_open Q o hQ r) (scalarBlockBase Q.val)
    (fun p _ he => h_base p he)
  refine ⟨W, hW, hbase, fun M hM hMW => ?_⟩
  obtain ⟨p, hp, he⟩ := hcover M hMW (by rw [Set.image_univ, range_smallFactorValue]; exact hM)
  exact he ▸ smallFullFactors_map_mem Q o hQ r p hp.2

end GS.UnitaryLocalModel

open Matrix GS GS.UnitaryManifold GS.UnitaryLocalModel GS.UnitaryGeometry
open GS.NonmanifoldFinal GS.NonmanifoldClosure GS.NonmanifoldObstruction
open GS.NonmanifoldTopology GS.NonmanifoldCompletion
open scoped BigOperators Topology

namespace GS.UnitaryTopology

abbrev RankThreeCone (κ : Type*) [Fintype κ] :=
  {W : Matrix (Fin 3) κ ℝ // W.rank ≤ 1}

def rankThreeZero {κ : Type*} [Fintype κ] : RankThreeCone κ := ⟨0, by simp⟩

def quaternionContraction {r : ℕ} (W : Matrix (Fin 3) (Fin r × Fin 4) ℝ) :
    Fin r × Fin 4 → ℝ := fun j =>
  ![W 0 (j.1, 0) - W 1 (j.1, 1) - W 2 (j.1, 2),
    W 0 (j.1, 1) + W 1 (j.1, 0) + W 2 (j.1, 3),
    W 0 (j.1, 2) - W 1 (j.1, 3) + W 2 (j.1, 0),
    W 0 (j.1, 3) + W 1 (j.1, 2) - W 2 (j.1, 1)] j.2

theorem continuous_quaternionContraction (r : ℕ) :
    Continuous (@quaternionContraction r) := by
  apply continuous_pi; rintro ⟨j, a⟩
  fin_cases a <;> simp [quaternionContraction] <;> fun_prop

theorem quaternionContraction_preserves_square {r : ℕ}
    (W : RankThreeCone (Fin r × Fin 4)) :
    vectorSq (quaternionContraction W.val) = frobSq W.val := by
  obtain ⟨u, hu, z, hz⟩ := exists_sphereOuter_of_rank_le_one W.val W.property
  rw [← hz, frobSq_outer_unitSq hu.unitSq]
  simp only [vectorSq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h_sq : (∑ a : Fin 4, quaternionContraction (outer u z) (j, a) ^ 2) =
      (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) * (∑ a : Fin 4, z (j, a) ^ 2) := by
    norm_num [quaternionContraction, outer, Fin.sum_univ_succ,
      show (2 : Fin 3).succ = (3 : Fin 4) from rfl]; ring
  rw [h_sq, hu, one_mul]

def firstRowSection {κ : Type*} [Fintype κ] [DecidableEq κ] (z : κ → ℝ) :
    RankThreeCone κ :=
  ⟨outer (fun i => if i = 0 then 1 else 0) z, rank_outer_le_one _ _⟩

theorem continuous_firstRowSection {κ : Type*} [Fintype κ] [DecidableEq κ] :
    Continuous (@firstRowSection κ _ _) := by
  apply Continuous.subtype_mk; unfold outer; fun_prop

@[simp] theorem firstRowSection_zero {κ : Type*} [Fintype κ] [DecidableEq κ] :
    firstRowSection (0 : κ → ℝ) = rankThreeZero := by
  ext i j; simp [firstRowSection, outer, rankThreeZero]

@[simp] theorem quaternionContraction_section {r : ℕ} (z : Fin r × Fin 4 → ℝ) :
    quaternionContraction (firstRowSection z).val = z := by
  funext ⟨j, a⟩
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  fin_cases a <;> norm_num [quaternionContraction, firstRowSection, outer, h20]

theorem quaternionContraction_zero_iff {r : ℕ} (W : RankThreeCone (Fin r × Fin 4)) :
    quaternionContraction W.val = 0 ↔ W = rankThreeZero := by
  refine ⟨fun he => ?_, ?_⟩
  · have hs := quaternionContraction_preserves_square W
    rw [he] at hs
    exact Subtype.ext ((frobSq_eq_zero_iff W.val).mp (by simpa [vectorSq] using hs.symm))
  · rintro rfl; funext ⟨j, a⟩; fin_cases a <;> norm_num [quaternionContraction, rankThreeZero]

theorem rankThreeProduct_not_euclidean_blocks (e r : ℕ) (hr : 0 < r) :
    ¬ EuclideanAt ((0, rankThreeZero) : (Fin e → ℝ) × RankThreeCone (Fin r × Fin 4)) := by
  apply not_euclidean_of_retract_regular_charts
    (productIsolatedRetract rankThreeZero firstRowSection (fun W => quaternionContraction W.val)
      continuous_firstRowSection ((continuous_quaternionContraction r).comp continuous_subtype_val)
      quaternionContraction_section firstRowSection_zero quaternionContraction_zero_iff
      e (e + r * 4) (by simp))
    (Fintype.card (Fin e) + Fintype.card (Fin r × Fin 4) + 2) (by simp)
  intro U hU h0
  let j : Fin r × Fin 4 := (⟨0, hr⟩, 0)
  obtain ⟨p, hp, hpc⟩ := exists_regular_in_openN (ι := Fin e) 2 j U hU h0
  exact ⟨pivotProductChartN (ι := Fin e) 2 j, p, hp, hpc⟩

def blockUTuplePartialChart {ι : Type*} [Finite ι] {n : ℕ}
    (a : ι → FullUnitary n) :
    OpenPartialHomeomorph (ι → FullUnitary n) (ι → FullSkewModel n) :=
  OpenPartialHomeomorph.pi (fun i => blockPartialChart (a i))

def euclideanConeCoordinates (n d r : ℕ) (f : Fin d ≃ Fin r × Fin 4) :
    ((Fin n → ℝ) × ConeCoordinates d) ≃ₜ ((Fin (n + d) → ℝ) × RankThreeCone (Fin r × Fin 4)) :=
  (Homeomorph.prodAssoc _ _ _).symm.trans
    ((sumCoordinates.trans (reindexReal finSumFinEquiv)).prodCongr (reindexRankConeN 2 f))

def unitaryFamilyBase {q : ℕ} (Q : FullUnitary q) (o : Fin q) :
    GS.UnitaryNonmanifold.localFamily q :=
  ⟨scalarBlockBase Q.val, scalarBlockBase_mem_localFamily Q.val Q.property.2 o⟩

theorem unitary_gs_not_euclidean_at {q : ℕ} (hq : 3 ≤ q) (hodd : Odd q)
    (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o) :
    ¬ EuclideanAtSubset (GS.UnitaryNonmanifold.localFamily q) (scalarBlockBase Q.val) := by
  let ψ := euclideanDephasedParametrization Q o hQ
  let U := euclideanDephasedDomain Q o hQ
  let d := (q - 1) ^ 2
  obtain ⟨r, hr, hargs⟩ := exists_parameterBox_in_chart U
    (euclideanDephasedDomain_open Q o hQ) (zero_mem_euclideanDephasedDomain Q o hQ)
  have hsub := fullCompactImage_subset_localFamily ψ o U
    (fun x _ => dephasedParametrization_unitary Q o hQ x) r hargs
  obtain ⟨W, hW, hbaseW, hcoverW⟩ := exists_open_full_compact_coverage Q o hQ r hr
  have hcover : fullCompactSource (GS.UnitaryNonmanifold.localFamily q) ψ o r ∈
      𝓝 (unitaryFamilyBase Q o) :=
    Filter.mem_of_superset ((hW.preimage continuous_subtype_val).mem_nhds hbaseW)
      fun M hM => hcoverW M.val M.property hM
  obtain ⟨g⟩ := full_compact_pointed_neighbourhood_model
    (GS.UnitaryNonmanifold.localFamily q) (unitaryFamilyBase Q o) Q.val o ψ U
    (euclideanDephasedParametrization_continuousOn Q o hQ)
    (euclideanDephasedParametrization_injectiveOn Q o hQ)
    (fun _ hy => (dephased_constraints_iff Q.val _ o).mp
      (dephasedParametrization_constraints Q o hQ _ hy))
    r hr hargs hsub hcover (fullParameterZero q d o r)
    (by simp [ψ, d, unitaryFamilyBase]) (parameterCone_zero d)
  let a := identityOuter q o
  obtain ⟨k, hk⟩ := hodd
  have hk_pos : 0 < k := by omega
  have hr_pos : 0 < k ^ 2 := by positivity
  have hd_eq : d = k ^ 2 * 4 := by dsimp [d]; rw [show q - 1 = 2 * k by omega]; ring
  let e_col : Fin d ≃ Fin (k ^ 2) × Fin 4 := (finCongr hd_eq).trans finProdFinEquiv.symm
  let E := (Fin q → FullSkewModel 2) × ({j : Fin q // j ≠ o} → FullSkewModel 2)
  let n := Module.finrank ℝ E
  let e : E ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [n])
  let c := (((blockUTuplePartialChart a.1).prod (blockUTuplePartialChart a.2)).trans
    e.toHomeomorph.toOpenPartialHomeomorph).prod (OpenPartialHomeomorph.refl (ConeCoordinates d))
  have hx : (a, coneCoordinatesZero d) ∈ c.source :=
    ⟨⟨⟨fun i _ => base_mem_chartSource (a.1 i), fun j _ => base_mem_chartSource (a.2 j)⟩, trivial⟩, trivial⟩
  let gm : PointedOpenModel (OuterFactors q o × ConeCoordinates d) ((Fin n → ℝ) × ConeCoordinates d)
      (a, coneCoordinatesZero d) (c (a, coneCoordinatesZero d)) :=
    { source := c.source, target := c.target, source_open := c.open_source, target_open := c.open_target,
      source_point := hx, target_point := c.map_source hx, chart := c.toHomeomorphSourceTarget,
      map_point := fun _ => rfl }
  have hc0 : c (a, coneCoordinatesZero d) = (0, coneCoordinatesZero d) := by
    refine Prod.ext ?_ rfl
    change e (fun i => chartMap (a.1 i) (a.1 i).val, fun j => chartMap (a.2 j) (a.2 j).val) = 0
    simp only [chartMap_base]; exact map_zero e
  intro he
  have hf := (euclideanAtSubset_iff (GS.UnitaryNonmanifold.localFamily q)
    (scalarBlockBase Q.val) (unitaryFamilyBase Q o).property).mp he
  have h1 := (euclideanAt_pointedOpenModel (pointedOpenModel g)).mp hf
  have h2 := hc0 ▸ (euclideanAt_pointedOpenModel gm).mp h1
  have h3 := euclideanAt_of_homeomorph (euclideanConeCoordinates n d (k ^ 2) e_col)
    (0, coneCoordinatesZero d) h2
  apply rankThreeProduct_not_euclidean_blocks (n + d) (k ^ 2) hr_pos
  convert h3 using 1
  apply Prod.ext
  · funext i
    change 0 = Sum.elim (0 : Fin n → ℝ) (0 : Fin d → ℝ) (finSumFinEquiv.symm i)
    cases finSumFinEquiv.symm i <;> rfl
  · ext i j; rfl

def unitaryReflection (q : ℕ) (hq : 3 ≤ q) : FullUnitary q :=
  fullUnitary (ofRealMatrix (GS.Results.reflectionBase q))
    (ofRealMatrix_unitary (GS.Results.reflectionBase_orthogonal q (by omega)))

theorem exists_unitary_nonEuclidean_point (q : ℕ) (hq : 3 ≤ q) (hodd : Odd q) :
    ∃ M : CMat (q * 2), M ∈ GS.UnitaryNonmanifold.localFamily q ∧
      ¬ EuclideanAtSubset (GS.UnitaryNonmanifold.localFamily q) M := by
  let o : Fin q := ⟨0, by omega⟩
  have hne (i j : Fin q) : (unitaryReflection q hq).val i j ≠ 0 := by
    change (GS.Results.reflectionBase q i j : ℂ) ≠ 0
    exact_mod_cast GS.Results.reflectionBase_entries_ne_zero q hq i j
  exact ⟨scalarBlockBase (unitaryReflection q hq).val,
    (unitaryFamilyBase (unitaryReflection q hq) o).property,
    unitary_gs_not_euclidean_at hq hodd (unitaryReflection q hq) o
      ⟨fun i => ⟨hne i o, hne i o⟩, fun j => ⟨hne o j, hne o j⟩⟩⟩

end GS.UnitaryTopology
