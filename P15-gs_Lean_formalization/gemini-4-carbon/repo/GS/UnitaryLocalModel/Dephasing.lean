module

public import GS.UnitaryNonmanifold.ScalarBridge
public import GS.UnitaryManifold.LocalProduct
public import GS.UnitaryManifold.Dimension
public import Mathlib.Analysis.Calculus.Implicit
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold GS.UnitaryNonmanifold Set
open scoped Topology

namespace GS.UnitaryLocalModel
variable {q : ℕ}

def phase (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

theorem norm_phase {z : ℂ} (hz : z ≠ 0) : ‖phase z‖ = 1 := by
  simp [phase, norm_div, Complex.norm_real, abs_of_nonneg (norm_nonneg z), hz]

theorem conj_phase_mul_phase {z : ℂ} (hz : z ≠ 0) : star (phase z) * phase z = 1 := by
  change (starRingEnd ℂ) (phase z) * phase z = 1
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, norm_phase hz]; norm_num

theorem conj_phase_mul (z : ℂ) : star (phase z) * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [hz, phase]
  · have hn : (‖z‖ : ℂ) * phase z = z := mul_div_cancel₀ z (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))
    calc star (phase z) * z = star (phase z) * ((‖z‖ : ℂ) * phase z) := congrArg (star (phase z) * ·) hn.symm
      _ = (‖z‖ : ℂ) * (star (phase z) * phase z) := by ring
      _ = (‖z‖ : ℂ) := by rw [conj_phase_mul_phase hz, mul_one]

def AnchorNonzero (Q A : CMat q) (o : Fin q) : Prop :=
  (∀ i, Q i o ≠ 0 ∧ A i o ≠ 0) ∧ (∀ j, Q o j ≠ 0 ∧ A o j ≠ 0)

def rowPhase (Q A : CMat q) (o i : Fin q) : ℂ := phase (A i o / Q i o)
def colPhase (Q A : CMat q) (o j : Fin q) : ℂ := phase (A o j / Q o j)

def dephase (Q A : CMat q) (o : Fin q) : CMat q := fun i j =>
  star (rowPhase Q A o i) * A i j * star (colPhase Q A o j) * rowPhase Q A o o

theorem diagonal_unitary_of_norm_one {n : ℕ} (u : Fin n → ℂ) (hu : ∀ i, ‖u i‖ = 1) :
    GS.Unitary (Matrix.diagonal u) := by
  have h : (Matrix.diagonal u)ᴴ * Matrix.diagonal u = 1 := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    ext i j; by_cases hij : i = j
    · subst hij; simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      change (starRingEnd ℂ) (u i) * u i = 1
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hu i]; norm_num
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply, hij]
  exact ⟨h, mul_eq_one_comm.mp h⟩

theorem dephase_unitary {Q A : CMat q} {o : Fin q} (hA : GS.Unitary A) (ha : AnchorNonzero Q A o) :
    GS.Unitary (dephase Q A o) := by
  have hr (i) : ‖rowPhase Q A o i‖ = 1 := norm_phase (div_ne_zero (ha.1 i).2 (ha.1 i).1)
  have hc (j) : ‖colPhase Q A o j‖ = 1 := norm_phase (div_ne_zero (ha.2 j).2 (ha.2 j).1)
  rw [show dephase Q A o = Matrix.diagonal (fun i => star (rowPhase Q A o i)) * A *
        Matrix.diagonal (fun j => star (colPhase Q A o j) * rowPhase Q A o o) by
        ext i j; simp [dephase, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_assoc]]
  exact ((diagonal_unitary_of_norm_one _ fun i => by simpa using hr i).mul hA).mul
    (diagonal_unitary_of_norm_one _ fun j => by rw [norm_mul, norm_star, hc j, hr o, mul_one])

theorem dephase_anchor_column_positive {Q A : CMat q} {o : Fin q} (ha : AnchorNonzero Q A o) (i : Fin q) :
    ∃ r : ℝ, 0 < r ∧ dephase Q A o i o / Q i o = r := by
  refine ⟨‖A i o / Q i o‖, norm_pos_iff.mpr (div_ne_zero (ha.1 i).2 (ha.1 i).1), ?_⟩
  calc dephase Q A o i o / Q i o
    _ = (star (rowPhase Q A o i) * (A i o / Q i o)) * (star (phase (A o o / Q o o)) * phase (A o o / Q o o)) := by
      simp only [dephase, rowPhase, colPhase]; ring
    _ = (‖A i o / Q i o‖ : ℂ) := by rw [conj_phase_mul_phase (div_ne_zero (ha.1 o).2 (ha.1 o).1), mul_one]; exact conj_phase_mul _

theorem dephase_anchor_row_positive {Q A : CMat q} {o : Fin q} (ha : AnchorNonzero Q A o) (j : Fin q) :
    ∃ r : ℝ, 0 < r ∧ dephase Q A o o j / Q o j = r := by
  refine ⟨‖A o j / Q o j‖, norm_pos_iff.mpr (div_ne_zero (ha.2 j).2 (ha.2 j).1), ?_⟩
  calc dephase Q A o o j / Q o j
    _ = (star (colPhase Q A o j) * (A o j / Q o j)) * (star (phase (A o o / Q o o)) * phase (A o o / Q o o)) := by
      simp only [dephase, rowPhase, colPhase]; ring
    _ = (‖A o j / Q o j‖ : ℂ) := by rw [conj_phase_mul_phase (div_ne_zero (ha.1 o).2 (ha.1 o).1), mul_one]; exact conj_phase_mul _

def rowPhaseDiagonal (Q A B : CMat q) (o i : Fin q) : CMat 2 := Matrix.diagonal ![rowPhase Q A o i, rowPhase Q B o i]
def colPhaseDiagonal (Q A B : CMat q) (o j : Fin q) : CMat 2 := Matrix.diagonal ![colPhase Q A o j, colPhase Q B o j]

theorem rowPhaseDiagonal_unitary {Q A B : CMat q} {o : Fin q}
    (ha : AnchorNonzero Q A o) (hb : AnchorNonzero Q B o) (i : Fin q) :
    GS.Unitary (rowPhaseDiagonal Q A B o i) :=
  diagonal_unitary_of_norm_one _ fun k => by
    fin_cases k
    · exact norm_phase (div_ne_zero (ha.1 i).2 (ha.1 i).1)
    · exact norm_phase (div_ne_zero (hb.1 i).2 (hb.1 i).1)

theorem colPhaseDiagonal_unitary {Q A B : CMat q} {o : Fin q}
    (ha : AnchorNonzero Q A o) (hb : AnchorNonzero Q B o) (j : Fin q) :
    GS.Unitary (colPhaseDiagonal Q A B o j) :=
  diagonal_unitary_of_norm_one _ fun k => by
    fin_cases k
    · exact norm_phase (div_ne_zero (ha.2 j).2 (ha.2 j).1)
    · exact norm_phase (div_ne_zero (hb.2 j).2 (hb.2 j).1)

def phaseGaugeLeft (U V : Fin q → CMat 2) (Q A B : CMat q) (o i : Fin q) : CMat 2 :=
  U i * rowPhaseDiagonal Q A B o i * V o

def phaseGaugeRight (V : Fin q → CMat 2) (Q A B : CMat q) (o j : Fin q) : CMat 2 :=
  (V o)ᴴ * (rowPhaseDiagonal Q A B o o)ᴴ * colPhaseDiagonal Q A B o j * V j

theorem phaseGaugeLeft_unitary (U V : Fin q → CMat 2) (Q A B : CMat q) (o : Fin q)
    (hU : ∀ i, GS.Unitary (U i)) (hV : ∀ j, GS.Unitary (V j))
    (ha : AnchorNonzero Q A o) (hb : AnchorNonzero Q B o) (i : Fin q) :
    GS.Unitary (phaseGaugeLeft U V Q A B o i) :=
  ((hU i).mul (rowPhaseDiagonal_unitary ha hb i)).mul (hV o)

theorem phaseGaugeRight_unitary (V : Fin q → CMat 2) (Q A B : CMat q) (o : Fin q)
    (hV : ∀ j, GS.Unitary (V j)) (ha : AnchorNonzero Q A o) (hb : AnchorNonzero Q B o) (j : Fin q) :
    GS.Unitary (phaseGaugeRight V Q A B o j) :=
  ((((hV o).conjTranspose).mul (rowPhaseDiagonal_unitary ha hb o).conjTranspose).mul
    (colPhaseDiagonal_unitary ha hb j)).mul (hV j)

theorem phaseGaugeRight_anchor (V : Fin q → CMat 2) (Q A B : CMat q) (o : Fin q)
    (hV : GS.Unitary (V o)) (ha : AnchorNonzero Q A o) (hb : AnchorNonzero Q B o) :
    phaseGaugeRight V Q A B o o = 1 := by
  unfold phaseGaugeRight
  change (V o)ᴴ * (rowPhaseDiagonal Q A B o o)ᴴ * rowPhaseDiagonal Q A B o o * V o = 1
  rw [Matrix.mul_assoc (V o)ᴴ, (rowPhaseDiagonal_unitary ha hb o).1, Matrix.mul_one, hV.1]

theorem phase_normalization_block (U V : Fin q → CMat 2) (Q A B : CMat q)
    (o i j : Fin q) (hU : GS.Unitary (U i)) (hV : GS.Unitary (V j)) :
    (phaseGaugeLeft U V Q A B o i)ᴴ * (U i * diagTwo (A i j) (B i j) * V j) *
      (phaseGaugeRight V Q A B o j)ᴴ =
    (V o)ᴴ * diagTwo (dephase Q A o i j) (dephase Q B o i j) * V o := by
  unfold phaseGaugeLeft phaseGaugeRight
  have hc : (U i * rowPhaseDiagonal Q A B o i * V o)ᴴ * (U i * diagTwo (A i j) (B i j) * V j) *
      ((V o)ᴴ * (rowPhaseDiagonal Q A B o o)ᴴ * colPhaseDiagonal Q A B o j * V j)ᴴ =
      (V o)ᴴ * ((rowPhaseDiagonal Q A B o i)ᴴ * diagTwo (A i j) (B i j) *
        (colPhaseDiagonal Q A B o j)ᴴ * rowPhaseDiagonal Q A B o o) * V o := by
    calc _ = (V o)ᴴ * (rowPhaseDiagonal Q A B o i)ᴴ * ((U i)ᴴ * U i) * diagTwo (A i j) (B i j) *
            (V j * (V j)ᴴ) * (colPhaseDiagonal Q A B o j)ᴴ * rowPhaseDiagonal Q A B o o * V o := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = _ := by rw [hU.1, hV.2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hc]; congr 2; ext a b; fin_cases a <;> fin_cases b <;>
    simp [rowPhaseDiagonal, colPhaseDiagonal, diagTwo, dephase, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]

theorem base_fibre_anchor_and_dephase (U V : Fin q → CMat 2) (Q A B : CMat q) (o : Fin q)
    (hU : ∀ i, GS.Unitary (U i)) (hV : ∀ j, GS.Unitary (V j))
    (hQc : ∀ i, Q i o ≠ 0) (hQr : ∀ j, Q o j ≠ 0)
    (he : ∀ i j, U i * diagTwo (A i j) (B i j) * V j = Q i j • (1 : CMat 2)) :
    (AnchorNonzero Q A o ∧ AnchorNonzero Q B o) ∧ dephase Q A o = Q ∧ dephase Q B o = Q := by
  have hsw {X Y : CMat 2} {a b c : ℂ} (hX : GS.Unitary X) (hY : GS.Unitary Y) (hc : c ≠ 0)
      (h : X * diagTwo a b * Y = c • (1 : CMat 2)) :
      (a ≠ 0 ∧ b ≠ 0) ∧ X * diagTwo (phase (a / c)) (phase (b / c)) * Y = 1 := by
    have hd : X * diagTwo (a / c) (b / c) * Y = 1 := by
      rw [show diagTwo (a / c) (b / c) = c⁻¹ • diagTwo a b by
            ext i j; fin_cases i <;> fin_cases j <;> simp [diagTwo, div_eq_mul_inv, mul_comm],
          Matrix.mul_smul, Matrix.smul_mul, h, smul_smul]; simp [hc]
    have hu : GS.Unitary (diagTwo (a / c) (b / c)) := by
      have heq : diagTwo (a / c) (b / c) = Xᴴ * Yᴴ := by
        calc _ = Xᴴ * (X * diagTwo (a / c) (b / c) * Y) * Yᴴ := by
              simp only [← Matrix.mul_assoc, hX.1, Matrix.one_mul]; rw [Matrix.mul_assoc, hY.2, Matrix.mul_one]
          _ = _ := by rw [hd, Matrix.mul_one]
      exact heq ▸ hX.conjTranspose.mul hY.conjTranspose
    have hna : ‖a / c‖ = 1 := by
      have h0 : star (a / c) * (a / c) = 1 := by
        simpa [diagTwo, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] using congrFun (congrFun hu.1 0) 0
      have hn := congrArg norm h0; simp only [norm_mul, norm_star, norm_one] at hn; nlinarith [norm_nonneg (a / c)]
    have hnb : ‖b / c‖ = 1 := by
      have h1 : star (b / c) * (b / c) = 1 := by
        simpa [diagTwo, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] using congrFun (congrFun hu.1 1) 1
      have hn := congrArg norm h1; simp only [norm_mul, norm_star, norm_one] at hn; nlinarith [norm_nonneg (b / c)]
    refine ⟨⟨fun ha0 => by simp [ha0] at hna, fun hb0 => by simp [hb0] at hnb⟩, ?_⟩
    rw [show phase (a / c) = a / c by simp only [phase, hna, Complex.ofReal_one, div_one],
        show phase (b / c) = b / c by simp only [phase, hnb, Complex.ofReal_one, div_one]]
    exact hd
  have hcol (i) := hsw (hU i) (hV o) (hQc i) (he i o)
  have hrow (j) := hsw (hU o) (hV j) (hQr j) (he o j)
  have hl (i) : phaseGaugeLeft U V Q A B o i = 1 := (hcol i).2
  have hr (j) : phaseGaugeRight V Q A B o j = 1 := by
    have ha : phaseGaugeRight V Q A B o j = (phaseGaugeLeft U V Q A B o o)ᴴ * (U o * colPhaseDiagonal Q A B o j * V j) := by
      unfold phaseGaugeLeft phaseGaugeRight; simp only [Matrix.conjTranspose_mul]
      calc _ = (V o)ᴴ * (rowPhaseDiagonal Q A B o o)ᴴ * ((U o)ᴴ * U o) * colPhaseDiagonal Q A B o j * V j := by
            rw [(hU o).1, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [ha, hl o, Matrix.conjTranspose_one, Matrix.one_mul]; exact (hrow j).2
  have hd (i j) : diagTwo (dephase Q A o i j) (dephase Q B o i j) = Q i j • (1 : CMat 2) := by
    have hn := phase_normalization_block U V Q A B o i j (hU i) (hV j)
    rw [hl i, hr j, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, he i j] at hn
    calc _ = V o * ((V o)ᴴ * diagTwo (dephase Q A o i j) (dephase Q B o i j) * V o) * (V o)ᴴ := by
          simp only [← Matrix.mul_assoc, (hV o).2, Matrix.one_mul]; rw [Matrix.mul_assoc, (hV o).2, Matrix.mul_one]
      _ = _ := by rw [← hn, Matrix.mul_smul, Matrix.smul_mul]; simp [(hV o).2]
  exact ⟨⟨⟨fun i => ⟨hQc i, (hcol i).1.1⟩, fun j => ⟨hQr j, (hrow j).1.1⟩⟩,
          ⟨fun i => ⟨hQc i, (hcol i).1.2⟩, fun j => ⟨hQr j, (hrow j).1.2⟩⟩⟩,
         Matrix.ext fun i j => by simpa [diagTwo] using congrFun (congrFun (hd i j) 0) 0,
         Matrix.ext fun i j => by simpa [diagTwo] using congrFun (congrFun (hd i j) 1) 1⟩

theorem isOpen_anchorNonzero (Q : CMat q) (o : Fin q) : IsOpen {A : CMat q | AnchorNonzero Q A o} := by
  unfold AnchorNonzero
  refine IsOpen.and ?_ ?_ <;> simp only [Set.setOf_forall] <;> apply isOpen_iInter_of_finite <;> intro i
  · exact isOpen_const.and (isOpen_ne_fun (by fun_prop) continuous_const)
  · exact isOpen_const.and (isOpen_ne_fun (by fun_prop) continuous_const)

theorem continuousAt_dephase {Q A : CMat q} {o : Fin q} (ha : AnchorNonzero Q A o) :
    ContinuousAt (fun M : CMat q => dephase Q M o) A := by
  have hph {z : ℂ} (hz : z ≠ 0) : ContinuousAt phase z :=
    continuousAt_id.div (Complex.continuous_ofReal.continuousAt.comp continuous_norm.continuousAt)
      (by exact_mod_cast norm_ne_zero_iff.mpr hz)
  have hrp (i) : ContinuousAt (fun M : CMat q => rowPhase Q M o i) A :=
    ContinuousAt.comp (f := fun M : CMat q => M i o / Q i o) (hph (div_ne_zero (ha.1 i).2 (ha.1 i).1))
      ((show Continuous fun M : CMat q => M i o by fun_prop).continuousAt.div_const _)
  have hcp (j) : ContinuousAt (fun M : CMat q => colPhase Q M o j) A :=
    ContinuousAt.comp (f := fun M : CMat q => M o j / Q o j) (hph (div_ne_zero (ha.2 j).2 (ha.2 j).1))
      ((show Continuous fun M : CMat q => M o j by fun_prop).continuousAt.div_const _)
  refine continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j => ?_
  exact (((hrp i).star.mul (continuous_apply_apply i j).continuousAt).mul (hcp j).star).mul (hrp o)

abbrev FullUnitary (q : ℕ) := BlockU (fun _ : Fin q => 0)
abbrev FullSkewModel (q : ℕ) := Model (fun _ : Fin q => 0)
abbrev AnchorCoordinates (o : Fin q) := (Fin q → ℝ) × ({j : Fin q // j ≠ o} → ℝ)

def fullUnitary (Q : CMat q) (hQ : Unitary Q) : FullUnitary q :=
  ⟨Q, fun _ _ hij => (hij rfl).elim, hQ⟩

def anchorImag (Q : CMat q) (o : Fin q) : CMat q →L[ℝ] AnchorCoordinates o :=
  ({ toFun := fun A => (fun i => (A i o / Q i o).im, fun j => (A o j.val / Q o j.val).im)
     map_add' := fun A B => by apply Prod.ext <;> funext i <;> simp [add_div, Complex.add_im]
     map_smul' := fun r A => by apply Prod.ext <;> funext i <;> simp [Complex.real_smul, mul_div_assoc, Complex.mul_im]
   } : CMat q →ₗ[ℝ] AnchorCoordinates o).toContinuousLinearMap

def anchorConstraints (Q : FullUnitary q) (o : Fin q) (x : FullSkewModel q) : AnchorCoordinates o :=
  anchorImag Q.val o (chartInv Q x)

def anchorDerivative (Q : FullUnitary q) (o : Fin q) : FullSkewModel q →L[ℝ] AnchorCoordinates o :=
  (anchorImag Q.val o).comp (fderiv ℝ (chartInv Q) 0)

theorem anchorConstraints_hasStrictFDerivAt (Q : FullUnitary q) (o : Fin q) :
    HasStrictFDerivAt (anchorConstraints Q o) (anchorDerivative Q o) 0 :=
  (((anchorImag Q.val o).contDiff.comp (chartInv_smooth Q)).contDiffAt).hasStrictFDerivAt'
    (((anchorImag Q.val o).hasFDerivAt).comp 0 (((chartInv_smooth Q).differentiable (by simp) 0).hasFDerivAt)) (by simp)

theorem anchorDerivative_range (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o) :
    LinearMap.range (anchorDerivative Q o : FullSkewModel q →ₗ[ℝ] AnchorCoordinates o) = ⊤ := by
  refine LinearMap.range_eq_top.mpr fun ⟨a, b⟩ => ?_
  let β : Fin q → ℝ := fun j => if hj : j = o then 0 else b ⟨j, hj⟩ - a o
  let pd (v : Fin q → ℝ) : CMat q := Matrix.diagonal fun i => (v i : ℂ) * Complex.I
  have hpd (v) : IsSkewHermitian (pd v) := by
    unfold IsSkewHermitian pd; rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_neg]
    exact congrArg Matrix.diagonal (funext fun i => by simp)
  let x : FullSkewModel q :=
    ⟨(-1 / 2 : ℝ) • (Q.valᴴ * pd a * Q.val + pd β), fun _ _ hij => (hij rfl).elim,
      skewHermitian_real_smul _ (skewHermitian_add
        (by simpa using conjugate_skewHermitian Q.valᴴ (pd a) (hpd a)) (hpd β))⟩
  refine ⟨x, ?_⟩
  change anchorImag Q.val o (fderiv ℝ (chartInv Q) 0 x) = (a, b)
  have hv : fderiv ℝ (chartInv Q) 0 x = pd a * Q.val + Q.val * pd β := by
    rw [chartInv_fderiv_zero]
    change (-2 : ℝ) • (Q.val * ((-1 / 2 : ℝ) • (Q.valᴴ * pd a * Q.val + pd β))) = _
    rw [Matrix.mul_smul, smul_smul]; norm_num; rw [Matrix.mul_add]; congr 1
    simp only [← Matrix.mul_assoc, Q.property.2.2, Matrix.one_mul]
  rw [hv]; apply Prod.ext
  · funext i
    change (((pd a * Q.val + Q.val * pd β) i o) / Q.val i o).im = a i
    simp only [Matrix.add_apply, pd, Matrix.diagonal_mul, Matrix.mul_diagonal, β, ↓reduceDIte,
      Complex.ofReal_zero, zero_mul, mul_zero, add_zero]
    rw [mul_div_cancel_right₀ _ (hQ.1 i).1]; simp
  · funext j
    change (((pd a * Q.val + Q.val * pd β) o j.val) / Q.val o j.val).im = b j
    simp only [Matrix.add_apply, pd, Matrix.diagonal_mul, Matrix.mul_diagonal, β, dif_neg j.property]
    rw [add_div, mul_div_cancel_right₀ _ (hQ.2 j.val).1, mul_div_cancel_left₀ _ (hQ.2 j.val).1]
    simp

def AnchorPositive (Q A : CMat q) (o : Fin q) : Prop :=
  (∀ i, 0 < (A i o / Q i o).re) ∧ (∀ j, 0 < (A o j / Q o j).re)

theorem anchorPositive_open (Q : CMat q) (o : Fin q) : IsOpen {A : CMat q | AnchorPositive Q A o} := by
  have hc (i) : IsOpen {A : CMat q | 0 < (A i o / Q i o).re} :=
    isOpen_lt continuous_const ((Complex.continuous_re).comp (((continuous_apply o).comp (continuous_apply i)).div_const _))
  have hr (j) : IsOpen {A : CMat q | 0 < (A o j / Q o j).re} :=
    isOpen_lt continuous_const ((Complex.continuous_re).comp (((continuous_apply j).comp (continuous_apply o)).div_const _))
  convert (isOpen_iInter_of_finite hc).inter (isOpen_iInter_of_finite hr) using 1
  ext A; simp [AnchorPositive]

theorem anchorPositive_self (Q : CMat q) (o : Fin q) (hQ : AnchorNonzero Q Q o) : AnchorPositive Q Q o :=
  ⟨fun i => by simp [div_self (hQ.1 i).1], fun j => by simp [div_self (hQ.2 j).1]⟩

theorem dephased_constraints_iff (Q A : CMat q) (o : Fin q) :
    anchorImag Q o A = 0 ∧ AnchorPositive Q A o ↔
      (∀ i, ∃ r : ℝ, 0 < r ∧ A i o / Q i o = r) ∧ (∀ j, ∃ r : ℝ, 0 < r ∧ A o j / Q o j = r) := by
  have hpr (z : ℂ) : (∃ r : ℝ, 0 < r ∧ z = r) ↔ z.im = 0 ∧ 0 < z.re :=
    ⟨fun ⟨r, hr, h⟩ => by subst h; exact ⟨rfl, hr⟩, fun ⟨hi, hr⟩ => ⟨z.re, hr, Complex.ext rfl hi⟩⟩
  have hai : anchorImag Q o A = 0 ↔ (∀ i, (A i o / Q i o).im = 0) ∧ (∀ j, (A o j / Q o j).im = 0) :=
    ⟨fun h => ⟨fun i => congrArg (fun p : AnchorCoordinates o => p.1 i) h,
       fun j => if hj : j = o then hj ▸ congrArg (fun p : AnchorCoordinates o => p.1 o) h
                else congrArg (fun p : AnchorCoordinates o => p.2 ⟨j, hj⟩) h⟩,
     fun ⟨hc, hr⟩ => Prod.ext (funext hc) (funext fun j => hr j.val)⟩
  rw [hai]
  exact ⟨fun ⟨⟨hic, hir⟩, hpc, hpr'⟩ => ⟨fun i => (hpr _).mpr ⟨hic i, hpc i⟩, fun j => (hpr _).mpr ⟨hir j, hpr' j⟩⟩,
    fun ⟨hc, hr⟩ => ⟨⟨fun i => ((hpr _).mp (hc i)).1, fun j => ((hpr _).mp (hr j)).1⟩,
      fun i => ((hpr _).mp (hc i)).2, fun j => ((hpr _).mp (hr j)).2⟩⟩

abbrev DephasedUnitary (Q : FullUnitary q) (o : Fin q) :=
  {A : FullUnitary q // anchorImag Q.val o A.val = 0 ∧ AnchorPositive Q.val A.val o}

abbrev DephasedModel (Q : FullUnitary q) (o : Fin q) :=
  ↥(LinearMap.ker (anchorDerivative Q o : FullSkewModel q →ₗ[ℝ] AnchorCoordinates o))

def constraintChart (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o) :
    OpenPartialHomeomorph (FullSkewModel q) (AnchorCoordinates o × DephasedModel Q o) :=
  (anchorConstraints_hasStrictFDerivAt Q o).implicitToOpenPartialHomeomorph
    (anchorConstraints Q o) (anchorDerivative Q o) (anchorDerivative_range Q o hQ)

def unitaryConstraintChart (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o) :
    OpenPartialHomeomorph (FullUnitary q) (AnchorCoordinates o × DephasedModel Q o) :=
  ((blockPartialChart Q).trans (constraintChart Q o hQ)).restrOpen
    {A | AnchorPositive Q.val A.val o} ((anchorPositive_open Q.val o).preimage continuous_subtype_val)

theorem base_mem_unitaryConstraintChart_source (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : Q ∈ (unitaryConstraintChart Q o hQ).source :=
  ⟨⟨base_mem_chartSource Q, by
      change chartMap Q Q.val ∈ (constraintChart Q o hQ).source; rw [chartMap_base]
      exact (anchorConstraints_hasStrictFDerivAt Q o).mem_implicitToOpenPartialHomeomorph_source (anchorDerivative_range Q o hQ)⟩,
   anchorPositive_self Q.val o hQ⟩

@[simp] theorem anchorConstraints_zero (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : anchorConstraints Q o 0 = 0 := by
  rw [anchorConstraints, chartInv_zero]
  exact Prod.ext (funext fun i => by simp [anchorImag, div_self (hQ.1 i).1])
    (funext fun j => by simp [anchorImag, div_self (hQ.2 j.val).1])

@[simp] theorem unitaryConstraintChart_base (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : unitaryConstraintChart Q o hQ Q = (0, 0) := by
  change constraintChart Q o hQ (chartMap Q Q.val) = _
  rw [chartMap_base]; unfold constraintChart
  rw [HasStrictFDerivAt.implicitToOpenPartialHomeomorph_self, anchorConstraints_zero Q o hQ]

theorem unitaryConstraintChart_fst (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o)
    (A : FullUnitary q) (hA : A ∈ (unitaryConstraintChart Q o hQ).source) :
    (unitaryConstraintChart Q o hQ A).1 = anchorImag Q.val o A.val := by
  change (constraintChart Q o hQ (chartMap Q A.val)).1 = _
  dsimp only [constraintChart]
  rw [(anchorConstraints_hasStrictFDerivAt Q o).implicitToOpenPartialHomeomorph_fst (anchorDerivative_range Q o hQ)]
  unfold anchorConstraints; rw [chartInv_chartMap Q A hA.1.1]

def dephasedChartDomain (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o) : Set (DephasedModel Q o) :=
  {y | (0, y) ∈ (unitaryConstraintChart Q o hQ).target}

def dephasedParametrization (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o)
    (y : DephasedModel Q o) : CMat q :=
  ((unitaryConstraintChart Q o hQ).symm (0, y)).val

theorem dephasedParametrization_unitary (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (y : DephasedModel Q o) :
    Unitary (dephasedParametrization Q o hQ y) :=
  ((unitaryConstraintChart Q o hQ).symm (0, y)).property.2

theorem dephasedParametrization_constraints (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (y : DephasedModel Q o) (hy : y ∈ dephasedChartDomain Q o hQ) :
    anchorImag Q.val o (dephasedParametrization Q o hQ y) = 0 ∧
      AnchorPositive Q.val (dephasedParametrization Q o hQ y) o := by
  have hs := (unitaryConstraintChart Q o hQ).map_target hy
  refine ⟨?_, hs.2⟩
  unfold dephasedParametrization
  rw [← unitaryConstraintChart_fst Q o hQ _ hs]
  exact congrArg Prod.fst ((unitaryConstraintChart Q o hQ).right_inv hy)

def dephasedBase (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o) : DephasedUnitary Q o :=
  ⟨Q, by simpa [anchorConstraints] using anchorConstraints_zero Q o hQ, anchorPositive_self Q.val o hQ⟩

def dephasedChartSource (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o) : Set (DephasedUnitary Q o) :=
  {A | A.val ∈ (unitaryConstraintChart Q o hQ).source}

theorem dephasedChartSource_open (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o) :
    IsOpen (dephasedChartSource Q o hQ) :=
  (unitaryConstraintChart Q o hQ).open_source.preimage continuous_subtype_val

def dephasedCoordinates (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o)
    (A : DephasedUnitary Q o) : DephasedModel Q o :=
  (unitaryConstraintChart Q o hQ A.val).2

theorem finrank_dephasedModel (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o) :
    Module.finrank ℝ (DephasedModel Q o) = (q - 1) ^ 2 := by
  classical
  have hac : Module.finrank ℝ (AnchorCoordinates o) = q + (q - 1) := by
    dsimp only [AnchorCoordinates]; rw [Module.finrank_prod, Module.finrank_pi, Module.finrank_pi]
    simp only [Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  have hd := LinearMap.finrank_range_add_finrank_ker
    (anchorDerivative Q o : FullSkewModel q →ₗ[ℝ] AnchorCoordinates o)
  rw [anchorDerivative_range Q o hQ, finrank_top, hac, finrank_fullModel q] at hd
  have hq : q - 1 + 1 = q := by have := o.isLt; omega
  change Module.finrank ℝ (LinearMap.ker (anchorDerivative Q o : FullSkewModel q →ₗ[ℝ] AnchorCoordinates o)) = (q - 1) ^ 2
  nlinarith

theorem nonempty_dephasedCoordinateEquiv (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o) :
    Nonempty (DephasedModel Q o ≃L[ℝ] (Fin ((q - 1) ^ 2) → ℝ)) := by
  letI : Module.Free ℝ (DephasedModel Q o) := Module.Free.of_basis (Module.Basis.ofVectorSpace ℝ (DephasedModel Q o))
  exact ⟨LinearEquiv.toContinuousLinearEquiv (𝕜 := ℝ) (E := DephasedModel Q o) (F := Fin ((q - 1) ^ 2) → ℝ)
    (Module.finBasisOfFinrankEq ℝ (DephasedModel Q o) (finrank_dephasedModel Q o hQ)).equivFun⟩

def dephasedCoordinateEquiv (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o) :
    DephasedModel Q o ≃L[ℝ] (Fin ((q - 1) ^ 2) → ℝ) :=
  Classical.choice (nonempty_dephasedCoordinateEquiv Q o hQ)

def euclideanDephasedDomain (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o) :
    Set (Fin ((q - 1) ^ 2) → ℝ) :=
  (dephasedCoordinateEquiv Q o hQ).symm ⁻¹' dephasedChartDomain Q o hQ

def euclideanDephasedParametrization (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o)
    (x : Fin ((q - 1) ^ 2) → ℝ) : CMat q :=
  dephasedParametrization Q o hQ ((dephasedCoordinateEquiv Q o hQ).symm x)

def euclideanDephasedCoordinates (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o)
    (A : DephasedUnitary Q o) : Fin ((q - 1) ^ 2) → ℝ :=
  dephasedCoordinateEquiv Q o hQ (dephasedCoordinates Q o hQ A)

theorem euclideanDephasedDomain_open (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o) :
    IsOpen (euclideanDephasedDomain Q o hQ) :=
  ((unitaryConstraintChart Q o hQ).open_target.preimage (continuous_const.prodMk continuous_id)).preimage
    (dephasedCoordinateEquiv Q o hQ).symm.continuous

theorem zero_mem_euclideanDephasedDomain (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o) :
    (0 : Fin ((q - 1) ^ 2) → ℝ) ∈ euclideanDephasedDomain Q o hQ := by
  change (0, (dephasedCoordinateEquiv Q o hQ).symm 0) ∈ (unitaryConstraintChart Q o hQ).target
  simpa [unitaryConstraintChart_base] using (unitaryConstraintChart Q o hQ).map_source (base_mem_unitaryConstraintChart_source Q o hQ)

@[simp] theorem euclideanDephasedParametrization_zero (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : euclideanDephasedParametrization Q o hQ 0 = Q.val := by
  simp only [euclideanDephasedParametrization, map_zero, dephasedParametrization]
  have h := (unitaryConstraintChart Q o hQ).left_inv (base_mem_unitaryConstraintChart_source Q o hQ)
  rw [unitaryConstraintChart_base] at h; exact congrArg Subtype.val h

theorem euclideanDephasedParametrization_continuousOn (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    ContinuousOn (euclideanDephasedParametrization Q o hQ) (euclideanDephasedDomain Q o hQ) :=
  (continuous_subtype_val.continuousOn.comp
    ((unitaryConstraintChart Q o hQ).continuousOn_symm.comp
      (continuous_const.prodMk continuous_id).continuousOn fun _ h => h)
    fun _ _ => Set.mem_univ _).comp (dephasedCoordinateEquiv Q o hQ).symm.continuous.continuousOn fun _ h => h

theorem euclideanDephasedParametrization_injectiveOn (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    Set.InjOn (euclideanDephasedParametrization Q o hQ) (euclideanDephasedDomain Q o hQ) := fun _ hx _ hy he => by
  apply (dephasedCoordinateEquiv Q o hQ).symm.injective
  have hh := congrArg (unitaryConstraintChart Q o hQ) (Subtype.ext he)
  rw [(unitaryConstraintChart Q o hQ).right_inv hx, (unitaryConstraintChart Q o hQ).right_inv hy] at hh
  exact congrArg Prod.snd hh

theorem euclideanDephasedParametrization_coordinates (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (A : DephasedUnitary Q o) (hA : A ∈ dephasedChartSource Q o hQ) :
    euclideanDephasedParametrization Q o hQ (euclideanDephasedCoordinates Q o hQ A) = A.val.val := by
  simp only [euclideanDephasedParametrization, euclideanDephasedCoordinates, ContinuousLinearEquiv.symm_apply_apply,
    dephasedParametrization]
  have hu : unitaryConstraintChart Q o hQ A.val = (0, dephasedCoordinates Q o hQ A) :=
    Prod.ext ((unitaryConstraintChart_fst Q o hQ A.val hA).trans A.property.1) rfl
  rw [← hu, (unitaryConstraintChart Q o hQ).left_inv hA]

end GS.UnitaryLocalModel
