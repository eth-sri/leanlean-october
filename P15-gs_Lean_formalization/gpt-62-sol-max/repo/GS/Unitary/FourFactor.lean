module

public import GS.M4Certificate
public import GS.Unitary.RealEmbedding
public import Mathlib.Analysis.InnerProductSpace.NormDet

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section

/-!
# Unitary four-factor insufficiency

The exact real counterexample remains a counterexample when arbitrary complex
unitary blocks are permitted. This does not follow merely from its real
nonfactorization: we prove the determinant-modulus obstruction for all complex
unitary factors, then transfer the exact real certificate through ℝ → ℂ.
-/

open Matrix
open scoped BigOperators

namespace GS.UnitaryGeometry

def product4 {n : ℕ} (B₄ P₃ B₃ P₂ B₂ P₁ B₁ : CMat n) : CMat n :=
  B₄ * P₃ * B₃ * P₂ * B₂ * P₁ * B₁

def CInA4 {n : ℕ} (b₁ b₂ b₃ b₄ : ℕ) (P₁ P₂ P₃ A : CMat n) : Prop :=
  ∃ B₁ B₂ B₃ B₄, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ CBlockDiagonal b₄ B₄ ∧
    A = product4 B₄ P₃ B₃ P₂ B₂ P₁ B₁

def CInA4Unitary {n : ℕ} (b₁ b₂ b₃ b₄ : ℕ) (P₁ P₂ P₃ A : CMat n) : Prop :=
  ∃ B₁ B₂ B₃ B₄, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ CBlockDiagonal b₄ B₄ ∧
    Unitary B₁ ∧ Unitary B₂ ∧ Unitary B₃ ∧ Unitary B₄ ∧
    A = product4 B₄ P₃ B₃ P₂ B₂ P₁ B₁

end GS.UnitaryGeometry

namespace GS.UnitaryFour
open GS.UnitaryGeometry
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

def P : CMat 6 := ofRealMatrix GS.M4.P
open GS.M4 (index minorIndex minors assemble shuffle6 core_apply coreDet core_det)
open GS.Shared (blockView blockView_apply packBlocks_apply blockView_sandwich standard_block_label
  blockView_unitary supported_blocks_iff)

theorem P_eq_perm : P = GS.Shared.permMatrix shuffle6 := by
  ext i j
  simp [P, GS.M4.P_eq_perm, ofRealMatrix, GS.Shared.permMatrix, apply_ite Complex.ofRealHom]

def DetBound (d : Fin 4 → ℝ) : Prop := d 0 * d 3 ≤ d 2 * (1 - d 1)^2

theorem norm_det_unitary {n : ℕ} (U : CMat n) (hU : Unitary U) : ‖U.det‖ = 1 :=
  CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary
    (Matrix.mem_unitaryGroup_iff'.mpr hU.1))

theorem minors_outer (A C B : CMat 6)
    (hA : CBlockDiagonal 2 A) (hB : CBlockDiagonal 2 B)
    (hoA : Unitary A) (hoB : Unitary B) :
    (fun i => ‖minors (A*C*B) i‖) = fun i => ‖minors C i‖ := by
  funext i
  rw [minors, blockView_sandwich index standard_block_label (A := A) (B := B) hA hB]
  simp [Matrix.det_mul, norm_det_unitary _ (blockView_unitary index standard_block_label hA hoA _),
    norm_det_unitary _ (blockView_unitary index standard_block_label hB hoB _), minors]

/-- The entry-modulus identities hold for all complex unitary 2×2 blocks. -/
theorem unitary2_norm (W : CMat 2) (hW : Unitary W) :
    ‖W 1 0‖ = ‖W 0 1‖ ∧ ‖W 0 0‖^2 + ‖W 0 1‖^2 = 1 := by
  have hu : GS.Shared.Unitary W := hW
  have hc := hu.column_norm_sq 0
  have hr : ‖W 0 0‖^2 + ‖W 0 1‖^2 = 1 := by simpa [Fin.sum_univ_two] using hu.conjTranspose.column_norm_sq 0
  rw [Fin.sum_univ_two] at hc
  exact ⟨(sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by linarith), hr⟩

theorem core_bound (W Y : Fin 3 → CMat 2) (hW : ∀ i, Unitary (W i)) (hY : ∀ i, Unitary (Y i)) :
    DetBound (fun i => ‖coreDet W Y i‖) := by
  let a i := ‖W i 0 0‖
  let b i := ‖W i 0 1‖
  let e i := ‖Y i 0 0‖
  let f i := ‖Y i 0 1‖
  have h (V : CMat 2) (hv : Unitary V) : ‖V 0 1‖ ≤ 1 :=
    entry_norm_bound_of_unitary (Matrix.mem_unitaryGroup_iff'.mpr hv.1) 0 1
  have hb : b 0 ≤ 1 := h _ (hW 0)
  have hmul : a 1*b 0*e 1*f 2 ≤ a 1*e 1 := by
    calc
      _ = (a 1*e 1)*(b 0*f 2) := by ring
      _ ≤ (a 1*e 1)*(1*1) := by gcongr; exact h _ (hY 2)
      _ = _ := by simp
  have hh : a 1 * e 1 + b 1 * f 1 ≤ 1 := by
    nlinarith [(unitary2_norm _ (hW 1)).2, (unitary2_norm _ (hY 1)).2,
      sq_nonneg (a 1 - e 1), sq_nonneg (b 1 - f 1)]
  have hsq : (b 1*f 1)^2 ≤ (1-a 1*b 0*e 1*f 2)^2 := by
    gcongr
    linarith
  have hw (i : Fin 3) := (unitary2_norm _ (hW i)).1
  have hy (i : Fin 3) := (unitary2_norm _ (hY i)).1
  simp [DetBound, coreDet, hw, hy]
  change (b 0*b 1*f 1*f 0) * (b 1*b 2*f 2*f 1) ≤ (b 2*b 0*f 0*f 2) * (1-a 1*b 0*e 1*f 2)^2
  calc
    _ = (b 2*b 0*f 0*f 2) * (b 1*f 1)^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsq (by positivity)

theorem necessaryCondition (A : CMat 6) (h : CInA4Unitary 2 2 2 2 P P P A) :
    DetBound (fun i => ‖minors A i‖) := by
  obtain ⟨B₁,B₂,B₃,B₄,h₁,h₂,h₃,h₄,u₁,u₂,u₃,u₄,rfl⟩ := h
  rw [UnitaryGeometry.product4, show B₄ * P * B₃ * P * B₂ * P * B₁ =
      B₄ * (P * B₃ * P * B₂ * P) * B₁ by grind]
  rw [minors_outer _ _ _ h₄ h₁ u₄ u₁]
  obtain ⟨W,huW,rfl⟩ := (supported_blocks_iff index standard_block_label B₃).mp ⟨h₃,u₃⟩
  obtain ⟨Y,huY,rfl⟩ := (supported_blocks_iff index standard_block_label B₂).mp ⟨h₂,u₂⟩
  change DetBound (fun i => ‖minors (P * assemble W * P * assemble Y * P) i‖)
  rw [P_eq_perm, core_det]
  exact core_bound _ _ huW huY

end GS.UnitaryFour

end

section

/-!
# Exact complex four-factor counterexample

The certified real matrix is embedded entrywise into the complex matrices.
Its determinant-modulus table is unchanged, so the universal unitary
obstruction rules out complex factors as well as real factors.
-/

open Matrix
namespace GS.UnitaryFour
open GS.UnitaryGeometry

theorem norm_minors_ofRealMatrix (A : Mat 6) (i : Fin 4) :
    ‖GS.M4.minors (ofRealMatrix A) i‖ = |GS.M4.minors A i| := by
  simp [ofRealMatrix, GS.M4.minors, Matrix.det_fin_two,
    ← Complex.ofReal_mul, ← Complex.ofReal_sub, Real.norm_eq_abs]

/-- The explicit algebraic matrix, now considered over ℂ. -/
def Q : CMat 6 := ofRealMatrix GS.M4.Q

theorem Q_unitary : Unitary Q := ofRealMatrix_unitary GS.M4.Q_orthogonal

theorem Q_mem_A4 : CInA4 2 2 2 2 P P P Q := by
  obtain ⟨B₁,B₂,B₃,B₄,h₁,h₂,h₃,h₄,he⟩ := GS.M4.Q_mem_A4
  refine ⟨_,_,_,_,ofRealMatrix_blockDiagonal h₁,ofRealMatrix_blockDiagonal h₂,
    ofRealMatrix_blockDiagonal h₃,ofRealMatrix_blockDiagonal h₄,?_⟩
  simpa [Q,P,GS.product4,GS.UnitaryGeometry.product4] using congrArg ofRealMatrix he

theorem Q_not_mem_A4Unitary : ¬ CInA4Unitary 2 2 2 2 P P P Q := by
  intro h
  have hn := necessaryCondition Q h
  simp [DetBound, Q, norm_minors_ofRealMatrix, GS.M4.minors_Q, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg 2), abs_of_nonneg (Real.sqrt_nonneg 3)] at hn
  nlinarith [mul_pow (Real.sqrt 2) (Real.sqrt 3) 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num),
    Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]

/-- Unconditional insufficiency of four unitary block factors in the fixed GS family. -/
theorem _root_.GSPalomar.unitary_four_factor_counterexample :
    ∃ A : CMat 6, let P : CMat 6 := fun i j => (GS.M4.P i j : ℂ)
      CInA4 2 2 2 2 P P P A ∧ Unitary A ∧ ¬CInA4Unitary 2 2 2 2 P P P A := ⟨Q, Q_mem_A4, Q_unitary, Q_not_mem_A4Unitary⟩

end GS.UnitaryFour

namespace GS.M4

open GS.UnitaryGeometry

/-- Complex nonfactorization rules out real orthogonal factors by scalar extension. -/
theorem _root_.GSPalomar.four_factor_counterexample :
    ∃ A : GS.Mat 6,
      GS.InA4 2 2 2 2 GS.M4.P GS.M4.P GS.M4.P A ∧ GS.Orthogonal A ∧
      ¬ GS.InA4Orth 2 2 2 2 GS.M4.P GS.M4.P GS.M4.P A := by
  refine ⟨Q, Q_mem_A4, Q_orthogonal, ?_⟩
  rintro ⟨B₁, B₂, B₃, B₄, h₁, h₂, h₃, h₄, u₁, u₂, u₃, u₄, h⟩
  apply GS.UnitaryFour.Q_not_mem_A4Unitary
  refine ⟨_,_,_,_,ofRealMatrix_blockDiagonal h₁, ofRealMatrix_blockDiagonal h₂,
    ofRealMatrix_blockDiagonal h₃, ofRealMatrix_blockDiagonal h₄,
    ofRealMatrix_unitary u₁, ofRealMatrix_unitary u₂, ofRealMatrix_unitary u₃,
    ofRealMatrix_unitary u₄, ?_⟩
  simpa only [GS.product4, GS.UnitaryGeometry.product4, ofRealMatrix_mul,
    GS.UnitaryFour.Q, GS.UnitaryFour.P] using
    congrArg ofRealMatrix h

end GS.M4

end
