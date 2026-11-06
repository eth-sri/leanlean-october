/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/SmoothingMatrix.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `@[expose] public section`). No other line was
changed; see docs/PORT-LOG.md.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.DifferentialSplitting

@[expose] public section

namespace OAI

noncomputable section

open MeasureTheory Matrix

namespace EuclideanRamsey

lemma covariance_splitting {k d : ℕ} (C : Matrix (Fin k) (Fin k) ℝ)
    (U : Matrix (Fin d) (Fin k) ℝ) (hC : C.IsSymm)
    (hU : U * C * U.transpose = 1) :
    let R := C * U.transpose
    let Z := 1 - R * U
    U * R = 1 ∧ U * Z = 0 ∧ C = R * R.transpose + Z * C * Z.transpose := by
  dsimp only
  let R := C * U.transpose
  have hR : U * R = 1 := by simpa only [R, ← Matrix.mul_assoc] using hU
  have hRt : R.transpose = U * C := by simp only [R, Matrix.transpose_mul,
    Matrix.transpose_transpose, hC.eq]
  have hRR : R.transpose * U.transpose = 1 := by
    rw [← Matrix.transpose_mul, hR, Matrix.transpose_one]
  refine ⟨hR, ?_, ?_⟩
  · change U * (1 - R * U) = 0
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hR, Matrix.one_mul, sub_self]
  · change C = R * R.transpose + (1 - R * U) * C * (1 - R * U).transpose
    have ht : (1 - R * U).transpose = 1 - U.transpose * R.transpose := by
      rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul]
    have h1 : R * U * C = R * R.transpose := by rw [hRt, Matrix.mul_assoc]
    have h2 : C * (U.transpose * R.transpose) = R * R.transpose := by
      rw [← Matrix.mul_assoc]
    have h3 : R * R.transpose * (U.transpose * R.transpose) = R * R.transpose := by
      rw [ Matrix.mul_assoc, ← Matrix.mul_assoc R.transpose, hRR, Matrix.one_mul]
    simp only [ht, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      h1, h2, h3]
    abel

end EuclideanRamsey

namespace EuclideanRamsey

def stencilDifferential {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ)
    (b : (Fin k → ℝ) → ℝ) (x : Fin k → ℝ) : ℝ :=
  (1/2 : ℝ) * ∑ j, ∑ l, C j l *
    iteratedFDeriv ℝ 2 b x ![Pi.single j 1, Pi.single l 1]

def gradientWeight {k d : ℕ} (U : Matrix (Fin d) (Fin k) ℝ) (x : Fin k → ℝ) : ℝ :=
  ∑ a, (∑ j, U a j * x j)^2

def CompactSmoothing : Prop :=
  ∀ (k d : ℕ), 1 ≤ d → ∀ (C : Matrix (Fin k) (Fin k) ℝ)
    (U : Matrix (Fin d) (Fin k) ℝ), C.IsSymm → U * C * U.transpose = 1 →
    ∀ η : ℝ, 0 < η → ∃ b : (Fin k → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) b ∧ HasCompactSupport b ∧ (∀ x, 0 ≤ b x) ∧
      0 < ∫ x, b x ∧
      (∫ x, max (-(stencilDifferential C b x)) 0 * gradientWeight U x) < η * ∫ x, b x

end EuclideanRamsey
namespace EuclideanRamsey
open MeasureTheory Matrix

theorem compact_smoothing : CompactSmoothing := by
  intro k d hd C U hC hU η hη
  let R := C * U.transpose
  let Z : Matrix (Fin k) (Fin k) ℝ := 1-R*U
  obtain ⟨hUR,hUZ,hsplit⟩ := covariance_splitting C U hC hU
  change U*R=1 at hUR
  change U*Z=0 at hUZ
  change C=R*R.transpose+Z*C*Z.transpose at hsplit
  let H := EuclideanSpace ℝ (Fin d)
  let eH : H ≃ₗ[ℝ] (Fin d → ℝ) := (EuclideanSpace.equiv (Fin d) ℝ).toLinearEquiv
  let u : (Fin k → ℝ) →ₗ[ℝ] H := eH.symm.toLinearMap.comp (Matrix.toLin' U)
  let r : H →ₗ[ℝ] (Fin k → ℝ) := (Matrix.toLin' R).comp eH.toLinearMap
  have hur : u.comp r = LinearMap.id := by
    apply LinearMap.ext
    intro y
    simp only [u,r,LinearMap.comp_apply,Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec, hUR, Matrix.one_mulVec]
    exact eH.symm_apply_apply y
  let V := LinearMap.ker u
  let e : (Fin k → ℝ) ≃L[ℝ] H×V := (rightInverseSplit u r hur).toContinuousLinearEquiv
  let eh : OrthonormalBasis (Fin d) ℝ H := EuclideanSpace.basisFun (Fin d) ℝ
  have hRv (j : Fin d) : r (eh j) = fun l => R l j := by
    change R.mulVec (eH (eh j)) = _
    have h : eH (eh j) = Pi.single j 1 := by
      change ((EuclideanSpace.basisFun (Fin d) ℝ) j).ofLp = _
      rw [EuclideanSpace.basisFun_apply]
      rfl
    rw [h, Matrix.mulVec_single]
    simp
    rfl
  have hZv (j : Fin k) : (fun l => Z l j) ∈ LinearMap.ker u := by
    rw [LinearMap.mem_ker]
    change eH.symm (U.mulVec (fun l => Z l j)) = 0
    have h : U.mulVec (fun l => Z l j) = 0 := by
      ext a
      change (U*Z) a j = 0
      rw [hUZ]; rfl
    rw [h,map_zero]
  let z : Fin k → V := fun j => ⟨fun l => Z l j,hZv j⟩
  have hR (j : Fin d) : e (fun l => R l j) = (eh j,0) := by
    rw [← hRv]
    exact rightInverseSplit_apply_R u r hur (eh j)
  have hZ (j : Fin k) : e (fun l => Z l j) = (0,z j) := by
    apply Prod.ext
    · exact hZv j
    · apply Subtype.ext
      change (fun l => Z l j) - r (u (fun l => Z l j)) = _
      rw [show u (fun l => Z l j) = 0 from hZv j,map_zero,sub_zero]
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let : MeasurableSpace V := borel V
  let : BorelSpace V := ⟨rfl⟩
  have hn : 1 ≤ Module.finrank ℝ H := by simpa [H] using hd
  obtain ⟨b,hbs,hbk,hbp,hbm,hsmall⟩ := exists_split_smoothing hn C R Z hsplit e eh z hR hZ hη
  refine ⟨b,hbs,hbk,hbp,hbm,?_⟩
  have hw (x : Fin k → ℝ) : ‖(e x).1‖^2 = gradientWeight U x := by
    change ‖eH.symm (U.mulVec x)‖^2 = _
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  have hop (x : Fin k → ℝ) : secondOperator C (fun j => Pi.single j 1) b x =
      stencilDifferential C b x := by simp only [secondOperator,stencilDifferential,hessianB_eq]
  simpa only [hw,hop] using hsmall

end EuclideanRamsey

end

end OAI
