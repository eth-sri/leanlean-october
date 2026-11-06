module
public import OAI.NumberTheory.DirichletL.Reflection.NormalizedEnergy
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open InverseReflectedNormalization InverseKernelSourceUniform
noncomputable section
variable {φ : Type*} [Fintype φ]

lemma sqrt_extraction_identity (A B C r U V : ℝ)
    (hA : 0<A) (hB : 0<B) (hC : 0<C) (hr : 0< r) (hU : 0<U) (hV : 0<V) :
    (Real.sqrt A*Real.sqrt B/Real.sqrt C) /
      (r*Real.sqrt (A*U)*(B*V)) =
      1/(r*Real.sqrt U*V*Real.sqrt (C*B)) := by
  rw [Real.sqrt_mul hA.le,Real.sqrt_mul hC.le]
  pm_4923 hsa hA hsb hB
  pm_4923 hsc hC hsu hU
  field_simp
  grind

def extractedOutsideScalar (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→ Fin 3)
    (r U B R : ℝ) : ℝ :=
  smallScalar R / (r*Real.sqrt ((Ideal.absNorm (frozenExtracted F jF e 1):ℝ)*U)*
    ((Ideal.absNorm (frozenExtracted F jF e 2):ℝ)*B))

theorem extractedOutsideScalar_scale (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→ Fin 3)
    (r U B R : ℝ) (hr : 0< r) (hU : 0<U) (hB : 0<B) :
    extractedOutsideScalar F jF e r U B R * frozenBranchScale F jF e =
      smallScalar R / (r*Real.sqrt U*B*
        Real.sqrt ((Ideal.absNorm (frozenExtracted F jF e 0):ℝ)*
          (Ideal.absNorm (frozenExtracted F jF e 2):ℝ))) := by
  pm_3290
  unfold extractedOutsideScalar frozenBranchScale
  have hh := sqrt_extraction_identity _ _ _ r U B (hn 1) (hn 2) (hn 0) hr hU hB
  grind

lemma power_normalizer {Z : ℝ} (hZ : 1≤Z) (v ell el S₀ B₀ Td : ℝ) :
    smallScalar (Z ^(v+3*ell+el-Td)) /
      (Z ^(el/3)*Real.sqrt (Z ^v)*Z ^ell*Real.sqrt (Z ^S₀*Z ^B₀)) =
      outsideScalar Z v ell el S₀ B₀ Td := by
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_add hZ0,
    ← Real.rpow_mul hZ0.le,← Real.rpow_mul hZ0.le,
    ← Real.rpow_add hZ0,← Real.rpow_add hZ0,← Real.rpow_add hZ0]
  unfold outsideScalar
  rw [div_eq_mul_inv,← Real.rpow_neg hZ0.le]
  have he : -(el/3+v*(1/2:ℝ)+ell+(S₀+B₀)*(1/2:ℝ)) =
      -v/2-ell-el/3-(S₀+B₀)/2 := by ring
  grind

theorem extractedOutsideScalar_log_widths (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→ Fin 3)
    (Z r U B R : ℝ) (hZ : 1<Z) (hr : 0< r) (hU : 0<U) (hB : 0<B) (hR : 0<R) :
    extractedOutsideScalar F jF e r U B R * frozenBranchScale F jF e =
      outsideScalar Z (Real.logb Z U) (Real.logb Z B) (3*Real.logb Z r)
        (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
        (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
        (Real.logb Z U+3*Real.logb Z B+3*Real.logb Z r-Real.logb Z R) := by
  have hz0 : 0<Z := lt_trans zero_lt_one hZ
  pm_3290
  rw [extractedOutsideScalar_scale F jF e r U B R hr hU hB]
  symm
  rw [← power_normalizer hZ.le]
  unfold InverseTerminalWidths.normWidth
  rw [show 3*Real.logb Z r/3=Real.logb Z r by ring,
    show Real.logb Z U+3*Real.logb Z B+3*Real.logb Z r-
      (Real.logb Z U+3*Real.logb Z B+3*Real.logb Z r-Real.logb Z R)=Real.logb Z R by ring]
  rw [Real.rpow_logb hz0 (ne_of_gt hZ) hr,Real.rpow_logb hz0 (ne_of_gt hZ) hU,
    Real.rpow_logb hz0 (ne_of_gt hZ) hB,Real.rpow_logb hz0 (ne_of_gt hZ) hR,
    Real.rpow_logb hz0 (ne_of_gt hZ) (hn 0),Real.rpow_logb hz0 (ne_of_gt hZ) (hn 2)]

end
end SevenEighths.InverseReflectedPhase

end OAI
