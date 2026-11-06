module

public import Mathlib
public import RoughRegime.Macro
public import RoughRegime.Upper
public import RoughRegime.Notation

𝗌

/-!
Centered-kernel orthogonality and covariance ingredients for Lemma 7.
No covariance identity or centering contraction is assumed.
-/

𝚵

namespace RoughRegime.UpperCovariance

def kernelSum
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => 𝗓) ℝ)
    (X : Fin n → Ω → 𝗓) (ω : Ω) : ℝ :=
  ∑ e : 𝚖₁, H fun i => X (e i) ω

/-- The normalization in the centered expansion of the manuscript's lift. -/
def kernelStatistic
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => 𝗓) ℝ)
    (X : Fin n → Ω → 𝗓) (ω : Ω) : ℝ :=
  𝚐₂ * kernelSum H X ω

/-- Finite centered expansion, with the exact coefficients from the paper's Taylor lift. -/
def centeredKernelExpansion (c : ℝ)
    (H : (r : Fin R) → ContinuousMultilinearMap ℝ (fun _ : Fin 𝗙₁ => 𝗓) ℝ)
    (X : Fin n → Ω → 𝗓) (ω : Ω) : ℝ :=
  c + ∑ r : Fin R, kernelStatistic (H r) X ω

/-- The centered derivative expression appearing in the proof of Lemma 7. -/
def centeredDerivativeLift (R : ℕ)
    (F : 𝙩₁) (m : 𝗓)
    (Y : Fin n → Ω → 𝗓) : 𝘄 :=
  centeredKernelExpansion (MvPolynomial.eval m F)
    (fun r : Fin R => iteratedFDeriv ℝ 𝗙₁ 𝘣₁ m) Y
