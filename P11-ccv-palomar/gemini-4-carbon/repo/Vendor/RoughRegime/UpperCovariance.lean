module

public import Mathlib
public import RoughRegime.Upper

@[expose] public section

/-!
Centered-kernel orthogonality and covariance ingredients for Lemma 7.
No covariance identity or centering contraction is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace RoughRegime.UpperCovariance

def kernelSum {Ω : Type*} {n p r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (ω : Ω) : ℝ :=
  ∑ e : Fin r ↪ Fin n, H (fun i => X (e i) ω)

/-- The normalization in the centered expansion of the manuscript's lift. -/
def kernelStatistic {Ω : Type*} {n p r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (ω : Ω) : ℝ :=
  ((r.factorial : ℝ) * (n.descFactorial r : ℝ))⁻¹ * kernelSum H X ω

/-- Finite centered expansion, with the exact coefficients from the paper's Taylor lift. -/
def centeredKernelExpansion {Ω : Type*} {n p R : ℕ} (c : ℝ)
    (H : (r : Fin R) → ContinuousMultilinearMap ℝ (fun _ : Fin (r.val + 1) => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (ω : Ω) : ℝ :=
  c + ∑ r : Fin R, kernelStatistic (H r) X ω

/-- The centered derivative expression appearing in the proof of Lemma 7. -/
def centeredDerivativeLift {Ω : Type*} {n p : ℕ} (R : ℕ)
    (F : MvPolynomial (Fin p) ℝ) (m : Fin p → ℝ)
    (Y : Fin n → Ω → Fin p → ℝ) : Ω → ℝ :=
  centeredKernelExpansion (MvPolynomial.eval m F)
    (fun r : Fin R => iteratedFDeriv ℝ (r.val + 1) (fun x => MvPolynomial.eval x F) m) Y

end RoughRegime.UpperCovariance
