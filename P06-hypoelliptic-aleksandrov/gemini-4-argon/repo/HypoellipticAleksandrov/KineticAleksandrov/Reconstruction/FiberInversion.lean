module

public import HypoellipticAleksandrov.KineticAleksandrov.Reconstruction.FiberHeight

/-!
# Fourier inversion on a fibre

Step Lemma 5.2 of the reconstruction lemma.  For `m`-almost every `y`
with `g(y) < ∞` and `H(y) < ∞`, the finite measure `g(y) π_y` on `ℝ^d` has the integrable Fourier
transform `ξ ↦ k̃^ξ(y)`, hence (Fourier inversion, `eq_withDensity_vecInvDensity`) the nonnegative
density `G(y, ·)` bounded by `H(y)`, with integral `g(y)`; consequently
`∫ G(y, z)^q dz ≤ H(y)^{q-1} g(y)`.  The inverse integral is jointly measurable, and
`Γ` has the density `G` with respect to `m ⊗ Leb`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set
open scoped ENNReal

namespace HypoellipticAleksandrov.KineticAleksandrov.Reconstruction

variable {Y : Type*} [MeasurableSpace Y] {d : ℕ}

/- The fibre density `G(y, z) = (2π)^{-d} Re ∫ e^{i ξ·z} k̃^ξ(y) dξ` obtained by Fourier
inversion. -/
def fiberInversionDensity (g : Y → ℝ≥0∞) (κ : Kernel Y (PDE.Vec d)) (p : Y × PDE.Vec d) :
    ℝ≥0∞ :=
  ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹ *
    (vecInvIntegral (fun ξ => fiberDensity g κ ξ p.1) p.2).re)

/- The Fourier transform of `g(y) • κ y` is the fibre representative `k̃^ξ(y)`. -/
lemma vecFourier_smul_kernel (κ : Kernel Y (PDE.Vec d)) (g : Y → ℝ≥0∞) (y : Y)
    (ξ : PDE.Vec d) : vecFourier ((g y) • κ y) ξ = fiberDensity g κ ξ y := by
  unfold vecFourier fiberDensity fiberFourier
  rw [integral_smul_measure, Complex.real_smul]

/- Fibre inversion at a single `y`: the measure `g(y) π_y` equals the Lebesgue measure with
density `G(y, ·)`, and `G(y, ·) ≤ H(y)`. -/
lemma lintegral_rpow_le_of_le {μ : Measure (PDE.Vec d)} {G : PDE.Vec d → ℝ≥0∞} {H a : ℝ≥0∞}
    {q : ℝ} (hq : 1 < q) (hHT : H ≠ ∞) (hG : ∀ z, G z ≤ H) (hint : ∫⁻ z, G z ∂μ = a) :
    ∫⁻ z, G z ^ q ∂μ ≤ H ^ (q - 1) * a := by
  calc ∫⁻ z, G z ^ q ∂μ ≤ ∫⁻ z, H ^ (q - 1) * G z ∂μ := by
        refine lintegral_mono fun z => ?_
        calc G z ^ q = G z ^ (q - 1) * G z := by
              conv_lhs => rw [show q = (q - 1) + 1 by ring]
              rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) (by linarith), ENNReal.rpow_one]
          _ ≤ H ^ (q - 1) * G z :=
              mul_le_mul_left (ENNReal.rpow_le_rpow (hG z) (by linarith)) _
    _ = H ^ (q - 1) * a := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) hHT), hint]


/- **Step Lemma 5.2.**  Under the hypotheses of the reconstruction
lemma, the fibre inversion density `G` is jointly measurable, `Γ` has density `G` with respect to
`m ⊗ Leb`, and for `m`-almost every `y` one has `G(y, ·) ≤ H(y)`, `∫ G(y, z) dz = g(y)` and
`∫ G(y, z)^q dz ≤ H(y)^{q-1} g(y)`. -/
end HypoellipticAleksandrov.KineticAleksandrov.Reconstruction
