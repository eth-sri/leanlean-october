module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.Definitions
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.RightBounds
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Nonprincipality

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RowAnalyticContinuation

noncomputable section

open DedekindZetaZeroFree NumberField
open scoped Classical NumberField

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)











theorem W1Hat_differentiable : Differentiable ℂ D.W1Hat := by
  have hne : ∀ v, D.recipe.probe.finiteTrace v ≠ 1 := by
    intro v he
    obtain ⟨x, hx⟩ := D.recipe.probe.finiteTrace_ne_one D.recipe.A D.recipe.σ D.recipe.target
      D.recipe.traceBad v
    exact hx (by rw [he]; rfl)
  let w : NumberField.InfinitePlace F := Classical.choice inferInstance
  obtain ⟨dt, hdt, hdis, hsheet⟩ := probe_sheet_mellin_estimates F D.recipe.A
    D.recipe.probe.finiteTrace D.recipe.probe.continuousTrace D.recipe.probe.traceCompatible hne
    D.recipe.probe.additiveMeasure D.recipe.probe.multiplicativeMeasure
    D.recipe.probe.additiveHaar D.recipe.probe.multiplicativeHaar w
    D.recipe.probe.W0 D.recipe.probe.W1 D.recipe.probe.annular D.recipe.probe.compactSupport
    D.recipe.probe.supportUnits
  rcases hsheet with ⟨_, _, _, _, _, hW, _, _⟩
  exact hW

theorem mem_OmegaStar_of_re (ξ w z : ℂ) (h1 : Scales.goodLine - EulerDomain.pad ≤ ξ.re)
    (h2 : w.re = Scales.wLine) (h3 : z.re = Scales.zLine) :
    (ξ, w, z) ∈ EulerDomain.OmegaStar := by
  unfold Scales.goodLine EulerDomain.pad at h1
  unfold Scales.wLine at h2
  unfold Scales.zLine at h3
  show 0 < ξ.re ∧ 0 < w.re ∧ 0 < z.re ∧ 1 < 6 * z.re + w.re ∧ 1 < ξ.re + 6 * z.re ∧
    1 < ξ.re + w.re ∧ 2 < ξ.re + w.re + 6 * z.re ∧ 5 < 6 * ξ.re + 6 * z.re ∧ 1 / 2 < ξ.re ∧
    2 < 3 * ξ.re ∧ 5 / 2 < 3 * ξ.re + w.re
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- Analyticity of the common Mellin weight times a holomorphic Euler factor. -/
theorem kernel_product_differentiableAt (M W : ℂ → ℂ) (Z q : ℝ)
    (hZ : 0 < Z) (hq : 0 < q) (p : ℂ × ℂ × ℂ) {E : ℂ × ℂ × ℂ → ℂ}
    (hM : DifferentiableAt ℂ M p.2.2) (hW : DifferentiableAt ℂ W p.2.1)
    (hE : DifferentiableAt ℂ E p) :
    DifferentiableAt ℂ (fun x : ℂ × ℂ × ℂ =>
      (Z : ℂ) ^ (((Scales.xExponent / 2 : ℝ) : ℂ) + x.1 - 1 + (Scales.smoothingExponent : ℂ) * x.2.2
        + (Scales.yExponent : ℂ) * (x.2.1 - 1)) * Complex.exp ((x.1 + x.2.2 - 1) ^ 2)
        * M x.2.2 * W x.2.1 * (q : ℂ) ^ (-x.2.2) * E x) p := by
  refine DifferentiableAt.mul (DifferentiableAt.mul (DifferentiableAt.mul (DifferentiableAt.mul
    (DifferentiableAt.mul ?_ ?_) (hM.comp p (by fun_prop))) (hW.comp p (by fun_prop))) ?_) hE
  · exact DifferentiableAt.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr hZ.ne'))
  · fun_prop
  · exact DifferentiableAt.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr hq.ne'))

private theorem zeta_differentiableAt_six (z : ℂ) (hz : 0 < z.re) (h : 6 * z ≠ 1) :
    DifferentiableAt ℂ D.zetaSCont (6 * z) :=
  (RightHeckeBounds.zetaSCont_analyticOnNhd D _ ⟨by simp; linarith, h⟩).differentiableAt

/-- The common zeta and Hecke quotient, multiplied by a normal-convergent product. -/
theorem euler_quotient_differentiableAt (p : ℂ × ℂ × ℂ) (P Q : ℂ → ℂ)
    (hP : DifferentiableAt ℂ P p.2.1) (hQ : DifferentiableAt ℂ Q p.1)
    (hq : Q p.1 ≠ 0) (hz : 0 < p.2.2.re) (h : 6 * p.2.2 ≠ 1)
    {C : ℂ × ℂ × ℂ → ℂ} (hC : DifferentiableAt ℂ C p) :
    DifferentiableAt ℂ (fun x : ℂ × ℂ × ℂ => D.zetaSCont (6 * x.2.2) * P x.2.1 * C x / Q x.1) p := by
  simp only [div_eq_mul_inv]
  refine DifferentiableAt.mul (DifferentiableAt.mul (DifferentiableAt.mul ?_ ?_) hC)
    ((hQ.comp p (by fun_prop)).inv hq)
  · exact (zeta_differentiableAt_six D _ hz h).comp p (by fun_prop)
  · exact hP.comp p (by fun_prop)





end

end DedekindZetaZeroFree.Quantitative.RowAnalyticContinuation
