/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.StructureConstant
public import DOZZ.Statements.Defs.UnitVolumeStructureConstant
public import DOZZ.Statements.Defs.SExp
public import DOZZ.Statements.Correlations.ComplexifyNCharges
public import Mathlib.Analysis.Meromorphic.Complex
import DOZZ.ShiftEquations.Residual.Calibration
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The full structure constant along complex charge lines

From a holomorphic extension `f` of the unit-volume structure constant
(`DOZZ.unitVolumeStructureConstant_holomorphic_near_extended_domain`), the full structure constant
continues as `C_f(w) = μ^{-s(w)} Γ(s(w)) f(w)`. It is meromorphic along every analytic charge curve
staying in the domain of `f`, and equals `structureConstant` at real triples where `f` is the
unit-volume structure constant.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- The `s`-parameter of a complex charge triple. -/
noncomputable def sExpC (γ : ℝ) (w : Fin 3 → ℂ) : ℂ := (w 0 + w 1 + w 2 - 2 * Q γ) / γ

/-- The full structure constant built from a holomorphic extension `f` of the unit-volume one. -/
noncomputable def structureConstantH (f : (Fin 3 → ℂ) → ℂ) (γ μ : ℝ) (w : Fin 3 → ℂ) : ℂ :=
  (μ : ℂ) ^ (-sExpC γ w) * Complex.Gamma (sExpC γ w) * f w

theorem sExpC_complexify (γ : ℝ) (a : Fin 3 → ℝ) :
    sExpC γ (complexifyNCharges a) = (sExp γ (a 0) (a 1) (a 2) : ℂ) := by
  unfold sExpC sExp complexifyNCharges
  push_cast
  ring

/-- **The continued structure constant at real triples.** -/
theorem structureConstantH_complexify {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure ℂ) {f : (Fin 3 → ℂ) → ℂ} {γ μ : ℝ} (hμ : 0 < μ) (a : Fin 3 → ℝ)
    (hf : f (complexifyNCharges a) = (unitVolumeStructureConstant P M γ (a 0) (a 1) (a 2) : ℂ)) :
    structureConstantH f γ μ (complexifyNCharges a) =
      (structureConstant P M γ μ (a 0) (a 1) (a 2) : ℂ) := by
  unfold structureConstantH
  rw [sExpC_complexify, hf, structureConstant_eq_mul_unitVolume, ← Complex.ofReal_neg,
    ← Complex.ofReal_cpow hμ.le, Complex.Gamma_ofReal]
  push_cast
  ring

variable {f : (Fin 3 → ℂ) → ℂ} {V : Set (Fin 3 → ℂ)} (hV : IsOpen V) (hf : DifferentiableOn ℂ f V) {γ μ : ℝ} (hμ : 0 < μ) {ℓ : ℂ → Fin 3 → ℂ} (hℓ : Differentiable ℂ ℓ)

include f V hV hf γ μ hμ ℓ hℓ in
/-- **The continued structure constant is meromorphic along analytic charge curves** staying in
the open domain of holomorphy of `f`. -/
theorem meromorphicOn_structureConstantH_comp  :
    MeromorphicOn (fun t => structureConstantH f γ μ (ℓ t)) (ℓ ⁻¹' V) := by
  intro t ht
  have hUo  := hV.preimage hℓ.continuous
  have hfℓ  :=
    hf.comp hℓ.differentiableOn fun _ hx => hx
  have hfa  := hfℓ.analyticAt (hUo.mem_nhds ht)
  have hs : AnalyticAt ℂ (fun t => sExpC γ (ℓ t)) t := by
    unfold sExpC
    have h0  :=
      ((differentiable_pi.mp hℓ) 0).analyticAt t
    have h1  :=
      ((differentiable_pi.mp hℓ) 1).analyticAt t
    have h2  :=
      ((differentiable_pi.mp hℓ) 2).analyticAt t
    fun_prop (disch := positivity)
  have hμs  := Complex.ofReal_mem_slitPlane.mpr hμ
  have hpow  :=
    analyticAt_const.cpow hs.neg hμs
  have hΓ  :=
    (Meromorphic.Gamma _).comp_analyticAt (g := fun t => sExpC γ (ℓ t)) hs
  exact (hpow.meromorphicAt.mul hΓ).mul hfa.meromorphicAt

include f V hV hf γ μ hμ ℓ hℓ in
/-- **The continued structure constant is analytic** along analytic charge curves at points
where `s ∉ -ℕ`. -/
theorem analyticAt_structureConstantH_comp  {t : ℂ} (ht : ℓ t ∈ V)
    (hs : ∀ n : ℕ, sExpC γ (ℓ t) ≠ -(n : ℂ)) :
    AnalyticAt ℂ (fun t => structureConstantH f γ μ (ℓ t)) t := by
  have hUo  := hV.preimage hℓ.continuous
  have hfℓ  :=
    hf.comp hℓ.differentiableOn fun _ hx => hx
  have hfa  := hfℓ.analyticAt (hUo.mem_nhds ht)
  have hsa : AnalyticAt ℂ (fun t => sExpC γ (ℓ t)) t := by
    unfold sExpC
    have h0  :=
      ((differentiable_pi.mp hℓ) 0).analyticAt t
    have h1  :=
      ((differentiable_pi.mp hℓ) 1).analyticAt t
    have h2  :=
      ((differentiable_pi.mp hℓ) 2).analyticAt t
    fun_prop (disch := positivity)
  have hμs  := Complex.ofReal_mem_slitPlane.mpr hμ
  have hpow  :=
    analyticAt_const.cpow hsa.neg hμs
  have hΓa : AnalyticAt ℂ Complex.Gamma (sExpC γ (ℓ t)) := by
    have h1 : AnalyticAt ℂ (fun u => (Complex.Gamma u)⁻¹) (sExpC γ (ℓ t)) :=
      Complex.differentiable_one_div_Gamma.analyticAt _
    have h2 := h1.inv (inv_ne_zero (Complex.Gamma_ne_zero hs))
    have hfun : (fun u => (Complex.Gamma u)⁻¹)⁻¹ = Complex.Gamma := by
      funext u
      simp
    rwa [hfun] at h2
  have hΓ  :=
    AnalyticAt.comp_of_eq hΓa hsa rfl
  exact (hpow.mul hΓ).mul hfa

end DOZZ.Proofs

end
