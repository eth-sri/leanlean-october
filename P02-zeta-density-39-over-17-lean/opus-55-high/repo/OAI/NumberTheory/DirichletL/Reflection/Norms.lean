module
public import OAI.NumberTheory.DirichletL.Reflection.Ramified
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open ActualEisensteinCubic CubicEisenstein CompletedGauss LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}
noncomputable local instance phaseNormField (P : Ideal Eis) [P.IsMaximal] : Field (Eis ⧸ P) := Ideal.Quotient.field P
noncomputable local instance phaseNormFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

section
variable [∀ i, (Ideal.span {p i}).IsMaximal]
omit [Fintype ι] in
theorem crossSymbol_norm
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (i k : ι) (hik : i ≠ k) : ‖MixedCrossSeparation.crossSymbol p hg i k‖ = 1 := by
  pm_3791
  have h6 : MixedCrossSeparation.crossSymbol p hg i k ^ 6 = 1 := by
    simpa only [MixedCrossSeparation.crossSymbol,map_pow,ite_eq_right hnot] using
      canonicalSextic_sixth_power_mask (Ideal.span {p i}) (hg i) (p k)
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : (6:ℕ) ≠ 0)).mp
  simpa only [norm_pow,norm_one] using congrArg norm h6

theorem local_phase_norm
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (i : ι) (j : ℕ) (hj : j < 6) :
    ‖(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) j (D.epsilon i)‖ = 1 := by
  rw [norm_mul,FiniteRayExpansion.norm_char_unit,one_mul]
  exact canonical_phase_norm (Ideal.span {p i}) (hg i) (hchar i) (quotientTrace (p i) (hp i))
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i)) j hj (D.epsilon i)
end

set_option hygiene false in
macro "pf_184" x1:term:max x2:ident x3:term:max : tactic => `(tactic| (
  have h := local_phase_norm D hp hg hchar i $x1:term (by decide)
  rw [$x2:ident,norm_mul,norm_prod] at h
  have he : (∏ k ∈ Finset.univ.erase i, ‖MixedCrossSeparation.crossSymbol p hg i k^$x3:term‖) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [norm_pow,crossSymbol_norm hg hcop i k (Finset.mem_erase.mp hk).1.symm,one_pow]
  simpa only [he,mul_one] using h))
section
variable [∀ i, (Ideal.span {p i}).IsMaximal] (D : ControlledStratumArithmetic p N a c mode) (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2) (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
include D hp hg hchar hcop
theorem markedPrimeScalar_norm (i : ι) :
    ‖markedPrimeScalar (p i) c (hp i) (hg i)‖ = 1 := by pf_184 0 controlled_marked_phase 2

theorem residualPrimeScalar_norm (i : ι) :
    ‖residualPrimeScalar (p i) c (hp i) (hg i)‖ = 1 := by pf_184 1 controlled_residual_phase 4

theorem residualWithFrozen_norm
    (R F : Finset ι) (hd : Disjoint R F) : ‖residualWithFrozen hp hg c R F‖ = 1 := by
  unfold residualWithFrozen
  pm_5366 residualPrimeScalar_norm
  have hR : (∏ k ∈ R.erase i, ‖MixedCrossSeparation.crossSymbol p hg i k‖^4) = 1 := by
    pm_5840
  have hF : (∏ k ∈ F, ‖MixedCrossSeparation.crossSymbol p hg i k‖^4) = 1 := by
    pm_806
  rw [hR,hF,one_mul]

theorem markedWithFrozen_norm
    (P F : Finset ι) (hd : Disjoint P F) : ‖markedWithFrozen hp hg c P F‖ = 1 := by
  unfold markedWithFrozen
  pm_5366 markedPrimeScalar_norm
  have hP : (∏ k ∈ P.erase i, ‖MixedCrossSeparation.crossSymbol p hg i k‖^2) = 1 := by
    pm_5840
  have hF : (∏ k ∈ F, ‖MixedCrossSeparation.crossSymbol p hg i k‖^2) = 1 := by
    pm_806
  rw [hP,hF,one_mul]
end

end
end SevenEighths.InverseReflectedPhase

end OAI
