module
import Mathlib
public import OAI.NumberTheory.DirichletL.Detector.MellinBoundary
public import OAI.NumberTheory.DirichletL.Hecke.LogarithmicInput
public import OAI.NumberTheory.DirichletL.Hecke.DeletionBounds

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical Topology
open Complex Set
namespace SevenEighths.PrincipalMellinGrowth
open HeckeFamily PrincipalMellinResidues ProbeMellinBoundary

def principalConstant (M : Ideal HeckeFamily.O) : ℝ :=
  (1+HeckeLogarithmicInput.uniformConstant)*(M.absNorm : ℝ)^(3/5 : ℝ)*
    HeckeDeletionBounds.localBound (19/20)^(IdealMobiusDivisorSum.primeSupport M).card

theorem principalConstant_pos (M : Ideal HeckeFamily.O) [NeZero M] :
    0<principalConstant M := by
  have hQ : 0<(M.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (NeZero.ne M))
  exact mul_pos (mul_pos (by linarith [HeckeLogarithmicInput.uniformConstant_nonneg])
    (Real.rpow_pos_of_pos hQ _)) (pow_pos (HeckeDeletionBounds.localBound_pos (by norm_num)) _)

section
variable (χ : Character) (hχ : χ.residue=1)
    {s : ℂ}
include χ hχ s

lemma poleRemoved_eq_mul_regular  (hs : s+1≠0) :
    HeckeOrigin.poleRemoved χ s=(s+1)*HeckeLogarithmicInput.regular χ s := by
  simp only [HeckeLogarithmicInput.regular,ite_eq_left hχ,HeckePrincipalStrip.sourceNormalized]
  field_simp

theorem principal_poleRemoved_growth  (hs : (19/20 : ℝ)≤ s.re) :
    ‖HeckeOrigin.poleRemoved χ s‖≤principalConstant χ.modulus*‖s+1‖*(3+|s.im|)^2 := by
  obtain ⟨ψ,_,hp,hQ,hmask⟩ := exists_primitive_character χ
  have hψ : ψ.residue=1 := (HeckeFiniteDeletion.principal_iff_of_mask χ ψ hmask).mp hχ
  have hs0 : 0<s.re := by linarith
  have h0 : s≠0 := by intro hh; norm_num [hh] at hs
  have hplus : s+1≠0 := by
    intro hh
    have hr := congrArg Complex.re hh
    simp only [add_re,one_re,zero_re] at hr
    linarith
  have heq : HeckeOrigin.poleRemoved χ s=
      ((s+1)*HeckeLogarithmicInput.regular ψ s)*HeckeFiniteDeletion.factors χ.modulus ψ s := by
    rw [← poleRemoved_eq_mul_regular ψ hψ hplus]
    by_cases h1 : s=1
    · subst s
      rw [HeckeOrigin.poleRemoved_one,HeckeOrigin.poleRemoved_one]
      exact HeckeFiniteDeletion.regularizedL_eq_of_mask χ ψ hmask (by norm_num)
    · rw [HeckeOrigin.poleRemoved_eq χ h0 h1,HeckeOrigin.poleRemoved_eq ψ h0 h1,
        HeckeFiniteDeletion.LFunction_eq_of_mask χ ψ hmask hs0 h1]
      ring
  have hg := HeckeLogarithmicInput.regular_right_growth ψ hp (by linarith : -(1/10 : ℝ)≤ s.re)
  have hd := (HeckeDeletionBounds.factors_bound_pow (19/20) (by norm_num)
    χ.modulus ψ hs).1
  have hQ' : (ψ.modulus.absNorm : ℝ)^(3/5 : ℝ)≤(χ.modulus.absNorm : ℝ)^(3/5 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hQ) (by norm_num)
  have hC := HeckeLogarithmicInput.uniformConstant_nonneg
  have hD := (HeckeDeletionBounds.localBound_pos (by norm_num : (0 : ℝ)<19/20)).le
  rw [heq,norm_mul,norm_mul]
  calc
    _ ≤ (‖s+1‖*(HeckeLogarithmicInput.uniformConstant*(ψ.modulus.absNorm : ℝ)^(3/5 : ℝ)*
          (3+|s.im|)^2))*
        HeckeDeletionBounds.localBound (19/20)^(IdealMobiusDivisorSum.primeSupport χ.modulus).card := by
      gcongr
    _ ≤ (‖s+1‖*((1+HeckeLogarithmicInput.uniformConstant)*(χ.modulus.absNorm : ℝ)^(3/5 : ℝ)*
          (3+|s.im|)^2))*
        HeckeDeletionBounds.localBound (19/20)^(IdealMobiusDivisorSum.primeSupport χ.modulus).card := by
      gcongr
      linarith
    _ = _ := by unfold principalConstant; ring
end


def wAmplitude (M : Ideal HeckeFamily.O) (cw : ℝ) : ℝ := 9*(cw+2)*principalConstant M

section
variable (M : Ideal HeckeFamily.O) [NeZero M] {cw : ℝ} (hcw : 1<cw)
include M cw hcw

theorem wAmplitude_pos  :
    0<wAmplitude M cw := by
  unfold wAmplitude
  exact mul_pos (mul_pos (by norm_num) (by linarith)) (principalConstant_pos M)

theorem fixed_principal_w_growth  {x : ℝ} (hx : x∈Icc (19/20 : ℝ) cw) (t : ℝ) :
    ‖HeckeOrigin.poleRemoved (fixedPrincipal M) ((x:ℂ)+t*I)‖≤wAmplitude M cw*height t^3 := by
  have hb := principal_poleRemoved_growth (fixedPrincipal M) rfl
    (show (19/20 : ℝ)≤(((x:ℂ)+t*I) : ℂ).re by simpa using hx.1)
  have hn : ‖((x:ℂ)+t*I)+1‖≤(cw+2)*height t := by
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    simp
    rw [abs_of_pos (by linarith [hx.1] : 0<x+1)]
    unfold height
    have hmul : 0≤(cw+1)*|t| := mul_nonneg (by linarith) (abs_nonneg t)
    nlinarith [hx.2]
  have hheight : (3+|t|)^2≤9*height t^2 := by
    have hh : 3+|t|≤3*height t := by unfold height; linarith [abs_nonneg t]
    have hp := pow_le_pow_left₀ (by positivity : 0≤3+|t|) hh 2
    simpa only [mul_pow,show (3:ℝ)^2=9 by norm_num] using hp
  have hC := (principalConstant_pos M).le
  have ht0 := (height_pos t).le
  change ‖HeckeOrigin.poleRemoved (fixedPrincipal M) ((x:ℂ)+t*I)‖≤
    principalConstant M*‖((x:ℂ)+t*I)+1‖*(3+|(((x:ℂ)+t*I) : ℂ).im|)^2 at hb
  simp at hb
  calc
    _ ≤ principalConstant M*‖((x:ℂ)+t*I)+1‖*(3+|t|)^2 := hb
    _ ≤ principalConstant M*((cw+2)*height t)*(9*height t^2) := by
      have hc2 : 0≤cw+2 := by linarith
      gcongr
    _ = _ := by unfold wAmplitude; ring
end


theorem source_w_boundary (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ)
    (ha1 : 0<a1) (hW1 : Function.support W1⊆Icc a1 b1)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hY : 0<Y)
    (eta : Character) (s z : ℂ) (hEta : LFunction eta s≠0) (H B : ℂ → ℂ → ℂ) {cw AH : ℝ}
    (hcw : 1<cw) (hAH : 0≤AH) (JH : ℕ)
    (hHB : ContinuousOn (fun w => H w z*B w z) {w : ℂ | (19/20:ℝ)≤w.re ∧ w.re≤cw})
    (hHBbd : ∀x∈Icc (19/20:ℝ) cw, ∀t : ℝ, (x=19/20 ∨ x=cw ∨ 1≤|t|) →
      ‖H ((x:ℂ)+t*I) z * B ((x:ℂ)+t*I) z‖≤AH*height t^JH) :
    BoundaryControl (fun w => sourceMultiplier W0 W1 X Y Z eta s H B w z *
      LFunction (fixedPrincipal M) w) (19/20) cw := by
  apply ProbeMellinBoundary.source_w_boundary W0 W1 a1 b1 ha1 hW1 M X Y Z hY eta s z hEta H B
    (AL:=wAmplitude M cw) hcw hAH (wAmplitude_pos M hcw).le JH 3 hHB hHBbd
  intro x hx t _
  exact fixed_principal_w_growth M hcw hx t






