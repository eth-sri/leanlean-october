module
public import OAI.NumberTheory.DirichletL.PrimeRows.PrincipalMask
public import OAI.NumberTheory.DirichletL.PrimeRows.Conductor
public import OAI.NumberTheory.DirichletL.Hecke.LogarithmicInput
public import OAI.NumberTheory.DirichletL.Hecke.DeletionBounds
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

section
variable (σ δ : ℝ) (hσ : 0<σ) (hδ : 0<δ)
include σ δ hσ hδ
theorem nonprincipal_positive_growth :
    ∃C : ℝ,0<C ∧ ∀χ : Character,χ.residue≠1 → ∀s : ℂ,σ≤ s.re →
      ‖HeckeOrigin.continued χ s‖≤C*(χ.modulus.absNorm:ℝ)^(3/5+δ)*(3+|s.im|)^2 := by
  pm_97 Cd hCd hdel HeckeDeletionBounds.factors_subpower_bound σ δ hσ hδ
  pm_928
  pm_554 hQ
  pm_450
  have hg := HeckeLogarithmicInput.regular_right_growth ψ hp (by linarith : -(1/10:ℝ)≤ s.re)
  rw [HeckeLogarithmicInput.regular_eq_nonprincipal ψ hψ] at hg
  have hd : ‖HeckeFiniteDeletion.factors χ.modulus ψ s‖≤Cd*(χ.modulus.absNorm:ℝ)^δ :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans (hdel χ.modulus χ.modulus_ne_bot ψ s hs)
  have hQ' : (ψ.modulus.absNorm:ℝ)^(3/5:ℝ)≤(χ.modulus.absNorm:ℝ)^(3/5:ℝ) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hQ) (by norm_num)
  have hU := HeckeLogarithmicInput.uniformConstant_nonneg
  pm_5723 hN χ.modulus.absNorm χ.modulus_ne_bot
  rw [HeckeOrigin.continued,ite_eq_right hχ,
    HeckeFiniteDeletion.LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ (by linarith),norm_mul]
  calc
    _ ≤ (HeckeLogarithmicInput.uniformConstant*(ψ.modulus.absNorm:ℝ)^(3/5:ℝ)*(3+|s.im|)^2)*
        (Cd*(χ.modulus.absNorm:ℝ)^δ) := mul_le_mul hg hd (norm_nonneg _) (by positivity)
    _ ≤ ((1+HeckeLogarithmicInput.uniformConstant)*(χ.modulus.absNorm:ℝ)^(3/5:ℝ)*(3+|s.im|)^2)*
        (Cd*(χ.modulus.absNorm:ℝ)^δ) := by gcongr;linarith
    _ = _ := by rw [Real.rpow_add hN];ring

theorem calibrated_numerator_positive_growth
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0<C ∧ ∀(u : FreeRow),u.val≠1 → ∀s : ℂ,σ≤ s.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) s‖≤
        C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(3/5+δ)*(3+|s.im|)^2 := by
  pm_97 C hC hmain nonprincipal_positive_growth σ δ hσ hδ
  pm_1292
  pm_3395 hA A
  refine ⟨C*(1+A^(3/5+δ)),mul_pos hC (by positivity),?_⟩
  intro u hu s hs
  pm_410
  · simp only [hc,star_zero,zero_mul,norm_zero]
    positivity
  · have hnp := calibrated_row_nonprincipal S hS.prime hmax hS.bad u hu hc
    pm_422
    have hQ : ((rowCharacter S hS.prime u).modulus.absNorm:ℝ)≤
        A*((Ideal.span {u.val}:Ideal O).absNorm:ℝ) := by
      pm_1561
    rw [norm_mul]
    calc
      _ ≤ ‖HeckeOrigin.continued (rowCharacter S hS.prime u) s‖ :=
        mul_le_of_le_one_left (norm_nonneg _) hcal
      _ ≤ C*((rowCharacter S hS.prime u).modulus.absNorm:ℝ)^(3/5+δ)*(3+|s.im|)^2 := hg
      _ ≤ C*(A*((Ideal.span {u.val}:Ideal O).absNorm:ℝ))^(3/5+δ)*(3+|s.im|)^2 := by
        gcongr
      _ ≤ C*(1+A^(3/5+δ))*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(3/5+δ)*(3+|s.im|)^2 := by
        rw [Real.mul_rpow hA (by positivity)]
        calc
          _ = C*A^(3/5+δ)*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(3/5+δ)*(3+|s.im|)^2 := by ring
          _ ≤ _ := by gcongr;linarith
end

end SevenEighths.ProbeHighRowFamily
end

end OAI
