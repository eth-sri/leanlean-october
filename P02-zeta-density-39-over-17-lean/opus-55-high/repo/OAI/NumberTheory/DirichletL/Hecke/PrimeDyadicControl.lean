module
public import OAI.NumberTheory.DirichletL.Hecke.DyadicControl
public import OAI.NumberTheory.DirichletL.Hecke.DeletionDerivative
import WeylPort.Analytic.RealLaplace

public section

namespace OAI

open scoped Classical Topology
open Metric Complex
namespace SevenEighths.HeckePrimeDyadicControl
open HeckeFamily HeckeLogarithmicInput HeckeLogarithmic HeckeFiniteDeletion
open HeckeDeletionBounds

theorem logDeriv_eq_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    (hχ : χ.residue ≠ 1) {s : ℂ} (hs : 0 < s.re)
    (hψs : LFunction ψ s ≠ 0) :
    logDeriv (LFunction χ) s = logDeriv (LFunction ψ) s +
      logDeriv (factors χ.modulus ψ) s := by
  pm_5667
  have heq : LFunction χ =ᶠ[nhds s] (fun z => LFunction ψ z * factors χ.modulus ψ z) := by
    filter_upwards [(Complex.isOpen_re_gt 0).mem_nhds hs] with z hz
    exact LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hz
  rw [(logDeriv_congr_nhds heq).self_of_nhds]
  exact logDeriv_fun_mul s hψs (factors_ne_zero _ _ hs)
    (LFunction_entire_nonprincipal ψ hψ s) (factors_differentiable _ _ s)

section
variable (e : ℝ) (he : 0<e) (he' : e<1/1000)
include e he he'
theorem original_disk_control :
    ∃ B : ℝ, 0≤B ∧ ∀ (χ : Character), χ.residue ≠ 1 → ∀ a t : ℝ,
      1/2≤a → a≤1 →
      (∀ z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), LFunction χ z ≠ 0) →
      ∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-8*e),
        ‖logDeriv (LFunction χ) z‖ ≤ B*Real.log (complexity χ t) +
          localBound (1/2)*Real.log ((radical χ.modulus).absNorm : ℝ) := by
  obtain ⟨Dp,B,_,hB,hprimitive⟩ := HeckeLogarithmicActual.disk_control e 1 he he' (by norm_num)
  refine ⟨B,hB,?_⟩
  pm_3109
  have hbound := (hprimitive ψ hp a t ha ha' hzeroψ).2 z hz
  rw [hregular] at hbound
  pm_3110
  have hdel := HeckeDeletionDerivative.factors_logDeriv_norm (1/2) (by norm_num)
    χ.modulus ψ hzre
  have hQ : complexity ψ t ≤ complexity χ t := by
    unfold complexity
    pm_106 hn' ψ.modulus.absNorm χ.modulus.absNorm hn
    gcongr
  have hc0 : 0 < complexity ψ t := (Real.exp_pos 1).trans_le (complexity_ge_exp ψ t)
  rw [logDeriv_eq_of_mask χ ψ hmask hχ hzpos (by simpa [hregular] using hzeroψ z hz2)]
  apply (norm_add_le _ _).trans
  exact add_le_add (hbound.trans (mul_le_mul_of_nonneg_left (Real.log_le_log hc0 hQ) hB)) hdel

theorem buffered_original_control :
    ∃ B : ℝ, 0≤B ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue ≠ 1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T) < a+2*e →
      ∀ (j : ι) (t : ℝ), |t| ≤ (3*i+2 : ℕ)*T →
      ∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-8*e),
        ‖logDeriv (LFunction (χ j)) z‖ ≤ B*Real.log (complexity (χ j) t) +
          localBound (1/2)*Real.log ((radical (χ j).modulus).absNorm : ℝ) := by
  pm_114 B hB hbound original_disk_control e he he'
  refine ⟨B,hB,?_⟩
  pm_3112

theorem buffered_rectangle_control :
    ∃ B : ℝ, 0≤B ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (z : ℂ), a+8*e≤z.re → z.re≤2 →
      |z.im|≤(3*i+2 : ℕ)*T →
      LFunction (χ j) z≠0 ∧
      ‖logDeriv (LFunction (χ j)) z‖≤
        B*Real.log (complexity (χ j) ((3*i+2 : ℕ)*T)) +
          localBound (1/2)*Real.log ((radical (χ j).modulus).absNorm : ℝ) := by
  pm_114 B hB hbound buffered_original_control e he he'
  refine ⟨B,hB,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j z hzl hzr hzi
  have hz6 : z ∈ closedBall ((2 : ℂ)+z.im*I) (2-a-8*e) := by
    pm_271
  pm_228
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ hB
  apply Real.log_le_log ((Real.exp_pos 1).trans_le (complexity_ge_exp _ _))
  unfold complexity
  have hH : 0 ≤ (3*i+2 : ℕ)*T := (abs_nonneg z.im).trans hzi
  rw [abs_of_nonneg hH]
  gcongr
end

end SevenEighths.HeckePrimeDyadicControl


end OAI
