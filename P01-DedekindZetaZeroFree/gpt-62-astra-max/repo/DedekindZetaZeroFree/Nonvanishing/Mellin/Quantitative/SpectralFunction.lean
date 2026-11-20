module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.FixedData

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.Spectral

noncomputable section

open DedekindZetaZeroFree NumberField Filter Topology
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (D : FixedData S η)

def H (s : ℂ) : ℂ :=
  D.recipe.H s

def G (s : ℂ) : ℂ :=
  Complex.exp ((s - 5 / 6) ^ 2) * H D s / D.zetaSCont s

def f (Z : ℝ) : ℂ :=
  if 0 < Z then
    comparisonVerticalIntegral 2 (fun s => (Z : ℂ) ^ (s - 61 / 100) * G D s)
  else 0

def RS : ℂ :=
  comparisonPrincipalResidue F D.recipe.A D.recipe.target D.recipe.probe.principal
    D.recipe.continuation

theorem RS_spec :
    Tendsto (fun s : ℂ => (s - 1) * D.zetaSCont s) (𝓝[≠] 1) (𝓝 (RS D)) := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hE : ContinuousAt (fun s : ℂ => ∏ v ∈ D.recipe.A.Sf,
      (1 - D.recipe.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s))) 1 := by
    apply Continuous.continuousAt
    apply continuous_finset_prod
    intro v _
    apply Continuous.sub continuous_const
    apply Continuous.mul continuous_const
    unfold comparisonRealPower
    fun_prop
  refine (((((D.recipe.continuation.R_holo.differentiableAt (hopen.mem_nhds (by simp))).continuousAt).mul hE).tendsto).mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [(eventually_nhdsWithin_of_eventually_nhds (hopen.mem_nhds (by simp))), eventually_mem_nhdsWithin] with s hs hs1
  unfold FixedData.zetaSCont
  unfold PrincipalMellin.ActualRecipe.L comparisonPrincipalIncompleteL
  rw [Pi.mul_apply, (D.recipe.continuation.regularized s hs hs1)]
  ring

def c₀ : ℂ := RS D ^ 2 * D.M (1 / 6) * D.W1Hat 1 / 6

end

end DedekindZetaZeroFree.Quantitative.Spectral
