module
public import MathCollab.Density.ZetaCounting
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.Analysis.Calculus.Deriv.Star

@[expose] public section

open Complex Set Filter
open scoped BigOperators Topology ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- Conjugating both the argument and value preserves complex analyticity. -/
theorem analyticAt_conj_conj_local {g : ℂ → ℂ} {ρ : ℂ} (hg : AnalyticAt ℂ g ρ) :
    AnalyticAt ℂ (fun z => conj (g (conj z))) (conj ρ) := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have ht : Tendsto (fun z : ℂ => conj z) (𝓝 (conj ρ)) (𝓝 ρ) := by
    simpa only [ContinuousAt, conj_conj] using Complex.continuous_conj.continuousAt (x := conj ρ)
  filter_upwards [ht.eventually (Complex.analyticAt_iff_eventually_differentiableAt.mp hg)] with z hz
  exact differentiableAt_conj_conj_iff.mpr hz

theorem isNontrivialZetaZero_conj {ρ : ℂ} (hρ : IsNontrivialZetaZero ρ) :
    IsNontrivialZetaZero (conj ρ) := by
  refine ⟨?_, by simpa using hρ.2.1, by simpa using hρ.2.2⟩
  rw [riemannZeta_conj, hρ.1, map_zero]

/-- Analytic multiplicity on the complement of the pole is preserved. -/
theorem zetaMultiplicity_conj_of_ne_one {ρ : ℂ} (hρ : ρ ≠ 1) :
    zetaMultiplicity (conj ρ) = zetaMultiplicity ρ := by
  have hc : conj ρ ≠ 1 := fun h => hρ (by simpa using congrArg (starRingEnd ℂ) h)
  obtain ⟨g, hg, hg0, he⟩ := (analyticOn_riemannZeta ρ hρ).analyticOrderAt_ne_top.mp
    (zeta_analyticOrder_ne_top hρ)
  apply (analyticOn_riemannZeta (conj ρ) hc).analyticOrderNatAt_eq_iff
    (zeta_analyticOrder_ne_top hc) |>.mpr
  refine ⟨fun z => conj (g (conj z)), analyticAt_conj_conj_local hg, by simpa using hg0, ?_⟩
  have ht : Tendsto (fun z : ℂ => conj z) (𝓝 (conj ρ)) (𝓝 ρ) := by
    simpa only [ContinuousAt, conj_conj] using Complex.continuous_conj.continuousAt (x := conj ρ)
  filter_upwards [ht.eventually he] with z hz
  simpa only [riemannZeta_conj, conj_conj, map_mul, map_pow, map_sub, smul_eq_mul, zetaMultiplicity] using
    congrArg (starRingEnd ℂ) hz

theorem zetaMultiplicity_conj {ρ : ℂ} (hρ : IsNontrivialZetaZero ρ) :
    zetaMultiplicity (conj ρ) = zetaMultiplicity ρ :=
  zetaMultiplicity_conj_of_ne_one (nontrivialZetaZero_ne_one hρ)

/-- Conjugation bijects the literal closed slabs, with both endpoints retained. -/
theorem zetaSlabCount_conj (σ a b : ℝ) :
    zetaSlabCount σ (-b) (-a) = zetaSlabCount σ a b := by
  classical
  unfold zetaSlabCount
  apply Finset.sum_bij (fun ρ _ => conj ρ)
  · intro ρ hρ
    obtain ⟨hz, hσ, hlo, hhi⟩ := mem_zetaZeroFinset.mp hρ
    exact mem_zetaZeroFinset.mpr ⟨isNontrivialZetaZero_conj hz, by simpa using hσ,
      by simp only [conj_im]; linarith, by simp only [conj_im]; linarith⟩
  · intro ρ hρ z hz he
    exact (starRingEnd ℂ).injective he
  · intro ρ hρ
    refine ⟨conj ρ, ?_, by simp⟩
    obtain ⟨hz, hσ, hlo, hhi⟩ := mem_zetaZeroFinset.mp hρ
    exact mem_zetaZeroFinset.mpr ⟨isNontrivialZetaZero_conj hz, by simpa using hσ,
      by simp only [conj_im]; linarith, by simp only [conj_im]; linarith⟩
  · intro ρ hρ
    exact (zetaMultiplicity_conj (mem_zetaZeroFinset.mp hρ).1).symm

/-- Closed slab splitting is an upper bound even if the shared endpoint is a zero. -/
theorem zetaSlabCount_split_le (σ a b c : ℝ) :
    zetaSlabCount σ a c ≤ zetaSlabCount σ a b+zetaSlabCount σ b c := by
  classical
  have hs : zetaZeroFinset σ a c ⊆ zetaZeroFinset σ a b ∪ zetaZeroFinset σ b c := by
    intro ρ hρ
    obtain ⟨hz, hσ, hlo, hhi⟩ := mem_zetaZeroFinset.mp hρ
    by_cases hb : ρ.im ≤ b
    · exact Finset.mem_union_left _ (mem_zetaZeroFinset.mpr ⟨hz,hσ,hlo,hb⟩)
    · exact Finset.mem_union_right _ (mem_zetaZeroFinset.mpr ⟨hz,hσ,(not_le.mp hb).le,hhi⟩)
  apply (Finset.sum_le_sum_of_subset hs).trans
  have hh : (∑ ρ ∈ zetaZeroFinset σ a b ∪ zetaZeroFinset σ b c, zetaMultiplicity ρ) +
      (∑ ρ ∈ zetaZeroFinset σ a b ∩ zetaZeroFinset σ b c, zetaMultiplicity ρ) =
      (∑ ρ ∈ zetaZeroFinset σ a b, zetaMultiplicity ρ) +
      (∑ ρ ∈ zetaZeroFinset σ b c, zetaMultiplicity ρ) := Finset.sum_union_inter
  unfold zetaSlabCount
  omega

theorem zetaDensityCount_le_twice_positive (σ T : ℝ) :
    zetaDensityCount σ T ≤ 2*zetaSlabCount σ 0 T := by
  have hs := zetaSlabCount_split_le σ (-T) 0 T
  have hc := zetaSlabCount_conj σ 0 T
  simp only [neg_zero] at hc
  change zetaSlabCount σ (-T) T ≤ _
  rw [hc] at hs
  omega

end MathCollab.Density
