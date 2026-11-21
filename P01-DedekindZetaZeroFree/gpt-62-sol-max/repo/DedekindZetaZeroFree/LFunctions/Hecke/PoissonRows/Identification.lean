module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.FiniteEulerCorrections

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RowHeckeBridge

noncomputable section

open DedekindZetaZeroFree NumberField
open scoped Classical

theorem isOpen_re_gt (r : ℝ) : IsOpen {z : ℂ | r < z.re} :=
  isOpen_lt continuous_const Complex.continuous_re

theorem eqOn_halfPlane_of_eq_right {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.re}) (hg : AnalyticOnNhd ℂ g {z : ℂ | 0 < z.re})
    (h : ∀ z : ℂ, 1 < z.re → f z = g z) :
    ∀ z : ℂ, 0 < z.re → f z = g z := by
  have h2 : (2 : ℂ) ∈ {z : ℂ | 0 < z.re} := by
    show (0 : ℝ) < (2 : ℂ).re
    norm_num
  have hev : f =ᶠ[nhds (2 : ℂ)] g := by
    refine Filter.eventually_of_mem ((isOpen_re_gt 1).mem_nhds ?_) (fun z hz => h z hz)
    show (1 : ℝ) < (2 : ℂ).re
    norm_num
  have := hf.eqOn_of_preconnected_of_eventuallyEq hg
    (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected h2 hev
  assumption

theorem entire_eq_of_eq_right {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h : ∀ z : ℂ, 1 < z.re → f z = g z) : f = g := by
  have hev : f =ᶠ[nhds (2 : ℂ)] g := by
    refine Filter.eventually_of_mem ((isOpen_re_gt 1).mem_nhds ?_) (fun z hz => h z hz)
    show (1 : ℝ) < (2 : ℂ).re
    norm_num
  have hf' : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hg' : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  have := hf'.eqOn_of_preconnected_of_eventuallyEq hg' isPreconnected_univ
    (Set.mem_univ (2 : ℂ)) hev
  solve_by_elim [funext]

section Primitive

variable {F : Type} [Field F] [NumberField F]

def hecke (A : SArithmeticData F) (ν : Detector.PrimitiveFrequencyCharacter F)
    (hν : ¬ ν.character.IsPrincipal) :
    NonprincipalRayHeckeData F ν.conductor ν.character :=
  nonprincipalRayHeckeData F (primitive12_totallyComplex F A.zeta12 A.primitive_zeta12)
    ν.conductor ν.conductor_ne_zero ν.character ν.primitive hν

theorem hecke_analyticOn (A : SArithmeticData F) (ν : Detector.PrimitiveFrequencyCharacter F)
    (hν : ¬ ν.character.IsPrincipal) :
    AnalyticOnNhd ℂ (hecke A ν hν).L {z : ℂ | 0 < z.re} :=
  (hecke A ν hν).L_holo.analyticOnNhd (isOpen_re_gt 0)

theorem hecke_eq_idealLSeries (A : SArithmeticData F) (ν : Detector.PrimitiveFrequencyCharacter F)
    (hν : ¬ ν.character.IsPrincipal) (s : ℂ) (hs : 1 < s.re) :
    (hecke A ν hν).L s = Detector.idealLSeries F ν.character s := by
  rw [← ((hecke A ν hν).series s hs).tsum_eq]
  unfold Detector.idealLSeries
  refine tsum_congr fun I => ?_
  by_cases h : I = ⊥
  · simp_all
  grind

theorem eq_hecke_of_analyticOn (A : SArithmeticData F) (ν : Detector.PrimitiveFrequencyCharacter F)
    (hν : ¬ ν.character.IsPrincipal) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g {z : ℂ | 0 < z.re})
    (h : ∀ s : ℂ, 1 < s.re → g s = Detector.idealLSeries F ν.character s) :
    ∀ s : ℂ, 0 < s.re → g s = (hecke A ν hν).L s :=
  eqOn_halfPlane_of_eq_right hg (hecke_analyticOn A ν hν)
    (fun s hs => (h s hs).trans (hecke_eq_idealLSeries A ν hν s hs).symm)

theorem entire_eq_hecke (A : SArithmeticData F) (ν : Detector.PrimitiveFrequencyCharacter F)
    (hν : ¬ ν.character.IsPrincipal) {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (h : ∀ s : ℂ, 1 < s.re → g s = Detector.idealLSeries F ν.character s) :
    ∀ s : ℂ, 0 < s.re → g s = (hecke A ν hν).L s :=
  eq_hecke_of_analyticOn A ν hν (fun z _ => hg.analyticAt z) h

theorem hecke_exists_entire (A : SArithmeticData F) (ν : Detector.PrimitiveFrequencyCharacter F)
    (hν : ¬ ν.character.IsPrincipal) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ s : ℂ, 0 < s.re → g s = (hecke A ν hν).L s := by
  have hF := primitive12_totallyComplex F A.zeta12 A.primitive_zeta12
  exact ⟨nonprincipalHeckeEntireContinuation F ν.conductor ν.character (hecke A ν hν),
    nonprincipalHeckeEntireContinuation_differentiable F hF ν.conductor ν.conductor_ne_zero
      ν.character (hecke A ν hν),
    fun s hs => nonprincipalHeckeEntireContinuation_eq F hF ν.conductor ν.conductor_ne_zero
      ν.character (hecke A ν hν) s hs⟩


theorem mask_ne_zero (ν : Detector.PrimitiveFrequencyCharacter F)
    (E : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (hE : E.Finite) (s : ℂ)
    (hs : 0 < s.re) :
    Detector.finiteEulerDeletionMask F E (fun v => ν.character v.asIdeal) s ≠ 0 := by
  letI := hE.fintype
  rw [Detector.finiteEulerDeletionMask, finprod_eq_prod_of_fintype]
  apply Finset.prod_ne_zero_iff.mpr
  intro p _
  exact (Detector.finite_euler_local_factor_nonzero F s.re hs p.val
    (ν.character p.val.asIdeal) s
    (RayUnitary.ray_character_norm_le_one F ν.conductor ν.conductor_ne_zero
      ν.character p.val.asIdeal) le_rfl).2.2


end Primitive

section Rows

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

abbrev deletionSet (u : D.Row) :
    Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :=
  FrequencyCharacterMasks.frequencyMask u.toFrequency











abbrev heckePlus (u : D.Row) (hnp : ¬ (D.inducers u).plus.character.IsPrincipal) :
    NonprincipalRayHeckeData F (D.inducers u).plus.conductor (D.inducers u).plus.character :=
  hecke D.recipe.A (D.inducers u).plus hnp







end Rows

end

end DedekindZetaZeroFree.Quantitative.RowHeckeBridge
