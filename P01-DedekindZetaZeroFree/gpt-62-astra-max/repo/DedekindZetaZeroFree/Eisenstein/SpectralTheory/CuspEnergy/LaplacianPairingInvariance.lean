module
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspDivergence.CodifferentialInvariance
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspEnergy.GradientDensityInvariance

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspEnergy.RadialTests
public import DedekindZetaZeroFree.Geometry.SymmetricSpaces.QuaternionicMobius.LaplacianNaturality

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPCompactGreenRadialIntegrability
open KPMeanZeroWeightedEnergy

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    {ρ : S →* rootsOfUnity 3 F} {V : Submodule ℂ ℂ} {T : ℝ}

private theorem arch_real (d : ℕ) (z : KPArch.Space d) : arch d (real d z) = z := by
  ext i <;> simp [arch, real]

private alias smooth_arch := GradientDensityInvariance.smooth_arch

private alias smooth_real := GradientDensityInvariance.smooth_real

private alias smooth_mean := GradientDensityInvariance.smooth_mean

private alias derivative_smoothAt := GradientDensityInvariance.derivative_smoothAt

private theorem laplacian_smoothAt (d : ℕ) (g : HyperbolicChart.Space d → ℂ)
    (x : HyperbolicChart.Space d) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (HyperbolicChart.laplacian d g) x := by
  unfold HyperbolicChart.laplacian
  apply ContDiffAt.sum
  intro i hi
  have h (k : Fin 3) := derivative_smoothAt d g x hg i k
  have hh (k : Fin 3) := derivative_smoothAt d _ x (h k) i k
  have he : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : HyperbolicChart.Space d =>
      (Real.exp (2 * q (i, 2)) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x
      ((contDiffAt_const.mul (EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff.contDiffAt).exp)
  exact ((hh 2).neg.add (contDiffAt_const.mul (h 2))).sub
    (he.mul ((hh 0).add (hh 1)))

private alias representative_smoothAt := GradientDensityInvariance.representative_smoothAt

private alias chart_smooth := GradientDensityInvariance.chart_smooth

private theorem character_norm (ε : rootsOfUnity 3 F) :
    ‖(KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ)‖ = 1 := by
  apply IsOfFinOrder.norm_eq_one
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨3, by decide, ?_⟩
  have hp : ε ^ 3 = 1 := by
    apply Subtype.ext
    exact (mem_rootsOfUnity 3 _).mp ε.property
  simpa using
    congrArg (fun x => (KPCuspGenuineMonodromy.chi F ζ hζ x : ℂ)) hp

alias LaplacianPairingInvariance.character_norm := character_norm

open HyperbolicChart
 section

variable (d : ℕ) (h : Space d → ℂ)

def second (x v w : Space d) : ℂ :=
  fderiv ℝ (fderiv ℝ h) x v w
private theorem cd_second (x : Space d)
    (hh : ContDiffAt ℝ (⊤ : ℕ∞) h x) (i : Fin d) (k : Fin 3) :
    coordinateDerivative d i k (coordinateDerivative d i k h) x =
      second d h x (coordinateVector d i k) (coordinateVector d i k) := by apply @DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.CodifferentialInvariance.cd_second <;> assumption

end
private alias affine_first := DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.CodifferentialInvariance.affine_first
private theorem affine_second (d : ℕ) (L : Space d →L[ℝ] Space d) (b : Space d)
    (h : Space d → ℂ) (x : Space d) (i : Fin d) (k : Fin 3)
    (hh : ContDiffAt ℝ (⊤ : ℕ∞) h (L x + b)) :
    coordinateDerivative d i k (coordinateDerivative d i k (fun y => h (L y + b))) x =
      second d h (L x + b) (L (coordinateVector d i k)) (L (coordinateVector d i k)) := by apply @DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.CodifferentialInvariance.affine_second <;> assumption
 section

variable (d : ℕ) (u : Fin d → ℂ)

def lin : Space d →L[ℝ] Space d :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d × Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j =>
      ![(u j.1).re • EuclideanSpace.proj (j.1, (0 : Fin 3)) -
          (u j.1).im • EuclideanSpace.proj (j.1, (1 : Fin 3)),
        (u j.1).im • EuclideanSpace.proj (j.1, (0 : Fin 3)) +
          (u j.1).re • EuclideanSpace.proj (j.1, (1 : Fin 3)),
        EuclideanSpace.proj (j.1, (2 : Fin 3))] j.2))
private theorem lin_apply (x : Space d) (i : Fin d) (k : Fin 3) :
    lin d u x (i,k) =
      ![(u i).re * x (i,0) - (u i).im * x (i,1),
        (u i).im * x (i,0) + (u i).re * x (i,1), x (i,2)] k := by
  fin_cases k <;> rfl
private theorem lin_zero (i : Fin d) :
    lin d u (coordinateVector d i 0) =
      (u i).re • coordinateVector d i 0 + (u i).im • coordinateVector d i 1 := by
  ext ⟨j,k⟩
  fin_cases k <;> simp [lin_apply, coordinateVector]
  all_goals split_ifs <;> simp_all
private theorem lin_one (i : Fin d) :
    lin d u (coordinateVector d i 1) =
      -(u i).im • coordinateVector d i 0 + (u i).re • coordinateVector d i 1 := by
  ext ⟨j,k⟩
  fin_cases k <;> simp [lin_apply, coordinateVector]
  all_goals split_ifs <;> simp_all
private theorem lin_two (i : Fin d) :
    lin d u (coordinateVector d i 2) = coordinateVector d i 2 := by
  ext ⟨j,k⟩
  fin_cases k <;> simp [lin_apply, coordinateVector]
private theorem second_horizontal (h : Space d → ℂ)
    (x : Space d) (i : Fin d) :
    second d h x (lin d u (coordinateVector d i 0)) (lin d u (coordinateVector d i 0)) +
      second d h x (lin d u (coordinateVector d i 1)) (lin d u (coordinateVector d i 1)) =
      (‖u i‖ ^ 2 : ℝ) •
        (second d h x (coordinateVector d i 0) (coordinateVector d i 0) +
         second d h x (coordinateVector d i 1) (coordinateVector d i 1)) := by apply @DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.CodifferentialInvariance.second_horizontal <;> assumption
private theorem affine_laplacian (b : Space d)
    (hb : ∀ i, b (i,2) = Real.log ‖u i‖) (hu : ∀ i, u i ≠ 0)
    (h : Space d → ℂ) (x : Space d)
    (hh : ContDiffAt ℝ (⊤ : ℕ∞) h (lin d u x + b)) :
    laplacian d (fun y => h (lin d u y + b)) x = laplacian d h (lin d u x + b) := by apply @DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.CodifferentialInvariance.affine_laplacian <;> assumption

end
private alias laplacian_congr := DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.CodifferentialInvariance.laplacian_congr

alias LaplacianPairingInvariance.laplacian_congr := laplacian_congr
private alias laplacian_mul := DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.CodifferentialInvariance.laplacian_mul
private alias upper_fst := DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.CodifferentialInvariance.upper_fst
 def shift (d : ℕ) (u b : Fin d → ℂ) : Space d :=
  WithLp.toLp 2 (fun j => ![(b j.1).re, (b j.1).im, Real.log ‖u j.1‖] j.2)
private theorem upper_real (d : ℕ) (g : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (u : Fin d → ℂ) (hu : ∀ i, u i ≠ 0)
    (hz : ∀ i, g i 1 0 = 0) (hr : ∀ i, g i 0 0 = u i * g i 1 1)
    (x : Space d) : real d (KPArch.productAction d g (arch d x)) =
      lin d u x + shift d u (fun i => g i 0 1 / g i 1 1) := by apply @DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.CodifferentialInvariance.upper_real <;> assumption
private alias upper_equivariant_laplacian := DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.CodifferentialInvariance.upper_equivariant_laplacian

theorem laplacian_action_invariant (d : ℕ)
    (g : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (h : HyperbolicChart.Space d → ℂ) (x : HyperbolicChart.Space d) (c : ℂ)
    (hc : (fun y => h (real d (KPArch.productAction d g (arch d y)))) =ᶠ[nhds x]
      (fun y => c * h y))
    (hx : ContDiffAt ℝ (⊤ : ℕ∞) h x)
    (hy : ContDiffAt ℝ (⊤ : ℕ∞) h (real d (KPArch.productAction d g (arch d x)))) :
    HyperbolicChart.laplacian d h (real d (KPArch.productAction d g (arch d x))) =
      c * HyperbolicChart.laplacian d h x := by
  have hA : (CotangentLogCoframe.A d : Space d → KPArch.Space d) = arch d := by
    funext y
    ext i
    · apply Complex.ext <;> simp [CotangentLogCoframe.A_apply, arch]
    · rfl
  have hR : ((CotangentLogCoframe.A d).symm : KPArch.Space d → Space d) = real d := rfl
  have hp := KPShift68LaplacianInvariant.productAction_pullback_at d g h x
    (by simpa only [hA, hR] using hy)
  simp only [hA, hR] at hp
  rw [← hp, laplacian_congr d _ _ x hc, laplacian_mul d h x c hx]

theorem scalar_laplacian_continuousOn_and_invariant
    (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) :
    ContinuousOn (fun p => (star (v.scalar p) * v.laplacian p).re) {p | T < p.2} ∧
      ∀ p q : {p : KPCuspCharts.Coordinates F // T < p.2},
        KPCuspCharts.highRelation F S T p q →
          (star (v.scalar p.val) * v.laplacian p.val).re =
            (star (v.scalar q.val) * v.laplacian q.val).re := by
  constructor
  · apply continuousOn_of_forall_continuousAt
    intro p hp
    have hp' : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
        (arch (KPCuspLogShape.dimension F)
          (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p))) := by
      rw [arch_real, KPCuspCharts.toArch_meanHeight F G.positive_dimension]
      exact hp
    have hlap : ContinuousAt
        (fun q : KPCuspCharts.Coordinates F =>
          HyperbolicChart.laplacian (KPCuspLogShape.dimension F)
            (v.val ∘ arch (KPCuspLogShape.dimension F))
            (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F q))) p :=
      (laplacian_smoothAt _ _ _ (representative_smoothAt v _ hp')).continuousAt.comp
        (f := fun q : KPCuspCharts.Coordinates F =>
          real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F q))
        chart_smooth.continuous.continuousAt
    have hsc : ContinuousAt v.scalar p := by
      have h1 :=
        v.smooth.continuousOn.continuousAt ((isOpen_lt continuous_const (smooth_mean _).continuous).mem_nhds (by
          show T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
            (KPCuspCharts.toArch F p)
          rw [KPCuspCharts.toArch_meanHeight F G.positive_dimension]
          exact hp))
      exact h1.comp (KPCuspCharts.toArch_contDiff F).continuous.continuousAt
    exact Complex.continuous_re.continuousAt.comp (hsc.star.mul hlap)
  · intro p q hrel
    change MulAction.orbitRel S (KPArch.Space (KPCuspLogShape.dimension F))
      (KPCuspCharts.toArch F p.val) (KPCuspCharts.toArch F q.val) at hrel
    obtain ⟨s, hs⟩ := hrel
    change KPCuspSiegel.action F s
      (KPCuspCharts.toArch F q.val) = KPCuspCharts.toArch F p.val at hs
    obtain ⟨A, hA, hAz⟩ := D.upper s.val s.property
    set g : Fin (KPCuspLogShape.dimension F) → Matrix.GeneralLinearGroup (Fin 2) ℂ :=
      fun i => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding A with hg
    have hs' : KPArch.productAction (KPCuspLogShape.dimension F) g
        (KPCuspCharts.toArch F q.val) = KPCuspCharts.toArch F p.val := by
      have h1 := hs
      rw [← hA, KPCuspSiegel.action_mk] at h1
      simp only [KPCuspSiegel.glAction, hg] at h1
      exact h1
    have hc : (fun y : HyperbolicChart.Space (KPCuspLogShape.dimension F) =>
        (v.val ∘ arch (KPCuspLogShape.dimension F))
          (real (KPCuspLogShape.dimension F)
            (KPArch.productAction (KPCuspLogShape.dimension F) g
              (arch (KPCuspLogShape.dimension F) y)))) =ᶠ[nhds
          (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F q.val))]
        (fun y => (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) *
          (v.val ∘ arch (KPCuspLogShape.dimension F)) y) := by
      have hopen :=
        (isOpen_lt continuous_const (smooth_mean _).continuous).mem_nhds (by
          show T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
            (KPCuspCharts.toArch F q.val)
          rw [KPCuspCharts.toArch_meanHeight F G.positive_dimension]
          exact q.property)
      filter_upwards [((smooth_arch _).continuous.continuousAt).eventually hopen] with y hy
      have hys : KPArch.productAction (KPCuspLogShape.dimension F) g
          (arch (KPCuspLogShape.dimension F) y) =
          KPCuspSiegel.action F s
            (arch (KPCuspLogShape.dimension F) y) := by
        rw [← hA, KPCuspSiegel.action_mk]
        rfl
      simp only [Function.comp_apply, arch_real]
      rw [hys]
      exact v.equivariant s (arch (KPCuspLogShape.dimension F) y) hy
    let u :=
      fun i => (KPCusp.complexPlace F i).embedding ((D.ratio s : Fˣ) : F)
    have hz : ∀ i, g i 1 0 = 0 := by
      intro i
      change (KPCusp.complexPlace F i).embedding (A 1 0) = 0
      simp [hAz]
    have hr : ∀ i, g i 0 0 = u i * g i 1 1 := by
      intro i
      change (KPCusp.complexPlace F i).embedding (A 0 0) = _
      rw [D.ratioFormula s A hA hAz, map_mul]
      rfl
    have hkey := upper_equivariant_laplacian (KPCuspLogShape.dimension F) g u (fun i =>
      (map_ne_zero (KPCusp.complexPlace F i).embedding).mpr (Units.ne_zero _)) hz hr
      (v.val ∘ arch (KPCuspLogShape.dimension F))
      (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F q.val))
      (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) hc (representative_smoothAt v _ (by
        rw [arch_real, KPCuspCharts.toArch_meanHeight F G.positive_dimension]
        exact q.property))
      (by rw [arch_real, hs']; exact (representative_smoothAt v _ (by
        rw [arch_real, KPCuspCharts.toArch_meanHeight F G.positive_dimension]
        exact p.property)))
    have hlap : v.laplacian p.val =
        (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) * v.laplacian q.val := by
      have h := hkey
      rw [arch_real, hs'] at h
      simpa only [Representative.laplacian] using h
    have hsc : v.scalar p.val =
        (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) * v.scalar q.val := by
      have hq : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
          (KPCuspCharts.toArch F q.val) := by
        rw [KPCuspCharts.toArch_meanHeight F G.positive_dimension]
        exact q.property
      have he := v.equivariant s (KPCuspCharts.toArch F q.val) hq
      rw [hs] at he
      simpa only [Representative.scalar] using he
    have hcc : star (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) *
        (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) = 1 := by
      rw [Complex.star_def, Complex.conj_mul', character_norm (ρ s)]
      norm_num
    calc _
        = (star ((KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) * v.scalar q.val) *
            ((KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) * v.laplacian q.val)).re := by
          rw [hsc, hlap]
      _ = (star (v.scalar q.val) * v.laplacian q.val).re := by
          congr 1
          calc _
              = (star (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) *
                  (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ)) *
                  (star (v.scalar q.val) * v.laplacian q.val) := by
                rw [star_mul]
                ring
            _ = star (v.scalar q.val) * v.laplacian q.val := by rw [hcc, one_mul]

end DedekindZetaZeroFree.KPCompactGreenRadialIntegrability

end
