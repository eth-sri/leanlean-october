module

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

private theorem derivative_smoothAt (d : ℕ) (g : HyperbolicChart.Space d → ℂ)
    (x : HyperbolicChart.Space d)
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) (i : Fin d) (k : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (HyperbolicChart.coordinateDerivative d i k g) x :=
  (hg.fderiv_right (by simp)).clm_apply contDiffAt_const

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

private theorem representative_smoothAt (v : Representative ζ hζ S ρ V T)
    (x : HyperbolicChart.Space (KPCuspLogShape.dimension F))
    (hx : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F) x)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (v.val ∘ arch (KPCuspLogShape.dimension F)) x := by
  have hopen : IsOpen {z : KPArch.Space (KPCuspLogShape.dimension F) |
      T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z} :=
    isOpen_lt continuous_const (KPMeanZeroWeightedEnergy.meanHeight_contDiff _).continuous
  exact (v.smooth.contDiffAt (hopen.mem_nhds hx)).comp x (KPMeanZeroWeightedEnergy.arch_contDiff _).contDiffAt

private theorem chart_smooth : ContDiff ℝ (⊤ : ℕ∞)
    (fun p : KPCuspCharts.Coordinates F =>
      real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p)) :=
  (KPMeanZeroWeightedEnergy.real_contDiff _).comp ((KPCuspCharts.toArch_contDiff F).of_le (by simp))

private theorem character_norm (ε : rootsOfUnity 3 F) :
    ‖(KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ)‖ = 1 := by
  apply IsOfFinOrder.norm_eq_one
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨3, by decide, ?_⟩
  have hp : ε ^ 3 = 1 := by
    apply Subtype.ext
    exact (mem_rootsOfUnity 3 _).mp ε.property
  simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using
    congrArg (fun x => (KPCuspGenuineMonodromy.chi F ζ hζ x : ℂ)) hp

open HyperbolicChart
private theorem laplacian_congr (d : ℕ) (h f : Space d → ℂ) (x : Space d)
    (he : h =ᶠ[nhds x] f) : laplacian d h x = laplacian d f x := by
  have hd (i : Fin d) (k : Fin 3) : coordinateDerivative d i k h =ᶠ[nhds x]
      coordinateDerivative d i k f := (he.fderiv (𝕜 := ℝ)).mono fun y hy => congrArg (fun A : Space d →L[ℝ] ℂ => A (coordinateVector d i k)) hy
  have hdd (i : Fin d) (k : Fin 3) := congrArg (fun A => A (coordinateVector d i k))
    ((hd i k).fderiv_eq (𝕜 := ℝ))
  have hd0 (i : Fin d) (k : Fin 3) := (hd i k).eq_of_nhds
  unfold laplacian
  apply Finset.sum_congr rfl
  intro i hi
  simp only [coordinateDerivative] at hd0 hdd ⊢
  rw [hdd, hdd, hdd, hd0]
private theorem laplacian_mul (d : ℕ) (h : Space d → ℂ) (x : Space d) (c : ℂ)
    (hh : ContDiffAt ℝ (⊤ : ℕ∞) h x) :
    laplacian d (fun y => c * h y) x = c * laplacian d h x := by
  have ht : ∀ᶠ y in nhds x, DifferentiableAt ℝ h y :=
    ((hh.of_le (show (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).eventually (by simp)).mono
      (fun y hy => hy.differentiableAt (by simp))
  have he (i : Fin d) (k : Fin 3) : coordinateDerivative d i k (fun y => c * h y) =ᶠ[nhds x]
      (fun y => c * coordinateDerivative d i k h y) := by
    filter_upwards [ht] with y hy
    simpa [coordinateDerivative] using congrArg (fun A : Space d →L[ℝ] ℂ => A (coordinateVector d i k))
      (hy.hasFDerivAt.const_mul c).fderiv
  have hd (i : Fin d) (k : Fin 3) :
      coordinateDerivative d i k (coordinateDerivative d i k (fun y => c * h y)) x =
      c * coordinateDerivative d i k (coordinateDerivative d i k h) x := by
    change fderiv ℝ (coordinateDerivative d i k (fun y => c * h y)) x _ = _
    rw [(he i k).fderiv_eq]
    have hs : ContDiffAt ℝ (⊤ : ℕ∞) (coordinateDerivative d i k h) x :=
      (hh.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const
    simpa [coordinateDerivative] using congrArg (fun A : Space d →L[ℝ] ℂ => A (coordinateVector d i k))
      ((hs.differentiableAt (by simp)).hasFDerivAt.const_mul c).fderiv
  unfold laplacian
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hd, hd, hd, (he i 2).eq_of_nhds]
  ring

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
      rw [KPMeanZeroWeightedEnergy.arch_real_eq, KPCuspCharts.toArch_meanHeight F G.positive_dimension]
      exact hp
    have hv := representative_smoothAt v _ hp'
    have hlap : ContinuousAt
        (fun q : KPCuspCharts.Coordinates F =>
          HyperbolicChart.laplacian (KPCuspLogShape.dimension F)
            (v.val ∘ arch (KPCuspLogShape.dimension F))
            (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F q))) p :=
      (laplacian_smoothAt _ _ _ hv).continuousAt.comp
        (f := fun q : KPCuspCharts.Coordinates F =>
          real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F q))
        chart_smooth.continuous.continuousAt
    have hsc : ContinuousAt v.scalar p := by
      have hopen : IsOpen {z : KPArch.Space (KPCuspLogShape.dimension F) |
          T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z} :=
        isOpen_lt continuous_const (KPMeanZeroWeightedEnergy.meanHeight_contDiff _).continuous
      have h1 : ContinuousAt v.val (KPCuspCharts.toArch F p) :=
        v.smooth.continuousOn.continuousAt (hopen.mem_nhds (by
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
    change KPCuspSiegel.action F (s : KPCuspArithmetic.PGL2 F)
      (KPCuspCharts.toArch F q.val) = KPCuspCharts.toArch F p.val at hs
    obtain ⟨A, hA, _⟩ := D.upper s.val s.property
    set g : Fin (KPCuspLogShape.dimension F) → Matrix.GeneralLinearGroup (Fin 2) ℂ :=
      fun i => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding A
    have hs' : KPArch.productAction (KPCuspLogShape.dimension F) g
        (KPCuspCharts.toArch F q.val) = KPCuspCharts.toArch F p.val := by
      have h1 := hs
      rw [← hA, KPCuspSiegel.action_mk] at h1
      simp only [KPCuspSiegel.glAction] at h1
      exact h1
    have hcont_p : ContDiffAt ℝ (⊤ : ℕ∞)
        (v.val ∘ arch (KPCuspLogShape.dimension F))
        (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p.val)) :=
      representative_smoothAt v _ (by
        rw [KPMeanZeroWeightedEnergy.arch_real_eq, KPCuspCharts.toArch_meanHeight F G.positive_dimension]
        exact p.property)
    have hcont_q : ContDiffAt ℝ (⊤ : ℕ∞)
        (v.val ∘ arch (KPCuspLogShape.dimension F))
        (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F q.val)) :=
      representative_smoothAt v _ (by
        rw [KPMeanZeroWeightedEnergy.arch_real_eq, KPCuspCharts.toArch_meanHeight F G.positive_dimension]
        exact q.property)
    have hc : (fun y : HyperbolicChart.Space (KPCuspLogShape.dimension F) =>
        (v.val ∘ arch (KPCuspLogShape.dimension F))
          (real (KPCuspLogShape.dimension F)
            (KPArch.productAction (KPCuspLogShape.dimension F) g
              (arch (KPCuspLogShape.dimension F) y)))) =ᶠ[nhds
          (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F q.val))]
        (fun y => (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) *
          (v.val ∘ arch (KPCuspLogShape.dimension F)) y) := by
      have harch : ContinuousAt (arch (KPCuspLogShape.dimension F))
          (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F q.val)) :=
        (KPMeanZeroWeightedEnergy.arch_contDiff _).continuous.continuousAt
      have hopen : {z : KPArch.Space (KPCuspLogShape.dimension F) |
          T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z} ∈
          nhds (KPCuspCharts.toArch F q.val) :=
        (isOpen_lt continuous_const (KPMeanZeroWeightedEnergy.meanHeight_contDiff _).continuous).mem_nhds (by
          show T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
            (KPCuspCharts.toArch F q.val)
          rw [KPCuspCharts.toArch_meanHeight F G.positive_dimension]
          exact q.property)
      filter_upwards [harch.eventually hopen] with y hy
      have hys : KPArch.productAction (KPCuspLogShape.dimension F) g
          (arch (KPCuspLogShape.dimension F) y) =
          KPCuspSiegel.action F (s : KPCuspArithmetic.PGL2 F)
            (arch (KPCuspLogShape.dimension F) y) := by
        rw [← hA, KPCuspSiegel.action_mk]
        rfl
      simp only [Function.comp_apply, KPMeanZeroWeightedEnergy.arch_real_eq]
      rw [hys]
      exact v.equivariant s (arch (KPCuspLogShape.dimension F) y) hy
    have hkey := laplacian_action_invariant (KPCuspLogShape.dimension F) g
      (v.val ∘ arch (KPCuspLogShape.dimension F))
      (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F q.val))
      (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) hc hcont_q
      (by rw [KPMeanZeroWeightedEnergy.arch_real_eq, hs']; exact hcont_p)
    have hlap : v.laplacian p.val =
        (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) * v.laplacian q.val := by
      have h := hkey
      rw [KPMeanZeroWeightedEnergy.arch_real_eq, hs'] at h
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
      rw [Complex.star_def, Complex.conj_mul', character_norm (ζ := ζ) (hζ := hζ) (ρ s)]
      norm_num
    calc (star (v.scalar p.val) * v.laplacian p.val).re
        = (star ((KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) * v.scalar q.val) *
            ((KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) * v.laplacian q.val)).re := by
          rw [hsc, hlap]
      _ = (star (v.scalar q.val) * v.laplacian q.val).re := by
          congr 1
          calc star ((KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) * v.scalar q.val) *
                ((KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) * v.laplacian q.val)
              = (star (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) *
                  (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ)) *
                  (star (v.scalar q.val) * v.laplacian q.val) := by
                rw [star_mul]
                ring
            _ = star (v.scalar q.val) * v.laplacian q.val := by rw [hcc, one_mul]

end DedekindZetaZeroFree.KPCompactGreenRadialIntegrability

end
