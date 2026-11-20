module
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSections.ChartEllipticity

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspEnergy.GreenPairing

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Classical ENNReal

namespace DedekindZetaZeroFree.KPCompactGreenRadialIntegrability
open KPMeanZeroWeightedEnergy HyperbolicChart

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    {ρ : S →* rootsOfUnity 3 F} {V : Submodule ℂ ℂ} {T : ℝ}

private theorem arch_real (d : ℕ) (z : KPArch.Space d) : arch d (real d z) = z := by
  ext i <;> simp [arch, real]

alias GradientDensityInvariance.arch_real := arch_real

private theorem smooth_arch (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (arch d) := by
  apply contDiff_pi.mpr
  intro i
  apply ContDiff.prodMk
  · exact Complex.equivRealProdCLM.symm.contDiff.comp
      ((EuclideanSpace.proj (i, (0 : Fin 3))).contDiff.prodMk
       (EuclideanSpace.proj (i, (1 : Fin 3))).contDiff)
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff

alias GradientDensityInvariance.smooth_arch := smooth_arch

private theorem smooth_real (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (real d) := by
  apply (contDiff_piLp 2).mpr
  intro j
  rcases j with ⟨i, k⟩
  fin_cases k
  · simpa [real, Function.comp_def] using
      Complex.reCLM.contDiff.comp (contDiff_fst.comp (contDiff_apply ℝ KPArch.H3 i))
  · simpa [real, Function.comp_def] using
      Complex.imCLM.contDiff.comp (contDiff_fst.comp (contDiff_apply ℝ KPArch.H3 i))
  · simpa [real, Function.comp_def] using contDiff_snd.comp (contDiff_apply ℝ KPArch.H3 i)

alias GradientDensityInvariance.smooth_real := smooth_real

private theorem smooth_mean (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (KPCuspLogShape.meanHeight d) := by
  unfold KPCuspLogShape.meanHeight
  apply ContDiff.div_const
  apply ContDiff.sum
  intro i hi
  exact contDiff_snd.comp (contDiff_apply ℝ KPArch.H3 i)

alias GradientDensityInvariance.smooth_mean := smooth_mean

private theorem derivative_smoothAt (d : ℕ) (g : Space d → ℂ) (x : Space d)
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) (i : Fin d) (k : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (coordinateDerivative d i k g) x := (hg.fderiv_right (by simp)).clm_apply contDiffAt_const

alias GradientDensityInvariance.derivative_smoothAt := derivative_smoothAt

private theorem differential_smoothAt (d : ℕ) (g : Space d → ℂ) (x : Space d)
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) (i : Fin d) (k : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => differential d g q i k) x := by
  have he : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : Space d => (Real.exp (q (i,2)) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x
      ((EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff.contDiffAt.exp)
  fin_cases k
  · simpa [differential] using derivative_smoothAt d g x hg i 2
  · simpa [differential] using he.mul (derivative_smoothAt d g x hg i 0)
  · simpa [differential] using he.mul (derivative_smoothAt d g x hg i 1)

alias GradientDensityInvariance.differential_smoothAt := differential_smoothAt

private theorem representative_smoothAt (v : Representative ζ hζ S ρ V T)
    (x : Space (KPCuspLogShape.dimension F))
    (hx : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F) x)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (v.val ∘ arch (KPCuspLogShape.dimension F)) x := by
  exact (v.smooth.contDiffAt ((isOpen_lt continuous_const (smooth_mean _).continuous).mem_nhds hx)).comp x (smooth_arch _).contDiffAt

alias GradientDensityInvariance.representative_smoothAt := representative_smoothAt

private theorem chart_smooth : ContDiff ℝ (⊤ : ℕ∞)
    (fun p : KPCuspCharts.Coordinates F =>
      real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p)) :=
  (smooth_real _).comp ((KPCuspCharts.toArch_contDiff F).of_le (by simp))

alias GradientDensityInvariance.chart_smooth := chart_smooth

private theorem chart_height (G : KPCuspCharts.ChartOutput F hF S D)
    (p : KPCuspCharts.Coordinates F) :
    KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F)
        (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p))) = p.2 := by
  rw [arch_real, KPCuspCharts.toArch_meanHeight F G.positive_dimension]

alias GradientDensityInvariance.chart_height := chart_height

private theorem gradientSq_continuousOn (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) :
    ContinuousOn v.gradientSq {p | T < p.2} := by
  apply continuousOn_of_forall_continuousAt
  intro p hp
  apply tendsto_finsetSum
  intro i hi
  apply tendsto_finsetSum
  intro k hk
  exact (((differential_smoothAt _ _ _ (representative_smoothAt v _ (by rwa [chart_height G p])) i k).continuousAt.comp

    chart_smooth.continuous.continuousAt).norm.pow 2)

 def archL (d : ℕ) : Space d →L[ℝ] KPArch.Space d :=
  LinearMap.toContinuousLinearMap {
    toFun := arch d
    map_add' := by intro x y; ext i <;> simp [arch, Complex.add_re, Complex.add_im]; rfl
    map_smul' := by intro a x; ext i : 1; apply Prod.ext <;> simp [arch, Complex.real_smul]; apply Complex.ext <;> simp }
 def realL (d : ℕ) : KPArch.Space d →L[ℝ] Space d :=
  LinearMap.toContinuousLinearMap {
    toFun := real d
    map_add' := by
      intro x y; ext ⟨i,k⟩; fin_cases k <;> simp [real]
    map_smul' := by
      intro a x; ext ⟨i,k⟩; fin_cases k <;> simp [real, Complex.real_smul] }

private lemma arch_real' (d : ℕ) (x : KPArch.Space d) : arch d (real d x) = x := by
  ext i <;> simp [real, arch]

alias GradientDensityInvariance.arch_real' := arch_real'
 section

variable (d : ℕ) (w : Fin d × Fin 3 → ℝ)

def scaleL : Space d →L[ℝ] Space d :=
  LinearMap.toContinuousLinearMap {
    toFun := fun x => WithLp.toLp 2 (fun j => w j * x j)
    map_add' := by intro x y; ext j; simp [mul_add]
    map_smul' := by intro a x; ext j; simp; ring }
private lemma scaleL_apply (z : Space d) (j) :
    scaleL d w z j = w j * z j := rfl

end

alias GradientDensityInvariance.scaleL_apply := scaleL_apply
 def frame (d : ℕ) (x : Space d) : Space d →L[ℝ] Space d :=
  scaleL d (fun j => if j.2 = 2 then 1 else Real.exp (x (j.1, 2)))
 def unframe (d : ℕ) (x : Space d) : Space d →L[ℝ] Space d :=
  scaleL d (fun j => if j.2 = 2 then 1 else (Real.exp (x (j.1, 2)))⁻¹)
private lemma frame_unframe (d : ℕ) (x z : Space d) : frame d x (unframe d x z) = z := by
  ext j
  simp only [frame, unframe, scaleL_apply]
  split_ifs <;> simp [Real.exp_ne_zero, ← mul_assoc]

alias GradientDensityInvariance.frame_unframe := frame_unframe
private lemma metric_frame (d : ℕ) (x z : Space d) :
    KPArch.metric d (arch d x) (arch d (frame d x z)) = ‖z‖ ^ 2 := by apply @DedekindZetaZeroFree.KPLocalizedFormGraph.ChartEnergyGeometry.ChartEllipticity.metric_frame <;> assumption

alias GradientDensityInvariance.metric_frame := metric_frame
private alias sum_norm_basis := DedekindZetaZeroFree.KPLocalizedFormGraph.ChartEnergyGeometry.ChartEllipticity.sum_norm_basis
private lemma metric_unframe (d : ℕ) (x z : Space d) :
    ‖unframe d x z‖ ^ 2 = KPArch.metric d (arch d x) (arch d z) := by
  rw [← metric_frame d x (unframe d x z), frame_unframe]

alias GradientDensityInvariance.metric_unframe := metric_unframe
private lemma transport_sum (d : ℕ) (x y : Space d) (J : Space d →L[ℝ] Space d)
    (hm : ∀ z, KPArch.metric d (arch d y) (arch d (J z)) =
      KPArch.metric d (arch d x) (arch d z)) (L : Space d →L[ℝ] ℂ) :
    (∑ j, ‖L (J (frame d x (EuclideanSpace.basisFun (Fin d × Fin 3) ℝ j)))‖ ^ 2) =
      ∑ j, ‖L (frame d y (EuclideanSpace.basisFun (Fin d × Fin 3) ℝ j))‖ ^ 2 := by apply @DedekindZetaZeroFree.KPLocalizedFormGraph.ChartEnergyGeometry.transport_sum <;> assumption
private lemma frame_basis (d : ℕ) (x : Space d) (i : Fin d) (k : Fin 3) :
    frame d x (EuclideanSpace.basisFun (Fin d × Fin 3) ℝ (i,k)) =
      (if k = 2 then 1 else Real.exp (x (i,2))) • coordinateVector d i k := by apply @DedekindZetaZeroFree.KPLocalizedFormGraph.ChartEnergyGeometry.ChartEllipticity.frame_basis <;> assumption

alias GradientDensityInvariance.frame_basis := frame_basis
private lemma differential_sum (d : ℕ) (g : Space d → ℂ) (x : Space d) :
    (∑ i, ∑ k, ‖differential d g x i k‖ ^ 2) =
      ∑ j, ‖fderiv ℝ g x (frame d x (EuclideanSpace.basisFun (Fin d × Fin 3) ℝ j))‖ ^ 2 := by apply @DedekindZetaZeroFree.KPLocalizedFormGraph.ChartEnergyGeometry.differential_sum <;> assumption
 section

variable (d : ℕ) (a : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ)

def realAction
    (x : Space d) : Space d := real d (KPArch.productAction d a (arch d x))
private lemma realAction_deriv
    (x : Space d) :
    HasFDerivAt (realAction d a)
      ((realL d).comp ((fderiv ℝ (KPArch.productAction d a) (arch d x)).comp (archL d))) x := by apply @DedekindZetaZeroFree.KPLocalizedFormGraph.ChartEnergyGeometry.ChartEllipticity.realAction_deriv <;> assumption
private lemma realAction_metric
    (x z : Space d) :
    KPArch.metric d (arch d (realAction d a x)) (arch d (fderiv ℝ (realAction d a) x z)) =
      KPArch.metric d (arch d x) (arch d z) := by apply @DedekindZetaZeroFree.KPLocalizedFormGraph.ChartEnergyGeometry.ChartEllipticity.realAction_metric <;> assumption
private lemma differential_invariant
    (g : Space d → ℂ) (x : Space d) (c : ℂ)
    (hg : DifferentiableAt ℝ g x) (hy : DifferentiableAt ℝ g (realAction d a x))
    (heq : (g ∘ realAction d a) =ᶠ[nhds x] fun z => c * g z) (hc : ‖c‖ = 1) :
    (∑ i, ∑ k, ‖differential d g (realAction d a x) i k‖ ^ 2) =
      ∑ i, ∑ k, ‖differential d g x i k‖ ^ 2 := by apply @DedekindZetaZeroFree.KPLocalizedFormGraph.ChartEnergyGeometry.differential_invariant <;> assumption

end

theorem gradientSq_continuousOn_and_invariant
    (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) :
    ContinuousOn v.gradientSq {p | T < p.2} ∧
      ∀ p q : {p : KPCuspCharts.Coordinates F // T < p.2},
        KPCuspCharts.highRelation F S T p q →
          v.gradientSq p.val = v.gradientSq q.val := by
  refine ⟨gradientSq_continuousOn G v, ?_⟩
  intro p q hrel
  obtain ⟨s, hs⟩ := hrel
  change KPCuspSiegel.action F s
    (KPCuspCharts.toArch F q.val) = KPCuspCharts.toArch F p.val at hs
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective (s : KPCuspArithmetic.PGL2 F)
  let d := KPCuspLogShape.dimension F
  let a := fun i =>
    Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding A
  let x := real d (KPCuspCharts.toArch F q.val)
  let y := real d (KPCuspCharts.toArch F p.val)
  let g := v.val ∘ arch d
  have ha (z : KPArch.Space d) : KPArch.productAction d a z =
      KPCuspSiegel.action F s z := by
    rw [← hA, KPCuspSiegel.action_mk]
    rfl
  have hy : realAction d a x = y := by
    change real d (KPArch.productAction d a (arch d (real d _))) = _
    rw [arch_real, ha, hs]
  have hx := (chart_height G q.val).symm ▸ q.property
  have heq : (g ∘ realAction d a) =ᶠ[nhds x]
      fun z => (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) * g z := by
    filter_upwards [(isOpen_lt continuous_const ((smooth_mean d).continuous.comp (smooth_arch d).continuous)).mem_nhds hx] with z hz
    change v.val (arch d (real d (KPArch.productAction d a (arch d z)))) = _
    rw [arch_real, ha]
    exact v.equivariant s (arch d z) hz
  have hc : ‖(KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ)‖ = 1 := by
    apply IsOfFinOrder.norm_eq_one
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨3, by decide, ?_⟩
    have hp : ρ s ^ 3 = 1 := by
      apply Subtype.ext
      exact (mem_rootsOfUnity 3 _).mp (ρ s).property
    simpa using
      congrArg (fun z => (KPCuspGenuineMonodromy.chi F ζ hζ z : ℂ)) hp
  have hh := differential_invariant d a g x
    (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) ((representative_smoothAt v x hx).differentiableAt (by simp)) (by
      rw [hy]
      exact (representative_smoothAt v y ((chart_height G p.val).symm ▸ p.property)).differentiableAt (by simp)) heq hc
  rw [hy] at hh
  exact hh

end DedekindZetaZeroFree.KPCompactGreenRadialIntegrability

end
