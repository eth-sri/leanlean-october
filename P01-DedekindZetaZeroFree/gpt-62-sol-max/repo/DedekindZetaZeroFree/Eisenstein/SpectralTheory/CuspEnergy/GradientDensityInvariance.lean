module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspEnergy.GreenPairing

public import DedekindZetaZeroFree.Geometry.Hyperbolic.Cotangent.DifferentialCoframe

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSections.ChartEllipticity

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

open HyperbolicChart (differential_smoothAt)

private theorem representative_smoothAt (v : Representative ζ hζ S ρ V T)
    (x : Space (KPCuspLogShape.dimension F))
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

private theorem chart_height (G : KPCuspCharts.ChartOutput F hF S D)
    (p : KPCuspCharts.Coordinates F) :
    KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F)
        (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p))) = p.2 := by
  rw [KPMeanZeroWeightedEnergy.arch_real_eq, KPCuspCharts.toArch_meanHeight F G.positive_dimension]

private theorem gradientSq_continuousOn (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) :
    ContinuousOn v.gradientSq {p | T < p.2} := by
  apply continuousOn_of_forall_continuousAt
  intro p hp
  have hv := representative_smoothAt v _ (by rwa [chart_height G p])
  apply tendsto_finsetSum
  intro i hi
  apply tendsto_finsetSum
  intro k hk
  exact (((differential_smoothAt _ _ _ hv i k).continuousAt.comp
    (f := fun p : KPCuspCharts.Coordinates F => real _ (KPCuspCharts.toArch F p))
    chart_smooth.continuous.continuousAt).norm.pow 2)

open KPLocalizedFormGraph.ChartEnergyGeometry (realAction differential_invariant)

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
  change KPCuspSiegel.action F (s : KPCuspArithmetic.PGL2 F)
    (KPCuspCharts.toArch F q.val) = KPCuspCharts.toArch F p.val at hs
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective (s : KPCuspArithmetic.PGL2 F)
  let d := KPCuspLogShape.dimension F
  let a : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ := fun i =>
    Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding A
  let x := real d (KPCuspCharts.toArch F q.val)
  let y := real d (KPCuspCharts.toArch F p.val)
  let g := v.val ∘ arch d
  have ha (z : KPArch.Space d) : KPArch.productAction d a z =
      KPCuspSiegel.action F (s : KPCuspArithmetic.PGL2 F) z := by
    rw [← hA, KPCuspSiegel.action_mk]
    rfl
  have hy : realAction d a x = y := by
    change real d (KPArch.productAction d a (arch d (real d _))) = _
    rw [KPMeanZeroWeightedEnergy.arch_real_eq, ha, hs]
  have hx : T < KPCuspLogShape.meanHeight d (arch d x) := by
    exact (chart_height G q.val).symm ▸ q.property
  have hyp : T < KPCuspLogShape.meanHeight d (arch d y) := by
    exact (chart_height G p.val).symm ▸ p.property
  have hg : DifferentiableAt ℝ g x :=
    (representative_smoothAt v x hx).differentiableAt (by simp)
  have hgy : DifferentiableAt ℝ g (realAction d a x) := by
    rw [hy]
    exact (representative_smoothAt v y hyp).differentiableAt (by simp)
  have heq : (g ∘ realAction d a) =ᶠ[nhds x]
      fun z => (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) * g z := by
    have hopen : IsOpen {z : Space d | T < KPCuspLogShape.meanHeight d (arch d z)} :=
      isOpen_lt continuous_const ((KPMeanZeroWeightedEnergy.meanHeight_contDiff d).continuous.comp (KPMeanZeroWeightedEnergy.arch_contDiff d).continuous)
    filter_upwards [hopen.mem_nhds hx] with z hz
    change v.val (arch d (real d (KPArch.productAction d a (arch d z)))) = _
    rw [KPMeanZeroWeightedEnergy.arch_real_eq, ha]
    exact v.equivariant s (arch d z) hz
  have hc : ‖(KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ)‖ = 1 := by
    apply IsOfFinOrder.norm_eq_one
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨3, by decide, ?_⟩
    have hp : ρ s ^ 3 = 1 := by
      apply Subtype.ext
      exact (mem_rootsOfUnity 3 _).mp (ρ s).property
    simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg (fun z => (KPCuspGenuineMonodromy.chi F ζ hζ z : ℂ)) hp
  have hh := differential_invariant d a g x
    (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) hg hgy heq hc
  rw [hy] at hh
  exact hh

end DedekindZetaZeroFree.KPCompactGreenRadialIntegrability

end
