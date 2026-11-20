module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftIntegral
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic

/-! # C² compact-parameter integrals of jointly C² functions -/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Joint C² regularity gives spatial C² regularity after compact radius integration. -/
theorem bellman_joint_contDiff_integral {E F A : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A]
    (mu : Measure A) [IsFiniteMeasure mu] {U : Set E} (hU : IsOpen U)
    (radius : A → ℝ) (hr : Continuous radius) (hrp : ∀ a, 0 < radius a)
    (f : E × ℝ → F) (hf : ContDiffOn ℝ 2 f (U ×ˢ Ioi 0)) :
    ContDiffOn ℝ 2 (fun q => ∫ a, f (q, radius a) ∂mu) U := by
  let g := bellmanSpatialJet f
  let g' := bellmanSpatialJet g
  have hopen : IsOpen (U ×ˢ Ioi (0 : ℝ)) := hU.prod isOpen_Ioi
  have hg : ContDiffOn ℝ 1 g (U ×ˢ Ioi 0) :=
    contDiffOn_bellmanSpatialJet hopen hf (by norm_num)
  have hg' : ContinuousOn g' (U ×ˢ Ioi 0) :=
    (contDiffOn_bellmanSpatialJet (m := 0) hopen hg (by norm_num)).continuousOn
  have hmap : MapsTo (fun w : E × A => (w.1, radius w.2))
      (U ×ˢ univ) (U ×ˢ Ioi 0) := fun w hw => ⟨hw.1, hrp w.2⟩
  have hcm : Continuous (fun w : E × A => (w.1, radius w.2)) :=
    continuous_fst.prodMk (hr.comp continuous_snd)
  have hn (q) (hq : q ∈ U) (a : A) : U ×ˢ Ioi (0 : ℝ) ∈ 𝓝 (q, radius a) :=
    hopen.mem_nhds ⟨hq, hrp a⟩
  exact bellman_compact_parameter_contDiffOn_two mu hU
    (fun q a => f (q, radius a)) (fun q a => g (q, radius a)) (fun q a => g' (q, radius a))
    (hf.continuousOn.comp hcm.continuousOn hmap) (hg.continuousOn.comp hcm.continuousOn hmap)
    (hg'.comp hcm.continuousOn hmap)
    (fun q hq a => hasFDerivAt_bellmanSpatialJet ((hf.differentiableOn (by norm_num)).differentiableAt (hn q hq a)))
    (fun q hq a => hasFDerivAt_bellmanSpatialJet ((hg.differentiableOn (by norm_num)).differentiableAt (hn q hq a)))

end HypoellipticAleksandrov.KineticAleksandrov
