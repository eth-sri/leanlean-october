module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionCompactDerivative
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeRegularityCompact
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # The time derivative of the fixed compact cutoff integral -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory

/-- Differentiating in time acts only on the cutoff, and commutes with its compact integral. -/
theorem construction_deriv_cutoff_integral {d : ℕ} {A : Type*}
    [TopologicalSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A]
    (nu : Measure A) [IsFiniteMeasure nu]
    (y : A → XV d) (hy : Continuous y) (u : A → ℝ) (hu : Continuous u)
    (phi : ContDiffBump (0 : XV d)) (mu R t : ℝ) (q : XV d) :
    deriv (fun s => ∫ a, phi.normed volume (q - y a) * timeCutoffTheta
      (u a - Real.exp (-mu * s) * (2 - PDE.vecNormSq (y a).2 / R ^ 2)) ∂nu) t =
    ∫ a, phi.normed volume (q - y a) *
      deriv (fun s => timeCutoffTheta
        (u a - Real.exp (-mu * s) * (2 - PDE.vecNormSq (y a).2 / R ^ 2))) t ∂nu := by
  let f : ℝ × (XV d × ℝ) → ℝ := fun z =>
    phi.normed volume (q - z.2.1) * timeCutoffTheta
      (z.2.2 - Real.exp (-mu * z.1) * (2 - PDE.vecNormSq z.2.1.2 / R ^ 2))
  have hf : ContDiff ℝ _ f :=
    (phi.contDiff_normed.comp (contDiff_const.sub contDiff_snd.fst)).mul
      (contDiff_timeCutoffTheta.comp (contDiff_snd.snd.sub
        ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst)).mul
          (contDiff_const.sub
            ((PDE.contDiff_vecNormSq.comp contDiff_snd.fst.snd).div_const _)))))
  have he := construction_deriv_compact_parameter nu _ (hy.prodMk hu)
    f hf t
  aesop

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
