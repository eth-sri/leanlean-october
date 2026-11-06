module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import RequestProject.LocalConformalH1
public import RequestProject.SmoothCompactExtension
public import RequestProject.RiemannMappingInterior

/-!
# Finite energy of the actual interior Riemann map

Only holomorphicity and injectivity on the open disk are used below.
The area change of variables gives an integrable squared derivative for
a bounded image. Bounded values and those derivatives give an element
of the actual weak-gradient H¹ space. Integration by parts is localized
near each compact interior test support; no closed-disk continuity or
extension across the circle is an input or a conclusion.

The complex Dirichlet energy is the area of the image. The sum of the
two real gradient energies is twice that area.
-/

@[expose] public section


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology ENNReal ContDiff

/-- Local smoothness suffices for the actual weak-gradient identities:
each test is supported in a compact subset of the open domain. -/
theorem isWeakGradient_of_contDiffOn {U : Set ℂ} (hU : IsOpen U) 
    (hFs : ContDiffOn ℝ ∞ F U)
    (hu : MemLp F 2 (volume.restrict U))
    (hg : ∀ i : Fin 2, MemLp (fun z => fderiv ℝ F z (coordDir i)) 2
      (volume.restrict U)) :
    IsWeakGradient U (hu.toLp F) (fun i => (hg i).toLp _) := by
  intro φ hφ i
  obtain ⟨G, hG, hGF⟩ := exists_smooth_compact_extension
    hφ.2.1 hU hφ.2.2 hFs
  have hGu : MemLp G 2 (volume.restrict U) := hG.memLp' 2
  have hGg : ∀ j : Fin 2, MemLp (fun z => fderiv ℝ G z (coordDir j)) 2
      (volume.restrict U) := fun j => (hG.dirD (coordDir j)).memLp' 2
  have hweak := isWeakGradient_of_smooth hG.1 hGu hGg φ hφ i
  rw [integral_congr_ae (show (fun z => (hGu.toLp G : L2 U) z * fderiv ℝ φ z (coordDir i)) =ᵐ[volume.restrict U] fun z => F z * fderiv ℝ φ z (coordDir i) by
    filter_upwards [hGu.coeFn_toLp] with z hz
    rw [hz]
    by_cases hzs : z ∈ tsupport φ
    · rw [(hGF z hzs).self_of_nhds]
    · simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) hzs]), integral_congr_ae (show (fun z => ((hGg i).toLp _ : L2 U) z * φ z) =ᵐ[volume.restrict U] fun z => fderiv ℝ F z (coordDir i) * φ z by
    filter_upwards [(hGg i).coeFn_toLp] with z hz
    rw [hz]
    by_cases hzs : z ∈ tsupport φ
    · rw [(hGF z hzs).fderiv_eq (𝕜 := ℝ)]
    · simp [image_eq_zero_of_notMem_tsupport hzs])] at hweak
  rw [integral_congr_ae (by
    filter_upwards [hu.coeFn_toLp] with z hz
    rw [hz]), integral_congr_ae (show (fun z => ((hg i).toLp _ : L2 U) z * φ z) =ᵐ[volume.restrict U] fun z => fderiv ℝ F z (coordDir i) * φ z by
    filter_upwards [(hg i).coeFn_toLp] with z hz
    rw [hz])]
  exact hweak

/-- Bounded image makes the area weight genuinely integrable. -/
theorem interiorConformal_deriv_sq_integrable (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1))
    (hb : Bornology.IsBounded (F '' ball 0 1)) :
    IntegrableOn (fun z => ‖deriv F z‖ ^ 2) (ball 0 1) := by
  have hconst : IntegrableOn (fun _ : ℂ => (1 : ℝ)) (F '' ball 0 1) :=
    integrableOn_const hb.measure_lt_top.ne
  simpa using localConformal_integrable_weight isOpen_ball hF hinj hconst

end PolyaNeumann

end
