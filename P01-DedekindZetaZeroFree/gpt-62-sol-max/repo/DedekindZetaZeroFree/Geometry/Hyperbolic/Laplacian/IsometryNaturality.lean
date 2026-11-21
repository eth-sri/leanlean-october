module

public import DedekindZetaZeroFree.Geometry.Hyperbolic.Laplacian.LogarithmicCoordinates
public import DedekindZetaZeroFree.Geometry.SymmetricSpaces.QuaternionicMobius.LaplacianNaturality

@[expose] public section

noncomputable section
open scoped ContDiff BigOperators
open Filter Topology
namespace DedekindZetaZeroFree.KPContArchLaplacianNaturality
open HyperbolicChart
open KPShift68LaplacianInvariant (act productAction_pullback_at)

private theorem local_bridge (d : ℕ) (f : KPArch.Space d → ℂ) (hf : ContDiff ℝ ∞ f) (x : Space d) :
    KPContActualSphericalFlatStage.localLaplacian d f (CotangentLogCoframe.A d x) =
      laplacian d (f ∘ CotangentLogCoframe.A d) x := by
  have h := KPContArchLaplacianCoordinateBridge.bridge_equiv d d (Equiv.refl _) f hf x
  have ha : (fun k => CotangentLogCoframe.A d x k) = CotangentLogCoframe.A d x := funext (fun _ => rfl)
  have hf' : (fun y => f (fun k => CotangentLogCoframe.A d y k)) = f ∘ CotangentLogCoframe.A d := by
    funext y
    congr 1
  simp only [Equiv.refl_symm, Equiv.refl_apply] at h
  rw [ha, hf'] at h
  exact h

open DedekindZetaZeroFree

theorem localLaplacian_congr {d : ℕ} {f g : KPArch.Space d → ℂ}
    {x : KPArch.Space d} (h : f =ᶠ[nhds x] g) :
    KPContActualSphericalFlatStage.localLaplacian d f x =
      KPContActualSphericalFlatStage.localLaplacian d g x := by
  unfold KPContActualSphericalFlatStage.localLaplacian
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hd : (fun y => ((KPArch.volumeDensity d y * KPContActualSphericalFlatStage.inverseMetricWeight d y i j : ℝ) : ℂ) *
      fderiv ℝ f y (KPContActualSphericalFlatStage.coordinateDirection d i j)) =ᶠ[nhds x]
      (fun y => ((KPArch.volumeDensity d y * KPContActualSphericalFlatStage.inverseMetricWeight d y i j : ℝ) : ℂ) *
      fderiv ℝ g y (KPContActualSphericalFlatStage.coordinateDirection d i j)) := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
    rw [hy]
  rw [hd.fderiv_eq]

theorem localLaplacian_const_mul (d : ℕ) (f : KPArch.Space d → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : KPArch.Space d) (c : ℂ) :
    KPContActualSphericalFlatStage.localLaplacian d (fun y => c * f y) x =
      c * KPContActualSphericalFlatStage.localLaplacian d f x := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by simp)
  have hcf2 : ContDiff ℝ 2 (fun y => c * f y) := contDiff_const.mul hf2
  have he (h : KPArch.Space d → ℂ) (hh : ContDiff ℝ 2 h) :=
    KPContFlatCuspCasimirSpecialization.Δloc_coordinate_expression d h hh x
  change KPContFlatCuspCasimirSpecialization.Δloc d (fun y => c * f y) x = c * KPContFlatCuspCasimirSpecialization.Δloc d f x
  rw [he _ hcf2, he _ hf2, Finset.mul_sum]
  have hd (y : KPArch.Space d) : DifferentiableAt ℝ f y := hf2.differentiable (by norm_num) y
  have hfirst (y : KPArch.Space d) (u : KPArch.Space d) :
      fderiv ℝ (fun y => c * f y) y u = c * fderiv ℝ f y u := by
    rw [fderiv_const_mul (hd y) c]
    rfl
  have hsecond (u : KPArch.Space d) :
      fderiv ℝ (fun y => fderiv ℝ (fun y => c * f y) y u) x u =
        c * fderiv ℝ (fun y => fderiv ℝ f y u) x u := by
    simp_rw [hfirst]
    have hs : DifferentiableAt ℝ (fun y => fderiv ℝ f y u) x := by fun_prop
    rw [fderiv_const_mul hs c]
    rfl
  apply Finset.sum_congr rfl
  intro i _
  simp only [hsecond]
  simp only [hfirst, smul_eq_mul]
  ring

theorem pullback (d : ℕ)
    (g : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (f : KPArch.Space d → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x : KPArch.Space d) :
    KPContActualSphericalFlatStage.localLaplacian d
      (fun y => f (KPArch.productAction d g y)) x =
        KPContActualSphericalFlatStage.localLaplacian d f
          (KPArch.productAction d g x) := by
  let y := (CotangentLogCoframe.A d).symm x
  have ha : CotangentLogCoframe.A d y = x := (CotangentLogCoframe.A d).apply_symm_apply x
  have hb : CotangentLogCoframe.A d (act d g y) = KPArch.productAction d g x := by simp [act,ha]
  have hfg : ContDiff ℝ ∞ (fun y => f (KPArch.productAction d g y)) :=
    hf.comp ((KPArch.productAction_contDiff d g).of_le (show (⊤ : ℕ∞) ≤ (⊤ : ℕ∞ω) from le_top))
  rw [← ha]
  rw [local_bridge d (fun y => f (KPArch.productAction d g y)) hfg]
  rw [ha, ← hb, local_bridge d f hf]
  have he : ((fun y => f (KPArch.productAction d g y)) ∘ CotangentLogCoframe.A d) =
      (f ∘ CotangentLogCoframe.A d) ∘ act d g := by funext z; simp [act,Function.comp_def]
  rw [he]
  exact productAction_pullback_at d g (f ∘ CotangentLogCoframe.A d) y
    (hf.comp (CotangentLogCoframe.A d).contDiff).contDiffAt

theorem equivariant (d : ℕ)
    (g : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (f : KPArch.Space d → ℂ) (x : KPArch.Space d) (c : ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : (fun y => f (KPArch.productAction d g y)) =ᶠ[nhds x]
      fun y => c * f y) :
    KPContActualSphericalFlatStage.localLaplacian d f (KPArch.productAction d g x) =
      c * KPContActualSphericalFlatStage.localLaplacian d f x := by
  have h1 : KPContActualSphericalFlatStage.localLaplacian d
        (fun y => f (KPArch.productAction d g y)) x =
      KPContActualSphericalFlatStage.localLaplacian d f
        (KPArch.productAction d g x) :=
    pullback d g f hf x
  rw [← h1]
  exact (localLaplacian_congr hc).trans (localLaplacian_const_mul d f hf x c)

end DedekindZetaZeroFree.KPContArchLaplacianNaturality

end
