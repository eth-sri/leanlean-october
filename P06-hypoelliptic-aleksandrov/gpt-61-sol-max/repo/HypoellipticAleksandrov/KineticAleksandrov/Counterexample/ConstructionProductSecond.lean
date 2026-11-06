module

public import PDEFoundation.Sobolev.WeakDerivative.Product
public import PDEFoundation.Sobolev.WeakDerivative.Algebra
public import PDEFoundation.Calculus.RegularityOrder


/-! # Second weak product rule with the same first representatives -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory

/-- Multiplication by a smooth function preserves a prescribed second weak derivative.
The two first representatives are the ones appearing in both weak identities. -/
theorem construction_weak_second_product {n : ℕ} {D : PDE.VelocityRegion n}
    (u gi gk hik phi : PDE.ScalarField n) (i k : Fin n)
    (hu : PDE.HasWeakPartialDerivOn D i u gi)
    (hg : PDE.HasWeakPartialDerivOn D i gk hik)
    (hphi : ContDiff ℝ PDE.smoothOrder phi)
    (huL : LocallyIntegrable u (PDE.volumeOn D))
    (hgiL : LocallyIntegrable gi (PDE.volumeOn D))
    (hgkL : LocallyIntegrable gk (PDE.volumeOn D))
    (hhL : LocallyIntegrable hik (PDE.volumeOn D)) :
    PDE.HasWeakPartialDerivOn D i
      (fun x => phi x * gk x + u x * fderiv ℝ phi x (PDE.basisVec k))
      (fun x => phi x * hik x + gk x * fderiv ℝ phi x (PDE.basisVec i) +
        fderiv ℝ phi x (PDE.basisVec k) * gi x +
        u x * fderiv ℝ (fun y => fderiv ℝ phi y (PDE.basisVec k)) x
          (PDE.basisVec i)) := by
  let dk := fun x => fderiv ℝ phi x (PDE.basisVec k)
  let di := fun x => fderiv ℝ phi x (PDE.basisVec i)
  have hdk : ContDiff ℝ PDE.smoothOrder dk :=
    (hphi.contDiff_fderiv_apply (by simp)).comp (contDiff_id.prodMk contDiff_const)








  have he := (hg.mul_contDiff hphi hgkL hhL).add (hu.mul_contDiff hdk huL hgiL) (hgkL.continuous_mul hphi.continuous) (huL.continuous_mul hdk.continuous) ((hhL.continuous_mul hphi.continuous).add (hgkL.mul_continuous ((hphi.continuous_fderiv (by simp)).clm_apply continuous_const))) ((hgiL.continuous_mul hdk.continuous).add (huL.mul_continuous ((hdk.continuous_fderiv (by simp)).clm_apply continuous_const)))
  have hv : (fun x => phi x * gk x + dk x * u x) =
      (fun x => phi x * gk x + u x * fderiv ℝ phi x (PDE.basisVec k)) := by
    funext x
    dsimp only [dk]
    rw [mul_comm (fderiv ℝ phi x (PDE.basisVec k))]
  change PDE.HasWeakPartialDerivOn D i
    (fun x => phi x * gk x + dk x * u x)
    (fun x => (phi x * hik x + gk x * di x) +
      (dk x * gi x + u x * fderiv ℝ dk x (PDE.basisVec i))) at he
  rw [hv] at he
  simpa only [dk, di, add_assoc] using! he

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
