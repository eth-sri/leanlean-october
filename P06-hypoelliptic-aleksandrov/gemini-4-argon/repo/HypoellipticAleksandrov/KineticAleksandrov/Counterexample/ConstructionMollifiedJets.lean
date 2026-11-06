module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionExtensionSecond

/-! # Mollification of the literal zero extension and its selected spatial jets -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory

/- The selected first representative on the native carrier. -/
def constructionExtendedNativeGradient {d alpha}
    (h : CounterProfileStatement d alpha) (r mu R m t : ℝ)
    (q : XV d) (i : Fin (d + d)) : ℝ :=
  constructionExtendedPackedGradient h r mu R m t ((spatialCoordinateCLE d).symm q) i

/- The selected second velocity representative on the native carrier. -/
def constructionExtendedNativeHessian {d alpha}
    (h : CounterProfileStatement d alpha) (r mu R m t : ℝ)
    (q : XV d) (i k : Fin d) : ℝ :=
  constructionExtendedPackedHessian h r mu R m t ((spatialCoordinateCLE d).symm q) i k

/- Spatial convolution differentiates to convolution of the selected first representatives. -/
theorem construction_mollified_first_jet {d } (hd : 1 ≤ d)
    {alpha } (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 ≤ m)
    (t : ℝ) (i : Fin (d + d)) (phi : ContDiffBump (0 : XV d)) (q : XV d) :
    fderiv ℝ (spatialMollify phi (fun y =>
      zeroExtendedProfile (profileFunction h) alpha r mu R ⟨t, y.1, y.2⟩)) q
        (spatialCoordinateCLE d (PDE.basisVec i)) =
      spatialMollify phi (fun y => constructionExtendedNativeGradient h r mu R m t y i) q := by
  have hc := continuous_zeroExtendedProfile_spatial_of_profile h r mu R hr hmu hR hscale
    (fun y hy => (hmargin y hy).trans_lt hm) t
  exact mollify_weak_directional_jet phi _ _ hc.locallyIntegrable _
    (construction_zero_extension_weak_native hd ha ha1 h r mu R m hr hmu hR hm
      hscale hmargin t i) q

/- The first velocity representative differentiates after convolution to the selected Hessian. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
