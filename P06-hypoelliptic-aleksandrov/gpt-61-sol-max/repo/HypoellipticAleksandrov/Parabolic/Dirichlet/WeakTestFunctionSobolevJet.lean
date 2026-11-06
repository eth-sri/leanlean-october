module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolev

/-!
# Sobolev jets of bundled spatial test functions

This module records the almost-everywhere representative identities for the
canonical inclusion of bundled smooth compactly supported test functions into
the Hilbert realization of spatial `H¹₀`.
-/

 public section


open scoped ENNReal



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The value cofunction of a bundled smooth compactly supported test
function agrees almost everywhere with its literal function after canonical
inclusion into the Hilbert `H¹₀` graph. -/
theorem ae_valueCLM_smoothCompactlySupportedH1HilbertGraph
    {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω)
    (ψ : PDE.WeakTestFunction Ω) :
    (fun y => valueCLM hΩ
      (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ) y)
      =ᵐ[PDE.volumeOn Ω] ψ := (id
  (id
    (PDE.W1pFunction.coeFn_toW1pGraph_fst
      (PDE.W1pFunction.ofContDiff hΩ
        (ContDiff.of_le ψ.contDiff
          (of_eq_true
            (Eq.trans WithTop.le_coe_top._simp_1
              (Eq.trans (congrArg Not WithTop.one_ne_top._simp_2) not_false_eq_true))))
        ψ.hasCompactSupport 2))))

/-- Each gradient-coordinate cofunction of a bundled smooth compactly
supported test function agrees almost everywhere with its literal derivative
after canonical inclusion into the Hilbert `H¹₀` graph. -/
theorem ae_gradientCoordCLM_smoothCompactlySupportedH1HilbertGraph
    {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω)
    (ψ : PDE.WeakTestFunction Ω) (j : Fin d) :
    (fun y => gradientCLM hΩ
      (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ) y j)
      =ᵐ[PDE.volumeOn Ω] fun y => ψ.partialDeriv j y := (id
  (id
    (PDE.W1pFunction.coeFn_toW1pGraph_snd_apply
      (PDE.W1pFunction.ofContDiff hΩ
        (ContDiff.of_le ψ.contDiff
          (of_eq_true
            (Eq.trans WithTop.le_coe_top._simp_1
              (Eq.trans (congrArg Not WithTop.one_ne_top._simp_2) not_false_eq_true))))
        ψ.hasCompactSupport 2)
      j)))

end HypoellipticAleksandrov.Parabolic.Dirichlet
