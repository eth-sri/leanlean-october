module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.CutoffPiBernsteinSpatialFactor
public import HypoellipticAleksandrov.Parabolic.Dirichlet.FiniteSeparatedSpacetimeTest
public import HypoellipticAleksandrov.Parabolic.Dirichlet.PiBernsteinCore
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SampledTimeFactor
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Finite separated assembly of cutoff Bernstein sums

This module reindexes product-Bernstein multi-indices by a finite ordinal and packages the
sampled time and cutoff spatial factors as one finite separated spacetime test.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The affine image of the product Bernstein grid in the centered cube. -/
def centeredPiBernsteinGrid {d n : ℕ} (R : ℝ)
    (k : Fin d → Fin (n + 1)) : PDE.Vec d :=
  fun i => R * (2 * (piBernsteinGrid k i : ℝ) - 1)

variable {d n : ℕ}

/-- The sampled, cutoff product-Bernstein sum on the centered cube. -/
def cutoffPiBernsteinApproximation  (R : ℝ)
    (χ : PDE.ScalarField d) (f : HypoellipticAleksandrov.Parabolic.ScalarField d) :
    HypoellipticAleksandrov.Parabolic.ScalarField d :=
  fun z => χ z.2 * ∑ k : Fin d → Fin (n + 1),
    (∏ i : Fin d,
      (bernsteinPolynomial ℝ n (k i)).eval (((z.2 i / R) + 1) / 2)) *
      f (z.1, centeredPiBernsteinGrid R k)

/-- The sampled cutoff Bernstein sum and its literal time derivative have a finite separated
representation whose factors share the prescribed compact product support. -/
theorem exists_finiteSeparatedSpacetimeTest_cutoffPiBernstein
     {τ₁ τ₂ : ℝ} {O : PDE.VelocityRegion d} (hO : IsOpen O)
    (φ : TestFunction (originalTimeOpenCylinderOpens τ₁ τ₂ O hO) ℝ (⊤ ))
    (χ : PDE.ScalarField d) (hχ : ContDiff ℝ PDE.smoothOrder χ)
    (hχcompact : IsCompact (tsupport χ)) (hχO : tsupport χ ⊆ O)
    (R : ℝ) (hR : 0 < R) :
    ∃ q : FiniteSeparatedSpacetimeTest τ₁ τ₂ O,
      q.toFun = cutoffPiBernsteinApproximation (n := n) R χ φ ∧
      q.timeDeriv =
        cutoffPiBernsteinApproximation (n := n) R χ (timeDerivative φ) ∧
      ∀ m,
        tsupport ((q.timeFactor m ) : ℝ → ℝ) ×ˢ
            tsupport ((q.spatialFactor m ) : PDE.ScalarField d) ⊆
          (spacetimeTestTimeSupportCompact φ : Set ℝ) ×ˢ tsupport χ := by
  let ι := Fin d → Fin (n + 1)
  let e  := Fintype.equivFin ι
  let η : ι → OriginalTimeScalarTest τ₁ τ₂ := fun k =>
    (exists_sampledTimeFactor φ (centeredPiBernsteinGrid R k)).choose
  have hη (k : ι) :=
    (exists_sampledTimeFactor φ (centeredPiBernsteinGrid R k)).choose_spec
  let ψ : ι → PDE.WeakTestFunction O := fun k =>
    (exists_cutoffPiBernsteinSpatialFactor χ hχ hχcompact hχO R hR k).choose
  have hψ (k : ι) :=
    (exists_cutoffPiBernsteinSpatialFactor χ hχ hχcompact hχO R hR k).choose_spec
  let q : FiniteSeparatedSpacetimeTest τ₁ τ₂ O :=
    { termCount := Fintype.card ι
      timeFactor := fun m => η (e.symm m)
      spatialFactor := fun m => ψ (e.symm m) }
  refine ⟨q, ?_, ?_, ?_⟩
  · funext z
    unfold FiniteSeparatedSpacetimeTest.toFun cutoffPiBernsteinApproximation
    change (∑ m : Fin (Fintype.card ι),
      η (e.symm m) z.1 * ψ (e.symm m) z.2) = _
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv e.symm _ _ ?_
    intro m
    rw [(hη (e.symm m)).1, (hψ (e.symm m)).1]
    ring
  · funext z
    unfold FiniteSeparatedSpacetimeTest.timeDeriv cutoffPiBernsteinApproximation
    change (∑ m : Fin (Fintype.card ι),
      (η (e.symm m)).deriv z.1 * ψ (e.symm m) z.2) = _
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv e.symm _ _ ?_
    intro m
    rw [(hη (e.symm m)).2.1, (hψ (e.symm m)).1]
    ring
  · intro m z hz
    exact ⟨(hη (e.symm m)).2.2 hz.1, (hψ (e.symm m)).2 hz.2⟩

end HypoellipticAleksandrov.Parabolic.Dirichlet
