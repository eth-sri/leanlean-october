module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolev

/-!
# Extensionality of the spatial `H¹₀` value map

The weak-gradient graph has no nontrivial element with zero value component:
weak derivatives are unique almost everywhere on an open domain.  This gives
injectivity of the value map on the closed spatial `H¹₀` carrier.
-/

 public section


open scoped ENNReal



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : PDE.VelocityRegion d}

private theorem weakGradientGraph_snd_eq_of_fst_eq
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hΩ : IsOpen Ω) {q r : PDE.WeakGradientLpPair Ω p}
    (hq : q ∈ (PDE.weakGradientGraph Ω p).toSubmodule)
    (hr : r ∈ (PDE.weakGradientGraph Ω p).toSubmodule)
    (hvalue : q.1 = r.1) :
    q.2 = r.2 := by
  apply MeasureTheory.Lp.ext

  filter_upwards [Filter.eventually_all.2 (by
      intro i

      have hrWeak : PDE.HasWeakPartialDerivOn Ω i
          (fun x => r.1 x) (fun x => r.2 x i) := by
        rw [PDE.hasWeakPartialDerivOn_iff_forall_testFunction]
        intro φ
        exact eq_neg_iff_add_eq_zero.mpr
          ((PDE.mem_weakGradientGraph_iff_integral r).mp hr i φ)
      rw [← hvalue] at hrWeak
      apply PDE.HasWeakPartialDerivOn.ae_eq hΩ
      · exact MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
          ((MeasureTheory.MemLp.ae_eq
            (PDE.coeFn_hilbertVectorLpCoord Ω p i q.2)
            (MeasureTheory.Lp.memLp _)).locallyIntegrable Fact.out)
      · exact MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
          ((MeasureTheory.MemLp.ae_eq
            (PDE.coeFn_hilbertVectorLpCoord Ω p i r.2)
            (MeasureTheory.Lp.memLp _)).locallyIntegrable Fact.out)
      · exact (by
          rw [PDE.hasWeakPartialDerivOn_iff_forall_testFunction]
          intro φ
          exact eq_neg_iff_add_eq_zero.mpr
            ((PDE.mem_weakGradientGraph_iff_integral q).mp hq i φ))
      · exact hrWeak)] with x hx
  exact PiLp.ext hx

private theorem h1HilbertGraph_valueCLM_injective
    (hΩ : IsOpen Ω) :
    Function.Injective (PDE.H1HilbertGraph.valueCLM (U := Ω)) := (fun ⦃z w⦄ hzw =>
  Equiv.injective PDE.H1HilbertGraph.equivH1Graph
    (Subtype.ext (Prod.ext hzw (weakGradientGraph_snd_eq_of_fst_eq hΩ z.toH1Graph.property w.toH1Graph.property hzw))))

/-- Equality of scalar `L²` values determines a spatial `H¹₀` graph point. -/
theorem valueCLM_injective
    {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) :
    Function.Injective (valueCLM hΩ) := (fun ⦃u v⦄ huv => Subtype.ext (h1HilbertGraph_valueCLM_injective hΩ (id huv)))

end HypoellipticAleksandrov.Parabolic.Dirichlet
