module

public import PDEFoundation.Sobolev.W1p.EuclideanGradient
public import PDEFoundation.Sobolev.W1p.Graph
public import PDEFoundation.Measure.FiniteVectorConvergence

@[expose] public noncomputable section

namespace PDE
open MeasureTheory Filter
open scoped ENNReal Topology


/-- The quotient `L^p` value-gradient pair associated with concrete
representatives. -/
def weakGradientLpPairOfRepresentatives
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemLpOn U p u) (hDu : GradMemLpOn U p Du) :
    WeakGradientLpPair U p :=
  (hu.toScalarLp, hDu.toHilbertVectorLp)

/-- The value component of
`PDE.weakGradientLpPairOfRepresentatives` has the original representative. -/
theorem coeFn_weakGradientLpPairOfRepresentatives_fst
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemLpOn U p u) (hDu : GradMemLpOn U p Du) :
    ⇑(weakGradientLpPairOfRepresentatives hu hDu).1
      =ᵐ[volumeOn U] u :=
  hu.coeFn_toScalarLp


/-- Coordinatewise a.e. representative identity for the gradient component
of `PDE.weakGradientLpPairOfRepresentatives`. -/
theorem coeFn_weakGradientLpPairOfRepresentatives_snd_apply
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemLpOn U p u) (hDu : GradMemLpOn U p Du)
    (i : Fin d) :
    (fun x => (weakGradientLpPairOfRepresentatives hu hDu).2 x i)
      =ᵐ[volumeOn U] fun x => Du x i :=
  hDu.coeFn_toHilbertVectorLp_apply i

/-- Concrete weak-gradient representatives determine an element of the
closed weak-gradient graph. -/
theorem weakGradientLpPairOfRepresentatives_mem_weakGradientGraph
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    [Fact (1 ≤ p)]
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemLpOn U p u) (hDu : GradMemLpOn U p Du)
    (hweak : HasWeakGradientOn U u Du) :
    weakGradientLpPairOfRepresentatives hu hDu ∈
      weakGradientGraph U p := by
  rw [mem_weakGradientGraph_iff_integral]
  intro i φ
  have hvalueIntegral :
      (∫ x,
          (weakGradientLpPairOfRepresentatives hu hDu).1 x *
            φ.partialDeriv i x ∂(volumeOn U)) =
        ∫ x, u x * φ.partialDeriv i x ∂(volumeOn U) := by
    apply integral_congr_ae
    filter_upwards
      [coeFn_weakGradientLpPairOfRepresentatives_fst hu hDu]
      with x hx
    rw [hx]
  have hgradIntegral :
      (∫ x,
          (weakGradientLpPairOfRepresentatives hu hDu).2 x i *
            φ x ∂(volumeOn U)) =
        ∫ x, Du x i * φ x ∂(volumeOn U) := by
    apply integral_congr_ae
    filter_upwards
      [coeFn_weakGradientLpPairOfRepresentatives_snd_apply hu hDu i]
      with x hx
    rw [hx]
  have hweakTest :
      (∫ x, u x * φ.partialDeriv i x ∂(volumeOn U)) =
        -∫ x, Du x i * φ x ∂(volumeOn U) := by
    exact
      (hasWeakPartialDerivOn_iff_forall_testFunction.mp
        (hweak i)) φ
  rw [hvalueIntegral, hgradIntegral]
  exact eq_neg_iff_add_eq_zero.mp hweakTest

/-- Membership of a representative pair in the closed weak-gradient graph
recovers the raw distributional weak-gradient identity.  Together with
`weakGradientLpPairOfRepresentatives_mem_weakGradientGraph`, this is the exact
bridge between representative-level weak derivatives and the quotient
closed-graph carrier. -/
theorem hasWeakGradientOn_of_weakGradientLpPairOfRepresentatives_mem
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    [Fact (1 ≤ p)]
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemLpOn U p u) (hDu : GradMemLpOn U p Du)
    (hmem :
      weakGradientLpPairOfRepresentatives hu hDu ∈
        weakGradientGraph U p) :
    HasWeakGradientOn U u Du := by
  intro i
  rw [hasWeakPartialDerivOn_iff_forall_testFunction]
  intro φ
  have hconstraint :=
    (mem_weakGradientGraph_iff_integral
      (weakGradientLpPairOfRepresentatives hu hDu)).mp
      hmem i φ
  have hvalueIntegral :
      (∫ x,
          (weakGradientLpPairOfRepresentatives hu hDu).1 x *
            φ.partialDeriv i x ∂(volumeOn U)) =
        ∫ x, u x * φ.partialDeriv i x ∂(volumeOn U) := by
    apply integral_congr_ae
    filter_upwards
      [coeFn_weakGradientLpPairOfRepresentatives_fst hu hDu]
      with x hx
    rw [hx]
  have hgradIntegral :
      (∫ x,
          (weakGradientLpPairOfRepresentatives hu hDu).2 x i *
            φ x ∂(volumeOn U)) =
        ∫ x, Du x i * φ x ∂(volumeOn U) := by
    apply integral_congr_ae
    filter_upwards
      [coeFn_weakGradientLpPairOfRepresentatives_snd_apply
        hu hDu i]
      with x hx
    rw [hx]
  rw [hvalueIntegral, hgradIntegral] at hconstraint
  exact eq_neg_iff_add_eq_zero.mpr hconstraint

/-- Package concrete weak-gradient representatives as an element of the
complete quotient-level `W^{1,p}` graph. -/
def w1pGraphOfRepresentatives
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    [Fact (1 ≤ p)]
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemLpOn U p u) (hDu : GradMemLpOn U p Du)
    (hweak : HasWeakGradientOn U u Du) :
    W1pGraph U p :=
  ⟨weakGradientLpPairOfRepresentatives hu hDu,
    weakGradientLpPairOfRepresentatives_mem_weakGradientGraph
      hu hDu hweak⟩




namespace W1pFunction

/-- Send a concrete representative-level Sobolev function to the complete
closed-graph carrier. -/
def toW1pGraph
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : W1pFunction U p) :
    W1pGraph U p :=
  w1pGraphOfRepresentatives u.memLp u.gradMemLp u.hasWeakGradient

/-- The value component of `PDE.W1pFunction.toW1pGraph` agrees a.e. with the
original concrete value representative. -/
theorem coeFn_toW1pGraph_fst
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : W1pFunction U p) :
    ⇑u.toW1pGraph.1.1 =ᵐ[volumeOn U] u.toFun  := by
  exact coeFn_weakGradientLpPairOfRepresentatives_fst u.memLp u.gradMemLp

/-- The gradient component of `PDE.W1pFunction.toW1pGraph` agrees a.e. with
the Euclidean Hilbert lift of the original native gradient. -/
theorem coeFn_toW1pGraph_snd
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : W1pFunction U p) :
    ⇑u.toW1pGraph.1.2 =ᵐ[volumeOn U] toHilbertVecField u.grad  := by
  exact u.gradMemLp.coeFn_toHilbertVectorLp

/-- Coordinatewise a.e. representative identity for the gradient component
of `PDE.W1pFunction.toW1pGraph`. -/
theorem coeFn_toW1pGraph_snd_apply
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : W1pFunction U p) (i : Fin d) :
    (fun x => u.toW1pGraph.1.2 x i) =ᵐ[volumeOn U]
      fun x => u.grad x i  := by
  exact coeFn_weakGradientLpPairOfRepresentatives_snd_apply u.memLp u.gradMemLp i

end W1pFunction



/-- Weak gradients are closed under value and coordinatewise gradient
convergence in `L^p`, for every exponent `p ≥ 1`. -/
theorem HasWeakGradientOn.of_tendsto_eLpNorm
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    [Fact (1 ≤ p)]
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    {uSeq : ℕ → Vec d → ℝ}
    {DuSeq : ℕ → Vec d → Vec d}
    (hu : MemLpOn U p u) (hDu : GradMemLpOn U p Du)
    (huSeq : ∀ n, MemLpOn U p (uSeq n))
    (hDuSeq : ∀ n, GradMemLpOn U p (DuSeq n))
    (hweak :
      ∀ n, HasWeakGradientOn U (uSeq n) (DuSeq n))
    (hValue :
      Tendsto
        (fun n =>
          eLpNorm (uSeq n - u) p (volumeOn U))
        atTop (𝓝 0))
    (hGradient :
      ∀ i,
        Tendsto
          (fun n =>
            eLpNorm
              (fun x => DuSeq n x i - Du x i)
              p (volumeOn U))
          atTop (𝓝 0)) :
    HasWeakGradientOn U u Du := by
  have hValueLp :
      Tendsto
        (fun n => (huSeq n).toScalarLp)
        atTop (𝓝 hu.toScalarLp) := by
    exact
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        uSeq huSeq u hu).mpr hValue
  have hGradientEuclidean :
      Tendsto
        (fun n =>
          eLpNorm
            (fun x =>
              vecEuclideanNorm (DuSeq n x - Du x))
            p (volumeOn U))
        atTop (𝓝 0) := by
    apply
      tendsto_eLpNorm_vecEuclideanNorm_sub_zero_of_coordinate
        Fact.out
    · intro n i
      exact
        ((hDuSeq n i).aestronglyMeasurable.sub
          (hDu i).aestronglyMeasurable)
    · exact hGradient
  have hGradientHilbert :
      Tendsto
        (fun n =>
          eLpNorm
            (toHilbertVecField (DuSeq n) -
              toHilbertVecField Du)
            p (volumeOn U))
        atTop (𝓝 0) := by
    have hEq : ∀ n,
        eLpNorm (toHilbertVecField fun x => DuSeq n x - Du x) p (volumeOn U) =
          eLpNorm (fun x => vecEuclideanNorm (DuSeq n x - Du x)) p (volumeOn U) :=
      fun n => eLpNorm_toHilbertVecField_eq _ _ _
        (aemeasurable_pi_iff.2 fun i =>
          ((hDuSeq n i).aestronglyMeasurable.sub
            (hDu i).aestronglyMeasurable).aemeasurable).aestronglyMeasurable
    simpa only [toHilbertVecField_sub, hEq] using
      hGradientEuclidean
  have hGradientLp :
      Tendsto
        (fun n => (hDuSeq n).toHilbertVectorLp)
        atTop (𝓝 hDu.toHilbertVectorLp) := by
    exact
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        (fun n => toHilbertVecField (DuSeq n))
        (fun n =>
          gradMemLpOn_iff_memLp_toHilbertVecField.mp
            (hDuSeq n))
        (toHilbertVecField Du)
        (gradMemLpOn_iff_memLp_toHilbertVecField.mp hDu)).mpr
        hGradientHilbert
  have hPair :
      Tendsto
        (fun n =>
          weakGradientLpPairOfRepresentatives
            (huSeq n) (hDuSeq n))
        atTop
        (𝓝
          (weakGradientLpPairOfRepresentatives hu hDu)) := by
    simpa only [weakGradientLpPairOfRepresentatives] using
      hValueLp.prodMk_nhds hGradientLp
  have hPairMem :
      weakGradientLpPairOfRepresentatives hu hDu ∈
        weakGradientGraph U p := by
    exact
      (weakGradientGraph U p).isClosed.mem_of_tendsto
        hPair
        (Eventually.of_forall fun n =>
          weakGradientLpPairOfRepresentatives_mem_weakGradientGraph
            (huSeq n) (hDuSeq n) (hweak n))
  exact
    hasWeakGradientOn_of_weakGradientLpPairOfRepresentatives_mem
      hu hDu hPairMem

end PDE

