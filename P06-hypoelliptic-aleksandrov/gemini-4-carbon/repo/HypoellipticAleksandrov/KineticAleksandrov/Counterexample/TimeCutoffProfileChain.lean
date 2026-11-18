module

public import PDEFoundation.Sobolev.W1p.Composition
public import PDEFoundation.Sobolev.W1p.Algebra
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoff
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyWeakCoordinates
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningProfile
import Mathlib.Topology.MetricSpace.ProperSpace
public import PDEFoundation.Sobolev.W1p.ConvexApprox.Density
public import PDEFoundation.Sobolev.WeakDerivative.Product
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Ring
public import PDEFoundation.Sobolev.W1p.Smooth
import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningSourceProfile
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffSecondBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Set Filter
open scoped ENNReal Topology


/-- The fixed Appendix C cutoff has multiplier bound one in the weak chain rule. -/
theorem weakGradient_timeCutoff_sub {n : ℕ} {D : Set (PDE.Vec n)} {p : ℝ≥0∞}
    (hD : PDE.IsOpenBoundedConvexDomain D) (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u B : PDE.W1pFunction D p) :
    PDE.HasWeakGradientOn D
      (fun x => timeCutoffTheta (u.toFun x - B.toFun x))
      (fun x i => deriv timeCutoffTheta (u.toFun x - B.toFun x) *
        (u.grad x i - B.grad x i))  := by
  have weakGradient_cutoff_sub (theta : ℝ → ℝ) (htheta : ContDiff ℝ 1 theta) (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ s, |deriv theta s| ≤ M) :
      PDE.HasWeakGradientOn D
      (fun x => theta (u.toFun x - B.toFun x))
      (fun x i => deriv theta (u.toFun x - B.toFun x) * (u.grad x i - B.grad x i)) := by
    let : Fact (1 ≤ p) := ⟨hp⟩
    simpa using!
      PDE.W1pFunction.hasWeakGradient_comp_contDiff_of_deriv_bounded
        hD hp hpTop (u - B) htheta hM hbound
  apply weakGradient_cutoff_sub timeCutoffTheta
    (contDiff_timeCutoffTheta.of_le (by simp)) 1 zero_le_one
  intro s
  rw [abs_of_nonneg (timeCutoffTheta_deriv_bounds s).1]
  exact (timeCutoffTheta_deriv_bounds s).2


/-- Concatenation of the native position and velocity weak jets in the standard chart. -/
def spatialPackedGradient {d : ℕ} (gx gv : XV d → PDE.Vec d)
    (x : PDE.Vec (d + d)) : PDE.Vec (d + d) :=
  Fin.addCases (gx (spatialCoordinateCLE d x)) (gv (spatialCoordinateCLE d x))

/-- Native weak first jets supply the full weak gradient in the existing Sobolev chart. -/
theorem weakGradient_spatialCoordinate {d : ℕ} (D : Set (PDE.Vec (d + d)))
    (u : XV d → ℝ) (gx gv : XV d → PDE.Vec d)
    (hweak : ∀ test : XV d → ℝ, ContDiff ℝ 2 test → HasCompactSupport test →
      (∀ i, (∫ q, u q * dx test q i) = -(∫ q, gx q i * test q)) ∧
      (∀ i, (∫ q, u q * dv test q i) = -(∫ q, gv q i * test q))) :
    PDE.HasWeakGradientOn D (fun x => u (spatialCoordinateCLE d x))
      (spatialPackedGradient gx gv) := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [spatialPackedGradient, Fin.addCases_left]
    apply weakPartial_on_of_global
    intro test ht hs
    exact weak_directional_spatialCoordinate u (fun q => gx q j)
      (PDE.basisVec j, 0) (PDE.basisVec (Fin.castAdd d j))
      (spatialCoordinate_basis_position j)
      (fun test ht hs => (hweak test (ht.of_le (by simp)) hs).1 j) test ht hs
  · simp only [spatialPackedGradient, Fin.addCases_right]
    apply weakPartial_on_of_global
    intro test ht hs
    exact weak_directional_spatialCoordinate u (fun q => gv q j)
      (0, PDE.basisVec j) (PDE.basisVec (Fin.natAdd d j))
      (spatialCoordinate_basis_velocity j)
      (fun test ht hs => (hweak test (ht.of_le (by simp)) hs).2 j) test ht hs

/-- Compact bounds and measurability imply finite-exponent membership after chart pullback. -/
theorem memLp_spatialCoordinate_of_compact_bound {d : ℕ} {D : Set (PDE.Vec (d + d))}
    (hD : PDE.IsOpenBoundedConvexDomain D) (f : XV d → ℝ) (hf : Measurable f)
    (hb : ∀ K : Set (XV d), IsCompact K → ∃ C : ℝ, ∀ q ∈ K, ‖f q‖ ≤ C)
    (p : ℝ≥0∞) : PDE.MemLpOn D p (fun x => f (spatialCoordinateCLE d x)) := by
  have : IsFiniteMeasure (PDE.volumeOn D) :=
    hD.isBoundedDomain.isFiniteMeasure_volumeOn
  obtain ⟨C, hC⟩ := hb _ (hD.isBoundedDomain.isBounded.isCompact_closure.image (spatialCoordinateCLE d).continuous)
  apply MemLp.of_bound
    (hf.comp (spatialCoordinateCLE d).continuous.measurable).aestronglyMeasurable.restrict C
  filter_upwards [ae_restrict_mem hD.isOpen.measurableSet] with x hx
  exact hC _ ⟨x, subset_closure hx, rfl⟩

/-- The complete upstream source theorem discharges all local Sobolev hypotheses for
its selected value and first jets, including on neighborhoods of the origin. -/
def flatProfileW1p_of_flatProfile_source
    (hflat : ∀ {d : ℕ}, 1 ≤ d → ∀ {alpha : ℝ}, 0 < alpha → alpha < 1 →
      ∀ h : CounterProfileStatement d alpha, ∀ r : ℝ, 0 < r →
        FlatProfileSourceStatement h r)
    {d : ℕ} (hd : 1 ≤ d) {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    {D : Set (PDE.Vec (d + d))} (hD : PDE.IsOpenBoundedConvexDomain D) :
    PDE.W1pFunction D 2 := by
  obtain ⟨hc, hx, hv, _, hb, _, _, _, _, hw, _, _⟩ := hflat hd ha ha1 h r hr
  refine ⟨fun x => selectedFlatProfile h r (spatialCoordinateCLE d x),
    spatialPackedGradient (flatProfilePositionJet h r) (flatProfileVelocityJet h r),
    ?_, ?_, weakGradient_spatialCoordinate D _ _ _ (fun t ht hs =>
      ⟨(hw t ht hs).1, (hw t ht hs).2.1⟩)⟩
  · apply memLp_spatialCoordinate_of_compact_bound hD _ hc.measurable
    intro K hK
    obtain ⟨C, hC⟩ := hK.bddAbove_image hc.norm.continuousOn
    exact ⟨C, fun q hq => hC ⟨q, hq, rfl⟩⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [spatialPackedGradient, Fin.addCases_left]
      apply memLp_spatialCoordinate_of_compact_bound hD _ (measurable_pi_iff.mp hx j)
      intro K hK
      obtain ⟨M, _, hM⟩ := hb K hK
      exact ⟨M, fun q hq => (norm_le_pi_norm _ j).trans (hM q hq).1⟩
    · simp only [spatialPackedGradient, Fin.addCases_right]
      apply memLp_spatialCoordinate_of_compact_bound hD _ (measurable_pi_iff.mp hv j)
      intro K hK
      obtain ⟨M, _, hM⟩ := hb K hK
      exact ⟨M, fun q hq => (norm_le_pi_norm _ j).trans (hM q hq).2.1⟩




/-- Strong `L²` convergence passes scalar pairings with a fixed `L²` function to the limit. -/
theorem integral_pairing_tendsto_of_eLpNorm_two {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (F : ℕ → X → ℝ) (f g : X → ℝ)
    (hF : ∀ n, MemLp (F n) 2 mu) (hf : MemLp f 2 mu) (hg : MemLp g 2 mu)
    (hlim : Tendsto (fun n => eLpNorm (F n - f) 2 mu) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, F n x * g x ∂mu) atTop (𝓝 (∫ x, f x * g x ∂mu)) := by
  have he (a b : X → ℝ) (ha : MemLp a 2 mu) (hb : MemLp b 2 mu) :
      inner ℝ (ha.toLp a) (hb.toLp b) = ∫ x, a x * b x ∂mu := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hx hy
    rw [hx, hy]
    simp only [Real.inner_apply]
  have hi := ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' F hF f hf).2 hlim).inner (𝕜 := ℝ) (tendsto_const_nhds :
    Tendsto (fun _ => hg.toLp g) atTop (𝓝 (hg.toLp g)))
  simpa only [he] using hi

/-- A Sobolev multiplier obeys the weak product rule with a function having only the
specified weak partial derivative. All three products are locally integrable by `L²`.
No smoothness of the multiplier or of the weak derivative representative is assumed. -/
theorem weakPartial_product_sobolev {d : ℕ} {D : Set (PDE.Vec d)}
    (hD : PDE.IsOpenBoundedConvexDomain D) (a : PDE.W1pFunction D 2)
    (i : Fin d) (b Db : PDE.Vec d → ℝ)
    (hb : PDE.MemLpOn D 2 b) (hDb : PDE.MemLpOn D 2 Db)
    (hweak : PDE.HasWeakPartialDerivOn D i b Db) :
    PDE.HasWeakPartialDerivOn D i (fun x => a.toFun x * b x)
      (fun x => a.toFun x * Db x + b x * a.grad x i) := by
  rcases D.eq_empty_or_nonempty with hEmpty | hNonempty
  · subst D
    intro test _ _ _
    simp
  obtain ⟨x0, r, hr, hball⟩ :=
    PDE.exists_metricClosedBall_subset_of_isOpenBoundedConvexDomain hD hNonempty
  let mu := PDE.volumeOn D
  have : IsFiniteMeasure mu := hD.isSobolevRegularDomain.isFiniteMeasure_volumeOn
  let A (n : ℕ) := a.convexApproxSmoothW1p hD (by norm_num) x0 hr n
  have hsmooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (A n).toFun :=
    a.contDiff_convexApproxSmoothW1p_toFun hD (by norm_num) x0 hr n
  have hv := a.tendsto_convexApproxSmoothW1p_toFun_eLpNorm_sub
    hD (by norm_num) (by norm_num) hball hr
  intro test ht hc hsub
  let dt := fun x => fderiv ℝ test x (PDE.basisVec i)
  have hdt : Continuous dt :=
    (ht.continuous_fderiv (by simp)).clm_apply continuous_const
  have top_mem (f : PDE.Vec d → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) :
      MemLp f ∞ mu := by
    obtain ⟨C, hC⟩ := hfc.exists_bound_of_continuous hf
    exact MemLp.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  have htTop := top_mem test ht.continuous hc
  have hdtTop := top_mem dt hdt (hc.fderiv_apply (𝕜 := ℝ) (PDE.basisVec i))
  have hbt : MemLp (fun x => b x * test x) 2 mu := hb.fun_mul htTop
  have hDbt : MemLp (fun x => Db x * test x) 2 mu := hDb.fun_mul htTop
  have hbdt : MemLp (fun x => b x * dt x) 2 mu := hb.fun_mul hdtTop
  have hR2 := integral_pairing_tendsto_of_eLpNorm_two mu
    (fun n x => (A n).grad x i) (fun x => a.grad x i) (fun x => b x * test x)
    (fun n => (A n).gradMemLp i) (a.gradMemLp i) hbt (a.tendsto_convexApproxSmoothW1p_grad_coord_eLpNorm_sub hD (by norm_num) (by norm_num) hball hr i)
  have he (n : ℕ) : (∫ x, (A n).toFun x * (b x * dt x) ∂mu) =
      -((∫ x, (A n).toFun x * (Db x * test x) ∂mu) +
        ∫ x, (A n).grad x i * (b x * test x) ∂mu) := by
    have ha := (hweak.mul_contDiff (hsmooth n) (hb.integrable (by norm_num)).locallyIntegrable (hDb.integrable (by norm_num)).locallyIntegrable) test ht hc hsub
    have h1 : Integrable (fun x => (A n).toFun x * (Db x * test x)) mu :=
      (memLp_one_iff_integrable.mp ((A n).memLp.mul hDbt))
    have h2 : Integrable (fun x => (A n).grad x i * (b x * test x)) mu :=
      (memLp_one_iff_integrable.mp ((A n).gradMemLp i |>.mul hbt))
    have hj : ∀ x, fderiv ℝ (A n).toFun x (PDE.basisVec i) = (A n).grad x i := by
      intro x
      exact (a.convexApproxSmoothW1p_grad_apply hD (by norm_num) x0 hr n x i).symm
    simp_rw [hj] at ha
    rw [← integral_add h1 h2]
    simpa only [mul_add, mul_assoc, mul_comm, mul_left_comm] using! ha
  have heq := tendsto_nhds_unique (integral_pairing_tendsto_of_eLpNorm_two mu (fun n => (A n).toFun) a.toFun (fun x => b x * dt x) (fun n => (A n).memLp) a.memLp hbdt hv) (((integral_pairing_tendsto_of_eLpNorm_two mu (fun n => (A n).toFun) a.toFun (fun x => Db x * test x) (fun n => (A n).memLp) a.memLp hDbt hv).add hR2).neg.congr (fun n => (he n).symm))
  have h1 : Integrable (fun x => a.toFun x * (Db x * test x)) mu :=
    memLp_one_iff_integrable.mp (a.memLp.mul hDbt)
  have h2 : Integrable (fun x => a.grad x i * (b x * test x)) mu :=
    memLp_one_iff_integrable.mp ((a.gradMemLp i).mul hbt)
  change (∫ x, (a.toFun x * b x) * dt x ∂mu) =
    -(∫ x, (a.toFun x * Db x + b x * a.grad x i) * test x ∂mu)
  rw [← integral_add h1 h2] at heq
  simpa only [mul_add, mul_assoc, mul_comm, mul_left_comm] using! heq


/-- The second weak chain rule for a `C²` scalar cutoff of a Sobolev difference.
The prescribed mixed second derivative is genuine Sobolev regularity of that difference. -/
theorem weakSecond_cutoff_sub {d : ℕ} {D : Set (PDE.Vec d)}
    (hD : PDE.IsOpenBoundedConvexDomain D) (u B : PDE.W1pFunction D 2)
    (i k : Fin d) (hess : PDE.Vec d → ℝ) (hhess : PDE.MemLpOn D 2 hess)
    (hweak : PDE.HasWeakPartialDerivOn D i (fun x => u.grad x k - B.grad x k) hess)
    (theta : ℝ → ℝ) (htheta : ContDiff ℝ 2 theta)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ s, |deriv (deriv theta) s| ≤ M) :
    PDE.HasWeakPartialDerivOn D i
      (fun x => deriv theta (u.toFun x - B.toFun x) * (u.grad x k - B.grad x k))
      (fun x => deriv theta (u.toFun x - B.toFun x) * hess x +
        deriv (deriv theta) (u.toFun x - B.toFun x) *
          (u.grad x i - B.grad x i) * (u.grad x k - B.grad x k)) := by
  have : Fact (1 ≤ 2) := ⟨by norm_num⟩
  have hd : ContDiff ℝ 1 (deriv theta) := htheta.deriv'
  let a := (u - B).compContDiffOfDerivBounded hD (by norm_num) (by norm_num)
    hd hM hbound
  have hb :=
    (u.gradMemLp k).sub (B.gradMemLp k)
  have he := weakPartial_product_sobolev hD a i _ hess hb hhess hweak
  convert he using 1
  · funext x
    rfl
  · funext x
    dsimp only [a, PDE.W1pFunction.compContDiffOfDerivBounded,
      PDE.W1pFunction.sub_toFun, PDE.W1pFunction.sub_grad, Pi.sub_apply]
    ring

/-- The second weak chain rule with a smooth subtracted function. Its Sobolev bounds
and weak derivatives are constructed internally on the bounded convex domain. -/
theorem weakSecond_cutoff_sub_smooth {d : ℕ} {D : Set (PDE.Vec d)}
    (hD : PDE.IsOpenBoundedConvexDomain D) (u : PDE.W1pFunction D 2)
    (B : PDE.Vec d → ℝ) (hB : ContDiff ℝ (⊤ : ℕ∞) B) (i k : Fin d)
    (hess : PDE.Vec d → ℝ) (hhess : PDE.MemLpOn D 2 hess)
    (hweak : PDE.HasWeakPartialDerivOn D i (fun x => u.grad x k) hess)
    (theta : ℝ → ℝ) (htheta : ContDiff ℝ 2 theta)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ s, |deriv (deriv theta) s| ≤ M) :
    PDE.HasWeakPartialDerivOn D i
      (fun x => deriv theta (u.toFun x - B x) *
        (u.grad x k - PDE.classicalGradient B x k))
      (fun x => deriv theta (u.toFun x - B x) *
        (hess x - PDE.classicalGradient (fun y => PDE.classicalGradient B y k) x i) +
        deriv (deriv theta) (u.toFun x - B x) *
          (u.grad x i - PDE.classicalGradient B x i) *
          (u.grad x k - PDE.classicalGradient B x k)) := by
  have : IsFiniteMeasure (PDE.volumeOn D) :=
    hD.isBoundedDomain.isFiniteMeasure_volumeOn
  let b := PDE.W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain (p := 2) hD
    (hB.of_le (by simp))
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun x => PDE.classicalGradient B x k) := by
    exact (hB.contDiff_fderiv_apply (by simp)).comp
      (contDiff_id.prodMk contDiff_const)
  let bg := PDE.W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain (p := 2) hD
    (hg.of_le (by simp))
  have hdiff : PDE.HasWeakPartialDerivOn D i
      (fun x => u.grad x k - b.grad x k)
      (fun x => hess x - bg.grad x i) := by
    simpa using!
      hweak.sub (bg.hasWeakPartialDerivOn i)
        ((u.gradMemLp k).integrable (by norm_num)).locallyIntegrable
        (bg.memLp.integrable (by norm_num)).locallyIntegrable
        (hhess.integrable (by norm_num)).locallyIntegrable
        ((bg.gradMemLp i).integrable (by norm_num)).locallyIntegrable
  simpa using!
    weakSecond_cutoff_sub hD u b i k _ (hhess.sub (bg.gradMemLp i)) hdiff theta htheta M hM hbound


/-- The literal velocity barrier in the measure-preserving spatial chart. -/
def spatialPackedBarrier (d : ℕ) (mu R t : ℝ) (x : PDE.Vec (d + d)) : ℝ :=
  barrier mu R ⟨t, (spatialCoordinateCLE d x).1, (spatialCoordinateCLE d x).2⟩

/-- The packed barrier is globally smooth at every finite order. -/
theorem contDiff_spatialPackedBarrier (d : ℕ) (mu R t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (spatialPackedBarrier d mu R t) := by
  simpa only [spatialPackedBarrier, barrier, Function.comp_apply] using!
    (contDiff_const (c := Real.exp (-mu * t))).mul ((contDiff_const (c := 2)).sub
      ((PDE.contDiff_vecNormSq.comp (spatialCoordinateCLE d).contDiff.snd).div_const (R ^ 2)))

/-- The first weak chain rule for the actual cutoff profile. All regularity of the
flattened profile is discharged by the complete published upstream source theorem. -/
theorem weakGradient_timeCutoffProfile_of_flatProfile_source
    (hflat : ∀ {d : ℕ}, 1 ≤ d → ∀ {alpha : ℝ}, 0 < alpha → alpha < 1 →
      ∀ h : CounterProfileStatement d alpha, ∀ r : ℝ, 0 < r →
        FlatProfileSourceStatement h r)
    {d : ℕ} (hd : 1 ≤ d) {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    {D : Set (PDE.Vec (d + d))} (hD : PDE.IsOpenBoundedConvexDomain D)
    (mu R t : ℝ) :
    PDE.HasWeakGradientOn D
      (fun x => timeCutoffTheta
        (selectedFlatProfile h r (spatialCoordinateCLE d x) - spatialPackedBarrier d mu R t x))
      (fun x i => deriv timeCutoffTheta
        (selectedFlatProfile h r (spatialCoordinateCLE d x) - spatialPackedBarrier d mu R t x) *
        (spatialPackedGradient (flatProfilePositionJet h r) (flatProfileVelocityJet h r) x i -
          PDE.classicalGradient (spatialPackedBarrier d mu R t) x i)) := by
  let u := flatProfileW1p_of_flatProfile_source hflat hd ha ha1 h r hr hD
  let B := PDE.W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain (p := 2) hD
    ((contDiff_spatialPackedBarrier d mu R t).of_le (by simp))
  simpa only [u, B, flatProfileW1p_of_flatProfile_source,
    PDE.W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
    PDE.W1pFunction.ofContDiffOnIsSobolevRegularDomain] using!
    weakGradient_timeCutoff_sub hD (by norm_num) (by norm_num) u B

/-- The actual velocity Hessian chain rule for the cutoff profile, proved using the
same first and second upstream weak representatives and the smooth barrier. -/
theorem weakSecond_timeCutoffProfile_of_flatProfile_source
    (hflat : ∀ {d : ℕ}, 1 ≤ d → ∀ {alpha : ℝ}, 0 < alpha → alpha < 1 →
      ∀ h : CounterProfileStatement d alpha, ∀ r : ℝ, 0 < r →
        FlatProfileSourceStatement h r)
    {d : ℕ} (hd : 1 ≤ d) {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    {D : Set (PDE.Vec (d + d))} (hD : PDE.IsOpenBoundedConvexDomain D)
    (mu R t : ℝ) (i k : Fin d) :
    let u := fun x => selectedFlatProfile h r (spatialCoordinateCLE d x)
    let B := spatialPackedBarrier d mu R t
    let gv := fun x j => flatProfileVelocityJet h r (spatialCoordinateCLE d x) j -
      PDE.classicalGradient B x (Fin.natAdd d j)
    PDE.HasWeakPartialDerivOn D (Fin.natAdd d i)
      (fun x => deriv timeCutoffTheta (u x - B x) * gv x k)
      (fun x => deriv timeCutoffTheta (u x - B x) *
        (flatProfileHessian h r (spatialCoordinateCLE d x) i k -
          PDE.classicalGradient
            (fun y => PDE.classicalGradient B y (Fin.natAdd d k)) x (Fin.natAdd d i)) +
        deriv (deriv timeCutoffTheta) (u x - B x) * gv x i * gv x k)   := by
  have memLp_flatProfileHessian_spatialCoordinate_of_flatProfile_source (hflat : ∀ {d : ℕ}, 1 ≤ d → ∀ {alpha : ℝ}, 0 < alpha → alpha < 1 →
      ∀ h : CounterProfileStatement d alpha, ∀ r : ℝ, 0 < r →
        FlatProfileSourceStatement h r) (p : ℝ≥0∞) :
      PDE.MemLpOn D p (fun x => flatProfileHessian h r (spatialCoordinateCLE d x) i k) := by
    obtain ⟨_, _, _, hm, hb, _, _, _, _, _, _, _⟩ := hflat hd ha ha1 h r hr
    apply memLp_spatialCoordinate_of_compact_bound hD _ (hm i k)
    intro K hK
    obtain ⟨M, _, hM⟩ := hb K hK
    exact ⟨M, fun q hq => by simpa using (hM q hq).2.2 i k⟩
  have weak_velocityJet_spatialCoordinate_of_flatProfile_source (hflat : ∀ {d : ℕ}, 1 ≤ d → ∀ {alpha : ℝ}, 0 < alpha → alpha < 1 →
      ∀ h : CounterProfileStatement d alpha, ∀ r : ℝ, 0 < r →
        FlatProfileSourceStatement h r) :
      PDE.HasWeakPartialDerivOn D (Fin.natAdd d i)
      (fun x => flatProfileVelocityJet h r (spatialCoordinateCLE d x) k)
      (fun x => flatProfileHessian h r (spatialCoordinateCLE d x) i k) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hw, _, _⟩ := hflat hd ha ha1 h r hr
    apply weakPartial_on_of_global
    intro test ht hs
    apply weak_directional_spatialCoordinate (fun q => flatProfileVelocityJet h r q k)
      (fun q => flatProfileHessian h r q i k) (0, PDE.basisVec i)
      (PDE.basisVec (Fin.natAdd d i)) (spatialCoordinate_basis_velocity i) _ test ht hs
    intro test ht hs
    apply weak_first_jet_of_second (selectedFlatProfile h r) _ _
      (0, PDE.basisVec k) (0, PDE.basisVec i) _ _ test ht hs
    · intro test ht hs
      exact (hw test (ht.of_le (by simp)) hs).2.1 k
    · intro test ht hs
      have he := (hw test (ht.of_le (by simp)) hs).2.2 i k
      simpa only [dvv, dv, PDE.basisVec,
        smooth_test_second_swap test (ht.of_le (by simp))] using! he
  let u := flatProfileW1p_of_flatProfile_source hflat hd ha ha1 h r hr hD
  have hw : PDE.HasWeakPartialDerivOn D (Fin.natAdd d i)
      (fun x => u.grad x (Fin.natAdd d k))
      (fun x => flatProfileHessian h r (spatialCoordinateCLE d x) i k) := by
    simpa only [u, flatProfileW1p_of_flatProfile_source, spatialPackedGradient,
      Fin.addCases_right] using!
      weak_velocityJet_spatialCoordinate_of_flatProfile_source hflat
  obtain ⟨M, hM, hb⟩ := timeCutoffTheta_deriv2_abs_bound
  have he := weakSecond_cutoff_sub_smooth hD u (spatialPackedBarrier d mu R t)
    (contDiff_spatialPackedBarrier d mu R t) (Fin.natAdd d i) (Fin.natAdd d k)
    _ (memLp_flatProfileHessian_spatialCoordinate_of_flatProfile_source hflat 2) hw timeCutoffTheta (contDiff_timeCutoffTheta.of_le (by simp)) M hM.le hb
  simpa only [u, flatProfileW1p_of_flatProfile_source, spatialPackedGradient,
    Fin.addCases_right] using! he

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

