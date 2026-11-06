module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10FunctionAdd
public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10FunctionAECopy
public import HypoellipticAleksandrov.Parabolic.Dirichlet.GeneralOpenH1ZeroLevel
public import PDEFoundation.Sobolev.H1.ZeroBoundaryCutoff
public import PDEFoundation.Sobolev.H1.ZeroExtension
public import PDEFoundation.Geometry.EuclideanBall.Topology
public import PDEFoundation.Geometry.ConvexDomain
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.Compactness.LocallyFinite
public import Mathlib.Topology.Separation.Regular
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Compactly interior supported H1 representatives have zero boundary values

An `H1Function` which vanishes almost everywhere off a compact subset of an
open set admits a representative-level `H10Function` certificate.
-/

@[expose] public section

open scoped ENNReal Topology ContDiff Manifold

namespace PDE.H1Function

open Filter Function MeasureTheory Set

variable {d : ℕ}

private theorem exists_smooth_cutoff_tsupport_subset
     {K U : PDE.VelocityRegion d}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ b : PDE.ScalarField d,
      ContDiff ℝ ∞ b ∧
      (∀ᶠ x in 𝓝ˢ K, b x = 1) ∧
      HasCompactSupport b ∧
      tsupport b ⊆ U := by
  obtain ⟨L, hLcompact, hLclosed, hKinterior, hLU⟩ :=
    exists_compact_closed_between hK hU hKU
  obtain ⟨b, hbOne, hbZero, _hbRange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior
      (I := modelWithCornersSelf ℝ (PDE.Vec d)) (n := (⊤ )) hK.isClosed
      (hKinterior)
  have hbL : tsupport b ⊆ L := by
    apply closure_minimal _ hLclosed
    intro x hx
    by_contra hxL
    exact (mem_support.mp hx) (hbZero x hxL)
  exact ⟨b, b.contMDiff.contDiff, hbOne,
    hLcompact.of_isClosed_subset isClosed_closure hbL, hbL.trans hLU⟩

private noncomputable def zeroH10  {U : PDE.VelocityRegion d} :
    PDE.H10Function U where
  toH1Function := 0
  approx := fun _ _ => 0
  approx_smooth := fun _ => contDiff_const
  approx_hasCompactSupport := fun _ => HasCompactSupport.zero
  approx_support_subset := fun _ => by simp
  tendsto_approx := by
    simp_all
  tendsto_approx_grad := by
    simp_all

/-- An `H¹` representative supported almost everywhere on a compact subset of
an open set has a representative-level zero-boundary certificate. -/
theorem exists_h10Function_of_ae_zero_outside_compact
     {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω)
    (q : PDE.H1Function Ω) (K : PDE.VelocityRegion d)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hqzero : ∀ᵐ x ∂(PDE.volumeOn Ω), x ∉ K → q.toFun x = 0) :
    ∃ w : PDE.H10Function Ω, w.toH1Function = q := by
  obtain ⟨b, hbSmooth, hbOne, hbCompact, hbΩ⟩ :=
    exists_smooth_cutoff_tsupport_subset hK hΩ hKΩ
  let L  := tsupport b

  have hballs : ∀ x : L, ∃ R : ℝ, 0 < R ∧
      PDE.euclideanClosedBall x.1 R ⊆ Ω := by
    intro x
    rcases Metric.isOpen_iff.1 hΩ x.1 (hbΩ x.2) with ⟨δ, hδ, hball⟩
    refine ⟨δ / 2, by positivity, ?_⟩
    exact (PDE.euclideanClosedBall_subset_supClosedBall (by positivity)).trans
      ((Metric.closedBall_subset_ball (by linarith)).trans hball)
  choose R hRpos hRsub using hballs
  let V  := fun x => PDE.euclideanBall x.1 (R x)
  have hVOpen : ∀ x, IsOpen (V x) := fun x => PDE.isOpen_euclideanBall _ _

  obtain ⟨ρ, hρV⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate
       (modelWithCornersSelf ℝ (PDE.Vec d))
      (isClosed_tsupport b) V hVOpen (by
          intro x hx
          exact mem_iUnion_of_mem ⟨x, hx⟩
            (PDE.center_mem_euclideanBall x (hRpos ⟨x, hx⟩)))

  have hactiveFinite : ({x | (Function.support (ρ x) ∩ L).Nonempty}).Finite :=
    ρ.locallyFinite.finite_nonempty_inter_compact hbCompact.isCompact
  let J  := hactiveFinite.toFinset
  let φ  := fun x y => b y * ρ x y
  have hφSmooth (x : L) : ContDiff ℝ PDE.smoothOrder (φ x) :=
    hbSmooth.mul (ρ x).contMDiff.contDiff
  have hφCompact (x : L) : HasCompactSupport (φ x) := hbCompact.mul_right
  have hφV (x : L) : tsupport (φ x) ⊆ V x :=
    (tsupport_mul_subset_right (f := b) (g := ρ x)).trans (hρV x)
  have hVU (x : L) : V x ⊆ Ω :=
    (PDE.euclideanBall_subset_euclideanClosedBall _ _).trans (hRsub x)
  have hsumφ : (∑ x ∈ J, φ x) = b := by
    funext y
    by_cases hy : y ∈ L
    ·
      dsimp only [φ]
      rw [Finset.sum_apply, ← Finset.mul_sum]
      rw [ρ.sum_finsupport' (x₀ := y) hy (by
          intro x hx
          rw [SmoothPartitionOfUnity.mem_finsupport] at hx
          exact hactiveFinite.mem_toFinset.mpr ⟨y, hx, hy⟩), mul_one]
    ·
      simp [φ, (image_eq_zero_of_notMem_tsupport hy)]
  have hlocal (x : L) : ∃ w : PDE.H10Function Ω,
      w.toH1Function.toFun = (fun y => φ x y * q.toFun y) ∧
      w.toH1Function.grad = (fun y =>
        φ x y • q.grad y + q.toFun y • PDE.classicalGradient (φ x) y) := by
    let qx  := q.restrict (hVOpen x) (hVU x)
    let wx0  :=
      qx.mulContDiffHasCompactSupportToH10
        (PDE.isOpenBoundedConvexDomain_euclideanBall x.1 (hRpos x))
        (hφSmooth x) (hφCompact x) (hφV x)
    let wx := wx0.zeroExtend hΩ (hVOpen x) (hVU x)
    refine ⟨wx, ?_, ?_⟩
    · dsimp only [wx]
      rw [PDE.H10Function.zeroExtend_toFun,
        PDE.H1Function.mulContDiffHasCompactSupportToH10_toFun]
      funext y
      by_cases hy : y ∈ V x
      · simp [Set.indicator_of_mem hy, qx]
      ·
        simp [Set.indicator_of_notMem hy, (image_eq_zero_of_notMem_tsupport (fun h => hy (hφV x h)))]
    · dsimp only [wx]
      rw [PDE.H10Function.zeroExtend_grad,
        PDE.H1Function.mulContDiffHasCompactSupportToH10_grad]
      funext y
      by_cases hy : y ∈ V x
      · simp [Set.indicator_of_mem hy, qx]
      · have hyts : y ∉ tsupport (φ x) := fun h => hy (hφV x h)


        have hdφ : PDE.classicalGradient (φ x) y = 0 := by
          funext i
          simp only [PDE.classicalGradient]
          rw [(notMem_tsupport_iff_eventuallyEq.mp hyts).fderiv_eq]
          simp
        simp [Set.indicator_of_notMem hy, (image_eq_zero_of_notMem_tsupport hyts), hdφ]
  choose wx hwxFun hwxGrad using hlocal
  have hfinite : ∃ w : PDE.H10Function Ω,
      w.toH1Function.toFun = (fun y => ∑ x ∈ J, φ x y * q.toFun y) ∧
      w.toH1Function.grad = (fun y => ∑ x ∈ J,
        (φ x y • q.grad y + q.toFun y • PDE.classicalGradient (φ x) y)) := by
    classical
    induction J using Finset.induction_on with
    | empty =>
        refine ⟨zeroH10, ?_, ?_⟩ <;>
          funext y <;> rfl
    | @insert a s ha ih =>
        obtain ⟨w, hwFun, hwGrad⟩ := ih
        refine ⟨wx a + w, ?_, ?_⟩
        · rw [PDE.H10Function.toH1Function_add,
            PDE.H1Function.add_toFun, hwxFun a, hwFun]
          funext y
          simp [ha]
        · rw [PDE.H10Function.toH1Function_add,
            PDE.H1Function.add_grad, hwxGrad a, hwGrad]
          funext y
          simp [ha]
  obtain ⟨w, hwFun, hwGrad⟩ := hfinite

  have hfun : w.toH1Function.toFun =ᵐ[PDE.volumeOn Ω] q.toFun := by
    rw [hwFun]
    filter_upwards [hqzero] with y hy
    by_cases hyK : y ∈ K
    · have hbeq : b =ᶠ[𝓝 y] (fun _ => 1) :=
        mem_nhdsSet_iff_forall.1 hbOne y hyK

      rw [← Finset.sum_mul, ← Finset.sum_apply, congrFun hsumφ y, hbeq.self_of_nhds, one_mul]
    · simp [hy hyK]
  have hgrad : ∀ i : Fin d,
      (fun y => w.toH1Function.grad y i) =ᵐ[PDE.volumeOn Ω]
        (fun y => q.grad y i) := by
    intro i
    rw [hwGrad]
    filter_upwards [hqzero, (show ∀ᵐ x ∂(PDE.volumeOn Ω), x ∉ K → q.grad x = 0 by
        filter_upwards [hqzero, q.grad_ae_zero_on_zero_set_of_isOpen hΩ] with x hzero hgrad hx
        exact hgrad (hzero hx))] with y hy hgy
    by_cases hyK : y ∈ K
    · have hbeq : b =ᶠ[𝓝 y] 1 := mem_nhdsSet_iff_forall.1 hbOne y hyK

      have hdb : PDE.classicalGradient b y = 0 := by
        funext j
        simp only [PDE.classicalGradient]
        rw [hbeq.fderiv_eq]
        simp
      have hsumDeriv : ∑ x ∈ J, PDE.classicalGradient (φ x) y =
          PDE.classicalGradient b y := by
        have hd := congrArg (fun f => fderiv ℝ f y) hsumφ
        change fderiv ℝ (∑ x ∈ J, φ x) y = fderiv ℝ b y at hd
        rw [fderiv_sum (fun x _ => (hφSmooth x).differentiable (by simp) y)] at hd
        funext j
        have hdj := congrArg (fun A => A (PDE.basisVec j)) hd
        rw [ContinuousLinearMap.sum_apply] at hdj
        simpa only [PDE.classicalGradient, Finset.sum_apply] using hdj
      rw [Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.smul_sum,
        ← Finset.sum_apply, congrFun hsumφ y, hbeq.self_of_nhds, hsumDeriv, hdb]
      simp
    ·

      simp [(hy hyK), (hgy hyK)]
  refine ⟨PDE.H10Function.copyToH1Function_of_ae_eq w q hfun hgrad, ?_⟩
  exact PDE.H10Function.copyToH1Function_of_ae_eq_toH1Function w q hfun hgrad

end PDE.H1Function
