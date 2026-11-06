module

public import PDEFoundation.Sobolev.WeakDerivative
public import PDEFoundation.Geometry.EuclideanBall.Topology
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.Compactness.LocallyFinite

/-!
# Ballwise gluing of weak gradients

This file records the locality of coordinate weak derivatives on an open
Euclidean domain.  The proof uses a smooth partition of unity on the compact
support of a test function.
-/

@[expose] public section


namespace PDE

open Filter MeasureTheory Set
open scoped Topology

/-- Weak gradients on an open set glue from a ball around every point. -/
theorem HasWeakGradientOn.of_ballwise
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {f : Vec d → ℝ} {Df : Vec d → Vec d}
    (hf : MeasureTheory.LocallyIntegrableOn f U MeasureTheory.volume)
    (hDf : ∀ i : Fin d,
      MeasureTheory.LocallyIntegrableOn (fun x => Df x i) U MeasureTheory.volume)
    (hlocal : ∀ x ∈ U, ∃ R : ℝ, 0 < R ∧
      euclideanClosedBall x R ⊆ U ∧
      HasWeakGradientOn (euclideanBall x R) f Df) :
    HasWeakGradientOn U f Df := by
  intro i φ hφSmooth hφCompact hφU
  let K  := tsupport φ
  have hKClosed : IsClosed K := by aesop
  have hKCompact : IsCompact K := hφCompact.isCompact
  choose R hRpos hRsub hweak using fun x : K => hlocal x.1 (hφU x.2)
  let V  := fun x => euclideanBall x.1 (R x)
  have hVOpen : ∀ x, IsOpen (V x) := fun x => isOpen_euclideanBall _ _
  have hKCover : K ⊆ ⋃ x, V x := by
    intro x hx
    exact mem_iUnion_of_mem ⟨x, hx⟩ (center_mem_euclideanBall x (hRpos _))
  obtain ⟨ρ, hρV⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate
      (ι := K) (modelWithCornersSelf ℝ (Vec d)) hKClosed V hVOpen hKCover
  let active  := {x | (Function.support (ρ x) ∩ K).Nonempty}
  have hactiveFinite : active.Finite := ρ.locallyFinite.finite_nonempty_inter_compact hKCompact
  let J  := hactiveFinite.toFinset
  let ψ  := fun x y => φ y * ρ x y
  have hsumψ : (∑ x ∈ J, ψ x) = φ := by
    funext y
    by_cases hy : y ∈ K
    · have hfin : ρ.finsupport y ⊆ J := by
        intro x hx
        rw [SmoothPartitionOfUnity.mem_finsupport] at hx
        have hxactive : x ∈ active := ⟨y, hx, hy⟩
        aesop
      rw [Finset.sum_apply, ← Finset.mul_sum]
      rw [ρ.sum_finsupport' (x₀ := y) hy hfin, mul_one]
    · have hφy : φ y = 0 := image_eq_zero_of_notMem_tsupport hy
      aesop
  have hψSmooth (x : K) : ContDiff ℝ (⊤ : ℕ∞) (ψ x) := hφSmooth.mul (ρ x).contMDiff.contDiff
  have hψCompact (x : K) : HasCompactSupport (ψ x) := by
    simpa only [ψ, Pi.mul_def] using hφCompact.mul_right (f' := ρ x)
  have hψV (x : K) : tsupport (ψ x) ⊆ V x := (tsupport_mul_subset_right (f := φ) (g := ρ x)).trans (hρV x)
  have hVU (x : K) : V x ⊆ U := (euclideanBall_subset_euclideanClosedBall _ _).trans (hRsub x)
  have hlocalIdentity (x : K) :
      ∫ y in U, f y * (fderiv ℝ (ψ x) y) (basisVec i) ∂volume =
        -∫ y in U, Df y i * ψ x y ∂volume := by
    have hball := hweak x i _ (hψSmooth x) (hψCompact x) (hψV x)
    have hleftZero (y : Vec d) (hy : y ∉ V x) :
        f y * (fderiv ℝ (ψ x) y) (basisVec i) = 0 := by
      have hy' : y ∉ tsupport _ := fun h => hy (hψV x h)
      have heq : ψ x =ᶠ[nhds y] 0 :=
        (isClosed_tsupport _).isOpen_compl.eventually_mem hy' |>.mono
          (fun z hz => image_eq_zero_of_notMem_tsupport hz)
      rw [heq.fderiv_eq]
      simp
    have hrightZero (y : Vec d) (hy : y ∉ V x) : Df y i * ψ x y = 0 := by
      simp [image_eq_zero_of_notMem_tsupport (fun h => hy (hψV x h))]
    have hleftZeroU (y : Vec d) (hy : y ∉ U)  :=
      hleftZero y (fun h => hy (hVU x h))
    have hrightZeroU (y : Vec d) (hy : y ∉ U)  :=
      hrightZero y (fun h => hy (hVU x h))
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hleftZeroU,
      setIntegral_eq_integral_of_forall_compl_eq_zero hrightZeroU,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero hleftZero,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero hrightZero]
    omega
  have hleftIntegrable (x : K) :
      Integrable (fun y => f y * (fderiv ℝ (ψ x) y) (basisVec i)) (volumeOn U) := by
    let g  := fun y => (fderiv ℝ (ψ x) y) (basisVec i)
    have hgCont : Continuous g :=
      (hψSmooth x).continuous_fderiv (by simp) |>.clm_apply continuous_const
    have hgCompact : HasCompactSupport g :=
      (hψCompact x).fderiv_apply (𝕜 := ℝ) _
    have hgU : tsupport g ⊆ U :=
      (closure_minimal (by
        intro y hy
        apply (tsupport_fderiv_subset ℝ)
        exact subset_tsupport _ (fun hz => hy (by grind)))
        (isClosed_tsupport _)).trans ((hψV x).trans (hVU x))
    have hfK := hf.integrableOn_compact_subset hgU hgCompact.isCompact
    have hfgK : IntegrableOn (fun y => f y * g y) _ volume :=
      hfK.mul_continuousOn hgCont.continuousOn hgCompact.isCompact
    simpa only [IntegrableOn, volumeOn, g] using
      hfgK.of_forall_sdiff_eq_zero hU.measurableSet fun y hy => by
        simp [image_eq_zero_of_notMem_tsupport hy.2]
  have hrightIntegrable (x : K) :
      Integrable (fun y => Df y i * ψ x y) (volumeOn U) := by
    have hDfK := (hDf i).integrableOn_compact_subset
      ((hψV x).trans (hVU x)) (hψCompact x).isCompact
    have hprodK : IntegrableOn (fun y => Df y i * ψ x y) _ volume :=
      hDfK.mul_continuousOn (hψSmooth x).continuous.continuousOn (hψCompact x).isCompact
    simpa only [IntegrableOn, volumeOn] using
      hprodK.of_forall_sdiff_eq_zero hU.measurableSet fun y hy => by
        simp [image_eq_zero_of_notMem_tsupport hy.2]
  have hsumIdentity :
      (∑ x ∈ J, ∫ y in U, f y * (fderiv ℝ (ψ x) y) (basisVec i) ∂volume) =
        ∑ x ∈ J, -∫ y in U, Df y i * ψ x y ∂volume := by
    simp_all
  rw [← MeasureTheory.integral_finsetSum _ (fun x _ => hleftIntegrable x),
    Finset.sum_neg_distrib] at hsumIdentity
  rw [← MeasureTheory.integral_finsetSum _ (fun x _ => hrightIntegrable x)] at hsumIdentity
  have hderivSum (y : Vec d) :
      ∑ x ∈ J, (fderiv ℝ (ψ x) y) (basisVec i) =
        (fderiv ℝ φ y) (basisVec i) := by
    rw [← hsumψ]
    rw [fderiv_sum (fun x _ =>
      (hψSmooth x).contDiffAt.differentiableAt (by simp))]
    simp
  have hvalueSum (y : Vec d) : ∑ x ∈ J, ψ x y = φ y := by
    simpa only [Finset.sum_apply, Finset.sum_apply] using congrFun hsumψ y
  calc
    ∫ x in U, f x * (fderiv ℝ φ x) _ ∂volume =
        ∫ x, ∑ y ∈ J, f x * (fderiv ℝ _ x) _ ∂volumeOn U := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change f x * (fderiv ℝ φ x) _ =
          ∑ y ∈ J, f x * (fderiv ℝ _ x) _
        rw [← Finset.mul_sum, hderivSum]
    _ = -∫ x, ∑ y ∈ J, Df x i * ψ y x ∂volumeOn U := hsumIdentity
    _ = -∫ x in U, Df x i * φ x ∂volume := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change (∑ y ∈ J, Df x i * ψ y x) = Df x i * φ x
        rw [← Finset.mul_sum, hvalueSum]

end PDE
