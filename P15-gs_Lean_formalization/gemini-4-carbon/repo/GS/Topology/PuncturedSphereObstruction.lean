module

public import GS.NonmanifoldClosure.PuncturedBall
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.Topology.TietzeExtension
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Module.Determinant

@[expose] public section

set_option autoImplicit false
noncomputable section

open Set Metric Function MeasureTheory Polynomial
open scoped Topology ContDiff unitInterval RealInnerProductSpace BigOperators

namespace GS.Topology

def sphereNormalize {F X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X]
    (g : C(X, F)) (hg : ∀ x, g x ≠ 0) : C(X, sphere (0 : F) 1) :=
  ⟨fun x => ⟨‖g x‖⁻¹ • g x, by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr (hg x))),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hg x))]⟩,
    ((g.continuous.norm.inv₀ fun x => norm_ne_zero_iff.mpr (hg x)).smul g.continuous).subtype_mk _⟩

section Approx
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

private theorem exists_contDiff_dist_lt_on_compact (f : C(E, F)) {K : Set E}
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ ∀ x ∈ K, dist (g x) (f x) < ε := by
  have hu : UniformContinuousOn f (cthickening 1 K) :=
    hK.cthickening.uniformContinuousOn_of_continuous (by fun_prop)
  rcases Metric.uniformContinuousOn_iff.mp hu (ε / 2) (half_pos hε) with ⟨δ, hδ, hfδ⟩
  rcases (map_continuous f).exists_contDiff_dist_le_of_forall_mem_ball_dist_le (lt_min one_pos hδ) with ⟨g, hgc, hg⟩
  refine ⟨g, hgc, fun x hx => (hg _ _ fun y hy => ?_).trans_lt (half_lt_self hε)⟩
  rw [mem_ball, lt_min_iff] at hy
  exact (hfδ _ (mem_cthickening_of_dist_le _ x _ _ hx hy.1.le) _ (self_subset_cthickening _ hx) hy.2).le

private theorem sphereMap_nullhomotopic_of_finrank_lt
    (hdim : Module.finrank ℝ E < Module.finrank ℝ F)
    (f : C(sphere (0 : E) 1, sphere (0 : F) 1)) : f.Nullhomotopic := by
  let e : F ≃L[ℝ] (Fin (Module.finrank ℝ F) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  letI : TietzeExtension F := TietzeExtension.of_homeo e.toHomeomorph
  obtain ⟨f₀, hf₀⟩ := (⟨fun x => f x, continuous_subtype_val.comp f.continuous⟩ :
    C(sphere (0 : E) 1, F)).exists_restrict_eq isClosed_sphere
  obtain ⟨g₀, hgc₀, hg₀⟩ := exists_contDiff_dist_lt_on_compact f₀ (isCompact_sphere (0 : E) 1)
    (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨y, hy, hyε⟩ := (hgc₀.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).dense_compl_range_of_finrank_lt_finrank
    hdim |>.exists_dist_lt 0 (by norm_num : (0 : ℝ) < 1 / 2)
  let g : C(E, F) := ⟨fun x => g₀ x - y, (hgc₀.sub contDiff_const).continuous⟩
  have hg0 (x : E) : g x ≠ 0 := fun h => hy ⟨x, sub_eq_zero.mp h⟩
  have hclose (x : sphere (0 : E) 1) : dist (g x) (f x : F) < 1 := by
    have heq : f₀ x = (f x : F) := congrArg (fun h : C(sphere (0 : E) 1, F) => h x) hf₀
    calc dist (g₀ x - y) (f x : F) ≤ dist (g₀ x - y) (g₀ x) + dist (g₀ x) (f₀ x) := by rw [← heq]; exact dist_triangle _ _ _
      _ < 1 / 2 + 1 / 2 := add_lt_add (by simpa using hyε) (hg₀ x x.property)
      _ = 1 := by norm_num
  let a : C(unitInterval × sphere (0 : E) 1, F) :=
    ⟨fun z => (1 - (z.1 : ℝ)) • (f z.2 : F) + (z.1 : ℝ) • g z.2, by fun_prop⟩
  have ha (z : unitInterval × sphere (0 : E) 1) : a z ≠ 0 := by
    have hv : ‖(f z.2 : F)‖ = 1 := mem_sphere_zero_iff_norm.mp (f z.2).property
    have hb : a z ∈ ball (f z.2 : F) 1 :=
      (convex_ball (f z.2 : F) 1) (by simp) (hclose z.2) (sub_nonneg.mpr z.1.2.2) z.1.2.1 (sub_add_cancel 1 _)
    intro h0; simp [h0, hv] at hb
  have hfg : f.Homotopic (sphereNormalize (g.restrict _) fun x => hg0 x) :=
    ⟨{ toContinuousMap := sphereNormalize a ha
       map_zero_left := fun x => Subtype.ext <| by
         have hf : ‖(f x : F)‖ = 1 := mem_sphere_zero_iff_norm.mp (f x).property
         simp [sphereNormalize, a, hf]
       map_one_left := fun x => Subtype.ext (by simp [sphereNormalize, a]) }⟩
  have hn : (sphereNormalize g hg0).Nullhomotopic := by
    simpa using (id_nullhomotopic E).comp_right (sphereNormalize g hg0)
  obtain ⟨c, hc⟩ := hn.comp_left (⟨Subtype.val, continuous_subtype_val⟩ : C(sphere (0 : E) 1, E))
  exact ⟨c, hfg.trans hc⟩
end Approx

private abbrev Eucl (m : ℕ) := EuclideanSpace ℝ (Fin m)

private theorem det_fderiv_sphere_valued_eq_zero {m : ℕ}
    {g : Eucl m → Eucl m} (hg : Differentiable ℝ g) (hnorm : ∀ x, ‖g x‖ = 1) (x : Eucl m) :
    (fderiv ℝ g x).det = 0 := by
  have hd1 := (hg x).hasFDerivAt.norm_sq
  rw [show (fun y => ‖g y‖ ^ 2) = fun _ => (1 : ℝ) by funext y; simp [hnorm y]] at hd1
  have hd0 := hd1.unique (hasFDerivAt_const (1 : ℝ) x)
  by_contra hne
  obtain ⟨uL, huL⟩ := (LinearMap.isUnit_iff_isUnit_det (fderiv ℝ g x : Eucl m →ₗ[ℝ] Eucl m)).mpr
    (isUnit_iff_ne_zero.mpr hne)
  have hlin := congrArg (fun L : Eucl m →L[ℝ] ℝ => L (uL.inv (g x))) hd0
  simp only [smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, zero_apply, nsmul_eq_mul] at hlin
  rw [show (fderiv ℝ g x) (uL.inv (g x)) = g x by simpa [huL] using LinearMap.congr_fun uL.val_inv (g x),
    real_inner_self_eq_norm_sq, hnorm x] at hlin
  norm_num at hlin

private theorem no_smooth_sphere_retraction {m : ℕ} [Nontrivial (Eucl m)]
    (μ : Measure (Eucl m)) [Measure.IsAddHaarMeasure μ]
    (g : Eucl m → Eucl m) (hgsmooth : ContDiff ℝ ∞ g)
    (hgnorm : ∀ x, ‖g x‖ = 1) (hgsph : ∀ x, ‖x‖ = 1 → g x = x) : False := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Eucl m) 1).exists_bound_of_continuousOn
    (hgsmooth.continuous_fderiv (by simp)).continuousOn
  let M : ℝ := max C 1
  have hM1 : 1 ≤ M := le_max_right _ _
  have hfd_le (x : Eucl m) (hx : x ∈ closedBall 0 1) : ‖fderiv ℝ g x‖ ≤ M :=
    (hC x hx).trans (le_max_left _ _)
  have hglip (x y : Eucl m) (hx : x ∈ closedBall 0 1) (hy : y ∈ closedBall 0 1) :
      ‖g x - g y‖ ≤ M * ‖x - y‖ :=
    (convex_closedBall (0 : Eucl m) 1).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hgsmooth.differentiable (by simp)) z) hfd_le hy hx
  let f (t : ℝ) (x : Eucl m) : Eucl m := (1 - t) • x + t • g x
  let D (t : ℝ) (x : Eucl m) : Eucl m →L[ℝ] Eucl m :=
    (1 - t) • ContinuousLinearMap.id ℝ (Eucl m) + t • fderiv ℝ g x
  have hfderiv (t : ℝ) (x : Eucl m) : HasStrictFDerivAt (f t) (D t x) x := by
    convert ((hasStrictFDerivAt_id x).const_smul (1 - t)).add
      ((hgsmooth.contDiffAt.hasStrictFDerivAt (by simp)).const_smul t) using 1
    funext y; rfl
  let bas := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
  let δ : ℝ := 1 / (2 * (M + 1))
  have hδpos : 0 < δ := by positivity
  have hvol_eq (t : ℝ) (ht : t ∈ Ioo 0 δ) :
      ∫ x in ball (0 : Eucl m) 1, (D t x).det ∂μ = (μ (ball (0 : Eucl m) 1)).toReal := by
    have ht0 : 0 < t := ht.1
    have htM : t * (M + 1) < 1 / 2 := by
      have hpos2 : (0 : ℝ) < 2 * (M + 1) := by positivity
      have hmul := mul_lt_mul_of_pos_right ht.2 hpos2
      dsimp [δ] at hmul; rw [one_div_mul_cancel hpos2.ne'] at hmul; linarith
    have hunit (s : ℝ) (hs : s ∈ Icc 0 t) (x : Eucl m) (hx : x ∈ closedBall 0 1) : IsUnit (D s x) := by
      rw [show D s x = 1 - s • (1 - fderiv ℝ g x) by ext v; simp [D, sub_smul, smul_sub]; abel]
      refine isUnit_one_sub_of_norm_lt_one ?_
      calc ‖s • (1 - fderiv ℝ g x)‖ = s * ‖(1 : Eucl m →L[ℝ] Eucl m) - fderiv ℝ g x‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
        _ ≤ t * (1 + M) := (mul_le_mul hs.2 (norm_sub_le _ _) (norm_nonneg _) ht0.le).trans
            (mul_le_mul_of_nonneg_left (add_le_add norm_one.le (hfd_le x hx)) ht0.le)
        _ < 1 := by linarith
    have hdet_pos (x : Eucl m) (hx : x ∈ closedBall 0 1) : 0 < (D t x).det := by
      by_contra hle
      have hdc : Continuous fun s : ℝ => (D s x).det :=
        ContinuousLinearMap.continuous_det.comp
          (((continuous_const.sub continuous_id).smul continuous_const).add (continuous_id.smul continuous_const))
      have hD0 : (D 0 x).det = 1 := by
        rw [show D 0 x = ContinuousLinearMap.id ℝ (Eucl m) by ext v; simp [D]]; exact LinearMap.det_id
      obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' ht0.le hdc.continuousOn ⟨le_of_not_gt hle, by linarith⟩
      obtain ⟨u_s, hu_s⟩ := hunit s hs x hx
      exact ((LinearMap.isUnit_iff_isUnit_det _).mp
        ⟨Units.map ContinuousLinearMap.toLinearMapRingHom.toMonoidHom u_s, by simp [hu_s]⟩).ne_zero hs0
    have hinj : InjOn (f t) (ball 0 1) := fun x hx y hy hxy => by
      have heq : (1 - t) • (x - y) = t • (g y - g x) := by
        dsimp [f] at hxy; calc (1 - t) • (x - y) = ((1 - t) • x + t • g x) - ((1 - t) • y + t • g x) := by simp [smul_sub]
          _ = t • (g y - g x) := by rw [hxy]; simp [smul_sub]
      have hn1 : (1 - t) * ‖x - y‖ ≤ t * M * ‖x - y‖ := by
        calc (1 - t) * ‖x - y‖ = ‖(1 - t) • (x - y)‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by nlinarith)]
          _ = t * ‖g y - g x‖ := by rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0.le]
          _ ≤ t * (M * ‖y - x‖) :=
              mul_le_mul_of_nonneg_left (hglip y x (ball_subset_closedBall hy) (ball_subset_closedBall hx)) ht0.le
          _ = t * M * ‖x - y‖ := by rw [norm_sub_rev, mul_assoc]
      exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (x - y)]))
    have himg_sub : f t '' ball 0 1 ⊆ ball 0 1 := by
      rintro _ ⟨x, hx, rfl⟩; rw [mem_ball_zero_iff] at hx ⊢
      have ht1 : 0 < 1 - t := by nlinarith
      calc ‖(1 - t) • x + t • g x‖ ≤ (1 - t) * ‖x‖ + t * 1 := by
            simpa [norm_smul, abs_of_pos ht1, abs_of_pos ht0, hgnorm x] using norm_add_le ((1 - t) • x) (t • g x)
        _ < 1 := by nlinarith
    have hopen : IsOpen (f t '' ball 0 1) := by
      rw [isOpen_iff_mem_nhds]; rintro _ ⟨x, hx, rfl⟩
      obtain ⟨u_x, hu_x⟩ := hunit t ⟨ht0.le, le_rfl⟩ x (ball_subset_closedBall hx)
      let e_x : Eucl m ≃L[ℝ] Eucl m :=
        { toLinearEquiv := LinearEquiv.ofLinearMap u_x.val.toLinearMap u_x.inv.toLinearMap
            (LinearMap.ext fun v => DFunLike.congr_fun u_x.val_inv v)
            (LinearMap.ext fun v => DFunLike.congr_fun u_x.inv_val v)
          continuous_toFun := u_x.val.continuous, continuous_invFun := u_x.inv.continuous }
      have hf' : HasStrictFDerivAt (f t) (e_x : Eucl m →L[ℝ] Eucl m) x := by
        have hcoe : (e_x : Eucl m →L[ℝ] Eucl m) = D t x := ContinuousLinearMap.ext fun v => DFunLike.congr_fun hu_x v
        rw [hcoe]; exact hfderiv t x
      let φ := hf'.toOpenPartialHomeomorph (f t)
      exact Filter.mem_of_superset
        ((φ.isOpen_image_of_subset_source (φ.open_source.inter isOpen_ball) inter_subset_left).mem_nhds
          ⟨x, ⟨hf'.mem_toOpenPartialHomeomorph_source, hx⟩, rfl⟩)
        (image_mono inter_subset_right)
    have himg : f t '' ball 0 1 = ball 0 1 := by
      have hclosed_B : IsClosed (f t '' closedBall 0 1) :=
        ((isCompact_closedBall (0 : Eucl m) 1).image
          (((contDiff_id.const_smul (1 - t)).add (hgsmooth.const_smul t)).continuous)).isClosed
      refine Subset.antisymm himg_sub ((convex_ball (0 : Eucl m) 1).isPreconnected.subset_of_closure_inter_subset
        hopen ⟨f t 0, himg_sub ⟨0, mem_ball_self zero_lt_one, rfl⟩, 0, mem_ball_self zero_lt_one, rfl⟩ ?_)
      refine (inter_subset_inter_left _ (closure_mono (image_mono ball_subset_closedBall))).trans ?_
      rw [hclosed_B.closure_eq]
      rintro y ⟨⟨x, hxB, rfl⟩, hyU⟩
      by_cases hxU : x ∈ ball 0 1
      · exact ⟨x, hxU, rfl⟩
      · have hx1 : ‖x‖ = 1 := le_antisymm (mem_closedBall_zero_iff.mp hxB)
          (not_lt.mp (by simpa [mem_ball_zero_iff] using hxU))
        have hfx : f t x = x := by simp [f, hgsph x hx1, sub_smul, one_smul]
        rw [hfx] at hyU; exact (hxU hyU).elim
    have hjac := himg ▸ lintegral_abs_det_fderiv_eq_addHaar_image (μ := μ) measurableSet_ball
      (fun x _ => (hfderiv t x).hasFDerivAt.hasFDerivWithinAt) hinj
    have hint : Integrable (fun x => (D t x).det) (μ.restrict (ball (0 : Eucl m) 1)) :=
      (ContinuousLinearMap.continuous_det.comp
        (continuous_const.add ((hgsmooth.continuous_fderiv (by simp)).const_smul t))).continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : Eucl m) 1) |>.mono_set ball_subset_closedBall
    have hnn : 0 ≤ᵐ[μ.restrict (ball (0 : Eucl m) 1)] fun x => (D t x).det := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact (hdet_pos x (ball_subset_closedBall hx)).le
    have h1 := setLIntegral_congr_fun (μ := μ) measurableSet_ball fun x hx =>
      congrArg ENNReal.ofReal (abs_of_pos (hdet_pos x (ball_subset_closedBall hx)))
    have h4 := congrArg ENNReal.toReal ((ofReal_integral_eq_lintegral_ofReal hint hnn).trans (h1.symm.trans hjac))
    rwa [ENNReal.toReal_ofReal (integral_nonneg_of_ae hnn)] at h4
  let M_g (x : Eucl m) : Matrix (Fin m) (Fin m) ℝ :=
    LinearMap.toMatrix bas bas (fderiv ℝ g x : Eucl m →ₗ[ℝ] Eucl m)
  let pEntry (x : Eucl m) (i j : Fin m) : ℝ[X] :=
    Polynomial.C ((1 : Matrix (Fin m) (Fin m) ℝ) i j) * (1 - Polynomial.X) +
      Polynomial.C (M_g x i j) * Polynomial.X
  let PMat (x : Eucl m) : Matrix (Fin m) (Fin m) ℝ[X] := Matrix.of (pEntry x)
  have hdeg (x : Eucl m) : (PMat x).det.natDegree ≤ m := by
    rw [Matrix.det_apply]
    refine (Polynomial.natDegree_sum_le _ _).trans ?_
    rw [Finset.fold_max_le]; refine ⟨Nat.zero_le _, fun π _ => ?_⟩
    calc (Units.val (Equiv.Perm.sign π) • ∏ i : Fin m, PMat x (π i) i).natDegree
      _ ≤ (∏ i : Fin m, PMat x (π i) i).natDegree := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
      _ ≤ ∑ i : Fin m, (PMat x (π i) i).natDegree := Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ _i : Fin m, 1 := Finset.sum_le_sum fun i _ => by simp only [PMat, Matrix.of_apply, pEntry]; compute_degree!
      _ = m := by simp
  have heval (t : ℝ) (x : Eucl m) :
      (D t x).det = ∑ k ∈ Finset.range (m + 1), (PMat x).det.coeff k * t ^ k := by
    rw [← Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hdeg x)), ← Polynomial.coe_evalRingHom,
      show (D t x).det = LinearMap.det (D t x : Eucl m →ₗ[ℝ] Eucl m) from rfl,
      ← LinearMap.det_toMatrix bas, RingHom.map_det (Polynomial.evalRingHom t) (PMat x)]
    congr 1; ext i j; simp [PMat, pEntry, M_g, D]; ring
  have hcoeff_int (k : ℕ) : IntegrableOn (fun x => (PMat x).det.coeff k) (ball (0 : Eucl m) 1) μ := by
    refine ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : Eucl m) 1) (Continuous.continuousOn ?_)
      |>.mono_set ball_subset_closedBall
    have hMc (i j : Fin m) : Continuous fun x : Eucl m => M_g x i j := by
      have heq : (fun x : Eucl m => M_g x i j) = fun x => (fderiv ℝ g x (bas j)).ofLp i := by
        funext x; simp [M_g, LinearMap.toMatrix_apply, bas, EuclideanSpace.basisFun_repr]
      rw [heq]; exact (PiLp.continuous_apply 2 _ i).comp
        ((ContinuousLinearMap.apply ℝ (Eucl m) (bas j)).continuous.comp (hgsmooth.continuous_fderiv (by simp)))
    have hpc (π : Equiv.Perm (Fin m)) (s : Finset (Fin m)) :
        ∀ d, Continuous fun x => (∏ i ∈ s, pEntry x (π i) i).coeff d := by
      induction s using Finset.cons_induction with
      | empty => intro d; simp; fun_prop
      | cons a s _ ih =>
        intro d; simp_rw [Finset.prod_cons, Polynomial.coeff_mul]
        refine continuous_finsetSum _ fun pq _ => Continuous.mul ?_ (ih pq.2)
        have hM := hMc (π a) a; dsimp [pEntry]; rcases pq.1 with _ | _ | _ <;> simp [sub_eq_add_neg] <;> fun_prop
    have hdet_eq : (fun x : Eucl m => (PMat x).det.coeff k) =
        fun x => ∑ π : Equiv.Perm (Fin m), (Equiv.Perm.sign π : ℝ) * (∏ i : Fin m, pEntry x (π i) i).coeff k := by
      funext x; rw [Matrix.det_apply, Polynomial.finsetSum_coeff]
      exact Finset.sum_congr rfl fun π _ => by rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [PMat, h]
    rw [hdet_eq]; exact continuous_finsetSum _ fun π _ => continuous_const.mul (hpc π Finset.univ k)
  let Qpoly : ℝ[X] := ∑ k ∈ Finset.range (m + 1),
    Polynomial.C (∫ x in ball (0 : Eucl m) 1, (PMat x).det.coeff k ∂μ) * Polynomial.X ^ k
  have hQeval (t : ℝ) : Qpoly.eval t = ∫ x in ball (0 : Eucl m) 1, (D t x).det ∂μ := by
    simp_rw [heval t]; rw [integral_finsetSum _ fun k _ => (hcoeff_int k).mul_const (t ^ k)]
    simp [Qpoly, Polynomial.eval_finsetSum, integral_mul_const]
  have hQconst : Qpoly = Polynomial.C (μ (ball (0 : Eucl m) 1)).toReal :=
    Polynomial.eq_of_infinite_eval_eq _ _ ((Ioo_infinite hδpos).mono fun t ht => by simp [hQeval t, hvol_eq t ht])
  have h1 : (μ (ball (0 : Eucl m) 1)).toReal = ∫ x in ball (0 : Eucl m) 1, (D 1 x).det ∂μ := by
    simpa [hQeval 1] using (congrArg (Polynomial.eval 1) hQconst).symm
  have hD1 (x : Eucl m) : (D 1 x).det = 0 := by
    rw [show D 1 x = fderiv ℝ g x by ext v; simp [D]]
    exact det_fderiv_sphere_valued_eq_zero (hgsmooth.differentiable (by simp)) hgnorm x
  simp_rw [hD1, integral_zero] at h1
  linarith [ENNReal.toReal_pos (Metric.measure_ball_pos μ (0 : Eucl m) zero_lt_one).ne' measure_ball_lt_top.ne]

theorem sphere_id_not_nullhomotopic (m : ℕ) :
    ¬ (ContinuousMap.id (sphere (0 : EuclideanSpace ℝ (Fin m)) 1)).Nullhomotopic := by
  rintro ⟨u, ⟨h⟩⟩
  have hu1 : ‖(u : Eucl m)‖ = 1 := by simp
  have : Nontrivial (Eucl m) := ⟨0, u, fun he => by simp [← he] at hu1⟩
  let H := h.symm.toContinuousMap
  let nrm (x : Eucl m) : sphere (0 : Eucl m) 1 :=
    if hx : x = 0 then u else ⟨‖x‖⁻¹ • x, by simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩
  let tau (x : Eucl m) : unitInterval := ⟨min 1 (2 * ‖x‖), by positivity, min_le_left _ _⟩
  let R (x : Eucl m) : Eucl m := H (tau x, nrm x)
  have htau_cont : Continuous tau :=
    Continuous.subtype_mk (continuous_const.min (continuous_const.mul continuous_norm)) _
  have hRnorm (x : Eucl m) : ‖R x‖ = 1 := by simp [R]
  have hRrad (x : Eucl m) (hx : 1 / 2 ≤ ‖x‖) : R x = ‖x‖⁻¹ • x := by
    have hx0 : x ≠ 0 := by rintro rfl; norm_num at hx
    have hH1 : H (tau x, nrm x) = nrm x := by
      rw [show tau x = 1 from Subtype.ext (min_eq_left (by linarith))]; exact h.symm.map_one_left (nrm x)
    exact (congrArg Subtype.val hH1).trans (by simp [nrm, hx0])
  have hRcont : Continuous R := by
    rw [continuous_iff_continuousAt]; intro x
    by_cases hx : x = 0
    · subst x; rw [Metric.continuousAt_iff]; intro ε hε
      obtain ⟨δ, hδ, hHδ⟩ := Metric.uniformContinuous_iff.mp
        (CompactSpace.uniformContinuous_of_continuous H.continuous) ε hε
      refine ⟨min (1 / 2) (δ / 2), by positivity, fun y hy => ?_⟩
      rw [dist_zero_right] at hy
      have hy1 : ‖y‖ < 1 / 2 := lt_of_lt_of_le hy (min_le_left _ _)
      have hy2 : ‖y‖ < δ / 2 := lt_of_lt_of_le hy (min_le_right _ _)
      have hR0 : R 0 = H (0, nrm y) := by
        change (H (tau 0, nrm 0) : Eucl m) = (H (0, nrm y) : Eucl m)
        rw [show tau 0 = 0 from Subtype.ext (by simp [tau])]
        exact congrArg Subtype.val ((h.symm.map_zero_left (nrm 0)).trans (h.symm.map_zero_left (nrm y)).symm)
      rw [hR0]; apply hHδ
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
      change |min 1 (2 * ‖y‖) - 0| < δ
      rw [sub_zero, min_eq_right (by linarith), abs_of_nonneg (by positivity)]; linarith
    · refine continuous_subtype_val.continuousAt.comp (H.continuous.continuousAt.comp (htau_cont.continuousAt.prodMk ?_))
      rw [Topology.IsInducing.subtypeVal.continuousAt_iff]
      refine ContinuousAt.congr ((continuousAt_id.norm.inv₀ (norm_ne_zero_iff.mpr hx)).smul continuousAt_id) ?_
      filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
      simp [nrm, mem_compl_singleton_iff.mp hy]
  obtain ⟨P, hPsmooth, hPdist⟩ := exists_contDiff_dist_lt_on_compact ⟨R, hRcont⟩
    (isCompact_closedBall (0 : Eucl m) 1) (by norm_num : (0 : ℝ) < 1 / 4)
  let b : ContDiffBump (0 : Eucl m) := ⟨1 / 2, 3 / 4, by norm_num, by norm_num⟩
  let Q (x : Eucl m) : Eucl m := b x • P x + (1 - b x) • x
  have hQsmooth : ContDiff ℝ ∞ Q :=
    (b.contDiff.smul hPsmooth).add ((contDiff_const.sub b.contDiff).smul contDiff_id)
  have hQne (x : Eucl m) : Q x ≠ 0 := by
    by_cases hx2 : 3 / 4 ≤ ‖x‖
    · have hb0 : b x = 0 := b.zero_of_le_dist (by simpa [b] using hx2)
      intro h0; simp [Q, hb0] at h0; simp [h0] at hx2; linarith
    · have hd : ‖P x - R x‖ < 1 / 4 := by simpa [dist_eq_norm] using hPdist x (by simp; linarith)
      have hPR : 3 / 4 < ⟪P x, R x⟫ := by
        have hcs := abs_real_inner_le_norm (P x - R x) (R x)
        rw [hRnorm x, mul_one] at hcs
        rw [show ⟪P x, R x⟫ = ⟪R x, R x⟫ + ⟪P x - R x, R x⟫ by rw [inner_sub_left]; ring,
          real_inner_self_eq_norm_sq, hRnorm x]
        linarith [abs_le.mp hcs]
      have hQR : 0 < ⟪Q x, R x⟫ := by
        dsimp only [Q]; rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
        by_cases hx1 : ‖x‖ ≤ 1 / 2
        · rw [b.one_of_mem_closedBall (by simpa [b] using hx1)]; linarith
        · have hx1' : 1 / 2 < ‖x‖ := lt_of_not_ge hx1
          have hxR : ⟪x, R x⟫ = ‖x‖ := by
            rw [hRrad x hx1'.le, inner_smul_right, real_inner_self_eq_norm_sq]
            have : ‖x‖ ≠ 0 := by linarith
            field_simp
          rw [hxR]; nlinarith [b.nonneg (x := x), b.le_one (x := x)]
      intro h0; simp [h0] at hQR
  refine no_smooth_sphere_retraction volume (fun x => ‖Q x‖⁻¹ • Q x) ?_ ?_ ?_
  · exact contDiff_iff_contDiffAt.mpr fun x =>
      ((hQsmooth.contDiffAt.norm ℝ (hQne x)).inv (norm_ne_zero_iff.mpr (hQne x))).smul hQsmooth.contDiffAt
  · intro x; rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hQne x))]
  · intro x hx
    dsimp only [Q]
    rw [show b x = 0 from b.zero_of_le_dist (by simp [b, hx]; norm_num)]
    simp [hx]

section Obstruction
open GS.NonmanifoldClosure GS.NonmanifoldFinal GS.NonmanifoldObstruction

theorem sphere_retract_ball_dimension (m n : ℕ) {r : ℝ} (hr : 0 < r)
    (p : ContinuousSectionPair (UnitSphere (Fin m))
      (PuncturedNormBall (EuclideanSpace ℝ (Fin n)) r)) : n = m := by
  let a : C(UnitSphere (Fin m), PuncturedNormBall (EuclideanSpace ℝ (Fin n)) r) :=
    ⟨p.sectionMap, p.section_continuous⟩
  let b : C(PuncturedNormBall (EuclideanSpace ℝ (Fin n)) r, UnitSphere (Fin m)) :=
    ⟨p.retractionMap, p.retraction_continuous⟩
  let v : C(PuncturedNormBall (EuclideanSpace ℝ (Fin n)) r, UnitSphere (Fin n)) :=
    (⟨normSphereStandard n, (normSphereStandard n).continuous⟩ :
      C(NormSphere (EuclideanSpace ℝ (Fin n)), UnitSphere (Fin n))).comp ⟨ballNormalize, continuous_ballNormalize r⟩
  let w : C(UnitSphere (Fin n), PuncturedNormBall (EuclideanSpace ℝ (Fin n)) r) :=
    (⟨ballSection hr, continuous_ballSection hr⟩ :
      C(NormSphere (EuclideanSpace ℝ (Fin n)), PuncturedNormBall (EuclideanSpace ℝ (Fin n)) r)).comp
      ⟨(normSphereStandard n).symm, (normSphereStandard n).symm.continuous⟩
  let s := v.comp a
  let t := b.comp w
  have hid : ContinuousMap.Homotopic (t.comp s) (ContinuousMap.id (UnitSphere (Fin m))) :=
    ⟨{ toFun := fun z => b (radialDeform hr (z.1, a z.2))
       continuous_toFun := b.continuous.comp
         ((continuous_radialDeform hr).comp (continuous_fst.prodMk (a.continuous.comp continuous_snd)))
       map_zero_left := fun x => congrArg b <| by
         change radialDeform hr (0, a x) = ballSection hr ((normSphereStandard n).symm ((normSphereStandard n) (ballNormalize (a x))))
         rw [Homeomorph.symm_apply_apply]; exact (puncturedBallHomotopy hr).map_zero_left (a x)
       map_one_left := fun x =>
         (congrArg b ((puncturedBallHomotopy hr).map_one_left (a x))).trans (p.retraction_section x) }⟩
  by_contra hne
  have hnull : (t.comp s).Nullhomotopic := by
    rcases lt_or_gt_of_ne hne with hnm | hmn
    · exact (sphereMap_nullhomotopic_of_finrank_lt (by simpa using hnm) t).comp_left s
    · exact (sphereMap_nullhomotopic_of_finrank_lt (by simpa using hmn) s).comp_right t
  obtain ⟨c, hc⟩ := hnull
  exact sphere_id_not_nullhomotopic m ⟨c, hid.symm.trans hc⟩
end Obstruction

end GS.Topology
