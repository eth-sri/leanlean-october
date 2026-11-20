module

public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Tactic.FunProp
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.Topology.TietzeExtension
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Complex.Tietze
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Tactic.Module
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Topology.ContinuousMap.Interval

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

open Set Metric Function
open scoped Topology unitInterval
namespace GS.Topology
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Normalize a continuous, nowhere-zero map to the unit sphere. -/
def sphereNormalize {X : Type*} [TopologicalSpace X] (g : C(X, F))
    (hg : ∀ x, g x ≠ 0) : C(X, sphere (0 : F) 1) :=
  ⟨fun x => ⟨NormedSpace.normalize (g x), mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize (hg x))⟩,
    ((g.continuous.norm.inv₀ fun x => norm_ne_zero_iff.mpr (hg x)).smul g.continuous).subtype_mk _⟩

private theorem ne_zero_of_dist_lt_norm {v w : F} (h : dist w v < ‖v‖) : w ≠ 0 := by
  rintro rfl
  simp at h

/-- A continuous approximation within distance one of a sphere map becomes
homotopic to that map after normalization. -/
theorem homotopic_sphereNormalize_of_dist_lt_one {X : Type*} [TopologicalSpace X]
    (f : C(X, sphere (0 : F) 1)) (g : C(X, F)) (hg : ∀ x, g x ≠ 0)
    (hclose : ∀ x, dist (g x) (f x : F) < 1) :
    f.Homotopic (sphereNormalize g hg) := by
  let a : C(unitInterval × X, F) :=
    ⟨fun z => (1 - (z.1 : ℝ)) • (f z.2 : F) + (z.1 : ℝ) • g z.2, by
      fun_prop⟩
  have ha (z : unitInterval × X) : a z ≠ 0 := by
    apply ne_zero_of_dist_lt_norm (v := (f z.2 : F))
    rw [mem_sphere_zero_iff_norm.mp (f z.2).property]
    exact convex_ball (f z.2 : F) 1 (by simp) (hclose z.2)
      (sub_nonneg.mpr z.1.property.2) z.1.property.1 (sub_add_cancel ..)
  refine ⟨⟨sphereNormalize a ha, ?_, ?_⟩⟩ <;> intro x <;> apply Subtype.ext
  · simp [sphereNormalize, a, NormedSpace.normalize_eq_self_of_norm_eq_one
      (mem_sphere_zero_iff_norm.mp (f x).property)]
  · simp [sphereNormalize, a]

/-!
# Nullhomotopy of maps between spheres of increasing dimension

The proof extends a sphere map continuously to the ambient vector space,
approximates the extension by a smooth map near the compact source sphere,
and subtracts a sufficiently small point outside the smooth map's range.
The resulting map never vanishes and hence normalizes to a sphere-valued
map on the entire, contractible ambient vector space.

All approximation and dimension facts are theorems of the pinned mathlib;
no homology or homotopy computation is assumed.
-/

open Filter
open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Every map between unit spheres is nullhomotopic if the source ambient
vector space has strictly smaller real dimension than the target.

For spheres `S^k` and `S^m`, the hypothesis is precisely `k < m`.
The assertion concerns arbitrary continuous maps and the usual subspace
topology on the spheres. -/
theorem sphereMap_nullhomotopic_of_finrank_lt
    (hdim : Module.finrank ℝ E < Module.finrank ℝ F)
    (f : C(sphere (0 : E) 1, sphere (0 : F) 1)) : f.Nullhomotopic := by
  let : TietzeExtension F := TietzeExtension.of_tvs ℝ
  let fF : C(sphere (0 : E) 1, F) :=
    ⟨fun x => f x, continuous_subtype_val.comp f.continuous⟩
  obtain ⟨f₀, hf₀⟩ := fF.exists_restrict_eq isClosed_sphere
  obtain ⟨g, hgc, hg, -⟩ := f₀.continuous.exists_contDiff_approx (⊤ : ℕ∞)
    (ε := fun _ => 1/2) continuous_const (fun _ => by norm_num)
  have hdense := (hgc.differentiable (by simp)).dense_compl_range_of_finrank_lt_finrank hdim
  obtain ⟨y, hy, hyε⟩ := hdense.exists_dist_lt 0 (by norm_num : (0 : ℝ) < 1/2)
  let gC : C(E, F) := ⟨fun x => g x - y, hgc.continuous.sub continuous_const⟩
  have hg0 (x : E) : gC x ≠ 0 := fun h => hy ⟨x,sub_eq_zero.mp h⟩
  have hclose (x : sphere (0 : E) 1) : dist (gC.restrict _ x) (f x : F) < 1 := by
    have h : f₀ x = (f x : F) := DFunLike.congr_fun hf₀ x
    calc
      dist (g x - y) (f x : F) ≤ dist (g x - y) (g x) + dist (g x) (f x : F) := dist_triangle ..
      _ < 1/2 + 1/2 := add_lt_add (by simpa [dist_eq_norm] using hyε) (h ▸ hg x)
      _ = 1 := by norm_num
  have hfg := homotopic_sphereNormalize_of_dist_lt_one f (gC.restrict _) (fun x => hg0 x) hclose
  have hn : (sphereNormalize gC hg0).Nullhomotopic := by
    simpa using (id_nullhomotopic E).comp_right (sphereNormalize gC hg0)
  obtain ⟨c,hc⟩ := hn.comp_left (⟨Subtype.val,continuous_subtype_val⟩ : C(sphere (0 : E) 1,E))
  exact ⟨c, hfg.trans hc⟩

/-! The no-retraction argument via change of variables. The Jacobian integral of
an affine perturbation of the identity is polynomial in the perturbation parameter.
It equals the ball's volume for small parameters, so it still does at the endpoint. -/

open MeasureTheory MeasureTheory.Measure Polynomial NormedSpace _root_.Topology
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Delay the sphere homotopy until a positive radius, so the angular
coordinate disappears near the origin. -/
private theorem smooth_sphere_extension
    (h : (ContinuousMap.id (sphere (0 : E) 1)).Nullhomotopic) :
    ∃ f : E → E, ContDiff ℝ ∞ f ∧ (∀ x, ‖f x‖ = 1) ∧
      ∀ x, ‖x‖ = 1 → f x = x := by
  classical
  obtain ⟨u,⟨h⟩⟩ := h
  let t (x : E) : unitInterval := projIcc 0 1 zero_le_one (2 * ‖x‖ - 1)
  let U (x : E) : sphere (0 : E) 1 :=
    if hx : x = 0 then u else ⟨normalize x, mem_sphere_zero_iff_norm.mpr (norm_normalize hx)⟩
  let F (x : E) := (h.symm (t x,U x) : E)
  have ht : Continuous t := (continuous_projIcc (h := zero_le_one)).comp (by fun_prop)
  have hc : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x = 0
    · subst x
      apply (continuousAt_const (y := (u : E))).congr
      filter_upwards [Metric.ball_mem_nhds (0 : E) (by norm_num : 0 < (1/2 : ℝ))] with y hy
      rw [mem_ball_zero_iff] at hy
      have hty : t y = 0 := projIcc_eq_zero.mpr (by linarith)
      simp [F, hty]
    have hU : ContinuousAt U x := by
      apply IsInducing.subtypeVal.continuousAt_iff.mpr
      apply (((continuous_norm.continuousAt (x := x)).inv₀ (norm_ne_zero_iff.mpr hx)).smul continuousAt_id).congr
      filter_upwards [isOpen_compl_singleton.mem_nhds (show x ∈ {0}ᶜ from hx)] with y hy
      simp [U, NormedSpace.normalize, show y ≠ 0 from hy]
    exact continuous_subtype_val.continuousAt.comp
      (h.symm.continuous.continuousAt.comp (ht.continuousAt.prodMk hU))
  have hnorm (x : E) : ‖F x‖ = 1 := mem_sphere_zero_iff_norm.mp (h.symm _).property
  have hfix (x : E) (hx : ‖x‖ = 1) : F x = x := by
    have htx : t x = 1 := projIcc_eq_one.mpr (by norm_num [hx])
    have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (by simp [hx])
    simp [F, htx, U, hx0, normalize_eq_self_of_norm_eq_one hx]
  obtain ⟨g,hg,hclose,hsupp⟩ := (hc.sub continuous_id).exists_contDiff_approx (⊤ : ℕ∞)
    (ε := fun _ => 1) continuous_const (fun _ => zero_lt_one)
  let v (x : E) := x + g x
  have hv : ContDiff ℝ ∞ v := contDiff_id.add hg
  have hne (x : E) : v x ≠ 0 := by
    apply ne_zero_of_dist_lt_norm (v := F x)
    rw [hnorm, dist_eq_norm, show v x - F x = g x - (F x - x) by dsimp [v]; abel, ← dist_eq_norm]
    exact hclose x
  refine ⟨fun x => normalize (v x),
    (hv.norm ℝ hne |>.inv (fun x => norm_ne_zero_iff.mpr (hne x))).smul hv,
    fun x => norm_normalize (hne x), fun x hx => ?_⟩
  have hg0 : g x = 0 := notMem_support.mp <| mt (hsupp (a := x)) (by
    simpa using sub_eq_zero.mpr (hfix x hx))
  simpa [v, hg0] using normalize_eq_self_of_norm_eq_one hx

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsAddHaarMeasure μ]

/-- Take the determinant over polynomials with continuous-function coefficients,
then integrate each coefficient over the bounded domain. -/
private theorem integral_det_poly {s : Set E} {K : Set E} (hK : IsCompact K) (hs : s ⊆ K)
    {D : E → E →L[ℝ] E} (hD : Continuous D) :
    ∃ p : ℝ[X], ∀ t, p.eval t = ∫ x in s, ((1 : E →L[ℝ] E) + t • D x).det ∂μ := by
  let b := Module.finBasis ℝ E
  let A := (LinearMap.toMatrix b b).toLinearMap.comp (ContinuousLinearMap.coeLM ℝ)
  let B := fun i j => (⟨fun x => A (D x) i j,
    (A.continuous_of_finiteDimensional.comp hD).matrix_elem i j⟩ : C(E,ℝ))
  let p := ((1 : Matrix _ _ C(E,ℝ)[X]) + (X : C(E,ℝ)[X]) • (Matrix.of B).map C).det
  let ev (t : ℝ) (x : E) : C(E, ℝ)[X] →+* ℝ :=
    eval₂RingHom (ContinuousMap.evalAlgHom ℝ ℝ x).toRingHom t
  have he (t : ℝ) (x : E) : ev t x p = ((1 : E →L[ℝ] E) + t • D x).det := by
    change ev t x p = LinearMap.det (1 + t • (D x).toLinearMap)
    rw [← LinearMap.det_toMatrix b, map_add, map_smul, LinearMap.toMatrix_one]
    dsimp only [p]
    rw [(ev t x).map_det, map_add, map_one]
    congr 2
    ext i j
    change ev t x (X * C (B i j)) = t * A (D x) i j
    simp [ev, B, A, mul_comm t]
  refine ⟨p.sum fun k c => monomial k (∫ x in s, c x ∂μ), fun t => ?_⟩
  simp only [Polynomial.sum, Polynomial.eval_finsetSum, eval_monomial]
  simp_rw [← he, ev, coe_eval₂RingHom, eval₂_eq_sum]
  simp only [Polynomial.sum]
  rw [integral_finsetSum]
  · simp [integral_mul_const]
  · exact fun k _ => (((p.coeff k).continuous.continuousOn.integrableOn_compact hK).mono_set hs).mul_const _

/-- A smooth sphere-valued map cannot restrict to the identity on the unit sphere. -/
private theorem impossible_smooth_sphere (μ : Measure E) [IsAddHaarMeasure μ]
    {f : E → E} (hf : ContDiff ℝ ∞ f) (hfn : ∀ x, ‖f x‖ = 1)
    (hrad : ∀ x, ‖x‖ = 1 → f x = x) : False := by
  let := nontrivial_of_ne (f 0) 0 (norm_ne_zero_iff.mp (by simp [hfn]))
  let B := ball (0 : E) 1
  let K := closedBall (0 : E) 1
  let g : E → E := fun x => f x - x
  have hg : ContDiff ℝ ∞ g := hf.sub contDiff_id
  have hK : IsCompact K := isCompact_closedBall _ _
  obtain ⟨L,hL⟩ := hg.contDiffOn.exists_lipschitzOnWith (by simp) (convex_closedBall _ _) hK
  let D := fderiv ℝ g
  let φ := fun (t : ℝ) (x : E) => x + t • g x
  have hφ (t : ℝ) (x : E) : HasFDerivAt (φ t) (1 + t • D x) x :=
    (hasFDerivAt_id x).add ((hg.differentiable (by simp) x).hasFDerivAt.const_smul t)
  have hD : Continuous D := hg.continuous_fderiv (by simp)
  have hpos : ∀ᶠ t : ℝ in 𝓝 0, ∀ x ∈ K, 0 < ((1 : E →L[ℝ] E) + t • D x).det := by
    apply hK.eventually_forall_of_forall_eventually
    intro x _
    have h : Continuous (fun p : ℝ × E => ((1 : E →L[ℝ] E) + p.1 • D p.2).det) :=
      ContinuousLinearMap.continuous_det.comp (by fun_prop)
    exact continuousAt_const.eventually_lt (h.continuousAt (x := (0, x))) (by simp [ContinuousLinearMap.det])
  have hB (t : ℝ) (ht : 0 ≤ t) (ht₁ : t < 1) (htL : t * L < 1) : InjOn (φ t) B ∧ φ t '' B = B := by
    let e := ContinuousLinearEquiv.refl ℝ E
    have ha : ApproximatesLinearOn (φ t) (e : E →L[ℝ] E) B (‖t‖₊ * L) := by
      apply LipschitzOnWith.approximatesLinearOn
      rw [show φ t - ⇑(e : E →L[ℝ] E) = (fun z : E => t • z) ∘ g by ext x; simp [φ, e]]
      exact (lipschitzWith_smul t).comp_lipschitzOnWith (hL.mono ball_subset_closedBall)
    have hc : Subsingleton E ∨ ‖t‖₊ * L < ‖(e.symm : E →L[ℝ] E)‖₊⁻¹ := Or.inr <| by
      apply NNReal.coe_lt_coe.mp
      simpa [e, Real.nnnorm_of_nonneg ht] using htL
    have hinto : φ t '' B ⊆ B := by
      rintro _ ⟨x,hx,rfl⟩
      have hB' : interior K = B := interior_closedBall _ one_ne_zero
      rw [← hB'] at hx ⊢
      rw [show φ t x = (1-t) • x + t • f x by dsimp [φ,g]; module]
      exact (convex_closedBall _ _).combo_interior_self_mem_interior hx
        (mem_closedBall_zero_iff.mpr (hfn x).le) (sub_pos.mpr ht₁) ht (sub_add_cancel ..)
    refine ⟨ha.injOn hc, hinto.antisymm ?_⟩
    apply (convex_ball (0 : E) 1).isPreconnected.subset_of_closure_inter_subset
      (ha.toOpenPartialHomeomorph _ _ hc isOpen_ball).open_target
    · have hz : φ t 0 ∈ φ t '' B := mem_image_of_mem _ (mem_ball_self zero_lt_one)
      exact ⟨_,hinto hz,hz⟩
    rintro x ⟨hx,hx'⟩
    have hm := closure_minimal (image_mono (ball_subset_closedBall : B ⊆ K))
      ((hK.image (continuous_id.add (hg.continuous.const_smul t))).isClosed) hx
    have hfix : EqOn (φ t) id (sphere 0 1) := fun z hz => by
      simp [φ,g,hrad z (mem_sphere_zero_iff_norm.mp hz)]
    change x ∈ φ t '' K at hm
    rw [show K = B ∪ sphere 0 1 from ball_union_sphere.symm, image_union, hfix.image_eq, image_id] at hm
    exact hm.elim id fun hs => (sphere_disjoint_ball.le_bot ⟨hs,hx'⟩).elim
  obtain ⟨p,hp⟩ := integral_det_poly (μ := μ) hK (ball_subset_closedBall : B ⊆ K) hD
  let V : ℝ := ∫ _ in B, (1 : ℝ) ∂μ
  have heq : ∀ᶠ t : ℝ in 𝓝[>] 0, p.eval t = V := by
    have hsmall : ∀ᶠ t : ℝ in 𝓝 0, t < 1 ∧ t * (L : ℝ) < 1 :=
      (continuous_id.continuousAt.eventually_lt continuousAt_const zero_lt_one).and <|
        (continuous_id.mul continuous_const).continuousAt.eventually_lt
          continuousAt_const (by simp : (0 : ℝ) * L < 1)
    filter_upwards [(hpos.and hsmall).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ⟨h₀,ht,htL⟩ htpos
    obtain ⟨hinj, him⟩ := hB t (le_of_lt htpos) ht htL
    have hh := integral_image_eq_integral_abs_det_fderiv_smul μ (s := B) measurableSet_ball
      (fun x _ => (hφ t x).hasFDerivWithinAt) hinj (fun _ => (1 : ℝ))
    rw [him] at hh
    rw [hp]
    exact (integral_congr_ae (ae_restrict_mem measurableSet_ball |>.mono fun x hx => by
      simp [abs_of_pos (h₀ x (ball_subset_closedBall hx))])).trans hh.symm
  have hconst : p = C V := Polynomial.eq_of_infinite_eval_eq _ _ <| by
    obtain ⟨ε,hε,hI⟩ := (mem_nhdsGT_iff_exists_Ioo_subset.mp heq)
    exact (Set.Ioo_infinite hε).mono fun t ht => by simpa using hI ht
  have hz (x : E) : ((1 : E →L[ℝ] E) + (1 : ℝ) • D x).det = 0 := by
    let A : E →L[ℝ] E := 1 + (1 : ℝ) • D x
    have hd : HasFDerivAt f A x := by
      simpa only [A,φ,g,one_smul,add_sub_cancel] using hφ 1 x
    by_contra hn
    have hs : Surjective A := ((Module.End.isUnit_iff A.toLinearMap).mp
      ((LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hn))).2
    obtain ⟨v,hv⟩ := hs (f x)
    have heq := hd.norm_sq.fderiv
    simp only [hfn, fderiv_const_apply] at heq
    have h := DFunLike.congr_fun heq v
    change 0 = (2 : ℕ) • inner ℝ (f x) (A v) at h
    simp [hv, hfn] at h
  have hv : 0 < V := by
    simpa [V, measureReal_def] using ENNReal.toReal_pos (measure_ball_pos μ (0 : E) zero_lt_one).ne'
      (measure_ball_lt_top (μ := μ)).ne
  have h := hp 1
  rw [hconst, eval_C] at h
  rw [integral_congr_ae (ae_restrict_mem measurableSet_ball |>.mono fun x _ => hz x), integral_zero] at h
  exact hv.ne' h

omit [MeasurableSpace E] [BorelSpace E] in
theorem sphere_id_not_nullhomotopic : ¬ (ContinuousMap.id (sphere (0 : E) 1)).Nullhomotopic := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  intro h
  obtain ⟨f,hf,hn,hr⟩ := smooth_sphere_extension h
  exact impossible_smooth_sphere (Module.finBasis ℝ E).addHaar hf hn hr

end GS.Topology
