module
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Algebra.Group.Matrix
@[expose] public section

/-! Milnor's volume argument: the integral of the signed Jacobian of a
perturbation of the identity is polynomial in the size of the perturbation.
Small Lipschitz perturbations fixing the exterior preserve the volume of a
ball by change of variables. Polynomiality extends the identity to any size. -/
noncomputable section
open Set Metric MeasureTheory Polynomial Matrix Filter
open scoped Topology Polynomial NNReal
namespace GS.Jacobian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
private abbrev ev (x : E) := (ContinuousMap.evalAlgHom ℝ ℝ x).toRingHom

private lemma integral_poly (p : C(E,ℝ)[X]) {K : Set E} (hK : IsCompact K) :
    ∃ q : ℝ[X], ∀ t, q.eval t = ∫ x in K, p.eval₂ (ev x) t ∂μ := by
  refine ⟨∑ i ∈ p.support, monomial i (∫ x in K, p.coeff i x ∂μ),fun t => ?_⟩
  simp only [eval_finsetSum,eval_monomial,eval₂_eq_sum,Polynomial.sum]
  rw [integral_finsetSum]; congr 1; funext i; exact (integral_mul_const _ _).symm
  intro i hi; exact ((p.coeff i).continuous.mul continuous_const).continuousOn.integrableOn_compact hK

local notation "V" => E →L[ℝ] E
local notation "Id" => ContinuousLinearMap.id ℝ E
lemma det_poly {u : E → V} (hu : Continuous u) {K : Set E} (hK : IsCompact K) :
    ∃ q : ℝ[X], ∀ t, q.eval t = ∫ x in K, (Id + t • u x).det ∂μ := by
  let b := Module.finBasis ℝ E
  let a i j : C(E,ℝ) := ⟨fun x => b.equivFunL (u x (b j)) i, by fun_prop⟩
  let M : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) C(E,ℝ)[X] := 1 + (X : C(E,ℝ)[X]) • (Matrix.of a).map (Polynomial.C : C(E,ℝ) →+* _)
  obtain ⟨q,hq⟩ := integral_poly μ M.det hK
  refine ⟨q,fun t => (hq t).trans ?_⟩
  congr 1; funext x
  let e := eval₂RingHom (ev x) t
  change e M.det = LinearMap.det (Id + t • u x).toLinearMap
  rw [RingHom.map_det, ← LinearMap.det_toMatrix b]
  congr 1; ext i j
  simp [a,M,e,LinearMap.toMatrix_apply,one_apply]
  by_cases h : i = j <;> simp [h,Finsupp.single_apply,Ne.symm,mul_comm]

section Ball
variable {r : ℝ}
local notation "K" => closedBall (0 : E) r

/-- Extend a Lipschitz displacement by zero. For points on opposite sides
of the sphere the intermediate value theorem provides a boundary point. -/
private lemma extend_lip {u : E → E} {k : ℝ≥0} (h : LipschitzOnWith k u K)
    (hz : ∀ x, ‖x‖ = r → u x = 0) : LipschitzWith k ((K).indicator u) := by
  have cross {x y : E} (hx : x ∈ K) (hy : y ∉ K) : dist (u x) 0 ≤ k * dist x y := by
    have b : y ∈ closedBall x (dist x y) := by simp [dist_comm]
    obtain ⟨z,hz',he⟩ := (convex_closedBall _ _).isPreconnected.intermediate_value (mem_closedBall_self dist_nonneg) b continuous_norm.continuousOn
      (show r ∈ Icc ‖x‖ ‖y‖ from ⟨mem_closedBall_zero_iff.mp hx, le_of_not_ge (fun h => hy (mem_closedBall_zero_iff.mpr h))⟩)
    rw [← hz z he]; exact (h.dist_le_mul x hx z (mem_closedBall_zero_iff.mpr he.le)).trans
      (mul_le_mul_of_nonneg_left (by simpa [dist_comm] using hz') k.coe_nonneg)
  apply LipschitzWith.of_dist_le_mul; intro x y
  by_cases hx : x ∈ K <;> by_cases hy : y ∈ K
  · simpa [hx,hy] using h.dist_le_mul x hx y hy
  · simpa [hx,hy] using cross hx hy
  · simpa [hx,hy,dist_comm] using cross hy hx
  · simp [hx,hy,mul_nonneg]

lemma signed_volume (g : E → E) (hg : ContDiff ℝ 1 g) (hfix : ∀ x, ‖x‖ = r → g x = x) :
    ∫ x in K, (fderiv ℝ g x).det ∂μ = μ.real K := by
  classical
  let u := (K).indicator (g-id)
  let d := fun x => fderiv ℝ g x - Id
  have hd : Continuous d := (hg.continuous_fderiv one_ne_zero).sub continuous_const
  obtain ⟨q,hq⟩ := det_poly μ hd (isCompact_closedBall (0:E) r)
  obtain ⟨k,hl⟩ := (hg.sub contDiff_id).contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_closedBall (0:E) r) (isCompact_closedBall _ _)
  have hu : LipschitzWith k u := extend_lip hl (fun x h => by simp [hfix _ h])
  have hc : ∀ᶠ t : ℝ in 𝓝 0, ‖t‖₊ * k < 1 := (continuous_nnnorm.mul continuous_const).continuousAt.eventually_lt continuousAt_const (by simp)
  have pos : ∀ᶠ t : ℝ in 𝓝 0, ∀ x ∈ K, 0 < (Id + t • d x).det := by
    apply (isCompact_closedBall _ _).eventually_forall_of_forall_eventually; intro x hx
    have h : Continuous (fun z : ℝ × E => (Id + z.1 • d z.2).det) :=
      ContinuousLinearMap.continuous_det.comp (continuous_const.add (continuous_fst.smul (hd.comp continuous_snd)))
    exact continuousAt_const.eventually_lt h.continuousAt (by simp [ContinuousLinearMap.det])
  have H : ∀ᶠ t : ℝ in 𝓝 0, q.eval t = (C (μ.real K)).eval t := by
    filter_upwards [hc,pos] with t ht hp
    let f x := x + t • u x
    have ap : ApproximatesLinearOn f Id univ (‖t‖₊ * k) := by
      apply LipschitzOnWith.approximatesLinearOn
      simpa [f,Pi.sub_def,Function.comp_def] using! ((lipschitzWith_smul t).comp hu).lipschitzOnWith (s := univ)
    let e := ContinuousLinearEquiv.refl ℝ E
    have ok : Subsingleton E ∨ ‖t‖₊ * k < ‖e.symm.toContinuousLinearMap‖₊⁻¹ := by
      rcases subsingleton_or_nontrivial E with h|h
      · exact Or.inl h
      · exact Or.inr (by simpa [e] using ht)
    have bij : Function.Bijective f := ⟨injOn_univ.mp (ap.injOn (f' := e) ok),ap.surjective (f' := e) ok⟩
    have fix {x} (hx : x ∉ K) : f x = x := by simp [f,u,hx]
    have im : f '' K = K := compl_injective ((image_compl_eq bij).symm.trans (EqOn.image_eq_self (s := Kᶜ) (fun _ hx => fix hx)))
    have df (x) (hx : x ∈ K) : HasFDerivWithinAt f (Id + t • d x) K x := by
      have h := (hasFDerivAt_id x).add (((hg.differentiable one_ne_zero x).hasFDerivAt.sub (hasFDerivAt_id x)).const_smul t)
      exact h.hasFDerivWithinAt.congr (fun z hz => by simp [f,u,hz]) (by simp [f,u,hx])
    have eq := integral_image_eq_integral_abs_det_fderiv_smul μ measurableSet_closedBall df bij.1.injOn (fun _ => (1:ℝ))
    rw [im] at eq; rw [hq,eval_C]
    refine Eq.trans (setIntegral_congr_fun measurableSet_closedBall (fun x hx => (abs_of_pos (hp x hx)).symm)) ?_
    simpa using eq.symm
  rw [q.eq_of_infinite_eval_eq _ (infinite_of_mem_nhds 0 H)] at hq
  simpa [d] using (hq 1).symm
end Ball
end GS.Jacobian
