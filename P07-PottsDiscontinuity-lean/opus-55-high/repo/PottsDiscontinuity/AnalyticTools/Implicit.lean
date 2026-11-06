module

public import PottsDiscontinuity.AnalyticTools.Inverse

/-!
# Real analytic implicit functions in finite dimension

For an equation `F (t, x) = 0`, the map `(t, x) ↦ (t, F (t, x))` has an invertible derivative
whenever the derivative of `F` in `x` is invertible.  Applying the analytic inverse theorem to
that map gives a local analytic solution branch.
-/

public section

open Filter
open scoped Topology

namespace PottsDiscontinuity.AnalyticTools

noncomputable def parameterShear
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ →L[ℝ] E) : (ℝ × E) ≃L[ℝ] (ℝ × E) where
  toFun p := (p.1, A p.1 + p.2)
  invFun p := (p.1, p.2 - A p.1)
  left_inv p := by simp
  right_inv p := by simp
  map_add' p q := by
    change (p.1 + q.1, A (p.1 + q.1) + (p.2 + q.2)) =
      (p.1 + q.1, A p.1 + p.2 + (A q.1 + q.2))
    grind
  map_smul' c p := by
    change (c • p.1, A (c • p.1) + c • p.2) =
      (c • p.1, c • (A p.1 + p.2))
    rw [map_smul, smul_add]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {F : ℝ × E → E} {t₀ : ℝ} {x₀ : E} (hF : AnalyticAt ℝ F (t₀, x₀)) (hzero : F (t₀, x₀) = 0) (e : E ≃L[ℝ] E) (hDx : (fderiv ℝ F (t₀, x₀)).comp (ContinuousLinearMap.inr ℝ ℝ E) = (e : E →L[ℝ] E))
include hF hzero e hDx
/-- A finite-dimensional real analytic implicit function theorem with a one-dimensional
parameter.  The branch is defined on all of `ℝ` by the local inverse's totalized inverse map;
the equation is asserted on a neighborhood of the base parameter. -/
theorem exists_analytic_implicitFunction_with_local_uniqueness
     :
    ∃ ψ : ℝ → E,
      ψ t₀ = x₀ ∧ AnalyticAt ℝ ψ t₀ ∧
      ∃ W : Set (ℝ × E), ∃ V : Set ℝ,
        IsOpen W ∧ IsOpen V ∧ (t₀, x₀) ∈ W ∧ t₀ ∈ V ∧
        (∀ t ∈ V, (t, ψ t) ∈ W ∧ F (t, ψ t) = 0) ∧
        (∀ t y, (t, y) ∈ W → F (t, y) = 0 → y = ψ t) := by
  let z₀ := (t₀, x₀)
  let D := fderiv ℝ F z₀
  let A := D.comp (ContinuousLinearMap.inl ℝ ℝ E)
  let J :=
    (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) e).trans
      (parameterShear A)
  let g := fun z => (z.1, F z)
  let Dg :=
    (ContinuousLinearMap.fst ℝ ℝ E).prod D
  have hsplit (z : ℝ × E) : D z = A z.1 + (e : E →L[ℝ] E) z.2 := by
    have hz : z = ContinuousLinearMap.inl ℝ ℝ E z.1 +
        ContinuousLinearMap.inr ℝ ℝ E z.2 := by
      simp
    grind
  have hJ (z : ℝ × E) : J z = (z.1, A z.1 + e z.2) := by
    rfl
  have hDg (z : ℝ × E) : Dg z = (z.1, D z) := by
    rfl
  have hlin : Dg = (J : (ℝ × E) →L[ℝ] (ℝ × E)) := by
    apply DFunLike.ext
    simp_all
  have hGanalytic :=
    analyticAt_fst.prod hF
  have hGstrict : HasStrictFDerivAt g (J : (ℝ × E) →L[ℝ] (ℝ × E)) z₀ := by
    have h : HasStrictFDerivAt g Dg z₀ :=
      (hasStrictFDerivAt_fst (𝕜 := ℝ)).prodMk hF.hasStrictFDerivAt
    simp_all
  have hzero' : g z₀ = (t₀, 0) := by grind
  have hinverse := analyticAt_localInverse hGanalytic hGstrict
  let R := hGstrict.toOpenPartialHomeomorph g
  let q : ℝ → ℝ × E := fun t => (t, 0)
  let pairBranch := R.symm ∘ q
  let ψ := fun t => (pairBranch t).2
  have hsource := hGstrict.mem_toOpenPartialHomeomorph_source
  have hψ₀ : ψ t₀ = x₀ := by
    have hqbase : q t₀ = g z₀ := by grind
    have hleft : R.symm (q t₀) = z₀ := by
      simpa [R, hqbase] using R.left_inv hsource
    grind
  have hinverse' : AnalyticAt ℝ R.symm (t₀, (0 : E)) := by
    grind
  have hpair : AnalyticAt ℝ pairBranch t₀ := by
    fun_prop
  have hψanalytic :=
    (analyticAt_snd (𝕜 := ℝ)).comp hpair
  have himage : g z₀ ∈ R.target := hGstrict.image_mem_toOpenPartialHomeomorph_target
  have hqtarget : (t₀, (0 : E)) ∈ R.target := by simp_all
  have hqcontinuous : Continuous q := by fun_prop
  let V := q ⁻¹' R.target
  refine ⟨ψ, hψ₀, hψanalytic, R.source, V, R.open_source, (IsOpen.preimage hqcontinuous R.open_target), hsource, hqtarget, ?_, ?_⟩
  · intro t ht
    have htarg := ht
    have hbranchsource :=
      R.map_target htarg
    have heq : g (pairBranch t) = q t := by
      simpa [pairBranch, R] using R.right_inv htarg
    grind
  · intro t y hyW hyzero
    have hleft := R.left_inv hyW
    change R.symm (g (t, y)) = (t, y) at hleft
    grind

/-- The usual local analytic implicit function theorem, with the equation asserted on a
neighborhood of the base parameter. -/
theorem exists_analytic_implicitFunction
     :
    ∃ ψ : ℝ → E,
      ψ t₀ = x₀ ∧ AnalyticAt ℝ ψ t₀ ∧
      ∀ᶠ t in 𝓝 t₀, F (t, ψ t) = 0 := by
  obtain ⟨ψ, hψ₀, hψanalytic, W, V, hWopen, hVopen, hWbase, hVbase, hbranch, hunique⟩ :=
    exists_analytic_implicitFunction_with_local_uniqueness hF hzero e hDx
  refine ⟨ψ, hψ₀, hψanalytic, ?_⟩
  filter_upwards [hVopen.mem_nhds hVbase] with t ht
  simp_all
end

end PottsDiscontinuity.AnalyticTools
