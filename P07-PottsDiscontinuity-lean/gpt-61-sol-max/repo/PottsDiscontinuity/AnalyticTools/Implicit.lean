module
public import Mathlib

public import PottsDiscontinuity.AnalyticTools.Inverse

/-!
# Real analytic implicit functions in finite dimension

For an equation `F (t, x) = 0`, the map `(t, x) ↦ (t, F (t, x))` has an invertible derivative
whenever the derivative of `F` in `x` is invertible.  Applying the analytic inverse theorem to
that map gives a local analytic solution branch.
-/

public section


open scoped Topology

namespace PottsDiscontinuity.AnalyticTools

noncomputable def parameterShear
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ →L[ℝ] E) : (ℝ × E) ≃L[ℝ]  ℝ × E  where
  toFun p := (p.1, A p.1 + p.2)
  invFun p := (p.1, p.2 - A p.1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_add' p q := by
    simp_all <;> grind
  map_smul' c p := by
    change (c • p.1, A (c • p.1) + c • p.2) =
      (c • p.1, c • (A p.1 + p.2))
    rw [map_smul, smul_add]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- A finite-dimensional real analytic implicit function theorem with a one-dimensional
parameter.  The branch is defined on all of `ℝ` by the local inverse's totalized inverse map;
the equation is asserted on a neighborhood of the base parameter. -/
theorem exists_analytic_implicitFunction_with_local_uniqueness
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : ℝ × E → E}
    {t₀ : ℝ} {x₀ : E}
    (hF : AnalyticAt ℝ F (t₀, x₀))
    (hzero : F (t₀, x₀) = 0)
    (e : E ≃L[ℝ] E)
    (hDx : (fderiv ℝ F (t₀, x₀)).comp (ContinuousLinearMap.inr ℝ ℝ E) =
      (e : E →L[ℝ] E)) :
    ∃ ψ : ℝ → E,
      ψ t₀ = x₀ ∧ AnalyticAt ℝ ψ t₀ ∧
      ∃ W : Set (ℝ × E), ∃ V : Set ℝ,
        IsOpen W ∧ IsOpen V ∧ (t₀, x₀) ∈ W ∧ t₀ ∈ V ∧
        (∀ t ∈ V, (t, ψ t) ∈ W ∧ F (t, ψ t) = 0) ∧
         ∀ t y, (t, y) ∈ W → F (t, y) = 0 → y = ψ t  := by
  let z₀  := (t₀, x₀)
  let D  := fderiv ℝ F z₀
  let A  := D.comp (ContinuousLinearMap.inl ℝ ℝ E)
  let J  :=
    (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) e).trans
      (parameterShear A)
  let g  := fun z => (z.1, F z)
  let Dg  :=
    (ContinuousLinearMap.fst ℝ ℝ E).prod D
  have hsplit (z : ℝ × E) : D z = A z.1 +  e  z.2 := by
    have hz : z = ContinuousLinearMap.inl ℝ ℝ E z.1 +
        ContinuousLinearMap.inr ℝ ℝ E z.2 := by
      simp_all
    rw [hz, map_add]
    simp only [ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply,
      Prod.fst_add, Prod.snd_add, zero_add, add_zero]
    
    congr 1
    
    
    
    exact  congrArg (fun L  => L z.2) hDx 
  have hJ (z : ℝ × E) : J z = (z.1, A z.1 + e z.2) := by
    simp [J, parameterShear]
  have hDg (z : ℝ × E) : Dg z = (z.1, D z) := by
    simp [Dg]
  have hlin : Dg =  J  := by
    apply DFunLike.ext
    simp_all
  
  have hGstrict : HasStrictFDerivAt g (J :  ℝ × E  →L[ℝ]  ℝ × E ) z₀ := by
    have h : HasStrictFDerivAt g Dg z₀ := HasStrictFDerivAt.prodMk hasStrictFDerivAt_fst (AnalyticAt.hasStrictFDerivAt hF)
    rw [hlin] at h
    exact h
  have hzero' : g z₀ = (t₀, 0) := by simp [g, z₀, hzero]
  have hinverse := analyticAt_localInverse (analyticAt_fst.prod hF) hGstrict
  let R := hGstrict.toOpenPartialHomeomorph g
  let q : ℝ → ℝ × E := fun t => (t, 0)
  let pairBranch  := R.symm ∘ q
  let ψ  := fun t => (pairBranch t).2
  have hsource  := hGstrict.mem_toOpenPartialHomeomorph_source
  have hψ₀ : ψ t₀ = x₀ := by
    have hqbase : q t₀ = g z₀ := by grind
    have hleft : R.symm (q t₀) = z₀ := by
      simpa [R, hqbase] using R.left_inv hsource
    simp [ψ, pairBranch, z₀, hleft]
  
  have hinverse' : AnalyticAt ℝ R.symm (t₀, 0) := by
    grind
  
  
  have himage  := hGstrict.image_mem_toOpenPartialHomeomorph_target
  have hqtarget : (t₀, (0 )) ∈ R.target := by simpa [← hzero'] using himage
  
  
  
  have hbaseV  := hqtarget
  refine ⟨ψ, hψ₀,  AnalyticAt.comp analyticAt_snd (by
                                                                                                fun_prop) , R.source, (q ⁻¹' R.target), R.open_source,  IsOpen.preimage (by fun_prop) R.open_target , hsource, hbaseV, ?_, ?_⟩
  · intro t ht
    have htarg  := ht
    
    have heq : g (pairBranch t) = q t := OpenPartialHomeomorph.right_inv R htarg
    have hfst : (pairBranch t).1 = t := congrArg Prod.fst heq
    have hpairEq : pairBranch t = (t, ψ t) := by
      apply Prod.ext
      · exact hfst
      · rfl
    
    constructor
    · rw [← hpairEq]
      exact  R.map_target htarg 
    · grind
  · intro t y hyW hyzero
    have hgy : g (t, y) = q t := by simp [g, q, hyzero]
    have hleft := R.left_inv hyW
    change R.symm (g (t, y)) = (t, y) at hleft
    rw [hgy] at hleft
    
    exact (congrArg Prod.snd hleft).symm

/-- The usual local analytic implicit function theorem, with the equation asserted on a
neighborhood of the base parameter. -/
theorem exists_analytic_implicitFunction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : ℝ × E → E}
    {t₀ : ℝ} {x₀ : E}
    (hF : AnalyticAt ℝ F (t₀, x₀))
    (hzero : F (t₀, x₀) = 0)
    (e : E ≃L[ℝ] E)
    (hDx : (fderiv ℝ F (t₀, x₀)).comp (ContinuousLinearMap.inr ℝ ℝ E) =
      (e : E →L[ℝ] E)) :
    ∃ ψ : ℝ → E,
      ψ t₀ = x₀ ∧ AnalyticAt ℝ ψ t₀ ∧
      ∀ᶠ t in 𝓝 t₀, F (t, ψ t) = 0 := by
  obtain ⟨ψ, hψ₀, hψanalytic, W, V, hWopen, hVopen, hWbase, hVbase, hbranch, hunique⟩ :=
    exists_analytic_implicitFunction_with_local_uniqueness hF hzero e hDx
  refine ⟨ψ, hψ₀, hψanalytic, ?_⟩
  filter_upwards [hVopen.mem_nhds hVbase] with t ht
  exact (hbranch t ht).2

end PottsDiscontinuity.AnalyticTools
