module

public import RequestProject.Area
public import RequestProject.TraceBound
public import RequestProject.NormAttained
public import RequestProject.CutFourier

@[expose] public section

open MeasureTheory Set Filter
open scoped Real Topology ComplexConjugate

noncomputable section

namespace PolyaNeumann

section Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private abbrev EigIdx (U : H →L[ℂ] H) : Type := Σ z : {z : ℂ // z ≠ 1}, Fin (eigenMult U z)

private def eigVec (U : H →L[ℂ] H) (p : EigIdx U) : H :=
  haveI : FiniteDimensional ℂ (Module.End.eigenspace (U : H →ₗ[ℂ] H) (p.1 : ℂ)) :=
    Module.finite_of_finrank_pos (Fin.pos p.2)
  ((stdOrthonormalBasis ℂ (Module.End.eigenspace (U : H →ₗ[ℂ] H) (p.1 : ℂ))) p.2 : H)

omit [CompleteSpace H] in
private lemma eigVec_eigen (U : H →L[ℂ] H) (p : EigIdx U) :
    U (eigVec U p) = (p.1 : ℂ) • eigVec U p := by
  unfold eigVec; exact Module.End.mem_eigenspace_iff.mp (Submodule.coe_mem _)

private lemma orthonormal_eigVec {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H)) :
    Orthonormal ℂ (eigVec U) := by
  rw [orthonormal_iff_ite]
  rintro ⟨⟨z, hz⟩, k⟩ ⟨⟨z', hz'⟩, k'⟩
  by_cases hzz : z = z'
  · subst hzz
    haveI : FiniteDimensional ℂ (Module.End.eigenspace (U : H →ₗ[ℂ] H) z) :=
      Module.finite_of_finrank_pos (Fin.pos k)
    have := (orthonormal_iff_ite.mp
      (stdOrthonormalBasis ℂ (Module.End.eigenspace (U : H →ₗ[ℂ] H) z)).orthonormal) k k'
    simp only [eigVec]; rw [← Submodule.coe_inner, this]; congr 1
    exact propext ⟨fun h => by subst h; rfl, fun h => by cases h; rfl⟩
  · have hv : eigVec U ⟨⟨z, hz⟩, k⟩ ≠ 0 := by
      haveI : FiniteDimensional ℂ (Module.End.eigenspace (U : H →ₗ[ℂ] H) z) :=
        Module.finite_of_finrank_pos (Fin.pos k)
      simpa [eigVec] using (stdOrthonormalBasis ℂ
        (Module.End.eigenspace (U : H →ₗ[ℂ] H) z)).orthonormal.ne_zero k
    rw [inner_eq_zero_of_eigen_unitary hU (eigVec_eigen U _) (eigVec_eigen U ⟨⟨z', hz'⟩, k'⟩)
      hzz (norm_eq_one_of_eigen hU hv (eigVec_eigen U _)), if_neg]
    exact fun h => hzz (congrArg (fun p : EigIdx U => (p.1 : ℂ)) h)

private lemma norm_eigVal {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H)) (p : EigIdx U) :
    ‖(p.1 : ℂ)‖ = 1 :=
  norm_eq_one_of_eigen hU ((orthonormal_eigVec hU).ne_zero p) (eigVec_eigen U p)

private theorem eigVec_complete {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (hC : IsCompactOperator ⇑(U - 1)) {v : H} (hv : ∀ p, inner ℂ (eigVec U p) v = 0) :
    U v = v := by
  set K : Submodule ℂ H := (Submodule.span ℂ (Set.range (eigVec U)))ᗮ with hKdef
  have memK : ∀ w, w ∈ K ↔ ∀ p, inner ℂ (eigVec U p) w = 0 := fun w => by
    rw [hKdef, Submodule.mem_orthogonal]
    refine ⟨fun h p => h _ (Submodule.subset_span ⟨p, rfl⟩), fun h u hu => ?_⟩
    induction hu using Submodule.span_induction with
    | mem _ hx => obtain ⟨p, rfl⟩ := hx; exact h p
    | zero => simp
    | add _ _ _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul _ _ _ hx => rw [inner_smul_left, hx, mul_zero]
  have hUK : ∀ w ∈ K, U w ∈ K := fun w hw => (memK _).mpr fun p => by
    have hcz : conj (p.1 : ℂ) ≠ 0 :=
      norm_ne_zero_iff.mp (by rw [Complex.norm_conj, norm_eigVal hU p]; norm_num)
    refine mul_left_cancel₀ hcz ?_
    rw [mul_zero, ← inner_smul_left, ← eigVec_eigen, ← ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.mul_apply,
      Unitary.star_mul_self_of_mem hU, ContinuousLinearMap.one_apply, (memK w).mp hw p]
  have hUsK : ∀ w ∈ K, star U w ∈ K := fun w hw => (memK _).mpr fun p => by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
      eigVec_eigen, inner_smul_left, (memK w).mp hw p, mul_zero]
  let UK : K →L[ℂ] K := (U.comp K.subtypeL).codRestrict K fun x => hUK x x.2
  let UsK : K →L[ℂ] K := ((star U).comp K.subtypeL).codRestrict K fun x => hUsK x x.2
  have hstar : star UK = UsK := by
    rw [ContinuousLinearMap.star_eq_adjoint]; symm; rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    change inner ℂ (star U (x : H)) (y : H) = inner ℂ (x : H) (U (y : H))
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  have hUKu : UK ∈ unitary (K →L[ℂ] K) := by
    rw [Unitary.mem_iff, hstar]
    refine ⟨ContinuousLinearMap.ext fun x => Subtype.ext ?_,
      ContinuousLinearMap.ext fun x => Subtype.ext ?_⟩
    · change star U (U (x : H)) = (x : H)
      rw [← ContinuousLinearMap.mul_apply, Unitary.star_mul_self_of_mem hU,
        ContinuousLinearMap.one_apply]
    · change U (star U (x : H)) = (x : H)
      rw [← ContinuousLinearMap.mul_apply, Unitary.mul_star_self_of_mem hU,
        ContinuousLinearMap.one_apply]
  have hCK : IsCompactOperator ⇑(UK - 1) := by
    have heq : UK - 1 = K.orthogonalProjection.comp ((U - 1).comp K.subtypeL) :=
      ContinuousLinearMap.ext fun x =>
        (Submodule.orthogonalProjection_mem_subspace_eq_self (K := K)
          ⟨U x - x, K.sub_mem (hUK x x.2) x.2⟩).symm
    rw [heq]
    exact (hC.comp_clm K.subtypeL).clm_comp K.orthogonalProjection
  by_cases h1 : UK = 1
  · have hv' : UK ⟨v, (memK v).mpr hv⟩ = ⟨v, (memK v).mpr hv⟩ := by rw [h1]; rfl
    exact congrArg Subtype.val hv'
  · exfalso
    obtain ⟨z, w, hw0, hUw, hz1, -⟩ := exists_eigenvalue_norm_sub_one hUKu hCK h1
    haveI := finiteDimensional_eigenspace hC hz1
    set b := stdOrthonormalBasis ℂ (Module.End.eigenspace (U : H →ₗ[ℂ] H) z)
    have hwm : (w : H) ∈ Module.End.eigenspace (U : H →ₗ[ℂ] H) z :=
      Module.End.mem_eigenspace_iff.mpr (congrArg Subtype.val hUw)
    have hsum := b.sum_repr' ⟨(w : H), hwm⟩
    have h0 : ∀ j, inner ℂ (b j) (⟨(w : H), hwm⟩ : Module.End.eigenspace (U : H →ₗ[ℂ] H) z) = 0 :=
      fun j => (Submodule.coe_inner _ _ _).trans ((memK w).mp w.2 ⟨⟨z, hz1⟩, j⟩)
    simp only [h0, zero_smul, Finset.sum_const_zero] at hsum
    have hwH : (w : H) = 0 := congrArg Subtype.val hsum.symm
    exact hw0 (Subtype.ext hwH)

private theorem hasSum_inner_pow_sub_one {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (hC : IsCompactOperator ⇑(U - 1)) (k : ℕ) (x y : H) :
    HasSum (fun p : EigIdx U => ((p.1 : ℂ) ^ k - 1) * inner ℂ (eigVec U p) x *
      inner ℂ y (eigVec U p)) (inner ℂ y ((U ^ k - 1) x)) := by
  have he := orthonormal_eigVec hU
  have hsumm : Summable (fun p => inner ℂ (eigVec U p) x • eigVec U p) :=
    (he.orthogonalFamily.summable_iff_norm_sq_summable
      (fun p => inner ℂ (eigVec U p) x)).mpr (he.inner_products_summable x)
  have hsum := hsumm.hasSum
  set s := ∑' p, inner ℂ (eigVec U p) x • eigVec U p
  have horth : ∀ q, inner ℂ (eigVec U q) (x - s) = 0 := fun q => by
    have h1 := hsum.mapL (innerSL ℂ (eigVec U q))
    simp only [innerSL_apply_apply, inner_smul_right] at h1
    have h2 : HasSum (fun p => inner ℂ (eigVec U p) x * inner ℂ (eigVec U q) (eigVec U p))
        (inner ℂ (eigVec U q) x) :=
      (hasSum_ite_eq q (inner ℂ (eigVec U q) x)).congr_fun fun p => by
        rw [orthonormal_iff_ite.mp he q p]
        by_cases h : p = q
        · subst h; simp
        · rw [if_neg (Ne.symm h), if_neg h, mul_zero]
    rw [inner_sub_right, h1.unique h2, sub_self]
  have hfix : ∀ n : ℕ, (U ^ n) (x - s) = x - s := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', ContinuousLinearMap.mul_apply, ih, eigVec_complete hU hC horth]
  have hpow : ∀ (n : ℕ) (p : EigIdx U), (U ^ n) (eigVec U p) = ((p.1 : ℂ) ^ n) • eigVec U p :=
    fun n p => by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', ContinuousLinearMap.mul_apply, ih, map_smul, eigVec_eigen, smul_smul,
          pow_succ', mul_comm]
  have h1 : (U ^ k - 1) x = (U ^ k - 1) s := by
    have := hfix k; rw [map_sub] at this
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    exact sub_eq_sub_iff_sub_eq_sub.mpr this
  rw [h1]
  refine ((hsum.mapL (U ^ k - 1)).mapL (innerSL ℂ y)).congr_fun fun p => ?_
  simp only [Function.comp_apply, innerSL_apply_apply, map_smul, ContinuousLinearMap.sub_apply,
    hpow, ContinuousLinearMap.one_apply, inner_smul_right, inner_sub_right]
  ring

private lemma hasSum_norm_inner_sq_gen {ι : Type*} (b : HilbertBasis ι ℂ H) (v : H) :
    HasSum (fun i => ‖inner ℂ (b i) v‖ ^ 2) (‖v‖ ^ 2) := by
  have h := Complex.hasSum_re (b.hasSum_inner_mul_inner v v)
  rw [inner_self_eq_norm_sq_to_K] at h
  convert h using 1
  · funext i
    rw [← inner_conj_symm (b i) v, RCLike.norm_conj, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  · simp [← Complex.ofReal_pow]

private theorem hasSum_trace_pow_sub_one {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (hC : IsCompactOperator ⇑(U - 1)) {ι : Type*} (b : HilbertBasis ι ℂ H) (k : ℕ)
    (hs : Summable (fun p : EigIdx U => ‖(p.1 : ℂ) ^ k - 1‖)) :
    HasSum (fun n => inner ℂ (b n) ((U ^ k - 1) (b n)))
      (∑' p : EigIdx U, ((p.1 : ℂ) ^ k - 1)) := by
  have he := orthonormal_eigVec hU
  set F : EigIdx U × ι → ℂ := fun q => ((q.1.1 : ℂ) ^ k - 1) * inner ℂ (eigVec U q.1) (b q.2) *
    inner ℂ (b q.2) (eigVec U q.1) with hF
  have hfib : ∀ p : EigIdx U, HasSum (fun n => F (p, n)) ((p.1 : ℂ) ^ k - 1) := fun p => by
    have := (b.hasSum_inner_mul_inner (eigVec U p) (eigVec U p)).mul_left ((p.1 : ℂ) ^ k - 1)
    rw [inner_self_eq_norm_sq_to_K, he.1 p, RCLike.ofReal_one, one_pow, mul_one] at this
    simpa only [hF, mul_assoc] using this
  have hfibn : ∀ p : EigIdx U, HasSum (fun n => ‖F (p, n)‖) ‖(p.1 : ℂ) ^ k - 1‖ := fun p => by
    have hnorm : ∀ n, ‖F (p, n)‖ = ‖(p.1 : ℂ) ^ k - 1‖ * ‖inner ℂ (b n) (eigVec U p)‖ ^ 2 :=
      fun n => by simp only [hF, norm_mul]; rw [← inner_conj_symm, RCLike.norm_conj]; ring
    simp_rw [hnorm]
    simpa [he.1 p] using (hasSum_norm_inner_sq_gen b (eigVec U p)).mul_left ‖(p.1 : ℂ) ^ k - 1‖
  have hFs : Summable F := Summable.of_norm <| (summable_prod_of_nonneg fun _ => norm_nonneg _).mpr
    ⟨fun p => (hfibn p).summable, by simpa only [(hfibn _).tsum_eq] using hs⟩
  have hA := hFs.hasSum
  rw [(hA.prod_fiberwise hfib).tsum_eq]
  exact ((Equiv.prodComm ι (EigIdx U)).hasSum_iff.mpr hA).prod_fiberwise
    fun n => hasSum_inner_pow_sub_one hU hC k (b n) (b n)

end Spectral

private lemma inner_diagN (x y : Ell2) :
    inner ℂ x (diagN y) = 2 * (inner ℂ (basisVec 0) y * inner ℂ x (basisVec 0)) -
      inner ℂ (basisVec 1) y * inner ℂ x (basisVec 1) := by
  simp only [diagN, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, ContinuousLinearMap.toSpanSingleton_apply,
    inner_sub_right, inner_smul_right, basisVec]

private def traceForm (W : ℝ → Ell2 →L[ℂ] Ell2) (b : ℝ → ℝ) (X : Ell2 →L[ℂ] Ell2) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * π), (b θ : ℂ) *
    (2 * inner ℂ (star (W θ) (basisVec 0)) (X (star (W θ) (basisVec 0))) -
      inner ℂ (star (W θ) (basisVec 1)) (X (star (W θ) (basisVec 1))))

private lemma intervalIntegrable_smul_bdd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {b : ℝ → ℝ} (hb : AEStronglyMeasurable b volume) {B : ℝ}
    (hbB : ∀ θ ∈ Icc 0 (2 * π), |b θ| ≤ B) {f : ℝ → E} (hf : ContinuousOn f (Icc 0 (2 * π))) :
    IntervalIntegrable (fun θ => b θ • f θ) volume 0 (2 * π) := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity)]
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine Integrable.of_bound (hb.restrict.smul (hf.aestronglyMeasurable measurableSet_Icc)) (B * M)
    ((ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun θ hθ => ?_))
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul (hbB θ hθ) (hM θ hθ) (norm_nonneg _) ((abs_nonneg _).trans (hbB θ hθ))

private lemma intervalIntegrable_ofReal_mul {b : ℝ → ℝ} (hb : AEStronglyMeasurable b volume) {B : ℝ}
    (hbB : ∀ θ ∈ Icc 0 (2 * π), |b θ| ≤ B) {f : ℝ → ℂ} (hf : ContinuousOn f (Icc 0 (2 * π))) :
    IntervalIntegrable (fun θ => (b θ : ℂ) * f θ) volume 0 (2 * π) := by
  simpa [Complex.real_smul] using intervalIntegrable_smul_bdd hb hbB hf

private lemma hasSum_integral_inner_mul_inner {v w : ℝ → Ell2} (hv : ContinuousOn v (Icc 0 (2 * π)))
    (hw : ContinuousOn w (Icc 0 (2 * π))) {b : ℝ → ℝ} (hb : AEStronglyMeasurable b volume) {B : ℝ}
    (hbB : ∀ θ ∈ Icc 0 (2 * π), |b θ| ≤ B) {ι : Type*} [Countable ι]
    (e : HilbertBasis ι ℂ Ell2) :
    HasSum (fun n => ∫ θ in (0 : ℝ)..(2 * π), (b θ : ℂ) * (inner ℂ (v θ) (e n) * inner ℂ (e n) (w θ)))
      (∫ θ in (0 : ℝ)..(2 * π), (b θ : ℂ) * inner ℂ (v θ) (w θ)) := by
  have hsub : uIoc 0 (2 * π) ⊆ Icc 0 (2 * π) := by
    rw [uIoc_of_le (by positivity)]; exact Ioc_subset_Icc_self
  haveI : SecondCountableTopologyEither ℝ Ell2 := secondCountableTopologyEither_of_left _ _
  have hgs : ∀ θ, HasSum (fun n => |b θ| * ((‖inner ℂ (e n) (v θ)‖ ^ 2 +
      ‖inner ℂ (e n) (w θ)‖ ^ 2) / 2)) (|b θ| * ((‖v θ‖ ^ 2 + ‖w θ‖ ^ 2) / 2)) := fun θ =>
    (((hasSum_norm_inner_sq_gen e _).add (hasSum_norm_inner_sq_gen e _)).div_const 2).mul_left _
  have hGi : IntervalIntegrable (fun θ => |b θ| * ((‖v θ‖ ^ 2 + ‖w θ‖ ^ 2) / 2)) volume 0 (2 * π) := by
    simpa using intervalIntegrable_smul_bdd hb.norm
      (fun θ hθ => by simpa using hbB θ hθ) (((hv.norm.pow 2).add (hw.norm.pow 2)).div_const 2)
  have hvm : AEStronglyMeasurable v (volume.restrict (uIoc 0 (2 * π))) :=
    (hv.aestronglyMeasurable measurableSet_Icc).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hwm : AEStronglyMeasurable w (volume.restrict (uIoc 0 (2 * π))) :=
    (hw.aestronglyMeasurable measurableSet_Icc).mono_measure (Measure.restrict_mono hsub le_rfl)
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n θ => |b θ| * ((‖inner ℂ (e n) (v θ)‖ ^ 2 + ‖inner ℂ (e n) (w θ)‖ ^ 2) / 2))
    (fun _ => (Complex.continuous_ofReal.comp_aestronglyMeasurable hb).restrict.mul
      ((hvm.inner aestronglyMeasurable_const).mul (aestronglyMeasurable_const.inner hwm)))
    (fun n => Eventually.of_forall fun θ _ => ?_)
    (Eventually.of_forall fun θ _ => (hgs θ).summable)
    (hGi.congr fun θ _ => (hgs θ).tsum_eq.symm)
    (Eventually.of_forall fun θ _ => (e.hasSum_inner_mul_inner (v θ) (w θ)).mul_left _)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [norm_mul, norm_inner_symm (v θ) (e n)]
  nlinarith [sq_nonneg (‖inner ℂ (e n) (v θ)‖ - ‖inner ℂ (e n) (w θ)‖)]

private theorem hasSum_trace_integral_conj_diagN_mul {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : ContinuousOn W (Icc 0 (2 * π)))
    (hunit : ∀ θ ∈ Icc 0 (2 * π), W θ ∈ unitary (Ell2 →L[ℂ] Ell2))
    {b : ℝ → ℝ} (hb : AEStronglyMeasurable b volume) {B : ℝ}
    (hbB : ∀ θ ∈ Icc 0 (2 * π), |b θ| ≤ B) (X : Ell2 →L[ℂ] Ell2) {ι : Type*} [Countable ι]
    (e : HilbertBasis ι ℂ Ell2) :
    HasSum (fun n => inner ℂ (e n)
        (((∫ θ in (0 : ℝ)..(2 * π), b θ • (star (W θ) * diagN * W θ)) * X) (e n)))
      (traceForm W b X) := by
  have hint := intervalIntegrable_conj_diagN hW hunit hb hbB
  have huc : ∀ j, ContinuousOn (fun θ => star (W θ) (basisVec j)) (Icc 0 (2 * π)) := fun _ =>
    hW.star.clm_apply continuousOn_const
  have hXc : ∀ j, ContinuousOn (fun θ => ContinuousLinearMap.adjoint X (star (W θ) (basisVec j)))
      (Icc 0 (2 * π)) := fun j => (ContinuousLinearMap.adjoint X).continuous.comp_continuousOn (huc j)
  have hS : ∀ j, HasSum (fun n => ∫ θ in (0 : ℝ)..(2 * π), (b θ : ℂ) *
      (inner ℂ (ContinuousLinearMap.adjoint X (star (W θ) (basisVec j))) (e n) *
        inner ℂ (e n) (star (W θ) (basisVec j))))
      (∫ θ in (0 : ℝ)..(2 * π), (b θ : ℂ) *
        inner ℂ (star (W θ) (basisVec j)) (X (star (W θ) (basisVec j)))) := fun j => by
    simpa only [ContinuousLinearMap.adjoint_inner_left] using
      hasSum_integral_inner_mul_inner (hXc j) (huc j) hb hbB e
  have hI : ∀ j n, IntervalIntegrable (fun θ => (b θ : ℂ) *
      (inner ℂ (ContinuousLinearMap.adjoint X (star (W θ) (basisVec j))) (e n) *
        inner ℂ (e n) (star (W θ) (basisVec j)))) volume 0 (2 * π) := fun j _ =>
    intervalIntegrable_ofReal_mul hb hbB (((hXc j).inner continuousOn_const).mul
      (continuousOn_const.inner (huc j)))
  have h1 : ∀ n, inner ℂ (e n)
      (((∫ θ in (0 : ℝ)..(2 * π), b θ • (star (W θ) * diagN * W θ)) * X) (e n)) =
      2 * (∫ θ in (0 : ℝ)..(2 * π), (b θ : ℂ) *
        (inner ℂ (ContinuousLinearMap.adjoint X (star (W θ) (basisVec 0))) (e n) *
          inner ℂ (e n) (star (W θ) (basisVec 0)))) -
      ∫ θ in (0 : ℝ)..(2 * π), (b θ : ℂ) *
        (inner ℂ (ContinuousLinearMap.adjoint X (star (W θ) (basisVec 1))) (e n) *
          inner ℂ (e n) (star (W θ) (basisVec 1))) := fun n => by
    set L : (Ell2 →L[ℂ] Ell2) →L[ℂ] ℂ :=
      (innerSL ℂ (e n)).comp (ContinuousLinearMap.apply ℂ Ell2 (X (e n)))
    have hL : ∀ Y, L Y = inner ℂ (e n) (Y (X (e n))) := fun _ => rfl
    rw [ContinuousLinearMap.mul_apply, ← hL, ← L.intervalIntegral_comp_comm hint,
      ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
        ((hI 0 n).const_mul 2) (hI 1 n)]
    congr 1; funext θ
    rw [hL, ContinuousLinearMap.smul_apply, real_smul_eq_coe_smul_ell2, inner_smul_right,
      ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right, inner_diagN]
    simp only [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
    ring
  simp_rw [h1]
  have hJ : ∀ j, IntervalIntegrable (fun θ => (b θ : ℂ) *
      inner ℂ (star (W θ) (basisVec j)) (X (star (W θ) (basisVec j)))) volume 0 (2 * π) :=
    fun j => intervalIntegrable_ofReal_mul hb hbB ((huc j).inner
      (X.continuous.comp_continuousOn (huc j)))
  rw [show traceForm W b X = 2 * (∫ θ in (0 : ℝ)..(2 * π), (b θ : ℂ) *
        inner ℂ (star (W θ) (basisVec 0)) (X (star (W θ) (basisVec 0)))) -
      ∫ θ in (0 : ℝ)..(2 * π), (b θ : ℂ) *
        inner ℂ (star (W θ) (basisVec 1)) (X (star (W θ) (basisVec 1))) by
    rw [traceForm, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub ((hJ 0).const_mul 2) (hJ 1)]
    congr 1; funext _; ring]
  exact ((hS 0).mul_left 2).sub (hS 1)

lemma monodromy_mem_unitary' {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) :
    monodromy W ∈ unitary (Ell2 →L[ℂ] Ell2) := by
  rw [monodromy, ← ContinuousLinearMap.star_eq_adjoint]
  exact Unitary.star_mem (transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩)

private theorem hasDerivAt_monodromy_pow {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2}
    (hWs : ∀ E, IsTransport γ E (Ws E)) {E : ℝ} (hE : 0 < E) (n : ℕ) :
    HasDerivAt (fun E => monodromy (Ws E) ^ n)
      (Complex.I • ∑ j ∈ Finset.range n,
        monodromy (Ws E) ^ j * curvatureOp γ (Ws E) * monodromy (Ws E) ^ (n - j)) E := by
  induction n with
  | zero => simpa using hasDerivAt_const E (1 : Ell2 →L[ℂ] Ell2)
  | succ n ih =>
    have h := ih.mul (hasDerivAt_monodromy_energy hK hclosed hWs hE)
    rw [show (fun E => monodromy (Ws E) ^ n) * (fun E => monodromy (Ws E)) =
      fun E => monodromy (Ws E) ^ (n + 1) by funext; simp [pow_succ]] at h
    refine h.congr_deriv (Eq.symm ?_)
    rw [Finset.sum_range_succ, smul_add, Finset.smul_sum, Finset.smul_sum, Finset.sum_mul,
      Nat.add_sub_cancel_left, pow_one, mul_smul_comm, mul_assoc]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Nat.sub_add_comm (Finset.mem_range.mp hj).le, pow_succ]
    simp only [smul_mul_assoc, mul_assoc]

private lemma traceBound_sum_pow_mul_mul_pow {T U : Ell2 →L[ℂ] Ell2} {C : ℝ} (hT : TraceBound T C)
    (hU : U ∈ unitary (Ell2 →L[ℂ] Ell2)) (n : ℕ) :
    TraceBound (Complex.I • ∑ j ∈ Finset.range n, U ^ j * T * U ^ (n - j)) (n * C) := by
  have hs : ∀ m : ℕ, m ≤ n →
      TraceBound (∑ j ∈ Finset.range m, U ^ j * T * U ^ (n - j)) (m * C) := fun m => by
    induction m with
    | zero => exact fun _ => by simpa using TraceBound.zero
    | succ m ih =>
      intro hm; rw [Finset.sum_range_succ, Nat.cast_succ, add_mul, one_mul]
      exact (ih (by omega)).add ((hT.unitary_mul (pow_mem hU m)).mul_unitary (pow_mem hU _))
  have := (hs n le_rfl).smul Complex.I
  rwa [Complex.norm_I, one_mul] at this

private def tauE (γ : ℝ → ℂ) (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) (n : ℕ) (E : ℝ) : ℂ :=
  Complex.I * n * ((1 / 4 : ℂ) * traceForm (Ws E) (areaDensity γ) (monodromy (Ws E) ^ n))

private theorem hasSum_trace_deriv_monodromy_pow {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2} (hWs : ∀ E, IsTransport γ E (Ws E)) (E : ℝ) (n : ℕ)
    {ι : Type*} [Countable ι] (e : HilbertBasis ι ℂ Ell2) :
    HasSum (fun m => inner ℂ (e m) ((Complex.I • ∑ j ∈ Finset.range n,
        monodromy (Ws E) ^ j * curvatureOp γ (Ws E) * monodromy (Ws E) ^ (n - j)) (e m)))
      (tauE γ Ws n E) := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 (2 * π))
    (f := fun θ => γ θ - γ 0) (hK.continuous.sub continuous_const).continuousOn
  have hterm : ∀ j ≤ n, HasSum (fun m => inner ℂ (e m)
      ((monodromy (Ws E) ^ j * curvatureOp γ (Ws E) * monodromy (Ws E) ^ (n - j)) (e m)))
      ((1 / 4 : ℂ) * traceForm (Ws E) (areaDensity γ) (monodromy (Ws E) ^ n)) := fun j hjn => by
    set U := monodromy (Ws E)
    have hU : U ∈ unitary (Ell2 →L[ℂ] Ell2) := monodromy_mem_unitary' hK (hWs E)
    set V := U ^ j with hVdef
    have hV : V ∈ unitary (Ell2 →L[ℂ] Ell2) := pow_mem hU j
    have hVX : V * U ^ n = U ^ n * V := by rw [hVdef, ← pow_add, ← pow_add, add_comm]
    have hpow : U ^ (n - j) = star V * U ^ n := by
      rw [hVdef, ← Nat.add_sub_cancel' hjn, pow_add, ← mul_assoc, ← hVdef,
        Unitary.star_mul_self_of_mem hV, one_mul, Nat.add_sub_cancel' hjn]
    set W' : ℝ → Ell2 →L[ℂ] Ell2 := fun θ => Ws E θ * star V with hW'
    have hW'u : ∀ θ ∈ Icc 0 (2 * π), W' θ ∈ unitary (Ell2 →L[ℂ] Ell2) := fun θ hθ =>
      Submonoid.mul_mem _ (transport_mem_unitary hK (hWs E) hθ) (Unitary.star_mem hV)
    have hint := intervalIntegrable_conj_diagN (hWs E).1
      (fun θ hθ => transport_mem_unitary hK (hWs E) hθ)
      (areaDensity_aestronglyMeasurable hK.continuous) (fun θ hθ => abs_areaDensity_le hK hR hθ)
    set L : (Ell2 →L[ℂ] Ell2) →L[ℝ] (Ell2 →L[ℂ] Ell2) :=
      (ContinuousLinearMap.mul ℝ (Ell2 →L[ℂ] Ell2) V).comp
        ((ContinuousLinearMap.mul ℝ (Ell2 →L[ℂ] Ell2)).flip (star V))
    have hL : ∀ Y, L Y = V * (Y * star V) := fun _ => rfl
    have hconj : V * curvatureOp γ (Ws E) * U ^ (n - j) = (1 / 4 : ℝ) •
        ((∫ θ in (0 : ℝ)..(2 * π), areaDensity γ θ • (star (W' θ) * diagN * W' θ)) * U ^ n) := by
      rw [hpow, curvatureOp, mul_smul_comm, smul_mul_assoc, ← mul_assoc]
      congr 2
      rw [mul_assoc V, ← hL, ← L.intervalIntegral_comp_comm hint]
      congr 1; funext θ
      rw [hL, smul_mul_assoc, mul_smul_comm]
      congr 1; simp only [hW', star_mul, star_star, mul_assoc]
    rw [hconj]
    have hW'c : ContinuousOn W' (Icc 0 (2 * π)) := (hWs E).1.mul continuousOn_const
    have h := (hasSum_trace_integral_conj_diagN_mul hW'c hW'u
      (areaDensity_aestronglyMeasurable hK.continuous) (fun θ hθ => abs_areaDensity_le hK hR hθ)
      (U ^ n) e).mul_left ((1 / 4 : ℝ) : ℂ)
    have htf : traceForm W' (areaDensity γ) (U ^ n) = traceForm (Ws E) (areaDensity γ) (U ^ n) := by
      unfold traceForm; congr 1; funext θ
      have key : ∀ u : Ell2, inner ℂ (star (W' θ) u) ((U ^ n) (star (W' θ) u)) =
          inner ℂ (star (Ws E θ) u) ((U ^ n) (star (Ws E θ) u)) := fun u => by
        rw [hW', star_mul, star_star, ContinuousLinearMap.mul_apply,
          ← ContinuousLinearMap.mul_apply (U ^ n) V, ← hVX, ContinuousLinearMap.mul_apply,
          ← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
          ← ContinuousLinearMap.mul_apply (star V) V, Unitary.star_mul_self_of_mem hV,
          ContinuousLinearMap.one_apply]
      rw [key, key]
    rw [htf] at h; push_cast at h
    convert h using 2 with m
    rw [ContinuousLinearMap.smul_apply, real_smul_eq_coe_smul_ell2, inner_smul_right]
    push_cast; ring
  have h := (hasSum_sum (s := Finset.range n) fun j hj =>
    hterm j (Finset.mem_range.mp hj).le).mul_left Complex.I
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  convert h using 1
  · funext m
    rw [ContinuousLinearMap.smul_apply, inner_smul_right, ContinuousLinearMap.sum_apply, inner_sum]
  · rw [tauE]; ring

private theorem trace_monodromy_pow_sub {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {R : ℝ}
    (hR : ∀ θ ∈ Icc 0 (2 * π), ‖γ θ - γ 0‖ ≤ R)
    {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2}
    (hWs : ∀ E, IsTransport γ E (Ws E)) {E₁ E₂ : ℝ} (h1 : 0 < E₁) (h12 : E₁ ≤ E₂) (n : ℕ)
    (e : HilbertBasis ℕ ℂ Ell2) {T₁ T₂ : ℂ}
    (hT₁ : HasSum (fun m => inner ℂ (e m) ((monodromy (Ws E₁) ^ n - 1) (e m))) T₁)
    (hT₂ : HasSum (fun m => inner ℂ (e m) ((monodromy (Ws E₂) ^ n - 1) (e m))) T₂) :
    IntervalIntegrable (tauE γ Ws n) volume E₁ E₂ ∧
      (∀ E, ‖tauE γ Ws n E‖ ≤ n * (1 / 4 * ((R * K * 3) * (2 * π)))) ∧
      T₂ - T₁ = ∫ E in E₁..E₂, tauE γ Ws n E := by
  set C0 : ℝ := 1 / 4 * ((R * K * 3) * (2 * π))
  set D : ℝ → Ell2 →L[ℂ] Ell2 := fun E => Complex.I • ∑ j ∈ Finset.range n,
    monodromy (Ws E) ^ j * curvatureOp γ (Ws E) * monodromy (Ws E) ^ (n - j)
  have hTB : ∀ E, TraceBound (D E) (n * C0) := fun E =>
    traceBound_sum_pow_mul_mul_pow (traceBound_curvatureOp hK hR (hWs E))
      (monodromy_mem_unitary' hK (hWs E)) n
  have hpos : ∀ E ∈ uIoc E₁ E₂, 0 < E := fun E hE => by rw [uIoc_of_le h12] at hE; exact h1.trans hE.1
  have hposc : ∀ E ∈ uIcc E₁ E₂, 0 < E := fun E hE => by rw [uIcc_of_le h12] at hE; exact h1.trans_le hE.1
  set g : ℕ → ℝ → ℂ := fun m E => inner ℂ (e m) ((monodromy (Ws E) ^ n) (e m)) with hg
  set d : ℕ → ℝ → ℂ := fun m E => inner ℂ (e m) (D E (e m))
  have hgd : ∀ m E, 0 < E → HasDerivAt (g m) (d m E) E := fun m E hE =>
    (((innerSL ℂ (e m)).comp (ContinuousLinearMap.apply ℂ Ell2 (e m))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt E
      (hasDerivAt_monodromy_pow hK hclosed hWs hE n)
  have hpart : ∀ (M : ℕ) E, ‖∑ m ∈ Finset.range M, d m E‖ ≤ n * C0 := fun M E => by
    have := hTB E (Fin M) (fun i => e i) (fun i => e i)
      (e.orthonormal.comp _ fun _ _ h => Fin.val_injective h)
      (e.orthonormal.comp _ fun _ _ h => Fin.val_injective h)
    rwa [Fin.sum_univ_eq_sum_range (fun m => inner ℂ (e m) (D E (e m)))] at this
  have hone : ∀ m E, ‖d m E‖ ≤ n * C0 := fun m E => by
    simpa using hTB E Unit (fun _ => e m) (fun _ => e m)
      (e.orthonormal.comp _ fun i j _ => Subsingleton.elim i j)
      (e.orthonormal.comp _ fun i j _ => Subsingleton.elim i j)
  haveI : SecondCountableTopologyEither ℝ ℂ := secondCountableTopologyEither_of_left _ _
  have hdm : ∀ m, AEStronglyMeasurable (d m) (volume.restrict (uIoc E₁ E₂)) := fun m =>
    (stronglyMeasurable_deriv (g m)).aestronglyMeasurable.congr <|
      (ae_restrict_iff' measurableSet_uIoc).mpr <| Eventually.of_forall fun E hE => (hgd m E (hpos E hE)).deriv
  have hdi : ∀ m, IntervalIntegrable (d m) volume E₁ E₂ := fun m =>
    IntervalIntegrable.mono_fun' (intervalIntegrable_const (c := (n : ℝ) * C0)) (hdm m)
      (Eventually.of_forall fun E => hone m E)
  have hS : ∀ M : ℕ, ∫ E in E₁..E₂, (∑ m ∈ Finset.range M, d m E) =
      ∑ m ∈ Finset.range M, (g m E₂ - g m E₁) := fun M => by
    rw [intervalIntegral.integral_finset_sum fun m _ => hdi m]
    exact Finset.sum_congr rfl fun m _ =>
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun E hE => hgd m E (hposc E hE)) (hdi m)
  have hlimT : Tendsto (fun M => ∑ m ∈ Finset.range M, (g m E₂ - g m E₁)) atTop
      (𝓝 (T₂ - T₁)) := by
    convert (hT₂.sub hT₁).tendsto_sum_nat using 3 with M m
    simp only [hg, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, inner_sub_right]
    ring
  have hlimS : ∀ E, Tendsto (fun M => ∑ m ∈ Finset.range M, d m E) atTop
      (𝓝 (tauE γ Ws n E)) := fun E =>
    (hasSum_trace_deriv_monodromy_pow hK hWs E n e).tendsto_sum_nat
  have hntau : ∀ E, ‖tauE γ Ws n E‖ ≤ n * C0 := fun E =>
    le_of_tendsto' (hlimS E).norm fun M => hpart M E
  have hlimI := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => (n : ℝ) * C0)
    (Eventually.of_forall fun M => Finset.aestronglyMeasurable_fun_sum _ fun m _ => hdm m)
    (Eventually.of_forall fun M => Eventually.of_forall fun E _ => hpart M E)
    intervalIntegrable_const (Eventually.of_forall fun E _ => hlimS E)
  simp_rw [hS] at hlimI
  exact ⟨IntervalIntegrable.mono_fun' (intervalIntegrable_const (c := (n : ℝ) * C0))
    (aestronglyMeasurable_of_tendsto_ae atTop
      (fun M => Finset.aestronglyMeasurable_fun_sum _ fun m _ => hdm m)
      (Eventually.of_forall hlimS))
    (Eventually.of_forall hntau), hntau, tendsto_nhds_unique hlimT hlimI⟩

private lemma norm_pow_sub_one_le {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) : ‖z ^ n - 1‖ ≤ n * ‖z - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show z ^ (n + 1) - 1 = z * (z ^ n - 1) + (z - 1) by ring, Nat.cast_succ, add_mul, one_mul]
    exact (norm_add_le _ _).trans (add_le_add (by rwa [norm_mul, hz, one_mul]) le_rfl)

private lemma hasSum_re_inner_pow {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (hC : IsCompactOperator ⇑(U - 1)) (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖))
    (h1 : HasSum (fun n : ℕ => 2 * (a n).re) 1)
    (hz : ∀ p : EigIdx U, HasSum (fun n : ℕ => 2 * (a n * (p.1 : ℂ) ^ n).re) 1) (u : H) :
    HasSum (fun n : ℕ => 2 * (a n * inner ℂ u ((U ^ n) u)).re) (‖u‖ ^ 2) := by
  have he := orthonormal_eigVec hU
  set w : EigIdx U → ℝ := fun p => ‖inner ℂ (eigVec U p) u‖ ^ 2 with hw
  have hws : Summable w := he.inner_products_summable u
  set F : ℕ × EigIdx U → ℝ := fun q => 2 * (a q.1 * ((q.2.1 : ℂ) ^ q.1 - 1)).re * w q.2 with hF
  have hFs : Summable F := Summable.of_norm_bounded
    ((ha.mul_of_nonneg hws (fun _ => norm_nonneg _) fun _ => by positivity).mul_left 4) fun q => by
      rw [hF, Real.norm_eq_abs, abs_mul, abs_mul, abs_two, abs_of_nonneg (by positivity : 0 ≤ w q.2)]
      have h1' := (Complex.abs_re_le_norm (a q.1 * ((q.2.1 : ℂ) ^ q.1 - 1))).trans (norm_mul_le _ _)
      have h2' : ‖(q.2.1 : ℂ) ^ q.1 - 1‖ ≤ 2 :=
        (norm_sub_le _ _).trans (by rw [norm_pow, norm_eigVal hU, one_pow, norm_one]; norm_num)
      nlinarith [mul_le_mul_of_nonneg_left h2' (norm_nonneg (a q.1)), show 0 ≤ w q.2 by positivity]
  have hfibp : ∀ p : EigIdx U, HasSum (fun n => F (n, p)) 0 := fun p => by
    convert (((hz p).sub h1).mul_right (w p)) using 2 with n
    · simp only [hF, mul_sub, mul_one, Complex.sub_re]
    · ring
  have hfibn : ∀ n : ℕ, HasSum (fun p => F (n, p))
      (2 * (a n * (inner ℂ u ((U ^ n) u) - ((‖u‖ ^ 2 : ℝ) : ℂ))).re) := fun n => by
    have h := hasSum_inner_pow_sub_one hU hC n u u
    rw [show inner ℂ u ((U ^ n - 1) u) = inner ℂ u ((U ^ n) u) - ((‖u‖ ^ 2 : ℝ) : ℂ) by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, inner_sub_right,
        inner_self_eq_norm_sq_to_K]; push_cast; rfl] at h
    convert (Complex.hasSum_re (h.mul_left (a n))).mul_left 2 using 2 with p
    have hprod : inner ℂ (eigVec U p) u * inner ℂ u (eigVec U p) = (w p : ℂ) := by
      rw [hw, ← inner_conj_symm u (eigVec U p), Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [hF]
    rw [mul_assoc ((p.1 : ℂ) ^ n - 1), hprod, ← mul_assoc, Complex.re_mul_ofReal]; ring
  have hA := hFs.hasSum
  have hz0 : ∑' q, F q = 0 :=
    (hasSum_zero.unique (((Equiv.prodComm (EigIdx U) ℕ).hasSum_iff.mpr hA).prod_fiberwise hfibp)).symm
  have h2 := hA.prod_fiberwise hfibn
  rw [hz0] at h2
  have h3 := (h1.mul_right (‖u‖ ^ 2)).add h2
  rw [one_mul, add_zero] at h3
  convert h3 using 2 with n
  rw [mul_sub, Complex.sub_re, Complex.re_mul_ofReal]; ring

private theorem hasSum_re_tauE {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2} (hWs : ∀ E, IsTransport γ E (Ws E)) (E : ℝ)
    (hC : IsCompactOperator ⇑(monodromy (Ws E) - 1)) (c : ℕ → ℂ)
    (hc : Summable (fun n : ℕ => n * ‖c n‖))
    (h1 : HasSum (fun n : ℕ => 2 * (Complex.I * n * c n).re) 1)
    (hz : ∀ p : EigIdx (monodromy (Ws E)),
      HasSum (fun n : ℕ => 2 * (Complex.I * n * c n * (p.1 : ℂ) ^ n).re) 1) :
    HasSum (fun n : ℕ => 2 * (c n * tauE γ Ws n E).re)
      ((1 / 4) * ∫ θ in (0 : ℝ)..(2 * π), areaDensity γ θ) := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 (2 * π))
    (f := fun θ => γ θ - γ 0) (hK.continuous.sub continuous_const).continuousOn
  have hsub : uIoc 0 (2 * π) ⊆ Icc 0 (2 * π) := by
    rw [uIoc_of_le (by positivity)]; exact Ioc_subset_Icc_self
  set W := Ws E; set U := monodromy W; set b := areaDensity γ
  have hU : U ∈ unitary (Ell2 →L[ℂ] Ell2) := monodromy_mem_unitary' hK (hWs E)
  have hb : AEStronglyMeasurable b volume := areaDensity_aestronglyMeasurable hK.continuous
  have hbB : ∀ θ ∈ Icc 0 (2 * π), |b θ| ≤ R * K := fun θ hθ => abs_areaDensity_le hK hR hθ
  set a : ℕ → ℂ := fun n => Complex.I * n * c n with ha
  have has : Summable (fun n => ‖a n‖) := hc.congr fun n => by
    rw [ha, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_natCast]
  set u : ℕ → ℝ → Ell2 := fun j θ => star (W θ) (basisVec j) with hu
  have huc : ∀ j, ContinuousOn (u j) (Icc 0 (2 * π)) := fun _ =>
    (hWs E).1.star.clm_apply continuousOn_const
  have hun : ∀ j, ∀ θ ∈ Icc 0 (2 * π), ‖u j θ‖ = 1 := fun j θ hθ => by
    simpa [hu, basisVec] using
      Unitary.norm_map ⟨star (W θ), Unitary.star_mem (transport_mem_unitary hK (hWs E) hθ)⟩
        (basisVec j)
  set f : ℕ → ℝ → ℂ := fun n θ => (b θ : ℂ) *
    (2 * inner ℂ (u 0 θ) ((U ^ n) (u 0 θ)) - inner ℂ (u 1 θ) ((U ^ n) (u 1 θ))) with hf
  have hfi : ∀ n, IntervalIntegrable (f n) volume 0 (2 * π) := fun n =>
    intervalIntegrable_ofReal_mul hb hbB
      ((continuousOn_const.mul ((huc 0).inner ((U ^ n).continuous.comp_continuousOn (huc 0)))).sub
        ((huc 1).inner ((U ^ n).continuous.comp_continuousOn (huc 1))))
  set G : ℕ → ℝ → ℝ := fun n θ => 2 * (a n * f n θ).re with hG
  have hterm : ∀ n, 2 * (c n * tauE γ Ws n E).re =
      (1 / 4) * ∫ θ in (0 : ℝ)..(2 * π), G n θ := fun n => by
    have hGi : ∫ θ in (0 : ℝ)..(2 * π), G n θ = 2 * (a n * traceForm W b (U ^ n)).re := by
      have e1 : traceForm W b (U ^ n) = ∫ θ in (0 : ℝ)..(2 * π), f n θ := rfl
      rw [e1, ← intervalIntegral.integral_const_mul, ← Complex.reCLM_apply,
        ← Complex.reCLM.intervalIntegral_comp_comm ((hfi n).const_mul (a n)),
        ← intervalIntegral.integral_const_mul]; rfl
    rw [hGi, tauE, show c n * (Complex.I * n * ((1 / 4 : ℂ) * traceForm W b (U ^ n))) =
      ((1 / 4 : ℝ) : ℂ) * (a n * traceForm W b (U ^ n)) by rw [ha]; push_cast; ring,
      Complex.re_ofReal_mul]
    ring
  simp_rw [hterm]
  refine HasSum.mul_left _ ?_
  have hpt : ∀ θ ∈ Icc 0 (2 * π), HasSum (fun n => G n θ) (b θ) := fun θ hθ => by
    have h0 := hasSum_re_inner_pow hU hC a has h1 hz (u 0 θ)
    have h1' := hasSum_re_inner_pow hU hC a has h1 hz (u 1 θ)
    rw [hun 0 θ hθ] at h0; rw [hun 1 θ hθ] at h1'
    convert (((h0.mul_left 2).sub h1').mul_left (b θ)) using 1
    · funext n
      simp only [hG, hf]
      rw [show a n * ((b θ : ℂ) * (2 * inner ℂ (u 0 θ) ((U ^ n) (u 0 θ)) -
          inner ℂ (u 1 θ) ((U ^ n) (u 1 θ)))) = ((b θ : ℝ) : ℂ) *
          (2 * (a n * inner ℂ (u 0 θ) ((U ^ n) (u 0 θ))) -
            a n * inner ℂ (u 1 θ) ((U ^ n) (u 1 θ))) by ring]
      simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.re_ofNat,
        Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im]; ring
    · ring
  have hGb : ∀ n, ∀ θ ∈ Icc 0 (2 * π), ‖G n θ‖ ≤ |b θ| * (6 * ‖a n‖) := fun n θ hθ => by
    have hk : ∀ j, ‖inner ℂ (u j θ) ((U ^ n) (u j θ))‖ ≤ 1 := fun j =>
      (norm_inner_le_norm _ _).trans <| by
        rw [hun j θ hθ, one_mul]
        exact ((U ^ n).le_opNorm _).trans (by
          rw [hun j θ hθ, mul_one]; exact norm_le_one_of_mem_unitary (pow_mem hU n))
    have h3 : ‖2 * inner ℂ (u 0 θ) ((U ^ n) (u 0 θ)) - inner ℂ (u 1 θ) ((U ^ n) (u 1 θ))‖ ≤ 3 :=
      (norm_sub_le _ _).trans (by rw [norm_mul, Complex.norm_ofNat]; linarith [hk 0, hk 1])
    have hf3 : ‖f n θ‖ ≤ |b θ| * 3 := by
      simp only [hf]; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    calc ‖G n θ‖ = 2 * |(a n * f n θ).re| := by simp [hG, abs_mul]
      _ ≤ 2 * (‖a n‖ * ‖f n θ‖) := by gcongr; exact (Complex.abs_re_le_norm _).trans (norm_mul_le _ _)
      _ ≤ 2 * (‖a n‖ * (|b θ| * 3)) := by gcongr
      _ = |b θ| * (6 * ‖a n‖) := by ring
  have hsumb : ∀ θ, HasSum (fun n => |b θ| * (6 * ‖a n‖)) (|b θ| * (6 * ∑' n, ‖a n‖)) :=
    fun _ => (has.hasSum.mul_left 6).mul_left _
  have hbi : IntervalIntegrable (fun θ => |b θ| * (6 * ∑' n, ‖a n‖)) volume 0 (2 * π) :=
    intervalIntegrable_smul_bdd hb.norm (fun θ hθ => by simpa using hbB θ hθ) continuousOn_const
  exact intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n θ => |b θ| * (6 * ‖a n‖))
    (fun n => (Complex.continuous_re.comp_aestronglyMeasurable
      (intervalIntegrable_iff.mp ((hfi n).const_mul (a n))).aestronglyMeasurable).const_mul 2)
    (fun n => Eventually.of_forall fun θ hθ => hGb n θ (hsub hθ))
    (Eventually.of_forall fun θ _ => (hsumb θ).summable)
    (hbi.congr fun θ _ => (hsumb θ).tsum_eq.symm)
    (Eventually.of_forall fun θ hθ => hpt θ (hsub hθ))

private lemma exists_cut_radius {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 2 * π) {E₁ E₂ : ℝ}
    (h1 : 0 < E₁)
    (hcut : ∀ E ∈ Icc E₁ E₂, Complex.exp (ε * Complex.I) ∉ spectrum ℂ (monodromyAt γ E)) :
    ∃ r, 0 < r ∧ r ≤ ‖1 - Complex.exp (ε * Complex.I)‖ ∧
      ∀ E ∈ Icc E₁ E₂, ∀ (z : ℂ) (v : Ell2), v ≠ 0 → monodromyAt γ E v = z • v →
        r ≤ ‖z - Complex.exp (ε * Complex.I)‖ := by
  set w := Complex.exp (ε * Complex.I) with hw
  set G : ℝ × ℂ → Ell2 →L[ℂ] Ell2 := fun q => algebraMap ℂ _ q.2 - monodromyAt γ q.1 with hG
  have hGc : ContinuousOn G (Ioi 0 ×ˢ univ) := fun q hq =>
    (((continuous_algebraMap ℂ (Ell2 →L[ℂ] Ell2)).continuousAt.comp continuousAt_snd).sub
      ((continuousAt_monodromyAt hK hclosed hq.1).comp continuousAt_fst)).continuousWithinAt
  have hO := hGc.isOpen_inter_preimage (isOpen_Ioi.prod isOpen_univ) Units.isOpen
  have hKO : Icc E₁ E₂ ×ˢ ({w} : Set ℂ) ⊆ (Ioi 0 ×ˢ univ) ∩ G ⁻¹' {x | IsUnit x} := by
    rintro ⟨E, z⟩ ⟨hE, rfl : z = w⟩
    exact ⟨⟨h1.trans_le hE.1, mem_univ _⟩, spectrum.notMem_iff.mp (hcut E hE)⟩
  obtain ⟨δ, hδ, hδO⟩ := (isCompact_Icc.prod isCompact_singleton).exists_thickening_subset_open hO hKO
  have hw1 : 0 < ‖1 - w‖ := by
    have hsin : 0 < Real.sin (ε / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    rw [norm_sub_rev, hw, mul_comm, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
      abs_two, abs_of_pos hsin]
    positivity
  refine ⟨min δ ‖1 - w‖, lt_min hδ hw1, min_le_right _ _, fun E hE z v hv hUv =>
    (min_le_left _ _).trans ?_⟩
  by_contra hlt
  push_neg at hlt
  have hmem : (E, z) ∈ Metric.thickening δ (Icc E₁ E₂ ×ˢ ({w} : Set ℂ)) :=
    Metric.mem_thickening_iff.mpr ⟨(E, w), ⟨hE, mem_singleton _⟩, by
      simpa [Prod.dist_eq, dist_eq_norm] using hlt⟩
  obtain ⟨u, hu⟩ := (hδO hmem).2
  have h0 : G (E, z) v = 0 := by simp [hG, Algebra.algebraMap_eq_smul_one, hUv]
  exact hv (calc v = ((↑u⁻¹ : Ell2 →L[ℂ] Ell2) * ↑u) v := by rw [Units.inv_mul]; rfl
    _ = 0 := by rw [ContinuousLinearMap.mul_apply, hu, h0, map_zero])

theorem cutPhaseSum_monodromyAt_sub' {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 2 * π) (E₁ E₂ : ℝ)
    (h1 : 0 < E₁) (h12 : E₁ ≤ E₂)
    (hcut : ∀ E ∈ Set.Icc E₁ E₂,
      Complex.exp (ε * Complex.I) ∉ spectrum ℂ (monodromyAt γ E)) :
    cutPhaseSum ε (monodromyAt γ E₂) - cutPhaseSum ε (monodromyAt γ E₁) =
      (E₂ - E₁) * ((1 / 4) * ∫ θ in (0 : ℝ)..(2 * π), areaDensity γ θ) := by
  obtain ⟨r, hr, hr1, hrE⟩ := exists_cut_radius hK hclosed hε0 hε h1 hcut
  obtain ⟨c, hc, hcF⟩ := exists_cutFourier hε0 hε hr
  choose Ws hWs using fun E => transport_exists_of_lipschitz γ hK E
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 (2 * π))
    (f := fun θ => γ θ - γ 0) (hK.continuous.sub continuous_const).continuousOn
  set C0 : ℝ := 1 / 4 * ((R * K * 3) * (2 * π))
  set τ₀ : ℝ := (1 / 4) * ∫ θ in (0 : ℝ)..(2 * π), areaDensity γ θ
  set e : HilbertBasis ℕ ℂ Ell2 := default
  set T : ℕ → ℝ → ℂ := fun n E => ∑' p : EigIdx (monodromy (Ws E)), ((p.1 : ℂ) ^ n - 1)
  have hfar : ∀ E ∈ Icc E₁ E₂, ∀ p : EigIdx (monodromy (Ws E)),
      ‖(p.1 : ℂ)‖ = 1 ∧ r ≤ ‖(p.1 : ℂ) - Complex.exp (ε * Complex.I)‖ := fun E hE p => by
    have hU := monodromy_mem_unitary' hK (hWs E)
    refine ⟨norm_eigVal hU p, hrE E hE _ (eigVec _ p) ((orthonormal_eigVec hU).ne_zero p) ?_⟩
    rw [monodromyAt_eq hK (hWs E)]; exact eigVec_eigen _ p
  have hE0 : ∀ E ∈ Icc E₁ E₂, 0 ≤ E := fun _ hE => (h1.trans_le hE.1).le
  have hper : ∀ E ∈ Icc E₁ E₂, (∀ n : ℕ, HasSum (fun m => inner ℂ (e m)
      ((monodromy (Ws E) ^ n - 1) (e m))) (T n E)) ∧
      HasSum (fun n : ℕ => 2 * (c n * T n E).re) (cutPhaseSum ε (monodromyAt γ E)) := fun E hE => by
    rw [monodromyAt_eq hK (hWs E)]
    set U := monodromy (Ws E) with hUdef
    have hU := monodromy_mem_unitary' hK (hWs E)
    have hC := isCompactOperator_monodromy_sub_one hK hclosed (hE0 E hE) (hWs E)
    have hz := norm_eigVal hU
    have hs : Summable (fun p : EigIdx U => ‖(p.1 : ℂ) - 1‖) := by
      rw [summable_sigma_of_nonneg fun _ => norm_nonneg _]
      refine ⟨fun _ => (hasSum_fintype _).summable,
        (summable_eigenMult_monodromy hK hclosed (hE0 E hE) (hWs E)).congr fun _ => ?_⟩
      rw [tsum_fintype]; simp [hUdef, Finset.sum_const, nsmul_eq_mul]
    refine ⟨fun n => hasSum_trace_pow_sub_one hU hC e n
      (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun p => norm_pow_sub_one_le (hz p) n) (hs.mul_left (n : ℝ))), ?_⟩
    set F : EigIdx U × ℕ → ℝ := fun q => 2 * (c q.2 * ((q.1.1 : ℂ) ^ q.2 - 1)).re with hFdef
    have hFs : Summable F := Summable.of_norm_bounded
      (by simpa only [mul_assoc] using
        (hs.mul_of_nonneg hc (fun _ => norm_nonneg _) fun _ => by positivity).mul_left 2) fun q => by
        rw [hFdef, Real.norm_eq_abs, abs_mul, abs_two]
        have h1' := (Complex.abs_re_le_norm (c q.2 * ((q.1.1 : ℂ) ^ q.2 - 1))).trans (norm_mul_le _ _)
        nlinarith [mul_le_mul_of_nonneg_left (norm_pow_sub_one_le (hz q.1) q.2) (norm_nonneg (c q.2))]
    have hA := hFs.hasSum
    have h1f := hA.prod_fiberwise fun p => (hcF _ (hfar E hE p).1 (hfar E hE p).2).1
    have hn : ∀ n : ℕ, HasSum (fun p : EigIdx U => F (p, n)) (2 * (c n * T n E).re) := fun n => by
      have hp : HasSum (fun p : EigIdx U => (p.1 : ℂ) ^ n - 1) (T n E) :=
        (Summable.of_norm_bounded (hs.mul_left (n : ℝ)) fun p => norm_pow_sub_one_le (hz p) n).hasSum
      simpa only [hFdef] using (Complex.hasSum_re (hp.mul_left (c n))).mul_left 2
    have h2f := ((Equiv.prodComm ℕ (EigIdx U)).hasSum_iff.mpr hA).prod_fiberwise hn
    rw [show cutPhaseSum ε U = ∑' p : EigIdx U, argCut ε p.1 by
      rw [h1f.summable.tsum_sigma' fun _ => (hasSum_fintype _).summable, cutPhaseSum]
      congr 1; funext _; rw [tsum_fintype, cutPhaseTerm]
      simp [Finset.sum_const, nsmul_eq_mul], h1f.tsum_eq]
    exact h2f
  have hint := fun n => trace_monodromy_pow_sub hK hclosed hR hWs h1 h12 n e
    ((hper E₁ ⟨le_rfl, h12⟩).1 n) ((hper E₂ ⟨h12, le_rfl⟩).1 n)
  have hL : HasSum (fun n : ℕ => ∫ E in E₁..E₂, 2 * (c n * tauE γ Ws n E).re)
      (cutPhaseSum ε (monodromyAt γ E₂) - cutPhaseSum ε (monodromyAt γ E₁)) := by
    convert (hper E₂ ⟨h12, le_rfl⟩).2.sub (hper E₁ ⟨le_rfl, h12⟩).2 using 1
    funext n
    rw [intervalIntegral.integral_const_mul]
    have h := Complex.reCLM.intervalIntegral_comp_comm ((hint n).1.const_mul (c n))
    simp only [Complex.reCLM_apply] at h
    rw [h, intervalIntegral.integral_const_mul, ← (hint n).2.2, mul_sub, Complex.sub_re]; ring
  have hR' : HasSum (fun n : ℕ => ∫ E in E₁..E₂, 2 * (c n * tauE γ Ws n E).re)
      (∫ _ in E₁..E₂, τ₀) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => 2 * (n * ‖c n‖) * C0)
      (fun n => (continuous_const.mul Complex.continuous_re).comp_aestronglyMeasurable
        (intervalIntegrable_iff.mp ((hint n).1.const_mul (c n))).aestronglyMeasurable)
      (fun n => Eventually.of_forall fun E _ => ?_)
      (Eventually.of_forall fun _ _ => (hc.mul_left 2).mul_right C0)
      intervalIntegrable_const
      (Eventually.of_forall fun E hE => ?_)
    · rw [Real.norm_eq_abs, abs_mul, abs_two]
      have h1' := (Complex.abs_re_le_norm (c n * tauE γ Ws n E)).trans (norm_mul_le _ _)
      have h2' : ‖c n‖ * ‖tauE γ Ws n E‖ ≤ ‖c n‖ * (n * C0) :=
        mul_le_mul_of_nonneg_left ((hint n).2.1 E) (norm_nonneg (c n))
      nlinarith
    · rw [uIoc_of_le h12] at hE
      have hEI := Ioc_subset_Icc_self hE
      exact hasSum_re_tauE hK hWs E
        (isCompactOperator_monodromy_sub_one hK hclosed (hE0 E hEI) (hWs E)) c hc
        (by simpa using (hcF 1 (by simp) hr1).2)
        fun p => (hcF _ (hfar E hEI p).1 (hfar E hEI p).2).2
  rw [hL.unique hR', intervalIntegral.integral_const, smul_eq_mul]

end PolyaNeumann

end
