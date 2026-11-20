module

public import RequestProject.TraceBound
public import RequestProject.NormAttained

/-!
# Spectral expansion of a unitary operator with compact `U - I`

For a unitary operator `U` on a complex Hilbert space with `U - I` compact, we list the
eigenvalues `z ≠ 1` with multiplicity through an orthonormal family of eigenvectors
`eigVec U p` (`p = (z, j)`, `j < mult(z)`), show that this family is complete in the sense that
every vector orthogonal to it is fixed by `U`, and deduce the expansion
`(U^k - I) x = ∑_p (z_p^k - 1) ⟨e_p, x⟩ e_p`. As a consequence, if `∑_p |z_p - 1| < ∞`, the
diagonal sum of `U^k - I` in any Hilbert basis is `∑_p (z_p^k - 1)`.
-/

@[expose] public section

open Filter
open scoped ComplexConjugate Topology

noncomputable section

namespace PolyaNeumann

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- An eigenvector for `z ≠ 1` orthogonal to all `e_p` vanishes. -/
lemma eq_zero_of_eigen_of_orth {U : H →L[ℂ] H} (hC : IsCompactOperator ⇑(U - 1)) {z : ℂ}
    (hz : z ≠ 1) {v : H} (hv : U v = z • v) (horth : ∀ p : EigIdx U, inner ℂ (eigVec U p) v = 0) :
    v = 0 := by
  haveI := finiteDimensional_eigenspace hC hz
  set b := stdOrthonormalBasis ℂ (Module.End.eigenspace (U : H →ₗ[ℂ] H) z)
  have hvm := Module.End.mem_eigenspace_iff.mpr hv
  have h := b.sum_repr' ⟨v, hvm⟩
  have h0 : ∀ j, inner ℂ (b j) (⟨v, hvm⟩ : Module.End.eigenspace (U : H →ₗ[ℂ] H) z) = 0 := by
    intro j
    rw [Submodule.coe_inner]
    exact horth ⟨⟨z, hz⟩, j⟩
  simp  [h0, Finset.sum_const_zero] at h
  exact congrArg Subtype.val h.symm

/-- The adjoint of a unitary operator acts on an eigenvector by the conjugate eigenvalue. -/
lemma star_apply_of_eigen {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H)) {z : ℂ} {v : H}
    (hz : ‖z‖ = 1) (hv : U v = z • v) : star U v = conj z • v := by
  have h1 : star U (U v) = v := by
    rw [← ContinuousLinearMap.mul_apply, Unitary.star_mul_self_of_mem hU,
      ContinuousLinearMap.one_apply]
  rw [hv, map_smul] at h1
  have hzc : conj z * z = 1 := by
    simp [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
  calc star U v = (conj z * z) • star U v := by simp_all
    _ = conj z • v := by rw [mul_smul, h1]

/-- **Completeness of the eigenvector family.** If `U` is unitary and `U - I` is compact, every
vector orthogonal to all eigenvectors `e_p` (eigenvalues `≠ 1`) is fixed by `U`. -/
theorem eigVec_complete {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (hC : IsCompactOperator ⇑(U - 1)) {v : H} (hv : ∀ p, inner ℂ (eigVec U p) v = 0) :
    U v = v := by
  set K : Submodule ℂ H := (Submodule.span ℂ (Set.range (eigVec U)))ᗮ
  have memK (w : H) : w ∈ K ↔ ∀ p, inner ℂ (eigVec U p) w = 0 := by
    rw [Submodule.mem_orthogonal']
    change (Submodule.span ℂ (Set.range (eigVec U)) ≤ (innerSL ℂ w).ker) ↔ _
    simp [Submodule.span_le, Set.range_subset_iff, inner_eq_zero_symm]
  have hstar_e := fun p =>
    star_apply_of_eigen hU (norm_eigVal hU p) (eigVec_eigen U p)
  have hUK : ∀ w ∈ K, U w ∈ K := by
    intro w hw
    rw [memK] at hw ⊢
    intro p
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint, hstar_e,
      inner_smul_left, hw, mul_zero]
  have hUsK : ∀ w ∈ K, star U w ∈ K := by
    intro w hw
    rw [memK] at hw ⊢
    intro p
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
      eigVec_eigen, inner_smul_left, hw p, mul_zero]
  have hK : IsClosed (K : Set H) := Submodule.isClosed_orthogonal _
  letI : CompleteSpace K := hK.completeSpace_coe
  let A := U.restrict hUK
  let B := (star U).restrict hUsK
  have hstar : star A = B := ((ContinuousLinearMap.eq_adjoint_iff B A).mpr
    (fun x y => ContinuousLinearMap.adjoint_inner_left U (y : H) (x : H))).symm
  have hAu : A ∈ unitary (K →L[ℂ] K) := by
    refine ⟨?_, ?_⟩ <;> rw [hstar] <;> ext1 x <;> apply Subtype.ext
    · exact congrArg (fun X : H →L[ℂ] H => X (x : H)) (Unitary.star_mul_self_of_mem hU)
    · exact congrArg (fun X : H →L[ℂ] H => X (x : H)) (Unitary.mul_star_self_of_mem hU)
  have hAc :=
    IsCompactOperator.restrict (show IsCompactOperator ⇑(U - 1).toLinearMap from hC)
      (fun w hw => K.sub_mem (hUK w hw) hw) hK
  by_contra hv'
  have hA1 : A ≠ 1 := fun h => hv' (congrArg (fun X : K →L[ℂ] K =>
    (X ⟨v, (memK v).mpr hv⟩ : H)) h)
  obtain ⟨z, w, hw0, hw, hz, _⟩ := exists_eigenvalue_norm_sub_one hAu hAc hA1
  exact hw0 (Subtype.ext (eq_zero_of_eigen_of_orth hC hz
    (congrArg Subtype.val hw) ((memK w).mp w.property)))

lemma hasSum_norm_inner_sq {ι : Type*} (b : HilbertBasis ι ℂ H) (v : H) :
    HasSum (fun i => ‖inner ℂ (b i) v‖ ^ 2) (‖v‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, b.repr_apply_apply, LinearIsometryEquiv.norm_map] using
    lp.hasSum_norm (p := 2) (by norm_num) (b.repr v)

lemma clm_pow_apply_of_eigen {A : H →L[ℂ] H} {z : ℂ} {x : H}
    (hx : A x = z • x) (n : ℕ) : (A ^ n) x = z ^ n • x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', ContinuousLinearMap.mul_apply, ih, map_smul, hx, smul_smul, pow_succ]

section

variable {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
include U hU

/-- The orthogonal eigenvector series leaves a remainder fixed by `U`. -/
lemma eigVec_decomposition (hC : IsCompactOperator ⇑(U - 1)) (x : H) :
    ∃ s, HasSum (fun p => inner ℂ (eigVec U p) x • eigVec U p) s ∧ U (x - s) = x - s := by
  have he := orthonormal_eigVec hU
  have h : Summable (fun p => inner ℂ (eigVec U p) x • eigVec U p) :=
    (he.orthogonalFamily.summable_iff_norm_sq_summable _).mpr (he.inner_products_summable x)
  let s := ∑' p, inner ℂ (eigVec U p) x • eigVec U p
  have hsum : HasSum _ s := h.hasSum
  have horth : ∀ q, inner ℂ (eigVec U q) (x - s) = 0 := by
    intro q
    have h1 := hsum.mapL (innerSL ℂ (eigVec U q))
    simp  [innerSL_apply_apply, inner_smul_right] at h1
    have h2 : HasSum (fun p => inner ℂ (eigVec U p) x * inner ℂ (eigVec U q) (eigVec U p))
        (inner ℂ (eigVec U q) x) := by
      have : (fun p => inner ℂ (eigVec U p) x * inner ℂ (eigVec U q) (eigVec U p)) =
          fun p => if p = q then inner ℂ (eigVec U q) x else 0 := by
        funext p
        rw [orthonormal_iff_ite.mp he q p]
        by_cases h : p = q
        simp_all
        grind
      rw [this]
      exact hasSum_ite_eq q _
    rw [inner_sub_right, h1.unique h2, sub_self]
  exact ⟨s, hsum, eigVec_complete hU hC horth⟩

/-- A bounded operator is determined by its action on the eigenvectors and the fixed space. -/
lemma eq_of_eigVec_and_fixed (hC : IsCompactOperator ⇑(U - 1)) {A B : H →L[ℂ] H}
    (h_eig : ∀ p, A (eigVec U p) = B (eigVec U p)) (h_fix : ∀ x, U x = x → A x = B x) : A = B := by
  ext1 x
  obtain ⟨s, hs, hf⟩ := eigVec_decomposition hU hC x
  have he := (hs.mapL A).unique (by simpa only [map_smul, h_eig] using hs.mapL B)
  simpa only [map_sub, he, sub_left_inj] using h_fix (x - s) hf

/-- **Spectral expansion.** For `U` unitary with `U - I` compact and every `k`,
`(U^k - I) x = ∑_p (z_p^k - 1) ⟨e_p, x⟩ e_p`. -/
theorem hasSum_pow_sub_one_apply 
    (hC : IsCompactOperator ⇑(U - 1)) (k : ℕ) (x : H) :
    HasSum (fun p : EigIdx U => (((p.1 : ℂ) ^ k - 1) * inner ℂ (eigVec U p) x) • eigVec U p)
      ((U ^ k - 1) x) := by
  obtain ⟨s, hsum, hfix⟩ := eigVec_decomposition hU hC x
  have hfix : (U ^ k) (x - s) = x - s := by
    simpa only [one_pow, one_smul] using
      clm_pow_apply_of_eigen (A := U) (x := x - s) (z := 1)
        (by simpa only [one_smul] using hfix) k
  have h := map_sub (U ^ k - 1) x s
  have h1 : (U ^ k - 1) (x - s) = 0 := by simp [hfix]
  rw [sub_eq_zero.mp (h.symm.trans h1)]
  have := hsum.mapL (U ^ k - 1)
  convert this using 1
  funext p
  rw [map_smul, ContinuousLinearMap.sub_apply, clm_pow_apply_of_eigen (eigVec_eigen U p), ContinuousLinearMap.one_apply, smul_sub,
    smul_smul, sub_mul, one_mul, sub_smul, mul_comm]

/-- The quadratic form of `U^k - I`: `⟨y, (U^k - I) x⟩ = ∑_p (z_p^k - 1) ⟨e_p, x⟩ ⟨y, e_p⟩`. -/
theorem hasSum_inner_pow_sub_one 
    (hC : IsCompactOperator ⇑(U - 1)) (k : ℕ) (x y : H) :
    HasSum (fun p : EigIdx U => ((p.1 : ℂ) ^ k - 1) * inner ℂ (eigVec U p) x *
      inner ℂ y (eigVec U p)) (inner ℂ y ((U ^ k - 1) x)) := by
  have := (hasSum_pow_sub_one_apply hU hC k x).mapL (innerSL ℂ y)
  simpa only [innerSL_apply_apply, inner_smul_right] using this

end

/-- **Trace of `U^k - I`.** If `∑_p |z_p^k - 1| < ∞`, the diagonal sum of `U^k - I` in any
Hilbert basis is `∑_p (z_p^k - 1)`. -/
theorem hasSum_trace_pow_sub_one {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (hC : IsCompactOperator ⇑(U - 1)) {ι : Type*} (b : HilbertBasis ι ℂ H) (k : ℕ)
    (hs : Summable (fun p : EigIdx U => ‖(p.1 : ℂ) ^ k - 1‖)) :
    HasSum (fun n => inner ℂ (b n) ((U ^ k - 1) (b n)))
      (∑' p : EigIdx U, ((p.1 : ℂ) ^ k - 1)) := by
  have he := orthonormal_eigVec hU
  set F : EigIdx U × ι → ℂ := fun q => ((q.1.1 : ℂ) ^ k - 1) * inner ℂ (eigVec U q.1) (b q.2) *
    inner ℂ (b q.2) (eigVec U q.1) with hF
  have hfib : ∀ p : EigIdx U, HasSum (fun n => F (p, n)) ((p.1 : ℂ) ^ k - 1) := by
    intro p
    have := (b.hasSum_inner_mul_inner (eigVec U p) (eigVec U p)).mul_left ((p.1 : ℂ) ^ k - 1)
    rw [inner_self_eq_norm_sq_to_K, he.1 p, RCLike.ofReal_one, one_pow, mul_one] at this
    simpa only [hF, mul_assoc] using this
  have hnorm : ∀ q, ‖F q‖ = ‖(q.1.1 : ℂ) ^ k - 1‖ * ‖inner ℂ (b q.2) (eigVec U q.1)‖ ^ 2 := by
    intro q
    rw [hF]
    simp  
    rw [← inner_conj_symm, RCLike.norm_conj]
    ring
  have hfibn : ∀ p : EigIdx U, HasSum (fun n => ‖F (p, n)‖) ‖(p.1 : ℂ) ^ k - 1‖ := by
    intro p
    simp  [hnorm]
    simpa only [he.1 p, one_pow, mul_one] using
      (hasSum_norm_inner_sq b (eigVec U p)).mul_left ‖(p.1 : ℂ) ^ k - 1‖
  have hFs : Summable F := by
    refine Summable.of_norm ?_
    rw [summable_prod_of_nonneg (fun _ => norm_nonneg _)]
    exact ⟨fun p => (hfibn p).summable, by simpa only [(hfibn _).tsum_eq] using hs⟩
  have hA := hFs.hasSum
  have h1 :=
    hA.prod_fiberwise hfib
  have hn := fun n =>
    hasSum_inner_pow_sub_one hU hC k (b n) (b n)
  have hA' :=
    (Equiv.prodComm ι (EigIdx U)).hasSum_iff.mpr hA
  have h2 := hA'.prod_fiberwise (fun n => hn n)
  rw [h1.tsum_eq]
  assumption

end PolyaNeumann

end
