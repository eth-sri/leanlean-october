module

public import RequestProject.NeumannBoundaryPole
public import RequestProject.NeumannMultiplicity
public import RequestProject.NormAttained
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Dimension of the genuine form resonance space

The H¹ kernel used in the boundary pole is linearly equivalent to the
original weak Neumann eigenspace. Its complex dimension therefore agrees
with the multiplicity in the original variational sequence, established via
the compact positive shifted resolvent `(h1Value Ω) ∘L (h1Value Ω)†`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann.CompactSpectral

open Set Filter Topology
open scoped InnerProductSpace ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A nonzero compact positive complex operator attains its norm at a unit
eigenvector. Positivity rules out a negative extremal eigenvalue. -/
theorem exists_top_eigenvector {T : H →L[ℂ] H} (hT : IsCompactOperator T)
    (hP : T.IsPositive) (hT0 : T ≠ 0) :
    ∃ x : H, ‖x‖ = 1 ∧ T x = (‖T‖ : ℂ) • x ∧
      ∀ y : H, (⟪T y, y⟫_ℂ).re ≤ ‖T‖ * ‖y‖ ^ 2 := by
  haveI : Nontrivial H := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    letI : Subsingleton H := h
    exact hT0 (ContinuousLinearMap.ext fun _ => Subsingleton.elim _ _)
  obtain ⟨k, hk, hkn⟩ := spectrum.exists_nnnorm_eq_spectralRadius T
  have hkn' : ‖k‖ = ‖T‖ :=
    congrArg NNReal.toReal (ENNReal.coe_inj.mp (hkn.trans hP.isSelfAdjoint.spectralRadius_eq_nnnorm))
  have hk0 : k ≠ 0 := fun hk0 => by
    rw [hk0, norm_zero, eq_comm, norm_eq_zero] at hkn'
    exact hT0 hkn'
  obtain ⟨v, hv0, hv⟩ := PolyaNeumann.exists_eigenvector_of_mem_spectrum hT hk hk0
  have hkreal : k = (k.re : ℂ) := hP.isSelfAdjoint.mem_spectrum_eq_re hk
  have hkpos : 0 ≤ k.re := by
    have hp := hP.re_inner_nonneg_left v
    rw [hv, inner_smul_left, hkreal, inner_self_eq_norm_sq_to_K] at hp
    exact nonneg_of_mul_nonneg_left
      (by simpa [RCLike.re_eq_complex_re, pow_two, Complex.mul_re] using hp)
      (sq_pos_of_pos (norm_pos_iff.mpr hv0))
  have hkeq : k = (‖T‖ : ℂ) := by
    rw [hkreal] at hkn'
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hkpos] at hkn'
    rw [hkreal, hkn']
  refine ⟨(‖v‖⁻¹ : ℂ) • v, ?_, ?_, fun y => ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
  · rw [map_smul, hv, hkeq, smul_comm]
  · calc
      (⟪T y, y⟫_ℂ).re ≤ ‖T y‖ * ‖y‖ := re_inner_le_norm (𝕜 := ℂ) (T y) y
      _ ≤ ‖T‖ * ‖y‖ * ‖y‖ := by gcongr; exact T.le_opNorm _
      _ = ‖T‖ * ‖y‖ ^ 2 := by ring

omit [CompleteSpace H] in
theorem exists_nonzero_orthogonal (hInfinite : ¬ Module.Finite ℂ H)
    (e : ℕ → H) (n : ℕ) :
    ∃ x : H, x ≠ 0 ∧ ∀ i < n, ⟪e i, x⟫_ℂ = 0 := by
  let coordinates : H →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun x i => ⟪e i, x⟫_ℂ
      map_add' := by intro x y; ext i; simp [inner_add_right]
      map_smul' := by intro c x; ext i; simp [inner_smul_right] }
  have hker : LinearMap.ker coordinates ≠ ⊥ := fun hker =>
    hInfinite (FiniteDimensional.of_injective coordinates (LinearMap.ker_eq_bot.mp hker))
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨x, hx0, fun i hi => congrFun (LinearMap.mem_ker.mp hx) ⟨i, hi⟩⟩

/-- Successive actual eigenpairs, with maximality on the preceding orthogonal
complement. Dimensions are complex dimensions throughout. -/
structure PositiveEigenFamily (T : H →L[ℂ] H) (n : ℕ) where
  vectors : ℕ → H
  values : ℕ → ℝ
  orthogonal : ∀ i < n, ∀ l < n,
    ⟪vectors i, vectors l⟫_ℂ = if i = l then 1 else 0
  eigenvector : ∀ i < n, T (vectors i) = (values i : ℂ) • vectors i
  positive : ∀ i < n, 0 < values i
  maximal : ∀ i < n, ∀ x,
    (∀ l < i, ⟪vectors l, x⟫_ℂ = 0) →
      (⟪T x, x⟫_ℂ).re ≤ values i * ‖x‖ ^ 2

namespace PositiveEigenFamily

variable {T : H →L[ℂ] H} {n : ℕ}

omit [CompleteSpace H] in
theorem norm_sq_eq_one (f : PositiveEigenFamily T n) {i : ℕ} (hi : i < n) :
    ‖f.vectors i‖ ^ 2 = 1 := by
  have h := congrArg Complex.re (f.orthogonal i hi i hi)
  simpa [inner_self_eq_norm_sq_to_K, pow_two, Complex.mul_re] using h

omit [CompleteSpace H] in
theorem orthonormal (f : PositiveEigenFamily T n) :
    Orthonormal ℂ (fun i : Fin n => f.vectors i) := by
  rw [orthonormal_iff_ite]
  intro i l
  simpa only [Fin.ext_iff] using f.orthogonal i i.isLt l l.isLt

omit [CompleteSpace H] in
theorem value_le (f : PositiveEigenFamily T n) {i j : ℕ}
    (hi : i < n) (hj : j < n) (hij : i ≤ j) : f.values j ≤ f.values i := by
  have h := f.maximal i hi (f.vectors j) (fun l hl => by
    rw [f.orthogonal l (hl.trans hi) j hj, if_neg (lt_of_lt_of_le hl hij).ne])
  rw [f.eigenvector j hj, inner_smul_left, f.orthogonal j hj j hj, if_pos rfl,
    f.norm_sq_eq_one hj] at h
  simpa using h

omit [CompleteSpace H] in
def truncate (f : PositiveEigenFamily T n) {m : ℕ} (hm : m ≤ n) : PositiveEigenFamily T m where
  vectors := f.vectors
  values := f.values
  orthogonal _ hi _ hl := f.orthogonal _ (hi.trans_le hm) _ (hl.trans_le hm)
  eigenvector _ hi := f.eigenvector _ (hi.trans_le hm)
  positive _ hi := f.positive _ (hi.trans_le hm)
  maximal _ hi x hx := f.maximal _ (hi.trans_le hm) x hx

end PositiveEigenFamily

/-- Strict positivity and infinite complex dimension ensure the successive
construction never stops. -/
theorem exists_positive_eigenfamily {T : H →L[ℂ] H}
    (hCompact : IsCompactOperator T) (hP : T.IsPositive)
    (hStrict : ∀ x : H, x ≠ 0 → 0 < (⟪T x, x⟫_ℂ).re)
    (hInfinite : ¬ Module.Finite ℂ H) (n : ℕ) :
    Nonempty (PositiveEigenFamily T n) := by
  classical
  induction n with
  | zero =>
    exact ⟨{ vectors := fun _ => 0, values := fun _ => 0, orthogonal := by simp,
             eigenvector := by simp, positive := by simp, maximal := by simp }⟩
  | succ n ih =>
    obtain ⟨f⟩ := ih
    let Q : H →L[ℂ] H := 1 - ∑ l ∈ Finset.range n,
      (innerSL ℂ (f.vectors l)).smulRight (f.vectors l)
    have hQapp : ∀ x, Q x = x - ∑ l ∈ Finset.range n, ⟪f.vectors l, x⟫_ℂ • f.vectors l :=
      fun x => by simp [Q]
    have hQorth : ∀ x, ∀ k < n, ⟪f.vectors k, Q x⟫_ℂ = 0 := by
      intro x k hk
      rw [hQapp, inner_sub_right, inner_sum]
      simp_rw [inner_smul_right]
      rw [Finset.sum_eq_single k]
      · rw [f.orthogonal k hk k hk]; simp
      · intro l hl hlk
        rw [f.orthogonal k hk l (Finset.mem_range.mp hl), if_neg (Ne.symm hlk), mul_zero]
      · intro h; exact absurd (Finset.mem_range.mpr hk) h
    have hQfix : ∀ x, (∀ l < n, ⟪f.vectors l, x⟫_ℂ = 0) → Q x = x := fun x hx => by
      rw [hQapp, Finset.sum_eq_zero (fun l hl => by
        rw [hx l (Finset.mem_range.mp hl), zero_smul]), sub_zero]
    have hTe : ∀ x, ∀ k < n, ⟪f.vectors k, T (Q x)⟫_ℂ = 0 := fun x k hk => by
      rw [← hP.inner_left_eq_inner_right, f.eigenvector k hk, inner_smul_left,
        hQorth x k hk, mul_zero]
    let T' : H →L[ℂ] H := T.comp Q
    have hTq : ∀ x y, ⟪T' x, y⟫_ℂ = ⟪T (Q x), Q y⟫_ℂ := by
      intro x y
      have hperp : ⟪T (Q x), y - Q y⟫_ℂ = 0 := by
        rw [show y - Q y = ∑ l ∈ Finset.range n, ⟪f.vectors l, y⟫_ℂ • f.vectors l by
          rw [hQapp]; abel, inner_sum]
        exact Finset.sum_eq_zero fun l hl => by
          rw [inner_smul_right, inner_eq_zero_symm.mpr (hTe x l (Finset.mem_range.mp hl)), mul_zero]
      change ⟪T (Q x), y⟫_ℂ = _
      conv_lhs => rw [show y = Q y + (y - Q y) by abel]
      rw [inner_add_right, hperp, add_zero]
    have hSym' : T'.IsSymmetric := fun x y => by
      change ⟪T' x, y⟫_ℂ = ⟪x, T' y⟫_ℂ
      rw [hTq x y, hP.inner_left_eq_inner_right, ← inner_conj_symm x (T' y), hTq y x, inner_conj_symm]
    have hP' : T'.IsPositive := ⟨hSym', fun x => by
      change 0 ≤ (⟪T' x, x⟫_ℂ).re; rw [hTq]; exact hP.re_inner_nonneg_left _⟩
    obtain ⟨y, hy0, hy⟩ := exists_nonzero_orthogonal hInfinite f.vectors n
    have hT'0 : T' ≠ 0 := fun hz => by
      have hTy0 : T y = 0 := by
        calc T y = T' y := by dsimp [T']; rw [hQfix y hy]
          _ = 0 := by rw [hz]; rfl
      have h := hStrict y hy0
      rw [hTy0, inner_zero_left, Complex.zero_re] at h
      exact lt_irrefl 0 h
    obtain ⟨x, hx1, hTx, hmax⟩ := exists_top_eigenvector (hCompact.comp_clm Q) hP' hT'0
    have hM : 0 < ‖T'‖ := norm_pos_iff.mpr hT'0
    have hxperp : ∀ k < n, ⟪f.vectors k, x⟫_ℂ = 0 := fun k hk => by
      have hx : x = ((‖T'‖ : ℂ)⁻¹) • T' x := by
        rw [hTx, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hM.ne'), one_smul]
      rw [hx, inner_smul_right]
      change (‖T'‖ : ℂ)⁻¹ * ⟪f.vectors k, T (Q x)⟫_ℂ = 0
      rw [hTe x k hk, mul_zero]
    refine ⟨{ vectors := Function.update f.vectors n x
              values := Function.update f.values n ‖T'‖
              orthogonal := fun i hi l hl => ?_
              eigenvector := fun i hi => ?_
              positive := fun i hi => ?_
              maximal := fun i hi z hz => ?_ }⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl <;>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl' | rfl
      · rw [Function.update_of_ne hi'.ne, Function.update_of_ne hl'.ne]
        exact f.orthogonal i hi' l hl'
      · rw [Function.update_of_ne hi'.ne, Function.update_self, hxperp i hi', if_neg hi'.ne]
      · rw [Function.update_self, Function.update_of_ne hl'.ne, ← inner_conj_symm,
          hxperp l hl', map_zero, if_neg hl'.ne']
      · rw [Function.update_self, inner_self_eq_norm_sq_to_K, hx1]; simp
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
      · rw [Function.update_of_ne hi'.ne, Function.update_of_ne hi'.ne]; exact f.eigenvector i hi'
      · rw [Function.update_self, Function.update_self]
        simpa only [T', ContinuousLinearMap.comp_apply, hQfix x hxperp] using hTx
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
      · rw [Function.update_of_ne hi'.ne]; exact f.positive i hi'
      · rw [Function.update_self]; exact hM
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hEq
      · rw [Function.update_of_ne hi'.ne]
        exact f.maximal i hi' z fun l hl => by
          simpa [Function.update_of_ne (hl.trans hi').ne] using hz l hl
      · subst i
        rw [Function.update_self]
        have hz' : ∀ l < n, ⟪f.vectors l, z⟫_ℂ = 0 := fun l hl => by
          simpa [Function.update_of_ne hl.ne] using hz l hl
        simpa only [T', ContinuousLinearMap.comp_apply, hQfix z hz'] using hmax z

omit [CompleteSpace H] in
theorem norm_sq_sum_orthonormal {n : ℕ} {e : Fin n → H} (he : Orthonormal ℂ e)
    (c : Fin n → ℂ) : ‖∑ i, c i • e i‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
  have h := congrArg Complex.re (he.inner_sum c c Finset.univ)
  simpa [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    pow_two, Complex.mul_re] using h

end PolyaNeumann.CompactSpectral

namespace PolyaNeumann

open Set Topology
open scoped InnerProductSpace ComplexConjugate

/-- The shifted form resolvent `K = (A_N + I)⁻¹ = J J†`. -/
def neumannResolvent (Ω : Set ℂ) : L2 Ω →L[ℂ] L2 Ω :=
  (h1Value Ω).comp (ContinuousLinearMap.adjoint (h1Value Ω))

theorem neumannResolvent_inner (Ω : Set ℂ) (f g : L2 Ω) :
    ⟪neumannResolvent Ω f, g⟫_ℂ =
      ⟪ContinuousLinearMap.adjoint (h1Value Ω) f,
        ContinuousLinearMap.adjoint (h1Value Ω) g⟫_ℂ :=
  (ContinuousLinearMap.adjoint_inner_right (h1Value Ω)
    (ContinuousLinearMap.adjoint (h1Value Ω) f) g).symm

theorem neumannResolvent_strictPositive {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (f : L2 Ω) (hf : f ≠ 0) : 0 < (⟪neumannResolvent Ω f, f⟫_ℂ).re := by
  rw [neumannResolvent_inner]
  have ha : ContinuousLinearMap.adjoint (h1Value Ω) f ≠ 0 := fun h =>
    hf <| eq_zero_of_inner_h1 hΩ f fun u => by
      rw [← ContinuousLinearMap.adjoint_inner_right (h1Value Ω) u f, h, inner_zero_right]
  exact (re_inner_self_pos (𝕜 := ℂ)).mpr ha

/-- Any positive resolvent eigenvector lifts directly to `NeumannH1` and solves
the weak Neumann eigenvalue equation with eigenvalue `ν⁻¹ - 1 ≥ 0`. -/
private theorem neumannResolvent_weak_lift {Ω : Set ℂ} {ν : ℝ} (hν : 0 < ν) {u : L2 Ω}
    (hu : neumannResolvent Ω u = (ν : ℂ) • u) :
    let w : NeumannH1 Ω := ContinuousLinearMap.adjoint (h1Value Ω) (((ν⁻¹ : ℝ) : ℂ) • u)
    h1Value Ω w = u ∧
      ∀ z : NeumannH1 Ω,
        ∑ i, ⟪h1Gradient Ω i z, h1Gradient Ω i w⟫_ℂ =
          ((ν⁻¹ - 1 : ℝ) : ℂ) * ⟪h1Value Ω z, u⟫_ℂ := by
  intro w
  have hw : h1Value Ω w = u := by
    change neumannResolvent Ω (((ν⁻¹ : ℝ) : ℂ) • u) = u
    rw [map_smul, hu, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hν.ne',
      Complex.ofReal_one, one_smul]
  refine ⟨hw, fun z => ?_⟩
  have h1 := h1_inner Ω z w
  have h2 : ⟪z, w⟫_ℂ = ((ν⁻¹ : ℝ) : ℂ) * ⟪h1Value Ω z, u⟫_ℂ := by
    dsimp only [w]
    rw [ContinuousLinearMap.adjoint_inner_right, inner_smul_right]
  rw [hw, h2] at h1
  exact (eq_sub_of_add_eq' h1.symm).trans (by push_cast; ring)

private theorem neumannResolvent_eigenvalue_nonneg {Ω : Set ℂ} {ν : ℝ} (hν : 0 < ν) {u : L2 Ω}
    (hu0 : u ≠ 0) (hu : neumannResolvent Ω u = (ν : ℂ) • u) : 0 ≤ ν⁻¹ - 1 := by
  obtain ⟨hw, hform⟩ := neumannResolvent_weak_lift hν hu
  let w : NeumannH1 Ω := ContinuousLinearMap.adjoint (h1Value Ω) (((ν⁻¹ : ℝ) : ℂ) • u)
  have hre := congrArg Complex.re (hform w)
  rw [hw, Complex.re_sum, inner_self_eq_norm_sq_to_K] at hre
  have hnn : 0 ≤ ∑ i : Fin 2, (⟪h1Gradient Ω i w, h1Gradient Ω i w⟫_ℂ).re :=
    Finset.sum_nonneg fun _ _ => inner_self_nonneg (𝕜 := ℂ)
  rw [hre] at hnn
  exact nonneg_of_mul_nonneg_left
    (by simpa [RCLike.re_eq_complex_re, pow_two, Complex.mul_re] using hnn)
    (sq_pos_of_pos (norm_pos_iff.mpr hu0))

private theorem L2_infinite_of_isOpen {Ω : Set ℂ} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) :
    ¬ Module.Finite ℂ (L2 Ω) := fun hFinite => by
  letI : Module.Finite ℂ (L2 Ω) := hFinite
  let d := Module.finrank ℂ (L2 Ω)
  refine (neumannEigenvalue_lt_top_of_isOpen hΩ hne d).ne (iInf₂_eq_top.mpr fun S hS => ?_)
  have hle := Submodule.finrank_le S
  rw [hS] at hle
  exact False.elim (by dsimp [d] at hle; omega)

private theorem exists_positive_neumann_eigenfamily {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (n : ℕ) :
    Nonempty (CompactSpectral.PositiveEigenFamily (neumannResolvent Ω) n) :=
  CompactSpectral.exists_positive_eigenfamily
    ((h1Value_isCompactOperator hb hL).comp_clm (ContinuousLinearMap.adjoint (h1Value Ω)))
    (ContinuousLinearMap.isPositive_self_comp_adjoint (h1Value Ω))
    (neumannResolvent_strictPositive hL.1.1)
    (L2_infinite_of_isOpen hL.1.1 hL.1.2.nonempty) n

private theorem neumannEigenvalue_lower_of_eigenfamily {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {j : ℕ} (f : CompactSpectral.PositiveEigenFamily (neumannResolvent Ω) (j + 1)) :
    ENNReal.ofReal ((f.values j)⁻¹ - 1) ≤ neumannEigenvalue Ω j := by
  unfold neumannEigenvalue
  refine le_iInf₂ fun S hS => ?_
  letI : Module.Finite ℂ S := Module.finite_of_finrank_pos (by rw [hS]; omega)
  let coordinates : S →ₗ[ℂ] (Fin j → ℂ) :=
    { toFun := fun u i => ⟪f.vectors i, (u : L2 Ω)⟫_ℂ
      map_add' := by intro x y; ext i; simp [inner_add_right]
      map_smul' := by intro c x; ext i; simp [inner_smul_right] }
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := coordinates) (by simp [hS]))
  have hu0' : (u : L2 Ω) ≠ 0 := fun h => hu0 (Subtype.ext h)
  have horth : ∀ i < j, ⟪f.vectors i, (u : L2 Ω)⟫_ℂ = 0 :=
    fun i hi => congrFun (LinearMap.mem_ker.mp hu) ⟨i, hi⟩
  refine le_trans ?_ (le_iSup₂_of_le (u : L2 Ω) u.property
    (le_iSup (fun _ : (u : L2 Ω) ≠ 0 => rayleigh Ω (u : L2 Ω)) hu0'))
  by_cases hR : rayleigh Ω (u : L2 Ω) = ⊤
  · rw [hR]; exact le_top
  obtain ⟨g, hg⟩ : ∃ g, IsWeakGradient Ω (u : L2 Ω) g := by
    by_contra hno
    have htop : neumannEnergy Ω (u : L2 Ω) = ⊤ :=
      iInf₂_eq_top.mpr fun g hg => False.elim (hno ⟨g, hg⟩)
    exact hR (by unfold rayleigh; rw [htop, ENNReal.top_div_of_ne_top (by simp)])
  let v := h1Vector hg
  let a := ContinuousLinearMap.adjoint (h1Value Ω) (u : L2 Ω)
  have hU : 0 < ‖(u : L2 Ω)‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu0')
  have hν : 0 < f.values j := f.positive j (by omega)
  have hc : ‖(u : L2 Ω)‖ ^ 2 ≤ ‖v‖ * ‖a‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) v a
    rwa [ContinuousLinearMap.adjoint_inner_right, h1Value_h1Vector, inner_self_eq_norm_sq_to_K,
      ← RCLike.ofReal_pow, RCLike.ofReal_eq_complex_ofReal, Complex.norm_real,
      Real.norm_of_nonneg (sq_nonneg _)] at h
  have ha : ‖a‖ ^ 2 ≤ f.values j * ‖(u : L2 Ω)‖ ^ 2 := by
    have h := f.maximal j (by omega) (u : L2 Ω) horth
    rw [neumannResolvent_inner, inner_self_eq_norm_sq_to_K] at h
    simpa [a, pow_two, Complex.mul_re] using h
  have hc2 : (‖(u : L2 Ω)‖ ^ 2) ^ 2 ≤ ‖v‖ ^ 2 * ‖a‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (sq_nonneg ‖(u : L2 Ω)‖) hc 2
  have hUV : ‖(u : L2 Ω)‖ ^ 2 ≤ ‖v‖ ^ 2 * f.values j := by
    have h := hc2.trans (mul_le_mul_of_nonneg_left ha (sq_nonneg ‖v‖))
    exact le_of_mul_le_mul_right (a := ‖(u : L2 Ω)‖ ^ 2) (by convert h using 1 <;> ring) hU
  have hV : (f.values j)⁻¹ * ‖(u : L2 Ω)‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [← div_eq_inv_mul, div_le_iff₀ hν]; simpa only [mul_comm] using hUV
  have hnorm : ‖v‖ ^ 2 = ‖(u : L2 Ω)‖ ^ 2 + ∑ i, ‖g i‖ ^ 2 := by
    simpa only [v, h1Value_h1Vector, h1Gradient_h1Vector] using h1_norm_sq Ω (h1Vector hg)
  rw [rayleigh_eq_ofReal hΩ hu0' hg]
  exact ENNReal.ofReal_le_ofReal ((le_div_iff₀ hU).mpr (by rw [hnorm] at hV; nlinarith))

private theorem neumannEigenvalue_upper_of_eigenfamily {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {j : ℕ} (f : CompactSpectral.PositiveEigenFamily (neumannResolvent Ω) (j + 1)) :
    neumannEigenvalue Ω j ≤ ENNReal.ofReal ((f.values j)⁻¹ - 1) := by
  classical
  let e : Fin (j + 1) → L2 Ω := fun i => f.vectors i
  let E : Fin (j + 1) → ℝ := fun i => (f.values i)⁻¹ - 1
  let w : Fin (j + 1) → NeumannH1 Ω := fun i =>
    ContinuousLinearMap.adjoint (h1Value Ω) ((((f.values i)⁻¹ : ℝ) : ℂ) • e i)
  have he : Orthonormal ℂ e := f.orthonormal
  have hlift : ∀ i : Fin (j + 1), h1Value Ω (w i) = e i ∧
      ∀ z : NeumannH1 Ω, ∑ k, ⟪h1Gradient Ω k z, h1Gradient Ω k (w i)⟫_ℂ =
        (E i : ℂ) * ⟪h1Value Ω z, e i⟫_ℂ :=
    fun i => neumannResolvent_weak_lift (f.positive i i.isLt) (f.eigenvector i i.isLt)
  have hEbound : ∀ i : Fin (j + 1), E i ≤ (f.values j)⁻¹ - 1 := fun i => by
    have h := one_div_le_one_div_of_le (f.positive j (by omega))
      (f.value_le i.isLt (by omega) (by omega))
    simpa only [E, one_div] using sub_le_sub_right h 1
  let S : Submodule ℂ (L2 Ω) := Submodule.span ℂ (Set.range e)
  have hS : Module.finrank ℂ S = j + 1 := by
    rw [finrank_span_eq_card he.linearIndependent, Fintype.card_fin]
  unfold neumannEigenvalue
  refine (iInf₂_le S hS).trans (iSup₂_le fun u hu => iSup_le fun hu0 => ?_)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hu
  let W : NeumannH1 Ω := ∑ i, c i • w i
  have hWval : h1Value Ω W = u := by
    rw [map_sum]; simp_rw [map_smul, (hlift _).1]; exact hc
  have hgW : IsWeakGradient Ω u (fun k => h1Gradient Ω k W) :=
    hWval ▸ h1Value_weakGradient Ω W
  have hquad : ∑ k : Fin 2, ⟪h1Gradient Ω k W, h1Gradient Ω k W⟫_ℂ =
      ∑ i : Fin (j + 1), ((E i * ‖c i‖ ^ 2 : ℝ) : ℂ) := by
    calc
      ∑ k : Fin 2, ⟪h1Gradient Ω k W, h1Gradient Ω k W⟫_ℂ =
          ∑ k : Fin 2, ∑ i : Fin (j + 1), c i * ⟪h1Gradient Ω k W, h1Gradient Ω k (w i)⟫_ℂ :=
        Finset.sum_congr rfl fun k _ => by
          dsimp [W]; rw [map_sum, inner_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [map_smul, inner_smul_right]
      _ = ∑ i : Fin (j + 1), c i * ∑ k : Fin 2, ⟪h1Gradient Ω k W, h1Gradient Ω k (w i)⟫_ℂ := by
        rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
      _ = ∑ i : Fin (j + 1), ((E i * ‖c i‖ ^ 2 : ℝ) : ℂ) :=
        Finset.sum_congr rfl fun i _ => by
          rw [(hlift i).2 W, hWval, ← hc, he.inner_left_fintype c i]
          calc
            c i * ((E i : ℂ) * conj (c i)) = (E i : ℂ) * (conj (c i) * c i) := by ring
            _ = ((E i * ‖c i‖ ^ 2 : ℝ) : ℂ) := by
              rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.ofReal_mul]
  have hre := congrArg Complex.re hquad
  have hgrad_sq : ∑ k : Fin 2, ‖h1Gradient Ω k W‖ ^ 2 = ∑ i : Fin (j + 1), E i * ‖c i‖ ^ 2 := by
    simpa [inner_self_eq_norm_sq_to_K, Complex.re_sum, pow_two] using hre
  have hnorm : ‖u‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
    rw [← hc]; exact CompactSpectral.norm_sq_sum_orthonormal he c
  rw [rayleigh_eq_ofReal hΩ hu0 hgW]
  refine ENNReal.ofReal_le_ofReal ((div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hu0))).mpr ?_)
  rw [hgrad_sq, hnorm, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hEbound i) (sq_nonneg _)

/-- Exact complex multiplicity identification with the weak eigenspace. -/
theorem neumannEigenvalue_multiplicity_eq {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E) :
    (Module.finrank ℂ (neumannEigenspace Ω E) : ℕ∞) =
      {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E}.encard := by
  refine le_antisymm (finrank_neumannEigenspace_le hb hL hE) ?_
  classical
  let S : Set ℕ := {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E}
  have hlt : ENNReal.ofReal E < ENNReal.ofReal (E + 1) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hE).mpr (by linarith)
  have hS : S.Finite :=
    (finite_setOf_neumannEigenvalue_lt hb hL ENNReal.ofReal_ne_top).subset fun j hj => by
      change neumannEigenvalue Ω j < ENNReal.ofReal (E + 1)
      rwa [show neumannEigenvalue Ω j = ENNReal.ofReal E from hj]
  letI : Fintype S := hS.fintype
  obtain ⟨N, hN⟩ := hS.bddAbove
  obtain ⟨f⟩ := exists_positive_neumann_eigenfamily hb hL (N + 1)
  have hidx : ∀ j : S, (j : ℕ) < N + 1 := fun j => Nat.lt_succ_of_le (hN j.property)
  have hmem : ∀ j : S, f.vectors j ∈ neumannEigenspace Ω E := fun j => by
    let g := f.truncate (hidx j)
    have heq : neumannEigenvalue Ω j = ENNReal.ofReal ((f.values j)⁻¹ - 1) :=
      le_antisymm (neumannEigenvalue_upper_of_eigenfamily hL.1.1 g)
        (neumannEigenvalue_lower_of_eigenfamily hL.1.1 g)
    have hvec0 : f.vectors j ≠ 0 := fun h0 => by
      have h1 := f.norm_sq_eq_one (hidx j)
      simp [h0] at h1
    have hnn := neumannResolvent_eigenvalue_nonneg (f.positive j (hidx j)) hvec0
      (f.eigenvector j (hidx j))
    have hval : (f.values j)⁻¹ - 1 = E := by
      have htr := congrArg ENNReal.toReal (j.property.symm.trans heq)
      rwa [ENNReal.toReal_ofReal hE, ENNReal.toReal_ofReal hnn, eq_comm] at htr
    obtain ⟨hw, hform⟩ := neumannResolvent_weak_lift (f.positive j (hidx j))
      (f.eigenvector j (hidx j))
    refine ⟨_, hw ▸ h1Value_weakGradient Ω _, fun v h hv => ?_⟩
    simpa only [hval, h1Value_h1Vector, h1Gradient_h1Vector] using hform (h1Vector hv)
  have hON : Orthonormal ℂ (fun j : S => f.vectors j) := by
    rw [orthonormal_iff_ite]
    intro i k
    simpa only [Subtype.ext_iff] using f.orthogonal i (hidx i) k (hidx k)
  letI : FiniteDimensional ℂ (neumannEigenspace Ω E) :=
    finiteDimensional_neumannEigenspace hb hL E
  simpa only [Set.coe_fintypeCard] using ENat.coe_le_coe.mpr
    (hON.codRestrict (neumannEigenspace Ω E) hmem).linearIndependent.fintype_card_le_finrank

/-- Inclusion sends the actual form kernel to the weak eigenspace. -/
def h1ResonantInclusion (Ω : Set ℂ) (E : ℝ) :
    h1ResonantSpace Ω E →ₗ[ℂ] neumannEigenspace Ω E where
  toFun u := ⟨h1Value Ω u, h1HelmholtzForm_kernel_mem Ω E u u.property⟩
  map_add' u v := Subtype.ext ((h1Value Ω).map_add u v)
  map_smul' c u := Subtype.ext ((h1Value Ω).map_smul c u)

def h1ResonantEquiv {Ω : Set ℂ} (hΩ : IsOpen Ω) (E : ℝ) :
    h1ResonantSpace Ω E ≃ₗ[ℂ] neumannEigenspace Ω E :=
  LinearEquiv.ofBijective (h1ResonantInclusion Ω E)
    ⟨fun _ _ huv => Subtype.ext (h1Value_injective hΩ (congrArg Subtype.val huv)),
     fun u => by
      obtain ⟨g, hg, hw⟩ := u.property
      have hzero : h1HelmholtzForm Ω E (h1Vector hg) = 0 := ext_inner_left ℂ fun v => by
        rw [h1HelmholtzForm_inner, inner_zero_right]
        simp only [h1Value_h1Vector, h1Gradient_h1Vector]
        exact sub_eq_zero.mpr (hw _ _ (h1Value_weakGradient Ω v))
      exact ⟨⟨h1Vector hg, hzero⟩, Subtype.ext rfl⟩⟩

theorem h1ResonantSpace_multiplicity_eq {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E) :
    (Module.finrank ℂ (h1ResonantSpace Ω E) : ℕ∞) =
      {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E}.encard := by
  rw [(h1ResonantEquiv hL.1.1 E).finrank_eq]
  exact neumannEigenvalue_multiplicity_eq hb hL hE

end PolyaNeumann

end
