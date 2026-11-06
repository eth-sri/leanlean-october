module

public import RequestProject.NeumannOperator
public import RequestProject.NeumannMultiplicity
public import RequestProject.FiniteRankCompletion
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Ordered spectrum of the genuine Neumann resolvent

All trial-space dimensions and orthogonality below are over ℂ. The ordered
spectral values are defined using actual eigenvector equations, independently
of the variational values in `Defs`.
-/

@[expose] public section

open Set Filter Topology
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace PolyaNeumann.CompactSpectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {T : H →L[ℂ] H}

theorem exists_eigenvector_of_mem_spectrum (hT : IsCompactOperator T)
    {k : ℂ} (hk : k ∈ spectrum ℂ T) (hk0 : k ≠ 0) :
    ∃ v : H, v ≠ 0 ∧ T v = k • v := by
  let C  := (-k⁻¹) • T
  have hrel : algebraMap ℂ (H →L[ℂ] H) k - T = k • (1 + C) := by
    rw [smul_add, smul_smul, mul_neg, mul_inv_cancel₀ hk0, neg_one_smul,
      Algebra.algebraMap_eq_smul_one, sub_eq_add_neg]
  by_contra hno
  have hinj : Function.Injective ⇑(1 + C) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    change v + (-k⁻¹) • T v = 0 at (by assumption)
    have h2 : k • (v + (-k⁻¹) • T v) = 0 := by simp_all
    rw [smul_add, smul_smul, mul_neg, mul_inv_cancel₀ hk0, neg_one_smul] at h2
    grind
  apply hk
  show IsUnit _
  rw [hrel]
  exact ((IsUnit.mk0 k hk0).map (algebraMap ℂ (H →L[ℂ] H))).mul (isUnit_of_bijective _ ⟨hinj, (injective_iff_surjective_one_add (hT.smul _)).mp hinj⟩)

/-- A nonzero compact positive complex operator attains its norm at a unit
eigenvector. Positivity rules out a negative extremal eigenvalue. -/
theorem exists_top_eigenvector (hT : IsCompactOperator T)
    (hP : T.IsPositive) (hT0 : T ≠ 0) :
    ∃ x : H, ‖x‖ = 1 ∧ T x = (‖T‖ : ℂ) • x ∧
      ∀ y : H, (⟪T y, y⟫_ℂ).re ≤ ‖T‖ * ‖y‖ ^ 2 := by
  haveI : Nontrivial H := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hT0 (ContinuousLinearMap.ext fun x => Subsingleton.elim _ _)
  obtain ⟨k, hk, hkn⟩ := spectrum.exists_nnnorm_eq_spectralRadius T
  have hkn' : ‖k‖ = ‖T‖ := congrArg NNReal.toReal (ENNReal.coe_inj.mp (hkn.trans hP.isSelfAdjoint.spectralRadius_eq_nnnorm))
  obtain ⟨v, hv0, hv⟩ := exists_eigenvector_of_mem_spectrum hT hk (by
    intro hk0
    rw [hk0, norm_zero, eq_comm, norm_eq_zero] at hkn'
    trivial)
  have hkreal  := hP.isSelfAdjoint.mem_spectrum_eq_re hk
  have hkeq : k = ‖T‖ := by
    rw [hkreal] at hkn'
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by
    have hp := hP.re_inner_nonneg_left v
    rw [hv, inner_smul_left] at hp
    exact nonneg_of_mul_nonneg_left (by
      simpa [pow_two] using hp) (sq_pos_of_pos (norm_pos_iff.mpr hv0)))] at hkn'
    grind
  let x  := (‖v‖⁻¹ : ℂ) • v
  refine ⟨x, ?_, ?_, fun y => ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
  · rw [map_smul, hv, hkeq]
    exact smul_comm _ _ _
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
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (by
    intro hker
    exact hInfinite
      (FiniteDimensional.of_injective coordinates (LinearMap.ker_eq_bot.mp hker)))
  refine ⟨x, hx0, fun i hi => ?_⟩
  have h := congrFun (LinearMap.mem_ker.mp hx) ⟨i, hi⟩
  assumption

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

variable (f : PositiveEigenFamily T n)

omit [CompleteSpace H] in
theorem norm_sq_eq_one {i : ℕ} (hi : i < n) :
    ‖f.vectors i‖ ^ 2 = 1 := by
  simpa [pow_two] using congrArg Complex.re (f.orthogonal i hi i hi)

omit [CompleteSpace H] in
theorem orthonormal :
    Orthonormal ℂ (fun i : Fin n => f.vectors i) := by
  rw [orthonormal_iff_ite]
  intro i l
  simpa only [Fin.ext_iff] using f.orthogonal i i.isLt l l.isLt

omit [CompleteSpace H] in
theorem value_le {i j : ℕ}
    (hi : i < n) (hj : j < n) (hij : i ≤ j) : f.values j ≤ f.values i := by
  have h := f.maximal i hi (f.vectors j) (fun l hl => by
    simp [f.orthogonal l (hl.trans hi) j hj, if_neg (lt_of_lt_of_le hl hij).ne])
  rw [f.eigenvector j hj, inner_smul_left, f.orthogonal j hj j hj, f.norm_sq_eq_one hj] at h
  simp_all

end PositiveEigenFamily

variable {T : H →L[ℂ] H} {n : ℕ} {e : Fin n → H}

/-- Strict positivity and infinite complex dimension ensure the successive
construction never stops. -/
theorem exists_positive_eigenfamily (hCompact : IsCompactOperator T) (hP : T.IsPositive)
    (hStrict : ∀ x : H, x ≠ 0 → 0 < (⟪T x, x⟫_ℂ).re)
    (hInfinite : ¬ Module.Finite ℂ H) (n : ℕ) :
    Nonempty (PositiveEigenFamily T n) := by
  classical
  induction n with
  | zero =>
    exact ⟨{ vectors := fun _ => 0
             values := fun _ => 0
             orthogonal := by simp
             eigenvector := by simp
             positive := by simp
             maximal := by simp }⟩
  | succ n ih =>
    obtain ⟨f⟩ := ih
    let Q  := 1 - ∑ l ∈ Finset.range n,
      (innerSL ℂ (f.vectors l)).smulRight (f.vectors l)
    have hQapp : ∀ x, Q x = x - ∑ l ∈ Finset.range n,
        ⟪f.vectors l, x⟫_ℂ • f.vectors l := by
      simp [Q]
    have hQorth : ∀ x, ∀ k < n, ⟪f.vectors k, Q x⟫_ℂ = 0 := by
      intro x k hk
      rw [hQapp, inner_sub_right, inner_sum]
      simp_rw [inner_smul_right]
      rw [Finset.sum_eq_single k]
      · rw [f.orthogonal k hk k hk]; simp
      · intro l hl hlk
        simp [f.orthogonal k hk l (Finset.mem_range.mp hl), if_neg (Ne.symm hlk), mul_zero]
      simp_all
    have hQfix : ∀ x, (∀ l < n, ⟪f.vectors l, x⟫_ℂ = 0) → Q x = x := by
      intro x hx
      rw [hQapp, Finset.sum_eq_zero (fun l hl => by
        simp_all), sub_zero]
    have hTe : ∀ x, ∀ k < n, ⟪f.vectors k, T (Q x)⟫_ℂ = 0 := by
      intro x k hk
      calc
        ⟪f.vectors k, T (Q x)⟫_ℂ = ⟪T (f.vectors k), Q x⟫_ℂ :=
          (hP.inner_left_eq_inner_right _ _).symm
        _ = 0 := by rw [f.eigenvector k hk, inner_smul_left, hQorth x k hk, mul_zero]
    let T'  := T.comp Q
    have hsub : ∀ y, y - Q y = ∑ l ∈ Finset.range n,
        ⟪f.vectors l, y⟫_ℂ • f.vectors l := by
      simp_all
    have hperp : ∀ x y, ⟪T (Q x), y - Q y⟫_ℂ = 0 := by
      intro x y
      rw [hsub, inner_sum]
      apply Finset.sum_eq_zero
      intro l hl
      simp [inner_smul_right, (inner_eq_zero_symm).mpr (hTe x l (Finset.mem_range.mp hl)), mul_zero]
    have hTq : ∀ x y, ⟪T' x, y⟫_ℂ = ⟪T (Q x), Q y⟫_ℂ := by
      intro x y
      have hy : y = Q y + (y - Q y) := by abel
      change ⟪T (Q x), y⟫_ℂ = _
      conv_lhs => rw [hy]
      rw [inner_add_right, hperp, add_zero]
    have hSym' : T'.IsSymmetric := by
      intro x y
      calc
        ⟪T' x, y⟫_ℂ = ⟪T (Q x), Q y⟫_ℂ := hTq x y
        _ = ⟪Q x, T (Q y)⟫_ℂ := hP.isSymmetric _ _
        _ = ⟪x, T' y⟫_ℂ := by
          simp [← inner_conj_symm x (T' y), hTq y x, inner_conj_symm]
    obtain ⟨y, hy0, hy⟩ := exists_nonzero_orthogonal hInfinite f.vectors n
    have hT'0 : T' ≠ 0 := by
      intro hz
      have hTy : T' y = T y := by grind
      have hTy0 : T y = 0 := by simp_all
      have h := hStrict y hy0
      simp_all
    obtain ⟨x, hx1, hTx, hmax⟩ := exists_top_eigenvector (hCompact.comp_clm Q) ⟨hSym', fun x => by
      change 0 ≤ (⟪T' x, x⟫_ℂ).re
      rw [hTq]
      exact hP.re_inner_nonneg_left _⟩ hT'0
    have hM  := norm_pos_iff.mpr hT'0
    have hxperp : ∀ k < n, ⟪f.vectors k, x⟫_ℂ = 0 := by
      intro k hk
      have hx : x = ((‖T'‖ : ℂ)⁻¹) • T' x := by
        rw [hTx, smul_smul, inv_mul_cancel₀ (by simp_all), one_smul]
      rw [hx, inner_smul_right]
      grind
    have hQx  := hQfix x hxperp
    refine ⟨{ vectors := Function.update f.vectors n x
              values := Function.update f.values n ‖T'‖
              orthogonal := ?_
              eigenvector := ?_
              positive := ?_
              maximal := ?_ }⟩
    · intro i hi l hl
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl <;>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl' | rfl
      · rw [Function.update_of_ne hi'.ne, Function.update_of_ne hl'.ne]
        exact f.orthogonal i hi' l hl'
      · grind
      · rw [Function.update_self, Function.update_of_ne hl'.ne, ← inner_conj_symm,
          hxperp l hl', map_zero, if_neg hl'.ne']
      simp_all
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
      · rw [Function.update_of_ne hi'.ne, Function.update_of_ne hi'.ne]
        exact f.eigenvector i hi'
      grind
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
      · rw [Function.update_of_ne hi'.ne]; exact f.positive i hi'
      simp_all
    · intro i hi z hz
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hEq
      · rw [Function.update_of_ne hi'.ne]
        exact f.maximal i hi' z fun l hl => by
          grind
      · subst i
        rw [Function.update_self]
        simpa only [T', ContinuousLinearMap.comp_apply, hQfix z fun l hl => by
          have h := hz l hl
          simp_all [Function.update_of_ne hl.ne]] using hmax z

/-- Actual orthonormal eigenvectors above a positive threshold. -/
def SpectralThreshold (T : H →L[ℂ] H) (j : ℕ) : Set ℝ :=
  {s | 0 < s ∧ ∃ e : Fin j → H, Orthonormal ℂ e ∧
    ∃ ν : Fin j → ℝ, ∀ i, T (e i) = (ν i : ℂ) • e i ∧ s ≤ ν i}

def spectralEigenvalue (T : H →L[ℂ] H) (j : ℕ) : ℝ :=
  sSup (SpectralThreshold T j)

omit [CompleteSpace H] in
theorem norm_sq_sum_orthonormal (he : Orthonormal ℂ e)
    (c : Fin n → ℂ) : ‖∑ i, c i • e i‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
  simpa [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    pow_two] using congrArg Complex.re (he.inner_sum c c Finset.univ)

omit [CompleteSpace H] in
theorem quadratic_sum_eigenvectors (he : Orthonormal ℂ e) (ν : Fin n → ℝ)
    (hEigen : ∀ i, T (e i) = (ν i : ℂ) • e i) (c : Fin n → ℂ) :
    (⟪T (∑ i, c i • e i), ∑ i, c i • e i⟫_ℂ).re = ∑ i, ν i * ‖c i‖ ^ 2 := by
  have h : ⟪T (∑ i, c i • e i), ∑ i, c i • e i⟫_ℂ =
      ∑ i, ((ν i * ‖c i‖ ^ 2 : ℝ) : ℂ) := by
    rw [map_sum, sum_inner]
    simp_rw [map_smul, hEigen, smul_smul, inner_smul_left, he.inner_right_fintype c]
    apply Finset.sum_congr rfl
    intro i _
    calc
      conj (c i * ν i) * c i = ν i * (conj (c i) * c i) := by
        rw [map_mul, Complex.conj_ofReal]; ring
      _ = (ν i * ‖c i‖ ^ 2 : ℝ) := by
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.ofReal_mul]
  rw [h, Complex.re_sum]
  rfl

omit [CompleteSpace H] in
theorem quadratic_lower_on_eigenspan (he : Orthonormal ℂ e) (ν : Fin n → ℝ)
    (hEigen : ∀ i, T (e i) = (ν i : ℂ) • e i) {s : ℝ} (hs : ∀ i, s ≤ ν i)
    {x : H} (hx : x ∈ Submodule.span ℂ (Set.range e)) :
    s * ‖x‖ ^ 2 ≤ (⟪T x, x⟫_ℂ).re := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
  rw [← hc, norm_sq_sum_orthonormal he c, quadratic_sum_eigenvectors he ν hEigen c,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hs i) (sq_nonneg _)

namespace PositiveEigenFamily

variable {T : H →L[ℂ] H} {j : ℕ}

variable (f : PositiveEigenFamily T j)

omit [CompleteSpace H] in
theorem threshold_le_last (hj : 0 < j)
    {s : ℝ} (hs : s ∈ SpectralThreshold T j) : s ≤ f.values (j - 1) := by
  obtain ⟨_, e, he, ν, hν⟩ := hs
  let W  := Submodule.span ℂ (Set.range e)
  have hWdim : Module.finrank ℂ W = j := by
    rw [finrank_span_eq_card he.linearIndependent, Fintype.card_fin]
  letI  := Module.finite_of_finrank_pos (by rw [hWdim]; assumption)
  let coordinates : W →ₗ[ℂ] (Fin (j - 1) → ℂ) :=
    { toFun := fun x i => ⟪f.vectors i, x⟫_ℂ
      map_add' := by intro x y; ext i; simp [inner_add_right]
      map_smul' := by intro c x; ext i; simp [inner_smul_right] }
  have hker : LinearMap.ker coordinates ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simp_all)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact le_of_mul_le_mul_right ((quadratic_lower_on_eigenspan he ν (fun i => (hν i).1) (fun i => (hν i).2) x.property).trans (f.maximal (j - 1) (by omega) x (by
    intro l hl
    have h := congrFun (LinearMap.mem_ker.mp hx) ⟨l, hl⟩
    assumption))) (sq_pos_of_pos (norm_pos_iff.mpr fun h => hx0 (Subtype.ext h)))

omit [CompleteSpace H] in
theorem last_mem_threshold (hj : 0 < j) :
    f.values (j - 1) ∈ SpectralThreshold T j := by
  refine ⟨f.positive (j - 1) (by omega), (fun i  => f.vectors i), f.orthonormal,
    (fun i  => f.values i), fun i => ⟨f.eigenvector i i.isLt, ?_⟩⟩
  exact f.value_le i.isLt (by omega) (by omega)

omit [CompleteSpace H] in
theorem spectralEigenvalue_eq_last (hj : 0 < j) :
    spectralEigenvalue T j = f.values (j - 1) := by
  apply le_antisymm
  · exact csSup_le ⟨_, f.last_mem_threshold hj⟩ (fun s hs => f.threshold_le_last hj hs)
  · exact le_csSup ⟨f.values (j - 1), fun s hs => f.threshold_le_last hj hs⟩
      (f.last_mem_threshold hj)

omit [CompleteSpace H] in
theorem spectralEigenvalue_at_index {n : ℕ} (f : PositiveEigenFamily T n)
    {i : ℕ} (hi : i < n) : spectralEigenvalue T (i + 1) = f.values i := by
  let g : PositiveEigenFamily T (i + 1) :=
    { vectors := f.vectors
      values := f.values
      orthogonal := fun k hk l hl => f.orthogonal k (by omega) l (by omega)
      eigenvector := fun k hk => f.eigenvector k (by omega)
      positive := fun k hk => f.positive k (by omega)
      maximal := fun k hk x hx => f.maximal k (by omega) x hx }
  simpa only [Nat.add_sub_cancel] using g.spectralEigenvalue_eq_last (by omega)

end PositiveEigenFamily

end PolyaNeumann.CompactSpectral

namespace PolyaNeumann

variable {Ω : Set ℂ} {u : L2 Ω}

theorem L2_infinite_of_isOpen (hΩ : IsOpen Ω) (hne : Ω.Nonempty) :
    ¬ Module.Finite ℂ (L2 Ω) := by
  intro hFinite
  let d := Module.finrank ℂ (L2 Ω)
  exact (neumannEigenvalue_lt_top_of_isOpen hΩ hne d).ne (by
    apply iInf₂_eq_top.mpr
    intro S hS
    have hle := Submodule.finrank_le S
    omega)

/-- Numbered values of the actual resolvent spectrum; Neumann indices start
at zero, so the reciprocal resolvent index is `j + 1`. -/
def spectralNeumannEigenvalue (Ω : Set ℂ) (j : ℕ) : ℝ :=
  (CompactSpectral.spectralEigenvalue (neumannResolvent Ω) (j + 1))⁻¹ - 1

theorem exists_positive_neumann_eigenfamily (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (n : ℕ) :
    Nonempty (CompactSpectral.PositiveEigenFamily (neumannResolvent Ω) n) :=
  CompactSpectral.exists_positive_eigenfamily (neumannResolvent_compact hb hL)
    (neumannResolvent_isPositive Ω) (neumannResolvent_strictPositive hL.1.1)
    (L2_infinite_of_isOpen hL.1.1 hL.1.2.nonempty) n

/-- The genuine H¹ norm is exactly mass plus weak-gradient energy. -/
theorem h1Vector_norm_sq {g : Fin 2 → L2 Ω}
    (hg : IsWeakGradient Ω u g) :
    ‖h1Vector hg‖ ^ 2 = ‖u‖ ^ 2 + ∑ i, ‖g i‖ ^ 2 := by
  simpa only [h1Value_h1Vector, h1Gradient_h1Vector] using h1_norm_sq Ω (h1Vector hg)

theorem exists_grad_of_rayleigh_ne_top (hR : rayleigh Ω u ≠ ⊤) : ∃ g, IsWeakGradient Ω u g := by
  by_contra hno
  have htop : neumannEnergy Ω u = ⊤ := by
    apply iInf₂_eq_top.mpr
    simp_all
  exact hR (by unfold rayleigh; rw [htop, ENNReal.top_div_of_ne_top (by simp)])

/-- Maximality of a resolvent eigenfamily gives the original Neumann
Rayleigh lower bound, by Cauchy–Schwarz in the actual H¹ space. -/
theorem neumann_rayleigh_lower_of_orthogonality (hΩ : IsOpen Ω)
    {j : ℕ} (f : CompactSpectral.PositiveEigenFamily (neumannResolvent Ω) (j + 1))
    {u : L2 Ω} (hu0 : u ≠ 0) (horth : ∀ i < j, ⟪f.vectors i, u⟫_ℂ = 0) :
    ENNReal.ofReal ((f.values j)⁻¹ - 1) ≤ rayleigh Ω u := by
  by_cases hR : rayleigh Ω u = ⊤
  · simp_all
  obtain ⟨g, hg⟩ := exists_grad_of_rayleigh_ne_top hR
  let v := h1Vector hg
  let a := ContinuousLinearMap.adjoint (h1Value Ω) u
  have hU  := sq_pos_of_pos (norm_pos_iff.mpr hu0)
  have hc : ‖u‖ ^ 2 ≤ ‖v‖ * ‖a‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) v a
    rwa [ContinuousLinearMap.adjoint_inner_right, h1Value_h1Vector,
      inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_eq_complex_ofReal,
      Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)] at h
  have ha : ‖a‖ ^ 2 ≤ f.values j * ‖u‖ ^ 2 := by
    have h := f.maximal j (by omega) u horth
    rw [neumannResolvent_inner] at h
    simpa [pow_two] using h
  have hUV : ‖u‖ ^ 2 ≤ ‖v‖ ^ 2 * f.values j := by
    nlinarith
  have hV : (f.values j)⁻¹ * ‖u‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    simp_all [← div_eq_inv_mul, div_le_iff₀ (f.positive j (by omega))]
  have hnorm  := h1Vector_norm_sq hg
  have hq : ((f.values j)⁻¹ - 1) * ‖u‖ ^ 2 ≤ ∑ i, ‖g i‖ ^ 2 := by
    nlinarith
  rw [rayleigh_eq_ofReal hΩ hu0 hg]
  apply ENNReal.ofReal_le_ofReal
  simp_all [le_div_iff₀ hU]

/-- The dimension argument takes place directly in the original L² trial
space, with complex dimensions; it does not assume spectral identification. -/
theorem neumannEigenvalue_lower_of_eigenfamily (hΩ : IsOpen Ω)
    {j : ℕ} (f : CompactSpectral.PositiveEigenFamily (neumannResolvent Ω) (j + 1)) :
    ENNReal.ofReal ((f.values j)⁻¹ - 1) ≤ neumannEigenvalue Ω j := by
  refine le_iInf₂ fun S hS => ?_
  letI : Module.Finite ℂ S := Module.finite_of_finrank_pos (by omega)
  let coordinates : S →ₗ[ℂ] (Fin j → ℂ) :=
    { toFun := fun u i => ⟪f.vectors i, u⟫_ℂ
      map_add' := by intro x y; ext i; simp [inner_add_right]
      map_smul' := by intro c x; ext i; simp [inner_smul_right] }
  have hker : LinearMap.ker coordinates ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simp_all)
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hu0'  := fun h => hu0 (Subtype.ext h)
  exact (neumann_rayleigh_lower_of_orthogonality hΩ f hu0' (by
    intro i hi
    have h := congrFun (LinearMap.mem_ker.mp hu) ⟨i, hi⟩
    assumption)).trans
    (le_iSup₂_of_le u u.property (le_iSup (fun _  =>
      rayleigh Ω u) hu0'))

theorem rayleigh_eq_operator (hΩ : IsOpen Ω)
    (u : (neumannOperator Ω).domain) (hu0 : (u : L2 Ω) ≠ 0) :
    rayleigh Ω u =
      ENNReal.ofReal ((⟪(u : L2 Ω), neumannOperator Ω u⟫_ℂ).re / ‖(u : L2 Ω)‖ ^ 2) := by
  obtain ⟨g, hg, hw⟩ := (neumannOperator_weak_representation hΩ u
    (neumannOperator Ω u)).mp ⟨u.property, rfl⟩
  have h' : ∑ i, ‖g i‖ ^ 2 = (⟪(u : L2 Ω), neumannOperator Ω u⟫_ℂ).re := by
    simpa [pow_two] using congrArg Complex.re (hw u g hg)
  rw [rayleigh_eq_ofReal hΩ hu0 hg, h']

theorem neumann_operator_eigenpair_of_resolvent (hΩ : IsOpen Ω)
    {eigenCoefficient : ℝ} (heigenCoefficient : 0 < eigenCoefficient) {u : L2 Ω} (hu : neumannResolvent Ω u = (eigenCoefficient : ℂ) • u) :
    ∃ hd : u ∈ (neumannOperator Ω).domain,
      neumannOperator Ω ⟨u, hd⟩ = ((eigenCoefficient⁻¹ - 1 : ℝ) : ℂ) • u := by
  have hparam : (eigenCoefficient⁻¹ - 1 : ℝ) + 1 = (eigenCoefficient : ℂ)⁻¹ := by
    norm_num
  apply (neumannOperator_eigen_iff_resolvent hΩ _ (by
    rw [hparam]; exact inv_ne_zero (by exact_mod_cast heigenCoefficient.ne')) u).mpr
  simp_all

/-- The span of the actual first `j + 1` eigenvectors yields the original
complex Neumann min–max upper bound. -/
theorem neumannEigenvalue_upper_of_eigenfamily (hΩ : IsOpen Ω)
    {j : ℕ} (f : CompactSpectral.PositiveEigenFamily (neumannResolvent Ω) (j + 1)) :
    neumannEigenvalue Ω j ≤ ENNReal.ofReal ((f.values j)⁻¹ - 1) := by
  classical
  let e : Fin (j + 1) → L2 Ω := fun i => f.vectors i
  let E : Fin (j + 1) → ℝ := fun i => (f.values i)⁻¹ - 1
  have he  := f.orthonormal
  have heig : ∀ i : Fin (j + 1), ∃ hu : e i ∈ (neumannOperator Ω).domain,
      neumannOperator Ω ⟨e i, hu⟩ = (E i : ℂ) • e i := fun i =>
    neumann_operator_eigenpair_of_resolvent hΩ (f.positive i i.isLt) (f.eigenvector i i.isLt)
  choose hd hEigen using heig
  let ed : Fin (j + 1) → (neumannOperator Ω).domain := fun i => ⟨e i, hd i⟩
  have hEbound : ∀ i : Fin (j + 1), E i ≤ (f.values j)⁻¹ - 1 := by
    intro i
    have h := one_div_le_one_div_of_le (f.positive j (by omega))
      (f.value_le i.isLt (by omega) (by omega))
    grind
  let S  := Submodule.span ℂ (Set.range e)
  refine (iInf₂_le S (by
    rw [finrank_span_eq_card he.linearIndependent, Fintype.card_fin])).trans (iSup₂_le fun u hu => iSup_le fun hu0 => ?_)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hu
  let v  := ∑ i, c i • ed i
  have hvsum : v = ∑ i, c i • e i := by simp [v, ed]
  have hv : v = u := by simp_all
  have hAv : neumannOperator Ω v = ∑ i, (c i * E i) • e i := by
    change (neumannOperator Ω).toFun (∑ i, c i • ed i) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    change c i • neumannOperator Ω ⟨e i, hd i⟩ = _
    rw [hEigen i, smul_smul]
  have hquadratic : (⟪(v : L2 Ω), neumannOperator Ω v⟫_ℂ).re =
      ∑ i, E i * ‖c i‖ ^ 2 := by
    rw [hAv, inner_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_smul_right]
    have hcoeff : ⟪(v : L2 Ω), e i⟫_ℂ = conj (c i) := by
      rw [hvsum]
      exact he.inner_left_fintype c i
    rw [hcoeff]
    have heq : (c i * E i) * conj (c i) = (E i * ‖c i‖ ^ 2 : ℝ) := by
      calc
        (c i * E i) * conj (c i) = E i * (conj (c i) * c i) := by ring
        _ = _ := by
          rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.ofReal_mul]
    rw [heq, Complex.ofReal_re]
  have hnorm : ‖(v : L2 Ω)‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
    rw [hvsum]
    exact CompactSpectral.norm_sq_sum_orthonormal he c
  have hq : (⟪(v : L2 Ω), neumannOperator Ω v⟫_ℂ).re ≤
      ((f.values j)⁻¹ - 1) * ‖(v : L2 Ω)‖ ^ 2 := by
    rw [hquadratic, hnorm, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hEbound i) (sq_nonneg _)
  have hv0 : (v : L2 Ω) ≠ 0 := by simp_all
  rw [← hv, rayleigh_eq_operator hΩ v hv0]
  apply ENNReal.ofReal_le_ofReal
  rwa [div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hv0))]

/-- Identification with the ordered spectrum of the actual shifted form
resolvent, proved using the original complex min–max definition. -/
theorem neumannEigenvalue_eq_spectral {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (j : ℕ) :
    neumannEigenvalue Ω j = ENNReal.ofReal (spectralNeumannEigenvalue Ω j) := by
  obtain ⟨f⟩ := exists_positive_neumann_eigenfamily hb hL (j + 1)
  have heigenCoefficient : CompactSpectral.spectralEigenvalue (neumannResolvent Ω) (j + 1) = f.values j := by
    simpa using f.spectralEigenvalue_eq_last (by omega)
  rw [spectralNeumannEigenvalue, heigenCoefficient]
  exact le_antisymm (neumannEigenvalue_upper_of_eigenfamily hL.1.1 f)
    (neumannEigenvalue_lower_of_eigenfamily hL.1.1 f)

theorem spectralNeumannEigenvalue_nonneg (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (j : ℕ) : 0 ≤ spectralNeumannEigenvalue Ω j := by
  obtain ⟨f⟩ := exists_positive_neumann_eigenfamily hb hL (j + 1)
  obtain ⟨hu, hAu⟩ := neumann_operator_eigenpair_of_resolvent hL.1.1
    (f.positive j (by omega)) (f.eigenvector j (by omega))
  have h := neumannOperator_nonneg hL.1.1 ⟨f.vectors j, hu⟩
  rw [hAu, inner_smul_right, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
    f.norm_sq_eq_one (by omega)] at h
  have heigenCoefficient : CompactSpectral.spectralEigenvalue (neumannResolvent Ω) (j + 1) = f.values j := by
    simpa using f.spectralEigenvalue_eq_last (by omega)
  simp_all [spectralNeumannEigenvalue]

theorem neumannEigenvalue_toReal_eq_spectral (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (j : ℕ) :
    (neumannEigenvalue Ω j).toReal = spectralNeumannEigenvalue Ω j := by
  simp [neumannEigenvalue_eq_spectral hb hL j, ENNReal.toReal_ofReal (spectralNeumannEigenvalue_nonneg hb hL j)]

theorem neumannEigenvalue_toReal_eq_family (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {n : ℕ}
    (f : CompactSpectral.PositiveEigenFamily (neumannResolvent Ω) n)
    {j : ℕ} (hj : j < n) :
    (neumannEigenvalue Ω j).toReal = (f.values j)⁻¹ - 1 := by
  rw [neumannEigenvalue_toReal_eq_spectral hb hL j, spectralNeumannEigenvalue,
    f.spectralEigenvalue_at_index hj]

/-- The converse multiplicity bound: repeated numbered values give linearly
independent actual eigenfunctions over ℂ. -/
theorem neumannEigenvalue_multiplicity_le_finrank (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {E : ℝ} (hE : 0 ≤ E) :
    {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E}.encard ≤
      Module.finrank ℂ (neumannEigenspace Ω E) := by
  classical
  let S  := {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E}
  have hlt : ENNReal.ofReal E < ENNReal.ofReal (E + 1) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hE).mpr (by linarith)
  have hS : S.Finite :=
    (finite_setOf_neumannEigenvalue_lt hb hL ENNReal.ofReal_ne_top).subset
      (fun j hj => by
        change neumannEigenvalue Ω j < ENNReal.ofReal (E + 1)
        grind)
  letI  := hS.fintype
  obtain ⟨N, hN⟩ := hS.bddAbove
  obtain ⟨f⟩ := exists_positive_neumann_eigenfamily hb hL (N + 1)
  have hidx : ∀ j : S, j < N + 1 := fun j => Nat.lt_succ_of_le (hN j.property)
  have hON : Orthonormal ℂ (fun j : S => f.vectors j) := by
    rw [orthonormal_iff_ite]
    intro i k
    simpa only [Subtype.ext_iff] using f.orthogonal i (hidx i) k (hidx k)
  letI  :=
    finiteDimensional_neumannEigenspace hb hL E
  simpa only [Set.coe_fintypeCard] using (ENat.coe_le_coe.mpr (hON.codRestrict (neumannEigenspace Ω E) (by
    intro j
    obtain ⟨hu, hAu⟩ := neumann_operator_eigenpair_of_resolvent hL.1.1
      (f.positive j (hidx j)) (f.eigenvector j (hidx j))
    have hvalue : (f.values j)⁻¹ - 1 = E := by
      rw [← neumannEigenvalue_toReal_eq_family hb hL f (hidx j)]
      rw [j.property, ENNReal.toReal_ofReal hE]
    rw [← neumannOperatorEigenspace_eq hL.1.1 E, mem_neumannOperatorEigenspace_iff]
    grind)).linearIndependent.fintype_card_le_finrank)

/-- Exact complex multiplicity identification with the weak and actual
operator eigenspaces. -/
theorem neumannEigenvalue_multiplicity_eq (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E) :
    Module.finrank ℂ (neumannEigenspace Ω E) =
      {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E}.encard :=
  le_antisymm (finrank_neumannEigenspace_le hb hL hE)
    (neumannEigenvalue_multiplicity_le_finrank hb hL hE)

end PolyaNeumann

end
