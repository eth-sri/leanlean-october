module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Tactic

/-!
# The weighted shift (Section 4 of the paper, Definition 4.1 and Lemma 4.2)

On `ℋ = ℓ²(ℕ₀)` with orthonormal basis `(e_n)`, the weighted shift is
`S_N e_0 = √2 e_1`, `S_N e_n = e_{n+1}` (`n ≥ 1`), and `D_N = 2 P_0 - P_1`.
-/

@[expose] public section

open scoped ComplexConjugate

noncomputable section

namespace PolyaNeumann

/-- The Hilbert space `ℋ = ℓ²(ℕ₀)`. -/
abbrev Ell2 := lp (fun _ : ℕ => ℂ) 2

/-! ### Instance normalisation for the Lean/Mathlib `v4.35.0-rc2` port

With Lean/Mathlib `v4.35.0-rc2`, type-class search elaborates the additive and module
structures of the `lp` model of `ℋ` through the subtype (`AddSubmonoidClass`) path, and the
stricter transparency discipline of the new unifier then no longer identifies these with the
structures expected by generic lemmas such as `add_smul` or by instances on `ℋ →L[ℂ] ℋ`.
The instances below fix one canonical choice: each is the standard Mathlib instance (all are
definitionally equal to the previously inferred ones), registered with high priority so that
every statement is elaborated with it.  They change no definition or statement of the
development. -/

instance (priority := high) instIsTopologicalAddGroupComplex : IsTopologicalAddGroup ℂ :=
  SeminormedAddCommGroup.toIsTopologicalAddGroup

instance (priority := high) instAddCommGroupEll2 : AddCommGroup Ell2 :=
  NormedAddCommGroup.toAddCommGroup

instance (priority := high) instAddCommMonoidEll2 : AddCommMonoid Ell2 :=
  AddCommGroup.toAddCommMonoid

instance (priority := high) instModuleComplexEll2 : Module ℂ Ell2 :=
  NormedSpace.toModule

instance (priority := high) instModuleRealEll2 : Module ℝ Ell2 :=
  NormedSpace.toModule

instance (priority := high) instIsTopologicalAddGroupEll2 : IsTopologicalAddGroup Ell2 :=
  SeminormedAddCommGroup.toIsTopologicalAddGroup

instance : ContinuousStar (Ell2 →L[ℂ] Ell2) :=
  @NormedStarGroup.to_continuousStar (Ell2 →L[ℂ] Ell2) _ _ _

instance : StarModule ℝ (Ell2 →L[ℂ] Ell2) :=
  @StarModule.complexToReal (Ell2 →L[ℂ] Ell2) _ _ _ _



/-- `r • x = (r : ℂ) • x` for real scalars acting on `ℋ`. -/
lemma real_smul_eq_coe_smul_ell2 (r : ℝ) (x : Ell2) : r • x = (r : ℂ) • x :=
  (Complex.coe_smul r x).symm

/-- `r • A = (r : ℂ) • A` for real scalars acting on `ℋ →L[ℂ] ℋ`. -/
lemma real_smul_eq_coe_smul_clm (r : ℝ) (A : Ell2 →L[ℂ] Ell2) : r • A = (r : ℂ) • A :=
  (Complex.coe_smul r A).symm

section

variable (n : ℕ)
include n

/-- The weights of the shift: `w_0 = √2`, `w_n = 1` for `n ≥ 1`. -/
def shiftWeight  : ℂ := if n = 0 then (Real.sqrt 2 : ℂ) else 1

lemma conj_shiftWeight  : conj (shiftWeight n) = shiftWeight n := by
  unfold shiftWeight; aesop

lemma norm_shiftWeight_sq_le  : ‖shiftWeight n‖ ^ 2 ≤ 2 := by
  unfold shiftWeight; aesop

lemma shiftWeight_mul_self  :
    shiftWeight n * shiftWeight n = if n = 0 then 2 else 1 := by
  unfold shiftWeight; split_ifs
  · rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; simp
  simp

end

section

variable (f : ℕ → ℂ)
include f

/-- Coordinates of `S_N f`. -/
def shiftFun  : ℕ → ℂ
  | 0 => 0
  | n + 1 => shiftWeight n * f n


end

lemma summable_sq (f : Ell2) : Summable fun n => ‖(f : ℕ → ℂ) n‖ ^ 2 := by
  have := (memℓp_gen_iff (p := 2) (by simp)).mp f.2
  simp_all

lemma memℓp_of_summable_sq {g : ℕ → ℂ} (h : Summable fun n => ‖g n‖ ^ 2) :
    Memℓp g 2 := by
  rw [memℓp_gen_iff (by simp)]
  norm_cast

section

variable (f : Ell2)
include f

lemma tsum_sq_eq_norm_sq  : ∑' n, ‖(f : ℕ → ℂ) n‖ ^ 2 = ‖f‖ ^ 2 := by
  have := lp.norm_rpow_eq_tsum (p := 2) (by simp) f
  simp_all

lemma shift_sq_bound  (n : ℕ) :
    ‖shiftWeight n * (f : ℕ → ℂ) n‖ ^ 2 ≤ 2 * ‖(f : ℕ → ℂ) n‖ ^ 2 := by
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (norm_shiftWeight_sq_le n) (by positivity)

lemma summable_shiftFun  : Summable fun n => ‖shiftFun f n‖ ^ 2 := by
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_)
    ((summable_sq f).mul_left 2)
  exact shift_sq_bound f n


end

/-- `S_N` as a linear map. -/
def shiftLin : Ell2 →ₗ[ℂ] Ell2 where
  toFun f := ⟨shiftFun f, memℓp_of_summable_sq (summable_shiftFun f)⟩
  map_add' f g := by
    apply lp.ext; funext n
    change shiftFun (⇑(f + g)) n = shiftFun ⇑f n + shiftFun ⇑g n
    cases n <;> simp [shiftFun, mul_add]
  map_smul' c f := by
    apply lp.ext; funext n
    change shiftFun (⇑(c • f)) n = c • shiftFun ⇑f n
    cases n <;> simp [shiftFun]; ring

lemma shiftLin_norm_le (f : Ell2) : ‖shiftLin f‖ ≤ Real.sqrt 2 * ‖f‖ := by
  apply lp.norm_le_of_tsum_le (p := 2) (by simp) (by positivity)
  simp  
  rw [mul_pow, Real.sq_sqrt (by norm_num), ← tsum_sq_eq_norm_sq, ← tsum_mul_left]
  change ∑' n, ‖shiftFun f n‖ ^ 2 ≤ _
  rw [(summable_shiftFun f).tsum_eq_zero_add]
  simp only [shiftFun, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_add]
  calc ∑' n, ‖shiftWeight n * (f : ℕ → ℂ) n‖ ^ 2 ≤ ∑' n, 2 * ‖(f : ℕ → ℂ) n‖ ^ 2 :=
        Summable.tsum_le_tsum (fun n => shift_sq_bound f n)
          ((summable_nat_add_iff 1).mpr (summable_shiftFun f))
          ((summable_sq f).mul_left 2)
    _ ≤ _ := le_rfl

/-- The weighted shift `S_N`: `S_N e_0 = √2 e_1`, `S_N e_n = e_{n+1}` for `n ≥ 1`. -/
def shiftN : Ell2 →L[ℂ] Ell2 := shiftLin.mkContinuous (Real.sqrt 2) shiftLin_norm_le

/-- The adjoint of the weighted shift. -/
def shiftNAdj : Ell2 →L[ℂ] Ell2 := ContinuousLinearMap.adjoint shiftN

section

variable (f : Ell2)
include f

@[simp] lemma shiftN_apply_zero  : (shiftN f : ℕ → ℂ) 0 = 0 := rfl

@[simp] lemma shiftN_apply_succ  (n : ℕ) :
    (shiftN f : ℕ → ℂ) (n + 1) = shiftWeight n * (f : ℕ → ℂ) n := rfl

end

/-- The standard basis vector `e_n` of `ℓ²(ℕ₀)`. -/
def basisVec (n : ℕ) : Ell2 := lp.single 2 n (1 : ℂ)

lemma inner_single (f : Ell2) (k : ℕ) :
    inner ℂ (lp.single 2 k (1 : ℂ) : Ell2) f = (f : ℕ → ℂ) k := by
  simp [lp.inner_single_left, RCLike.inner_apply]

private lemma shiftN_basisVec (n : ℕ) : shiftN (basisVec n) = shiftWeight n • basisVec (n+1) := by
  apply lp.ext; funext i
  cases i with
  | zero => simp [basisVec]
  | succ i => by_cases hi : i = n <;> simp [basisVec, lp.single_apply, hi]

@[simp] lemma shiftNAdj_apply (f : Ell2) (n : ℕ) :
    (shiftNAdj f : ℕ → ℂ) n = shiftWeight n * (f : ℕ → ℂ) (n + 1) := by
  rw [← inner_single (shiftNAdj f), ← inner_single f (n + 1)]
  change inner ℂ (basisVec n) (ContinuousLinearMap.adjoint shiftN f) = _
  rw [ContinuousLinearMap.adjoint_inner_right, shiftN_basisVec, inner_smul_left]
  simp [conj_shiftWeight, basisVec]

lemma shiftNAdj_eq_adjoint : shiftNAdj = ContinuousLinearMap.adjoint shiftN := rfl

/-- The operator `D_N = 2 P_0 - P_1`, i.e. the diagonal operator with entries
`(2, -1, 0, 0, …)`. -/
def diagN : Ell2 →L[ℂ] Ell2 :=
  (2 : ℂ) • (ContinuousLinearMap.toSpanSingleton ℂ (lp.single 2 0 (1 : ℂ) : Ell2)).comp
      (innerSL ℂ (lp.single 2 0 (1 : ℂ) : Ell2)) -
    (ContinuousLinearMap.toSpanSingleton ℂ (lp.single 2 1 (1 : ℂ) : Ell2)).comp
      (innerSL ℂ (lp.single 2 1 (1 : ℂ) : Ell2))

/-- The diagonal entries of `D_N`. -/
def diagEntry (n : ℕ) : ℂ := if n = 0 then 2 else if n = 1 then -1 else 0

lemma diagN_apply (f : Ell2) (n : ℕ) :
    (diagN f : ℕ → ℂ) n = diagEntry n * (f : ℕ → ℂ) n := by
  simp only [diagN, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, inner_single, lp.coeFn_sub, Pi.sub_apply, Pi.smul_apply, diagEntry]
  aesop

/-- Lemma 4.2: `[S_N^*, S_N] = D_N`. -/
theorem shift_commutator :
    ContinuousLinearMap.adjoint shiftN * shiftN - shiftN * ContinuousLinearMap.adjoint shiftN
      = diagN := by
  rw [← shiftNAdj_eq_adjoint]
  ext1 f
  apply lp.ext; funext n
  simp  [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, lp.coeFn_sub, Pi.sub_apply, diagN_apply]
  rcases n with _ | _ | n
  · simp [shiftWeight_mul_self, diagEntry, ← mul_assoc]
  · simp only [shiftN_apply_succ, shiftNAdj_apply, diagEntry]
    grind [mul_assoc, shiftWeight_mul_self]
  · simp only [shiftN_apply_succ, shiftNAdj_apply, diagEntry]
    grind [mul_assoc, shiftWeight_mul_self]

end PolyaNeumann

end
