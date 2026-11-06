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

instance : IsScalarTower ℝ (Ell2 →L[ℂ] Ell2) (Ell2 →L[ℂ] Ell2) :=
  @IsScalarTower.right ℝ (Ell2 →L[ℂ] Ell2) _ _ _

instance : SMulCommClass ℝ (Ell2 →L[ℂ] Ell2) (Ell2 →L[ℂ] Ell2) :=
  @Algebra.to_smulCommClass ℝ (Ell2 →L[ℂ] Ell2) _ _ _

variable (r : ℝ) (f : Ell2) (n : ℕ)

/-- `r • x = (r : ℂ) • x` for real scalars acting on `ℋ`. -/
lemma real_smul_eq_coe_smul_ell2 (x : Ell2) : r • x = (r : ℂ) • x :=
  (Complex.coe_smul r x).symm

/-- `r • A = (r : ℂ) • A` for real scalars acting on `ℋ →L[ℂ] ℋ`. -/
lemma real_smul_eq_coe_smul_clm (A : Ell2 →L[ℂ] Ell2) : r • A = (r : ℂ) • A :=
  (Complex.coe_smul r A).symm

/-- The weights of the shift: `w_0 = √2`, `w_n = 1` for `n ≥ 1`. -/
def shiftWeight (n : ℕ) : ℂ := if n = 0 then (Real.sqrt 2 : ℂ) else 1

lemma conj_shiftWeight : conj (shiftWeight n) = shiftWeight n := by
  unfold shiftWeight; split_ifs <;> simp

lemma norm_shiftWeight_sq_le : ‖shiftWeight n‖ ^ 2 ≤ 2 := by
  unfold shiftWeight; split_ifs <;> simp

lemma shiftWeight_mul_self :
    shiftWeight n * shiftWeight n = if n = 0 then 2 else 1 := by
  unfold shiftWeight; simp_all [← Complex.ofReal_mul]

/-- Coordinates of `S_N f`. -/
def shiftFun (f : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => shiftWeight n * f n

/-- Coordinates of `S_N^* f`. -/
def shiftAdjFun (f : ℕ → ℂ) : ℕ → ℂ := fun n => shiftWeight n * f (n + 1)

lemma two_toReal : (2 : ENNReal).toReal = 2 := by simp

lemma summable_sq : Summable fun n => ‖f n‖ ^ 2 := by
  have := (memℓp_gen_iff  (by simp)).mp f.2
  simp_all

lemma memℓp_of_summable_sq {g : ℕ → ℂ} (h : Summable fun n => ‖g n‖ ^ 2) :
    Memℓp g 2 := by
  rw [memℓp_gen_iff (by simp)]
  simp_all

lemma tsum_sq_eq_norm_sq : ∑' n, ‖f n‖ ^ 2 = ‖f‖ ^ 2 := by
  have := lp.norm_rpow_eq_tsum  (by simp) f
  simp_all

lemma shift_sq_bound :
    ‖shiftWeight n * f n‖ ^ 2 ≤ 2 * ‖f n‖ ^ 2 := by
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (norm_shiftWeight_sq_le n) (by positivity)

lemma shiftAdj_sq_bound :
    ‖shiftWeight n * f (n + 1)‖ ^ 2 ≤ 2 * ‖f (n + 1)‖ ^ 2 := by
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (norm_shiftWeight_sq_le n) (by positivity)

lemma summable_shiftFun : Summable fun n => ‖shiftFun f n‖ ^ 2 := by
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_)
    ((summable_sq f).mul_left 2)
  exact shift_sq_bound f n

lemma summable_shiftAdjFun : Summable fun n => ‖shiftAdjFun f n‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (shiftAdj_sq_bound f)
    (((summable_nat_add_iff 1).mpr (summable_sq f)).mul_left 2)

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

/-- `S_N^*` as a linear map. -/
def shiftAdjLin : Ell2 →ₗ[ℂ] Ell2 where
  toFun f := ⟨shiftAdjFun f, memℓp_of_summable_sq (summable_shiftAdjFun f)⟩
  map_add' f g := by
    apply lp.ext; funext n
    change shiftAdjFun (⇑(f + g)) n = shiftAdjFun ⇑f n + shiftAdjFun ⇑g n
    simp [shiftAdjFun, mul_add]
  map_smul' c f := by
    apply lp.ext; funext n
    change shiftAdjFun (⇑(c • f)) n = c • shiftAdjFun ⇑f n
    simp [shiftAdjFun]; ring

lemma shiftLin_norm_le : ‖shiftLin f‖ ≤ Real.sqrt 2 * ‖f‖ := by
  apply lp.norm_le_of_tsum_le  (by simp) (by positivity)
  simp 
  rw [mul_pow, Real.sq_sqrt (by norm_num), ← tsum_sq_eq_norm_sq, ← tsum_mul_left]
  change ∑' n, ‖shiftFun f n‖ ^ 2 ≤ _
  rw [(summable_shiftFun f).tsum_eq_zero_add]
  simp only [shiftFun, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_add]
  calc ∑' n, ‖shiftWeight n * f n‖ ^ 2 ≤ ∑' n, 2 * ‖f n‖ ^ 2 :=
        Summable.tsum_le_tsum (shift_sq_bound f)
          ((summable_nat_add_iff 1).mpr (summable_shiftFun f))
          ((summable_sq f).mul_left 2)
    _ ≤ _ := le_rfl

lemma shiftAdjLin_norm_le : ‖shiftAdjLin f‖ ≤ Real.sqrt 2 * ‖f‖ := by
  apply lp.norm_le_of_tsum_le  (by simp) (by positivity)
  simp 
  rw [mul_pow, Real.sq_sqrt (by norm_num), ← tsum_sq_eq_norm_sq, ← tsum_mul_left]
  calc ∑' n, ‖shiftAdjFun f n‖ ^ 2 ≤ ∑' n, 2 * ‖f (n + 1)‖ ^ 2 :=
        Summable.tsum_le_tsum (shiftAdj_sq_bound f) (summable_shiftAdjFun f)
          (((summable_nat_add_iff 1).mpr (summable_sq f)).mul_left 2)
    _ ≤ ∑' n, 2 * ‖f n‖ ^ 2 := by
      simp [((summable_sq f).mul_left 2).tsum_eq_zero_add]

/-- The weighted shift `S_N`: `S_N e_0 = √2 e_1`, `S_N e_n = e_{n+1}` for `n ≥ 1`. -/
def shiftN : Ell2 →L[ℂ] Ell2 := shiftLin.mkContinuous (Real.sqrt 2) shiftLin_norm_le

/-- The concrete formula for `S_N^*`. -/
def shiftNAdj : Ell2 →L[ℂ] Ell2 := shiftAdjLin.mkContinuous (Real.sqrt 2) shiftAdjLin_norm_le

@[simp] lemma shiftN_apply_zero : shiftN f 0 = 0 := rfl

@[simp] lemma shiftN_apply_succ :
    shiftN f (n + 1) = shiftWeight n * f n := rfl

@[simp] lemma shiftNAdj_apply :
    shiftNAdj f n = shiftWeight n * f (n + 1) := rfl

/-- `shiftNAdj` is the Hilbert-space adjoint of `S_N`. -/
lemma shiftNAdj_eq_adjoint : shiftNAdj = ContinuousLinearMap.adjoint shiftN := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro f g
  have hs : Summable fun i => inner ℂ (f i) (shiftN g i) :=
    lp.summable_inner f (shiftN g)
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, hs.tsum_eq_zero_add]
  simp only [shiftNAdj_apply, shiftN_apply_zero, shiftN_apply_succ,
    RCLike.inner_apply]
  rw [zero_mul, zero_add]
  congr 1; funext n
  rw [map_mul, conj_shiftWeight]; ring

/-- The operator `D_N = 2 P_0 - P_1`, i.e. the diagonal operator with entries
`(2, -1, 0, 0, …)`. -/
def diagN : Ell2 →L[ℂ] Ell2 :=
  (2 : ℂ) • (ContinuousLinearMap.toSpanSingleton ℂ (lp.single 2 0 (1 : ℂ) : Ell2)).comp
      (innerSL ℂ (lp.single 2 0 (1 : ℂ) : Ell2)) -
    (ContinuousLinearMap.toSpanSingleton ℂ (lp.single 2 1 (1 : ℂ) : Ell2)).comp
      (innerSL ℂ (lp.single 2 1 (1 : ℂ) : Ell2))

/-- The diagonal entries of `D_N`. -/
def diagEntry (n : ℕ) : ℂ := if n = 0 then 2 else if n = 1 then -1 else 0

lemma inner_single (k : ℕ) :
    inner ℂ (lp.single 2 k 1) f = f k := by
  simp_all [lp.inner_eq_tsum, tsum_eq_single k]

lemma diagN_apply (f : Ell2) (n : ℕ) :
    diagN f n = diagEntry n * f n := by
  simp only [diagN, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, inner_single,
    lp.coeFn_sub, diagEntry]
  rcases n with _ | _ | n <;> simp

/-- Lemma 4.2: `[S_N^*, S_N] = D_N`. -/
theorem shift_commutator :
    ContinuousLinearMap.adjoint shiftN * shiftN - shiftN * ContinuousLinearMap.adjoint shiftN
      = diagN := by
  rw [← shiftNAdj_eq_adjoint]
  ext1 f
  apply lp.ext; funext n
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, lp.coeFn_sub,
    Pi.sub_apply, diagN_apply]
  rcases n with _ | _ | n
  · simp [shiftWeight_mul_self, diagEntry, ← mul_assoc]
  · simp only [shiftN_apply_succ, shiftNAdj_apply, diagEntry]
    rw [← mul_assoc, ← mul_assoc, shiftWeight_mul_self, shiftWeight_mul_self]; norm_num; ring
  simp [diagEntry, ← mul_assoc, shiftWeight_mul_self]


/-- The standard basis vector `e_n` of `ℓ²(ℕ₀)`. -/
def basisVec (n : ℕ) : Ell2 := lp.single 2 n (1 : ℂ)

end PolyaNeumann

end
