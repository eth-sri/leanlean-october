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

/-- Operators and operator paths on the boundary sequence space. -/
scoped notation "vacuumWeight" => (Real.sqrt 2 : ℂ)
scoped notation "ShiftOp" => Ell2 →L[ℂ] Ell2
scoped notation "TransportPath" => ℝ → ShiftOp

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

instance : ContinuousStar ShiftOp :=
  @NormedStarGroup.to_continuousStar ShiftOp _ _ _

instance : StarModule ℝ ShiftOp :=
  @StarModule.complexToReal ShiftOp _ _ _ _

section

variable (r : ℝ) (n : ℕ) (f : ℕ → ℂ)

/-- `r • x = (r : ℂ) • x` for real scalars acting on `ℋ`. -/
lemma real_smul_eq_coe_smul_ell2 (x : Ell2) : r • x = (r : ℂ) • x :=
  (Complex.coe_smul r x).symm

/-- `r • A = (r : ℂ) • A` for real scalars acting on `ℋ →L[ℂ] ℋ`. -/
lemma real_smul_eq_coe_smul_clm (A : ShiftOp) : r • A = (r : ℂ) • A :=
  (Complex.coe_smul r A).symm

include n in
/-- The weights of the shift: `w_0 = √2`, `w_n = 1` for `n ≥ 1`. -/
def shiftWeight : ℂ := if n = 0 then (Real.sqrt 2 : ℂ) else 1

lemma conj_shiftWeight : conj (shiftWeight n) = shiftWeight n := by
  unfold shiftWeight; split_ifs <;> simp

lemma norm_shiftWeight_sq_le : ‖shiftWeight n‖ ^ 2 ≤ 2 := by
  unfold shiftWeight; split_ifs <;> simp

lemma shiftWeight_mul_self :
    shiftWeight n * shiftWeight n = if n = 0 then 2 else 1 := by
  unfold shiftWeight; split_ifs
  · rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; simp
  · simp

include f in
/-- Coordinates of `S_N f`. -/
def shiftFun : ℕ → ℂ
  | 0 => 0
  | n + 1 => shiftWeight n * f n

include f in
/-- Coordinates of `S_N^* f`. -/
def shiftAdjFun : ℕ → ℂ := fun n => shiftWeight n * f (n + 1)

end

section

variable (f : Ell2) (n : ℕ)

lemma two_toReal : (2 : ENNReal).toReal = 2 := by simp

lemma summable_sq : Summable fun n => ‖(f : ℕ → ℂ) n‖ ^ 2 := by
  have := (memℓp_gen_iff (p := 2) (by simp)).mp f.2
  simpa using this

lemma memℓp_of_summable_sq {g : ℕ → ℂ} (h : Summable fun n => ‖g n‖ ^ 2) :
    Memℓp g 2 := by
  rw [memℓp_gen_iff (by simp)]
  simpa using h

lemma tsum_sq_eq_norm_sq : ∑' n, ‖(f : ℕ → ℂ) n‖ ^ 2 = ‖f‖ ^ 2 := by
  have := lp.norm_rpow_eq_tsum  (by simp) f
  simp at this
  exact this.symm

lemma shift_sq_bound :
    ‖shiftWeight n * (f : ℕ → ℂ) n‖ ^ 2 ≤ 2 * ‖(f : ℕ → ℂ) n‖ ^ 2 := by
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (norm_shiftWeight_sq_le n) (by positivity)

lemma shiftAdj_sq_bound :
    ‖shiftWeight n * (f : ℕ → ℂ) (n + 1)‖ ^ 2 ≤ 2 * ‖(f : ℕ → ℂ) (n + 1)‖ ^ 2 := by
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
    
    simp [shiftAdjFun]; ring

lemma shiftLin_norm_le : ‖shiftLin f‖ ≤ Real.sqrt 2 * ‖f‖ := by
  apply lp.norm_le_of_tsum_le (p := 2) (by simp) (by positivity)
  simp
  rw [mul_pow, Real.sq_sqrt (by norm_num), ← tsum_sq_eq_norm_sq, ← tsum_mul_left]
  change ∑' n, ‖shiftFun f n‖ ^ 2 ≤ _
  rw [(summable_shiftFun f).tsum_eq_zero_add]
  simp only [shiftFun, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_add]
  calc _ ≤ _ :=
        Summable.tsum_le_tsum (shift_sq_bound f)
          ((summable_nat_add_iff 1).mpr (summable_shiftFun f))
          ((summable_sq f).mul_left 2)
    _ ≤ _ := le_rfl

lemma shiftAdjLin_norm_le : ‖shiftAdjLin f‖ ≤ Real.sqrt 2 * ‖f‖ := by
  apply lp.norm_le_of_tsum_le (p := 2) (by simp) (by positivity)
  simp
  rw [mul_pow, Real.sq_sqrt (by norm_num), ← tsum_sq_eq_norm_sq, ← tsum_mul_left]
  
  calc _ ≤ _ :=
        Summable.tsum_le_tsum (shiftAdj_sq_bound f) (summable_shiftAdjFun f)
          (((summable_nat_add_iff 1).mpr (summable_sq f)).mul_left 2)
    _ ≤ _ := by
      rw [((summable_sq f).mul_left 2).tsum_eq_zero_add]
      simp

/-- The weighted shift `S_N`: `S_N e_0 = √2 e_1`, `S_N e_n = e_{n+1}` for `n ≥ 1`. -/
def shiftN : ShiftOp := shiftLin.mkContinuous (Real.sqrt 2) shiftLin_norm_le

/-- The concrete formula for `S_N^*`. -/
def shiftNAdj : ShiftOp := shiftAdjLin.mkContinuous (Real.sqrt 2) shiftAdjLin_norm_le

@[simp] lemma shiftN_apply_zero : (shiftN f : ℕ → ℂ) 0 = 0 := rfl

@[simp] lemma shiftN_apply_succ :
    (shiftN f : ℕ → ℂ) (n + 1) = shiftWeight n * (f : ℕ → ℂ) n := rfl

@[simp] lemma shiftNAdj_apply :
    (shiftNAdj f : ℕ → ℂ) n = shiftWeight n * (f : ℕ → ℂ) (n + 1) := rfl

/-- `shiftNAdj` is the Hilbert-space adjoint of `S_N`. -/
lemma shiftNAdj_eq_adjoint : shiftNAdj = ContinuousLinearMap.adjoint shiftN := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro f g
  have hs : Summable fun i => inner ℂ (f i) ((shiftN g) i) :=
    lp.summable_inner f (shiftN g)
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, hs.tsum_eq_zero_add]
  simp only [shiftNAdj_apply, shiftN_apply_zero, shiftN_apply_succ,
    RCLike.inner_apply]
  rw [zero_mul, zero_add]
  congr 1; funext n
  rw [map_mul, conj_shiftWeight]; ring

/-- The operator `D_N = 2 P_0 - P_1`, i.e. the diagonal operator with entries
`(2, -1, 0, 0, …)`. -/
def diagN : ShiftOp :=
  (2 : ℂ) • (ContinuousLinearMap.toSpanSingleton ℂ (lp.single 2 0 (1 : ℂ) : Ell2)).comp
      (innerSL ℂ (lp.single 2 0 (1 : ℂ) : Ell2)) -
    (ContinuousLinearMap.toSpanSingleton ℂ (lp.single 2 1 (1 : ℂ) : Ell2)).comp
      (innerSL ℂ (lp.single 2 1 (1 : ℂ) : Ell2))

include n in
/-- The diagonal entries of `D_N`. -/
def diagEntry : ℂ := if n = 0 then 2 else if n = 1 then -1 else 0

lemma inner_single (k : ℕ) :
    inner ℂ (lp.single 2 k (1 : ℂ) : Ell2) f = (f : ℕ → ℂ) k := by
  rw [lp.inner_eq_tsum, tsum_eq_single k]
  · simp
  · intro b hb; simp [hb]

lemma diagN_apply :
    (diagN f : ℕ → ℂ) n = diagEntry n * (f : ℕ → ℂ) n := by
  simp only [diagN, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, inner_single,
    ContinuousLinearMap.toSpanSingleton_apply, lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply,
    Pi.smul_apply, lp.single_apply, diagEntry]
  aesop

/-- Lemma 4.2: `[S_N^*, S_N] = D_N`. -/
theorem shift_commutator :
    ContinuousLinearMap.adjoint shiftN * shiftN - shiftN * ContinuousLinearMap.adjoint shiftN
      = diagN := by
  rw [← shiftNAdj_eq_adjoint]
  ext1 f
  apply lp.ext; funext n
  simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, lp.coeFn_sub, Pi.sub_apply, diagN_apply, shiftNAdj_apply, shiftN_apply_succ]
  rcases n with _ | _ | n
  · simp [shiftWeight_mul_self, diagEntry, ← mul_assoc]
  · simp only [shiftN_apply_succ, shiftNAdj_apply, diagEntry]
    rw [← mul_assoc, ← mul_assoc, shiftWeight_mul_self, shiftWeight_mul_self]; norm_num; ring
  · simp only [shiftN_apply_succ, shiftNAdj_apply, diagEntry]
    rw [← mul_assoc, ← mul_assoc, shiftWeight_mul_self, shiftWeight_mul_self]; simp

include n in
/-- The standard basis vector `e_n` of `ℓ²(ℕ₀)`. -/
def basisVec : Ell2 := lp.single 2 n (1 : ℂ)

end

end PolyaNeumann

end
