module

public import RequestProject.PlanarTypes

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

instance : ContinuousStar (ComplexEnd Ell2) :=
  @NormedStarGroup.to_continuousStar (ComplexEnd Ell2) _ _ _

instance : StarModule ℝ (ComplexEnd Ell2) :=
  @StarModule.complexToReal (ComplexEnd Ell2) _ _ _ _

instance : IsScalarTower ℝ (ComplexEnd Ell2) (ComplexEnd Ell2) :=
  @IsScalarTower.right ℝ (ComplexEnd Ell2) _ _ _

instance : SMulCommClass ℝ (ComplexEnd Ell2) (ComplexEnd Ell2) :=
  @Algebra.to_smulCommClass ℝ (ComplexEnd Ell2) _ _ _

/-- `r • x = (r : ℂ) • x` for real scalars acting on `ℋ`. -/
lemma real_smul_eq_coe_smul_ell2 (r : ℝ) (x : Ell2) : r • x = (r : ℂ) • x :=
  (Complex.coe_smul r x).symm

/-- `r • A = (r : ℂ) • A` for real scalars acting on `ℋ →L[ℂ] ℋ`. -/
lemma real_smul_eq_coe_smul_clm (r : ℝ) (A : ComplexEnd Ell2) : r • A = (r : ℂ) • A :=
  (Complex.coe_smul r A).symm

/-- The weights of the shift: `w_0 = √2`, `w_n = 1` for `n ≥ 1`. -/
def shiftWeight n  := if n = 0 then (Real.sqrt 2 : ℂ) else 1

lemma conj_shiftWeight n : conj (shiftWeight n) = shiftWeight n := by
  unfold shiftWeight; split_ifs <;> simp

lemma norm_shiftWeight_sq_le n : ‖shiftWeight n‖ ^ 2 ≤ 2 := by
  unfold shiftWeight; split_ifs <;> simp

lemma shiftWeight_mul_self n :
    shiftWeight n * shiftWeight n = if n = 0 then 2 else 1 := by
  unfold shiftWeight; split_ifs
  · rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; simp
  · simp

/-- Coordinates of `S_N f`. -/
def shiftFun (f : ComplexSeq) : ℕ → ℂ
  | 0 => 0
  | n + 1 => shiftWeight n * f n

/-- Coordinates of `S_N^* f`. -/
def shiftAdjFun (f : ComplexSeq)  := fun n => shiftWeight n * f (n + 1)

lemma two_toReal : (2 : ENNReal).toReal = 2 := by simp

section
variable (f : Ell2)

include f in
lemma summable_sq : Summable fun n => ‖(f : ComplexSeq) n‖ ^ 2 := by
  have := (memℓp_gen_iff (p := 2) (by simp)).mp f.2
  simpa  using this

lemma memℓp_of_summable_sq {g : ComplexSeq} (h : Summable fun n => ‖g n‖ ^ 2) :
    Memℓp g 2 := by
  rw [memℓp_gen_iff (by simp)]
  simpa  using h

section
include f

lemma tsum_sq_eq_norm_sq : ∑' n, ‖(f : ComplexSeq) n‖ ^ 2 = ‖f‖ ^ 2 := by
  have := lp.norm_rpow_eq_tsum (p := 2) (by simp) f
  simp_all

lemma shift_sq_bound n :
    ‖shiftWeight n * (f : ComplexSeq) n‖ ^ 2 ≤ 2 * ‖(f : ComplexSeq) n‖ ^ 2 := by
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (norm_shiftWeight_sq_le n) (by positivity)

lemma shiftAdj_sq_bound n :
    ‖shiftWeight n * (f : ComplexSeq) (n + 1)‖ ^ 2 ≤ 2 * ‖(f : ComplexSeq) (n + 1)‖ ^ 2 := by
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (norm_shiftWeight_sq_le n) (by positivity)

lemma summable_shiftFun : Summable fun n => ‖shiftFun f n‖ ^ 2 := by
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_)
    ((summable_sq f).mul_left 2)
  exact shift_sq_bound f n

lemma summable_shiftAdjFun : Summable fun n => ‖shiftAdjFun f n‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun _ => by positivity) ((shiftAdj_sq_bound f))
    (((summable_nat_add_iff 1).mpr (summable_sq f)).mul_left 2)

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

include f in
lemma shiftLin_norm_le : ‖shiftLin f‖ ≤ Real.sqrt 2 * ‖f‖ := by
  apply lp.norm_le_of_tsum_le (p := 2) (by simp) (by positivity)
  simp only [two_toReal, Real.rpow_two]
  rw [mul_pow, Real.sq_sqrt (by norm_num), ← tsum_sq_eq_norm_sq, ← tsum_mul_left]
  change ∑' n, ‖shiftFun f n‖ ^ 2 ≤ _
  rw [(summable_shiftFun f).tsum_eq_zero_add]
  simp only [shiftFun, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_add]
  calc ∑' n, ‖shiftWeight n * f n‖ ^ 2 ≤ ∑' n, 2 * ‖f n‖ ^ 2 :=
        Summable.tsum_le_tsum (fun n => shift_sq_bound f n)
          ((summable_nat_add_iff 1).mpr (summable_shiftFun f))
          ((summable_sq f).mul_left 2)
    _ ≤ _ := le_rfl

include f in
lemma shiftAdjLin_norm_le : ‖shiftAdjLin f‖ ≤ Real.sqrt 2 * ‖f‖ := by
  apply lp.norm_le_of_tsum_le (p := 2) (by simp) (by positivity)
  simp  
  rw [mul_pow, Real.sq_sqrt (by norm_num), ← tsum_sq_eq_norm_sq, ← tsum_mul_left]
  calc ∑' n, ‖shiftAdjFun f n‖ ^ 2 ≤ ∑' n, 2 * ‖f (n + 1)‖ ^ 2 :=
        Summable.tsum_le_tsum ((shiftAdj_sq_bound f)) (summable_shiftAdjFun f)
          (((summable_nat_add_iff 1).mpr (summable_sq f)).mul_left 2)
    _ ≤ ∑' n, 2 * ‖f n‖ ^ 2 := by
      rw [((summable_sq f).mul_left 2).tsum_eq_zero_add]
      bound

/-- The weighted shift `S_N`: `S_N e_0 = √2 e_1`, `S_N e_n = e_{n+1}` for `n ≥ 1`. -/
def shiftN  := shiftLin.mkContinuous (Real.sqrt 2) shiftLin_norm_le

/-- The concrete formula for `S_N^*`. -/
def shiftNAdj  := shiftAdjLin.mkContinuous (Real.sqrt 2) shiftAdjLin_norm_le

section
include f

@[simp] lemma shiftN_apply_zero : (shiftN f : ComplexSeq) 0 = 0 := rfl

@[simp] lemma shiftN_apply_succ n :
    (shiftN f : ComplexSeq) (n + 1) = shiftWeight n * (f : ComplexSeq) n := rfl

@[simp] lemma shiftNAdj_apply n :
    (shiftNAdj f : ComplexSeq) n = shiftWeight n * (f : ComplexSeq) (n + 1) := rfl

end


/-- `shiftNAdj` is the Hilbert-space adjoint of `S_N`. -/
lemma shiftNAdj_eq_adjoint : shiftNAdj = ContinuousLinearMap.adjoint shiftN := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro f g
  have hs : Summable fun i => inner ℂ ((f : ComplexSeq) i) ((shiftN g : ComplexSeq) i) :=
    lp.summable_inner f (shiftN g)
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, hs.tsum_eq_zero_add]
  simp only [shiftNAdj_apply, shiftN_apply_zero, shiftN_apply_succ,
    RCLike.inner_apply]
  grind [conj_shiftWeight, PolyaNeumann.shiftWeight]

/-- The operator `D_N = 2 P_0 - P_1`, i.e. the diagonal operator with entries
`(2, -1, 0, 0, …)`. -/
def diagN : ComplexEnd Ell2 :=
  (2 : ℂ) • (ContinuousLinearMap.toSpanSingleton ℂ (lp.single 2 0 (1 : ℂ) : Ell2)).comp
      (innerSL ℂ (lp.single 2 0 (1 : ℂ) : Ell2)) -
    (ContinuousLinearMap.toSpanSingleton ℂ (lp.single 2 1 (1 : ℂ) : Ell2)).comp
      (innerSL ℂ (lp.single 2 1 (1 : ℂ) : Ell2))

/-- The diagonal entries of `D_N`. -/
def diagEntry (n : ℕ) : ℂ := if n = 0 then 2 else if n = 1 then -1 else 0

include f in
lemma inner_single k :
    inner ℂ (lp.single 2 k (1 : ℂ) : Ell2) f = (f : ComplexSeq) k := by
  rw [lp.inner_eq_tsum, tsum_eq_single k]
  · simp
  simp_all

include f in
lemma diagN_apply n :
    (diagN f : ComplexSeq) n = diagEntry n * (f : ComplexSeq) n := by
  simp only [diagN, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, inner_single, lp.coeFn_sub, diagEntry]
  rcases n with _ | _ | n <;> simp

end


/-- Lemma 4.2: `[S_N^*, S_N] = D_N`. -/
theorem shift_commutator :
    ContinuousLinearMap.adjoint shiftN * shiftN - shiftN * ContinuousLinearMap.adjoint shiftN
      = diagN := by
  rw [← shiftNAdj_eq_adjoint]
  ext1 f
  apply lp.ext; funext n
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, lp.coeFn_sub, Pi.sub_apply, diagN_apply]
  rcases n with _ | _ | n
  · simp [shiftWeight_mul_self, diagEntry, ← mul_assoc]
  · grind only [shiftN_apply_succ, shiftNAdj_apply, diagEntry, shiftWeight_mul_self]
  · grind only [shiftN_apply_succ, shiftNAdj_apply, diagEntry, shiftWeight_mul_self]



/-- The standard basis vector `e_n` of `ℓ²(ℕ₀)`. -/
def basisVec (n : ℕ) : Ell2 := lp.single 2 n (1 : ℂ)

end PolyaNeumann

end
