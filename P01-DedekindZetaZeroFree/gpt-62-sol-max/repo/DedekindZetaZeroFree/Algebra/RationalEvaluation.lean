module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Complex.Basic

/-! Arithmetic of rational functions evaluated away from their poles. -/

@[expose] public section

namespace DedekindZetaZeroFree.RationalEvaluation

section Specialization

universe u

/-- Evaluation (also allowing a change of coefficient field) with a nonzero denominator. -/
def Evaluates₂ {K L : Type u} [Field K] [Field L] (f : K →+* L) (a : L) (x : RatFunc K) (b : L) : Prop :=
  Polynomial.eval₂ f a x.denom ≠ 0 ∧ RatFunc.eval f a x = b
variable {K L : Type u} [Field K] [Field L] {f : K →+* L} {a : L}
lemma Evaluates₂.const (c : K) : Evaluates₂ f a (RatFunc.C c) (f c) := by
  simp [Evaluates₂]
lemma Evaluates₂.var : Evaluates₂ f a (RatFunc.X : RatFunc K) a := by
  simp [Evaluates₂]
lemma Evaluates₂.mul {x y : RatFunc K} {b c : L} (hx : Evaluates₂ f a x b) (hy : Evaluates₂ f a y c) :
    Evaluates₂ f a (x*y) (b*c) := by
  refine ⟨?_, by rw [RatFunc.eval_mul f a hx.1 hy.1, hx.2, hy.2]⟩
  intro h
  have h' := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero f a (RatFunc.denom_mul_dvd x y) h
  rw [Polynomial.eval₂_mul] at h'
  exact (mul_ne_zero hx.1 hy.1) h'
lemma Evaluates₂.add {x y : RatFunc K} {b c : L} (hx : Evaluates₂ f a x b) (hy : Evaluates₂ f a y c) :
    Evaluates₂ f a (x+y) (b+c) := by
  refine ⟨?_, by rw [RatFunc.eval_add f a hx.1 hy.1, hx.2, hy.2]⟩
  intro h
  have h' := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero f a (RatFunc.denom_add_dvd x y) h
  rw [Polynomial.eval₂_mul] at h'
  exact (mul_ne_zero hx.1 hy.1) h'
lemma Evaluates₂.neg {x : RatFunc K} {b : L} (hx : Evaluates₂ f a x b) : Evaluates₂ f a (-x) (-b) := by
  simpa using Evaluates₂.mul (Evaluates₂.const (f := f) (a := a) (-1)) hx
lemma Evaluates₂.sub {x y : RatFunc K} {b c : L} (hx : Evaluates₂ f a x b) (hy : Evaluates₂ f a y c) :
    Evaluates₂ f a (x-y) (b-c) := by
  simpa [sub_eq_add_neg] using Evaluates₂.add hx (Evaluates₂.neg hy)
lemma Evaluates₂.one : Evaluates₂ f a (1 : RatFunc K) 1 := by
  simpa using Evaluates₂.const (f := f) (a := a) 1
lemma Evaluates₂.zero : Evaluates₂ f a (0 : RatFunc K) 0 := by
  simpa using Evaluates₂.const (f := f) (a := a) 0
lemma Evaluates₂.inv {x : RatFunc K} {b : L} (hx : Evaluates₂ f a x b) (hb : b ≠ 0) :
    Evaluates₂ f a x⁻¹ b⁻¹ := by
  have hnum : Polynomial.eval₂ f a x.num ≠ 0 := by
    intro h
    have : b = 0 := by rw [← hx.2, RatFunc.eval, h, zero_div]
    exact hb this
  have hxn : x ≠ 0 := by
    intro h; subst x; simpa using hnum
  have hi : Polynomial.eval₂ f a x⁻¹.denom ≠ 0 := by
    intro h
    exact hnum (Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero f a (RatFunc.denom_inv_dvd hxn) h)
  refine ⟨hi, ?_⟩
  have hm := Evaluates₂.mul hx (show Evaluates₂ f a x⁻¹ (RatFunc.eval f a x⁻¹) from ⟨hi, rfl⟩)
  have he : b * RatFunc.eval f a x⁻¹ = 1 := by
    rw [← hm.2, mul_inv_cancel₀ hxn, RatFunc.eval_one]
  apply (mul_left_cancel₀ hb)
  rw [he, mul_inv_cancel₀ hb]
lemma Evaluates₂.div {x y : RatFunc K} {b c : L} (hx : Evaluates₂ f a x b) (hy : Evaluates₂ f a y c) (hc : c ≠ 0) :
    Evaluates₂ f a (x/y) (b/c) := by
  simpa [div_eq_mul_inv] using Evaluates₂.mul hx (Evaluates₂.inv hy hc)
lemma Evaluates₂.pow {x : RatFunc K} {b : L} (hx : Evaluates₂ f a x b) (n : ℕ) :
    Evaluates₂ f a (x^n) (b^n) := by
  induction n with
  | zero => simpa using (Evaluates₂.one (f := f) (a := a))
  | succ n hn => simpa [pow_succ] using Evaluates₂.mul hn hx
lemma Evaluates₂.zpow {x : RatFunc K} {b : L} (hx : Evaluates₂ f a x b) (hb : b ≠ 0) (n : ℤ) :
    Evaluates₂ f a (x^n) (b^n) := by
  cases n with
  | ofNat n => simpa using Evaluates₂.pow hx n
  | negSucc n => simpa [zpow_negSucc] using Evaluates₂.inv (Evaluates₂.pow hx (n+1)) (pow_ne_zero _ hb)
lemma Evaluates₂.sum {ι : Type*} (s : Finset ι) {x : ι → RatFunc K} {b : ι → L}
    (h : ∀ i ∈ s, Evaluates₂ f a (x i) (b i)) : Evaluates₂ f a (∑ i ∈ s, x i) (∑ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Evaluates₂.zero (f := f) (a := a))
  | @insert i s hi hs =>
    simp only [Finset.sum_insert hi]
    exact Evaluates₂.add (h i (Finset.mem_insert_self _ _)) (hs fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma Evaluates₂.ne_zero {x : RatFunc K} {b : L}
    (hx : Evaluates₂ f a x b) (hb : b ≠ 0) : x ≠ 0 := by
  intro h
  exact hb (by simpa [h] using hx.2.symm)

end Specialization

variable {K : Type*} [Field K]

/-- The evaluation point is not a pole. -/
def Regular (a : K) (x : RatFunc K) : Prop := x.denom.eval a ≠ 0

abbrev Evaluates (a : K) := Evaluates₂ (RingHom.id K) a

namespace Evaluates

variable {u a b : K} {r s : RatFunc K}

lemma const (a b : K) : Evaluates a (RatFunc.C b) b := Evaluates₂.const b
lemma var (a : K) : Evaluates a RatFunc.X a := Evaluates₂.var
lemma add (hr : Evaluates u r a) (hs : Evaluates u s b) : Evaluates u (r + s) (a + b) :=
  Evaluates₂.add hr hs
lemma mul (hr : Evaluates u r a) (hs : Evaluates u s b) : Evaluates u (r * s) (a * b) :=
  Evaluates₂.mul hr hs
lemma neg (hr : Evaluates u r a) : Evaluates u (-r) (-a) := Evaluates₂.neg hr
lemma sub (hr : Evaluates u r a) (hs : Evaluates u s b) : Evaluates u (r - s) (a - b) :=
  Evaluates₂.sub hr hs
lemma inv (hr : Evaluates u r a) (ha : a ≠ 0) : Evaluates u r⁻¹ a⁻¹ := Evaluates₂.inv hr ha
lemma div (hr : Evaluates u r a) (hs : Evaluates u s b) (hb : b ≠ 0) : Evaluates u (r / s) (a / b) :=
  Evaluates₂.div hr hs hb
lemma pow (hr : Evaluates u r a) (n : ℕ) : Evaluates u (r ^ n) (a ^ n) := Evaluates₂.pow hr n
lemma zpow (hr : Evaluates u r a) (ha : a ≠ 0) (n : ℤ) : Evaluates u (r ^ n) (a ^ n) :=
  Evaluates₂.zpow hr ha n
lemma sum {ι : Type*} (s : Finset ι) {r : ι → RatFunc K} {a : ι → K}
    (h : ∀ i ∈ s, Evaluates u (r i) (a i)) : Evaluates u (∑ i ∈ s, r i) (∑ i ∈ s, a i) :=
  Evaluates₂.sum s h
lemma ne_zero (hr : Evaluates u r a) (ha : a ≠ 0) : r ≠ 0 := Evaluates₂.ne_zero hr ha

end Evaluates

variable {a : K} {x y : RatFunc K}

lemma at_regular (hx : Regular a x) : Evaluates a x (RatFunc.eval (RingHom.id K) a x) :=
  ⟨hx, rfl⟩

lemma regular_C (a b : K) : Regular a (RatFunc.C b) := (Evaluates.const a b).1
lemma regular_X (a : K) : Regular a RatFunc.X := (Evaluates.var a).1
lemma regular_zero (a : K) : Regular a 0 := Evaluates₂.zero (f := RingHom.id K) (a := a) |>.1
lemma regular_add (hx : Regular a x) (hy : Regular a y) : Regular a (x + y) :=
  (Evaluates.add (at_regular hx) (at_regular hy)).1
lemma regular_mul (hx : Regular a x) (hy : Regular a y) : Regular a (x * y) :=
  (Evaluates.mul (at_regular hx) (at_regular hy)).1
lemma eval_mul (hx : Regular a x) (hy : Regular a y) :
    RatFunc.eval (RingHom.id K) a (x * y) = RatFunc.eval (RingHom.id K) a x * RatFunc.eval (RingHom.id K) a y :=
  RatFunc.eval_mul _ _ hx hy
theorem eq_of_regular_infinite (R S : RatFunc K) (u : Set K) (hu : u.Infinite)
    (he : ∀ a ∈ u, R.denom.eval a ≠ 0 ∧ S.denom.eval a ≠ 0 ∧
      RatFunc.eval (RingHom.id K) a R = RatFunc.eval (RingHom.id K) a S) : R = S := by
  have hp : R.num * S.denom = S.num * R.denom := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply hu.mono
    intro a ha
    obtain ⟨hR,hS,h⟩ := he a ha
    simp only [RatFunc.eval, Polynomial.eval₂_id] at h
    change Polynomial.eval a (R.num * S.denom) = Polynomial.eval a (S.num * R.denom)
    simpa only [Polynomial.eval_mul] using (div_eq_div_iff hR hS).mp h
  have hh := (RatFunc.num_mul_eq_mul_denom_iff (RatFunc.denom_ne_zero S)).mp hp
  rwa [RatFunc.num_div_denom] at hh


private lemma eval_smul (c : ℂ) {R : RatFunc ℂ} {w : ℂ} (hR : Regular w R) :
    Evaluates w (c • R) (c * RatFunc.eval (RingHom.id ℂ) w R) := by
  simpa only [Algebra.smul_def, RatFunc.algebraMap_eq_C] using
    (Evaluates.const w c).mul (at_regular hR)

theorem rational_sum_scalar {ι V : Type*} [AddCommMonoid V] [Module ℂ V]
    (s : Finset ι) (a : ι → RatFunc ℂ) (M : ι → Module.End ℂ V) (c : RatFunc ℂ)
    (U : Set ℂ) (hU : U.Infinite)
    (ha : ∀ w ∈ U, ∀ i ∈ s, (a i).denom.eval w ≠ 0)
    (hc : ∀ w ∈ U, c.denom.eval w ≠ 0)
    (hn : ∀ w ∈ U, (∑ i ∈ s, RatFunc.eval (RingHom.id ℂ) w (a i) • M i) =
      RatFunc.eval (RingHom.id ℂ) w c • LinearMap.id) :
    (∑ i ∈ s, a i • (M i).baseChange (RatFunc ℂ)) = c • LinearMap.id := by
  classical
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℂ
  let b := Module.Free.chooseBasis ℂ V
  let e := TensorProduct.equivFinsuppOfBasisRight (M := RatFunc ℂ) b
  apply TensorProduct.AlgebraTensorModule.ext
  intro f v
  suffices h : (∑ i ∈ s, a i • (M i).baseChange (RatFunc ℂ)) (1 ⊗ₜ[ℂ] v) =
      (c • LinearMap.id) (1 ⊗ₜ[ℂ] v) by
    calc
      _ = f • (∑ i ∈ s, a i • (M i).baseChange (RatFunc ℂ)) (1 ⊗ₜ[ℂ] v) := by
        rw [← map_smul,TensorProduct.smul_tmul',smul_eq_mul,mul_one]
      _ = f • (c • LinearMap.id) (1 ⊗ₜ[ℂ] v) := congrArg (fun x => f • x) h
      _ = _ := by rw [← map_smul,TensorProduct.smul_tmul',smul_eq_mul,mul_one]
  apply e.injective
  ext j
  change (e ((∑ i ∈ s, a i • (M i).baseChange (RatFunc ℂ)) (1 ⊗ₜ[ℂ] v))) j =
    (e ((c • LinearMap.id) (1 ⊗ₜ[ℂ] v))) j
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.baseChange_tmul,
    TensorProduct.smul_tmul', smul_eq_mul,mul_one, map_sum, LinearMap.id_apply,
    Finsupp.finsetSum_apply]
  dsimp only [e]
  simp only [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  apply eq_of_regular_infinite _ _ U hU
  intro w hw
  have hs := Evaluates.sum s (fun i hi => eval_smul ((b.repr (M i v)) j) (ha w hw i hi))
  have ht := eval_smul ((b.repr v) j) (hc w hw)
  refine ⟨hs.1, ht.1, ?_⟩
  rw [hs.2, ht.2]
  have hh := congrArg (fun L : Module.End ℂ V => (b.repr (L v)) j) (hn w hw)
  simpa only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.id_apply,map_sum,map_smul,
    Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul,mul_comm] using hh

private lemma product_regular (a b : RatFunc ℂ) (w : ℂ)
    (ha : Regular w a) (hb : Regular w b) : Regular w (a * b) := regular_mul ha hb

theorem rational_rectangular_composition {ι κ V W : Type*}
    [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]
    (s : Finset ι) (t : Finset κ) (a : ι → RatFunc ℂ) (b : κ → RatFunc ℂ)
    (A : ι → V →ₗ[ℂ] W) (B : κ → W →ₗ[ℂ] V) (c : RatFunc ℂ)
    (U : Set ℂ) (hU : U.Infinite)
    (ha : ∀ w ∈ U, ∀ i ∈ s, (a i).denom.eval w ≠ 0)
    (hb : ∀ w ∈ U, ∀ j ∈ t, (b j).denom.eval w ≠ 0)
    (hc : ∀ w ∈ U, c.denom.eval w ≠ 0)
    (hn : ∀ w ∈ U,
      (∑ j ∈ t, RatFunc.eval (RingHom.id ℂ) w (b j) • B j).comp
        (∑ i ∈ s, RatFunc.eval (RingHom.id ℂ) w (a i) • A i) =
      RatFunc.eval (RingHom.id ℂ) w c • LinearMap.id) :
    (∑ j ∈ t, b j • (B j).baseChange (RatFunc ℂ)).comp
      (∑ i ∈ s, a i • (A i).baseChange (RatFunc ℂ)) = c • LinearMap.id := by
  classical
  have hh := rational_sum_scalar (t ×ˢ s) (fun ji => b ji.1 * a ji.2)
    (fun ji => (B ji.1).comp (A ji.2)) c U hU
    (fun w hw ji hji => product_regular _ _ w
      (hb w hw ji.1 (Finset.mem_product.mp hji).1)
      (ha w hw ji.2 (Finset.mem_product.mp hji).2)) hc ?_
  · apply LinearMap.ext
    intro v
    have hhv := LinearMap.congr_fun hh v
    simp only [Finset.sum_product,LinearMap.comp_apply,LinearMap.sum_apply,
      LinearMap.smul_apply,LinearMap.id_apply,map_sum,map_smul,Finset.smul_sum,
      smul_smul,LinearMap.baseChange_comp] at hhv ⊢
    rw [Finset.sum_comm]
    simpa only [mul_comm] using hhv
  · intro w hw
    have he (ji : κ × ι) (hji : ji ∈ t ×ˢ s) :
        RatFunc.eval (RingHom.id ℂ) w (b ji.1 * a ji.2) =
          RatFunc.eval (RingHom.id ℂ) w (b ji.1) * RatFunc.eval (RingHom.id ℂ) w (a ji.2) :=
      RatFunc.eval_mul _ _ (hb w hw ji.1 (Finset.mem_product.mp hji).1)
        (ha w hw ji.2 (Finset.mem_product.mp hji).2)
    rw [Finset.sum_congr rfl (fun ji hji => congrArg (fun z => z • ((B ji.1).comp (A ji.2))) (he ji hji))]
    apply LinearMap.ext
    intro v
    have hhv := LinearMap.congr_fun (hn w hw) v
    simp only [Finset.sum_product,LinearMap.comp_apply,LinearMap.sum_apply,
      LinearMap.smul_apply,LinearMap.id_apply,map_sum,map_smul,Finset.smul_sum,
      smul_smul] at hhv ⊢
    rw [Finset.sum_comm]
    simpa only [mul_comm] using hhv

end DedekindZetaZeroFree.RationalEvaluation
