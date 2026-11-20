module

public import Mathlib

@[expose] public section

section

namespace DedekindZetaZeroFree

noncomputable section
open scoped BigOperators
open MeasureTheory

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) := inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
def shiftDiff {d : Type*} [Fintype d] (f : C(UnitAddTorus d, ℂ)) (a : d → ℝ) : C(UnitAddTorus d, ℂ) :=
  ⟨fun t => f (t + fun i => (a i : UnitAddCircle)) - f t, by fun_prop⟩
private lemma diff_bounds {d : Type*} [Fintype d] (f : C(UnitAddTorus d, ℂ)) (a : d → ℝ) (N : ℕ) (C : ℝ)
    (hf : ContDiff ℝ (N + 1 : ℕ) (fun x : d → ℝ => f (fun i => (x i : UnitAddCircle))))
    (hb : ∀ k ≤ N+1, ∀ x : d → ℝ, ‖iteratedFDeriv ℝ k (fun y : d → ℝ => f (fun i => (y i : UnitAddCircle))) x‖ ≤ C) :
    ContDiff ℝ (N : ℕ) (fun x : d → ℝ => shiftDiff f a (fun i => (x i : UnitAddCircle))) ∧
    (∀ k ≤ N, ∀ x : d → ℝ, ‖iteratedFDeriv ℝ k (fun y : d → ℝ => shiftDiff f a (fun i => (y i : UnitAddCircle))) x‖ ≤ C * ‖a‖) := by
  let F := fun x : d → ℝ => f (fun i => (x i : UnitAddCircle))
  have heq : (fun x : d → ℝ => shiftDiff f a (fun i => (x i : UnitAddCircle))) = (fun x => F (x+a)) - F := by
    funext x
    change f (fun i => (x i : UnitAddCircle) + (a i : UnitAddCircle)) - _ = _
    simp [F, AddCircle.coe_add, Pi.add_apply]
  have ht : ContDiff ℝ (N+1 : ℕ) (fun x => F (x+a)) := hf.comp (contDiff_id.add contDiff_const)
  rw [heq]
  constructor
  · exact (ht.sub hf).of_le (by exact_mod_cast Nat.le_succ N)
  intro k hk x
  rw [iteratedFDeriv_sub (ht.of_le (by exact_mod_cast (show k ≤ N+1 by omega))) (hf.of_le (by exact_mod_cast (show k ≤ N+1 by omega)))]
  simp only [Pi.sub_apply, iteratedFDeriv_comp_add_right]
  have hh := (convex_univ : Convex ℝ (Set.univ : Set (d → ℝ))).norm_image_sub_le_of_norm_fderiv_le
    (𝕜 := ℝ) (f := iteratedFDeriv ℝ k F) (C := C)
    (fun y _ => (hf.differentiable_iteratedFDeriv (by exact_mod_cast (show k < N+1 by omega))).differentiableAt)
    (fun y _ => by rw [norm_fderiv_iteratedFDeriv]; exact hb (k+1) (by omega) y)
    (Set.mem_univ x) (Set.mem_univ (x+a))
  simpa only [add_sub_cancel_left] using hh
variable {d : Type*} [Fintype d]

private lemma fourier_shift [DecidableEq d]
    (n : d → ℤ) (i : d) (hi : n i ≠ 0) (t : UnitAddTorus d) :
    UnitAddTorus.mFourier (-n) (t + fun j => (((Pi.single i (1 / 2 / (-(n i) : ℝ)) : d → ℝ) j : ℝ) : UnitAddCircle)) = - UnitAddTorus.mFourier (-n) t := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply, Pi.add_apply]
  have h : ∀ j ∈ Finset.univ, fourier (-(n j)) (t j + (((Pi.single i (1 / 2 / (-(n i) : ℝ)) : d → ℝ) j) : UnitAddCircle)) =
      if j = i then -fourier (-(n j)) (t j) else fourier (-(n j)) (t j) := by
    intro j hj
    split_ifs with hji
    · subst j
      rw [Pi.single_eq_same]
      simpa using fourier_add_half_inv_index (neg_ne_zero.mpr hi) (by norm_num : (0:ℝ)<1) (t i)
    · simp [Pi.single_eq_of_ne hji, hji]
  rw [Finset.prod_congr rfl h]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), ← Finset.mul_prod_erase Finset.univ (fun j => fourier (-(n j)) (t j)) (Finset.mem_univ i)]
  simp only [ite_true, neg_mul]
  congr 1
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [if_neg (Finset.ne_of_mem_erase hj)]
private lemma coeff_diff [DecidableEq d]
    (f : C(UnitAddTorus d, ℂ)) (n : d → ℤ) (i : d) (hi : n i ≠ 0) :
    ‖UnitAddTorus.mFourierCoeff f n‖ ≤ ‖UnitAddTorus.mFourierCoeff (shiftDiff f (Pi.single i (1/2/(-(n i) : ℝ)))) n‖ := by
  let a : d → ℝ := Pi.single i (1/2/(-(n i) : ℝ))
  let z := fun j => (a j : UnitAddCircle)
  have hInt (g : C(UnitAddTorus d, ℂ)) : Integrable (fun t => UnitAddTorus.mFourier (-n) t * g t) :=
    (by fun_prop : Continuous (fun t => UnitAddTorus.mFourier (-n) t * g t)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hshift : (∫ t, UnitAddTorus.mFourier (-n) t * f (t+z)) = - UnitAddTorus.mFourierCoeff f n := by
    have h := integral_add_right_eq_self (μ := volume) (fun t => UnitAddTorus.mFourier (-n) t * f t) z
    change (∫ t, UnitAddTorus.mFourier (-n) (t + fun j => ((Pi.single i (1/2/(-(n i) : ℝ)) : d → ℝ) j : UnitAddCircle)) * f (t+z)) = _ at h
    simp only [fourier_shift n i hi, neg_mul, integral_neg, UnitAddTorus.mFourierCoeff, smul_eq_mul] at h ⊢
    linear_combination -h
  have hcoef : UnitAddTorus.mFourierCoeff (shiftDiff f a) n = -2 * UnitAddTorus.mFourierCoeff f n := by
    simp only [UnitAddTorus.mFourierCoeff, smul_eq_mul, shiftDiff, ContinuousMap.coe_mk, mul_sub]
    have h1 : Integrable (fun t => UnitAddTorus.mFourier (-n) t * f (t+z)) := hInt ⟨fun t => f (t+z), by fun_prop⟩
    rw [integral_sub h1 (hInt f), hshift]
    simp only [UnitAddTorus.mFourierCoeff, smul_eq_mul]
    ring
  rw [hcoef, norm_mul]
  norm_num
  linarith [norm_nonneg (UnitAddTorus.mFourierCoeff f n)]
private lemma shift_norm_le [DecidableEq d]
    (n : d → ℤ) (i : d) (hi : n i ≠ 0) :
    ‖(Pi.single i (1/2/(-(n i) : ℝ)) : d → ℝ)‖ ≤ (max 1 |(n i : ℝ)|)⁻¹ := by
  have hab : 1 ≤ |(n i : ℝ)| := by exact_mod_cast (show (1 : ℤ) ≤ |n i| by cases lt_or_gt_of_ne hi with | inl h => rw [abs_of_neg h]; omega | inr h => rw [abs_of_pos h]; omega)
  rw [max_eq_right hab, Pi.norm_single, norm_div, Real.norm_eq_abs, norm_neg, Real.norm_eq_abs]
  norm_num
  rw [div_eq_mul_inv]
  nlinarith [inv_nonneg.mpr (abs_nonneg (n i : ℝ))]
private lemma coeff_bound (f : C(UnitAddTorus d, ℂ)) (n : d → ℤ) (C : ℝ)
    (hb : ∀ x : d → ℝ, ‖f (fun i => (x i : UnitAddCircle))‖ ≤ C) :
    ‖UnitAddTorus.mFourierCoeff f n‖ ≤ C := by
  have ht : ∀ t : UnitAddTorus d, ‖f t‖ ≤ C := by
    intro t
    choose x hx using (fun i => QuotientAddGroup.mk_surjective (t i))
    simpa only [hx] using hb x
  have hm : ∀ t : UnitAddTorus d, ‖UnitAddTorus.mFourier (-n) t‖ = 1 := by
    intro t
    simp [UnitAddTorus.mFourier, norm_prod, fourier_apply, Circle.norm_coe]
  simpa only [UnitAddTorus.mFourierCoeff, smul_eq_mul, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := (volume : Measure (UnitAddTorus d)))
      (Filter.Eventually.of_forall (fun t => by simpa only [norm_mul, hm t, one_mul] using ht t))
private lemma coeff_list [DecidableEq d]
    (l : List d) (f : C(UnitAddTorus d, ℂ)) (C : ℝ) (hC : 0 ≤ C)
    (hf : ContDiff ℝ (l.length : ℕ) (fun x : d → ℝ => f (fun i => (x i : UnitAddCircle))))
    (hb : ∀ k ≤ l.length, ∀ x : d → ℝ, ‖iteratedFDeriv ℝ k (fun y : d → ℝ => f (fun i => (y i : UnitAddCircle))) x‖ ≤ C)
    (n : d → ℤ) :
    ‖UnitAddTorus.mFourierCoeff f n‖ ≤ C * (l.map (fun i => (max 1 |(n i : ℝ)|)⁻¹)).prod := by
  induction l generalizing f C with
  | nil =>
    simp only [List.map_nil, List.prod_nil, mul_one]
    exact coeff_bound f n C (fun x => by simpa using hb 0 (by simp) x)
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    by_cases hi : n i = 0
    · simp only [hi, Int.cast_zero, abs_zero, max_eq_left zero_le_one, inv_one, one_mul]
      exact ih f C hC (hf.of_le (by simp only [List.length_cons]; exact_mod_cast Nat.le_succ l.length))
        (fun k hk x => hb k (by simp only [List.length_cons]; omega) x)
    · let a : d → ℝ := Pi.single i (1/2/(-(n i) : ℝ))
      obtain ⟨hfd, hbd⟩ := diff_bounds f a l.length C hf hb
      calc
        _ ≤ ‖UnitAddTorus.mFourierCoeff (shiftDiff f a) n‖ := coeff_diff f n i hi
        _ ≤ (C * ‖a‖) * (l.map (fun j => (max 1 |(n j : ℝ)|)⁻¹)).prod := (ih (shiftDiff f a) (C * ‖a‖) (mul_nonneg hC (norm_nonneg _)) hfd hbd)
        _ ≤ (C * (max 1 |(n i : ℝ)|)⁻¹) * (l.map (fun j => (max 1 |(n j : ℝ)|)⁻¹)).prod := by
          gcongr
          · exact List.prod_nonneg (fun x hx => by obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx; positivity)
          · exact shift_norm_le n i hi
        _ = _ := by ring

theorem compactTorus_mFourierCoeff_decay_of_deriv_bound (f : C(UnitAddTorus d, ℂ)) (C : ℝ)
    (hC : 0 ≤ C)
    (hf : ContDiff ℝ (2 * Fintype.card d : ℕ)
      (fun x : d → ℝ => f (fun i => (x i : UnitAddCircle))))
    (hbound : ∀ k ≤ 2 * Fintype.card d, ∀ x : d → ℝ,
      ‖iteratedFDeriv ℝ k
        (fun y : d → ℝ => f (fun i => (y i : UnitAddCircle))) x‖ ≤ C) :
    ∀ n : d → ℤ, ‖UnitAddTorus.mFourierCoeff f n‖ ≤
      C * ∏ i : d, ((max 1 |(n i : ℝ)|) ^ 2)⁻¹ := by
  classical
  intro n
  let l := Finset.univ.toList ++ (Finset.univ : Finset d).toList
  have hlen : l.length = 2 * Fintype.card d := by simp [l]; omega
  have hh := coeff_list l f C hC (by simpa only [hlen] using hf) (by simpa only [hlen] using hbound) n
  convert hh using 1
  simp only [l, List.map_append, List.prod_append, Finset.prod_map_toList]
  rw [← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp [pow_two, mul_inv]

end
end DedekindZetaZeroFree

end

section

namespace DedekindZetaZeroFree

noncomputable section
open scoped BigOperators

theorem compactTorus_product_decay_comparison
    {d : Type*} [Fintype d] (x : d → ℝ) :
    (∏ i : d, ((max 1 |x i|) ^ 2)⁻¹) ≤
      (4 : ℝ) ^ Fintype.card d * ∏ i : d, ((1 + |x i|) ^ 2)⁻¹ := by
  calc _
      ≤ ∏ i : d, (4 * ((1 + |x i|) ^ 2)⁻¹) := by
        apply Finset.prod_le_prod₀
        · intro i _
          exact inv_nonneg.mpr (sq_nonneg _)
        · intro i _
          let x := (x i)
          set m : ℝ := max 1 |x| with hm_def
          have hmpos : (0 : ℝ) < m := lt_of_lt_of_le one_pos (le_max_left _ _)
          have hle : 1 + |x| ≤ 2 * m := by
            rcases lt_or_ge |x| 1 with h | h
            · rw [hm_def, max_eq_left (le_of_lt h)]; linarith
            · rw [hm_def, max_eq_right h]; linarith
          have hpos2 : (0 : ℝ) < (1 + |x|) ^ 2 := by positivity
          have hsq : (1 + |x|) ^ 2 ≤ 4 * m ^ 2 := by
            have hnn : (0 : ℝ) ≤ 2 * m := by positivity
            nlinarith [hle, abs_nonneg x, hnn, hmpos]
          have key : (1 : ℝ) / (m ^ 2) ≤ 4 / (1 + |x|) ^ 2 := by
            rw [div_le_div_iff₀ (by positivity) hpos2]
            linarith [hsq]
          simpa [hm_def, div_eq_mul_inv] using key
    _ = (4 : ℝ) ^ Fintype.card d * ∏ i : d, ((1 + |x i|) ^ 2)⁻¹ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

end
end DedekindZetaZeroFree

end

section

namespace DedekindZetaZeroFree

noncomputable section
open scoped BigOperators

set_option maxHeartbeats 1000000

private lemma summable_int_inv_one_add_abs_sq :
    Summable (fun n : ℤ => ((1 + |(n : ℝ)|) ^ 2)⁻¹) := by
  have hnat : Summable (fun n : ℕ => ((1 + (n : ℝ)) ^ 2)⁻¹) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_comm] using ((summable_nat_add_iff 1).mpr
      (Real.summable_nat_pow_inv.mpr (by norm_num : (1 : ℕ) < 2)))
  apply Summable.of_nat_of_neg
  · simpa using hnat
  · simpa using hnat

private lemma summable_mul_prod_of_nonneg {α β : Type*} {f : α → ℝ} {g : β → ℝ}
    (hf : Summable f) (hg : Summable g) (hf0 : ∀ a, 0 ≤ f a) (hg0 : ∀ b, 0 ≤ g b) :
    Summable (fun p : α × β => f p.1 * g p.2) := by
  rw [summable_prod_of_nonneg (fun p => mul_nonneg (hf0 p.1) (hg0 p.2))]
  refine ⟨fun a => hg.mul_left (f a), ?_⟩
  simp_rw [tsum_mul_left]
  exact hf.mul_right _

private lemma summable_pi_prod_of_equiv {d d' : Type*} [Fintype d] [Fintype d'] (e : d ≃ d')
    (w : ℤ → ℝ) (h : Summable (fun m : d' → ℤ => ∏ i : d', w (m i))) :
    Summable (fun n : d → ℤ => ∏ i : d, w (n i)) := by
  let φ : (d → ℤ) ≃ (d' → ℤ) :=
    { toFun := fun n => fun i' => n (e.symm i')
      invFun := fun m => fun i => m (e i)
      left_inv := by intro n; funext i; simp
      right_inv := by intro m; funext i'; simp }
  have hfun : (fun n : d → ℤ => ∏ i : d, w (n i)) =
      (fun m : d' → ℤ => ∏ i : d', w (m i)) ∘ φ := by
    funext n
    show ∏ i : d, w (n i) = ∏ i' : d', w (n (e.symm i'))
    exact (Equiv.prod_comp e.symm (fun i : d => w (n i))).symm
  rw [hfun]
  exact (Equiv.summable_iff φ).mpr h

private lemma summable_pi_prod_of_summable {d : Type*} [Fintype d] (w : ℤ → ℝ)
    (hw : Summable w) (hw0 : ∀ n, 0 ≤ w n) :
    Summable (fun n : d → ℤ => ∏ i : d, w (n i)) := by
  classical
  refine Fintype.induction_empty_option
    (P := fun d _ => Summable (fun n : d → ℤ => ∏ i : d, w (n i))) ?_ ?_ ?_ d
  · intro α β inst e ih
    letI : Fintype α := Fintype.ofEquiv β e.symm
    exact summable_pi_prod_of_equiv e.symm w ih
  · exact Summable.of_finite
  · intro α _ ih
    let φ : (Option α → ℤ) ≃ ℤ × (α → ℤ) :=
      { toFun := fun n => (n none, fun i => n (some i))
        invFun := fun p => fun o => o.elim p.1 p.2
        left_inv := by intro n; funext o; cases o <;> rfl
        right_inv := by intro p; cases p; rfl }
    have hfun : (fun n : Option α → ℤ => ∏ i : Option α, w (n i)) =
        (fun p : ℤ × (α → ℤ) => w p.1 * ∏ i : α, w (p.2 i)) ∘ φ := by
      funext n
      show ∏ i : Option α, w (n i) = w (n none) * ∏ i : α, w (n (some i))
      exact Fintype.prod_option (fun i => w (n i))
    rw [hfun]
    exact (Equiv.summable_iff φ).mpr (summable_mul_prod_of_nonneg hw ih hw0 (fun m => Finset.prod_nonneg fun i _ => hw0 _))

theorem compactTorus_summable_product_decay
    {d : Type*} [Fintype d] :
    Summable (fun n : d → ℤ => ∏ i : d, ((1 + |(n i : ℝ)|) ^ 2)⁻¹) := summable_pi_prod_of_summable (fun n : ℤ => ((1 + |(n : ℝ)|) ^ 2)⁻¹)
    summable_int_inv_one_add_abs_sq (fun _ => inv_nonneg.mpr (sq_nonneg _))

end
end DedekindZetaZeroFree

end

section

namespace DedekindZetaZeroFree

noncomputable section
open scoped BigOperators
open Filter Set

def compactTorusLift {d : Type*} (f : UnitAddTorus d → ℂ) : (d → ℝ) → ℂ :=
  fun x => f (fun i => (x i : UnitAddCircle))

theorem compactTorus_parametric_mFourier {d P : Type*} [Fintype d]
    [TopologicalSpace P] [CompactSpace P]
    (f : P → C(UnitAddTorus d, ℂ))
    (hcontinuous : Continuous (fun z : P × UnitAddTorus d => f z.1 z.2))
    (hregular : ∀ p, ContDiff ℝ (2 * (Fintype.card d + 1) : ℕ)
      (compactTorusLift (f p)))
    (hderivatives : ∀ k ≤ 2 * (Fintype.card d + 1),
      Continuous (fun z : P × (d → ℝ) =>
        iteratedFDeriv ℝ k (compactTorusLift (f z.1)) z.2))
    (hbounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : P) (k : ℕ),
      k ≤ 2 * (Fintype.card d + 1) → ∀ t : d → ℝ,
      ‖iteratedFDeriv ℝ k (compactTorusLift (f p)) t‖ ≤ C) :
    (∃ b : (d → ℤ) → ℝ, Summable b ∧ (∀ n, 0 ≤ b n) ∧
      ∀ p n, ‖UnitAddTorus.mFourierCoeff (f p) n‖ ≤ b n) ∧
    (∀ p, Summable (UnitAddTorus.mFourierCoeff (f p))) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ p,
      (∑' n : d → ℤ, ‖UnitAddTorus.mFourierCoeff (f p) n‖) ≤ C) ∧
    TendstoUniformly
      (fun s : Finset (d → ℤ) => fun z : P × UnitAddTorus d =>
        ∑ n ∈ s, UnitAddTorus.mFourierCoeff (f z.1) n *
          UnitAddTorus.mFourier n z.2)
      (fun z : P × UnitAddTorus d => f z.1 z.2) atTop ∧
    TendstoLocallyUniformly
      (fun s : Finset (d → ℤ) => fun p : P =>
        ∑ n ∈ s, UnitAddTorus.mFourierCoeff (f p) n • UnitAddTorus.mFourier n)
      f atTop := by
  have hmajorant : ∃ b : (d → ℤ) → ℝ, Summable b ∧ (∀ n, 0 ≤ b n) ∧
      ∀ p n, ‖UnitAddTorus.mFourierCoeff (f p) n‖ ≤ b n := by
    classical
    obtain ⟨C, hC, hCbound⟩ := hbounded
    let A := C * (4 : ℝ) ^ Fintype.card d
    let w : (d → ℤ) → ℝ :=
      fun n => ∏ i : d, ((1 + |(n i : ℝ)|) ^ 2)⁻¹
    refine ⟨fun n => A * w n, compactTorus_summable_product_decay.mul_left A, ?_, ?_⟩
    · intro n
      exact mul_nonneg (mul_nonneg hC (pow_nonneg (by norm_num) _)) (Finset.prod_nonneg (fun i _ =>
        inv_nonneg.mpr (sq_nonneg _)))
    · intro p n
      have horder : 2 * Fintype.card d ≤ 2 * (Fintype.card d + 1) := by omega
      calc
        _ ≤
            C * ∏ i : d, ((max 1 |(n i : ℝ)|) ^ 2)⁻¹ := (compactTorus_mFourierCoeff_decay_of_deriv_bound (f p) C hC ((hregular p).of_le (by exact_mod_cast horder))
              (fun k hk x => hCbound p k (hk.trans horder) x) n)
        _ ≤ C * ((4 : ℝ) ^ Fintype.card d * w n) :=
          mul_le_mul_of_nonneg_left
            (compactTorus_product_decay_comparison (fun i => (n i : ℝ))) hC
        _ = A * w n := (mul_assoc _ _ _).symm
  obtain ⟨b, hb, hbpos, hbound⟩ := hmajorant
  have hn :=
    fun p => hb.of_nonneg_of_le (fun n => norm_nonneg _) (hbound p)
  have hs :=
    fun p => (hn p).of_norm
  refine ⟨⟨b, hb, hbpos, hbound⟩, hs, ⟨∑' n, b n, tsum_nonneg hbpos, ?_⟩, ?_, ?_⟩
  · intro p
    exact (hn p).tsum_le_tsum (hbound p) hb
  · have h := tendstoUniformly_tsum hb (fun n (z : P × UnitAddTorus d) =>
      calc
        ‖UnitAddTorus.mFourierCoeff (f z.1) n * UnitAddTorus.mFourier n z.2‖
          ≤ ‖UnitAddTorus.mFourierCoeff (f z.1) n‖ * ‖UnitAddTorus.mFourier n‖ := by
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left
              ((UnitAddTorus.mFourier n).norm_coe_le_norm z.2) (norm_nonneg _)
        _ = ‖UnitAddTorus.mFourierCoeff (f z.1) n‖ := by
          rw [UnitAddTorus.mFourier_norm, mul_one]
        _ ≤ b n := hbound z.1 n)
    convert h using 1
    ext z
    simpa using
      (UnitAddTorus.hasSum_mFourier_series_apply_of_summable (hs z.1) z.2).tsum_eq.symm
  · have h := tendstoUniformly_tsum hb (fun n (p : P) =>
      calc
        ‖UnitAddTorus.mFourierCoeff (f p) n • UnitAddTorus.mFourier n‖
          = ‖UnitAddTorus.mFourierCoeff (f p) n‖ := by
            rw [norm_smul, UnitAddTorus.mFourier_norm, mul_one]
        _ ≤ b n := hbound p n)
    have heq : (fun p => ∑' n, UnitAddTorus.mFourierCoeff (f p) n •
        UnitAddTorus.mFourier n) = f := by
      funext p
      exact (UnitAddTorus.hasSum_mFourier_series_of_summable (hs p)).tsum_eq
    rw [heq] at h
    exact h.tendstoLocallyUniformly

end
end DedekindZetaZeroFree

end
