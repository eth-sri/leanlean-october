module

public import Erdos821.P4Frame.Frame
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

set_option autoImplicit false

open scoped BigOperators Classical

namespace OAI.LargePrimeGaps
open scoped ComplexConjugate
noncomputable def bvExp (x : ℝ) : ℂ := Complex.exp (Complex.I*(2*Real.pi*x:ℝ))

@[simp] theorem bvExp_zero : bvExp 0=1 := by simp [bvExp]

@[simp] theorem norm_bvExp (x : ℝ) : ‖bvExp x‖=1 := by simp [bvExp,Complex.norm_exp]

theorem bvExp_add (x y : ℝ) : bvExp (x+y)=bvExp x*bvExp y := by
  unfold bvExp
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

theorem conj_bvExp (x : ℝ) : conj (bvExp x)=bvExp (-x) := by
  unfold bvExp
  rw [←Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem bvExp_nat_mul (n : ℕ) (x : ℝ) : bvExp ((n:ℝ)*x)=bvExp x^n := by
  unfold bvExp
  rw [←Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem bvExp_sub_one_lower {x : ℝ} (hx : |x|≤1/2) :
    4*|x|≤‖bvExp x-1‖ := by
  rw [bvExp,Complex.norm_exp_I_mul_ofReal_sub_one]
  have hs : |Real.pi*x|≤Real.pi/2 := by
    rw [abs_mul,abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have h := Real.mul_abs_le_abs_sin hs
  rw [abs_mul,abs_of_pos Real.pi_pos] at h
  have hpi : Real.pi≠0 := ne_of_gt Real.pi_pos
  have he : 2/Real.pi*(Real.pi*|x|)=2*|x| := by field_simp
  rw [he] at h
  have hid : 2*Real.pi*x/2=Real.pi*x := by ring
  rw [hid,Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith

theorem exponential_sum_bound (N : ℕ) {x : ℝ} (hx : |x|≤1/2) (hx0 : x≠0) :
    ‖∑ n∈Finset.range N,bvExp ((n:ℝ)*x)‖≤1/(2*|x|) := by
  have ha : 0 < |x| := abs_pos.mpr hx0
  have hden := bvExp_sub_one_lower hx
  have hn : 0<‖bvExp x-1‖ := lt_of_lt_of_le (by positivity : 0<4*|x|) hden
  have he := geom_sum_mul (bvExp x) N
  have hnorm := congrArg norm he
  rw [norm_mul] at hnorm
  have hu : ‖bvExp x^N-1‖≤2 := by
    calc
      _ ≤ ‖bvExp x^N‖+‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp [norm_pow]; norm_num
  have htimes : ‖∑ n∈Finset.range N,bvExp x^n‖*(4*|x|)≤2 := by
    exact (mul_le_mul_of_nonneg_left hden (norm_nonneg _)).trans (hnorm.trans_le hu)
  simp_rw [bvExp_nat_mul]
  apply (le_div_iff₀ (by positivity : (0:ℝ)<2*|x|)).mpr
  nlinarith

theorem reciprocal_sum_le_harmonic {ι : Type*} (s : Finset ι) (t : ι→ℝ) (D : ℕ)
    (ht : ∀ i∈s,1≤t i ∧ t i≤D)
    (hsep : ∀ i∈s,∀ j∈s,i≠j→1≤|t i-t j|) :
    (∑ i∈s,1/t i)≤(harmonic D:ℝ) := by
  classical
  let r : ι→ℕ := fun i => ⌊t i⌋₊
  have hr : ∀ i∈s,r i∈Finset.Icc 1 D := by
    intro i hi
    exact Finset.mem_Icc.mpr ⟨Nat.le_floor (by simpa using (ht i hi).1),
      Nat.floor_le_of_le (ht i hi).2⟩
  have hinj : Set.InjOn r s := by
    intro i hi j hj he
    by_contra hij
    have h := hsep i hi j hj hij
    have hil := Nat.floor_le (le_trans (by norm_num : (0:ℝ)≤1) (ht i hi).1)
    have hjl := Nat.floor_le (le_trans (by norm_num : (0:ℝ)≤1) (ht j hj).1)
    have hiu := Nat.lt_floor_add_one (t i)
    have hju := Nat.lt_floor_add_one (t j)
    change ⌊t i⌋₊=⌊t j⌋₊ at he
    rw [he] at hil hiu
    rcases le_abs.mp h with h|h <;> linarith
  calc
    _ ≤ ∑ i∈s,1/(r i:ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply one_div_le_one_div_of_le
      · exact_mod_cast (Finset.mem_Icc.mp (hr i hi)).1
      · exact Nat.floor_le (le_trans (by norm_num : (0:ℝ)≤1) (ht i hi).1)
    _ = ∑ k∈s.image r,1/(k:ℝ) := (Finset.sum_image (f := fun k : ℕ => (1:ℝ)/k) hinj).symm
    _ ≤ ∑ k∈Finset.Icc 1 D,1/(k:ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hr)
        (fun _ _ _ => by positivity)
    _ = _ := by simp [harmonic_eq_sum_Icc]

theorem reciprocal_sum_le_scaled_harmonic {ι : Type*} (s : Finset ι) (t : ι→ℝ)
    {D : ℕ} (hD : 0<D) (ht : ∀ i∈s,1/(D:ℝ)≤t i ∧ t i≤1)
    (hsep : ∀ i∈s,∀ j∈s,i≠j→1/(D:ℝ)≤|t i-t j|) :
    (∑ i∈s,1/t i)≤(D:ℝ)*(harmonic D:ℝ) := by
  have hDr : 0<(D:ℝ) := by exact_mod_cast hD
  have hh := reciprocal_sum_le_harmonic s (fun i => (D:ℝ)*t i) D
    (fun i hi => ⟨by have h := mul_le_mul_of_nonneg_left (ht i hi).1 hDr.le
                     field_simp at h
                     nlinarith,
      by nlinarith [(ht i hi).2]⟩)
    (fun i hi j hj hij => by
      rw [←mul_sub,abs_mul,abs_of_pos hDr]
      have h := (div_le_iff₀ hDr).mp (hsep i hi j hj hij)
      nlinarith)
  have hm := mul_le_mul_of_nonneg_left hh hDr.le
  rw [Finset.mul_sum] at hm
  calc
    _ = ∑ i∈s,(D:ℝ)*(1/((D:ℝ)*t i)) := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp
    _ ≤ _ := hm

@[simp] theorem bvExp_int (m : ℤ) : bvExp m=1 := by
  unfold bvExp
  have he : Complex.I * ((2*Real.pi*(m:ℝ):ℝ):ℂ)=(m:ℂ)*(2*Real.pi*Complex.I) := by
    push_cast
    ring
  rw [he,Complex.exp_int_mul,Complex.exp_two_pi_mul_I,one_zpow]

theorem bvExp_sub_int (x : ℝ) (m : ℤ) : bvExp (x-m)=bvExp x := by
  rw [sub_eq_add_neg,bvExp_add]
  have h : bvExp (-(m:ℝ))=1 := by simpa using bvExp_int (-m)
  rw [h,mul_one]

noncomputable def bvCentered (x : ℝ) : ℝ := x-(⌊x+1/2⌋:ℤ)

theorem abs_bvCentered_le (x : ℝ) : |bvCentered x|≤1/2 := by
  have hl := Int.floor_le (x+1/2)
  have hu := Int.lt_floor_add_one (x+1/2)
  dsimp [bvCentered]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem bvExp_centered (x : ℝ) : bvExp (bvCentered x)=bvExp x := bvExp_sub_int _ _

theorem exponential_sum_centered (N : ℕ) (x : ℝ) :
    (∑ n∈Finset.range N,bvExp ((n:ℝ)*bvCentered x))=
      ∑ n∈Finset.range N,bvExp ((n:ℝ)*x) := by
  simp_rw [bvExp_nat_mul,bvExp_centered]

theorem centered_difference_separated {ι : Type*} (s : Finset ι) (θ : ι→ℝ) {D : ℕ}
    (hsep : ∀ i∈s,∀ j∈s,i≠j→∀ m:ℤ,1/(D:ℝ)≤|θ i-θ j-m|)
    (a : ℝ) {i j : ι} (hi : i∈s) (hj : j∈s) (hij : i≠j) :
    1/(D:ℝ)≤|bvCentered (θ i-a)-bvCentered (θ j-a)| := by
  have h := hsep i hi j hj hij (⌊θ i-a+1/2⌋-⌊θ j-a+1/2⌋)
  dsimp [bvCentered]
  convert h using 2
  push_cast
  ring

theorem exponential_kernel_row_bound {ι : Type*} (s : Finset ι) (θ : ι→ℝ)
    {D : ℕ} (hD : 0<D)
    (hsep : ∀ i∈s,∀ j∈s,i≠j→∀ m:ℤ,1/(D:ℝ)≤|θ i-θ j-m|)
    (N : ℕ) {i : ι} (hi : i∈s) :
    (∑ j∈s,‖∑ n∈Finset.range N,bvExp ((n:ℝ)*(θ j-θ i))‖)≤
      (N:ℝ)+(D:ℝ)*(harmonic D:ℝ) := by
  classical
  let t := s.erase i
  let r := fun j => bvCentered (θ j-θ i)
  have hDr : 0<(D:ℝ) := by exact_mod_cast hD
  have hr : ∀ j∈t,1/(D:ℝ)≤|r j| := by
    intro j hj
    rcases Finset.mem_erase.mp hj with ⟨hji,hjs⟩
    exact hsep j hjs i hi hji ⌊θ j-θ i+1/2⌋
  have hn : ∀ j∈t,r j≠0 := by
    intro j hj hj0
    have h := hr j hj
    rw [hj0,abs_zero] at h
    exact (not_le_of_gt (one_div_pos.mpr hDr)) h
  have hpair : ∀ j∈t,∀ k∈t,j≠k→1/(D:ℝ)≤|r j-r k| := by
    intro j hj k hk hjk
    exact centered_difference_separated s θ hsep (θ i)
      (Finset.mem_of_mem_erase hj) (Finset.mem_of_mem_erase hk) hjk
  have hhalf : ∀ b:Bool,
      (∑ j∈t.filter (fun j => decide (0≤r j)=b),1/|r j|)≤(D:ℝ)*(harmonic D:ℝ) := by
    intro b
    apply reciprocal_sum_le_scaled_harmonic _ _ hD
    · intro j hj
      exact ⟨hr j ((Finset.mem_filter.mp hj).1),(abs_bvCentered_le _).trans (by norm_num)⟩
    · intro j hj k hk hjk
      have h := hpair j ((Finset.mem_filter.mp hj).1) k ((Finset.mem_filter.mp hk).1) hjk
      have hjb := (Finset.mem_filter.mp hj).2
      have hkb := (Finset.mem_filter.mp hk).2
      cases b <;> simp only [decide_eq_false_iff_not,decide_eq_true_eq,not_le] at hjb hkb
      · simpa only [abs_of_neg hjb,abs_of_neg hkb,neg_sub_neg,abs_sub_comm] using h
      · simpa only [abs_of_nonneg hjb,abs_of_nonneg hkb] using h
  have hrec : (∑ j∈t,1/|r j|)≤2*(D:ℝ)*(harmonic D:ℝ) := by
    have hp := hhalf true
    have hm := hhalf false
    simp only [decide_eq_true_eq,decide_eq_false_iff_not] at hp hm
    have he := Finset.sum_filter_add_sum_filter_not t (fun j => 0≤r j) (fun j => 1/|r j|)
    linarith
  have hoff : (∑ j∈t,‖∑ n∈Finset.range N,bvExp ((n:ℝ)*(θ j-θ i))‖)≤
      (D:ℝ)*(harmonic D:ℝ) := by
    calc
      _ ≤ ∑ j∈t,1/(2*|r j|) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [←exponential_sum_centered]
        exact exponential_sum_bound N (abs_bvCentered_le _) (hn j hj)
      _ = (∑ j∈t,1/|r j|)/2 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ _ := by linarith
  rw [←Finset.sum_erase_add _ _ hi]
  have hd : ‖∑ n∈Finset.range N,bvExp ((n:ℝ)*(θ i-θ i))‖=(N:ℝ) := by simp
  rw [hd]
  linarith

noncomputable def bvExponentialVector (N : ℕ) (θ : ℝ) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 (fun n => bvExp (-((n:ℕ):ℝ)*θ))

theorem inner_bvExponentialVector (N : ℕ) (θ η : ℝ) :
    inner ℂ (bvExponentialVector N θ) (bvExponentialVector N η)=
      ∑ n∈Finset.range N,bvExp ((n:ℝ)*(θ-η)) := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,bvExponentialVector]
  simp_rw [mul_comm (bvExp _)]
  simp_rw [conj_bvExp,←bvExp_add]
  have he : ∀ n:Fin N,-(-((n:ℕ):ℝ)*θ)+(-((n:ℕ):ℝ)*η)=((n:ℕ):ℝ)*(θ-η) := by
    intro n
    ring
  simp_rw [he]
  exact Fin.sum_univ_eq_sum_range (fun n : ℕ => bvExp ((n:ℝ)*(θ-η))) N

theorem inner_bvExponentialVector_coefficients (N : ℕ) (θ : ℝ) (a : Fin N→ℂ) :
    inner ℂ (bvExponentialVector N θ) (WithLp.toLp 2 a)=
      ∑ n:Fin N,a n*bvExp (((n:ℕ):ℝ)*θ) := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,bvExponentialVector]
  apply Finset.sum_congr rfl
  intro n _
  rw [conj_bvExp]
  congr 2
  ring

theorem additive_large_sieve {ι : Type*} (s : Finset ι) (θ : ι→ℝ)
    {D : ℕ} (hD : 0<D)
    (hsep : ∀ i∈s,∀ j∈s,i≠j→∀ m:ℤ,1/(D:ℝ)≤|θ i-θ j-m|)
    (N : ℕ) (a : Fin N→ℂ) :
    (∑ i∈s,‖∑ n:Fin N,a n*bvExp (((n:ℕ):ℝ)*θ i)‖^2)≤
      ((N:ℝ)+(D:ℝ)*(harmonic D:ℝ))*(∑ n:Fin N,‖a n‖^2) := by
  have hH : 0≤(harmonic D:ℝ) := by
    rw [harmonic_eq_sum_Icc,Rat.cast_sum]
    exact Finset.sum_nonneg (fun _ _ => by simp only [Rat.cast_inv,Rat.cast_natCast]; positivity)
  have hB : 0≤(N:ℝ)+(D:ℝ)*(harmonic D:ℝ) := by positivity
  have hr : ∀ i∈s,(∑ j∈s,‖inner ℂ (bvExponentialVector N (θ i))
      (bvExponentialVector N (θ j))‖)≤(N:ℝ)+(D:ℝ)*(harmonic D:ℝ) := by
    intro i hi
    simp_rw [inner_bvExponentialVector]
    have hh := exponential_kernel_row_bound s (fun i => -θ i) hD
      (fun j hj k hk hjk m => by
        have h := hsep j hj k hk hjk (-m)
        have he : -θ j- -θ k-(m:ℝ)=-(θ j-θ k-(-m:ℤ)) := by
          push_cast
          ring
        rw [he,abs_neg]
        exact h) N hi
    convert hh using 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    congr 1
    ring
  have h := gram_large_sieve s (fun i => bvExponentialVector N (θ i)) hB hr (WithLp.toLp 2 a)
  simpa only [inner_bvExponentialVector_coefficients,EuclideanSpace.norm_sq_eq,WithLp.ofLp_toLp] using h


end OAI.LargePrimeGaps

open OAI.LargePrimeGaps

namespace Erdos821.S34.Proofs

/-- Extend a sequence by zero into an integer interval, without changing its
sum. The origin lo is unrestricted. -/
theorem sum_interval_extension {E : Type*} [AddCommMonoid E]
    (s : Finset ℤ) (lo : ℤ) (N : ℕ)
    (hs : ∀ n ∈ s, lo ≤ n ∧ n < lo + N) (f : ℤ → E) :
    (∑ i : Fin N, if lo + (i : ℤ) ∈ s then f (lo + (i : ℤ)) else 0) =
      ∑ n ∈ s, f n := by
  let index : Fin N → ℤ := fun i => lo + (i : ℤ)
  have hinj : Function.Injective index := by
    intro i j h
    apply Fin.ext
    dsimp [index] at h
    exact_mod_cast add_left_cancel h
  have him : s ⊆ Finset.univ.image index := by
    intro n hn
    obtain ⟨hlo, hhi⟩ := hs n hn
    refine Finset.mem_image.mpr ⟨⟨(n - lo).toNat, by omega⟩, Finset.mem_univ _, ?_⟩
    dsimp [index]
    omega
  calc
    _ = ∑ n ∈ Finset.univ.image index, if n ∈ s then f n else 0 :=
      (Finset.sum_image (f := fun n => if n ∈ s then f n else 0)
        (fun i _ j _ h => hinj h)).symm
    _ = ∑ n ∈ s, f n := by
      symm
      calc
        _ = ∑ n ∈ s, if n ∈ s then f n else 0 := by
          apply Finset.sum_congr rfl
          intro n hn
          simp [hn]
        _ = _ := Finset.sum_subset him (fun n _ hn => by simp [hn])

/-- The prebuilt additive large sieve on an arbitrary integer interval, with
arbitrary holes in the coefficient support. -/
theorem integer_additive_large_sieve {ι : Type*} (frequencies : Finset ι) (θ : ι → ℝ)
    (D : ℕ) (hD : 0 < D)
    (hsep : ∀ i ∈ frequencies, ∀ j ∈ frequencies, i ≠ j →
      ∀ m : ℤ, 1 / (D : ℝ) ≤ |θ i - θ j - m|)
    (s : Finset ℤ) (lo : ℤ) (N : ℕ) (a : ℤ → ℂ)
    (hs : ∀ n ∈ s, lo ≤ n ∧ n < lo + N) :
    (∑ i ∈ frequencies, ‖∑ n ∈ s, a n * bvExp ((n : ℝ) * θ i)‖ ^ 2) ≤
      ((N : ℝ) + (D : ℝ) * (harmonic D : ℝ)) * (∑ n ∈ s, ‖a n‖ ^ 2) := by
  let a' : Fin N → ℂ := fun i => if lo + (i : ℤ) ∈ s then a (lo + (i : ℤ)) else 0
  have hsq : (∑ i : Fin N, ‖a' i‖ ^ 2) = ∑ n ∈ s, ‖a n‖ ^ 2 := by
    simpa [a', apply_ite] using sum_interval_extension s lo N hs (fun n => ‖a n‖ ^ 2)
  have hsum (t : ℝ) : (∑ n ∈ s, a n * bvExp ((n : ℝ) * t)) =
      bvExp ((lo : ℝ) * t) * (∑ i : Fin N, a' i * bvExp (((i : ℕ) : ℝ) * t)) := by
    calc
      _ = ∑ i : Fin N, a' i * bvExp (((lo + (i : ℤ) : ℤ) : ℝ) * t) := by
        symm
        simpa [a', ite_mul] using
          sum_interval_extension s lo N hs (fun n => a n * bvExp ((n : ℝ) * t))
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        push_cast
        rw [add_mul, bvExp_add]
        ring
  calc
    _ = ∑ i ∈ frequencies, ‖∑ n : Fin N, a' n * bvExp (((n : ℕ) : ℝ) * θ i)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hsum, norm_mul]
      simp
    _ ≤ _ := additive_large_sieve frequencies θ hD hsep N a'
    _ = _ := by rw [hsq]

end Erdos821.S34.Proofs
