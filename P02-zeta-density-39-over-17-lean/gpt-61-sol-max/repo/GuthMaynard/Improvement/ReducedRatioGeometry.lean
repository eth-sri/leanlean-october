module
public import Mathlib

@[expose] public section
noncomputable section
open Finset
namespace GuthMaynard.Improvement

/-- Primitive positive ratios have a unique numerator/denominator pair. -/
theorem primitive_ratio_cross_unique {a b c d : ℕ}
    (ha : 0 < a) (hab : a.Coprime b) (hcd : c.Coprime d)
    (he : a*d=c*b) : a=c ∧ b=d := by
  have hac := hab.dvd_of_dvd_mul_right ⟨d,he.symm⟩
  have hca := hcd.dvd_of_dvd_mul_right ⟨b,he⟩
  have hac' := Nat.dvd_antisymm hac hca
  refine ⟨hac',?_⟩
  apply Nat.eq_of_mul_eq_mul_left ha
  simpa only [← hac'] using he.symm

/-- Every positive point on a primitive rational ray has a unique integral
scale. This is the actual source of ratio multiplicities. -/
theorem primitive_ratio_fiber_scale {a b n m : ℕ} (ha : 0 < a)
    (hn : 0 < n) (hab : a.Coprime b) (he : n*b=a*m) :
    ∃ k : ℕ, 0 < k ∧ n=a*k ∧ m=b*k := by
  have han := hab.dvd_of_dvd_mul_right ⟨m,he⟩
  obtain ⟨k,hk⟩ := han
  refine ⟨k,?_,hk,?_⟩
  · by_contra h
    have hk0 : k=0 := by omega
    simp [hk0] at hk
    omega
  · apply Nat.eq_of_mul_eq_mul_left ha
    calc
      a*m = n*b := he.symm
      _ = a*(b*k) := by rw [hk]; ring

def reducedRatioFiber (X a b : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 X) ×ˢ (Icc 1 X)).filter (fun p => p.1*b=a*p.2)

/-- Actual primitive ratio multiplicity up to natural top X. The dyadic
source interval (N,2N] is a subset with X=floor(2N). -/
theorem reducedRatioFiber_card {X a b : ℕ} (ha : 0 < a) (_hb : 0 < b)
    (hab : a.Coprime b) :
    (reducedRatioFiber X a b).card ≤ X/(max a b) := by
  have hmap : ∀ p ∈ reducedRatioFiber X a b,
      p.1/a ∈ Icc 1 (X/(max a b)) := by
    intro p hp
    obtain ⟨hp,hcross⟩ := mem_filter.mp hp
    obtain ⟨hn,hm⟩ := mem_product.mp hp
    have hpn := (mem_Icc.mp hn).1
    obtain ⟨k,hk,hnk,hmk⟩ := primitive_ratio_fiber_scale ha (by omega : 0 < p.1) hab hcross
    have hdiv : p.1/a=k := by rw [hnk,Nat.mul_div_cancel_left _ ha]
    rw [hdiv,mem_Icc]
    refine ⟨hk,?_⟩
    apply (Nat.le_div_iff_mul_le (lt_of_lt_of_le ha (le_max_left _ _))).mpr
    by_cases hh : a ≤ b
    all_goals (grind)
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1/a) (reducedRatioFiber X a b : Set (ℕ × ℕ)) := by
    intro p hp q hq he
    obtain ⟨hp,hpc⟩ := mem_filter.mp hp
    obtain ⟨hq,hqc⟩ := mem_filter.mp hq
    obtain ⟨kp,hkp,hpn,hpm⟩ := primitive_ratio_fiber_scale ha
      (by have := (mem_Icc.mp (mem_product.mp hp).1).1; omega) hab hpc
    obtain ⟨kq,hkq,hqn,hqm⟩ := primitive_ratio_fiber_scale ha
      (by have := (mem_Icc.mp (mem_product.mp hq).1).1; omega) hab hqc
    have hk : kp=kq := by simpa [hpn,hqn,Nat.mul_div_cancel_left _ ha] using he
    exact Prod.ext (by rw [hpn,hqn,hk]) (by rw [hpm,hqm,hk])
  have hc := card_le_card_of_injOn (fun p : ℕ × ℕ => p.1/a) hmap hinj
  simpa using hc

/-- A one-unit gap between positive cross-products gives logarithmic
spacing at the reciprocal square height, without a ratio-band premise. -/
theorem log_cross_gap {p q Y : ℝ} (hq : 0 < q) (hgap : q+1 ≤ p)
    (hpY : p ≤ Y^2) : (Y^2)⁻¹ ≤ Real.log p-Real.log q := by
  have hp : 0 < p := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hq hp)
  rw [Real.log_div hq.ne' hp.ne'] at hlog
  have hgap' : p⁻¹ ≤ 1-q/p := by field_simp <;> nlinarith
  calc
    (Y^2)⁻¹ ≤ p⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le hp hpY
    _ ≤ _ := hgap'.trans (by linarith)

/-- Distinct primitive pairs of height at most Y have genuinely separated
logarithmic ratios. This includes the diagonal primitive pair (1,1). -/
theorem primitive_log_ratio_separated {a b c d : ℕ} {Y : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hab : a.Coprime b) (hcd : c.Coprime d) (hne : (a,b) ≠ (c,d))
    (haY : (a:ℝ) ≤ Y) (hbY : (b:ℝ) ≤ Y)
    (hcY : (c:ℝ) ≤ Y) (hdY : (d:ℝ) ≤ Y) :
    (Y^2)⁻¹ ≤ |Real.log ((a:ℝ)/b)-Real.log ((c:ℝ)/d)| := by
  have hcross : a*d ≠ c*b := by
    intro he
    obtain ⟨rfl,rfl⟩ := primitive_ratio_cross_unique ha hab hcd he
    exact hne rfl
  have heq : Real.log ((a:ℝ)/b)-Real.log ((c:ℝ)/d) =
      Real.log ((a:ℝ)*d)-Real.log ((c:ℝ)*b) := by
    rw [Real.log_div (by positivity) (by positivity),Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity)]
    ring
  rw [heq]
  have hY : 0 ≤ Y := (show 0 ≤ (a:ℝ) by positivity).trans haY
  have hadY : (a:ℝ)*d ≤ Y^2 := by nlinarith [mul_le_mul haY hdY (by positivity : 0 ≤ (d:ℝ)) hY]
  have hcbY : (c:ℝ)*b ≤ Y^2 := by nlinarith [mul_le_mul hcY hbY (by positivity : 0 ≤ (b:ℝ)) hY]
  rcases lt_or_gt_of_ne hcross with h | h
  · have hg : (a:ℝ)*d+1 ≤ (c:ℝ)*b := by exact_mod_cast (show a*d+1 ≤ c*b by omega)
    have hh := log_cross_gap (by positivity : 0 < (a:ℝ)*d) hg hcbY
    exact hh.trans (by rw [abs_sub_comm]; exact le_abs_self _)
  · have hg : (c:ℝ)*b+1 ≤ (a:ℝ)*d := by exact_mod_cast (show c*b+1 ≤ a*d by omega)
    exact (log_cross_gap (by positivity : 0 < (c:ℝ)*b) hg hadY).trans (le_abs_self _)

/-- Even without primitivity, at most 2q positive pairs have height q. -/
theorem positive_height_shell_card (S : Finset (ℕ × ℕ))
    (hpos : ∀ p ∈ S, 0 < p.1 ∧ 0 < p.2) (q : ℕ) :
    (S.filter (fun p => max p.1 p.2=q)).card ≤ 2*q := by
  have hsub : S.filter (fun p => max p.1 p.2=q) ⊆
      ({q} ×ˢ Icc 1 q) ∪ (Icc 1 q ×ˢ {q}) := by grind
  exact (card_le_card hsub).trans ((card_union_le _ _).trans_eq (by simp; omega))

section
variable (S : Finset (ℕ × ℕ)) {Y : ℕ} {X : ℝ}
    (hX : 0 ≤ X) (hpos : ∀ p ∈ S, 0 < p.1 ∧ 0 < p.2)
    (hY : ∀ p ∈ S, max p.1 p.2 ≤ Y) (w : ℕ × ℕ → ℝ)
    (hw0 : ∀ p ∈ S, 0 ≤ w p)
    (hw : ∀ p ∈ S, w p ≤ X/(max p.1 p.2:ℕ))
include S Y X hX hpos hY w hw0 hw

/-- The actual squared ratio-weight budget follows just from the integral
ray multiplicity upper bound; no coprime counting asymptotic is needed. -/
theorem positive_ratio_square_weight  :
    (∑ p ∈ S, (w p)^2) ≤ 2*X^2*(harmonic Y:ℝ) := by
  have hmap : ∀ p ∈ S, max p.1 p.2 ∈ Icc 1 Y := by grind
  rw [← sum_fiberwise_of_maps_to hmap (fun p => (w p)^2)]
  calc
    _ ≤ ∑ q ∈ Icc 1 Y, 2*X^2/(q:ℝ) := by
      apply sum_le_sum
      intro q hq
      have hqpos : (0:ℝ) < q := by exact_mod_cast (mem_Icc.mp hq).1
      calc
        _ ≤ ∑ p ∈ S.filter (fun p => max p.1 p.2=q), (X/(q:ℝ))^2 := by
          apply sum_le_sum
          intro p hp
          obtain ⟨hp,he⟩ := mem_filter.mp hp
          exact (sq_le_sq₀ (hw0 p hp) (div_nonneg hX hqpos.le)).mpr (by simpa only [he] using hw p hp)
        _ = ((S.filter (fun p => max p.1 p.2=q)).card:ℝ)*(X/(q:ℝ))^2 := by simp
        _ ≤ (2*(q:ℝ))*(X/(q:ℝ))^2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact_mod_cast positive_height_shell_card S hpos q
        _ = _ := by field_simp
    _ = _ := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      rw [mul_sum]
      rfl

/-- Explicit logarithmic form of the square multiplicity budget. -/
theorem positive_ratio_square_weight_log  :
    (∑ p ∈ S, (w p)^2) ≤ 2*X^2*(1+Real.log Y) :=
  (positive_ratio_square_weight S hX hpos hY w hw0 hw).trans
    (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log Y) (by positivity))
end



