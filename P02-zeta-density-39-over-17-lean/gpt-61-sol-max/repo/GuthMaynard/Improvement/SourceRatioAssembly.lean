module
import Mathlib
public import GuthMaynard.Improvement.ReducedRatioGeometry

@[expose] public section
noncomputable section
open Finset
namespace GuthMaynard.Improvement

def sourceReducedPair (p : ℕ × ℕ) : ℕ × ℕ :=
  (p.1 / Nat.gcd p.1 p.2, p.2 / Nat.gcd p.1 p.2)

def sourceRatioFiber (P : Finset (ℕ × ℕ)) (q : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  P.filter (fun p => p.1*q.2=q.1*p.2)

section
variable {p : ℕ × ℕ} (hp : 0 < p.1 ∧ 0 < p.2)
include p hp

/-- The actual gcd normalization is positive, primitive, and never increases
height. -/
theorem sourceReducedPair_properties  :
    0 < (sourceReducedPair p).1 ∧ 0 < (sourceReducedPair p).2 ∧
    (sourceReducedPair p).1.Coprime (sourceReducedPair p).2 ∧
    (sourceReducedPair p).1 ≤ p.1 ∧ (sourceReducedPair p).2 ≤ p.2 := by
  dsimp only [sourceReducedPair]
  refine ⟨Nat.div_gcd_pos_of_pos_left _ hp.1,?_,
    Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left _ hp.1),
    Nat.div_le_self _ _,Nat.div_le_self _ _⟩
  simpa only [Nat.gcd_comm] using Nat.div_gcd_pos_of_pos_left p.1 hp.2

theorem sourceReducedPair_ratio  :
    ((sourceReducedPair p).1:ℝ)/(sourceReducedPair p).2 = (p.1:ℝ)/p.2 := by
  have hq := sourceReducedPair_properties hp
  have hleft : (sourceReducedPair p).1 * Nat.gcd p.1 p.2 = p.1 := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  have hright : (sourceReducedPair p).2 * Nat.gcd p.1 p.2 = p.2 := Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
  apply (div_eq_div_iff (by exact_mod_cast (Nat.ne_of_gt hq.2.1) : ((sourceReducedPair p).2:ℝ) ≠ 0)
    (by exact_mod_cast (Nat.ne_of_gt hp.2) : (p.2:ℝ) ≠ 0)).mpr
  have he : (sourceReducedPair p).1*p.2 = p.1*(sourceReducedPair p).2 := by nlinarith
  exact_mod_cast he
end


/-- A gcd fiber is exactly the primitive cross-product fiber, with no
missing or duplicated source pairs. -/
theorem sourceReducedPair_eq_iff {p q : ℕ × ℕ}
    (hp : 0 < p.1 ∧ 0 < p.2) (hq : 0 < q.1 ∧ 0 < q.2)
    (hprim : q.1.Coprime q.2) : sourceReducedPair p=q ↔ p.1*q.2=q.1*p.2 := by
  have hn := sourceReducedPair_properties hp
  have he := sourceReducedPair_ratio hp
  constructor
  · intro h
    rw [h] at he
    have hh := (div_eq_div_iff (by exact_mod_cast (Nat.ne_of_gt hq.2) : (q.2:ℝ) ≠ 0)
      (by exact_mod_cast (Nat.ne_of_gt hp.2) : (p.2:ℝ) ≠ 0)).mp he
    exact_mod_cast hh.symm
  · intro h
    have hh : ((sourceReducedPair p).1:ℝ)/(sourceReducedPair p).2=(q.1:ℝ)/q.2 := by
      rw [he]
      apply (div_eq_div_iff (by exact_mod_cast (Nat.ne_of_gt hp.2) : (p.2:ℝ) ≠ 0) (by exact_mod_cast (Nat.ne_of_gt hq.2) : (q.2:ℝ) ≠ 0)).mpr
      exact_mod_cast h
    have hc : (sourceReducedPair p).1*q.2=q.1*(sourceReducedPair p).2 := by
      exact_mod_cast (div_eq_div_iff (by exact_mod_cast (Nat.ne_of_gt hn.2.1) : ((sourceReducedPair p).2:ℝ) ≠ 0)
        (by exact_mod_cast (Nat.ne_of_gt hq.2) : (q.2:ℝ) ≠ 0)).mp hh
    obtain ⟨h₁,h₂⟩ := primitive_ratio_cross_unique hn.1 hn.2.2.1 hprim hc
    exact Prod.ext h₁ h₂

/-- Exact reindexing of the actual logarithmic ratio sum. The multiplicity
is the cardinality of the actual cross-product fiber. -/
theorem source_ratio_sum_assembly (P : Finset (ℕ × ℕ))
    (hP : ∀ p ∈ P, 0 < p.1 ∧ 0 < p.2) (F : ℝ → ℝ) :
    (∑ p ∈ P, F (Real.log ((p.1:ℝ)/p.2))) =
      ∑ q ∈ P.image sourceReducedPair, (sourceRatioFiber P q).card *
        F (Real.log ((q.1:ℝ)/q.2)) := by
  rw [← sum_fiberwise_of_maps_to
    (fun p hp => mem_image_of_mem sourceReducedPair hp) (fun p => F (Real.log ((p.1:ℝ)/p.2)))]
  apply sum_congr rfl
  intro q hq
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hq
  have hqp := sourceReducedPair_properties (hP p hp)
  have hf : P.filter (fun p' => sourceReducedPair p'=sourceReducedPair p) =
      sourceRatioFiber P (sourceReducedPair p) := by
    ext p'
    simp only [sourceRatioFiber,mem_filter]
    constructor
    · rintro ⟨hp',he⟩
      exact ⟨hp',(sourceReducedPair_eq_iff (hP p' hp') ⟨hqp.1,hqp.2.1⟩ hqp.2.2.1).mp he⟩
    · rintro ⟨hp',he⟩
      exact ⟨hp',(sourceReducedPair_eq_iff (hP p' hp') ⟨hqp.1,hqp.2.1⟩ hqp.2.2.1).mpr he⟩
  calc
    _ = ∑ p' ∈ P.filter (fun p' => sourceReducedPair p'=sourceReducedPair p),
        F (Real.log (((sourceReducedPair p).1:ℝ)/(sourceReducedPair p).2)) := by
      apply sum_congr rfl
      intro p' hp'
      obtain ⟨hp',he⟩ := mem_filter.mp hp'
      rw [← sourceReducedPair_ratio (hP p' hp'),he]
    _ = _ := by rw [hf]; simp

/-- The actual normalized image has all primitive/height properties needed
by the spacing and square-weight budget. -/
theorem source_ratio_image_properties (P : Finset (ℕ × ℕ)) {X : ℕ}
    (hP : ∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧ p.1 ≤ X ∧ p.2 ≤ X) :
    ∀ q ∈ P.image sourceReducedPair,
      0 < q.1 ∧ 0 < q.2 ∧ q.1.Coprime q.2 ∧ max q.1 q.2 ≤ X := by
  intro q hq
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hq
  obtain ⟨hp1,hp2,hpX,hpX'⟩ := hP p hp
  obtain ⟨h₁,h₂,hcop,h₃,h₄⟩ := sourceReducedPair_properties ⟨hp1,hp2⟩
  exact ⟨h₁,h₂,hcop,max_le (h₃.trans hpX) (h₄.trans hpX')⟩

/-- Actual source fibers inherit the full positive-box multiplicity bound. -/
theorem sourceRatioFiber_card {P : Finset (ℕ × ℕ)} {X : ℕ}
    (hP : ∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧ p.1 ≤ X ∧ p.2 ≤ X)
    {q : ℕ × ℕ} (hq : q ∈ P.image sourceReducedPair) :
    (sourceRatioFiber P q).card ≤ X/max q.1 q.2 := by
  have hqp := source_ratio_image_properties P hP q hq
  have hs : sourceRatioFiber P q ⊆ reducedRatioFiber X q.1 q.2 := by
    intro p hp
    obtain ⟨hp,he⟩ := mem_filter.mp hp
    obtain ⟨h₁,h₂,h₃,h₄⟩ := hP p hp
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨h₁,h₃⟩,mem_Icc.mpr ⟨h₂,h₄⟩⟩,he⟩
  exact (card_le_card hs).trans (reducedRatioFiber_card hqp.1 hqp.2.1 hqp.2.2.1)

/-- Exact finite dyadic height decomposition, including the low-height part.
This is a sum identity, not a dyadic-loss estimate. -/
theorem source_height_dyadic_prefix {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (height weight : ι → ℝ) {Y : ℝ} (hY : 0 ≤ Y) (J : ℕ) :
    (∑ q ∈ S.filter (fun q => height q ≤ (2:ℝ)^J*Y), weight q) =
      (∑ q ∈ S.filter (fun q => height q ≤ Y), weight q) +
      ∑ j ∈ range J, ∑ q ∈ S.filter
        (fun q => (2:ℝ)^j*Y < height q ∧ height q ≤ (2:ℝ)^(j+1)*Y), weight q := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hstep : (2:ℝ)^J*Y ≤ (2:ℝ)^(J+1)*Y := by bound
    have hlo : (S.filter (fun q => height q ≤ (2:ℝ)^(J+1)*Y)).filter
        (fun q => height q ≤ (2:ℝ)^J*Y) = S.filter (fun q => height q ≤ (2:ℝ)^J*Y) := by grind
    have hhi : (S.filter (fun q => height q ≤ (2:ℝ)^(J+1)*Y)).filter
        (fun q => ¬height q ≤ (2:ℝ)^J*Y) = S.filter
        (fun q => (2:ℝ)^J*Y < height q ∧ height q ≤ (2:ℝ)^(J+1)*Y) := by
      ext q
      simp only [mem_filter,not_le]
      tauto
    have hh := sum_filter_add_sum_filter_not (S.filter (fun q => height q ≤ (2:ℝ)^(J+1)*Y))
      (fun q => height q ≤ (2:ℝ)^J*Y) weight
    rw [hlo,hhi] at hh
    rw [← hh,ih,sum_range_succ]
    ring

/-- The gcd-normalized source sum has an exact low-plus-dyadic-shell
assembly whenever the chosen last shell covers its actual heights. -/
theorem source_ratio_sum_dyadic (P : Finset (ℕ × ℕ))
    (hP : ∀ p ∈ P, 0 < p.1 ∧ 0 < p.2) (F : ℝ → ℝ) {Y : ℝ}
    (hY : 0 ≤ Y) (J : ℕ)
    (hcover : ∀ q ∈ P.image sourceReducedPair, (max q.1 q.2:ℕ) ≤ (2:ℝ)^J*Y) :
    (∑ p ∈ P, F (Real.log ((p.1:ℝ)/p.2))) =
      (∑ q ∈ (P.image sourceReducedPair).filter (fun q => (max q.1 q.2:ℕ) ≤ Y),
        (sourceRatioFiber P q).card * F (Real.log ((q.1:ℝ)/q.2))) +
      ∑ j ∈ range J, ∑ q ∈ (P.image sourceReducedPair).filter
        (fun q => (2:ℝ)^j*Y < (max q.1 q.2:ℕ) ∧ (max q.1 q.2:ℕ) ≤ (2:ℝ)^(j+1)*Y),
        (sourceRatioFiber P q).card * F (Real.log ((q.1:ℝ)/q.2)) := by
  rw [source_ratio_sum_assembly P hP F]
  have he := source_height_dyadic_prefix (P.image sourceReducedPair)
    (fun q => (max q.1 q.2:ℕ))
    (fun q => (sourceRatioFiber P q).card * F (Real.log ((q.1:ℝ)/q.2))) hY J
  rw [filter_eq_self.mpr hcover] at he
  exact he

def sourceRatioIndices (N : ℝ) : Finset ℕ := Ioc ⌊N⌋₊ ⌊2*N⌋₊

/-- Exact real-parameter source index interval. -/
theorem sourceRatioIndices_mem {N : ℝ} (hN : 0 ≤ N) (n : ℕ) :
    n ∈ sourceRatioIndices N ↔ N < (n:ℝ) ∧ (n:ℝ) ≤ 2*N := by
  simp only [sourceRatioIndices,mem_Ioc,Nat.floor_lt hN,Nat.le_floor_iff (by positivity : 0 ≤ 2*N)]

/-- Source log-ratios lie in a fixed interval with room for disjoint
sampling neighborhoods. -/
theorem source_ratio_log_band {N : ℝ} (hN : 0 ≤ N) {n m : ℕ}
    (hn : n ∈ sourceRatioIndices N) (hm : m ∈ sourceRatioIndices N) :
    |Real.log ((n:ℝ)/m)| ≤ Real.log 2 := by
  obtain ⟨hn,hn'⟩ := (sourceRatioIndices_mem hN n).mp hn
  obtain ⟨hm,hm'⟩ := (sourceRatioIndices_mem hN m).mp hm
  have hn0 : (0:ℝ) < n := hN.trans_lt hn
  have hm0 : (0:ℝ) < m := hN.trans_lt hm
  have hnm : (n:ℝ)/m ≤ 2 := (div_le_iff₀ hm0).mpr (by linarith)
  have hmn : (m:ℝ)/n ≤ 2 := (div_le_iff₀ hn0).mpr (by linarith)
  apply abs_le.mpr
  refine ⟨?_,Real.log_le_log (div_pos hn0 hm0) hnm⟩
  have hh := Real.log_le_log (div_pos hm0 hn0) hmn
  rw [Real.log_div hm0.ne' hn0.ne'] at hh
  rw [Real.log_div hn0.ne' hm0.ne']
  linarith


