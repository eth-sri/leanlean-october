module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.SectorLocalization
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Int.Interval

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.CenteredMomentDyadicCount
open CenteredMomentSectorLocalization

def indices (a b : ℝ)  :=
  Finset.Icc ⌈Real.logb 2 a⌉ ⌊Real.logb 2 (4*b)⌋

section
variable (C R Z a b q ε : ℝ) (hC : 1≤C) (hR : 0≤R) (hZ : 1≤Z) (ha : 0<a) (hb : 0<b) (hab : a≤b) (hq : q∈Icc a b) (n : ℤ)

lemma logb_dyadicScale   : Real.logb 2 (dyadicScale n)=(n:ℝ) := by
  rw [dyadicScale,←Real.rpow_intCast,Real.logb_rpow (by norm_num : (0:ℝ)<2) (by norm_num)]

include ha hb in
lemma mem_indices_iff_scale         :
    n∈indices a b ↔ a≤dyadicScale n ∧ dyadicScale n≤4*b := by
  rw [indices,Finset.mem_Icc,Int.ceil_le,Int.le_floor]
  rw [←logb_dyadicScale n]
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨(Real.logb_le_logb (by norm_num) ha (dyadicScale_pos n)).mp h1,
      (Real.logb_le_logb (by norm_num) (dyadicScale_pos n) (by positivity)).mp h2⟩
  · rintro ⟨h1,h2⟩
    exact ⟨Real.logb_le_logb_of_le (by norm_num) ha h1,
      Real.logb_le_logb_of_le (by norm_num) (dyadicScale_pos n) h2⟩

include ha hab in
lemma mem_indices_iff_whole_support         :
    n∈indices a b ↔ ∃q∈Icc a b,q∈tsupport (dyadicWeight n) := by
  rw [mem_indices_iff_scale a b ha (ha.trans_le hab) n]
  constructor
  · rintro ⟨hlo,hhi⟩
    refine ⟨max a (dyadicScale n/4),⟨le_max_left _ _,max_le hab (by linarith)⟩,?_⟩
    rw [dyadicWeight_tsupport_eq]
    grind
  · rintro ⟨q,hq,hq'⟩
    have hh := dyadicWeight_tsupport n hq'
    exact ⟨hq.1.trans hh.2,by linarith [hq.2,hh.1]⟩

include ha hq in
lemma support_indices      
      (hne : dyadicWeight n q≠0) : n∈indices a b :=
  (mem_indices_iff_whole_support a b ha (hq.1.trans hq.2) n).mpr
    ⟨q,hq,subset_tsupport _ hne⟩

include hb in
lemma logb_four_mul     :
    Real.logb 2 (4*b)=2+Real.logb 2 b := by
  rw [Real.logb_mul (by norm_num) hb.ne']
  congr 1
  rw [show (4:ℝ)=(2:ℝ)^2 by norm_num,Real.logb_pow]
  norm_num [Real.logb_self_eq_one]

include ha hab in
theorem indices_card_bound       :
    ((indices a b).card:ℝ)≤3+Real.logb 2 (b/a) := by
  have hb := ha.trans_le hab
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) ha hab
  have hu := Int.ceil_lt_add_one (Real.logb 2 a)
  have hl := Int.sub_one_lt_floor (Real.logb 2 (4*b))
  have he := logb_four_mul b hb
  have hle : ⌈Real.logb 2 a⌉≤⌊Real.logb 2 (4*b)⌋+1 := by
    have hh : (⌈Real.logb 2 a⌉:ℝ)≤(⌊Real.logb 2 (4*b)⌋:ℝ)+1 := by linarith
    exact_mod_cast hh
  have hcard := Int.card_Icc_of_le _ _ hle
  have hcard' : ((indices a b).card:ℝ)=(⌊Real.logb 2 (4*b)⌋:ℝ)+1-(⌈Real.logb 2 a⌉:ℝ) := by
    exact_mod_cast hcard
  rw [hcard',Real.logb_div hb.ne' ha.ne']
  linarith [Int.floor_le (Real.logb 2 (4*b)),Int.le_ceil (Real.logb 2 a)]

include ha hq in
lemma dyadic_partition_on_interval       :
    (∑n∈indices a b,dyadicWeight n q)=1 := by
  rw [←dyadicWeight_partition q (ha.trans_le hq.1)]
  symm
  apply tsum_eq_sum
  grind [support_indices]

lemma retained_integral_mem   (hq : 1≤q)  n 
    (hr : Retained R n) (hne : dyadicWeight n q≠0) :
    n∈indices 1 (max 1 R) := by
  rw [mem_indices_iff_scale 1 (max 1 R) (by norm_num) (by positivity) n]
  exact ⟨hq.trans (dyadicWeight_support n hne).2.le,
    (retained_scale_le R n hr).trans (by linarith [le_max_right (1:ℝ) R])⟩

include hC hR hZ ha hab in
theorem indices_card_log_bound      
          (hratio : b/a≤C*Z^R) :
    ((indices a b).card:ℝ)≤
      (3+Real.logb 2 C+R/Real.log 2)*(1+Real.log Z) := by
  have hb := ha.trans_le hab
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hCp : 0<C := zero_lt_one.trans_le hC
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (div_pos hb ha) hratio
  rw [Real.logb_mul hCp.ne' (Real.rpow_pos_of_pos hZp R).ne',
    Real.logb_rpow_eq_mul_logb_of_pos hZp] at hlog
  apply (indices_card_bound a b ha hab).trans
  have hc0 := Real.logb_nonneg (by norm_num : (1:ℝ)<2) hC
  have hz0 := Real.log_nonneg hZ
  have hr0 : 0≤R/Real.log 2 := div_nonneg hR (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  have hp := mul_nonneg (show 0≤3+Real.logb 2 C by linarith) hz0
  have he : R*Real.logb 2 Z=(R/Real.log 2)*Real.log Z := by unfold Real.logb;ring
  rw [he] at hlog
  nlinarith

include hC hR in
theorem four_indices_subpower       (hε : 0<ε) :
    ∃D : ℝ,0<D ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ∀a b : Fin 4→ℝ,(∀j,0<a j) → (∀j,a j≤b j) →
      (∀j,b j/a j≤C*Z^R) →
      (Fintype.card (∀j:Fin 4,↥(indices (a j) (b j))):ℝ)≤D*Z^ε := by
  let K : ℝ := 3+Real.logb 2 C+R/Real.log 2
  have hK : 0<K := by
    have hc := Real.logb_nonneg (by norm_num : (1:ℝ)<2) hC
    have hr := div_nonneg hR (Real.log_pos (by norm_num : (1:ℝ)<2)).le
    dsimp [K]
    linarith
  have hlog := (isLittleO_log_rpow_rpow_atTop (4:ℝ) hε).bound (by norm_num : (0:ℝ)<1)
  refine ⟨16*K^4,by positivity,?_⟩
  filter_upwards [hlog,Filter.eventually_ge_atTop (Real.exp 1),Filter.eventually_ge_atTop (1:ℝ)] with Z hlog hZexp hZ
  intro a b ha hab hratio
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hz : 1≤Real.log Z := by
    have hh := Real.log_le_log (Real.exp_pos (1:ℝ)) hZexp
    simpa only [Real.log_exp] using hh
  have hp : (Real.log Z)^4≤Z^ε := by
    apply (le_abs_self _).trans
    simpa only [Real.rpow_ofNat,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hZp.le _),one_mul] using hlog
  have hcard : (Fintype.card (∀j:Fin 4,↥(indices (a j) (b j))):ℝ)≤(K*(1+Real.log Z))^4 := by
    rw [Fintype.card_pi]
    push_cast
    calc
      _ ≤ ∏j:Fin 4,K*(1+Real.log Z) := by
        apply Finset.prod_le_prod₀ (by intros;positivity)
        intro j hj
        simpa only [Fintype.card_coe] using indices_card_log_bound C R Z (a j) (b j) hC hR hZ (ha j) (hab j) (hratio j)
      _ = _ := by simp
  calc
    _ ≤ (K*(1+Real.log Z))^4 := hcard
    _ ≤ (K*(2*Real.log Z))^4 := by gcongr;linarith
    _ = (16*K^4)*(Real.log Z)^4 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

end

end SevenEighths.CenteredMomentDyadicCount

end

end OAI
