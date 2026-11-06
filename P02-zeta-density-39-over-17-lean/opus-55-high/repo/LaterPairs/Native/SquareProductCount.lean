module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.BourgainDyadicBands
public import LaterPairs.Native.DyadicMomentCutoff
public import LaterPairs.Native.ExponentPairShiftUniformity
public import LaterPairs.Native.LogarithmicSixthMoment
public import LaterPairs.Native.SargosDualTentWindow
public import LaterPairs.Native.SargosWithinDerivativeCalculus
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                                

                                                               
                                                             
                                                                           
                                                                         
                                                                    

                                                                   
                                                                           
                                                                           
                                                                        
                                                                              
                                                                                
                                                                             
                                                                          
                                                                      
                                                                        
                                                                          

noncomputable section
open Set MeasureTheory GafniTao
open scoped FourierTransform
namespace TaoTrudgianYang2025.SquareProductCount
open LogarithmicSixth

def logSum (S : Finset ℕ) (p : ℝ × ℝ) : ℂ :=
  ∑ n∈S, fordAdditiveCharacter (p.1*(n:ℝ)^2+p.2*Real.log (n:ℝ))

theorem continuous_logSum (S : Finset ℕ) : Continuous (logSum S) := by
  unfold logSum fordAdditiveCharacter
  fun_prop

theorem logSum_sixth_eq (S : Finset ℕ) (T : ℝ) :
    (∫ p : ℝ × ℝ in Icc (0:ℝ) 1 ×ˢ Icc (-T) T, ‖logSum S p‖^6) =
      logarithmicSixMoment T S (fun _ => 1) (fun n => (n:ℤ)) := by
  have hc : Continuous (fun p => ‖logSum S p‖^6) := (continuous_logSum S).norm.pow 6
  pm_2544 hc.continuousOn.integrableOn_compact
  have hh := integral_prod_symm (fun p => ‖logSum S p‖^6) hi
  rw [Measure.prod_restrict,←Measure.volume_eq_prod] at hh
  pm_89 logSum logarithmicSixMoment one_mul Int.cast_natCast hh

theorem three_mul_prod_le_sum_cube (a : Fin 3 → ℝ) (ha : ∀j, 0 ≤ a j) :
    3*(∏j, a j) ≤ ∑j, (a j)^3 := by
  have hp := mul_nonneg (add_nonneg (add_nonneg (ha 0) (ha 1)) (ha 2))
    (add_nonneg (add_nonneg (sq_nonneg (a 0-a 1)) (sq_nonneg (a 1-a 2)))
      (sq_nonneg (a 2-a 0)))
  simp only [Fin.sum_univ_succ,Fin.prod_univ_succ,
    Fin.sum_univ_zero,Fin.prod_univ_zero,add_zero,mul_one]
  change 3*(a 0*(a 1*a 2)) ≤ a 0^3+(a 1^3+a 2^3)
  nlinarith only [hp]

theorem normalized_triple_bound (a A : Fin 3 → ℝ) (hA : ∀j, 0 < A j) :
    (∏j, a j^2) ≤ (∏j, A j)/3*∑j, a j^6/(A j)^3 := by
  have hh := three_mul_prod_le_sum_cube (fun j => a j^2/A j)
    (fun j => div_nonneg (sq_nonneg _) (hA j).le)
  have hc (j : Fin 3) : (a j^2/A j)^3=a j^6/(A j)^3 := by ring
  simp only [hc,Finset.prod_div_distrib] at hh
  have hpos : 0 < ∏j, A j := Finset.prod_pos (fun j _ => hA j)
  have he : 3*((∏j, a j^2)/(∏j, A j))=(3*(∏j, a j^2))/(∏j, A j) := by ring
  rw [he] at hh
  pm_548 hmul div_le_iff₀ hpos hh

                                                                          
                                                                         
theorem exists_mixed_logarithmic_sixth {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (T : ℝ), 0 ≤ T →
      ∀ (M : Fin 3 → ℕ), (∀j, 1 ≤ M j ∧ M j ≤ N) →
      ∀ (S : Fin 3 → Finset ℕ), (∀j, ∀n∈S j, 1 ≤ n ∧ n ≤ M j) →
      (∫ p : ℝ × ℝ in Icc (0:ℝ) 1 ×ˢ Icc (-T) T,
        ∏j, ‖logSum (S j) p‖^2) ≤
        C*(T+N)*(∏j, (M j:ℝ))^((1:ℝ)+ε) := by
  classical
  obtain ⟨C,hC,h⟩ := exists_logarithmic_sixth (ε:=3*ε) (by positivity)
  refine ⟨C,hC,?_⟩
  intro N _hN T hT M hM S hS
  pm_5329 R T
  let A := fun j => (M j:ℝ)^((1:ℝ)+ε)
  have hM₀ (j : Fin 3) : (0:ℝ) < M j := by exact_mod_cast (by have := (hM j).1; omega : 0 < M j)
  have hA (j : Fin 3) : 0 < A j := Real.rpow_pos_of_pos (hM₀ j) _
  have hAcube (j : Fin 3) : (A j)^3=(M j:ℝ)^((3:ℝ)+3*ε) := by
    dsimp only [A]
    rw [←Real.rpow_mul_natCast (hM₀ j).le]
    congr 1
    ring
  have hint (j : Fin 3) : IntegrableOn (fun p => ‖logSum (S j) p‖^6) R :=
    ((continuous_logSum (S j)).norm.pow 6).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hsingle (j : Fin 3) :
      (∫ p in R, ‖logSum (S j) p‖^6/(A j)^3) ≤ C*(T+N) := by
    have hm (n : ℕ) (hn : n∈S j) : (1:ℤ) ≤ n ∧ (n:ℤ) ≤ M j := by
      exact_mod_cast hS j n hn
    have hz (k : ℤ) :
        (∑ _n∈(S j).filter (fun n : ℕ => (n:ℤ)=k), ‖(1:ℂ)‖) ≤ (1:ℝ) := by
      simp only [norm_one,Finset.sum_const,nsmul_eq_mul,mul_one]
      have hc : ((S j).filter (fun n : ℕ => (n:ℤ)=k)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        pm_8158 he ha hb
        exact_mod_cast he
      exact_mod_cast hc
    have hh := h (M j) (hM j).1 T hT ℕ (S j) (fun _ => 1) (fun n => (n:ℤ)) 1
      (by norm_num) hm hz
    simp only [one_pow,mul_one] at hh
    rw [integral_div,logSum_sixth_eq]
    apply (div_le_iff₀ (pow_pos (hA j) 3)).mpr
    rw [hAcube]
    apply hh.trans
    have hMN : (M j:ℝ) ≤ N := by exact_mod_cast (hM j).2
    gcongr
  have hpoint (p : ℝ × ℝ) :
      (∏j, ‖logSum (S j) p‖^2) ≤
        (∏j, A j)/3*∑j, ‖logSum (S j) p‖^6/(A j)^3 :=
    normalized_triple_bound _ A hA
  have hiSum : IntegrableOn
      (fun p => (∏j, A j)/3*∑j, ‖logSum (S j) p‖^6/(A j)^3) R :=
    (integrable_finsetSum _ (fun j _ => (hint j).div_const _)).const_mul _
  have hmain := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun p => Finset.prod_nonneg
      (fun j (_hj : j∈Finset.univ) => sq_nonneg ‖logSum (S j) p‖))) hiSum
    (Filter.Eventually.of_forall hpoint)
  rw [integral_const_mul,integral_finsetSum _ (fun j _ => (hint j).div_const _)] at hmain
  have hsum := Finset.sum_le_sum (fun j (_hj : j∈Finset.univ) => hsingle j)
  pm_423 Finset.sum_const Finset.card_univ Fintype.card_fin nsmul_eq_mul hsum
  have hprod : (∏j, A j)=(∏j, (M j:ℝ))^((1:ℝ)+ε) := by
    dsimp only [A]
    exact Real.finsetProd_rpow _ _ (fun j _ => (hM₀ j).le) _
  have hbound := hmain.trans (mul_le_mul_of_nonneg_left hsum
    (div_nonneg (Finset.prod_nonneg (fun j _ => (hA j).le)) (by norm_num)))
  rw [hprod] at hbound
  exact hbound.trans_eq (by ring)

def logBoxSquare (q : ℤ) (n : Fin 3 → ℕ) : ℝ := (q:ℝ)+∑j, (n j:ℝ)^2

def logBoxLog (n : Fin 3 → ℕ) : ℝ := ∑j, Real.log (n j:ℝ)

def logBoxSum (q : ℤ) (S : Fin 3 → Finset ℕ) (p : ℝ × ℝ) : ℂ :=
  sargosPlanarSum (Fintype.piFinset S) (fun _ => 1) (logBoxSquare q) logBoxLog p.1 p.2

section
variable (q : ℤ) (S : Fin 3 → Finset ℕ) (p : ℝ × ℝ)
include q S p
theorem logBoxSum_eq_product :
    logBoxSum q S p=fordAdditiveCharacter ((q:ℝ)*p.1)*∏j, logSum (S j) p := by
  classical
  unfold logBoxSum sargosPlanarSum logSum
  rw [Finset.prod_univ_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [sargos_character_finset_prod,←fordAdditiveCharacter_add]
  simp only [one_mul,logBoxSquare,logBoxLog,Finset.sum_add_distrib,
    ←Finset.mul_sum]
  congr 1
  ring

theorem logBoxSum_norm_sq :
    ‖logBoxSum q S p‖^2=∏j, ‖logSum (S j) p‖^2 := by
  pm_502 logBoxSum_eq_product norm_mul sargos_character_norm one_mul norm_prod Finset.prod_pow
end

theorem logSum_periodic (S : Finset ℕ) (t : ℝ) :
    Function.Periodic (fun α => logSum S (α,t)) 1 := by
  intro α
  unfold logSum
  apply Finset.sum_congr rfl
  intro n _hn
  have hk : fordAdditiveCharacter ((n^2:ℕ):ℝ)=1 := by
    unfold fordAdditiveCharacter
    have he : 2*Real.pi*Complex.I*((n^2:ℕ):ℂ)=((n^2:ℕ):ℂ)*(2*Real.pi*Complex.I) := by ring
    rw [Complex.ofReal_natCast,he,Complex.exp_nat_mul_two_pi_mul_I]
  have he : (α+1)*(n:ℝ)^2+t*Real.log (n:ℝ)=
      (α*(n:ℝ)^2+t*Real.log (n:ℝ))+((n^2:ℕ):ℝ) := by push_cast; ring
  rw [he,fordAdditiveCharacter_add,hk,mul_one]

theorem periodic_integral_two (f : ℝ → ℝ) (hf : Continuous f)
    (hp : Function.Periodic f 1) :
    (∫ α : ℝ in Icc (-1:ℝ) 1, f α)=2*∫ α : ℝ in Icc (0:ℝ) 1, f α := by
  rw [integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
  have hh := hp.intervalIntegral_add_zsmul_eq (2:ℤ) (-1)
    (fun a b => hf.intervalIntegrable a b)
  rw [hp.intervalIntegral_add_eq (-1) 0] at hh
  norm_num only [zsmul_eq_mul,Int.cast_ofNat,mul_one,zero_add,neg_add_cancel] at hh
  pm_5646

theorem logBoxSum_central_integral (q : ℤ) (S : Fin 3 → Finset ℕ) (T : ℝ) :
    (∫ α : ℝ in Icc (-1:ℝ) 1, ∫ t : ℝ in Icc (-T) T,
      ‖logBoxSum q S (α,t)‖^2)=
      2*(∫ p : ℝ × ℝ in Icc (0:ℝ) 1 ×ˢ Icc (-T) T,
        ∏j, ‖logSum (S j) p‖^2) := by
  let F := fun p : ℝ × ℝ => ∏j, ‖logSum (S j) p‖^2
  have hc : Continuous F := by unfold F logSum fordAdditiveCharacter; fun_prop
  have hi (a b : ℝ) : Integrable F
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc (-T) T))) := by
    have hh := hc.continuousOn.integrableOn_compact (μ:=volume)
      (isCompact_Icc.prod isCompact_Icc : IsCompact (Icc a b ×ˢ Icc (-T) T))
    rwa [IntegrableOn,Measure.volume_eq_prod,←Measure.prod_restrict] at hh
  have hp (t : ℝ) : Function.Periodic (fun α => F (α,t)) 1 := by
    intro α
    apply Finset.prod_congr rfl
    intro j _hj
    have he := logSum_periodic (S j) t α
    change logSum (S j) (α+1,t)=logSum (S j) (α,t) at he
    rw [he]
  have hinner (t : ℝ) : (∫ α : ℝ in Icc (-1:ℝ) 1, F (α,t))=
      2*∫ α : ℝ in Icc (0:ℝ) 1, F (α,t) :=
    periodic_integral_two _ (hc.comp (continuous_id.prodMk continuous_const)) (hp t)
  simp_rw [logBoxSum_norm_sq]
  change (∫ α : ℝ in Icc (-1:ℝ) 1, ∫ t : ℝ in Icc (-T) T, F (α,t))=_
  rw [←integral_prod _ (hi (-1) 1),integral_prod_symm _ (hi (-1) 1)]
  simp_rw [hinner]
  rw [integral_const_mul,←integral_prod_symm _ (hi 0 1),Measure.prod_restrict,
    ←Measure.volume_eq_prod]

def logBoxFamily (S : Fin 2 → Fin 3 → Finset ℕ) : Finset ((_j : Fin 2) × (Fin 3 → ℕ)) :=
  Finset.univ.sigma (fun j => Fintype.piFinset (S j))

def logBoxFamilySquare (q : Fin 2 → ℤ) (v : (_j : Fin 2) × (Fin 3 → ℕ)) : ℝ :=
  logBoxSquare (q v.1) v.2

def logBoxFamilyLog (v : (_j : Fin 2) × (Fin 3 → ℕ)) : ℝ := logBoxLog v.2

section
variable (q : Fin 2 → ℤ) (S : Fin 2 → Fin 3 → Finset ℕ) (p : ℝ × ℝ)
include q S p
theorem logBoxFamily_sum :
    sargosPlanarSum (logBoxFamily S) (fun _ => 1) (logBoxFamilySquare q) logBoxFamilyLog p.1 p.2=
      ∑j, logBoxSum (q j) (S j) p := by
  pm_162 logBoxFamily logBoxFamilySquare logBoxFamilyLog logBoxSum sargosPlanarSum Finset.sum_sigma

theorem logBoxFamily_norm_sq_le :
    ‖sargosPlanarSum (logBoxFamily S) (fun _ => 1) (logBoxFamilySquare q) logBoxFamilyLog p.1 p.2‖^2 ≤
      2*∑j, ‖logBoxSum (q j) (S j) p‖^2 := by
  rw [logBoxFamily_sum]
  have hn := pow_le_pow_left₀ (norm_nonneg (∑j, logBoxSum (q j) (S j) p))
    (norm_sum_le Finset.univ (fun j => logBoxSum (q j) (S j) p)) 2
  have hh := pow_sum_le_card_mul_sum_pow (s:=Finset.univ)
    (f:=fun j => ‖logBoxSum (q j) (S j) p‖) (fun _ _ => norm_nonneg _) 1
  norm_num only [Finset.card_univ,Fintype.card_fin,Nat.cast_ofNat,pow_one,Nat.reduceAdd] at hh
  exact hn.trans hh
end

theorem continuous_logBoxSum (q : ℤ) (S : Fin 3 → Finset ℕ) :
    Continuous (logBoxSum q S) := by
  have he : logBoxSum q S = fun p => fordAdditiveCharacter ((q:ℝ)*p.1)*∏j, logSum (S j) p :=
    funext (logBoxSum_eq_product q S)
  rw [he]
  apply Continuous.mul
  · unfold fordAdditiveCharacter
    fun_prop
  · exact continuous_finsetProd _ (fun j _ => continuous_logSum (S j))

theorem logBoxFamily_central_le (q : Fin 2 → ℤ)
    (S : Fin 2 → Fin 3 → Finset ℕ) (T : ℝ) :
    (∫ α : ℝ in Icc (-1:ℝ) 1, ∫ t : ℝ in Icc (-T) T,
      ‖sargosPlanarSum (logBoxFamily S) (fun _ => 1)
        (logBoxFamilySquare q) logBoxFamilyLog α t‖^2) ≤
      2*∑j, (∫ α : ℝ in Icc (-1:ℝ) 1, ∫ t : ℝ in Icc (-T) T,
        ‖logBoxSum (q j) (S j) (α,t)‖^2) := by
  let R := Icc (-1:ℝ) 1 ×ˢ Icc (-T) T
  let F := fun p : ℝ × ℝ =>
    ‖sargosPlanarSum (logBoxFamily S) (fun _ => 1)
      (logBoxFamilySquare q) logBoxFamilyLog p.1 p.2‖^2
  let H := fun (j : Fin 2) (p : ℝ × ℝ) => ‖logBoxSum (q j) (S j) p‖^2
  have hFc : Continuous F := by
    have he : F=fun p => ‖∑j, logBoxSum (q j) (S j) p‖^2 := by
      funext p
      dsimp only [F]
      rw [logBoxFamily_sum]
    rw [he]
    exact (continuous_finsetSum _ (fun j _ => continuous_logBoxSum (q j) (S j))).norm.pow 2
  pm_7332 hFi R
  have hHi (j : Fin 2) : IntegrableOn (H j) R :=
    ((continuous_logBoxSum (q j) (S j)).norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hprodF := setIntegral_prod F (s:=Icc (-1:ℝ) 1) (t:=Icc (-T) T) (μ:=volume) (ν:=volume)
    (by simpa only [Measure.volume_eq_prod] using hFi)
  rw [←Measure.volume_eq_prod] at hprodF
  have hprodH (j : Fin 2) := setIntegral_prod (H j) (s:=Icc (-1:ℝ) 1) (t:=Icc (-T) T) (μ:=volume) (ν:=volume)
    (by simpa only [Measure.volume_eq_prod] using hHi j)
  simp only [←Measure.volume_eq_prod] at hprodH
  have himajor : IntegrableOn (fun p => 2*∑j, H j p) R :=
    (integrable_finsetSum _ (fun j _ => hHi j)).const_mul 2
  have hmain : (∫ p in R, F p) ≤ ∫ p in R, 2*∑j, H j p := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun p => sq_nonneg
      ‖sargosPlanarSum (logBoxFamily S) (fun _ => 1)
        (logBoxFamilySquare q) logBoxFamilyLog p.1 p.2‖)) himajor
    (Filter.Eventually.of_forall (logBoxFamily_norm_sq_le q S))
  pm_7396 hHi
  rw [hprodF] at hmain
  dsimp only [R] at hmain
  simp_rw [hprodH] at hmain
  exact hmain

section
variable {ε : ℝ} (hε : 0 < ε)
include ε hε
theorem exists_two_box_central_moment :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (T : ℝ), 0 ≤ T →
      ∀ (M : Fin 2 → Fin 3 → ℕ), (∀j r, 1 ≤ M j r ∧ M j r ≤ N) →
      ∀ (S : Fin 2 → Fin 3 → Finset ℕ), (∀j r, ∀n∈S j r, 1 ≤ n ∧ n ≤ M j r) →
      ∀ (q : Fin 2 → ℤ),
      (∫ α : ℝ in Icc (-1:ℝ) 1, ∫ t : ℝ in Icc (-T) T,
        ‖sargosPlanarSum (logBoxFamily S) (fun _ => 1)
          (logBoxFamilySquare q) logBoxFamilyLog α t‖^2) ≤
        C*(T+N)*∑j, (∏r, (M j r:ℝ))^((1:ℝ)+ε) := by
  pm_1985 h exists_mixed_logarithmic_sixth hε
  intro N hN T hT M hM S hS q
  have hbox (j : Fin 2) :
      (∫ α : ℝ in Icc (-1:ℝ) 1, ∫ t : ℝ in Icc (-T) T,
        ‖logBoxSum (q j) (S j) (α,t)‖^2) ≤
        2*C*(T+N)*(∏r, (M j r:ℝ))^((1:ℝ)+ε) := by
    rw [logBoxSum_central_integral]
    exact (mul_le_mul_of_nonneg_left (h N hN T hT (M j) (hM j) (S j) (hS j))
      (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring)
  have hsum := Finset.sum_le_sum (fun j (_hj : j∈Finset.univ) => hbox j)
  rw [←Finset.mul_sum] at hsum
  exact ((logBoxFamily_central_le q S T).trans
    (mul_le_mul_of_nonneg_left hsum (by norm_num))).trans_eq (by ring)

                                                                     
                                                                          
theorem exists_two_box_log_near_count :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (T : ℝ), 0 < T →
      ∀ (M : Fin 2 → Fin 3 → ℕ), (∀j r, 1 ≤ M j r ∧ M j r ≤ N) →
      ∀ (S : Fin 2 → Fin 3 → Finset ℕ), (∀j r, ∀n∈S j r, 1 ≤ n ∧ n ≤ M j r) →
      ∀ (q : Fin 2 → ℤ),
      ((sargosNearPairs (logBoxFamily S) (logBoxFamilySquare q) logBoxFamilyLog
        (1/2) (1/(2*T))).card : ℝ) ≤
        C*(1+N/T)*∑j, (∏r, (M j r:ℝ))^((1:ℝ)+ε) := by
  pm_7066 exists_two_box_central_moment hε
  intro N hN T hT M hM S hS q
  have hmom := h N hN T hT.le M hM S hS q
  have hk := sargosNearPairs_card_le_central (logBoxFamily S)
    (logBoxFamilySquare q) logBoxFamilyLog (Δ:=2) (μ:=2*T) (by norm_num) (by positivity)
  norm_num only [show (2:ℝ)/2=1 by norm_num,show 2*T/2=T by ring] at hk
  have hcoef : 64/((2:ℝ)*(2*T))=16/T := by field_simp; ring
  rw [hcoef] at hk
  apply hk.trans ((mul_le_mul_of_nonneg_left hmom (by positivity : 0 ≤ 16/T)).trans_eq ?_)
  field_simp
end

def logCrossPairs (S : Fin 2 → Fin 3 → Finset ℕ) (q : Fin 2 → ℤ)
    (δ : ℝ) : Finset ((Fin 3 → ℕ) × (Fin 3 → ℕ)) := by
  classical
  exact ((Fintype.piFinset (S 0)) ×ˢ (Fintype.piFinset (S 1))).filter
    (fun p => logBoxSquare (q 0) p.1=logBoxSquare (q 1) p.2 ∧
      |logBoxLog p.1-logBoxLog p.2| ≤ δ)

theorem logCrossPairs_card_le_near (S : Fin 2 → Fin 3 → Finset ℕ)
    (q : Fin 2 → ℤ) (δ : ℝ) :
    (logCrossPairs S q δ).card ≤
      (sargosNearPairs (logBoxFamily S) (logBoxFamilySquare q) logBoxFamilyLog (1/2) δ).card := by
  classical
  let f := fun p : (Fin 3 → ℕ) × (Fin 3 → ℕ) =>
    ((⟨(0:Fin 2),p.1⟩ : (_j : Fin 2) × (Fin 3 → ℕ)),
      (⟨(1:Fin 2),p.2⟩ : (_j : Fin 2) × (Fin 3 → ℕ)))
  apply Finset.card_le_card_of_injOn f
  · intro p hp
    obtain ⟨hp,he,hlog⟩ := Finset.mem_filter.mp hp
    obtain ⟨hleft,hright⟩ := Finset.mem_product.mp hp
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _,hleft⟩
      · exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _,hright⟩
    · constructor
      · change |logBoxSquare (q 0) p.1-logBoxSquare (q 1) p.2| ≤ (1/2:ℝ)
        rw [he,sub_self,abs_zero]
        norm_num
      · exact hlog
  · intro p _hp r _hr he
    have ha := congrArg (fun v => v.1.2) he
    have hb := congrArg (fun v => v.2.2) he
    exact Prod.ext ha hb

theorem exists_logCrossPairs_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (δ : ℝ), 0 < δ →
      ∀ (M : Fin 2 → Fin 3 → ℕ), (∀j r, 1 ≤ M j r ∧ M j r ≤ N) →
      ∀ (S : Fin 2 → Fin 3 → Finset ℕ), (∀j r, ∀n∈S j r, 1 ≤ n ∧ n ≤ M j r) →
      ∀ (q : Fin 2 → ℤ),
      ((logCrossPairs S q δ).card : ℝ) ≤
        C*(1+N*δ)*∑j, (∏r, (M j r:ℝ))^((1:ℝ)+ε) := by
  pm_416 h exists_two_box_log_near_count
  intro N hN δ hδ M hM S hS q
  have hh := h N hN (1/(2*δ)) (by positivity) M hM S hS q
  have htol : 1/(2*(1/(2*δ)))=δ := by field_simp
  rw [htol] at hh
  have hcard : ((logCrossPairs S q δ).card : ℝ) ≤
      (sargosNearPairs (logBoxFamily S) (logBoxFamilySquare q) logBoxFamilyLog (1/2) δ).card := by
    exact_mod_cast logCrossPairs_card_le_near S q δ
  apply (hcard.trans hh).trans
  have hsum : 0 ≤ ∑j, (∏r, (M j r:ℝ))^((1:ℝ)+ε) :=
    Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (Finset.prod_nonneg (fun r _ => Nat.cast_nonneg _)) _)
  have he : 1+(N:ℝ)/(1/(2*δ))=1+2*N*δ := by field_simp
  rw [he]
  apply mul_le_mul_of_nonneg_right _ hsum
  nlinarith only [hC]

theorem logBoxLog_eq_log_product (n : Fin 3 → ℕ) (hn : ∀j, 1 ≤ n j) :
    logBoxLog n=Real.log (∏j, (n j:ℝ)) := by
  exact (Real.log_prod (fun j _ => (show (0:ℝ) < n j by exact_mod_cast (hn j)).ne')).symm

theorem abs_log_sub_le_gap {a b L P : ℝ} (hL : 0 < L)
    (ha : L ≤ a) (hb : L ≤ b) (hd : |a-b| ≤ P) :
    |Real.log a-Real.log b| ≤ P/L := by
  have ha₀ := hL.trans_le ha
  have hb₀ := hL.trans_le hb
  pm_2279 hP P abs_nonneg hd
  have hside {x y : ℝ} (hx : 0 < x) (hy : L ≤ y) (hdiff : |x-y| ≤ P) :
      Real.log x-Real.log y ≤ P/L := by
    have hy₀ := hL.trans_le hy
    calc
      _ = Real.log (x/y) := (Real.log_div hx.ne' hy₀.ne').symm
      _ ≤ x/y-1 := Real.log_le_sub_one_of_pos (div_pos hx hy₀)
      _ = (x-y)/y := by field_simp
      _ ≤ |x-y|/y := div_le_div_of_nonneg_right (le_abs_self _) hy₀.le
      _ ≤ P/L := by gcongr
  have hab := hside ha₀ hb hd
  have hba := hside hb₀ ha (by simpa only [abs_sub_comm] using hd)
  exact abs_le.mpr ⟨by linarith,hab⟩

theorem logBoxLog_difference_le {a b : Fin 3 → ℕ} (ha : ∀j, 1 ≤ a j)
    (hb : ∀j, 1 ≤ b j) {L P : ℝ} (hL : 0 < L)
    (hpa : L ≤ ∏j, (a j:ℝ)) (hpb : L ≤ ∏j, (b j:ℝ))
    (hd : |(∏j, (a j:ℝ))-(∏j, (b j:ℝ))| ≤ P) :
    |logBoxLog a-logBoxLog b| ≤ P/L := by
  rw [logBoxLog_eq_log_product a ha,logBoxLog_eq_log_product b hb]
  exact abs_log_sub_le_gap hL hpa hpb hd

theorem logBoxLog_mem {N : ℕ} {n : Fin 3 → ℕ}
    (hn : ∀j, 1 ≤ n j ∧ n j ≤ N) : logBoxLog n∈Icc 0 (3*Real.log N) := by
  have hlow (j : Fin 3) : 0 ≤ Real.log (n j:ℝ) :=
    Real.log_nonneg (by exact_mod_cast (hn j).1)
  have hhigh (j : Fin 3) : Real.log (n j:ℝ) ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast (hn j).1) (by exact_mod_cast (hn j).2)
  constructor
  · exact Finset.sum_nonneg (fun j _ => hlow j)
  · have hh := Finset.sum_le_sum (fun j (_hj : j∈Finset.univ) => hhigh j)
    pm_436 logBoxLog Finset.sum_const Finset.card_univ Fintype.card_fin nsmul_eq_mul Nat.cast_ofNat hh

theorem logBoxLog_difference_le_global {N : ℕ} {a b : Fin 3 → ℕ}
    (ha : ∀j, 1 ≤ a j ∧ a j ≤ N) (hb : ∀j, 1 ≤ b j ∧ b j ≤ N) :
    |logBoxLog a-logBoxLog b| ≤ 3*Real.log N := by
  have hA := logBoxLog_mem ha
  have hB := logBoxLog_mem hb
  exact abs_le.mpr ⟨by linarith [hA.1,hB.2],by linarith [hA.2,hB.1]⟩

def boxProduct (n : Fin 3 → ℕ) : ℝ := ∏j, (n j:ℝ)

theorem boxProduct_pos {n : Fin 3 → ℕ} (hn : ∀j, 1 ≤ n j) : 0 < boxProduct n :=
  Finset.prod_pos (fun j _ => by exact_mod_cast hn j)

theorem boxProduct_le_cube {N : ℕ} {n : Fin 3 → ℕ} (hn : ∀j, n j ≤ N) :
    boxProduct n ≤ (N:ℝ)^3 := by
  have hh := Finset.prod_le_prod₀ (s:=Finset.univ)
    (f:=fun j => (n j:ℝ)) (g:=fun _ => (N:ℝ))
    (fun j _ => Nat.cast_nonneg _) (fun j _ => by change (n j:ℝ) ≤ N; exact_mod_cast hn j)
  pm_89 boxProduct Finset.prod_const Finset.card_univ Fintype.card_fin hh

theorem boxProduct_le_square_of_one {N : ℕ} {n : Fin 3 → ℕ}
    (hn : ∀j, n j ≤ N) (hone : ∃j, n j=1) : boxProduct n ≤ (N:ℝ)^2 := by
  obtain ⟨j,hj⟩ := hone
  have hn₀ : (n 0:ℝ) ≤ N := by exact_mod_cast hn 0
  have hn₁ : (n 1:ℝ) ≤ N := by exact_mod_cast hn 1
  have hn₂ : (n 2:ℝ) ≤ N := by exact_mod_cast hn 2
  have hbound {a b : ℝ} (ha₀ : 0 ≤ a) (hb₀ : 0 ≤ b) (ha : a ≤ N) (hb : b ≤ N) :
      a*b ≤ (N:ℝ)^2 := by nlinarith [mul_le_mul ha hb hb₀ (Nat.cast_nonneg N)]
  fin_cases j
  · change n 0=1 at hj
    pm_2021
    pm_5324 one_mul hn₁ hn₂
  · change n 1=1 at hj
    pm_2021
    pm_5324 one_mul hn₀ hn₂
  · change n 2=1 at hj
    pm_2021
    pm_5324 mul_one hn₀ hn₁

theorem boxProduct_comparison {M n : Fin 3 → ℕ}
    (hlow : ∀j, (M j:ℝ) ≤ 2*(n j:ℝ)) (hhigh : ∀j, n j ≤ M j) :
    boxProduct M ≤ 8*boxProduct n ∧ boxProduct n ≤ boxProduct M := by
  constructor
  · have hh := Finset.prod_le_prod₀ (s:=Finset.univ)
      (f:=fun j => (M j:ℝ)) (g:=fun j => 2*(n j:ℝ))
      (fun j _ => Nat.cast_nonneg _) (fun j _ => hlow j)
    rw [Finset.prod_mul_distrib] at hh
    norm_num only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,show (2:ℝ)^3=8 by norm_num] at hh
    exact hh
  · exact Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) (fun j _ => by exact_mod_cast hhigh j)

def zeroAdjustedProduct (z : Bool) (n : Fin 3 → ℕ) : ℝ := if z then 0 else boxProduct n

def zeroAdjustedPairs (S : Fin 2 → Fin 3 → Finset ℕ) (q : Fin 2 → ℤ)
    (z : Fin 2 → Bool) (P : ℝ) : Finset ((Fin 3 → ℕ) × (Fin 3 → ℕ)) := by
  classical
  exact ((Fintype.piFinset (S 0)) ×ˢ (Fintype.piFinset (S 1))).filter
    (fun p => logBoxSquare (q 0) p.1=logBoxSquare (q 1) p.2 ∧
      |zeroAdjustedProduct (z 0) p.1-zeroAdjustedProduct (z 1) p.2| ≤ P)

theorem zeroAdjustedPairs_subset_global (S : Fin 2 → Fin 3 → Finset ℕ)
    (q : Fin 2 → ℤ) (z : Fin 2 → Bool) (P : ℝ) {N : ℕ}
    (hS : ∀j r, ∀n∈S j r, 1 ≤ n ∧ n ≤ N) :
    zeroAdjustedPairs S q z P ⊆ logCrossPairs S q (1+3*Real.log N) := by
  pm_8238 _hprod
  pm_2022
  exact Finset.mem_filter.mpr ⟨hp,hsq,(logBoxLog_difference_le_global ha hb).trans (by linarith)⟩

theorem positive_products_high_log {M : Fin 2 → Fin 3 → ℕ} {a b : Fin 3 → ℕ}
    (ha : ∀r, 1 ≤ a r) (hb : ∀r, 1 ≤ b r)
    (hMa : boxProduct (M 0) ≤ 8*boxProduct a) (hMb : boxProduct (M 1) ≤ 8*boxProduct b)
    {U P : ℝ} (hU : U=max (boxProduct (M 0)) (boxProduct (M 1)))
    (hP : 0 ≤ P) (hlarge : 16*(P+1) < U) (hd : |boxProduct a-boxProduct b| ≤ P) :
    |logBoxLog a-logBoxLog b| ≤ 16*(P+1)/U := by
  have hU₀ : 0 < U := by linarith
  have hab := abs_le.mp hd
  have hmin : U/16 ≤ boxProduct a ∧ U/16 ≤ boxProduct b := by
    rcases le_total (boxProduct (M 0)) (boxProduct (M 1)) with h | h
    pm_8909 max_eq_right
    pm_8909 max_eq_left
  have hh := logBoxLog_difference_le ha hb (show 0 < U/16 by positivity) hmin.1 hmin.2 hd
  have he : P/(U/16)=16*P/U := by ring
  rw [he] at hh
  apply hh.trans
  apply div_le_div_of_nonneg_right _ hU₀.le
  linarith

theorem zero_product_upper {z₀ z₁ : Bool} {U₀ U₁ A B V P : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hV : 0 ≤ V) (hP : 0 ≤ P)
    (hU₀ : U₀ ≤ 8*A) (hU₁ : U₁ ≤ 8*B)
    (hz₀ : z₀=true → U₀ ≤ V) (hz₁ : z₁=true → U₁ ≤ V)
    (hz : z₀=true ∨ z₁=true)
    (hd : |(if z₀ then 0 else A)-(if z₁ then 0 else B)| ≤ P) :
    max U₀ U₁ ≤ V+8*P := by
  cases z₀ <;> cases z₁
  · simp at hz
  · have hu := hz₁ rfl
    have ha : A ≤ P := by simpa only [Bool.false_eq_true,ite_false,ite_true,sub_zero,abs_of_nonneg hA] using hd
    exact max_le (by linarith) (by linarith)
  · have hu := hz₀ rfl
    have hb : B ≤ P := by simpa only [Bool.false_eq_true,ite_false,ite_true,zero_sub,abs_neg,abs_of_nonneg hB] using hd
    exact max_le (by linarith) (by linarith)
  · have hu := hz₀ rfl
    have hv := hz₁ rfl
    exact max_le (by linarith) (by linarith)

theorem zeroAdjustedPairs_subset_high
    (S : Fin 2 → Fin 3 → Finset ℕ) (q : Fin 2 → ℤ) (z : Fin 2 → Bool)
    {M : Fin 2 → Fin 3 → ℕ} {N : ℕ} {P U : ℝ} (hP : 0 ≤ P)
    (hM : ∀j r, M j r ≤ N)
    (hzero : ∀j, z j=true → ∃r, M j r=1)
    (hS : ∀j r, ∀n∈S j r, 1 ≤ n ∧ n ≤ M j r ∧ (M j r:ℝ) ≤ 2*n)
    (hU : U=max (boxProduct (M 0)) (boxProduct (M 1)))
    (hlarge : 16*((N:ℝ)^2+P+1) < U) :
    zeroAdjustedPairs S q z P ⊆ logCrossPairs S q (16*(P+1)/U) := by
  pm_8238 hprod
  pm_2022
  pm_6132 hMa ha
  pm_6132 hMb hb
  have hfalse : z 0=false ∧ z 1=false := by
    have hnot : ¬(z 0=true ∨ z 1=true) := by
      intro hz
      have hu := zero_product_upper (boxProduct_pos (fun r => (ha r).1)).le
        (boxProduct_pos (fun r => (hb r).1)).le (sq_nonneg (N:ℝ)) hP hMa hMb
        (fun h => boxProduct_le_square_of_one (hM 0) (hzero 0 h))
        (fun h => boxProduct_le_square_of_one (hM 1) (hzero 1 h)) hz hprod
      rw [←hU] at hu
      nlinarith [sq_nonneg (N:ℝ)]
    constructor <;> apply Bool.eq_false_iff.mpr
    · exact fun h => hnot (Or.inl h)
    · exact fun h => hnot (Or.inr h)
  have hd : |boxProduct p.1-boxProduct p.2| ≤ P := by
    simpa only [zeroAdjustedProduct,hfalse.1,hfalse.2,Bool.false_eq_true,ite_false] using hprod
  have hh := positive_products_high_log (fun r => (ha r).1) (fun r => (hb r).1)
    hMa hMb hU hP (by nlinarith [sq_nonneg (N:ℝ)]) hd
  exact Finset.mem_filter.mpr ⟨hp,hsq,hh⟩

theorem boxProduct_rpow_budget {N : ℕ} {M : Fin 2 → Fin 3 → ℕ}
    (hM : ∀j r, 1 ≤ M j r ∧ M j r ≤ N) {η : ℝ} (hη : 0 ≤ η)
    {U : ℝ} (hU : U=max (boxProduct (M 0)) (boxProduct (M 1))) :
    (∑j, (boxProduct (M j))^((1:ℝ)+η)) ≤ 2*U*(N:ℝ)^(3*η) := by
  have hupper (j : Fin 2) : boxProduct (M j) ≤ U := by
    rw [hU]
    fin_cases j
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hterm (j : Fin 2) : (boxProduct (M j))^((1:ℝ)+η) ≤ U*(N:ℝ)^(3*η) := by
    have hp := boxProduct_pos (fun r => (hM j r).1)
    have hc := boxProduct_le_cube (fun r => (hM j r).2)
    have hpow := Real.rpow_le_rpow hp.le hc hη
    rw [←Real.rpow_natCast_mul (Nat.cast_nonneg N) 3 η] at hpow
    norm_num only [Nat.cast_ofNat] at hpow
    rw [Real.rpow_add hp,Real.rpow_one]
    exact mul_le_mul (hupper j) hpow (Real.rpow_nonneg hp.le _) (hp.le.trans (hupper j))
  have hh := Finset.sum_le_sum (fun j (_hj : j∈Finset.univ) => hterm j)
  norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hh
  exact hh.trans_eq (by ring)

                                                                      
                                                                         
                                              
theorem exists_zeroAdjustedPairs_box_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (P : ℝ), 0 ≤ P →
      ∀ (M : Fin 2 → Fin 3 → ℕ), (∀j r, 1 ≤ M j r ∧ M j r ≤ N) →
      ∀ (S : Fin 2 → Fin 3 → Finset ℕ),
        (∀j r, ∀n∈S j r, 1 ≤ n ∧ n ≤ M j r ∧ (M j r:ℝ) ≤ 2*n) →
      ∀ (q : Fin 2 → ℤ) (z : Fin 2 → Bool),
        (∀j, z j=true → ∃r, M j r=1) →
      ((zeroAdjustedPairs S q z P).card : ℝ) ≤
        C*((N:ℝ)^2+P+1)*(N:ℝ)^((1:ℝ)+ε)*(1+Real.log N) := by
  obtain ⟨C,hC,h⟩ := exists_logCrossPairs_bound (ε:=ε/3) (by positivity)
  refine ⟨96*C,by positivity,?_⟩
  intro N hN P hP M hM S hS q z hzero
  let U := max (boxProduct (M 0)) (boxProduct (M 1))
  let D := (N:ℝ)^2+P+1
  let K := (N:ℝ)^ε
  let L := 1+Real.log N
  pm_2023
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN₁
  pm_1611 hL L
  pm_64 hD D
  have hK : 0 ≤ K := Real.rpow_nonneg hN₀.le _
  have hU : 0 < U := (boxProduct_pos (fun r => (hM 0 r).1)).trans_le (le_max_left _ _)
  have hUcube : U ≤ (N:ℝ)^3 := max_le
    (boxProduct_le_cube (fun r => (hM 0 r).2)) (boxProduct_le_cube (fun r => (hM 1 r).2))
  have hSbasic (j : Fin 2) (r : Fin 3) (n : ℕ) (hn : n∈S j r) : 1 ≤ n ∧ n ≤ M j r :=
    ⟨(hS j r n hn).1,(hS j r n hn).2.1⟩
  have hsum : (∑j, (∏r, (M j r:ℝ))^((1:ℝ)+ε/3)) ≤ 2*U*K := by
    have hh := boxProduct_rpow_budget hM (show 0 ≤ ε/3 by positivity) (U:=U) rfl
    norm_num only [show (3:ℝ)*(ε/3)=ε by ring] at hh
    exact hh
  have hcommon : ((zeroAdjustedPairs S q z P).card : ℝ) ≤ 96*C*D*N*K*L := by
    by_cases hsmall : U ≤ 16*D
    · let δ := 1+3*Real.log N
      pm_358 hδ δ
      have hsubset := zeroAdjustedPairs_subset_global S q z P
        (fun j r n hn => ⟨(hSbasic j r n hn).1,(hSbasic j r n hn).2.trans (hM j r).2⟩)
      pm_2024
      have hlength : 1+(N:ℝ)*δ ≤ 3*N*L := by dsimp [δ,L]; nlinarith
      have hnum : (1+(N:ℝ)*δ)*(2*U) ≤ (3*N*L)*(32*D) :=
        mul_le_mul hlength (by linarith) (by positivity) (by positivity)
      have hbudget := mul_le_mul_of_nonneg_left hnum (mul_nonneg hC.le hK)
      exact hb.trans (by nlinarith only [hbudget])
    · let δ := 16*(P+1)/U
      pm_64 hδ δ
      have hsubset := zeroAdjustedPairs_subset_high S q z hP (fun j r => (hM j r).2)
        hzero hS (U:=U) rfl (lt_of_not_ge hsmall)
      pm_2024
      have he : C*(1+(N:ℝ)*δ)*(2*U*K)=2*C*(U+16*N*(P+1))*K := by
        dsimp [δ]
        field_simp
      rw [he] at hb
      have hpoly : U+16*(N:ℝ)*(P+1) ≤ 16*D*N := by
        dsimp [D]
        nlinarith [pow_nonneg hN₀.le 3]
      have hb' := hb.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpoly (by positivity : 0 ≤ 2*C)) hK)
      have hbudget : (2*C*(16*D*N))*K ≤ 96*C*D*N*K*L := by
        have hh := mul_le_mul_of_nonneg_left hL (show 0 ≤ 96*C*D*N*K by positivity)
        nlinarith only [hh,mul_nonneg (show 0 ≤ C*D*N by positivity) hK]
      exact hb'.trans hbudget
  have he : (N:ℝ)^((1:ℝ)+ε)=(N:ℝ)*K := by rw [Real.rpow_add hN₀,Real.rpow_one]
  rw [he]
  exact hcommon.trans_eq (by dsimp [D,L]; ring)

def positiveCode (a : ℤ) : ℕ := if a=0 then 1 else a.natAbs

theorem positiveCode_pos (a : ℤ) : 1 ≤ positiveCode a := by
  pm_7462
  · have ha : 0 < a.natAbs := Int.natAbs_pos.mpr h
    simp only [positiveCode,h,ite_false]
    omega

theorem positiveCode_le {N : ℕ} (hN : 1 ≤ N) {a : ℤ} (ha : |a| ≤ N) :
    positiveCode a ≤ N := by
  by_cases h : a=0
  pm_504 positiveCode h ite_true hN
  · simp only [positiveCode,h,ite_false]
    exact_mod_cast (show (a.natAbs:ℤ) ≤ N by rwa [Int.natCast_natAbs])

theorem positiveCode_reconstruct (a : ℤ) :
    a = if a=0 then 0 else if a<0 then -(positiveCode a:ℤ) else (positiveCode a:ℤ) := by
  by_cases h : a=0
  · simp [h]
  · by_cases hs : a<0
    · simp [positiveCode,h,hs,abs_of_neg hs]
    · simp [positiveCode,h,hs,abs_of_nonneg (le_of_not_gt hs)]

theorem positiveCode_square (a : ℤ) :
    (a:ℝ)^2=(positiveCode a:ℝ)^2-(if a=0 then 1 else 0) := by
  pm_7462
  · simp only [positiveCode,h,ite_false,sub_zero]
    have he : (a.natAbs:ℝ)=|(a:ℝ)| := by rw [Nat.cast_natAbs,Int.cast_abs]
    rw [he,sq_abs]

abbrev SignedBoxLabel (N : ℕ) := Bool × Bool × Fin (Nat.log 2 N+1)

def signedBoxLabel (N : ℕ) (a : ℤ) : SignedBoxLabel N :=
  (decide (a=0),decide (a<0),⟨min (Nat.log 2 (positiveCode a)) (Nat.log 2 N),
    (min_le_right _ _).trans_lt (Nat.lt_succ_self _)⟩)

def signedBoxLength (N : ℕ) (l : SignedBoxLabel N) : ℕ :=
  if l.1 then 1 else min N (2^((l.2.2:ℕ)+1))

def signedBoxSet (N : ℕ) (l : SignedBoxLabel N) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (signedBoxLength N l)).filter (fun n => signedBoxLength N l ≤ 2*n)

section
variable {N : ℕ}
include N
theorem signedBoxLength_bounds (hN : 1 ≤ N) (l : SignedBoxLabel N) :
    1 ≤ signedBoxLength N l ∧ signedBoxLength N l ≤ N := by
  unfold signedBoxLength
  split_ifs
  · exact ⟨le_rfl,hN⟩
  · have hp : 0 < (2:ℕ)^((l.2.2:ℕ)+1) := pow_pos (by norm_num) _
    exact ⟨le_min hN (by omega),min_le_left _ _⟩

theorem signedBoxSet_range {l : SignedBoxLabel N} {n : ℕ}
    (hn : n∈signedBoxSet N l) :
    1 ≤ n ∧ n ≤ signedBoxLength N l ∧ (signedBoxLength N l:ℝ) ≤ 2*n := by
  obtain ⟨hn,hh⟩ := Finset.mem_filter.mp hn
  obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hn
  exact ⟨hlo,hhi,by exact_mod_cast hh⟩

theorem positiveCode_mem_signedBox (hN : 1 ≤ N) {a : ℤ} (ha : |a| ≤ N) :
    positiveCode a ∈ signedBoxSet N (signedBoxLabel N a) := by
  have hc := positiveCode_pos a
  have hcN := positiveCode_le hN ha
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_Icc.mpr
    refine ⟨hc,?_⟩
    by_cases hz : a=0
    · simp [signedBoxLength,signedBoxLabel,positiveCode,hz]
    · have hh := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) (positiveCode a)
      simp only [signedBoxLength,signedBoxLabel,hz,decide_false]
      rw [min_eq_left (Nat.log_mono_right hcN)]
      exact le_min hcN hh.le
  · by_cases hz : a=0
    · simp [signedBoxLength,signedBoxLabel,positiveCode,hz]
    · have hh := Nat.pow_log_le_self 2 (by omega : positiveCode a ≠ 0)
      have hm : signedBoxLength N (signedBoxLabel N a) ≤ 2^(Nat.log 2 (positiveCode a)+1) := by
        unfold signedBoxLength
        simp only [signedBoxLabel,hz,decide_false]
        rw [min_eq_left (Nat.log_mono_right hcN)]
        exact min_le_right _ _
      rw [pow_succ] at hm
      omega

theorem positiveCode_inj_of_label {a b : ℤ}
    (hl : signedBoxLabel N a=signedBoxLabel N b) (hc : positiveCode a=positiveCode b) : a=b := by
  have hz : (a=0) ↔ (b=0) := by
    have hh := congrArg (fun l : SignedBoxLabel N => l.1) hl
    simpa only [signedBoxLabel,decide_eq_decide] using hh
  have hs : (a<0) ↔ (b<0) := by
    have hh := congrArg (fun l : SignedBoxLabel N => l.2.1) hl
    simpa only [signedBoxLabel,decide_eq_decide] using hh
  calc
    a = if a=0 then 0 else if a<0 then -(positiveCode a:ℤ) else (positiveCode a:ℤ) := positiveCode_reconstruct a
    _ = if b=0 then 0 else if b<0 then -(positiveCode b:ℤ) else (positiveCode b:ℤ) := by simp only [hz,hs,hc]
    _ = b := (positiveCode_reconstruct b).symm
end

def signedBoxShift {N : ℕ} (l : Fin 3 → SignedBoxLabel N) : ℤ :=
  -(∑r, if (l r).1 then 1 else 0)

def signedBoxZero {N : ℕ} (l : Fin 3 → SignedBoxLabel N) : Bool :=
  decide (∃r, (l r).1=true)

def positiveTriple (a : Fin 3 → ℤ) : Fin 3 → ℕ := fun r => positiveCode (a r)

section
variable {N : ℕ} {a : Fin 3 → ℤ} {l : Fin 3 → SignedBoxLabel N} (hl : ∀r, signedBoxLabel N (a r)=l r)
include N a l hl
theorem signedBoxShift_square :
    logBoxSquare (signedBoxShift l) (positiveTriple a)=∑r, (a r:ℝ)^2 := by
  pm_2025
  have hshift : (signedBoxShift l:ℝ)=-(∑r, if a r=0 then (1:ℝ) else 0) := by
    simp [signedBoxShift,hz]
  have hs : (∑r, (a r:ℝ)^2)=(∑r, (positiveCode (a r):ℝ)^2)-
      ∑r, if a r=0 then (1:ℝ) else 0 := by
    simp_rw [positiveCode_square]
    rw [Finset.sum_sub_distrib]
  rw [hs]
  unfold logBoxSquare positiveTriple
  rw [hshift]
  ring

theorem signedBoxZero_product :
    zeroAdjustedProduct (signedBoxZero l) (positiveTriple a)=|∏r, (a r:ℝ)| := by
  pm_2025
  by_cases h : ∃r, a r=0
  · have hflag : signedBoxZero l=true := by simp [signedBoxZero,hz,h]
    obtain ⟨r,hr⟩ := h
    have hp : (∏r, (a r:ℝ))=0 := Finset.prod_eq_zero (Finset.mem_univ r) (by rw [hr]; norm_num)
    pm_94 zeroAdjustedProduct hflag ite_true hp abs_zero
  · have hn (r : Fin 3) : a r ≠ 0 := fun he => h ⟨r,he⟩
    have hflag : signedBoxZero l=false := by simp [signedBoxZero,hz,h]
    pm_382 zeroAdjustedProduct hflag Bool.false_eq_true ite_false boxProduct positiveTriple
    rw [Finset.abs_prod]
    apply Finset.prod_congr rfl
    intro r _hr
    simp only [positiveCode,hn r,ite_false,Nat.cast_natAbs,Int.cast_abs]
end

theorem signedBoxZero_has_unit {N : ℕ} {l : Fin 3 → SignedBoxLabel N}
    (hz : signedBoxZero l=true) : ∃r, signedBoxLength N (l r)=1 := by
  obtain ⟨r,hr⟩ := of_decide_eq_true hz
  exact ⟨r,by simp only [signedBoxLength,hr,ite_true]⟩

abbrev SignedPair := (Fin 3 → ℤ) × (Fin 3 → ℤ)
abbrev SignedPairLabel (N : ℕ) := (Fin 3 → SignedBoxLabel N) × (Fin 3 → SignedBoxLabel N)

def signedPairLabel (N : ℕ) (p : SignedPair) : SignedPairLabel N :=
  (fun r => signedBoxLabel N (p.1 r),fun r => signedBoxLabel N (p.2 r))

def positivePair (p : SignedPair) : (Fin 3 → ℕ) × (Fin 3 → ℕ) :=
  (positiveTriple p.1,positiveTriple p.2)

def signedLabelRow {N : ℕ} (l : SignedPairLabel N) : Fin 2 → Fin 3 → SignedBoxLabel N := ![l.1,l.2]

section
variable {N : ℕ}
include N
theorem positivePair_mem_box (hN : 1 ≤ N) {P : ℝ}
    {p : SignedPair} {l : SignedPairLabel N} (hl : signedPairLabel N p=l)
    (hbox : ∀r, |p.1 r| ≤ N ∧ |p.2 r| ≤ N)
    (hsq : (∑r, (p.1 r:ℝ)^2)=(∑r, (p.2 r:ℝ)^2))
    (hprod : |(∏r, (p.1 r:ℝ))-(∏r, (p.2 r:ℝ))| ≤ P) :
    positivePair p ∈ zeroAdjustedPairs
      (fun j r => signedBoxSet N (signedLabelRow l j r))
      (fun j => signedBoxShift (signedLabelRow l j))
      (fun j => signedBoxZero (signedLabelRow l j)) P := by
  have hl₀ (r : Fin 3) : signedBoxLabel N (p.1 r)=l.1 r :=
    congrFun (congrArg Prod.fst hl) r
  have hl₁ (r : Fin 3) : signedBoxLabel N (p.2 r)=l.2 r :=
    congrFun (congrArg Prod.snd hl) r
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro r
      have hh := positiveCode_mem_signedBox hN (hbox r).1
      rw [hl₀ r] at hh
      exact hh
    · apply Fintype.mem_piFinset.mpr
      intro r
      have hh := positiveCode_mem_signedBox hN (hbox r).2
      rw [hl₁ r] at hh
      exact hh
  · constructor
    · change logBoxSquare (signedBoxShift l.1) (positiveTriple p.1)=
        logBoxSquare (signedBoxShift l.2) (positiveTriple p.2)
      rw [signedBoxShift_square hl₀,signedBoxShift_square hl₁]
      exact hsq
    · change |zeroAdjustedProduct (signedBoxZero l.1) (positiveTriple p.1)-
        zeroAdjustedProduct (signedBoxZero l.2) (positiveTriple p.2)| ≤ P
      rw [signedBoxZero_product hl₀,signedBoxZero_product hl₁]
      exact (abs_abs_sub_abs_le_abs_sub _ _).trans hprod

theorem positivePair_inj_of_label {p r : SignedPair}
    (hl : signedPairLabel N p=signedPairLabel N r) (hc : positivePair p=positivePair r) : p=r := by
  apply Prod.ext
  pm_6170 Prod.fst
  pm_6170 Prod.snd

theorem signed_fiber_card_le_box (hN : 1 ≤ N) {P : ℝ}
    (Q : Finset SignedPair) (l : SignedPairLabel N)
    (hbox : ∀p∈Q, ∀r, |p.1 r| ≤ N ∧ |p.2 r| ≤ N)
    (hsq : ∀p∈Q, (∑r, (p.1 r:ℝ)^2)=(∑r, (p.2 r:ℝ)^2))
    (hprod : ∀p∈Q, |(∏r, (p.1 r:ℝ))-(∏r, (p.2 r:ℝ))| ≤ P) :
    (Q.filter (fun p => signedPairLabel N p=l)).card ≤
      (zeroAdjustedPairs (fun j r => signedBoxSet N (signedLabelRow l j r))
        (fun j => signedBoxShift (signedLabelRow l j))
        (fun j => signedBoxZero (signedLabelRow l j)) P).card := by
  classical
  apply Finset.card_le_card_of_injOn positivePair
  · intro p hp
    obtain ⟨hp,hl⟩ := Finset.mem_filter.mp hp
    exact positivePair_mem_box hN hl (hbox p hp) (hsq p hp) (hprod p hp)
  · intro p hp r hr he
    pm_8158 hl hp hr
    exact positivePair_inj_of_label hl he
end

theorem signedPairLabel_card (N : ℕ) :
    Fintype.card (SignedPairLabel N)=(4*(Nat.log 2 N+1))^6 := by
  pm_162 SignedPairLabel SignedBoxLabel Fintype.card_prod Fintype.card_fun Fintype.card_bool Fintype.card_fin
  ring

theorem exists_signed_square_product_count_log_loss {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (P : ℝ), 0 ≤ P →
      ∀ (Q : Finset SignedPair),
        (∀p∈Q, ∀r, |p.1 r| ≤ N ∧ |p.2 r| ≤ N) →
        (∀p∈Q, (∑r, (p.1 r:ℝ)^2)=(∑r, (p.2 r:ℝ)^2)) →
        (∀p∈Q, |(∏r, (p.1 r:ℝ))-(∏r, (p.2 r:ℝ))| ≤ P) →
      (Q.card:ℝ) ≤ C*((4*(Nat.log 2 N+1):ℕ):ℝ)^6*
        ((N:ℝ)^2+P+1)*(N:ℝ)^((1:ℝ)+ε)*(1+Real.log N) := by
  classical
  pm_102 C hC h exists_zeroAdjustedPairs_box_bound hε
  intro N hN P hP Q hbox hsq hprod
  have hcell (l : SignedPairLabel N) :
      ((Q.filter (fun p => signedPairLabel N p=l)).card : ℝ) ≤
        C*((N:ℝ)^2+P+1)*(N:ℝ)^((1:ℝ)+ε)*(1+Real.log N) := by
    have hc : ((Q.filter (fun p => signedPairLabel N p=l)).card : ℝ) ≤
        (zeroAdjustedPairs (fun j r => signedBoxSet N (signedLabelRow l j r))
          (fun j => signedBoxShift (signedLabelRow l j))
          (fun j => signedBoxZero (signedLabelRow l j)) P).card := by
      exact_mod_cast signed_fiber_card_le_box hN Q l hbox hsq hprod
    apply hc.trans
    exact h N hN P hP (fun j r => signedBoxLength N (signedLabelRow l j r))
      (fun j r => signedBoxLength_bounds hN _) _ (fun _ _ _ hn => signedBoxSet_range hn)
      _ _ (fun _ hz => signedBoxZero_has_unit hz)
  have he := Finset.card_eq_sum_card_fiberwise (s:=Q) (t:=Finset.univ)
    (f:=signedPairLabel N) (fun p (_hp : p∈Q) => Finset.mem_univ _)
  have her : (Q.card:ℝ)=∑l : SignedPairLabel N, ((Q.filter (fun p => signedPairLabel N p=l)).card : ℝ) := by
    exact_mod_cast he
  rw [her]
  have hh := Finset.sum_le_sum (fun l (_hl : l∈Finset.univ) => hcell l)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,signedPairLabel_card,Nat.cast_pow] at hh
  exact hh.trans_eq (by ring)

theorem signed_label_log_budget {η : ℝ} (hη : 0 < η) {N : ℕ} (hN : 1 ≤ N) :
    (((4*(Nat.log 2 N+1):ℕ):ℝ))^6*(1+Real.log N) ≤
      (8:ℝ)^6*(1+7/η)^7*(N:ℝ)^η := by
  pm_2023
  have hL : 0 ≤ 1+Real.log N := by linarith [Real.log_nonneg hN₁]
  pm_2547
  have hn := Real.natLog_le_logb N 2
  norm_num only [Nat.cast_ofNat,Real.logb] at hn
  have hh := (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mp hn
  pm_7463
  have hc : ((4*(Nat.log 2 N+1):ℕ):ℝ) ≤ 8*(1+Real.log N) := by
    push_cast
    nlinarith only [hh,hmul]
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg (4*(Nat.log 2 N+1))) hc 6
  have hfirst : (((4*(Nat.log 2 N+1):ℕ):ℝ))^6*(1+Real.log N) ≤
      (8:ℝ)^6*(1+Real.log N)^7 :=
    (mul_le_mul_of_nonneg_right hp hL).trans_eq (by ring)
  have hl := one_add_log_le_rpow_budget hN₁ (show 0 < η/7 by positivity)
  have he : 1/(η/7)=7/η := by field_simp
  rw [he] at hl
  have hraised := pow_le_pow_left₀ hL hl 7
  rw [mul_pow,←Real.rpow_mul_natCast hN₀.le] at hraised
  norm_num only [Nat.cast_ofNat,show η/7*7=η by ring] at hraised
  exact hfirst.trans ((mul_le_mul_of_nonneg_left hraised
    (by positivity : (0:ℝ) ≤ 8^6)).trans_eq (by ring))

                                                                          
                                                       
theorem exists_signed_square_product_count {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (P : ℝ), 0 ≤ P →
      ∀ (Q : Finset SignedPair),
        (∀p∈Q, ∀r, |p.1 r| ≤ N ∧ |p.2 r| ≤ N) →
        (∀p∈Q, (∑r, (p.1 r:ℝ)^2)=(∑r, (p.2 r:ℝ)^2)) →
        (∀p∈Q, |(∏r, (p.1 r:ℝ))-(∏r, (p.2 r:ℝ))| ≤ P) →
      (Q.card:ℝ) ≤ C*((N:ℝ)^2+P)*(N:ℝ)^((1:ℝ)+ε) := by
  obtain ⟨C,hC,h⟩ := exists_signed_square_product_count_log_loss (ε:=ε/2) (by positivity)
  let D := (8:ℝ)^6*(1+7/(ε/2))^7
  pm_64 hD D
  refine ⟨2*C*D,by positivity,?_⟩
  intro N hN P hP Q hbox hsq hprod
  pm_2023
  pm_528 hh h N hN P hP Q hbox hsq hprod
  have hbudget := signed_label_log_budget (show 0 < ε/2 by positivity) hN
  change (((4*(Nat.log 2 N+1):ℕ):ℝ))^6*(1+Real.log N) ≤ D*(N:ℝ)^(ε/2) at hbudget
  have he : C*((4*(Nat.log 2 N+1):ℕ):ℝ)^6*((N:ℝ)^2+P+1)*(N:ℝ)^((1:ℝ)+ε/2)*(1+Real.log N)=
      (C*((N:ℝ)^2+P+1)*(N:ℝ)^((1:ℝ)+ε/2))*
        (((4*(Nat.log 2 N+1):ℕ):ℝ)^6*(1+Real.log N)) := by ring
  rw [he] at hh
  pm_738 hm hh.trans hbudget
  have hpow : (N:ℝ)^((1:ℝ)+ε/2)*(N:ℝ)^(ε/2)=(N:ℝ)^((1:ℝ)+ε) := by
    rw [←Real.rpow_add hN₀]
    congr 1
    ring
  have he' : (C*((N:ℝ)^2+P+1)*(N:ℝ)^((1:ℝ)+ε/2))*(D*(N:ℝ)^(ε/2))=
      C*D*((N:ℝ)^2+P+1)*(N:ℝ)^((1:ℝ)+ε) := by
    calc
      _ = C*D*((N:ℝ)^2+P+1)*((N:ℝ)^((1:ℝ)+ε/2)*(N:ℝ)^(ε/2)) := by ring
      _ = _ := by rw [hpow]
  rw [he'] at hm
  have hscale : (N:ℝ)^2+P+1 ≤ 2*((N:ℝ)^2+P) := by nlinarith
  apply hm.trans
  have hs := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale (by positivity : 0 ≤ C*D))
    (Real.rpow_nonneg hN₀.le ((1:ℝ)+ε))
  exact hs.trans_eq (by ring)

namespace CubicEight

def hadamardFour (x : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![x 0+x 1+x 2+x 3, x 0+x 1-x 2-x 3,
    x 0-x 1+x 2-x 3, x 0-x 1-x 2+x 3]

                                                                    
                                                              
theorem hadamardFour_involution (x : Fin 4 → ℤ) :
    hadamardFour (hadamardFour x) = fun i => 4*x i := by
  funext i
  fin_cases i <;> simp [hadamardFour] <;> ring

theorem hadamardFour_injective : Function.Injective hadamardFour := by
  intro x y hxy
  have he := congrArg hadamardFour hxy
  rw [hadamardFour_involution,hadamardFour_involution] at he
  funext i
  have hi := congrFun he i
  omega

                                                                       
theorem hadamardFour_power_sums (x : Fin 4 → ℤ) :
    (∑ i, x i)=hadamardFour x 0 ∧
      4*(∑ i, (x i)^2)=(hadamardFour x 0)^2+(hadamardFour x 1)^2+
        (hadamardFour x 2)^2+(hadamardFour x 3)^2 ∧
      16*(∑ i, (x i)^3)=(hadamardFour x 0)^3+
        3*hadamardFour x 0*((hadamardFour x 1)^2+
          (hadamardFour x 2)^2+(hadamardFour x 3)^2)+
        6*hadamardFour x 1*hadamardFour x 2*hadamardFour x 3 := by
  refine ⟨?_,?_,?_⟩ <;> simp [Fin.sum_univ_succ,hadamardFour] <;> ring

                                                                        
                                                        
section
variable (x y : Fin 4 → ℤ)
include x y
theorem hadamardFour_cubic_resonance
    (hfirst : (∑ i, x i)=∑ i, y i)
    (hsecond : (∑ i, (x i)^2)=∑ i, (y i)^2) :
    hadamardFour x 0=hadamardFour y 0 ∧
      (hadamardFour x 1)^2+(hadamardFour x 2)^2+(hadamardFour x 3)^2 =
        (hadamardFour y 1)^2+(hadamardFour y 2)^2+(hadamardFour y 3)^2 ∧
      3*(hadamardFour x 1*hadamardFour x 2*hadamardFour x 3-
        hadamardFour y 1*hadamardFour y 2*hadamardFour y 3) =
        8*((∑ i, (x i)^3)-∑ i, (y i)^3) := by
  obtain ⟨hx₁,hx₂,hx₃⟩ := hadamardFour_power_sums x
  obtain ⟨hy₁,hy₂,hy₃⟩ := hadamardFour_power_sums y
  have hzero : hadamardFour x 0=hadamardFour y 0 := by omega
  have hsq : (hadamardFour x 1)^2+(hadamardFour x 2)^2+(hadamardFour x 3)^2 =
      (hadamardFour y 1)^2+(hadamardFour y 2)^2+(hadamardFour y 3)^2 := by
    rw [hzero,hsecond] at hx₂
    linarith only [hx₂,hy₂]
  refine ⟨hzero,hsq,?_⟩
  rw [hzero,hsq] at hx₃
  linarith only [hx₃,hy₃]

                                                               
                                             
theorem hadamardFour_near_product {P : ℤ}
    (hfirst : (∑ i, x i)=∑ i, y i)
    (hsecond : (∑ i, (x i)^2)=∑ i, (y i)^2)
    (hthird : |(∑ i, (x i)^3)-∑ i, (y i)^3| ≤ P) :
    3*|hadamardFour x 1*hadamardFour x 2*hadamardFour x 3-
      hadamardFour y 1*hadamardFour y 2*hadamardFour y 3| ≤ 8*P := by
  have he := congrArg abs (hadamardFour_cubic_resonance x y hfirst hsecond).2.2
  simp only [abs_mul,show |(3:ℤ)|=3 by norm_num,show |(8:ℤ)|=8 by norm_num] at he
  linarith only [he,hthird]
end

                                                                 
theorem hadamardFour_abs_le (x : Fin 4 → ℤ) {N : ℤ}
    (hx : ∀ i, |x i| ≤ N) (i : Fin 4) : |hadamardFour x i| ≤ 4*N := by
  have h0 := abs_le.mp (hx 0)
  have h1 := abs_le.mp (hx 1)
  have h2 := abs_le.mp (hx 2)
  have h3 := abs_le.mp (hx 3)
  fin_cases i <;> simp [hadamardFour,abs_le] <;> omega

def sixSquareProductSolutions (N P : ℕ) :
    Finset ((Fin 3 → ℤ) × (Fin 3 → ℤ)) := by
  classical
  let box := Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(N:ℤ)) N)
  exact (box ×ˢ box).filter (fun p => (∑ i, (p.1 i)^2)=∑ i, (p.2 i)^2 ∧
    |p.1 0*p.1 1*p.1 2-p.2 0*p.2 1*p.2 2| ≤ (P:ℤ))

def cubicEightCode (p : (Fin 4 → ℤ) × (Fin 4 → ℤ)) :
    ℤ × ((Fin 3 → ℤ) × (Fin 3 → ℤ)) :=
  (hadamardFour p.1 0,(fun i => hadamardFour p.1 i.succ,
    fun i => hadamardFour p.2 i.succ))

                                                                         
                                                                   
theorem cubicEightCode_injOn :
    Set.InjOn cubicEightCode {p | (∑ i, p.1 i)=∑ i, p.2 i} := by
  intro p hp q hq he
  have h0 := congrArg (fun z => z.1) he
  have h1 := congrArg (fun z => z.2.1) he
  have h2 := congrArg (fun z => z.2.2) he
  have hp₀ : hadamardFour p.1 0=hadamardFour p.2 0 :=
    (hadamardFour_power_sums p.1).1.symm.trans (hp.trans (hadamardFour_power_sums p.2).1)
  have hq₀ : hadamardFour q.1 0=hadamardFour q.2 0 :=
    (hadamardFour_power_sums q.1).1.symm.trans (hq.trans (hadamardFour_power_sums q.2).1)
  apply Prod.ext
  · apply hadamardFour_injective
    pm_7749
    · exact h0
    · exact congrFun h1 j
  · apply hadamardFour_injective
    pm_7749
    · exact hp₀.symm.trans (h0.trans hq₀)
    · exact congrFun h2 j

                                                                     
                                                                             
                                                                       
theorem cubic_eight_count_le_six (N P : ℕ)
    (S : Finset ((Fin 4 → ℤ) × (Fin 4 → ℤ)))
    (hbox : ∀ p∈S, (∀ i, |p.1 i| ≤ (N:ℤ)) ∧ ∀ i, |p.2 i| ≤ (N:ℤ))
    (hfirst : ∀ p∈S, (∑ i, p.1 i)=∑ i, p.2 i)
    (hsecond : ∀ p∈S, (∑ i, (p.1 i)^2)=∑ i, (p.2 i)^2)
    (hthird : ∀ p∈S, |(∑ i, (p.1 i)^3)-∑ i, (p.2 i)^3| ≤ (P:ℤ)) :
    S.card ≤ (8*N+1)*(sixSquareProductSolutions (4*N) (8*P)).card := by
  classical
  let T := Finset.Icc (-4*(N:ℤ)) (4*N) ×ˢ sixSquareProductSolutions (4*N) (8*P)
  have hmaps : Set.MapsTo cubicEightCode S T := by
    intro p hp
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_Icc.mpr (abs_le.mp (hadamardFour_abs_le p.1 (hbox p hp).1 0))
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor
        · apply Fintype.mem_piFinset.mpr
          intro i
          have hh := abs_le.mp (hadamardFour_abs_le p.1 (hbox p hp).1 i.succ)
          pm_6667
        · apply Fintype.mem_piFinset.mpr
          intro i
          have hh := abs_le.mp (hadamardFour_abs_le p.2 (hbox p hp).2 i.succ)
          pm_6667
      · constructor
        · have hh := (hadamardFour_cubic_resonance p.1 p.2
            (hfirst p hp) (hsecond p hp)).2.1
          simpa [cubicEightCode,Fin.sum_univ_succ,←add_assoc] using hh
        · have hh := hadamardFour_near_product p.1 p.2
            (hfirst p hp) (hsecond p hp) (hthird p hp)
          change |hadamardFour p.1 1*hadamardFour p.1 2*hadamardFour p.1 3-
            hadamardFour p.2 1*hadamardFour p.2 2*hadamardFour p.2 3| ≤ ((8*P:ℕ):ℤ)
          push_cast
          linarith [abs_nonneg (hadamardFour p.1 1*hadamardFour p.1 2*hadamardFour p.1 3-
            hadamardFour p.2 1*hadamardFour p.2 2*hadamardFour p.2 3)]
  have hc := Finset.card_le_card_of_injOn cubicEightCode hmaps
    (fun p hp q hq he => cubicEightCode_injOn (hfirst p hp) (hfirst q hq) he)
  have hcard : (Finset.Icc (-4*(N:ℤ)) (4*N)).card=8*N+1 := by
    rw [Int.card_Icc]
    omega
  simpa only [T,Finset.card_product,hcard] using hc


section
variable {ε : ℝ} (hε : 0 < ε)
include ε hε
theorem exists_sixSquareProductSolutions_bound :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (P : ℕ),
      ((sixSquareProductSolutions N P).card : ℝ) ≤
        C*((N:ℝ)^2+P)*(N:ℝ)^((1:ℝ)+ε) := by
  pm_102 C hC h exists_signed_square_product_count hε
  intro N hN P
  apply h N hN P (Nat.cast_nonneg _) (sixSquareProductSolutions N P)
  · intro p hp r
    have hmem := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    exact ⟨abs_le.mpr (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hmem.1 r)),
      abs_le.mpr (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hmem.2 r))⟩
  · intro p hp
    exact_mod_cast (Finset.mem_filter.mp hp).2.1
  · intro p hp
    have hh := (Finset.mem_filter.mp hp).2.2
    have hi : |(∏r, p.1 r)-(∏r, p.2 r)| ≤ (P:ℤ) := by
      simpa [Fin.prod_univ_succ,mul_assoc] using hh
    exact_mod_cast hi

                                                                         
                                                     
theorem exists_cubic_eight_count :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (P : ℕ),
      ∀ (S : Finset ((Fin 4 → ℤ) × (Fin 4 → ℤ))),
        (∀p∈S, (∀r, |p.1 r| ≤ (N:ℤ)) ∧ ∀r, |p.2 r| ≤ (N:ℤ)) →
        (∀p∈S, (∑r, p.1 r)=∑r, p.2 r) →
        (∀p∈S, (∑r, (p.1 r)^2)=∑r, (p.2 r)^2) →
        (∀p∈S, |(∑r, (p.1 r)^3)-∑r, (p.2 r)^3| ≤ (P:ℤ)) →
      (S.card:ℝ) ≤ C*((N:ℝ)^2+P)*(N:ℝ)^((2:ℝ)+ε) := by
  obtain ⟨C,hC,h⟩ := exists_sixSquareProductSolutions_bound hε
  refine ⟨144*C*(4:ℝ)^((1:ℝ)+ε),by positivity,?_⟩
  intro N hN P S hbox hfirst hsecond hthird
  pm_2023
  have hc : (S.card:ℝ) ≤ (8*N+1)*((sixSquareProductSolutions (4*N) (8*P)).card:ℝ) := by
    exact_mod_cast cubic_eight_count_le_six N P S hbox hfirst hsecond hthird
  have hh := h (4*N) (by omega) (8*P)
  norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hh
  pm_738 hm hc.trans hh
  rw [Real.mul_rpow (by norm_num) hN₀.le] at hm
  have hscale : (4*(N:ℝ))^2+8*P ≤ 16*((N:ℝ)^2+P) := by
    nlinarith [(Nat.cast_nonneg P : (0:ℝ) ≤ P)]
  have hlen : 8*(N:ℝ)+1 ≤ 9*N := by linarith
  have hbound : (8*(N:ℝ)+1)*(C*((4*N)^2+8*P)*((4:ℝ)^((1:ℝ)+ε)*(N:ℝ)^((1:ℝ)+ε))) ≤
      (9*N)*(C*(16*((N:ℝ)^2+P))*((4:ℝ)^((1:ℝ)+ε)*(N:ℝ)^((1:ℝ)+ε))) := by gcongr
  apply hm.trans (hbound.trans_eq ?_)
  have he : (N:ℝ)^((2:ℝ)+ε)=(N:ℝ)*(N:ℝ)^((1:ℝ)+ε) := by
    rw [show (2:ℝ)+ε=1+(1+ε) by ring,Real.rpow_add hN₀,Real.rpow_one]
  rw [he]
  ring
end


end CubicEight

namespace CubicMoment
open CubicEight
open scoped ComplexConjugate

theorem integer_carry_separation {a b c d B : ℤ} (hB : 0 < B)
    (hab : |a-b| < B) : a+B*c=b+B*d ↔ a=b ∧ c=d := by
  constructor
  · intro h
    have he : a-b=-(B*(c-d)) := by linarith only [h]
    have ha := congrArg abs he
    rw [abs_neg,abs_mul,abs_of_pos hB] at ha
    have hcd : c=d := by
      by_contra hn
      have hg : 1 ≤ |c-d| := by
        have hp := abs_pos.mpr (sub_ne_zero.mpr hn)
        omega
      have hm := mul_le_mul_of_nonneg_left hg hB.le
      omega
    exact ⟨by rw [hcd] at h; omega,hcd⟩
  · rintro ⟨rfl,rfl⟩
    rfl

def cubicTupleSet (N : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (1:ℤ) N)

def cubicFirst (n : Fin 4 → ℤ) : ℤ := ∑r, n r
def cubicSecond (n : Fin 4 → ℤ) : ℤ := ∑r, (n r)^2
def cubicThird (n : Fin 4 → ℤ) : ℤ := ∑r, (n r)^3
def cubicCombined (N : ℕ) (n : Fin 4 → ℤ) : ℤ := cubicFirst n+(8*(N:ℤ)+1)*cubicSecond n

section
variable {N : ℕ} {n : Fin 4 → ℤ} (hn : n∈cubicTupleSet N)
include N n hn
theorem cubicTuple_abs (r : Fin 4) :
    |n r| ≤ (N:ℤ) := by
  have hh := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hn r)
  rw [abs_of_nonneg (by omega)]
  exact hh.2

theorem cubicFirst_abs :
    |cubicFirst n| ≤ 4*(N:ℤ) := by
  have hh := (Finset.abs_sum_le_sum_abs (s:=Finset.univ) (f:=n)).trans
    (Finset.sum_le_sum (fun r (_hr : r∈Finset.univ) => cubicTuple_abs hn r))
  pm_436 cubicFirst Finset.sum_const Finset.card_univ Fintype.card_fin nsmul_eq_mul Nat.cast_ofNat hh
end

theorem cubicCombined_collision {N : ℕ} {n m : Fin 4 → ℤ}
    (hn : n∈cubicTupleSet N) (hm : m∈cubicTupleSet N) :
    cubicCombined N n=cubicCombined N m ↔ cubicFirst n=cubicFirst m ∧ cubicSecond n=cubicSecond m := by
  have ha := (abs_sub_le (cubicFirst n) 0 (cubicFirst m)).trans
    (add_le_add (by simpa using cubicFirst_abs hn) (by simpa using cubicFirst_abs hm))
  have hb : 0 < 8*(N:ℤ)+1 := by positivity
  exact integer_carry_separation hb (by linarith only [ha])

def cubicSourceSum (N : ℕ) (z : ℤ → ℂ) (α β γ : ℝ) : ℂ :=
  ∑ n∈Finset.Icc (1:ℤ) N,
    z n*fordAdditiveCharacter ((n:ℝ)*α+(n:ℝ)^2*β+(n:ℝ)^3*γ)

def cubicTupleCoefficient (z : ℤ → ℂ) (n : Fin 4 → ℤ) : ℂ := ∏r, z (n r)

theorem cubicSourceSum_fourth (N : ℕ) (z : ℤ → ℂ) (α β γ : ℝ) :
    (cubicSourceSum N z α β γ)^4=
      sargosPlanarSum (cubicTupleSet N)
        (fun n => cubicTupleCoefficient z n*fordAdditiveCharacter ((cubicThird n:ℝ)*γ))
        (fun n => (cubicFirst n:ℝ)) (fun n => (cubicSecond n:ℝ)) α β := by
  classical
  have hp : (cubicSourceSum N z α β γ)^4=∏ _r : Fin 4, cubicSourceSum N z α β γ := by simp
  rw [hp]
  unfold cubicSourceSum
  rw [Finset.prod_univ_sum]
  unfold sargosPlanarSum cubicTupleSet
  apply Finset.sum_congr rfl
  intro n _hn
  rw [Finset.prod_mul_distrib,sargos_character_finset_prod]
  unfold cubicTupleCoefficient
  rw [mul_assoc,←fordAdditiveCharacter_add]
  congr 2
  unfold cubicFirst cubicSecond cubicThird
  push_cast
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.sum_mul,←Finset.sum_mul,←Finset.sum_mul]
  ring

theorem cubicTupleCoefficient_norm {N : ℕ} {z : ℤ → ℂ}
    (hz : ∀n∈Finset.Icc (1:ℤ) N, ‖z n‖ ≤ 1) {n : Fin 4 → ℤ} (hn : n∈cubicTupleSet N) :
    ‖cubicTupleCoefficient z n‖ ≤ 1 := by
  unfold cubicTupleCoefficient
  rw [norm_prod]
  have hh := Finset.prod_le_prod₀ (s:=Finset.univ) (f:=fun r => ‖z (n r)‖) (g:=fun _ => (1:ℝ))
    (fun r _ => norm_nonneg _) (fun r _ => hz _ (Fintype.mem_piFinset.mp hn r))
  simpa only [Finset.prod_const_one] using hh

theorem int_eq_of_real_half_gap {a b : ℤ} (h : |(a:ℝ)-(b:ℝ)| ≤ 1/2) : a=b := by
  have hh : |(a:ℝ)-(b:ℝ)| < 1 := lt_of_le_of_lt h (by norm_num)
  have hi : |a-b| < 1 := by exact_mod_cast hh
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (by omega) (abs_nonneg _)))

theorem exists_cubic_combined_near_count {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (P : ℝ), 0 ≤ P →
      ((sargosNearPairs (cubicTupleSet N) (fun n => (cubicCombined N n:ℝ))
        (fun n => (cubicThird n:ℝ)) (1/2) P).card:ℝ) ≤
        C*((N:ℝ)^2+P)*(N:ℝ)^((2:ℝ)+ε) := by
  pm_416 h exists_cubic_eight_count
  intro N hN P hP
  let S := sargosNearPairs (cubicTupleSet N) (fun n => (cubicCombined N n:ℝ))
    (fun n => (cubicThird n:ℝ)) (1/2) P
  have hbox (p : (Fin 4 → ℤ) × (Fin 4 → ℤ)) (hp : p∈S) :
      (∀r, |p.1 r| ≤ (N:ℤ)) ∧ ∀r, |p.2 r| ≤ (N:ℤ) := by
    have hh := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    exact ⟨cubicTuple_abs hh.1,cubicTuple_abs hh.2⟩
  have hcollision (p : (Fin 4 → ℤ) × (Fin 4 → ℤ)) (hp : p∈S) :
      cubicFirst p.1=cubicFirst p.2 ∧ cubicSecond p.1=cubicSecond p.2 := by
    obtain ⟨hp,hfirst,_hthird⟩ := Finset.mem_filter.mp hp
    have hh := Finset.mem_product.mp hp
    exact (cubicCombined_collision hh.1 hh.2).mp (int_eq_of_real_half_gap hfirst)
  have hthird (p : (Fin 4 → ℤ) × (Fin 4 → ℤ)) (hp : p∈S) :
      |(∑r, (p.1 r)^3)-∑r, (p.2 r)^3| ≤ (⌈P⌉₊:ℤ) := by
    have hh := (Finset.mem_filter.mp hp).2.2
    have hb : |(cubicThird p.1:ℝ)-(cubicThird p.2:ℝ)| ≤ (⌈P⌉₊:ℝ) :=
      hh.trans (Nat.le_ceil P)
    exact_mod_cast hb
  have hh := h N hN ⌈P⌉₊ S hbox (fun p hp => (hcollision p hp).1)
    (fun p hp => (hcollision p hp).2) hthird
  pm_278 hN₁ N hN
  have hceil : (⌈P⌉₊:ℝ) ≤ P+1 := (Nat.ceil_lt_add_one hP).le
  have hscale : (N:ℝ)^2+⌈P⌉₊ ≤ 2*((N:ℝ)^2+P) := by nlinarith
  apply hh.trans
  have hs := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale hC.le)
    (Real.rpow_nonneg (Nat.cast_nonneg N) ((2:ℝ)+ε))
  exact hs.trans_eq (by ring)

end CubicMoment
namespace CubicSource
open CubicMoment
def cubicTuplePoint (n : Fin 4 → ℤ) : Fin 4 → ℝ :=
  ![(cubicFirst n:ℝ),(cubicSecond n:ℝ),(cubicThird n:ℝ),0]

def cubicSamplePoint (α β γ : ℝ) : Fin 4 → ℝ := ![α,β,γ,0]

section
variable (N : ℕ) (z : ℤ → ℂ) (α β γ : ℝ)
include N z α β γ
theorem cubicSourceSum_fourth_four :
    (cubicSourceSum N z α β γ)^4=
      ∑ n∈cubicTupleSet N, cubicTupleCoefficient z n*
        fordAdditiveCharacter (∑ d, cubicTuplePoint n d*cubicSamplePoint α β γ d) := by
  rw [cubicSourceSum_fourth]
  unfold sargosPlanarSum
  apply Finset.sum_congr rfl
  intro n _hn
  rw [mul_assoc,←fordAdditiveCharacter_add]
  congr 2
  simp [cubicTuplePoint,cubicSamplePoint,Fin.sum_univ_succ]
  ring

theorem cubicSourceSum_fract :
    cubicSourceSum N z (Int.fract α) (Int.fract β) γ=cubicSourceSum N z α β γ := by
  unfold cubicSourceSum
  apply Finset.sum_congr rfl
  intro n _hn
  simp only [fordAdditiveCharacter_add]
  rw [sargos_character_integer_fract]
  have hs := sargos_character_integer_fract (n^2) β
  push_cast at hs
  rw [hs]
end

theorem cubic_sample_eighth_sieve {ι : Type*}
    (S : Finset ι) (N : ℕ) (z : ℤ → ℂ) (α β γ : ι → ℝ)
    {a c δ : Fin 4 → ℝ} (ha : ∀ d, 0 < a d) (hδ : ∀ d, 0 < δ d)
    (hz : ∀ n∈Finset.Icc (1:ℤ) N, ‖z n‖ ≤ 1)
    (hx : ∀ i∈S, ∀ d, cubicSamplePoint (α i) (β i) (γ i) d∈Icc (c d) (c d+δ d))
    (hu : ∀ n∈cubicTupleSet N, ∀ d, a d*|cubicTuplePoint n d| ≤ 1/2) :
    (∑ i∈S, ‖cubicSourceSum N z (α i) (β i) (γ i)‖)^8 ≤
      (S.card:ℝ)^6*(16777216*(∏ d, (δ d+2*a d))/(∏ d, a d))*
        (((S ×ˢ S).filter (fun ij => ∀ d,
          |cubicSamplePoint (α ij.1) (β ij.1) (γ ij.1) d-
            cubicSamplePoint (α ij.2) (β ij.2) (γ ij.2) d| ≤ 2*a d)).card:ℝ)*
        ((((cubicTupleSet N) ×ˢ (cubicTupleSet N)).filter (fun ij => ∀ d,
          |cubicTuplePoint ij.1 d-cubicTuplePoint ij.2 d| ≤ 1/(δ d+2*a d))).card:ℝ) := by
  classical
  let A := fun i => cubicSourceSum N z (α i) (β i) (γ i)
  have hs := bourgain_four_dimensional_double_large_sieve_sum_norm S (cubicTupleSet N)
    (cubicTupleCoefficient z) (fun i => cubicSamplePoint (α i) (β i) (γ i))
    cubicTuplePoint ha hδ (fun _ hn => cubicTupleCoefficient_norm hz hn) hx hu
  have he (i : ι) : ‖∑ n∈cubicTupleSet N, cubicTupleCoefficient z n*
      fordAdditiveCharacter (∑ d, cubicTuplePoint n d*cubicSamplePoint (α i) (β i) (γ i) d)‖=
      ‖A i‖^4 := by rw [←cubicSourceSum_fourth_four,norm_pow]
  simp_rw [he] at hs
  have hj := pow_sum_le_card_mul_sum_pow (s:=S)
    (f:=fun i => ‖A i‖) (fun _ _ => norm_nonneg _) 3
  have hsq := pow_le_pow_left₀
    (pow_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) 4) hj 2
  have hm := mul_le_mul_of_nonneg_left hs (pow_nonneg (Nat.cast_nonneg S.card) 6)
  calc
    _ = ((∑ i∈S, ‖A i‖)^4)^2 := by ring
    _ ≤ ((S.card:ℝ)^3*(∑ i∈S, ‖A i‖^4))^2 := hsq
    _ = (S.card:ℝ)^6*(∑ i∈S, ‖A i‖^4)^2 := by ring
    _ ≤ _ := hm.trans_eq (by ring)

theorem cubic_frequency_pairs_subset (N : ℕ) {a δ : Fin 4 → ℝ}
    (ha : ∀ d, 0 < a d)
    (hδ₀ : 2 ≤ δ 0) (hδ₁ : 2 ≤ δ 1) :
    (((cubicTupleSet N) ×ˢ (cubicTupleSet N)).filter (fun ij => ∀ d,
      |cubicTuplePoint ij.1 d-cubicTuplePoint ij.2 d| ≤ 1/(δ d+2*a d))) ⊆
      sargosNearPairs (cubicTupleSet N) (fun n => (cubicCombined N n:ℝ))
        (fun n => (cubicThird n:ℝ)) (1/2) (1/(δ 2+2*a 2)) := by
  pm_477 p hp hnear
  have htol (d : Fin 4) (hd : 2 ≤ δ d) : 1/(δ d+2*a d) ≤ (1/2:ℝ) := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith [ha d]
  have hfirst : cubicFirst p.1=cubicFirst p.2 :=
    int_eq_of_real_half_gap ((hnear 0).trans (htol 0 hδ₀))
  have hsecond : cubicSecond p.1=cubicSecond p.2 :=
    int_eq_of_real_half_gap ((hnear 1).trans (htol 1 hδ₁))
  have hcombined : cubicCombined N p.1=cubicCombined N p.2 := by
    simp only [cubicCombined,hfirst,hsecond]
  apply Finset.mem_filter.mpr
  refine ⟨hp,?_,hnear 2⟩
  simpa only [hcombined,sub_self,abs_zero] using (by norm_num : (0:ℝ) ≤ 1/2)

theorem exists_cubic_frequency_pair_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ N : ℕ, 1 ≤ N → ∀ a δ : Fin 4 → ℝ,
      (∀ d, 0 < a d) → (∀ d, 0 < δ d) → 2 ≤ δ 0 → 2 ≤ δ 1 →
      ((((cubicTupleSet N) ×ˢ (cubicTupleSet N)).filter (fun ij => ∀ d,
        |cubicTuplePoint ij.1 d-cubicTuplePoint ij.2 d| ≤ 1/(δ d+2*a d))).card:ℝ) ≤
        C*((N:ℝ)^2+1/(δ 2+2*a 2))*(N:ℝ)^((2:ℝ)+ε) := by
  pm_102 C hC h exists_cubic_combined_near_count hε
  intro N hN a δ ha hδ hδ₀ hδ₁
  have hc := Finset.card_le_card (cubic_frequency_pairs_subset N ha hδ₀ hδ₁)
  have hwidth : 0 < δ 2+2*a 2 := by linarith [hδ 2,ha 2]
  have hh := h N hN (1/(δ 2+2*a 2)) (by positivity)
  exact (show _ ≤ _ by exact_mod_cast hc).trans hh

theorem cubicTuple_power_abs {N : ℕ} {n : Fin 4 → ℤ}
    (hn : n∈cubicTupleSet N) (k : ℕ) :
    |∑r, (n r:ℝ)^k| ≤ 4*(N:ℝ)^k := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hb (r : Fin 4) : |(n r:ℝ)| ≤ (N:ℝ) := by
    exact_mod_cast cubicTuple_abs hn r
  have hh := Finset.sum_le_sum (s:=(Finset.univ:Finset (Fin 4)))
    (fun r _ => (show |(n r:ℝ)^k| ≤ (N:ℝ)^k by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hb r) k))
  simpa using hh

def cubicSamplingScale (N : ℕ) : Fin 4 → ℝ :=
  ![1/(8*(N:ℝ)),1/(8*(N:ℝ)^2),1/(8*(N:ℝ)^3),1]

def cubicSamplingWidth (μ : ℝ) : Fin 4 → ℝ := ![2,2,μ,1]

theorem cubicSamplingScale_pos {N : ℕ} (hN : 1 ≤ N) (d : Fin 4) :
    0 < cubicSamplingScale N d := by
  pm_2026
  fin_cases d
  · change 0 < 1/(8*(N:ℝ))
    positivity
  · change 0 < 1/(8*(N:ℝ)^2)
    positivity
  · change 0 < 1/(8*(N:ℝ)^3)
    positivity
  · norm_num [cubicSamplingScale]

theorem cubicSamplingWidth_pos {μ : ℝ} (hμ : 0 < μ) (d : Fin 4) :
    0 < cubicSamplingWidth μ d := by
  fin_cases d <;> norm_num [cubicSamplingWidth]
  exact hμ

section
variable {N : ℕ} (hN : 1 ≤ N)
include N hN
theorem cubicTuplePoint_scale
    {n : Fin 4 → ℤ} (hn : n∈cubicTupleSet N) (d : Fin 4) :
    cubicSamplingScale N d*|cubicTuplePoint n d| ≤ 1/2 := by
  pm_2026
  have h₁ : |(cubicFirst n:ℝ)| ≤ 4*(N:ℝ) := by
    simpa [cubicFirst] using cubicTuple_power_abs hn 1
  have h₂ : |(cubicSecond n:ℝ)| ≤ 4*(N:ℝ)^2 := by
    simpa [cubicSecond] using cubicTuple_power_abs hn 2
  have h₃ : |(cubicThird n:ℝ)| ≤ 4*(N:ℝ)^3 := by
    simpa [cubicThird] using cubicTuple_power_abs hn 3
  fin_cases d
  · change 1/(8*(N:ℝ))*|(cubicFirst n:ℝ)| ≤ 1/2
    pm_885
  · change 1/(8*(N:ℝ)^2)*|(cubicSecond n:ℝ)| ≤ 1/2
    pm_885
  · change 1/(8*(N:ℝ)^3)*|(cubicThird n:ℝ)| ≤ 1/2
    pm_885
  · norm_num [cubicSamplingScale,cubicTuplePoint]

theorem cubic_sampling_box_factor {μ : ℝ} (hμ : 0 < μ) :
    ((∏ d, (cubicSamplingWidth μ d+2*cubicSamplingScale N d))/
      (∏ d, cubicSamplingScale N d)) ≤
      7776*(μ+1/(4*(N:ℝ)^3))*(N:ℝ)^6 := by
  pm_2023
  have he : ((∏ d, (cubicSamplingWidth μ d+2*cubicSamplingScale N d))/
      (∏ d, cubicSamplingScale N d)) =
      (16*(N:ℝ)+2)*(16*(N:ℝ)^2+2)*(8*(μ+1/(4*(N:ℝ)^3))*(N:ℝ)^3)*3 := by
    pm_341 cubicSamplingWidth cubicSamplingScale Fin.prod_univ_succ Matrix.cons_val_zero Matrix.cons_val_succ Fin.prod_univ_zero mul_one
    field_simp
    ring
  rw [he]
  have h₁ : 16*(N:ℝ)+2 ≤ 18*(N:ℝ) := by linarith
  have h₂ : 16*(N:ℝ)^2+2 ≤ 18*(N:ℝ)^2 := by nlinarith
  have hh :
      (16*(N:ℝ)+2)*(16*(N:ℝ)^2+2)*(8*(μ+1/(4*(N:ℝ)^3))*(N:ℝ)^3)*3 ≤
      (18*(N:ℝ))*(18*(N:ℝ)^2)*(8*(μ+1/(4*(N:ℝ)^3))*(N:ℝ)^3)*3 := by
    gcongr
  exact hh.trans_eq (by ring)

theorem cubic_sampling_moment_factor {μ ε : ℝ} (hμ : 0 < μ) :
    (μ+1/(4*(N:ℝ)^3))*(N:ℝ)^6*((N:ℝ)^2+1/(μ+1/(4*(N:ℝ)^3)))*
      (N:ℝ)^((2:ℝ)+ε) ≤ 2*(1+μ*(N:ℝ)^2)*(N:ℝ)^((8:ℝ)+ε) := by
  pm_2023
  have hW : 0 < μ+1/(4*(N:ℝ)^3) := by positivity
  have he : (μ+1/(4*(N:ℝ)^3))*((N:ℝ)^2+1/(μ+1/(4*(N:ℝ)^3)))=
      1+μ*(N:ℝ)^2+1/(4*(N:ℝ)) := by field_simp; ring
  have hn : (N:ℝ)^6*(N:ℝ)^((2:ℝ)+ε)=(N:ℝ)^((8:ℝ)+ε) := by
    pm_5470 Real.rpow_natCast hN₀
  have hsmall : 1/(4*(N:ℝ)) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  calc
    _ = ((μ+1/(4*(N:ℝ)^3))*((N:ℝ)^2+1/(μ+1/(4*(N:ℝ)^3))))*
        ((N:ℝ)^6*(N:ℝ)^((2:ℝ)+ε)) := by ring
    _ = (1+μ*(N:ℝ)^2+1/(4*(N:ℝ)))*(N:ℝ)^((8:ℝ)+ε) := by rw [he,hn]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
end

def cubicSamplePairs {ι : Type*} (S : Finset ι) (N : ℕ) (α β γ : ι → ℝ) :
    Finset (ι × ι) := by
  classical
  exact (S ×ˢ S).filter (fun ij => ∀ d,
    |cubicSamplePoint (α ij.1) (β ij.1) (γ ij.1) d-
      cubicSamplePoint (α ij.2) (β ij.2) (γ ij.2) d| ≤ 2*cubicSamplingScale N d)

section
variable {ε : ℝ} (hε : 0 < ε)
include ε hε
theorem exists_cubic_sample_bound :
    ∃ C > (0:ℝ), ∀ (ι : Type) (S : Finset ι) (N : ℕ), 1 ≤ N →
      ∀ (z : ℤ → ℂ) (α β γ : ι → ℝ) (c μ : ℝ), 0 < μ →
      (∀ n∈Finset.Icc (1:ℤ) N, ‖z n‖ ≤ 1) →
      (∀ i∈S, α i∈Icc (0:ℝ) 1 ∧ β i∈Icc (0:ℝ) 1 ∧ γ i∈Icc c (c+μ)) →
      (∑ i∈S, ‖cubicSourceSum N z (α i) (β i) (γ i)‖)^8 ≤
        C*(S.card:ℝ)^6*(cubicSamplePairs S N α β γ).card*
          (1+μ*(N:ℝ)^2)*(N:ℝ)^((8:ℝ)+ε) := by
  obtain ⟨C,hC,hcount⟩ := exists_cubic_frequency_pair_bound hε
  refine ⟨16777216*15552*C,by positivity,?_⟩
  intro ι S N hN z α β γ c μ hμ hz hx
  let a := cubicSamplingScale N
  let δ := cubicSamplingWidth μ
  let W := μ+1/(4*(N:ℝ)^3)
  pm_2026
  pm_116 hW W
  have ha : ∀ d, 0 < a d := cubicSamplingScale_pos hN
  have hδ : ∀ d, 0 < δ d := cubicSamplingWidth_pos hμ
  have hsource : ∀ i∈S, ∀ d,
      cubicSamplePoint (α i) (β i) (γ i) d∈Icc (![0,0,c,0] d) (![0,0,c,0] d+δ d) := by
    intro i hi d
    pm_69 hα hβ hγ hx i hi
    fin_cases d
    · change α i∈Icc (0:ℝ) (0+2)
      exact ⟨hα.1,by linarith [hα.2]⟩
    · change β i∈Icc (0:ℝ) (0+2)
      exact ⟨hβ.1,by linarith [hβ.2]⟩
    · exact hγ
    · norm_num [cubicSamplePoint,δ,cubicSamplingWidth]
  have hs := cubic_sample_eighth_sieve S N z α β γ ha hδ hz hsource
    (fun _ hn d => cubicTuplePoint_scale hN hn d)
  have hwidth : δ 2+2*a 2=W := by
    change μ+2*(1/(8*(N:ℝ)^3))=μ+1/(4*(N:ℝ)^3)
    ring
  have hc := hcount N hN a δ ha hδ (by norm_num [δ,cubicSamplingWidth])
    (by norm_num [δ,cubicSamplingWidth])
  rw [hwidth] at hc
  have hf := cubic_sampling_box_factor hN hμ
  change (∏ d, (δ d+2*a d))/(∏ d, a d) ≤ 7776*W*(N:ℝ)^6 at hf
  have hf' : 16777216*(∏ d, (δ d+2*a d))/(∏ d, a d) ≤
      16777216*7776*W*(N:ℝ)^6 := by
    have hh := mul_le_mul_of_nonneg_left hf (by norm_num : (0:ℝ) ≤ 16777216)
    exact (by convert hh using 1 <;> ring)
  have hmain :
      (∑ i∈S, ‖cubicSourceSum N z (α i) (β i) (γ i)‖)^8 ≤
      (S.card:ℝ)^6*(16777216*7776*W*(N:ℝ)^6)*(cubicSamplePairs S N α β γ).card*
        (C*((N:ℝ)^2+1/W)*(N:ℝ)^((2:ℝ)+ε)) := by
    apply hs.trans
    change (S.card:ℝ)^6*(16777216*(∏ d, (δ d+2*a d))/(∏ d, a d))*
      (cubicSamplePairs S N α β γ).card*_ ≤ _
    gcongr
  have hm := cubic_sampling_moment_factor (ε:=ε) hN hμ
  change W*(N:ℝ)^6*((N:ℝ)^2+1/W)*(N:ℝ)^((2:ℝ)+ε) ≤ _ at hm
  calc
    _ ≤ _ := hmain
    _ = (16777216*7776*C)*(S.card:ℝ)^6*(cubicSamplePairs S N α β γ).card*
        (W*(N:ℝ)^6*((N:ℝ)^2+1/W)*(N:ℝ)^((2:ℝ)+ε)) := by ring
    _ ≤ (16777216*7776*C)*(S.card:ℝ)^6*(cubicSamplePairs S N α β γ).card*
        (2*(1+μ*(N:ℝ)^2)*(N:ℝ)^((8:ℝ)+ε)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

theorem exists_cubic_sample_bound_fract :
    ∃ C > (0:ℝ), ∀ (ι : Type) (S : Finset ι) (N : ℕ), 1 ≤ N →
      ∀ (z : ℤ → ℂ) (α β γ : ι → ℝ) (c μ : ℝ), 0 < μ →
      (∀ n∈Finset.Icc (1:ℤ) N, ‖z n‖ ≤ 1) →
      (∀ i∈S, γ i∈Icc c (c+μ)) →
      (∑ i∈S, ‖cubicSourceSum N z (α i) (β i) (γ i)‖)^8 ≤
        C*(S.card:ℝ)^6*(cubicSamplePairs S N (fun i => Int.fract (α i))
          (fun i => Int.fract (β i)) γ).card*(1+μ*(N:ℝ)^2)*(N:ℝ)^((8:ℝ)+ε) := by
  pm_102 C hC h exists_cubic_sample_bound hε
  intro ι S N hN z α β γ c μ hμ hz hγ
  have hh := h ι S N hN z (fun i => Int.fract (α i)) (fun i => Int.fract (β i)) γ c μ hμ hz
    (fun i hi => ⟨⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩,
      ⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩,hγ i hi⟩)
  simpa only [cubicSourceSum_fract] using hh
end

def cubicPrefixCoefficient (J : ℕ) (n : ℤ) : ℂ := if n ≤ J then 1 else 0

theorem cubicPrefixCoefficient_norm (J : ℕ) (n : ℤ) : ‖cubicPrefixCoefficient J n‖ ≤ 1 := by
  unfold cubicPrefixCoefficient
  split_ifs <;> norm_num

theorem cubicSourceSum_prefix {J N : ℕ} (hJN : J ≤ N) (α β γ : ℝ) :
    cubicSourceSum N (cubicPrefixCoefficient J) α β γ=
      ∑ j∈Finset.range J, fordAdditiveCharacter
        (γ*(1+(j:ℝ))^3+β*(1+(j:ℝ))^2+α*(1+(j:ℝ))) := by
  classical
  unfold cubicSourceSum cubicPrefixCoefficient
  simp only [ite_mul,one_mul,zero_mul,←Finset.sum_filter]
  have hset : (Finset.Icc (1:ℤ) N).filter (fun n => n ≤ (J:ℤ))=
      Finset.Ioc (0:ℤ) (0+(J:ℤ)) := by
    ext n
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ioc]
    omega
  rw [hset]
  have ht := sargos_sum_Ioc_eq_range 0 J (fun n : ℤ =>
    fordAdditiveCharacter ((n:ℝ)*α+(n:ℝ)^2*β+(n:ℝ)^3*γ))
  simp only [Nat.cast_zero] at ht
  pm_5314 ht j _hj
  push_cast
  ring

                                                                   
                                                                        
theorem exists_C4_cubic_sample_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (ι : Type) (S : Finset ι) (f : ι → ℝ → ℝ)
      (m : ι → ℝ) (H : ℕ), 1 ≤ H → ∀ (B c μ : ℝ), 0 ≤ B → 0 < μ →
      B*((H:ℝ)+1)^4 ≤ 1 →
      (∀ i∈S, ∀ y∈Icc (m i-((H:ℝ)+1)) (m i+((H:ℝ)+1)), ContDiffAt ℝ 4 (f i) y) →
      (∀ i∈S, ∀ y∈Icc (m i-((H:ℝ)+1)) (m i+((H:ℝ)+1)), |iteratedDeriv 4 (f i) y| ≤ B) →
      (∀ i∈S, iteratedDeriv 3 (f i) (m i)/6∈Icc c (c+μ)) →
      (∑ i∈S, ‖∑ j∈Finset.range H,
        fordAdditiveCharacter (f i (m i+(1+(j:ℝ))))‖)^8 ≤
      C*(S.card:ℝ)^6*(cubicSamplePairs S H
        (fun i => Int.fract (deriv (f i) (m i)))
        (fun i => Int.fract (iteratedDeriv 2 (f i) (m i)/2))
        (fun i => iteratedDeriv 3 (f i) (m i)/6)).card*
        (1+μ*(H:ℝ)^2)*(H:ℝ)^((8:ℝ)+ε) := by
  obtain ⟨C,hC,h⟩ := exists_cubic_sample_bound_fract hε
  let K := 1+2*Real.pi
  pm_116 hK K
  refine ⟨K^8*C,by positivity,?_⟩
  intro ι S f m H hH B c μ hB hμ hsmall hf hfour hγ
  let L := (H:ℝ)+1
  pm_82 hL L
  have hRange : ∀ x∈Icc (1:ℝ) (1+H), |x| ≤ L := by
    intro x hx
    rw [abs_of_nonneg (by linarith [hx.1] : 0 ≤ x)]
    dsimp only [L]
    linarith [hx.2]
  obtain ⟨J,hJ,hprefix⟩ := bourgain_cubic_taylor_common_prefix S f m
    (fun i => iteratedDeriv 2 (f i) (m i)/2) 1 H hL hB (le_refl (0:ℝ))
    hRange hf hfour (fun _ _ => by simp)
  have hcost : 1+2*Real.pi*H*(B*L^3+2*0*L) ≤ K := by
    have hHL : (H:ℝ) ≤ L := by dsimp only [L]; linarith
    pm_8474 hm mul_le_mul_of_nonneg_right
    have hb : (H:ℝ)*(B*L^3) ≤ 1 := by
      change B*L^4 ≤ 1 at hsmall
      nlinarith
    dsimp only [K]
    nlinarith [Real.pi_pos]
  let A := fun i => cubicSourceSum H (cubicPrefixCoefficient J)
    (deriv (f i) (m i)) (iteratedDeriv 2 (f i) (m i)/2) (iteratedDeriv 3 (f i) (m i)/6)
  have he (i : ι) : (∑ j∈Finset.range J,
      (𝐞 ((iteratedDeriv 3 (f i) (m i)/6)*(1+(j:ℝ))^3+
        (iteratedDeriv 2 (f i) (m i)/2)*(1+(j:ℝ))^2+
          deriv (f i) (m i)*(1+(j:ℝ))) : ℂ))=A i := by
    dsimp only [A]
    rw [cubicSourceSum_prefix hJ]
    simp only [sargos_ford_character_eq_fourier]
  have hsource : (∑ i∈S, ‖∑ j∈Finset.range H,
      fordAdditiveCharacter (f i (m i+(1+(j:ℝ))))‖) ≤ K*∑ i∈S, ‖A i‖ := by
    simp_rw [he] at hprefix
    simp only [←sargos_ford_character_eq_fourier] at hprefix
    pm_8475 hprefix.trans hcost
  have hs := h ι S H hH (cubicPrefixCoefficient J)
    (fun i => deriv (f i) (m i)) (fun i => iteratedDeriv 2 (f i) (m i)/2)
    (fun i => iteratedDeriv 3 (f i) (m i)/6) c μ hμ
    (fun n _hn => cubicPrefixCoefficient_norm J n) hγ
  have hp := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hsource 8
  rw [mul_pow] at hp
  apply hp.trans
  have hh := mul_le_mul_of_nonneg_left hs (pow_nonneg hK.le 8)
  exact hh.trans_eq (by ring)

theorem norm_range_sum_shift_sub (w : ℕ → ℂ) (M n : ℕ)
    (hw : ∀ k, ‖w k‖ ≤ 1) :
    ‖(∑ m∈Finset.range M, w m)-(∑ m∈Finset.range M, w (n+m))‖ ≤ 2*(n:ℝ) := by
  have h₁ := Finset.sum_range_add w M n
  have h₂ := Finset.sum_range_add w n M
  rw [Nat.add_comm n M] at h₂
  have he : (∑ m∈Finset.range M, w m)-(∑ m∈Finset.range M, w (n+m))=
      (∑ k∈Finset.range n, w k)-(∑ k∈Finset.range n, w (M+k)) := by
    linear_combination h₂-h₁
  have hb (b : ℕ) : ‖∑ k∈Finset.range n, w (b+k)‖ ≤ (n:ℝ) := by
    apply (norm_sum_le _ _).trans
    have hh := Finset.sum_le_sum (s:=Finset.range n) (fun k _ => hw (b+k))
    simpa using hh
  rw [he]
  have hzero := hb 0
  simp only [zero_add] at hzero
  exact (norm_sub_le _ _).trans (by linarith [hb M])

theorem source_shift_average_norm (w : ℕ → ℂ) (M H : ℕ)
    (hw : ∀ k, ‖w k‖ ≤ 1) :
    (H:ℝ)*‖∑ m∈Finset.range M, w m‖ ≤
      (∑ m∈Finset.range M, ‖∑ j∈Finset.range H, w (m+(j+1))‖)+2*(H:ℝ)^2 := by
  let A := ∑ m∈Finset.range M, w m
  let Z := ∑ j∈Finset.range H, ∑ m∈Finset.range M, w ((j+1)+m)
  have he : (H:ℂ)*A-Z=
      ∑ j∈Finset.range H, (A-∑ m∈Finset.range M, w ((j+1)+m)) := by
    pm_94 Finset.sum_sub_distrib Finset.sum_const Finset.card_range nsmul_eq_mul Z
  have herr : ‖(H:ℂ)*A-Z‖ ≤ 2*(H:ℝ)^2 := by
    rw [he]
    apply (norm_sum_le _ _).trans
    have hb : (∑ j∈Finset.range H, ‖A-∑ m∈Finset.range M, w ((j+1)+m)‖) ≤
        ∑ _j∈Finset.range H, 2*(H:ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      have hh := norm_range_sum_shift_sub w M (j+1) hw
      have hjH : ((j+1:ℕ):ℝ) ≤ H := by exact_mod_cast (Finset.mem_range.mp hj)
      exact hh.trans (by linarith)
    simpa [pow_two,mul_left_comm] using hb
  have hz : ‖Z‖ ≤ ∑ m∈Finset.range M, ‖∑ j∈Finset.range H, w (m+(j+1))‖ := by
    dsimp only [Z]
    rw [Finset.sum_comm]
    simpa only [Nat.add_comm] using norm_sum_le (Finset.range M)
      (fun m => ∑ j∈Finset.range H, w ((j+1)+m))
  have ht := (norm_sub_le ((H:ℂ)*A-Z) (-Z)).trans (add_le_add herr (by simpa using hz))
  pm_423 sub_neg_eq_add sub_add_cancel norm_mul Complex.norm_natCast ht
  change (H:ℝ)*‖A‖ ≤ _
  linarith

def cubicDerivativePairs (f : ℝ → ℝ) (M H : ℕ) : Finset (ℕ × ℕ) :=
  cubicSamplePairs (Finset.range M) H
    (fun m => Int.fract (deriv f ((m:ℝ)+1)))
    (fun m => Int.fract (iteratedDeriv 2 f ((m:ℝ)+1)/2))
    (fun m => iteratedDeriv 3 f ((m:ℝ)+1)/6)

                                                                       
                                                                               
theorem exists_C4_source_eighth_reduction {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (f : ℝ → ℝ) (M H : ℕ), 1 ≤ H →
      ∀ B c μ : ℝ, 0 ≤ B → 0 < μ → B*((H:ℝ)+1)^4 ≤ 1 →
      (∀ m∈Finset.range M, ∀ y∈Icc ((m:ℝ)-H) ((m:ℝ)+H+2), ContDiffAt ℝ 4 f y) →
      (∀ m∈Finset.range M, ∀ y∈Icc ((m:ℝ)-H) ((m:ℝ)+H+2), |iteratedDeriv 4 f y| ≤ B) →
      (∀ m∈Finset.range M, iteratedDeriv 3 f ((m:ℝ)+1)/6∈Icc c (c+μ)) →
      ‖∑ m∈Finset.range M, fordAdditiveCharacter (f ((m:ℝ)+1))‖^8 ≤
        C*((M:ℝ)^6*(cubicDerivativePairs f M H).card*(1+μ*(H:ℝ)^2)*(H:ℝ)^ε+(H:ℝ)^8) := by
  obtain ⟨C,hC,hfamily⟩ := exists_C4_cubic_sample_bound hε
  refine ⟨128*C+32768,by positivity,?_⟩
  intro f M H hH B c μ hB hμ hsmall hf hfour hγ
  pm_1671 hH₀ H
  let A := ‖∑ m∈Finset.range M, fordAdditiveCharacter (f ((m:ℝ)+1))‖
  let F := ∑ m∈Finset.range M, ‖∑ j∈Finset.range H,
    fordAdditiveCharacter (f ((m:ℝ)+1+(1+(j:ℝ))))‖
  let R := (M:ℝ)^6*(cubicDerivativePairs f M H).card*(1+μ*(H:ℝ)^2)*(H:ℝ)^ε
  pm_82 hR R
  pm_4459 hF F norm_nonneg
  have hshift : (H:ℝ)*A ≤ F+2*(H:ℝ)^2 := by
    have hh := source_shift_average_norm
      (fun n => fordAdditiveCharacter (f ((n:ℝ)+1))) M H
      (fun _ => le_of_eq (sargos_character_norm _))
    have he (m j : ℕ) : (((m+(j+1):ℕ):ℝ)+1)=(m:ℝ)+1+(1+(j:ℝ)) := by push_cast; ring
    simpa only [he] using hh
  have hseg (m : ℕ) (y : ℝ)
      (hy : y∈Icc ((m:ℝ)+1-((H:ℝ)+1)) ((m:ℝ)+1+((H:ℝ)+1))) :
      y∈Icc ((m:ℝ)-H) ((m:ℝ)+H+2) := by
    constructor <;> linarith [hy.1,hy.2]
  have hh := hfamily ℕ (Finset.range M) (fun _ => f) (fun m => (m:ℝ)+1)
    H hH B c μ hB hμ hsmall
    (fun m hm y hy => hf m hm y (hseg m y hy))
    (fun m hm y hy => hfour m hm y (hseg m y hy)) hγ
  have he : (H:ℝ)^((8:ℝ)+ε)=(H:ℝ)^8*(H:ℝ)^ε := by
    rw [Real.rpow_add hH₀]
    norm_num
  have hmain : F^8 ≤ C*(H:ℝ)^8*R := by
    simp only [Finset.card_range] at hh
    change F^8 ≤ C*(M:ℝ)^6*(cubicDerivativePairs f M H).card*
      (1+μ*(H:ℝ)^2)*(H:ℝ)^((8:ℝ)+ε) at hh
    rw [he] at hh
    pm_446 hh.trans_eq R
  have hp := pow_le_pow_left₀ (mul_nonneg hH₀.le (norm_nonneg _)) hshift 8
  have ha := add_pow_le hF (show 0 ≤ 2*(H:ℝ)^2 by positivity) 8
  have hall : (H:ℝ)^8*A^8 ≤ 128*(C*(H:ℝ)^8*R+(2*(H:ℝ)^2)^8) := by
    rw [mul_pow] at hp
    apply hp.trans (ha.trans ?_)
    norm_num only at ⊢
    gcongr
  have hbound : A^8 ≤ 128*C*R+32768*(H:ℝ)^8 := by
    apply (mul_le_mul_iff_right₀ (show 0 < (H:ℝ)^8 by positivity)).mp
    exact hall.trans_eq (by ring)
  change A^8 ≤ (128*C+32768)*(R+(H:ℝ)^8)
  apply hbound.trans
  nlinarith [mul_nonneg hC.le (pow_nonneg hH₀.le 8)]

end CubicSource

end TaoTrudgianYang2025.SquareProductCount


namespace TaoTrudgianYang2025.CubicJointCount

open Set MeasureTheory Expdb Filter GafniTao
open SquareProductCount.CubicSource
open scoped Topology ContDiff NNReal

                                                                       
                                                                       
                                                                        
                                                                      
                                                                       
                                                                       
                                                                  

theorem negative_first_derivative_model
    {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ} (hσ : 0 < σ)
    (hF : IsApproximateModelPhaseFunction F σ (P+1) δ) :
    IsApproximateModelPhaseFunction
      (fun u => -σ⁻¹*iteratedDerivWithin 1 F phaseInterval u)
      (σ+1) P (δ/σ) := by
  refine ⟨contDiffOn_const.mul
    (sargos_contDiffOn_iteratedDerivWithin hF.1 uniqueDiffOn_phaseInterval 1),?_⟩
  intro p hp u
  have hu : 0 < (u:ℝ) := lt_of_lt_of_le zero_lt_one u.property.1
  have hw (τ : ℝ) (n : ℕ) :
      iteratedDerivWithin n (modelPhase τ) phaseInterval u =
        iteratedDeriv n (modelPhase τ) u :=
    iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_phaseInterval
      (Real.contDiffAt_rpow_const_of_ne hu.ne') u.property
  have hm : -σ⁻¹*iteratedDerivWithin (p+1) (modelPhase σ) phaseInterval u =
      iteratedDerivWithin p (modelPhase (σ+1)) phaseInterval u := by
    rw [hw,hw,modelPhase_iteratedDeriv_succ_parameter σ hu]
    field_simp
  have he : modelPhaseErrorAt
      (fun u => -σ⁻¹*iteratedDerivWithin 1 F phaseInterval u) (σ+1) p u =
      -σ⁻¹*modelPhaseErrorAt F σ (p+1) u := by
    rw [modelPhaseErrorAt,iteratedDerivWithin_const_mul_field,
      sargos_iteratedDerivWithin_comp_order,← hm,← mul_sub]
    rfl
  rw [he,norm_mul,Real.norm_eq_abs,abs_neg,
    abs_of_pos (inv_pos.mpr hσ)]
  have h := mul_le_mul_of_nonneg_left (hF.2 (p+1) (by omega) u)
    (inv_nonneg.mpr hσ.le)
  simpa only [div_eq_mul_inv,mul_comm] using h

theorem inverse_slope_shift_stationary_identity
    {σ δ k u : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hu : u∈modelPhaseSlopeRange F) (huk : u+k∈modelPhaseSlopeRange F) :
    let c := modelPhaseInverseSlope F
    let K := fun v => modelPhaseLegendreDual F v-modelPhaseLegendreDual F (v+k)
    let d := c u-c (u+k)
    HasDerivAt K d u ∧
      2*(F (c (u+k))-F (c u)-k*c (u+k)) = -2*(d*u-K u) := by
  intro c K d
  have hleft := modelPhaseLegendreDual_hasDerivAt hσ hδ hF hu
  have hright := (modelPhaseLegendreDual_hasDerivAt hσ hδ hF huk).comp u
    ((hasDerivAt_id u).add_const k)
  refine ⟨?_,?_⟩
  · convert hleft.sub hright using 1
    · rfl
    · simp only [c,d,mul_one]
  · dsimp only [c,K,d,modelPhaseLegendreDual]
    ring

theorem double_dual_physical_scales
    {P V A B τ θ η : ℝ} (hP : 0 < P) (hV : 0 < V)
    (hA : 0 < A) (hB : 0 < B) (hτ : 0 < τ) (hη : 0 < η) (hηone : η < 1) :
    let s := A^(τ-1)/(τ*η)
    let M := B*P/(s*A*(1-η))
    let H := 2*V/(s*B^(θ-1))
    let K := V*A*η/P
    0 < M ∧ 0 < H ∧ 0 < K ∧
      H/M=(2*V/P)*A*(1-η)*B^(-θ) ∧
      M=(B*τ/(A^(τ+1)*(1-η)))*(P^2/V)*K ∧
      ∀ d:ℝ, (s*A*(1-η)*(d/P))/B=d/M ∧
        2*V*(A*η)*(d/P)=2*K*d := by
  intro s M H K
  pm_2028
  have h1 : 0 < 1-η := by linarith
  pm_4365
  pm_2027
  pm_64 hK K
  have hE : B^(θ-1)*B=B^θ := by
    calc
      _ = B^(θ-1)*B^(1:ℝ) := by rw [Real.rpow_one]
      _ = B^((θ-1)+1) := (Real.rpow_add hB _ _).symm
      _ = _ := by congr 1; ring
  have hAexp : A^(τ-1)*A^2=A^(τ+1) := by
    calc
      _ = A^(τ-1)*A^(2:ℝ) := by rw [Real.rpow_two]
      _ = A^((τ-1)+2) := (Real.rpow_add hA _ _).symm
      _ = _ := by congr 1; ring
  refine ⟨hM,hH,hK,?_,?_,?_⟩
  · rw [Real.rpow_neg hB.le]
    dsimp [H,M]
    field_simp
    nlinarith only [hE]
  · rw [← hAexp]
    dsimp [M,K,s]
    field_simp
  · intro d
    dsimp [M,K]
    constructor <;> field_simp

theorem finite_slope_values_retained
    {ι : Type*} (S : Finset ι) {lo hi : ℝ} (hlohi : lo < hi)
    (v : ι → ℝ) (hv : ∀ i∈S, v i ∈ Ioo lo hi) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧ lo+4*h < hi ∧
      ∀ i∈S, v i ∈ Icc (lo+2*h) (hi-2*h) := by
  classical
  let t := S.image (fun i => min (v i-lo) (hi-v i))
  let b := min 1 (hi-lo)
  pm_485 hb b lt_min zero_lt_one sub_pos.mpr hlohi
  let m := (insert b t).min' (Finset.insert_nonempty b t)
  have hm : 0 < m := by
    have hx : m ∈ insert b t := Finset.min'_mem _ _
    rcases Finset.mem_insert.mp hx with hx | hx
    · rw [hx]
      exact hb
    · obtain ⟨i,hiS,he⟩ := Finset.mem_image.mp hx
      rw [← he]
      exact lt_min (sub_pos.mpr (hv i hiS).1) (sub_pos.mpr (hv i hiS).2)
  have hmb : m ≤ b := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have hm₁ : m ≤ 1 := hmb.trans (min_le_left _ _)
  have hmspan : m ≤ hi-lo := hmb.trans (min_le_right _ _)
  refine ⟨m/8,by positivity,by linarith,by linarith,?_⟩
  intro i hiS
  have hmi : m ≤ min (v i-lo) (hi-v i) :=
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,hiS,rfl⟩))
  pm_4998 hl hmi.trans hr
  constructor <;> linarith

theorem moving_legendre_hasDerivAt
    {σ δ A a v h : ℝ} {F : ℝ → ℝ} (Q : ℕ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hA : 0 < A) (ha : 0 < a) (hv : 0 < v) (hh : 0 < h)
    (hret : v ∈ Ioo (modelPhaseClosedSlope F 2+2*h)
      (modelPhaseClosedSlope F 1-2*h)) :
    HasDerivAt (canonicalTaylorLegendrePhase F σ A Q a h)
      (A^(σ⁻¹-1)*modelPhaseInverseSlope F v*A) (v/A) := by
  have hvwin : v ∈ modelPhaseSlopeRange F := by
    rw [modelPhaseSlopeRange_eq_endpoint_Ioo hσ hδ hF]
    constructor <;> linarith [hret.1,hret.2]
  have he : canonicalTaylorLegendrePhase F σ A Q a h =ᶠ[𝓝 (v/A)]
      fun x => A^(σ⁻¹-1)*(modelPhaseLegendreDual F (A*x)-modelPhaseLegendreDual F a)+
        referenceModelPrimitive σ⁻¹ (a/A) := by
    have hc : ContinuousAt (fun x:ℝ => A*x) (v/A) := by fun_prop
    have hn : Ioo (max 0 (modelPhaseClosedSlope F 2+2*h))
        (modelPhaseClosedSlope F 1-2*h) ∈ 𝓝 (A*(v/A)) := by
      rw [mul_div_cancel₀ _ hA.ne']
      exact isOpen_Ioo.mem_nhds ⟨max_lt hv hret.1,hret.2⟩
    filter_upwards [hc.preimage_mem_nhds hn] with x hx
    have hpos : 0 < A*x := lt_of_le_of_lt (le_max_left _ _) hx.1
    have hlow := lt_of_le_of_lt (le_max_right _ _) hx.1
    have hval := canonicalTaylorLegendrePhase_agrees (σ:=σ) Q hA ha hpos hh
      ⟨hlow.le,hx.2.le⟩
    simpa only [mul_div_cancel_left₀ _ hA.ne'] using hval
  have hd₀ : HasDerivAt (modelPhaseLegendreDual F) (modelPhaseInverseSlope F v)
      (A*(v/A)) := by
    simpa only [mul_div_cancel₀ _ hA.ne'] using
      modelPhaseLegendreDual_hasDerivAt hσ hδ hF hvwin
  have hd := hd₀.comp (v/A) ((hasDerivAt_id (v/A)).const_mul A)
  simp only [mul_one] at hd
  convert (((hd.sub_const (modelPhaseLegendreDual F a)).const_mul
    (A^(σ⁻¹-1))).add_const (referenceModelPrimitive σ⁻¹ (a/A))).congr_of_eventuallyEq
      he using 1
  ring

theorem moving_shift_displacement
    {σ δ A a h η y : ℝ} {F : ℝ → ℝ} (Q : ℕ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hA : 0 < A) (ha : 0 < a) (hh : 0 < h)
    (hu : 0 < A*aProcessShiftPoint η 0 y)
    (huk : 0 < A*aProcessShiftPoint η 1 y)
    (hret₀ : A*aProcessShiftPoint η 0 y ∈
      Ioo (modelPhaseClosedSlope F 2+2*h) (modelPhaseClosedSlope F 1-2*h))
    (hret₁ : A*aProcessShiftPoint η 1 y ∈
      Ioo (modelPhaseClosedSlope F 2+2*h) (modelPhaseClosedSlope F 1-2*h)) :
    let u := A*aProcessShiftPoint η 0 y
    let k := A*η
    let d := modelPhaseInverseSlope F u-modelPhaseInverseSlope F (u+k)
    let s := A^(σ⁻¹-1)/(σ⁻¹*η)
    let J := aProcessShiftPhase (canonicalTaylorLegendrePhase F σ A Q a h) σ⁻¹ η
    J y=s*(modelPhaseLegendreDual F u-modelPhaseLegendreDual F (u+k)) ∧
      HasDerivAt J (s*A*(1-η)*d) y := by
  intro u k d s J
  have hcoords : A*aProcessShiftPoint η 1 y = u+k := by
    dsimp [u,k,aProcessShiftPoint]
    ring
  have h0 := canonicalTaylorLegendrePhase_agrees (σ:=σ) Q hA ha hu hh
    ⟨hret₀.1.le,hret₀.2.le⟩
  have h1 := canonicalTaylorLegendrePhase_agrees (σ:=σ) Q hA ha huk hh
    ⟨hret₁.1.le,hret₁.2.le⟩
  simp only [mul_div_cancel_left₀ _ hA.ne'] at h0 h1
  constructor
  · dsimp only [J,aProcessShiftPhase]
    rw [h0,h1,hcoords]
    dsimp [s,u]
    ring
  · have hd (t:ℝ) (ht:0 < A*aProcessShiftPoint η t y)
        (hr:A*aProcessShiftPoint η t y ∈
          Ioo (modelPhaseClosedSlope F 2+2*h) (modelPhaseClosedSlope F 1-2*h)) :
        HasDerivAt
          (fun x => canonicalTaylorLegendrePhase F σ A Q a h (aProcessShiftPoint η t x))
          (A^(σ⁻¹-1)*modelPhaseInverseSlope F (A*aProcessShiftPoint η t y)*A*(1-η)) y := by
      have hv := moving_legendre_hasDerivAt Q hσ hδ hF hA ha ht hh hr
      rw [mul_div_cancel_left₀ _ hA.ne'] at hv
      convert hv.comp y
        (((hasDerivAt_id y).const_mul (1-η)).add_const ((1+t)*η)) using 1
      · rfl
      · ring
    have hj := ((hd 0 hu hret₀).sub (hd 1 huk hret₁)).div_const (σ⁻¹*η)
    rw [hcoords] at hj
    convert hj using 1
    · rfl
    · dsimp only [s,d,u]
      ring

theorem moving_double_dual_resonance
    {σ δ δJ A B a c h g η y : ℝ} {F : ℝ → ℝ} (Q₁ Q₂ : ℕ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hδJ : δJ ≤ min (modelPhaseCurvatureLower (σ⁻¹+1)) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hA : 0 < A) (hB : 0 < B) (ha : 0 < a) (hc : 0 < c)
    (hh : 0 < h) (hg : 0 < g) (hy : y ∈ Ioo (1:ℝ) 2)
    (hu : 0 < A*aProcessShiftPoint η 0 y)
    (huk : 0 < A*aProcessShiftPoint η 1 y)
    (hret₀ : A*aProcessShiftPoint η 0 y ∈
      Ioo (modelPhaseClosedSlope F 2+2*h) (modelPhaseClosedSlope F 1-2*h))
    (hret₁ : A*aProcessShiftPoint η 1 y ∈
      Ioo (modelPhaseClosedSlope F 2+2*h) (modelPhaseClosedSlope F 1-2*h)) :
    let u := A*aProcessShiftPoint η 0 y
    let k := A*η
    let d := modelPhaseInverseSlope F u-modelPhaseInverseSlope F (u+k)
    let s := A^(σ⁻¹-1)/(σ⁻¹*η)
    let J := aProcessShiftPhase (canonicalTaylorLegendrePhase F σ A Q₁ a h) σ⁻¹ η
    let w := s*A*(1-η)*d
    let R := 2*(F (modelPhaseInverseSlope F (u+k))-F (modelPhaseInverseSlope F u)-
      k*modelPhaseInverseSlope F (u+k))
    IsApproximateModelPhaseFunction J (σ⁻¹+1) 1 δJ → 0 < w →
      w ∈ Icc (modelPhaseClosedSlope J 2+2*g) (modelPhaseClosedSlope J 1-2*g) →
      canonicalTaylorLegendrePhase J (σ⁻¹+1) B Q₂ c g (w/B) =
        B^((σ⁻¹+1)⁻¹-1)*(-s/2*R-s*k*d-modelPhaseLegendreDual J c)+
          referenceModelPrimitive (σ⁻¹+1)⁻¹ (c/B) := by
  intro u k d s J w R hJ hw hwret
  have hcoords : A*aProcessShiftPoint η 1 y=u+k := by
    dsimp [u,k,aProcessShiftPoint]
    ring
  obtain ⟨hval,hderiv⟩ := moving_shift_displacement Q₁ hσ hδ hF hA ha hh
    hu huk hret₀ hret₁
  change J y=s*(modelPhaseLegendreDual F u-modelPhaseLegendreDual F (u+k)) at hval
  change HasDerivAt J w y at hderiv
  have hinv : modelPhaseInverseSlope J w=y := by
    rw [← hderiv.deriv]
    exact modelPhaseInverseSlope_deriv (by positivity) hδJ hJ hy
  have huwin : u ∈ modelPhaseSlopeRange F := by
    rw [modelPhaseSlopeRange_eq_endpoint_Ioo hσ hδ hF]
    constructor <;> linarith [hret₀.1,hret₀.2]
  have hukwin : u+k ∈ modelPhaseSlopeRange F := by
    rw [← hcoords,modelPhaseSlopeRange_eq_endpoint_Ioo hσ hδ hF]
    constructor <;> linarith [hret₁.1,hret₁.2]
  have hR := (inverse_slope_shift_stationary_identity hσ hδ hF huwin hukwin).2
  change R = -2*(d*u-(modelPhaseLegendreDual F u-modelPhaseLegendreDual F (u+k))) at hR
  have hdual : modelPhaseLegendreDual J w = -s/2*R-s*k*d := by
    rw [modelPhaseLegendreDual,hinv,hval,hR]
    dsimp [w,u,k,aProcessShiftPoint]
    ring
  rw [canonicalTaylorLegendrePhase_agrees Q₂ hB hc hw hg hwret,hdual]

theorem finite_moving_double_dual_realization
    {σ A B : ℝ} (hσ : 0 < σ) (hA : 0 < A) (hA₂ : A ≤ 2)
    (hB : 0 < B) (hB₂ : B ≤ 2) (Q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∃ P Q₁ : ℕ, 1 ≤ P ∧
        ∀ (F : ℝ → ℝ) (η : ℝ), IsApproximateModelPhaseFunction F σ P δ →
          0 < η → η ≤ η₀ → ∀ (ι : Type*) (S : Finset ι) (y : ι → ℝ),
          (∀ i∈S, y i ∈ Ioo (1:ℝ) 2) →
          (∀ i∈S, A*aProcessShiftPoint η 0 (y i) ∈ modelPhaseSlopeRange F) →
          (∀ i∈S, A*aProcessShiftPoint η 1 (y i) ∈ modelPhaseSlopeRange F) →
          let u := fun i => A*aProcessShiftPoint η 0 (y i)
          let k := A*η
          let d := fun i => modelPhaseInverseSlope F (u i)-modelPhaseInverseSlope F (u i+k)
          let s := A^(σ⁻¹-1)/(σ⁻¹*η)
          let R := fun i => 2*(F (modelPhaseInverseSlope F (u i+k))-
            F (modelPhaseInverseSlope F (u i))-k*modelPhaseInverseSlope F (u i+k))
          ∃ h g : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < g ∧ g ≤ 1 ∧
            let L := canonicalTaylorLegendrePhase F σ A Q₁ (deriv F (3/2)) h
            let J := aProcessShiftPhase L σ⁻¹ η
            let c := deriv J (3/2)
            let G := canonicalTaylorLegendrePhase J (σ⁻¹+1) B Q c g
            IsApproximateModelPhaseFunction G (σ⁻¹+1)⁻¹ Q ε ∧
              (∀ i∈S, s*A*(1-η)*d i∈Icc ((2:ℝ)^(-(σ⁻¹+1))/2) 2) ∧
              ∀ i∈S, G (s*A*(1-η)*d i/B) =
                B^((σ⁻¹+1)⁻¹-1)*(-s/2*R i-s*k*d i-modelPhaseLegendreDual J c)+
                  referenceModelPrimitive (σ⁻¹+1)⁻¹ (c/B) := by
  classical
  have hτ : 0 < σ⁻¹+1 := by positivity
  obtain ⟨δ₂,hδ₂,hsmall₂,hpos₂,hsecond⟩ :=
    canonicalTaylorLegendrePhase_uniformity hτ hB hB₂ Q hε
  let QJ := max 1 (legendreFiniteInputOrder (Q+2))
  obtain ⟨δ₁,η₀,hδ₁,hη₀,hηhalf,hshift⟩ :=
    aProcessShiftPhase_uniform_model (inv_pos.mpr hσ) QJ hδ₂
  obtain ⟨δ,hδ,hsmall,hpos,hfirst⟩ :=
    canonicalTaylorLegendrePhase_uniformity hσ hA hA₂ (QJ+1) hδ₁
  let P := max 1 (legendreFiniteInputOrder ((QJ+1)+2))
  refine ⟨δ,η₀,hδ,hη₀,hηhalf,P,QJ+1,le_max_left _ _,?_⟩
  intro F η hF hη hηle ι S y hy hu huk u k d s R
  pm_7306 hF₁ hF le_max_left
  pm_7306 hFQ hF le_max_right
  have hwin := modelPhaseSlopeRange_eq_endpoint_Ioo hσ hsmall hF₁
  have hpositive {v:ℝ} (hv:v∈modelPhaseSlopeRange F) : 0 < v :=
    lt_of_lt_of_le (by positivity : (0:ℝ) < (2:ℝ)^(-σ)/2)
      (modelPhaseSlopeRange_positive_window hσ hpos hF hv).1
  have ha : deriv F (3/2) ∈ modelPhaseSlopeRange F := ⟨3/2,by norm_num,rfl⟩
  have hai := ha
  rw [hwin] at hai
  let U := S.image u ∪ S.image (fun i => A*aProcessShiftPoint η 1 (y i))
  have hU : ∀ v∈U, v ∈ Ioo (modelPhaseClosedSlope F 2) (modelPhaseClosedSlope F 1) := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    pm_6389 hu
    pm_6389 huk
  obtain ⟨b,hb,hb₁,hgap,hvalues⟩ := finite_slope_values_retained U
    (lt_trans hai.1 hai.2) id hU
  have hh : 0 < b/2 := by positivity
  have hh₁ : b/2 ≤ 1 := by linarith
  have hhgap : modelPhaseClosedSlope F 2+4*(b/2) < modelPhaseClosedSlope F 1 := by
    linarith
  have hret₀ (i:ι) (hi:i∈S) : A*aProcessShiftPoint η 0 (y i) ∈
      Ioo (modelPhaseClosedSlope F 2+2*(b/2)) (modelPhaseClosedSlope F 1-2*(b/2)) := by
    have hv := hvalues (u i) (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩))
    change modelPhaseClosedSlope F 2+2*b ≤ u i ∧ u i ≤ modelPhaseClosedSlope F 1-2*b at hv
    change modelPhaseClosedSlope F 2+2*(b/2) < u i ∧ u i < modelPhaseClosedSlope F 1-2*(b/2)
    constructor <;> linarith [hv.1,hv.2]
  have hret₁ (i:ι) (hi:i∈S) : A*aProcessShiftPoint η 1 (y i) ∈
      Ioo (modelPhaseClosedSlope F 2+2*(b/2)) (modelPhaseClosedSlope F 1-2*(b/2)) := by
    have hv := hvalues _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩))
    change modelPhaseClosedSlope F 2+2*b ≤ A*aProcessShiftPoint η 1 (y i) ∧
      A*aProcessShiftPoint η 1 (y i) ≤ modelPhaseClosedSlope F 1-2*b at hv
    constructor <;> linarith [hv.1,hv.2]
  let L := canonicalTaylorLegendrePhase F σ A (QJ+1) (deriv F (3/2)) (b/2)
  let J := aProcessShiftPhase L σ⁻¹ η
  have hL := hfirst F hFQ _ ha (b/2) hh hh₁ hhgap
  have hJ := hshift L η hL hη hηle
  pm_7306 hJ₁ hJ le_max_left
  pm_7306 hJQ hJ le_max_right
  let w := fun i => s*A*(1-η)*d i
  have hw (i:ι) (hi:i∈S) : w i ∈ modelPhaseSlopeRange J := by
    have hd := (moving_shift_displacement (QJ+1) hσ hsmall hF₁ hA
      (hpositive ha) hh (hpositive (hu i hi)) (hpositive (huk i hi))
      (hret₀ i hi) (hret₁ i hi)).2
    exact ⟨y i,hy i hi,hd.deriv⟩
  pm_8319
  have hc : c ∈ modelPhaseSlopeRange J := ⟨3/2,by norm_num,rfl⟩
  have hwinJ := modelPhaseSlopeRange_eq_endpoint_Ioo hτ hsmall₂ hJ₁
  change modelPhaseSlopeRange J = Ioo (modelPhaseClosedSlope J 2)
    (modelPhaseClosedSlope J 1) at hwinJ
  have hci := hc
  rw [hwinJ] at hci
  have hpositiveJ {v:ℝ} (hv:v∈modelPhaseSlopeRange J) : 0 < v :=
    lt_of_lt_of_le (by positivity : (0:ℝ) < (2:ℝ)^(-(σ⁻¹+1))/2)
      (modelPhaseSlopeRange_positive_window hτ hpos₂ hJ hv).1
  obtain ⟨g,hg,hg₁,hgapJ,hvaluesJ⟩ := finite_slope_values_retained S
    (lt_trans hci.1 hci.2) w (fun i hi => by simpa only [hwinJ] using hw i hi)
  refine ⟨b/2,g,hh,hh₁,hg,hg₁,?_,?_,?_⟩
  · exact hsecond J hJQ c hc g hg hg₁ hgapJ
  · intro i hi
    exact modelPhaseSlopeRange_positive_window hτ hpos₂ hJ (hw i hi)
  · intro i hi
    exact moving_double_dual_resonance (QJ+1) Q hσ hsmall hsmall₂ hF₁
      hA hB (hpositive ha) (hpositiveJ hc) hh hg (hy i hi)
      (hpositive (hu i hi)) (hpositive (huk i hi)) (hret₀ i hi) (hret₁ i hi)
      hJ₁ (hpositiveJ (hw i hi)) (hvaluesJ i hi)

theorem actual_displacement_interval_exponent_pair_bound
    {σ A B k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hA : 0 < A) (hA₂ : A ≤ 2) (hB : 0 < B) (hB₂ : B ≤ 2)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∃ Q : ℕ, 1 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (η P V : ℝ) (a b : ℕ) (K : ℤ) (y : ℕ → ℝ),
          IsApproximateModelPhaseFunction F σ Q δ → 0 < η → η ≤ η₀ →
          0 < P → 0 < V →
          (∀ n∈Finset.Icc a b, y n ∈ Ioo (1:ℝ) 2) →
          (∀ n∈Finset.Icc a b, A*aProcessShiftPoint η 0 (y n) ∈ modelPhaseSlopeRange F) →
          (∀ n∈Finset.Icc a b, A*aProcessShiftPoint η 1 (y n) ∈ modelPhaseSlopeRange F) →
          let u := fun n => A*aProcessShiftPoint η 0 (y n)
          let k := A*η
          let d := fun n => modelPhaseInverseSlope F (u n)-modelPhaseInverseSlope F (u n+k)
          let s := A^(σ⁻¹-1)/(σ⁻¹*η)
          let θ := (σ⁻¹+1)⁻¹
          let M := B*P/(s*A*(1-η))
          let H := 2*V/(s*B^(θ-1))
          let R := fun n => 2*(F (modelPhaseInverseSlope F (u n+k))-
            F (modelPhaseInverseSlope F (u n))-k*modelPhaseInverseSlope F (u n+k))
          1 ≤ M → M ≤ (a:ℝ) → (b:ℝ) ≤ 2*M → V*k/P=(K:ℝ) →
          (∀ n∈Finset.Icc a b, P*d n=(n:ℝ)) →
          ∀ r : ℤ, r ≠ 0 →
            ‖∑ n∈Finset.Icc a b, fordAdditiveCharacter ((r:ℝ)*V*R n)‖ ≤
              C*(((|(r:ℝ)| * H)/M)^(k₀+ε)*M^(l₀+ε)+M/(|(r:ℝ)| * H)) := by
  have hθ : 0 < (σ⁻¹+1)⁻¹ := by positivity
  pm_371 δG hδG QG _hQG C hC hbound hpair.allPositiveHeight_bound hθ hε
  obtain ⟨δ,η₀,hδ,hη₀,hηhalf,Q,Q₁,hQ,hrealize⟩ :=
    finite_moving_double_dual_realization hσ hA hA₂ hB hB₂ QG hδG
  pm_2029
  intro F η P V a b K y hF hη hηle hP hV hy hu huk u k d s θ M H R
    hM ha hb hK hn
  obtain ⟨h,g,_hh,_hh₁,_hg,_hg₁,hG,_hwindow,hvalues⟩ :=
    hrealize F η hF hη hηle ℕ (Finset.Icc a b) y hy hu huk
  let J := aProcessShiftPhase
    (canonicalTaylorLegendrePhase F σ A Q₁ (deriv F (3/2)) h) σ⁻¹ η
  pm_8319
  let G := canonicalTaylorLegendrePhase J (σ⁻¹+1) B QG c g
  let C₀ := -2*V/s*modelPhaseLegendreDual J c+H*referenceModelPrimitive θ (c/B)
  pm_2028
  have hz : 0 < B^(θ-1) := Real.rpow_pos_of_pos hB _
  pm_2027
  pm_781
  have hphase (n:ℕ) (hni:n∈Finset.Icc a b) :
      V*R n=C₀-H*G ((n:ℝ)/M)-2*(K:ℝ)*(n:ℝ) := by
    have hd : d n=(n:ℝ)/P := by
      apply (eq_div_iff hP.ne').mpr
      nlinarith only [hn n hni]
    have hv := hvalues n hni
    change G (s*A*(1-η)*d n/B)=
      B^(θ-1)*(-s/2*R n-s*k*d n-modelPhaseLegendreDual J c)+
        referenceModelPrimitive θ (c/B) at hv
    have harg := (hscales.2.2.2.2.2 (n:ℝ)).1
    change s*A*(1-η)*((n:ℝ)/P)/B=(n:ℝ)/M at harg
    rw [hd,harg] at hv
    rw [hv,← hK]
    dsimp only [H,C₀]
    field_simp
    ring
  have hint (z:ℤ) : fordAdditiveCharacter (z:ℝ)=1 := by
    unfold fordAdditiveCharacter
    have he : 2*Real.pi*Complex.I*((z:ℝ):ℂ) =
        (z:ℂ)*(2*Real.pi*Complex.I) := by push_cast; ring
    rw [he,Complex.exp_int_mul_two_pi_mul_I]
  intro r hr
  have hchar (n:ℕ) (hni:n∈Finset.Icc a b) :
      fordAdditiveCharacter ((r:ℝ)*V*R n) =
        fordAdditiveCharacter ((r:ℝ)*C₀)*
          star (fordAdditiveCharacter ((r:ℝ)*H*G ((n:ℝ)/M))) := by
    have he : (r:ℝ)*V*R n =
        ((r:ℝ)*C₀+-((r:ℝ)*H*G ((n:ℝ)/M)))+
          ((-2*r*K*(n:ℤ):ℤ):ℝ) := by
      push_cast
      rw [mul_assoc,hphase n hni]
      ring
    rw [he,fordAdditiveCharacter_add,hint,mul_one,
      fordAdditiveCharacter_add,← conj_fordAdditiveCharacter]
    rfl
  have hsum : (∑ n∈Finset.Icc a b, fordAdditiveCharacter ((r:ℝ)*V*R n)) =
      fordAdditiveCharacter ((r:ℝ)*C₀)*star (exponentialSumAt G ((r:ℝ)*H) M a b) := by
    pm_476 exponentialSumAt star_sum Finset.mul_sum n hni
    simp only [hchar n hni,sargos_ford_character_eq_fourier,oscillatory]
  rw [hsum,norm_mul,sargos_character_norm,one_mul,norm_star]
  have hnormheight : ‖exponentialSumAt G ((r:ℝ)*H) M a b‖ =
      ‖exponentialSumAt G (|(r:ℝ)| * H) M a b‖ := by
    pm_7957 hrpos
    · have hrneg : (r:ℝ) < 0 := lt_of_not_ge hrpos
      have he : exponentialSumAt G ((r:ℝ)*H) M a b =
          star (exponentialSumAt G (|(r:ℝ)| * H) M a b) := by
        simp only [exponentialSumAt,star_sum]
        apply Finset.sum_congr rfl
        intro n _hn
        simp only [oscillatory,←sargos_ford_character_eq_fourier,abs_of_neg hrneg]
        have harg : (r:ℝ)*H*G ((n:ℝ)/M) = -(-(r:ℝ)*H*G ((n:ℝ)/M)) := by ring
        rw [harg,←conj_fordAdditiveCharacter]
        rfl
      rw [he,norm_star]
  rw [hnormheight]
  exact hbound (|(r:ℝ)| * H) M G a b
    (mul_pos (abs_pos.mpr (Int.cast_ne_zero.mpr hr)) hH)
    hM ha hb hG

theorem positive_slope_chart_compressed_coordinate
    {d v k : ℝ} (hd : 0 < d) (hv : v ∈ Icc (4*d) 2)
    (hk : 0 ≤ k) (hkd : k ≤ d) :
    let j := positiveSlopeChartIndex d v
    let A := positiveSlopeChartScale d j
    let η := k/A
    let y := (v/A-η)/(1-η)
    j ∈ positiveSlopeChartIndices d ∧ 0 < A ∧ A ≤ 3/2 ∧
      0 ≤ η ∧ η ≤ 1/3 ∧ y ∈ Ioo (1:ℝ) 2 ∧
        A*aProcessShiftPoint η 0 y=v ∧ A*aProcessShiftPoint η 1 y=v+k := by
  intro j A η y
  have hj : j ∈ positiveSlopeChartIndices d := positiveSlopeChartIndex_mem hd hv
  obtain ⟨hA,hA₂⟩ := positiveSlopeChartScale_bounds hd hj
  have hj₄ : (4:ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  have hjd := mul_le_mul_of_nonneg_right hj₄ hd.le
  have hAd : 3*d ≤ A := by dsimp [A,positiveSlopeChartScale]; nlinarith only [hjd]
  have hη : 0 ≤ η := div_nonneg hk hA.le
  have hη₁ : η ≤ 1/3 := by
    apply (div_le_iff₀ hA).mpr
    linarith only [hkd,hAd]
  have hden : 0 < 1-η := by linarith
  have hvpos : 0 ≤ v := (by positivity : (0:ℝ) ≤ 4*d).trans hv.1
  pm_5577 hvpos hcoord
  have hupper : v+k < 2*A := by
    dsimp [A,positiveSlopeChartScale]
    nlinarith only [hcell.2,hkd,hjd]
  have hy : y ∈ Ioo (1:ℝ) 2 := by
    constructor
    · apply (one_lt_div hden).mpr
      linarith only [hcoord.1]
    · apply (div_lt_iff₀ hden).mpr
      have hdiv : v/A+η < 2 := by
        dsimp only [η]
        rw [← add_div]
        exact (div_lt_iff₀ hA).mpr hupper
      linarith only [hdiv]
  have hzero : A*aProcessShiftPoint η 0 y=v := by
    dsimp only [aProcessShiftPoint,y]
    field_simp [show A ≠ 0 from hA.ne',hden.ne']
    ring
  pm_2030 hj hA hA₂ hη hη₁ hy hzero
  have hkA : A*η=k := mul_div_cancel₀ k (show A ≠ 0 from hA.ne')
  calc
    A*aProcessShiftPoint η 1 y=A*aProcessShiftPoint η 0 y+A*η := by
      dsimp [aProcessShiftPoint]
      ring
    _ = v+k := by rw [hzero,hkA]

theorem actual_displacement_interval_near_count
    {σ A B k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hA : 0 < A) (hA₂ : A ≤ 2) (hB : 0 < B) (hB₂ : B ≤ 2)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∃ Q : ℕ, 1 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (η P V : ℝ) (a b : ℕ) (K : ℤ) (y : ℕ → ℝ),
          IsApproximateModelPhaseFunction F σ Q δ → 0 < η → η ≤ η₀ →
          0 < P → 0 < V →
          (∀ n∈Finset.Icc a b, y n ∈ Ioo (1:ℝ) 2) →
          (∀ n∈Finset.Icc a b, A*aProcessShiftPoint η 0 (y n) ∈ modelPhaseSlopeRange F) →
          (∀ n∈Finset.Icc a b, A*aProcessShiftPoint η 1 (y n) ∈ modelPhaseSlopeRange F) →
          let u := fun n => A*aProcessShiftPoint η 0 (y n)
          let k := A*η
          let d := fun n => modelPhaseInverseSlope F (u n)-modelPhaseInverseSlope F (u n+k)
          let s := A^(σ⁻¹-1)/(σ⁻¹*η)
          let θ := (σ⁻¹+1)⁻¹
          let M := B*P/(s*A*(1-η))
          let H := 2*V/(s*B^(θ-1))
          let R := fun n => 2*(F (modelPhaseInverseSlope F (u n+k))-
            F (modelPhaseInverseSlope F (u n))-k*modelPhaseInverseSlope F (u n+k))
          1 ≤ M → M ≤ (a:ℝ) → (b:ℝ) ≤ 2*M → V*k/P=(K:ℝ) →
          (∀ n∈Finset.Icc a b, P*d n=(n:ℝ)) →
          ∀ (W : ℝ), 0 < W → W ≤ 1/2 →
          ∀ (I : Finset ℕ), I ⊆ Finset.Icc a b →
          (∀ n∈I, ∃ e : ℤ, |V*R n-(e:ℝ)| ≤ W/2) →
            (I.card:ℝ) ≤ 2*W*(Finset.Icc a b).card+
              (4+4/(1-(k₀+ε)))*(C*(H/M)^(k₀+ε)*M^(l₀+ε))*W^(-(k₀+ε))+
              2*(C*M/H) := by
  obtain ⟨δ,η₀,hδ,hη₀,hηhalf,Q,hQ,C,hC,hbound⟩ :=
    actual_displacement_interval_exponent_pair_bound hσ hA hA₂ hB hB₂ hpair hε
  pm_2029
  intro F η P V a b K y hF hη hηle hP hV hy hu huk u k d s θ M H R
    hM ha hb hK hn W hW hWhalf I hI hnear
  have hηone : η < 1 := by linarith
  pm_2028
  pm_2027
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  pm_8245 hp0
  have hfreq (r:ℤ) (hr : r ≠ 0) :
      ‖∑ n∈Finset.Icc a b, fordAdditiveCharacter ((r:ℝ)*(V*R n))‖ ≤
        (C*(H/M)^(k₀+ε)*M^(l₀+ε))*|(r:ℝ)|^(k₀+ε)+C*M/H := by
    have hh := hbound F η P V a b K y hF hη hηle hP hV hy hu huk
      hM ha hb hK hn r hr
    change ‖∑ n∈Finset.Icc a b, fordAdditiveCharacter ((r:ℝ)*V*R n)‖ ≤
      C*(((|(r:ℝ)| * H)/M)^(k₀+ε)*M^(l₀+ε)+M/(|(r:ℝ)| * H)) at hh
    pm_7397 hr1
    have htail : M/(|(r:ℝ)| * H) ≤ M/H :=
      div_le_div_of_nonneg_left hMpos.le hH (by nlinarith)
    have he : ((|(r:ℝ)| * H)/M)^(k₀+ε)=
        |(r:ℝ)|^(k₀+ε)*(H/M)^(k₀+ε) := by
      rw [show |(r:ℝ)| * H/M=|(r:ℝ)| * (H/M) by ring,
        Real.mul_rpow (abs_nonneg _) (div_nonneg hH.le hMpos.le)]
    simp only [mul_assoc] at hh ⊢
    rw [he] at hh
    calc
      _ ≤ C*(|(r:ℝ)|^(k₀+ε)*(H/M)^(k₀+ε)*M^(l₀+ε)+M/(|(r:ℝ)| * H)) := hh
      _ ≤ C*(|(r:ℝ)|^(k₀+ε)*(H/M)^(k₀+ε)*M^(l₀+ε)+M/H) := by gcongr
      _ = _ := by ring
  exact CubicNearCurve.cubic_near_integer_count_power
    (Finset.Icc a b) I (fun n => V*R n) hW hWhalf
    (by positivity) (by positivity) hp0 hp hI hnear hfreq

theorem finite_actual_displacement_interval_completion
    {σ δ A η P : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hA : 0 < A) (hη : η < 1)
    (S : Finset ℕ) (hne : S.Nonempty) (y : ℕ → ℝ)
    (hy : ∀ n∈S, y n∈Ioo (1:ℝ) 2)
    (hu : ∀ n∈S, A*aProcessShiftPoint η 0 (y n)∈modelPhaseSlopeRange F)
    (huk : ∀ n∈S, A*aProcessShiftPoint η 1 (y n)∈modelPhaseSlopeRange F)
    (hn : ∀ n∈S, P*(modelPhaseInverseSlope F (A*aProcessShiftPoint η 0 (y n))-
      modelPhaseInverseSlope F (A*aProcessShiftPoint η 1 (y n)))=(n:ℝ)) :
    ∃ z : ℕ → ℝ,
      (∀ n∈S, z n=y n) ∧
      ∀ n∈Finset.Icc (S.min' hne) (S.max' hne),
        z n∈Ioo (1:ℝ) 2 ∧
        A*aProcessShiftPoint η 0 (z n)∈modelPhaseSlopeRange F ∧
        A*aProcessShiftPoint η 1 (z n)∈modelPhaseSlopeRange F ∧
        P*(modelPhaseInverseSlope F (A*aProcessShiftPoint η 0 (z n))-
          modelPhaseInverseSlope F (A*aProcessShiftPoint η 1 (z n)))=(n:ℝ) := by
  classical
  pm_2031
  let U := fun t v => A*aProcessShiftPoint η t v
  let D := fun v => P*(modelPhaseInverseSlope F (U 0 v)-modelPhaseInverseSlope F (U 1 v))
  have hmono (t : ℝ) : Monotone (U t) := by
    intro v w hvw
    dsimp [U,aProcessShiftPoint]
    gcongr
  have hpoint (v : ℝ) (hv : v∈uIcc (y a) (y b)) :
      v∈Ioo (1:ℝ) 2 ∧ U 0 v∈modelPhaseSlopeRange F ∧ U 1 v∈modelPhaseSlopeRange F := by
    have hconv : Set.OrdConnected (modelPhaseSlopeRange F) := by
      rw [modelPhaseSlopeRange_eq_endpoint_Ioo hσ hδ hF]
      exact (convex_Ioo _ _).ordConnected
    refine ⟨(convex_Ioo (1:ℝ) 2).ordConnected.uIcc_subset (hy a ha) (hy b hb) hv,?_,?_⟩
    · exact hconv.uIcc_subset (hu a ha) (hu b hb) ((hmono 0).image_uIcc_subset ⟨v,hv,rfl⟩)
    · exact hconv.uIcc_subset (huk a ha) (huk b hb) ((hmono 1).image_uIcc_subset ⟨v,hv,rfl⟩)
  have hD : ContinuousOn D (uIcc (y a) (y b)) := by
    intro v hv
    have hc (t : ℝ) (ht : U t v∈modelPhaseSlopeRange F) :
        ContinuousAt (fun w => modelPhaseInverseSlope F (U t w)) v := by
      exact ((modelPhaseInverseSlope_contDiffAt hσ hδ hF ht).continuousAt).comp
        (by dsimp [U,aProcessShiftPoint]; fun_prop)
    exact ((hc 0 (hpoint v hv).2.1).sub (hc 1 (hpoint v hv).2.2)).const_mul P
      |>.continuousWithinAt
  have hex (n : ℕ) (hni : n∈Finset.Icc a b) :
      ∃ v : ℝ, v∈Ioo (1:ℝ) 2 ∧ U 0 v∈modelPhaseSlopeRange F ∧
        U 1 v∈modelPhaseSlopeRange F ∧ D v=(n:ℝ) ∧ (n∈S → v=y n) := by
    by_cases hns : n∈S
    · exact ⟨y n,hy n hns,hu n hns,huk n hns,hn n hns,fun _ => rfl⟩
    have hna : a ≤ n := (Finset.mem_Icc.mp hni).1
    have hnb : n ≤ b := (Finset.mem_Icc.mp hni).2
    have hab : (a:ℝ) ≤ b := by exact_mod_cast hna.trans hnb
    have htarget : (n:ℝ)∈uIcc (D (y a)) (D (y b)) := by
      change (n:ℝ)∈uIcc (P*(_-_)) (P*(_-_))
      rw [hn a ha,hn b hb,uIcc_of_le hab]
      exact ⟨by exact_mod_cast hna,by exact_mod_cast hnb⟩
    pm_69 v hv he intermediate_value_uIcc hD htarget
    exact ⟨v,(hpoint v hv).1,(hpoint v hv).2.1,(hpoint v hv).2.2,he,
      fun hh => False.elim (hns hh)⟩
  let z := fun n => if hni : n∈Finset.Icc a b then Classical.choose (hex n hni) else y n
  refine ⟨z,?_,?_⟩
  · intro n hns
    have hni : n∈Finset.Icc a b := Finset.mem_Icc.mpr
      ⟨Finset.min'_le S n hns,Finset.le_max' S n hns⟩
    simp only [z,dite_eq_left hni]
    exact (Classical.choose_spec (hex n hni)).2.2.2.2 hns
  · intro n hni
    change n∈Finset.Icc a b at hni
    simp only [z,dite_eq_left hni]
    have hh := Classical.choose_spec (hex n hni)
    exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩

theorem actual_displacement_finite_near_count
    {σ A B k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hA : 0 < A) (hA₂ : A ≤ 2) (hB : 0 < B) (hB₂ : B ≤ 2)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∃ Q : ℕ, 1 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (η P V : ℝ) (K : ℤ) (S : Finset ℕ) (y : ℕ → ℝ),
          IsApproximateModelPhaseFunction F σ Q δ → 0 < η → η ≤ η₀ →
          0 < P → 0 < V →
          (∀ n∈S, y n ∈ Ioo (1:ℝ) 2) →
          (∀ n∈S, A*aProcessShiftPoint η 0 (y n) ∈ modelPhaseSlopeRange F) →
          (∀ n∈S, A*aProcessShiftPoint η 1 (y n) ∈ modelPhaseSlopeRange F) →
          let u := fun n => A*aProcessShiftPoint η 0 (y n)
          let k := A*η
          let d := fun n => modelPhaseInverseSlope F (u n)-modelPhaseInverseSlope F (u n+k)
          let s := A^(σ⁻¹-1)/(σ⁻¹*η)
          let θ := (σ⁻¹+1)⁻¹
          let M := B*P/(s*A*(1-η))
          let H := 2*V/(s*B^(θ-1))
          let R := fun n => 2*(F (modelPhaseInverseSlope F (u n+k))-
            F (modelPhaseInverseSlope F (u n))-k*modelPhaseInverseSlope F (u n+k))
          1 ≤ M → (∀ n∈S, M ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*M) → V*k/P=(K:ℝ) →
          (∀ n∈S, P*d n=(n:ℝ)) →
          ∀ (W : ℝ), 0 < W → W ≤ 1/2 →
          (∀ n∈S, ∃ e : ℤ, |V*R n-(e:ℝ)| ≤ W/2) →
            (S.card:ℝ) ≤ 4*W*M+
              (4+4/(1-(k₀+ε)))*(C*(H/M)^(k₀+ε)*M^(l₀+ε))*W^(-(k₀+ε))+
              2*(C*M/H) := by
  pm_8599 δ₀ hδ₀ C hC hbound actual_displacement_interval_near_count
  let δ := min δ₀ (min (modelPhaseCurvatureLower σ) 1)
  have hδ : 0 < δ := lt_min hδ₀ (lt_min (modelPhaseCurvatureLower_pos hσ) zero_lt_one)
  pm_2029
  intro F η P V K S y hF hη hηle hP hV hy hu huk u k d s θ M H R
    hM hbox hK hn W hW hWhalf hnear
  pm_2028
  pm_2027
  pm_1610 hMpos M hM hCpos C hC
  have hFlarge := approximateModelPhase_mono hF (le_refl Q) (min_le_left δ₀ _)
  have hFone := approximateModelPhase_mono hF hQ (le_refl δ)
  have hshift (v : ℝ) : A*aProcessShiftPoint η 1 v=A*aProcessShiftPoint η 0 v+k := by
    dsimp [aProcessShiftPoint,k]
    ring
  by_cases hne : S.Nonempty
  · obtain ⟨z,hagree,hcomplete⟩ := finite_actual_displacement_interval_completion
      hσ (min_le_right δ₀ _) hFone hA (by linarith) S hne y hy hu huk
      (by intro n hni; rw [hshift]; exact hn n hni)
    pm_2031
    have hab : a ≤ b := Finset.min'_le S b hb
    have hsubset : S ⊆ Finset.Icc a b := fun n hni => Finset.mem_Icc.mpr
      ⟨Finset.min'_le S n hni,Finset.le_max' S n hni⟩
    have hMa : M ≤ (a:ℝ) := (hbox a ha).1
    have hbM : (b:ℝ) ≤ 2*M := (hbox b hb).2
    have hz₀ : ∀ n∈Finset.Icc a b, z n∈Ioo (1:ℝ) 2 :=
      fun n hni => (hcomplete n hni).1
    have hz₁ : ∀ n∈Finset.Icc a b, A*aProcessShiftPoint η 0 (z n)∈modelPhaseSlopeRange F :=
      fun n hni => (hcomplete n hni).2.1
    have hz₂ : ∀ n∈Finset.Icc a b, A*aProcessShiftPoint η 1 (z n)∈modelPhaseSlopeRange F :=
      fun n hni => (hcomplete n hni).2.2.1
    have hz₃ : ∀ n∈Finset.Icc a b,
        P*(modelPhaseInverseSlope F (A*aProcessShiftPoint η 0 (z n))-
          modelPhaseInverseSlope F (A*aProcessShiftPoint η 0 (z n)+k))=(n:ℝ) := by
      intro n hni
      have hh := (hcomplete n hni).2.2.2
      rwa [hshift] at hh
    let Rz := fun n => 2*(F (modelPhaseInverseSlope F (A*aProcessShiftPoint η 0 (z n)+k))-
      F (modelPhaseInverseSlope F (A*aProcessShiftPoint η 0 (z n)))-
      k*modelPhaseInverseSlope F (A*aProcessShiftPoint η 0 (z n)+k))
    have hznear : ∀ n∈S, ∃ e : ℤ, |V*Rz n-(e:ℝ)| ≤ W/2 := by
      intro n hni
      have he : Rz n=R n := by
        dsimp only [Rz,R,u]
        rw [hagree n hni]
      rw [he]
      exact hnear n hni
    have hh := hbound F η P V a b K z hFlarge hη hηle hP hV hz₀ hz₁ hz₂
      hM hMa hbM hK hz₃ W hW hWhalf S hsubset hznear
    change (S.card:ℝ) ≤ 2*W*(Finset.Icc a b).card+
      (4+4/(1-(k₀+ε)))*(C*(H/M)^(k₀+ε)*M^(l₀+ε))*W^(-(k₀+ε))+
      2*(C*M/H) at hh
    have hcard : ((Finset.Icc a b).card:ℝ) ≤ 2*M := by
      rw [Nat.card_Icc,Nat.cast_sub (by omega : a ≤ b+1),Nat.cast_add,Nat.cast_one]
      linarith
    calc
      _ ≤ _ := hh
      _ ≤ 2*W*(2*M)+(4+4/(1-(k₀+ε)))*(C*(H/M)^(k₀+ε)*M^(l₀+ε))*W^(-(k₀+ε))+
          2*(C*M/H) := by gcongr
      _ = _ := by ring
  pm_2032

theorem finite_moving_displacement_window
    {σ A : ℝ} (hσ : 0 < σ) (hA : 0 < A) (hA₂ : A ≤ 2) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∃ Q : ℕ, 1 ≤ Q ∧
        ∀ (F : ℝ → ℝ) (η : ℝ), IsApproximateModelPhaseFunction F σ Q δ →
          0 < η → η ≤ η₀ → ∀ (ι : Type*) (S : Finset ι) (y : ι → ℝ),
          (∀ i∈S, y i∈Ioo (1:ℝ) 2) →
          (∀ i∈S, A*aProcessShiftPoint η 0 (y i)∈modelPhaseSlopeRange F) →
          (∀ i∈S, A*aProcessShiftPoint η 1 (y i)∈modelPhaseSlopeRange F) →
          let u := fun i => A*aProcessShiftPoint η 0 (y i)
          let k := A*η
          let d := fun i => modelPhaseInverseSlope F (u i)-modelPhaseInverseSlope F (u i+k)
          let s := A^(σ⁻¹-1)/(σ⁻¹*η)
          ∀ i∈S, s*A*(1-η)*d i∈Icc ((2:ℝ)^(-(σ⁻¹+1))/2) 2 := by
  obtain ⟨δ,η₀,hδ,hη₀,hηhalf,Q,Q₁,hQ,hrealize⟩ :=
    finite_moving_double_dual_realization hσ hA hA₂ (by norm_num : (0:ℝ)<1)
      (by norm_num : (1:ℝ)≤2) 0 (by norm_num : (0:ℝ)<1)
  pm_2030 δ η₀ hδ hη₀ hηhalf Q hQ
  intro F η hF hη hηle ι S y hy hu huk u k d s
  obtain ⟨h,g,_hh,_hh1,_hg,_hg1,_hG,hwindow,_hvalues⟩ :=
    hrealize F η hF hη hηle ι S y hy hu huk
  exact hwindow

theorem displacement_second_chart_geometry
    {mesh w L P n : ℝ} (hd : 0 < mesh) (hL : 0 < L) (hP : 0 < P)
    (hw : w∈Icc (4*mesh) 2) (hn : 2 ≤ n) (he : w=L*n/P) :
    let j := positiveSlopeChartIndex mesh w
    let B := positiveSlopeChartScale mesh j
    let M := B*P/L
    j∈positiveSlopeChartIndices mesh ∧ 0 < B ∧ B ≤ 3/2 ∧
      1 ≤ M ∧ M ≤ n ∧ n ≤ 2*M := by
  intro j B M
  have hj := positiveSlopeChartIndex_mem hd hw
  have hBj := positiveSlopeChartScale_bounds hd hj
  have hw0 : 0 ≤ w := (by positivity : (0:ℝ) ≤ 4*mesh).trans hw.1
  pm_5577 hw0 hc
  have hB : 0 < B := hBj.1
  pm_4365
  have harg : w/B=n/M := by
    rw [he]
    dsimp only [M]
    field_simp
  change w/B∈Ioo (1:ℝ) 2 at hc
  rw [harg] at hc
  have hlo : M < n := (one_lt_div hM).mp hc.1
  have hhi : n < 2*M := (div_lt_iff₀ hM).mp hc.2
  exact ⟨hj,hB,hBj.2,by linarith,hlo.le,hhi.le⟩

theorem actual_displacement_physical_chart_count
    {σ A B k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hA : 0 < A) (hA₂ : A ≤ 2) (hB : 0 < B) (hB₂ : B ≤ 2)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∃ Q : ℕ, 1 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (η P V N : ℝ) (K : ℤ) (S : Finset ℕ) (y : ℕ → ℝ),
          IsApproximateModelPhaseFunction F σ Q δ → 0 < η → η ≤ η₀ →
          0 < P → 0 < V → 0 < N →
          (∀ n∈S, y n ∈ Ioo (1:ℝ) 2) →
          (∀ n∈S, A*aProcessShiftPoint η 0 (y n) ∈ modelPhaseSlopeRange F) →
          (∀ n∈S, A*aProcessShiftPoint η 1 (y n) ∈ modelPhaseSlopeRange F) →
          let u := fun n => A*aProcessShiftPoint η 0 (y n)
          let k := A*η
          let d := fun n => modelPhaseInverseSlope F (u n)-modelPhaseInverseSlope F (u n+k)
          let s := A^(σ⁻¹-1)/(σ⁻¹*η)
          let M := B*P/(s*A*(1-η))
          let R := fun n => 2*(F (modelPhaseInverseSlope F (u n+k))-
            F (modelPhaseInverseSlope F (u n))-k*modelPhaseInverseSlope F (u n+k))
          1 ≤ M → (∀ n∈S, M ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*M) →
          (∀ n∈S, (n:ℝ) ≤ 2*N) → V*k/P=(K:ℝ) →
          (∀ n∈S, P*d n=(n:ℝ)) →
          ∀ (W : ℝ), 0 < W → W ≤ 1/2 →
          (∀ n∈S, ∃ e : ℤ, |V*R n-(e:ℝ)| ≤ W/2) →
            (S.card:ℝ) ≤ C*(W*N+(V/P)^(k₀+ε)*N^(l₀+ε)*W^(-(k₀+ε))+P/V) := by
  pm_8599 δ hδ C₀ hC₀ hcount actual_displacement_finite_near_count
  let p := k₀+ε
  let q := l₀+ε
  let θ := (σ⁻¹+1)⁻¹
  let c := A*B^(-θ)
  let D := (4+4/(1-p))*C₀*(2*c)^p*(2:ℝ)^q
  let E := 2*C₀/c
  let C := 8+D+E
  have hp₀ : 0 ≤ p := by dsimp [p]; linarith [hpair.1.1]
  have hq₀ : 0 ≤ q := by dsimp [q]; linarith [hpair.1.2.2.1]
  pm_64 hc c
  have hD : 0 ≤ D := by dsimp [D,p]; positivity
  pm_61 hE E
  pm_1608
  pm_2029
  intro F η P V N K S y hF hη hηle hP hV hN hy hu huk u k d s M R
    hM hbox hNbox hK hn W hW hWhalf hnear
  let H := 2*V/(s*B^(θ-1))
  have hηh : η ≤ 1/2 := hηle.trans hηhalf
  pm_781
  have hMpos : 0 < M := hscales.1
  have hH : 0 < H := hscales.2.1
  have heq : H/M=2*c*(1-η)*(V/P) := by
    calc
      _ = (2*V/P)*A*(1-η)*B^(-θ) := hscales.2.2.2.1
      _ = _ := by dsimp [c]; ring
  have hlo : c*(V/P) ≤ H/M := by rw [heq]; nlinarith [mul_pos hc (div_pos hV hP)]
  have hhi : H/M ≤ (2*c)*(V/P) := by rw [heq]; nlinarith [mul_pos hc (div_pos hV hP)]
  have htail : M/H ≤ (1/c)*(P/V) := by
    have hh := one_div_le_one_div_of_le (mul_pos hc (div_pos hV hP)) hlo
    convert hh using 1 <;> field_simp
  by_cases hne : S.Nonempty
  · obtain ⟨n,hns⟩ := hne
    have hMN : M ≤ 2*N := (hbox n hns).1.trans (hNbox n hns)
    have hfreq : (H/M)^p ≤ (2*c)^p*(V/P)^p := by
      rw [← Real.mul_rpow (by positivity : 0 ≤ 2*c) (div_nonneg hV.le hP.le)]
      exact Real.rpow_le_rpow (div_nonneg hH.le hMpos.le) hhi hp₀
    have hlength : M^q ≤ (2:ℝ)^q*N^q := by
      rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hN.le]
      exact Real.rpow_le_rpow hMpos.le hMN hq₀
    have hh := hcount F η P V K S y hF hη hηle hP hV hy hu huk
      hM hbox hK hn W hW hWhalf hnear
    change (S.card:ℝ) ≤ 4*W*M+
      (4+4/(1-p))*(C₀*(H/M)^p*M^q)*W^(-p)+2*(C₀*M/H) at hh
    have hmain : (4+4/(1-p))*(C₀*(H/M)^p*M^q)*W^(-p) ≤
        D*((V/P)^p*N^q*W^(-p)) := by
      calc
        _ ≤ (4+4/(1-p))*(C₀*((2*c)^p*(V/P)^p)*((2:ℝ)^q*N^q))*W^(-p) := by
          gcongr
        _ = _ := by dsimp [D]; ring
    have htail' : 2*(C₀*M/H) ≤ E*(P/V) := by
      calc
        _ = 2*C₀*(M/H) := by ring
        _ ≤ 2*C₀*((1/c)*(P/V)) := by gcongr
        _ = _ := by dsimp [E]; ring
    have hvolume : 4*W*M ≤ 8*(W*N) := by nlinarith [mul_le_mul_of_nonneg_left hMN hW.le]
    pm_8246 hbig₀
    pm_182 hbig₁ D C
    pm_182 hbig₂ E C
    calc
      _ ≤ 8*(W*N)+D*((V/P)^p*N^q*W^(-p))+E*(P/V) := by linarith
      _ ≤ C*(W*N)+C*((V/P)^p*N^q*W^(-p))+C*(P/V) := by gcongr
      _ = _ := by dsimp [p,q]; ring
  pm_2032

theorem actual_displacement_first_chart_count
    {σ A k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hA : 0 < A) (hA₂ : A ≤ 2)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∃ Q : ℕ, 1 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (η P V N : ℝ) (K : ℤ) (S : Finset ℕ) (y : ℕ → ℝ),
          IsApproximateModelPhaseFunction F σ Q δ → 0 < η → η ≤ η₀ →
          0 < P → 0 < V → 0 < N →
          (∀ n∈S, y n ∈ Ioo (1:ℝ) 2) →
          (∀ n∈S, A*aProcessShiftPoint η 0 (y n) ∈ modelPhaseSlopeRange F) →
          (∀ n∈S, A*aProcessShiftPoint η 1 (y n) ∈ modelPhaseSlopeRange F) →
          let u := fun n => A*aProcessShiftPoint η 0 (y n)
          let k := A*η
          let d := fun n => modelPhaseInverseSlope F (u n)-modelPhaseInverseSlope F (u n+k)
          let R := fun n => 2*(F (modelPhaseInverseSlope F (u n+k))-
            F (modelPhaseInverseSlope F (u n))-k*modelPhaseInverseSlope F (u n+k))
          (∀ n∈S, 2 ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N) → V*k/P=(K:ℝ) →
          (∀ n∈S, P*d n=(n:ℝ)) →
          ∀ (W : ℝ), 0 < W → W ≤ 1/2 →
          (∀ n∈S, ∃ e : ℤ, |V*R n-(e:ℝ)| ≤ W/2) →
            (S.card:ℝ) ≤ C*(W*N+(V/P)^(k₀+ε)*N^(l₀+ε)*W^(-(k₀+ε))+P/V) := by
  classical
  let mesh := (2:ℝ)^(-(σ⁻¹+1))/8
  pm_64 hmesh mesh
  have hmesh₂ : 4*mesh ≤ 2 := by
    have hh : (2:ℝ)^(-(σ⁻¹+1)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by have := inv_pos.mpr hσ; linarith)
    dsimp [mesh]
    linarith
  pm_2037
  pm_2038 B hBj
  have hlocal (j : {j // j∈J}) := actual_displacement_physical_chart_count
    hσ hA hA₂ (hBj j).1 (hBj j).2 hpair hε hp
  pm_7464
  obtain ⟨δw,ηw,hδw,hηw,hηhalfw,Qw,hQw,hwindow⟩ :=
    finite_moving_displacement_window hσ hA hA₂
  let δ := min δw (J.attach.inf' ht δj)
  let η₀ := min ηw (J.attach.inf' ht ηj)
  let Q := max Qw (J.attach.sup Qj)
  pm_7750
  pm_8617 hδ δ hδw hδj
  pm_8617 hη₀ η₀ hηw hηj
  have hηhalf : η₀ ≤ 1/2 := (min_le_left _ _).trans hηhalfw
  pm_5105 hQ Q hQw.trans
  pm_2035
  pm_2029
  intro F η P V N K S y hF hη hηle hP hV hN hy hu huk u k d R hbox hK hn W hW hWhalf hnear
  let s := A^(σ⁻¹-1)/(σ⁻¹*η)
  let L := s*A*(1-η)
  let w := fun n => L*d n
  have hηwle : η ≤ ηw := hηle.trans (min_le_left _ _)
  have hηone : η < 1 := by linarith [hηwle,hηhalfw]
  pm_8675 hL s
  have hFwindow := approximateModelPhase_mono hF (le_max_left _ _) (min_le_left _ _)
  have hw₀ := hwindow F η hFwindow hη hηwle ℕ S y hy hu huk
  have hw (n : ℕ) (hns : n∈S) : w n∈Icc (4*mesh) 2 := by
    have hh := hw₀ n hns
    change L*d n ∈ Icc ((2:ℝ)^(-(σ⁻¹+1))/2) 2 at hh
    change L*d n∈Icc (4*mesh) 2
    rw [show 4*mesh=(2:ℝ)^(-(σ⁻¹+1))/2 by dsimp [mesh]; ring]
    exact hh
  let label := fun n => positiveSlopeChartIndex mesh (w n)
  pm_2034
  have hcell (j : {j // j∈J}) :
      ((cell j).card:ℝ) ≤ Cj j*(W*N+(V/P)^(k₀+ε)*N^(l₀+ε)*W^(-(k₀+ε))+P/V) := by
    let M := B j*P/L
    have hgeom (n : ℕ) (hni : n∈cell j) : 1 ≤ M ∧ M ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*M := by
      have hns := (Finset.mem_filter.mp hni).1
      have he : w n=L*(n:ℝ)/P := by
        dsimp only [w]
        have hd : d n=(n:ℝ)/P := by
          apply (eq_div_iff hP.ne').mpr
          simpa [mul_comm] using hn n hns
        rw [hd]
        ring
      have hh := displacement_second_chart_geometry hmesh hL hP (hw n hns) (hbox n hns).1 he
      change label n∈J ∧ 0 < positiveSlopeChartScale mesh (label n) ∧
        positiveSlopeChartScale mesh (label n) ≤ 3/2 ∧
        1 ≤ positiveSlopeChartScale mesh (label n)*P/L ∧
        positiveSlopeChartScale mesh (label n)*P/L ≤ (n:ℝ) ∧
        (n:ℝ) ≤ 2*(positiveSlopeChartScale mesh (label n)*P/L) at hh
      rw [(Finset.mem_filter.mp hni).2] at hh
      exact hh.2.2.2
    by_cases hne : (cell j).Nonempty
    · obtain ⟨n,hni⟩ := hne
      pm_2036
      have hηjle : η ≤ ηj j := hηle.trans
        ((min_le_right _ _).trans (Finset.inf'_le ηj (Finset.mem_attach J j)))
      exact hcount j F η P V N K (cell j) y hFj hη hηjle hP hV hN
        (fun n hn => hy n (Finset.mem_filter.mp hn).1)
        (fun n hn => hu n (Finset.mem_filter.mp hn).1)
        (fun n hn => huk n (Finset.mem_filter.mp hn).1)
        (hgeom n hni).1 (fun n hn => (hgeom n hn).2)
        (fun n hn => (hbox n (Finset.mem_filter.mp hn).1).2) hK
        (fun n hni => hn n (Finset.mem_filter.mp hni).1) W hW hWhalf
        (fun n hn => hnear n (Finset.mem_filter.mp hn).1)
    · have he : cell j=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [he,Finset.card_empty,Nat.cast_zero]
      have hCj₀ : 0 ≤ Cj j := (by norm_num : (0:ℝ)≤1).trans (hCj j)
      positivity
  pm_2033

theorem actual_displacement_near_curve_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 1 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (κ P V N : ℝ) (K : ℤ) (S : Finset ℕ) (u : ℕ → ℝ),
          IsApproximateModelPhaseFunction F σ Q δ → 0 < κ → κ ≤ κ₀ →
          0 < P → 0 < V → 0 < N →
          (∀ n∈S, u n ∈ modelPhaseSlopeRange F) →
          (∀ n∈S, u n+κ ∈ modelPhaseSlopeRange F) →
          let d := fun n => modelPhaseInverseSlope F (u n)-modelPhaseInverseSlope F (u n+κ)
          let R := fun n => 2*(F (modelPhaseInverseSlope F (u n+κ))-
            F (modelPhaseInverseSlope F (u n))-κ*modelPhaseInverseSlope F (u n+κ))
          (∀ n∈S, 2 ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N) → V*κ/P=(K:ℝ) →
          (∀ n∈S, P*d n=(n:ℝ)) →
          ∀ (W : ℝ), 0 < W → W ≤ 1/2 →
          (∀ n∈S, ∃ e : ℤ, |V*R n-(e:ℝ)| ≤ W/2) →
            (S.card:ℝ) ≤ C*(W*N+(V/P)^(k₀+ε)*N^(l₀+ε)*W^(-(k₀+ε))+P/V) := by
  classical
  let mesh := (2:ℝ)^(-σ)/8
  pm_64 hmesh mesh
  have hmesh₂ : 4*mesh ≤ 2 := by
    have hh : (2:ℝ)^(-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    dsimp [mesh]
    linarith
  pm_2037
  pm_2038 A hAj
  have hlocal (j : {j // j∈J}) := actual_displacement_first_chart_count
    hσ (hAj j).1 (hAj j).2 hpair hε hp
  pm_7464
  let δ := min (min ((2:ℝ)^(-σ)/2) 1) (J.attach.inf' ht δj)
  let ηmin := J.attach.inf' ht ηj
  let κ₀ := min mesh (3*mesh*ηmin)
  let Q := max 1 (J.attach.sup Qj)
  pm_7750
  have hδ : 0 < δ := lt_min (lt_min (by positivity) zero_lt_one)
    ((Finset.lt_inf'_iff ht).mpr (fun j _ => hδj j))
  have hηmin : 0 < ηmin := (Finset.lt_inf'_iff ht).mpr (fun j _ => hηj j)
  have hκ₀ : 0 < κ₀ := lt_min hmesh (by positivity)
  pm_4884 hQ Q
  pm_2035
  pm_2039
  intro F κ P V N K S u hF hκ hκle hP hV hN hu huk d R hbox hK hn W hW hWhalf hnear
  have hκmesh : κ ≤ mesh := hκle.trans (min_le_left _ _)
  have hw (n : ℕ) (hns : n∈S) : u n∈Icc (4*mesh) 2 := by
    rw [show 4*mesh=(2:ℝ)^(-σ)/2 by dsimp [mesh]; ring]
    exact modelPhaseSlopeRange_positive_window hσ (min_le_left _ _) hF (hu n hns)
  let label := fun n => positiveSlopeChartIndex mesh (u n)
  pm_2034
  have hcell (j : {j // j∈J}) :
      ((cell j).card:ℝ) ≤ Cj j*(W*N+(V/P)^(k₀+ε)*N^(l₀+ε)*W^(-(k₀+ε))+P/V) := by
    let η := κ/A j
    let y := fun n => (u n/A j-η)/(1-η)
    have hη : 0 < η := div_pos hκ (hAj j).1
    have hk : A j*η=κ := mul_div_cancel₀ κ (hAj j).1.ne'
    have hηle : η ≤ ηj j := by
      have hAmesh : 3*mesh ≤ A j := by
        have hj4 : (4:ℝ) ≤ j.val := by exact_mod_cast (Finset.mem_Icc.mp j.property).1
        dsimp [A,positiveSlopeChartScale]
        nlinarith [mul_le_mul_of_nonneg_right hj4 hmesh.le]
      have hcap : κ ≤ 3*mesh*ηmin := hκle.trans (min_le_right _ _)
      have hmin : ηmin ≤ ηj j := Finset.inf'_le ηj (Finset.mem_attach J j)
      apply (div_le_iff₀ (hAj j).1).mpr
      calc
        κ ≤ 3*mesh*ηmin := hcap
        _ ≤ A j*ηj j := mul_le_mul hAmesh hmin hηmin.le (hAj j).1.le
        _ = ηj j*A j := by ring
    have hgeom (n : ℕ) (hni : n∈cell j) :
        y n∈Ioo (1:ℝ) 2 ∧
          A j*aProcessShiftPoint η 0 (y n)=u n ∧
          A j*aProcessShiftPoint η 1 (y n)=u n+κ := by
      have hns := (Finset.mem_filter.mp hni).1
      have hh := positive_slope_chart_compressed_coordinate hmesh (hw n hns) hκ.le hκmesh
      dsimp only at hh
      have he : positiveSlopeChartIndex mesh (u n)=j.val := (Finset.mem_filter.mp hni).2
      rw [he] at hh
      exact hh.2.2.2.2.2
    pm_2036
    have huj : ∀ n∈cell j, A j*aProcessShiftPoint η 0 (y n)∈modelPhaseSlopeRange F := by
      intro n hni
      rw [(hgeom n hni).2.1]
      exact hu n (Finset.mem_filter.mp hni).1
    have hukj : ∀ n∈cell j, A j*aProcessShiftPoint η 1 (y n)∈modelPhaseSlopeRange F := by
      intro n hni
      rw [(hgeom n hni).2.2]
      exact huk n (Finset.mem_filter.mp hni).1
    have hnj : ∀ n∈cell j, P*(modelPhaseInverseSlope F (A j*aProcessShiftPoint η 0 (y n))-
        modelPhaseInverseSlope F (A j*aProcessShiftPoint η 0 (y n)+A j*η))=(n:ℝ) := by
      pm_6179 hn
    have hnearj : ∀ n∈cell j, ∃ e : ℤ,
        |V*(2*(F (modelPhaseInverseSlope F (A j*aProcessShiftPoint η 0 (y n)+A j*η))-
          F (modelPhaseInverseSlope F (A j*aProcessShiftPoint η 0 (y n)))-
          (A j*η)*modelPhaseInverseSlope F (A j*aProcessShiftPoint η 0 (y n)+A j*η)))-(e:ℝ)| ≤ W/2 := by
      pm_6179 hnear
    exact hcount j F η P V N K (cell j) y hFj hη hηle hP hV hN
      (fun n hn => (hgeom n hn).1) huj hukj
      (fun n hn => hbox n (Finset.mem_filter.mp hn).1)
      (by rw [hk]; exact hK) hnj W hW hWhalf hnearj
  pm_2033

theorem negative_first_derivative_point
    {σ δ z : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hz : z∈Ioo (1:ℝ) 2) :
    let G := fun u => -σ⁻¹*iteratedDerivWithin 1 F phaseInterval u
    G z=-σ⁻¹*deriv F z ∧ deriv G z=-σ⁻¹*deriv (deriv F) z := by
  intro G
  have he : G =ᶠ[𝓝 z] (fun u => -σ⁻¹*deriv F u) := by
    filter_upwards [isOpen_Ioo.mem_nhds hz] with u hu
    dsimp [G]
    rw [iteratedDerivWithin_one]
    have hd : derivWithin F phaseInterval u=deriv F u :=
      derivWithin_of_mem_nhds (Icc_mem_nhds hu.1 hu.2)
    rw [hd]
  refine ⟨he.eq_of_nhds,?_⟩
  rw [he.deriv_eq]
  exact ((approximateModelPhase_deriv_contDiffAt hF hz).differentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)).hasDerivAt.const_mul (-σ⁻¹) |>.deriv

theorem original_derivative_resonance_displacement
    {σ δ T N x q : ℝ} {P : ℕ} {F : ℝ → ℝ} {K : ℤ}
    (hσ : 0 < σ) (hT : 0 < T) (hN : 0 < N) (hP : 1 ≤ P)
    (hδ : δ/σ ≤ min (modelPhaseCurvatureLower (σ+1)) 1)
    (hF : IsApproximateModelPhaseFunction F σ (P+1) δ)
    (hx : x/N∈Ioo (1:ℝ) 2) (hxq : (x+q)/N∈Ioo (1:ℝ) 2) :
    let f := fun z => T*F (z/N)
    let G := fun u => -σ⁻¹*iteratedDerivWithin 1 F phaseInterval u
    let κ := 2*(K:ℝ)*N^2/(σ*T)
    let V := σ*T/(2*N)
    let u := deriv G ((x+q)/N)
    (iteratedDeriv 2 f (x+q)-iteratedDeriv 2 f x)/2=(K:ℝ) →
    u∈modelPhaseSlopeRange G ∧ u+κ∈modelPhaseSlopeRange G ∧
      modelPhaseInverseSlope G u=(x+q)/N ∧
      modelPhaseInverseSlope G (u+κ)=x/N ∧
      N*(modelPhaseInverseSlope G u-modelPhaseInverseSlope G (u+κ))=q ∧
      V*κ/N=(K:ℝ) ∧
      V*(2*(G (modelPhaseInverseSlope G (u+κ))-G (modelPhaseInverseSlope G u)-
          κ*modelPhaseInverseSlope G (u+κ)))=
        iteratedDeriv 1 f (x+q)-iteratedDeriv 1 f x-2*(K:ℝ)*x := by
  intro f G κ V u hlevel
  have hG := negative_first_derivative_model hσ hF
  have hG₁ := approximateModelPhase_mono hG hP (le_refl (δ/σ))
  have hσ₁ : 0 < σ+1 := by linarith
  have hf : modelPhaseFrequencyPhase F T N 0=f := by
    funext z
    simp [modelPhaseFrequencyPhase,f]
  have hd (z : ℝ) (hz : z/N∈Ioo (1:ℝ) 2) :
      iteratedDeriv 1 f z=T/N*deriv F (z/N) ∧
      iteratedDeriv 2 f z=T/N^2*deriv (deriv F) (z/N) := by
    constructor
    · simpa only [hf,iteratedDeriv_one,sub_zero] using
        (modelPhaseFrequencyPhase_hasDerivAt (T:=T) (r:=0) hF hz).deriv
    · simpa only [hf,
        iteratedDeriv_succ,iteratedDeriv_zero] using
        (modelPhaseFrequencyPhase_secondDeriv (T:=T) (r:=0) hF hz)
  have hκeq : u+κ=deriv G (x/N) := by
    dsimp only [u]
    rw [(negative_first_derivative_point hF hxq).2,(negative_first_derivative_point hF hx).2]
    rw [(hd (x+q) hxq).2,(hd x hx).2] at hlevel
    dsimp only [κ]
    field_simp [hσ.ne',hT.ne',hN.ne'] at hlevel ⊢
    nlinarith only [hlevel]
  have hu : u∈modelPhaseSlopeRange G := ⟨(x+q)/N,hxq,rfl⟩
  have huk : u+κ∈modelPhaseSlopeRange G := by rw [hκeq]; exact ⟨x/N,hx,rfl⟩
  have hi : modelPhaseInverseSlope G u=(x+q)/N :=
    modelPhaseInverseSlope_deriv hσ₁ hδ hG₁ hxq
  have hik : modelPhaseInverseSlope G (u+κ)=x/N := by
    rw [hκeq]
    exact modelPhaseInverseSlope_deriv hσ₁ hδ hG₁ hx
  refine ⟨hu,huk,hi,hik,?_,?_,?_⟩
  · rw [hi,hik]
    field_simp
    ring
  · dsimp [V,κ]
    field_simp
  · have hGx : G (x/N)=-σ⁻¹*deriv F (x/N) := (negative_first_derivative_point hF hx).1
    have hGxq : G ((x+q)/N)=-σ⁻¹*deriv F ((x+q)/N) :=
      (negative_first_derivative_point hF hxq).1
    rw [hi,hik,hGx,hGxq,(hd (x+q) hxq).1,(hd x hx).1]
    dsimp [V,κ]
    field_simp
    ring

theorem original_second_level_near_curve_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 2 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (T N D : ℝ) (K : ℤ) (S : Finset ℕ) (x : ℕ → ℝ),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 0 < D → 0 < K →
          2*(K:ℝ)*N^2/(σ*T) ≤ κ₀ →
          (∀ n∈S, x n/N ∈ Ioo (1:ℝ) 2) →
          (∀ n∈S, (x n+(n:ℝ))/N ∈ Ioo (1:ℝ) 2) →
          (∀ n∈S, 2 ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*D) →
          let f := fun z => T*F (z/N)
          (∀ n∈S, (iteratedDeriv 2 f (x n+(n:ℝ))-iteratedDeriv 2 f (x n))/2=(K:ℝ)) →
          ∀ (W : ℝ), 0 < W → W ≤ 1/2 →
          (∀ n∈S, ∃ e : ℤ,
            |iteratedDeriv 1 f (x n+(n:ℝ))-iteratedDeriv 1 f (x n)-
              2*(K:ℝ)*x n-(e:ℝ)| ≤ W/2) →
            (S.card:ℝ) ≤ C*(W*D+(T/N^2)^(k₀+ε)*D^(l₀+ε)*W^(-(k₀+ε))+N^2/T) := by
  have hσ₁ : 0 < σ+1 := by linarith
  obtain ⟨δ₀,κ₀,hδ₀,hκ₀,Q,hQ,C₀,hC₀,hcount⟩ :=
    actual_displacement_near_curve_count hσ₁ hpair hε hp
  let δg := min δ₀ (min (modelPhaseCurvatureLower (σ+1)) 1)
  let δ := σ*δg
  let p := k₀+ε
  let a := (σ/2)^p
  let b := 2/σ
  let L := 1+a+b
  let C := C₀*L
  have hδg : 0 < δg := lt_min hδ₀
    (lt_min (modelPhaseCurvatureLower_pos hσ₁) zero_lt_one)
  have hδ : 0 < δ := mul_pos hσ hδg
  have hquot : δ/σ=δg := by dsimp [δ]; field_simp
  pm_61 ha a
  pm_61 hb b
  pm_1611 hL L
  have hC : 1 ≤ C := by
    dsimp [C]
    pm_385 mul_nonneg sub_nonneg.mpr hC₀ hL
  refine ⟨δ,κ₀,hδ,hκ₀,Q+1,by omega,C,hC,?_⟩
  intro F T N D K S x hF hT hN hD hK hκle hx hxq hbox f hlevel W hW hWhalf hnear
  let G := fun u => -σ⁻¹*iteratedDerivWithin 1 F phaseInterval u
  let κ := 2*(K:ℝ)*N^2/(σ*T)
  let V := σ*T/(2*N)
  let u := fun n => deriv G ((x n+(n:ℝ))/N)
  have hκ : 0 < κ := by
    pm_4411 hKr K hK
    dsimp [κ]
    positivity
  pm_64 hV V
  have hG : IsApproximateModelPhaseFunction G (σ+1) Q δ₀ := by
    pm_126 hh negative_first_derivative_model hσ hF hquot
    exact approximateModelPhase_mono hh le_rfl (min_le_left _ _)
  have hgeom (n : ℕ) (hns : n∈S) :=
    original_derivative_resonance_displacement hσ hT hN hQ
      (by rw [hquot]; exact min_le_right _ _)
      hF (hx n hns) (hxq n hns) (hlevel n hns)
  have hu : ∀ n∈S, u n∈modelPhaseSlopeRange G := fun n hns => (hgeom n hns).1
  have huk : ∀ n∈S, u n+κ∈modelPhaseSlopeRange G := fun n hns => (hgeom n hns).2.1
  have hdis : ∀ n∈S, N*(modelPhaseInverseSlope G (u n)-modelPhaseInverseSlope G (u n+κ))=(n:ℝ) :=
    fun n hns => (hgeom n hns).2.2.2.2.1
  have hres : V*κ/N=(K:ℝ) := by dsimp [V,κ]; field_simp
  have hnear' : ∀ n∈S, ∃ e : ℤ,
      |V*(2*(G (modelPhaseInverseSlope G (u n+κ))-G (modelPhaseInverseSlope G (u n))-
          κ*modelPhaseInverseSlope G (u n+κ)))-(e:ℝ)| ≤ W/2 := by
    intro n hns
    have hh := (hgeom n hns).2.2.2.2.2.2
    change V*(2*(G (modelPhaseInverseSlope G (u n+κ))-G (modelPhaseInverseSlope G (u n))-
      κ*modelPhaseInverseSlope G (u n+κ)))=
        iteratedDeriv 1 f (x n+(n:ℝ))-iteratedDeriv 1 f (x n)-2*(K:ℝ)*x n at hh
    rw [hh]
    exact hnear n hns
  have hh := hcount G κ N V D K S u hG hκ hκle hN hV hD hu huk hbox hres hdis W hW hWhalf hnear'
  have hfreq : (V/N)^p=a*(T/N^2)^p := by
    have he : V/N=(σ/2)*(T/N^2) := by dsimp [V]; field_simp
    rw [he,Real.mul_rpow (by positivity : 0 ≤ σ/2) (by positivity : 0 ≤ T/N^2)]
  have htail : N/V=b*(N^2/T) := by dsimp [V,b]; field_simp
  change (S.card:ℝ) ≤ C₀*(W*D+(V/N)^p*D^(l₀+ε)*W^(-p)+N/V) at hh
  rw [hfreq,htail] at hh
  pm_182 haL a L
  pm_182 hbL b L
  have hv : W*D ≤ L*(W*D) := le_mul_of_one_le_left (by positivity) hL
  calc
    _ ≤ C₀*(W*D+a*((T/N^2)^p*D^(l₀+ε)*W^(-p))+b*(N^2/T)) := by
      convert hh using 1; ring
    _ ≤ C₀*(L*(W*D)+L*((T/N^2)^p*D^(l₀+ε)*W^(-p))+L*(N^2/T)) := by gcongr
    _ = _ := by dsimp [C,p]; ring

theorem cubic_second_difference_derivative
    (f : ℝ → ℝ) {x q B lam : ℝ} (hq : 0 < q)
    (hf : ∀ t∈Icc x (x+q), ContDiffAt ℝ 4 f t)
    (hfour : ∀ t∈Icc x (x+q),
      -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam) :
    HasDerivAt (fun t => (iteratedDeriv 2 f (t+q)-iteratedDeriv 2 f t)/2)
      ((iteratedDeriv 3 f (x+q)-iteratedDeriv 3 f x)/2) x ∧
    -(B*q/2) ≤ (iteratedDeriv 3 f (x+q)-iteratedDeriv 3 f x)/2 ∧
      (iteratedDeriv 3 f (x+q)-iteratedDeriv 3 f x)/2 ≤ -(lam*q/2) := by
  have hxx : x ≤ x+q := by linarith
  have hd (t : ℝ) (ht : t∈Icc x (x+q)) :
      HasDerivAt (iteratedDeriv 3 f) (iteratedDeriv 4 f t) t :=
    hasDerivAt_iteratedDeriv_finite (j:=3) (by norm_num : 3 < 4) (hf t ht)
  have hd₀ := hasDerivAt_iteratedDeriv_finite (j:=2) (by norm_num : 2 < 4)
    (hf x ⟨le_rfl,hxx⟩)
  have hd₁ := hasDerivAt_iteratedDeriv_finite (j:=2) (by norm_num : 2 < 4)
    (hf (x+q) ⟨hxx,le_rfl⟩)
  constructor
  · convert ((hd₁.comp x ((hasDerivAt_id x).add_const q)).sub hd₀).div_const 2 using 1
    · funext t
      simp only [Pi.sub_apply,Function.comp_apply,id_eq,add_comm]
    · norm_num
  obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope (iteratedDeriv 3 f)
    (iteratedDeriv 4 f) (show x < x+q by linarith)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t ⟨ht.1.le,ht.2.le⟩)
  have he' : iteratedDeriv 4 f t*q=iteratedDeriv 3 f (x+q)-iteratedDeriv 3 f x := by
    pm_7919 hh x
    nlinarith only [hh]
  pm_5737 hfour hq.le
  constructor <;> nlinarith only [he',hlo,hhi]

section
variable (f : ℝ → ℝ)
include f
theorem cubic_exact_second_difference_level {n q B lam R δ K : ℝ}
    (hq : 0 < q) (hR : 0 < R)
    (hbudget : δ ≤ lam*q*R/2)
    (hf : ∀ t∈Icc (n-R) (n+R+q), ContDiffAt ℝ 4 f t)
    (hfour : ∀ t∈Icc (n-R) (n+R+q),
      -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam)
    (hnear : |(iteratedDeriv 2 f (n+q)-iteratedDeriv 2 f n)/2-K| ≤ δ) :
    ∃ x∈Icc (n-R) (n+R),
      (iteratedDeriv 2 f (x+q)-iteratedDeriv 2 f x)/2=K ∧ |x-n| ≤ R := by
  pm_2040
  have hsub (x : ℝ) (hx : x∈Icc (n-R) (n+R)) :
      Icc x (x+q) ⊆ Icc (n-R) (n+R+q) := by
    intro t ht
    constructor <;> linarith [hx.1,hx.2,ht.1,ht.2]
  have hd (x : ℝ) (hx : x∈Icc (n-R) (n+R)) :
      HasDerivAt g (dg x) x ∧ dg x ≤ -(lam*q/2) := by
    have hh := cubic_second_difference_derivative f hq
      (fun t ht => hf t (hsub x hx ht)) (fun t ht => hfour t (hsub x hx ht))
    exact ⟨hh.1,hh.2.2⟩
  have hdec {a b : ℝ} (hab : a < b)
      (ha : n-R ≤ a) (hb : b ≤ n+R) :
      g b-g a ≤ -(lam*q/2)*(b-a) := by
    have hi (t : ℝ) (ht : t∈Icc a b) : t∈Icc (n-R) (n+R) :=
      ⟨ha.trans ht.1,ht.2.trans hb⟩
    pm_2041 hab hi
    have hh := mul_le_mul_of_nonneg_right (hd t (hi t ⟨ht.1.le,ht.2.le⟩)).2
      (sub_nonneg.mpr hab.le)
    nlinarith only [he',hh]
  have hleft := hdec (a:=n-R) (b:=n) (by linarith) le_rfl (by linarith)
  have hright := hdec (a:=n) (b:=n+R) (by linarith) (by linarith) le_rfl
  have hnear' : |g n-K| ≤ δ := hnear
  have hK : K∈Icc (g (n+R)) (g (n-R)) := by
    have hh := abs_le.mp hnear'
    constructor <;> nlinarith only [hleft,hright,hbudget,hh.1,hh.2]
  obtain ⟨x,hx,he⟩ := intermediate_value_Icc' (by linarith : n-R ≤ n+R)
    (fun t ht => (hd t ht).1.continuousAt.continuousWithinAt) hK
  exact ⟨x,hx,he,abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩⟩

theorem cubic_stationary_curve_near_integer (n K e : ℤ) {x q B lam R δ : ℝ}
    (hq : 0 < q) (hlam : 0 < lam) (hR : 0 ≤ R)
    (hx : x∈Icc ((n:ℝ)-R) ((n:ℝ)+R))
    (hf : ∀ t∈Icc ((n:ℝ)-R) ((n:ℝ)+R+q), ContDiffAt ℝ 4 f t)
    (hfour : ∀ t∈Icc ((n:ℝ)-R) ((n:ℝ)+R+q),
      -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam)
    (hlevel : (iteratedDeriv 2 f (x+q)-iteratedDeriv 2 f x)/2=(K:ℝ))
    (hnear : |iteratedDeriv 1 f ((n:ℝ)+q)-iteratedDeriv 1 f n-(e:ℝ)| ≤ δ) :
    |(iteratedDeriv 1 f (x+q)-iteratedDeriv 1 f x-2*(K:ℝ)*x)-
      ((e-2*K*n:ℤ):ℝ)| ≤ δ+B*q*R^2 := by
  let G := fun t => iteratedDeriv 1 f (t+q)-iteratedDeriv 1 f t-2*(K:ℝ)*t
  let G₁ := fun t => iteratedDeriv 2 f (t+q)-iteratedDeriv 2 f t-2*(K:ℝ)
  let G₂ := fun t => iteratedDeriv 3 f (t+q)-iteratedDeriv 3 f t
  have hsub (t : ℝ) (ht : t∈uIcc x (n:ℝ)) : t∈Icc ((n:ℝ)-R) ((n:ℝ)+R) :=
    (convex_Icc _ _).ordConnected.uIcc_subset hx ⟨by linarith,by linarith⟩ ht
  have hseg (t : ℝ) (ht : t∈uIcc x (n:ℝ)) :
      Icc t (t+q) ⊆ Icc ((n:ℝ)-R) ((n:ℝ)+R+q) := by
    intro z hz
    have hh := hsub t ht
    constructor <;> linarith [hh.1,hh.2,hz.1,hz.2]
  have hjets (t : ℝ) (ht : t∈uIcc x (n:ℝ)) :
      HasDerivAt G (G₁ t) t ∧ HasDerivAt G₁ (G₂ t) t ∧ |G₂ t| ≤ B*q := by
    have hI := hseg t ht
    have ht₀ := hf t (hI ⟨le_rfl,by linarith⟩)
    have ht₁ := hf (t+q) (hI ⟨by linarith,le_rfl⟩)
    have hd (j : ℕ) (hj : j < 4) :
        HasDerivAt (fun z => iteratedDeriv j f (z+q)-iteratedDeriv j f z)
          (iteratedDeriv (j+1) f (t+q)-iteratedDeriv (j+1) f t) t := by
      pm_733 h₀ hasDerivAt_iteratedDeriv_finite hj ht₀ h₁ ht₁
      convert (h₁.comp t ((hasDerivAt_id t).add_const q)).sub h₀ using 1
      · funext z
        simp only [Function.comp_apply,Pi.sub_apply,id_eq,add_comm]
      · simp only [mul_one]
    constructor
    · convert (hd 1 (by norm_num)).sub ((hasDerivAt_id t).const_mul (2*(K:ℝ))) using 1
      · funext z
        dsimp only [G,Pi.sub_apply,id_eq]
      · dsimp only [G₁]
        norm_num
    constructor
    · exact (hd 2 (by norm_num)).sub_const (2*(K:ℝ))
    · have hh := cubic_second_difference_derivative f hq
        (fun z hz => hf z (hI hz)) (fun z hz => hfour z (hI hz))
      dsimp only [G₂]
      apply abs_le.mpr
      constructor <;> nlinarith [hh.2.1,hh.2.2,mul_pos hlam hq]
  have hB : 0 ≤ B := by
    have hh := hfour n ⟨by linarith,by linarith⟩
    linarith [hh.1,hh.2]
  have hG₁x : G₁ x=0 := by dsimp only [G₁]; linarith only [hlevel]
  have hdist : |(n:ℝ)-x| ≤ R := by
    pm_8312
  have hfirst (t : ℝ) (ht : t∈uIcc x (n:ℝ)) : |G₁ t| ≤ B*q*R := by
    have hh := (convex_uIcc x (n:ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz => (hjets z hz).2.1.hasDerivWithinAt)
      (fun z hz => by simpa only [Real.norm_eq_abs] using (hjets z hz).2.2)
      left_mem_uIcc ht
    rw [hG₁x,sub_zero,Real.norm_eq_abs,Real.norm_eq_abs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      ((abs_sub_left_of_mem_uIcc ht).trans hdist) (mul_nonneg hB hq.le))
  have herror := (convex_uIcc x (n:ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (hjets z hz).1.hasDerivWithinAt)
    (fun z hz => by simpa only [Real.norm_eq_abs] using hfirst z hz)
    left_mem_uIcc right_mem_uIcc
  rw [Real.norm_eq_abs,Real.norm_eq_abs] at herror
  have herror' : |G x-G n| ≤ B*q*R^2 := by
    rw [abs_sub_comm]
    exact herror.trans ((mul_le_mul_of_nonneg_left hdist (by positivity : 0 ≤ B*q*R)).trans_eq (by ring))
  have hnear' : |G n-((e-2*K*n:ℤ):ℝ)| ≤ δ := by
    pm_7902 hnear G
    push_cast
    ring
  have hh := (abs_sub_le (G x) (G n) ((e-2*K*n:ℤ):ℝ)).trans (add_le_add herror' hnear')
  change |G x-((e-2*K*n:ℤ):ℝ)| ≤ _
  exact hh.trans_eq (by ring)

theorem cubicDerivativePairs_integer_resonances {M H : ℕ} {p : ℕ × ℕ}
    (hp : p∈cubicDerivativePairs f M H) :
    p.1 < M ∧ p.2 < M ∧
    ∃ e K : ℤ,
      |iteratedDeriv 1 f ((p.2:ℝ)+1)-iteratedDeriv 1 f ((p.1:ℝ)+1)-(e:ℝ)| ≤ 1/(4*(H:ℝ)) ∧
      |(iteratedDeriv 2 f ((p.2:ℝ)+1)-iteratedDeriv 2 f ((p.1:ℝ)+1))/2-(K:ℝ)| ≤
        1/(4*(H:ℝ)^2) ∧
      |iteratedDeriv 3 f ((p.2:ℝ)+1)-iteratedDeriv 3 f ((p.1:ℝ)+1)| ≤
        3/(2*(H:ℝ)^3) := by
  obtain ⟨hmem,hnear⟩ := Finset.mem_filter.mp hp
  have hmem' := Finset.mem_product.mp hmem
  refine ⟨Finset.mem_range.mp hmem'.1,Finset.mem_range.mp hmem'.2,
    ⌊deriv f ((p.2:ℝ)+1)⌋-⌊deriv f ((p.1:ℝ)+1)⌋,
    ⌊iteratedDeriv 2 f ((p.2:ℝ)+1)/2⌋-⌊iteratedDeriv 2 f ((p.1:ℝ)+1)/2⌋,
    ?_,?_,?_⟩
  · have hh := hnear 0
    change |Int.fract (deriv f ((p.1:ℝ)+1))-Int.fract (deriv f ((p.2:ℝ)+1))| ≤
      2*(1/(8*(H:ℝ))) at hh
    rw [abs_sub_comm] at hh
    convert hh using 1
    · congr 1
      simp only [Int.fract,Int.cast_sub,iteratedDeriv_one]
      ring
    · ring
  · have hh := hnear 1
    change |Int.fract (iteratedDeriv 2 f ((p.1:ℝ)+1)/2)-
      Int.fract (iteratedDeriv 2 f ((p.2:ℝ)+1)/2)| ≤ 2*(1/(8*(H:ℝ)^2)) at hh
    rw [abs_sub_comm] at hh
    convert hh using 1
    · congr 1
      simp only [Int.fract,Int.cast_sub]
      ring
    · ring
  · have hh := hnear 2
    change |iteratedDeriv 3 f ((p.1:ℝ)+1)/6-iteratedDeriv 3 f ((p.2:ℝ)+1)/6| ≤
      2*(1/(8*(H:ℝ)^3)) at hh
    rw [abs_sub_comm,←sub_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<6)] at hh
    have he := (div_le_iff₀ (by norm_num : (0:ℝ)<6)).mp hh
    exact he.trans_eq (by ring)

theorem cubicDerivativePairs_displacement {M H : ℕ} {p : ℕ × ℕ} {lam : ℝ}
    (hH : 1 ≤ H) (hlam : 0 < lam)
    (hp : p∈cubicDerivativePairs f M H) (hlt : p.1 < p.2)
    (hf : ∀ t∈Icc ((p.1:ℝ)+1) ((p.2:ℝ)+1), ContDiffAt ℝ 4 f t)
    (hfour : ∀ t∈Icc ((p.1:ℝ)+1) ((p.2:ℝ)+1), iteratedDeriv 4 f t ≤ -lam) :
    (p.2:ℝ)-p.1 ≤ 3/(2*lam*(H:ℝ)^3) := by
  obtain ⟨_,_,e,K,_hfirst,_hsecond,hthird⟩ := cubicDerivativePairs_integer_resonances f hp
  pm_1671 hHpos H
  have hxy : (p.1:ℝ)+1 < (p.2:ℝ)+1 := by exact_mod_cast Nat.add_lt_add_right hlt 1
  have hd (t : ℝ) (ht : t∈Icc ((p.1:ℝ)+1) ((p.2:ℝ)+1)) :
      HasDerivAt (iteratedDeriv 3 f) (iteratedDeriv 4 f t) t :=
    hasDerivAt_iteratedDeriv_finite (j:=3) (by norm_num : 3 < 4) (hf t ht)
  obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope (iteratedDeriv 3 f)
    (iteratedDeriv 4 f) hxy
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t ⟨ht.1.le,ht.2.le⟩)
  have he' := (eq_div_iff (sub_pos.mpr hxy).ne').mp he
  have hlow := mul_le_mul_of_nonneg_right (hfour t ⟨ht.1.le,ht.2.le⟩) (sub_pos.mpr hxy).le
  have hprod : lam*((p.2:ℝ)-p.1) ≤ 3/(2*(H:ℝ)^3) := by
    have hab := abs_le.mp hthird
    nlinarith only [he',hlow,hab.1]
  have hh : (p.2:ℝ)-p.1 ≤ (3/(2*(H:ℝ)^3))/lam :=
    (le_div_iff₀ hlam).mpr (by nlinarith only [hprod])
  exact hh.trans_eq (by ring)

theorem cubic_second_difference_fiber_card (S : Finset ℤ) {a b q B lam δ K : ℝ}
    (hq : 0 < q) (hlam : 0 < lam) (hδ : 0 ≤ δ)
    (hf : ∀ t∈Icc a (b+q), ContDiffAt ℝ 4 f t)
    (hfour : ∀ t∈Icc a (b+q),
      -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam)
    (hS : ∀ n∈S, (n:ℝ)∈Icc a b)
    (hnear : ∀ n∈S, |(iteratedDeriv 2 f ((n:ℝ)+q)-iteratedDeriv 2 f n)/2-K| ≤ δ) :
    (S.card:ℝ) ≤ 4*δ/(lam*q)+1 := by
  classical
  by_cases hne : S.Nonempty
  · let n₀ := S.min' hne
    have hn₀ : n₀∈S := Finset.min'_mem S hne
    pm_2040
    have hd (t : ℝ) (ht : t∈Icc a b) : HasDerivAt g (dg t) t ∧ dg t ≤ -(lam*q/2) := by
      have hsub : Icc t (t+q) ⊆ Icc a (b+q) := by
        intro z hz
        constructor <;> linarith [ht.1,ht.2,hz.1,hz.2]
      have hh := cubic_second_difference_derivative f hq
        (fun z hz => hf z (hsub hz)) (fun z hz => hfour z (hsub hz))
      exact ⟨hh.1,hh.2.2⟩
    have hbound (n : ℤ) (hn : n∈S) :
        (n₀:ℝ) ≤ n ∧ (n:ℝ) ≤ n₀+4*δ/(lam*q) := by
      have hle : n₀ ≤ n := Finset.min'_le S n hn
      pm_404 hleR n₀ n hle
      refine ⟨hleR,?_⟩
      rcases eq_or_lt_of_le hleR with heq|hlt
      · rw [←heq]
        exact le_add_of_nonneg_right (by positivity)
      have hsub (t : ℝ) (ht : t∈Icc (n₀:ℝ) n) : t∈Icc a b :=
        ⟨(hS n₀ hn₀).1.trans ht.1,ht.2.trans (hS n hn).2⟩
      pm_2041 hlt hsub
      have hdec := mul_le_mul_of_nonneg_right (hd t (hsub t ⟨ht.1.le,ht.2.le⟩)).2
        (sub_pos.mpr hlt).le
      have hnear₀ : |g n₀-K| ≤ δ := hnear n₀ hn₀
      have hnear₁ : |g n-K| ≤ δ := hnear n hn
      have hp : ((n:ℝ)-n₀)*(lam*q) ≤ 4*δ := by
        have hh₀ := abs_le.mp hnear₀
        have hh₁ := abs_le.mp hnear₁
        nlinarith only [he',hdec,hh₀.2,hh₁.1]
      have hh := (le_div_iff₀ (mul_pos hlam hq)).mpr hp
      linarith
    have hinterval : (n₀:ℝ) ≤ n₀+4*δ/(lam*q) :=
      le_add_of_nonneg_right (by positivity)
    have hcount := integer_card_le_interval_length_add_one S hinterval
      hbound
    exact hcount.trans_eq (by ring)
  pm_2032

theorem cubic_second_level_positive (K : ℤ) {n q L U δ : ℝ}
    (hq : 1 ≤ q) (hL : 0 < L)
    (hδL : δ ≤ L/4) (hδhalf : δ ≤ 1/2)
    (hf : ∀ t∈Icc n (n+q), ContDiffAt ℝ 3 f t)
    (hthree : ∀ t∈Icc n (n+q),
      L ≤ iteratedDeriv 3 f t ∧ iteratedDeriv 3 f t ≤ U)
    (hnear : |(iteratedDeriv 2 f (n+q)-iteratedDeriv 2 f n)/2-(K:ℝ)| ≤ δ) :
    0 < K ∧ 0 < U ∧ 1/U ≤ q ∧ (K:ℝ) ≤ U*q := by
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hU : 0 < U := hL.trans_le ((hthree n ⟨le_rfl,by linarith⟩).1.trans
    (hthree n ⟨le_rfl,by linarith⟩).2)
  have hd (t : ℝ) (ht : t∈Icc n (n+q)) :
      HasDerivAt (iteratedDeriv 2 f) (iteratedDeriv 3 f t) t :=
    hasDerivAt_iteratedDeriv_finite (j:=2) (by norm_num : 2 < 3) (hf t ht)
  obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope (iteratedDeriv 2 f)
    (iteratedDeriv 3 f) (show n < n+q by linarith)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t ⟨ht.1.le,ht.2.le⟩)
  pm_7919 he' n
  pm_5737 hthree hqpos.le
  have hab := abs_le.mp hnear
  have hLq : L ≤ L*q := by nlinarith only [mul_le_mul_of_nonneg_left hq hL.le]
  have hKpos : (0:ℝ) < K := by nlinarith only [he',hlo,hab.2,hδL,hLq,hL]
  have hKi : 0 < K := by exact_mod_cast hKpos
  pm_6571 hK1 K
  refine ⟨hKi,hU,?_,?_⟩
  · apply (div_le_iff₀ hU).mpr
    nlinarith only [he',hhi,hab.1,hδhalf,hK1]
  · have hLU : L ≤ U := (hthree t ⟨ht.1.le,ht.2.le⟩).1.trans
      (hthree t ⟨ht.1.le,ht.2.le⟩).2
    have hUq : U ≤ U*q := by nlinarith only [mul_le_mul_of_nonneg_left hq hU.le]
    nlinarith only [he',hhi,hab.1,hδL,hLU,hUq,hU]
end

set_option hygiene false in
macro "pb_446" : tactic => `(tactic| (
  have hnorm (t : ℝ) (ht : t∈Icc (a-R) (b+R+2*D)) :
      t/N∈Ioo (1:ℝ) 2 := by
    constructor
    · apply (one_lt_div hN).mpr
      linarith [ht.1]
    · apply (div_lt_iff₀ hN).mpr
      linarith [ht.2]
  have hf (t : ℝ) (ht : t∈Icc (a-R) (b+R+2*D)) : ContDiffAt ℝ 4 f t := by
    have hc := (approximateModelPhase_contDiffAt hF (hnorm t ht)).comp t
      (show ContDiffAt ℝ ∞ (fun z : ℝ => z/N) t by fun_prop)
    exact (contDiffAt_const.mul hc).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)))
theorem original_joint_level_block_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 2 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (T N D a b R B lam δ₁ δ₂ W : ℝ)
          (K : ℤ) (S : Finset (ℤ × ℕ)),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 2 ≤ D → 0 < R → 0 ≤ B → 0 < lam → 0 ≤ δ₂ →
          N < a-R → b+R+2*D < 2*N →
          δ₂ ≤ lam*D*R/2 → δ₁+2*B*D*R^2 ≤ W/2 →
          0 < K → 2*(K:ℝ)*N^2/(σ*T) ≤ κ₀ → 0 < W → W ≤ 1/2 →
          let f := fun z => T*F (z/N)
          (∀ t∈Icc (a-R) (b+R+2*D),
            -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam) →
          (∀ p∈S, (p.1:ℝ)∈Icc a b ∧ (p.2:ℝ)∈Icc D (2*D)) →
          (∀ p∈S, |(iteratedDeriv 2 f ((p.1:ℝ)+(p.2:ℝ))-
            iteratedDeriv 2 f p.1)/2-(K:ℝ)| ≤ δ₂) →
          (∀ p∈S, ∃ e : ℤ, |iteratedDeriv 1 f ((p.1:ℝ)+(p.2:ℝ))-
            iteratedDeriv 1 f p.1-(e:ℝ)| ≤ δ₁) →
            (S.card:ℝ) ≤ (4*δ₂/(lam*D)+1)*
              (C*(W*D+(T/N^2)^(k₀+ε)*D^(l₀+ε)*W^(-(k₀+ε))+N^2/T)) := by
  pm_2046 δ hδ Q hQ C hC hcount original_second_level_near_curve_count
  pm_2039
  intro F T N D a b R B lam δ₁ δ₂ W K S hF hT hN hD hR hB hlam hδ₂
    hleft hright hbuffer hwidth hK hκle hW hWhalf f hfour hbox hsecond hfirst
  have hDpos : 0 < D := by linarith
  let J := S.image Prod.snd
  have hmem (q : ℕ) (hq : q∈J) : D ≤ (q:ℝ) ∧ (q:ℝ) ≤ 2*D := by
    pm_2044
  pb_446
  have hex (q : ℕ) (hq : q∈J) :
      ∃ x : ℝ, x/N∈Ioo (1:ℝ) 2 ∧ (x+(q:ℝ))/N∈Ioo (1:ℝ) 2 ∧
        (iteratedDeriv 2 f (x+(q:ℝ))-iteratedDeriv 2 f x)/2=(K:ℝ) ∧
        ∃ e : ℤ, |iteratedDeriv 1 f (x+(q:ℝ))-iteratedDeriv 1 f x-
          2*(K:ℝ)*x-(e:ℝ)| ≤ W/2 := by
    pm_5286 hDpos.trans_le
    pm_2042
  pm_2043
  pm_2047 hD.trans
  have hfiber (q : ℕ) (hq : q∈J) :
      ((S.filter (fun p => p.2=q)).card:ℝ) ≤ 4*δ₂/(lam*D)+1 := by
    let U := S.filter (fun p => p.2=q)
    let Y := U.image Prod.fst
    have hinj : Set.InjOn (Prod.fst : ℤ × ℕ → ℤ) U := by
      pm_7620 r hr
    have hcard : Y.card=U.card := Finset.card_image_of_injOn hinj
    have hsub : Icc a (b+(q:ℝ)) ⊆ Icc (a-R) (b+R+2*D) := by
      intro t ht
      constructor <;> linarith [ht.1,ht.2,(hmem q hq).2]
    have hY : ∀ n∈Y, (n:ℝ)∈Icc a b := by
      pm_1672
      exact (hbox p (Finset.mem_filter.mp hp).1).1
    have hnear : ∀ n∈Y,
        |(iteratedDeriv 2 f ((n:ℝ)+(q:ℝ))-iteratedDeriv 2 f n)/2-(K:ℝ)| ≤ δ₂ := by
      pm_1672
      simpa only [(Finset.mem_filter.mp hp).2] using hsecond p (Finset.mem_filter.mp hp).1
    have hh := cubic_second_difference_fiber_card f Y
      (hDpos.trans_le (hmem q hq).1) hlam hδ₂
      (fun t ht => hf t (hsub ht)) (fun t ht => hfour t (hsub ht)) hY hnear
    rw [hcard] at hh
    have hquot : 4*δ₂/(lam*(q:ℝ)) ≤ 4*δ₂/(lam*D) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hlam hDpos)
        (mul_le_mul_of_nonneg_left (hmem q hq).1 hlam.le)
    linarith only [hh,hquot]
  have hmaps : Set.MapsTo (Prod.snd : ℤ × ℕ → ℕ) S J := by
    pm_1673
  pm_2045
  calc
    _ = _ := hcard
    _ ≤ ∑ _q∈J, (4*δ₂/(lam*D)+1) := Finset.sum_le_sum hfiber
    _ = (4*δ₂/(lam*D)+1)*(J.card:ℝ) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcountJ (by positivity)

theorem original_joint_dyadic_block_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 3 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (T N D a b R δ₁ δ₂ W : ℝ) (S : Finset (ℤ × ℕ)),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 2 ≤ D → 0 < R → 0 ≤ δ₂ →
          N < a-R → b+R+2*D < 2*N →
          let lam := modelPhaseJetLower σ 3*T/N^4
          let B := (modelPhaseJetCoefficient σ 3+1)*T/N^4
          let L := modelPhaseJetLower σ 2*T/N^3
          let U := (modelPhaseJetCoefficient σ 2+1)*T/N^3
          δ₂ ≤ lam*D*R/2 → δ₁+2*B*D*R^2 ≤ W/2 →
          δ₂ ≤ L/4 → δ₂ ≤ 1/2 →
          4*U*D*N^2/(σ*T) ≤ κ₀ → 0 < W → W ≤ 1/2 →
          let f := fun z => T*F (z/N)
          (∀ p∈S, (p.1:ℝ)∈Icc a b ∧ (p.2:ℝ)∈Icc D (2*D)) →
          (∀ p∈S, ∃ K : ℤ, |(iteratedDeriv 2 f ((p.1:ℝ)+(p.2:ℝ))-
            iteratedDeriv 2 f p.1)/2-(K:ℝ)| ≤ δ₂) →
          (∀ p∈S, ∃ e : ℤ, |iteratedDeriv 1 f ((p.1:ℝ)+(p.2:ℝ))-
            iteratedDeriv 1 f p.1-(e:ℝ)| ≤ δ₁) →
            (S.card:ℝ) ≤ (2*U*D)*(4*δ₂/(lam*D)+1)*
              (C*(W*D+(T/N^2)^(k₀+ε)*D^(l₀+ε)*W^(-(k₀+ε))+N^2/T)) := by
  pm_2046 δ₀ hδ₀ Q₀ hQ₀ C hC hcount original_joint_level_block_count
  pm_2051
  pm_2050
  intro F T N D a b R δ₁ δ₂ W S hF hT hN hD hR hδ₂ hleft hright
    lam B L U hbuffer hwidth hδL hδhalf hshift hW hWhalf f hbox hsecond hfirst
  pm_2048
  pm_2053
  have hDpos : 0 < D := by linarith
  pm_2049
  have hB : 0 ≤ B := by dsimp [B]; positivity [modelPhaseJetCoefficient_pos hσ 3]
  pm_2052
  pm_2054 δ₂
  have hlevels (p : ℤ × ℕ) (hps : p∈S) :
      0 < level p ∧ (level p:ℝ) ≤ 2*U*D := by
    have hprange := hbox p hps
    have hq : 1 ≤ (p.2:ℝ) := by linarith [hprange.2.1]
    have hsub : Icc (p.1:ℝ) ((p.1:ℝ)+(p.2:ℝ)) ⊆ Ioo N (2*N) := by
      intro t ht
      apply hsegment
      constructor <;> linarith [ht.1,ht.2,hprange.1.1,hprange.1.2,hprange.2.2]
    have hh := cubic_second_level_positive f (level p) hq hL hδL hδhalf
      (fun t ht => (hreg t (hsub ht)).of_le (by norm_num))
      (fun t ht => hthree t (hsub ht)) (hlevel p hps)
    exact ⟨hh.1,hh.2.2.2.trans (by nlinarith [mul_le_mul_of_nonneg_left hprange.2.2 hU.le])⟩
  let J := S.image level
  have hJbound : (J.card:ℝ) ≤ 2*U*D := by
    by_cases hne : J.Nonempty
    · have hJ (K : ℤ) (hK : K∈J) : (1:ℝ) ≤ K ∧ (K:ℝ) ≤ 2*U*D := by
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hK
        have hh := hlevels p hp
        pm_5815
      pm_6541 hb J hJ hb.trans_eq
    pm_6617 J
  let X := C*(W*D+(T/N^2)^(k₀+ε)*D^(l₀+ε)*W^(-(k₀+ε))+N^2/T)
  let Z := 4*δ₂/(lam*D)+1
  pm_61 hX X
  pm_61 hZ Z
  have hcell (K : ℤ) (hK : K∈J) :
      ((S.filter (fun p => level p=K)).card:ℝ) ≤ Z*X := by
    obtain ⟨p,hps,hpK⟩ := Finset.mem_image.mp hK
    have hKpos : 0 < K := by rw [← hpK]; exact (hlevels p hps).1
    have hKbound : (K:ℝ) ≤ 2*U*D := by rw [← hpK]; exact (hlevels p hps).2
    have hκle : 2*(K:ℝ)*N^2/(σ*T) ≤ κ₀ := by
      calc
        _ ≤ 2*(2*U*D)*N^2/(σ*T) := by gcongr
        _ = 4*U*D*N^2/(σ*T) := by ring
        _ ≤ κ₀ := hshift
    have hsec : ∀ p∈S.filter (fun p => level p=K),
        |(iteratedDeriv 2 f ((p.1:ℝ)+(p.2:ℝ))-iteratedDeriv 2 f p.1)/2-(K:ℝ)| ≤ δ₂ := by
      intro p hp
      rw [← (Finset.mem_filter.mp hp).2]
      exact hlevel p (Finset.mem_filter.mp hp).1
    exact hcount F T N D a b R B lam δ₁ δ₂ W K (S.filter (fun p => level p=K))
      hF₀ hT hN hD hR hB hlam hδ₂ hleft hright hbuffer hwidth hKpos hκle hW hWhalf
      (fun t ht => hfour t (hsegment ht))
      (fun p hp => hbox p (Finset.mem_filter.mp hp).1) hsec
      (fun p hp => hfirst p (Finset.mem_filter.mp hp).1)
  have hmaps : Set.MapsTo level S J := by
    pm_1673
  pm_5330 S.card J S.filter
  calc
    _ = _ := hcard
    _ ≤ ∑ _K∈J, Z*X := Finset.sum_le_sum hcell
    _ = (J.card:ℝ)*(Z*X) := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (2*U*D)*(Z*X) := mul_le_mul_of_nonneg_right hJbound (mul_nonneg hZ hX)
    _ = _ := by dsimp [Z,X]; ring

theorem cubic_short_displacement_count
    (f : ℝ → ℝ) (S : Finset (ℤ × ℕ)) {a b D B lam L U δ : ℝ}
    (hD : 1 ≤ D) (hlam : 0 < lam) (hL : 0 < L) (hU : 0 < U) (hδ : 0 ≤ δ)
    (hδL : δ ≤ L/4) (hδhalf : δ ≤ 1/2)
    (hf : ∀ t∈Icc a (b+D), ContDiffAt ℝ 4 f t)
    (hthree : ∀ t∈Icc a (b+D), L ≤ iteratedDeriv 3 f t ∧ iteratedDeriv 3 f t ≤ U)
    (hfour : ∀ t∈Icc a (b+D), -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam)
    (hbox : ∀ p∈S, (p.1:ℝ)∈Icc a b ∧ (p.2:ℝ)∈Icc 1 D)
    (hsecond : ∀ p∈S, ∃ K : ℤ,
      |(iteratedDeriv 2 f ((p.1:ℝ)+(p.2:ℝ))-iteratedDeriv 2 f p.1)/2-(K:ℝ)| ≤ δ) :
    (S.card:ℝ) ≤ D*(4*U*δ/lam+U*D) := by
  classical
  pm_2054 δ
  have hlevels (p : ℤ × ℕ) (hps : p∈S) :
      0 < level p ∧ (level p:ℝ) ≤ U*(p.2:ℝ) := by
    have hb := hbox p hps
    have hsub : Icc (p.1:ℝ) ((p.1:ℝ)+(p.2:ℝ)) ⊆ Icc a (b+D) := by
      intro t ht
      constructor <;> linarith [hb.1.1,hb.1.2,hb.2.2,ht.1,ht.2]
    have hh := cubic_second_level_positive f (level p) hb.2.1 hL hδL hδhalf
      (fun t ht => (hf t (hsub ht)).of_le (by norm_num))
      (fun t ht => hthree t (hsub ht)) (hlevel p hps)
    exact ⟨hh.1,hh.2.2.2⟩
  let J := S.image Prod.snd
  have hqbox (q : ℕ) (hq : q∈J) : 1 ≤ (q:ℝ) ∧ (q:ℝ) ≤ D := by
    pm_2044
  have hJ : (J.card:ℝ) ≤ D := by
    let I := J.image (fun q : ℕ => (q:ℤ))
    have hcard : I.card=J.card := Finset.card_image_of_injective J Int.ofNat_injective
    have hh := integer_card_le_interval_length_add_one I hD (by
      pm_2532 z hz q hq
      simpa only [Int.cast_natCast] using hqbox q hq)
    rw [hcard] at hh
    linarith
  have hfiber (q : ℕ) (hq : q∈J) :
      ((S.filter (fun p => p.2=q)).card:ℝ) ≤ 4*U*δ/lam+U*D := by
    let T := S.filter (fun p => p.2=q)
    let I := T.image level
    have hqpos : 0 < (q:ℝ) := zero_lt_one.trans_le (hqbox q hq).1
    have hI : (I.card:ℝ) ≤ U*(q:ℝ) := by
      by_cases hne : I.Nonempty
      · have hi (K : ℤ) (hK : K∈I) : (1:ℝ) ≤ K ∧ (K:ℝ) ≤ U*(q:ℝ) := by
          obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hK
          have hh := hlevels p (Finset.mem_filter.mp hp).1
          rw [(Finset.mem_filter.mp hp).2] at hh
          pm_5815
        pm_6541 hh I hi hh.trans_eq
      pm_6617 I
    have hsub : Icc a (b+(q:ℝ)) ⊆ Icc a (b+D) := by
      intro t ht
      exact ⟨ht.1,ht.2.trans (by linarith [(hqbox q hq).2])⟩
    have hcell (K : ℤ) :
        ((T.filter (fun p => level p=K)).card:ℝ) ≤ 4*δ/(lam*(q:ℝ))+1 := by
      pm_2283 Z T.filter p level K
      let Y := Z.image Prod.fst
      have hinj : Set.InjOn (Prod.fst : ℤ × ℕ → ℤ) Z := by
        intro p hp r hr he
        exact Prod.ext he ((Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.trans
          (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.symm)
      have hcard : Y.card=Z.card := Finset.card_image_of_injOn hinj
      have hY : ∀ n∈Y, (n:ℝ)∈Icc a b := by
        pm_1672
        exact (hbox p (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
      have hnear : ∀ n∈Y,
          |(iteratedDeriv 2 f ((n:ℝ)+(q:ℝ))-iteratedDeriv 2 f n)/2-(K:ℝ)| ≤ δ := by
        pm_1672
        have hh := hlevel p (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
        rwa [(Finset.mem_filter.mp hp).2,
          (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2] at hh
      have hh := cubic_second_difference_fiber_card f Y hqpos hlam hδ
        (fun t ht => hf t (hsub ht)) (fun t ht => hfour t (hsub ht)) hY hnear
      rwa [hcard] at hh
    have hmaps : Set.MapsTo level T I := by
      pm_1673
    pm_5330 T.card I T.filter
    calc
      _ = _ := hcard
      _ ≤ ∑ _K∈I, (4*δ/(lam*(q:ℝ))+1) := Finset.sum_le_sum (fun K _ => hcell K)
      _ = (I.card:ℝ)*(4*δ/(lam*(q:ℝ))+1) := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ (U*(q:ℝ))*(4*δ/(lam*(q:ℝ))+1) := mul_le_mul_of_nonneg_right hI (by positivity)
      _ = 4*U*δ/lam+U*(q:ℝ) := by field_simp
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left (hqbox q hq).2 hU.le]
  have hmaps : Set.MapsTo (Prod.snd : ℤ × ℕ → ℕ) S J := by
    pm_1673
  pm_2045
  calc
    _ = _ := hcard
    _ ≤ ∑ _q∈J, (4*U*δ/lam+U*D) := Finset.sum_le_sum hfiber
    _ = (J.card:ℝ)*(4*U*δ/lam+U*D) := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hJ (by positivity)

theorem cubic_free_width_and_buffer
    {H Y lam B D : ℝ} (hH : 2 ≤ H) (hY : 2 ≤ Y)
    (hlam : 0 < lam) (hB : lam ≤ B) (hD : 2 ≤ D)
    (hthreshold : 4*B/(lam^2*H^4) ≤ D) :
    let R := 1/(2*lam*D*H^2)
    let W := max (1/(2*H)+B/(lam^2*D*H^4)) (1/Y)
    0 < R ∧ R ≤ H^2 ∧ 0 < W ∧ W ≤ 1/2 ∧
      1/(4*H^2)=lam*D*R/2 ∧
      1/(4*H)+2*B*D*R^2 ≤ W/2 ∧
      W*D ≤ D/(2*H)+B/(lam^2*H^4)+D/Y ∧
      ∀ p : ℝ, 0 ≤ p → W^(-p) ≤ Y^p := by
  intro R W
  pm_72 hHpos H hYpos Y
  pm_4945 hDpos D hBpos B hlam.trans_le hB
  pm_64 hR R
  have hraw : 4*B ≤ D*(lam^2*H^4) :=
    (div_le_iff₀ (by positivity : 0 < lam^2*H^4)).mp hthreshold
  have hsize : 4 ≤ lam*D*H^4 := by
    apply (mul_le_mul_iff_right₀ hlam).mp
    nlinarith only [hraw,hB]
  have hRsmall : R ≤ H^2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*lam*D*H^2)).mpr
    nlinarith only [hsize]
  have hW : 0 < W := (one_div_pos.mpr hYpos).trans_le (le_max_right _ _)
  have hquarter : 1/(2*H) ≤ 1/4 := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2*H) (by norm_num : (0:ℝ)<4)).mpr
    linarith
  have hother : B/(lam^2*D*H^4) ≤ 1/4 := by
    apply (div_le_div_iff₀ (by positivity : 0 < lam^2*D*H^4) (by norm_num : (0:ℝ)<4)).mpr
    nlinarith only [hraw]
  have hWhalf : W ≤ 1/2 := by
    apply max_le
    · linarith
    · exact one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hY
  have hbuffer : 1/(4*H^2)=lam*D*R/2 := by dsimp [R]; field_simp; norm_num
  have hwidth : 1/(4*H)+2*B*D*R^2 ≤ W/2 := by
    have he : 1/(4*H)+2*B*D*R^2=(1/(2*H)+B/(lam^2*D*H^4))/2 := by
      dsimp [R]
      field_simp
      ring
    rw [he]
    exact div_le_div_of_nonneg_right (le_max_left _ _) (by norm_num)
  have hWD : W*D ≤ D/(2*H)+B/(lam^2*H^4)+D/Y := by
    have hsum : W ≤ (1/(2*H)+B/(lam^2*D*H^4))+1/Y := by
      apply max_le
      · linarith [one_div_pos.mpr hYpos]
      · have hpos : 0 ≤ 1/(2*H)+B/(lam^2*D*H^4) := by positivity
        linarith
    calc
      _ ≤ ((1/(2*H)+B/(lam^2*D*H^4))+1/Y)*D := mul_le_mul_of_nonneg_right hsum hDpos.le
      _ = _ := by field_simp
  pm_2030 hR hRsmall hW hWhalf hbuffer hwidth hWD
  intro p hp
  have hh := Real.rpow_le_rpow_of_nonpos (one_div_pos.mpr hYpos)
    (show 1/Y ≤ W from le_max_right _ _) (neg_nonpos.mpr hp)
  have he : (1/Y)^(-p)=Y^p := by
    rw [one_div,Real.inv_rpow hYpos.le,Real.rpow_neg hYpos.le,inv_inv]
  exact hh.trans_eq he

private theorem cubic_long_block_majorant
    {H Y lam B U D Qcut Freq Tail C p q : ℝ}
    (hH : 2 ≤ H) (hY : 2 ≤ Y) (hlam : 0 < lam) (hB : lam ≤ B)
    (hD : 2 ≤ D) (hthreshold : 4*B/(lam^2*H^4) ≤ D)
    (hU : 0 ≤ U) (hDQ : D ≤ Qcut) (hthin : lam*Qcut*H^2 ≤ 1)
    (hFreq : 0 ≤ Freq) (hTail : 0 ≤ Tail) (hC : 1 ≤ C) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    let W := max (1/(2*H)+B/(lam^2*D*H^4)) (1/Y)
    (2*U*D)*(4*(1/(4*H^2))/(lam*D)+1)*
      (C*(W*D+Freq*D^q*W^(-p)+Tail)) ≤
      4*C*(U/(lam*H^2))*
        (1+B/(lam^2*H^4)+Qcut/H+Qcut/Y+Freq*Qcut^q*Y^p+Tail) := by
  intro W
  pm_2074 hHpos H hH
  pm_2074 hYpos Y hY
  pm_2074 hDpos D hD
  pm_4278 hQpos Qcut hDpos.trans_le hDQ hBpos B hlam.trans_le hB
  let V := U/(lam*H^2)
  let X := 1+B/(lam^2*H^4)+Qcut/H+Qcut/Y+Freq*Qcut^q*Y^p+Tail
  pm_61 hV V
  pm_61 hX X
  obtain ⟨_hR,_hRsmall,hW,_hWhalf,_hbuf,_hwidth,hWD,hWp⟩ :=
    cubic_free_width_and_buffer hH hY hlam hB hD hthreshold
  pm_985 hU
  have hfactorEq : (2*U*D)*(4*(1/(4*H^2))/(lam*D)+1)=2*V+2*U*D := by
    dsimp [V]
    field_simp
  have hfactor : (2*U*D)*(4*(1/(4*H^2))/(lam*D)+1) ≤ 4*V := by
    rw [hfactorEq]
    have hh := (mul_le_mul_of_nonneg_left hDQ hU).trans hUQ
    linarith only [hh]
  have hlen : D^q ≤ Qcut^q := Real.rpow_le_rpow hDpos.le hDQ hq
  have hosc : Freq*D^q*W^(-p) ≤ Freq*Qcut^q*Y^p := by
    gcongr
    exact hWp p hp
  have hvolume : W*D ≤ Qcut/H+B/(lam^2*H^4)+Qcut/Y := by
    calc
      _ ≤ D/(2*H)+B/(lam^2*H^4)+D/Y := hWD
      _ ≤ Qcut/(2*H)+B/(lam^2*H^4)+Qcut/Y := by gcongr
      _ ≤ _ := by
        have hh : Qcut/(2*H) ≤ Qcut/H :=
          div_le_div_of_nonneg_left hQpos.le hHpos (by linarith only [hHpos])
        linarith only [hh]
  have hinner : W*D+Freq*D^q*W^(-p)+Tail ≤ X := by
    dsimp [X]
    linarith only [hvolume,hosc]
  calc
    _ ≤ (4*V)*(C*X) := by gcongr
    _ = _ := by change (4*V)*(C*X)=4*C*V*X; ring

theorem original_full_joint_derivative_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 3 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (T N H Y a b Qcut : ℝ) (M : ℕ) (S : Finset (ℤ × ℕ)),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 2 ≤ H → 2 ≤ Y → 1 ≤ Qcut → Qcut ≤ (2:ℝ)^M →
          N < a-H^2 → b+H^2+2*Qcut < 2*N →
          let lam := modelPhaseJetLower σ 3*T/N^4
          let B := (modelPhaseJetCoefficient σ 3+1)*T/N^4
          let L := modelPhaseJetLower σ 2*T/N^3
          let U := (modelPhaseJetCoefficient σ 2+1)*T/N^3
          lam*Qcut*H^2 ≤ 1 → 1/(4*H^2) ≤ L/4 →
          4*U*Qcut*N^2/(σ*T) ≤ κ₀ →
          let f := fun z => T*F (z/N)
          (∀ p∈S, (p.1:ℝ)∈Icc a b ∧ (p.2:ℝ)∈Icc 1 Qcut) →
          (∀ p∈S, ∃ K : ℤ, |(iteratedDeriv 2 f ((p.1:ℝ)+(p.2:ℝ))-
            iteratedDeriv 2 f p.1)/2-(K:ℝ)| ≤ 1/(4*H^2)) →
          (∀ p∈S, ∃ e : ℤ, |iteratedDeriv 1 f ((p.1:ℝ)+(p.2:ℝ))-
            iteratedDeriv 1 f p.1-(e:ℝ)| ≤ 1/(4*H)) →
            (S.card:ℝ) ≤ C*((M:ℝ)+2)*(U/(lam*H^2))*
              (1+B/(lam^2*H^4)+Qcut/H+Qcut/Y+
                (T/N^2)^(k₀+ε)*Qcut^(l₀+ε)*Y^(k₀+ε)+N^2/T) := by
  pm_2046 δ₀ hδ₀ Q₀ hQ₀ C₀ hC₀ hcount original_joint_dyadic_block_count
  pm_2051
  let C := 8+4*C₀
  pm_1608
  pm_8246 hC8
  have hC4 : 4*C₀ ≤ C := by dsimp [C]; linarith
  pm_2050
  intro F T N H Y a b Qcut M S hF hT hN hH hY hQcut hQpow hleft hright
    lam B L U hthin hδL hshift f hbox hsecond hfirst
  pm_2048
  pm_2053
  pm_72 hHpos H hYpos Y
  have hQpos : 0 < Qcut := zero_lt_one.trans_le hQcut
  pm_2049
  pm_5554 hBpos B modelPhaseJetCoefficient_pos
  have hB : lam ≤ B := by
    have hh := modelPhase_signed_referenceJet_bounds hσ (by norm_num : (3/2:ℝ)∈Ioo 1 2) 3
    have hc : modelPhaseJetLower σ 3 ≤ modelPhaseJetCoefficient σ 3+1 := by
      linarith only [hh.1,hh.2,modelPhaseJetLower_pos hσ 3]
    dsimp [lam,B]
    gcongr
  have hδhalf : 1/(4*H^2) ≤ 1/2 := by
    apply (div_le_div_iff₀ (by positivity : 0 < 4*H^2) (by norm_num : (0:ℝ)<2)).mpr
    nlinarith only [hH]
  pm_8245 hp₀
  have hq₀ : 0 ≤ l₀+ε := by linarith [hpair.1.2.2.1]
  let V := U/(lam*H^2)
  let X := 1+B/(lam^2*H^4)+Qcut/H+Qcut/Y+
    (T/N^2)^(k₀+ε)*Qcut^(l₀+ε)*Y^(k₀+ε)+N^2/T
  let A := C*V*X
  let D₀ := 2+4*B/(lam^2*H^4)
  pm_64 hV V
  pm_64 hX X
  pm_61 hA A
  have hD₀ : 2 ≤ D₀ := by
    have hh : 0 ≤ 4*B/(lam^2*H^4) := by positivity
    dsimp [D₀]
    linarith
  pm_985 hU.le
  have hsegment : Icc a (b+Qcut) ⊆ Ioo N (2*N) := by
    intro t ht
    constructor <;> linarith only [ht.1,ht.2,sq_nonneg H,hleft,hright,hQpos]
  let short := S.filter (fun p => (p.2:ℝ)<D₀)
  have hshort : (short.card:ℝ) ≤ A := by
    let d := min D₀ Qcut
    have hd : 1 ≤ d := le_min (by linarith) hQcut
    have hdQ : d ≤ Qcut := min_le_right _ _
    have hd₀ : d ≤ D₀ := min_le_left _ _
    have hsub : Icc a (b+d) ⊆ Ioo N (2*N) := by
      intro t ht
      exact hsegment ⟨ht.1,ht.2.trans (by linarith)⟩
    have hh := cubic_short_displacement_count f short hd hlam hL hU (by positivity)
      hδL hδhalf
      (fun t ht => (hreg t (hsub ht)).of_le (by norm_num))
      (fun t ht => hthree t (hsub ht)) (fun t ht => hfour t (hsub ht))
      (by
        pm_7465
        exact ⟨hb.1,hb.2.1,le_min (Finset.mem_filter.mp hp).2.le hb.2.2⟩)
      (fun p hp => hsecond p (Finset.mem_filter.mp hp).1)
    have he : 4*U*(1/(4*H^2))/lam=V := by dsimp [V]; field_simp
    rw [he] at hh
    have hUd : U*d ≤ V := (mul_le_mul_of_nonneg_left hdQ hU.le).trans hUQ
    have hsmall : (short.card:ℝ) ≤ 2*D₀*V := by
      calc
        _ ≤ d*(V+U*d) := hh
        _ ≤ D₀*(V+V) := by gcongr
        _ = _ := by ring
    have hDX : 2*D₀ ≤ 8*X := by
      have hterms : 0 ≤ Qcut/H+Qcut/Y+
          (T/N^2)^(k₀+ε)*Qcut^(l₀+ε)*Y^(k₀+ε)+N^2/T := by positivity
      dsimp [D₀,X]
      ring_nf at hterms ⊢
      linarith only [hterms]
    calc
      _ ≤ 2*D₀*V := hsmall
      _ ≤ (8*X)*V := mul_le_mul_of_nonneg_right hDX hV.le
      _ ≤ (C*X)*V := by gcongr
      _ = A := by dsimp [A]; ring
  let scale := fun j : ℕ => D₀*(2:ℝ)^j
  let block := fun j : ℕ => S.filter (fun p => scale j ≤ (p.2:ℝ) ∧ (p.2:ℝ)<2*scale j)
  have hblock (j : ℕ) : ((block j).card:ℝ) ≤ A := by
    by_cases hne : (block j).Nonempty
    · obtain ⟨p,hps⟩ := hne
      let D := scale j
      have hDlow : D₀ ≤ D := by
        pm_8210 hh j
        dsimp [D,scale]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hh
          (show 0 ≤ D₀ by linarith only [hD₀])
      pm_8409 hD D hD₀.trans hDlow hDpos
      have hDQ : D ≤ Qcut := (Finset.mem_filter.mp hps).2.1.trans (hbox p (Finset.mem_filter.mp hps).1).2.2
      have hthreshold : 4*B/(lam^2*H^4) ≤ D := by
        dsimp [D₀] at hDlow
        linarith
      let R := 1/(2*lam*D*H^2)
      let W := max (1/(2*H)+B/(lam^2*D*H^4)) (1/Y)
      obtain ⟨hR,hRsmall,hW,hWhalf,hbuf,hwidth,_hWD,_hWp⟩ :=
        cubic_free_width_and_buffer hH hY hlam hB hD hthreshold
      have hshiftD : 4*U*D*N^2/(σ*T) ≤ κ₀ := by
        calc
          _ ≤ 4*U*Qcut*N^2/(σ*T) := by gcongr
          _ ≤ κ₀ := hshift
      have hh := hcount F T N D a b R (1/(4*H)) (1/(4*H^2)) W (block j)
        hF₀ hT hN hD hR (by positivity)
        (by linarith only [hleft,hRsmall])
        (by linarith only [hright,hRsmall,hDQ])
        hbuf.le hwidth hδL hδhalf hshiftD hW hWhalf
        (by
          pm_7465
          exact ⟨hb.1,(Finset.mem_filter.mp hp).2.1,(Finset.mem_filter.mp hp).2.2.le⟩)
        (fun p hp => hsecond p (Finset.mem_filter.mp hp).1)
        (fun p hp => hfirst p (Finset.mem_filter.mp hp).1)
      have hmajor := cubic_long_block_majorant hH hY hlam hB hD hthreshold
        hU.le hDQ hthin (by positivity : 0 ≤ (T/N^2)^(k₀+ε))
        (by positivity : 0 ≤ N^2/T) hC₀ hp₀ hq₀
      have hbound : ((block j).card:ℝ) ≤ 4*C₀*V*X := hh.trans hmajor
      calc
        _ ≤ 4*C₀*V*X := hbound
        _ ≤ C*V*X := by gcongr
    · have he : block j=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp only [he,Finset.card_empty,Nat.cast_zero]
      exact hA
  have hcover : S ⊆ short ∪ (Finset.range (M+1)).biUnion block := by
    intro p hp
    by_cases hs : (p.2:ℝ)<D₀
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp,hs⟩)
    have hterminal : (p.2:ℝ)<D₀*(2:ℝ)^(M+1) := by
      have hh := (hbox p hp).2.2.trans hQpow
      have hpowpos : (0:ℝ)<2^M := by positivity
      rw [pow_succ]
      nlinarith only [hh,hpowpos,hD₀]
    obtain ⟨j,hj,hlo,hhi⟩ := exists_bourgain_dyadic_amplitude (le_of_not_gt hs) hterminal
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨j,hj,Finset.mem_filter.mpr ⟨hp,hlo,hhi⟩⟩)
  have hcard : (S.card:ℝ) ≤ (short.card:ℝ)+∑ j∈Finset.range (M+1), ((block j).card:ℝ) := by
    have hh := (Finset.card_le_card hcover).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _))
    exact_mod_cast hh
  calc
    _ ≤ (short.card:ℝ)+∑ j∈Finset.range (M+1), ((block j).card:ℝ) := hcard
    _ ≤ A+∑ _j∈Finset.range (M+1), A := add_le_add hshort (Finset.sum_le_sum (fun j _ => hblock j))
    _ = _ := by
      pm_94 Finset.sum_const Finset.card_range nsmul_eq_mul Nat.cast_add Nat.cast_one
      dsimp only [A]
      ring

theorem cubicDerivativePairs_card_le_positive
    (f : ℝ → ℝ) (M H : ℕ) :
    (SquareProductCount.CubicSource.cubicDerivativePairs f M H).card ≤ M+
      2*((SquareProductCount.CubicSource.cubicDerivativePairs f M H).filter
        (fun p => p.1<p.2)).card := by
  classical
  let S := SquareProductCount.CubicSource.cubicDerivativePairs f M H
  let diag := S.filter (fun p => p.1=p.2)
  pm_8724 S.filter
  let down := S.filter (fun p => p.2<p.1)
  have hswap (p : ℕ × ℕ) (hp : p∈S) : p.swap∈S := by
    unfold S SquareProductCount.CubicSource.cubicDerivativePairs
      SquareProductCount.CubicSource.cubicSamplePairs at hp ⊢
    obtain ⟨hbox,hnear⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(Finset.mem_product.mp hbox).2,(Finset.mem_product.mp hbox).1⟩,?_⟩
    intro d
    simpa only [Prod.swap,abs_sub_comm] using hnear d
  have hd : diag.card ≤ M := by
    have hinj : Set.InjOn (Prod.fst : ℕ × ℕ → ℕ) diag := by
      intro p hp q hq he
      exact Prod.ext he ((Finset.mem_filter.mp hp).2.symm.trans
        (he.trans (Finset.mem_filter.mp hq).2))
    have hsub : diag.image Prod.fst ⊆ Finset.range M := by
      pm_1672
      have hm := (cubicDerivativePairs_integer_resonances f
        (Finset.mem_filter.mp hp).1).1
      exact Finset.mem_range.mpr hm
    have hh := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injOn hinj,Finset.card_range] at hh
  have hdown : down.card ≤ up.card := by
    have hsub : down.image Prod.swap ⊆ up := by
      pm_2551
      exact Finset.mem_filter.mpr ⟨hswap q (Finset.mem_filter.mp hq).1,(Finset.mem_filter.mp hq).2⟩
    have hh := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injective down Prod.swap_injective] at hh
  have hcover : S ⊆ (diag∪up)∪down := by
    intro p hp
    rcases lt_trichotomy p.1 p.2 with hlt|heq|hgt
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp,hlt⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp,heq⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp,hgt⟩)
  have hh := (Finset.card_le_card hcover).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  change S.card ≤ M+2*up.card
  omega

theorem cubic_shifted_positive_pair_resonances
    (f : ℝ → ℝ) (A : ℤ) {M H : ℕ} {p : ℕ × ℕ}
    (hp : p∈SquareProductCount.CubicSource.cubicDerivativePairs
      (fun x => f ((A:ℝ)+x)) M H) (hlt : p.1<p.2) :
    let n : ℤ := A+(p.1:ℤ)+1
    let q : ℕ := p.2-p.1
    (A:ℝ)+1 ≤ n ∧ (n:ℝ) ≤ (A:ℝ)+M ∧ 1 ≤ q ∧
      ∃ e K : ℤ,
        |iteratedDeriv 1 f ((n:ℝ)+(q:ℝ))-iteratedDeriv 1 f n-(e:ℝ)| ≤ 1/(4*(H:ℝ)) ∧
        |(iteratedDeriv 2 f ((n:ℝ)+(q:ℝ))-iteratedDeriv 2 f n)/2-(K:ℝ)| ≤ 1/(4*(H:ℝ)^2) := by
  intro n q
  obtain ⟨hm₀,_hm₁,e,K,hfirst,hsecond,_hthird⟩ :=
    cubicDerivativePairs_integer_resonances
      (fun x => f ((A:ℝ)+x)) hp
  have hder (j : ℕ) (x : ℝ) :
      iteratedDeriv j (fun y => f ((A:ℝ)+y)) x=iteratedDeriv j f ((A:ℝ)+x) :=
    congrFun (iteratedDeriv_comp_const_add j f (A:ℝ)) x
  have hn : (n:ℝ)=(A:ℝ)+(p.1:ℝ)+1 := by dsimp [n]; push_cast; ring
  have hq : (q:ℝ)=(p.2:ℝ)-(p.1:ℝ) := Nat.cast_sub hlt.le
  have he₀ : (A:ℝ)+((p.1:ℝ)+1)=(n:ℝ) := by rw [hn]; ring
  have he₁ : (A:ℝ)+((p.2:ℝ)+1)=(n:ℝ)+(q:ℝ) := by rw [hn,hq]; ring
  rw [hder,hder,he₀,he₁] at hfirst hsecond
  refine ⟨?_,?_,by dsimp [q]; omega,e,K,hfirst,hsecond⟩
  · rw [hn]
    pm_8535 hh
    linarith only [hh]
  · rw [hn]
    have hh : (p.1:ℝ)+1 ≤ M := by exact_mod_cast (show p.1+1 ≤ M by omega)
    linarith only [hh]

section
variable {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ) (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1)
include σ k₀ l₀ ε hσ hpair hε hp
theorem original_cubicDerivativePairs_count :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 3 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (T N Y : ℝ) (A : ℤ) (M H J : ℕ),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 2 ≤ H → 2 ≤ Y →
          let lam := modelPhaseJetLower σ 3*T/N^4
          let B := (modelPhaseJetCoefficient σ 3+1)*T/N^4
          let L := modelPhaseJetLower σ 2*T/N^3
          let U := (modelPhaseJetCoefficient σ 2+1)*T/N^3
          let Qcut := 3/(2*lam*(H:ℝ)^3)
          1 ≤ Qcut → Qcut ≤ (2:ℝ)^J →
          N < (A:ℝ)+1-(H:ℝ)^2 → (A:ℝ)+M+(H:ℝ)^2+2*Qcut < 2*N →
          1/(4*(H:ℝ)^2) ≤ L/4 → 4*U*Qcut*N^2/(σ*T) ≤ κ₀ →
          let g := fun x => T*F (((A:ℝ)+x)/N)
          ((SquareProductCount.CubicSource.cubicDerivativePairs g M H).card:ℝ) ≤
            M+2*(C*((J:ℝ)+2)*(U/(lam*(H:ℝ)^2))*
              (1+B/(lam^2*(H:ℝ)^4)+Qcut/(H:ℝ)+Qcut/Y+
                (T/N^2)^(k₀+ε)*Qcut^(l₀+ε)*Y^(k₀+ε)+N^2/T)) := by
  pm_2046 δ₀ hδ₀ Q₀ hQ₀ C hC hcount original_full_joint_derivative_count
  pm_2051
  pm_2050
  intro F T N Y A M H J hF hT hN hH hY lam B L U Qcut hQcut hQpow hleft hright hδL hshift g
  pm_2048
  pm_562 hreg _hthree hfour _hsecondabs hdata F T N hT hN hFd
  pm_5545 x F N
  let pairs := SquareProductCount.CubicSource.cubicDerivativePairs g M H
  pm_8724 pairs.filter
  let label := fun p : ℕ × ℕ => (A+(p.1:ℤ)+1,p.2-p.1)
  let S := up.image label
  pm_2056
  pm_5554 hlam lam modelPhaseJetLower_pos
  pm_2055
  have hphysical (x : ℝ) (hx : x∈Icc 1 (M:ℝ)) : (A:ℝ)+x∈Ioo N (2*N) := by
    constructor <;> linarith only [hx.1,hx.2,hleft,hright,sq_nonneg (H:ℝ),hQpos]
  have hdisp (p : ℕ × ℕ) (hps : p∈up) : ((p.2-p.1:ℕ):ℝ) ≤ Qcut := by
    pm_317 hpairs Finset.mem_filter.mp hps hlt
    obtain ⟨hm₀,hm₁,_he,_hK,_hfirst,_hsecond,_hthird⟩ :=
      cubicDerivativePairs_integer_resonances g hpairs
    have hsub (x : ℝ) (hx : x∈Icc ((p.1:ℝ)+1) ((p.2:ℝ)+1)) : x∈Icc 1 (M:ℝ) := by
      have hm : (p.2:ℝ)+1 ≤ M := by exact_mod_cast (show p.2+1≤M by omega)
      pm_8535 hp0
      constructor <;> linarith only [hx.1,hx.2,hm,hp0]
    have hgc : ∀ x∈Icc ((p.1:ℝ)+1) ((p.2:ℝ)+1), ContDiffAt ℝ 4 g x := by
      intro x hx
      exact ((hreg ((A:ℝ)+x) (hphysical x (hsub x hx))).comp x
        (show ContDiffAt ℝ 5 (fun y : ℝ => (A:ℝ)+y) x by fun_prop)).of_le (by norm_num)
    have hgf : ∀ x∈Icc ((p.1:ℝ)+1) ((p.2:ℝ)+1), iteratedDeriv 4 g x ≤ -lam := by
      intro x hx
      rw [hder]
      exact (hfour ((A:ℝ)+x) (hphysical x (hsub x hx))).2
    rw [Nat.cast_sub hlt.le]
    exact cubicDerivativePairs_displacement g (by omega) hlam hpairs hlt hgc hgf
  have hinj : Set.InjOn label up := by
    intro p hp q hq he
    pm_194 hfst congrArg Prod.fst he hsnd Prod.snd
    dsimp only [label] at hfst hsnd
    have hp := (Finset.mem_filter.mp hp).2
    have hq := (Finset.mem_filter.mp hq).2
    have he₁ : p.1=q.1 := by omega
    exact Prod.ext he₁ (by omega)
  have hcard : S.card=up.card := Finset.card_image_of_injOn hinj
  have hboxS : ∀ p∈S, (p.1:ℝ)∈Icc ((A:ℝ)+1) ((A:ℝ)+M) ∧
      (p.2:ℝ)∈Icc 1 Qcut := by
    pm_2551
    have hh := cubic_shifted_positive_pair_resonances f A
      (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2
    exact ⟨⟨hh.1,hh.2.1⟩,by exact_mod_cast hh.2.2.1,hdisp q hq⟩
  have hsecondS : ∀ p∈S, ∃ K : ℤ,
      |(iteratedDeriv 2 f ((p.1:ℝ)+(p.2:ℝ))-iteratedDeriv 2 f p.1)/2-(K:ℝ)| ≤ 1/(4*(H:ℝ)^2) := by
    pm_2551
    pm_5948 _hfirst hsecond
    exact ⟨K,hsecond⟩
  have hfirstS : ∀ p∈S, ∃ e : ℤ,
      |iteratedDeriv 1 f ((p.1:ℝ)+(p.2:ℝ))-iteratedDeriv 1 f p.1-(e:ℝ)| ≤ 1/(4*(H:ℝ)) := by
    pm_2551
    pm_5948 hfirst _hsecond
    exact ⟨e,hfirst⟩
  have hthin : lam*Qcut*(H:ℝ)^2 ≤ 1 := by
    have he : lam*Qcut*(H:ℝ)^2=3/(2*(H:ℝ)) := by dsimp [Qcut]; field_simp
    rw [he]
    apply (div_le_iff₀ (by positivity : 0 < 2*(H:ℝ))).mpr
    linarith only [hHr]
  have hh := hcount F T N (H:ℝ) Y ((A:ℝ)+1) ((A:ℝ)+M) Qcut J S
    hF₀ hT hN hHr hY hQcut hQpow hleft hright hthin hδL hshift hboxS hsecondS hfirstS
  rw [hcard] at hh
  have hsplit : (pairs.card:ℝ) ≤ (M:ℝ)+2*(up.card:ℝ) := by
    exact_mod_cast cubicDerivativePairs_card_le_positive g M H
  exact hsplit.trans (by gcongr)

                                                                    
                                                                           
                                               
theorem exists_original_cubic_eighth_estimate :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 3 ≤ Q ∧ ∃ C : ℝ, 0 < C ∧
        ∀ (F : ℝ → ℝ) (T N Y : ℝ) (A : ℤ) (M H J : ℕ),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 2 ≤ H → 2 ≤ Y →
          let lam := modelPhaseJetLower σ 3*T/N^4
          let B := (modelPhaseJetCoefficient σ 3+1)*T/N^4
          let L := modelPhaseJetLower σ 2*T/N^3
          let U := (modelPhaseJetCoefficient σ 2+1)*T/N^3
          let Qcut := 3/(2*lam*(H:ℝ)^3)
          1 ≤ Qcut → Qcut ≤ (2:ℝ)^J →
          N < (A:ℝ)+1-(H:ℝ)^2 → (A:ℝ)+M+(H:ℝ)^2+2*Qcut < 2*N →
          1/(4*(H:ℝ)^2) ≤ L/4 → 4*U*Qcut*N^2/(σ*T) ≤ κ₀ →
          B*((H:ℝ)+1)^4 ≤ 1 →
          let E := ((J:ℝ)+2)*(U/(lam*(H:ℝ)^2))*
            (1+B/(lam^2*(H:ℝ)^4)+Qcut/(H:ℝ)+Qcut/Y+
              (T/N^2)^(k₀+ε)*Qcut^(l₀+ε)*Y^(k₀+ε)+N^2/T)
          ‖∑ m∈Finset.range M,
            fordAdditiveCharacter (T*F (((A:ℝ)+(m:ℝ)+1)/N))‖^8 ≤
              C*((M:ℝ)^6*((M:ℝ)+E)*(1+U*(H:ℝ)^2)*(H:ℝ)^ε+(H:ℝ)^8) := by
  obtain ⟨δ₀,κ₀,hδ₀,hκ₀,Q₀,hQ₀,C₀,hC₀,hcount⟩ :=
    original_cubicDerivativePairs_count hσ hpair hε hp
  obtain ⟨δd,hδd,hdata⟩ := model_displacement_derivative_data hσ
  obtain ⟨C₁,hC₁,hsource⟩ := SquareProductCount.CubicSource.exists_C4_source_eighth_reduction hε
  let δ := min δ₀ δd
  let Q := max Q₀ 3
  let C := C₁*(1+2*C₀)
  pm_64 hC C
  pm_2050
  intro F T N Y A M H J hF hT hN hH hY lam B L U Qcut hQcut hQpow hleft hright hδL hshift hTaylor E
  pm_2048
  pm_2053
  pm_5545 x F N
  let g := fun x => f ((A:ℝ)+x)
  pm_2056
  pm_2049
  pm_5554 hB B modelPhaseJetCoefficient_pos
  pm_2055
  have hHbuf : (H:ℝ)+1 ≤ (H:ℝ)^2 := by nlinarith only [hHr]
  have hpoint (m : ℕ) (hm : m∈Finset.range M) (y : ℝ)
      (hy : y∈Icc ((m:ℝ)-H) ((m:ℝ)+H+2)) : (A:ℝ)+y∈Ioo N (2*N) := by
    pm_491 hm0 m
    have hmM : (m:ℝ)+1 ≤ M := by
      exact_mod_cast (show m+1≤M by have := Finset.mem_range.mp hm; omega)
    constructor <;> linarith only [hy.1,hy.2,hm0,hmM,hHbuf,hleft,hright,hQpos]
  have hg (m : ℕ) (hm : m∈Finset.range M) (y : ℝ)
      (hy : y∈Icc ((m:ℝ)-H) ((m:ℝ)+H+2)) : ContDiffAt ℝ 4 g y := by
    exact ((hreg ((A:ℝ)+y) (hpoint m hm y hy)).comp y
      (show ContDiffAt ℝ 5 (fun z : ℝ => (A:ℝ)+z) y by fun_prop)).of_le (by norm_num)
  have hfour' (m : ℕ) (hm : m∈Finset.range M) (y : ℝ)
      (hy : y∈Icc ((m:ℝ)-H) ((m:ℝ)+H+2)) : |iteratedDeriv 4 g y| ≤ B := by
    rw [hder]
    have hh := hfour ((A:ℝ)+y) (hpoint m hm y hy)
    apply abs_le.mpr
    exact ⟨hh.1,by linarith only [hh.2,hlam,hB]⟩
  have hthree' (m : ℕ) (hm : m∈Finset.range M) :
      iteratedDeriv 3 g ((m:ℝ)+1)/6∈Icc (0:ℝ) (0+U/6) := by
    rw [hder]
    have hcenter : (m:ℝ)+1∈Icc ((m:ℝ)-H) ((m:ℝ)+H+2) := by
      constructor <;> linarith only [hHpos]
    have hh := hthree ((A:ℝ)+((m:ℝ)+1)) (hpoint m hm ((m:ℝ)+1) hcenter)
    pm_4893 hL
  have hnear := hcount F T N Y A M H J hF₀ hT hN hH hY hQcut hQpow hleft hright hδL hshift
  have hsum := hsource g M H (by omega) B 0 (U/6) hB.le (by positivity)
    hTaylor hg hfour' hthree'
  pm_61 hE E
  have hnear' : ((SquareProductCount.CubicSource.cubicDerivativePairs g M H).card:ℝ) ≤
      (1+2*C₀)*((M:ℝ)+E) := by
    have hh : ((SquareProductCount.CubicSource.cubicDerivativePairs g M H).card:ℝ) ≤
        (M:ℝ)+2*C₀*E := by
      convert hnear using 1
      dsimp [E]
      ring
    pm_491 hm M
    have hx : 0 ≤ 2*C₀*(M:ℝ) := by positivity
    nlinarith only [hh,hE,hx]
  have hUwidth : 1+(U/6)*(H:ℝ)^2 ≤ 1+U*(H:ℝ)^2 := by
    nlinarith only [mul_nonneg hU.le (sq_nonneg (H:ℝ))]
  have hb : ‖∑ m∈Finset.range M, fordAdditiveCharacter (g ((m:ℝ)+1))‖^8 ≤
      C*((M:ℝ)^6*((M:ℝ)+E)*(1+U*(H:ℝ)^2)*(H:ℝ)^ε+(H:ℝ)^8) := by
    calc
      _ ≤ C₁*((M:ℝ)^6*(SquareProductCount.CubicSource.cubicDerivativePairs g M H).card*
          (1+(U/6)*(H:ℝ)^2)*(H:ℝ)^ε+(H:ℝ)^8) := hsum
      _ ≤ C₁*((M:ℝ)^6*((1+2*C₀)*((M:ℝ)+E))*(1+U*(H:ℝ)^2)*(H:ℝ)^ε+(H:ℝ)^8) := by gcongr
      _ ≤ C₁*((1+2*C₀)*((M:ℝ)^6*((M:ℝ)+E)*(1+U*(H:ℝ)^2)*(H:ℝ)^ε+(H:ℝ)^8)) := by
        apply mul_le_mul_of_nonneg_left _ hC₁.le
        nlinarith only [mul_nonneg (show 0 ≤ 2*C₀ by positivity) (pow_nonneg hHpos.le 8)]
      _ = _ := by dsimp [C]; ring
  simpa only [g,f,add_assoc] using hb
end



                                                                        
                                                                 
theorem cubic_source_trim
    (z : ℕ → ℂ) (hz : ∀ n, ‖z n‖ ≤ 1) (a b K : ℕ)
    (hab : a+2*K ≤ b) :
    ‖∑ n∈Finset.Icc a b, z n‖ ≤
      ‖∑ m∈Finset.range (b-a-2*K), z (a+K+m+1)‖+2*(K:ℝ)+1 := by
  let M := b-a-2*K
  have he : b-a+1=((K+1)+M)+K := by dsimp [M]; omega
  rw [RiemannZeta.GuthMaynard.sum_Icc_eq_shifted_range z a b (by omega),he,
    Finset.sum_range_add,Finset.sum_range_add]
  have hleft : ‖∑ i∈Finset.range (K+1), z (a+i)‖ ≤ (K:ℝ)+1 := by
    calc
      _ ≤ ∑ i∈Finset.range (K+1), ‖z (a+i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i∈Finset.range (K+1), (1:ℝ) := Finset.sum_le_sum (fun i _ => hz (a+i))
      _ = _ := by simp
  have hright : ‖∑ i∈Finset.range K, z (a+((K+1)+M+i))‖ ≤ (K:ℝ) := by
    calc
      _ ≤ ∑ i∈Finset.range K, ‖z (a+((K+1)+M+i))‖ := norm_sum_le _ _
      _ ≤ ∑ _i∈Finset.range K, (1:ℝ) := Finset.sum_le_sum (fun i _ => hz _)
      _ = _ := by simp
  have hmid : (∑ i∈Finset.range M, z (a+(K+1+i))) =
      ∑ i∈Finset.range M, z (a+K+i+1) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    omega
  rw [hmid]
  have htriangle := norm_add_le
    ((∑ i∈Finset.range (K+1), z (a+i))+
      ∑ i∈Finset.range M, z (a+K+i+1))
    (∑ i∈Finset.range K, z (a+((K+1)+M+i)))
  have htriangle₂ := norm_add_le (∑ i∈Finset.range (K+1), z (a+i))
    (∑ i∈Finset.range M, z (a+K+i+1))
  dsimp [M] at htriangle
  dsimp [M] at htriangle₂
  linarith only [htriangle,htriangle₂,hleft,hright]


                                                                     
                                                                        
theorem exists_complete_cubic_eighth_estimate
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 3 ≤ Q ∧ ∃ C : ℝ, 0 < C ∧
        ∀ (F : ℝ → ℝ) (T N Y : ℝ) (a b H J : ℕ),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 2 ≤ H → 2 ≤ Y →
          N ≤ a → (b:ℝ) ≤ 2*N →
          let lam := modelPhaseJetLower σ 3*T/N^4
          let B := (modelPhaseJetCoefficient σ 3+1)*T/N^4
          let L := modelPhaseJetLower σ 2*T/N^3
          let U := (modelPhaseJetCoefficient σ 2+1)*T/N^3
          let Qcut := 3/(2*lam*(H:ℝ)^3)
          1 ≤ Qcut → Qcut ≤ (2:ℝ)^J →
          1/(4*(H:ℝ)^2) ≤ L/4 → 4*U*Qcut*N^2/(σ*T) ≤ κ₀ →
          B*((H:ℝ)+1)^4 ≤ 1 →
          let E := ((J:ℝ)+2)*(U/(lam*(H:ℝ)^2))*
            (1+B/(lam^2*(H:ℝ)^4)+Qcut/(H:ℝ)+Qcut/Y+
              (T/N^2)^(k₀+ε)*Qcut^(l₀+ε)*Y^(k₀+ε)+N^2/T)
          ‖exponentialSumAt F T N a b‖^8 ≤
            C*(N^6*(N+E)*(1+U*(H:ℝ)^2)*(H:ℝ)^ε+
              (H:ℝ)^8+((H:ℝ)^2+Qcut+1)^8) := by
  pm_2046 δ hδ Q hQ C₀ hC₀ hsource exists_original_cubic_eighth_estimate
  let C := 128*(C₀+5^8+1)
  pm_64 hC C
  pm_2039
  intro F T N Y a b H J hF hT hN hH hY ha hb lam B L U Qcut hQcut hQpow hδL hshift hTaylor E
  let R := (H:ℝ)^2+Qcut+1
  let K : ℕ := ⌈(H:ℝ)^2+2*Qcut+1⌉₊
  have hKlo : (H:ℝ)^2+2*Qcut+1 ≤ K := Nat.le_ceil _
  have hQpos : 0 < Qcut := zero_lt_one.trans_le hQcut
  have hKhi : (K:ℝ) < (H:ℝ)^2+2*Qcut+2 := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ (H:ℝ)^2+2*Qcut+1 by positivity)
    convert hh using 1
    ring
  pm_64 hR R
  have hboundary : 2*(K:ℝ)+1 ≤ 5*R := by
    dsimp [R]
    nlinarith only [hKhi,sq_nonneg (H:ℝ),hQpos]
  have hE : 0 ≤ E := by dsimp [E,U,lam,B]; positivity [modelPhaseJetLower_pos hσ 3,
    modelPhaseJetCoefficient_pos hσ 2,modelPhaseJetCoefficient_pos hσ 3]
  have hU : 0 < U := by dsimp [U]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  let Z := N^6*(N+E)*(1+U*(H:ℝ)^2)*(H:ℝ)^ε+(H:ℝ)^8
  pm_61 hZ Z
  have hmajor : 128*(C₀*Z+5^8*R^8) ≤ C*(Z+R^8) := by
    dsimp [C]
    nlinarith only [hZ,pow_nonneg hR.le 8,
      mul_nonneg hC₀.le (pow_nonneg hR.le 8)]
  by_cases hab : a+2*K ≤ b
  · let M := b-a-2*K
    let A : ℤ := (a:ℤ)+(K:ℤ)
    have hAr : (A:ℝ)=(a:ℝ)+(K:ℝ) := by dsimp [A]; push_cast; rfl
    have hM : (M:ℝ)=(b:ℝ)-(a:ℝ)-2*(K:ℝ) := by
      dsimp [M]
      push_cast [Nat.cast_sub (show 2*K≤b-a by omega),Nat.cast_sub (show a≤b by omega)]
      ring
    have hMN : (M:ℝ) ≤ N := by
      rw [hM]
      linarith only [ha,hb,(Nat.cast_nonneg K : (0:ℝ) ≤ K)]
    have hleft : N < (A:ℝ)+1-(H:ℝ)^2 := by
      rw [hAr]
      linarith only [ha,hKlo,hQpos]
    have hright : (A:ℝ)+M+(H:ℝ)^2+2*Qcut < 2*N := by
      rw [hAr,hM]
      linarith only [hb,hKlo]
    have hc := hsource F T N Y A M H J hF hT hN hH hY hQcut hQpow
      hleft hright hδL hshift hTaylor
    let S := ∑ m∈Finset.range M, fordAdditiveCharacter (T*F (((A:ℝ)+(m:ℝ)+1)/N))
    have hc' : ‖S‖^8 ≤ C₀*Z := by
      refine hc.trans ?_
      dsimp [Z]
      gcongr
    have htrim := cubic_source_trim (fun n => oscillatory F T N n)
      (fun n => (norm_oscillatory F T N n).le) a b K hab
    have hmid : (∑ m∈Finset.range (b-a-2*K), oscillatory F T N ((a+K+m+1:ℕ):ℝ))=S := by
      apply Finset.sum_congr rfl
      intro m _
      pm_94 sargos_ford_character_eq_fourier oscillatory Nat.cast_add Nat.cast_one hAr
    have hnorm : ‖exponentialSumAt F T N a b‖ ≤ ‖S‖+5*R := by
      rw [hmid] at htrim
      change ‖exponentialSumAt F T N a b‖ ≤ _ at htrim
      linarith only [htrim,hboundary]
    have hpow := (pow_le_pow_left₀ (norm_nonneg _) hnorm 8).trans
      (add_pow_le (norm_nonneg S) (by positivity : 0 ≤ 5*R) 8)
    pm_5419 hpow
    exact (hpow.trans (by norm_num; gcongr)).trans hmajor
  · have hnorm : ‖exponentialSumAt F T N a b‖ ≤ 5*R := by
      have hh := norm_exponentialSumAt_le_card F T N a b
      have hcard : ((Finset.Icc a b).card:ℝ) ≤ 2*(K:ℝ)+1 := by
        have hn : (Finset.Icc a b).card ≤ 2*K+1 := by rw [Nat.card_Icc]; omega
        exact_mod_cast hn
      exact (hh.trans hcard).trans hboundary
    have hp := pow_le_pow_left₀ (norm_nonneg _) hnorm 8
    pm_5419 hp
    exact hp.trans ((by nlinarith only [mul_nonneg hC₀.le hZ,pow_nonneg hR.le 8] :
      5^8*R^8 ≤ 128*(C₀*Z+5^8*R^8)).trans hmajor)

                                                                        
section
variable {X T : VariableObject ℝ} {a : ℝ} (hX : IsPowerAsymptotic X T a) (hT : ∀ i, 1 ≤ T i)
include X T a hX hT
private theorem cubic_power_rpow (p : ℝ) :
    IsPowerAsymptotic (fun i => (X i)^p) T (a*p) := by
  obtain ⟨e,he,hXe⟩ := hX
  refine ⟨fun i => e i*p,?_,?_⟩
  · convert he.const_smul p using 1
    · funext i
      exact mul_comm (e i) p
    · funext i
      exact mul_comm a p
  · filter_upwards [hXe] with i hi
    rw [hi,← Real.rpow_mul (zero_le_one.trans (hT i))]

private theorem cubic_power_natpow (n : ℕ) :
    IsPowerAsymptotic (fun i => (X i)^n) T (a*(n:ℝ)) := by
  simpa only [Real.rpow_natCast] using cubic_power_rpow hX hT (n:ℝ)
end

private theorem cubic_power_const
    {T : VariableObject ℝ} (hT : ∀ i, 1 ≤ T i) (hTunbounded : T.IsUnbounded)
    {c : ℝ} (hc : 0 < c) :
    IsPowerAsymptotic (fun _ => c) T 0 := by
  pm_1391
  apply isPowerAsymptotic_of_logb_tendsto
    (hTtop.eventually (eventually_gt_atTop 1)) (Filter.Eventually.of_forall (fun _ => hc))
  simpa only [Real.logb,Function.comp_apply] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.log c) atTop (𝓝 (Real.log c))).div_atTop
      (Real.tendsto_log_atTop.comp hTtop)

private theorem cubic_power_eventually_le
    {X T : VariableObject ℝ} {a b : ℝ}
    (hX : IsPowerAsymptotic X T a) (hT : ∀ i, 1 ≤ T i) (hab : a < b) :
    ∀ᶠ i in atTop, X i ≤ (T i)^b := by
  have hh := hX.eventually_between (Filter.Eventually.of_forall hT)
    (sub_pos.mpr hab)
  filter_upwards [hh] with i hi
  convert hi.2 using 1
  congr 1
  ring

                                                                      
                                                     
private theorem cubic_dyadic_index_bound
    {T X : VariableObject ℝ} (hT : ∀ i, 1 ≤ T i) (hTunbounded : T.IsUnbounded)
    {q η : ℝ} (hq : 0 < q) (hη : 0 < η)
    (hX : ∀ᶠ i in atTop, 1 ≤ X i ∧ X i ≤ (T i)^q) :
    ∀ᶠ i in atTop, ∃ J : ℕ, X i ≤ (2:ℝ)^J ∧ (J:ℝ)+2 ≤ (T i)^η := by
  let γ := η/(2*q)
  pm_64 hγ γ
  obtain ⟨D,hD,hcount⟩ := exists_dyadic_count_sq_le_rpow hγ
  pm_1391
  have hconstant := hTtop.eventually (eventually_const_mul_rpow_le_rpow
    (D := 2*D*(2:ℝ)^γ) (a := η/2) (b := η) (by linarith))
  filter_upwards [hX,hconstant] with i hi hconst
  obtain ⟨J,hJlo,hJhi⟩ := exists_dyadic_cutoff hi.1
  refine ⟨J,hJlo,?_⟩
  have hJ := hcount J
  have hj : (J:ℝ)+2 ≤ 2*((J:ℝ)+1)^2 := by
    nlinarith only [(Nat.cast_nonneg J : (0:ℝ) ≤ J),sq_nonneg (J:ℝ)]
  pm_5104 hTp T hT
  calc
    _ ≤ 2*(D*((2:ℝ)^J)^γ) := hj.trans (by gcongr)
    _ ≤ 2*(D*(2*(T i)^q)^γ) := by gcongr; exact hJhi.trans (by gcongr; exact hi.2)
    _ = (2*D*2^γ)*(T i)^(η/2) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity),
        ← Real.rpow_mul hTp.le]
      have he : q*γ=η/2 := by dsimp [γ]; field_simp
      rw [he]
      ring
    _ ≤ _ := hconst

                                                                        
                                                                            
theorem eventually_cubic_bourgain_parameters
    {T N : VariableObject ℝ} {α σ κ₀ η : ℝ}
    (hlo : 140/391 ≤ α) (hhi : α < 16/39) (hσ : 0 < σ)
    (hκ₀ : 0 < κ₀) (hη : 0 < η)
    (hT : ∀ i, 1 ≤ T i) (hTunbounded : T.IsUnbounded)
    (hNT : IsPowerAsymptotic N T α) :
    let h := (246*α-55)/398
    let r := (362*α-123)/398
    let H := floorRpow T h
    let Y := fun i => (T i)^r
    let lam := fun i => modelPhaseJetLower σ 3*T i/(N i)^4
    let B := fun i => (modelPhaseJetCoefficient σ 3+1)*T i/(N i)^4
    let L := fun i => modelPhaseJetLower σ 2*T i/(N i)^3
    let U := fun i => (modelPhaseJetCoefficient σ 2+1)*T i/(N i)^3
    let Qcut := fun i => 3/(2*lam i*(H i:ℝ)^3)
    ∀ᶠ i in atTop, 0 < N i ∧ 2 ≤ H i ∧ 2 ≤ Y i ∧
      ∃ J : ℕ, 1 ≤ Qcut i ∧ Qcut i ≤ (2:ℝ)^J ∧ (J:ℝ)+2 ≤ (T i)^η ∧
        1/(4*(H i:ℝ)^2) ≤ L i/4 ∧
        4*U i*Qcut i*(N i)^2/(σ*T i) ≤ κ₀ ∧
        B i*((H i:ℝ)+1)^4 ≤ 1 := by
  intro h r H Y lam B L U Qcut
  let q := 4*α-1-3*h
  pm_5331 hh h
  pm_5331 hr r
  have hq : 0 < q := by dsimp [q,h]; linarith only [hlo]
  pm_909
  have hY : IsPowerAsymptotic Y T r := by
    simpa using cubic_power_rpow hTscale hT r
  pm_2057
  have hB : IsPowerAsymptotic B T (1-4*α) := by
    convert ((hc (modelPhaseJetCoefficient σ 3+1) (by positivity [modelPhaseJetCoefficient_pos hσ 3])).mul hTscale hT).div
      (cubic_power_natpow hNT hT 4) hT using 1
    ring
  have hL : IsPowerAsymptotic L T (1-3*α) := by
    convert ((hc _ (modelPhaseJetLower_pos hσ 2)).mul hTscale hT).div
      (cubic_power_natpow hNT hT 3) hT using 1
    ring
  have hU : IsPowerAsymptotic U T (1-3*α) := by
    convert ((hc (modelPhaseJetCoefficient σ 2+1) (by positivity [modelPhaseJetCoefficient_pos hσ 2])).mul hTscale hT).div
      (cubic_power_natpow hNT hT 3) hT using 1
    ring
  pm_2058
  pm_1462 hLH L hL.mul
  have hshift : IsPowerAsymptotic (fun i => 4*U i*Qcut i*(N i)^2/(σ*T i)) T (q-α) := by
    convert ((((hc 4 (by norm_num)).mul hU hT).mul hQ hT).mul
      (cubic_power_natpow hNT hT 2) hT).div ((hc σ hσ).mul hTscale hT) hT using 1
    ring
  have htaylor : IsPowerAsymptotic (fun i => 16*B i*(H i:ℝ)^4) T (1-4*α+4*h) := by
    convert ((hc 16 (by norm_num)).mul hB hT).mul
      (cubic_power_natpow hH hT 4) hT using 1
    ring
  pm_1133
  have hHlarge := (hH.tendsto_atTop_of_pos hh hT hTunbounded).eventually
    (eventually_ge_atTop 2)
  have hYlarge := (hY.tendsto_atTop_of_pos hr hT hTunbounded).eventually
    (eventually_ge_atTop 2)
  have hQlarge := (hQ.tendsto_atTop_of_pos hq hT hTunbounded).eventually
    (eventually_ge_atTop 1)
  have hLHlarge := (hLH.tendsto_atTop_of_pos
    (by dsimp [h]; linarith only [hhi] : 0 < 1-3*α+2*h) hT hTunbounded).eventually
    (eventually_ge_atTop 1)
  have hshiftsmall := (hshift.tendsto_zero_of_neg
    (by dsimp [q,h]; linarith only [hhi] : q-α < 0) hT hTunbounded).eventually
    (eventually_lt_nhds hκ₀)
  have htaylorsmall := (htaylor.tendsto_zero_of_neg
    (by dsimp [h]; linarith only [hlo] : 1-4*α+4*h < 0) hT hTunbounded).eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ) < 1))
  have hindex := cubic_dyadic_index_bound hT hTunbounded
    (by linarith only [hq] : 0 < q+1) hη
    (hQlarge.and (cubic_power_eventually_le hQ hT (by linarith : q<q+1)))
  filter_upwards [hNlarge,hHlarge,hYlarge,hLHlarge,hshiftsmall,htaylorsmall,hindex,hQlarge]
    with i hNi hHi hYi hLHi hsi hti hJi hQi
  obtain ⟨J,hJq,hJcount⟩ := hJi
  refine ⟨hNi,by exact_mod_cast hHi,hYi,J,hQi,hJq,hJcount,?_,hsi.le,?_⟩
  · have hHp : (0:ℝ) < H i := by linarith only [hHi]
    apply (div_le_iff₀ (by positivity : 0 < 4*(H i:ℝ)^2)).mpr
    nlinarith only [hLHi]
  · have hBp : 0 < B i := by
      dsimp [B]
      positivity [modelPhaseJetCoefficient_pos hσ 3,zero_lt_one.trans_le (hT i)]
    have hsum : (H i:ℝ)+1 ≤ 2*(H i:ℝ) := by linarith only [hHi]
    have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (H i:ℝ)+1) hsum 4
    have hm := mul_le_mul_of_nonneg_left hp hBp.le
    nlinarith only [hm,hti]


                                                                 
                                                                      
theorem eventually_cubic_bourgain_cost
    {T N : VariableObject ℝ} {α σ η : ℝ}
    (hlo : 140/391 ≤ α) (hhi : α < 16/39) (hσ : 0 < σ) (hη : 0 < η)
    (hT : ∀ i, 1 ≤ T i) (hTunbounded : T.IsUnbounded)
    (hNT : IsPowerAsymptotic N T α) :
    let h := (246*α-55)/398
    let r := (362*α-123)/398
    let β := 18/199+(521/796)*α
    let H := floorRpow T h
    let Y := fun i => (T i)^r
    let lam := fun i => modelPhaseJetLower σ 3*T i/(N i)^4
    let B := fun i => (modelPhaseJetCoefficient σ 3+1)*T i/(N i)^4
    let U := fun i => (modelPhaseJetCoefficient σ 2+1)*T i/(N i)^3
    let Qcut := fun i => 3/(2*lam i*(H i:ℝ)^3)
    ∀ᶠ i in atTop, ∀ J : ℕ, (J:ℝ)+2 ≤ (T i)^η →
      let E := ((J:ℝ)+2)*(U i/(lam i*(H i:ℝ)^2))*
        (1+B i/((lam i)^2*(H i:ℝ)^4)+Qcut i/(H i:ℝ)+Qcut i/Y i+
          (T i/(N i)^2)^(13/84+η)*(Qcut i)^(55/84+η)*(Y i)^(13/84+η)+(N i)^2/T i)
      (N i)^6*(N i+E)*(1+U i*(H i:ℝ)^2)*(H i:ℝ)^η+
          (H i:ℝ)^8+((H i:ℝ)^2+Qcut i+1)^8 ≤
        (15+3^8)*(T i)^(8*β+5*η) := by
  intro h r β H Y lam B U Qcut
  let q := 4*α-1-3*h
  let V := fun i => U i/(lam i*(H i:ℝ)^2)
  let f₁ := fun i => V i/N i
  let f₂ := fun i => V i*(B i/((lam i)^2*(H i:ℝ)^4))/N i
  let f₃ := fun i => V i*(Qcut i/(H i:ℝ))/N i
  let f₄ := fun i => V i*(Qcut i/Y i)/N i
  let f₅ := fun i => V i*((T i/(N i)^2)^(13/84+η)*(Qcut i)^(55/84+η)*(Y i)^(13/84+η))/N i
  let f₆ := fun i => V i*((N i)^2/T i)/N i
  pm_5331 hh h
  pm_909
  have hY : IsPowerAsymptotic Y T r := by simpa using cubic_power_rpow hTscale hT r
  pm_2057
  have hB : IsPowerAsymptotic B T (1-4*α) := by
    convert ((hc (modelPhaseJetCoefficient σ 3+1)
      (by positivity [modelPhaseJetCoefficient_pos hσ 3])).mul hTscale hT).div
      (cubic_power_natpow hNT hT 4) hT using 1
    ring
  have hU : IsPowerAsymptotic U T (1-3*α) := by
    convert ((hc (modelPhaseJetCoefficient σ 2+1)
      (by positivity [modelPhaseJetCoefficient_pos hσ 2])).mul hTscale hT).div
      (cubic_power_natpow hNT hT 3) hT using 1
    ring
  pm_2058
  have hV : IsPowerAsymptotic V T (α-2*h) := by
    convert hU.div (hlam.mul (cubic_power_natpow hH hT 2) hT) hT using 1
    ring
  have hf₁ : IsPowerAsymptotic f₁ T (-2*h) := by
    convert hV.div hNT hT using 1
    ring
  have hf₂ : IsPowerAsymptotic f₂ T (4*α-1-6*h) := by
    convert (hV.mul (hB.div ((cubic_power_natpow hlam hT 2).mul
      (cubic_power_natpow hH hT 4) hT) hT) hT).div hNT hT using 1
    ring
  have hf₃ : IsPowerAsymptotic f₃ T (4*α-1-6*h) := by
    pm_7969 hH
    dsimp [q]
    ring
  have hf₄ : IsPowerAsymptotic f₄ T 0 := by
    pm_7969 hY
    dsimp [q,h,r]
    ring
  have hf₅ : IsPowerAsymptotic f₅ T (η*(1-2*α+q+r)) := by
    convert (hV.mul (((cubic_power_rpow (hTscale.div
      (cubic_power_natpow hNT hT 2) hT) hT (13/84+η)).mul
        (cubic_power_rpow hQ hT (55/84+η)) hT).mul
          (cubic_power_rpow hY hT (13/84+η)) hT) hT).div hNT hT using 1
    dsimp [q,h,r]
    ring
  have hf₆ : IsPowerAsymptotic f₆ T (2*α-1-2*h) := by
    convert (hV.mul ((cubic_power_natpow hNT hT 2).div hTscale hT) hT).div hNT hT using 1
    ring
  have hmain : IsPowerAsymptotic
      (fun i => (N i)^7*U i*(H i:ℝ)^2*(H i:ℝ)^η) T (8*β+h*η) := by
    convert (((cubic_power_natpow hNT hT 7).mul hU hT).mul
      (cubic_power_natpow hH hT 2) hT).mul (cubic_power_rpow hH hT η) hT using 1
    dsimp [β,h]
    ring
  pm_1462 hwidth U hU.mul
  have hqβ : q < β := by dsimp [q,h,β]; linarith only [hlo,hhi]
  have h2hβ : 2*h < β := by dsimp [h,β]; linarith only [hlo,hhi]
  have hhβ : h < β := by linarith only [hh,h2hβ]
  have hβ : 0 < β := by linarith only [hh,hhβ]
  have he₂ : 4*α-1-6*h ≤ 0 := by dsimp [h]; linarith only [hhi]
  have he₆ : 2*α-1-2*h < 0 := by dsimp [h]; linarith only [hhi]
  have he₅ : 1-2*α+q+r < 1 := by dsimp [q,h,r]; linarith only [hhi]
  have hh1 : h < 1 := by dsimp [h]; linarith only [hhi]
  have hb₁ := cubic_power_eventually_le hf₁ hT (by linarith only [hh,hη] : -2*h<2*η)
  pm_5481 hb₂ hf₂
  pm_5481 hb₃ hf₃
  have hb₄ := cubic_power_eventually_le hf₄ hT (by linarith only [hη] : 0<2*η)
  have hb₅ := cubic_power_eventually_le hf₅ hT
    (by nlinarith only [he₅,hη] : η*(1-2*α+q+r)<2*η)
  have hb₆ := cubic_power_eventually_le hf₆ hT (by linarith only [he₆,hη] : 2*α-1-2*h<2*η)
  have hbmain := cubic_power_eventually_le hmain hT
    (by nlinarith only [hh1,hη] : 8*β+h*η<8*β+2*η)
  have hbH := cubic_power_eventually_le hH hT hhβ
  have hbH₂ := cubic_power_eventually_le (cubic_power_natpow hH hT 2) hT
    (by linarith only [h2hβ] : h*2<β)
  have hbQ := cubic_power_eventually_le hQ hT hqβ
  have hbwidth := (hwidth.tendsto_atTop_of_pos
    (by dsimp [h]; linarith only [hhi] : 0 < 1-3*α+2*h) hT hTunbounded).eventually
      (eventually_ge_atTop 1)
  pm_1133
  filter_upwards [hb₁,hb₂,hb₃,hb₄,hb₅,hb₆,hbmain,hbH,hbH₂,hbQ,hbwidth,hNlarge]
    with i h₁ h₂ h₃ h₄ h₅ h₆ hm hHi hH₂i hQi hwi hNi
  intro J hJ E
  pm_5104 hTi T hT
  have hHp : (0:ℝ) < H i := by exact_mod_cast floorRpow_pos T h i
  have hUp : 0 < U i := by dsimp [U]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hlampos : 0 < lam i := by dsimp [lam]; positivity [modelPhaseJetLower_pos hσ 3]
  have hQp : 0 < Qcut i := by dsimp [Qcut]; positivity
  have hVp : 0 < V i := by dsimp [V]; positivity
  have hsum : f₁ i+f₂ i+f₃ i+f₄ i+f₅ i+f₆ i ≤ 6*(T i)^(2*η) := by
    linarith only [h₁,h₂,h₃,h₄,h₅,h₆]
  have heq : E=((J:ℝ)+2)*N i*(f₁ i+f₂ i+f₃ i+f₄ i+f₅ i+f₆ i) := by
    dsimp [E,f₁,f₂,f₃,f₄,f₅,f₆,V]
    field_simp
  have hE : E ≤ 6*N i*(T i)^(3*η) := by
    rw [heq]
    calc
      _ ≤ ((J:ℝ)+2)*N i*(6*(T i)^(2*η)) := by gcongr
      _ ≤ (T i)^η*N i*(6*(T i)^(2*η)) := by gcongr
      _ = _ := by
        rw [show (T i)^η*N i*(6*(T i)^(2*η)) =
          6*N i*((T i)^η*(T i)^(2*η)) by ring,← Real.rpow_add hTi]
        congr 2
        ring
  have hone₃ : 1 ≤ (T i)^(3*η) := Real.one_le_rpow (hT i) (by positivity)
  have hNE : N i+E ≤ 7*N i*(T i)^(3*η) := by
    have hn := mul_le_mul_of_nonneg_left hone₃ hNi.le
    nlinarith only [hE,hn]
  have hUW : 1+U i*(H i:ℝ)^2 ≤ 2*U i*(H i:ℝ)^2 := by linarith only [hwi]
  have hcost : (N i)^6*(N i+E)*(1+U i*(H i:ℝ)^2)*(H i:ℝ)^η ≤
      14*(T i)^(8*β+5*η) := by
    calc
      _ ≤ (N i)^6*(7*N i*(T i)^(3*η))*(2*U i*(H i:ℝ)^2)*(H i:ℝ)^η := by gcongr
      _ = 14*((N i)^7*U i*(H i:ℝ)^2*(H i:ℝ)^η)*(T i)^(3*η) := by ring
      _ ≤ 14*(T i)^(8*β+2*η)*(T i)^(3*η) := by gcongr
      _ = _ := by rw [mul_assoc,← Real.rpow_add hTi]; congr 2; ring
  have honeβ : 1 ≤ (T i)^β := Real.one_le_rpow (hT i) hβ.le
  have hR : (H i:ℝ)^2+Qcut i+1 ≤ 3*(T i)^β := by
    linarith only [hH₂i,hQi,honeβ]
  have hH8 : (H i:ℝ)^8 ≤ (T i)^(8*β+5*η) := by
    calc
      _ ≤ ((T i)^β)^8 := pow_le_pow_left₀ hHp.le hHi 8
      _ = (T i)^(8*β) := by rw [← Real.rpow_mul_natCast hTi.le]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (hT i) (by linarith only [hη])
  have hR8 : ((H i:ℝ)^2+Qcut i+1)^8 ≤ 3^8*(T i)^(8*β+5*η) := by
    calc
      _ ≤ (3*(T i)^β)^8 := pow_le_pow_left₀ (by positivity) hR 8
      _ = 3^8*(T i)^(8*β) := by
        rw [mul_pow,← Real.rpow_mul_natCast hTi.le]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (hT i) (by linarith only [hη])) (by norm_num)
  linarith only [hcost,hH8,hR8]


                                                                         
                                                                       
                                                         
section
variable {α : ℝ≥0} (hlo : 140/391 ≤ (α:ℝ)) (hhi : (α:ℝ) < 16/39)
include α hlo hhi
theorem isExponentSumBound_cubic_bourgain_gap :
    IsExponentSumBound α (18/199+(521/796)*(α:ℝ)) := by
  intro N T F a b _hN hT hTunbounded hNT hF hab
  apply (isPowerBounded_iff_forall_pos
    (exponentialSum F T N a b) T (18/199+(521/796)*(α:ℝ)) hT hTunbounded).mpr
  pm_6438
  pm_4843 hη η lt_min hε
  have hηε : η ≤ ε := min_le_right _ _
  have hηsmall : (13/84:ℝ)+η < 1 := by
    pm_8676 hh η
    linarith only [hh]
  obtain ⟨hphase,σ,hσ,herror⟩ := hF
  obtain ⟨δ,κ₀,hδ,hκ₀,Q,_hQ,C₀,hC₀,hsource⟩ :=
    TaoTrudgianYang2025.CubicJointCount.exists_complete_cubic_eighth_estimate
      hσ exponentPair_bourgain hη hηsmall
  pm_8053
  pm_528 hparameters eventually_cubic_bourgain_parameters hlo hhi hσ hκ₀ hη hT hTunbounded hNT
  have hcost := eventually_cubic_bourgain_cost hlo hhi hσ hη hT hTunbounded hNT
  let β := 18/199+(521/796)*(α:ℝ)
  let C := max 1 (C₀*(15+3^8))
  pm_4884 hC C
  have hC₀C : C₀*(15+3^8) ≤ C := le_max_right _ _
  have hCpow : C ≤ C^8 := by
    calc
      C = C*1 := (mul_one C).symm
      _ ≤ C*C^7 := mul_le_mul_of_nonneg_left (one_le_pow₀ hC) (zero_le_one.trans hC)
      _ = _ := by ring
  pm_6439
  obtain ⟨hNi,hHi,hYi,J,hQi,hQJ,hJ,hcurv,hshift,hTaylor⟩ := hpi
  pm_5104 hTi T hT
  have hs := hsource (F i) (T i) (N i)
    ((T i)^((362*(α:ℝ)-123)/398)) (a i) (b i)
    (floorRpow T ((246*(α:ℝ)-55)/398) i) J
    hFi hTi hNi hHi hYi (hab i).1 (hab i).2
    hQi hQJ hcurv hshift hTaylor
  have hmajor := mul_le_mul_of_nonneg_left (hci J hJ) hC₀.le
  have hbound : ‖exponentialSumAt (F i) (T i) (N i) (a i) (b i)‖^8 ≤
      C₀*(15+3^8)*(T i)^(8*β+5*η) := by
    exact hs.trans (by convert hmajor using 1; ring)
  have hexp : 8*β+5*η ≤ (β+ε)*8 := by linarith only [hηε,hε]
  have hp : ‖exponentialSumAt (F i) (T i) (N i) (a i) (b i)‖^8 ≤
      (C*(T i)^(β+ε))^8 := by
    calc
      _ ≤ C₀*(15+3^8)*(T i)^(8*β+5*η) := hbound
      _ ≤ C^8*(T i)^((β+ε)*8) :=
        mul_le_mul (hC₀C.trans hCpow) (Real.rpow_le_rpow_of_exponent_le (hT i) hexp)
          (Real.rpow_nonneg hTi.le _) (by positivity)
      _ = _ := by rw [mul_pow,← Real.rpow_mul_natCast hTi.le]; norm_num
  have hh := (pow_le_pow_iff_left₀ (norm_nonneg _)
    (by positivity : 0 ≤ C*(T i)^(β+ε)) (by norm_num : (8:ℕ)≠0)).mp hp
  pm_6668

theorem exponentSumGrowthExponent_le_cubic_bourgain_gap :
    exponentSumGrowthExponent α ≤ 18/199+(521/796)*(α:ℝ) :=
  exponentSumGrowthExponent_le_iff.mpr (isExponentSumBound_cubic_bourgain_gap hlo hhi)
end

                                                                         
                                                                            
theorem bourgain_d_target_outside_gap
    {α : NNReal} (hhalf : (α:ℝ) ≤ 1/2)
    (hgap : (α:ℝ) ≤ 140/391 ∨ 16/39 ≤ (α:ℝ)) :
    exponentSumGrowthExponent α ≤ (18:ℝ)/199+521/796*(α:ℝ) := by
  rcases hgap with hlo | hhi
  · have h := exponentSumGrowthExponent_le_exponentPairLine_closed
      exponentPair_robertSargos α (by linarith only [hhalf])
    unfold exponentPairLine at h
    linarith only [h,hlo]
  · by_cases hfirst : (α:ℝ) ≤ 5/12
    · have h := TaoTrudgianYang2025.exponentSumGrowthExponent_le_bourgain_table_first
        (α:=α) (by linarith only [hhi]) hfirst
      linarith only [h,hhi]
    · by_cases hsecond : (α:ℝ) ≤ 3/7
      · have h := TaoTrudgianYang2025.exponentSumGrowthExponent_le_bourgain_table_second
          (α:=α) (le_of_not_ge hfirst) hsecond
        linarith only [h,hhalf]
      · have h := exponentSumGrowthExponent_le_bourgain_baseline
          (α:=α) (le_of_not_ge hsecond) hhalf
        have hα : (3:ℝ)/7 ≤ (α:ℝ) := le_of_not_ge hsecond
        linarith only [h,hα]

theorem exponentPair_sargosD_bourgain : ExponentPair (18/199) (593/796) := by
  apply exponentPair_of_beta_bound_half (by norm_num [InExponentPairTriangle]) (by norm_num)
  intro α hhalf
  have hbound : exponentSumGrowthExponent α ≤ 18/199+(521/796)*(α:ℝ) := by
    by_cases hlo : (α:ℝ) ≤ 140/391
    · exact bourgain_d_target_outside_gap hhalf (Or.inl hlo)
    · by_cases hhi : (α:ℝ) < 16/39
      · exact exponentSumGrowthExponent_le_cubic_bourgain_gap (le_of_not_ge hlo) hhi
      · exact bourgain_d_target_outside_gap hhalf (Or.inr (le_of_not_gt hhi))
  convert hbound using 1
  unfold exponentPairLine
  ring

theorem exponentSumGrowthExponent_le_sargosD_bourgain
    {α : ℝ≥0} (hα : (α:ℝ) ≤ 1) :
    exponentSumGrowthExponent α ≤ 18/199+(521/796)*(α:ℝ) := by
  have h := exponentSumGrowthExponent_le_exponentPairLine_closed exponentPair_sargosD_bourgain α hα
  convert h using 1
  unfold exponentPairLine
  ring

section
variable {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ) (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1)
include σ k₀ l₀ ε hσ hpair hε hp
theorem original_joint_level_displacement_count :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 2 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (T N d D a b R B lam δ₁ δ₂ W : ℝ)
          (K : ℤ) (S : Finset (ℤ × ℕ)),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 2 ≤ d → 0 < D → 0 < R → 0 ≤ B → 0 < lam →
          N < a-R → b+R+2*D < 2*N →
          δ₂ ≤ lam*d*R/2 → δ₁+2*B*D*R^2 ≤ W/2 →
          0 < K → 2*(K:ℝ)*N^2/(σ*T) ≤ κ₀ → 0 < W → W ≤ 1/2 →
          let f := fun z => T*F (z/N)
          (∀ t∈Icc (a-R) (b+R+2*D),
            -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam) →
          (∀ p∈S, (p.1:ℝ)∈Icc a b ∧ (p.2:ℝ)∈Icc d (2*D)) →
          (∀ p∈S, |(iteratedDeriv 2 f ((p.1:ℝ)+(p.2:ℝ))-
            iteratedDeriv 2 f p.1)/2-(K:ℝ)| ≤ δ₂) →
          (∀ p∈S, ∃ e : ℤ, |iteratedDeriv 1 f ((p.1:ℝ)+(p.2:ℝ))-
            iteratedDeriv 1 f p.1-(e:ℝ)| ≤ δ₁) →
            ((S.image Prod.snd).card:ℝ) ≤
              C*(W*D+(T/N^2)^(k₀+ε)*D^(l₀+ε)*W^(-(k₀+ε))+N^2/T) := by
  pm_2046 δ hδ Q hQ C hC hcount original_second_level_near_curve_count
  pm_2039
  intro F T N d D a b R B lam δ₁ δ₂ W K S hF hT hN hd hDpos hR hB hlam
    hleft hright hbuffer hwidth hK hκle hW hWhalf f hfour hbox hsecond hfirst
  have hdpos : 0 < d := by linarith
  let J := S.image Prod.snd
  have hmem (q : ℕ) (hq : q∈J) : d ≤ (q:ℝ) ∧ (q:ℝ) ≤ 2*D := by
    pm_2044
  pb_446
  have hex (q : ℕ) (hq : q∈J) :
      ∃ x : ℝ, x/N∈Ioo (1:ℝ) 2 ∧ (x+(q:ℝ))/N∈Ioo (1:ℝ) 2 ∧
        (iteratedDeriv 2 f (x+(q:ℝ))-iteratedDeriv 2 f x)/2=(K:ℝ) ∧
        ∃ e : ℤ, |iteratedDeriv 1 f (x+(q:ℝ))-iteratedDeriv 1 f x-
          2*(K:ℝ)*x-(e:ℝ)| ≤ W/2 := by
    pm_5286 hdpos.trans_le
    pm_2042
  pm_2043
  pm_2047 hd.trans
  exact hcountJ

                                                                            
                                                                        
                                   
theorem original_model_block_source_pair_count :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 2 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ {ι : Type*} [DecidableEq ι] (S : Finset ι) (V : Finset (ι × ι))
          (center block : ι → ℤ) (H Bmul : ℕ) (s K : ℤ)
          (F : ℝ → ℝ) (T N d D a b R B lam δ₁ δ₂ W : ℝ),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 2 ≤ d → 0 < D → 0 < R → 0 ≤ B →
          0 < lam → 0 ≤ δ₂ → 0 < H →
          N < a-R → b+R+2*D < 2*N →
          δ₂ ≤ lam*d*R/2 → δ₁+2*B*D*R^2 ≤ W/2 →
          0 < K → 2*(K:ℝ)*N^2/(σ*T) ≤ κ₀ → 0 < W → W ≤ 1/2 →
          (∀ i∈S, (H:ℤ) ≤ s+(H:ℤ)*block i-center i ∧
            s+(H:ℤ)*block i-center i ≤ 3*(H:ℤ)) →
          (∀ j : ℤ, (S.filter (fun i => block i=j)).card ≤ Bmul) →
          (∀ i∈S, (center i:ℝ)∈Icc a b) →
          V ⊆ S ×ˢ S →
          (∀ p∈V, (center p.2:ℝ)-center p.1∈Icc d (2*D)) →
          let f := fun z => T*F (z/N)
          (∀ t∈Icc (a-R) (b+R+2*D),
            -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam) →
          (∀ p∈V, |(iteratedDeriv 2 f (center p.2)-
            iteratedDeriv 2 f (center p.1))/2-(K:ℝ)| ≤ δ₂) →
          (∀ p∈V, ∃ e : ℤ, |iteratedDeriv 1 f (center p.2)-
            iteratedDeriv 1 f (center p.1)-(e:ℝ)| ≤ δ₁) →
            (V.card:ℝ) ≤ (3*(Bmul:ℝ)^2*(3+8*δ₂/(lam*d*H)))*
              (C*(W*D+(T/N^2)^(k₀+ε)*D^(l₀+ε)*W^(-(k₀+ε))+N^2/T)) := by
  pm_2046 δ hδ Q hQ C hC hcount original_joint_level_displacement_count
  pm_2039
  intro ι _ S V center block H Bmul s K F T N d D a b R B lam δ₁ δ₂ W
    hF hT hN hd hD hR hB hlam hδ₂ hH hleft hright hbuffer hwidth hK hκle hW hWhalf
    hspan hmul hcenter hVS hdisp f hfour hsecond hfirst
  have hdp : 0 < d := by linarith
  pm_1661
  let n := fun p : ι × ι => (center p.2-center p.1).toNat
  let E := V.image (fun p => (center p.1,n p))
  let J := E.image Prod.snd
  have hn p (hp : p∈V) : (n p:ℝ)=(center p.2:ℝ)-center p.1 := by
    have hnn : 0 ≤ center p.2-center p.1 := by
      exact_mod_cast (hdp.le.trans (hdisp p hp).1)
    have he := Int.toNat_of_nonneg hnn
    exact_mod_cast he
  have hpoints p (hp : p∈V) : (center p.1:ℝ)+(n p:ℝ)=center p.2 := by
    rw [hn p hp]
    ring
  have hcountJ : (J.card:ℝ) ≤
      C*(W*D+(T/N^2)^(k₀+ε)*D^(l₀+ε)*W^(-(k₀+ε))+N^2/T) := by
    apply hcount F T N d D a b R B lam δ₁ δ₂ W K E hF hT hN hd hD hR hB hlam
      hleft hright hbuffer hwidth hK hκle hW hWhalf hfour
    · intro p hp
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hp
      exact ⟨hcenter _ (Finset.mem_product.mp (hVS hv)).1, by
        simpa only [hn v hv] using hdisp v hv⟩
    pm_5519 hsecond
    pm_5519 hfirst
  have hf t (ht : t∈Ioo (a-R) (b+R+2*D)) : ContDiffAt ℝ 4 f t := by
    have hnrm : t/N∈Ioo (1:ℝ) 2 := by
      constructor
      · apply (one_lt_div hN).mpr
        linarith [ht.1]
      · apply (div_lt_iff₀ hN).mpr
        linarith [ht.2]
    have hc := (approximateModelPhase_contDiffAt hF hnrm).comp t
      (show ContDiffAt ℝ ∞ (fun z : ℝ => z/N) t by fun_prop)
    exact (contDiffAt_const.mul hc).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)
  have hcent i (hi : i∈S) : (center i:ℝ)∈Ioo (a-R) (b+R+2*D) := by
    pm_1342 hcenter
  let M := 3*(Bmul:ℝ)^2*(3+8*δ₂/(lam*d*H))
  pm_82 hM M
  have hfiber q : ((V.filter (fun p => n p=q)).card:ℝ) ≤ M := by
    pm_2283 Vq V.filter p n q
    by_cases hvq : Vq.Nonempty
    · obtain ⟨v,hv⟩ := hvq
      obtain ⟨hv,he⟩ := Finset.mem_filter.mp hv
      have hqd : d ≤ (q:ℝ) := by rw [←he,hn v hv]; exact (hdisp v hv).1
      have hqp : (0:ℝ)<q := hdp.trans_le hqd
      have hb := fixed_displacement_source_pair_fibers S Vq center block H Bmul s f
        hH hlam hqp hδ₂ hspan hmul hf
        (fun t ht => (hfour t ⟨ht.1.le,ht.2.le⟩).2) hcent
        (fun p hp => hVS (Finset.mem_filter.mp hp).1)
        (fun p hp => by
          rw [←hn p (Finset.mem_filter.mp hp).1,(Finset.mem_filter.mp hp).2])
        (fun p hp => hsecond p (Finset.mem_filter.mp hp).1)
      have hfrac : 8*δ₂/(lam*(q:ℝ)*H) ≤ 8*δ₂/(lam*d*H) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqd hlam.le) hHr.le)
      pm_7173
    · change (Vq.card:ℝ) ≤ M
      rw [Finset.not_nonempty_iff_eq_empty.mp hvq,Finset.card_empty,Nat.cast_zero]
      exact hM
  have hmap p (hp : p∈V) : n p∈J :=
    Finset.mem_image.mpr ⟨(center p.1,n p),Finset.mem_image_of_mem _ hp,rfl⟩
  have hc : (V.card:ℝ)=∑ q∈J,((V.filter (fun p => n p=q)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmap
  calc
    _ = _ := hc
    _ ≤ ∑ _q∈J,M := Finset.sum_le_sum (fun q _ => hfiber q)
    _ = M*J.card := by simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hcountJ hM
end

                                                                         
                                                                             
theorem original_model_rounded_shift_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 3 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ {ι : Type*} [DecidableEq ι] (S : Finset ι) (V : Finset (ι × ι))
          (center block : ι → ℤ) (z : ι → ℝ) (H Bmul : ℕ) (s K : ℤ)
          (F : ℝ → ℝ) (T N a b R δ₁ W : ℝ),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 0 < R → 0 < H → 0 < K →
          let L := modelPhaseJetLower σ 2*T/N^3
          let U := (modelPhaseJetCoefficient σ 2+1)*T/N^3
          let lam := modelPhaseJetLower σ 3*T/N^4
          let B := (modelPhaseJetCoefficient σ 3+1)*T/N^4
          let d := (K:ℝ)/(6*U)
          let D := (K:ℝ)/L+1
          12*U ≤ 1 → N < a-R → b+R+2*D < 2*N →
          3*U ≤ lam*d*R/2 → δ₁+2*B*D*R^2 ≤ W/2 →
          2*(K:ℝ)*N^2/(σ*T) ≤ κ₀ → 0 < W → W ≤ 1/2 →
          (∀ i∈S, (H:ℤ) ≤ s+(H:ℤ)*block i-center i ∧
            s+(H:ℤ)*block i-center i ≤ 3*(H:ℤ)) →
          (∀ j : ℤ, (S.filter (fun i => block i=j)).card ≤ Bmul) →
          (∀ i∈S, (center i:ℝ)∈Icc a b) →
          (∀ i∈S, z i∈Ioo N (2*N)) →
          (∀ i∈S, |(center i:ℝ)-z i| ≤ 1/2) →
          V ⊆ S ×ˢ S →
          let f := fun t => T*F (t/N)
          (∀ p∈V, iteratedDeriv 2 f (z p.2)/2-
            iteratedDeriv 2 f (z p.1)/2=(K:ℝ)) →
          (∀ p∈V, ∃ e : ℤ, |iteratedDeriv 1 f (center p.2)-
            iteratedDeriv 1 f (center p.1)-(e:ℝ)| ≤ δ₁) →
            (V.card:ℝ) ≤ (3*(Bmul:ℝ)^2*(3+144*U^2/(lam*(K:ℝ)*H)))*
              (C*(W*D+(T/N^2)^(k₀+ε)*D^(l₀+ε)*W^(-(k₀+ε))+N^2/T)) := by
  pm_2046 δ₀ hδ₀ Q₀ hQ₀ C hC hcount original_model_block_source_pair_count
  pm_2051
  pm_2050
  intro ι _ S V center block z H Bmul s K F T N a b R δ₁ W
    hF hT hN hR hH hK L U lam B d D hUsmall hleft hright hbuffer hwidth
    hκle hW hWhalf hspan hmul hcenter hz hround hVS f hlevel hfirst
  pm_2048
  obtain ⟨hreg,hthree,hfour,_⟩ := hdata F T N hT hN hFd
  pm_2059
  pm_2060
  have hd : 2 ≤ d := by
    pm_7970 U
    linarith
  pm_2841
  pm_2052
  have hcent i (hi : i∈S) : (center i:ℝ)∈Ioo N (2*N) := by
    apply hsegment
    pm_1342 hcenter
  pm_2061 hthree'
  have hdisp p (hp : p∈V) : (center p.2:ℝ)-center p.1∈Icc d (2*D) := by
    have hpp := Finset.mem_product.mp (hVS hp)
    have hb := rounded_positive_curvature_shift_bounds f hL hU
      (by linarith only [hUsmall,hKr,hU] : 6*U ≤ (K:ℝ))
      (fun t ht => (hreg t ht).of_le (by norm_num)) hthree'
      (hz _ hpp.1) (hz _ hpp.2) (hround _ hpp.1) (hround _ hpp.2) (hlevel p hp)
    refine ⟨hb.1,?_⟩
    dsimp only [D]
    have hbhi : (center p.2:ℝ)-center p.1 ≤ 2*((K:ℝ)/L)+1 := by
      simpa only [mul_div_assoc] using hb.2
    linarith only [hbhi]
  have hsecond p (hp : p∈V) :
      |(iteratedDeriv 2 f (center p.2)-iteratedDeriv 2 f (center p.1))/2-(K:ℝ)| ≤ 3*U := by
    have hpp := Finset.mem_product.mp (hVS hp)
    have hseg : uIcc (z p.1) (center p.1:ℝ) ∪ uIcc (z p.2) (center p.2:ℝ) ⊆ Ioo N (2*N) :=
      union_subset ((convex_Ioo N (2*N)).ordConnected.uIcc_subset (hz _ hpp.1) (hcent _ hpp.1))
        ((convex_Ioo N (2*N)).ordConnected.uIcc_subset (hz _ hpp.2) (hcent _ hpp.2))
    pm_2084 hreg hthree'
  have hb := hcount S V center block H Bmul s K F T N d D a b R B lam δ₁ (3*U) W
    hF₀ hT hN hd hD hR hB hlam (by positivity) hH hleft hright hbuffer hwidth
    hK hκle hW hWhalf hspan hmul hcenter hVS hdisp
    (fun t ht => hfour t (hsegment ht)) hsecond hfirst
  have he : 8*(3*U)/(lam*d*H)=144*U^2/(lam*(K:ℝ)*H) := by
    dsimp only [d]
    field_simp
    ring
  rwa [he] at hb

                                                                         
                                                                                
theorem rounded_shift_free_width
    {L U lam B K η w : ℝ}
    (hL : 0 < L) (hU : 0 < U) (hlam : 0 < lam) (hB : 0 ≤ B)
    (hK : 1 ≤ K) (hLK : L ≤ K) (hη : 0 ≤ η) (hw : 0 < w) (hwhalf : w ≤ 1/2)
    (hsmall : 2*η+10368*B*U^4/(lam^2*L) ≤ 1/2) :
    let d := K/(6*U)
    let D := K/L+1
    let R := 36*U^2/(lam*K)
    let W := max (2*η+4*B*D*R^2) w
    0 < R ∧ 0 < W ∧ W ≤ 1/2 ∧
      3*U=lam*d*R/2 ∧ η+2*B*D*R^2 ≤ W/2 ∧
      W*D ≤ (2*η+w)*D+20736*B*U^4/(lam^2*L^2) ∧
      ∀ p : ℝ, 0 ≤ p → W^(-p) ≤ w^(-p) := by
  intro d D R W
  have hKp : 0 < K := zero_lt_one.trans_le hK
  pm_2841
  pm_116 hR R
  have hDup : D ≤ 2*K/L := by
    pm_5443 h1 K L hL hLK
    dsimp only [D]
    rw [mul_div_assoc]
    linarith
  have hraw : 4*B*D*R^2 ≤ 10368*B*U^4/(lam^2*L) := by
    calc
      _ ≤ 4*B*(2*K/L)*R^2 := by gcongr
      _ = 10368*B*U^4/(lam^2*L*K) := by dsimp only [R]; field_simp; ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by nlinarith [mul_le_mul_of_nonneg_left hK (show 0 ≤ lam^2*L by positivity)])
  pm_2546 hW W hw.trans_le le_max_right
  have hwidth : η+2*B*D*R^2 ≤ W/2 := by
    have hh : 2*η+4*B*D*R^2 ≤ W := le_max_left _ _
    linarith
  have hbudget : 4*B*D^2*R^2 ≤ 20736*B*U^4/(lam^2*L^2) := by
    calc
      _ ≤ 4*B*(2*K/L)^2*R^2 := by gcongr
      _ = _ := by dsimp only [R]; field_simp; ring
  have hWD : W*D ≤ (2*η+w)*D+20736*B*U^4/(lam^2*L^2) := by
    have hsum : W ≤ 2*η+4*B*D*R^2+w := by
      apply max_le
      · linarith
      · have hh : 0 ≤ 2*η+4*B*D*R^2 := by positivity
        linarith
    calc
      _ ≤ (2*η+4*B*D*R^2+w)*D := mul_le_mul_of_nonneg_right hsum hD.le
      _ = (2*η+w)*D+4*B*D^2*R^2 := by ring
      _ ≤ _ := add_le_add le_rfl hbudget
  refine ⟨hR,hW,max_le (by linarith only [hraw,hsmall]) hwhalf,?_,hwidth,hWD,?_⟩
  · dsimp only [d,R]
    field_simp
    ring
  · intro p hp
    exact Real.rpow_le_rpow_of_nonpos hw (le_max_right _ _) (neg_nonpos.mpr hp)

                                                                         
                                                                               
                                 
theorem original_model_uniform_positive_shift_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 3 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ {ι : Type*} [DecidableEq ι] (S : Finset ι) (V : Finset (ι × ι))
          (center block : ι → ℤ) (z : ι → ℝ) (H Bmul : ℕ) (s K : ℤ)
          (F : ℝ → ℝ) (T N a b Kmax η w : ℝ),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 0 < H → 0 < K → (K:ℝ) ≤ Kmax →
          0 ≤ η → 0 < w → w ≤ 1/2 →
          let L := modelPhaseJetLower σ 2*T/N^3
          let U := (modelPhaseJetCoefficient σ 2+1)*T/N^3
          let lam := modelPhaseJetLower σ 3*T/N^4
          let B := (modelPhaseJetCoefficient σ 3+1)*T/N^4
          let Rmax := 36*U^2/lam
          let Dmax := Kmax/L+1
          12*U ≤ 1 → L ≤ 1 →
          2*η+10368*B*U^4/(lam^2*L) ≤ 1/2 →
          N < a-Rmax → b+Rmax+2*Dmax < 2*N →
          2*Kmax*N^2/(σ*T) ≤ κ₀ →
          (∀ i∈S, (H:ℤ) ≤ s+(H:ℤ)*block i-center i ∧
            s+(H:ℤ)*block i-center i ≤ 3*(H:ℤ)) →
          (∀ j : ℤ, (S.filter (fun i => block i=j)).card ≤ Bmul) →
          (∀ i∈S, (center i:ℝ)∈Icc a b) →
          (∀ i∈S, z i∈Ioo N (2*N)) →
          (∀ i∈S, |(center i:ℝ)-z i| ≤ 1/2) →
          V ⊆ S ×ˢ S →
          let f := fun t => T*F (t/N)
          (∀ p∈V, iteratedDeriv 2 f (z p.2)/2-
            iteratedDeriv 2 f (z p.1)/2=(K:ℝ)) →
          (∀ p∈V, ∃ e : ℤ, |iteratedDeriv 1 f (center p.2)-
            iteratedDeriv 1 f (center p.1)-(e:ℝ)| ≤ η) →
            (V.card:ℝ) ≤ (3*(Bmul:ℝ)^2*(3+144*U^2/(lam*(K:ℝ)*H)))*
              (C*((2*η+w)*Dmax+20736*B*U^4/(lam^2*L^2)+
                (T/N^2)^(k₀+ε)*Dmax^(l₀+ε)*w^(-(k₀+ε))+N^2/T)) := by
  pm_2046 δ hδ Q hQ C hC hcount original_model_rounded_shift_count
  pm_2039
  intro ι _ S V center block z H Bmul s K F T N a b Kmax η w
    hF hT hN hH hK hKmax hη hw hwhalf L U lam B Rmax Dmax hUsmall hLsmall
    hsmall hleft hright hκle hspan hmul hcenter hz hround hVS f hlevel hfirst
  pm_2059
  pm_2060
  let R := 36*U^2/(lam*(K:ℝ))
  pm_8725 D
  let W := max (2*η+4*B*D*R^2) w
  have hwidth := rounded_shift_free_width hL hU hlam hB hKr (hLsmall.trans hKr)
    hη hw hwhalf hsmall
  change 0 < R ∧ 0 < W ∧ W ≤ 1/2 ∧
    3*U=lam*((K:ℝ)/(6*U))*R/2 ∧ η+2*B*D*R^2 ≤ W/2 ∧
    W*D ≤ (2*η+w)*D+20736*B*U^4/(lam^2*L^2) ∧
    ∀ p : ℝ, 0 ≤ p → W^(-p) ≤ w^(-p) at hwidth
  have hRmax : R ≤ Rmax := by
    apply div_le_div_of_nonneg_left (by positivity) hlam
    nlinarith only [mul_le_mul_of_nonneg_left hKr hlam.le]
  have hDD : D ≤ Dmax := add_le_add
    (div_le_div_of_nonneg_right hKmax hL.le) le_rfl
  pm_116 hDp D
  have hDmax : 0 < Dmax := hDp.trans_le hDD
  have hκ : 2*(K:ℝ)*N^2/(σ*T) ≤ κ₀ := le_trans
    (by gcongr) hκle
  have hb := hcount S V center block z H Bmul s K F T N a b R η W
    hF hT hN hwidth.1 hH hK hUsmall
    (by linarith only [hleft,hRmax])
    (by change b+R+2*D < 2*N; linarith only [hright,hRmax,hDD])
    hwidth.2.2.2.1.le hwidth.2.2.2.2.1 hκ hwidth.2.1 hwidth.2.2.1
    hspan hmul hcenter hz hround hVS hlevel hfirst
  have hp0 : 0 ≤ k₀+ε := by linarith [hpair.inTriangle.1]
  have hl0 : 0 ≤ l₀+ε := by linarith [hpair.inTriangle.2.2.1]
  have hfirstTerm : W*D ≤ (2*η+w)*Dmax+20736*B*U^4/(lam^2*L^2) :=
    hwidth.2.2.2.2.2.1.trans (add_le_add
      (mul_le_mul_of_nonneg_left hDD (by positivity)) le_rfl)
  have hosc : (T/N^2)^(k₀+ε)*D^(l₀+ε)*W^(-(k₀+ε)) ≤
      (T/N^2)^(k₀+ε)*Dmax^(l₀+ε)*w^(-(k₀+ε)) :=
    mul_le_mul
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hDp.le hDD hl0) (by positivity))
      (hwidth.2.2.2.2.2.2 _ hp0) (by positivity) (by positivity)
  exact hb.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hfirstTerm hosc) le_rfl)
      (zero_le_one.trans hC)) (by positivity))

                                                                      
                                                                        
theorem original_model_all_shifts_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 3 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ {ι : Type*} [DecidableEq ι] (S : Finset ι) (R : Finset (ι × ι))
          (center block : ι → ℤ) (z : ι → ℝ) (H Bmul Kcut : ℕ) (s : ℤ)
          (F : ℝ → ℝ) (T N a b η w : ℝ),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 0 < H → 0 ≤ η → 0 < w → w ≤ 1/2 →
          let L := modelPhaseJetLower σ 2*T/N^3
          let U := (modelPhaseJetCoefficient σ 2+1)*T/N^3
          let lam := modelPhaseJetLower σ 3*T/N^4
          let B := (modelPhaseJetCoefficient σ 3+1)*T/N^4
          let Rmax := 36*U^2/lam
          let Dmax := (Kcut:ℝ)/L+1
          12*U ≤ 1 → L ≤ 1 →
          2*η+10368*B*U^4/(lam^2*L) ≤ 1/2 →
          N < a-Rmax → b+Rmax+2*Dmax < 2*N →
          2*(Kcut:ℝ)*N^2/(σ*T) ≤ κ₀ →
          (∀ i∈S, (H:ℤ) ≤ s+(H:ℤ)*block i-center i ∧
            s+(H:ℤ)*block i-center i ≤ 3*(H:ℤ)) →
          (∀ j : ℤ, (S.filter (fun i => block i=j)).card ≤ Bmul) →
          (∀ i∈S, (center i:ℝ)∈Icc a b) →
          (∀ i∈S, z i∈Ioo N (2*N)) →
          (∀ i∈S, |(center i:ℝ)-z i| ≤ 1/2) →
          R ⊆ S ×ˢ S → (∀ p∈R, p.swap∈R) →
          let f := fun t => T*F (t/N)
          (∀ p∈R, ∃ k : ℤ, iteratedDeriv 2 f (z p.2)/2-
            iteratedDeriv 2 f (z p.1)/2=(k:ℝ) ∧ |(k:ℝ)| ≤ Kcut) →
          (∀ p∈R, ∃ e : ℤ, |iteratedDeriv 1 f (center p.2)-
            iteratedDeriv 1 f (center p.1)-(e:ℝ)| ≤ η) →
          let Count := C*((2*η+w)*Dmax+20736*B*U^4/(lam^2*L^2)+
                (T/N^2)^(k₀+ε)*Dmax^(l₀+ε)*w^(-(k₀+ε))+N^2/T)
          let Dweight := 144*U^2/(lam*H)
          (R.card:ℝ) ≤ 4*(Bmul:ℝ)*S.card+
            6*(Bmul:ℝ)^2*Count*(3*(Kcut:ℝ)+Dweight*(harmonic Kcut:ℝ)) := by
  pm_2046 δ₀ hδ₀ Q hQ C hC hcount original_model_uniform_positive_shift_count
  pm_2062
  intro ι _ S R center block z H Bmul Kcut s F T N a b η w
    hF hT hN hH hη hw hwhalf L U lam B Rmax Dmax hUsmall hLsmall
    hsmall hleft hright hκle hspan hmul hcenter hz hround hRS hsym f hshift hnear Count D
  pm_4942 hF₀ hF hFd hQ
  obtain ⟨hreg,hthree,_,_⟩ := hdata F T N hT hN hFd
  pm_2059
  pm_7920 hB B
  pm_116 hDmax Dmax
  pm_82 hCount Count
  pm_82 hD D
  pm_2089
  pm_2098 hreg
  pm_2088
  have hex (p : ι × ι) : ∃ d : ℕ, p∈Rp →
      0 < d ∧ h (z p.2)-h (z p.1)=(d:ℝ) ∧ d ≤ Kcut := by
    by_cases hp : p∈Rp
    · obtain ⟨d,he,hd⟩ := hshift p (hpmem p hp).1
      pm_2090
      pm_5520 Kcut
    pm_2148 hh hp
  pm_8910 Kcut
  pm_2094
  have hfiber n (hn : n∈J) :
      ((Rp.filter (fun p => shift p=n)).card:ℝ) ≤
        3*(Bmul:ℝ)^2*Count*(3+D/n) := by
    pm_2283 E Rp.filter p shift n
    have hnmem := Finset.mem_Icc.mp hn
    have hEmem p (hp : p∈E) : p∈Rp ∧ shift p=n := Finset.mem_filter.mp hp
    have hb := hcount S E center block z H Bmul s (n:ℤ) F T N a b Kcut η w
      hF₀ hT hN hH (by exact_mod_cast hnmem.1) (by exact_mod_cast hnmem.2)
      hη hw hwhalf hUsmall hLsmall hsmall hleft hright hκle hspan hmul hcenter hz hround
      (fun p hp => hRS (hpmem p (hEmem p hp).1).1)
      (by
        pm_782
        simpa only [Int.cast_natCast] using he)
      (fun p hp => hnear p (hpmem p (hEmem p hp).1).1)
    change (E.card:ℝ) ≤
      (3*(Bmul:ℝ)^2*(3+144*U^2/(lam*((n:ℤ):ℝ)*H)))*Count at hb
    pm_2092
    rw [hDeq] at hb
    exact hb.trans_eq (by ring)
  have hsum : (∑ n∈J,(3+D/(n:ℝ))) ≤ 3*(Kcut:ℝ)+D*(harmonic Kcut:ℝ) := by
    have hh := sum_positive_displacement_weight_le_harmonic (η:=0) (N:=Kcut) le_rfl
      (by positivity : 0 ≤ D/3)
    pm_2097 Kcut
  have hRp : (Rp.card:ℝ) ≤ 3*(Bmul:ℝ)^2*Count*(3*(Kcut:ℝ)+D*(harmonic Kcut:ℝ)) := by
    pm_2093
    pm_2095 Count
  pm_2096 Count Kcut

                                                                           
                                                                        
                                                       
section
variable {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ) (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1)
include σ k₀ l₀ ε hσ hpair hε hp
theorem original_model_four_coordinate_count :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 3 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ {ι : Type*} [DecidableEq ι] (S : Finset ι)
          (center block label inverse : ι → ℤ) (z : ι → ℝ) (q : ι → ℕ)
          (parity : ι → Fin 2) (H Bmul M Qden : ℕ) [NeZero M] (s : ℤ)
          (F : ℝ → ℝ) (T N a₀ b₀ w : ℝ),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 0 < H → 0 < Qden → 0 < w → w ≤ 1/2 →
          (Qden:ℝ)^2 < 6*(M:ℝ)^2 →
          let L := modelPhaseJetLower σ 2*T/N^3
          let U := (modelPhaseJetCoefficient σ 2+1)*T/N^3
          let lam := modelPhaseJetLower σ 3*T/N^4
          let B := (modelPhaseJetCoefficient σ 3+1)*T/N^4
          let f := fun t => T*F (t/N)
    let mu := fun i => iteratedDeriv 3 f (center i)/6
    let ell := fun i => iteratedDeriv 1 f (center i)
    let b := fun i => (⌊(q i:ℝ)*ell i⌋:ℤ)+(parity i:ℕ)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let coeff := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let Y := fun i => (![Int.fract (-(inverse i:ℝ)*b i/q i),Int.fract (-(inverse i:ℝ)/q i),
      coeff i/Real.sqrt M,(3*coeff i*tau i/2)/Real.sqrt M] : Fin 4 → ℝ)
    let window : Fin 4 → ℝ :=
      ![1/(12*(M:ℝ)),1/(12*(M:ℝ)^2),(1/(M:ℝ)^2)/12,(1/(M:ℝ))/12]
    let R := (S ×ˢ S).filter (fun ij => ∀ j, |Y ij.1 j-Y ij.2 j| ≤ 2*window j)
    let D₀ : ℝ := (Real.sqrt M/(9*(M:ℝ))+Real.sqrt M/(12*(M:ℝ)^2))*
      Real.sqrt (U*(Qden:ℝ)^3)
    let η : ℝ := 4*D₀/(Qden:ℝ)
    let rho := (12*U*Real.sqrt (U*(Qden:ℝ)^3)/lam)*(Real.sqrt M/(6*(M:ℝ)^2))
    let Kcut := ⌈3*U*(rho+1)⌉₊
    let Rmax := 36*U^2/lam
    let Dmax := (Kcut:ℝ)/L+1
    12*U ≤ 1 → L ≤ 1 →
    2*η+10368*B*U^4/(lam^2*L) ≤ 1/2 →
    N < a₀-Rmax → b₀+Rmax+2*Dmax < 2*N →
    2*(Kcut:ℝ)*N^2/(σ*T) ≤ κ₀ →
    (∀ i∈S, (H:ℤ) ≤ s+(H:ℤ)*block i-center i ∧
      s+(H:ℤ)*block i-center i ≤ 3*(H:ℤ)) →
    (∀ j : ℤ, (S.filter (fun i => block i=j)).card ≤ Bmul) →
    (∀ i∈S, (center i:ℝ)∈Icc a₀ b₀) →
    (∀ i∈S, z i∈Ioo N (2*N)) →
    (∀ i∈S, |(center i:ℝ)-z i| ≤ 1/2) →
    (∀ i∈S, 0 < q i ∧ q i ≤ Qden ∧ Qden ≤ 2*q i) →
    (∀ i∈S, (q i:ℤ) ∣ label i*inverse i-1) →
    (∀ i∈S, iteratedDeriv 2 f (z i)/2=(label i:ℝ)/q i) →
    let Count := C*((2*η+w)*Dmax+20736*B*U^4/(lam^2*L^2)+
      (T/N^2)^(k₀+ε)*Dmax^(l₀+ε)*w^(-(k₀+ε))+N^2/T)
    let Dweight := 144*U^2/(lam*H)
    (R.card:ℝ) ≤ 4*(Bmul:ℝ)*S.card+
      6*(Bmul:ℝ)^2*Count*(3*(Kcut:ℝ)+Dweight*(harmonic Kcut:ℝ)) := by
  pm_2046 δ₀ hδ₀ Q hQ C hC hcount original_model_all_shifts_count
  pm_2062
  intro ι _ S center block label inverse z q parity H Bmul M Qden _ s F T N a₀ b₀ w
    hF hT hN hH hQden hw hwhalf hthin L U lam B f
    mu ell b tau coeff Y window R D₀ η rho Kcut Rmax Dmax hUsmall hLsmall
    hsmall hleft hright hκle hspan hmul hcenter hz hround hq hinverse hlevel Count Dweight
  pm_4942 hF₀ hF hFd hQ
  obtain ⟨hreg,hthree,hfour,_⟩ := hdata F T N hT hN hFd
  pm_2059
  pm_2063
  have hcent i (hi : i∈S) : (center i:ℝ)∈Ioo N (2*N) := by
    have hh := hcenter i hi
    constructor <;> linarith [hh.1,hh.2]
  pm_2061 hthreeUpper
  pm_4473 hQr Qden hQden
  pm_2102
  pm_82 hη η
  pm_2100
  have hshift p (hp : p∈R) : ∃ k : ℤ,
      iteratedDeriv 2 f (z p.2)/2-iteratedDeriv 2 f (z p.1)/2=(k:ℝ) ∧ |(k:ℝ)| ≤ Kcut := by
    pm_2101
    have hh := source_four_coordinate_integer_shift_bound f M (q p.1) (q p.2) Qden
      (label p.1) (label p.2) (inverse p.1) (inverse p.2) (center p.1) (center p.2)
      (hq _ hi).1 (hq _ hj).1 (hq _ hi).2.1 (hq _ hj).2.1 hthin hlam hU
      (fun t ht => (hreg t ht).of_le (by norm_num))
      (fun t ht => ⟨hL.trans_le (hthreeUpper t ht).1,(hthreeUpper t ht).2⟩)
      (fun t ht => by
        pm_1392
        linarith only [hb])
      (hz _ hi) (hz _ hj) (hcent _ hi) (hcent _ hj)
      (by simpa only [abs_sub_comm] using hround _ hi)
      (by simpa only [abs_sub_comm] using hround _ hj)
      (hinverse _ hi) (hinverse _ hj) (hlevel _ hi) (hlevel _ hj)
      (by
        pm_2103
        · change _ = |Int.fract (-(inverse p.1:ℝ)/(q p.1:ℝ))-
            Int.fract (-(inverse p.2:ℝ)/(q p.2:ℝ))|
          rfl
        · ring)
      (by
        pm_2104
        · change _ = |coeff p.1/Real.sqrt (M:ℝ)-coeff p.2/Real.sqrt (M:ℝ)|
          dsimp only [coeff,mu]
        · ring)
    pm_1255
  have hnear p (hp : p∈R) : ∃ e : ℤ, |ell p.2-ell p.1-(e:ℝ)| ≤ η := by
    pm_2101
    pm_2105 hthreeUpper hcent
    pm_2099
  exact hcount S R center block z H Bmul Kcut s F T N a₀ b₀ η w
    hF₀ hT hN hH hη hw hwhalf hUsmall hLsmall hsmall hleft hright hκle
    hspan hmul hcenter hz hround (fun _ hp => (Finset.mem_filter.mp hp).1)
    hRsym hshift hnear

                                                                        
                                                                           
                                                                 
theorem exists_model_refined_frozen_source :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Qphase : ℕ, 3 ≤ Qphase ∧ ∃ C > (0:ℝ), ∃ Cp : ℝ, 1 ≤ Cp ∧
      ∀ (ι : Type*) [DecidableEq ι] (S : Finset ι)
      (G : ℝ → ℝ) (T P : ℝ) (r : ι → ℚ) (z : ι → ℝ) (m k : ι → ℤ)
      (H : ι → ℕ) (N Q Bmul : ℕ) (s : ℤ) (A B w : ℝ),
      IsApproximateModelPhaseFunction G σ Qphase δ →
      0 < T → 0 < P → 0 < N → 0 < Q → 0 < w → w ≤ 1/2 →
      let f := fun t => T*G (t/P)
      let L := modelPhaseJetLower σ 2*T/P^3
      let U := (modelPhaseJetCoefficient σ 2+1)*T/P^3
      let lam := modelPhaseJetLower σ 3*T/P^4
      let F := (modelPhaseJetCoefficient σ 3+1)*T/P^4
      12*U ≤ 1 → L ≤ 1 →
      F*(6*(N:ℝ)+1)^4 ≤ 1 → (3*U/2)*(6*(N:ℝ)+1)^2 ≤ 1 →
      (∀ i∈S, z i∈Ioo A B) →
      (∀ i∈S, Icc ((m i:ℝ)-(6*(N:ℝ)+1)) ((m i:ℝ)+(6*(N:ℝ)+1)) ⊆ Icc A B) →
      (∀ i∈S, |z i-m i| ≤ 1/2) →
      (∀ i∈S, (N:ℤ) ≤ s+(N:ℤ)*k i-m i ∧ s+(N:ℤ)*k i-m i ≤ 3*(N:ℤ)) →
      (∀ n : ℤ, (S.filter (fun i => k i=n)).card ≤ Bmul) →
      (∀ i∈S, H i ≤ N) →
      (∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧ (r i).den ≤ N) →
      (∀ i∈S, iteratedDeriv 2 f (z i)/2=(r i:ℝ)) →
      12 ≤ L*(Q:ℝ)*(N:ℝ)^2 → 384 ≤ L^2*(Q:ℝ)^3*(N:ℝ)^3 →
      let Z := (S.card:ℝ)
      let M : ℕ := ⌈63*U*(Q:ℝ)*(N:ℝ)^2⌉₊+1
      let V := 756*U/L
      let Wloss := 1+32/(L*(Q:ℝ)^2*N)
      let d := L*(Q:ℝ)*N/12
      let D₀ := (Real.sqrt M/(9*(M:ℝ))+Real.sqrt M/(12*(M:ℝ)^2))*Real.sqrt (U*(Q:ℝ)^3)
      let η : ℝ := 4*D₀/(Q:ℝ)
      let rho := (12*U*Real.sqrt (U*(Q:ℝ)^3)/lam)*(Real.sqrt M/(6*(M:ℝ)^2))
      let K := ⌈3*U*(rho+1)⌉₊
      let Rmax := 36*U^2/lam
      let Dmax := (K:ℝ)/L+1
      let Dweight := 144*U^2/(lam*N)
      let Count := Cp*((2*η+w)*Dmax+20736*F*U^4/(lam^2*L^2)+
        (T/P^2)^(k₀+ε)*Dmax^(l₀+ε)*w^(-(k₀+ε))+P^2/T)
      let Pair := 4*(Bmul:ℝ)*Z+6*(Bmul:ℝ)^2*Count*(3*(K:ℝ)+Dweight*(harmonic K:ℝ))
      let Loss := (5*Wloss)^11*Wloss^2*(6*(3+8*Real.pi*V)*(1+Real.log M))^12*
        (2/d)^6*(M:ℝ)^((12:ℝ)+ε)
      let Err := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)+
        Real.sqrt (12/(L*(N:ℝ)*Q))
      (Q:ℝ)^2 < 6*(M:ℝ)^2 →
      2*η+10368*F*U^4/(lam^2*L) ≤ 1/2 →
      P < A-Rmax → B+Rmax+2*Dmax < 2*P →
      2*(K:ℝ)*P^2/(σ*T) ≤ κ₀ →
      (∑ i∈S, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖)^12 ≤
        C*(Loss*(2*Z)^10*Pair+(Z*Err)^12) := by
  pm_2046 δ₀ hδ₀ Qphase hQphase Cp hCp hcount original_model_four_coordinate_count
  obtain ⟨δd,hδd,hdata⟩ := model_displacement_derivative_data hσ
  obtain ⟨C,hC,hsource⟩ := exists_bourgain_C4_frozen_source_second_spacing_reduction hε
  refine ⟨min δ₀ δd,κ₀,lt_min hδ₀ hδd,hκ₀,Qphase,hQphase,4*C,by positivity,Cp,hCp,?_⟩
  intro ι instι S G T P r z m k H N Q Bmul s A B w
    hG hT hP hN hQ hw hwhalf f L U lam F hUsmall hLsmall hfourSmall hquadSmall
    hz hbuffer hround hspan hmul hH hq hlevel hdual hfrozen
    Z M V Wloss d D₀ η rho K Rmax Dmax Dweight Count Pair Loss Err hthin
    hliftSmall hleft hright hκle
  pm_4942 hG₀ hG hGd hQphase
  obtain ⟨hreg,hthreeModel,hfourModel,_⟩ := hdata G T P hT hP hGd
  pm_2059
  have hF : 0 < F := by dsimp only [F]; positivity [modelPhaseJetCoefficient_pos hσ 3]
  pm_2063
  have hdomain : Icc A B ⊆ Ioo P (2*P) := by
    pm_8054
  have hf x (hx : x∈Icc A B) : ContDiffAt ℝ 5 f x := hreg x (hdomain hx)
  pm_4970 x hx
  have hfour x (hx : x∈Icc A B) :
      -F ≤ iteratedDeriv 4 f x ∧ iteratedDeriv 4 f x ≤ -lam := hfourModel x (hdomain hx)
  pm_2108
  pm_2140
  pm_2107
  pm_2166
  · obtain ⟨i₀,hi₀⟩ := hS
    pm_2106
    have hc₀ := hcount S₂
      (fun p => m p.1) (fun p => k p.1) (fun p => (r p.1).num) (fun p => rinv p.1)
      (fun p => z p.1) (fun p => (r p.1).den) Prod.snd N (2*Bmul) M Q s G T P A B w
      hG₀ hT hP hN hQ hw hwhalf hthin hUsmall hLsmall hliftSmall hleft hright hκle
      (fun p hp => hspan _ (Finset.mem_product.mp hp).1) hmul₂
      (fun p hp => ⟨(hm _ (Finset.mem_product.mp hp).1).1.le,(hm _ (Finset.mem_product.mp hp).1).2.le⟩)
      (fun p hp => hdomain ⟨(hz _ (Finset.mem_product.mp hp).1).1.le,(hz _ (Finset.mem_product.mp hp).1).2.le⟩)
      (fun p hp => by simpa only [abs_sub_comm] using hround _ (Finset.mem_product.mp hp).1)
      (fun p hp => ⟨(r p.1).pos,(hq _ (Finset.mem_product.mp hp).1).1,
        (hq _ (Finset.mem_product.mp hp).1).2.1⟩)
      (fun p hp => hinv _ (Finset.mem_product.mp hp).1)
      (fun p hp => by simpa only [Rat.cast_def] using hlevel _ (Finset.mem_product.mp hp).1)
    pb_36
  pb_562
end


                                                                       
                                                                                 
theorem refined_count_physical_majorant
    {l a b u n p q : ℝ} (hl : 0<l) (ha : 0<a) (hb : 0≤b)
    (hu : 0<u) (hn : 0≤n) (hq : 0≤q) :
    ∃ C > (0:ℝ), ∀ P U K η w : ℝ,
      0<P → 0<U → U≤1 → 1≤P*U*Real.sqrt U →
      0≤K → K≤n*(P*U*Real.sqrt U) →
      0≤η → η≤4*Real.sqrt U → 0<w →
      let D := K/(l*U)+1
      (2*η+w)*D+20736*(b*U/P)*U^4/((a*U/P)^2*(l*U)^2)+
        (P*U/u)^p*D^q*w^(-p)+u/(P*U) ≤
      C*(P*U+w*(P*Real.sqrt U)+(P*U)^p*(P*Real.sqrt U)^q*w^(-p)+1/(P*U)) := by
  let d := n/l+1
  let c := 20736*b/(a^2*l^2)
  let e := (1/u)^p*d^q
  let C := 8*d+c+d+e+u
  pm_307 hd d
  pm_2164 hc c
  pm_2164 he e
  pm_307 hC C
  refine ⟨C,hC,?_⟩
  intro P U K η w hP hU hU1 hscale hK hKhi hη hηhi hw D
  have hs : 0<Real.sqrt U := Real.sqrt_pos.mpr hU
  have hPU : 0<P*U := mul_pos hP hU
  pm_2064 hscale.trans
  pm_2179
  have hDu : D≤d*(P*Real.sqrt U) := by
    calc
      _ ≤ (n*(P*U*Real.sqrt U))/(l*U)+P*Real.sqrt U :=
        add_le_add (div_le_div_of_nonneg_right hKhi (by positivity)) hPS
      _ = _ := by dsimp only [d]; field_simp
  have hmain : (2*η+w)*D≤(8*d)*(P*U)+d*(w*(P*Real.sqrt U)) := by
    calc
      _ ≤ (8*Real.sqrt U+w)*(d*(P*Real.sqrt U)) :=
        mul_le_mul (by linarith only [hηhi]) hDu hD.le (by positivity)
      _ = (8*d*P)*(Real.sqrt U)^2+d*(w*(P*Real.sqrt U)) := by ring
      _ = _ := by rw [Real.sq_sqrt hU.le]; ring
  have hcorr : 20736*(b*U/P)*U^4/((a*U/P)^2*(l*U)^2)=c*(P*U) := by
    dsimp only [c]
    field_simp
  have hosc : (P*U/u)^p*D^q*w^(-p) ≤ e*((P*U)^p*(P*Real.sqrt U)^q*w^(-p)) := by
    calc
      _ ≤ (P*U/u)^p*(d*(P*Real.sqrt U))^q*w^(-p) := by gcongr
      _ = _ := by
        rw [show P*U/u=(P*U)*(1/u) by ring,
          Real.mul_rpow hPU.le (by positivity),
          Real.mul_rpow hd.le (by positivity)]
        dsimp only [e]
        ring
  have hC₁ : 8*d+c≤C := by dsimp only [C]; linarith
  pm_1331 hC₂ d
  pm_1331 hC₃ e
  pm_1331 hC₄ u
  calc
    _ ≤ ((8*d)*(P*U)+d*(w*(P*Real.sqrt U)))+c*(P*U)+
        e*((P*U)^p*(P*Real.sqrt U)^q*w^(-p))+u/(P*U) := by
      rw [hcorr]
      exact add_le_add (add_le_add (add_le_add hmain le_rfl) hosc) le_rfl
    _ = (8*d+c)*(P*U)+d*(w*(P*Real.sqrt U))+
        e*((P*U)^p*(P*Real.sqrt U)^q*w^(-p))+u*(1/(P*U)) := by ring
    _ ≤ C*(P*U)+C*(w*(P*Real.sqrt U))+
        C*((P*U)^p*(P*Real.sqrt U)^q*w^(-p))+C*(1/(P*U)) := by gcongr
    _ = _ := by ring

                                                                           
                                                                              
                                                                      
theorem exists_model_refined_source_bands
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Qphase : ℕ, 3 ≤ Qphase ∧ ∃ Cd ≥ (1:ℝ), ∃ Cf > (0:ℝ),
      ∃ Cp : ℝ, 1 ≤ Cp ∧ ∀ (ι : Type*) [DecidableEq ι]
      (S : Finset ι) (F : ℝ → ℝ) (T P : ℝ) (k : ι → ℤ) (H : ι → ℕ)
      (N : ℕ) (s : ℤ) (A B w : ℝ),
      IsApproximateModelPhaseFunction F σ Qphase δ →
      0<T → 0<P → 0<N → 0<w → w≤1/2 → P<A → B<2*P →
      let f := fun t => T*F (t/P)
      let L := modelPhaseJetLower σ 2*T/P^3
      let U := (modelPhaseJetCoefficient σ 2+1)*T/P^3
      let lam := modelPhaseJetLower σ 3*T/P^4
      let F4 := (modelPhaseJetCoefficient σ 3+1)*T/P^4
      let X := (modelPhaseJetCoefficient σ 1+1)*T/P^2/2
      12*U≤1 → L≤1 →
      F4*(6*(N:ℝ)+1)^4≤1 → (3*U/2)*(6*(N:ℝ)+1)^2≤1 →
      (∀ j : ℤ, (S.filter (fun i => k i=j)).card ≤ 1) →
      (∀ i∈S, H i ≤ N) →
      let base := fun i => (s:ℝ)-2*(N:ℝ)+(N:ℝ)*(k i:ℝ)
      (∀ i∈S, Icc (base i-(7*(N:ℝ)+2)) (base i+(7*(N:ℝ)+2)) ⊆ Icc A B) →
      ∃ r : ι → ℚ,
        (∀ Q₀ : ℕ, 2 ≤ Q₀ →
          let D₀ := 8/(L*(N:ℝ)*(Q₀:ℝ))
          ((S.filter (fun i => Q₀ ≤ (r i).den)).card:ℝ) ≤
            4*(X+1)*D₀^2+D₀*(2+Real.log (D₀+1))) ∧
        (∀ j : ℕ,
          let Q : ℕ := 2^(j+1)
          let G := (S.filter (fun i => (r i).den ≤ N)).filter (fun i => Nat.log 2 (r i).den=j)
          let Z := (G.card:ℝ)
          let Zd := 4*(Q:ℝ)*(2*X*Q+1)
          let D := 16/(L*(N:ℝ)*(Q:ℝ))
          let Err := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)+
            Real.sqrt (12/(L*(N:ℝ)*Q))
          Z ≤ Zd ∧
          (1 ≤ j → Z ≤ 4*(X+1)*D^2+D*(2+Real.log (D+1))) ∧
          (∑ i∈G, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖) ≤
            Cd*Zd*(3*(N:ℝ)*Real.sqrt (3*U*(Q:ℝ)*N)+Err) ∧
          (12 ≤ L*(Q:ℝ)*(N:ℝ)^2 → 384 ≤ L^2*(Q:ℝ)^3*(N:ℝ)^3 →
            let M : ℕ := ⌈63*U*(Q:ℝ)*(N:ℝ)^2⌉₊+1
            let V := 756*U/L
            let W := 1+32/(L*(Q:ℝ)^2*N)
            let d := L*(Q:ℝ)*N/12
            let Loss := (5*W)^11*W^2*(6*(3+8*Real.pi*V)*(1+Real.log M))^12*
              (2/d)^6*(M:ℝ)^((12:ℝ)+ε)
            let D₀ := (Real.sqrt M/(9*(M:ℝ))+Real.sqrt M/(12*(M:ℝ)^2))*
              Real.sqrt (U*(Q:ℝ)^3)
            let η := 4*D₀/(Q:ℝ)
            let rho := (12*U*Real.sqrt (U*(Q:ℝ)^3)/lam)*(Real.sqrt M/(6*(M:ℝ)^2))
            let K := ⌈3*U*(rho+1)⌉₊
            let Rmax := 36*U^2/lam
            let Dmax := (K:ℝ)/L+1
            let Dweight := 144*U^2/(lam*N)
            let Count := Cp*((2*η+w)*Dmax+20736*F4*U^4/(lam^2*L^2)+
              (T/P^2)^(k₀+ε)*Dmax^(l₀+ε)*w^(-(k₀+ε))+P^2/T)
            let Pair := 4*Z+6*Count*(3*(K:ℝ)+Dweight*(harmonic K:ℝ))
            (Q:ℝ)^2 < 6*(M:ℝ)^2 →
            2*η+10368*F4*U^4/(lam^2*L) ≤ 1/2 →
            P < A-Rmax → B+Rmax+2*Dmax < 2*P →
            2*(K:ℝ)*P^2/(σ*T) ≤ κ₀ →
            (∑ i∈G, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖)^12 ≤
              Cf*(Loss*(2*Z)^10*Pair+(Z*Err)^12))) := by
  classical
  obtain ⟨δ₀,κ₀,hδ₀,hκ₀,Qphase,hQphase,Cf,hCf,Cp,hCp,hfrozenSource⟩ :=
    exists_model_refined_frozen_source hσ hpair hε hp
  obtain ⟨δd,hδd,hdata⟩ := model_displacement_derivative_data hσ
  obtain ⟨Cd,hCd,hdirect⟩ := exists_bourgain_C4_low_denominator_source
  refine ⟨min δ₀ δd,κ₀,lt_min hδ₀ hδd,hκ₀,Qphase,hQphase,Cd,hCd,Cf,hCf,Cp,hCp,?_⟩
  intro ι _ S F T P k H N s A B w hF hT hP hN hw hwhalf hA hB
    f L U lam F4 X hUsmall hLsmall hfourSmall hquadSmall hmul hH base hbuffer
  pm_4942 hF₀ hF hFd hQphase
  pm_562 hreg hthreeModel hfourModel hcurvModel hdata F T P hT hP hFd
  pm_2059
  pm_7920 hF4 F4
  have hX : 0 ≤ X := by dsimp only [X]; positivity [modelPhaseJetCoefficient_pos hσ 1]
  have hdomain : Icc A B ⊆ Ioo P (2*P) := by
    intro t ht
    exact ⟨hA.trans_le ht.1,ht.2.trans_lt hB⟩
  have hf₄ t (ht : t∈Icc A B) : ContDiffAt ℝ 4 f t :=
    (hreg t (hdomain ht)).of_le (by norm_num)
  pm_4970 t ht
  have hfourAbs t (ht : t∈Icc A B) : |iteratedDeriv 4 f t| ≤ F4 := by
    have hh := hfourModel t (hdomain ht)
    pm_6025
  have hcurv t (ht : t∈Icc A B) : |iteratedDeriv 2 f t/2| ≤ X :=
    hcurvModel t (hdomain ht)
  pm_278 hNr N hN
  pm_2115
  obtain ⟨r,z,hr,htail₀⟩ := exists_bourgain_C3_minimal_curvature_arc_count S f k N 1
    ((s:ℝ)-2*(N:ℝ)) hN hL hX
    (fun t ht => (hf₄ t ht).of_le (by norm_num)) (fun t ht => (hthree t ht).1) hmul
    (by
      pm_2114
      constructor <;> linarith only [hx.1,hx.2,hNr])
    (fun i hi => hcurv _ (ht i hi))
  have hgeo i (hi : i∈S) : z i∈Ioo A B ∧ |z i-(round (z i):ℝ)| ≤ 1/2 ∧
      ((N:ℤ) ≤ s+(N:ℤ)*k i-round (z i) ∧
        s+(N:ℤ)*k i-round (z i) ≤ 3*(N:ℤ)) ∧
      Icc ((round (z i):ℝ)-(6*(N:ℝ)+1)) ((round (z i):ℝ)+(6*(N:ℝ)+1)) ⊆ Icc A B := by
    have hz := (hr i hi).1
    change z i∈Ioo (base i-(N:ℝ)/4) (base i+(N:ℝ)/4) at hz
    have hround : |z i-(round (z i):ℝ)| ≤ 1/2 := abs_sub_round (z i)
    have hround' := abs_le.mp hround
    have hlo := (hbuffer i hi (left_mem_Icc.mpr (by linarith only [hNr]))).1
    have hhi := (hbuffer i hi (right_mem_Icc.mpr (by linarith only [hNr]))).2
    have hstart : ((s+(N:ℤ)*k i:ℤ):ℝ)=base i+2*(N:ℝ) := by
      dsimp only [base]; push_cast; ring
    pm_2152
    · have hlow : (N:ℝ) ≤ ((s+(N:ℤ)*k i:ℤ):ℝ)-(round (z i):ℝ) := by
        pm_2151
      have hhigh : ((s+(N:ℤ)*k i:ℤ):ℝ)-(round (z i):ℝ) ≤ 3*(N:ℝ) := by
        pm_2151
      constructor
      · exact_mod_cast hlow
      · exact_mod_cast hhigh
    · intro x hx
      apply hbuffer i hi
      pm_6026
  have hlevel i (hi : i∈S) : iteratedDeriv 2 f (z i)/2=(r i:ℝ) := (hr i hi).2.1
  have htail (Q₀ : ℕ) (hQ₀ : 2≤Q₀) :
      let D₀ := 8/(L*(N:ℝ)*(Q₀:ℝ))
      ((S.filter (fun i => Q₀ ≤ (r i).den)).card:ℝ) ≤
        4*(X+1)*D₀^2+D₀*(2+Real.log (D₀+1)) := by
    simpa only [Nat.cast_one,one_mul] using htail₀ Q₀ hQ₀
  pm_2119
  pm_2173
  have hdir := hdirect ι G f r z (fun i => round (z i)) k H N Q 1 s A B L F4 U X
    hN hQ hL hF4 hU hX hfourSmall hquadSmall hf₄ hthree hfourAbs
    (fun i hi => (hgeo i (hGS hi)).1)
    (fun i hi => (hgeo i (hGS hi)).2.2.2)
    (fun i hi => (hgeo i (hGS hi)).2.1)
    (fun i hi => (hgeo i (hGS hi)).2.2.1)
    hmulG (fun i hi => hH i (hGS hi)) hqdata
    (fun i hi => hlevel i (hGS hi))
    (fun i hi => hcurv _ ⟨(hgeo i (hGS hi)).1.1.le,(hgeo i (hGS hi)).1.2.le⟩)
  pm_2118
  · intro hdual hfrozen M V Wloss d Loss D₀ η rho K Rmax Dmax Dweight Count Pair
      hthin hliftSmall hleft hright hκle
    have hs := hfrozenSource ι G F T P r z (fun i => round (z i)) k H N Q 1 s A B w
      hF₀ hT hP hN hQ hw hwhalf hUsmall hLsmall hfourSmall hquadSmall
      (fun i hi => (hgeo i (hGS hi)).1)
      (fun i hi => (hgeo i (hGS hi)).2.2.2)
      (fun i hi => (hgeo i (hGS hi)).2.1)
      (fun i hi => (hgeo i (hGS hi)).2.2.1)
      hmulG (fun i hi => hH i (hGS hi)) hqdata
      (fun i hi => hlevel i (hGS hi)) hdual hfrozen hthin hliftSmall hleft hright hκle
    simpa only [Nat.cast_one,mul_one,one_pow] using hs

                                                                    
                                                                
theorem refined_elementary_twelfth
    {P U Z C Log ε r : ℝ} (hP : 1≤P) (hU : 0<U) (hU1 : U≤1)
    (hZ : 0≤Z) (hC : 0≤C) (hLog : 1≤Log) (hε : 0≤ε)
    (hr : 1/4≤r) (hsmall : P*U^2≤1)
    (hbound : Z≤C*P*U^r*Log^2) :
    Z^12 ≤ C^12*P^ε*Log^24*(P^11*U) := by
  have hPp : 0<P := zero_lt_one.trans_le hP
  have hUquarter : U^r≤U^((1:ℝ)/4) :=
    Real.rpow_le_rpow_of_exponent_ge hU hU1 hr
  have hpower : (U^((1:ℝ)/4))^12=U^3 := by
    rw [←Real.rpow_mul_natCast hU.le]
    norm_num
  pm_2065 hbase
  pm_242 hPe P ε hP hε
  calc
    _ ≤ (C*P*U^((1:ℝ)/4)*Log^2)^12 := by
      apply pow_le_pow_left₀ hZ
      exact hbound.trans (by gcongr)
    _ = C^12*Log^24*(P^12*U^3) := by
      rw [mul_pow,mul_pow,mul_pow,hpower]
      ring
    _ ≤ C^12*Log^24*(P^11*U) := mul_le_mul_of_nonneg_left hbase (by positivity)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hPe (show 0≤C^12*Log^24*(P^11*U) by positivity)
      nlinarith only [hh]


theorem refined_spacing_physical_product
    {P U w p q : ℝ} (hP : 0<P) (hU : 0<U) :
    P^10*Real.sqrt U*(P*U*Real.sqrt U)*
      (P*U+w*(P*Real.sqrt U)+(P*U)^p*(P*Real.sqrt U)^q*w^(-p)+1/(P*U)) =
    P^12*U^3+w*P^12*U^((5:ℝ)/2)+
      P^(11+p+q)*U^(2+p+q/2)*w^(-p)+P^10*U := by
  have hbase : P^10*Real.sqrt U*(P*U*Real.sqrt U)=P^11*U^2 := by
    calc
      _ = P^11*U*(Real.sqrt U)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hU.le]; ring
  have hroot : U^2*Real.sqrt U=U^((5:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_natCast U 2,←Real.rpow_add hU]
    norm_num
  have hpowers : P^(11+p+q)=P^11*P^p*P^q := by
    rw [Real.rpow_add hP,Real.rpow_add hP]
    norm_num
  have hupowers : U^(2+p+q/2)=U^2*U^p*U^(q/2) := by
    rw [Real.rpow_add hU,Real.rpow_add hU]
    norm_num
  have hdensity : P^11*U^2*((P*U)^p*(P*Real.sqrt U)^q)=
      P^(11+p+q)*U^(2+p+q/2) := by
    rw [Real.mul_rpow hP.le hU.le,Real.mul_rpow hP.le (Real.sqrt_nonneg U),
      Real.sqrt_eq_rpow,←Real.rpow_mul hU.le,hpowers,hupowers]
    rw [show (1/2:ℝ)*q=q/2 by ring]
    ring
  have hinv : P^11*U^2*(1/(P*U))=P^10*U := by
    field_simp
  rw [hbase]
  calc
    _ = P^12*U^3+w*P^12*(U^2*Real.sqrt U)+
        (P^11*U^2*((P*U)^p*(P*Real.sqrt U)^q))*w^(-p)+P^11*U^2*(1/(P*U)) := by ring
    _ = _ := by rw [hroot,hdensity,hinv]

theorem refined_spacing_physical_product_bound
    {P U w p q : ℝ} (hP : 1≤P) (hU : 0<U) (hw : 0≤w) (hsmall : P*U^2≤1) :
    P^10*Real.sqrt U*(P*U*Real.sqrt U)*
      (P*U+w*(P*Real.sqrt U)+(P*U)^p*(P*Real.sqrt U)^q*w^(-p)+1/(P*U)) ≤
    2*(P^11*U+w*P^12*U^((5:ℝ)/2)+P^(11+p+q)*U^(2+p+q/2)*w^(-p)) := by
  have hPp : 0<P := zero_lt_one.trans_le hP
  rw [refined_spacing_physical_product hPp hU]
  pm_2065 hfirst
  have hlast : P^10*U≤P^11*U := by
    have hh := mul_le_mul_of_nonneg_left hP (show 0≤P^10*U by positivity)
    nlinarith only [hh]
  pm_2066 hdensity
  linarith only [hfirst,hlast,hmid,hdensity]
                                                                     
                                                                             
theorem exists_refined_uniform_frozen_rhs
    {l ε Cc p q : ℝ} (hl : 0<l) (hε : 0<ε) (hCc : 1≤Cc) :
    ∃ C > (0:ℝ), ∀ (P U Z w : ℝ) (Q : ℕ),
      0<P → 0<U → U≤1/3600 → 1≤P*U → P*U^2≤1 → 0≤Z → 0<w →
      0<Q → (Q:ℝ)≤P →
      Z≤Cc*P*U*(Q:ℝ)^2 → Z≤Cc*(P/(Q:ℝ)^2)*(1+Real.log P) →
      let N := ⌊1/(10*Real.sqrt U)⌋₊
      let L := l*U
      let M : ℕ := ⌈63*U*(Q:ℝ)*(N:ℝ)^2⌉₊+1
      let V := 756*U/L
      let W := 1+32/(L*(Q:ℝ)^2*N)
      let d := L*(Q:ℝ)*N/12
      let Loss := (5*W)^11*W^2*(6*(3+8*Real.pi*V)*(1+Real.log M))^12*
        (2/d)^6*(M:ℝ)^((12:ℝ)+ε)
      let Err := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)+
        Real.sqrt (12/(L*(N:ℝ)*Q))
      let E := P*U+w*(P*Real.sqrt U)+(P*U)^p*(P*Real.sqrt U)^q*w^(-p)+1/(P*U)
      let R := Z+(P*U*Real.sqrt U)*E*(1+Real.log P)
      Loss*(2*Z)^10*R+(Z*Err)^12 ≤
        C*P^ε*(1+Real.log P)^24*
          (P^11*U+w*P^12*U^((5:ℝ)/2)+P^(11+p+q)*U^(2+p+q/2)*w^(-p)) := by
  pm_2125
  have hCcp : 0<Cc := zero_lt_one.trans_le hCc
  pm_2121
  intro P U Z w Q hP hU hUsmall hPU hsmall hZ hw hQ hQP hZlo hZhi
    N L M V W d Loss Err E R
  pm_2067
  have hP1 : 1≤P := hPU.trans (by nlinarith only [mul_le_mul_of_nonneg_left hU1 hP.le])
  have hQr : (0:ℝ)<Q := Nat.cast_pos.mpr hQ
  pm_277 hQ1 Q hQ
  pm_6924
  let Cost := P^11*U+w*P^12*U^((5:ℝ)/2)+P^(11+p+q)*U^(2+p+q/2)*w^(-p)
  have hlogP := Real.log_nonneg hP1
  have hJ1 : 1≤J := by dsimp only [J]; linarith only [hlogP]
  have hJ : 0<J := zero_lt_one.trans_le hJ1
  pm_307 hB B
  pm_2164 hCost Cost
  have hFirst : P^11*U≤Cost := by
    pm_2066 hlast
    pm_737 Cost hmid hlast
  pm_2124
  pm_2123
  have hZprod : P^10*Real.sqrt U*Z≤Cc*J*(P^11*U) := by
    calc
      _ ≤ P^10*Real.sqrt U*(Cc*P*J*Real.sqrt U) :=
        mul_le_mul_of_nonneg_left hZgeo (by positivity)
      _ = Cc*J*P^11*(Real.sqrt U)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hU.le]; ring
  have hprod := refined_spacing_physical_product_bound (p:=p) (q:=q) hP1 hU hw.le hsmall
  change P^10*Real.sqrt U*(P*U*Real.sqrt U)*E≤2*Cost at hprod
  have hRprod : P^10*Real.sqrt U*R≤(Cc+2)*J*Cost := by
    calc
      _ = P^10*Real.sqrt U*Z+(P^10*Real.sqrt U*(P*U*Real.sqrt U)*E)*J := by
        dsimp only [R,J]
        ring
      _ ≤ Cc*J*(P^11*U)+(2*Cost)*J :=
        add_le_add hZprod (mul_le_mul_of_nonneg_right hprod hJ.le)
      _ ≤ Cc*J*Cost+(2*Cost)*J := by gcongr
      _ = _ := by ring
  pm_658 hR R E
  have hmain : Loss*(2*Z)^10*R≤Cl*Cc^10*(Cc+2)*P^ε*J^24*Cost := by
    calc
      _ ≤ (Cl*Cc^10*P^10*Real.sqrt U*P^ε*J^22)*R :=
        mul_le_mul_of_nonneg_right hLoss hR
      _ = (Cl*Cc^10*P^ε*J^22)*(P^10*Real.sqrt U*R) := by ring
      _ ≤ (Cl*Cc^10*P^ε*J^22)*((Cc+2)*J*Cost) :=
        mul_le_mul_of_nonneg_left hRprod (by positivity)
      _ = Cl*Cc^10*(Cc+2)*P^ε*J^23*Cost := by ring
      _ ≤ _ := by gcongr; norm_num
  pm_2122
  have herror₀ := refined_elementary_twelfth hP1 hU hU1 (mul_nonneg hZ hErr0)
    (mul_nonneg hCcp.le hCe.le) hJ1 hε.le (le_refl ((1:ℝ)/4)) hsmall hZE
  have herror' : (Z*Err)^12≤(Cc*Ce)^12*P^ε*J^24*Cost :=
    herror₀.trans (mul_le_mul_of_nonneg_left hFirst (by positivity))
  calc
    _ ≤ Cl*Cc^10*(Cc+2)*P^ε*J^24*Cost+(Cc*Ce)^12*P^ε*J^24*Cost :=
      add_le_add hmain herror'
    _ = _ := by dsimp only [C,Cost]; ring


                                                                             
theorem exists_refined_physical_pair_bound
    {l a b u p q Cp : ℝ} (hl : 0<l) (ha : 0<a) (hb : 0≤b)
    (hu : 0<u) (hq : 0≤q) (hCp : 1≤Cp) :
    ∃ Ca ≥ (1:ℝ), ∀ P U M Q Z w : ℝ,
      0<P → 0<U → U≤1/3600 → 1≤P*U*Real.sqrt U →
      1≤M → 0<Q → Q≤4*M → 0≤Z → 0<w →
      let N := ⌊1/(10*Real.sqrt U)⌋₊
      let L := l*U
      let lam := a*U/P
      let D₀ := (Real.sqrt M/(9*M)+Real.sqrt M/(12*M^2))*Real.sqrt (U*Q^3)
      let η := 4*D₀/Q
      let rho := (12*U*Real.sqrt (U*Q^3)/lam)*(Real.sqrt M/(6*M^2))
      let K := ⌈3*U*(rho+1)⌉₊
      let Dmax := (K:ℝ)/L+1
      let Dweight := 144*U^2/(lam*N)
      let E := P*U+w*(P*Real.sqrt U)+(P*U)^p*(P*Real.sqrt U)^q*w^(-p)+1/(P*U)
      let Count := Cp*((2*η+w)*Dmax+20736*(b*U/P)*U^4/(lam^2*L^2)+
        (P*U/u)^p*Dmax^q*w^(-p)+u/(P*U))
      4*Z+6*Count*(3*(K:ℝ)+Dweight*(harmonic K:ℝ)) ≤
        Ca*(Z+(P*U*Real.sqrt U)*E*(1+Real.log P)) := by
  let n := 2+48/a
  pm_700
  obtain ⟨Ce,hCe,hcount⟩ := refined_count_physical_majorant
    (p:=p) hl ha hb hu (le_trans zero_le_one hn) hq
  let Ch := 3*n+(1728/a)*(1+Real.log n)
  have hCh : 0<Ch := by
    have hlogn := Real.log_nonneg hn
    dsimp only [Ch]
    positivity
  let Ca := 4+6*Cp*Ce*Ch
  have hCa : 1≤Ca := by
    have hh : 0≤6*Cp*Ce*Ch := by positivity
    dsimp only [Ca]
    linarith only [hh]
  refine ⟨Ca,hCa,?_⟩
  intro P U M Q Z w hP hU hUsmall hK hM hQ hQM hZ hw
    N L lam D₀ η rho K Dmax Dweight E Count
  pm_2067
  have hscale := displacement_block_physical_scale hP hU hUsmall hK
  pm_528 hcut displacement_physical_cutoff ha hP hU hUsmall hK hM hQ hQM
  pm_2068
  pm_658 hη η D₀
  have hN : (0:ℝ)<N := Nat.cast_pos.mpr (displacement_block_scale hU hUsmall).1
  pm_307 hlam lam
  pm_2164 hDweight Dweight
  have hcount' : Count≤(Cp*Ce)*E := by
    have hh := hcount P U K η w hP hU hU1 hK (Nat.cast_nonneg K) hcut.2.1 hη hcut.2.2.1 hw
    dsimp only [Count]
    calc
      _ ≤ Cp*(Ce*E) := mul_le_mul_of_nonneg_left hh (le_trans zero_le_one hCp)
      _ = _ := by ring
  have hweight := displacement_harmonic_weight hn hscale.2.1 hU hU1
    hcut.1 hcut.2.1 hDweight hcut.2.2.2
  change _≤Ch*(P*U*Real.sqrt U)*(1+Real.log P) at hweight
  have hharm : 0≤(harmonic K:ℝ) := by
    pm_1256
  have hweight0 : 0≤3*(K:ℝ)+Dweight*(harmonic K:ℝ) := by positivity
  have hlogP := Real.log_nonneg hscale.2.1
  pm_2164 hE E
  have hweighted : Count*(3*(K:ℝ)+Dweight*(harmonic K:ℝ))≤
      (Cp*Ce*Ch)*((P*U*Real.sqrt U)*E*(1+Real.log P)) := by
    calc
      _ ≤ ((Cp*Ce)*E)*(Ch*(P*U*Real.sqrt U)*(1+Real.log P)) :=
        mul_le_mul hcount' hweight hweight0 (by positivity)
      _ = _ := by ring
  have hc0 : 0≤Cp*Ce*Ch := by positivity
  have ht0 : 0≤(P*U*Real.sqrt U)*E*(1+Real.log P) := by positivity
  dsimp only [Ca]
  nlinarith only [hweighted,mul_nonneg hc0 hZ,ht0]

                                                                          
theorem refined_physical_lifting_domain
    {σ l a b u n P T U η K κ₀ A B : ℝ}
    (hσ : 0<σ) (hl : 0<l) (ha : 0<a) (hn : 0≤n)
    (hP : 0<P) (hT : 0<T) (hU : 0<U) (hU1 : U≤1)
    (hUeq : U=u*T/P^3) (hK : 1≤P*U*Real.sqrt U)
    (hKhi : K≤n*(P*U*Real.sqrt U)) (hηhi : η≤4*Real.sqrt U)
    (hlift : 8*Real.sqrt U+(10368*b/(a^2*l))*(P*U^2)≤1/2)
    (hκ : (2*n*u/σ)*Real.sqrt U≤κ₀)
    (hA : P+(36/a+2*(n/l+1)+1)*(P*Real.sqrt U)<A)
    (hB : B+(36/a+2*(n/l+1)+1)*(P*Real.sqrt U)<2*P) :
    let L := l*U
    let lam := a*U/P
    let Rmax := 36*U^2/lam
    let Dmax := K/L+1
    2*η+10368*(b*U/P)*U^4/(lam^2*L)≤1/2 ∧
      P<A-Rmax ∧ B+Rmax+2*Dmax<2*P ∧ 2*K*P^2/(σ*T)≤κ₀ := by
  intro L lam Rmax Dmax
  pm_6226
  pm_307 hL L
  have hRmax : Rmax≤(36/a)*(P*Real.sqrt U) := by
    have hUsqrt : U≤Real.sqrt U := by
      nlinarith only [Real.sq_sqrt hU.le,Real.sqrt_le_one.mpr hU1,Real.sqrt_nonneg U]
    calc
      _ = (36/a)*(P*U) := by dsimp only [Rmax,lam]; field_simp
      _ ≤ _ := by gcongr
  pm_2064 hK.trans
  have hDmax : Dmax≤(n/l+1)*(P*Real.sqrt U) := by
    calc
      _ ≤ (n*(P*U*Real.sqrt U))/(l*U)+P*Real.sqrt U :=
        add_le_add (div_le_div_of_nonneg_right hKhi hL.le) hPS
      _ = _ := by field_simp
  have hlift' : 2*η+10368*(b*U/P)*U^4/(lam^2*L)≤1/2 := by
    have hid : 10368*(b*U/P)*U^4/(lam^2*L)=
        (10368*b/(a^2*l))*(P*U^2) := by dsimp only [lam,L]; field_simp
    rw [hid]
    linarith only [hηhi,hlift]
  have hleft : P<A-Rmax := by
    have hgap : Rmax < m*(P*Real.sqrt U) := by
      have hh : 0<(2*(n/l+1)+1)*(P*Real.sqrt U) := by positivity
      dsimp only [m]
      nlinarith only [hRmax,hh]
    linarith only [hA,hgap]
  have hright : B+Rmax+2*Dmax<2*P := by
    have hh : 0<P*Real.sqrt U := by positivity
    nlinarith only [hB,hRmax,hDmax,hh]
  have hκ' : 2*K*P^2/(σ*T)≤κ₀ := by
    calc
      _ ≤ 2*(n*(P*U*Real.sqrt U))*P^2/(σ*T) := by gcongr
      _ = (2*n*u/σ)*Real.sqrt U := by simp only [hUeq]; field_simp
      _ ≤ _ := hκ
  exact ⟨hlift',hleft,hright,hκ'⟩

                                                                        
                                                                              
                                                                          
theorem exists_model_uniform_refined_source_bands
    {σ k₀ l₀ ε : ℝ} (hσ : 0<σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0<ε) (hp : k₀+ε<1) :
    let u := modelPhaseJetCoefficient σ 2+1
    let l := modelPhaseJetLower σ 2/u
    let a := modelPhaseJetLower σ 3/u
    let b := (modelPhaseJetCoefficient σ 3+1)/u
    let x := (modelPhaseJetCoefficient σ 1+1)/(2*u)
    let n := 2+48/a
    let m := 36/a+2*(n/l+1)+1
    ∃ δ κ₀ : ℝ, 0<δ ∧ 0<κ₀ ∧
      ∃ Qphase : ℕ, 3≤Qphase ∧ ∃ Cd ≥ (1:ℝ), ∃ C > (0:ℝ),
      ∀ (ι : Type*) [DecidableEq ι] (S : Finset ι) (F : ℝ→ℝ)
        (T P : ℝ) (k : ι→ℤ) (H : ι→ℕ) (s : ℤ) (A B w : ℝ),
      IsApproximateModelPhaseFunction F σ Qphase δ →
      0<T → 0<P → 0<w → w≤1/2 →
      let U := u*T/P^3
      let N := ⌊1/(10*Real.sqrt U)⌋₊
      let L := l*U
      let X := x*P*U
      U≤1/3600 → 1≤P*U*Real.sqrt U → b≤P*U → l*U≤1 →
      P*U^2≤1 → 8*Real.sqrt U+(10368*b/(a^2*l))*(P*U^2)≤1/2 →
      (2*n*u/σ)*Real.sqrt U≤κ₀ →
      P+m*(P*Real.sqrt U)<A → B+m*(P*Real.sqrt U)<2*P →
      (∀ j : ℤ, (S.filter (fun i => k i=j)).card≤1) →
      (∀ i∈S, H i≤N) →
      let base := fun i => (s:ℝ)-2*(N:ℝ)+(N:ℝ)*(k i:ℝ)
      (∀ i∈S, Icc (base i-(7*(N:ℝ)+2)) (base i+(7*(N:ℝ)+2))⊆Icc A B) →
      ∃ r : ι→ℚ,
        (∀ Q₀ : ℕ, 2≤Q₀ →
          let D₀ := 8/(L*(N:ℝ)*(Q₀:ℝ))
          ((S.filter (fun i => Q₀≤(r i).den)).card:ℝ)≤
            4*(X+1)*D₀^2+D₀*(2+Real.log (D₀+1))) ∧
        (∀ j : ℕ,
          let Q : ℕ := 2^(j+1)
          let G := (S.filter (fun i => (r i).den≤N)).filter (fun i => Nat.log 2 (r i).den=j)
          let Zd := 4*(Q:ℝ)*(2*X*Q+1)
          let Err := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)+
            Real.sqrt (12/(L*(N:ℝ)*Q))
          (∑ i∈G, ‖∑ t∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),
            (𝐞 (T*F ((t:ℝ)/P)):ℂ)‖)≤
            Cd*Zd*(3*(N:ℝ)*Real.sqrt (3*U*(Q:ℝ)*N)+Err) ∧
          (1≤j → 12≤L*(Q:ℝ)*(N:ℝ)^2 → 384≤L^2*(Q:ℝ)^3*(N:ℝ)^3 →
            (∑ i∈G, ‖∑ t∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),
              (𝐞 (T*F ((t:ℝ)/P)):ℂ)‖)^12 ≤
              C*P^ε*(1+Real.log P)^24*
                (P^11*U+w*P^12*U^((5:ℝ)/2)+
                  P^(11+(k₀+ε)+(l₀+ε))*U^(2+(k₀+ε)+(l₀+ε)/2)*w^(-(k₀+ε))))) := by
  classical
  intro u l a b x n m
  pm_2069
  pm_5377 ha a modelPhaseJetLower_pos
  pm_5377 hb b modelPhaseJetCoefficient_pos
  pm_5816
  pm_700
  pm_2091
  have hq : 0≤l₀+ε := by linarith [hpair.inTriangle.2.2.1]
  obtain ⟨δ,κ₀,hδ,hκ₀,Qphase,hQphase,Cd,hCd,Cf,hCf,Cp,hCp,hsource⟩ :=
    exists_model_refined_source_bands hσ hpair hε hp
  pm_69 Cc hCc hcard exists_displacement_cardinality_majorants hl hx
  obtain ⟨Cr,hCr,hrhs⟩ := exists_refined_uniform_frozen_rhs
    (p:=k₀+ε) (q:=l₀+ε) hl hε hCc
  obtain ⟨Ca,hCa,hpairPhysical⟩ := exists_refined_physical_pair_bound
    (p:=k₀+ε) hl ha hb.le hu hq hCp
  refine ⟨δ,κ₀,hδ,hκ₀,Qphase,hQphase,Cd,hCd,Cf*Ca*Cr,by positivity,?_⟩
  intro ι _ S F T P k H s A B w hF hT hP hw hwhalf
    U N L X hUsmall hK hbPU hLsmall hsmall hlift hκ hA hB hmul hH base hbuffer
  pm_307 hU U
  pm_2067
  have hscale := displacement_block_physical_scale hP hU hUsmall hK
  have hblock := displacement_block_scale hU hUsmall
  have hN : 0<N := hblock.1
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  pm_307 hL L
  have hmargin : 0 < m*(P*Real.sqrt U) := by positivity
  have hA₀ : P<A := by linarith only [hA,hmargin]
  have hB₀ : B<2*P := by linarith only [hB,hmargin]
  have hLeq : modelPhaseJetLower σ 2*T/P^3=L := by
    dsimp only [L,l,U]; field_simp
  have hlameq : modelPhaseJetLower σ 3*T/P^4=a*U/P := by
    dsimp only [a,U]; field_simp
  have hFeq : (modelPhaseJetCoefficient σ 3+1)*T/P^4=b*U/P := by
    dsimp only [b,U]; field_simp
  have hXeq : (modelPhaseJetCoefficient σ 1+1)*T/P^2/2=X := by
    dsimp only [X,x,U]; field_simp
  have htaylor := displacement_taylor_smallness hb hP hU hUsmall hbPU
  obtain ⟨r,htail,hbands⟩ := hsource ι S F T P k H N s A B w hF hT hP hN hw hwhalf
    hA₀ hB₀ (by change 12*U≤1; linarith only [hUsmall])
    (by rw [hLeq]; exact hLsmall)
    (by rw [hFeq]; exact htaylor.1) htaylor.2 hmul hH hbuffer
  clear hsource
  rw [hLeq,hXeq] at htail
  pm_1188 r htail j Q G Zd Err
  have hband := hbands j
  clear hbands
  rw [hLeq,hlameq,hFeq,hXeq] at hband
  pm_2126
  pm_307 hQ Q
  have hQr : (0:ℝ)<Q := Nat.cast_pos.mpr hQ
  pm_277 hQ1 Q hQ
  pm_600 hpow
  have hQN : (Q:ℝ)≤2*(N:ℝ) := by
    have hh : Q≤2*N := by
      calc
        Q=2*2^j := by dsimp only [Q]; rw [pow_succ,Nat.mul_comm]
        _≤2*N := Nat.mul_le_mul_left _ (hpow.trans hiN)
    exact_mod_cast hh
  pm_7466
  clear hcard
  have hZlo : (G.card:ℝ)≤Cc*P*U*(Q:ℝ)^2 := hband.1.trans hc.1
  have hZhi : (G.card:ℝ)≤Cc*(P/(Q:ℝ)^2)*(1+Real.log P) :=
    (hband.2.1 hj).trans hc.2
  let M : ℕ := ⌈63*U*(Q:ℝ)*(N:ℝ)^2⌉₊+1
  let lam := a*U/P
  let D₀ := (Real.sqrt M/(9*(M:ℝ))+Real.sqrt M/(12*(M:ℝ)^2))*Real.sqrt (U*(Q:ℝ)^3)
  let η := 4*D₀/(Q:ℝ)
  let rho := (12*U*Real.sqrt (U*(Q:ℝ)^3)/lam)*(Real.sqrt M/(6*(M:ℝ)^2))
  let K := ⌈3*U*(rho+1)⌉₊
  let Rmax := 36*U^2/lam
  pm_8725 Dmax
  let Dweight := 144*U^2/(lam*N)
  let E := P*U+w*(P*Real.sqrt U)+(P*U)^(k₀+ε)*(P*Real.sqrt U)^(l₀+ε)*w^(-(k₀+ε))+1/(P*U)
  let Count := Cp*((2*η+w)*Dmax+20736*(b*U/P)*U^4/(lam^2*L^2)+
    (T/P^2)^(k₀+ε)*Dmax^(l₀+ε)*w^(-(k₀+ε))+P^2/T)
  let Weight := 3*(K:ℝ)+Dweight*(harmonic K:ℝ)
  let Pair := 4*(G.card:ℝ)+6*Count*Weight
  let R := (G.card:ℝ)+(P*U*Real.sqrt U)*E*(1+Real.log P)
  have hM1 : (1:ℝ)≤M := by
    have hh : 1≤M := by dsimp only [M]; omega
    exact_mod_cast hh
  have hMscale := hblock.2.2.2.2.2 Q hQ
  have hQM : (Q:ℝ)≤4*(M:ℝ) := by
    have hh := hMscale.1
    change (7/16:ℝ)*Q≤(M:ℝ) at hh
    linarith only [hh,hQr.le]
  have hthin : (Q:ℝ)^2<6*(M:ℝ)^2 := hMscale.2.2
  pm_528 hcut displacement_physical_cutoff ha hP hU hUsmall hK hM1 hQr hQM
  pm_2068
  obtain ⟨hlift',hleft,hright,hκ'⟩ := refined_physical_lifting_domain
    hσ hl ha (le_trans zero_le_one hn) hP hT hU hU1 rfl hK
    hcut.2.1 hcut.2.2.1 hlift hκ hA hB
  have hPair : Pair≤Ca*R := by
    have hh := hpairPhysical P U M Q G.card w hP hU hUsmall hK
      hM1 hQr hQM (by positivity) hw
    have hTP : T/P^2=P*U/u := by dsimp only [U]; field_simp
    have hPT : P^2/T=u/(P*U) := by dsimp only [U]; field_simp
    dsimp only [Pair,Count,Weight,R]
    rw [hTP,hPT]
    exact hh
  have hs := hband.2.2.2 hdual hfrozen hthin hlift' hleft hright hκ'
  have hr := hrhs P U G.card w Q hP hU hUsmall hscale.1 hsmall
    (by positivity) hw hQ (hQN.trans hscale.2.2) hZlo hZhi
  clear hband hpairPhysical hrhs
  let V := 756*U/L
  let W := 1+32/(L*(Q:ℝ)^2*N)
  let d := L*(Q:ℝ)*N/12
  pm_2167 W
  change _ ≤ Cf*(Loss*(2*(G.card:ℝ))^10*Pair+((G.card:ℝ)*Err)^12) at hs
  change Loss*(2*(G.card:ℝ))^10*R+((G.card:ℝ)*Err)^12≤_ at hr
  pm_2164 hW0 W
  have hLoss0 : 0≤Loss*(2*(G.card:ℝ))^10 :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) hW0) 11)
            (sq_nonneg W)) ((show Even (12:ℕ) from ⟨6,rfl⟩).pow_nonneg _))
          ((show Even (6:ℕ) from ⟨3,rfl⟩).pow_nonneg _))
        (Real.rpow_nonneg (Nat.cast_nonneg M) _))
      ((show Even (10:ℕ) from ⟨5,rfl⟩).pow_nonneg _)
  have he0 : 0≤((G.card:ℝ)*Err)^12 := (show Even (12:ℕ) from ⟨6,rfl⟩).pow_nonneg _
  have habsorb : Cf*(Loss*(2*(G.card:ℝ))^10*Pair+((G.card:ℝ)*Err)^12)≤
      (Cf*Ca)*(Loss*(2*(G.card:ℝ))^10*R+((G.card:ℝ)*Err)^12) := by
    have hh := mul_le_mul_of_nonneg_left hPair hLoss0
    rw [mul_left_comm (Loss*(2*(G.card:ℝ))^10) Ca R] at hh
    have he := le_mul_of_one_le_left he0 hCa
    calc
      _ ≤ Cf*(Ca*(Loss*(2*(G.card:ℝ))^10*R+((G.card:ℝ)*Err)^12)) :=
        mul_le_mul_of_nonneg_left
          ((add_le_add hh he).trans_eq (mul_add Ca _ _).symm) hCf.le
      _ = _ := (mul_assoc _ _ _).symm
  exact hs.trans (habsorb.trans (by
    have hh := mul_le_mul_of_nonneg_left hr (show 0≤Cf*Ca by positivity)
    simpa only [mul_assoc] using hh))

                                                                                          
theorem exists_model_refined_source_global
    {σ k₀ l₀ ε : ℝ} (hσ : 0<σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0<ε) (hp : k₀+ε<1) :
    let u := modelPhaseJetCoefficient σ 2+1
    let l := modelPhaseJetLower σ 2/u
    let a := modelPhaseJetLower σ 3/u
    let b := (modelPhaseJetCoefficient σ 3+1)/u
    let n := 2+48/a
    let m := 36/a+2*(n/l+1)+1
    ∃ δ κ₀ : ℝ, 0<δ ∧ 0<κ₀ ∧
      ∃ Qphase : ℕ, 3≤Qphase ∧ ∃ C > (0:ℝ),
      ∀ (ι : Type*) [DecidableEq ι] (S : Finset ι) (F : ℝ→ℝ)
        (T P : ℝ) (k : ι→ℤ) (H : ι→ℕ) (s : ℤ) (A B w : ℝ),
      IsApproximateModelPhaseFunction F σ Qphase δ →
      0<T → 0<P → 0<w → w≤1/2 →
      let U := u*T/P^3
      let N := ⌊1/(10*Real.sqrt U)⌋₊
      U≤1/3600 → 1≤P*U*Real.sqrt U → b≤P*U → l*U≤1 →
      P*U^2≤1 → 8*Real.sqrt U+(10368*b/(a^2*l))*(P*U^2)≤1/2 →
      (2*n*u/σ)*Real.sqrt U≤κ₀ →
      P+m*(P*Real.sqrt U)<A → B+m*(P*Real.sqrt U)<2*P →
      (∀ j : ℤ, (S.filter (fun i => k i=j)).card≤1) →
      (∀ i∈S, H i≤N) →
      let base := fun i => (s:ℝ)-2*(N:ℝ)+(N:ℝ)*(k i:ℝ)
      (∀ i∈S, Icc (base i-(7*(N:ℝ)+2)) (base i+(7*(N:ℝ)+2))⊆Icc A B) →
      (1+23*(N:ℝ)+∑ i∈S,
        ‖∑ t∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),
          (𝐞 (T*F ((t:ℝ)/P)):ℂ)‖)^12 ≤
        C*P^ε*(1+Real.log P)^36*(P^11*U+w*P^12*U^((5:ℝ)/2)+P^(11+(k₀+ε)+(l₀+ε))*U^(2+(k₀+ε)+(l₀+ε)/2)*w^(-(k₀+ε))) := by
  classical
  intro u l a b n m
  let x := (modelPhaseJetCoefficient σ 1+1)/(2*u)
  pm_2069
  pm_5816
  obtain ⟨δ,κ₀,hδ,hκ₀,Qphase,hQphase,Cd,hCd,Cf,hCf,hsource⟩ :=
    exists_model_uniform_refined_source_bands hσ hpair hε hp
  pm_2131
  refine ⟨δ,κ₀,hδ,hκ₀,Qphase,hQphase,1000^12*C₀,by positivity,?_⟩
  intro ι _ S F T P k H s A B w hF hT hP hw₀ hwhalf U N
    hUsmall hKscale hbPU hLsmall hsmall₀ hlift hκ hA hB hmul hH base hbuffer
  let L := l*U
  let X := x*P*U
  pm_5545 t F P
  pm_307 hU U
  have hscale := displacement_block_physical_scale hP hU hUsmall hKscale
  pm_2110
  have hN := (displacement_block_scale hU hUsmall).1
  obtain ⟨r,htail,hband⟩ := hsource ι S F T P k H s A B w hF hT hP hw₀ hwhalf
    hUsmall hKscale hbPU hLsmall hsmall₀ hlift hκ hA hB hmul hH hbuffer
  pc_148 weight
  let E := P^11*U+w*P^12*U^((5:ℝ)/2)+P^(11+(k₀+ε)+(l₀+ε))*U^(2+(k₀+ε)+(l₀+ε)/2)*w^(-(k₀+ε))
  pm_2132
  pm_2280
  pm_2070
  pm_2133
  have hbaseBudget (c : ℝ) (hc0 : 0≤c) (hc : c≤C₀) :
      c*P^ε*Log^24*(P^11*U)≤Budget :=
    (mul_le_mul_of_nonneg_left hFirst (by positivity)).trans (hbudget c hc)
  pm_2128
  pm_8600 i ι weight norm_nonneg
  have hwH (i : ι) (hi : i∈S) : weight i ≤ N := by
    pb_563
  have htail' : (∑ i∈R,weight i) ≤ Ct*P*Real.sqrt U := by
    pm_5647
    have hs : (∑ i∈R,weight i) ≤ (R.card:ℝ)*(N:ℝ) := by
      pm_2134
    pm_2130
  have htailMoment : (∑ i∈R,weight i)^12 ≤ Budget := by
    have hh : (∑ i∈R,weight i) ≤ Ct*P*U^((1:ℝ)/2)*Log^2 := by
      rw [←Real.sqrt_eq_rpow]
      exact htail'.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hlog1))
    exact (refined_elementary_twelfth hscale.2.1 hU hU1 (Finset.sum_nonneg (fun i _ => hw i))
      hCt.le hlog1 hε.le (by norm_num : (1:ℝ)/4 ≤ 1/2) hsmall₀ hh).trans (hbaseBudget _ (by positivity) hCt₀)
  have hboundary : (1+23*(N:ℝ))^12 ≤ Budget := by
    have hh : 1+23*(N:ℝ) ≤ 24*P*U^((1:ℝ)/2)*Log^2 := by
      rw [←Real.sqrt_eq_rpow]
      exact (htailSize P U hP hU hUsmall hscale.1).1.trans
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hlog1))
    exact (refined_elementary_twelfth hscale.2.1 hU hU1 (by positivity)
      (by norm_num : (0:ℝ)≤24) hlog1 hε.le (by norm_num : (1:ℝ)/4 ≤ 1/2) hsmall₀ hh).trans
        (hbaseBudget _ (by positivity) hCb₀)
  have hbands (j : ℕ) : (g j)^12 ≤ Budget := by
    pm_2127
    have hg' : g j≤(Cd*Cs)*P*U^((1:ℝ)/3)*Log^2 :=
      hg.trans (by
        have hh : Log≤Log^2 := by nlinarith only [hlog1]
        gcongr)
    exact (refined_elementary_twelfth hscale.2.1 hU hU1 (Finset.sum_nonneg (fun i _ => hw i))
      (mul_nonneg hCdp hCs.le) hlog1 hε.le (by norm_num : (1:ℝ)/4 ≤ 1/3) hsmall₀ hg').trans
        (hbaseBudget _ (by positivity) hCs₀)
  pm_2129
  pm_2135 weight
  calc
    _ = (1+23*(N:ℝ)+(∑ i∈R,weight i)+∑ j∈Finset.range J,g j)^12 := by congr 1; ring
    _ ≤ ((J:ℝ)+2)^12*Budget := hfinite
    _ ≤ (1000*Log)^12*Budget := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) hJbound 12) (by dsimp only [Budget]; positivity)
    _ = (1000^12*C₀)*P^ε*(1+Real.log P)^36*(P^11*U+w*P^12*U^((5:ℝ)/2)+P^(11+(k₀+ε)+(l₀+ε))*U^(2+(k₀+ε)+(l₀+ε)/2)*w^(-(k₀+ε))) := by
      pm_1014

                                                                                  
theorem refined_integer_source_trim
    (g : ℤ→ℂ) (hg : ∀ n, ‖g n‖≤1) {a b : ℤ} {K : ℕ}
    (hab : a+2*(K:ℤ)≤b) :
    ‖∑ n∈Finset.Icc a b,g n‖≤
      ‖∑ n∈Finset.Ioc (a+K) (b-K),g n‖+2*(K:ℝ)+1 := by
  have hlo : a≤a+K := by omega
  have hmid : a+(K:ℤ)≤b-K := by omega
  have hhi : b-(K:ℤ)≤b := by omega
  rw [←Finset.add_sum_Ioc_eq_sum_Icc (show a≤b by omega)]
  rw [sargos_integer_Ioc_sum_split g hlo (hmid.trans hhi),
    sargos_integer_Ioc_sum_split g hmid hhi]
  have hleft := norm_sum_integer_Ioc_le g hg hlo
  have hright := norm_sum_integer_Ioc_le g hg hhi
  have hnorm₁ := norm_add_le (g a)
    ((∑ n∈Finset.Ioc a (a+K),g n)+
      ((∑ n∈Finset.Ioc (a+K) (b-K),g n)+(∑ n∈Finset.Ioc (b-K) b,g n)))
  have hnorm₂ := norm_add_le (∑ n∈Finset.Ioc a (a+K),g n)
    ((∑ n∈Finset.Ioc (a+K) (b-K),g n)+(∑ n∈Finset.Ioc (b-K) b,g n))
  have hnorm₃ := norm_add_le (∑ n∈Finset.Ioc (a+K) (b-K),g n)
    (∑ n∈Finset.Ioc (b-K) b,g n)
  push_cast at hleft hright
  linarith only [hnorm₁,hnorm₂,hnorm₃,hleft,hright,hg a]

                                                                      
                                                                  
theorem exists_model_refined_global_bound
    {σ k₀ l₀ ε : ℝ} (hσ : 0<σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0<ε) (hp : k₀+ε<1) :
    let u := modelPhaseJetCoefficient σ 2+1
    let l := modelPhaseJetLower σ 2/u
    let a := modelPhaseJetLower σ 3/u
    let b := (modelPhaseJetCoefficient σ 3+1)/u
    let n := 2+48/a
    ∃ δ κ₀ : ℝ, 0<δ ∧ 0<κ₀ ∧
      ∃ Qphase : ℕ, 3≤Qphase ∧ ∃ C > (0:ℝ),
      ∀ (F : ℝ→ℝ) (T P : ℝ) (aa bb : ℕ) (w : ℝ),
      IsApproximateModelPhaseFunction F σ Qphase δ →
      0<T → 0<P → P≤aa → (bb:ℝ)≤2*P → 0<w → w≤1/2 →
      let U := u*T/P^3
      U≤1/3600 → 1≤P*U*Real.sqrt U → b≤P*U → l*U≤1 →
      P*U^2≤1 → 8*Real.sqrt U+(10368*b/(a^2*l))*(P*U^2)≤1/2 →
      (2*n*u/σ)*Real.sqrt U≤κ₀ →
      ‖exponentialSumAt F T P aa bb‖^12 ≤
        C*P^ε*(1+Real.log P)^36*
          (P^11*U+w*P^12*U^((5:ℝ)/2)+
            P^(11+(k₀+ε)+(l₀+ε))*U^(2+(k₀+ε)+(l₀+ε)/2)*w^(-(k₀+ε))) := by
  classical
  intro u l a b n
  pm_6226
  pm_2069
  pm_5377 ha a modelPhaseJetLower_pos
  pm_307 hn n
  pm_2091
  obtain ⟨δ,κ₀,hδ,hκ₀,Qphase,hQphase,Cf,hCf,hsource⟩ :=
    exists_model_refined_source_global hσ hpair hε hp
  let Ctrim := 2*m+3
  pm_307 hCtrim Ctrim
  let C := 2^11*(Cf+Ctrim^12)
  pm_307 hC C
  pm_145 δ κ₀ hδ hκ₀ Qphase hQphase C hC
  intro F T P aa bb w hF hT hP haa hbb hw hwhalf U
    hUsmall hKscale hbPU hLsmall hsmall hlift hκ
  pm_307 hU U
  pm_2067
  have hscale := displacement_block_physical_scale hP hU hUsmall hKscale
  pm_7174
  have hN : 0<N := (displacement_block_scale hU hUsmall).1
  let K := ⌈m*(P*Real.sqrt U)⌉₊
  let E := P^11*U+w*P^12*U^((5:ℝ)/2)+
    P^(11+(k₀+ε)+(l₀+ε))*U^(2+(k₀+ε)+(l₀+ε)/2)*w^(-(k₀+ε))
  let Log := 1+Real.log P
  let Budget := P^ε*Log^36*E
  have hLog1 : 1≤Log := by
    have hh := Real.log_nonneg hscale.2.1
    dsimp only [Log]
    linarith only [hh]
  have hLog : 0<Log := zero_lt_one.trans_le hLog1
  pm_2164 hE E
  pm_2164 hBudget Budget
  pm_2070
  pm_2064 hKscale.trans
  have hKlo : m*(P*Real.sqrt U)≤(K:ℝ) := Nat.le_ceil _
  have hKhi : (K:ℝ) ≤ m*(P*Real.sqrt U)+1 :=
    (Nat.ceil_lt_add_one (show 0 ≤ m*(P*Real.sqrt U) by positivity)).le
  have htrimBound : 2*(K:ℝ)+1≤Ctrim*P*Real.sqrt U := by
    dsimp only [Ctrim]
    nlinarith only [hKhi,hPS]
  have htrimMoment : (2*(K:ℝ)+1)^12≤Ctrim^12*Budget := by
    have hh : 2*(K:ℝ)+1≤Ctrim*P*U^((1:ℝ)/2)*Log^2 := by
      rw [←Real.sqrt_eq_rpow]
      exact htrimBound.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hLog1))
    have he := refined_elementary_twelfth hscale.2.1 hU hU1 (by positivity)
      hCtrim.le hLog1 hε.le (by norm_num : (1:ℝ)/4≤1/2) hsmall hh
    calc
      _ ≤ Ctrim^12*P^ε*Log^24*(P^11*U) := he
      _ ≤ Ctrim^12*P^ε*Log^36*E := by gcongr; norm_num
      _ = _ := by simp only [Budget,mul_assoc]
  by_cases hlong : aa+2*K≤bb
  · let A : ℤ := (aa:ℤ)+K
    let B : ℤ := (bb:ℤ)-K
    let g := fun t : ℤ => (𝐞 (T*F ((t:ℝ)/P)):ℂ)
    have hg (t : ℤ) : ‖g t‖≤1 := by dsimp only [g]; simp
    have hAB : A≤B := by dsimp only [A,B]; omega
    obtain ⟨S,hbuffer,_,hblocks⟩ := exists_buffered_integer_source_blocks_interval g hg
      hAB (le_refl (A:ℝ)) (le_refl (B:ℝ)) N hN
    have hmul (j : ℤ) : (S.filter (fun k : ℕ => (k:ℤ)=j)).card≤1 := by
      apply Finset.card_le_one.mpr
      intro v hv z hz
      pm_547 hv' Finset.mem_filter.mp hv hz' hz
      exact_mod_cast hv'.trans hz'.symm
    have hA : P+m*(P*Real.sqrt U)<(A:ℝ)+1/2 := by
      dsimp only [A]
      push_cast
      linarith only [haa,hKlo]
    have hB : (B:ℝ)-1/2+m*(P*Real.sqrt U)<2*P := by
      dsimp only [B]
      push_cast
      linarith only [hbb,hKlo]
    have hs := hsource ℕ S F T P (fun k => (k:ℤ)) (fun _ => N) A
      ((A:ℝ)+1/2) ((B:ℝ)-1/2) w hF hT hP hw hwhalf
      hUsmall hKscale hbPU hLsmall hsmall hlift hκ hA hB hmul (fun _ _ => le_rfl)
      (by simpa only [Int.cast_natCast] using hbuffer)
    let Core := 1+23*(N:ℝ)+∑ k∈S, ‖∑ t∈Finset.Ioc (A+(N:ℤ)*k) (A+(N:ℤ)*k+N),g t‖
    pm_2164 hCore Core
    change Core^12≤Cf*P^ε*Log^36*E at hs
    have hs' : Core^12≤Cf*Budget := by simpa only [Budget,mul_assoc] using hs
    have ht := refined_integer_source_trim g hg (a:=(aa:ℤ)) (b:=(bb:ℤ)) (K:=K)
      (by exact_mod_cast hlong)
    have hnorm : ‖exponentialSumAt F T P aa bb‖≤Core+(2*(K:ℝ)+1) := by
      rw [exponentialSumAt_eq_int_sum]
      change ‖∑ t∈Finset.Icc (aa:ℤ) (bb:ℤ),g t‖≤_
      change ‖∑ t∈Finset.Icc (aa:ℤ) (bb:ℤ),g t‖≤‖∑ t∈Finset.Ioc A B,g t‖+2*(K:ℝ)+1 at ht
      pm_737 Core ht hblocks
    have hp₀ := (pow_le_pow_left₀ (norm_nonneg _) hnorm 12).trans
      (add_pow_le hCore (by positivity : 0≤2*(K:ℝ)+1) 12)
    have hm := mul_le_mul_of_nonneg_left (add_le_add hs' htrimMoment)
      (show (0:ℝ)≤2^(12-1) by positivity)
    exact hp₀.trans (by
      rw [←add_mul,←mul_assoc] at hm
      simpa only [C,Budget,Log,E,mul_assoc,Nat.reduceSub] using hm)
  · have hnorm : ‖exponentialSumAt F T P aa bb‖≤2*(K:ℝ)+1 := by
      have hc : ((Finset.Icc aa bb).card:ℝ)≤2*(K:ℝ)+1 := by
        have hh : (Finset.Icc aa bb).card≤2*K+1 := by rw [Nat.card_Icc]; omega
        exact_mod_cast hh
      exact (norm_exponentialSumAt_le_card F T P aa bb).trans hc
    have hCtrimC : Ctrim^12≤C := by
      exact (le_add_of_nonneg_left hCf.le).trans
        (le_mul_of_one_le_left (by positivity) (by norm_num : (1:ℝ)≤2^11))
    exact ((pow_le_pow_left₀ (norm_nonneg _) hnorm 12).trans htrimMoment).trans
      (by
        simpa only [Budget,Log,E,mul_assoc] using mul_le_mul_of_nonneg_right hCtrimC hBudget)

                                                                                    
theorem eventually_refined_bourgain_parameters
    {T P : VariableObject ℝ} {α σ κ₀ : ℝ}
    (hlo : 2/5<α) (hhi : α<3/7) (hσ : 0<σ) (hκ₀ : 0<κ₀)
    (hT : ∀ i, 1≤T i) (hTunbounded : T.IsUnbounded)
    (hPT : IsPowerAsymptotic P T α) :
    let u := modelPhaseJetCoefficient σ 2+1
    let l := modelPhaseJetLower σ 2/u
    let a := modelPhaseJetLower σ 3/u
    let b := (modelPhaseJetCoefficient σ 3+1)/u
    let n := 2+48/a
    let U := fun i => u*T i/(P i)^3
    let w := fun i => (T i)^(-(3+23*α)/194)
    ∀ᶠ i in atTop, 0<P i ∧ 0<w i ∧ w i≤1/2 ∧ U i≤1/3600 ∧
      1≤P i*U i*Real.sqrt (U i) ∧ b≤P i*U i ∧ l*U i≤1 ∧
      P i*(U i)^2≤1 ∧
      8*Real.sqrt (U i)+(10368*b/(a^2*l))*(P i*(U i)^2)≤1/2 ∧
      (2*n*u/σ)*Real.sqrt (U i)≤κ₀ := by
  intro u l a b n U w
  pm_5817
  have hTscale := isPowerAsymptotic_self T
  pm_6027
  pm_5648
  have hv : v<0 := by dsimp only [v]; linarith only [hlo]
  have homegaScale : omegaScale<0 := by dsimp only [omegaScale]; linarith only [hlo]
  pm_2071
  have hroot : IsPowerAsymptotic (fun i => Real.sqrt (U i)) T (v/2) := by
    simpa only [Real.sqrt_eq_rpow,mul_one_div] using cubic_power_rpow hU hT ((1:ℝ)/2)
  have hPU : IsPowerAsymptotic (fun i => P i*U i) T (α+v) := hPT.mul hU hT
  have hcurve : IsPowerAsymptotic (fun i => P i*U i*Real.sqrt (U i)) T (α+v+v/2) :=
    hPU.mul hroot hT
  have hlifting : IsPowerAsymptotic (fun i => P i*(U i)^2) T (α+2*v) := by
    convert hPT.mul (cubic_power_natpow hU hT 2) hT using 1
    ring
  have hw : IsPowerAsymptotic w T omegaScale := by
    simpa using cubic_power_rpow hTscale hT omegaScale
  have hPpos := (hPT.tendsto_atTop_of_pos (by linarith only [hlo] : 0<α)
    hT hTunbounded).eventually (eventually_gt_atTop 0)
  have hUzero := hU.tendsto_zero_of_neg hv hT hTunbounded
  have hrootzero := hroot.tendsto_zero_of_neg (by linarith only [hv]) hT hTunbounded
  have hliftzero := hlifting.tendsto_zero_of_neg
    (by dsimp only [v]; linarith only [hlo] : α+2*v<0) hT hTunbounded
  have hsmall := hUzero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/3600))
  have hwsmall := (hw.tendsto_zero_of_neg homegaScale hT hTunbounded).eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2))
  have hcurveLarge := (hcurve.tendsto_atTop_of_pos
    (by dsimp only [v]; linarith only [hhi] : 0<α+v+v/2) hT hTunbounded).eventually
    (eventually_ge_atTop 1)
  have hPULarge := (hPU.tendsto_atTop_of_pos
    (by dsimp only [v]; linarith only [hhi] : 0<α+v) hT hTunbounded).eventually
    (eventually_ge_atTop b)
  have hLsmall := (hUzero.const_mul l).eventually
    (by simpa using (eventually_lt_nhds (by norm_num : (0:ℝ)<1)))
  have hLiftSmall := hliftzero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))
  have hsourceLift := ((hrootzero.const_mul 8).add
    (hliftzero.const_mul (10368*b/(a^2*l)))).eventually
      (by simpa using (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2)))
  have hshift := (hrootzero.const_mul (2*n*u/σ)).eventually
    (by simpa using (eventually_lt_nhds hκ₀))
  filter_upwards [hPpos,hwsmall,hsmall,hcurveLarge,hPULarge,hLsmall,hLiftSmall,hsourceLift,hshift]
    with i hPi hwi hUi hci hpui hli hlifti hsi hki
  exact ⟨hPi,Real.rpow_pos_of_pos (zero_lt_one.trans_le (hT i)) _,
    hwi.le,hUi.le,hci,hpui,hli.le,hlifti.le,by simpa only [one_div] using hsi.le,hki.le⟩

                                                                           
theorem eventually_refined_bourgain_cost
    {T P : VariableObject ℝ} {α σ η : ℝ}
    (hlo : 2/5<α) (hhi : α<3/7) (hσ : 0<σ) (hη : 0<η)
    (hT : ∀ i, 1≤T i) (hTunbounded : T.IsUnbounded)
    (hPT : IsPowerAsymptotic P T α) :
    let u := modelPhaseJetCoefficient σ 2+1
    let U := fun i => u*T i/(P i)^3
    let w := fun i => (T i)^(-(3+23*α)/194)
    let β := max (1/12+2*α/3) (241/1164+425*α/1164)
    ∀ᶠ i in atTop,
      (P i)^η*(1+Real.log (P i))^36*
        ((P i)^11*U i+w i*(P i)^12*(U i)^((5:ℝ)/2)+
          (P i)^(11+(13/84+η)+(55/84+η))*
            (U i)^(2+(13/84+η)+(55/84+η)/2)*(w i)^(-(13/84+η))) ≤
        3*(T i)^(12*β+5*η) := by
  intro u U w β
  pm_5817
  pm_5648
  let β₁ := 1/12+2*α/3
  let β₂ := 241/1164+425*α/1164
  have hβ₁ : β₁≤β := le_max_left _ _
  have hβ₂ : β₂≤β := le_max_right _ _
  have hα1 : α<1 := by linarith only [hhi]
  have hcoef : 3*α+3*v/2-omegaScale≤3 := by dsimp only [v,omegaScale]; linarith only [hlo,hhi]
  pm_6027
  have hTscale := isPowerAsymptotic_self T
  pm_2071
  have hw : IsPowerAsymptotic w T omegaScale := by simpa using cubic_power_rpow hTscale hT omegaScale
  let g₁ := fun i => (P i)^η*((P i)^11*U i)
  let g₂ := fun i => (P i)^η*(w i*(P i)^12*(U i)^((5:ℝ)/2))
  let g₃ := fun i => (P i)^η*((P i)^(11+(13/84+η)+(55/84+η))*
    (U i)^(2+(13/84+η)+(55/84+η)/2)*(w i)^(-(13/84+η)))
  have hg₁ : IsPowerAsymptotic g₁ T (α*η+(α*11+v)) :=
    (cubic_power_rpow hPT hT η).mul ((cubic_power_natpow hPT hT 11).mul hU hT) hT
  have hg₂ : IsPowerAsymptotic g₂ T (α*η+(omegaScale+α*12+v*(5/2))) :=
    (cubic_power_rpow hPT hT η).mul
      ((hw.mul (cubic_power_natpow hPT hT 12) hT).mul (cubic_power_rpow hU hT (5/2)) hT) hT
  have hg₃ : IsPowerAsymptotic g₃ T
      (α*η+(α*(11+(13/84+η)+(55/84+η))+v*(2+(13/84+η)+(55/84+η)/2)+omegaScale*(-(13/84+η)))) :=
    (cubic_power_rpow hPT hT η).mul
      (((cubic_power_rpow hPT hT _).mul (cubic_power_rpow hU hT _) hT).mul
        (cubic_power_rpow hw hT _) hT) hT
  have hexp₁ : α*η+(α*11+v)<12*β+4*η := by
    have hid : α*η+(α*11+v)=12*β₁+η*α := by dsimp only [v,β₁]; ring
    pm_5165 hα1.le hβ₁
  have hexp₂ : α*η+(omegaScale+α*12+v*(5/2))<12*β+4*η := by
    have hid : α*η+(omegaScale+α*12+v*(5/2))=12*β₂+η*α := by dsimp only [v,omegaScale,β₂]; ring
    pm_5165 hα1.le hβ₂
  have hexp₃ :
      α*η+(α*(11+(13/84+η)+(55/84+η))+v*(2+(13/84+η)+(55/84+η)/2)+omegaScale*(-(13/84+η)))<
        12*β+4*η := by
    have hid : α*η+(α*(11+(13/84+η)+(55/84+η))+v*(2+(13/84+η)+(55/84+η)/2)+omegaScale*(-(13/84+η)))=
        12*β₂+η*(3*α+3*v/2-omegaScale) := by dsimp only [v,omegaScale,β₂]; ring
    pm_5165 hcoef hβ₂
  have hb₁ := cubic_power_eventually_le hg₁ hT hexp₁
  have hb₂ := cubic_power_eventually_le hg₂ hT hexp₂
  have hb₃ := cubic_power_eventually_le hg₃ hT hexp₃
  have hP1 := (hPT.tendsto_atTop_of_pos (by linarith only [hlo] : 0<α)
    hT hTunbounded).eventually (eventually_ge_atTop 1)
  have hPTle := cubic_power_eventually_le hPT hT hα1
  have hTtop : Tendsto T atTop atTop :=
    (VariableObject.isUnbounded_iff_tendsto_atTop (fun i => zero_le_one.trans (hT i))).mp hTunbounded
  have hlogT := (Real.tendsto_log_atTop.comp hTtop).eventually (eventually_ge_atTop 1)
  have hlogPower := hTtop.eventually
    (eventually_const_log_pow_le_rpow ((2:ℝ)^36) (by positivity) 36 hη)
  filter_upwards [hb₁,hb₂,hb₃,hP1,hPTle,hlogT,hlogPower] with i hi₁ hi₂ hi₃ hPi hPTi hlogi hlogPoweri
  have hTi : 0<T i := zero_lt_one.trans_le (hT i)
  have hPp : 0<P i := zero_lt_one.trans_le hPi
  have hlogP := Real.log_nonneg hPi
  change 1≤Real.log (T i) at hlogi
  have hlog : (1+Real.log (P i))^36≤(T i)^η := by
    have hlogPT : Real.log (P i)≤Real.log (T i) := by
      apply Real.log_le_log hPp
      simpa only [Real.rpow_one] using hPTi
    calc
      _ ≤ (2*Real.log (T i))^36 :=
        pow_le_pow_left₀ (by positivity) (by linarith only [hlogPT,hlogi]) 36
      _ = (2:ℝ)^36*(Real.log (T i))^36 := mul_pow _ _ _
      _ ≤ _ := hlogPoweri
  have hsum : g₁ i+g₂ i+g₃ i≤3*(T i)^(12*β+4*η) := by
    linarith only [hi₁,hi₂,hi₃]
  have hg0 : 0≤g₁ i+g₂ i+g₃ i := by dsimp only [g₁,g₂,g₃,U,w]; positivity
  calc
    _ = (1+Real.log (P i))^36*(g₁ i+g₂ i+g₃ i) := by dsimp only [g₁,g₂,g₃]; ring
    _ ≤ (T i)^η*(3*(T i)^(12*β+4*η)) := mul_le_mul hlog hsum hg0 (by positivity)
    _ = _ := by rw [mul_left_comm,←Real.rpow_add hTi]; congr 2; ring

                                                                      
                                                                             
section
variable {α : ℝ≥0} (hlo : 2/5<(α:ℝ)) (hhi : (α:ℝ)<3/7)
include α hlo hhi
theorem isExponentSumBound_refined_bourgain :
    IsExponentSumBound α (max (1/12+2*(α:ℝ)/3) (241/1164+425*(α:ℝ)/1164)) := by
  intro P T F a b _hP hT hTunbounded hPT hF hab
  let β := max (1/12+2*(α:ℝ)/3) (241/1164+425*(α:ℝ)/1164)
  apply (isPowerBounded_iff_forall_pos (exponentialSum F T P a b) T β hT hTunbounded).mpr
  pm_6438
  have hη : 0<η := lt_min (by norm_num) hε
  have hηε : η≤ε := min_le_right _ _
  have hηsmall : (13/84:ℝ)+η<1 := by
    have hh : η≤(1:ℝ)/100 := min_le_left _ _
    linarith only [hh]
  obtain ⟨hphase,σ,hσ,herror⟩ := hF
  obtain ⟨δ,κ₀,hδ,hκ₀,Q,_hQ,C₀,hC₀,hsource⟩ :=
    exists_model_refined_global_bound hσ exponentPair_bourgain hη hηsmall
  pm_8053
  have hparameters := eventually_refined_bourgain_parameters hlo hhi hσ hκ₀ hT hTunbounded hPT
  have hcost := eventually_refined_bourgain_cost hlo hhi hσ hη hT hTunbounded hPT
  let C := max 1 (3*C₀)
  pm_4909 hC C
  have hC₀C : 3*C₀≤C := le_max_right _ _
  have hCpow : C≤C^12 := by
    calc
      C=C*1 := (mul_one C).symm
      _≤C*C^11 := mul_le_mul_of_nonneg_left (one_le_pow₀ hC) (zero_le_one.trans hC)
      _=C^12 := by ring
  pm_6439
  obtain ⟨hPi,hwi,hwhalf,hUsmall,hcurve,hPU,hLsmall,hliftSmall,hlift,hκ⟩ := hpi
  have hTi : 0<T i := zero_lt_one.trans_le (hT i)
  have hs := hsource (F i) (T i) (P i) (a i) (b i) ((T i)^(-(3+23*(α:ℝ))/194))
    hFi hTi hPi (hab i).1 (hab i).2 hwi hwhalf
    hUsmall hcurve hPU hLsmall hliftSmall hlift hκ
  have hmajor := mul_le_mul_of_nonneg_left hci hC₀.le
  have hbound : ‖exponentialSumAt (F i) (T i) (P i) (a i) (b i)‖^12≤
      (3*C₀)*(T i)^(12*β+5*η) := by
    apply hs.trans
    simpa only [mul_assoc,mul_left_comm C₀ 3] using hmajor
  have hexp : 12*β+5*η≤(β+ε)*12 := by linarith only [hηε,hε]
  have hp : ‖exponentialSumAt (F i) (T i) (P i) (a i) (b i)‖^12≤
      (C*(T i)^(β+ε))^12 := by
    calc
      _≤(3*C₀)*(T i)^(12*β+5*η) := hbound
      _≤C^12*(T i)^((β+ε)*12) :=
        mul_le_mul (hC₀C.trans hCpow) (Real.rpow_le_rpow_of_exponent_le (hT i) hexp)
          (Real.rpow_nonneg hTi.le _) (by positivity)
      _=_ := by rw [mul_pow,←Real.rpow_mul_natCast hTi.le]; norm_num
  have hh := (pow_le_pow_iff_left₀ (norm_nonneg _)
    (by positivity : 0≤C*(T i)^(β+ε)) (by norm_num : (12:ℕ)≠0)).mp hp
  pm_6668

                                                                      
theorem exponentSumGrowthExponent_le_refined_bourgain :
    exponentSumGrowthExponent α ≤ max (1/12+2*(α:ℝ)/3) (241/1164+425*(α:ℝ)/1164) :=
  exponentSumGrowthExponent_le_iff.mpr (isExponentSumBound_refined_bourgain hlo hhi)
end

theorem exponentPair_trudgianYang_first :
    ExponentPair (4742/38463) (35731/51284) := by
  pm_2072
  by_cases hlo : (α:ℝ)≤403/1000
  · have hh := exponentSumGrowthExponent_le_sargosD_bourgain
      (α:=α) (by linarith only [hhalf] : (α:ℝ)≤1)
    unfold exponentPairLine at hh ⊢
    linarith only [hh,hlo]
  by_cases hhi : (α:ℝ)<3/7
  · have hh := exponentSumGrowthExponent_le_refined_bourgain
      (by linarith only [lt_of_not_ge hlo] : 2/5<(α:ℝ)) hhi
    apply hh.trans
    unfold exponentPairLine
    apply max_le <;> linarith only [lt_of_not_ge hlo,hhi]
  · have hh := exponentSumGrowthExponent_le_exponentPairLine_closed
      exponentPair_bourgain α (by linarith only [hhalf] : (α:ℝ)≤1)
    unfold exponentPairLine at hh ⊢
    linarith only [hh,le_of_not_gt hhi]

                                                             
theorem exponentPair_aTrudgianYang_first :
    ExponentPair (2371/43205) (280013/345640) := by
  have h := exponentPair_trudgianYang_first.aProcess
  norm_num at h
  exact h

                                                               
theorem exponentSumGrowthExponent_le_trudgianYang_sixthRow
    {α : ℝ≥0} (hα : (α:ℝ)≤1) :
    exponentSumGrowthExponent α ≤ 2371/43205+52209*(α:ℝ)/69128 := by
  have h := exponentSumGrowthExponent_le_exponentPairLine_closed
    exponentPair_aTrudgianYang_first α hα
  convert h using 1
  unfold exponentPairLine
  ring

end TaoTrudgianYang2025.CubicJointCount
