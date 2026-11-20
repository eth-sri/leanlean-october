module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import TaoTrudgianYang2025.FourierDecayCore
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline

public import LaterPairs.Native.SargosPlanarRegularity
public import LaterPairs.Native.SargosPlanarIntegral

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0

open MeasureTheory GafniTao Set Filter
open scoped BigOperators ComplexConjugate ContDiff Topology FourierTransform ENNReal NNReal
noncomputable section
namespace TaoTrudgianYang2025

theorem planarSum_mul {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (z : ι → ℂ) (w : κ → ℂ)
    (u v : ι → ℝ) (p q : κ → ℝ) (α γ : ℝ) :
    sargosPlanarSum S z u v α γ * sargosPlanarSum T w p q α γ =
      sargosPlanarSum (S ×ˢ T) (fun i => z i.1*w i.2)
        (fun i => u i.1+p i.2) (fun i => v i.1+q i.2) α γ := by
  unfold sargosPlanarSum
  rw [Finset.sum_mul_sum,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = (z i*w j)*(fordAdditiveCharacter (u i*α+v i*γ)*
        fordAdditiveCharacter (p j*α+q j*γ)) := by ring
    _ = _ := by
      rw [← fordAdditiveCharacter_add]
      congr 2
      ring

private theorem banded_real_sum_le (J : Finset ℤ) (G : ℤ → ℤ → ℝ)
    (E : ℤ → ℝ) (m : ℕ)
    (hE : ∀ i ∈ J, 0 ≤ E i)
    (hG : ∀ i ∈ J, ∀ j ∈ J, 2*G i j ≤ E i+E j)
    (hzero : ∀ i ∈ J, ∀ j ∈ J, (m : ℤ) < |i-j| → G i j = 0) :
    ∑ i ∈ J, ∑ j ∈ J, G i j ≤ (2*(m : ℝ)+1)*∑ i ∈ J, E i := by
  classical
  have hcard (i : ℤ) : ((J.filter (fun j => |i-j| ≤ (m : ℤ))).card : ℝ) ≤
      2*(m : ℝ)+1 := by
    have hs : J.filter (fun j => |i-j| ≤ (m : ℤ)) ⊆
        Finset.Icc (i-(m : ℤ)) (i+(m : ℤ)) := by
      intro j hj
      have hj' := abs_le.mp (Finset.mem_filter.mp hj).2
      apply Finset.mem_Icc.mpr
      constructor <;> omega
    have hn : (J.filter (fun j => |i-j| ≤ (m : ℤ))).card ≤ 2*m+1 := by
      calc
        _ ≤ (Finset.Icc (i-(m : ℤ)) (i+(m : ℤ))).card := Finset.card_le_card hs
        _ = 2*m+1 := by rw [Int.card_Icc]; omega
    exact_mod_cast hn
  let A : ℤ → ℤ → ℝ := fun i j => if |i-j| ≤ (m : ℤ) then E i else 0
  have ha : (∑ i ∈ J, ∑ j ∈ J, A i j) ≤
      (2*(m : ℝ)+1)*∑ i ∈ J, E i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    calc
      _ = ((J.filter (fun j => |i-j| ≤ (m : ℤ))).card : ℝ)*E i := by
        dsimp [A]
        rw [← Finset.sum_filter]
        simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (hcard i) (hE i hi)
  have hab : 2*(∑ i ∈ J, ∑ j ∈ J, G i j) ≤
      (∑ i ∈ J, ∑ j ∈ J, A i j)+(∑ i ∈ J, ∑ j ∈ J, A j i) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    dsimp [A]
    rw [abs_sub_comm j i]
    by_cases h : |i-j| ≤ (m : ℤ)
    · simp only [ite_eq_left h]
      exact hG i hi j hj
    · simp only [ite_eq_right h,hzero i hi j hj (lt_of_not_ge h),mul_zero,add_zero,le_refl]
  have hswap : (∑ i ∈ J, ∑ j ∈ J, A j i) = ∑ i ∈ J, ∑ j ∈ J, A i j :=
    Finset.sum_comm
  rw [hswap] at hab
  linarith

private theorem weighted_family_banded (J : Finset ℤ)
    (F : ℤ → (ℝ × ℝ) → ℂ) (W : (ℝ × ℝ) → ℝ) (m : ℕ)
    (hW : ∀ p, 0 ≤ W p)
    (hi : ∀ i ∈ J, ∀ j ∈ J, Integrable (fun p => (W p : ℂ)*F i p*conj (F j p)))
    (hz : ∀ i ∈ J, ∀ j ∈ J, (m : ℤ) < |i-j| →
      (∫ p, (W p : ℂ)*F i p*conj (F j p)) = 0) :
    (∫ p, W p*‖∑ i ∈ J, F i p‖^2) ≤
      (2*(m : ℝ)+1)*∑ i ∈ J, ∫ p, W p*‖F i p‖^2 := by
  classical
  have hself (i : ℤ) (p : ℝ × ℝ) :
      (W p : ℂ)*F i p*conj (F i p) = (W p*‖F i p‖^2 : ℝ) := by
    rw [mul_assoc,Complex.mul_conj']
    push_cast
    ring
  have hdiag (i : ℤ) (hiJ : i ∈ J) : Integrable (fun p => W p*‖F i p‖^2) := by
    apply (Integrable.iff_ofReal (𝕜:=ℂ)).mpr
    convert (hi i hiJ i hiJ) using 1
    funext p
    exact (hself i p).symm
  have hexpand (p : ℝ × ℝ) :
      (W p*‖∑ i ∈ J, F i p‖^2 : ℝ) =
        ∑ i ∈ J, ∑ j ∈ J, (W p : ℂ)*F i p*conj (F j p) := by
    rw [Complex.ofReal_mul,Complex.ofReal_pow,← Complex.mul_conj']
    rw [map_sum,Finset.sum_mul_sum]
    simp only [Finset.mul_sum,mul_assoc]
  have he : ((∫ p, W p*‖∑ i ∈ J, F i p‖^2 : ℝ) : ℂ) =
      ∑ i ∈ J, ∑ j ∈ J, ∫ p, (W p : ℂ)*F i p*conj (F j p) := by
    rw [← integral_complex_ofReal]
    simp_rw [hexpand]
    rw [integral_finsetSum J (fun i hiJ =>
      integrable_finsetSum J (fun j hj => hi i hiJ j hj))]
    apply Finset.sum_congr rfl
    intro i hiJ
    exact integral_finsetSum J (hi i hiJ)
  have hre := congrArg Complex.re he
  simp only [Complex.ofReal_re,Complex.re_sum] at hre
  rw [hre]
  apply banded_real_sum_le
  · intro i hiJ
    exact integral_nonneg (fun p => mul_nonneg (hW p) (sq_nonneg _))
  · intro i hiJ j hj
    have hpoint (p : ℝ × ℝ) :
        2*((W p : ℂ)*F i p*conj (F j p)).re ≤
          W p*‖F i p‖^2+W p*‖F j p‖^2 := by
      have hn : (F i p*conj (F j p)).re ≤ ‖F i p‖*‖F j p‖ := by
        simpa only [norm_mul,Complex.norm_conj] using
          Complex.re_le_norm (F i p*conj (F j p))
      have hc : 2*(F i p*conj (F j p)).re ≤ ‖F i p‖^2+‖F j p‖^2 := by
        nlinarith [sq_nonneg (‖F i p‖-‖F j p‖)]
      have hm := mul_le_mul_of_nonneg_left hc (hW p)
      rw [mul_assoc,Complex.re_ofReal_mul]
      nlinarith only [hm]
    have hre' : (∫ p, (W p : ℂ)*F i p*conj (F j p)).re =
        ∫ p, ((W p : ℂ)*F i p*conj (F j p)).re :=
      (integral_re (hi i hiJ j hj)).symm
    rw [hre',← integral_const_mul,← integral_add (hdiag i hiJ) (hdiag j hj)]
    exact integral_mono ((hi i hiJ j hj).re.const_mul 2)
      ((hdiag i hiJ).add (hdiag j hj)) hpoint
  · intro i hiJ j hj hij
    rw [hz i hiJ j hj hij]
    rfl

private theorem rapidCross_expand {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (z : ι → ℂ) (z' : κ → ℂ)
    (u v : ι → ℝ) (u' v' : κ → ℝ) (W α γ : ℝ) :
    (W : ℂ)*sargosPlanarSum S z u v α γ*
      conj (sargosPlanarSum T z' u' v' α γ) =
      ∑ ij ∈ S ×ˢ T, (z ij.1*conj (z' ij.2))*
        ((W : ℂ)*fordAdditiveCharacter
          ((u ij.1-u' ij.2)*α+(v ij.1-v' ij.2)*γ)) := by
  unfold sargosPlanarSum
  rw [map_sum,mul_assoc,Finset.sum_mul_sum,Finset.sum_product]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul,conj_fordAdditiveCharacter]
  calc
    _ = (z i*conj (z' j))*((W : ℂ)*
      (fordAdditiveCharacter (u i*α+v i*γ)*fordAdditiveCharacter (-(u' j*α+v' j*γ)))) := by ring
    _ = _ := by
      rw [← fordAdditiveCharacter_add]
      congr 3
      ring

def parabolaBandGauge (ξ κ : ℝ) : ℝ := max |κ| |κ-2*ξ|

theorem parabolaBandGauge_nonneg (ξ κ : ℝ) : 0 ≤ parabolaBandGauge ξ κ :=
  le_trans (abs_nonneg _) (le_max_left _ _)

theorem parabolaBandGauge_slope_le {a : ℝ} (ha : a ∈ Icc 0 1) (ξ κ : ℝ) :
    |κ-2*a*ξ| ≤ parabolaBandGauge ξ κ := by
  have heq : κ-2*a*ξ = (1-a)*κ+a*(κ-2*ξ) := by ring
  rw [heq]
  calc
    _ ≤ |(1-a)*κ|+|a*(κ-2*ξ)| := abs_add_le _ _
    _ = (1-a)*|κ|+a*|κ-2*ξ| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (by linarith [ha.2] : 0 ≤ 1-a),abs_of_nonneg ha.1]
    _ ≤ (1-a)*parabolaBandGauge ξ κ+a*parabolaBandGauge ξ κ :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith [ha.2]))
        (mul_le_mul_of_nonneg_left (le_max_right _ _) ha.1)
    _ = _ := by ring

private theorem band_weighted_integrable {f : ℝ × ℝ → ℂ} {W : ℝ × ℝ → ℝ}
    (hf : Continuous f) (hW : Integrable W) {M : ℝ} (hM : ∀ p, ‖f p‖ ≤ M) :
    Integrable (fun p : ℝ × ℝ => (W p : ℂ)*f p) := by
  have hw : Integrable (fun p : ℝ × ℝ => (W p : ℂ)) := hW.ofReal
  exact hw.mul_bdd hf.aestronglyMeasurable (Filter.Eventually.of_forall hM)

private theorem bandCross_integrable {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (z : ι → ℂ) (z' : κ → ℂ)
    (u v : ι → ℝ) (u' v' : κ → ℝ) {W : ℝ × ℝ → ℝ} (hW : Integrable W) :
    Integrable (fun p : ℝ × ℝ => (W p : ℂ)*
      sargosPlanarSum S z u v p.1 p.2*conj (sargosPlanarSum T z' u' v' p.1 p.2)) := by
  have hf : Continuous (fun p : ℝ × ℝ =>
      sargosPlanarSum S z u v p.1 p.2*conj (sargosPlanarSum T z' u' v' p.1 p.2)) := by
    unfold sargosPlanarSum fordAdditiveCharacter
    fun_prop
  have hn (p : ℝ × ℝ) :
      ‖sargosPlanarSum S z u v p.1 p.2*conj (sargosPlanarSum T z' u' v' p.1 p.2)‖ ≤
        (∑ i ∈ S, ‖z i‖)*(∑ j ∈ T, ‖z' j‖) := by
    rw [norm_mul,Complex.norm_conj]
    exact mul_le_mul (norm_sargosPlanarSum_le_sum_norm S z u v p.1 p.2)
      (norm_sargosPlanarSum_le_sum_norm T z' u' v' p.1 p.2)
      (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  simpa only [mul_assoc] using band_weighted_integrable hf hW hn

private theorem bandCharacter_integrable {W : ℝ × ℝ → ℝ} (hW : Integrable W)
    (u v : ℝ) :
    Integrable (fun p : ℝ × ℝ => (W p : ℂ)*fordAdditiveCharacter (u*p.1+v*p.2)) :=
  band_weighted_integrable (by unfold fordAdditiveCharacter; fun_prop) hW
    (fun p => (sargos_character_norm _).le)

theorem sargosWeightedPlanarFamily_banded_bound {ι : Type*}
    (J : Finset ℤ) (S : ℤ → Finset ι)
    (z : ℤ → ι → ℂ) (u v : ℤ → ι → ℝ)
    (W : ℝ × ℝ → ℝ) (hW₀ : ∀ p, 0≤W p) (hW : Integrable W) (m : ℕ)
    (hzero : ∀ i∈J, ∀ j∈J, (m : ℤ) < |i-j| → ∀ s∈S i, ∀ t∈S j,
      (∫ p : ℝ × ℝ, (W p : ℂ)*fordAdditiveCharacter
        ((u i s-u j t)*p.1+(v i s-v j t)*p.2))=0) :
    (∫ p : ℝ × ℝ, W p*‖sargosPlanarSum (J.sigma S)
      (fun ij => z ij.1 ij.2) (fun ij => u ij.1 ij.2) (fun ij => v ij.1 ij.2) p.1 p.2‖^2)≤
      (2*(m : ℝ)+1)*∑ i∈J, ∫ p : ℝ × ℝ,
        W p*‖sargosPlanarSum (S i) (z i) (u i) (v i) p.1 p.2‖^2 := by
  have hz : ∀ i∈J, ∀ j∈J, (m : ℤ) < |i-j| →
      (∫ p : ℝ × ℝ, (W p : ℂ)*sargosPlanarSum (S i) (z i) (u i) (v i) p.1 p.2*
        conj (sargosPlanarSum (S j) (z j) (u j) (v j) p.1 p.2))=0 := by
    intro i hi j hj hij
    simp_rw [rapidCross_expand]
    rw [integral_finsetSum (S i ×ˢ S j) (fun st _ =>
      (bandCharacter_integrable hW (u i st.1-u j st.2) (v i st.1-v j st.2)).const_mul _)]
    apply Finset.sum_eq_zero
    intro st hst
    have hs := Finset.mem_product.mp hst
    rw [integral_const_mul,hzero i hi j hj hij st.1 hs.1 st.2 hs.2,mul_zero]
  have h := weighted_family_banded J
    (fun i p => sargosPlanarSum (S i) (z i) (u i) (v i) p.1 p.2) W m hW₀
    (fun i _ j _ => bandCross_integrable (S i) (S j) (z i) (z j)
      (u i) (v i) (u j) (v j) hW) hz
  simpa only [sargosPlanarSum,Finset.sum_sigma] using h

private theorem add_sixth_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a+b)^6 ≤ 64*(a^6+b^6) := by
  rcases le_total a b with h | h
  · have hs := pow_le_pow_left₀ (by positivity : 0 ≤ a+b)
      (show a+b ≤ 2*b by linarith) 6
    nlinarith only [hs,pow_nonneg ha 6]
  · have hs := pow_le_pow_left₀ (by positivity : 0 ≤ a+b)
      (show a+b ≤ 2*a by linarith) 6
    nlinarith only [hs,pow_nonneg hb 6]

public  theorem near_grid_interval_card (J : Finset ℤ) (i : ℤ) :
    ((J.filter (fun j => |i-j| ≤ 3)).card : ℝ) ≤ 7 := by
  have hs : J.filter (fun j => |i-j| ≤ 3) ⊆ Finset.Icc (i-3) (i+3) := by
    intro j hj
    have hh := abs_le.mp (Finset.mem_filter.mp hj).2
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  have hc : (J.filter (fun j => |i-j| ≤ 3)).card ≤ 7 := by
    calc
      _ ≤ (Finset.Icc (i-3) (i+3)).card := Finset.card_le_card hs
      _ = 7 := by rw [Int.card_Icc]; omega
  exact_mod_cast hc

theorem weighted_decoupling_pointwise (J : Finset ℤ) (f : ℤ → ℂ) :
    ‖∑ i ∈ J, f i‖^6 ≤
      (64*7^6:ℝ)*∑ i ∈ J, ‖f i‖^6 +
      64*(J.card:ℝ)^5*
        ∑ i ∈ J, ∑ j ∈ J.filter (fun j => 3 < |i-j|), ‖f j‖^2*‖f i‖^4 := by
  classical
  rcases J.eq_empty_or_nonempty with rfl | hJ
  · simp
  obtain ⟨i,hi,hmax⟩ := J.exists_max_image (fun j => ‖f j‖) hJ
  let K := J.filter (fun j => |i-j| ≤ 3)
  let L := J.filter (fun j => 3 < |i-j|)
  let A := ∑ j ∈ K, ‖f j‖
  let B := ∑ j ∈ L, ‖f j‖
  let M := ‖f i‖
  let n := (J.card:ℝ)
  have hM : 0 ≤ M := norm_nonneg _
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hK : (K.card:ℝ) ≤ 7 := near_grid_interval_card J i
  have hL : (L.card:ℝ) ≤ n := by
    dsimp only [L,n]
    exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun j => 3 < |i-j|) J)
  have hnear : A ≤ 7*M := by
    calc
      A ≤ ∑ _j ∈ K, M := Finset.sum_le_sum fun j hj => hmax j (Finset.mem_filter.mp hj).1
      _ = (K.card:ℝ)*M := by simp
      _ ≤ 7*M := mul_le_mul_of_nonneg_right hK hM
  have hfar : B ≤ n*M := by
    calc
      B ≤ ∑ _j ∈ L, M := Finset.sum_le_sum fun j hj => hmax j (Finset.mem_filter.mp hj).1
      _ = (L.card:ℝ)*M := by simp
      _ ≤ n*M := mul_le_mul_of_nonneg_right hL hM
  have hfar₂ : B^2 ≤ n*∑ j ∈ L, ‖f j‖^2 :=
    (sq_sum_le_card_mul_sum_sq (s:=L) (f:=fun j => ‖f j‖)).trans
      (mul_le_mul_of_nonneg_right hL (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hfar₆ : B^6 ≤ n^5*∑ j ∈ L, ‖f j‖^2*M^4 := by
    calc
      B^6 = B^4*B^2 := by ring
      _ ≤ (n*M)^4*(n*∑ j ∈ L, ‖f j‖^2) :=
        mul_le_mul (pow_le_pow_left₀ hB hfar 4) hfar₂ (sq_nonneg B) (by positivity)
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hdiag : M^6 ≤ ∑ j ∈ J, ‖f j‖^6 :=
    Finset.single_le_sum (fun j _ => pow_nonneg (norm_nonneg _) 6) hi
  have hcross : (∑ j ∈ L, ‖f j‖^2*M^4) ≤
      ∑ k ∈ J, ∑ j ∈ J.filter (fun j => 3 < |k-j|), ‖f j‖^2*‖f k‖^4 :=
by
    dsimp only [L,M]
    exact Finset.single_le_sum (f := fun k =>
      ∑ j ∈ J.filter (fun j => 3 < |k-j|), ‖f j‖^2*‖f k‖^4)
      (fun k _ => Finset.sum_nonneg fun j _ => by positivity) hi
  have hsplit : (∑ j ∈ J, ‖f j‖) = A+B := by
    dsimp [A,B,K,L]
    simpa only [not_le] using
      (Finset.sum_filter_add_sum_filter_not J (fun j => |i-j| ≤ 3) (fun j => ‖f j‖)).symm
  have hsum : ‖∑ j ∈ J, f j‖ ≤ A+B := by
    rw [← hsplit]
    exact norm_sum_le _ _
  have hnear₆ : A^6 ≤ 7^6*M^6 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hA hnear 6
  calc
    _ ≤ (A+B)^6 := pow_le_pow_left₀ (norm_nonneg _) hsum 6
    _ ≤ 64*(A^6+B^6) := add_sixth_le A B hA hB
    _ ≤ 64*(7^6*M^6+n^5*∑ j ∈ L, ‖f j‖^2*M^4) := by
      gcongr
    _ ≤ _ := by
      dsimp only [n]
      have hd := mul_le_mul_of_nonneg_left hdiag (by positivity : (0:ℝ) ≤ 64*7^6)
      have hc := mul_le_mul_of_nonneg_left hcross (by positivity : (0:ℝ) ≤ 64*(J.card:ℝ)^5)
      nlinarith only [hd,hc]

def parabolaDyadicBilinearBudget (D : ℕ → ℝ) (n r : ℕ) : ℕ → ℕ → ℕ → ℝ
  | 0,a,b => (D (n-a))^2*(D (n-b))^4
  | t+1,_,b => (7/(1/(2:ℝ)^r))*
      (Real.sqrt (parabolaDyadicBilinearBudget D n r t b (2*b))*(D (n-b))^3)

private theorem two_rpow_product (C x y : ℝ) (m k : ℕ) :
    (C*(2:ℝ)^x)^m*(C*(2:ℝ)^y)^k =
      C^(m+k)*(2:ℝ)^(x*m+y*k) := by
  rw [Real.rpow_add (by norm_num), Real.rpow_mul_natCast (by norm_num),
    Real.rpow_mul_natCast (by norm_num), pow_add]
  ring

theorem parabolaDyadicBilinearBudget_exponential {C ε : ℝ} (hC : 0 ≤ C)
    {n r a b t : ℕ} (ht : 1 ≤ t) (hb : b*2^t ≤ n) :
    parabolaDyadicBilinearBudget (fun j => C*(2:ℝ)^(ε*j)) n r t a b ≤
      49*C^6*(2:ℝ)^(6*ε*n-(3*(t:ℝ)+5)*ε*b+2*r) := by
  obtain ⟨s,rfl⟩ := Nat.exists_eq_add_of_le ht
  induction s generalizing a b with
  | zero =>
    have hb₂ : 2*b ≤ n := by simpa [mul_comm] using hb
    have hb₁ : b ≤ n := by omega
    have hx : 0 ≤ C*(2:ℝ)^(ε*((n-b:ℕ):ℝ)) := by positivity
    have hy : 0 ≤ C*(2:ℝ)^(ε*((n-2*b:ℕ):ℝ)) := by positivity
    simp only [Nat.add_zero,parabolaDyadicBilinearBudget]
    rw [show (C*(2:ℝ)^(ε*((n-b:ℕ):ℝ)))^2*
        (C*(2:ℝ)^(ε*((n-2*b:ℕ):ℝ)))^4 =
        ((C*(2:ℝ)^(ε*((n-b:ℕ):ℝ)))*
          (C*(2:ℝ)^(ε*((n-2*b:ℕ):ℝ)))^2)^2 by ring,
      Real.sqrt_sq (by positivity)]
    have hp := two_rpow_product C (ε*((n-b:ℕ):ℝ))
      (ε*((n-2*b:ℕ):ℝ)) 4 2
    simp only [Nat.cast_sub hb₁,Nat.cast_sub hb₂,Nat.cast_mul,Nat.cast_ofNat] at hp ⊢
    have he : (ε*((n:ℝ)-b))*4+(ε*((n:ℝ)-2*b))*2 =
        6*ε*n-8*ε*b := by ring
    norm_num only [show (4+2:ℕ)=6 by omega] at hp
    rw [he] at hp
    have hmain :
        7/(1/(2:ℝ)^r)*
          (C*(2:ℝ)^(ε*((n:ℝ)-b))*
            (C*(2:ℝ)^(ε*((n:ℝ)-2*b)))^2*
              (C*(2:ℝ)^(ε*((n:ℝ)-b)))^3) =
        7*(2:ℝ)^r*(C^6*(2:ℝ)^(6*ε*n-8*ε*b)) := by
      rw [div_div_eq_mul_div,div_one]
      calc
        _ = 7*(2:ℝ)^r*((C*(2:ℝ)^(ε*((n:ℝ)-b)))^4*
          (C*(2:ℝ)^(ε*((n:ℝ)-2*b)))^2) := by ring
        _ = _ := by rw [hp]
    rw [hmain]
    have hrpow : (2:ℝ)^r ≤ (2:ℝ)^(2*(r:ℝ)) := by
      rw [←Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r; linarith)
    have he' : 6*ε*n-(3*(1:ℝ)+5)*ε*b+2*r =
        (6*ε*n-8*ε*b)+2*r := by ring
    simp only [Nat.cast_one]
    rw [he',Real.rpow_add (by norm_num)]
    have hmul := mul_le_mul_of_nonneg_right hrpow
      (show 0 ≤ C^6*(2:ℝ)^(6*ε*n-8*ε*b) by positivity)
    nlinarith [mul_nonneg (show 0 ≤ C^6*(2:ℝ)^(6*ε*n-8*ε*b) by positivity)
      (show 0 ≤ (2:ℝ)^(2*(r:ℝ)) by positivity)]
  | succ s ih =>
    have hp : (1:ℕ) ≤ 2^(1+s) := Nat.succ_le_iff.mpr (by positivity)
    have he : (2*b)*2^(1+s)=b*2^(1+(s+1)) := by
      rw [show 1+(s+1)=(1+s)+1 by omega,pow_succ]; ring
    have hbnext : (2*b)*2^(1+s) ≤ n := by rw [he]; exact hb
    have hb₂ : 2*b ≤ n :=
      (show 2*b ≤ (2*b)*2^(1+s) by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (Nat.zero_le (2*b))).trans hbnext
    have hb₁ : b ≤ n := by omega
    have hprev := ih (a:=b) (by omega) hbnext
    have hsquare :
        (7*C^3*(2:ℝ)^(3*ε*n-(3*((1+s:ℕ):ℝ)+5)*ε*b+r))^2 =
        49*C^6*(2:ℝ)^(6*ε*n-(3*((1+s:ℕ):ℝ)+5)*ε*(2*b)+2*r) := by
      rw [mul_pow,mul_pow,←pow_mul,←Real.rpow_mul_natCast (by norm_num)]
      norm_num only [show (3*2:ℕ)=6 by omega,show (7:ℝ)^2=49 by norm_num,Nat.cast_ofNat]
      congr 1
      congr 1
      ring
    have hsqrt : Real.sqrt
        (parabolaDyadicBilinearBudget (fun j => C*(2:ℝ)^(ε*j)) n r (1+s) b (2*b)) ≤
        7*C^3*(2:ℝ)^(3*ε*n-(3*((1+s:ℕ):ℝ)+5)*ε*b+r) := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity,?_⟩
      rw [hsquare]
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using hprev
    rw [show 1+(s+1)=(1+s)+1 by omega,parabolaDyadicBilinearBudget]
    calc
      _ ≤ (7/(1/(2:ℝ)^r))*
          ((7*C^3*(2:ℝ)^(3*ε*n-(3*((1+s:ℕ):ℝ)+5)*ε*b+r))*
            (C*(2:ℝ)^(ε*((n-b:ℕ):ℝ)))^3) := by
        gcongr
      _ = _ := by
        rw [div_div_eq_mul_div,div_one,mul_pow,←Real.rpow_mul_natCast (by norm_num)]
        rw [←Real.rpow_natCast (2:ℝ) r]
        simp only [Nat.cast_sub hb₁,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
        have he' : 6*ε*n-(3*(1+(s:ℝ)+1)+5)*ε*b+2*r =
            (r:ℝ)+(3*ε*n-(3*(1+s:ℝ)+5)*ε*b+r)+(ε*((n:ℝ)-b))*3 := by ring
        rw [he']
        conv_rhs =>
          rw [Real.rpow_add (by norm_num),Real.rpow_add (by norm_num)]
        ring

namespace LogarithmicSixth
universe u

def logQuadraticError (x : ℝ) : ℝ := Real.log (1+x)-x+x^2/2

private theorem analyticAt_dslope_zero {f : ℝ → ℝ} {x : ℝ}
    (hzero : AnalyticAt ℝ f 0) (hx : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (dslope f 0) x := by
  by_cases h : x=0
  · subst x
    obtain ⟨p,hp⟩ := hzero
    exact ⟨p.fslope,hp.has_fpower_series_dslope_fslope⟩
  · have hq : AnalyticAt ℝ (fun y => y⁻¹*(f y-f 0)) x :=
      (analyticAt_id.inv h).mul (hx.sub analyticAt_const)
    apply hq.congr
    filter_upwards [eventually_ne_nhds h] with y hy
    simp [dslope_of_ne _ hy,slope_def_field,div_eq_inv_mul]

theorem logQuadraticError_analytic {x : ℝ} (hx : -1<x) :
    AnalyticAt ℝ logQuadraticError x := by
  unfold logQuadraticError
  exact (((analyticAt_const.add analyticAt_id).log (by change 0<1+x; linarith)).sub
    analyticAt_id).add ((analyticAt_id.pow 2).div analyticAt_const (by norm_num))

theorem logQuadraticError_cubic_bound {x : ℝ} (hx : |x|≤1/2) :
    |logQuadraticError x|≤2*|x|^3 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -x)
    (by rw [abs_neg]; linarith) 2
  norm_num [Finset.sum_range_succ] at h
  have he : -x+x^2/2+Real.log (1+x)=logQuadraticError x := by
    unfold logQuadraticError
    ring
  rw [he] at h
  apply h.trans
  apply (div_le_iff₀ (by linarith : 0<1-|x|)).mpr
  nlinarith [pow_nonneg (abs_nonneg x) 3]

private theorem logQuadraticError_zero : logQuadraticError 0=0 := by
  simp [logQuadraticError]

private theorem logQuadraticError_deriv_zero : deriv logQuadraticError 0=0 := by
  have h := ((((hasDerivAt_id (0:ℝ)).const_add 1).log (by norm_num)).sub
    (hasDerivAt_id 0)).add (((hasDerivAt_id 0).pow 2).div_const 2)
  have hh : HasDerivAt logQuadraticError 0 0 := by
    convert h using 1
    · rfl
    · norm_num
  exact hh.deriv

private theorem logQuadraticError_second_slope_zero :
    dslope (dslope logQuadraticError 0) 0 0=0 := by
  rw [dslope_same]
  apply HasDerivAt.deriv
  rw [hasDerivAt_iff_tendsto_slope]
  have hlim : Tendsto (fun x : ℝ => 2*|x|) (𝓝[≠] 0) (𝓝 0) := by
    have hc : Continuous (fun x : ℝ => 2*|x|) := continuous_const.mul continuous_abs
    simpa only [abs_zero,mul_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply squeeze_zero_norm' _ hlim
  have hsmall : ∀ᶠ x : ℝ in 𝓝[≠] 0, |x|≤1/2 := by
    have h : ∀ᶠ x : ℝ in 𝓝 0, |x|<1/2 :=
      (continuous_abs.tendsto 0).eventually
        (Iio_mem_nhds (by norm_num : |(0:ℝ)|<1/2))
    exact (h.filter_mono nhdsWithin_le_nhds).mono fun _ hh => hh.le
  filter_upwards [hsmall,self_mem_nhdsWithin] with x hx hne
  have hxne : x≠0 := hne
  rw [slope_def_field,dslope_same,logQuadraticError_deriv_zero,
    dslope_of_ne _ hxne,slope_def_field,logQuadraticError_zero]
  simp only [sub_zero,Real.norm_eq_abs,abs_div]
  have hp : 0 < |x| := abs_pos.mpr hxne
  have hb := logQuadraticError_cubic_bound hx
  calc
    |logQuadraticError x|/|x|/|x| ≤ (2*|x|^3)/|x|/|x| := by gcongr
    _ = 2*|x| := by field_simp

def logCubicProfile : ℝ → ℝ :=
  dslope (dslope (dslope logQuadraticError 0) 0) 0

                                                                         
theorem logCubicProfile_analytic {x : ℝ} (hx : -1<x) :
    AnalyticAt ℝ logCubicProfile x := by
  have h0 := logQuadraticError_analytic (x:=0) (by norm_num)
  have h1 := analyticAt_dslope_zero h0 h0
  have h2 := analyticAt_dslope_zero h1 h1
  exact analyticAt_dslope_zero h2
    (analyticAt_dslope_zero h1 (analyticAt_dslope_zero h0 (logQuadraticError_analytic hx)))

                                                                          
theorem logCubicProfile_identity (x : ℝ) :
    x^3*logCubicProfile x=Real.log (1+x)-x+x^2/2 := by
  have h1 := sub_smul_dslope logQuadraticError 0 x
  have h2 := sub_smul_dslope (dslope logQuadraticError 0) 0 x
  have h3 := sub_smul_dslope (dslope (dslope logQuadraticError 0) 0) 0 x
  simp only [sub_zero,smul_eq_mul,logQuadraticError_zero,dslope_same,
    logQuadraticError_deriv_zero] at h1 h2
  rw [logQuadraticError_second_slope_zero] at h3
  simp only [sub_zero,smul_eq_mul] at h3
  change x*logCubicProfile x=dslope (dslope logQuadraticError 0) 0 x at h3
  calc
    _ = x*(x*(x*logCubicProfile x)) := by ring
    _ = logQuadraticError x := by rw [h3,h2,h1]
    _ = _ := rfl

def smoothLogCubicProfile (x : ℝ) : ℝ :=
  modelPhaseBufferedCutoff (-1) 1 (1/4) x*logCubicProfile x

theorem smoothLogCubicProfile_smooth : ContDiff ℝ ∞ smoothLogCubicProfile := by
  apply smoothCutoff_mul_contDiff (modelPhaseBufferedCutoff_contDiff _ _ _)
  intro x hx
  have hs := modelPhaseBufferedCutoff_tsupport (by norm_num : (0:ℝ)<1/4) hx
  exact (logCubicProfile_analytic (by linarith [hs.1])).contDiffAt

theorem smoothLogCubicProfile_agrees {x : ℝ} (hx : |x|≤1/2) :
    smoothLogCubicProfile x=logCubicProfile x := by
  unfold smoothLogCubicProfile
  rw [modelPhaseBufferedCutoff_one (by norm_num)
    (by linarith [(abs_le.mp hx).1]) (by linarith [(abs_le.mp hx).2]),one_mul]

def logCurve (κ s : ℝ) : ℝ := s^2-2*κ*s^3*logCubicProfile (κ*s)

@[simp] theorem logCurve_zero (s : ℝ) : logCurve 0 s = s^2 := by simp [logCurve]

theorem logCurve_identity (κ s : ℝ) :
    κ^2*logCurve κ s=2*(κ*s-Real.log (1+κ*s)) := by
  have h := logCubicProfile_identity (κ*s)
  unfold logCurve
  nlinarith only [h]

private theorem logCurve_eq_log {κ : ℝ} (hκ : κ≠0) (s : ℝ) :
    logCurve κ s=2*(κ*s-Real.log (1+κ*s))/κ^2 := by
  apply (eq_div_iff (pow_ne_zero 2 hκ)).mpr
  simpa only [mul_comm] using logCurve_identity κ s

                                                                        
                                                                 
theorem logCurve_rescaling (κ a h s : ℝ)
    (ha : 0<1+κ*a) (hs : 0<1+κ*(a+h*s)) :
    logCurve κ (a+h*s)=logCurve κ a+(2*a*h/(1+κ*a))*s+
      (h^2/(1+κ*a)^2)*logCurve (κ*h/(1+κ*a)) s := by
  by_cases hκ : κ=0
  · subst κ
    simp [logCurve]
    ring
  by_cases hh : h=0
  · subst h
    simp
  have hnew : κ*h/(1+κ*a)≠0 := div_ne_zero (mul_ne_zero hκ hh) ha.ne'
  have hfactor : 1+κ*(a+h*s)=(1+κ*a)*(1+(κ*h/(1+κ*a))*s) := by
    field_simp
    ring
  have hright : 0<1+(κ*h/(1+κ*a))*s := by
    rw [hfactor] at hs
    exact (mul_pos_iff_of_pos_left ha).mp hs
  have hlog : Real.log (1+κ*(a+h*s))=
      Real.log (1+κ*a)+Real.log (1+(κ*h/(1+κ*a))*s) := by
    rw [hfactor,Real.log_mul ha.ne' hright.ne']
  rw [logCurve_eq_log hκ,logCurve_eq_log hκ,logCurve_eq_log hnew,hlog]
  field_simp
  ring

theorem logCurve_hasDerivAt (κ s : ℝ) (hs : 1+κ*s≠0) :
    HasDerivAt (logCurve κ) (2*s/(1+κ*s)) s := by
  by_cases hκ : κ=0
  · subst κ
    have hz : logCurve 0=(fun x : ℝ => x^2) := by funext x; simp [logCurve]
    rw [hz]
    simpa using hasDerivAt_pow 2 s
  rw [show logCurve κ=(fun x => 2*(κ*x-Real.log (1+κ*x))/κ^2) from
    funext (logCurve_eq_log hκ)]
  have h := (((hasDerivAt_id s).const_mul κ).sub
    ((((hasDerivAt_id s).const_mul κ).const_add 1).log hs)).const_mul 2 |>.div_const (κ^2)
  convert h using 1
  · rfl
  · simp only [id_eq]
    field_simp [hs,hκ]
    have hs' : 1+s*κ ≠ 0 := by simpa only [mul_comm] using hs
    field_simp [hs']
    ring

                                                                        
theorem logCurve_rescaled_parameter {κ a h : ℝ}
    (hκ : κ∈Icc (0:ℝ) (1/4)) (ha : 0≤a) (hh : h∈Icc (0:ℝ) 1) :
    κ*h/(1+κ*a)∈Icc (0:ℝ) (1/4) := by
  have hp : 0<1+κ*a := by nlinarith [mul_nonneg hκ.1 ha]
  constructor
  · exact div_nonneg (mul_nonneg hκ.1 hh.1) hp.le
  · apply (div_le_iff₀ hp).mpr
    have hn : κ*h≤κ := by nlinarith [hκ.1,hh.2]
    nlinarith [hκ.1,hκ.2,mul_nonneg hκ.1 ha]

                                                                        
                                                                             
theorem logCurve_square_source_phase {A n κ s : ℝ}
    (hA : 0<A) (hn : 0<n) (hcoord : n^2=A^2*(1+κ*s)) (α t : ℝ) :
    α*n^2+t*Real.log n=(α*A^2+t*Real.log A)+
      (α*A^2*κ+t*κ/2)*s-(t*κ^2/4)*logCurve κ s := by
  have hq : 0<1+κ*s := by
    have h := sq_pos_of_pos hn
    rw [hcoord] at h
    exact (mul_pos_iff_of_pos_left (sq_pos_of_pos hA)).mp h
  have hlog : 2*Real.log n=2*Real.log A+Real.log (1+κ*s) := by
    have he := congrArg Real.log hcoord
    rw [Real.log_mul (pow_ne_zero 2 hA.ne') hq.ne',Real.log_pow,Real.log_pow] at he
    norm_num only [Nat.cast_ofNat] at he
    exact he
  have hc := logCurve_identity κ s
  rw [hcoord]
  linear_combination (t/2)*hlog+(t/4)*hc

                                                                            
                                                                                 
                                                                          
theorem logCurve_separated_secant {κ d u ν x y : ℝ}
    (hκ : κ∈Icc (0:ℝ) (1/4)) (hν : 0<ν) (hu : u≤ν)
    (hd : 3*ν≤|d|) (hl : -1≤d) (hr : d+u≤1)
    (hx : x∈Icc d (d+u)) (hy : y∈Icc d (d+u)) :
    2*ν*|x-y|≤|logCurve κ x-logCurve κ y| := by
  have hden (v : ℝ) (hv : v∈Icc d (d+u)) : 0<1+κ*v ∧ 1+κ*v≤2 := by
    have hv₁ : -1≤v := hl.trans hv.1
    have hv₂ : v≤1 := hv.2.trans hr
    have hlow := mul_le_mul_of_nonneg_left hv₁ hκ.1
    have hhigh := mul_le_mul_of_nonneg_left hv₂ hκ.1
    constructor <;> nlinarith [hκ.2]
  have hfar (v : ℝ) (hv : v∈Icc d (d+u)) : 2*ν≤|v| := by
    rcases le_total 0 d with hd₀|hd₀
    · rw [abs_of_nonneg hd₀] at hd
      exact (by linarith [hv.1] : 2*ν≤v).trans (le_abs_self v)
    · rw [abs_of_nonpos hd₀] at hd
      have hv₀ : v≤0 := by linarith [hv.2]
      rw [abs_of_nonpos hv₀]
      linarith [hv.2]
  have hordered (a b : ℝ) (ha : a∈Icc d (d+u)) (hb : b∈Icc d (d+u))
      (hab : a<b) : 2*ν*|b-a|≤|logCurve κ b-logCurve κ a| := by
    have hsub : Icc a b⊆Icc d (d+u) := Icc_subset_Icc ha.1 hb.2
    obtain ⟨c,hc,he⟩ := exists_hasDerivAt_eq_slope (logCurve κ)
      (fun v => 2*v/(1+κ*v)) hab
      (fun v hv => (logCurve_hasDerivAt κ v (hden v (hsub hv)).1.ne').continuousAt.continuousWithinAt)
      (fun v hv => logCurve_hasDerivAt κ v (hden v (hsub (Ioo_subset_Icc_self hv))).1.ne')
    have hcI := hsub (Ioo_subset_Icc_self hc)
    have hderiv : 2*ν≤|2*c/(1+κ*c)| := by
      apply (hfar c hcI).trans
      rw [abs_div,abs_mul,abs_of_pos (hden c hcI).1]
      rw [abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
      apply (le_div_iff₀ (hden c hcI).1).mpr
      nlinarith [mul_le_mul_of_nonneg_left (hden c hcI).2 (abs_nonneg c)]
    have he' : (2*c/(1+κ*c))*(b-a)=logCurve κ b-logCurve κ a :=
      (eq_div_iff (sub_ne_zero.mpr hab.ne')).mp he
    have hh := mul_le_mul_of_nonneg_right hderiv (abs_nonneg (b-a))
    simpa only [←abs_mul,he'] using hh
  rcases lt_trichotomy x y with hxy|hxy|hxy
  · simpa only [abs_sub_comm] using hordered x y hx hy hxy
  · subst y
    simp
  · exact hordered y x hy hx hxy

                                                                        
                                                                       
                                                                     
theorem logCurve_nonneg_le_sq {κ y : ℝ} (hκ : 0≤κ) (hy : 0≤y) :
    0≤logCurve κ y ∧ logCurve κ y≤y^2 := by
  have hp (v : ℝ) (hv : 0≤v) : 0<1+κ*v := by nlinarith [mul_nonneg hκ hv]
  have hd (v : ℝ) (hv : 0≤v) := logCurve_hasDerivAt κ v (hp v hv).ne'
  have hmono : MonotoneOn (logCurve κ) (Ici (0:ℝ)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0:ℝ))
      (fun v hv => (hd v hv).continuousAt.continuousWithinAt)
      (fun v hv => (hd v (interior_subset hv)).hasDerivWithinAt)
      (fun v hv => div_nonneg (mul_nonneg (by norm_num) (show 0≤v from interior_subset hv))
        (hp v (interior_subset hv)).le)
  have hg (v : ℝ) (hv : 0≤v) :
      HasDerivAt (fun t : ℝ => t^2-logCurve κ t) (2*v-2*v/(1+κ*v)) v := by
    convert ((hasDerivAt_id v).pow 2).sub (hd v hv) using 1
    · rfl
    · norm_num
  have hg₀ (v : ℝ) (hv : 0≤v) : 0≤2*v-2*v/(1+κ*v) := by
    have hh : 2*v/(1+κ*v)≤2*v := by
      apply (div_le_iff₀ (hp v hv)).mpr
      nlinarith [mul_nonneg hv (mul_nonneg hκ hv)]
    linarith
  have hmonog : MonotoneOn (fun t : ℝ => t^2-logCurve κ t) (Ici (0:ℝ)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0:ℝ))
      (fun v hv => (hg v hv).continuousAt.continuousWithinAt)
      (fun v hv => (hg v (interior_subset hv)).hasDerivWithinAt)
      (fun v hv => hg₀ v (interior_subset hv))
  have hz : logCurve κ 0=0 := by simp [logCurve]
  have hlow := hmono (show (0:ℝ)∈Ici (0:ℝ) by simp) hy hy
  have hupp := hmonog (show (0:ℝ)∈Ici (0:ℝ) by simp) hy hy
  change (0:ℝ)^2-logCurve κ 0≤y^2-logCurve κ y at hupp
  rw [hz] at hlow hupp
  exact ⟨hlow,by nlinarith only [hupp]⟩

theorem logCurve_sixth_frequency_gap {κ d u ν x x' y₁ y₂ y₃ y₄ w b : ℝ}
    (hκ : κ∈Icc (0:ℝ) (1/4)) (hν : 0<ν) (hu : u≤ν)
    (hd : 3*ν≤|d|) (hl : -1≤d) (hr : d+u≤1)
    (hx : x∈Icc d (d+u)) (hx' : x'∈Icc d (d+u)) (hw : 0≤w)
    (h₁ : y₁∈Icc 0 w) (h₂ : y₂∈Icc 0 w)
    (h₃ : y₃∈Icc 0 w) (h₄ : y₄∈Icc 0 w)
    (hgap : (b+2*w^2)/(2*ν) < |x-x'|) :
    b < |logCurve κ x+logCurve κ y₁+logCurve κ y₂-
      (logCurve κ x'+logCurve κ y₃+logCurve κ y₄)| := by
  have hxgap := logCurve_separated_secant hκ hν hu hd hl hr hx hx'
  have hvalue {v : ℝ} (hv : v∈Icc (0:ℝ) w) : 0≤logCurve κ v ∧ logCurve κ v≤w^2 := by
    have h := logCurve_nonneg_le_sq hκ.1 hv.1
    exact ⟨h.1,h.2.trans ((pow_le_pow_iff_left₀ hv.1 hw (by norm_num : (2:ℕ)≠0)).mpr hv.2)⟩
  have hy₁ := hvalue h₁
  have hy₂ := hvalue h₂
  have hy₃ := hvalue h₃
  have hy₄ := hvalue h₄
  by_contra! hn
  have hb := abs_le.mp hn
  have hxupper : |logCurve κ x-logCurve κ x'|≤b+2*w^2 := by
    apply abs_le.mpr
    constructor <;> linarith [hy₁.1,hy₁.2,hy₂.1,hy₂.2,hy₃.1,hy₃.2,hy₄.1,hy₄.2,hb.1,hb.2]
  have hg := (div_lt_iff₀ (by positivity : 0<2*ν)).mp hgap
  nlinarith only [hxgap,hxupper,hg]

                                                                      
                                                                             
def logCurveBandGauge (κ ξ η : ℝ) : ℝ :=
  (1+κ)^2*parabolaBandGauge (ξ/(1+κ)) η

private theorem logCurve_slope_band {κ a : ℝ} (hκ : 0≤κ) (ha : a∈Icc (0:ℝ) 1)
    (ξ η : ℝ) : |η-(2*a/(1+κ*a))*ξ|≤parabolaBandGauge (ξ/(1+κ)) η := by
  have hA : 0<1+κ*a := by nlinarith [mul_nonneg hκ ha.1]
  have hK : 0<1+κ := by linarith
  have hb : (1+κ)*a/(1+κ*a)∈Icc (0:ℝ) 1 := by
    constructor
    · exact div_nonneg (mul_nonneg hK.le ha.1) hA.le
    · apply (div_le_one hA).mpr
      nlinarith [ha.2]
  have h := parabolaBandGauge_slope_le hb (ξ/(1+κ)) η
  convert h using 1
  congr 1
  field_simp

                                                                         
                                                                                
theorem logCurveBandGauge_rescale {κ a σ : ℝ}
    (hκ : 0≤κ) (ha : 0≤a) (hσ : 0≤σ) (haσ : a+σ≤1) (ξ η : ℝ) :
    σ^2*logCurveBandGauge (κ*σ/(1+κ*a)) ξ η≤
      logCurveBandGauge κ (σ*ξ)
        ((2*a/(1+κ*a))*σ*ξ+(σ^2/(1+κ*a)^2)*η) := by
  let A := 1+κ*a
  let B := 1+κ*(a+σ)
  let k := κ*σ/A
  let V := (2*a/A)*σ*ξ+(σ^2/A^2)*η
  have hA : 0<A := by dsimp [A]; nlinarith [mul_nonneg hκ ha]
  have hB : 0<B := by dsimp [B]; nlinarith [mul_nonneg hκ (add_nonneg ha hσ)]
  have hK : 0<1+κ := by linarith
  have hk : 0≤k := div_nonneg (mul_nonneg hκ hσ) hA.le
  have hk₁ : 0<1+k := by linarith
  have h1 := logCurve_slope_band hκ (show a∈Icc (0:ℝ) 1 from ⟨ha,by linarith⟩)
    (σ*ξ) V
  have h2 := logCurve_slope_band hκ
    (show a+σ∈Icc (0:ℝ) 1 from ⟨add_nonneg ha hσ,haσ⟩) (σ*ξ) V
  have he1 : V-(2*a/(1+κ*a))*(σ*ξ)=(σ^2/A^2)*η := by dsimp [V,A]; ring
  have he2 : V-(2*(a+σ)/(1+κ*(a+σ)))*(σ*ξ)=
      (σ^2/A^2)*(η-2*(ξ/(1+k))) := by
    dsimp [V,k,A]
    field_simp
    ring
  rw [he1,abs_mul,abs_of_nonneg (by positivity : 0≤σ^2/A^2)] at h1
  rw [he2,abs_mul,abs_of_nonneg (by positivity : 0≤σ^2/A^2)] at h2
  have hlocal : (σ^2/A^2)*parabolaBandGauge (ξ/(1+k)) η≤
      parabolaBandGauge ((σ*ξ)/(1+κ)) V := by
    unfold parabolaBandGauge
    rw [mul_max_of_nonneg _ _ (by positivity : 0≤σ^2/A^2)]
    exact max_le h1 h2
  have hBA : A*(1+k)=B := by dsimp [A,B,k]; field_simp; ring
  have hBle : B≤1+κ := by dsimp [B]; nlinarith [mul_le_mul_of_nonneg_left haσ hκ]
  have hn : (1+k)^2≤(1+κ)^2/A^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hA)).mpr
    have hh := mul_self_le_mul_self hB.le hBle
    rw [←hBA] at hh
    nlinarith only [hh]
  have hc : σ^2*(1+k)^2≤(1+κ)^2*(σ^2/A^2) := by
    have hh := mul_le_mul_of_nonneg_left hn (sq_nonneg σ)
    simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh
  change σ^2*((1+k)^2*parabolaBandGauge (ξ/(1+k)) η)≤
    (1+κ)^2*parabolaBandGauge ((σ*ξ)/(1+κ)) V
  calc
    _ = (σ^2*(1+k)^2)*parabolaBandGauge (ξ/(1+k)) η := by ring
    _ ≤ ((1+κ)^2*(σ^2/A^2))*parabolaBandGauge (ξ/(1+k)) η :=
      mul_le_mul_of_nonneg_right hc (parabolaBandGauge_nonneg _ _)
    _ = (1+κ)^2*((σ^2/A^2)*parabolaBandGauge (ξ/(1+k)) η) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlocal (sq_nonneg (1+κ))

                                                                         
theorem logCurve_sum_rescale {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ) (κ a σ α γ : ℝ)
    (hσ : σ≠0) (ha : 0<1+κ*a) (hx : ∀ i∈S, 0<1+κ*x i) :
    sargosPlanarSum S z x (fun i => logCurve κ (x i)) α γ=
      fordAdditiveCharacter (a*α+logCurve κ a*γ)*
        sargosPlanarSum S z (fun i => (x i-a)/σ)
          (fun i => logCurve (κ*σ/(1+κ*a)) ((x i-a)/σ))
          (σ*α+(2*a*σ/(1+κ*a))*γ) ((σ^2/(1+κ*a)^2)*γ) := by
  unfold sargosPlanarSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show fordAdditiveCharacter (a*α+logCurve κ a*γ)*
      (z i*fordAdditiveCharacter (((x i-a)/σ)*(σ*α+(2*a*σ/(1+κ*a))*γ)+
        logCurve (κ*σ/(1+κ*a)) ((x i-a)/σ)*((σ^2/(1+κ*a)^2)*γ)))=
      z i*(fordAdditiveCharacter (a*α+logCurve κ a*γ)*
        fordAdditiveCharacter (((x i-a)/σ)*(σ*α+(2*a*σ/(1+κ*a))*γ)+
          logCurve (κ*σ/(1+κ*a)) ((x i-a)/σ)*((σ^2/(1+κ*a)^2)*γ))) by ring,
    ←fordAdditiveCharacter_add]
  congr 2
  have he : a+σ*((x i-a)/σ)=x i := by field_simp; ring
  have hc := logCurve_rescaling κ a σ ((x i-a)/σ) ha (by rw [he]; exact hx i hi)
  rw [he] at hc
  dsimp only
  rw [hc]
  field_simp
  ring

                                                                        
                                                                       
theorem logCurve_band_sixth_gap {κ x x' y₁ y₂ y₃ y₄ w a β u ν δ : ℝ}
    (hκ : κ∈Icc (0:ℝ) (1/4)) (hw : 0<w) (hν : 0<ν)
    (hβ : β∈Icc (0:ℝ) 1) (ha : 0≤a) (har : a+u≤1)
    (hwidth : δ^2≤w^2) (hu : u≤ν) (hd : 3*ν≤|a-β|)
    (hx : x∈Icc a (a+u)) (hx' : x'∈Icc a (a+u))
    (h₁ : y₁∈Icc β (β+w)) (h₂ : y₂∈Icc β (β+w))
    (h₃ : y₃∈Icc β (β+w)) (h₄ : y₄∈Icc β (β+w))
    (hgap : 2*w^2/ν≤|x-x'|) :
    δ^2≤logCurveBandGauge κ (x+y₁+y₂-(x'+y₃+y₄))
      (logCurve κ x+logCurve κ y₁+logCurve κ y₂-
        (logCurve κ x'+logCurve κ y₃+logCurve κ y₄)) := by
  let A := 1+κ*β
  let k := κ/A
  have hA : 0<A := by dsimp [A]; nlinarith [mul_nonneg hκ.1 hβ.1]
  have hk : k∈Icc (0:ℝ) (1/4) := by
    simpa only [mul_one] using logCurve_rescaled_parameter hκ hβ.1
      (show (1:ℝ)∈Icc (0:ℝ) 1 by norm_num)
  have hmem {v : ℝ} (hv : v∈Icc β (β+w)) : v-β∈Icc (0:ℝ) w :=
    ⟨by linarith [hv.1],by linarith [hv.2]⟩
  have hxp : x-β∈Icc (a-β) (a-β+u) := ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hxp' : x'-β∈Icc (a-β) (a-β+u) := ⟨by linarith [hx'.1],by linarith [hx'.2]⟩
  have hg : (δ^2+2*w^2)/(2*ν) < |(x-β)-(x'-β)| := by
    rw [show (x-β)-(x'-β)=x-x' by ring]
    have hh := (div_le_iff₀ hν).mp hgap
    apply (div_lt_iff₀ (by positivity : 0<2*ν)).mpr
    nlinarith [sq_pos_of_pos hw]
  have hgap' := logCurve_sixth_frequency_gap hk hν hu hd
    (by linarith [hβ.2] : -1≤a-β) (by linarith [hβ.1] : a-β+u≤1)
    hxp hxp' hw.le (hmem h₁) (hmem h₂) (hmem h₃) (hmem h₄) hg
  have hid (v : ℝ) (hv : 0≤v) :
      A^2*(logCurve κ v-logCurve κ β-(2*β/A)*(v-β))=logCurve k (v-β) := by
    have hp : 0<1+κ*v := by nlinarith [mul_nonneg hκ.1 hv]
    have heq : β+1*(v-β)=v := by ring
    have hh := logCurve_rescaling κ β 1 (v-β) hA (by rwa [heq])
    rw [heq] at hh
    simp only [mul_one,one_pow] at hh
    change logCurve κ v=logCurve κ β+(2*β/A)*(v-β)+(1/A^2)*logCurve k (v-β) at hh
    rw [hh]
    field_simp
    ring
  let ξ := x+y₁+y₂-(x'+y₃+y₄)
  let η := logCurve κ x+logCurve κ y₁+logCurve κ y₂-
    (logCurve κ x'+logCurve κ y₃+logCurve κ y₄)
  have he : logCurve k (x-β)+logCurve k (y₁-β)+logCurve k (y₂-β)-
      (logCurve k (x'-β)+logCurve k (y₃-β)+logCurve k (y₄-β))=
      A^2*(η-(2*β/A)*ξ) := by
    rw [←hid x (ha.trans hx.1),←hid x' (ha.trans hx'.1),
      ←hid y₁ (hβ.1.trans h₁.1),←hid y₂ (hβ.1.trans h₂.1),
      ←hid y₃ (hβ.1.trans h₃.1),←hid y₄ (hβ.1.trans h₄.1)]
    dsimp [ξ,η]
    ring
  rw [he,abs_mul,abs_of_nonneg (sq_nonneg A)] at hgap'
  have hAle : A≤1+κ := by
    dsimp [A]
    nlinarith [mul_le_mul_of_nonneg_left hβ.2 hκ.1]
  have hsquare : A^2≤(1+κ)^2 := by nlinarith [mul_self_le_mul_self hA.le hAle]
  have hbound := logCurve_slope_band hκ.1 hβ ξ η
  change δ^2≤(1+κ)^2*parabolaBandGauge (ξ/(1+κ)) η
  exact hgap'.le.trans (mul_le_mul hsquare hbound
    (abs_nonneg _) (sq_nonneg (1+κ)))

private def logCurveRescaling (κ a σ : ℝ) (hσ : σ≠0) (hA : 1+κ*a≠0) :
    (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) where
  toFun p := (σ*p.1+(2*a*σ/(1+κ*a))*p.2,(σ^2/(1+κ*a)^2)*p.2)
  invFun p := (p.1/σ-(2*a*(1+κ*a)/σ^2)*p.2,((1+κ*a)^2/σ^2)*p.2)
  left_inv p := by
    ext <;> dsimp <;> field_simp
    ring
  right_inv p := by
    ext <;> dsimp <;> field_simp
    ring
  map_add' p q := by ext <;> dsimp <;> ring
  map_smul' c p := by ext <;> dsimp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem logCurve_haar_factor (e : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) :
    ∃ c : ℝ≥0, 0<c ∧ Measure.map e (volume : Measure (ℝ × ℝ))=(c : ℝ≥0∞) • volume := by
  have : (Measure.map e (volume : Measure (ℝ × ℝ))).IsAddHaarMeasure :=
    e.isAddHaarMeasure_map volume
  exact ⟨Measure.addHaarScalarFactor (Measure.map e volume) volume,
    Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _,
    Measure.isAddLeftInvariant_eq_smul _ _⟩

theorem logCurve_rescaling_integrable
    (e : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) {W : ℝ × ℝ → ℝ} (hW : Integrable W) :
    Integrable (fun p => W (e p)) := by
  obtain ⟨c,hc,he⟩ := logCurve_haar_factor e
  apply (integrable_map_equiv e.toHomeomorph.toMeasurableEquiv W).mp
  change Integrable W (Measure.map e volume)
  rw [he]
  exact hW.smul_measure ENNReal.coe_ne_top

theorem logCurve_rescaling_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) :
    ∃ c : ℝ, 0<c ∧ ∀ f : ℝ × ℝ → F,
      (∫ p : ℝ × ℝ, f (e p))=c • ∫ p : ℝ × ℝ, f p := by
  obtain ⟨c,hc,he⟩ := logCurve_haar_factor e
  refine ⟨c,hc,fun f => ?_⟩
  calc
    (∫ p : ℝ × ℝ, f (e p))=∫ p, f p ∂Measure.map e volume :=
      (integral_map_equiv (μ:=volume) e.toHomeomorph.toMeasurableEquiv f).symm
    _ = _ := by rw [he,integral_smul_measure,ENNReal.coe_toReal]

                                                                   
                                                                            
def LogCurveWeightBand (κ δ : ℝ) (W : ℝ × ℝ → ℝ) : Prop :=
  (∀ p, 0≤W p) ∧ Integrable W ∧ ∀ ξ η : ℝ, δ^2≤logCurveBandGauge κ ξ η →
    (∫ p : ℝ × ℝ, (W p : ℂ)*fordAdditiveCharacter (ξ*p.1+η*p.2))=0

theorem LogCurveWeightBand.rescale {κ δ a σ : ℝ} {W : ℝ × ℝ → ℝ}
    (hW : LogCurveWeightBand κ δ W) (hκ : 0≤κ) (hσ : 0<σ)
    (ha : 0≤a) (haσ : a+σ≤1) :
    LogCurveWeightBand (κ*σ/(1+κ*a)) (δ/σ)
      (fun p => W (p.1/σ-(2*a*(1+κ*a)/σ^2)*p.2,((1+κ*a)^2/σ^2)*p.2)) := by
  have hA : 0<1+κ*a := by nlinarith [mul_nonneg hκ ha]
  let e := logCurveRescaling κ a σ hσ.ne' hA.ne'
  refine ⟨fun p => hW.1 _,logCurve_rescaling_integrable e.symm hW.2.1,?_⟩
  intro ξ η hgap
  obtain ⟨c,hc,hint⟩ := logCurve_rescaling_integral (F:=ℂ) e.symm
  let f := fun p : ℝ × ℝ => (W p : ℂ)*fordAdditiveCharacter (ξ*(e p).1+η*(e p).2)
  have heq : (∫ p : ℝ × ℝ,
      (W (p.1/σ-(2*a*(1+κ*a)/σ^2)*p.2,((1+κ*a)^2/σ^2)*p.2) : ℂ)*
        fordAdditiveCharacter (ξ*p.1+η*p.2))=∫ p : ℝ × ℝ, f (e.symm p) := by
    apply integral_congr_ae
    filter_upwards with p
    dsimp only [f]
    rw [e.apply_symm_apply]
    rfl
  rw [heq,hint f]
  have hg := (mul_le_mul_of_nonneg_left hgap (sq_nonneg σ)).trans
    (logCurveBandGauge_rescale hκ ha hσ.le haσ ξ η)
  have hcancel : σ^2*(δ/σ)^2=δ^2 := by field_simp
  rw [hcancel] at hg
  have hz := hW.2.2 (σ*ξ) ((2*a/(1+κ*a))*σ*ξ+(σ^2/(1+κ*a)^2)*η) hg
  have he (p : ℝ × ℝ) : ξ*(e p).1+η*(e p).2=
      (σ*ξ)*p.1+((2*a/(1+κ*a))*σ*ξ+(σ^2/(1+κ*a)^2)*η)*p.2 := by
    dsimp [e,logCurveRescaling]
    ring
  dsimp only [f]
  simp_rw [he]
  rw [hz,smul_zero]

                                                                        
                                                                          
def logCurveWeightedBilinearMoment {ι τ : Type*}
    (κ : ℝ) (W : ℝ × ℝ → ℝ) (S : Finset ι) (V : Finset τ)
    (z : ι → ℂ) (c : τ → ℂ) (x : ι → ℝ) (y : τ → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, W p*
    ‖sargosPlanarSum S z x (fun i => logCurve κ (x i)) p.1 p.2‖^2*
    ‖sargosPlanarSum V c y (fun i => logCurve κ (y i)) p.1 p.2‖^4

                                                                       
                                                                          
theorem exists_logCurveWeightedBilinearMoment_rescale (κ a σ : ℝ)
    (hσ : σ≠0) (hA : 0<1+κ*a) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι τ : Type u} (W : ℝ × ℝ → ℝ)
      (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
      (x : ι → ℝ) (y : τ → ℝ),
      (∀ i∈S, 0<1+κ*x i) → (∀ j∈V, 0<1+κ*y j) →
      logCurveWeightedBilinearMoment (κ*σ/(1+κ*a))
        (fun p => W (p.1/σ-(2*a*(1+κ*a)/σ^2)*p.2,((1+κ*a)^2/σ^2)*p.2))
        S V z c (fun i => (x i-a)/σ) (fun j => (y j-a)/σ)=
      C*logCurveWeightedBilinearMoment κ W S V z c x y := by
  let e := logCurveRescaling κ a σ hσ hA.ne'
  obtain ⟨C,hC,hint⟩ := logCurve_rescaling_integral (F:=ℝ) e.symm
  refine ⟨C,hC,?_⟩
  intro ι τ W S V z c x y hx hy
  have hn {ρ : Type u} (T : Finset ρ) (v : ρ → ℂ) (s : ρ → ℝ)
      (hs : ∀ i∈T, 0<1+κ*s i) (p : ℝ × ℝ) :
      ‖sargosPlanarSum T v s (fun i => logCurve κ (s i)) (e.symm p).1 (e.symm p).2‖=
        ‖sargosPlanarSum T v (fun i => (s i-a)/σ)
          (fun i => logCurve (κ*σ/(1+κ*a)) ((s i-a)/σ)) p.1 p.2‖ := by
    have h := congrArg norm (logCurve_sum_rescale T v s κ a σ
      (e.symm p).1 (e.symm p).2 hσ hA hs)
    rw [norm_mul,sargos_character_norm,one_mul] at h
    change _ = ‖sargosPlanarSum T v (fun i => (s i-a)/σ)
      (fun i => logCurve (κ*σ/(1+κ*a)) ((s i-a)/σ)) (e (e.symm p)).1
        (e (e.symm p)).2‖ at h
    simpa only [e.apply_symm_apply] using h
  let f := fun p : ℝ × ℝ => W p*
    ‖sargosPlanarSum S z x (fun i => logCurve κ (x i)) p.1 p.2‖^2*
    ‖sargosPlanarSum V c y (fun i => logCurve κ (y i)) p.1 p.2‖^4
  calc
    _ = ∫ p : ℝ × ℝ, f (e.symm p) := by
      apply integral_congr_ae
      filter_upwards with p
      dsimp only [f]
      rw [hn S z x hx,hn V c y hy]
      rfl
    _ = _ := by simpa only [f,logCurveWeightedBilinearMoment,smul_eq_mul] using hint f

def logCurveWeightedSixNorm {ι : Type*} (κ : ℝ) (W : ℝ × ℝ → ℝ)
    (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ) : ℝ :=
  lpNorm (fun p : ℝ × ℝ => sargosPlanarSum S z x (fun i => logCurve κ (x i)) p.1 p.2)
    6 (volume.withDensity (fun p => ENNReal.ofReal (W p)))

private theorem logCurveWeighted_memLp {ι : Type*} (κ : ℝ) {W : ℝ × ℝ → ℝ}
    (hW : Integrable W) (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ) :
    MemLp (fun p : ℝ × ℝ => sargosPlanarSum S z x (fun i => logCurve κ (x i)) p.1 p.2)
      6 (volume.withDensity (fun p => ENNReal.ofReal (W p))) := by
  let := isFiniteMeasure_withDensity_ofReal hW.2
  have hc : Continuous (fun p : ℝ × ℝ =>
      sargosPlanarSum S z x (fun i => logCurve κ (x i)) p.1 p.2) := by
    unfold sargosPlanarSum fordAdditiveCharacter
    fun_prop
  exact MemLp.of_bound hc.aestronglyMeasurable (∑ i∈S, ‖z i‖)
    (Filter.Eventually.of_forall fun p =>
      norm_sargosPlanarSum_le_sum_norm S z x (fun i => logCurve κ (x i)) p.1 p.2)

theorem logCurveWeightedSixNorm_nonneg {ι : Type*} (κ : ℝ) (W : ℝ × ℝ → ℝ)
    (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ) :
    0≤logCurveWeightedSixNorm κ W S z x := lpNorm_nonneg

theorem logCurveWeightedSixNorm_pow_six {ι : Type*} (κ : ℝ) (W : ℝ × ℝ → ℝ)
    (hW₀ : ∀ p, 0≤W p) (hW : Integrable W)
    (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ) :
    (logCurveWeightedSixNorm κ W S z x)^6=logCurveWeightedBilinearMoment κ W S S z z x x := by
  unfold logCurveWeightedSixNorm
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    (logCurveWeighted_memLp κ hW S z x).aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat,show (6:ℝ)=((6:ℕ):ℝ) from rfl,Real.rpow_natCast]
  simp only [one_div]
  have hroot (m : ℝ) (hm : 0 ≤ m) : (m^((6:ℝ)⁻¹))^6=m := by
    simpa only [Nat.cast_ofNat] using Real.rpow_inv_natCast_pow hm (by norm_num : (6:ℕ)≠0)
  rw [hroot _ (integral_nonneg fun _ => by positivity)]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    hW.1.aemeasurable.ennreal_ofReal (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  unfold logCurveWeightedBilinearMoment
  apply integral_congr_ae
  filter_upwards with p
  rw [ENNReal.toReal_ofReal (hW₀ p)]
  dsimp only [smul_eq_mul]
  norm_num only [Real.rpow_ofNat]
  ring

section
variable {τ ι : Type*} (κ : ℝ) (J : Finset τ) (S : τ → Finset ι) (z : τ → ι → ℂ) (x : τ → ι → ℝ) (W : ℝ × ℝ → ℝ) (hW : Integrable W)
include τ ι κ J S z x W hW

theorem logCurveWeightedSixNorm_sum_le :
    logCurveWeightedSixNorm κ W (J.sigma S) (fun ij => z ij.1 ij.2)
      (fun ij => x ij.1 ij.2)≤∑ i∈J, logCurveWeightedSixNorm κ W (S i) (z i) (x i) := by
  unfold logCurveWeightedSixNorm
  have he : (fun p : ℝ × ℝ => sargosPlanarSum (J.sigma S)
      (fun ij => z ij.1 ij.2) (fun ij => x ij.1 ij.2)
      (fun ij => logCurve κ (x ij.1 ij.2)) p.1 p.2)=
      ∑ i∈J, fun p : ℝ × ℝ =>
        sargosPlanarSum (S i) (z i) (x i) (fun k => logCurve κ (x i k)) p.1 p.2 := by
    ext p
    simp only [sargosPlanarSum,Finset.sum_sigma,Finset.sum_apply]
  rw [he]
  exact lpNorm_sum_le (fun i _ => logCurveWeighted_memLp κ hW (S i) (z i) (x i)) (by norm_num)

theorem logCurveWeightedSixNorm_sq_le_card :
    (logCurveWeightedSixNorm κ W (J.sigma S) (fun ij => z ij.1 ij.2)
      (fun ij => x ij.1 ij.2))^2≤
      (J.card:ℝ)*∑ i∈J, (logCurveWeightedSixNorm κ W (S i) (z i) (x i))^2 :=
  (pow_le_pow_left₀ (logCurveWeightedSixNorm_nonneg _ _ _ _ _)
    (logCurveWeightedSixNorm_sum_le κ J S z x W hW) 2).trans sq_sum_le_card_mul_sum_sq

end

theorem exists_logCurveWeightedSixNorm_rescale (κ a σ : ℝ)
    (hσ : σ≠0) (hA : 0<1+κ*a) :
    ∃ C : ℝ, 0<C ∧ ∀ (ι : Type u) (W : ℝ × ℝ → ℝ),
      (∀ p, 0≤W p) → Integrable W → ∀ (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ),
      (∀ i∈S, 0<1+κ*x i) →
      logCurveWeightedSixNorm (κ*σ/(1+κ*a))
        (fun p => W (p.1/σ-(2*a*(1+κ*a)/σ^2)*p.2,((1+κ*a)^2/σ^2)*p.2))
        S z (fun i => (x i-a)/σ)=C*logCurveWeightedSixNorm κ W S z x := by
  obtain ⟨d,hd,hscale⟩ := exists_logCurveWeightedBilinearMoment_rescale κ a σ hσ hA
  let C := d^((6:ℝ)⁻¹)
  have hC : 0<C := Real.rpow_pos_of_pos hd _
  have hCpow : C^6=d := by
    simpa only [C,Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow hd.le (by norm_num : (6:ℕ)≠0)
  refine ⟨C,hC,fun ι W hW₀ hW S z x hx => ?_⟩
  let e := logCurveRescaling κ a σ hσ hA.ne'
  let W' : ℝ × ℝ → ℝ := fun p => W (e.symm p)
  have hW' : Integrable W' := logCurve_rescaling_integrable e.symm hW
  have hW'₀ : ∀ p, 0≤W' p := fun p => hW₀ _
  change logCurveWeightedSixNorm (κ*σ/(1+κ*a)) W' S z (fun i => (x i-a)/σ)=
    C*logCurveWeightedSixNorm κ W S z x
  apply (pow_left_inj₀ (logCurveWeightedSixNorm_nonneg _ _ _ _ _)
    (mul_nonneg hC.le (logCurveWeightedSixNorm_nonneg _ _ _ _ _))
    (by norm_num : (6:ℕ)≠0)).mp
  rw [logCurveWeightedSixNorm_pow_six _ W' hW'₀ hW',mul_pow,hCpow,
    logCurveWeightedSixNorm_pow_six _ W hW₀ hW]
  exact hscale W S S z z x x hx hx

private theorem logCurveMoment_integrable {ι τ : Type*}
    (κ : ℝ) (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) {W : ℝ × ℝ → ℝ} (hW : Integrable W) :
    Integrable (fun p : ℝ × ℝ => W p*
      ‖sargosPlanarSum S z x (fun i => logCurve κ (x i)) p.1 p.2‖^2*
      ‖sargosPlanarSum V c y (fun i => logCurve κ (y i)) p.1 p.2‖^4) := by
  have hc : Continuous (fun p : ℝ × ℝ =>
      ‖sargosPlanarSum S z x (fun i => logCurve κ (x i)) p.1 p.2‖^2*
      ‖sargosPlanarSum V c y (fun i => logCurve κ (y i)) p.1 p.2‖^4) := by
    unfold sargosPlanarSum fordAdditiveCharacter
    fun_prop
  have hb (p : ℝ × ℝ) :
      ‖‖sargosPlanarSum S z x (fun i => logCurve κ (x i)) p.1 p.2‖^2*
        ‖sargosPlanarSum V c y (fun i => logCurve κ (y i)) p.1 p.2‖^4‖≤
        (∑ i∈S, ‖z i‖)^2*(∑ j∈V, ‖c j‖)^4 := by
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul
      (pow_le_pow_left₀ (norm_nonneg _) (norm_sargosPlanarSum_le_sum_norm S z x _ p.1 p.2) 2)
      (pow_le_pow_left₀ (norm_nonneg _) (norm_sargosPlanarSum_le_sum_norm V c y _ p.1 p.2) 4)
      (by positivity) (by positivity)
  simpa only [mul_assoc] using hW.mul_bdd hc.aestronglyMeasurable (Filter.Eventually.of_forall hb)

                                                                       
                                                                            
section
variable {ι τ : Type*} (κ : ℝ) (W : ℝ × ℝ → ℝ) (hW₀ : ∀ p, 0≤W p) (hW : Integrable W) (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ) (x : ι → ℝ) (y : τ → ℝ)
include ι τ κ W hW₀ hW S V z c x y

theorem logCurveWeightedBilinearMoment_holder_swap :
    (logCurveWeightedBilinearMoment κ W S V z c x y)^2≤
      logCurveWeightedBilinearMoment κ W V S c z y x*
        logCurveWeightedBilinearMoment κ W V V c c y y := by
  let A := fun p : ℝ × ℝ => ‖sargosPlanarSum S z x (fun i => logCurve κ (x i)) p.1 p.2‖
  let B := fun p : ℝ × ℝ => ‖sargosPlanarSum V c y (fun i => logCurve κ (y i)) p.1 p.2‖
  let M := logCurveWeightedBilinearMoment κ W S V z c x y
  let N := logCurveWeightedBilinearMoment κ W V S c z y x
  let E := logCurveWeightedBilinearMoment κ W V V c c y y
  have hMi : Integrable (fun p => W p*(A p)^2*(B p)^4) :=
    logCurveMoment_integrable κ S V z c x y hW
  have hNi : Integrable (fun p => W p*(B p)^2*(A p)^4) :=
    logCurveMoment_integrable κ V S c z y x hW
  have hEi : Integrable (fun p => W p*(B p)^2*(B p)^4) :=
    logCurveMoment_integrable κ V V c c y y hW
  have hquad (t : ℝ) : 0≤N*(t*t)+(-2*M)*t+E := by
    have hp : 0≤∫ p : ℝ × ℝ, W p*(t*(A p)^2*B p-(B p)^3)^2 :=
      integral_nonneg (fun p => mul_nonneg (hW₀ p) (sq_nonneg _))
    have he (p : ℝ × ℝ) : W p*(t*(A p)^2*B p-(B p)^3)^2=
        t^2*(W p*(B p)^2*(A p)^4)-(2*t)*(W p*(A p)^2*(B p)^4)+
          W p*(B p)^2*(B p)^4 := by ring
    simp_rw [he] at hp
    have h1 : Integrable (fun p => t^2*(W p*(B p)^2*(A p)^4)) := hNi.const_mul _
    have h2 : Integrable (fun p => (2*t)*(W p*(A p)^2*(B p)^4)) := hMi.const_mul _
    have h12 : Integrable (fun p => t^2*(W p*(B p)^2*(A p)^4)-
        (2*t)*(W p*(A p)^2*(B p)^4)) := h1.sub h2
    rw [integral_add h12 hEi,integral_sub h1 h2,integral_const_mul,integral_const_mul] at hp
    change 0≤t^2*N-(2*t)*M+E at hp
    nlinarith only [hp]
  have hdisc := discrim_le_zero hquad
  unfold discrim at hdisc
  change M^2≤N*E
  nlinarith only [hdisc]

theorem logCurveWeightedBilinearMoment_le_sixNorm :
    logCurveWeightedBilinearMoment κ W S V z c x y≤
      (logCurveWeightedSixNorm κ W S z x)^2*(logCurveWeightedSixNorm κ W V c y)^4 := by
  let M := logCurveWeightedBilinearMoment κ W S V z c x y
  let N := logCurveWeightedBilinearMoment κ W V S c z y x
  let A := logCurveWeightedSixNorm κ W S z x
  let B := logCurveWeightedSixNorm κ W V c y
  have hM : 0≤M := integral_nonneg fun p =>
    mul_nonneg (mul_nonneg (hW₀ p) (sq_nonneg _)) (by positivity)
  have hA : 0≤A := logCurveWeightedSixNorm_nonneg _ _ _ _ _
  have hB : 0≤B := logCurveWeightedSixNorm_nonneg _ _ _ _ _
  have hMN : M^2≤N*B^6 := by
    simpa only [M,N,B,logCurveWeightedSixNorm_pow_six κ W hW₀ hW] using
      logCurveWeightedBilinearMoment_holder_swap κ W hW₀ hW S V z c x y
  have hNM : N^2≤M*A^6 := by
    simpa only [M,N,A,logCurveWeightedSixNorm_pow_six κ W hW₀ hW] using
      logCurveWeightedBilinearMoment_holder_swap κ W hW₀ hW V S c z y x
  have hfour : M^4≤M*A^6*B^12 := by
    calc
      M^4=(M^2)^2 := by ring
      _ ≤ (N*B^6)^2 := pow_le_pow_left₀ (sq_nonneg M) hMN 2
      _ = N^2*B^12 := by ring
      _ ≤ M*A^6*B^12 := mul_le_mul_of_nonneg_right hNM (pow_nonneg hB 12)
  change M≤A^2*B^4
  by_cases hz : M=0
  · rw [hz]
    positivity
  have hMp := lt_of_le_of_ne hM (Ne.symm hz)
  have hcube : M^3≤(A^2*B^4)^3 := by
    apply (mul_le_mul_iff_right₀ hMp).mp
    nlinarith only [hfour]
  exact (pow_le_pow_iff_left₀ hM (by positivity) (by norm_num : (3:ℕ)≠0)).mp hcube

end

                                                                           
                                                                              
def LogCurveDecouplingBound (n : ℕ) (D : ℝ) : Prop :=
  0≤D ∧ ∀ κ∈Icc (0:ℝ) (1/4), ∀ (ι : Type u) (W : ℝ × ℝ → ℝ),
    LogCurveWeightBand κ (1/(n:ℝ)) W →
    ∀ (S : Fin n → Finset ι) (z : Fin n → ι → ℂ) (x : Fin n → ι → ℝ),
      (∀ j, ∀ k∈S j, x j k∈Icc ((j:ℕ)/(n:ℝ)) (((j:ℕ)+1)/(n:ℝ))) →
      (logCurveWeightedSixNorm κ W (Finset.univ.sigma S)
        (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2))^2≤
        D^2*∑ j, (logCurveWeightedSixNorm κ W (S j) (z j) (x j))^2

theorem logCurveDecouplingBound_trivial (n : ℕ) : LogCurveDecouplingBound.{u} n (Real.sqrt n) := by
  refine ⟨Real.sqrt_nonneg _,fun κ _ ι W hW S z x _ => ?_⟩
  rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  simpa only [Finset.card_univ,Fintype.card_fin] using
    logCurveWeightedSixNorm_sq_le_card κ Finset.univ S z x W hW.2.1

                                                                      
                                                                 
theorem LogCurveDecouplingBound.rescale {n : ℕ} {D κ a σ : ℝ}
    (hD : LogCurveDecouplingBound.{u} n D) (hκ : κ∈Icc (0:ℝ) (1/4))
    (hσ : 0<σ) (ha : 0≤a) (haσ : a+σ≤1)
    (ι : Type u) (W : ℝ × ℝ → ℝ) (hW : LogCurveWeightBand κ (σ/(n:ℝ)) W)
    (S : Fin n → Finset ι) (z : Fin n → ι → ℂ) (x : Fin n → ι → ℝ)
    (hx : ∀ j, ∀ k∈S j,
      x j k∈Icc (a+σ*((j:ℕ)/(n:ℝ))) (a+σ*(((j:ℕ)+1)/(n:ℝ)))) :
    (logCurveWeightedSixNorm κ W (Finset.univ.sigma S)
      (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2))^2≤
      D^2*∑ j, (logCurveWeightedSixNorm κ W (S j) (z j) (x j))^2 := by
  let W' : ℝ × ℝ → ℝ := fun p =>
    W (p.1/σ-(2*a*(1+κ*a)/σ^2)*p.2,((1+κ*a)^2/σ^2)*p.2)
  have hW' : LogCurveWeightBand (κ*σ/(1+κ*a)) (1/(n:ℝ)) W' := by
    have he : (σ/(n:ℝ))/σ=1/(n:ℝ) := by rw [div_right_comm,div_self hσ.ne']
    simpa only [he,W'] using hW.rescale hκ.1 hσ ha haσ
  have hx' (j : Fin n) (k : ι) (hk : k∈S j) :
      (x j k-a)/σ∈Icc ((j:ℕ)/(n:ℝ)) (((j:ℕ)+1)/(n:ℝ)) := by
    constructor
    · apply (le_div_iff₀ hσ).mpr
      nlinarith [(hx j k hk).1]
    · apply (div_le_iff₀ hσ).mpr
      nlinarith [(hx j k hk).2]
  have hxpos (j : Fin n) (k : ι) (hk : k∈S j) : 0<1+κ*x j k := by
    have hx₀ : 0≤x j k := by
      have hp : 0≤σ*((j:ℕ)/(n:ℝ)) := by positivity
      linarith [(hx j k hk).1]
    nlinarith [mul_nonneg hκ.1 hx₀]
  have h := hD.2 _ (logCurve_rescaled_parameter hκ ha ⟨hσ.le,by linarith⟩)
    ι W' hW' S z (fun j k => (x j k-a)/σ) hx'
  have hA : 0<1+κ*a := by nlinarith [mul_nonneg hκ.1 ha]
  obtain ⟨C,hC,hscale⟩ := exists_logCurveWeightedSixNorm_rescale κ a σ hσ.ne' hA
  have ht := hscale (Sigma fun _ : Fin n => ι) W hW.1 hW.2.1 (Finset.univ.sigma S)
    (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2)
    (fun jk hjk => hxpos jk.1 jk.2 (Finset.mem_sigma.mp hjk).2)
  have hi (j : Fin n) := hscale ι W hW.1 hW.2.1 (S j) (z j) (x j) (hxpos j)
  change logCurveWeightedSixNorm _ W' _ _ _ = _ at ht
  change ∀ j, logCurveWeightedSixNorm _ W' _ _ _ = _ at hi
  rw [ht] at h
  simp_rw [hi,mul_pow] at h
  rw [←Finset.mul_sum] at h
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hC)).mp
  nlinarith only [h]

                                                                        
                                                                           
def LogCurveBilinearSixBound (δ : ℝ) (p q : ℕ) (ν K : ℝ) : Prop :=
  0≤K ∧ ∀ κ∈Icc (0:ℝ) (1/4), ∀ (ι τ : Type u) (W : ℝ × ℝ → ℝ),
    LogCurveWeightBand κ δ W → ∀ (a b : ℝ),
    0≤a → a+δ*p≤1 → 0≤b → b+δ*q≤1 →
    (a+δ*p+3*ν≤b ∨ b+δ*q+3*ν≤a) →
    ∀ (S : Fin p → Finset ι) (V : Fin q → Finset τ)
      (z : Fin p → ι → ℂ) (c : Fin q → τ → ℂ)
      (x : Fin p → ι → ℝ) (y : Fin q → τ → ℝ),
    (∀ j, ∀ k∈S j, x j k∈Icc (a+δ*(j:ℕ)) (a+δ*((j:ℕ)+1))) →
    (∀ j, ∀ k∈V j, y j k∈Icc (b+δ*(j:ℕ)) (b+δ*((j:ℕ)+1))) →
    logCurveWeightedBilinearMoment κ W (Finset.univ.sigma S) (Finset.univ.sigma V)
      (fun jk => z jk.1 jk.2) (fun jk => c jk.1 jk.2)
      (fun jk => x jk.1 jk.2) (fun jk => y jk.1 jk.2)≤
      K*(∑ j, (logCurveWeightedSixNorm κ W (S j) (z j) (x j))^2)*
        (∑ j, (logCurveWeightedSixNorm κ W (V j) (c j) (y j))^2)^2

private theorem logCurve_grid_rescale_bound {n : ℕ} {D κ δ a : ℝ}
    (hn : 0<n) (hδ : 0<δ) (hD : LogCurveDecouplingBound.{u} n D)
    (hκ : κ∈Icc (0:ℝ) (1/4)) (ha : 0≤a) (haδ : a+δ*n≤1)
    (ι : Type u) (W : ℝ × ℝ → ℝ) (hW : LogCurveWeightBand κ δ W)
    (S : Fin n → Finset ι) (z : Fin n → ι → ℂ) (x : Fin n → ι → ℝ)
    (hx : ∀ j, ∀ k∈S j, x j k∈Icc (a+δ*(j:ℕ)) (a+δ*((j:ℕ)+1))) :
    (logCurveWeightedSixNorm κ W (Finset.univ.sigma S)
      (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2))^2≤
      D^2*∑ j, (logCurveWeightedSixNorm κ W (S j) (z j) (x j))^2 := by
  have hn' : (n:ℝ)≠0 := by positivity
  apply hD.rescale hκ (a:=a) (σ:=δ*n) (by positivity) ha haδ ι W
    (by simpa only [mul_div_cancel_right₀ _ hn'] using hW) S z x
  intro j k hk
  have h := hx j k hk
  have hleft : δ*n*((j:ℕ)/(n:ℝ))=δ*(j:ℕ) := by field_simp
  have hright : δ*n*(((j:ℕ)+1)/(n:ℝ))=δ*((j:ℕ)+1) := by field_simp
  simpa only [hleft,hright] using h

theorem logCurveBilinearSixBound_of_linear {p q : ℕ} {δ ν A B : ℝ}
    (hp : 0<p) (hq : 0<q) (hδ : 0<δ)
    (hA : LogCurveDecouplingBound.{u} p A) (hB : LogCurveDecouplingBound.{u} q B) :
    LogCurveBilinearSixBound.{u} δ p q ν (A^2*B^4) := by
  refine ⟨by positivity,fun κ hκ ι τ W hW a b ha haδ hb hbδ _ S V z c x y hx hy => ?_⟩
  have hS := logCurve_grid_rescale_bound hp hδ hA hκ ha haδ ι W hW S z x hx
  have hV := logCurve_grid_rescale_bound hq hδ hB hκ hb hbδ τ W hW V c y hy
  have hm := logCurveWeightedBilinearMoment_le_sixNorm κ W hW.1 hW.2.1
    (Finset.univ.sigma S) (Finset.univ.sigma V)
    (fun jk => z jk.1 jk.2) (fun jk => c jk.1 jk.2)
    (fun jk => x jk.1 jk.2) (fun jk => y jk.1 jk.2)
  refine hm.trans ?_
  have hV₂ := pow_le_pow_left₀ (sq_nonneg _) hV 2
  have hs := mul_le_mul hS hV₂ (sq_nonneg _) (by positivity)
  convert hs using 1 <;> ring

theorem LogCurveBilinearSixBound.holder_swap {p q : ℕ} {δ ν K B : ℝ}
    (hq : 0<q) (hδ : 0<δ) (hK : LogCurveBilinearSixBound.{u} δ q p ν K)
    (hB : LogCurveDecouplingBound.{u} q B) :
    LogCurveBilinearSixBound.{u} δ p q ν (Real.sqrt K*B^3) := by
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hB.1 3),
    fun κ hκ ι τ W hW a b ha haδ hb hbδ hsep S V z c x y hx hy => ?_⟩
  let ES := ∑ j, (logCurveWeightedSixNorm κ W (S j) (z j) (x j))^2
  let EV := ∑ j, (logCurveWeightedSixNorm κ W (V j) (c j) (y j))^2
  let M := logCurveWeightedBilinearMoment κ W (Finset.univ.sigma S) (Finset.univ.sigma V)
    (fun jk => z jk.1 jk.2) (fun jk => c jk.1 jk.2)
    (fun jk => x jk.1 jk.2) (fun jk => y jk.1 jk.2)
  let N := logCurveWeightedBilinearMoment κ W (Finset.univ.sigma V) (Finset.univ.sigma S)
    (fun jk => c jk.1 jk.2) (fun jk => z jk.1 jk.2)
    (fun jk => y jk.1 jk.2) (fun jk => x jk.1 jk.2)
  let Q := logCurveWeightedSixNorm κ W (Finset.univ.sigma V)
    (fun jk => c jk.1 jk.2) (fun jk => y jk.1 jk.2)
  have hES : 0≤ES := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hEV : 0≤EV := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hM : 0≤M := integral_nonneg fun r =>
    mul_nonneg (mul_nonneg (hW.1 r) (sq_nonneg _)) (pow_nonneg (norm_nonneg _) 4)
  have hN : N≤K*EV*ES^2 :=
    hK.2 κ hκ τ ι W hW b a hb hbδ ha haδ hsep.symm V S c z y x hy hx
  have hQ : Q^2≤B^2*EV :=
    logCurve_grid_rescale_bound hq hδ hB hκ hb hbδ τ W hW V c y hy
  have hMN : M^2≤N*Q^6 := by
    simpa only [M,N,Q,logCurveWeightedSixNorm_pow_six κ W hW.1 hW.2.1] using
      logCurveWeightedBilinearMoment_holder_swap κ W hW.1 hW.2.1
        (Finset.univ.sigma S) (Finset.univ.sigma V)
        (fun jk => z jk.1 jk.2) (fun jk => c jk.1 jk.2)
        (fun jk => x jk.1 jk.2) (fun jk => y jk.1 jk.2)
  have hQ₆ : Q^6≤B^6*EV^3 := by
    convert pow_le_pow_left₀ (sq_nonneg Q) hQ 3 using 1 <;> ring
  have hprod := mul_le_mul hN hQ₆ (by positivity : 0≤Q^6)
    (mul_nonneg (mul_nonneg hK.1 hEV) (sq_nonneg ES))
  have he : (Real.sqrt K*B^3*ES*EV^2)^2=(K*EV*ES^2)*(B^6*EV^3) := by
    rw [show (Real.sqrt K*B^3*ES*EV^2)^2=(Real.sqrt K)^2*B^6*ES^2*EV^4 by ring,
      Real.sq_sqrt hK.1]
    ring
  have hB₀ := hB.1
  change M≤Real.sqrt K*B^3*ES*EV^2
  apply (pow_le_pow_iff_left₀ hM (by positivity) (by norm_num : (2:ℕ)≠0)).mp
  rw [he]
  exact hMN.trans hprod

private theorem logCurve_product_sum {ι τ : Type*}
    (κ : ℝ) (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) (α γ : ℝ) :
    sargosPlanarSum ((S ×ˢ V) ×ˢ V)
      (fun ij => z ij.1.1*c ij.1.2*c ij.2)
      (fun ij => x ij.1.1+y ij.1.2+y ij.2)
      (fun ij => logCurve κ (x ij.1.1)+logCurve κ (y ij.1.2)+logCurve κ (y ij.2)) α γ =
    sargosPlanarSum S z x (fun i => logCurve κ (x i)) α γ *
      (sargosPlanarSum V c y (fun k => logCurve κ (y k)) α γ)^2 := by
  rw [←planarSum_mul (S ×ˢ V) V (fun ij => z ij.1*c ij.2) c
    (fun ij => x ij.1+y ij.2) (fun ij => logCurve κ (x ij.1)+logCurve κ (y ij.2)) y
    (fun k => logCurve κ (y k)) α γ,
    ←planarSum_mul S V z c x (fun i => logCurve κ (x i)) y
      (fun k => logCurve κ (y k)) α γ]
  ring

private theorem logCurve_family_product_sum {ι τ : Type*}
    (κ : ℝ) (J : Finset ℤ) (S : ℤ → Finset ι) (V : Finset τ)
    (z : ℤ → ι → ℂ) (c : τ → ℂ)
    (x : ℤ → ι → ℝ) (y : τ → ℝ) (α γ : ℝ) :
    sargosPlanarSum (J.sigma (fun i => (S i ×ˢ V) ×ˢ V))
      (fun ij => z ij.1 ij.2.1.1*c ij.2.1.2*c ij.2.2)
      (fun ij => x ij.1 ij.2.1.1+y ij.2.1.2+y ij.2.2)
      (fun ij => logCurve κ (x ij.1 ij.2.1.1)+logCurve κ (y ij.2.1.2)+
        logCurve κ (y ij.2.2)) α γ =
    sargosPlanarSum (J.sigma S) (fun ij => z ij.1 ij.2)
      (fun ij => x ij.1 ij.2) (fun ij => logCurve κ (x ij.1 ij.2)) α γ *
      (sargosPlanarSum V c y (fun k => logCurve κ (y k)) α γ)^2 := by
  change (∑ ij ∈ J.sigma (fun i => (S i ×ˢ V) ×ˢ V), _) = _
  rw [Finset.sum_sigma]
  change (∑ i ∈ J, sargosPlanarSum ((S i ×ˢ V) ×ˢ V)
    (fun ij => z i ij.1.1*c ij.1.2*c ij.2)
    (fun ij => x i ij.1.1+y ij.1.2+y ij.2)
    (fun ij => logCurve κ (x i ij.1.1)+logCurve κ (y ij.1.2)+logCurve κ (y ij.2)) α γ) = _
  simp_rw [logCurve_product_sum]
  rw [←Finset.sum_mul]
  congr 1
  simp only [sargosPlanarSum,Finset.sum_sigma]

private theorem logCurve_block_gap {i j : ℤ} {m : ℕ} {x x' d w ν : ℝ}
    (hm : 2/ν≤(m : ℝ))
    (hx : x∈Icc (d+w^2*(i : ℝ)) (d+w^2*((i : ℝ)+1)))
    (hx' : x'∈Icc (d+w^2*(j : ℝ)) (d+w^2*((j : ℝ)+1)))
    (hij : (m : ℤ) < |i-j|) :
    2*w^2/ν≤|x-x'| := by
  have hm' : 2*w^2/ν≤w^2*(m : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hm (sq_nonneg w)
    convert h using 1
    ring
  rcases le_total i j with h|h
  · have hji : (m : ℤ)+1 ≤ j-i := by
      rw [abs_of_nonpos (sub_nonpos.mpr h)] at hij
      omega
    have hji' : (m : ℝ)+1≤(j : ℝ)-(i : ℝ) := by exact_mod_cast hji
    have hp := mul_le_mul_of_nonneg_left hji' (sq_nonneg w)
    have hg : w^2*(m : ℝ)≤x'-x := by nlinarith [hx.2,hx'.1]
    exact (hm'.trans hg).trans (by rw [abs_sub_comm]; exact le_abs_self _)
  · have hij' : (m : ℤ)+1 ≤ i-j := by
      rw [abs_of_nonneg (sub_nonneg.mpr h)] at hij
      omega
    have hij'' : (m : ℝ)+1≤(i : ℝ)-(j : ℝ) := by exact_mod_cast hij'
    have hp := mul_le_mul_of_nonneg_left hij'' (sq_nonneg w)
    have hg : w^2*(m : ℝ)≤x-x' := by nlinarith [hx.1,hx'.2]
    exact (hm'.trans hg).trans (le_abs_self _)

                                                                
                                                                 
                                                                              
theorem logCurveWeightedBilinearMoment_localization_closed {ι τ : Type*}
    (J : Finset ℤ) (S : ℤ → Finset ι) (V : Finset τ)
    (z : ℤ → ι → ℂ) (c : τ → ℂ)
    (x : ℤ → ι → ℝ) (y : τ → ℝ)
    {κ w a β u ν δ : ℝ} {W : ℝ × ℝ → ℝ}
    (hκ : κ∈Icc (0:ℝ) (1/4)) (hW : LogCurveWeightBand κ δ W)
    (hw : 0<w) (hν : 0<ν) (hν₁ : ν≤1) (hβ : β∈Icc (0:ℝ) 1)
    (ha : 0≤a) (har : a+u≤1) (hwidth : δ^2≤w^2) (hu : u≤ν) (hd : 3*ν≤|a-β|)
    (hx : ∀ i∈J, ∀ k∈S i, x i k∈Icc a (a+u))
    (hy : ∀ k∈V, y k∈Icc β (β+w))
    (hblock : ∀ i∈J, ∀ k∈S i,
      x i k∈Icc (a+w^2*(i : ℝ)) (a+w^2*((i : ℝ)+1))) :
    logCurveWeightedBilinearMoment κ W (J.sigma S) V
      (fun ij => z ij.1 ij.2) c (fun ij => x ij.1 ij.2) y≤
      (7/ν)*∑ i∈J, logCurveWeightedBilinearMoment κ W (S i) V (z i) c (x i) y := by
  classical
  let m := ⌈2/ν⌉₊
  have hm : 2/ν≤(m : ℝ) := Nat.le_ceil _
  have hceil : (m : ℝ)<2/ν+1 := Nat.ceil_lt_add_one (by positivity)
  have hfac : 2*(m : ℝ)+1≤7/ν := by
    have hn := (lt_div_iff₀ hν).mp (show (m : ℝ)-1<2/ν by linarith)
    apply (le_div_iff₀ hν).mpr
    nlinarith
  let F := fun i : ℤ => (S i ×ˢ V) ×ˢ V
  let Z := fun i : ℤ => fun ij : (ι × τ) × τ => z i ij.1.1*c ij.1.2*c ij.2
  let X := fun i : ℤ => fun ij : (ι × τ) × τ => x i ij.1.1+y ij.1.2+y ij.2
  let Y := fun i : ℤ => fun ij : (ι × τ) × τ =>
    logCurve κ (x i ij.1.1)+logCurve κ (y ij.1.2)+logCurve κ (y ij.2)
  have hmain := sargosWeightedPlanarFamily_banded_bound J F Z X Y W hW.1 hW.2.1 m (by
    intro i hi j hj hij p hp q hq
    apply hW.2.2
    have hp' := Finset.mem_product.mp hp
    have hq' := Finset.mem_product.mp hq
    have hps := Finset.mem_product.mp hp'.1
    have hqs := Finset.mem_product.mp hq'.1
    have hgap := logCurve_block_gap hm (hblock i hi _ hps.1) (hblock j hj _ hqs.1) hij
    exact logCurve_band_sixth_gap hκ hw hν hβ ha har hwidth hu hd
      (hx i hi _ hps.1) (hx j hj _ hqs.1) (hy _ hps.2) (hy _ hp'.2)
      (hy _ hqs.2) (hy _ hq'.2) hgap)
  have heq : logCurveWeightedBilinearMoment κ W (J.sigma S) V
      (fun ij => z ij.1 ij.2) c (fun ij => x ij.1 ij.2) y=
      ∫ p : ℝ × ℝ, W p*‖sargosPlanarSum (J.sigma F)
        (fun ij => Z ij.1 ij.2) (fun ij => X ij.1 ij.2) (fun ij => Y ij.1 ij.2) p.1 p.2‖^2 := by
    unfold logCurveWeightedBilinearMoment
    apply integral_congr_ae
    filter_upwards with p
    dsimp only [F,Z,X,Y]
    rw [logCurve_family_product_sum,norm_mul,norm_pow]
    ring
  have hsingle (i : ℤ) : (∫ p : ℝ × ℝ,
      W p*‖sargosPlanarSum (F i) (Z i) (X i) (Y i) p.1 p.2‖^2)=
      logCurveWeightedBilinearMoment κ W (S i) V (z i) c (x i) y := by
    unfold logCurveWeightedBilinearMoment
    apply integral_congr_ae
    filter_upwards with p
    dsimp only [F,Z,X,Y]
    rw [logCurve_product_sum,norm_mul,norm_pow]
    ring
  rw [←heq] at hmain
  simp_rw [hsingle] at hmain
  refine hmain.trans (mul_le_mul_of_nonneg_right hfac ?_)
  apply Finset.sum_nonneg
  intro i hi
  unfold logCurveWeightedBilinearMoment
  exact integral_nonneg (fun p => mul_nonneg (mul_nonneg (hW.1 p) (sq_nonneg _)) (by positivity))

theorem logCurve_finGrid_sum {k l : ℕ} {A : Type*} [AddCommMonoid A]
    (f : Fin (k*l) → A) :
    ∑ r, f r=∑ i : Fin k, ∑ j : Fin l, f (finProdFinEquiv (i,j)) := by
  simpa only [Fintype.sum_prod_type] using (Equiv.sum_comp finProdFinEquiv f).symm

private def logCurveIntGridIndex (k : ℕ) (hk : 0 < k) (i : ℤ) : Fin k :=
  ⟨i.toNat % k,Nat.mod_lt _ hk⟩

private theorem logCurveIntGridIndex_cast {k : ℕ} (hk : 0 < k) (i : Fin k) :
    logCurveIntGridIndex k hk (i:ℕ) = i := by
  apply Fin.ext
  simp [logCurveIntGridIndex,Nat.mod_eq_of_lt i.isLt]

private theorem logCurveIntGridIndex_val {k : ℕ} (hk : 0 < k) {i : ℤ}
    (hi : i ∈ Finset.Ico 0 (k:ℤ)) :
    ((logCurveIntGridIndex k hk i : Fin k):ℕ) = i.toNat := by
  have hh := Finset.mem_Ico.mp hi
  simp only [logCurveIntGridIndex]
  exact Nat.mod_eq_of_lt (by omega)

private theorem logCurve_intGrid_sum {k : ℕ} (hk : 0 < k)
    {A : Type*} [AddCommMonoid A] (f : Fin k → A) :
    ∑ i ∈ Finset.Ico 0 (k:ℤ), f (logCurveIntGridIndex k hk i) = ∑ j, f j := by
  classical
  symm
  refine Finset.sum_bij (fun j _ => (j:ℤ)) ?_ ?_ ?_ ?_
  · intro j _
    apply Finset.mem_Ico.mpr
    constructor
    · exact_mod_cast (Nat.zero_le (j:ℕ))
    · exact_mod_cast j.isLt
  · intro i _ j _ h
    apply Fin.ext
    exact_mod_cast h
  · intro i hi
    have hh := Finset.mem_Ico.mp hi
    refine ⟨⟨i.toNat,by omega⟩,Finset.mem_univ _,?_⟩
    dsimp
    omega
  · intro i _
    rw [logCurveIntGridIndex_cast]

private theorem logCurveWeightedBilinearMoment_fin_localization {k : ℕ}
    (hk : 0 < k) {ι τ : Type*}
    (S : Fin k → Finset ι) (V : Finset τ)
    (z : Fin k → ι → ℂ) (c : τ → ℂ) (x : Fin k → ι → ℝ) (y : τ → ℝ)
    {κ w a β u ν δ : ℝ} {W : ℝ × ℝ → ℝ}
    (hκ : κ∈Icc (0:ℝ) (1/4)) (hW : LogCurveWeightBand κ δ W)
    (hw : 0 < w) (hν : 0 < ν) (hν₁ : ν ≤ 1) (hβ : β ∈ Icc 0 1)
    (ha : 0≤a) (har : a+u≤1)
    (hwidth : δ^2 ≤ w^2) (hu : u ≤ ν) (hd : 3*ν ≤ |a-β|)
    (hx : ∀ i, ∀ v ∈ S i, x i v ∈ Icc a (a+u))
    (hy : ∀ v ∈ V, y v ∈ Icc β (β+w))
    (hblock : ∀ i, ∀ v ∈ S i,
      x i v ∈ Icc (a+w^2*(i:ℕ)) (a+w^2*((i:ℕ)+1))) :
    logCurveWeightedBilinearMoment κ W (Finset.univ.sigma S) V
      (fun iv => z iv.1 iv.2) c (fun iv => x iv.1 iv.2) y ≤
      (7/ν)*∑ i, logCurveWeightedBilinearMoment κ W (S i) V (z i) c (x i) y := by
  let R := logCurveIntGridIndex k hk
  let J := Finset.Ico 0 (k:ℤ)
  have hR (i : ℤ) (hi : i ∈ J) : ((R i:Fin k):ℝ) = (i:ℝ) := by
    have hv := logCurveIntGridIndex_val hk hi
    have hn : 0 ≤ i := (Finset.mem_Ico.mp hi).1
    change (((R i:Fin k):ℕ):ℝ) = _
    rw [hv]
    exact_mod_cast Int.toNat_of_nonneg hn
  have h := logCurveWeightedBilinearMoment_localization_closed J
    (fun i => S (R i)) V (fun i => z (R i)) c (fun i => x (R i)) y
    hκ hW hw hν hν₁ hβ ha har hwidth hu hd
    (fun i _ => hx (R i)) hy (fun i hi v hv => by
      simpa only [hR i hi] using hblock (R i) v hv)
  have he (α γ : ℝ) :
      sargosPlanarSum (J.sigma (fun i => S (R i)))
        (fun iv => z (R iv.1) iv.2) (fun iv => x (R iv.1) iv.2)
        (fun iv => logCurve κ (x (R iv.1) iv.2)) α γ =
      sargosPlanarSum (Finset.univ.sigma S) (fun iv => z iv.1 iv.2)
        (fun iv => x iv.1 iv.2) (fun iv => logCurve κ (x iv.1 iv.2)) α γ := by
    simp only [sargosPlanarSum,Finset.sum_sigma]
    exact logCurve_intGrid_sum hk (fun i => ∑ v ∈ S i,
      z i v*fordAdditiveCharacter (x i v*α+logCurve κ (x i v)*γ))
  have hm : logCurveWeightedBilinearMoment κ W (J.sigma (fun i => S (R i))) V
      (fun iv => z (R iv.1) iv.2) c (fun iv => x (R iv.1) iv.2) y =
      logCurveWeightedBilinearMoment κ W (Finset.univ.sigma S) V
        (fun iv => z iv.1 iv.2) c (fun iv => x iv.1 iv.2) y := by
    unfold logCurveWeightedBilinearMoment
    simp_rw [he]
  rw [hm] at h
  have hsum := logCurve_intGrid_sum hk (fun i =>
    logCurveWeightedBilinearMoment κ W (S i) V (z i) c (x i) y)
  change (∑ i ∈ J, logCurveWeightedBilinearMoment κ W (S (R i)) V (z (R i)) c (x (R i)) y) = _ at hsum
  rw [hsum] at h
  exact h

                                                                           
                                                                                 
theorem LogCurveBilinearSixBound.localization {k m q : ℕ} {δ ν K : ℝ}
    (hk : 0 < k) (hq : 0 < q) (hδ : 0 < δ)
    (hν : 0 < ν) (hν₁ : ν ≤ 1)
    (hsmall : δ*(k*m) ≤ ν) (hscale : δ*m = (δ*q)^2)
    (hK : LogCurveBilinearSixBound.{u} δ m q ν K) :
    LogCurveBilinearSixBound.{u} δ (k*m) q ν ((7/ν)*K) := by
  refine ⟨mul_nonneg (by positivity) hK.1,
    fun κ hκ ι τ W hW a b ha haδ hb hbδ hsep S V z c x y hx hy => ?_⟩
  simp only [Nat.cast_mul] at haδ hsep
  let e : Fin k × Fin m ≃ Fin (k*m) := finProdFinEquiv
  let T := fun i : Fin k => Finset.univ.sigma (fun j : Fin m => S (e (i,j)))
  let Z := fun i : Fin k => fun jv : (j : Fin m) × ι => z (e (i,jv.1)) jv.2
  let X := fun i : Fin k => fun jv : (j : Fin m) × ι => x (e (i,jv.1)) jv.2
  let U := Finset.univ.sigma V
  let C := fun jv : (j : Fin q) × τ => c jv.1 jv.2
  let Y := fun jv : (j : Fin q) × τ => y jv.1 jv.2
  let ai := fun i : Fin k => a+δ*m*(i:ℕ)
  have heval (i : Fin k) (j : Fin m) :
      ((e (i,j):Fin (k*m)):ℝ) = (j:ℕ)+(m:ℝ)*(i:ℕ) := by
    simp [e,finProdFinEquiv,Nat.cast_add,Nat.cast_mul]
  have hai (i : Fin k) : a ≤ ai i ∧ ai i+δ*m ≤ a+δ*(k*m) := by
    have hi : ((i:ℕ):ℝ)+1 ≤ k := by exact_mod_cast i.isLt
    have hp := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ δ*m)
    have hzero : 0 ≤ δ*m*(i:ℕ) := by positivity
    dsimp only [ai]
    constructor
    · linarith
    · nlinarith only [hp]
  have hfine (i : Fin k) (j : Fin m) (v : ι) (hv : v ∈ S (e (i,j))) :
      x (e (i,j)) v ∈ Icc (ai i+δ*(j:ℕ)) (ai i+δ*((j:ℕ)+1)) := by
    have hf := hx (e (i,j)) v hv
    change x (e (i,j)) v ∈ Icc (a+δ*((e (i,j):Fin (k*m)):ℝ))
      (a+δ*(((e (i,j):Fin (k*m)):ℝ)+1)) at hf
    rw [heval] at hf
    dsimp only [ai]
    constructor <;> nlinarith [hf.1,hf.2]
  have hblock (i : Fin k) (v : (j : Fin m) × ι) (hv : v ∈ T i) :
      X i v ∈ Icc (ai i) (ai i+δ*m) := by
    have hf := hfine i v.1 v.2 (Finset.mem_sigma.mp hv).2
    have hj : ((v.1:ℕ):ℝ)+1 ≤ m := by exact_mod_cast v.1.isLt
    have hp := mul_le_mul_of_nonneg_left hj hδ.le
    have hn : 0 ≤ δ*(v.1:ℕ) := by positivity
    constructor <;> dsimp only [X] <;> nlinarith [hf.1,hf.2]
  have hglobal (i : Fin k) (v : (j : Fin m) × ι) (hv : v ∈ T i) :
      X i v ∈ Icc a (a+δ*(k*m)) :=
    ⟨(hai i).1.trans (hblock i v hv).1,(hblock i v hv).2.trans (hai i).2⟩
  have hsecondary (v : (j : Fin q) × τ) (hv : v ∈ U) :
      Y v ∈ Icc b (b+δ*q) := by
    have hf := hy v.1 v.2 (Finset.mem_sigma.mp hv).2
    have hj : ((v.1:ℕ):ℝ)+1 ≤ q := by exact_mod_cast v.1.isLt
    have hp := mul_le_mul_of_nonneg_left hj hδ.le
    have hn : 0 ≤ δ*(v.1:ℕ) := by positivity
    constructor <;> dsimp only [Y] <;> nlinarith [hf.1,hf.2]
  have hd : 3*ν ≤ |a-b| := by
    rcases hsep with hs | hs
    · have hz : 0 ≤ δ*(k*m) := by positivity
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hz : 0 ≤ δ*q := by positivity
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hq₁ : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hwidth : δ^2 ≤ (δ*q)^2 :=
    pow_le_pow_left₀ hδ.le (by nlinarith) 2
  have hloc := logCurveWeightedBilinearMoment_fin_localization hk T U Z C X Y
    hκ hW (by positivity : 0 < δ*q) hν hν₁
    (show b ∈ Icc 0 1 from ⟨hb,by nlinarith [mul_nonneg hδ.le (Nat.cast_nonneg q)]⟩)
    ha haδ hwidth hsmall hd hglobal hsecondary (fun i v hv => by
      have h := hblock i v hv
      dsimp only [ai] at h
      simpa only [← hscale,mul_add,mul_one,mul_assoc,add_assoc] using h)

  let EV := ∑ j, (logCurveWeightedSixNorm κ W (V j) (c j) (y j))^2
  have hpiece (i : Fin k) :
      logCurveWeightedBilinearMoment κ W (T i) U (Z i) C (X i) Y ≤
        K*(∑ j : Fin m,
          (logCurveWeightedSixNorm κ W (S (e (i,j))) (z (e (i,j))) (x (e (i,j))))^2)*EV^2 := by
    have hsep' : ai i+δ*m+3*ν ≤ b ∨ b+δ*q+3*ν ≤ ai i := by
      rcases hsep with hs | hs
      · exact Or.inl (by linarith [(hai i).2])
      · exact Or.inr (by linarith [(hai i).1])
    exact hK.2 κ hκ ι τ W hW (ai i) b (ha.trans (hai i).1) ((hai i).2.trans haδ)
      hb hbδ hsep' (fun j => S (e (i,j))) V (fun j => z (e (i,j))) c
      (fun j => x (e (i,j))) y (hfine i) hy
  have ht :
      logCurveWeightedBilinearMoment κ W (Finset.univ.sigma S) U
        (fun rv => z rv.1 rv.2) C (fun rv => x rv.1 rv.2) Y =
      logCurveWeightedBilinearMoment κ W (Finset.univ.sigma T) U
        (fun iv => Z iv.1 iv.2) C (fun iv => X iv.1 iv.2) Y := by
    unfold logCurveWeightedBilinearMoment
    apply integral_congr_ae
    filter_upwards with r
    have he :
        sargosPlanarSum (Finset.univ.sigma S) (fun rv => z rv.1 rv.2)
          (fun rv => x rv.1 rv.2) (fun rv => logCurve κ (x rv.1 rv.2)) r.1 r.2 =
        sargosPlanarSum (Finset.univ.sigma T) (fun iv => Z iv.1 iv.2)
          (fun iv => X iv.1 iv.2) (fun iv => logCurve κ (X iv.1 iv.2)) r.1 r.2 := by
      simp only [sargosPlanarSum,Finset.sum_sigma,T,Z,X]
      exact logCurve_finGrid_sum _
    rw [he]
  change logCurveWeightedBilinearMoment κ W (Finset.univ.sigma S) U
    (fun rv => z rv.1 rv.2) C (fun rv => x rv.1 rv.2) Y ≤ _
  rw [ht]
  refine hloc.trans ?_
  have hp := Finset.sum_le_sum (fun i (_hi : i ∈ Finset.univ) => hpiece i)
  have hp' := mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ) ≤ 7/ν)
  have he : (∑ i : Fin k, K*(∑ j : Fin m,
      (logCurveWeightedSixNorm κ W (S (e (i,j))) (z (e (i,j))) (x (e (i,j))))^2)*EV^2) =
      K*(∑ r, (logCurveWeightedSixNorm κ W (S r) (z r) (x r))^2)*EV^2 := by
    rw [← Finset.sum_mul,← Finset.mul_sum,logCurve_finGrid_sum]
  rw [he] at hp'
  simpa only [EV,mul_assoc] using hp'

                                                                    
                                                                  
theorem LogCurveBilinearSixBound.localization_holder {k m q : ℕ} {δ ν K B : ℝ}
    (hk : 0 < k) (hq : 0 < q) (hδ : 0 < δ) (hν : 0 < ν) (hν₁ : ν ≤ 1)
    (hsmall : δ*(k*m) ≤ ν) (hscale : δ*m = (δ*q)^2)
    (hK : LogCurveBilinearSixBound.{u} δ q m ν K)
    (hB : LogCurveDecouplingBound.{u} q B) :
    LogCurveBilinearSixBound.{u} δ (k*m) q ν ((7/ν)*(Real.sqrt K*B^3)) :=
  (hK.holder_swap hq hδ hB).localization hk hq hδ hν hν₁ hsmall hscale

private theorem logCurve_dyadic_width_mul_cells {a n : ℕ} (ha : a ≤ n) :
    (1/(2:ℝ)^n)*(2:ℝ)^(n-a) = 1/(2:ℝ)^a := by
  rw [pow_sub₀ (2:ℝ) (by norm_num) ha]
  field_simp

private theorem logCurve_dyadic_width_sq (b : ℕ) :
    (1/(2:ℝ)^b)^2 = 1/(2:ℝ)^(2*b) := by
  rw [div_pow,one_pow,← pow_mul]
  congr 2
  omega

                                                            
theorem LogCurveBilinearSixBound.dyadic_step {n a b r : ℕ} {K B : ℝ}
    (ha : a ≤ 2*b) (hb : 2*b ≤ n) (hr : r ≤ a)
    (hK : LogCurveBilinearSixBound.{u} (1/(2:ℝ)^n)
      (2^(n-b)) (2^(n-2*b)) (1/(2:ℝ)^r) K)
    (hB : LogCurveDecouplingBound.{u} (2^(n-b)) B) :
    LogCurveBilinearSixBound.{u} (1/(2:ℝ)^n)
      (2^(n-a)) (2^(n-b)) (1/(2:ℝ)^r)
      ((7/(1/(2:ℝ)^r))*(Real.sqrt K*B^3)) := by
  have hcount : (2:ℕ)^(2*b-a)*2^(n-2*b) = 2^(n-a) := by
    rw [← pow_add]
    congr 1
    omega
  have hsmall : (1/(2:ℝ)^n)*((2:ℕ)^(2*b-a)*(2:ℕ)^(n-2*b)) ≤ 1/(2:ℝ)^r := by
    push_cast
    rw [← pow_add,show (2*b-a)+(n-2*b) = n-a by omega,
      logCurve_dyadic_width_mul_cells (ha.trans hb)]
    exact one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hr)
  have hscale : (1/(2:ℝ)^n)*(((2:ℕ)^(n-2*b):ℕ):ℝ) =
      ((1/(2:ℝ)^n)*(((2:ℕ)^(n-b):ℕ):ℝ))^2 := by
    push_cast
    rw [logCurve_dyadic_width_mul_cells hb,logCurve_dyadic_width_mul_cells (by omega : b ≤ n),
      logCurve_dyadic_width_sq]
  have hν₁ : 1/(2:ℝ)^r ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2^r)).mpr
    simpa only [one_mul] using one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n:=r)
  have h := hK.localization_holder (k:=2^(2*b-a)) (by positivity) (by positivity)
    (by positivity) (by positivity) hν₁ (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hsmall) hscale hB
  simpa only [hcount] using h


theorem logCurveBilinearSixBound_dyadic_iterate (D : ℕ → ℝ)
    {n r a b t : ℕ} (hr : 0 < r) (hra : r ≤ a) (hab : a ≤ b)
    (hb : b*2^t ≤ n)
    (hD : ∀ j < n, LogCurveDecouplingBound.{u} (2^j) (D j)) :
    LogCurveBilinearSixBound.{u} (1/(2:ℝ)^n) (2^(n-a)) (2^(n-b))
      (1/(2:ℝ)^r) (parabolaDyadicBilinearBudget D n r t a b) := by
  induction t generalizing a b with
  | zero =>
    simp only [pow_zero,mul_one] at hb
    exact logCurveBilinearSixBound_of_linear (by positivity) (by positivity)
      (by positivity) (hD (n-a) (by omega)) (hD (n-b) (by omega))
  | succ t ih =>
    have hpow : (1:ℕ) ≤ 2^t := Nat.succ_le_iff.mpr (by positivity)
    have he : (2*b)*2^t = b*2^(t+1) := by rw [pow_succ]; ring
    have hnext : (2*b)*2^t ≤ n := by rw [he]; exact hb
    have hb₂ : 2*b ≤ n :=
      (show 2*b ≤ (2*b)*2^t by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hpow (Nat.zero_le (2*b))).trans hnext
    have hprev := ih (hra.trans hab) (by omega : b ≤ 2*b) hnext
    have h := hprev.dyadic_step (a:=a) (by omega) hb₂ hra (hD (n-b) (by omega))
    simpa only [parabolaDyadicBilinearBudget] using h

theorem logCurveWeightedSixNorm_bilinear_reduction {ι : Type*}
    (κ : ℝ)
    (J : Finset ℤ) (S : ℤ → Finset ι) (z : ℤ → ι → ℂ) (x : ℤ → ι → ℝ)
    (W : ℝ × ℝ → ℝ) (hW₀ : ∀ p, 0 ≤ W p) (hW : Integrable W) :
    (logCurveWeightedSixNorm κ W (J.sigma S) (fun ij => z ij.1 ij.2)
      (fun ij => x ij.1 ij.2))^6 ≤
      (64*7^6:ℝ)*∑ i ∈ J, (logCurveWeightedSixNorm κ W (S i) (z i) (x i))^6 +
      64*(J.card:ℝ)^5*∑ i ∈ J, ∑ j ∈ J.filter (fun j => 3 < |i-j|),
        logCurveWeightedBilinearMoment κ W (S j) (S i) (z j) (z i) (x j) (x i) := by
  classical
  let F := fun i => fun p : ℝ × ℝ =>
    sargosPlanarSum (S i) (z i) (x i) (fun k => logCurve κ (x i k)) p.1 p.2
  let G := fun i j => fun p : ℝ × ℝ => W p*‖F i p‖^2*‖F j p‖^4
  let T := J.sigma S
  let Z := fun ij : (i : ℤ) × ι => z ij.1 ij.2
  let X := fun ij : (i : ℤ) × ι => x ij.1 ij.2
  let H := fun p : ℝ × ℝ => W p*
    ‖sargosPlanarSum T Z X (fun ij => logCurve κ (X ij)) p.1 p.2‖^2*
    ‖sargosPlanarSum T Z X (fun ij => logCurve κ (X ij)) p.1 p.2‖^4
  have hG (i j : ℤ) : Integrable (G i j) := by
    simpa only [G,F,mul_assoc] using
      logCurveMoment_integrable κ (S i) (S j) (z i) (z j) (x i) (x j) hW
  have hH : Integrable H := by
    simpa only [H,mul_assoc] using
      logCurveMoment_integrable κ T T Z Z X X hW
  have hs (p : ℝ × ℝ) :
      sargosPlanarSum T Z X (fun ij => logCurve κ (X ij)) p.1 p.2 = ∑ i ∈ J, F i p := by
    simp only [T,Z,X,F,sargosPlanarSum,Finset.sum_sigma]
  have hpoint (p : ℝ × ℝ) :
      H p ≤ (64*7^6:ℝ)*(∑ i ∈ J, G i i p) +
        64*(J.card:ℝ)^5*(∑ i ∈ J, ∑ j ∈ J.filter (fun j => 3 < |i-j|), G j i p) := by
    have hp := mul_le_mul_of_nonneg_left
      (weighted_decoupling_pointwise J (fun i => F i p)) (hW₀ p)
    have he (v : ℂ) : ‖v‖^6 = ‖v‖^2*‖v‖^4 := by ring
    dsimp only [H]
    rw [hs]
    simp_rw [he] at hp
    have hd : W p*((64*7^6:ℝ)*∑ i ∈ J, ‖F i p‖^2*‖F i p‖^4) =
        (64*7^6:ℝ)*∑ i ∈ J, G i i p := by
      rw [← mul_assoc,mul_comm (W p),mul_assoc,Finset.mul_sum]
      simp only [G,mul_assoc]
    have hc : W p*(64*(J.card:ℝ)^5*
        ∑ i ∈ J, ∑ j ∈ J.filter (fun j => 3 < |i-j|), ‖F j p‖^2*‖F i p‖^4) =
        64*(J.card:ℝ)^5*
          ∑ i ∈ J, ∑ j ∈ J.filter (fun j => 3 < |i-j|), G j i p := by
      rw [← mul_assoc,mul_comm (W p),mul_assoc]
      simp only [Finset.mul_sum,G,mul_assoc]
    rw [mul_add,hd,hc] at hp
    simpa only [mul_assoc] using hp
  have hdiag : Integrable (fun p => ∑ i ∈ J, G i i p) :=
    integrable_finsetSum J (fun i _ => hG i i)
  have hcross : Integrable (fun p => ∑ i ∈ J,
      ∑ j ∈ J.filter (fun j => 3 < |i-j|), G j i p) :=
    integrable_finsetSum J (fun i _ =>
      integrable_finsetSum _ (fun j _ => hG j i))
  have h := integral_mono hH
    ((hdiag.const_mul (64*7^6:ℝ)).add (hcross.const_mul (64*(J.card:ℝ)^5))) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add (hdiag.const_mul _) (hcross.const_mul _),
    integral_const_mul,integral_const_mul,
    integral_finsetSum J (fun i _ => hG i i),
    integral_finsetSum J (fun i _ => integrable_finsetSum _ (fun j _ => hG j i))] at h
  simp_rw [integral_finsetSum _ (fun j _ => hG j _)] at h
  simpa only [logCurveWeightedSixNorm_pow_six κ W hW₀ hW,
    logCurveWeightedBilinearMoment,H,T,Z,X,G,F] using h

theorem logCurve_finGrid_cell {k l : ℕ} (hk : 0 < k) (hl : 0 < l)
    (i : Fin k) (j : Fin l) :
    ((finProdFinEquiv (i,j) : Fin (k*l)):ℕ)/(k*l:ℝ) =
      (i:ℕ)/(k:ℝ)+(1/(k:ℝ))*((j:ℕ)/(l:ℝ)) ∧
    (((finProdFinEquiv (i,j) : Fin (k*l)):ℕ)+1)/(k*l:ℝ) =
      (i:ℕ)/(k:ℝ)+(1/(k:ℝ))*(((j:ℕ)+1)/(l:ℝ)) := by
  have hk' : (k:ℝ) ≠ 0 := by positivity
  have hl' : (l:ℝ) ≠ 0 := by positivity
  simp only [finProdFinEquiv,Equiv.coe_fn_mk,Nat.cast_add,Nat.cast_mul]
  constructor <;> field_simp <;> ring

private theorem logCurve_sum_nonneg_powers_le {ι : Type*} (J : Finset ι) (E : ι → ℝ)
    (hE : ∀ i ∈ J, 0 ≤ E i) {n : ℕ} (hn : n ≠ 0) :
    ∑ i ∈ J, (E i)^n ≤ (∑ i ∈ J, E i)^n := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [zero_pow hn]
  | @insert a J ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    have hJ : ∀ i ∈ J, 0 ≤ E i := fun i hi => hE i (Finset.mem_insert_of_mem hi)
    calc
      E a^n+(∑ i ∈ J, (E i)^n) ≤ E a^n+(∑ i ∈ J, E i)^n :=
        add_le_add le_rfl (ih hJ)
      _ ≤ _ := pow_add_pow_le (hE a (Finset.mem_insert_self a J))
        (Finset.sum_nonneg hJ) hn

private theorem logCurveWeightedSixNorm_bilinear_budget {ι : Type*}
    (κ : ℝ)
    (J : Finset ℤ) (S : ℤ → Finset ι) (z : ℤ → ι → ℂ) (x : ℤ → ι → ℝ)
    (W : ℝ × ℝ → ℝ) (hW₀ : ∀ p, 0 ≤ W p) (hW : Integrable W)
    (E : ℤ → ℝ) (A K : ℝ) (hE : ∀ i ∈ J, 0 ≤ E i) (hK : 0 ≤ K)
    (hdiag : ∀ i ∈ J, (logCurveWeightedSixNorm κ W (S i) (z i) (x i))^2 ≤ A^2*E i)
    (hfar : ∀ i ∈ J, ∀ j ∈ J, 3 < |i-j| →
      logCurveWeightedBilinearMoment κ W (S j) (S i) (z j) (z i) (x j) (x i) ≤ K*E j*(E i)^2) :
    (logCurveWeightedSixNorm κ W (J.sigma S)
      (fun iv => z iv.1 iv.2) (fun iv => x iv.1 iv.2))^6 ≤
      ((64*7^6:ℝ)*A^6+64*(J.card:ℝ)^5*K)*(∑ i ∈ J, E i)^3 := by
  have hmain := logCurveWeightedSixNorm_bilinear_reduction κ J S z x W hW₀ hW
  have hds : (∑ i ∈ J, (logCurveWeightedSixNorm κ W (S i) (z i) (x i))^6) ≤
      A^6*(∑ i ∈ J, E i)^3 := by
    calc
      _ ≤ ∑ i ∈ J, A^6*(E i)^3 := by
        apply Finset.sum_le_sum
        intro i hi
        convert pow_le_pow_left₀ (sq_nonneg _) (hdiag i hi) 3 using 1 <;> ring
      _ = A^6*∑ i ∈ J, (E i)^3 := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (logCurve_sum_nonneg_powers_le J E hE (by norm_num : (3:ℕ) ≠ 0)) (by positivity)
  have hc (i : ℤ) (hi : i ∈ J) :
      (∑ j ∈ J.filter (fun j => 3 < |i-j|),
        logCurveWeightedBilinearMoment κ W (S j) (S i) (z j) (z i) (x j) (x i)) ≤
      K*(∑ j ∈ J, E j)*(E i)^2 := by
    calc
      _ ≤ ∑ j ∈ J.filter (fun j => 3 < |i-j|), K*E j*(E i)^2 := by
        apply Finset.sum_le_sum
        intro j hj
        exact hfar i hi j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
      _ ≤ ∑ j ∈ J, K*E j*(E i)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun j hj _ => mul_nonneg (mul_nonneg hK (hE j hj)) (sq_nonneg _))
      _ = _ := by rw [← Finset.sum_mul,← Finset.mul_sum]
  have hcs : (∑ i ∈ J, ∑ j ∈ J.filter (fun j => 3 < |i-j|),
      logCurveWeightedBilinearMoment κ W (S j) (S i) (z j) (z i) (x j) (x i)) ≤
      K*(∑ i ∈ J, E i)^3 := by
    calc
      _ ≤ ∑ i ∈ J, K*(∑ j ∈ J, E j)*(E i)^2 := Finset.sum_le_sum hc
      _ = (K*(∑ j ∈ J, E j))*∑ i ∈ J, (E i)^2 := (Finset.mul_sum ..).symm
      _ ≤ (K*(∑ j ∈ J, E j))*(∑ i ∈ J, E i)^2 :=
        mul_le_mul_of_nonneg_left
          (logCurve_sum_nonneg_powers_le J E hE (by norm_num : (2:ℕ) ≠ 0))
          (mul_nonneg hK (Finset.sum_nonneg hE))
      _ = _ := by ring
  have hd := mul_le_mul_of_nonneg_left hds (by positivity : (0:ℝ) ≤ 64*7^6)
  have hf := mul_le_mul_of_nonneg_left hcs (by positivity : (0:ℝ) ≤ 64*(J.card:ℝ)^5)
  nlinarith only [hmain,hd,hf]

private theorem logCurve_sixth_budget_to_square {L E A K k : ℝ}
    (hE : 0 ≤ E) (hA : 0 ≤ A) (hK : 0 ≤ K) (hk : 1 ≤ k)
    (h : L^6 ≤ ((64*7^6:ℝ)*A^6+64*k^5*K)*E^3) :
    L^2 ≤ (14*A+2*k*K^((6:ℝ)⁻¹))^2*E := by
  let R := K^((6:ℝ)⁻¹)
  have hR : 0 ≤ R := Real.rpow_nonneg hK _
  have hR₆ : R^6 = K := by
    simpa only [R,Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow hK (by norm_num : (6:ℕ) ≠ 0)
  have hk₀ : 0 ≤ k := by linarith
  have hkp : k^5 ≤ k^6 := by
    have hp := mul_le_mul_of_nonneg_left hk (pow_nonneg hk₀ 5)
    simpa only [mul_one,← pow_succ] using hp
  have hab := pow_add_pow_le (by positivity : 0 ≤ 14*A)
    (by positivity : 0 ≤ 2*k*R) (by norm_num : (6:ℕ) ≠ 0)
  have hb : (64*7^6:ℝ)*A^6+64*k^5*K ≤ (14*A+2*k*R)^6 := by
    have he : (14*A)^6+(2*k*R)^6 = (64*7^6:ℝ)*A^6+64*k^6*K := by
      rw [mul_pow, mul_pow, mul_pow,hR₆]
      ring
    rw [he] at hab
    have hp := mul_le_mul_of_nonneg_right hkp (mul_nonneg (by norm_num : (0:ℝ) ≤ 64) hK)
    nlinarith only [hab,hp]
  have hc := h.trans (mul_le_mul_of_nonneg_right hb (pow_nonneg hE 3))
  apply (pow_le_pow_iff_left₀ (sq_nonneg L) (by positivity)
    (by norm_num : (3:ℕ) ≠ 0)).mp
  change (L^2)^3 ≤ ((14*A+2*k*R)^2*E)^3
  convert hc using 1 <;> ring

                                                                          
                                                                           
theorem LogCurveDecouplingBound.of_bilinear {k l : ℕ} {A K : ℝ}
    (hk : 0 < k) (hl : 0 < l) (hA : LogCurveDecouplingBound.{u} l A)
    (hK : LogCurveBilinearSixBound.{u} (1/((k*l:ℕ):ℝ)) l l (1/(k:ℝ)) K) :
    LogCurveDecouplingBound.{u} (k*l) (14*A+2*k*K^((6:ℝ)⁻¹)) := by
  have hA₀ := hA.1
  have hK₀ := hK.1
  refine ⟨by positivity,fun κ hκ ι W hW S z x hx => ?_⟩
  let δ : ℝ := 1/((k*l:ℕ):ℝ)
  let e : Fin k × Fin l ≃ Fin (k*l) := finProdFinEquiv
  let T := fun i : Fin k => Finset.univ.sigma (fun j : Fin l => S (e (i,j)))
  let Z := fun i : Fin k => fun jv : (j : Fin l) × ι => z (e (i,jv.1)) jv.2
  let X := fun i : Fin k => fun jv : (j : Fin l) × ι => x (e (i,jv.1)) jv.2
  let E := fun i : Fin k => ∑ j : Fin l,
    (logCurveWeightedSixNorm κ W (S (e (i,j))) (z (e (i,j))) (x (e (i,j))))^2
  let ai := fun i : Fin k => (i:ℕ)/(k:ℝ)
  let R := logCurveIntGridIndex k hk
  let J := Finset.Ico 0 (k:ℤ)
  have hk' : (0:ℝ) < k := by positivity
  have hl' : (0:ℝ) < l := by positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδl : δ*l = 1/(k:ℝ) := by
    dsimp [δ]
    push_cast
    field_simp
  have hfine (i : Fin k) (j : Fin l) (v : ι) (hv : v ∈ S (e (i,j))) :
      x (e (i,j)) v ∈ Icc (ai i+δ*(j:ℕ)) (ai i+δ*((j:ℕ)+1)) := by
    have h := hx (e (i,j)) v hv
    simp only [Nat.cast_mul] at h
    have hcell := logCurve_finGrid_cell hk hl i j
    change x (e (i,j)) v ∈ Icc
      (((e (i,j):Fin (k*l)):ℝ)/(k*l:ℝ))
      ((((e (i,j):Fin (k*l)):ℝ)+1)/(k*l:ℝ)) at h
    rw [hcell.1,hcell.2] at h
    convert h using 1
    dsimp [ai,δ]
    push_cast
    field_simp
  have hai (i : Fin k) : 0 ≤ ai i := by dsimp [ai]; positivity
  have htop (i : Fin k) : ai i+δ*l ≤ 1 := by
    rw [hδl]
    dsimp only [ai]
    rw [← add_div]
    apply (div_le_iff₀ hk').mpr
    simpa only [one_mul] using
      (show ((i:ℕ):ℝ)+1 ≤ k by exact_mod_cast i.isLt)
  have hlin (i : Fin k) :
      (logCurveWeightedSixNorm κ W (T i) (Z i) (X i))^2 ≤ A^2*E i :=
    logCurve_grid_rescale_bound hl hδ hA hκ (hai i) (htop i) ι W hW
      (fun j => S (e (i,j))) (fun j => z (e (i,j))) (fun j => x (e (i,j))) (hfine i)
  have hR (i : ℤ) (hi : i ∈ J) : ((R i:Fin k):ℝ) = (i:ℝ) := by
    have hv := logCurveIntGridIndex_val hk hi
    have hn : 0 ≤ i := (Finset.mem_Ico.mp hi).1
    change (((R i:Fin k):ℕ):ℝ) = _
    rw [hv]
    exact_mod_cast Int.toNat_of_nonneg hn
  have hfar (i : ℤ) (hi : i ∈ J) (j : ℤ) (hj : j ∈ J) (hij : 3 < |i-j|) :
      logCurveWeightedBilinearMoment κ W (T (R j)) (T (R i))
        (Z (R j)) (Z (R i)) (X (R j)) (X (R i)) ≤ K*E (R j)*(E (R i))^2 := by
    have hsep : ai (R j)+δ*l+3*(1/(k:ℝ)) ≤ ai (R i) ∨
        ai (R i)+δ*l+3*(1/(k:ℝ)) ≤ ai (R j) := by
      dsimp only [ai]
      rw [hδl,hR i hi,hR j hj]
      rcases le_total i j with h | h
      · right
        have hh : i+4 ≤ j := by
          rw [abs_of_nonpos (sub_nonpos.mpr h)] at hij
          omega
        have hh' : (i:ℝ)+4 ≤ j := by exact_mod_cast hh
        convert div_le_div_of_nonneg_right hh' hk'.le using 1
        ring
      · left
        have hh : j+4 ≤ i := by
          rw [abs_of_nonneg (sub_nonneg.mpr h)] at hij
          omega
        have hh' : (j:ℝ)+4 ≤ i := by exact_mod_cast hh
        convert div_le_div_of_nonneg_right hh' hk'.le using 1
        ring
    exact hK.2 κ hκ ι ι W hW (ai (R j)) (ai (R i)) (hai _) (htop _) (hai _) (htop _) hsep
      (fun v => S (e (R j,v))) (fun v => S (e (R i,v)))
      (fun v => z (e (R j,v))) (fun v => z (e (R i,v)))
      (fun v => x (e (R j,v))) (fun v => x (e (R i,v))) (hfine (R j)) (hfine (R i))

  have hE : ∀ i ∈ J, 0 ≤ E (R i) := fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbudget := logCurveWeightedSixNorm_bilinear_budget κ J
    (fun i => T (R i)) (fun i => Z (R i)) (fun i => X (R i)) W hW.1 hW.2.1
    (fun i => E (R i)) A K hE hK.1 (fun i _ => hlin (R i)) hfar
  have hcard : (J.card:ℝ) = k := by simp [J,Int.card_Ico]
  rw [hcard] at hbudget
  have hsq := logCurve_sixth_budget_to_square (Finset.sum_nonneg hE) hA.1 hK.1
    (show (1:ℝ) ≤ k by exact_mod_cast hk) hbudget
  have hsum : (∑ i ∈ J, E (R i)) =
      ∑ r, (logCurveWeightedSixNorm κ W (S r) (z r) (x r))^2 := by
    calc
      _ = ∑ i : Fin k, E i := logCurve_intGrid_sum hk E
      _ = _ := by
        dsimp only [E,e]
        exact (logCurve_finGrid_sum (fun r => (logCurveWeightedSixNorm κ W (S r) (z r) (x r))^2)).symm
  rw [hsum] at hsq
  have htotal :
      logCurveWeightedSixNorm κ W (Finset.univ.sigma S)
        (fun rv => z rv.1 rv.2) (fun rv => x rv.1 rv.2) =
      logCurveWeightedSixNorm κ W (J.sigma (fun i => T (R i)))
        (fun iv => Z (R iv.1) iv.2) (fun iv => X (R iv.1) iv.2) := by
    unfold logCurveWeightedSixNorm
    congr 1
    funext r
    simp only [sargosPlanarSum,Finset.sum_sigma]
    have hs := logCurve_intGrid_sum hk (fun i => ∑ v ∈ T i,
      Z i v*fordAdditiveCharacter (X i v*r.1+logCurve κ (X i v)*r.2))
    rw [hs]
    simp only [T,Z,X,Finset.sum_sigma]
    exact logCurve_finGrid_sum _
  rw [htotal]
  exact hsq

                                                                         
theorem LogCurveDecouplingBound.of_bilinear_dyadic {n r : ℕ} {A K : ℝ}
    (hr : r ≤ n) (hA : LogCurveDecouplingBound.{u} (2^(n-r)) A)
    (hK : LogCurveBilinearSixBound.{u} (1/(2:ℝ)^n)
      (2^(n-r)) (2^(n-r)) (1/(2:ℝ)^r) K) :
    LogCurveDecouplingBound.{u} (2^n) (14*A+2*(2:ℝ)^r*K^((6:ℝ)⁻¹)) := by
  have hcount : (2:ℕ)^r*2^(n-r) = 2^n := by
    rw [← pow_add]
    congr 1
    omega
  have hK' : LogCurveBilinearSixBound.{u} (1/(((2:ℕ)^r*2^(n-r):ℕ):ℝ))
      (2^(n-r)) (2^(n-r)) (1/((2^r:ℕ):ℝ)) K := by
    simpa only [hcount,Nat.cast_pow,Nat.cast_ofNat] using hK
  have h := LogCurveDecouplingBound.of_bilinear
    (by positivity : 0 < (2:ℕ)^r) (by positivity : 0 < (2:ℕ)^(n-r)) hA hK'
  simpa only [hcount,Nat.cast_pow,Nat.cast_ofNat] using h

                                                                              
                                                                 
theorem logCurveDecouplingBound_dyadic_iterate (D : ℕ → ℝ)
    {n r t : ℕ} (hr : 0 < r) (hn : r*2^t ≤ n)
    (hD : ∀ j < n, LogCurveDecouplingBound.{u} (2^j) (D j)) :
    LogCurveDecouplingBound.{u} (2^n)
      (14*D (n-r)+2*(2:ℝ)^r*
        (parabolaDyadicBilinearBudget D n r t r r)^((6:ℝ)⁻¹)) := by
  have hpow : (1:ℕ) ≤ 2^t := Nat.succ_le_iff.mpr (by positivity)
  have hrn : r ≤ n :=
    (show r ≤ r*2^t by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hpow (Nat.zero_le r)).trans hn
  exact LogCurveDecouplingBound.of_bilinear_dyadic hrn (hD (n-r) (by omega))
    (logCurveBilinearSixBound_dyadic_iterate D hr le_rfl le_rfl hn hD)

                                                                         
theorem LogCurveDecouplingBound.mono {n : ℕ} {A B : ℝ}
    (hA : LogCurveDecouplingBound.{u} n A) (hAB : A ≤ B) :
    LogCurveDecouplingBound.{u} n B := by
  refine ⟨hA.1.trans hAB,fun κ hκ ι W hW S z x hx => ?_⟩
  exact (hA.2 κ hκ ι W hW S z x hx).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA.1 hAB 2)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

private theorem logCurve_dyadic_exponential_root {C ε : ℝ} (hC : 0 ≤ C)
    {n r t : ℕ} (ht : 1 ≤ t) (hn : r*2^t ≤ n) :
    (parabolaDyadicBilinearBudget (fun j => C*(2:ℝ)^(ε*j)) n r t r r)^((6:ℝ)⁻¹) ≤
      2*C*(2:ℝ)^(ε*n-((3*(t:ℝ)+5)/6)*ε*r+(r:ℝ)/3) := by
  have hbudget : 0 ≤
      parabolaDyadicBilinearBudget (fun j => C*(2:ℝ)^(ε*j)) n r t r r := by
    cases t <;> simp only [parabolaDyadicBilinearBudget] <;> positivity
  have hmajor := parabolaDyadicBilinearBudget_exponential (ε:=ε) (r:=r) hC (a:=r) ht hn
  have hpower :
      (2*C*(2:ℝ)^(ε*n-((3*(t:ℝ)+5)/6)*ε*r+(r:ℝ)/3))^6 =
        64*C^6*(2:ℝ)^(6*ε*n-(3*(t:ℝ)+5)*ε*r+2*r) := by
    rw [mul_pow,mul_pow,←Real.rpow_mul_natCast (by norm_num)]
    norm_num only [show (2:ℝ)^6=64 by norm_num,Nat.cast_ofNat]
    congr 1
    congr 1
    ring
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity)
    (by norm_num : (6:ℕ) ≠ 0)).mp
  have hroot := Real.rpow_inv_natCast_pow hbudget (by norm_num : (6:ℕ) ≠ 0)
  simp only [Nat.cast_ofNat] at hroot
  rw [hroot,hpower]
  exact hmajor.trans (by gcongr; norm_num)

private theorem logCurve_dyadic_exponential_iteration {C ε : ℝ} (hC : 0 ≤ C)
    {n r t : ℕ} (ht : 1 ≤ t) (hn : r*2^t ≤ n)
    (hεt : 8 ≤ (3*(t:ℝ)-1)*ε) :
    14*(C*(2:ℝ)^(ε*((n-r:ℕ):ℝ)))+2*(2:ℝ)^r*
      (parabolaDyadicBilinearBudget (fun j => C*(2:ℝ)^(ε*j)) n r t r r)^((6:ℝ)⁻¹) ≤
        18*C*(2:ℝ)^(ε*((n-r:ℕ):ℝ)) := by
  have hpow : (1:ℕ) ≤ 2^t := Nat.succ_le_iff.mpr (by positivity)
  have hrn : r ≤ n :=
    (show r ≤ r*2^t by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hpow (Nat.zero_le r)).trans hn
  have hroot := logCurve_dyadic_exponential_root (ε:=ε) hC ht hn
  have hexp : ε*n-((3*(t:ℝ)+5)/6)*ε*r+(r:ℝ)/3+r ≤ ε*((n:ℝ)-r) := by
    have hmul := mul_le_mul_of_nonneg_right hεt (Nat.cast_nonneg r : (0:ℝ) ≤ r)
    nlinarith
  have hterm : 2*(2:ℝ)^r*
      (2*C*(2:ℝ)^(ε*n-((3*(t:ℝ)+5)/6)*ε*r+(r:ℝ)/3)) ≤
        4*C*(2:ℝ)^(ε*((n-r:ℕ):ℝ)) := by
    rw [Nat.cast_sub hrn]
    calc
      _ = 4*C*(2:ℝ)^(ε*n-((3*(t:ℝ)+5)/6)*ε*r+(r:ℝ)/3+r) := by
        rw [Real.rpow_add (by norm_num)
          (ε*n-((3*(t:ℝ)+5)/6)*ε*r+(r:ℝ)/3) (r:ℝ),
          Real.rpow_natCast]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) (by positivity)
  have h := mul_le_mul_of_nonneg_left hroot (show 0 ≤ 2*(2:ℝ)^r by positivity)
  linarith








                                                                                      
                                                                            
                                               
theorem exists_logCurveDecouplingBound_dyadic {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ n : ℕ,
      LogCurveDecouplingBound.{u} (2^n) (C*(2:ℝ)^(ε*n)) := by
  obtain ⟨s,hs⟩ := exists_nat_gt ((8:ℝ)/ε)
  let t := s+1
  have ht : 1 ≤ t := by omega
  have hεt : 8 ≤ (3*(t:ℝ)-1)*ε := by
    have h := (div_lt_iff₀ hε).mp hs
    dsimp only [t]
    push_cast
    nlinarith
  obtain ⟨r,hr'⟩ := exists_nat_gt ((5:ℝ)/ε)
  have hr0 : (0:ℝ) < r := (div_pos (by norm_num) hε).trans hr'
  have hr : 0 < r := by exact_mod_cast hr0
  have hεr : 5 ≤ ε*r := by
    have h := (div_lt_iff₀ hε).mp hr'
    nlinarith
  have hcontract : (18:ℝ) ≤ (2:ℝ)^(ε*r) := by
    calc
      18 ≤ (2:ℝ)^(5:ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hεr
  let N := r*2^t
  let C : ℝ := (2:ℝ)^N
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : N ≤ n
    · have hactual := logCurveDecouplingBound_dyadic_iterate
        (fun j => C*(2:ℝ)^(ε*j)) hr hn ih
      apply hactual.mono
      have hnum := logCurve_dyadic_exponential_iteration hC.le ht hn hεt
      have hpow : (1:ℕ) ≤ 2^t := Nat.succ_le_iff.mpr (by positivity)
      have hrn : r ≤ n :=
        (show r ≤ r*2^t by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hpow (Nat.zero_le r)).trans hn
      have he : ε*(n:ℝ)=ε*((n-r:ℕ):ℝ)+ε*r := by
        rw [Nat.cast_sub hrn]; ring
      calc
        _ ≤ 18*C*(2:ℝ)^(ε*((n-r:ℕ):ℝ)) := hnum
        _ ≤ (2:ℝ)^(ε*r)*C*(2:ℝ)^(ε*((n-r:ℕ):ℝ)) := by
          gcongr
        _ = C*(2:ℝ)^(ε*n) := by
          rw [he,Real.rpow_add (by norm_num) (ε*((n-r:ℕ):ℝ)) (ε*r)]
          ring
    · have hnN : n ≤ N := by omega
      have htrivial : LogCurveDecouplingBound.{u} (2^n) (Real.sqrt ((2:ℝ)^n)) := by
        simpa only [Nat.cast_pow,Nat.cast_ofNat] using logCurveDecouplingBound_trivial (2^n)
      apply htrivial.mono
      have hpow : (1:ℝ) ≤ (2:ℝ)^n := one_le_pow₀ (by norm_num)
      calc
        Real.sqrt ((2:ℝ)^n) ≤ (2:ℝ)^n := by
          apply Real.sqrt_le_iff.mpr
          exact ⟨by positivity,by nlinarith⟩
        _ ≤ C := pow_le_pow_right₀ (by norm_num) hnN
        _ ≤ C*(2:ℝ)^(ε*n) := by
          have h := Real.one_le_rpow (by norm_num : (1:ℝ) ≤ 2)
            (show 0 ≤ ε*(n:ℝ) by positivity)
          nlinarith

                                                                     
                                                               
end LogarithmicSixth
end TaoTrudgianYang2025
