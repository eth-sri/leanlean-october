module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.ReflectionDeletion

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentReflectionMass
open CenteredMomentReflectionDeletion HeckeFamily UniqueFactorizationMonoid
open IdealMobiusDivisorSum


def weight (I : Ideal HeckeFamily.O)  := (Real.sqrt (I.absNorm : ℝ))⁻¹
lemma weight_nonneg  I  : 0 ≤ weight I := by unfold weight; positivity
lemma weight_mul  I J  : weight (I*J) = weight I * weight J := by
  simp only [weight, map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), mul_inv_rev]
  ring
lemma weight_one : weight (1 : Ideal HeckeFamily.O) = 1 := by simp [weight]
lemma weight_pow  I   n  : weight (I^n) = weight I ^ n := by
  induction n with
  | zero => simpa only [pow_zero] using weight_one
  | succ n ih => rw [pow_succ,weight_mul,ih,pow_succ]
lemma weight_prod (S : Finset (Ideal HeckeFamily.O)) (f : Ideal HeckeFamily.O → Ideal HeckeFamily.O) :
    weight (∏ P ∈ S,f P) = ∏ P ∈ S,weight (f P) := by
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using weight_one
  | @insert P S h ih => simp only [Finset.prod_insert h,weight_mul,ih]
lemma prime_weight_lt_one  P  (hP : Prime P) : weight P < 1 := by
  have h : (1:ℝ) < P.absNorm := by
    have hh : 2 ≤ P.absNorm := SmoothMobiusCorrection.prime_norm_two_le ⟨P,hP⟩
    exact_mod_cast (by omega : 1 < P.absNorm)
  have hs : 1 < Real.sqrt (P.absNorm : ℝ) := by
    rw [Real.lt_sqrt (by norm_num)]
    simpa using h
  exact inv_lt_one_of_one_lt₀ hs

def exponents (S ) (I : SmoothIdeal S) (P : S)  :=
  (normalizedFactors I.val.val).count P.val
section
variable (S : Finset (Ideal HeckeFamily.O))
include S

lemma reconstruct_exponents    I  :
    (∏ P : S,P.val ^ exponents S I P) = I.val.val := by
  simp only [exponents]
  rw [Finset.prod_coe_sort S (fun P => P ^ (normalizedFactors I.val.val).count P)]
  exact (Finset.prod_multiset_count_of_subset (normalizedFactors I.val.val) S I.property).symm.trans
    (Ideal.prod_normalizedFactors_eq_self I.val.property)
lemma exponents_injective   : Function.Injective (exponents S) := by
  intro I J h
  apply Subtype.ext
  apply Subtype.ext
  rw [← reconstruct_exponents S I,← reconstruct_exponents S J,h]
lemma weight_exponents    I  :
    weight I.val.val = ∏ P : S,weight P.val ^ exponents S I P := by
  conv_lhs => rw [← reconstruct_exponents S I]
  simp only [exponents]
  rw [Finset.prod_coe_sort S (fun P => P ^ (normalizedFactors I.val.val).count P),
    Finset.prod_coe_sort S (fun P => weight P ^ (normalizedFactors I.val.val).count P), weight_prod]
  simp only [weight_pow]

end

lemma hasSum_geometric_pi {α : Type*} [Fintype α] (r : α → ℝ)
    (hr : ∀ a, 0 ≤ r a) (hr1 : ∀ a, r a < 1) :
    HasSum (fun n : α → ℕ => ∏ a,r a ^ n a) (∏ a,(1-r a)⁻¹) := by
  classical
  apply Fintype.induction_empty_option (P := fun β _ => ∀ (r : β → ℝ),
    (∀ a, 0 ≤ r a) → (∀ a, r a < 1) →
    HasSum (fun n : β → ℕ => ∏ a,r a ^ n a) (∏ a,(1-r a)⁻¹)) ?_ ?_ ?_ α r hr hr1
  · intro α β _ e ih r hr hr1
    let : Fintype α := Fintype.ofEquiv β e.symm
    have h := ih (r ∘ e) (fun a => hr (e a)) (fun a => hr1 (e a))
    let E : (β → ℕ) ≃ (α → ℕ) := Equiv.arrowCongr e.symm (Equiv.refl ℕ)
    have he := E.hasSum_iff.mpr h
    convert he using 1
    · funext n
      exact (e.prod_comp (fun b => r b ^ n b)).symm
    · exact (e.prod_comp (fun b => (1-r b)⁻¹)).symm
  · intro r _ _
    simp
  · intro α _ ih r hr hr1
    have h0 := hasSum_geometric_of_lt_one (hr none) (hr1 none)
    have ht := ih (fun a => r (some a)) (fun a => hr (some a)) (fun a => hr1 (some a))
    have hs := h0.summable.mul_of_nonneg ht.summable (pow_nonneg (hr none))
      (fun n => Finset.prod_nonneg (fun a _ => pow_nonneg (hr (some a)) (n a)))
    have hp := h0.mul ht hs
    have he := (Equiv.piOptionEquivProd (β := fun _ : Option α => ℕ)).hasSum_iff.mpr hp
    simpa only [Function.comp_def, Fintype.prod_option, Equiv.piOptionEquivProd_apply] using he

section
variable (S : Finset (Ideal HeckeFamily.O))
include S

section
variable (hS : ∀ P ∈ S,Prime P)
include hS

lemma smooth_summable     :
    Summable (fun I : SmoothIdeal S => weight I.val.val) := by
  have hs := (hasSum_geometric_pi (fun P : S => weight P.val)
    (fun P => weight_nonneg P.val) (fun P => prime_weight_lt_one P.val (hS P.val P.property))).summable
  exact (hs.comp_injective (exponents_injective S)).congr (fun I => (weight_exponents S I).symm)

lemma smooth_mass_le_euler     :
    (∑' I : SmoothIdeal S,weight I.val.val) ≤ ∏ P ∈ S,(1-weight P)⁻¹ := by
  have hh := hasSum_geometric_pi (fun P : S => weight P.val)
    (fun P => weight_nonneg P.val) (fun P => prime_weight_lt_one P.val (hS P.val P.property))
  have h := Summable.tsum_le_tsum_of_inj (exponents S) (exponents_injective S)
    (fun n _ => Finset.prod_nonneg (fun P _ => pow_nonneg (weight_nonneg P.val) (n P)))
    (fun I => (weight_exponents S I).le) (smooth_summable S hS) hh.summable
  rw [hh.tsum_eq,Finset.prod_coe_sort S (fun P => (1-weight P)⁻¹)] at h
  exact h

end

lemma deletion_mass   :
    (∑ D ∈ S.powerset, weight (∏ P ∈ D,P)) = ∏ P ∈ S,(1+weight P) := by
  simp_rw [weight_prod]
  exact (Finset.prod_one_add S).symm

end

def localMass (P : Ideal HeckeFamily.O)  := (1+weight P)/(1-weight P)
section
variable (P : Ideal HeckeFamily.O) (hP : Prime P)
include P hP

lemma localMass_nonneg     : 0 ≤ localMass P := div_nonneg (by linarith [weight_nonneg P]) (sub_pos.mpr (prime_weight_lt_one P hP)).le
lemma prime_weight_le     : weight P ≤ 3/4 := by
  have hn : (2:ℝ) ≤ P.absNorm := by
    exact_mod_cast (SmoothMobiusCorrection.prime_norm_two_le ⟨P,hP⟩ : 2 ≤ P.absNorm)
  have hs : 4/3 ≤ Real.sqrt (P.absNorm : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  rw [weight,inv_eq_one_div,div_le_iff₀ (by linarith : 0 < Real.sqrt (P.absNorm : ℝ))]
  nlinarith
lemma localMass_le_seven     : localMass P ≤ 7 := by
  apply (div_le_iff₀ (sub_pos.mpr (prime_weight_lt_one P hP))).mpr
  linarith [prime_weight_le P hP]
lemma localMass_le_three     (hn : (4:ℝ) ≤ P.absNorm) :
    localMass P ≤ 3 := by
  have hs : 2 ≤ Real.sqrt (P.absNorm : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    linarith
  have hw : weight P ≤ 1/2 := by
    rw [weight,inv_eq_one_div,div_le_iff₀ (by linarith : 0 < Real.sqrt (P.absNorm : ℝ))]
    linarith
  apply (div_le_iff₀ (sub_pos.mpr (prime_weight_lt_one P hP))).mpr
  linarith

end

theorem euler_mass_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal HeckeFamily.O)) (_hS : ∀ P ∈ S,Prime P),
      (∏ P ∈ S,localMass P) ≤ C * (Ideal.absNorm (∏ P ∈ S,P) : ℝ)^ε := by
  obtain ⟨B,hB⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hε).eventually (Filter.eventually_ge_atTop (3:ℝ)))
  let K : ℕ := ⌈max 4 B⌉₊
  let smallIdeals := ConcretePrimeRowBridge.idealsUpTo K
  have hK : max 4 B ≤ (K:ℝ) := Nat.le_ceil _
  refine ⟨(7:ℝ)^smallIdeals.card,by positivity,?_⟩
  intro S hS
  have hpoint (P : Ideal HeckeFamily.O) (hP : P ∈ S) :
      localMass P ≤ (if P ∈ smallIdeals then 7 else 1)*(P.absNorm:ℝ)^ε := by
    have hn : (1:ℝ) ≤ P.absNorm := by
      have hh : 2 ≤ P.absNorm := SmoothMobiusCorrection.prime_norm_two_le ⟨P,hS P hP⟩
      exact_mod_cast (by omega : 1 ≤ P.absNorm)
    have he : 1 ≤ (P.absNorm:ℝ)^ε := Real.one_le_rpow hn hε.le
    by_cases hp : P ∈ smallIdeals
    · simp only [ite_eq_left hp]
      grind [localMass_le_seven]
    · have hpk : (K:ℝ) < P.absNorm := by
        have hh : ¬ P.absNorm ≤ K := by
          intro h
          apply hp
          exact ConcretePrimeRowBridge.mem_idealsUpTo.mpr ⟨by exact_mod_cast hn,h⟩
        exact_mod_cast Nat.lt_of_not_ge hh
      have h4 : (4:ℝ) ≤ P.absNorm := (le_max_left _ _).trans (hK.trans hpk.le)
      have hb : B ≤ (P.absNorm:ℝ) := (le_max_right _ _).trans (hK.trans hpk.le)
      simp only [ite_eq_right hp,one_mul]
      grind [localMass_le_three]
  have hc : (S.filter (· ∈ smallIdeals)).card ≤ smallIdeals.card :=
    Finset.card_le_card (fun P hP => (Finset.mem_filter.mp hP).2)
  calc
    (∏ P ∈ S,localMass P) ≤ ∏ P ∈ S,((if P ∈ smallIdeals then 7 else 1)*(P.absNorm:ℝ)^ε) :=
      Finset.prod_le_prod₀ (fun P hP => localMass_nonneg P (hS P hP)) hpoint
    _ = (7:ℝ)^(S.filter (· ∈ smallIdeals)).card * (Ideal.absNorm (∏ P ∈ S,P):ℝ)^ε := by
      rw [Finset.prod_mul_distrib,← Finset.prod_filter]
      simp only [Finset.prod_const,Real.finsetProd_rpow S _ (fun _ _ => Nat.cast_nonneg _) ε,
        map_prod,Nat.cast_prod]
    _ ≤ _ := (by gcongr <;> first | assumption | positivity | linarith)

def coefficient (η ηi : Character) (S )
    (D : Finset (Ideal HeckeFamily.O)) (H : SmoothIdeal S)  :=
  (moebius (∏ P ∈ D,P) : ℂ) * idealCoeff η (∏ P ∈ D,P) * idealCoeff ηi H.val.val /
    (Real.sqrt ((Ideal.absNorm (∏ P ∈ D,P):ℝ) * norm H.val) : ℂ)

section
variable (η ηi : Character) (S : Finset (Ideal HeckeFamily.O))
include η ηi S

lemma coefficient_norm_le    
     D  (hD : ∀ P ∈ D,Prime P)  H  :
    ‖coefficient η ηi S D H‖ ≤ weight (∏ P ∈ D,P) * weight H.val.val := by
  rw [coefficient,subset_product_moebius D hD]
  simp only [norm_div,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  have h : ‖idealCoeff η (∏ P ∈ D,P)‖ * ‖idealCoeff ηi H.val.val‖ ≤ 1 :=
    (mul_le_mul (idealCoeff_norm_le_one η _) (idealCoeff_norm_le_one ηi _)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  apply (div_le_div_of_nonneg_right h (Real.sqrt_nonneg _)).trans_eq
  simp only [CenteredMomentReflectionDeletion.norm,weight,Real.sqrt_mul (Nat.cast_nonneg _),one_div,mul_inv_rev]
  ring

section
variable (hS : ∀ P ∈ S,Prime P)
include hS

lemma coefficient_summable_norm    
       D  (hD : D ⊆ S) :
    Summable (fun H : SmoothIdeal S => ‖coefficient η ηi S D H‖) := by
  apply ((smooth_summable S hS).mul_left (weight (∏ P ∈ D,P))).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  exact coefficient_norm_le η ηi S D (fun P hP => hS P (hD hP))

lemma coefficient_mass_le_euler    
      :
    (∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, ‖coefficient η ηi S D H‖) ≤
      ∏ P ∈ S,localMass P := by
  have hD (D : Finset (Ideal HeckeFamily.O)) (hD : D ∈ S.powerset) :
      (∑' H : SmoothIdeal S, ‖coefficient η ηi S D H‖) ≤
        weight (∏ P ∈ D,P) * (∏ P ∈ S,(1-weight P)⁻¹) := by
    have hsub := Finset.mem_powerset.mp hD
    apply ((coefficient_summable_norm η ηi S hS D hsub).tsum_le_tsum
      (coefficient_norm_le η ηi S D (fun P hP => hS P (hsub hP)))
      ((smooth_summable S hS).mul_left (weight (∏ P ∈ D,P)))).trans
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (smooth_mass_le_euler S hS) (weight_nonneg _)
  apply (Finset.sum_le_sum hD).trans_eq
  rw [← Finset.sum_mul,deletion_mass,← Finset.prod_mul_distrib]
  rfl

lemma coefficient_mass_summable    
      :
    Summable (fun H : SmoothIdeal S => ∑ D ∈ S.powerset,‖coefficient η ηi S D H‖) := summable_sum (fun D hD => coefficient_summable_norm η ηi S hS D (Finset.mem_powerset.mp hD))

end

end

theorem reflection_mass_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal HeckeFamily.O)) (_hS : ∀ P ∈ S,Prime P)
      (η ηi : Character),
      Summable (fun H : SmoothIdeal S => ∑ D ∈ S.powerset,‖coefficient η ηi S D H‖) ∧
      (∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, ‖coefficient η ηi S D H‖) ≤
        C * (Ideal.absNorm (∏ P ∈ S,P):ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := euler_mass_subpower ε hε
  exact ⟨C,hC,fun S hS η ηi => ⟨coefficient_mass_summable η ηi S hS,
    (coefficient_mass_le_euler η ηi S hS).trans (hbound S hS)⟩⟩

def unitSmooth (S ) : SmoothIdeal S :=
  ⟨⟨1,one_ne_zero⟩,by
    change (normalizedFactors (1 : Ideal HeckeFamily.O)).toFinset ⊆ S
    rw [normalizedFactors_one]
    exact Finset.empty_subset _⟩

end SevenEighths.CenteredMomentReflectionMass
end

end OAI
