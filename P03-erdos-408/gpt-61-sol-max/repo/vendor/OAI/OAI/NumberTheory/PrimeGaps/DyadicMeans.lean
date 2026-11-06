module
public import Mathlib.Tactic

public import OAI.NumberTheory.PrimeGaps.VaughanBounds

@[expose] public section

namespace OAI

namespace LargePrimeGaps

open Filter

open Set   MeasureTheory

open scoped Topology ContDiff

open Asymptotics

 

 

open scoped Classical

 

open Topology

open scoped Convolution   Pointwise

open scoped ComplexConjugate

section
variable {q : ℕ} (Q X U V D E : ℕ) (hE : E ≤ V+1) (hD : 0 < D) (hU : X/D ≤ U) (k : ℕ) (hk : X+1 ≤ 2^k) (χ : DirichletCharacter ℂ q) {a b m n x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {t z : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n) (hx : 0 ≤ x) (ht : 0 < t) (hz : 0 ≤ z) (T j : ℕ)

theorem primitiveCharacterMean_sum {ι : Type*} (Q : ℕ) (s : Finset ι)
    (f : ι→(q:Fin Q)→DirichletCharacter ℂ (q.val+1)→ℝ) :
    primitiveCharacterMean Q (fun q χ=>∑ i∈s,f i q χ)=
      ∑ i∈s,primitiveCharacterMean Q (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp [primitiveCharacterMean]
  | cons a s ha ih =>
    simp only [Finset.sum_cons,primitiveCharacterMean_add,ih]

include hE in
theorem vaughan_hyperbolaBlock_zero_left    
        :
    hyperbolaBlock X D E
      (fun m=>if V < m then (ArithmeticFunction.moebius m:ℂ) else 0)
      (fun n=>(vaughanSecondCoefficient U n:ℂ)) χ=0 := by
  apply Finset.sum_eq_zero
  intro m hm
  have h:=Finset.mem_Ico.mp hm
  have hn:¬V < m:=by omega
  simp [hn]

include hD hU in
theorem vaughan_hyperbolaBlock_zero_right    
          :
    hyperbolaBlock X D E
      (fun m=>if V < m then (ArithmeticFunction.moebius m:ℂ) else 0)
      (fun n=>(vaughanSecondCoefficient U n:ℂ)) χ=0 := by
  apply Finset.sum_eq_zero
  intro m hm
  have hmD: D ≤ m:=(Finset.mem_Ico.mp hm).1
  have hnU:X/m ≤ U:=(Nat.div_le_div_left hmD hD).trans hU
  have hz:(∑ n∈Finset.range (X/m+1),(vaughanSecondCoefficient U n:ℂ)*χ (n:ZMod q))=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hnle:n ≤ U:=by have h:=Finset.mem_range.mp hn; omega
    simp [vaughanSecondCoefficient_zero_of_le hnle]
  rw [hz,mul_zero]

include hk in
theorem vaughan_typeII_active_dyadic      
      :
    arithmeticCharacterSum X
      ((ArithmeticFunction.moebius-arithmeticCutoff V ArithmeticFunction.moebius)*
        vaughanSecondCoefficient U) χ=
      ∑ j∈(Finset.range k).filter (fun j=>V+1 < 2^(j+1) ∧ U < X/2^j),
        hyperbolaBlock X (2^j) (2^(j+1))
          (fun m=>if V < m then (ArithmeticFunction.moebius m:ℂ) else 0)
          (fun n=>(vaughanSecondCoefficient U n:ℂ)) χ := by
  rw [vaughan_typeII_dyadic X U V k hk]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro j hj hj'
  
  by_cases hl:V+1 < 2^(j+1)
  · simp_all [vaughan_hyperbolaBlock_zero_right]
  simp_all [vaughan_hyperbolaBlock_zero_left]

include hk in
theorem vaughan_typeII_active_mean     :
    primitiveCharacterMean Q (fun _ χ=>‖arithmeticCharacterSum X
      ((ArithmeticFunction.moebius-arithmeticCutoff V ArithmeticFunction.moebius)*
        vaughanSecondCoefficient U) χ‖) ≤
      ∑ j∈(Finset.range k).filter (fun j=>V+1 < 2^(j+1) ∧ U < X/2^j),
        ((k:ℝ)+1)*sieveBilinearConstant Q (2^(j+1)) (X/2^j+1)*
          Real.sqrt ((2^(j+1):ℕ):ℝ)*
            (Real.sqrt ((X/2^j+1:ℕ):ℝ)*Real.log ((X/2^j+1:ℕ):ℝ)) := by
  have h:=primitiveCharacterMean_mono (Q:=Q)
    (f:=fun _ χ=>‖arithmeticCharacterSum X
      ((ArithmeticFunction.moebius-arithmeticCutoff V ArithmeticFunction.moebius)*
        vaughanSecondCoefficient U) χ‖)
    (g:=fun _ χ=>∑ j∈(Finset.range k).filter (fun j=>V+1 < 2^(j+1) ∧ U < X/2^j),
      ‖hyperbolaBlock X (2^j) (2^(j+1))
        (fun m=>if V < m then (ArithmeticFunction.moebius m:ℂ) else 0)
        (fun n=>(vaughanSecondCoefficient U n:ℂ)) χ‖) (fun _ χ=>by
          rw [vaughan_typeII_active_dyadic X U V k hk]
          exact norm_sum_le _ _)
  rw [primitiveCharacterMean_sum] at h
  apply h.trans
  apply Finset.sum_le_sum
  intro j _
  exact vaughan_hyperbolaBlock_mean Q X U V (2^j) (2^(j+1)) k
    (pow_pos (by omega) _) ((Nat.add_le_add_right (Nat.div_le_self _ _) 1).trans hk)

include ha hb in
theorem sqrt_add_le_sqrt_add_sqrt       :
    Real.sqrt (a+b) ≤ Real.sqrt a+Real.sqrt b := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [Real.sq_sqrt (add_nonneg ha hb)]
  nlinarith [Real.sq_sqrt ha,Real.sq_sqrt hb,Real.sqrt_nonneg a,Real.sqrt_nonneg b]

include hm hn hz in
theorem sqrt_bilinear_expansion         :
    (Real.sqrt (m+z)*Real.sqrt (n+z))*Real.sqrt m*Real.sqrt n ≤
      m*n+Real.sqrt z*(m*Real.sqrt n+n*Real.sqrt m)+z*Real.sqrt m*Real.sqrt n := by
  have h:=mul_le_mul (sqrt_add_le_sqrt_add_sqrt hm hz) (sqrt_add_le_sqrt_add_sqrt hn hz)
    (Real.sqrt_nonneg _) (by positivity : 0 ≤ Real.sqrt m+Real.sqrt z)
  calc
    _ ≤ ((Real.sqrt m+Real.sqrt z)*(Real.sqrt n+Real.sqrt z))*Real.sqrt m*Real.sqrt n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    _ = (Real.sqrt m)^2*(Real.sqrt n)^2+
        Real.sqrt z*((Real.sqrt m)^2*Real.sqrt n+(Real.sqrt n)^2*Real.sqrt m)+
        (Real.sqrt z)^2*Real.sqrt m*Real.sqrt n := by ring
    _ = _ := by rw [Real.sq_sqrt hm,Real.sq_sqrt hn,Real.sq_sqrt hz]

include ha hb hx in
theorem sqrt_product_le_twice      
      (hab : a*b ≤ 4*x) :
    Real.sqrt a*Real.sqrt b ≤ 2*Real.sqrt x := by
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  grind

include hm hn hx ht hz in
theorem sqrt_bilinear_hyperbolic_bound  
             
    (hmn : m*n ≤ 4*x) (hmt : m*t ≤ 4*x) (hnt : n*t ≤ 4*x) :
    (Real.sqrt (m+z)*Real.sqrt (n+z))*Real.sqrt m*Real.sqrt n ≤
      4*x+Real.sqrt z*(8*x/Real.sqrt t)+z*(2*Real.sqrt x) := by
  have hmn' := sqrt_product_le_twice hm hn hx hmn
  have hmt' := sqrt_product_le_twice hm ht.le hx hmt
  have hnt' := sqrt_product_le_twice hn ht.le hx hnt
  have hcross : (m*Real.sqrt n+n*Real.sqrt m)*Real.sqrt t ≤ 8*x := by
    calc
      _ = (Real.sqrt m*Real.sqrt n)*
          (Real.sqrt m*Real.sqrt t+Real.sqrt n*Real.sqrt t) := by
        grind
      _ ≤ (2*Real.sqrt x)*(4*Real.sqrt x) :=
        mul_le_mul hmn' (by linarith) (by positivity) (by positivity)
      _ = _ := by nlinarith [Real.sq_sqrt hx]
  have hc : m*Real.sqrt n+n*Real.sqrt m ≤ 8*x/Real.sqrt t :=
    (le_div_iff₀ (Real.sqrt_pos.mpr ht)).mpr hcross
  apply (sqrt_bilinear_expansion hm hn hz).trans
  simpa only [mul_assoc] using
    (add_le_add (add_le_add hmn (mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg _)))
      (mul_le_mul_of_nonneg_left hmn' hz))

theorem vaughan_active_dimensions  
    (hleft : T+1 < 2^(j+1)) (hright : T < X/2^j) :
    (2^(j+1))*(X/2^j+1) ≤ 4*X ∧
    (2^(j+1))*(T+1) ≤ 4*X ∧ (X/2^j+1)*(T+1) ≤ 4*X := by
  have hD : 0 < 2^j := pow_pos (by omega) _
  have hprod : (T+1)*2^j ≤ X := (Nat.le_div_iff_mul_le hD).mp (by omega)
  have hX : 2^j ≤ X := by nlinarith
  have hdiv := Nat.div_mul_le_self X (2^j)
  have hpow : 2^(j+1)=2*2^j := by rw [pow_succ]; omega
  have harea : (2^(j+1))*(X/2^j+1) ≤ 4*X := by rw [hpow]; nlinarith
  refine ⟨harea,?_,?_⟩
  · rw [hpow]
    nlinarith
  · exact (Nat.mul_le_mul_left (X/2^j+1) hleft.le).trans (by simpa only [Nat.mul_comm] using harea)

end

noncomputable def vaughanBilinearBound (Q X T : ℕ)  :=
  let z:ℝ:=(Q:ℝ)^2*(harmonic (Q^2):ℝ)
  4*(X:ℝ)+Real.sqrt z*(8*(X:ℝ)/Real.sqrt (T+1:ℕ))+z*(2*Real.sqrt X)

section
variable (Q X T j k : ℕ)

theorem harmonic_real_nonneg  n  : 0 ≤ (harmonic n:ℝ) := by
  by_cases hn:n=0
  · simp [hn]
  · exact_mod_cast (harmonic_pos hn).le

theorem vaughanBilinearBound_nonneg   : 0 ≤ vaughanBilinearBound Q X T := by
  have hh:=harmonic_real_nonneg (Q^2)
  unfold vaughanBilinearBound
  positivity

theorem vaughan_active_bilinear_bound  
    (hleft : T+1 < 2^(j+1)) (hright : T < X/2^j) :
    sieveBilinearConstant Q (2^(j+1)) (X/2^j+1)*
      Real.sqrt ((2^(j+1):ℕ):ℝ)*Real.sqrt ((X/2^j+1:ℕ):ℝ) ≤
        vaughanBilinearBound Q X T := by
  obtain ⟨hmn,hmt,hnt⟩:=vaughan_active_dimensions X T j hleft hright
  apply sqrt_bilinear_hyperbolic_bound (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (by positivity) (mul_nonneg (sq_nonneg _) (harmonic_real_nonneg _))
  · exact_mod_cast hmn
  · exact_mod_cast hmt
  · exact_mod_cast hnt

theorem vaughan_typeII_equal_cutoff_mean   (hk : X+1 ≤ 2^k) :
    primitiveCharacterMean Q (fun _ χ=>‖arithmeticCharacterSum X
      ((ArithmeticFunction.moebius-arithmeticCutoff T ArithmeticFunction.moebius)*
        vaughanSecondCoefficient T) χ‖) ≤
      (k:ℝ)*((k:ℝ)+1)*vaughanBilinearBound Q X T*Real.log (X+1:ℕ) := by
  apply (vaughan_typeII_active_mean Q X T T k hk).trans
  let K:=((k:ℝ)+1)*vaughanBilinearBound Q X T*Real.log (X+1:ℕ)
  have hK : 0 ≤ K := mul_nonneg
    (mul_nonneg (by positivity) (vaughanBilinearBound_nonneg _ _ _))
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ X+1 by omega)))
  apply le_trans (b:=∑ _j∈(Finset.range k).filter (fun j=>T+1 < 2^(j+1) ∧ T < X/2^j),K)
  · apply Finset.sum_le_sum
    intro j hj
    obtain ⟨hl,hr⟩ := (Finset.mem_filter.mp hj).2
    have hb:=vaughan_active_bilinear_bound Q X T j hl hr
    have hlog : Real.log ((X/2^j+1:ℕ):ℝ) ≤ Real.log (X+1:ℕ) :=
      log_nat_monotone (Nat.add_le_add_right (Nat.div_le_self _ _) 1)
    have hlog0 : 0 ≤ Real.log ((X/2^j+1:ℕ):ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ X/2^j+1 by omega))
    calc
      _ = ((k:ℝ)+1)*(sieveBilinearConstant Q (2^(j+1)) (X/2^j+1)*
          Real.sqrt ((2^(j+1):ℕ):ℝ)*Real.sqrt ((X/2^j+1:ℕ):ℝ))*
            Real.log ((X/2^j+1:ℕ):ℝ) := by ring
      _ ≤ K := mul_le_mul (mul_le_mul_of_nonneg_left hb (by positivity)) hlog hlog0
        (mul_nonneg (by positivity) (vaughanBilinearBound_nonneg _ _ _))
  · rw [Finset.sum_const,nsmul_eq_mul]
    have hc : (((Finset.range k).filter (fun j=>T+1 < 2^(j+1) ∧ T < X/2^j)).card:ℝ) ≤ k := by
      exact_mod_cast (Finset.card_filter_le (Finset.range k) _).trans_eq (Finset.card_range k)
    exact (mul_le_mul_of_nonneg_right hc hK).trans_eq (by dsimp [K]; ring)

theorem primitiveCharacterMean_mono_primitive  {Q} 
     {f g} 
    (h : ∀ q χ,χ.IsPrimitive→f q χ ≤ g q χ) :
    primitiveCharacterMean Q f ≤ primitiveCharacterMean Q g := by
  apply Finset.sum_le_sum
  intro q _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  simp_all

theorem primitiveCharacterMean_constant_le    {A}  (hA : 0 ≤ A) :
    primitiveCharacterMean Q (fun _ _=>A) ≤ (Q:ℝ)^2*A := by
  classical
  calc
    _ ≤ ∑ _q:Fin Q,(Q:ℝ)*A := by
      apply Finset.sum_le_sum
      intro q _
      let d:=q.val+1
      have hd:0 < d:=by dsimp [d]; omega
      let : NeZero d:=⟨by omega⟩
      
      have hcard:Fintype.card (DirichletCharacter ℂ d)=d.totient := by
        simpa only [Nat.card_eq_fintype_card] using
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ d
      have hnum:(((Finset.univ : Finset (DirichletCharacter ℂ d)).filter
          DirichletCharacter.IsPrimitive).card:ℝ) ≤ d.totient := by
        exact_mod_cast (Finset.card_filter_le (Finset.univ : Finset (DirichletCharacter ℂ d)) _).trans_eq
          (by rw [Finset.card_univ,hcard])
      change (d:ℝ)/d.totient*(∑ _χ∈(Finset.univ : Finset (DirichletCharacter ℂ d)).filter
        DirichletCharacter.IsPrimitive,A) ≤ _
      rw [Finset.sum_const,nsmul_eq_mul]
      calc
        _ ≤ (d:ℝ)/d.totient*((d.totient:ℝ)*A) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnum hA) (by positivity)
        _ = (d:ℝ)*A := by field_simp
        _ ≤ (Q:ℝ)*A := mul_le_mul_of_nonneg_right (by exact_mod_cast (show d ≤ Q by dsimp [d]; omega)) hA
    _ = _ := by simp; ring

end

noncomputable def vaughanShortBound (Q X T : ℕ)  :=
  let K:=Real.sqrt Q*(1+Real.log Q)
  (T:ℝ)*Real.log T+(T:ℝ)*(2*Real.log (X+1:ℕ)*K)+
    ((T*T:ℕ)*Real.log (T*T:ℕ))*K

theorem log_nat_nonneg (n : ℕ) : 0 ≤ Real.log (n:ℝ) := by
  simpa using log_nat_monotone (Nat.zero_le n)

theorem vaughanShortBound_nonneg  Q X T  : 0 ≤ vaughanShortBound Q X T := by
  
  
  
  
  unfold vaughanShortBound
  positivity

section
variable {q Q : ℕ} (hq : 1 < q) (hqQ : q ≤ Q) {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {P : ℕ} (hQP : Q ≤ P) (X T : ℕ)

include hqQ in
theorem polya_constant_le     :
    Real.sqrt q*(harmonic q:ℝ) ≤ Real.sqrt Q*(1+Real.log Q) := mul_le_mul (Real.sqrt_le_sqrt (by exact_mod_cast hqQ))
    ((harmonic_le_one_add_log q).trans (add_le_add le_rfl (log_nat_monotone hqQ)))
    (harmonic_real_nonneg _) (Real.sqrt_nonneg _)

include hq hqQ hχ in
theorem primitive_vaughan_bound_uniform      
          :
    ‖arithmeticCharacterSum X ArithmeticFunction.vonMangoldt χ‖ ≤
      vaughanShortBound Q X T+
      ‖arithmeticCharacterSum X
        ((ArithmeticFunction.moebius-arithmeticCutoff T ArithmeticFunction.moebius)*
          vaughanSecondCoefficient T) χ‖ := by
  rw [vaughan_typeII_exact]
  apply (primitive_vaughan_bound hq hχ X T T).trans
  apply add_le_add_left
  unfold vaughanShortBound
  apply add_le_add
  · apply add_le_add_right
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (polya_constant_le hqQ)
      (mul_nonneg (by norm_num) (log_nat_nonneg _))) (Nat.cast_nonneg _)
  · exact mul_le_mul_of_nonneg_left (polya_constant_le hqQ)
      (mul_nonneg (Nat.cast_nonneg _) (log_nat_nonneg _))

theorem finite_vaughan_primitive_mean (Q X T k : ℕ) (hk : X+1 ≤ 2^k) :
    primitiveCharacterMean Q (fun q χ=>if 1 < q.val+1 then
      ‖arithmeticCharacterSum X ArithmeticFunction.vonMangoldt χ‖ else 0) ≤
      (Q:ℝ)^2*vaughanShortBound Q X T+
        (k:ℝ)*((k:ℝ)+1)*vaughanBilinearBound Q X T*Real.log (X+1:ℕ) := by
  have h:=primitiveCharacterMean_mono_primitive (Q:=Q)
    (f:=fun q χ=>if 1 < q.val+1 then ‖arithmeticCharacterSum X ArithmeticFunction.vonMangoldt χ‖ else 0)
    (g:=fun _ χ=>vaughanShortBound Q X T+
      ‖arithmeticCharacterSum X
        ((ArithmeticFunction.moebius-arithmeticCutoff T ArithmeticFunction.moebius)*
          vaughanSecondCoefficient T) χ‖) (fun q χ hχ=>by
      by_cases hq:1 < q.val+1
      · simp_all [primitive_vaughan_bound_uniform]
      · rw [ite_eq_right hq]
        exact add_nonneg (vaughanShortBound_nonneg _ _ _) (norm_nonneg _))
  rw [primitiveCharacterMean_add] at h
  exact h.trans (add_le_add (primitiveCharacterMean_constant_le _ (vaughanShortBound_nonneg _ _ _))
    (vaughan_typeII_equal_cutoff_mean Q X T k hk))

include hq hχ in
theorem primitive_ne_one      
      : χ ≠ 1 := by
  let : NeZero q:=⟨by omega⟩
  intro he
  have hc:=hχ
  rw [DirichletCharacter.isPrimitive_def,he,DirichletCharacter.conductor_one] at hc
  omega

theorem primeCharacterPrefix_nat     (χ : DirichletCharacter ℂ q) :
    primeCharacterPrefix (X:ℝ) χ=arithmeticCharacterSum X ArithmeticFunction.vonMangoldt χ := by
  have he : Finset.Ioc 0 X=Finset.Icc 1 X := by ext n; simp; omega
  simp only [primeCharacterPrefix,arithmeticCharacterSum,Nat.floor_natCast,he,mul_comm]

theorem primitiveErrorMass_eq_vonMangoldt_sum    {q}  (hq : 1 < q) :
    primitiveErrorMass (X:ℝ) q=
      ∑ χ∈(Finset.univ : Finset (DirichletCharacter ℂ q)).filter DirichletCharacter.IsPrimitive,
        ‖arithmeticCharacterSum X ArithmeticFunction.vonMangoldt χ‖ := by
  apply Finset.sum_congr rfl
  simp_all [primeCharacterError, primitive_ne_one, primeCharacterPrefix_nat]

theorem sum_Icc_one_eq_sum_fin {A : Type*} [AddCommMonoid A] (F : ℕ→A)  Q  :
    (∑ d∈Finset.Icc 1 Q,F d)=∑ q:Fin Q,F (q.val+1) := by
  classical
  apply Finset.sum_bij (fun d hd=>(⟨d-1,by have h:=Finset.mem_Icc.mp hd; omega⟩:Fin Q))
  · intro d hd
    exact Finset.mem_univ _
  · grind
  · intro q _
    refine ⟨q.val+1,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,?_⟩
    apply Fin.ext
    simp
  simp_all

theorem conductor_interval_error_le_vaughan (Q X T k R : ℕ) (hR : 1 ≤ R)
    (hk : X+1 ≤ 2^k) :
    (R:ℝ)*(∑ d∈Finset.Ioc R Q,primitiveErrorMass (X:ℝ) d/(d.totient:ℝ)) ≤
      (Q:ℝ)^2*vaughanShortBound Q X T+
        (k:ℝ)*((k:ℝ)+1)*vaughanBilinearBound Q X T*Real.log (X+1:ℕ) := by
  have hf : (Finset.Icc 1 Q).filter (fun d=>R < d)=Finset.Ioc R Q := by
    grind
  have he : (∑ d∈Finset.Ioc R Q,primitiveErrorMass (X:ℝ) d/(d.totient:ℝ))=
      ∑ q:Fin Q,if R < q.val+1 then primitiveErrorMass (X:ℝ) (q.val+1)/((q.val+1).totient:ℝ) else 0 := by
    rw [←hf,Finset.sum_filter,sum_Icc_one_eq_sum_fin]
  rw [he,Finset.mul_sum]
  apply le_trans (b:=primitiveCharacterMean Q (fun q χ=>if 1 < q.val+1 then
    ‖arithmeticCharacterSum X ArithmeticFunction.vonMangoldt χ‖ else 0))
  · apply Finset.sum_le_sum
    intro q _
    by_cases hq:R < q.val+1
    · have hq1:1 < q.val+1:=by omega
      simp only [ite_eq_left hq,ite_eq_left hq1]
      rw [←primitiveErrorMass_eq_vonMangoldt_sum X hq1]
      
      calc
        _ ≤ ((q.val+1:ℕ):ℝ)*(primitiveErrorMass (X:ℝ) (q.val+1)/((q.val+1).totient:ℝ)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hq.le)
            (div_nonneg (primitiveErrorMass_nonneg _ _) (Nat.cast_nonneg _))
        _ = _ := by ring
    · simp only [ite_eq_right hq,mul_zero]
      positivity
  · exact finite_vaughan_primitive_mean Q X T k hk

include hQP in
theorem vaughanShortBound_mono       :
    vaughanShortBound Q X T ≤ vaughanShortBound P X T := by
  have hK : Real.sqrt Q*(1+Real.log Q) ≤ Real.sqrt P*(1+Real.log P) :=
    mul_le_mul (Real.sqrt_le_sqrt (by exact_mod_cast hQP))
      (add_le_add le_rfl (log_nat_monotone hQP))
      (by have h:=log_nat_nonneg Q; positivity) (Real.sqrt_nonneg _)
  unfold vaughanShortBound
  exact add_le_add (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK
      (mul_nonneg (by norm_num) (log_nat_nonneg _))) (Nat.cast_nonneg _)))
    (mul_le_mul_of_nonneg_left hK (mul_nonneg (Nat.cast_nonneg _) (log_nat_nonneg _)))

end

noncomputable def conductorHarmonicBound (Q : ℕ)  := 1+Real.log (Q^2:ℕ)

theorem conductorHarmonicBound_pos  Q  : 0 < conductorHarmonicBound Q := by
  unfold conductorHarmonicBound
  have h:=log_nat_nonneg (Q^2)
  linarith

theorem conductor_harmonic_le  {q Q}  (hqQ : q ≤ Q) :
    (harmonic (q^2):ℝ) ≤ conductorHarmonicBound Q := (harmonic_le_one_add_log _).trans
    (add_le_add le_rfl (log_nat_monotone (Nat.pow_le_pow_left hqQ 2)))

noncomputable def highConductorBlockBound (Q X T R k : ℕ)  :=
  2*(Q:ℝ)*vaughanShortBound Q X T+
    ((k:ℝ)*((k:ℝ)+1)*Real.log (X+1:ℕ))*
      (4*(X:ℝ)/(R:ℝ)+16*Real.sqrt (conductorHarmonicBound Q)*(X:ℝ)/Real.sqrt (T+1:ℕ)+
        4*(Q:ℝ)*conductorHarmonicBound Q*Real.sqrt X)

section
variable (Q X T R k D : ℕ)

theorem highConductorBlockBound_nonneg   :
    0 ≤ highConductorBlockBound Q X T R k := by
  have hs:=vaughanShortBound_nonneg Q X T
  have hh:=(conductorHarmonicBound_pos Q).le
  
  unfold highConductorBlockBound
  positivity

theorem vaughanBilinearBound_doubling   (hD : 1 ≤ D) (hQ : 2*D ≤ Q) :
    vaughanBilinearBound (2*D) X T ≤ (D:ℝ)*
      (4*(X:ℝ)/(D:ℝ)+16*Real.sqrt (conductorHarmonicBound Q)*(X:ℝ)/Real.sqrt (T+1:ℕ)+
        4*(Q:ℝ)*conductorHarmonicBound Q*Real.sqrt X) := by
  let H:=conductorHarmonicBound Q
  have hH : 0 ≤ H := (conductorHarmonicBound_pos Q).le
  have hDr : 0 < (D:ℝ) := by exact_mod_cast (show 0 < D by omega)
  have hQr : 2*(D:ℝ) ≤ Q := by exact_mod_cast hQ
  have hz : ((2*D:ℕ):ℝ)^2*(harmonic ((2*D)^2):ℝ) ≤ ((2*D:ℕ):ℝ)^2*H :=
    mul_le_mul_of_nonneg_left (conductor_harmonic_le hQ) (sq_nonneg _)
  have hs : Real.sqrt (((2*D:ℕ):ℝ)^2*(harmonic ((2*D)^2):ℝ)) ≤
      ((2*D:ℕ):ℝ)*Real.sqrt H := by
    apply (Real.sqrt_le_sqrt hz).trans_eq
    rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (Nat.cast_nonneg _)]
  have htail : (((2*D:ℕ):ℝ)^2*H)*(2*Real.sqrt X) ≤
      (D:ℝ)*(4*(Q:ℝ)*H*Real.sqrt X) := by
    calc
      _ = (2*(D:ℝ))*(4*(D:ℝ)*H*Real.sqrt X) := by push_cast; ring
      _ ≤ (Q:ℝ)*(4*(D:ℝ)*H*Real.sqrt X) :=
        mul_le_mul_of_nonneg_right hQr (by positivity)
      _ = _ := by ring
  unfold vaughanBilinearBound
  calc
    _ ≤ 4*(X:ℝ)+(((2*D:ℕ):ℝ)*Real.sqrt H)*(8*(X:ℝ)/Real.sqrt (T+1:ℕ))+
        ((((2*D:ℕ):ℝ)^2*H)*(2*Real.sqrt X)) :=
      add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hs (by positivity)))
        (mul_le_mul_of_nonneg_right hz (by positivity))
    _ ≤ 4*(X:ℝ)+(((2*D:ℕ):ℝ)*Real.sqrt H)*(8*(X:ℝ)/Real.sqrt (T+1:ℕ))+
        (D:ℝ)*(4*(Q:ℝ)*H*Real.sqrt X) := add_le_add le_rfl htail
    _ = _ := by
      grind

end

end LargePrimeGaps

end OAI
