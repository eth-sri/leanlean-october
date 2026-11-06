module

public import OAI.NumberTheory.DirichletL.MeanSquare.InputEnergy

@[expose] public section

namespace OAI

noncomputable section


open MulChar AddChar Filter Asymptotics MeasureTheory

open MeasureTheory Real

open Finset Complex

open Filter Real Asymptotics ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Filter Asymptotics

open MeasureTheory Set ActualEisensteinCubic UniqueFactorizationMonoid

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm actualFirstKernel originalLabelColumn cubeActiveSupport dilationLabel columnLog)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

end

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)

end SecondPassArithmetic

namespace CompletedGauss

section
open ActualEisensteinCubic IdealMobiusDivisorSum UniqueFactorizationMonoid

theorem completed_branch_count_small_power (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(I : Ideal O),I≠0 → ∀{ι : Type*} [Fintype ι]
      (P : ι→Ideal O) [∀i,(P i).IsMaximal],Function.Injective P →
      (∀i,P i∣I) → (6:ℝ)^(2*Fintype.card ι)≤C*(Ideal.absNorm I:ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := SquarefreeDivisorBound.prime_support_subsets_bound (ε/6) (by positivity)
  refine ⟨C^6,by positivity,?_⟩
  intro I hI ι _ P _ hinj hd
  let f : ι→primeSupport I := fun i => ⟨P i,by

    exact Multiset.mem_toFinset.mpr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mpr
      ⟨Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance,hd i⟩)⟩
  have hfi : Function.Injective f := by
    intro i j hij
    exact hinj (congrArg Subtype.val hij)
  have hcard : Fintype.card ι≤(primeSupport I).card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hfi
  have htwo : (2:ℝ)^Fintype.card ι≤C*(Ideal.absNorm I:ℝ)^(ε/6) :=
    (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hcard).trans (hbound I hI)
  have hn : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  calc
    _ = (36:ℝ)^Fintype.card ι := by rw [pow_mul]; norm_num
    _ ≤ (64:ℝ)^Fintype.card ι := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = ((2:ℝ)^Fintype.card ι)^6 := by rw [←pow_mul, Nat.mul_comm, pow_mul]; norm_num
    _ ≤ (C*(Ideal.absNorm I:ℝ)^(ε/6))^6 := pow_le_pow_left₀ (by positivity) htwo 6
    _ = C^6*(Ideal.absNorm I:ℝ)^ε := by
      rw [mul_pow,←Real.rpow_mul_natCast hn.le]
      congr 2
      ring

end

open ActualEisensteinCubic CanonicalQuadraticSieve IdealMobiusDivisorSum

theorem sum_completedRowFibers (S : Finset (Ideal O)) (Q : Ideal O) (f : Ideal O→ℝ) :
    (∑A∈S.image rowPowerfulPart,∑T∈S.image (fun I => rowMaskPart I Q),
      ∑I∈completedRowFiber S Q A T,f I)=∑I∈S,f I := by
  let mapPair : Ideal O→Ideal O×Ideal O := fun I => (rowPowerfulPart I,rowMaskPart I Q)
  have hm : ∀I∈S,mapPair I∈(S.image rowPowerfulPart)×ˢ(S.image (fun J => rowMaskPart J Q)) := by
    intro I hI
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hI,Finset.mem_image_of_mem _ hI⟩
  have hh := Finset.sum_fiberwise_of_maps_to hm f
  rw [Finset.sum_product] at hh
  simpa only [mapPair,Prod.mk.injEq,completedRowFiber] using hh

theorem rowMaskPart_image_card (S : Finset (Ideal O)) (Q : Ideal O) (hQ : Q≠0) :
    (S.image (fun I => rowMaskPart I Q)).card≤(idealDivisors Q).card := by
  apply Finset.card_le_card
  intro T hT
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hT
  exact (mem_idealDivisors hQ).mpr (rowMaskPart_dvd I Q)

end CompletedGauss

namespace CompletedDyadic

def kernelTerm (t s A : ℝ) (n : ℕ) : ℝ := ((2:ℝ)^n)^s/(1+t*(2:ℝ)^n)^A

theorem pow_rpow_comm (s : ℝ) (n : ℕ) : ((2:ℝ)^n)^s=((2:ℝ)^s)^n := by
  rw [←Real.rpow_natCast_mul (by norm_num),←Real.rpow_mul_natCast (by norm_num)]
  congr 1
  ring

theorem kernelTerm_nonneg (t s A : ℝ) (ht : 0<t) (n : ℕ) : 0≤kernelTerm t s A n := by
  unfold kernelTerm
  positivity

theorem kernelTerm_le_head (t s A : ℝ) (ht : 0<t) (hA : 0≤A) (n : ℕ) :
    kernelTerm t s A n≤((2:ℝ)^s)^n := by
  rw [kernelTerm,←pow_rpow_comm]
  exact div_le_self (Real.rpow_nonneg (by positivity) _)
    (Real.one_le_rpow (by nlinarith [pow_pos (by norm_num : (0:ℝ)<2) n]) hA)

theorem kernelTerm_le_tail (t s A : ℝ) (ht : 0<t) (hA : 0≤A) (n : ℕ) :
    kernelTerm t s A n≤t^(-A)*((2:ℝ)^(s-A))^n := by
  have hn : 0<(2:ℝ)^n := by positivity
  have htA : 0<t^A := Real.rpow_pos_of_pos ht _
  calc
    _ ≤ ((2:ℝ)^n)^s/(t*(2:ℝ)^n)^A := by
      unfold kernelTerm
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (Real.rpow_le_rpow (by positivity) (by linarith) hA)
    _ = t^(-A)*(((2:ℝ)^n)^s/((2:ℝ)^n)^A) := by
      rw [Real.mul_rpow ht.le hn.le,Real.rpow_neg ht.le]
      ring
    _ = _ := by rw [←Real.rpow_sub hn,pow_rpow_comm]

theorem ratio_lt_one (s A : ℝ) (hsA : s<A) : (2:ℝ)^(s-A)<1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hsA)

theorem kernel_summable (t s A : ℝ) (ht : 0<t) (hA : 0≤A) (hsA : s<A) :
    Summable (kernelTerm t s A) := by
  have hq := summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (s-A)) (ratio_lt_one s A hsA)
  exact (hq.mul_left (t^(-A))).of_nonneg_of_le (kernelTerm_nonneg t s A ht) (kernelTerm_le_tail t s A ht hA)

theorem kernel_sum_cutoff (t s A : ℝ) (ht : 0<t) (hs : 0<s) (hsA : s<A) (N : ℕ) :
    (∑'n : ℕ,kernelTerm t s A n)≤
      ((2:ℝ)^s)^N/((2:ℝ)^s-1)+t^(-A)*((2:ℝ)^(s-A))^N/(1-(2:ℝ)^(s-A)) := by
  have hA : 0≤A := by linarith
  have hp : 1<(2:ℝ)^s := Real.one_lt_rpow (by norm_num) hs
  have hq : (2:ℝ)^(s-A)<1 := ratio_lt_one s A hsA
  have hq0 : 0≤(2:ℝ)^(s-A) := by positivity
  have hsum := kernel_summable t s A ht hA hsA
  have hhead : (∑n∈Finset.range N,kernelTerm t s A n)≤((2:ℝ)^s)^N/((2:ℝ)^s-1) := by
    apply (Finset.sum_le_sum (fun n _ => kernelTerm_le_head t s A ht hA n)).trans
    rw [geom_sum_eq hp.ne']
    exact div_le_div_of_nonneg_right (by linarith) (sub_nonneg.mpr hp.le)
  have htail : (∑'n : ℕ,kernelTerm t s A (n+N))≤
      t^(-A)*((2:ℝ)^(s-A))^N/(1-(2:ℝ)^(s-A)) := by
    have hgeo := (summable_geometric_of_lt_one hq0 hq).mul_left (t^(-A)*((2:ℝ)^(s-A))^N)
    have hb := Summable.tsum_le_tsum (fun n => show kernelTerm t s A (n+N)≤
      (t^(-A)*((2:ℝ)^(s-A))^N)*((2:ℝ)^(s-A))^n by
        simpa only [pow_add,mul_assoc,mul_left_comm,mul_comm] using kernelTerm_le_tail t s A ht hA (n+N))
      ((summable_nat_add_iff N).mpr hsum) hgeo
    rw [tsum_mul_left,tsum_geometric_of_lt_one hq0 hq] at hb
    simpa only [div_eq_mul_inv] using hb
  rw [←hsum.sum_add_tsum_nat_add N]
  exact add_le_add hhead htail

theorem kernel_sum_bound (s A : ℝ) (hs : 0<s) (hsA : s<A) :
    ∃C : ℝ,0<C ∧ ∀t : ℝ,0<t →
      Summable (kernelTerm t s A) ∧ (∑'n : ℕ,kernelTerm t s A n)≤C*t^(-s) := by
  let r : ℝ := (2:ℝ)^s
  let q : ℝ := (2:ℝ)^(s-A)
  have hr : 1<r := Real.one_lt_rpow (by norm_num) hs
  have hq : q<1 := ratio_lt_one s A hsA
  have hq0 : 0≤q := by dsimp [q]; positivity
  let C := r/(r-1)+1/(1-q)
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro t ht
  have hA : 0≤A := by linarith
  have hsum := kernel_summable t s A ht hA hsA
  refine ⟨hsum,?_⟩
  by_cases ht1 : 1≤t
  · have hg := (summable_geometric_of_lt_one hq0 hq).mul_left (t^(-A))
    have hb := hsum.tsum_le_tsum (fun n => kernelTerm_le_tail t s A ht hA n) hg

    rw [tsum_mul_left,tsum_geometric_of_lt_one hq0 hq] at hb
    calc
      _ ≤ t^(-A)/(1-q) := by simpa only [div_eq_mul_inv] using hb
      _ ≤ t^(-s)/(1-q) := div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)) (by linarith)
      _ ≤ C*t^(-s) := by
        have hp : 0≤r/(r-1)*t^(-s) := by positivity
        calc
          _ ≤ r/(r-1)*t^(-s)+t^(-s)/(1-q) := le_add_of_nonneg_left hp
          _ = C*t^(-s) := by dsimp [C]; ring
  · have ht_le : t≤1 := le_of_not_ge ht1
    have hit : 1≤1/t := (one_le_div ht).mpr ht_le
    obtain ⟨N,hN,hN'⟩ := exists_nat_pow_near hit (by norm_num : (1:ℝ)<2)
    have hheadpow : r^(N+1)≤r*t^(-s) := by

      rw [←pow_rpow_comm]
      calc
        _ ≤ ((2:ℝ)/t)^s := by
          apply Real.rpow_le_rpow (by positivity) _ hs.le
          rw [pow_succ]
          calc
            _ ≤ (1/t)*2 := mul_le_mul_of_nonneg_right hN (by norm_num)
            _ = 2/t := by ring
        _ = _ := by rw [Real.div_rpow (by norm_num) ht.le,Real.rpow_neg ht.le]; ring
    have htailpow : t^(-A)*q^(N+1)≤t^(-s) := by

      rw [←pow_rpow_comm]
      calc
        _ ≤ t^(-A)*(1/t)^(s-A) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by positivity) hN'.le (by linarith)) (by positivity)
        _ = t^(-A)*t^(-(s-A)) := by rw [one_div,Real.inv_rpow ht.le,←Real.rpow_neg ht.le]
        _ = t^(-s) := by rw [←Real.rpow_add ht]; congr 1; ring
    have hb := kernel_sum_cutoff t s A ht hs hsA (N+1)

    calc
      _ ≤ r^(N+1)/(r-1)+t^(-A)*q^(N+1)/(1-q) := hb
      _ ≤ (r*t^(-s))/(r-1)+t^(-s)/(1-q) := add_le_add
        (div_le_div_of_nonneg_right hheadpow (by linarith))
        (div_le_div_of_nonneg_right htailpow (by linarith))
      _ = C*t^(-s) := by dsimp [C]; ring

end CompletedDyadic

end

end OAI
