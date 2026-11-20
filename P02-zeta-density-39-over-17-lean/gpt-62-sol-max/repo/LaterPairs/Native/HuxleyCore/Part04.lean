module
public import LaterPairs.Native.HuxleyGridFibers
public import LaterPairs.Native.HuxleyCore.Part03

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxErrors 1000
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth Filter Polynomial Set
open scoped Classical ContDiff FourierTransform BigOperators Topology
universe huxleyNarrowV
noncomputable section
namespace TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators FourierTransform Classical ContDiff NNReal
open Filter


private theorem middleOriginal_approximateModelPhase_general_original_one_hundred_forty_fourth
    {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∃ δ η₀ B C : ℝ, 0<δ ∧ 0<η₀ ∧ η₀≤1/8 ∧ 1≤B ∧ 1≤C ∧
      ∀ (X M : ℝ) (F : ℝ → ℝ) (n N H a L : ℕ),
        1≤X → 1≤M → Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
        N=8*n → 2≤N → 2≤H → (H:ℝ)≤η₀*M → C≤X/M →
        B≤N → B^2*M^4≤X*(N:ℝ)^3 → B*X*(H:ℝ)*(N:ℝ)^2≤M^4 →
        B*(N:ℝ)^2≤M → True → B^2*X^3*(H:ℝ)^3*(N:ℝ)^11≤M^14 →
        B^2*X^7*(H:ℝ)^7*(N:ℝ)^27≤M^34 →
        M≤(a:ℝ) → ((a+L:ℕ):ℝ)≤2*M →
        ‖Expdb.exponentialSumAt F X M a (a+L)‖^144 ≤
          C*(1+(Nat.clog 2 H:ℝ))^72*X^(6*ε)*
            (1+(M^144/(H:ℝ)^72+
              ((M^144/(N:ℝ)^36+M^432/((H:ℝ)^72*X^72*(N:ℝ)^216)+
                  X^24*(H:ℝ)^24*(N:ℝ)^144/M^24)+
                (X^21*(H:ℝ)^15*M^54*(N:ℝ)^33+X^15*(H:ℝ)^15*M^78*(N:ℝ)^15+
                  X^19*(H:ℝ)^19*M^68*(N:ℝ)^9+X^7*(H:ℝ)^7*M^104*(N:ℝ)^9+
                  X^4*(H:ℝ)^4*M^128/(N:ℝ)^24)))) := by
  simpa only [CompletionRegime.shiftCurve, Nat.reduceMul, Nat.cast_ofNat, ←pow_mul,
    div_pow] using
    approximateModelPhase_weyl .general 6 144
      (fun X M N H => (M^144/N^36+M^432/(H^72*X^72*N^216)+X^24*H^24*N^144/M^24)+
        (X^21*H^15*M^54*N^33+X^15*H^15*M^78*N^15+X^19*H^19*M^68*N^9+
          X^7*H^7*M^104*N^9+X^4*H^4*M^128/N^24))
      (fun hX hM hN hK hH hR hKH hs => by
        simpa only [CompletionRegime.main, ←pow_mul, Nat.reduceMul] using
          middleOriginal_weighted_general_integer_moment_bound hX hM hN hK hH hR hKH hs)
      hσ hε

private theorem middleOriginal_general_nine_monomials_power_window
    {X M N H ℓ u ν h ξ : ℝ}
    (hX : 1≤X) (hξ : 0≤ξ)
    (hMl : X^ℓ≤M) (hMu : M≤X^u)
    (hNl : X^ν/2≤N) (hNu : N≤X^ν)
    (hHl : X^h/2≤H) (hHu : H≤X^h)
    (hDiag : 144*u-72*h≤ξ)
    (hSqrt : 144*u-36*ν≤ξ)
    (hCubic : 432*u-72*h-72-216*ν≤ξ)
    (hEndpoint : 24+24*h+144*ν-24*ℓ≤ξ)
    (hType1 : 21+15*h+54*u+33*ν≤ξ)
    (hType2 : 15+15*h+78*u+15*ν≤ξ)
    (hType3 : 19+19*h+68*u+9*ν≤ξ)
    (hType4 : 7+7*h+104*u+9*ν≤ξ)
    (hPair : 4+4*h+128*u-24*ν≤ξ) :
    1+(M^144/H^72+((M^144/N^36+M^432/(H^72*X^72*N^216)+X^24*H^24*N^144/M^24)+
      (X^21*H^15*M^54*N^33+X^15*H^15*M^78*N^15+
        X^19*H^19*M^68*N^9+X^7*H^7*M^104*N^9+X^4*H^4*M^128/N^24))) ≤ (10*(2:ℝ)^288)*X^ξ := by
  let es : List WindowMonomial := [⟨0,0,0,0,0,0,0,0⟩, ⟨0,0,144,0,0,72,0,0⟩, ⟨0,0,144,0,0,0,0,36⟩,
    ⟨0,0,432,0,72,72,0,216⟩, ⟨24,24,0,144,0,0,24,0⟩, ⟨21,15,54,33,0,0,0,0⟩,
    ⟨15,15,78,15,0,0,0,0⟩, ⟨19,19,68,9,0,0,0,0⟩, ⟨7,7,104,9,0,0,0,0⟩,
    ⟨4,4,128,0,0,0,0,24⟩]
  have hh := WindowMonomial.sum_le_rpow (k := 288) (ξ := ξ) hX hMl hMu hNl hNu hHl hHu es (by
    intro e he
    simp only [es, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      constructor <;> norm_num [WindowMonomial.exponent] <;> linarith only [hξ, hDiag, hSqrt, hCubic, hEndpoint, hType1, hType2, hType3, hType4, hPair])
  simpa [es, WindowMonomial.value, add_comm, add_left_comm, add_assoc,
    mul_comm, mul_left_comm, mul_assoc] using hh

private theorem middleOriginal_general_beta_of_power_window
    {α : ℝ≥0} {β δw ν h εs ζ : ℝ}
    (hδw : 0<δw) (hν : 0<ν) (hh : 0<h) (hεs : 0<εs) (hζ : 0<ζ)
    (hℓ : 0<(α:ℝ)-δw) (hu : (α:ℝ)+δw<1)
    (hhℓ : h<(α:ℝ)-δw) (hRN : 4*((α:ℝ)+δw)<1+3*ν)
    (hNR : 1+h+2*ν<4*((α:ℝ)-δw)) (hNM : 2*ν<(α:ℝ)-δw)
    (hFour : 3+3*h+11*ν<14*((α:ℝ)-δw))
    (hTen : 7+7*h+27*ν<34*((α:ℝ)-δw))
    (hBase : 6*εs+ζ≤144*β)
    (hDiag : 144*((α:ℝ)+δw)-72*h+6*εs+ζ≤144*β)
    (hSqrt : 144*((α:ℝ)+δw)-36*ν+6*εs+ζ≤144*β)
    (hCubic : 432*((α:ℝ)+δw)-72*h-72-216*ν+6*εs+ζ≤144*β)
    (hEndpoint : 24+24*h+144*ν-24*((α:ℝ)-δw)+6*εs+ζ≤144*β)
    (hType1 : 21+15*h+54*((α:ℝ)+δw)+33*ν+6*εs+ζ≤144*β)
    (hType2 : 15+15*h+78*((α:ℝ)+δw)+15*ν+6*εs+ζ≤144*β)
    (hType3 : 19+19*h+68*((α:ℝ)+δw)+9*ν+6*εs+ζ≤144*β)
    (hType4 : 7+7*h+104*((α:ℝ)+δw)+9*ν+6*εs+ζ≤144*β)
    (hPair : 4+4*h+128*((α:ℝ)+δw)-24*ν+6*εs+ζ≤144*β) :
    Expdb.IsExponentSumBoundNonAsymptotic α β := by
  intro ε hε σ hσ
  obtain ⟨δsrc,η,B,Csrc,hδsrc,hη,hηcap,hB,hCsrc,hSource⟩ :=
    middleOriginal_approximateModelPhase_general_original_one_hundred_forty_fourth hσ hεs
  have hPhys := upperOriginal_eventually_upper_polynomial_power_window
    hB hCsrc hη hℓ hν hh hu hhℓ hRN hNR hNM hFour hTen
  refine exponent_of_eventual_moment_window (h := h) (p := 144) (j := 72)
    (A := 10*2^288) (loss := 6*εs) hδsrc hδw hε.le (by decide)
    (zero_le_one.trans hCsrc) (by positivity) hζ (by linarith only [hhℓ,hu,hδw]) hPhys ?_
  intro T M F a L hT hMl hMu hF hStart hStop hData
  let n := ⌊T^ν/8⌋₊
  let N := 8*n
  let H := ⌊T^h⌋₊
  obtain ⟨hM,hN2,hH2,hNl,hNu,hHl,hHu,hHη,hThreshold,hBN,hRNM,hNRM,
      hNMM,hFourM,hTenM⟩ := hData
  refine ⟨H,_,hH2,hHu,hSource T M F n N H a L hT hM hF rfl hN2 hH2 hHη
    hThreshold hBN hRNM hNRM hNMM trivial hFourM hTenM hStart hStop,?_⟩
  apply middleOriginal_general_nine_monomials_power_window hT ?_ hMl hMu hNl hNu hHl hHu
  all_goals norm_num only [Nat.cast_ofNat] <;> linarith only [hBase,hDiag,hSqrt,hCubic,hEndpoint,hType1,hType2,hType3,hType4,hPair]

private theorem middleOriginal_general_ninth_row_nonAsymptotic
    {α : ℝ≥0} (hα : (423:ℝ)/1295≤(α:ℝ)) (hα₁ : (α:ℝ)≤(227:ℝ)/601) :
    Expdb.IsExponentSumBoundNonAsymptotic α ((89+908*(α:ℝ))/1282) := by
  let t := ((α:ℝ)-(423:ℝ)/1295)/((227:ℝ)/601-(423:ℝ)/1295)
  let ν := (1-t)*((115442:ℝ)/1000000)+t*((176182:ℝ)/1000000)
  let h := (1-t)*((52590:ℝ)/1000000)+t*((82521:ℝ)/1000000)
  apply middleOriginal_general_beta_of_power_window
    (δw:=1/1000000000000) (ν:=ν) (h:=h) (εs:=1/100000000) (ζ:=1/100000000)
  all_goals norm_num [ν,h,t]
  all_goals linarith only [hα,hα₁]

                                                                                                                  
theorem exponentSumGrowthExponent_le_huxley_ninthRow
    {α : ℝ≥0} (hα : (423:ℝ)/1295≤(α:ℝ)) (hα₁ : (α:ℝ)≤(227:ℝ)/601) :
    Expdb.exponentSumGrowthExponent α≤(89+908*(α:ℝ))/1282 := by
  exact Expdb.exponentSumGrowthExponent_le_iff_nonAsymptotic.mpr
    (middleOriginal_general_ninth_row_nonAsymptotic hα hα₁)


private theorem middleOriginal_lower_correlation_integer_moments
    {X M N K R : ℝ} (hX : 0 < X) (hM : 0 < M) (hN : 0 < N) (hK : 0 < K)
    (hscale : (X*K/M)*N*R^2=M^3) :
    (K^11*M^13/(N^3*R^6))^3=X^9*K^42*M^3 ∧
    (K^11*K*M^13/(N^5*R^4))^3=X^6*K^42*M^15/N^9 := by
  have hR2 : R^2=M^4/(X*K*N) := by
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero hX.ne' hK.ne') hN.ne')).mpr
    have hs := hscale
    field_simp at hs
    nlinarith only [hs]
  constructor
  · simp only [mul_pow,div_pow,←pow_mul]
    rw [show R^18=(R^2)^9 by rw [←pow_mul],hR2]
    field_simp
    ring
  · simp only [mul_pow,div_pow,←pow_mul]
    rw [show R^12=(R^2)^6 by rw [←pow_mul],hR2]
    field_simp
    ring

private theorem middleOriginal_lower_integer_moments_all_shifts
    {X M N K H R : ℝ}
    (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hH : 0<H) (hR : 0<R)
    (hKH : K≤H) (hscale : (X*K/M)*N*R^2=M^3) :
    (M/H)^36*(K*M/Real.sqrt N)^36≤M^72/N^18 ∧
    (M/H)^36*(K*M*R^2/N^2)^36≤M^216/(H^36*X^36*N^108) ∧
    (M/H)^36*(K*N*(N/R)^((2:ℝ)/3))^36≤X^12*H^12*N^72/M^12 ∧
    (M/H)^36*(K^11*M^13/(N^3*R^6))^3≤X^9*H^6*M^39 ∧
    (M/H)^36*(K^11*K*M^13/(N^5*R^4))^3≤X^6*H^6*M^51/N^9 ∧
    (M/H)^36*(K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3))^3≤
      X^2*H^2*M^64/N^12 := by
  obtain ⟨he₁,he₂,he₃,_,_,he₆⟩ :=
    upperOriginal_upper_integer_moments_all_shifts hX hM hN hK hH hR hKH hscale
  obtain ⟨h₁,h₂⟩ := middleOriginal_lower_correlation_integer_moments hX hM hN hK hscale
  refine ⟨he₁,he₂,he₃,?_,?_,he₆⟩
  · rw [h₁]
    calc
      _ ≤ (M/H)^36*(X^9*H^42*M^3) := by gcongr
      _ = _ := by field_simp
  · rw [h₂]
    calc
      _ ≤ (M/H)^36*(X^6*H^42*M^15/N^9) := by gcongr
      _ = _ := by field_simp

private theorem middleOriginal_weighted_lower_integer_moment_bound
    {X M N K H R : ℝ}
    (hX : 0<X) (hM : 0<M) (hN : 0<N) (hK : 0<K) (hH : 0<H) (hR : 0<R)
    (hKH : K≤H) (hscale : (X*K/M)*N*R^2=M^3) :
    let E := K*M/Real.sqrt N+K*M*R^2/N^2+K*N*(N/R)^((2:ℝ)/3)
    let Main := K^11*M^13/(N^3*R^6)+K^11*K*M^13/(N^5*R^4)+
      K^12*M^12/(N^4*R^2)*(R/N)^((2:ℝ)/3)
    (M/H)^36*(E^36+Main^3)≤(2:ℝ)^72*
      ((M^72/N^18+M^216/(H^36*X^36*N^108)+X^12*H^12*N^72/M^12)+
        (X^9*H^6*M^39+X^6*H^6*M^51/N^9+X^2*H^2*M^64/N^12)) := by
  intro E Main
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ := middleOriginal_lower_integer_moments_all_shifts hX hM hN hK hH hR hKH hscale
  refine weighted_power_pair (upperOriginal_three_term_power_bound (by positivity) (by positivity) (by positivity) 36)
    (upperOriginal_three_term_power_bound (by positivity) (by positivity) (by positivity) 3) (by positivity) (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by decide)) (by positivity) ?_ ?_
  all_goals (simp only [mul_add]; gcongr)


private theorem middleOriginal_approximateModelPhase_lower_original_seventy_second
    {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∃ δ η₀ B C : ℝ, 0<δ ∧ 0<η₀ ∧ η₀≤1/8 ∧ 1≤B ∧ 1≤C ∧
      ∀ (X M : ℝ) (F : ℝ → ℝ) (n N H a L : ℕ),
        1≤X → 1≤M → Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
        N=8*n → 2≤N → 2≤H → (H:ℝ)≤η₀*M → C≤X/M →
        B≤N → B^2*M^4≤X*(N:ℝ)^3 → B*X*(H:ℝ)*(N:ℝ)^2≤M^4 →
        B*(N:ℝ)^2≤M → B*X*(H:ℝ)≤M^3 → B^2*X^3*(H:ℝ)^3*(N:ℝ)^11≤M^14 →
        B^2*X^7*(H:ℝ)^7*(N:ℝ)^27≤M^34 →
        M≤(a:ℝ) → ((a+L:ℕ):ℝ)≤2*M →
        ‖Expdb.exponentialSumAt F X M a (a+L)‖^72 ≤
          C*(1+(Nat.clog 2 H:ℝ))^36*X^(3*ε)*
            (1+(M^72/(H:ℝ)^36+
              ((M^72/(N:ℝ)^18+M^216/((H:ℝ)^36*X^36*(N:ℝ)^108)+
                  X^12*(H:ℝ)^12*(N:ℝ)^72/M^12)+
                (X^9*(H:ℝ)^6*M^39+X^6*(H:ℝ)^6*M^51/(N:ℝ)^9+X^2*(H:ℝ)^2*M^64/(N:ℝ)^12)))) := by
  simpa only [CompletionRegime.shiftCurve, Nat.reduceMul, Nat.cast_ofNat, ←pow_mul,
    div_pow] using
    approximateModelPhase_weyl .lower 3 72
      (fun X M N H => (M^72/N^18+M^216/(H^36*X^36*N^108)+X^12*H^12*N^72/M^12)+
        (X^9*H^6*M^39+X^6*H^6*M^51/N^9+X^2*H^2*M^64/N^12))
      (fun hX hM hN hK hH hR hKH hs => by
        simpa only [CompletionRegime.main, ←pow_mul, Nat.reduceMul] using
          middleOriginal_weighted_lower_integer_moment_bound hX hM hN hK hH hR hKH hs)
      hσ hε

private theorem middleOriginal_eventually_lower_polynomial_power_window
    {B C η ℓ u ν h : ℝ}
    (hB : 1≤B) (hC : 1≤C) (hη : 0<η)
    (hℓ : 0<ℓ) (hν : 0<ν) (hh : 0<h)
    (hu : u<1) (hhℓ : h<ℓ) (hRN : 4*u<1+3*ν)
    (hNR : 1+h+2*ν<4*ℓ) (hNM : 2*ν<ℓ) (hCurve : 1+h<3*ℓ)
    (hFour : 3+3*h+11*ν<14*ℓ) (hTen : 7+7*h+27*ν<34*ℓ) :
    ∀ᶠ X : ℝ in Filter.atTop, 1≤X ∧
      ∀ M : ℝ, X^ℓ≤M → M≤X^u →
        let n := ⌊X^ν/8⌋₊
        let N := 8*n
        let H := ⌊X^h⌋₊
        1≤M ∧ 2≤N ∧ 2≤H ∧
        X^ν/2≤(N:ℝ) ∧ (N:ℝ)≤X^ν ∧ X^h/2≤(H:ℝ) ∧ (H:ℝ)≤X^h ∧
        (H:ℝ)≤η*M ∧ C≤X/M ∧ B≤N ∧
        B^2*M^4≤X*(N:ℝ)^3 ∧ B*X*(H:ℝ)*(N:ℝ)^2≤M^4 ∧
        B*(N:ℝ)^2≤M ∧ B*X*(H:ℝ)≤M^3 ∧ B^2*X^3*(H:ℝ)^3*(N:ℝ)^11≤M^14 ∧
        B^2*X^7*(H:ℝ)^7*(N:ℝ)^27≤M^34 := by
  have hBase := upperOriginal_eventually_upper_polynomial_power_window
    hB hC hη hℓ hν hh hu hhℓ hRN hNR hNM hFour hTen
  have hCurvedom := eventually_const_mul_rpow_le_rpow (D:=B) hCurve
  filter_upwards [hBase,hCurvedom] with X hBaseX hCurveX
  refine ⟨hBaseX.1,?_⟩
  intro M hMl hMu n N H
  obtain ⟨hM,hN2,hH2,hNl,hNu,hHl,hHu,hHη,hThreshold,hBN,hRNM,hNRM,
    hNMM,hFourM,hTenM⟩ := hBaseX.2 M hMl hMu
  have hXp := zero_lt_one.trans_le hBaseX.1
  refine ⟨hM,hN2,hH2,hNl,hNu,hHl,hHu,hHη,hThreshold,hBN,hRNM,hNRM,
    hNMM,?_,hFourM,hTenM⟩
  calc
    _ ≤ B*X*(X^h) := mul_le_mul_of_nonneg_left hHu
      (mul_nonneg (zero_le_one.trans hB) hXp.le)
    _ = B*X^(1+h) := by rw [Real.rpow_add hXp,Real.rpow_one,mul_assoc]
    _ ≤ X^(3*ℓ) := hCurveX
    _ = (X^ℓ)^3 := by
      simpa only [Nat.cast_ofNat,mul_comm] using Real.rpow_mul_natCast hXp.le ℓ 3
    _ ≤ M^3 := pow_le_pow_left₀ (Real.rpow_nonneg hXp.le _) hMl 3

private theorem middleOriginal_lower_seven_monomials_power_window
    {X M N H ℓ u ν h ξ : ℝ}
    (hX : 1≤X) (hξ : 0≤ξ)
    (hMl : X^ℓ≤M) (hMu : M≤X^u)
    (hNl : X^ν/2≤N) (hNu : N≤X^ν)
    (hHl : X^h/2≤H) (hHu : H≤X^h)
    (hDiag : 72*u-36*h≤ξ) (hSqrt : 72*u-18*ν≤ξ)
    (hCubic : 216*u-36*h-36-108*ν≤ξ)
    (hEndpoint : 12+12*h+72*ν-12*ℓ≤ξ)
    (hType1 : 9+6*h+39*u≤ξ) (hType2 : 6+6*h+51*u-9*ν≤ξ)
    (hPair : 2+2*h+64*u-12*ν≤ξ) :
    1+(M^72/H^36+
      ((M^72/N^18+M^216/(H^36*X^36*N^108)+X^12*H^12*N^72/M^12)+
        (X^9*H^6*M^39+X^6*H^6*M^51/N^9+X^2*H^2*M^64/N^12))) ≤
      (8*(2:ℝ)^144)*X^ξ := by
  let es : List WindowMonomial := [⟨0,0,0,0,0,0,0,0⟩, ⟨0,0,72,0,0,36,0,0⟩, ⟨0,0,72,0,0,0,0,18⟩,
    ⟨0,0,216,0,36,36,0,108⟩, ⟨12,12,0,72,0,0,12,0⟩, ⟨9,6,39,0,0,0,0,0⟩,
    ⟨6,6,51,0,0,0,0,9⟩, ⟨2,2,64,0,0,0,0,12⟩]
  have hh := WindowMonomial.sum_le_rpow (k := 144) (ξ := ξ) hX hMl hMu hNl hNu hHl hHu es (by
    intro e he
    simp only [es, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      constructor <;> norm_num [WindowMonomial.exponent] <;> linarith only [hξ, hDiag, hSqrt, hCubic, hEndpoint, hType1, hType2, hPair])
  simpa [es, WindowMonomial.value, add_comm, add_left_comm, add_assoc,
    mul_comm, mul_left_comm, mul_assoc] using hh

private theorem middleOriginal_lower_beta_of_power_window
    {α : ℝ≥0} {β δw ν h εs ζ : ℝ}
    (hδw : 0<δw) (hν : 0<ν) (hh : 0<h) (hεs : 0<εs) (hζ : 0<ζ)
    (hℓ : 0<(α:ℝ)-δw) (hu : (α:ℝ)+δw<1)
    (hhℓ : h<(α:ℝ)-δw) (hRN : 4*((α:ℝ)+δw)<1+3*ν)
    (hNR : 1+h+2*ν<4*((α:ℝ)-δw)) (hNM : 2*ν<(α:ℝ)-δw)
    (hCurve : 1+h<3*((α:ℝ)-δw))
    (hFour : 3+3*h+11*ν<14*((α:ℝ)-δw))
    (hTen : 7+7*h+27*ν<34*((α:ℝ)-δw))
    (hBase : 3*εs+ζ≤72*β)
    (hDiag : 72*((α:ℝ)+δw)-36*h+3*εs+ζ≤72*β)
    (hSqrt : 72*((α:ℝ)+δw)-18*ν+3*εs+ζ≤72*β)
    (hCubic : 216*((α:ℝ)+δw)-36*h-36-108*ν+3*εs+ζ≤72*β)
    (hEndpoint : 12+12*h+72*ν-12*((α:ℝ)-δw)+3*εs+ζ≤72*β)
    (hType1 : 9+6*h+39*((α:ℝ)+δw)+3*εs+ζ≤72*β)
    (hType2 : 6+6*h+51*((α:ℝ)+δw)-9*ν+3*εs+ζ≤72*β)
    (hPair : 2+2*h+64*((α:ℝ)+δw)-12*ν+3*εs+ζ≤72*β) :
    Expdb.IsExponentSumBoundNonAsymptotic α β := by
  intro ε hε σ hσ
  obtain ⟨δsrc,η,B,Csrc,hδsrc,hη,hηcap,hB,hCsrc,hSource⟩ :=
    middleOriginal_approximateModelPhase_lower_original_seventy_second hσ hεs
  have hPhys := middleOriginal_eventually_lower_polynomial_power_window
    hB hCsrc hη hℓ hν hh hu hhℓ hRN hNR hNM hCurve hFour hTen
  refine exponent_of_eventual_moment_window (h := h) (p := 72) (j := 36)
    (A := 8*2^144) (loss := 3*εs) hδsrc hδw hε.le (by decide)
    (zero_le_one.trans hCsrc) (by positivity) hζ (by linarith only [hhℓ,hu,hδw]) hPhys ?_
  intro T M F a L hT hMl hMu hF hStart hStop hData
  let n := ⌊T^ν/8⌋₊
  let N := 8*n
  let H := ⌊T^h⌋₊
  obtain ⟨hM,hN2,hH2,hNl,hNu,hHl,hHu,hHη,hThreshold,hBN,hRNM,hNRM,
      hNMM,hCurveM,hFourM,hTenM⟩ := hData
  refine ⟨H,_,hH2,hHu,hSource T M F n N H a L hT hM hF rfl hN2 hH2 hHη
    hThreshold hBN hRNM hNRM hNMM hCurveM hFourM hTenM hStart hStop,?_⟩
  apply middleOriginal_lower_seven_monomials_power_window hT ?_ hMl hMu hNl hNu hHl hHu
  all_goals norm_num only [Nat.cast_ofNat] <;> linarith only [hBase,hDiag,hSqrt,hCubic,hEndpoint,hType1,hType2,hPair]

private theorem middleOriginal_lower_tenth_row_nonAsymptotic
    {α : ℝ≥0} (hα : (227:ℝ)/601≤(α:ℝ)) (hα₁ : (α:ℝ)≤(12:ℝ)/31) :
    Expdb.IsExponentSumBoundNonAsymptotic α ((29+173*(α:ℝ))/280) := by
  let t := ((α:ℝ)-(227:ℝ)/601)/((12:ℝ)/31-(227:ℝ)/601)
  let ν := (1-t)*((176056:ℝ)/1000000)+t*((193164:ℝ)/1000000)
  let h := (1-t)*((82482:ℝ)/1000000)+t*((89862:ℝ)/1000000)
  apply middleOriginal_lower_beta_of_power_window
    (δw:=1/1000000000000) (ν:=ν) (h:=h) (εs:=1/100000000) (ζ:=1/100000000)
  all_goals norm_num [ν,h,t]
  all_goals linarith only [hα,hα₁]

                                                                                                                
theorem exponentSumGrowthExponent_le_huxley_tenthRow
    {α : ℝ≥0} (hα : (227:ℝ)/601≤(α:ℝ)) (hα₁ : (α:ℝ)≤(12:ℝ)/31) :
    Expdb.exponentSumGrowthExponent α≤(29+173*(α:ℝ))/280 := by
  exact Expdb.exponentSumGrowthExponent_le_iff_nonAsymptotic.mpr
    (middleOriginal_lower_tenth_row_nonAsymptotic hα hα₁)

private theorem middleOriginal_lower_eleventh_row_nonAsymptotic
    {α : ℝ≥0} (hα : (12:ℝ)/31≤(α:ℝ)) (hα₁ : (α:ℝ)≤(1508:ℝ)/3825) :
    Expdb.IsExponentSumBoundNonAsymptotic α ((4+103*(α:ℝ))/128) := by
  let t := ((α:ℝ)-(12:ℝ)/31)/((1508:ℝ)/3825-(12:ℝ)/31)
  let ν := (1-t)*((193164:ℝ)/1000000)+t*((197119:ℝ)/1000000)
  let h := (1-t)*((89862:ℝ)/1000000)+t*((92616:ℝ)/1000000)
  apply middleOriginal_lower_beta_of_power_window
    (δw:=1/1000000000000) (ν:=ν) (h:=h) (εs:=1/100000000) (ζ:=1/100000000)
  all_goals norm_num [ν,h,t]
  all_goals linarith only [hα,hα₁]

                                                                                                                   
theorem exponentSumGrowthExponent_le_huxley_eleventhRow
    {α : ℝ≥0} (hα : (12:ℝ)/31≤(α:ℝ)) (hα₁ : (α:ℝ)≤(1508:ℝ)/3825) :
    Expdb.exponentSumGrowthExponent α≤(4+103*(α:ℝ))/128 := by
  exact Expdb.exponentSumGrowthExponent_le_iff_nonAsymptotic.mpr
    (middleOriginal_lower_eleventh_row_nonAsymptotic hα hα₁)

                                                                         
                                                                      
                                                                            

open Set Expdb TaoTrudgianYang2025
open scoped BigOperators FourierTransform ContDiff Classical NNReal

private theorem twice_shift_physical {F : ℝ → ℝ} {σ X M r s m : ℝ}
    (hM : M ≠ 0) (hMr : M-r ≠ 0) (hMrs : M-r-s ≠ 0)
    (hσ : σ ≠ 0) (hσ₁ : σ+1 ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    ((σ+1)*(σ*X*r/M)*s/(M-r)) *
        aProcessShiftPhase (aProcessShiftPhase F σ (r/M)) (σ+1)
          (s/(M-r)) ((m-r-s)/(M-r-s)) =
      X*(F (m/M)-F ((m+r)/M)-F ((m+s)/M)+F ((m+r+s)/M)) := by
  have hsecond := aProcessShiftPhase_physical
    (F:=aProcessShiftPhase F σ (r/M)) (σ:=σ+1)
    (T:=σ*X*r/M) (N:=M-r) (r:=s) (m:=m-r) hMr hMrs hσ₁ hs
  have hfirst := aProcessShiftPhase_physical
    (F:=F) (σ:=σ) (T:=X) (N:=M) (r:=r) (m:=m) hM hMr hσ hr
  have hfirstShift := aProcessShiftPhase_physical
    (F:=F) (σ:=σ) (T:=X) (N:=M) (r:=r) (m:=m+s) hM hMr hσ hr
  rw [hsecond,mul_sub,hfirst]
  rw [show m-r+s=m+s-r by ring,hfirstShift]
  rw [show m+s+r=m+r+s by ring]
  ring

private theorem product_fiber_card_le_divisors (S : Finset (ℕ × ℕ))
    {l : ℕ} (hl : 0 < l) :
    (S.filter (fun p => p.1*p.2=l)).card ≤ l.divisors.card := by
  classical
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1)
  · intro p hp
    have he := (Finset.mem_filter.mp hp).2
    exact Nat.mem_divisors.mpr ⟨⟨p.2,he.symm⟩,hl.ne'⟩
  · intro p hp q hq he
    change p.1=q.1 at he
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    have hpp : 0 < p.1 := by
      by_contra h
      have hz : p.1=0 := by omega
      simp [hz] at hp'
      omega
    apply Prod.ext he
    apply Nat.mul_left_cancel hpp
    calc
      p.1*p.2=l := hp'
      _=q.1*q.2 := hq'.symm
      _=p.1*q.2 := by rw [he]

private theorem product_fiber_actual_maximum {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧
    ∀ (S : Finset (ℕ × ℕ)) (W : (ℕ × ℕ) → ℂ) (L : ℝ),
      (∀ p∈S, 0 < p.1 ∧ 0 < p.2) →
      (∀ p∈S, (p.1*p.2:ℕ) ≤ L) →
      ∃ pick : ℕ → ℕ × ℕ,
        (∀ l∈S.image (fun p => p.1*p.2),
          pick l∈S ∧ (pick l).1*(pick l).2=l ∧
          ∀ p∈S, p.1*p.2=l → ‖W p‖ ≤ ‖W (pick l)‖) ∧
        (∑ p∈S, ‖W p‖) ≤
          D*L^ε*(∑ l∈S.image (fun p => p.1*p.2), ‖W (pick l)‖) := by
  classical
  obtain ⟨D,hD,hdiv⟩ := RiemannZeta.GuthMaynard.divisorCountBound_native ε hε
  refine ⟨D,hD,?_⟩
  intro S W L hpos hcap
  let products := S.image (fun p => p.1*p.2)
  have hex (l : ℕ) : ∃ p : ℕ × ℕ, l∈products →
      p∈S ∧ p.1*p.2=l ∧ ∀ q∈S, q.1*q.2=l → ‖W q‖ ≤ ‖W p‖ := by
    by_cases hl : l∈products
    · obtain ⟨q,hq,heq⟩ := Finset.mem_image.mp hl
      have hn : (S.filter (fun p => p.1*p.2=l)).Nonempty :=
        ⟨q,Finset.mem_filter.mpr ⟨hq,heq⟩⟩
      obtain ⟨p,hp,hmax⟩ := Finset.exists_max_image _ (fun p => ‖W p‖) hn
      refine ⟨p,fun _ => ⟨(Finset.mem_filter.mp hp).1,
        (Finset.mem_filter.mp hp).2,?_⟩⟩
      intro q hq he
      exact hmax q (Finset.mem_filter.mpr ⟨hq,he⟩)
    · exact ⟨(1,1),fun h => (hl h).elim⟩
  choose pick hpick using hex
  refine ⟨pick,hpick,?_⟩
  have hfiber (l : ℕ) (hl : l∈products) :
      (∑ p∈S.filter (fun p => p.1*p.2=l), ‖W p‖) ≤
        D*L^ε*‖W (pick l)‖ := by
    obtain ⟨hp,he,hmax⟩ := hpick l hl
    have hpp := hpos (pick l) hp
    have hlpos : 0 < l := he ▸ Nat.mul_pos hpp.1 hpp.2
    have hlcap : (l:ℝ) ≤ L := by simpa only [he] using hcap (pick l) hp
    have hcard : ((S.filter (fun p => p.1*p.2=l)).card:ℝ) ≤ D*L^ε := by
      calc
        _ ≤ (l.divisors.card:ℝ) := by
          exact_mod_cast product_fiber_card_le_divisors S hlpos
        _ ≤ D*(l:ℝ)^ε := hdiv l hlpos
        _ ≤ D*L^ε := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hlcap hε.le) hD.le
    calc
      _ ≤ ∑ _p∈S.filter (fun p => p.1*p.2=l), ‖W (pick l)‖ := by
        apply Finset.sum_le_sum
        intro p hp
        exact hmax p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
      _ = ((S.filter (fun p => p.1*p.2=l)).card:ℝ)*‖W (pick l)‖ := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (norm_nonneg _)
  calc
    _ = ∑ l∈products, ∑ p∈S.filter (fun p => p.1*p.2=l), ‖W p‖ := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (fun p hp => Finset.mem_image_of_mem (fun p => p.1*p.2) hp) _
    _ ≤ ∑ l∈products, D*L^ε*‖W (pick l)‖ := Finset.sum_le_sum hfiber
    _ = _ := by rw [Finset.mul_sum]

private theorem source_weyl_length_cap (F : ℝ → ℝ) (T N : ℝ)
    (a L H : ℕ) {M : ℝ} (hH : 0 < H)
    (hL : (L:ℝ)+1 ≤ M) (hHM : (H:ℝ) ≤ M) :
    (H:ℝ)*‖exponentialSumAt F T N a (a+L)‖^2 ≤
      2*M*(M+2*∑ r∈Finset.Icc 1 (H-1), ‖sourceShiftCorrelation F T N a L r‖) := by
  have h := source_exponentialSum_weyl F T N a L H
  have hHp : (0:ℝ) < H := by exact_mod_cast hH
  have hM : 0 ≤ M := hHp.le.trans hHM
  have hC : 0 ≤ ∑ r∈Finset.Icc 1 (H-1), ‖sourceShiftCorrelation F T N a L r‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hbound :
      (H:ℝ)*((H:ℝ)*‖exponentialSumAt F T N a (a+L)‖^2) ≤
        (H:ℝ)*(2*M*(M+2*∑ r∈Finset.Icc 1 (H-1),
          ‖sourceShiftCorrelation F T N a L r‖)) := by
    calc
      _ = (H:ℝ)^2*‖exponentialSumAt F T N a (a+L)‖^2 := by ring
      _ ≤ ((L+1+H:ℕ):ℝ)*((H:ℝ)*(L+1)+
          2*H*∑ r∈Finset.Icc 1 (H-1), ‖sourceShiftCorrelation F T N a L r‖) := h
      _ ≤ (2*M)*((H:ℝ)*M+
          2*H*∑ r∈Finset.Icc 1 (H-1), ‖sourceShiftCorrelation F T N a L r‖) := by
        apply mul_le_mul
        · push_cast
          linarith
        · gcongr
        · positivity
        · positivity
      _ = _ := by ring
  exact le_of_mul_le_mul_left hbound hHp

private theorem source_twice_weyl_fourth
    (F : ℝ → ℝ) (σ X M : ℝ) (a L H K : ℕ)
    (hσ : 0 < σ) (hH : 0 < H) (hK : 0 < K)
    (hHa : H ≤ a) (hHL : H ≤ L+1) (hKL : K ≤ L+1) (hHM : (H:ℝ) < M) :
    let D := ∑ r∈Finset.Icc 1 (H-1), ∑ s∈Finset.Icc 1 (K-1),
      ‖sourceShiftCorrelation (aProcessShiftPhase F σ ((r:ℝ)/M))
        (σ*X*r/M) (M-r) (a-r) (L-r) s‖
    (H:ℝ)^2*K*‖exponentialSumAt F X M a (a+L)‖^4 ≤
      8*K*((L:ℝ)+1)^4+64*(H:ℝ)^2*((L:ℝ)+1)^4+
        128*H*((L:ℝ)+1)^3*D := by
  classical
  intro D
  let n : ℝ := L+1
  let C : ℕ → ℝ := fun r => ‖sourceShiftCorrelation F X M a L r‖
  let E : ℕ → ℝ := fun r => ∑ s∈Finset.Icc 1 (K-1),
    ‖sourceShiftCorrelation (aProcessShiftPhase F σ ((r:ℝ)/M))
      (σ*X*r/M) (M-r) (a-r) (L-r) s‖
  let A := ∑ r∈Finset.Icc 1 (H-1), C r
  let B := ∑ r∈Finset.Icc 1 (H-1), (C r)^2
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have hHp : (0:ℝ) < H := by exact_mod_cast hH
  have hKp : (0:ℝ) < K := by exact_mod_cast hK
  have hHLr : (H:ℝ) ≤ n := by dsimp only [n]; exact_mod_cast hHL
  have hKLr : (K:ℝ) ≤ n := by dsimp only [n]; exact_mod_cast hKL
  have hMp : 0 < M := hHp.trans hHM
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hcard : ((Finset.Icc 1 (H-1)).card:ℝ) ≤ H := by
    exact_mod_cast (show (Finset.Icc 1 (H-1)).card ≤ H by
      calc
        _ ≤ (Finset.range H).card := Finset.card_le_card (by
          intro r hr
          have hr' := Finset.mem_Icc.mp hr
          exact Finset.mem_range.mpr (by omega))
        _ = H := Finset.card_range H)
  have hfirst : (H:ℝ)*‖exponentialSumAt F X M a (a+L)‖^2 ≤ 2*n*(n+2*A) :=
    source_weyl_length_cap F X M a L H hH le_rfl hHLr
  have hsecond (r : ℕ) (hr : r∈Finset.Icc 1 (H-1)) :
      (K:ℝ)*(C r)^2 ≤ 2*n*(n+2*E r) := by
    have hr' := Finset.mem_Icc.mp hr
    have hrpos : 0 < r := by omega
    have hrL : r ≤ L := by omega
    have hra : r ≤ a := by omega
    have hrM : (r:ℝ) < M :=
      (by exact_mod_cast (show r < H by omega) : (r:ℝ) < H).trans hHM
    have heq := norm_sourceShiftCorrelation_compressed_sum
      (F:=F) (σ:=σ) (T:=X) (N:=M)
      hMp.ne' (by linarith : M-(r:ℝ) ≠ 0) hσ.ne' hrpos hra hrL
    dsimp only [C]
    rw [heq]
    exact source_weyl_length_cap _ _ _ _ _ K hK
      (by dsimp [n]; exact_mod_cast (show L-r+1 ≤ L+1 by omega)) hKLr
  have hsum : (K:ℝ)*B ≤ 2*n*((H:ℝ)*n+2*D) := by
    calc
      _ = ∑ r∈Finset.Icc 1 (H-1), (K:ℝ)*(C r)^2 := by rw [Finset.mul_sum]
      _ ≤ ∑ r∈Finset.Icc 1 (H-1), 2*n*(n+2*E r) := Finset.sum_le_sum hsecond
      _ = 2*n*(((Finset.Icc 1 (H-1)).card:ℝ)*n+2*D) := by
        rw [← Finset.mul_sum,Finset.sum_add_distrib]
        simp only [Finset.sum_const,nsmul_eq_mul]
        rw [← Finset.mul_sum]
      _ ≤ _ := by gcongr
  have hcs : A^2 ≤ (H:ℝ)*B := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 (H-1)) C (fun _ => (1:ℝ))
    simp only [mul_one,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hh
    calc
      _ ≤ B*((Finset.Icc 1 (H-1)).card:ℝ) := hh
      _ ≤ B*H := mul_le_mul_of_nonneg_left hcard hB
      _ = _ := mul_comm _ _
  have hKA : (K:ℝ)*A^2 ≤ (H:ℝ)*(2*n*((H:ℝ)*n+2*D)) := by
    calc
      _ ≤ (K:ℝ)*((H:ℝ)*B) := mul_le_mul_of_nonneg_left hcs hKp.le
      _ = (H:ℝ)*((K:ℝ)*B) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum hHp.le
  have hfourth : (H:ℝ)^2*‖exponentialSumAt F X M a (a+L)‖^4 ≤
      8*n^4+32*n^2*A^2 := by
    calc
      _ = ((H:ℝ)*‖exponentialSumAt F X M a (a+L)‖^2)^2 := by ring
      _ ≤ (2*n*(n+2*A))^2 := pow_le_pow_left₀ (by positivity) hfirst 2
      _ = 4*n^2*(n+2*A)^2 := by ring
      _ ≤ 4*n^2*(2*n^2+8*A^2) := mul_le_mul_of_nonneg_left
        (by nlinarith only [sq_nonneg (n-2*A)]) (by positivity)
      _ = _ := by ring
  calc
    _ = (K:ℝ)*((H:ℝ)^2*‖exponentialSumAt F X M a (a+L)‖^4) := by ring
    _ ≤ (K:ℝ)*(8*n^4+32*n^2*A^2) :=
      mul_le_mul_of_nonneg_left hfourth hKp.le
    _ = 8*K*n^4+32*n^2*((K:ℝ)*A^2) := by ring
    _ ≤ 8*K*n^4+32*n^2*((H:ℝ)*(2*n*((H:ℝ)*n+2*D))) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hKA (by positivity : 0 ≤ 32*n^2)) _
    _ = _ := by dsimp only [n]; ring

private theorem twice_shift_actual_sum {F : ℝ → ℝ} {σ X M : ℝ}
    {a L r s : ℕ} (hσ : 0 < σ) (hr : 0 < r) (hs : 0 < s)
    (hra : r+s ≤ a) (hrL : r ≤ L) (hrsM : (r:ℝ)+s < M) :
    ‖sourceShiftCorrelation (aProcessShiftPhase F σ ((r:ℝ)/M))
      (σ*X*r/M) (M-r) (a-r) (L-r) s‖ =
    ‖∑ j∈Finset.range (L+1-r-s),
      (𝐞 (X*(F (((a:ℝ)+j)/M)-F (((a:ℝ)+j+r)/M)-
        F (((a:ℝ)+j+s)/M)+F (((a:ℝ)+j+r+s)/M))) : ℂ)‖ := by
  have hrp : (0:ℝ) < r := by exact_mod_cast hr
  have hsp : (0:ℝ) < s := by exact_mod_cast hs
  have hM : M ≠ 0 := by linarith
  have hMr : M-(r:ℝ) ≠ 0 := by linarith
  have hMrs : M-(r:ℝ)-s ≠ 0 := by linarith
  by_cases hsL : s ≤ L-r
  · rw [norm_sourceShiftCorrelation_compressed_sum
      (σ:=σ+1) hMr hMrs (by linarith : σ+1 ≠ 0) hs (by omega) hsL,
      exponentialSumAt_eq_range]
    rw [show L-r-s+1=L+1-r-s by omega]
    apply congrArg norm
    apply Finset.sum_congr rfl
    intro j _
    apply congrArg (fun t : ℝ => (𝐞 t : ℂ))
    rw [Nat.cast_sub (show s ≤ a-r by omega),
      Nat.cast_sub (show r ≤ a by omega)]
    rw [show (a:ℝ)-r-s+j=(a:ℝ)+j-r-s by ring]
    exact twice_shift_physical hM hMr hMrs hσ.ne' (by linarith)
      hrp.ne' hsp.ne'
  · rw [sourceShiftCorrelation_empty _ _ _ _ _ _ (by omega)]
    simp [show L+1-r-s=0 by omega]

private theorem double_difference_common_jet
    {F : ℝ → ℝ} {x r s B : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hB : 0 ≤ B)
    (hreg : ∀ y∈Set.Icc x (x+r+s), ContDiffAt ℝ ∞ F y)
    (hthird : ∀ y∈Set.Icc x (x+r+s), |iteratedDeriv 3 F y| ≤ B) :
    |F x-F (x+r)-F (x+s)+F (x+r+s)-r*s*iteratedDeriv 2 F x| ≤
      B*r*s*(r+s) := by
  have hx : x∈Set.Icc x (x+r+s) := ⟨le_rfl,by linarith⟩
  have hd (j : ℕ) (y : ℝ) (hy : y∈Set.Icc x (x+r+s)) :
      HasDerivAt (iteratedDeriv j F) (iteratedDeriv (j+1) F y) y := by
    simpa only [iteratedDeriv_succ] using
      ((contDiffAt_iteratedDeriv_infty (hreg y hy) j).differentiableAt (by simp)).hasDerivAt
  have hjet (y : ℝ) (hy : y∈Set.Icc x (x+r+s)) :
      |iteratedDeriv 2 F y-iteratedDeriv 2 F x| ≤ B*(r+s) := by
    have hh := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (hd 2 z hz).differentiableAt)
      (fun z hz => by
        rw [(hd 2 z hz).deriv,Real.norm_eq_abs]
        exact hthird z hz)
      (convex_Icc x (x+r+s)) hx hy
    rw [Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ y-x by linarith [hy.1])] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith [hy.2]) hB)
  let G : ℝ → ℝ := fun z => deriv F z-z*iteratedDeriv 2 F x
  have hdG (z : ℝ) (hz : z∈Set.Icc x (x+r+s)) :
      HasDerivAt G (iteratedDeriv 2 F z-iteratedDeriv 2 F x) z := by
    have hh := (hd 1 z hz).sub ((hasDerivAt_id z).mul_const (iteratedDeriv 2 F x))
    convert hh using 1
    · funext u
      simp [G, iteratedDeriv_one]
    · simp only [Nat.reduceAdd, one_mul]
  have hsegment (y : ℝ) (hy : y∈Set.Icc x (x+r)) :
      |deriv F (y+s)-deriv F y-s*iteratedDeriv 2 F x| ≤ B*(r+s)*s := by
    have hsub (z : ℝ) (hz : z∈Set.Icc y (y+s)) : z∈Set.Icc x (x+r+s) :=
      ⟨hy.1.trans hz.1,by linarith [hy.2,hz.2]⟩
    have hh := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (hdG z (hsub z hz)).differentiableAt)
      (fun z hz => by
        rw [(hdG z (hsub z hz)).deriv,Real.norm_eq_abs]
        exact hjet z (hsub z hz))
      (convex_Icc y (y+s))
      (show y∈Set.Icc y (y+s) from ⟨le_rfl,by linarith⟩)
      (show y+s∈Set.Icc y (y+s) from ⟨by linarith,le_rfl⟩)
    rw [Real.norm_eq_abs,Real.norm_eq_abs,
      show y+s-y=s by ring,abs_of_nonneg hs] at hh
    convert hh using 1
    dsimp only [G]
    congr 1
    ring
  let E : ℝ → ℝ := fun y => F (y+s)-F y-y*s*iteratedDeriv 2 F x
  have hdE (y : ℝ) (hy : y∈Set.Icc x (x+r)) :
      HasDerivAt E (deriv F (y+s)-deriv F y-s*iteratedDeriv 2 F x) y := by
    have hy₀ : y∈Set.Icc x (x+r+s) := ⟨hy.1,by linarith [hy.2]⟩
    have hy₁ : y+s∈Set.Icc x (x+r+s) :=
      ⟨by linarith [hy.1],by linarith [hy.2]⟩
    have hleft := ((hreg (y+s) hy₁).differentiableAt (by simp)).hasDerivAt.comp y
      ((hasDerivAt_id y).add_const s)
    have hright := ((hreg y hy₀).differentiableAt (by simp)).hasDerivAt
    have hlin := (((hasDerivAt_id y).mul_const s).mul_const (iteratedDeriv 2 F x))
    convert (hleft.sub hright).sub hlin using 1
    · rfl
    · simp only [mul_one, one_mul]
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun y hy => (hdE y hy).differentiableAt)
    (fun y hy => by rw [(hdE y hy).deriv,Real.norm_eq_abs]; exact hsegment y hy)
    (convex_Icc x (x+r))
    (show x∈Set.Icc x (x+r) from ⟨le_rfl,by linarith⟩)
    (show x+r∈Set.Icc x (x+r) from ⟨by linarith,le_rfl⟩)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,show x+r-x=r by ring,abs_of_nonneg hr] at hh
  convert hh using 1
  · dsimp only [E]
    congr 1
    ring
  · ring

public  theorem source_product_twice_weyl {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧
    ∀ (F : ℝ → ℝ) (σ X M : ℝ) (a L H K : ℕ),
      0 < σ → 0 < H → 0 < K → H+K ≤ a →
      H ≤ L+1 → K ≤ L+1 → (H:ℝ)+K < M →
      let S := (Finset.Icc 1 (H-1)) ×ˢ (Finset.Icc 1 (K-1))
      let W := fun p : ℕ × ℕ => ∑ j∈Finset.range (L+1-p.1-p.2),
        (𝐞 (X*(F (((a:ℝ)+j)/M)-F (((a:ℝ)+j+p.1)/M)-
          F (((a:ℝ)+j+p.2)/M)+F (((a:ℝ)+j+p.1+p.2)/M))) : ℂ)
      ∃ pick : ℕ → ℕ × ℕ,
        (∀ l∈S.image (fun p => p.1*p.2),
          pick l∈S ∧ (pick l).1*(pick l).2=l ∧
          ∀ p∈S, p.1*p.2=l → ‖W p‖ ≤ ‖W (pick l)‖) ∧
        (H:ℝ)^2*K*‖exponentialSumAt F X M a (a+L)‖^4 ≤
          8*K*((L:ℝ)+1)^4+64*(H:ℝ)^2*((L:ℝ)+1)^4+
            128*H*((L:ℝ)+1)^3*
              (D*((H:ℝ)*K)^ε*
                (∑ l∈S.image (fun p => p.1*p.2), ‖W (pick l)‖)) := by
  classical
  obtain ⟨D,hD,hselect⟩ := product_fiber_actual_maximum hε
  refine ⟨D,hD,?_⟩
  intro F σ X M a L H K hσ hH hK hHa hHL hKL hM S W
  have hbound (p : ℕ × ℕ) (hp : p∈S) : 0 < p.1 ∧ p.1 < H ∧ 0 < p.2 ∧ p.2 < K := by
    obtain ⟨hr,hs⟩ := Finset.mem_product.mp hp
    obtain ⟨hr₁,hr₂⟩ := Finset.mem_Icc.mp hr
    obtain ⟨hs₁,hs₂⟩ := Finset.mem_Icc.mp hs
    omega
  obtain ⟨pick,hpick,hgroup⟩ := hselect S W ((H:ℝ)*K)
    (fun p hp => ⟨(hbound p hp).1,(hbound p hp).2.2.1⟩)
    (by
      intro p hp
      have hh := hbound p hp
      exact_mod_cast Nat.mul_le_mul hh.2.1.le hh.2.2.2.le)
  refine ⟨pick,hpick,?_⟩
  have hHp : (0:ℝ) < H := by exact_mod_cast hH
  have hKp : (0:ℝ) < K := by exact_mod_cast hK
  have hweyl := source_twice_weyl_fourth F σ X M a L H K
    hσ hH hK (by omega) hHL hKL (by linarith)
  dsimp only at hweyl
  have heq : (∑ r∈Finset.Icc 1 (H-1), ∑ s∈Finset.Icc 1 (K-1),
      ‖sourceShiftCorrelation (aProcessShiftPhase F σ ((r:ℝ)/M))
        (σ*X*r/M) (M-r) (a-r) (L-r) s‖) = ∑ p∈S, ‖W p‖ := by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro s hs
    have hh := hbound (r,s) (Finset.mem_product.mpr ⟨hr,hs⟩)
    have hrH : (r:ℝ) < H := by exact_mod_cast hh.2.1
    have hsK : (s:ℝ) < K := by exact_mod_cast hh.2.2.2
    exact twice_shift_actual_sum hσ hh.1 hh.2.2.1
      (by omega) (by omega) (by linarith)
  rw [heq] at hweyl
  exact hweyl.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hgroup (by positivity)))

private theorem double_difference_iterated_jet
    {F : ℝ → ℝ} {x r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hreg : ∀ y∈Set.Icc x (x+r+s), ContDiffAt ℝ ∞ F y) (j : ℕ) :
    iteratedDeriv j (fun u => F u-F (u+r)-F (u+s)+F (u+r+s)) x =
      iteratedDeriv j F x-iteratedDeriv j F (x+r)-
        iteratedDeriv j F (x+s)+iteratedDeriv j F (x+r+s) := by
  have h0 : ContDiffAt ℝ j F x :=
    (hreg x ⟨le_rfl,by linarith⟩).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)
  have h1 : ContDiffAt ℝ j (fun u => F (u+r)) x :=
    ((hreg (x+r) ⟨by linarith,by linarith⟩).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)).comp x
        (contDiffAt_id.add contDiffAt_const)
  have h2 : ContDiffAt ℝ j (fun u => F (u+s)) x :=
    ((hreg (x+s) ⟨by linarith,by linarith⟩).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)).comp x
        (contDiffAt_id.add contDiffAt_const)
  have h3 : ContDiffAt ℝ j (fun u => F (u+r+s)) x :=
    ((hreg (x+r+s) ⟨by linarith,le_rfl⟩).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)).comp x
        ((contDiffAt_id.add contDiffAt_const).add contDiffAt_const)
  rw [iteratedDeriv_fun_add ((h0.sub h1).sub h2) h3,
    iteratedDeriv_fun_sub (h0.sub h1) h2,iteratedDeriv_fun_sub h0 h1]
  simp only [add_assoc,iteratedDeriv_comp_add_const]

private theorem double_difference_all_common_jets
    {F : ℝ → ℝ} {x r s B : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hB : 0 ≤ B)
    (hreg : ∀ y∈Set.Icc x (x+r+s), ContDiffAt ℝ ∞ F y)
    (j : ℕ) (hjet : ∀ y∈Set.Icc x (x+r+s), |iteratedDeriv (j+3) F y| ≤ B) :
    |iteratedDeriv j (fun u => F u-F (u+r)-F (u+s)+F (u+r+s)) x-
      r*s*iteratedDeriv (j+2) F x| ≤ B*r*s*(r+s) := by
  rw [double_difference_iterated_jet hr hs hreg j]
  have hh := double_difference_common_jet (F:=iteratedDeriv j F) hr hs hB
    (fun y hy => contDiffAt_iteratedDeriv_infty (hreg y hy) j)
    (by
      intro y hy
      simpa only [iteratedDeriv_real_comp_order, Nat.add_comm] using hjet y hy)
  simpa only [iteratedDeriv_real_comp_order, Nat.add_comm] using hh

private theorem reference_curvature_root_transfer
    (f f' : ℝ → ℝ) {a b x c ε q : ℝ}
    (hc : 0 < c) (hε : 0 ≤ ε) (hx : x∈Ioo a b)
    (hsmall : ε < c*min (x-a) (b-x))
    (hd : ∀ t∈Icc a b, HasDerivAt f (f' t) t)
    (hlower : ∀ t∈Icc a b, c ≤ f' t)
    (herror : |f x-q| ≤ ε) :
    ∃ v∈Ioo a b, f v=q ∧ |v-x| ≤ ε/c := by
  let d := ε/c
  have hd0 : 0 ≤ d := div_nonneg hε hc.le
  have hcd : c*d=ε := by dsimp only [d]; field_simp
  have hleft : a < x-d := by
    have hh : d < x-a := (div_lt_iff₀ hc).mpr (by
      simpa only [mul_comm] using
        hsmall.trans_le (mul_le_mul_of_nonneg_left (min_le_left _ _) hc.le))
    linarith
  have hright : x+d < b := by
    have hh : d < b-x := (div_lt_iff₀ hc).mpr (by
      simpa only [mul_comm] using
        hsmall.trans_le (mul_le_mul_of_nonneg_left (min_le_right _ _) hc.le))
    linarith
  have hsub : Icc (x-d) (x+d) ⊆ Icc a b :=
    fun _ ht => ⟨hleft.le.trans ht.1,ht.2.trans hright.le⟩
  have hg (u v : ℝ) (hu : u∈Icc a b) (hv : v∈Icc a b) (huv : u ≤ v) :
      c*(v-u) ≤ f v-f u := by
    rcases huv.eq_or_lt with he | he
    · subst v
      simp
    have hsub' : Icc u v ⊆ Icc a b :=
      fun _ ht => ⟨hu.1.trans ht.1,ht.2.trans hv.2⟩
    obtain ⟨t,ht,heq⟩ := exists_hasDerivAt_eq_slope f f' he
      (fun z hz => (hd z (hsub' hz)).continuousAt.continuousWithinAt)
      (fun z hz => hd z (hsub' ⟨hz.1.le,hz.2.le⟩))
    have hh := hlower t (hsub' ⟨ht.1.le,ht.2.le⟩)
    rw [heq] at hh
    exact (le_div_iff₀ (sub_pos.mpr he)).mp hh
  have hxl : x-d∈Icc a b := ⟨hleft.le,by linarith [hx.2]⟩
  have hxu : x+d∈Icc a b := ⟨by linarith [hx.1],hright.le⟩
  have hlow := hg (x-d) x hxl ⟨hx.1.le,hx.2.le⟩ (by linarith)
  have hupp := hg x (x+d) ⟨hx.1.le,hx.2.le⟩ hxu (by linarith)
  have hcont : ContinuousOn f (Icc (x-d) (x+d)) :=
    fun z hz => (hd z (hsub hz)).continuousAt.continuousWithinAt
  obtain ⟨v,hv,hvroot⟩ := intermediate_value_Icc (by linarith : x-d ≤ x+d)
    hcont (show q∈Icc (f (x-d)) (f (x+d)) from
      ⟨by nlinarith only [hlow,hcd,(abs_le.mp herror).2],
       by nlinarith only [hupp,hcd,(abs_le.mp herror).1]⟩)
  refine ⟨v,⟨hleft.trans_le hv.1,hv.2.trans_lt hright⟩,hvroot,?_⟩
  exact abs_le.mpr ⟨by linarith [hv.1],by linarith [hv.2]⟩

private theorem reference_curvature_profile_transfer
    (f f' g g' : ℝ → ℝ) {a b x c ε q B E u : ℝ}
    (hc : 0 < c) (hε : 0 ≤ ε) (hB : 0 ≤ B) (hx : x∈Ioo a b)
    (hsmall : ε < c*min (x-a) (b-x))
    (hd : ∀ t∈Icc a b, HasDerivAt f (f' t) t)
    (hlower : ∀ t∈Icc a b, c ≤ f' t)
    (herror : |f x-q| ≤ ε)
    (hgd : ∀ t∈Icc a b, HasDerivAt g (g' t) t)
    (hgupper : ∀ t∈Icc a b, |g' t| ≤ B)
    (hgerror : |g x-u| ≤ E) :
    ∃ v∈Ioo a b, f v=q ∧ |v-x| ≤ ε/c ∧ |g v-u| ≤ E+B*(ε/c) := by
  obtain ⟨v,hv,hroot,hdist⟩ :=
    reference_curvature_root_transfer f f' hc hε hx hsmall hd hlower herror
  refine ⟨v,hv,hroot,hdist,?_⟩
  have hprofile := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hgd z hz).differentiableAt)
    (fun z hz => by rw [(hgd z hz).deriv,Real.norm_eq_abs]; exact hgupper z hz)
    (convex_Icc a b) (show x∈Icc a b from ⟨hx.1.le,hx.2.le⟩)
    (show v∈Icc a b from ⟨hv.1.le,hv.2.le⟩)
  simp only [Real.norm_eq_abs] at hprofile
  calc
    _ = |(g v-g x)+(g x-u)| := by congr 1; ring
    _ ≤ |g v-g x|+|g x-u| := abs_add_le _ _
    _ ≤ B*(ε/c)+E := add_le_add
      (hprofile.trans (mul_le_mul_of_nonneg_left hdist hB)) hgerror
    _ = _ := add_comm _ _

private theorem linear_reference_curvature_data
    (f : ℝ → ℝ) {x y c U : ℝ}
    (hx : 0 < x) (hy : y∈Icc (1/2:ℝ) 3)
    (hc : 0 < c)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ f u)
    (hlower : c ≤ deriv f x) (hupper : |deriv f x| ≤ U)
    (hdet : c ≤ |(deriv f x)^2-f x*iteratedDeriv 2 f x|) :
    let H := fun p : ℝ × ℝ => p.1*f p.2
    ContDiffAt ℝ 2 H (y,x) ∧
    fderiv ℝ H (y,x) (0,1)=y*deriv f x ∧
    fderiv ℝ H (y,x) (1,0)=f x ∧
    c/2 ≤ |fderiv ℝ H (y,x) (0,1)| ∧
    c/(3*U^2) ≤
      |deriv (fun u => fderiv ℝ H (y,u) (1,0)/
        fderiv ℝ H (y,u) (0,1)) x| := by
  intro H
  have hypos : 0 < y := by linarith only [hy.1]
  have hdpos : 0 < deriv f x := hc.trans_le hlower
  have hcol (u : ℝ) (hu : 0 < u) :
      fderiv ℝ H (y,u) (0,1)=y*deriv f u ∧
      fderiv ℝ H (y,u) (1,0)=f u := by
    have hd := ((hf u hu).differentiableAt (by simp)).hasDerivAt
    have hh := (hasFDerivAt_fst (𝕜:=ℝ) (p:=(y,u))).mul
      (hd.comp_hasFDerivAt (f:=fun p : ℝ × ℝ => p.2) (y,u) hasFDerivAt_snd)
    have he := hh.fderiv
    change fderiv ℝ H (y,u)=_ at he
    constructor
    · rw [he]
      change y*(deriv f u*1)+f u*0=_
      ring
    · rw [he]
      change y*(deriv f u*0)+f u*1=_
      ring
  refine ⟨(contDiffAt_fst.mul ((hf x hx).comp (y,x) contDiffAt_snd)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2),
    (hcol x hx).1,(hcol x hx).2,?_,?_⟩
  · rw [(hcol x hx).1,abs_of_pos (mul_pos hypos hdpos)]
    nlinarith only [mul_le_mul hy.1 hlower hc.le hypos.le]
  · have hd := ((hf x hx).differentiableAt (by simp)).hasDerivAt
    have hdd : HasDerivAt (deriv f) (iteratedDeriv 2 f x) x := by
      simpa only [iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using
        ((contDiffAt_iteratedDeriv_infty (hf x hx) 1).differentiableAt (by simp)).hasDerivAt
    have hratio := hd.div (hdd.const_mul y) (mul_pos hypos hdpos).ne'
    have hevent :
        (fun u => fderiv ℝ H (y,u) (1,0)/fderiv ℝ H (y,u) (0,1)) =ᶠ[nhds x]
          (fun u => f u/(y*deriv f u)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with u hu
      rw [(hcol u hu).1,(hcol u hu).2]
    have hratioder : deriv (fun u => f u/(y*deriv f u)) x =
        (deriv f x*(y*deriv f x)-f x*(y*iteratedDeriv 2 f x))/(y*deriv f x)^2 :=
      hratio.deriv
    rw [hevent.deriv_eq,hratioder]
    have heq :
        (deriv f x*(y*deriv f x)-f x*(y*iteratedDeriv 2 f x))/(y*deriv f x)^2 =
          ((deriv f x)^2-f x*iteratedDeriv 2 f x)/(y*(deriv f x)^2) := by
      field_simp
    rw [heq,abs_div,abs_of_pos (mul_pos hypos (sq_pos_of_pos hdpos))]
    have hsq : (deriv f x)^2 ≤ U^2 := by
      nlinarith only [(abs_le.mp hupper).2,hdpos]
    have hden : y*(deriv f x)^2 ≤ 3*U^2 :=
      mul_le_mul hy.2 hsq (sq_nonneg _) (by norm_num)
    exact (div_le_div_of_nonneg_left hc.le
      (mul_pos hypos (sq_pos_of_pos hdpos)) hden).trans
        (div_le_div_of_nonneg_right hdet (by positivity))

private theorem linear_reference_local_parameter_count
    {c U : ℝ} (hc : 0 < c) (hU : 0 < U) :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1/4 ∧ 0 < C ∧
      ∀ (f : ℝ → ℝ) (x₀ y₀ ε E J q g : ℝ) (S : Finset ℝ) (x : ℝ → ℝ),
        x₀∈Icc (1:ℝ) 2 → y₀∈Icc (1:ℝ) 2 →
        (∀ u, 0 < u → ContDiffAt ℝ ∞ f u) →
        (∀ u∈Icc (1/2:ℝ) 3, c ≤ deriv f u) →
        (∀ u∈Icc (1/2:ℝ) 3,
          |f u| ≤ U ∧ |deriv f u| ≤ U ∧ |iteratedDeriv 2 f u| ≤ U) →
        (∀ u∈Icc (1/2:ℝ) 3,
          c ≤ |(deriv f u)^2-f u*iteratedDeriv 2 f u|) →
        0 ≤ ε → ε ≤ c/64 → 0 ≤ E → 0 < J →
        |y₀*f x₀-q| ≤ ε →
        (∀ y∈S, y∈Icc (1:ℝ) 2 ∧ |y-y₀| < a ∧ x y∈Icc (1:ℝ) 2) →
        (∀ y∈S, ∀ z∈S, y ≠ z → 1 ≤ J*|y-z|) →
        (∀ y∈S, |y*f (x y)-q| ≤ ε) →
        (∀ y∈S, |y*deriv f (x y)-g| ≤ E) →
        (S.card:ℝ) ≤ 1+C*(E+6*U*ε/c)*J := by
  classical
  let a := min (1/4:ℝ) (c/(64*U))
  let L := c/2
  let K := c/(3*U^2)
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have hacap : a ≤ 1/4 := min_le_left _ _
  have hau : a*U ≤ c/64 := by
    have hh := (le_div_iff₀ (show 0 < 64*U by positivity)).mp
      (min_le_right (1/4:ℝ) (c/(64*U)))
    nlinarith only [hh]
  have hL : 0 < L := by dsimp only [L]; positivity
  have hK : 0 < K := by dsimp only [K, cubicDualPhase]; positivity
  refine ⟨a,2/(L*K),ha,hacap,by positivity,?_⟩
  intro f x₀ y₀ ε E J q g S x hx₀ hy₀ hf hlower hupper hdet hε hεcap hE hJ
    hanchor hpoints hsep hlevels hprofiles
  let H := fun p : ℝ × ℝ => p.1*f p.2
  let ρ := fun y => Function.invFunOn (fun u => H (y,u)) (Ioo (3/4:ℝ) (9/4)) q
  have hsub : Icc (3/4:ℝ) (9/4) ⊆ Icc (1/2:ℝ) 3 := by
    intro u hu
    constructor <;> linarith only [hu.1,hu.2]
  have hpos (u : ℝ) (hu : u∈Icc (3/4:ℝ) (9/4)) : 0 < u := by
    linarith only [hu.1]
  have hinside (u : ℝ) (hu : u∈Icc (1:ℝ) 2) :
      u∈Ioo (3/4:ℝ) (9/4) ∧ (1/4:ℝ) ≤ min (u-3/4) (9/4-u) := by
    refine ⟨⟨by linarith only [hu.1],by linarith only [hu.2]⟩,?_⟩
    exact le_min (by linarith only [hu.1]) (by linarith only [hu.2])
  have hywide (y : ℝ) (hy : y∈Ioo (y₀-a) (y₀+a)) :
      y∈Icc (1/2:ℝ) 3 := by
    constructor <;> linarith only [hy.1,hy.2,hy₀.1,hy₀.2,hacap]
  have hder (y u : ℝ) (hu : u∈Icc (3/4:ℝ) (9/4)) :
      HasDerivAt (fun z => y*f z) (y*deriv f u) u :=
    (((hf u (hpos u hu)).differentiableAt (by simp)).hasDerivAt).const_mul y
  have hlow (y : ℝ) (hy : y∈Icc (1/2:ℝ) 3)
      (u : ℝ) (hu : u∈Icc (3/4:ℝ) (9/4)) : L ≤ y*deriv f u := by
    dsimp only [L]
    have hh := mul_le_mul hy.1 (hlower u (hsub hu)) hc.le (by linarith only [hy.1])
    nlinarith only [hh]
  have hdata (y : ℝ) (hy : y∈Ioo (y₀-a) (y₀+a))
      (u : ℝ) (hu : u∈Ioo (3/4:ℝ) (9/4)) :=
    linear_reference_curvature_data f (hpos u ⟨hu.1.le,hu.2.le⟩) (hywide y hy)
      hc hf (hlower u (hsub ⟨hu.1.le,hu.2.le⟩))
      (hupper u (hsub ⟨hu.1.le,hu.2.le⟩)).2.1
      (hdet u (hsub ⟨hu.1.le,hu.2.le⟩))
  have hroots (y : ℝ) (hy : y∈Ioo (y₀-a) (y₀+a)) :
      ρ y∈Ioo (3/4:ℝ) (9/4) ∧ H (y,ρ y)=q := by
    have hclose : |y-y₀| ≤ a :=
      (abs_lt.mpr ⟨by linarith only [hy.1],by linarith only [hy.2]⟩).le
    have herr : |y*f x₀-q| ≤ ε+a*U := by
      calc
        _ = |(y-y₀)*f x₀+(y₀*f x₀-q)| := by congr 1; ring
        _ ≤ |(y-y₀)*f x₀|+|y₀*f x₀-q| := abs_add_le _ _
        _ ≤ a*U+ε := by
          rw [abs_mul]
          exact add_le_add
            (mul_le_mul hclose (hupper x₀ ⟨by linarith only [hx₀.1],
              by linarith only [hx₀.2]⟩).1 (abs_nonneg _) ha.le) hanchor
        _ = _ := add_comm _ _
    have hsmall : ε+a*U < L*min (x₀-3/4) (9/4-x₀) := by
      have hh := mul_le_mul_of_nonneg_left (hinside x₀ hx₀).2 hL.le
      dsimp only [L] at hh ⊢
      nlinarith only [hh,hau,hεcap,hc]
    obtain ⟨v,hv,hvroot,_⟩ := reference_curvature_root_transfer
      (fun u => y*f u) (fun u => y*deriv f u) hL (by positivity)
      (hinside x₀ hx₀).1 hsmall (hder y) (hlow y (hywide y hy)) herr
    have himage : q∈(fun u => H (y,u)) '' Ioo (3/4:ℝ) (9/4) := ⟨v,hv,hvroot⟩
    exact ⟨Function.invFunOn_mem himage,Function.invFunOn_eq himage⟩
  have hS (y : ℝ) (hy : y∈S) : y∈Ioo (y₀-a) (y₀+a) := by
    have hh := abs_lt.mp (hpoints y hy).2.1
    constructor <;> linarith only [hh.1,hh.2]
  have hres (y : ℝ) (hy : y∈S) :
      |fderiv ℝ H (y,ρ y) (0,1)-g| ≤ E+6*U*ε/c := by
    have hyw := hywide y (hS y hy)
    have hx := (hpoints y hy).2.2
    have hsmall : ε < L*min (x y-3/4) (9/4-x y) := by
      have hh := mul_le_mul_of_nonneg_left (hinside (x y) hx).2 hL.le
      dsimp only [L] at hh ⊢
      linarith only [hh,hεcap,hc]
    have hgd (u : ℝ) (hu : u∈Icc (3/4:ℝ) (9/4)) :
        HasDerivAt (fun z => y*deriv f z) (y*iteratedDeriv 2 f u) u := by
      have hh : HasDerivAt (deriv f) (iteratedDeriv 2 f u) u := by
        simpa only [iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using
          ((contDiffAt_iteratedDeriv_infty (hf u (hpos u hu)) 1).differentiableAt
            (by simp)).hasDerivAt
      exact hh.const_mul y
    have hgup (u : ℝ) (hu : u∈Icc (3/4:ℝ) (9/4)) :
        |y*iteratedDeriv 2 f u| ≤ 3*U := by
      rw [abs_mul,abs_of_nonneg (by linarith only [hyw.1] : 0 ≤ y)]
      exact mul_le_mul hyw.2 (hupper u (hsub hu)).2.2 (abs_nonneg _)
        (by norm_num)
    obtain ⟨v,hv,hvroot,_,hvprofile⟩ := reference_curvature_profile_transfer
      (fun u => y*f u) (fun u => y*deriv f u)
      (fun u => y*deriv f u) (fun u => y*iteratedDeriv 2 f u)
      hL hε (by positivity : 0 ≤ 3*U) (hinside (x y) hx).1 hsmall
      (hder y) (hlow y hyw) (hlevels y hy) hgd hgup (hprofiles y hy)
    have hmono : StrictMonoOn (fun u => y*f u) (Icc (3/4:ℝ) (9/4)) := by
      apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
        (fun u hu => (hder y u hu).continuousAt.continuousWithinAt)
        (fun u hu => (hder y u (interior_subset hu)).hasDerivWithinAt)
      exact fun u hu => hL.trans_le (hlow y hyw u (interior_subset hu))
    have hr := hroots y (hS y hy)
    have heq : ρ y=v := hmono.injOn ⟨hr.1.1.le,hr.1.2.le⟩
      ⟨hv.1.le,hv.2.le⟩ (hr.2.trans hvroot.symm)
    rw [(hdata y (hS y hy) (ρ y) hr.1).2.1,heq]
    convert hvprofile using 1
    dsimp only [L]
    ring
  have hcount := HuxleyRationalPhase.curvature_fiber_parameter_count S H ρ hL hK
    (show 0 ≤ E+6*U*ε/c by positivity) hJ hS hsep
    (fun y hy u hu => (hdata y hy u hu).1) hroots
    (fun y hy u hu => (hdata y hy u hu).2.2.2.1)
    (fun y hy u hu => (hdata y hy u hu).2.2.2.2) hres
  convert hcount using 1
  ring

private theorem linear_reference_parameter_count
    {c U : ℝ} (hc : 0 < c) (hU : 0 < U) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (f : ℝ → ℝ) (ε E J q g : ℝ) (S : Finset ℝ) (x : ℝ → ℝ),
        (∀ u, 0 < u → ContDiffAt ℝ ∞ f u) →
        (∀ u∈Icc (1/2:ℝ) 3, c ≤ deriv f u) →
        (∀ u∈Icc (1/2:ℝ) 3,
          |f u| ≤ U ∧ |deriv f u| ≤ U ∧ |iteratedDeriv 2 f u| ≤ U) →
        (∀ u∈Icc (1/2:ℝ) 3,
          c ≤ |(deriv f u)^2-f u*iteratedDeriv 2 f u|) →
        0 ≤ ε → ε ≤ c/64 → 0 ≤ E → 0 < J →
        (∀ y∈S, y∈Icc (1:ℝ) 2 ∧ x y∈Icc (1:ℝ) 2) →
        (∀ y∈S, ∀ z∈S, y ≠ z → 1 ≤ J*|y-z|) →
        (∀ y∈S, |y*f (x y)-q| ≤ ε) →
        (∀ y∈S, |y*deriv f (x y)-g| ≤ E) →
        (S.card:ℝ) ≤ K*(1+C*(E+6*U*ε/c)*J) := by
  classical
  obtain ⟨a,C,ha,_,hC,hlocal⟩ := linear_reference_local_parameter_count hc hU
  refine ⟨2+1/a,C,by positivity,hC,?_⟩
  intro f ε E J q g S x hf hlower hupper hdet hε hεcap hE hJ hpoints hsep hroot hres
  apply unit_interval_card_le_of_local S ha (by positivity) (fun y hy => (hpoints y hy).1)
  intro y₀ hy₀S V hsub hclose
  exact hlocal f (x y₀) y₀ ε E J q g V x (hpoints y₀ hy₀S).2
      (hpoints y₀ hy₀S).1 hf hlower hupper hdet hε hεcap hE hJ (hroot y₀ hy₀S)
      (fun y hy => ⟨(hpoints y (hsub hy)).1,hclose y hy,
        (hpoints y (hsub hy)).2⟩)
      (fun y hy z hz hyz => hsep y (hsub hy) z
        (hsub hz) hyz)
      (fun y hy => hroot y (hsub hy))
      (fun y hy => hres y (hsub hy))

private theorem normalized_double_difference_common_jet
    (F : ℝ → ℝ) {x r s δ y U w : ℝ} (j : ℕ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hδ : 0 < δ) (hy : y∈Icc (1:ℝ) 2)
    (hU : 0 ≤ U) (hprod : r*s=δ*y) (hshift : r+s ≤ w)
    (hreg : ∀ u∈Icc x (x+r+s), ContDiffAt ℝ ∞ F u)
    (hjet : ∀ u∈Icc x (x+r+s), |iteratedDeriv (j+3) F u| ≤ U) :
    |iteratedDeriv j
      (fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/δ) x-
        y*iteratedDeriv (j+2) F x| ≤ 2*U*w := by
  have hbase := double_difference_all_common_jets hr hs hU hreg j hjet
  rw [iteratedDeriv_div_const]
  have heq :
      iteratedDeriv j (fun u => F u-F (u+r)-F (u+s)+F (u+r+s)) x/δ-
        y*iteratedDeriv (j+2) F x =
      (iteratedDeriv j (fun u => F u-F (u+r)-F (u+s)+F (u+r+s)) x-
        r*s*iteratedDeriv (j+2) F x)/δ := by
    rw [hprod]
    field_simp
  rw [heq,abs_div,abs_of_pos hδ]
  calc
    _ ≤ U*r*s*(r+s)/δ := div_le_div_of_nonneg_right hbase hδ.le
    _ = U*y*(r+s) := by
      rw [show U*r*s=U*(r*s) by ring,hprod]
      field_simp
    _ ≤ (U*2)*w := mul_le_mul
      (mul_le_mul_of_nonneg_left hy.2 hU) hshift (by positivity) (by positivity)
    _ = _ := by ring

private theorem double_difference_parameter_count
    {c U : ℝ} (hc : 0 < c) (hU : 0 < U) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (δ w E J q g : ℝ) (S : Finset ℝ) (x r s : ℝ → ℝ),
        (∀ u, 0 < u → ContDiffAt ℝ ∞ F u) →
        (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
        (∀ u∈Icc (1/2:ℝ) 3,
          |iteratedDeriv 4 F u| ≤ U ∧ |iteratedDeriv 5 F u| ≤ U ∧
            |iteratedDeriv 6 F u| ≤ U) →
        (∀ u∈Icc (1/2:ℝ) 3,
          c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
        0 < δ → 0 ≤ w → w ≤ 1/4 → 2*U*w ≤ c/64 → 0 ≤ E → 0 < J →
        (∀ y∈S, y∈Icc (1:ℝ) 2 ∧ x y∈Icc (1:ℝ) 2) →
        (∀ y∈S, ∀ z∈S, y ≠ z → 1 ≤ J*|y-z|) →
        (∀ y∈S, 0 ≤ r y ∧ 0 ≤ s y ∧ r y*s y=δ*y ∧ r y+s y ≤ w) →
        let Q := fun y u =>
          (F u-F (u+r y)-F (u+s y)+F (u+r y+s y))/δ
        (∀ y∈S, iteratedDeriv 2 (Q y) (x y)=q) →
        (∀ y∈S, |iteratedDeriv 3 (Q y) (x y)-g| ≤ E) →
        (S.card:ℝ) ≤ K*(1+C*(E+2*U*w+12*U^2*w/c)*J) := by
  obtain ⟨K,C,hK,hC,hcount⟩ := linear_reference_parameter_count hc hU
  refine ⟨K,C,hK,hC,?_⟩
  intro F δ w E J q g S x r s hf hlower hupper hdet hδ hw hwcap hsmall hE hJ
    hpoints hsep hshifts Q hlevels hprofiles
  have hfd : deriv (iteratedDeriv 4 F)=iteratedDeriv 5 F :=
    (iteratedDeriv_succ (n:=4) (f:=F)).symm
  have hfd₂ : iteratedDeriv 2 (iteratedDeriv 4 F)=iteratedDeriv 6 F := by
    rw [iteratedDeriv_real_comp_order]
  have hsub (y : ℝ) (hy : y∈S) :
      Icc (x y) (x y+r y+s y) ⊆ Icc (1/2:ℝ) 3 := by
    intro u hu
    have hp := (hpoints y hy).2
    have hs' := (hshifts y hy).2.2.2
    constructor <;> linarith only [hu.1,hu.2,hp.1,hp.2,hs',hwcap]
  have hjet (y : ℝ) (hy : y∈S) (j : ℕ) (hj : j=2 ∨ j=3) :
      |iteratedDeriv j (Q y) (x y)-y*iteratedDeriv (j+2) F (x y)| ≤ 2*U*w := by
    apply normalized_double_difference_common_jet F j (hshifts y hy).1
      (hshifts y hy).2.1 hδ (hpoints y hy).1 hU.le (hshifts y hy).2.2.1
      (hshifts y hy).2.2.2
    · intro u hu
      exact hf u (by linarith only [(hsub y hy hu).1])
    · intro u hu
      rcases hj with rfl | rfl
      · exact (hupper u (hsub y hy hu)).2.1
      · exact (hupper u (hsub y hy hu)).2.2
  have hlevels' (y : ℝ) (hy : y∈S) :
      |y*iteratedDeriv 4 F (x y)-q| ≤ 2*U*w := by
    have hh := hjet y hy 2 (Or.inl rfl)
    rw [hlevels y hy,abs_sub_comm] at hh
    exact hh
  have hprofiles' (y : ℝ) (hy : y∈S) :
      |y*deriv (iteratedDeriv 4 F) (x y)-g| ≤ E+2*U*w := by
    rw [hfd]
    calc
      _ = |(y*iteratedDeriv 5 F (x y)-iteratedDeriv 3 (Q y) (x y))+
        (iteratedDeriv 3 (Q y) (x y)-g)| := by congr 1; ring
      _ ≤ |y*iteratedDeriv 5 F (x y)-iteratedDeriv 3 (Q y) (x y)|+
        |iteratedDeriv 3 (Q y) (x y)-g| := abs_add_le _ _
      _ ≤ 2*U*w+E := add_le_add
        (by simpa only [abs_sub_comm] using hjet y hy 3 (Or.inr rfl)) (hprofiles y hy)
      _ = _ := add_comm _ _
  have hh := hcount (iteratedDeriv 4 F) (2*U*w) (E+2*U*w) J q g S x
    (fun u hu => contDiffAt_iteratedDeriv_infty (hf u hu) 4)
    (by simpa only [hfd] using hlower)
    (by simpa only [hfd,hfd₂] using hupper)
    (by simpa only [hfd,hfd₂] using hdet)
    (by positivity) hsmall (by positivity) hJ hpoints hsep hlevels' hprofiles'
  convert hh using 1
  ring

public  theorem double_difference_cubic_jet_bounds
    (F : ℝ → ℝ) {x r s δ y U c w : ℝ}
    (hx : x∈Icc (3/4:ℝ) (9/4)) (hy : y∈Icc (1:ℝ) 2)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hδ : 0 < δ) (hU : 0 < U) (hc : 0 < c)
    (hprod : r*s=δ*y) (hshift : r+s ≤ w) (hw : w ≤ 1/4)
    (hsmall : 2*U*w ≤ c/64)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u)
    (hbound : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) :
    let Q := fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/δ
    (∀ u, 0 < u → ContDiffAt ℝ ∞ Q u) ∧
      c/2 ≤ iteratedDeriv 3 Q x ∧
      |iteratedDeriv 3 Q x| ≤ 3*U ∧ |iteratedDeriv 4 Q x| ≤ 3*U := by
  intro Q
  have hx' : x∈Icc (1/2:ℝ) 3 :=
    ⟨by linarith only [hx.1],by linarith only [hx.2]⟩
  have hsub : Icc x (x+r+s) ⊆ Icc (1/2:ℝ) 3 := by
    intro u hu
    constructor <;> linarith only [hu.1,hu.2,hx.1,hx.2,hshift,hw]
  have hj (j : ℕ) (hj : j≤4) :
      |iteratedDeriv j Q x-y*iteratedDeriv (j+2) F x| ≤ 2*U*w :=
    normalized_double_difference_common_jet F j hr hs hδ hy hU.le hprod hshift
      (fun u hu => hf u (by linarith only [(hsub hu).1]))
      (fun u hu => hbound u (hsub hu) (j+3) (by omega) (by omega))
  have hsize (j : ℕ) (hj' : j≤4) : |iteratedDeriv j Q x| ≤ 3*U := by
    have hmain : |y*iteratedDeriv (j+2) F x| ≤ 2*U := by
      rw [abs_mul,abs_of_nonneg (by linarith only [hy.1] : 0 ≤ y)]
      exact mul_le_mul hy.2 (hbound x hx' (j+2) (by omega) (by omega)) (abs_nonneg _)
        (by norm_num)
    have htri := abs_add_le
      (iteratedDeriv j Q x-y*iteratedDeriv (j+2) F x)
      (y*iteratedDeriv (j+2) F x)
    rw [sub_add_cancel] at htri
    have herror := mul_le_mul_of_nonneg_left hw (show 0 ≤ 2*U by positivity)
    linarith only [htri,hmain,hj j hj',herror,hU]
  refine ⟨?_,?_,hsize 3 (by norm_num),hsize 4 (by norm_num)⟩
  · intro u hu
    exact ((((hf u hu).sub ((hf (u+r) (by positivity)).comp u
      (contDiffAt_id.add contDiffAt_const))).sub
        ((hf (u+s) (by positivity)).comp u (contDiffAt_id.add contDiffAt_const))).add
          ((hf (u+r+s) (by positivity)).comp u
            ((contDiffAt_id.add contDiffAt_const).add contDiffAt_const))).div_const δ
  · have hh := (abs_le.mp (hj 3 (by norm_num))).1
    have hmain : c ≤ y*iteratedDeriv 5 F x := by
      have hh' := mul_le_mul hy.1 (hlower x hx') hc.le (by linarith only [hy.1])
      simpa only [one_mul] using hh'
    linarith only [hh,hmain,hsmall,hc]

private theorem double_difference_physical_parameter_count
    {c U : ℝ} (hc : 0 < c) (hU : 0 < U) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (δ w ya xa Δ J q t T M : ℝ)
        (S : Finset ℝ) (x r s : ℝ → ℝ),
        (∀ u, 0 < u → ContDiffAt ℝ ∞ F u) →
        (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
        (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
        (∀ u∈Icc (1/2:ℝ) 3,
          c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
        0 < δ → 0 ≤ w → w ≤ 1/4 → 2*U*w ≤ c/64 →
        ya∈Icc (1:ℝ) 2 → 0 < T → 2 ≤ M → 0 ≤ Δ → 0 < J →
        t∈Icc (1/2:ℝ) 2 → xa∈Icc M (2*M) →
        (∀ y∈S, y∈Icc (1:ℝ) 2 ∧ x y∈Icc M (2*M)) →
        (∀ y∈S, ∀ z∈S, y ≠ z → 1 ≤ J*|y-z|) →
        (∀ y, y=ya ∨ y∈S →
          0 ≤ r y ∧ 0 ≤ s y ∧ r y*s y=δ*y ∧ r y+s y ≤ w) →
        let Q := fun y u => (F u-F (u+r y)-F (u+s y)+F (u+r y+s y))/δ
        let f := fun y z => T*Q y (z/M)
        let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
        (∀ y∈S, iteratedDeriv 2 (f y) (x y)/2=q) →
        (∀ y∈S, |μ y (x y)/μ ya xa*t^3-1| ≤ Δ) →
        (S.card:ℝ) ≤ K*(1+C*(24*U*(Δ+5/M)+2*U*w+12*U^2*w/c)*J) := by
  classical
  obtain ⟨K,C,hK,hC,hcount⟩ := double_difference_parameter_count hc hU
  refine ⟨K,C,hK,hC,?_⟩
  intro F δ w ya xa Δ J q t T M S x r s hf hlower hbound hdet hδ hw hwcap hsmall
    hya hT hM hΔ hJ ht hxa hpoints hsep hshifts Q f μ hmap hthird
  have hMpos : 0 < M := by linarith only [hM]
  have htpos : 0 < t := by linarith only [ht.1]
  have hpar (y : ℝ) (hy : y=ya ∨ y∈S) : y∈Icc (1:ℝ) 2 := by
    rcases hy with rfl | hy
    · exact hya
    · exact (hpoints y hy).1
  have hjet (y : ℝ) (hy : y=ya ∨ y∈S) (u : ℝ) (hu : u∈Icc (3/4:ℝ) (9/4)) :=
    double_difference_cubic_jet_bounds F hu (hpar y hy) (hshifts y hy).1
      (hshifts y hy).2.1 hδ hU hc (hshifts y hy).2.2.1 (hshifts y hy).2.2.2
      hwcap hsmall hf hlower hbound
  have hreg (y : ℝ) (hy : y=ya ∨ y∈S) :
      ∀ u, 0 < u → ContDiffAt ℝ ∞ (Q y) u :=
    (hjet y hy 1 (by norm_num)).1
  have hd (n : ℕ) (z y : ℝ) (hz : 0 < z) (hy : y=ya ∨ y∈S) :
      iteratedDeriv n (f y) z=T/M^n*iteratedDeriv n (Q y) (z/M) := by
    have ha := sargos_iteratedDeriv_comp_affine_local (f:=Q y)
      (l:=0) (r:=z+1) (c:=M⁻¹) (d:=0)
      (fun u hu => hreg y hy _ (by
        simpa only [add_zero] using mul_pos (inv_pos.mpr hMpos) hu.1))
      (show z∈Ioo (0:ℝ) (z+1) from ⟨hz,by linarith⟩) n
    change iteratedDeriv n (fun u => T*Q y (u/M)) z=_
    rw [iteratedDeriv_const_mul_field]
    have he : (fun u => Q y (u/M))=(fun u => Q y (M⁻¹*u+0)) := by
      funext u
      congr 1
      ring
    rw [he,ha]
    simp only [add_zero,inv_pow]
    rw [show M⁻¹*z=z/M by ring]
    ring
  have hnorm (z : ℝ) (hz : z∈Icc M (2*M)) : z/M∈Icc (1:ℝ) 2 :=
    ⟨(le_div_iff₀ hMpos).mpr (by simpa using hz.1),(div_le_iff₀ hMpos).mpr hz.2⟩
  let G := fun y u => iteratedDeriv 3 (Q y) u
  let g := G ya (xa/M)/t^3
  have hroots (y : ℝ) (hy : y∈S) : iteratedDeriv 2 (Q y) (x y/M)=2*M^2*q/T := by
    calc
      _ = (2*M^2/T)*(iteratedDeriv 2 (f y) (x y)/2) := by
        rw [hd 2 _ _ (hMpos.trans_le (hpoints y hy).2.1) (Or.inr hy)]
        field_simp
      _ = _ := by rw [hmap y hy]; ring
  have hnear (y : ℝ) (hy : y∈S) : |G y (x y/M)-g| ≤ 24*U*(Δ+5/M) := by
    have hroundpos (z : ℝ) (hz : z∈Icc M (2*M)) : (0:ℝ) < round z := by
      have hh := abs_le.mp (abs_sub_round z)
      linarith only [hh.2,hz.1,hM]
    have hμ (y z : ℝ) (hy : y=ya ∨ y∈S) (hz : z∈Icc M (2*M)) :
        μ y z=(T/(6*M^3))*G y ((round z:ℝ)/M) := by
      dsimp only [μ]
      rw [hd 3 _ _ (hroundpos z hz) hy]
      dsimp only [G]
      ring
    have hthird' :
        |G y ((round (M*(x y/M)):ℝ)/M)/
          G ya ((round (M*(xa/M)):ℝ)/M)*t^3-1| ≤ Δ := by
      have he (z : ℝ) : M*(z/M)=z := mul_div_cancel₀ z hMpos.ne'
      rw [he,he]
      have hh := hthird y hy
      rw [hμ y _ (Or.inr hy) (hpoints y hy).2,hμ ya _ (Or.inl rfl) hxa,
        mul_div_mul_left _ _ (show T/(6*M^3) ≠ 0 by positivity)] at hh
      exact hh
    have hdG (v : ℝ) (hv : v=ya ∨ v∈S) (u : ℝ)
        (hu : u∈Icc (3/4:ℝ) (9/4)) :
        HasDerivAt (G v) (iteratedDeriv 4 (Q v) u) u := by
      simpa only [G,iteratedDeriv_succ] using
        ((contDiffAt_iteratedDeriv_infty (hreg v hv u (by linarith only [hu.1])) 3).differentiableAt
          (by simp)).hasDerivAt
    have hh := rounded_weighted_profile_bound (G ya) (G y)
      (iteratedDeriv 4 (Q ya)) (iteratedDeriv 4 (Q y))
      (hnorm _ hxa) (hnorm _ (hpoints y hy).2) hM (by positivity : 0 ≤ 3*U) hΔ
      (hdG ya (Or.inl rfl)) (hdG y (Or.inr hy))
      (fun u hu => (hjet ya (Or.inl rfl) u hu).2.2.2)
      (fun u hu => (hjet y (Or.inr hy) u hu).2.2.2)
      (fun u hu => ⟨(hjet ya (Or.inl rfl) u hu).2.2.1,
        ne_of_gt ((show 0 < c/2 by positivity).trans_le
          (hjet ya (Or.inl rfl) u hu).2.1)⟩) hthird'
    have htp : |t^3| ≤ 8 := by
      rw [abs_of_nonneg (pow_nonneg htpos.le 3)]
      exact (pow_le_pow_left₀ htpos.le ht.2 3).trans_eq (by norm_num)
    have hround : (|t^3|+1)/(2*M) ≤ 5/M := by
      apply (div_le_div_iff₀ (show 0 < 2*M by positivity) hMpos).mpr
      nlinarith only [htp,hMpos]
    have hb : |G y (x y/M)*t^3-G ya (xa/M)| ≤ 3*U*(Δ+5/M) :=
      hh.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hround) (by positivity))
    have htl : (1/8:ℝ) ≤ t^3 := by
      convert pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) ht.1 3 using 1
      norm_num
    calc
      _ = |G y (x y/M)*t^3-G ya (xa/M)|/t^3 := by
        have he : G y (x y/M)-g=(G y (x y/M)*t^3-G ya (xa/M))/t^3 := by
          dsimp only [g]
          field_simp
        rw [he,abs_div,abs_of_pos (pow_pos htpos 3)]
      _ ≤ |G y (x y/M)*t^3-G ya (xa/M)|/(1/8) :=
        div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) htl
      _ ≤ (3*U*(Δ+5/M))/(1/8) := div_le_div_of_nonneg_right hb (by norm_num)
      _ = _ := by ring
  exact hcount F δ w (24*U*(Δ+5/M)) J (2*M^2*q/T) g S (fun y => x y/M) r s
    hf hlower
    (fun u hu => ⟨hbound u hu 4 (by norm_num) (by norm_num),
      hbound u hu 5 (by norm_num) (by norm_num),hbound u hu 6 (by norm_num) (by norm_num)⟩)
    hdet hδ hw hwcap hsmall (by positivity) hJ
    (fun y hy => ⟨(hpoints y hy).1,hnorm _ (hpoints y hy).2⟩) hsep
    (fun y hy => hshifts y (Or.inr hy)) hroots hnear

private theorem modelPhase_positive_fifth_test {σ : ℝ} (hσ : 0 < σ) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧
      ∀ F : ℝ → ℝ,
        (∀ x∈Icc (1/2:ℝ) 3,
          |iteratedDeriv 5 F x-iteratedDeriv 4 (Expdb.modelPhase σ) x| ≤ ε) →
        ∀ x∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F x := by
  have hcont : ContinuousOn (iteratedDeriv 4 (Expdb.modelPhase σ)) (Icc (1/2:ℝ) 3) := by
    intro x hx
    exact (contDiffAt_iteratedDeriv_infty
      (Real.contDiffAt_rpow_const_of_ne (by linarith only [hx.1] : x ≠ 0)) 4).continuousAt.continuousWithinAt
  have hpos (x : ℝ) (hx : x∈Icc (1/2:ℝ) 3) :
      0 < iteratedDeriv 4 (Expdb.modelPhase σ) x := by
    have hxpos : 0 < x := by linarith only [hx.1]
    have hj : iteratedDeriv 4 (Expdb.modelPhase σ) x =
        (descPochhammer ℝ 4).eval (-σ)*x^(-σ-(4:ℝ)) := by
      rw [iteratedDeriv_eq_iterate]
      exact Real.iter_deriv_rpow_const (-σ) x 4
    have he : (descPochhammer ℝ 4).eval (-σ)=σ*(σ+1)*(σ+2)*(σ+3) := by
      norm_num [descPochhammer_eval_eq_prod_range,Finset.prod_range_succ]
      ring
    rw [hj,he]
    positivity
  obtain ⟨x₀,hx₀,hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (1/2:ℝ) 3).Nonempty from ⟨1,by norm_num⟩) hcont
  let c := iteratedDeriv 4 (Expdb.modelPhase σ) x₀/2
  have hc : 0 < c := by dsimp only [c]; exact half_pos (hpos x₀ hx₀)
  refine ⟨c,c,hc,hc,?_⟩
  intro F herror x hx
  have hh := (abs_le.mp (herror x hx)).1
  have hlo : iteratedDeriv 4 (Expdb.modelPhase σ) x₀ ≤
      iteratedDeriv 4 (Expdb.modelPhase σ) x := hmin hx
  dsimp only [c] at hh ⊢
  linarith only [hh,hlo]

public  theorem approximateModelPhase_enlarged_double_difference_count
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ₀ c U K C : ℝ,
      0 < δ₀ ∧ 0 < c ∧ 0 < U ∧ 0 < K ∧ 0 < C ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1 ≤ M →
        IsApproximateModelPhaseFunction F σ 7 δ₀ →
      ∃ Fext : ℝ → ℝ,
        (∀ u, 0 < u → ContDiffAt ℝ ∞ Fext u) ∧
        (∀ u∈Icc (1/2:ℝ) 3, ∀ n≤6,
          |iteratedDeriv (n+1) Fext u-iteratedDeriv n (Expdb.modelPhase σ) u| ≤ ε) ∧
        (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n Fext u| ≤ U) ∧
        (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 Fext u) ∧
        (∀ u∈Icc (1/2:ℝ) 3, ∀ j,
          c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fext u) j|) ∧
        (∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fext u ≤ -c) ∧
        (∀ (T : ℝ) (a b : ℕ), M ≤ (a:ℝ) → (b:ℝ) ≤ 2*M →
          ‖exponentialSumAt F T M a b-exponentialSumAt Fext T M a b‖ ≤ 6) ∧
        ∀ (δ w ya xa Δ J q t T : ℝ) (S : Finset ℝ) (x r s : ℝ → ℝ),
          0 < δ → 0 ≤ w → w ≤ 1/4 → 2*U*w ≤ c/64 →
          ya∈Icc (1:ℝ) 2 → 0 < T → 2 ≤ M → 0 ≤ Δ → 0 < J →
          t∈Icc (1/2:ℝ) 2 → xa∈Icc M (2*M) →
          (∀ y∈S, y∈Icc (1:ℝ) 2 ∧ x y∈Icc M (2*M)) →
          (∀ y∈S, ∀ z∈S, y ≠ z → 1 ≤ J*|y-z|) →
          (∀ y, y=ya ∨ y∈S →
            0 ≤ r y ∧ 0 ≤ s y ∧ r y*s y=δ*y ∧ r y+s y ≤ w) →
          let Q := fun y u =>
            (Fext u-Fext (u+r y)-Fext (u+s y)+Fext (u+r y+s y))/δ
          let f := fun y z => T*Q y (z/M)
          let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
          (∀ y∈S, iteratedDeriv 2 (f y) (x y)/2=q) →
          (∀ y∈S, |μ y (x y)/μ ya xa*t^3-1| ≤ Δ) →
          (S.card:ℝ) ≤ K*(1+C*(24*U*(Δ+5/M)+2*U*w+12*U^2*w/c)*J) := by
  obtain ⟨e₀,c₀,U,he₀,hc₀,hU,htests⟩ :=
    HuxleyRationalPhase.modelPhase_compact_jet_signed_source_tests hσ
  obtain ⟨e₅,c₅,he₅,hc₅,hfifth⟩ := modelPhase_positive_fifth_test hσ
  obtain ⟨D,hD,hbuild⟩ := HuxleyRationalPhase.approximateModelPhase_enlarged_sharp_transport 6
  let e := min ε (min e₀ e₅)
  let δ₀ := e/D
  let c := min c₀ c₅
  have hc : 0 < c := lt_min hc₀ hc₅
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have he : 0 < e := lt_min hε (lt_min he₀ he₅)
  have hδ₀ : 0 < δ₀ := div_pos he hDpos
  have heq : D*δ₀=e := by dsimp only [δ₀]; field_simp
  have heε : e ≤ ε := min_le_left _ _
  have he₀' : e ≤ e₀ := (min_le_right _ _).trans (min_le_left _ _)
  have he₅' : e ≤ e₅ := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨K,C,hK,hC,hcount⟩ := double_difference_physical_parameter_count hc hU
  refine ⟨δ₀,c,U,K,C,hδ₀,hc,hU,hK,hC,?_⟩
  intro M F hM hF
  obtain ⟨Fext,hreg,hjets,hsharp⟩ := hbuild σ δ₀ M F hδ₀.le hM hF
  have hj (u : ℝ) (hu : u∈Icc (1/2:ℝ) 3) (n : ℕ) (hn : n≤6) :
      |iteratedDeriv (n+1) Fext u-iteratedDeriv n (Expdb.modelPhase σ) u| ≤ e := by
    simpa only [heq] using hjets u hu n hn
  obtain ⟨hbound,htest,hnegative⟩ := htests Fext
    (fun u hu n hn => (hj u hu n hn).trans he₀')
  have hfive : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 Fext u := by
    have hh := hfifth Fext (fun u hu => (hj u hu 4 (by norm_num)).trans he₅')
    exact fun u hu => (min_le_right c₀ c₅).trans (hh u hu)
  have hbound' : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 →
      |iteratedDeriv n Fext u| ≤ U := by
    intro u hu n hn hn'
    simpa only [Nat.sub_add_cancel hn] using hbound u hu (n-1) (by omega)
  have htest' : ∀ u∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fext u) j| :=
    fun u hu j => (min_le_left c₀ c₅).trans (htest u hu j)
  have hdet : ∀ u∈Icc (1/2:ℝ) 3,
      c ≤ |(iteratedDeriv 5 Fext u)^2-iteratedDeriv 4 Fext u*iteratedDeriv 6 Fext u| := by
    intro u hu
    have hh := htest' u hu (4:Fin 7)
    simpa [HuxleyModel.tests,abs_sub_comm] using hh
  refine ⟨Fext,hreg,fun u hu n hn => (hj u hu n hn).trans heε,
    hbound',hfive,htest',
    fun u hu => (hnegative u hu).trans (neg_le_neg (min_le_left c₀ c₅)),hsharp,?_⟩
  intro δ w ya xa Δ J q t T S x r s hδ hw hwcap hsmall hya hT hM₂ hΔ hJ
    ht hxa hpoints hsep hshifts
  exact hcount Fext δ w ya xa Δ J q t T M S x r s hreg hfive hbound' hdet hδ
    hw hwcap hsmall hya hT hM₂ hΔ hJ ht hxa hpoints hsep hshifts

private theorem physical_curvature_strictMono_of_cubic
    (Q : ℝ → ℝ) {c T M : ℝ} (hc : 0 < c) (hT : 0 < T) (hM : 0 < M)
    (hreg : ∀ u, 0 < u → ContDiffAt ℝ ∞ Q u)
    (hlower : ∀ u∈Icc (1:ℝ) 2, c ≤ iteratedDeriv 3 Q u) :
    StrictMonoOn (fun z => iteratedDeriv 2 (fun u => T*Q (u/M)) z/2)
      (Icc M (2*M)) := by
  let f := fun u => T*Q (u/M)
  have hnorm (z : ℝ) (hz : z∈Icc M (2*M)) : z/M∈Icc (1:ℝ) 2 :=
    ⟨(le_div_iff₀ hM).mpr (by simpa using hz.1),(div_le_iff₀ hM).mpr hz.2⟩
  have hd (z : ℝ) (hz : z∈Icc M (2*M)) :
      HasDerivAt (fun u => iteratedDeriv 2 f u/2) (iteratedDeriv 3 f z/2) z := by
    have hcf : ContDiffAt ℝ ∞ f z :=
      contDiffAt_const.mul ((hreg (z/M) (div_pos (hM.trans_le hz.1) hM)).comp z
        (contDiffAt_id.div_const M))
    have hh : HasDerivAt (iteratedDeriv 2 f) (iteratedDeriv 3 f z) z := by
      simpa only [iteratedDeriv_succ] using
        ((contDiffAt_iteratedDeriv_infty hcf 2).differentiableAt (by simp)).hasDerivAt
    exact hh.div_const 2
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
    (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
    (fun z hz => (hd z (interior_subset hz)).hasDerivWithinAt)
  intro z hz
  have hz' := interior_subset hz
  have hzpos : 0 < z := hM.trans_le hz'.1
  have ha := sargos_iteratedDeriv_comp_affine_local (f:=Q)
    (l:=0) (r:=z+1) (c:=M⁻¹) (d:=0)
    (fun u hu => hreg _ (by
      simpa only [add_zero] using mul_pos (inv_pos.mpr hM) hu.1))
    (show z∈Ioo (0:ℝ) (z+1) from ⟨hzpos,by linarith⟩) 3
  have hid : iteratedDeriv 3 f z=T/M^3*iteratedDeriv 3 Q (z/M) := by
    change iteratedDeriv 3 (fun u => T*Q (u/M)) z=_
    rw [iteratedDeriv_const_mul_field]
    have he : (fun u => Q (u/M))=(fun u => Q (M⁻¹*u+0)) := by
      funext u
      congr 1
      ring
    rw [he,ha]
    simp only [add_zero,inv_pow]
    rw [show M⁻¹*z=z/M by ring]
    ring
  rw [hid]
  exact half_pos (mul_pos (div_pos hT (pow_pos hM 3))
    (hc.trans_le (hlower _ (hnorm z hz'))))

private theorem double_difference_physical_family_fiber_count
    {c U : ℝ} (hc : 0 < c) (hU : 0 < U) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (S : Finset ((ℝ × ℤ) × Fin 2)) (F : ℝ → ℝ) (r s : ℝ → ℝ)
        (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ) (N : ℕ) (Z : ℝ → ℤ)
        (δ w ya xa Δ J q t T M : ℝ),
        (∀ u, 0 < u → ContDiffAt ℝ ∞ F u) →
        (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
        (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
        (∀ u∈Icc (1/2:ℝ) 3,
          c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
        0 < δ → 0 ≤ w → w ≤ 1/4 → 2*U*w ≤ c/64 →
        ya∈Icc (1:ℝ) 2 → 0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J →
        t∈Icc (1/2:ℝ) 2 → xa∈Icc M (2*M) →
        (∀ ip∈S, ip.1.1∈Icc (1:ℝ) 2 ∧ z ip.1.1 ip.1.2∈Icc M (2*M)) →
        (∀ ip∈S, N ≤ Alen ip.1.1 ip.1.2 ∧ Alen ip.1.1 ip.1.2 ≤ 3*N ∧
          round (z ip.1.1 ip.1.2)+(Alen ip.1.1 ip.1.2:ℤ)=
            Z ip.1.1+(N:ℤ)*ip.1.2+2*(N:ℤ)) →
        (∀ ip∈S, ∀ jp∈S, ip.1.1 ≠ jp.1.1 → 1 ≤ J*|ip.1.1-jp.1.1|) →
        (∀ y, y=ya ∨ y∈S.image (fun ip => ip.1.1) →
          0 ≤ r y ∧ 0 ≤ s y ∧ r y*s y=δ*y ∧ r y+s y ≤ w) →
        let Q := fun y u => (F u-F (u+r y)-F (u+s y)+F (u+r y+s y))/δ
        let f := fun y u => T*Q y (u/M)
        let h := fun y u => iteratedDeriv 2 (f y) u/2
        let μ := fun y u => iteratedDeriv 3 (f y) (round u)/6
        (∀ ip∈S, h ip.1.1 (z ip.1.1 ip.1.2)=q) →
        (∀ ip∈S, |μ ip.1.1 (z ip.1.1 ip.1.2)/μ ya xa*t^3-1| ≤ Δ) →
        (S.card:ℝ) ≤ 6*K*(1+C*(24*U*(Δ+5/M)+2*U*w+12*U^2*w/c)*J) := by
  obtain ⟨K,C,hK,hC,hcount⟩ := double_difference_physical_parameter_count hc hU
  refine ⟨K,C,hK,hC,?_⟩
  intro S F r s z Alen N Z δ w ya xa Δ J q t T M hf hlower hbound hdet
    hδ hw hwcap hsmall hya hT hM hN hΔ hJ ht hxa hpoints hgeometry hsep hshifts
    Q f h μ hlevel hthird
  classical
  have hMp : 0 < M := by linarith only [hM]
  let Y := S.image (fun ip => ip.1.1)
  have hex y (hy : y∈Y) : ∃ ip, ip∈S ∧ ip.1.1=y := Finset.mem_image.mp hy
  let pick := fun y => if hy : y∈Y then Classical.choose (hex y hy) else ((y,0),0)
  have hpick y (hy : y∈Y) : pick y∈S ∧ (pick y).1.1=y := by
    dsimp only [pick]
    rw [dite_eq_left hy]
    exact Classical.choose_spec (hex y hy)
  let root := fun y => z y (pick y).1.2
  have hparams y (hy : y∈Y) : y∈Icc (1:ℝ) 2 ∧ root y∈Icc M (2*M) := by
    have hh := hpoints _ (hpick y hy).1
    rw [(hpick y hy).2] at hh
    exact hh
  have hY := hcount F δ w ya xa Δ J q t T M Y root r s hf hlower hbound hdet
    hδ hw hwcap hsmall hya hT hM hΔ hJ ht hxa hparams
    (by
      intro y hy y' hy' hne
      have hh := hsep _ (hpick y hy).1 _ (hpick y' hy').1
      rw [(hpick y hy).2,(hpick y' hy').2] at hh
      exact hh hne) hshifts
    (by
      intro y hy
      have hh := hlevel _ (hpick y hy).1
      rw [(hpick y hy).2] at hh
      exact hh)
    (by
      intro y hy
      have hh := hthird _ (hpick y hy).1
      rw [(hpick y hy).2] at hh
      exact hh)
  have hcardR := physical_grid_level_card S z Alen Z hN h
    (fun ip hip => (hpoints ip hip).2) hgeometry hlevel (by
    intro y hy
    have hjet (u : ℝ) (hu : u∈Icc (3/4:ℝ) (9/4)) :=
      double_difference_cubic_jet_bounds F hu (hparams y hy).1
        (hshifts y (Or.inr hy)).1 (hshifts y (Or.inr hy)).2.1 hδ hU hc
        (hshifts y (Or.inr hy)).2.2.1 (hshifts y (Or.inr hy)).2.2.2
        hwcap hsmall hf hlower hbound
    have hmono := physical_curvature_strictMono_of_cubic (Q y)
      (show 0 < c/2 by positivity) hT hMp (hjet 1 (by norm_num)).1
      (fun u hu => (hjet u ⟨by linarith only [hu.1],by linarith only [hu.2]⟩).2.1)
    exact hmono.injOn)
  have hh := hcardR.trans (mul_le_mul_of_nonneg_left hY (by norm_num : (0:ℝ) ≤ 6))
  convert hh using 1
  ring

private theorem double_difference_mean_value_jet
    (F : ℝ → ℝ) {x r s : ℝ} (j : ℕ) (hr : 0 < r) (hs : 0 < s)
    (hf : ∀ u∈Icc x (x+r+s), ContDiffAt ℝ ∞ F u) :
    ∃ v∈Ioo x (x+r+s),
      iteratedDeriv j (fun u => F u-F (u+r)-F (u+s)+F (u+r+s)) x =
        r*s*iteratedDeriv (j+2) F v := by
  let G := fun u => iteratedDeriv j F (u+s)-iteratedDeriv j F u
  have hd (n : ℕ) (u : ℝ) (hu : u∈Icc x (x+r+s)) :
      HasDerivAt (iteratedDeriv n F) (iteratedDeriv (n+1) F u) u := by
    simpa only [iteratedDeriv_succ] using
      ((contDiffAt_iteratedDeriv_infty (hf u hu) n).differentiableAt (by simp)).hasDerivAt
  have hdG (u : ℝ) (hu : u∈Icc x (x+r)) :
      HasDerivAt G (iteratedDeriv (j+1) F (u+s)-iteratedDeriv (j+1) F u) u := by
    have h₁ := (hd j (u+s) ⟨by linarith only [hu.1,hs],
      by linarith only [hu.2]⟩).comp u ((hasDerivAt_id u).add_const s)
    have h₀ := hd j u ⟨hu.1,by linarith only [hu.2,hs]⟩
    convert h₁.sub h₀ using 1
    · rfl
    · simp only [mul_one]
  obtain ⟨u,hu,huEq⟩ := exists_hasDerivAt_eq_slope G
    (fun u => iteratedDeriv (j+1) F (u+s)-iteratedDeriv (j+1) F u)
    (by linarith only [hr] : x < x+r)
    (fun u hu => (hdG u hu).continuousAt.continuousWithinAt)
    (fun u hu => hdG u ⟨hu.1.le,hu.2.le⟩)
  have hsub : Icc u (u+s) ⊆ Icc x (x+r+s) := by
    intro v hv
    constructor <;> linarith only [hu.1,hu.2,hv.1,hv.2]
  obtain ⟨v,hv,hvEq⟩ := exists_hasDerivAt_eq_slope (iteratedDeriv (j+1) F)
    (iteratedDeriv (j+2) F) (by linarith only [hs] : u < u+s)
    (fun v hv => (hd (j+1) v (hsub hv)).continuousAt.continuousWithinAt)
    (fun v hv => hd (j+1) v (hsub ⟨hv.1.le,hv.2.le⟩))
  rw [show x+r-x=r by ring] at huEq
  rw [show u+s-u=s by ring] at hvEq
  have hfirst := (eq_div_iff hr.ne').mp huEq
  have hsecond := (eq_div_iff hs.ne').mp hvEq
  refine ⟨v,⟨hu.1.trans hv.1,by linarith only [hu.2,hv.2]⟩,?_⟩
  rw [double_difference_iterated_jet hr.le hs.le hf j]
  calc
    _ = r*(iteratedDeriv (j+1) F (u+s)-iteratedDeriv (j+1) F u) := by
      dsimp only [G] at hfirst
      linear_combination -hfirst
    _ = r*(iteratedDeriv (j+2) F v*s) := by rw [hsecond]
    _ = _ := by ring

private theorem double_difference_common_model
    {σ : ℝ} (hσ : 0 < σ) (P : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (F : ℝ → ℝ) (e d r s y y₀ : ℝ),
        0 ≤ e → 0 < d → 0 < r → 0 < s → r+s ≤ 1/4 →
        y∈Icc (1:ℝ) 2 → y₀∈Icc (1:ℝ) 2 → r*s=d*y →
        (∀ u, 0 < u → ContDiffAt ℝ ∞ F u) →
        (∀ u∈Icc (1/2:ℝ) 3, ∀ p≤P+2,
          |iteratedDeriv (p+1) F u-iteratedDeriv p (Expdb.modelPhase σ) u| ≤ e) →
        IsApproximateModelPhaseFunction
          (fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/(σ*(σ+1)*d*y₀))
          (σ+2) P (C*(e+r+s+|y-y₀|)) := by
  classical
  choose B hB hLip using fun j : Fin (P+1) =>
    iteratedDeriv_modelPhase_positive_compact_lipschitz
      (r:=3) (show (0:ℝ)<1/2 by norm_num) (σ+2) j.val
  let V := ∑ j : Fin (P+1), B j
  let J := ∑ j : Fin (P+1), modelPhaseJetCoefficient (σ+2) j.val
  let A := σ*(σ+1)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hV : 0 ≤ V := Finset.sum_nonneg (fun j _ => zero_le_one.trans (hB j))
  have hJ : 0 ≤ J := Finset.sum_nonneg (fun j _ => modelPhaseJetCoefficient_nonneg _ _)
  let C := max 1 (max (2/A) (max (2*V) J))
  have hCe : 2/A ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCw : 2*V ≤ C := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hCy : J ≤ C := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨C,le_max_left _ _,?_⟩
  intro F e d r s y y₀ he hd hr hs hw hy hy₀ hprod hf hjets
  have hypos : 0 < y := zero_lt_one.trans_le hy.1
  have hy₀pos : 0 < y₀ := zero_lt_one.trans_le hy₀.1
  apply approximateModelPhase_of_interior_bounds
  · intro u hu
    have hupos : 0 < u := zero_lt_one.trans_le hu.1
    exact (((((hf u hupos).sub ((hf (u+r) (by positivity)).comp u
      (contDiffAt_id.add contDiffAt_const))).sub
        ((hf (u+s) (by positivity)).comp u (contDiffAt_id.add contDiffAt_const))).add
          ((hf (u+r+s) (by positivity)).comp u
            ((contDiffAt_id.add contDiffAt_const).add contDiffAt_const))).div_const
              (σ*(σ+1)*d*y₀)).contDiffWithinAt
  · intro u hu p hp
    let R := iteratedDeriv p (Expdb.modelPhase (σ+2)) u
    have hupos : 0 < u := zero_lt_one.trans hu.1
    have hwide (v : ℝ) (hv : v∈Icc u (u+r+s)) : v∈Icc (1/2:ℝ) 3 := by
      constructor <;> linarith only [hv.1,hv.2,hu.1,hu.2,hw]
    have huwide : u∈Icc (1/2:ℝ) 3 :=
      ⟨by linarith only [hu.1],by linarith only [hu.2]⟩
    obtain ⟨v,hv,hmean⟩ := double_difference_mean_value_jet F (p+1) hr hs
      (fun v hv => hf v (hupos.trans_le hv.1))
    have hvwide := hwide v ⟨hv.1.le,hv.2.le⟩
    have hvpos : 0 < v := hupos.trans hv.1
    have hBp : B ⟨p,by omega⟩ ≤ V :=
      Finset.single_le_sum (fun j _ => zero_le_one.trans (hB j)) (Finset.mem_univ _)
    have hJp : modelPhaseJetCoefficient (σ+2) p ≤ J :=
      Finset.single_le_sum (fun j _ => modelPhaseJetCoefficient_nonneg (σ+2) j.val)
        (Finset.mem_univ (⟨p,by omega⟩ : Fin (P+1)))
    have hmodel :
        iteratedDeriv (p+2) (Expdb.modelPhase σ) v =
          A*iteratedDeriv p (Expdb.modelPhase (σ+2)) v := by
      rw [show p+2=(p+1)+1 by omega,modelPhase_iteratedDeriv_succ_parameter σ hvpos (p+1),
        modelPhase_iteratedDeriv_succ_parameter (σ+1) hvpos p,
        show σ+1+1=σ+2 by ring]
      dsimp only [A]
      ring
    have herr : |iteratedDeriv (p+3) F v-A*R| ≤ e+A*V*(r+s) := by
      have hsrc := hjets v hvwide (p+2) (by omega)
      rw [hmodel] at hsrc
      have hlip : |iteratedDeriv p (Expdb.modelPhase (σ+2)) v-R| ≤ V*(r+s) := by
        have hh := hLip ⟨p,by omega⟩ v hvwide u huwide
        have hdist : |v-u| ≤ r+s := by
          rw [abs_of_pos (sub_pos.mpr hv.1)]
          linarith only [hv.2]
        exact hh.trans (mul_le_mul hBp hdist (abs_nonneg _) hV)
      calc
        _ = |(iteratedDeriv (p+3) F v-A*iteratedDeriv p (Expdb.modelPhase (σ+2)) v)+
          A*(iteratedDeriv p (Expdb.modelPhase (σ+2)) v-R)| := by congr 1; ring
        _ ≤ |iteratedDeriv (p+3) F v-A*iteratedDeriv p (Expdb.modelPhase (σ+2)) v|+
          |A*(iteratedDeriv p (Expdb.modelPhase (σ+2)) v-R)| := abs_add_le _ _
        _ ≤ e+A*(V*(r+s)) := by
          rw [abs_mul,abs_of_pos hA]
          exact add_le_add hsrc (mul_le_mul_of_nonneg_left hlip hA.le)
        _ = _ := by ring
    have hratio : y/y₀ ≤ 2 := (div_le_iff₀ hy₀pos).mpr (by linarith only [hy.2,hy₀.1])
    have hquot :
        |r*s*iteratedDeriv (p+3) F v/(A*d*y₀)-(y/y₀)*R| ≤
          (e/A+V*(r+s))*(y/y₀) := by
      have heq : r*s*iteratedDeriv (p+3) F v/(A*d*y₀)-(y/y₀)*R =
          (y/y₀)*(iteratedDeriv (p+3) F v-A*R)/A := by
        rw [hprod]
        field_simp
      rw [heq,abs_div,abs_mul,abs_of_pos hA,abs_of_pos (div_pos hypos hy₀pos)]
      have hh := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left herr (div_nonneg hypos.le hy₀pos.le)) hA.le
      convert hh using 1
      field_simp
    have hquot' :
        |r*s*iteratedDeriv (p+3) F v/(A*d*y₀)-(y/y₀)*R| ≤ 2*e/A+2*V*(r+s) := by
      apply hquot.trans
      have hh := mul_le_mul_of_nonneg_left hratio
        (show 0 ≤ e/A+V*(r+s) by positivity)
      convert hh using 1
      ring
    have hR : |R| ≤ J :=
      (iteratedDeriv_modelPhase_abs_le (show 0 ≤ σ+2 by linarith only [hσ]) hu p).trans hJp
    have hamp : |(y/y₀)*R-R| ≤ J*|y-y₀| := by
      rw [show (y/y₀)*R-R=((y-y₀)/y₀)*R by field_simp,
        abs_mul,abs_div,abs_of_pos hy₀pos]
      calc
        _ ≤ |y-y₀| * J := mul_le_mul
          (div_le_self (abs_nonneg _) hy₀.1) hR (abs_nonneg _) (abs_nonneg _)
        _ = _ := by ring
    rw [iteratedDeriv_div_const,hmean]
    change |r*s*iteratedDeriv (p+3) F v/(A*d*y₀)-R| ≤ _
    calc
      _ ≤ |r*s*iteratedDeriv (p+3) F v/(A*d*y₀)-(y/y₀)*R|+|(y/y₀)*R-R| :=
        abs_sub_le _ _ _
      _ ≤ 2*e/A+2*V*(r+s)+J*|y-y₀| := add_le_add hquot' hamp
      _ ≤ C*e+C*(r+s)+C*|y-y₀| := by
        rw [show 2*e/A=(2/A)*e by ring]
        exact add_le_add (add_le_add
          (mul_le_mul_of_nonneg_right hCe he)
          (mul_le_mul_of_nonneg_right hCw (by positivity)))
          (mul_le_mul_of_nonneg_right hCy (abs_nonneg _))
      _ = _ := by ring

private theorem double_difference_physical_family_fiber_source_scale
    {c U : ℝ} (hc : 0 < c) (hU : 0 < U) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (S : Finset ((ℝ × ℤ) × Fin 2)) (F : ℝ → ℝ) (r s : ℝ → ℝ)
        (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ) (N : ℕ) (Z : ℝ → ℤ)
        (δ w ya xa Δ J q t T M : ℝ),
        (∀ u, 0 < u → ContDiffAt ℝ ∞ F u) →
        (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
        (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
        (∀ u∈Icc (1/2:ℝ) 3,
          c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
        0 < δ → 0 ≤ w → w ≤ 1/4 → 2*U*w ≤ c/64 →
        ya∈Icc (1:ℝ) 2 → 0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J → J ≤ M → w*J ≤ 1 →
        t∈Icc (1/2:ℝ) 2 → xa∈Icc M (2*M) →
        (∀ ip∈S, ip.1.1∈Icc (1:ℝ) 2 ∧ z ip.1.1 ip.1.2∈Icc M (2*M)) →
        (∀ ip∈S, N ≤ Alen ip.1.1 ip.1.2 ∧ Alen ip.1.1 ip.1.2 ≤ 3*N ∧
          round (z ip.1.1 ip.1.2)+(Alen ip.1.1 ip.1.2:ℤ)=
            Z ip.1.1+(N:ℤ)*ip.1.2+2*(N:ℤ)) →
        (∀ ip∈S, ∀ jp∈S, ip.1.1 ≠ jp.1.1 → 1 ≤ J*|ip.1.1-jp.1.1|) →
        (∀ y, y=ya ∨ y∈S.image (fun ip => ip.1.1) →
          0 ≤ r y ∧ 0 ≤ s y ∧ r y*s y=δ*y ∧ r y+s y ≤ w) →
        let Q := fun y u => (F u-F (u+r y)-F (u+s y)+F (u+r y+s y))/δ
        let f := fun y u => T*Q y (u/M)
        let h := fun y u => iteratedDeriv 2 (f y) u/2
        let μ := fun y u => iteratedDeriv 3 (f y) (round u)/6
        (∀ ip∈S, h ip.1.1 (z ip.1.1 ip.1.2)=q) →
        (∀ ip∈S, |μ ip.1.1 (z ip.1.1 ip.1.2)/μ ya xa*t^3-1| ≤ Δ) →
        (S.card:ℝ) ≤ D*(1+Δ*J) := by
  obtain ⟨K,C,hK,hC,hcount⟩ := double_difference_physical_family_fiber_count hc hU
  let B := 2*U+12*U^2/c
  let A := 1+C*(144*U+B)
  have hB : 0 ≤ B := by dsimp only [B, cubicScaleMajorant]; positivity
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨6*K*A,by positivity,?_⟩
  intro S F r s z Alen N Z δ w ya xa Δ J q t T M hf hlower hbound hdet
    hδ hw hwcap hsmall hya hT hM hN hΔ hJ hJM hwJ ht hxa hpoints hgeometry hsep
    hshifts Q f h μ hlevel hthird
  have hh := hcount S F r s z Alen N Z δ w ya xa Δ J q t T M hf hlower hbound hdet
    hδ hw hwcap hsmall hya hT hM hN hΔ hJ ht hxa hpoints hgeometry hsep hshifts
    hlevel hthird
  have hMp : 0 < M := by linarith only [hM]
  have hratio : J/M ≤ 1 := (div_le_iff₀ hMp).mpr (by simpa using hJM)
  have hbudget :
      (24*U*(Δ+5/M)+2*U*w+12*U^2*w/c)*J ≤ 24*U*(Δ*J)+120*U+B := by
    calc
      _ = 24*U*(Δ*J)+120*U*(J/M)+B*(w*J) := by dsimp only [B, cubicScaleMajorant]; ring
      _ ≤ 24*U*(Δ*J)+120*U*1+B*1 :=
        add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hratio (by positivity)))
          (mul_le_mul_of_nonneg_left hwJ hB)
      _ = _ := by ring
  have ha₀ : 1+C*(120*U+B) ≤ A := by
    dsimp only [A]
    nlinarith only [mul_nonneg hC.le hU.le]
  have ha₁ : 24*C*U ≤ A := by
    dsimp only [A]
    nlinarith only [mul_nonneg hC.le hU.le,mul_nonneg hC.le hB]
  have htotal :
      1+C*(24*U*(Δ+5/M)+2*U*w+12*U^2*w/c)*J ≤ A*(1+Δ*J) := by
    calc
      _ = 1+C*((24*U*(Δ+5/M)+2*U*w+12*U^2*w/c)*J) := by ring
      _ ≤ 1+C*(24*U*(Δ*J)+120*U+B) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hbudget hC.le)
      _ = (1+C*(120*U+B))+(24*C*U)*(Δ*J) := by ring
      _ ≤ A+A*(Δ*J) := add_le_add ha₀
        (mul_le_mul_of_nonneg_right ha₁ (mul_nonneg hΔ hJ.le))
      _ = _ := by ring
  exact hh.trans (by
    calc
      _ ≤ (6*K)*(A*(1+Δ*J)) := mul_le_mul_of_nonneg_left htotal (by positivity)
      _ = _ := by ring)

public  theorem double_difference_colored_common_models
    {σ ε : ℝ} (hσ : 0 < σ) (P : ℕ) (hε : 0 < ε) :
    ∃ e w₀ a : ℝ, 0 < e ∧ 0 < w₀ ∧ w₀ ≤ 1/4 ∧ 0 < a ∧
      ∀ (F : ℝ → ℝ),
        (∀ u, 0 < u → ContDiffAt ℝ ∞ F u) →
        (∀ u∈Icc (1/2:ℝ) 3, ∀ p≤P+2,
          |iteratedDeriv (p+1) F u-iteratedDeriv p (Expdb.modelPhase σ) u| ≤ e) →
        ∀ {ι : Type*} (S : Finset ι) (y r s : ι → ℝ) (d : ℝ),
          0 < d →
          (∀ i∈S, y i∈Icc (1:ℝ) 2) →
          (∀ i∈S, 0 < r i ∧ 0 < s i ∧ r i+s i ≤ w₀ ∧ r i*s i=d*y i) →
          let color := fun i => ⌊y i/a⌋
          let Cap := 4/a+3
          ((S.image color).card:ℝ) ≤ Cap ∧
          (∀ z : ι → ℂ, ‖∑ i∈S,z i‖^12 ≤
            Cap^11*∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),z i‖^12) ∧
          ∀ j∈S.image color, ∃ i₀∈S, color i₀=j ∧
            ∀ i∈S, color i=j →
              let G := fun u =>
                (F u-F (u+r i)-F (u+s i)+F (u+r i+s i))/(σ*(σ+1)*d*y i₀)
              IsApproximateModelPhaseFunction G (σ+2) P ε ∧
              ∀ T M A x : ℝ,
                heathBrownPhysicalPhase G (T*σ*(σ+1)*y i₀) M A 1 x =
                  T*(F ((A+x)/M)-F ((A+x)/M+r i)-F ((A+x)/M+s i)+
                    F ((A+x)/M+r i+s i))/d := by
  classical
  obtain ⟨C,hC,hmodel⟩ := double_difference_common_model hσ P
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  let a := ε/(3*C)
  have ha : 0 < a := by dsimp only [a]; positivity
  refine ⟨a,min (1/4:ℝ) a,a,ha,lt_min (by norm_num) ha,min_le_left _ _,ha,?_⟩
  intro F hf hjets ι S y r s d hd hy hshifts color Cap
  have hcard : ((S.image color).card:ℝ) ≤ Cap := by
    have hh := HuxleyRationalPhase.scaled_floor_image_card (Q:=1) (δ:=a) (R:=2) S y
      (by norm_num) ha (by norm_num)
      (by
        intro i hi
        rw [abs_of_pos (zero_lt_one.trans_le (hy i hi).1)]
        simpa only [mul_one] using (hy i hi).2)
    simpa only [mul_one,show (2:ℝ)*2=4 by norm_num] using hh
  refine ⟨hcard,?_,?_⟩
  · intro z
    let J := S.image color
    let V := fun j => S.filter (fun i => color i=j)
    let g := fun j => ∑ i∈V j,z i
    have he : (∑ j∈J,g j)=∑ i∈S,z i :=
      Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem color hi) z
    have hnorm : ‖∑ i∈S,z i‖ ≤ ∑ j∈J,‖g j‖ := by
      rw [←he]
      exact norm_sum_le _ _
    have hp := pow_le_pow_left₀ (norm_nonneg _) hnorm 12
    have hholder := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg J
      (f:=fun j => ‖g j‖) (p:=(12:ℝ)) (by norm_num) (fun _ _ => norm_nonneg _)
    have hh : (∑ j∈J,‖g j‖)^12 ≤ (J.card:ℝ)^11*∑ j∈J,‖g j‖^12 := by
      simpa only [show (12:ℝ)-1=11 by norm_num,Real.rpow_ofNat] using hholder
    exact (hp.trans hh).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ J.card) hcard 11)
      (Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) _)))
  · intro j hj
    obtain ⟨i₀,hi₀,hcol₀⟩ := Finset.mem_image.mp hj
    refine ⟨i₀,hi₀,hcol₀,?_⟩
    intro i hi hcol G
    have hbin : ⌊y i/a⌋=⌊y i₀/a⌋ := hcol.trans hcol₀.symm
    have hh := Int.abs_sub_lt_one_of_floor_eq_floor hbin
    rw [←sub_div,abs_div,abs_of_pos ha] at hh
    have hnear : |y i-y i₀| ≤ a :=
      (by simpa only [one_mul] using ((div_lt_iff₀ ha).mp hh).le)
    have hshift : r i+s i ≤ a := (hshifts i hi).2.2.1.trans (min_le_right _ _)
    have hm := hmodel F a d (r i) (s i) (y i) (y i₀) ha.le hd
      (hshifts i hi).1 (hshifts i hi).2.1
      ((hshifts i hi).2.2.1.trans (min_le_left _ _))
      (hy i hi) (hy i₀ hi₀) (hshifts i hi).2.2.2 hf hjets
    have htol : C*(a+r i+s i+|y i-y i₀|) ≤ ε := by
      have hh' := mul_le_mul_of_nonneg_left
        (show a+r i+s i+|y i-y i₀| ≤ 3*a by linarith only [hshift,hnear]) hCpos.le
      have he : C*(3*a)=ε := by dsimp only [a]; field_simp
      exact hh'.trans_eq he
    refine ⟨approximateModelPhase_mono hm le_rfl htol,?_⟩
    intro T M A x
    have hy₀pos : 0 < y i₀ := zero_lt_one.trans_le (hy i₀ hi₀).1
    have hσ₁ : σ+1 ≠ 0 := by linarith only [hσ]
    dsimp only [G,heathBrownPhysicalPhase]
    field_simp

private theorem double_difference_exact_curvature_band
    (F : ℝ → ℝ) {x r s d y c U : ℝ}
    (hx : x∈Icc (3/4:ℝ) (9/4)) (hy : y∈Icc (1:ℝ) 2)
    (hr : 0 < r) (hs : 0 < s) (hd : 0 < d) (hc : 0 < c) (hU : 0 < U)
    (hprod : r*s=d*y) (hshift : r+s ≤ 1/4)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hneg : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c)
    (hbound : ∀ u∈Icc (1/2:ℝ) 3, |iteratedDeriv 4 F u| ≤ U) :
    let Q := fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/d;
    -2*U ≤ iteratedDeriv 2 Q x ∧ iteratedDeriv 2 Q x ≤ -c := by
  intro Q
  have hxpos : 0 < x := by linarith only [hx.1]
  obtain ⟨v,hv,hmean⟩ := double_difference_mean_value_jet F 2 hr hs
    (fun u hu => hf u (hxpos.trans_le hu.1))
  have hvwide : v∈Icc (1/2:ℝ) 3 := by
    constructor <;> linarith only [hv.1,hv.2,hx.1,hx.2,hshift]
  have heq : iteratedDeriv 2 Q x=y*iteratedDeriv 4 F v := by
    dsimp only [Q]
    rw [iteratedDeriv_div_const,hmean,hprod]
    field_simp
  rw [heq]
  have hsign := hneg v hvwide
  have hlow := (abs_le.mp (hbound v hvwide)).1
  constructor
  · have hh := mul_le_mul_of_nonneg_left hlow (by linarith only [hy.1] : 0 ≤ y)
    have hh' := mul_le_mul_of_nonpos_right hy.2 (neg_nonpos.mpr hU.le)
    nlinarith only [hh,hh']
  · have hh := mul_le_mul_of_nonneg_left hsign (by linarith only [hy.1] : 0 ≤ y)
    have hh' := mul_le_mul_of_nonpos_right hy.1 (neg_nonpos.mpr hc.le)
    nlinarith only [hh,hh']

private theorem double_difference_family_pair_card_le_matrix_points
    {c U : ℝ} (hc : 0 < c) (hU : 0 < U) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
        (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
        (F : ℝ → ℝ) (r s : ℝ → ℝ) (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ)
        (N : ℕ) (Z : ℝ → ℤ) (d w Δ J T M : ℝ),
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
      (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
      (∀ u∈Icc (1/2:ℝ) 3,
        c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
      0 < d → 0 ≤ w → w ≤ 1/4 → 2*U*w ≤ c/64 →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J → J ≤ M → w*J ≤ 1 →
      (∀ ij∈P,
        (ij.1.1.1∈Icc (1:ℝ) 2 ∧ z ij.1.1.1 ij.1.1.2∈Icc M (2*M)) ∧
        (ij.2.1.1∈Icc (1:ℝ) 2 ∧ z ij.2.1.1 ij.2.1.2∈Icc M (2*M))) →
      (∀ ij∈P, N ≤ Alen ij.2.1.1 ij.2.1.2 ∧ Alen ij.2.1.1 ij.2.1.2 ≤ 3*N ∧
        round (z ij.2.1.1 ij.2.1.2)+(Alen ij.2.1.1 ij.2.1.2:ℤ)=
          Z ij.2.1.1+(N:ℤ)*ij.2.1.2+2*(N:ℤ)) →
      (∀ ij∈P, ∀ kl∈P, ij.2.1.1 ≠ kl.2.1.1 → 1 ≤ J*|ij.2.1.1-kl.2.1.1|) →
      (∀ y∈(P.image (fun ij => ij.1.1.1)) ∪ (P.image (fun ij => ij.2.1.1)),
        0 ≤ r y ∧ 0 ≤ s y ∧ r y*s y=d*y ∧ r y+s y ≤ w) →
      let Q := fun y u => (F u-F (u+r y)-F (u+s y)+F (u+r y+s y))/d
      let f := fun y u => T*Q y (u/M)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let μ := fun y w => iteratedDeriv 3 (f y) (round w)/6
      let t := fun ij => (Mat ij 2:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 3
      (∀ ij∈P, t ij∈Icc (1/2:ℝ) 2) →
      (∀ ij∈P, ((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/t ij=
        h ij.2.1.1 (z ij.2.1.1 ij.2.1.2)) →
      (∀ ij∈P, |μ ij.2.1.1 (z ij.2.1.1 ij.2.1.2)/
        μ ij.1.1.1 (z ij.1.1.1 ij.1.1.2)*(t ij)^3-1| ≤ Δ) →
      (P.card:ℝ) ≤ D*(1+Δ*J)*
        ((P.image (fun ij => (Mat ij,ij.1))).card:ℝ) := by
  obtain ⟨D,hD,hcount⟩ := double_difference_physical_family_fiber_source_scale hc hU
  refine ⟨D,hD,?_⟩
  intro P Mat F r s z Alen N Z d w Δ J T M hf hlower hbound hdet
    hd hw hwcap hsmall hT hM hN hΔ hJ hJM hwJ hpoints hgeometry hsep hshifts
    Q f h μ t ht hmap hthird
  classical
  refine matrix_pair_card_of_fixed_left P Mat
    (fun ip => h ip.1.1 (z ip.1.1 ip.1.2)) (fun ip => μ ip.1.1 (z ip.1.1 ip.1.2))
    hmap hthird ?_
  intro ij₀ hij₀ S t₀ hsub hlev hmu
  exact hcount S F r s z Alen N Z d w ij₀.1.1.1 (z ij₀.1.1.1 ij₀.1.1.2)
      Δ J (((Mat ij₀ 0:ℝ)*h ij₀.1.1.1 (z ij₀.1.1.1 ij₀.1.1.2)+Mat ij₀ 1)/t ij₀)
      (t ij₀) T M hf hlower hbound hdet hd hw hwcap hsmall (hpoints ij₀ hij₀).1.1
      hT hM hN hΔ hJ hJM hwJ (ht ij₀ hij₀) (hpoints ij₀ hij₀).1.2
    (fun ip hip => (hpoints _ (hsub ip hip)).2)
    (fun ip hip => hgeometry _ (hsub ip hip))
    (fun ip hip jp hjp => hsep _ (hsub ip hip) _ (hsub jp hjp))
    (by
      intro y hy
      apply hshifts y
      rcases hy with rfl | hy
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hij₀)
      · obtain ⟨ip,hip,rfl⟩ := Finset.mem_image.mp hy
        exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (hsub ip hip)))
    hlev hmu

private theorem double_difference_type_one_matrix_source_scale
    {c U L : ℝ} (hc : 0 < c) (hU : 0 < U) (hL : 0 ≤ L) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
        (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
        (F : ℝ → ℝ) (r s : ℝ → ℝ) (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ)
        (N : ℕ) (Z : ℝ → ℤ) (d w Δ J T M : ℝ),
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
      (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
      (∀ u∈Icc (1/2:ℝ) 3,
        c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
      (∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c) →
      0 < d → 0 ≤ w → w ≤ 1/4 → 2*U*w ≤ c/64 →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J → (N:ℝ) ≤ M → J ≤ M → w*J ≤ 1 →
      (∀ ij∈P,
        (ij.1.1.1∈Icc (1:ℝ) 2 ∧ z ij.1.1.1 ij.1.1.2∈Icc M (2*M)) ∧
        (ij.2.1.1∈Icc (1:ℝ) 2 ∧ z ij.2.1.1 ij.2.1.2∈Icc M (2*M))) →
      (∀ ij∈P, N ≤ Alen ij.1.1.1 ij.1.1.2 ∧ Alen ij.1.1.1 ij.1.1.2 ≤ 3*N ∧
        round (z ij.1.1.1 ij.1.1.2)+(Alen ij.1.1.1 ij.1.1.2:ℤ)=
          Z ij.1.1.1+(N:ℤ)*ij.1.1.2+2*(N:ℤ)) →
      (∀ ij∈P, N ≤ Alen ij.2.1.1 ij.2.1.2 ∧ Alen ij.2.1.1 ij.2.1.2 ≤ 3*N ∧
        round (z ij.2.1.1 ij.2.1.2)+(Alen ij.2.1.1 ij.2.1.2:ℤ)=
          Z ij.2.1.1+(N:ℤ)*ij.2.1.2+2*(N:ℤ)) →
      (∀ ij∈P, ∀ kl∈P, ij.2.1.1 ≠ kl.2.1.1 → 1 ≤ J*|ij.2.1.1-kl.2.1.1|) →
      (∀ y∈(P.image (fun ij => ij.1.1.1)) ∪ (P.image (fun ij => ij.2.1.1)),
        0 ≤ r y ∧ 0 ≤ s y ∧ r y*s y=d*y ∧ r y+s y ≤ w) →
      (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
      (∀ ij∈P, Mat ij=![1,0,0,1] ∨
        (Mat ij 1 ≠ 0 ∧ Mat ij 2 ≠ 0 ∧ |(Mat ij 2:ℝ)| * (U*T/M^2) ≤ L)) →
      let Q := fun y u => (F u-F (u+r y)-F (u+s y)+F (u+r y+s y))/d
      let f := fun y u => T*Q y (u/M)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let μ := fun y w => iteratedDeriv 3 (f y) (round w)/6
      let t := fun ij => (Mat ij 2:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 3
      (∀ ij∈P, ((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/t ij=
        h ij.2.1.1 (z ij.2.1.1 ij.2.1.2)) →
      (∀ ij∈P, |t ij-1| ≤ 1/(8*(L+3))) →
      (∀ ij∈P, |((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/
        h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)-1| ≤ 1/(8*(L+3))) →
      (∀ ij∈P, |μ ij.2.1.1 (z ij.2.1.1 ij.2.1.2)/
        μ ij.1.1.1 (z ij.1.1.1 ij.1.1.2)*(t ij)^3-1| ≤ Δ) →
      (P.card:ℝ) ≤ D*((P.image (fun ij => ij.1.1.1)).card:ℝ)*(M/(N:ℝ))*(1+Δ*J) := by
  obtain ⟨D,hD,hcount⟩ := double_difference_family_pair_card_le_matrix_points hc hU
  let CMat := (2*(L+3)^2+1)*(2*L+5)^2*(L+3)^2
  have hCMat : 0 < CMat := by dsimp only [CMat]; positivity
  refine ⟨10*D*(1+CMat),by positivity,?_⟩
  intro P Mat F r s z Alen N Z d w Δ J T M hf hlower hbound hdet hnegative
    hd hw hwcap hsmall hT hM hN hΔ hJ hNM hJM hwJ hpoints hgeometryA hgeometryB
    hsep hshifts hmatdet hbranch Q f h μ t hmap hden hnum hthird
  classical
  have hMp : 0 < M := by linarith only [hM]
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  let Hcurv := U*T/M^2
  let Smat := P.image Mat
  let Snon := Smat.filter (fun A => A 1 ≠ 0)
  have hex A (hA : A∈Smat) : ∃ ij, ij∈P ∧ Mat ij=A := Finset.mem_image.mp hA
  let pick := fun A => if hA : A∈Smat then Classical.choose (hex A hA) else (((0,0),0),((0,0),0))
  have hpick A (hA : A∈Smat) : pick A∈P ∧ Mat (pick A)=A := by
    dsimp only [pick]
    rw [dite_eq_left hA]
    exact Classical.choose_spec (hex A hA)
  have hnon A (hA : A∈Snon) :
      A 1 ≠ 0 ∧ A 2 ≠ 0 ∧ |(A 2:ℝ)| * Hcurv ≤ L := by
    have hm := Finset.mem_filter.mp hA
    have hb := hbranch _ (hpick A hm.1).1
    rw [(hpick A hm.1).2] at hb
    rcases hb with he | hb
    · exfalso
      apply hm.2
      simp only [he,Matrix.cons_val_one,Matrix.cons_val_zero]
    · exact hb
  have hcurv y v
      (hy : y∈(P.image (fun ij => ij.1.1.1)) ∪ (P.image (fun ij => ij.2.1.1)))
      (hyI : y∈Icc (1:ℝ) 2) (hv : v∈Icc M (2*M)) :
      h y v ≠ 0 ∧ |h y v| ≤ Hcurv := by
    have hx : v/M∈Icc (3/4:ℝ) (9/4) := by
      constructor
      · apply (le_div_iff₀ hMp).mpr
        linarith only [hv.1,hMp]
      · apply (div_le_iff₀ hMp).mpr
        linarith only [hv.2,hMp]
    have hsdata := hshifts y hy
    have hprodpos : 0 < r y*s y := by
      rw [hsdata.2.2.1]
      exact mul_pos hd (by linarith only [hyI.1])
    have hrp : 0 < r y := by nlinarith only [hsdata.1,hsdata.2.1,hprodpos]
    have hsp : 0 < s y := by nlinarith only [hsdata.1,hsdata.2.1,hprodpos]
    have hband := double_difference_exact_curvature_band F hx hyI hrp hsp hd hc hU
      hsdata.2.2.1 (hsdata.2.2.2.trans hwcap) hf hnegative
      (fun u hu => hbound u hu 4 (by norm_num) (by norm_num))
    have hreg := (double_difference_cubic_jet_bounds F hx hyI hsdata.1 hsdata.2.1
      hd hU hc hsdata.2.2.1 hsdata.2.2.2 hwcap hsmall hf hlower hbound).1
    have ha := sargos_iteratedDeriv_comp_affine_local (f:=Q y)
      (l:=0) (r:=v+1) (c:=M⁻¹) (d:=0)
      (fun u hu => hreg _ (by
        simpa only [add_zero] using mul_pos (inv_pos.mpr hMp) hu.1))
      (show v∈Ioo (0:ℝ) (v+1) from ⟨hMp.trans_le hv.1,by linarith⟩) 2
    have heq : h y v=(T/M^2)*iteratedDeriv 2 (Q y) (v/M)/2 := by
      dsimp only [h,f, physicalFirstDifference]
      rw [iteratedDeriv_const_mul_field]
      have he : (fun u => Q y (u/M))=(fun u => Q y (M⁻¹*u+0)) := by
        funext u
        congr 1
        ring
      rw [he,ha]
      simp only [add_zero,inv_pow]
      rw [show M⁻¹*v=v/M by ring]
      ring
    have hscale : 0 < T/M^2 := div_pos hT (pow_pos hMp 2)
    have hneg : h y v < 0 := by
      rw [heq]
      exact div_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg hscale (lt_of_le_of_lt hband.2 (by linarith only [hc])))
        (by norm_num)
    refine ⟨ne_of_lt hneg,?_⟩
    rw [abs_of_neg hneg,heq]
    have hlo := mul_le_mul_of_nonneg_left hband.1 hscale.le
    change T/M^2*(-2*U) ≤ T/M^2*iteratedDeriv 2 (Q y) (v/M) at hlo
    dsimp only [Hcurv]
    convert neg_le_neg (div_le_div_of_nonneg_right hlo (by norm_num : (0:ℝ) ≤ 2)) using 1
    ring
  let x := fun A => h (pick A).1.1.1 (z (pick A).1.1.1 (pick A).1.1.2)
  let y := fun A => h (pick A).2.1.1 (z (pick A).2.1.1 (pick A).2.1.2)
  have hmat := HuxleyRationalPhase.bounded_action_narrow_nontriangular_matrix_count
    (H:=Hcurv) Snon x y hL
    (by
      intro A hA
      have hh := hmatdet _ (hpick A (Finset.mem_filter.mp hA).1).1
      rw [(hpick A (Finset.mem_filter.mp hA).1).2] at hh
      exact hh)
    (fun A hA => ⟨(hnon A hA).1,(hnon A hA).2.1⟩)
    (by
      intro A hA
      have hpickA := (hpick A (Finset.mem_filter.mp hA).1).1
      have hp := hpoints _ hpickA
      have ha := hcurv _ _
        (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hpickA)) hp.1.1 hp.1.2
      have hb := hcurv _ _
        (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hpickA)) hp.2.1 hp.2.2
      exact ⟨ha.1,ha.2,hb.2⟩)
    (fun A hA => (hnon A hA).2.2)
    (by
      intro A hA
      have hh := hmap _ (hpick A (Finset.mem_filter.mp hA).1).1
      dsimp only [t] at hh
      rw [(hpick A (Finset.mem_filter.mp hA).1).2] at hh
      exact hh)
    (by
      intro A hA
      have hh := hden _ (hpick A (Finset.mem_filter.mp hA).1).1
      dsimp only [t] at hh
      rw [(hpick A (Finset.mem_filter.mp hA).1).2] at hh
      exact hh)
    (by
      intro A hA
      have hh := hnum _ (hpick A (Finset.mem_filter.mp hA).1).1
      rw [(hpick A (Finset.mem_filter.mp hA).1).2] at hh
      exact hh)
  have hsubmat : Smat ⊆ insert ![1,0,0,1] Snon := by
    intro A hA
    have hb := hbranch _ (hpick A hA).1
    rw [(hpick A hA).2] at hb
    rcases hb with he | hb
    · exact Finset.mem_insert.mpr (Or.inl he)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨hA,hb.1⟩))
  have hmatall : (Smat.card:ℝ) ≤ 1+CMat := by
    have hh : (Smat.card:ℝ) ≤ (Snon.card:ℝ)+1 := by
      exact_mod_cast (Finset.card_le_card hsubmat).trans (Finset.card_insert_le _ _)
    linarith only [hh,hmat]
  have ht ij (hij : ij∈P) : t ij∈Icc (1/2:ℝ) 2 := by
    have hε : 1/(8*(L+3)) ≤ (1:ℝ)/24 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith only [hL])
    have hh := abs_le.mp ((hden ij hij).trans hε)
    constructor <;> linarith only [hh.1,hh.2]
  have hpair := hcount P Mat F r s z Alen N Z d w Δ J T M hf hlower hbound hdet
    hd hw hwcap hsmall hT hM hN hΔ hJ hJM hwJ hpoints hgeometryB hsep hshifts
    ht hmap hthird
  have hsub : P.image (fun ij => (Mat ij,ij.1)) ⊆ Smat ×ˢ P.image Prod.fst := by
    intro a ha
    obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem Mat hij,Finset.mem_image_of_mem Prod.fst hij⟩
  have hcard : ((P.image (fun ij => (Mat ij,ij.1))).card:ℝ) ≤
      (Smat.card:ℝ)*((P.image Prod.fst).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_product Smat (P.image Prod.fst))
  have hfirst := HuxleyRationalPhase.rounded_offset_family_point_count
    (P.image Prod.fst) z Alen N Z hMp.le hN
    (by
      intro ip hip
      obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hip
      exact (hpoints ij hij).1.2)
    (by
      intro ip hip
      obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hip
      exact hgeometryA ij hij)
  rw [Finset.image_image] at hfirst
  let I := ((P.image (fun ij => ij.1.1.1)).card:ℝ)
  have hI : 0 ≤ I := by dsimp only [I]; positivity
  have hscale : 1 ≤ M/(N:ℝ) := (le_div_iff₀ hNp).mpr (by simpa only [one_mul] using hNM)
  have hfirst' : ((P.image Prod.fst).card:ℝ) ≤ 10*(M/(N:ℝ))*I := by
    apply hfirst.trans
    apply mul_le_mul_of_nonneg_right _ hI
    linarith only [hscale]
  calc
    (P.card:ℝ) ≤ D*(1+Δ*J)*((P.image (fun ij => (Mat ij,ij.1))).card:ℝ) := hpair
    _ ≤ D*(1+Δ*J)*((Smat.card:ℝ)*((P.image Prod.fst).card:ℝ)) :=
      mul_le_mul_of_nonneg_left hcard (by positivity)
    _ ≤ D*(1+Δ*J)*((1+CMat)*(10*(M/(N:ℝ))*I)) := by gcongr
    _ = _ := by ring

private theorem double_difference_triangular_pair_source_scale
    {c U : ℝ} (hc : 0 < c) (hU : 0 < U) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
        (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
        (F : ℝ → ℝ) (r s : ℝ → ℝ) (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ)
        (N : ℕ) (Z : ℝ → ℤ) (d w Δ J T M B : ℝ),
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
      (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
      (∀ u∈Icc (1/2:ℝ) 3,
        c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
      0 < d → 0 ≤ w → w ≤ 1/4 → 2*U*w ≤ c/64 →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J → (N:ℝ) ≤ M → J ≤ M → w*J ≤ 1 → 0 ≤ B →
      (∀ ij∈P,
        (ij.1.1.1∈Icc (1:ℝ) 2 ∧ z ij.1.1.1 ij.1.1.2∈Icc M (2*M)) ∧
        (ij.2.1.1∈Icc (1:ℝ) 2 ∧ z ij.2.1.1 ij.2.1.2∈Icc M (2*M))) →
      (∀ ij∈P, N ≤ Alen ij.1.1.1 ij.1.1.2 ∧ Alen ij.1.1.1 ij.1.1.2 ≤ 3*N ∧
        round (z ij.1.1.1 ij.1.1.2)+(Alen ij.1.1.1 ij.1.1.2:ℤ)=
          Z ij.1.1.1+(N:ℤ)*ij.1.1.2+2*(N:ℤ)) →
      (∀ ij∈P, N ≤ Alen ij.2.1.1 ij.2.1.2 ∧ Alen ij.2.1.1 ij.2.1.2 ≤ 3*N ∧
        round (z ij.2.1.1 ij.2.1.2)+(Alen ij.2.1.1 ij.2.1.2:ℤ)=
          Z ij.2.1.1+(N:ℤ)*ij.2.1.2+2*(N:ℤ)) →
      (∀ ij∈P, ∀ kl∈P, ij.2.1.1 ≠ kl.2.1.1 → 1 ≤ J*|ij.2.1.1-kl.2.1.1|) →
      (∀ y∈(P.image (fun ij => ij.1.1.1)) ∪ (P.image (fun ij => ij.2.1.1)),
        0 ≤ r y ∧ 0 ≤ s y ∧ r y*s y=d*y ∧ r y+s y ≤ w) →
      (∀ ij∈P, Mat ij 0=1 ∧ Mat ij 3=1 ∧
        ((Mat ij 2=0 ∧ |(Mat ij 1:ℝ)| ≤ B) ∨ (Mat ij 1=0 ∧ |(Mat ij 2:ℝ)| ≤ B))) →
      let Q := fun y u => (F u-F (u+r y)-F (u+s y)+F (u+r y+s y))/d
      let f := fun y u => T*Q y (u/M)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let μ := fun y w => iteratedDeriv 3 (f y) (round w)/6
      let t := fun ij => (Mat ij 2:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 3
      (∀ ij∈P, t ij∈Icc (1/2:ℝ) 2) →
      (∀ ij∈P, ((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/t ij=
        h ij.2.1.1 (z ij.2.1.1 ij.2.1.2)) →
      (∀ ij∈P, |μ ij.2.1.1 (z ij.2.1.1 ij.2.1.2)/
        μ ij.1.1.1 (z ij.1.1.1 ij.1.1.2)*(t ij)^3-1| ≤ Δ) →
      (P.card:ℝ) ≤ D*(1+B)*((P.image (fun ij => ij.1.1.1)).card:ℝ)*(M/(N:ℝ))*(1+Δ*J) := by
  obtain ⟨D,hD,hcount⟩ := double_difference_family_pair_card_le_matrix_points hc hU
  refine ⟨40*D,by positivity,?_⟩
  intro P Mat F r s z Alen N Z d w Δ J T M B hf hlower hbound hdet
    hd hw hwcap hsmall hT hM hN hΔ hJ hNM hJM hwJ hB hpoints hgeometryA hgeometryB
    hsep hshifts hbranch Q f h μ t ht hmap hthird
  classical
  have hMp : 0 < M := by linarith only [hM]
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  let Smat := P.image Mat
  let Entries := Smat.image (fun A => A 1+A 2)
  have hdata A (hA : A∈Smat) : A 0=1 ∧ A 3=1 ∧
      ((A 2=0 ∧ |(A 1:ℝ)| ≤ B) ∨ (A 1=0 ∧ |(A 2:ℝ)| ≤ B)) := by
    obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hA
    exact hbranch ij hij
  have hentries : (Entries.card:ℝ) ≤ 2*B+1 :=
    integer_card_le_of_abs_sub_le (a:=0) Entries hB (by
      intro e he
      obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp he
      rcases (hdata A hA).2.2 with hb | hb
      · simpa only [hb.1,add_zero,sub_zero] using hb.2
      · simpa only [hb.1,zero_add,sub_zero] using hb.2)
  let Upper := Entries.image (fun e => (![1,e,0,1] : Fin 4 → ℤ))
  let Lower := Entries.image (fun e => (![1,0,e,1] : Fin 4 → ℤ))
  have hsubmat : Smat ⊆ Upper ∪ Lower := by
    intro A hA
    have he : A 1+A 2∈Entries := Finset.mem_image_of_mem _ hA
    have ha := hdata A hA
    rcases ha.2.2 with hb | hb
    · apply Finset.mem_union_left
      refine Finset.mem_image.mpr ⟨A 1+A 2,he,?_⟩
      funext j
      fin_cases j <;> simp [ha.1,ha.2.1,hb.1]
    · apply Finset.mem_union_right
      refine Finset.mem_image.mpr ⟨A 1+A 2,he,?_⟩
      funext j
      fin_cases j <;> simp [ha.1,ha.2.1,hb.1]
  have hmat : (Smat.card:ℝ) ≤ 4*(1+B) := by
    have hh : (Smat.card:ℝ) ≤ (Entries.card:ℝ)+(Entries.card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hsubmat).trans
        ((Finset.card_union_le Upper Lower).trans
          (Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)))
    linarith only [hh,hentries]
  have hpair := hcount P Mat F r s z Alen N Z d w Δ J T M hf hlower hbound hdet
    hd hw hwcap hsmall hT hM hN hΔ hJ hJM hwJ hpoints hgeometryB hsep hshifts
    ht hmap hthird
  have hsub : P.image (fun ij => (Mat ij,ij.1)) ⊆ Smat ×ˢ P.image Prod.fst := by
    intro a ha
    obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem Mat hij,Finset.mem_image_of_mem Prod.fst hij⟩
  have hcard : ((P.image (fun ij => (Mat ij,ij.1))).card:ℝ) ≤
      (Smat.card:ℝ)*((P.image Prod.fst).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_product Smat (P.image Prod.fst))
  have hfirst := HuxleyRationalPhase.rounded_offset_family_point_count
    (P.image Prod.fst) z Alen N Z hMp.le hN
    (by
      intro ip hip
      obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hip
      exact (hpoints ij hij).1.2)
    (by
      intro ip hip
      obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hip
      exact hgeometryA ij hij)
  rw [Finset.image_image] at hfirst
  let I := ((P.image (fun ij => ij.1.1.1)).card:ℝ)
  have hI : 0 ≤ I := by dsimp only [I]; positivity
  have hscale : 1 ≤ M/(N:ℝ) := (le_div_iff₀ hNp).mpr (by simpa only [one_mul] using hNM)
  have hfirst' : ((P.image Prod.fst).card:ℝ) ≤ 10*(M/(N:ℝ))*I := by
    apply hfirst.trans
    apply mul_le_mul_of_nonneg_right _ hI
    linarith only [hscale]
  calc
    (P.card:ℝ) ≤ D*(1+Δ*J)*((P.image (fun ij => (Mat ij,ij.1))).card:ℝ) := hpair
    _ ≤ D*(1+Δ*J)*((Smat.card:ℝ)*((P.image Prod.fst).card:ℝ)) :=
      mul_le_mul_of_nonneg_left hcard (by positivity)
    _ ≤ D*(1+Δ*J)*((4*(1+B))*(10*(M/(N:ℝ))*I)) := by gcongr
    _ = _ := by ring

private theorem double_difference_colored_fourier_cloud_type_one_and_triangular
    {c U L : ℝ} (hc : 0 < c) (hU : 0 < U) (hL : 0 ≤ L) :
    ∃ Dtype : ℝ, 0 < Dtype ∧
    ∀ (S : Finset (ℝ × ℤ)) (F rshift sshift : ℝ → ℝ)
      (z : (ℝ × ℤ) → ℝ) (r : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ)
      (Alen : (ℝ × ℤ) → ℕ) (Z : ℝ → ℤ)
      (Q K₀ N : ℕ) [NeZero K₀] (d Wmax T M Jsep : ℝ),
    (∀ u, 0 < u → ContDiffAt ℝ ∞ F u) →
    (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
    (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
    (∀ u∈Icc (1/2:ℝ) 3,
      c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
    (∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c) →
    0 < d → 0 ≤ Wmax → Wmax ≤ 1/4 → 2*U*Wmax ≤ c/64 →
    0 < T → 2 ≤ M → 0 < N → 0 < Q →
    0 < Jsep → (N:ℝ) ≤ M → Jsep ≤ M → Wmax*Jsep ≤ 1 →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Icc M (2*M)) →
    (∀ i∈S, N ≤ Alen i ∧ Alen i ≤ 3*N ∧
      round (z i)+(Alen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    (∀ y∈S.image Prod.fst,
      0 ≤ rshift y ∧ 0 ≤ sshift y ∧ rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
    let Φ := fun y u =>
      (F u-F (u+rshift y)-F (u+sshift y)+F (u+rshift y+sshift y))/d
    let f := fun i : ℝ × ℤ => fun u => T*Φ i.1 (u/M)
    (∀ i∈S, iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) →
    (∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den) →
    (∀ i∈S, ((r i).den:ℤ) ∣ (r i).num*v i-1) →
    let μ₀ := c*T/(12*M^3)
    let U₀ := U*T/(2*M^3)
    let q := fun i => (r i).den
    let μ := fun i => iteratedDeriv 3 (f i) (round (z i))/6
    let ℓ := fun i => deriv (f i) (round (z i))
    let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
    let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
    let K := fun i => cubicDualPhase (μ i) (q i)
    let x := fun i p => cubicCoordinates (v i) (b i p) (q i) (K i) (τ i p)
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let w := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![Int.fract (x ip.1 ip.2 0),Int.fract (x ip.1 ip.2 1),
        x ip.1 ip.2 2/Real.sqrt K₀,x ip.1 ip.2 3/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let P := (V ×ˢ V).filter (fun ij => ∀ d, |w ij.1 d-w ij.2 d| ≤ 2*radius d)
    let h := fun i => iteratedDeriv 2 (f i) (z i)/2
    let D := (Real.sqrt K₀/(9*(K₀:ℝ))+Real.sqrt K₀/(12*(K₀:ℝ)^2))*
      Real.sqrt (U₀*(Q:ℝ)^3)
    let δ := 1/(8*(L+3))
    let lambda := c*T/(2*M^2)
    let Hcurv := U*T/M^2
    let q₀ := (Q:ℝ)/2
    let p₀ := lambda*(Q:ℝ)/2
    let color := fun i => (⌊((r i).den:ℝ)/(δ*q₀)⌋,⌊((r i).num:ℝ)/(δ*p₀)⌋)
    let Cap := (4/δ+3)*(8*U/(c*δ)+3)
    ((S.image color).card:ℝ) ≤ Cap ∧
    (∀ coeff : (ℝ × ℤ) → ℂ, ‖∑ i∈S,coeff i‖^12 ≤ Cap^11*
      ∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),coeff i‖^12) ∧
    ∃ A : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ,
      (∀ ij∈P,
        A ij 0*A ij 3-A ij 1*A ij 2=1 ∧
        let t := (A ij 2:ℝ)*h ij.1.1+A ij 3
        t=(q ij.2.1:ℝ)/q ij.1.1 ∧ (1:ℝ)/2 ≤ t ∧ t ≤ 2 ∧
        ((A ij 0:ℝ)*h ij.1.1+A ij 1)/t=h ij.2.1 ∧
        |(A ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) ∧
        |μ ij.2.1/μ ij.1.1*t^3-1| ≤
          (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2) ∧
        |τ ij.1.1 ij.1.2-τ ij.2.1 ij.2.2| ≤ D ∧
        (∃ e₁ e₂ : ℤ,
          let F₁ := 2*(round (z ij.2.1):ℝ)-2*(A ij 3:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 2:ℝ)*ℓ ij.1.1
          let F₂ := ℓ ij.2.1-2*(A ij 1:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 0:ℝ)*ℓ ij.1.1
          |F₁-e₁| ≤ (q ij.2.1:ℝ)/(6*(K₀:ℝ))+|(A ij 2:ℝ)|/q ij.1.1 ∧
          |(F₂-e₂)-h ij.2.1*(F₁-e₁)| ≤ 2*D/q ij.2.1) ∧
        ((Q:ℝ)^2/(6*(K₀:ℝ)^2) < 1 →
          A ij 2=0 ∧ q ij.1.1=q ij.2.1 ∧
            (q ij.1.1:ℤ) ∣ (r ij.2.1).num-(r ij.1.1).num)) ∧
      (∀ ij∈P, color ij.1.1=color ij.2.1 →
        let t := (A ij 2:ℝ)*h ij.1.1+A ij 3
        |t-1| ≤ δ ∧
        |((A ij 0:ℝ)*h ij.1.1+A ij 1)/h ij.1.1-1| ≤ δ ∧
        ((A ij 0=1 ∧ A ij 1=0 ∧ A ij 2=0 ∧ A ij 3=1) ∨
         (A ij 0=1 ∧ A ij 3=1 ∧ A ij 2=0 ∧ A ij 1≠0 ∧ |(A ij 1:ℝ)| ≤ δ*Hcurv) ∨
         (A ij 0=1 ∧ A ij 3=1 ∧ A ij 1=0 ∧ A ij 2≠0 ∧ |(A ij 2:ℝ)| ≤ δ/lambda) ∨
         (A ij 1≠0 ∧ A ij 2≠0)) ∧
        (|(A ij 2:ℝ)| * Hcurv ≤ L →
          A ij 0+A ij 3=2 ∧ (A ij 0-1)^2= -A ij 1*A ij 2)) ∧
      let E := P.filter (fun ij =>
        color ij.1.1=color ij.2.1 ∧
        ((A ij 0=1 ∧ A ij 1=0 ∧ A ij 2=0 ∧ A ij 3=1) ∨
         (A ij 1≠0 ∧ A ij 2≠0 ∧ |(A ij 2:ℝ)| * Hcurv ≤ L)))
      let Δ := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
      (E.card:ℝ) ≤ Dtype*((S.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δ*Jsep) ∧
      let Etri := P.filter (fun ij =>
        color ij.1.1=color ij.2.1 ∧ (A ij 2=0 ∨ A ij 1=0))
      (Etri.card:ℝ) ≤ Dtype*(1+δ*(Hcurv+1/lambda))*
        ((S.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δ*Jsep) := by
  obtain ⟨Dtype,hDtype,hcount⟩ := double_difference_type_one_matrix_source_scale hc hU hL
  obtain ⟨Dtri,hDtri,htri⟩ := double_difference_triangular_pair_source_scale hc hU
  have hDsmall : Dtype ≤ Dtype+Dtri := by linarith only [hDtri]
  have hDtrismall : Dtri ≤ Dtype+Dtri := by linarith only [hDtype]
  refine ⟨Dtype+Dtri,add_pos hDtype hDtri,?_⟩
  intro S F rshift sshift z r v Alen Z Q K₀ N _ d Wmax T M Jsep
    hf hlower hbound hdet hnegative hd hw hwcap hsmall hT hM hN hQ
    hJsep hNM hJM hwJ hy hz hgeometry hsep hshifts Φ f hlevel hden hinv
    μ₀ U₀ q μ ℓ b τ K x V w radius P h D δ lambda Hcurv q₀ p₀ color Cap
  classical
  have hMp : 0 < M := by linarith only [hM]
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδmax : δ < 1 := by
    dsimp only [δ]
    apply (div_lt_iff₀ (by positivity)).mpr
    linarith only [hL]
  have hlambda : 0 < lambda := by dsimp only [lambda]; positivity
  have hHcurv : 0 < Hcurv := by dsimp only [Hcurv]; positivity
  have hμ₀ : 0 < μ₀ := by dsimp only [μ₀]; positivity
  have hjet i (hi : i∈S) u (hu : u∈Icc (3/4:ℝ) (9/4)) :=
    double_difference_cubic_jet_bounds F hu (hy i hi)
      (hshifts i.1 (Finset.mem_image_of_mem Prod.fst hi)).1
      (hshifts i.1 (Finset.mem_image_of_mem Prod.fst hi)).2.1 hd hU hc
      (hshifts i.1 (Finset.mem_image_of_mem Prod.fst hi)).2.2.1
      (hshifts i.1 (Finset.mem_image_of_mem Prod.fst hi)).2.2.2
      hwcap hsmall hf hlower hbound
  have hphysical (n : ℕ) i (hi : i∈S) u (hu : 0 < u) :
      iteratedDeriv n (f i) u=T/M^n*iteratedDeriv n (Φ i.1) (u/M) := by
    have hreg := (hjet i hi 1 (by norm_num)).1
    have ha := sargos_iteratedDeriv_comp_affine_local (f:=Φ i.1)
      (l:=0) (r:=u+1) (c:=M⁻¹) (d:=0)
      (fun v hv => hreg _ (by
        simpa only [add_zero] using mul_pos (inv_pos.mpr hMp) hv.1))
      (show u∈Ioo (0:ℝ) (u+1) from ⟨hu,by linarith⟩) n
    change iteratedDeriv n (fun v => T*Φ i.1 (v/M)) u=_
    rw [iteratedDeriv_const_mul_field]
    have he : (fun v => Φ i.1 (v/M))=(fun v => Φ i.1 (M⁻¹*v+0)) := by
      funext v
      congr 1
      ring
    rw [he,ha]
    simp only [add_zero,inv_pow]
    rw [show M⁻¹*u=u/M by ring]
    ring
  have hcurv i (hi : i∈S) : lambda ≤ |h i| ∧ |h i| ≤ Hcurv := by
    have hzi := hz i hi
    have hpar := hy i hi
    have hx : z i/M∈Icc (3/4:ℝ) (9/4) := by
      constructor
      · apply (le_div_iff₀ hMp).mpr
        linarith only [hzi.1,hMp]
      · apply (div_le_iff₀ hMp).mpr
        linarith only [hzi.2,hMp]
    have hsdata := hshifts i.1 (Finset.mem_image_of_mem Prod.fst hi)
    have hprodpos : 0 < rshift i.1*sshift i.1 := by
      rw [hsdata.2.2.1]
      exact mul_pos hd (by linarith only [hpar.1])
    have hrp : 0 < rshift i.1 := by nlinarith only [hsdata.1,hsdata.2.1,hprodpos]
    have hsp : 0 < sshift i.1 := by nlinarith only [hsdata.1,hsdata.2.1,hprodpos]
    have hband := double_difference_exact_curvature_band F hx hpar hrp hsp hd hc hU
      hsdata.2.2.1 (hsdata.2.2.2.trans hwcap) hf hnegative
      (fun u hu => hbound u hu 4 (by norm_num) (by norm_num))
    have hband' : -2*U ≤ iteratedDeriv 2 (Φ i.1) (z i/M) ∧
        iteratedDeriv 2 (Φ i.1) (z i/M) ≤ -c := hband
    have hsign : iteratedDeriv 2 (Φ i.1) (z i/M) < 0 := by
      linarith only [hband'.2,hc]
    have he : |h i|=(T/M^2)*(-iteratedDeriv 2 (Φ i.1) (z i/M))/2 := by
      dsimp only [h]
      rw [hphysical 2 i hi _ (hMp.trans_le hzi.1),abs_div,abs_mul,
        abs_of_pos (div_pos hT (pow_pos hMp 2)),abs_of_neg hsign,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    rw [he]
    constructor
    · calc
        lambda = (T/M^2)*c/2 := by dsimp only [lambda]; ring
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith only [hband'.2]) (by positivity)) (by norm_num)
    · calc
        _ ≤ (T/M^2)*(2*U)/2 := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith only [hband'.1]) (by positivity)) (by norm_num)
        _ = Hcurv := by dsimp only [Hcurv]; ring
  have hμbounds i (hi : i∈S) : μ₀ ≤ μ i ∧ μ i ≤ U₀ := by
    have hr := abs_le.mp (abs_sub_round (z i))
    have hzi := hz i hi
    have hrpos : (0:ℝ) < round (z i) := by linarith only [hr.2,hzi.1,hM]
    have hx : (round (z i):ℝ)/M∈Icc (3/4:ℝ) (9/4) := by
      constructor
      · apply (le_div_iff₀ hMp).mpr
        linarith only [hr.2,hzi.1,hM]
      · apply (div_le_iff₀ hMp).mpr
        linarith only [hr.1,hzi.2,hM]
    have hj := hjet i hi _ hx
    have hlo : c/2 ≤ iteratedDeriv 3 (Φ i.1) ((round (z i):ℝ)/M) := hj.2.1
    have hhi : iteratedDeriv 3 (Φ i.1) ((round (z i):ℝ)/M) ≤ 3*U :=
      (abs_le.mp hj.2.2.1).2
    have he : μ i=(T/M^3)*iteratedDeriv 3 (Φ i.1) ((round (z i):ℝ)/M)/6 := by
      dsimp only [μ]
      rw [hphysical 3 i hi _ hrpos]
    rw [he]
    constructor
    · calc
        μ₀ = (T/M^3)*(c/2)/6 := by dsimp only [μ₀]; ring
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlo (by positivity)) (by norm_num)
    · calc
        _ ≤ (T/M^3)*(3*U)/6 := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hhi (by positivity)) (by norm_num)
        _ = U₀ := by dsimp only [U₀]; ring
  have hband := HuxleyRationalPhase.rational_narrow_band_twelfth_partition
    S r Q hQ hlambda hHcurv.le hδ
    (by
      intro i hi
      rw [←hlevel i hi]
      exact hcurv i hi) hden
  have hcap : (4/δ+3)*(4*Hcurv/(lambda*δ)+3)=Cap := by
    dsimp only [Hcurv,lambda,Cap]
    field_simp; ring
  simp only [hcap] at hband
  refine ⟨hband.1,hband.2.2,?_⟩
  obtain ⟨A,hA⟩ := HuxleyRationalPhase.source_arc_fourier_cloud_matrices
    S f z r v Q K₀ μ₀ U₀ hμ₀ hμbounds hlevel hden hinv
  have hclass : ∀ ij∈P, color ij.1.1=color ij.2.1 →
        let t := (A ij 2:ℝ)*h ij.1.1+A ij 3
        |t-1| ≤ δ ∧
        |((A ij 0:ℝ)*h ij.1.1+A ij 1)/h ij.1.1-1| ≤ δ ∧
        ((A ij 0=1 ∧ A ij 1=0 ∧ A ij 2=0 ∧ A ij 3=1) ∨
         (A ij 0=1 ∧ A ij 3=1 ∧ A ij 2=0 ∧ A ij 1≠0 ∧ |(A ij 1:ℝ)| ≤ δ*Hcurv) ∨
         (A ij 0=1 ∧ A ij 3=1 ∧ A ij 1=0 ∧ A ij 2≠0 ∧ |(A ij 2:ℝ)| ≤ δ/lambda) ∨
         (A ij 1≠0 ∧ A ij 2≠0)) ∧
        (|(A ij 2:ℝ)| * Hcurv ≤ L →
          A ij 0+A ij 3=2 ∧ (A ij 0-1)^2= -A ij 1*A ij 2) := by
    intro ij hij hcolor t
    have hpair := Finset.mem_product.mp (Finset.mem_filter.mp hij).1
    have hi : ij.1.1∈S := (Finset.mem_product.mp hpair.1).1
    have hj : ij.2.1∈S := (Finset.mem_product.mp hpair.2).1
    have hb := hband.2.1 _ hi _ hj hcolor
    have hp := hA ij hij
    have ht : t=(q ij.2.1:ℝ)/q ij.1.1 := hp.2.1
    have htpos : 0 < t := by
      have hh : (1:ℝ)/2 ≤ t := hp.2.2.1
      linarith only [hh]
    have hmap : ((A ij 0:ℝ)*h ij.1.1+A ij 1)/t=h ij.2.1 := hp.2.2.2.2.1
    have hcurvi := hcurv _ hi
    have hcurvj := hcurv _ hj
    have hx : h ij.1.1 ≠ 0 := abs_pos.mp (hlambda.trans_le hcurvi.1)
    have hri : h ij.1.1=(r ij.1.1:ℝ) := hlevel _ hi
    have hrj : h ij.2.1=(r ij.2.1:ℝ) := hlevel _ hj
    have hnumeq : ((A ij 0:ℝ)*h ij.1.1+A ij 1)/h ij.1.1=
        ((r ij.2.1).num:ℝ)/(r ij.1.1).num := by
      rw [(div_eq_iff htpos.ne').mp hmap,ht,hri,hrj]
      dsimp only [q]
      simp only [Rat.cast_def]
      field_simp
    have hden' : |t-1| ≤ δ := by simpa only [ht,q] using hb.1
    have hnum' : |((A ij 0:ℝ)*h ij.1.1+A ij 1)/h ij.1.1-1| ≤ δ := by
      simpa only [hnumeq] using hb.2
    refine ⟨hden',hnum',?_,?_⟩
    · exact HuxleyRationalPhase.narrow_band_matrix_translation_cases (A ij 0) (A ij 1) (A ij 2) (A ij 3)
        hlambda hcurvi.1 hcurvi.2 hδ.le hδmax hp.1 hden' hnum'
    · intro haction
      exact HuxleyRationalPhase.bounded_action_narrow_ratios_trace_two (A ij 0) (A ij 1) (A ij 2) (A ij 3)
        hp.1 hx hcurvi.2 hcurvj.2 haction hmap hden' hnum'
  refine ⟨A,hA,hclass,?_⟩
  intro E Δ
  have hΔ : 0 ≤ Δ := by dsimp only [Δ,U₀,μ₀, quarticTaylorSlack]; positivity
  have hpoints ij (hij : ij∈P) : ij.1.1∈S ∧ ij.2.1∈S := by
    have hh := Finset.mem_product.mp (Finset.mem_filter.mp hij).1
    exact ⟨(Finset.mem_product.mp hh.1).1,(Finset.mem_product.mp hh.2).1⟩
  constructor
  · have hmem ij (hij : ij∈E) :
        ij∈P ∧ color ij.1.1=color ij.2.1 ∧
          ((A ij 0=1 ∧ A ij 1=0 ∧ A ij 2=0 ∧ A ij 3=1) ∨
           (A ij 1≠0 ∧ A ij 2≠0 ∧ |(A ij 2:ℝ)| * Hcurv ≤ L)) := by
      exact Finset.mem_filter.mp hij
    have hh := hcount E A F rshift sshift (fun a k => z (a,k)) (fun a k => Alen (a,k))
      N Z d Wmax Δ Jsep T M hf hlower hbound hdet hnegative hd hw hwcap hsmall
      hT hM hN hΔ hJsep hNM hJM hwJ
      (by
        intro ij hij
        have hp := hpoints ij (hmem ij hij).1
        exact ⟨⟨hy _ hp.1,hz _ hp.1⟩,⟨hy _ hp.2,hz _ hp.2⟩⟩)
      (fun ij hij => hgeometry _ (hpoints ij (hmem ij hij).1).1)
      (fun ij hij => hgeometry _ (hpoints ij (hmem ij hij).1).2)
      (fun ij hij kl hkl hne =>
        hsep _ (hpoints ij (hmem ij hij).1).2 _ (hpoints kl (hmem kl hkl).1).2 hne)
      (by
        intro y hy'
        apply hshifts y
        rcases Finset.mem_union.mp hy' with hy' | hy'
        · obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hy'
          exact Finset.mem_image_of_mem Prod.fst (hpoints ij (hmem ij hij).1).1
        · obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hy'
          exact Finset.mem_image_of_mem Prod.fst (hpoints ij (hmem ij hij).1).2)
      (fun ij hij => (hA ij (hmem ij hij).1).1)
      (by
        intro ij hij
        rcases (hmem ij hij).2.2 with hb | hb
        · left
          rcases hb with ⟨h0,h1,h2,h3⟩
          funext j
          fin_cases j <;> simp [h0,h1,h2,h3]
        · exact Or.inr hb)
      (fun ij hij => (hA ij (hmem ij hij).1).2.2.2.2.1)
      (fun ij hij => (hclass ij (hmem ij hij).1 (hmem ij hij).2.1).1)
      (fun ij hij => (hclass ij (hmem ij hij).1 (hmem ij hij).2.1).2.1)
      (fun ij hij => (hA ij (hmem ij hij).1).2.2.2.2.2.2.1)
    have hsub : E.image (fun ij => ij.1.1.1) ⊆ S.image Prod.fst := by
      intro a ha
      obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image_of_mem Prod.fst (hpoints ij (hmem ij hij).1).1
    have hI : ((E.image (fun ij => ij.1.1.1)).card:ℝ) ≤ ((S.image Prod.fst).card:ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact hh.trans (by gcongr)
  · intro Etri
    have hmemtri ij (hij : ij∈Etri) :
        ij∈P ∧ color ij.1.1=color ij.2.1 ∧ (A ij 2=0 ∨ A ij 1=0) :=
      Finset.mem_filter.mp hij
    have hB : 0 ≤ δ*(Hcurv+1/lambda) := by positivity
    have hbupper : δ*Hcurv ≤ δ*(Hcurv+1/lambda) := by
      have hh : 0 ≤ δ/lambda := by positivity
      calc
        δ*Hcurv ≤ δ*Hcurv+δ/lambda := le_add_of_nonneg_right hh
        _ = _ := by ring
    have hblower : δ/lambda ≤ δ*(Hcurv+1/lambda) := by
      have hh : 0 ≤ δ*Hcurv := by positivity
      calc
        δ/lambda ≤ δ*Hcurv+δ/lambda := le_add_of_nonneg_left hh
        _ = _ := by ring
    have hbranches ij (hij : ij∈Etri) : A ij 0=1 ∧ A ij 3=1 ∧
        ((A ij 2=0 ∧ |(A ij 1:ℝ)| ≤ δ*(Hcurv+1/lambda)) ∨
         (A ij 1=0 ∧ |(A ij 2:ℝ)| ≤ δ*(Hcurv+1/lambda))) := by
      have hm := hmemtri ij hij
      have hc := (hclass ij hm.1 hm.2.1).2.2.1
      rcases hc with hi | hu | hl | hn
      · refine ⟨hi.1,hi.2.2.2,Or.inl ⟨hi.2.2.1,?_⟩⟩
        simpa only [hi.2.1,Int.cast_zero,abs_zero] using hB
      · exact ⟨hu.1,hu.2.1,Or.inl ⟨hu.2.2.1,hu.2.2.2.2.trans hbupper⟩⟩
      · exact ⟨hl.1,hl.2.1,Or.inr ⟨hl.2.2.1,hl.2.2.2.2.trans hblower⟩⟩
      · rcases hm.2.2 with he | he
        · exact False.elim (hn.2 he)
        · exact False.elim (hn.1 he)
    have hh := htri Etri A F rshift sshift (fun a k => z (a,k)) (fun a k => Alen (a,k))
      N Z d Wmax Δ Jsep T M (δ*(Hcurv+1/lambda)) hf hlower hbound hdet
      hd hw hwcap hsmall hT hM hN hΔ hJsep hNM hJM hwJ hB
      (by
        intro ij hij
        have hp := hpoints ij (hmemtri ij hij).1
        exact ⟨⟨hy _ hp.1,hz _ hp.1⟩,⟨hy _ hp.2,hz _ hp.2⟩⟩)
      (fun ij hij => hgeometry _ (hpoints ij (hmemtri ij hij).1).1)
      (fun ij hij => hgeometry _ (hpoints ij (hmemtri ij hij).1).2)
      (fun ij hij kl hkl hne =>
        hsep _ (hpoints ij (hmemtri ij hij).1).2 _ (hpoints kl (hmemtri kl hkl).1).2 hne)
      (by
        intro y hy'
        apply hshifts y
        rcases Finset.mem_union.mp hy' with hy' | hy'
        · obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hy'
          exact Finset.mem_image_of_mem Prod.fst (hpoints ij (hmemtri ij hij).1).1
        · obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hy'
          exact Finset.mem_image_of_mem Prod.fst (hpoints ij (hmemtri ij hij).1).2)
      hbranches
      (fun ij hij => ⟨(hA ij (hmemtri ij hij).1).2.2.1,(hA ij (hmemtri ij hij).1).2.2.2.1⟩)
      (fun ij hij => (hA ij (hmemtri ij hij).1).2.2.2.2.1)
      (fun ij hij => (hA ij (hmemtri ij hij).1).2.2.2.2.2.2.1)
    have hsub : Etri.image (fun ij => ij.1.1.1) ⊆ S.image Prod.fst := by
      intro a ha
      obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image_of_mem Prod.fst (hpoints ij (hmemtri ij hij).1).1
    have hI : ((Etri.image (fun ij => ij.1.1.1)).card:ℝ) ≤ ((S.image Prod.fst).card:ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hfactor : 0 ≤ 1+δ*(Hcurv+1/lambda) := by positivity
    have hconst := mul_le_mul_of_nonneg_right hDtrismall hfactor
    have hprod := mul_le_mul hconst hI (Nat.cast_nonneg _) (by positivity)
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hprod (div_nonneg hMp.le (Nat.cast_nonneg _))) (by positivity))

private theorem clamped_narrowing_source_costs
    {H N Q C a b Uref : ℝ}
    (hH : 0 < H) (hHcap : H ≤ 1) (hN : 0 < N) (hQ : 0 < Q)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hU : 0 < Uref) :
    let V := max 1 (H*N/Q)
    1 ≤ V ∧
      V*(1+C*(H+1/H)) ≤ (1+2*C)*(1/H+N/Q) ∧
      V*(a/V^((5:ℝ)/3)+b/(Uref*V)) ≤
        a*(Q/(H*N))^((2:ℝ)/3)+b/Uref := by
  intro V
  have hprod : 0 < H*N/Q := by positivity
  have hVone : 1 ≤ V := le_max_left _ _
  have hVprod : H*N/Q ≤ V := le_max_right _ _
  have hVp : 0 < V := zero_lt_one.trans_le hVone
  have hVupper : V ≤ 1+H*N/Q :=
    max_le (by linarith only [hprod]) (by linarith)
  have hInv : 1 ≤ 1/H := (le_div_iff₀ hH).mpr (by simpa only [one_mul] using hHcap)
  have hFactor : 1+C*(H+1/H) ≤ (1+2*C)/H := by
    have hh := mul_le_mul_of_nonneg_left (hHcap.trans hInv) hC
    calc
      _ ≤ 1+C*(1/H+1/H) := by linarith only [hh]
      _ ≤ 1/H+C*(1/H+1/H) := by linarith only [hInv]
      _ = _ := by ring
  refine ⟨hVone,?_,?_⟩
  · calc
      _ ≤ (1+H*N/Q)*((1+2*C)/H) :=
        mul_le_mul hVupper hFactor (by positivity) (by positivity)
      _ = _ := by field_simp
  · have he : V^((5:ℝ)/3)=V*V^((2:ℝ)/3) := by
      rw [show (5:ℝ)/3=1+2/3 by norm_num,Real.rpow_add hVp,Real.rpow_one]
    have hc : a/V^((2:ℝ)/3) ≤ a*(Q/(H*N))^((2:ℝ)/3) := by
      calc
        _ ≤ a/(H*N/Q)^((2:ℝ)/3) :=
          div_le_div_of_nonneg_left ha (Real.rpow_pos_of_pos hprod _)
            (Real.rpow_le_rpow hprod.le hVprod (by norm_num))
        _ = _ := by
          rw [div_eq_mul_inv,←Real.inv_rpow hprod.le,inv_div]
    calc
      _ = a/V^((2:ℝ)/3)+b/Uref := by rw [he]; field_simp
      _ ≤ _ := add_le_add hc le_rfl

private theorem source_reference_seed_height_polynomial_window
    {σ J Jv T M R Q U V e r v s : ℝ}
    (hσ : 0 < σ) (hJ : 0 ≤ J) (hJv : 0 ≤ Jv)
    (hT1 : 1 ≤ T) (hM1 : 1 ≤ M) (hQ₀ : 0 ≤ Q)
    (hQT : Q ≤ T) (hRT : R^2 ≤ T)
    (hU : 1 ≤ U)
    (hV₀ : 0 ≤ V) (hV : V ≤ Jv*T/(2*M^2))
    (hr : |r| ≤ 4*R^2/U) (hs : |s| ≤ 4*R^2/U)
    (he : |e| ≤ (3*J*T/(2*σ*M^2)+1)*(4*R^2/U))
    (hv : |v| ≤ (3*J*T/(2*σ*M^2)+1)*(4*R^2/U)) :
    let C := 1+4*(3*J/(2*σ)+1+Jv/2)
    1 ≤ C ∧ 1+(|v|+|s| *V)*Q ≤ C*T^3 ∧
      1+(|r| *V+|e|)*Q ≤ C*T^3 := by
  intro C
  have hT : 0 < T := zero_lt_one.trans_le hT1
  have hM₂ : 1 ≤ M^2 := one_le_pow₀ hM1
  have hK : 4*R^2/U ≤ 4*T :=
    (div_le_self (by positivity) hU).trans (mul_le_mul_of_nonneg_left hRT (by norm_num))
  let c := 3*J/(2*σ)
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hcurv : 3*J*T/(2*σ*M^2) ≤ c*T := by
    calc
      _ = c*T/M^2 := by dsimp only [c]; ring
      _ ≤ c*T := div_le_self (mul_nonneg hc hT.le) hM₂
  have hV' : V ≤ (Jv/2)*T := hV.trans (by
    calc
      Jv*T/(2*M^2) = ((Jv/2)*T)/M^2 := by ring
      _ ≤ (Jv/2)*T := div_le_self (by positivity) hM₂)
  have hlabel {z : ℝ}
      (hz : |z| ≤ (3*J*T/(2*σ*M^2)+1)*(4*R^2/U)) :
      |z| ≤ 4*(c+1)*T^2 := by
    have htop : 3*J*T/(2*σ*M^2)+1 ≤ (c+1)*T := by nlinarith only [hcurv,hT1]
    apply hz.trans
    calc
      _ ≤ ((c+1)*T)*(4*T) :=
        mul_le_mul htop hK (by positivity) (by positivity)
      _ = _ := by ring
  have hr' : |r| ≤ 4*T := hr.trans hK
  have hs' : |s| ≤ 4*T := hs.trans hK
  have he' := hlabel he
  have hv' := hlabel hv
  have hvV : |s| *V ≤ 2*Jv*T^2 := by
    calc
      _ ≤ (4*T)*((Jv/2)*T) := mul_le_mul hs' hV' hV₀ (by positivity)
      _ = _ := by ring
  have hrV : |r| *V ≤ 2*Jv*T^2 := by
    calc
      _ ≤ (4*T)*((Jv/2)*T) := mul_le_mul hr' hV' hV₀ (by positivity)
      _ = _ := by ring
  have hC : 1 ≤ C := by
    change 1 ≤ 1+4*(c+1+Jv/2)
    exact le_add_of_nonneg_right (by positivity)
  have hpow : 1 ≤ T^3 := one_le_pow₀ hT1
  refine ⟨hC,?_,?_⟩
  · have hsum : |v|+|s| *V ≤ (4*(c+1)+2*Jv)*T^2 := by linarith only [hv',hvV]
    have hh := mul_le_mul hsum hQT hQ₀ (by positivity : 0 ≤ (4*(c+1)+2*Jv)*T^2)
    change 1+(|v|+|s| *V)*Q ≤ (1+4*(c+1+Jv/2))*T^3
    nlinarith only [hh,hpow]
  · have hsum : |r| *V+|e| ≤ (4*(c+1)+2*Jv)*T^2 := by linarith only [he',hrV]
    have hh := mul_le_mul hsum hQT hQ₀ (by positivity : 0 ≤ (4*(c+1)+2*Jv)*T^2)
    change 1+(|r| *V+|e|)*Q ≤ (1+4*(c+1+Jv/2))*T^3
    nlinarith only [hh,hpow]

private theorem eventually_physical_reference_chart_budgets_window
    {σ Jref εloss : ℝ} (hσ : 0 < σ) (hJref : 0 ≤ Jref) (hεloss : 0 < εloss) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀
    (Gaps : Finset (ℝ × ℝ)) (e r v s : ℝ × ℝ → ℤ) (Q Uref : ℕ)
    {δ M R : ℝ},
    0 ≤ δ → δ ≤ 1 → 1 ≤ M → 1 ≤ R →
    (Q:ℝ) ≤ T → R^2 ≤ T →
    1 ≤ Uref → (Uref:ℝ) ≤ R^2 →
    WithReferenceCoefficientBounds Gaps e r v s Uref Jref T σ M R (
    (∀ ab∈Gaps, ab.1 < ab.2 ∧ ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun ab => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun ab => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let εchart := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    ∃ Bmajor Cmajor : ℕ,
      (∀ ab∈Gaps, 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1) ≤ Bmajor) ∧
      (∀ ab∈Gaps, ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*εchart))⌋₊+1 ≤ Cmajor) ∧
      ((6+Cmajor*(105+544*Bmajor):ℕ):ℝ) ≤ T^εloss) := by
  let Jv := modelPhaseJetCoefficient σ 1+1
  let Ch := 1+4*(3*Jref/(2*σ)+1+Jv/2)
  let κ := modelPhaseThirdLower σ
  let Cp := σ*(σ+1)+1
  let Cc := 1+((14:ℝ)/3)*(Cp+2)/κ
  have hJv : 0 ≤ Jv := add_nonneg (modelPhaseJetCoefficient_nonneg σ 1) zero_le_one
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCp : 0 < Cp+2 := by dsimp only [Cp]; positivity
  have hCh : 1 ≤ Ch := by dsimp only [Ch]; exact le_add_of_nonneg_right (by positivity)
  have hCc : 1 ≤ Cc := by dsimp only [Cc]; exact le_add_of_nonneg_right (by positivity)
  filter_upwards [nativeHuxleyReference_eventually_reference_chart_majorants hCh hCc hεloss,
    Filter.eventually_ge_atTop (1:ℝ)] with T hmajor hT1
  intro Gaps e r v s Q Uref δ M R hδ₀ hδmax hM1 hR hQT hRT
    hU hUR hr hs he hv hgap Vheight P₁ P₂ εchart
  have hT : 0 < T := zero_lt_one.trans_le hT1
  let Bmajor := 6+216*(⌊Real.logb 2 ((Ch*T^3)^2)⌋₊+1)
  let Cmajor := ⌊Real.logb (5/4) (Cc*T)⌋₊+1
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hUr : (1:ℝ) ≤ Uref := by exact_mod_cast hU
  have hV₀ : 0 ≤ Vheight := div_nonneg
    (mul_nonneg hT.le (add_nonneg (modelPhaseJetCoefficient_nonneg σ 1) hδ₀)) (by positivity)
  have hVmax : Vheight ≤ Jv*T/(2*M^2) := by
    dsimp only [Vheight,Jv]
    rw [mul_comm (modelPhaseJetCoefficient σ 1+1) T]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hδmax) hT.le) (by positivity)
  have hheight ab (hab : ab∈Gaps) :=
    source_reference_seed_height_polynomial_window hσ hJref hJv hT1 hM1
      (Nat.cast_nonneg Q) hQT hRT hUr hV₀ hVmax
      (hr ab hab) (hs ab hab) (he ab hab) (hv ab hab)
  have hP₁ ab : 1 ≤ P₁ ab := le_add_of_nonneg_right
    (mul_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) hV₀)) (Nat.cast_nonneg Q))
  have hP₂ ab : 1 ≤ P₂ ab := le_add_of_nonneg_right
    (mul_nonneg (add_nonneg (mul_nonneg (abs_nonneg _) hV₀) (abs_nonneg _)) (Nat.cast_nonneg Q))
  refine ⟨Bmajor,Cmajor,?_,?_,hmajor⟩
  · intro ab hab
    apply Nat.add_le_add_left
    apply Nat.mul_le_mul_left
    apply Nat.add_le_add_right
    apply Nat.floor_mono
    apply Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
      (mul_pos (zero_lt_one.trans_le (hP₁ ab)) (zero_lt_one.trans_le (hP₂ ab)))
    calc
      P₁ ab*P₂ ab ≤ (Ch*T^3)*(Ch*T^3) :=
        mul_le_mul (hheight ab hab).2.1 (hheight ab hab).2.2
          (zero_le_one.trans (hP₂ ab)) (by positivity)
      _ = _ := by ring
  · intro ab hab
    have hε : 0 < εchart := by change 0 < κ/(16*(Cp+2)*R^2); positivity
    have hratio := nativeHuxleyReference_physical_reference_chart_ratio hκ hCp hRp (hgap ab hab).2
    have hratio' : (ab.2-ab.1)/(12*εchart) ≤ Cc*T := by
      apply hratio.trans
      calc
        ((14:ℝ)/3)*(Cp+2)/κ*(Uref:ℝ) ≤ ((14:ℝ)/3)*(Cp+2)/κ*T :=
          mul_le_mul_of_nonneg_left (hUR.trans hRT) (by positivity)
        _ ≤ Cc*T := mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left zero_le_one) hT.le
    apply Nat.add_le_add_right
    apply Nat.floor_mono
    exact Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<5/4)
      (div_pos (sub_pos.mpr (hgap ab hab).1) (by positivity)) hratio'

private theorem eventually_physicalModelPhase_actual_fourier_original_pair_mass_raw
    {σ Jref εloss : ℝ} (hσ : 0 < σ) (hJref : 0 ≤ Jref) (hεloss : 0 < εloss) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2))) (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ)
    (Q K₀ : ℕ) [NeZero K₀]
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ)
    (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2)
    (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {δ M R base Bcut lambda Uband θ V : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℝ},
    (∀ ij∈P, base ≤ za ij.1.1) →
    (∀ ij∈P, x ij 0=za ij.1.1) →
    (∀ ij∈P, x ij 1=zb ij.2.1) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ)) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < (N:ℝ)) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*(N:ℝ)*R^2=M^3) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ ij∈P, ∀ i, x ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, (rat ij i).den ≤ Q ∧ Q ≤ 2*(rat ij i).den) →
    (0 < lambda) →
    (0 ≤ Uband) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ij∈P, ∀ i, lambda ≤ |(rat ij i:ℝ)| ∧ |(rat ij i:ℝ)| ≤ Uband) →
    (∀ ij∈P, ∀ i, ((rat ij i).den:ℤ) ∣ (rat ij i).num*vinv ij i-1) →
    WithReferenceBasis Gaps Refs e r v s Uref R Bcut (
    (∀ ij∈P, ∀ i, x ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, x ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    WithReferenceScale Gaps r Uref Q (modelPhaseThirdLower σ) Bcut Bselect M (N:ℝ) R (
    (∀ ij∈P, (rat ij 0:ℝ)∈Icc (gap ij).1 (gap ij).2) →
    (∀ ij∈P, Mat ij 2 ≠ 0) →
    (∀ ij∈P, 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat ij 2:ℝ)| *(modelPhaseThirdLower σ)^2*T) →
    (∀ ij∈P, 8*Uband ≤ |(Mat ij 2:ℝ)| *lambda^2) →
    (1 ≤ V) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) → (Uref:ℝ) ≤ R^2 →
    WithReferenceCoefficientBounds Gaps e r v s Uref Jref T σ M R (
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let sourceColor := fun ij i => rationalSourceBin Q lambda θ (rat ij i)
    (∀ ij∈P, sourceColor ij 0=sourceColor ij 1) →
    WithRoundedSourceJets P F (fun i => (A i:ℝ)) T M x rat (fun f q mu ell =>
    WithCompletionCloud P q mu ell parity vinv K₀ (fun b cround tau dual cloud radius =>
    (∀ ij∈P,
      |cloud ij 0 1-cloud ij 1 1| ≤ 1/(6*(K₀:ℝ)^2*V)) →
    WithCubicScales σ M (N:ℝ) R Q (fun κ Cphys c J B =>
    (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
    (∀ ij∈P, (Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat ij 0:ℝ)*(rat ij 0:ℝ)+Mat ij 1)/
      ((Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3)=(rat ij 1:ℝ)) →
    (∀ ij∈P, |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    WithCompletionMargins P x (fun i => (W i:ℝ)) (N:ℝ) Cphys (fun H =>
    WithRationalAnchors P rat anchor ε Q (
    let budget := QuarticChartBudget.make σ δ κ Cphys B
    let Δ := budget.delta Q N
    let Ccurv := budget.Ccurv
    let D := budget.error Q N
    let Esize := budget.Esize
    let Dbase := budget.Dbase
    let Tbase := budget.Tbase
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Cmain := budget.Cmain
    let Ctail := budget.Ctail
    (P.card:ℝ) ≤
      (60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
        (Cmain/V^((5:ℝ)/3)+Ctail/((Uref:ℝ)*V)))*T^εloss)))))))) := by
  filter_upwards [nativeHuxleyReference_eventually_physical_reference_chart_budgets hσ hJref hεloss,
    eventually_physical_reference_chart_budgets_window hσ hJref hεloss] with T hbudgets hbudgetsWindow
  unfold WithRoundedSourceJets WithCompletionCloud WithCubicScales WithCompletionMargins
  intro Uref Refs Gaps Bselect P Mat gap Q K₀ _ N za zb AlenA AlenB Za Zb
    rat vinv parity anchor e r v s δ M R base Bcut lambda Uband θ V F A W x
    hbase hxa hxb hgapMem hgeometryA hgeometryB hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hc hlarge haction hV hgap
    hQN hNM hUR hrHeight hsHeight heHeight hvHeight
    ε sourceColor hsourceColor f hlevel q mu ell b cround tau dual cloud radius
    hcolor hnear hnearNarrow κ Cphys c J B hsmall hNR hRN hNcube hminscale
    hMatdet hMatt hMatmap hMatgamma H hNtwo hL hU hanchor hcut hcount
    budget Δ Ccurv D Esize Dbase Tbase hsize hD hΔ hBsize
    Cmain Ctail
  have hδ₀ := approximateModelPhase_tolerance_nonneg (hF 0)
  obtain ⟨Bmajor,Cmajor,hBmajor,hCmajor,hcost⟩ := hNM.elim
    (fun hNtwoM => hbudgets
      Gaps e r v s Q Uref hδ₀ (hδ.trans (min_le_right _ _)) hT hM hR hRQ hQN
      hNtwoM hUref hUR hscale hrHeight hsHeight heHeight hvHeight
      (fun ab hab => ⟨(hgap ab hab).2.2.1,hgapWidth ab hab⟩))
    (fun hwindow => hbudgetsWindow
      Gaps e r v s Q Uref hδ₀ (hδ.trans (min_le_right _ _)) hwindow.1 hR
      (hQN.trans hwindow.2.1) hwindow.2.2 hUref hUR
      hrHeight hsHeight heHeight hvHeight
      (fun ab hab => ⟨(hgap ab hab).2.2.1,hgapWidth ab hab⟩))
  have hh := physicalModelPhase_actual_fourier_original_pair_mass Uref Refs Gaps (Bselect:=Bselect) P Mat gap Bmajor Cmajor Q K₀ N za zb AlenA AlenB Za Zb rat vinv parity anchor e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (R:=R) (base:=base) (Bcut:=Bcut) (lambda:=lambda) (Uband:=Uband) (θ:=θ) (V:=V) (F:=F) (A:=A) (W:=W) (x:=x) hbase hxa hxb hgapMem hgeometryA hgeometryB hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hc hlarge haction hV hgap
    hsourceColor hlevel hcolor hnear hnearNarrow hsmall hNR hRN hNcube hminscale
    hMatdet hMatt hMatmap hMatgamma hNtwo hL hU hanchor hcut hcount
    hsize hD hΔ hBsize hBmajor hCmajor
  have hmass := hh.2.1
  let m0 := 6+Cmajor*(105+544*Bmajor)
  let Kbase := 60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
    (Cmain/V^((5:ℝ)/3)+Ctail/((Uref:ℝ)*V))
  have hmass' : (P.card:ℝ) ≤ (m0:ℝ)*Kbase := by
    convert hmass using 1
    dsimp only [m0,Kbase]
    ring
  have hmpos : (0:ℝ) < m0 := by dsimp only [m0]; positivity
  have hknon : 0 ≤ Kbase := by
    have hnon : 0 ≤ (m0:ℝ)*Kbase :=
      (Nat.cast_nonneg P.card).trans hmass'
    nlinarith only [hnon,hmpos]
  exact hmass'.trans (by
    calc
      (m0:ℝ)*Kbase ≤ T^εloss*Kbase := mul_le_mul_of_nonneg_right hcost hknon
      _ = Kbase*T^εloss := mul_comm _ _)

private theorem double_difference_actual_joint_narrowed_sieve
    {c U L εloss : ℝ} (hc : 0 < c) (hU : 0 < U) (hL : 0 ≤ L) (hεloss : 0 < εloss) :
    ∃ Dtype C : ℝ, 0 < Dtype ∧ 0 < C ∧
    ∀ (S : Finset (ℝ × ℤ)) (F rshift sshift : ℝ → ℝ)
      (z : (ℝ × ℤ) → ℝ) (r : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ)
      (Alen : (ℝ × ℤ) → ℕ) (Z : ℝ → ℤ)
      (Q K₀ N : ℕ) [NeZero K₀] (d Wmax T M Jsep : ℝ)
      (Nlen : (ℝ × ℤ) → ℕ) (Vscale Rphys : ℝ),
    (∀ u, 0 < u → ContDiffAt ℝ ∞ F u) →
    (∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 F u) →
    (∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n F u| ≤ U) →
    (∀ u∈Icc (1/2:ℝ) 3,
      c ≤ |(iteratedDeriv 5 F u)^2-iteratedDeriv 4 F u*iteratedDeriv 6 F u|) →
    (∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c) →
    0 < d → 0 ≤ Wmax → Wmax ≤ 1/4 → 2*U*Wmax ≤ c/64 →
    0 < T → 2 ≤ M → 0 < N → 0 < Q →
    0 < Jsep → (N:ℝ) ≤ M → Jsep ≤ M → Wmax*Jsep ≤ 1 →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Icc M (2*M)) →
    (∀ i∈S, N ≤ Alen i ∧ Alen i ≤ 3*N ∧
      round (z i)+(Alen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    (∀ y∈S.image Prod.fst,
      0 ≤ rshift y ∧ 0 ≤ sshift y ∧ rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
    let Φ := fun y u =>
      (F u-F (u+rshift y)-F (u+sshift y)+F (u+rshift y+sshift y))/d
    let f := fun i : ℝ × ℤ => fun u => T*Φ i.1 (u/M)
    (∀ i∈S, iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) →
    (∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den) →
    (∀ i∈S, ((r i).den:ℤ) ∣ (r i).num*v i-1) →
    let μ₀ := c*T/(12*M^3)
    let U₀ := U*T/(2*M^3)
    let q := fun i => (r i).den
    let μ := fun i => iteratedDeriv 3 (f i) (round (z i))/6
    1 ≤ Vscale → (Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*Rphys^2 →
    (∀ i∈S, 1 ≤ Nlen i ∧ q i ≤ Nlen i ∧ 1 ≤ μ i*(q i:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*(μ i*(q i:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →
    let ℓ := fun i => deriv (f i) (round (z i))
    let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
    let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
    let K := fun i => cubicDualPhase (μ i) (q i)
    let x := fun i p => cubicCoordinates (v i) (b i p) (q i) (K i) (τ i p)
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let w := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![Int.fract (x ip.1 ip.2 0),Int.fract (x ip.1 ip.2 1),
        x ip.1 ip.2 2/Real.sqrt K₀,x ip.1 ip.2 3/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let P := (V ×ˢ V).filter (fun ij => ∀ d, |w ij.1 d-w ij.2 d| ≤ 2*radius d)
    let h := fun i => iteratedDeriv 2 (f i) (z i)/2
    let D := (Real.sqrt K₀/(9*(K₀:ℝ))+Real.sqrt K₀/(12*(K₀:ℝ)^2))*
      Real.sqrt (U₀*(Q:ℝ)^3)
    let δ := 1/(8*(L+3))
    let lambda := c*T/(2*M^2)
    let Hcurv := U*T/M^2
    let q₀ := (Q:ℝ)/2
    let p₀ := lambda*(Q:ℝ)/2
    let color := fun i => (⌊((r i).den:ℝ)/(δ*q₀)⌋,⌊((r i).num:ℝ)/(δ*p₀)⌋)
    let Cap := (4/δ+3)*(8*U/(c*δ)+3)
    let offset := fun ip : (ℝ × ℤ) × Fin 2 => b ip.1 ip.2-round ((q ip.1:ℝ)*ℓ ip.1)
    let joint := fun ip : (ℝ × ℤ) × Fin 2 => (color ip.1,offset ip)
    let narrowRadius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2*Vscale),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let Fiber := fun key => V.filter (fun ip => joint ip=key)
    let Pairs := fun key => ((Fiber key) ×ˢ (Fiber key)).filter
      (fun ij => ∀ a, |w ij.1 a-w ij.2 a| ≤ 2*narrowRadius a)
    let Pall := (V ×ˢ V).filter
      (fun ij => ∀ a, |w ij.1 a-w ij.2 a| ≤ 2*narrowRadius a)
    ((S.image color).card:ℝ) ≤ Cap ∧
    (∀ coeff : (ℝ × ℤ) → ℂ, ‖∑ i∈S,coeff i‖^12 ≤ Cap^11*
      ∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),coeff i‖^12) ∧
    ∃ A : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ,
      (∀ ij∈P,
        A ij 0*A ij 3-A ij 1*A ij 2=1 ∧
        let t := (A ij 2:ℝ)*h ij.1.1+A ij 3
        t=(q ij.2.1:ℝ)/q ij.1.1 ∧ (1:ℝ)/2 ≤ t ∧ t ≤ 2 ∧
        ((A ij 0:ℝ)*h ij.1.1+A ij 1)/t=h ij.2.1 ∧
        |(A ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) ∧
        |μ ij.2.1/μ ij.1.1*t^3-1| ≤
          (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2) ∧
        |τ ij.1.1 ij.1.2-τ ij.2.1 ij.2.2| ≤ D ∧
        (∃ e₁ e₂ : ℤ,
          let F₁ := 2*(round (z ij.2.1):ℝ)-2*(A ij 3:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 2:ℝ)*ℓ ij.1.1
          let F₂ := ℓ ij.2.1-2*(A ij 1:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 0:ℝ)*ℓ ij.1.1
          |F₁-e₁| ≤ (q ij.2.1:ℝ)/(6*(K₀:ℝ))+|(A ij 2:ℝ)|/q ij.1.1 ∧
          |(F₂-e₂)-h ij.2.1*(F₁-e₁)| ≤ 2*D/q ij.2.1) ∧
        ((Q:ℝ)^2/(6*(K₀:ℝ)^2) < 1 →
          A ij 2=0 ∧ q ij.1.1=q ij.2.1 ∧
            (q ij.1.1:ℤ) ∣ (r ij.2.1).num-(r ij.1.1).num)) ∧
      (∀ ij∈P, color ij.1.1=color ij.2.1 →
        let t := (A ij 2:ℝ)*h ij.1.1+A ij 3
        |t-1| ≤ δ ∧
        |((A ij 0:ℝ)*h ij.1.1+A ij 1)/h ij.1.1-1| ≤ δ ∧
        ((A ij 0=1 ∧ A ij 1=0 ∧ A ij 2=0 ∧ A ij 3=1) ∨
         (A ij 0=1 ∧ A ij 3=1 ∧ A ij 2=0 ∧ A ij 1≠0 ∧ |(A ij 1:ℝ)| ≤ δ*Hcurv) ∨
         (A ij 0=1 ∧ A ij 3=1 ∧ A ij 1=0 ∧ A ij 2≠0 ∧ |(A ij 2:ℝ)| ≤ δ/lambda) ∨
         (A ij 1≠0 ∧ A ij 2≠0)) ∧
        (|(A ij 2:ℝ)| * Hcurv ≤ L →
          A ij 0+A ij 3=2 ∧ (A ij 0-1)^2= -A ij 1*A ij 2)) ∧
      let E := P.filter (fun ij =>
        color ij.1.1=color ij.2.1 ∧
        ((A ij 0=1 ∧ A ij 1=0 ∧ A ij 2=0 ∧ A ij 3=1) ∨
         (A ij 1≠0 ∧ A ij 2≠0 ∧ |(A ij 2:ℝ)| * Hcurv ≤ L)))
      let Δ := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
      (E.card:ℝ) ≤ Dtype*((S.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δ*Jsep) ∧
      let Etri := P.filter (fun ij =>
        color ij.1.1=color ij.2.1 ∧ (A ij 2=0 ∨ A ij 1=0))
      (Etri.card:ℝ) ≤ Dtype*(1+δ*(Hcurv+1/lambda))*
        ((S.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δ*Jsep) ∧
      ((V.image joint).card:ℝ) ≤ 3*Cap ∧
      (∀ k : ZMod K₀,
        (∑ ip∈V, ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
          GafniTao.fordAdditiveCharacter (∑ a,x ip.1 ip.2 a*
            (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
              Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) a)‖)^12 ≤
          C*Vscale*(K₀:ℝ)^((12:ℝ)+εloss)*(3*Cap)^11*
            ∑ key∈V.image joint,((Fiber key).card:ℝ)^10*((Pairs key).card:ℝ)) ∧
      (∀ ij∈Pall, |(A ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2*Vscale) ∧
        |(A ij 2:ℝ)| ≤ Rphys^4/(6*(N:ℝ)^2*Vscale)) := by
  classical
  obtain ⟨Dtype,hDtype,hsource⟩ :=
    double_difference_colored_fourier_cloud_type_one_and_triangular hc hU hL
  obtain ⟨C,hC,hcolored⟩ := huxley_completed_colored_source_sieve.{0} hεloss
  refine ⟨Dtype,C,hDtype,hC,?_⟩
  intro S F rshift sshift z r v Alen Z Q K₀ N instK d Wmax T M Jsep Nlen Vscale Rphys
    hf hlower hbound hdet hnegative hd hw hwcap hsmall hT hM hN hQ
    hJsep hNM hJM hwJ hy hz hgeometry hsep hshifts Φ f hlevel hden hinv
    μ₀ U₀ q μ hVscale hmesh hminor hcomplete
    ℓ b τ K x V w radius P h D δ lambda Hcurv q₀ p₀ color Cap
    offset joint narrowRadius Fiber Pairs Pall
  obtain ⟨hcard,hholder,A,hA,hclass,hTypeI,htri⟩ :=
    hsource S F rshift sshift z r v Alen Z Q K₀ N d Wmax T M Jsep
      hf hlower hbound hdet hnegative hd hw hwcap hsmall hT hM hN hQ
      hJsep hNM hJM hwJ hy hz hgeometry hsep hshifts hlevel hden hinv
  have hoffset : ((V.image offset).card:ℝ) ≤ 3 := by
    exact_mod_cast (fourier_parity_round_partition S (fun i => (q i:ℝ)*ℓ i)).2.1
  have hjointSub : V.image joint ⊆ (S.image color) ×ˢ (V.image offset) := by
    intro key hkey
    obtain ⟨ip,hip,rfl⟩ := Finset.mem_image.mp hkey
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem color (Finset.mem_product.mp hip).1,
        Finset.mem_image_of_mem offset hip⟩
  have hjoint : ((V.image joint).card:ℝ) ≤ 3*Cap := by
    have hh : ((V.image joint).card:ℝ) ≤
        ((S.image color).card:ℝ)*((V.image offset).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hjointSub).trans_eq (Finset.card_product _ _)
    have hcap : 0 ≤ Cap := (Nat.cast_nonneg _).trans hcard
    exact hh.trans ((mul_le_mul hcard hoffset (Nat.cast_nonneg _) hcap).trans_eq (mul_comm _ _))
  have hbox ip (hip : ip∈V) :
      |x ip.1 ip.2 2| ≤ Real.sqrt K₀ ∧ |x ip.1 ip.2 3| ≤ Real.sqrt K₀ := by
    have hi := (Finset.mem_product.mp hip).1
    have hqr : (0:ℝ) < q ip.1 := Nat.cast_pos.mpr (r ip.1).pos
    have hnr : (0:ℝ) < Nlen ip.1 := by exact_mod_cast (hminor ip.1 hi).1
    have hμ : 0 < μ ip.1 :=
      (mul_pos_iff_of_pos_right (sq_pos_of_pos hqr)).mp
        ((mul_pos_iff_of_pos_right hnr).mp (zero_lt_one.trans_le (hminor ip.1 hi).2.2))
    exact bourgain_actual_dual_source_box (r ip.1).pos
      (hminor ip.1 hi).1 (hminor ip.1 hi).2.1 hμ (hminor ip.1 hi).2.2
      (hcomplete ip.1 hi) (v ip.1) ip.2
  have hKone : (1:ℝ) ≤ K₀ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K₀)
  have hNphys : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hrad : ∀ a, narrowRadius a ≤ radius a := by
    intro a
    fin_cases a
    · exact le_rfl
    · change 1/(12*(K₀:ℝ)^2*Vscale) ≤ 1/(12*(K₀:ℝ)^2)
      apply one_div_le_one_div_of_le (by positivity)
      exact le_mul_of_one_le_right (by positivity) hVscale
    · exact le_rfl
    · exact le_rfl
  have hsub : Pall ⊆ P := by
    intro ij hij
    have hh := Finset.mem_filter.mp hij
    exact Finset.mem_filter.mpr ⟨hh.1,fun a =>
      (hh.2 a).trans (mul_le_mul_of_nonneg_left (hrad a) (by norm_num))⟩
  refine ⟨hcard,hholder,A,hA,hclass,hTypeI,htri,hjoint,?_,?_⟩
  · intro k
    exact hcolored K₀ Vscale hVscale ((ℝ × ℤ) × Fin 2) V
      (fun ip => x ip.1 ip.2) joint (3*Cap) hbox hjoint k
  · intro ij hij
    have hp := Finset.mem_filter.mp hij
    have hi := (Finset.mem_product.mp (Finset.mem_product.mp hp.1).1).1
    have hj := (Finset.mem_product.mp (Finset.mem_product.mp hp.1).2).1
    let pr : Fin 2 → ℚ := ![r ij.1.1,r ij.2.1]
    let qi : Fin 2 → ℤ := ![(q ij.1.1:ℤ),(q ij.2.1:ℤ)]
    let ei : Fin 2 → ℤ := ![(r ij.1.1).num,(r ij.2.1).num]
    let vi : Fin 2 → ℤ := ![v ij.1.1,v ij.2.1]
    have hcast a : (ei a:ℝ)/qi a=(pr a:ℝ) := by
      fin_cases a
      · change ((r ij.1.1).num:ℝ)/(r ij.1.1).den=(r ij.1.1:ℝ)
        exact (Rat.cast_def _).symm
      · change ((r ij.2.1).num:ℝ)/(r ij.2.1).den=(r ij.2.1:ℝ)
        exact (Rat.cast_def _).symm
    have hband : ∀ a, (qi a:ℝ) ≤ (Q:ℝ) ∧ (Q:ℝ) ≤ 2*(qi a:ℝ) := by
      intro a
      fin_cases a
      · change ((r ij.1.1).den:ℝ) ≤ Q ∧ (Q:ℝ) ≤ 2*((r ij.1.1).den:ℝ)
        exact ⟨by exact_mod_cast (hden _ hi).1,by exact_mod_cast (hden _ hi).2⟩
      · change ((r ij.2.1).den:ℝ) ≤ Q ∧ (Q:ℝ) ≤ 2*((r ij.2.1).den:ℝ)
        exact ⟨by exact_mod_cast (hden _ hj).1,by exact_mod_cast (hden _ hj).2⟩
    obtain ⟨hdetA,ht,_htlo,_hthi,hmap,hgamma,_hrest⟩ := hA ij (hsub hij)
    have ht' : (A ij 2:ℝ)*((ei 0:ℝ)/qi 0)+A ij 3=(qi 1:ℝ)/qi 0 := by
      rw [hcast]
      change (A ij 2:ℝ)*(iteratedDeriv 2 (f ij.1.1) (z ij.1.1)/2)+A ij 3=
        (q ij.2.1:ℝ)/q ij.1.1 at ht
      rw [hlevel _ hi] at ht
      exact ht
    have hmap' : ((A ij 0:ℝ)*((ei 0:ℝ)/qi 0)+A ij 1)/
        ((A ij 2:ℝ)*((ei 0:ℝ)/qi 0)+A ij 3)=(ei 1:ℝ)/qi 1 := by
      rw [hcast,hcast]
      change ((A ij 0:ℝ)*(iteratedDeriv 2 (f ij.1.1) (z ij.1.1)/2)+A ij 1)/
        ((A ij 2:ℝ)*(iteratedDeriv 2 (f ij.1.1) (z ij.1.1)/2)+A ij 3)=
          iteratedDeriv 2 (f ij.2.1) (z ij.2.1)/2 at hmap
      rw [hlevel _ hi,hlevel _ hj] at hmap
      exact hmap
    have hnear : |Int.fract (-(vi 0:ℝ)/qi 0)-Int.fract (-(vi 1:ℝ)/qi 1)| ≤
        1/(6*(K₀:ℝ)^2*Vscale) := by
      have hn := hp.2 (1:Fin 4)
      change |Int.fract (-(vi 0:ℝ)/qi 0)-Int.fract (-(vi 1:ℝ)/qi 1)| ≤
        2*(1/(12*(K₀:ℝ)^2*Vscale)) at hn
      convert hn using 1
      field_simp
      norm_num
    exact fourier_matrix_narrowed_coordinate_entry_bound qi ei vi (A ij)
      (by
        intro a
        fin_cases a
        · change (0:ℤ) < (r ij.1.1).den
          exact_mod_cast (r ij.1.1).pos
        · change (0:ℤ) < (r ij.2.1).den
          exact_mod_cast (r ij.2.1).pos)
      hKone hVscale hNphys hmesh hband
      (by intro a; fin_cases a; exact hinv _ hi; exact hinv _ hj)
      hdetA ht' hmap' hgamma hnear

public  theorem model_source_large_entry_main_coefficient_nonneg {σ δ : ℝ} (hσ : 0 < σ) (hδ₀ : 0 ≤ δ) :
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := cubicScaleMajorant J c
    let budget := QuarticChartBudget.make σ δ κ Cphys B
    let Cmain := budget.Cmain
    0 ≤ Cmain := by
  intro κ Cphys c J B budget Cmain
  let C₂ := budget.C₂
  let C₃ := budget.C₃
  let Ct := budget.Ct
  let Cc := budget.Cc
  let Kres := budget.Kres
  let Lunit := budget.Lunit
  let Gamma := budget.Gamma
  let Cthird := budget.Cthird
  let Cfirst := budget.Cfirst
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hC₂ : 0 ≤ C₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ₀
  have hC₃ : 0 ≤ C₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ₀
  have hC₄ : 0 ≤ modelPhaseJetCoefficient σ 4+δ :=
    add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ₀
  have hRes : 0 ≤ quarticNonlinearResidualConstant σ δ := by
    dsimp only [quarticNonlinearResidualConstant]
    positivity
  have hRecip : 0 ≤ quarticReciprocalConstant σ δ := by
    dsimp only [quarticReciprocalConstant]
    positivity
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hCt : 0 ≤ Ct := by dsimp only [Ct]; positivity
  have hCc : 0 ≤ Cc := by dsimp only [Cc]; positivity
  have hKres : 0 ≤ Kres := by dsimp only [Kres, quarticResidualBudget, quarticTaylorSlack]; positivity
  have hLunit : 0 < Lunit := by dsimp only [Lunit]; positivity
  have hGamma : 0 ≤ Gamma := by dsimp only [Gamma]; positivity
  have hCthird : 0 ≤ Cthird := by dsimp only [Cthird]; positivity
  have hCfirst : 0 ≤ Cfirst := by dsimp only [Cfirst]; positivity
  have hCmain : 0 ≤ Cmain := by dsimp only [Cmain]; positivity
  exact hCmain

private theorem eventually_model_tagged_large_entry_source_mass_clamped
    {σ Jref εloss : ℝ} (hσ : 0 < σ) (hJref : 0 ≤ Jref) (hεloss : 0 < εloss) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (F : Fin 2 → ℝ → ℝ) (ya yb : ℝ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2))) (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
    (gap : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → ℝ × ℝ)
    (Q K₀ : ℕ) [NeZero K₀]
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (rat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 2 → ℚ)
    (vinv : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 2 → ℤ)
    (parity : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 2 → Fin 2)
    (anchor : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {δ M R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ},
    let V := max 1 (Uband*(N:ℝ)/(Q:ℝ))
    let x := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) => (![za ij.1.1.2,zb ij.2.1.2] : Fin 2 → ℝ)
    let xlocal := fun ij i => x ij i-(A i:ℝ)
    (∀ ij∈P, ij.1.1.1=ya ∧ ij.2.1.1=yb) →
    (∀ ij∈P, base ≤ za ij.1.1.2-(A 0:ℝ)) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1.2 ∧ AlenA ij.1.1.2 ≤ 3*N ∧
      round (za ij.1.1.2)+(AlenA ij.1.1.2:ℤ)=Za+(N:ℤ)*ij.1.1.2+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1.2 ∧ AlenB ij.2.1.2 ≤ 3*N ∧
      round (zb ij.2.1.2)+(AlenB ij.2.1.2:ℤ)=Zb+(N:ℤ)*ij.2.1.2+2*(N:ℤ)) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < (N:ℝ)) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*(N:ℝ)*R^2=M^3) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ (A i:ℝ)) →
    (∀ i, (A i:ℝ)+W i ≤ 2*M) →
    (∀ ij∈P, ∀ i, xlocal ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, (rat ij i).den ≤ Q ∧ Q ≤ 2*(rat ij i).den) →
    (0 < lambda) →
    (0 < Uband) → (Uband ≤ 1) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ij∈P, ∀ i, lambda ≤ |(rat ij i:ℝ)| ∧ |(rat ij i:ℝ)| ≤ Uband) →
    (∀ ij∈P, ∀ i, ((rat ij i).den:ℤ) ∣ (rat ij i).num*vinv ij i-1) →
    WithReferenceBasis Gaps Refs e r v s Uref R Bcut (
    (∀ ij∈P, ∀ i, xlocal ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, xlocal ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    WithReferenceScale Gaps r Uref Q (modelPhaseThirdLower σ) Bcut Bselect M (N:ℝ) R (
    (∀ ij∈P, (rat ij 0:ℝ)∈Icc (gap ij).1 (gap ij).2) →
    (∀ ij∈P, Mat ij 2 ≠ 0) →
    (∀ ij∈P, 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat ij 2:ℝ)| *(modelPhaseThirdLower σ)^2*T) →
    (∀ ij∈P, 8*Uband ≤ |(Mat ij 2:ℝ)| *lambda^2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) → (Uref:ℝ) ≤ R^2 →
    WithReferenceCoefficientBounds Gaps e r v s Uref Jref T σ M R (
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let sourceColor := fun ij i => rationalSourceBin Q lambda θ (rat ij i)
    (∀ ij∈P, sourceColor ij 0=sourceColor ij 1) →
    let f := fun (i : Fin 2) w => T*F i (w/M)
    (∀ ij∈P, ∀ i, iteratedDeriv 2 (f i) (x ij i)/2=(rat ij i:ℝ)) →
    let q := fun ij i => (rat ij i).den
    let cloud := fun ij i => cubicProbeCloud (f i) (x ij i) (q ij i) K₀ (vinv ij i) (parity ij i)
    let radius : Fin 4 → ℝ := cubicCompletionRadius K₀
    (∀ ij∈P, cubicProbeColor (f 0) (x ij 0) (q ij 0) (parity ij 0)=
      cubicProbeColor (f 1) (x ij 1) (q ij 1) (parity ij 1)) →
    (∀ ij∈P, ∀ a, |cloud ij 0 a-cloud ij 1 a| ≤ 2*radius a) →
    (∀ ij∈P,
      |cloud ij 0 1-cloud ij 1 1| ≤ 1/(6*(K₀:ℝ)^2*V)) →
    WithCubicScales σ M (N:ℝ) R Q (fun κ Cphys c J B =>
    (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
    (∀ ij∈P, (Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat ij 0:ℝ)*(rat ij 0:ℝ)+Mat ij 1)/
      ((Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3)=(rat ij 1:ℝ)) →
    (∀ ij∈P, |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ ij∈P, ∀ i, xlocal ij i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, xlocal ij i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    WithRationalAnchors P rat anchor ε Q (
    let budget := QuarticChartBudget.make σ δ κ Cphys B
    let Δ := budget.delta Q N
    let Ccurv := budget.Ccurv
    let D := budget.error Q N
    let Esize := budget.Esize
    let Dbase := budget.Dbase
    let Tbase := budget.Tbase
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Cmain := budget.Cmain
    let Ctail := budget.Ctail
    V*(P.card:ℝ) ≤
      (60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
        (Cmain*((Q:ℝ)/(Uband*(N:ℝ)))^((2:ℝ)/3)+Ctail/(Uref:ℝ)))*T^εloss))))) := by
  classical
  filter_upwards [eventually_physicalModelPhase_actual_fourier_original_pair_mass_raw hσ hJref hεloss]
    with T hpair
  dsimp (config := {zeta := false, zetaUnused := false}) only [WithCubicScales]
  intro F ya yb Uref Refs Gaps Bselect P Mat gap Q K₀ inst N za zb AlenA AlenB Za Zb
    rat vinv parity anchor e r v s δ M R base Bcut lambda Uband θ A W V x xlocal
    hphase hbase hgapMem hgeometryA hgeometryB hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hlambda hUband hUbandCap hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hc hlarge haction hgap
    hQN hNM hUR hrHeight hsHeight heHeight hvHeight
    ε sourceColor hsourceColor f hlevel q cloud radius
    hcolor hnear hnearNarrow κ Cphys c J B hsmall hNR hRN hNcube hminscale
    hMatdet hMatt hMatmap hMatgamma H hNtwo hL hU hanchor hcut hcount
    budget Δ Ccurv D Esize Dbase Tbase hsize hD hΔ hBsize
    Cmain Ctail

  let forget := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
    ((ij.1.1.2,ij.1.2),(ij.2.1.2,ij.2.2))
  let embed := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) =>
    (((ya,ij.1.1),ij.1.2),((yb,ij.2.1),ij.2.2))
  let Pbar := P.image forget
  have hback ij (hij : ij∈P) : embed (forget ij)=ij := by
    rcases ij with ⟨⟨⟨a,n⟩,pa⟩,⟨⟨b,m⟩,pb⟩⟩
    have he := hphase _ hij
    dsimp only at he
    rcases he with ⟨rfl,rfl⟩
    rfl
  have hcard : Pbar.card=P.card := by
    apply Finset.card_image_of_injOn
    intro ij hij kl hkl he
    exact (hback ij hij).symm.trans ((congrArg embed he).trans (hback kl hkl))
  have hmem ij (hij : ij∈Pbar) : embed ij∈P := by
    obtain ⟨kl,hkl,rfl⟩ := Finset.mem_image.mp hij
    rw [hback kl hkl]
    exact hkl
  have lift {p : ((ℝ × ℤ) × Fin 2) × (ℝ × ℤ) × Fin 2 → Prop} (h : ∀ ij∈P, p ij) (ij) (hij : ij∈Pbar) : p (embed ij) := h _ (hmem ij hij)
  have hV : 1 ≤ V := le_max_left _ _
  let flocal := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
  have hsource i : flocal i = fun w => f i ((A i:ℝ)+w) := by
    funext w
    simp only [flocal,heathBrownPhysicalPhase,f,one_mul, physicalFirstDifference]
  let paint := fun ij i => cubicProbeColor (flocal i) (xlocal ij i) (q ij i) (parity ij i)
  let packed := fun ij i => cubicProbeCloud (flocal i) (xlocal ij i) (q ij i) K₀ (vinv ij i) (parity ij i)
  have hpaint ij i : paint ij i=cubicProbeColor (f i) (x ij i) (q ij i) (parity ij i) :=
    cubicProbeColor_translate (hsource i) _ _ _
  have hpacked ij i : packed ij i=cloud ij i :=
    cubicProbeCloud_translate (hsource i) _ _ _ _ _
  have hgeomA ij hij := translated_grid_geometry (a:=A 0) (hgeometryA ij hij)
  have hgeomB ij hij := translated_grid_geometry (a:=A 1) (hgeometryB ij hij)
  have hmass : (Pbar.card:ℝ) ≤
      (60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
        (Cmain/V^((5:ℝ)/3)+Ctail/((Uref:ℝ)*V)))*T^εloss := by
    apply hpair Uref Refs Gaps (Bselect:=Bselect) Pbar (fun ij => Mat (embed ij)) (fun ij => gap (embed ij)) Q K₀ N
      (fun n => za n-(A 0:ℝ)) (fun n => zb n-(A 1:ℝ))
      AlenA AlenB (Za-A 0) (Zb-A 1)
      (fun ij => rat (embed ij)) (fun ij => vinv (embed ij))
      (fun ij => parity (embed ij)) (fun ij => anchor (embed ij)) e r v s
      (δ:=δ) (M:=M) (R:=R) (base:=base) (Bcut:=Bcut)
      (lambda:=lambda) (Uband:=Uband) (θ:=θ) (V:=V) (F:=F)
      (A:=fun i => (A i:ℝ)) (W:=W) (x:=fun ij => xlocal (embed ij))
      (lift hbase) (by intro ij _; rfl) (by intro ij _; rfl) (lift hgapMem) (lift hgeomA) (lift hgeomB)
      hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW (lift hx) (lift hden) hlambda hUband.le hθ hθmax (lift hcurv)
      (lift hinv) hchart horientation hBcut hs hrefSet hparentSet hsep (lift hwideL) (lift hwideU) hUref
      hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
      hselectedUpper hscaleTen (lift hfamilyGap) (lift hc) (lift hlarge) (lift haction) hV hgap
      hQN hNM hUR hrHeight hsHeight heHeight hvHeight (lift hsourceColor)
      (fun ij hij i => (congrArg (· / (2:ℝ)) (translated_phase_iteratedDeriv (hsource i) (x (embed ij) i) 2)).trans (hlevel (embed ij) (hmem ij hij) i))
      (by
        intro ij hij
        change paint (embed ij) 0=paint (embed ij) 1
        simpa only [hpaint] using hcolor (embed ij) (hmem ij hij))
      (by
        intro ij hij d
        change |packed (embed ij) 0 d-packed (embed ij) 1 d| ≤ 2*radius d
        simpa only [hpacked] using hnear (embed ij) (hmem ij hij) d)
      (by
        intro ij hij
        change |packed (embed ij) 0 1-packed (embed ij) 1 1| ≤ 1/(6*(K₀:ℝ)^2*V)
        simpa only [hpacked] using hnearNarrow (embed ij) (hmem ij hij))
      hsmall hNR hRN hNcube hminscale (lift hMatdet) (lift hMatt) (lift hMatmap) (lift hMatgamma)
      hNtwo (lift hL) (lift hU) (lift hanchor) (lift hcut) (lift hcount) hsize hD hΔ hBsize
  rw [hcard] at hmass
  have hδ₀ := approximateModelPhase_tolerance_nonneg (hF 0)
  have hCmain : 0 ≤ Cmain := model_source_large_entry_main_coefficient_nonneg hσ hδ₀
  have hUp : (0:ℝ) < Uref := Nat.cast_pos.mpr (by omega)
  have hclamp := (clamped_narrowing_source_costs
    (H:=Uband) (N:=(N:ℝ)) (Q:=(Q:ℝ)) (C:=0) (a:=Cmain) (b:=Ctail) (Uref:=(Uref:ℝ))
    hUband hUbandCap hN (Nat.cast_pos.mpr hQ) (by norm_num) hCmain hUp).2.2
  let Kbase := 60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)
  have hKbase : 0 ≤ Kbase := by dsimp only [Kbase]; positivity
  have hbound : V*(P.card:ℝ) ≤
      Kbase*(V*(Cmain/V^((5:ℝ)/3)+Ctail/((Uref:ℝ)*V)))*T^εloss := by
    have hh := mul_le_mul_of_nonneg_left hmass (zero_le_one.trans hV)
    convert hh using 1
    dsimp only [Kbase]
    ring
  exact hbound.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hclamp hKbase) (Real.rpow_nonneg hT.le _))

private theorem double_difference_source_large_action_threshold
    {σ c U E : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) (hE : 0 < E) :
    let κ := modelPhaseThirdLower σ
    let L := max (32*U^2/c^2) (64*(modelPhaseJetCoefficient σ 3+1)*U*E/κ^2)
    0 ≤ L ∧ ∀ {Tsrc T M δ γ : ℝ}, 0 < Tsrc → 0 < T → 0 < M →
      Tsrc ≤ E*T → δ ≤ 1 →
      let lambda := c*Tsrc/(2*M^2)
      let Hcurv := U*Tsrc/M^2
      L < |γ| *Hcurv →
        γ ≠ 0 ∧ 8*Hcurv ≤ |γ| *lambda^2 ∧
          64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤ |γ| *κ^2*T := by
  intro κ L
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hL : 0 ≤ L := (by positivity : (0:ℝ) ≤ 32*U^2/c^2).trans (le_max_left _ _)
  refine ⟨hL,?_⟩
  intro Tsrc T M δ γ hTsrc _hT hM hsource hδ lambda Hcurv hlarge
  have hH : 0 < Hcurv := by dsimp only [Hcurv]; positivity
  have hγ : γ ≠ 0 := by
    intro he
    rw [he,abs_zero,zero_mul] at hlarge
    exact (not_lt_of_ge hL) hlarge
  have hratio := (le_max_left (32*U^2/c^2)
    (64*(modelPhaseJetCoefficient σ 3+1)*U*E/κ^2)).trans hlarge.le
  have hcoef := (le_max_right (32*U^2/c^2)
    (64*(modelPhaseJetCoefficient σ 3+1)*U*E/κ^2)).trans hlarge.le
  have hratioId : (32*U^2/c^2)*lambda^2=8*Hcurv^2 := by
    dsimp only [lambda,Hcurv]
    field_simp
    ring
  have haction : 8*Hcurv ≤ |γ| *lambda^2 := by
    apply (mul_le_mul_iff_right₀ hH).mp
    have hh := mul_le_mul_of_nonneg_right hratio (sq_nonneg lambda)
    rw [hratioId] at hh
    nlinarith only [hh]
  have hcoe : 64*(modelPhaseJetCoefficient σ 3+1)*U*E ≤ (|γ| *Hcurv)*κ^2 :=
    (div_le_iff₀ (sq_pos_of_pos hκ)).mp hcoef
  have hbudget : 64*(modelPhaseJetCoefficient σ 3+1)*U*E*M^2 ≤
      |γ| *U*Tsrc*κ^2 := by
    have hh := mul_le_mul_of_nonneg_right hcoe (sq_nonneg M)
    have he : (|γ| *Hcurv)*κ^2*M^2=|γ| *U*Tsrc*κ^2 := by
      dsimp only [Hcurv]
      field_simp
    simpa only [he] using hh
  have hnormalized : 64*(modelPhaseJetCoefficient σ 3+1)*M^2 ≤ |γ| *κ^2*T := by
    apply (mul_le_mul_iff_right₀ (mul_pos hU hE)).mp
    have hh := mul_le_mul_of_nonneg_left hsource
      (show 0 ≤ |γ| *U*κ^2 by positivity)
    nlinarith only [hbudget,hh]
  refine ⟨hγ,haction,?_⟩
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hδ) (by norm_num : (0:ℝ) ≤ 64))
    (sq_nonneg M)).trans hnormalized

public  theorem double_difference_physical_curvature_band
    (F : ℝ → ℝ) {z r s d y c U T M : ℝ}
    (hz : z∈Icc M (2*M)) (hy : y∈Icc (1:ℝ) 2)
    (hr : 0 < r) (hs : 0 < s) (hd : 0 < d)
    (hc : 0 < c) (hU : 0 < U) (hT : 0 < T) (hM : 0 < M)
    (hprod : r*s=d*y) (hshift : r+s ≤ 1/4)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ F u)
    (hneg : ∀ u∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F u ≤ -c)
    (hbound : ∀ u∈Icc (1/2:ℝ) 3, |iteratedDeriv 4 F u| ≤ U) :
    let Q := fun u => (F u-F (u+r)-F (u+s)+F (u+r+s))/d
    let f := fun w => T*Q (w/M)
    c*T/(2*M^2) ≤ |iteratedDeriv 2 f z/2| ∧
      |iteratedDeriv 2 f z/2| ≤ U*T/M^2 := by
  intro Q f
  have hzpos : 0 < z := hM.trans_le hz.1
  have hx : z/M∈Icc (3/4:ℝ) (9/4) := by
    constructor
    · apply (le_div_iff₀ hM).mpr
      linarith only [hz.1,hM]
    · apply (div_le_iff₀ hM).mpr
      linarith only [hz.2,hM]
  have hreg u (hu : 0 < u) : ContDiffAt ℝ ∞ Q u :=
    ((((hf u hu).sub ((hf (u+r) (by positivity)).comp u
      (contDiffAt_id.add contDiffAt_const))).sub
        ((hf (u+s) (by positivity)).comp u (contDiffAt_id.add contDiffAt_const))).add
          ((hf (u+r+s) (by positivity)).comp u
            ((contDiffAt_id.add contDiffAt_const).add contDiffAt_const))).div_const d
  have hphysical : iteratedDeriv 2 f z=T/M^2*iteratedDeriv 2 Q (z/M) := by
    have ha := sargos_iteratedDeriv_comp_affine_local (f:=Q)
      (l:=0) (r:=z+1) (c:=M⁻¹) (d:=0)
      (fun v hv => hreg _ (by
        simpa only [add_zero] using mul_pos (inv_pos.mpr hM) hv.1))
      (show z∈Ioo (0:ℝ) (z+1) from ⟨hzpos,by linarith⟩) 2
    change iteratedDeriv 2 (fun w => T*Q (w/M)) z=_
    rw [iteratedDeriv_const_mul_field]
    have he : (fun w => Q (w/M))=(fun w => Q (M⁻¹*w+0)) := by
      funext w
      congr 1
      ring
    rw [he,ha]
    simp only [add_zero,inv_pow]
    rw [show M⁻¹*z=z/M by ring]
    ring
  have hband : -2*U ≤ iteratedDeriv 2 Q (z/M) ∧
      iteratedDeriv 2 Q (z/M) ≤ -c :=
    double_difference_exact_curvature_band F hx hy hr hs hd hc hU hprod hshift hf hneg hbound
  have hsign : iteratedDeriv 2 Q (z/M) < 0 := by
    linarith only [hband.2,hc]
  rw [hphysical,abs_div,abs_mul,
    abs_of_pos (div_pos hT (pow_pos hM 2)),abs_of_neg hsign,
    abs_of_pos (by norm_num : (0:ℝ) < 2)]
  constructor
  · calc
      c*T/(2*M^2) = (T/M^2)*c/2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith only [hband.2]) (by positivity)) (by norm_num)
  · calc
      _ ≤ (T/M^2)*(2*U)/2 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith only [hband.1]) (by positivity)) (by norm_num)
      _ = U*T/M^2 := by ring

public  theorem eventually_double_difference_actual_family_source_sieve
    {csrc Usrc E σ εloss : ℝ}
    (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hE : 0 < E) (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let L := max (32*Usrc^2/csrc^2)
      (64*(modelPhaseJetCoefficient σ 3+1)*Usrc*E/κ^2)
    let θ := 1/(8*(L+3))
    ∃ C Dtype : ℝ, 0 < C ∧ 0 < Dtype ∧
    ∀ {Jref : ℝ}, 0 ≤ Jref →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (S : Finset (ℝ × ℤ)) (Fsrc rshift sshift : ℝ → ℝ)
    (z : (ℝ × ℤ) → ℝ) (rat : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ) (Nlen : (ℝ × ℤ) → ℕ)
    (Q K₀ N : ℕ) [NeZero K₀] (R Jsep : ℝ) (Z : ℝ → ℤ)
    {d Wmax Tsrc M δ Bcut Bselect : ℝ}
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (A : ℝ → ℤ) (W : ℝ → ℝ) (gap : (ℝ × ℤ) → ℝ × ℝ)
    (anchor : (ℝ × ℤ) → ℚ) (e r vRef s : ℝ × ℝ → ℤ),
    let lambda := csrc*Tsrc/(2*M^2)
    let Uband := Usrc*Tsrc/M^2
    let Vscale := max 1 (Uband*(N:ℝ)/(Q:ℝ))
    (0 < d) → (0 ≤ Wmax) → (Wmax ≤ 1/4) → (2*Usrc*Wmax ≤ csrc/64) →
    (0 < Tsrc) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (Tsrc ≤ E*T) →
    (0 < Q) → (Uband ≤ 1) →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Icc M (2*M)) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, csrc ≤ iteratedDeriv 5 Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 → |iteratedDeriv n Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3,
      csrc ≤ |(iteratedDeriv 5 Fsrc w)^2-iteratedDeriv 4 Fsrc w*iteratedDeriv 6 Fsrc w|) →
    (∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) →
    (∀ i∈S, ((rat i).den:ℤ) ∣ (rat i).num*v i-1) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (0 < N) →
    (0 < Jsep) → (Jsep ≤ M) → ((N:ℝ) ≤ M) → (Wmax*Jsep ≤ 1) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i∈S, N ≤ Nlen i ∧ Nlen i ≤ 3*N ∧
      round (z i)+(Nlen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    (∀ y∈S.image Prod.fst,
      0 ≤ rshift y ∧ 0 ≤ sshift y ∧ rshift y*sshift y=d*y ∧ rshift y+sshift y ≤ Wmax) →
    let Φ := fun y u =>
      (Fsrc u-Fsrc (u+rshift y)-Fsrc (u+sshift y)+Fsrc (u+rshift y+sshift y))/d
    let Fmodel := fun (i : ℝ × ℤ) u => (Tsrc/T)*Φ i.1 u
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 4 δ) →
    let f := fun p w => Tsrc*Φ p (w/M)
    (∀ i∈S, iteratedDeriv 2 (f (i.1)) (z i)/2=(rat i:ℝ)) →
    (∀ i∈S, 1 ≤ Nlen i ∧ (rat i).den ≤ Nlen i ∧
      1 ≤ (iteratedDeriv 3 (f (i.1)) (round (z i))/6)*((rat i).den:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*((iteratedDeriv 3 (f (i.1)) (round (z i))/6)*
      ((rat i).den:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →

    (1 ≤ R) → (R ≤ M) → (T*(N:ℝ)*R^2=M^3) →
    (∀ i∈S, M ≤ A i.1) → (∀ i∈S, A i.1+W i.1 ≤ 2*M) →
    let xlocal := fun i : ℝ × ℤ => z i-(A i.1:ℝ)
    (∀ i∈S, xlocal i∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, gap i∈Gaps) →
    WithReferenceBasis Gaps Refs e r vRef s Uref R Bcut (
    (∀ i∈S, xlocal i-(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    WithReferenceScale Gaps r Uref Q κ Bcut Bselect M (N:ℝ) R (
    (∀ i∈S, (rat i:ℝ)∈Icc (gap i).1 (gap i).2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) →
    ((N:ℝ)^2 ≤ M ∨ (1 ≤ M ∧ (N:ℝ) ≤ T ∧ R^2 ≤ T)) → (Uref:ℝ) ≤ R^2 →
    WithReferenceCoefficientBounds Gaps e r vRef s Uref Jref T σ M R (
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := cubicScaleMajorant J c
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ i∈S, xlocal i-H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    let ε := κ/(16*(Cphys+2)*R^2)
    (∀ i∈S, |(anchor i:ℝ)-(rat i:ℝ)| ≤ ε) →
    (∀ i∈S, 256*((anchor i).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ i∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor i).den) →
    let narrow := fun (i : ℝ × ℤ) => rationalSourceBin Q lambda θ (rat i)
    let qell := fun (i : ℝ × ℤ) => ((rat i).den:ℝ)*deriv (f (i.1)) (round (z i))
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let offset := fun ip : (ℝ × ℤ) × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : (ℝ × ℤ) × Fin 2 => (narrow ip.1,offset ip)
    let NarrowCap := (4/θ+3)*(8*Usrc/(csrc*θ)+3)
    let Cap := 3*NarrowCap

    let q := fun (i : ℝ × ℤ) => (rat i).den
    let μ := fun (i : ℝ × ℤ) => iteratedDeriv 3 (f (i.1)) (round (z i))/6
    let b := fun ip : (ℝ × ℤ) × Fin 2 => (⌊qell ip.1⌋+(ip.2:ℕ) : ℤ)
    let tau := fun ip : (ℝ × ℤ) × Fin 2 => ((b ip:ℝ)-qell ip.1)/2
    let dual := fun (i : ℝ × ℤ) => cubicDualPhase (μ i) (q i)
    let x := fun ip : (ℝ × ℤ) × Fin 2 => cubicCoordinates (v ip.1) (b ip) (q ip.1) (dual ip.1) (tau ip)
    let Fiber := fun key => V.filter (fun ip => color ip=key)
    let μ₀ := csrc*Tsrc/(12*M^3)
    let U₀ := Usrc*Tsrc/(2*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let budget := QuarticChartBudget.make σ δ κ Cphys B
    let Δ := budget.delta Q N
    let Ccurv := budget.Ccurv
    let D := budget.error Q N
    let Esize := budget.Esize
    let Dbase := budget.Dbase
    let Tbase := budget.Tbase
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Cmain := budget.Cmain
    let Ctail := budget.Ctail
    let Klarge := 60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain*((Q:ℝ)/(Uband*(N:ℝ)))^((2:ℝ)/3)+Ctail/(Uref:ℝ))
    let Y := S.image Prod.fst
    ((V.image color).card:ℝ) ≤ Cap ∧
    ∀ k : ZMod K₀,
      (∑ ip∈V, ‖∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x ip d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
        C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
          ∑ key∈V.image color, ((Fiber key).card:ℝ)^10*
            (Vscale*Dtype*(2+θ*(Uband+1/lambda))*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
              (Y.card:ℝ)^2*Klarge*T^εloss)))) := by
  classical
  intro κ L θ
  have hL : 0 ≤ L := (double_difference_source_large_action_threshold hσ hcsrc hUsrc hE).1
  have hθ : 0 < θ := by dsimp only [θ]; positivity
  have hθmax : θ ≤ 1/24 := by
    dsimp only [θ]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [hL]
  obtain ⟨Dtype,C,hDtype,hC,hsource⟩ :=
    double_difference_actual_joint_narrowed_sieve hcsrc hUsrc hL hεloss
  refine ⟨C,Dtype,hC,hDtype,?_⟩
  intro Jref hJref
  filter_upwards [eventually_model_tagged_large_entry_source_mass_clamped hσ hJref hεloss]
    with T hboundFn
  intro S Fsrc rshift sshift z rat v Nlen Q K₀ N instK R Jsep Z
    d Wmax Tsrc M δ Bcut Bselect Uref Refs Gaps A W gap anchor e r vRef s
    lambda Uband Vscale hd hw hwcap hsmallShift hTsrc hT hM hδ hsourceScale hQ hUbandCap
    hy hz hreg hlower hjets htests hden hinv hnegative hMtwo hN
    hJsep hJM hNM hwJ hmesh hgeometry hseparation hshifts Φ Fmodel hmodel f hlevel hminor hcomplete
    hR hRM hscale hA hW xlocal hx hgapMem
    hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
    hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
    hselectedUpper hscaleTen hfamilyGap hgap hQN hNsqM hUR
    hrHeight hsHeight heHeight hvHeight Cphys c J B hsmall hNR hRN hNcube hminscale
    H hNtwo hLeft hRight ε hanchor hcut hcount
    narrow qell V offset color NarrowCap Cap q μ b tau dual x Fiber μ₀ U₀ Δtype
    budget Δ Ccurv D Esize Dbase Tbase hsize hD hΔ hBsize
    Cmain Ctail Klarge Y
  have hVscale : 1 ≤ Vscale := le_max_left _ _
  have hlambda : 0 < lambda := by dsimp only [lambda]; positivity
  have hUband : 0 < Uband := by dsimp only [Uband]; positivity
  have hcurv i (hi : i∈S) : lambda ≤ |(rat i:ℝ)| ∧ |(rat i:ℝ)| ≤ Uband := by
    have hsdata := hshifts i.1 (Finset.mem_image_of_mem Prod.fst hi)
    have hpar := hy i hi
    have hprodpos : 0 < rshift i.1*sshift i.1 := by
      rw [hsdata.2.2.1]
      exact mul_pos hd (by linarith only [hpar.1])
    have hrp : 0 < rshift i.1 := by nlinarith only [hsdata.1,hsdata.2.1,hprodpos]
    have hsp : 0 < sshift i.1 := by nlinarith only [hsdata.1,hsdata.2.1,hprodpos]
    rw [←hlevel i hi]
    exact double_difference_physical_curvature_band Fsrc (hz i hi) hpar hrp hsp
      hd hcsrc hUsrc hTsrc hM hsdata.2.2.1 (hsdata.2.2.2.trans hwcap)
      hreg hnegative (fun u hu => hjets u hu 4 (by norm_num) (by norm_num))
  obtain ⟨_hNarrowCard,_hHolder,Mat,hglobal,_hclass,htype,htri,hcard,hfourier,_hnarrow⟩ :=
    hsource S Fsrc rshift sshift z rat v Nlen Z Q K₀ N d Wmax Tsrc M Jsep Nlen Vscale R
      hreg hlower hjets htests hnegative hd hw hwcap hsmallShift hTsrc hMtwo hN hQ
      hJsep hNM hJM hwJ hy hz hgeometry hseparation hshifts hlevel hden hinv
      hVscale hmesh hminor hcomplete
  let cloud := fun ip => (![Int.fract (x ip 0),Int.fract (x ip 1),
    x ip 2/Real.sqrt K₀,x ip 3/Real.sqrt K₀] : Fin 4 → ℝ)
  let radius : Fin 4 → ℝ :=
    ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2*Vscale),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
  let wideRadius : Fin 4 → ℝ :=
    ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
  let Pall := (V ×ˢ V).filter (fun ij => ∀ a, |cloud ij.1 a-cloud ij.2 a| ≤ 2*radius a)
  let Pwide := (V ×ˢ V).filter (fun ij => ∀ a, |cloud ij.1 a-cloud ij.2 a| ≤ 2*wideRadius a)
  let Pairs := fun key => ((Fiber key) ×ˢ (Fiber key)).filter
    (fun ij => ∀ a, |cloud ij.1 a-cloud ij.2 a| ≤ 2*radius a)
  let Etype := Pwide.filter (fun ij =>
    narrow ij.1.1=narrow ij.2.1 ∧
      ((Mat ij 0=1 ∧ Mat ij 1=0 ∧ Mat ij 2=0 ∧ Mat ij 3=1) ∨
       (Mat ij 1≠0 ∧ Mat ij 2≠0 ∧ |(Mat ij 2:ℝ)| *Uband ≤ L)))
  let Etri := Pwide.filter (fun ij =>
    narrow ij.1.1=narrow ij.2.1 ∧ (Mat ij 2=0 ∨ Mat ij 1=0))
  let Large := fun key => (Pairs key).filter (fun ij =>
    Mat ij 1≠0 ∧ Mat ij 2≠0 ∧ L < |(Mat ij 2:ℝ)| *Uband)
  let phaseFiber := fun key (ab : ℝ × ℝ) =>
    (Large key).filter (fun ij => ij.1.1.1=ab.1 ∧ ij.2.1.1=ab.2)
  have hRadius a : radius a ≤ wideRadius a := by
    have hKpos : (0:ℝ) < K₀ := by exact_mod_cast NeZero.pos K₀
    fin_cases a
    · exact le_rfl
    · change 1/(12*(K₀:ℝ)^2*Vscale) ≤ 1/(12*(K₀:ℝ)^2)
      apply one_div_le_one_div_of_le (by positivity)
      exact le_mul_of_one_le_right (by positivity) hVscale
    · exact le_rfl
    · exact le_rfl
  have hsub : Pall ⊆ Pwide := by
    intro ij hij
    obtain ⟨hh,hn⟩ := Finset.mem_filter.mp hij
    exact Finset.mem_filter.mpr ⟨hh,fun a => (hn a).trans
      (mul_le_mul_of_nonneg_left (hRadius a) (by norm_num))⟩
  have hPairData key ij (hij : ij∈Pairs key) :
      ij.1∈V ∧ ij.2∈V ∧ color ij.1=key ∧ color ij.2=key ∧ ij∈Pall := by
    have hp := Finset.mem_product.mp (Finset.mem_filter.mp hij).1
    have h1 := Finset.mem_filter.mp hp.1
    have h2 := Finset.mem_filter.mp hp.2
    exact ⟨h1.1,h2.1,h1.2,h2.2,
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1.1,h2.1⟩,
        (Finset.mem_filter.mp hij).2⟩⟩
  have hMatData ij (hij : ij∈Pall) :
      Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1 ∧
      (Mat ij 2:ℝ)*(rat ij.1.1:ℝ)+Mat ij 3=(q ij.2.1:ℝ)/q ij.1.1 ∧
      ((Mat ij 0:ℝ)*(rat ij.1.1:ℝ)+Mat ij 1)/
        ((Mat ij 2:ℝ)*(rat ij.1.1:ℝ)+Mat ij 3)=(rat ij.2.1:ℝ) ∧
      |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) := by
    have hg := hglobal ij (hsub hij)
    have hp := Finset.mem_product.mp (Finset.mem_filter.mp hij).1
    have hl1 := hlevel ij.1.1 (Finset.mem_product.mp hp.1).1
    have hl2 := hlevel ij.2.1 (Finset.mem_product.mp hp.2).1
    have ht : (Mat ij 2:ℝ)*(iteratedDeriv 2 (f ij.1.1.1) (z ij.1.1)/2)+Mat ij 3=
        (q ij.2.1:ℝ)/q ij.1.1 := hg.2.1
    have hm : ((Mat ij 0:ℝ)*(iteratedDeriv 2 (f ij.1.1.1) (z ij.1.1)/2)+Mat ij 1)/
        ((Mat ij 2:ℝ)*(iteratedDeriv 2 (f ij.1.1.1) (z ij.1.1)/2)+Mat ij 3)=
        iteratedDeriv 2 (f ij.2.1.1) (z ij.2.1)/2 := hg.2.2.2.2.1
    rw [hl1] at ht
    rw [hl1,hl2] at hm
    exact ⟨hg.1,ht,hm,hg.2.2.2.2.2.1⟩
  have hY y (hym : y∈Y) :
      y∈Icc (1:ℝ) 2 ∧ M ≤ A y ∧ A y+W y ≤ 2*M ∧
      Expdb.IsApproximateModelPhaseFunction (fun u => (Tsrc/T)*Φ y u) σ 4 δ := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hym
    exact ⟨hy i hi,hA i hi,hW i hi,hmodel i hi⟩
  have hLargeData key ij (hij : ij∈Large key) :
      Mat ij 2≠0 ∧ 8*Uband ≤ |(Mat ij 2:ℝ)| *lambda^2 ∧
        64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤ |(Mat ij 2:ℝ)| *κ^2*T := by
    have hd := (Finset.mem_filter.mp hij).2
    have hb := (double_difference_source_large_action_threshold hσ hcsrc hUsrc hE).2
      hTsrc hT hM hsourceScale (hδ.trans (min_le_right _ _)) hd.2.2
    exact ⟨hd.2.1,hb.2.1,hb.2.2⟩
  have hphaseBound key ab (hab : ab∈Y ×ˢ Y) :
      Vscale*((phaseFiber key ab).card:ℝ) ≤ Klarge*T^εloss := by
    let P := phaseFiber key ab
    let yp : Fin 2 → ℝ := ![ab.1,ab.2]
    let ip := fun p : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
      (![p.1,p.2] : Fin 2 → (ℝ × ℤ) × Fin 2)
    let xp := fun p : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
      (![z (ab.1,p.1.1.2),z (ab.2,p.2.1.2)] : Fin 2 → ℝ)
    let fp := fun i => f (yp i)
    let Ap := fun i => A (yp i)
    let Wp := fun i => W (yp i)
    let rp := fun p i => rat (ip p i).1
    let vp := fun p i => v (ip p i).1
    let pp := fun p i => (ip p i).2
    let qp := fun p i => (rp p i).den
    let mup := fun p i => iteratedDeriv 3 (fp i) (round (xp p i))/6
    let ellp := fun p i => deriv (fp i) (round (xp p i))
    let bp := fun p i => (⌊(qp p i:ℝ)*ellp p i⌋+(pp p i:ℕ) : ℤ)
    let crp := fun p i => round ((qp p i:ℝ)*ellp p i)
    let taup := fun p i => ((bp p i:ℝ)-(qp p i:ℝ)*ellp p i)/2
    let dualp := fun p i => cubicDualPhase (mup p i) (qp p i)
    let cloudp := fun p i => (![Int.fract (-(vp p i:ℝ)*bp p i/qp p i),
      Int.fract (-(vp p i:ℝ)/qp p i),dualp p i/Real.sqrt K₀,
      (3*dualp p i*taup p i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    have hLarge p (hp : p∈P) : p∈Large key := (Finset.mem_filter.mp hp).1
    have hPairs p (hp : p∈P) : p∈Pairs key := (Finset.mem_filter.mp (hLarge p hp)).1
    have hPhase p (hp : p∈P) : p.1.1.1=ab.1 ∧ p.2.1.1=ab.2 :=
      (Finset.mem_filter.mp hp).2
    have hSlot p (hp : p∈P) i : ip p i∈V := by
      fin_cases i
      · exact (hPairData key p (hPairs p hp)).1
      · exact (hPairData key p (hPairs p hp)).2.1
    have hS p (hp : p∈P) i : (ip p i).1∈S :=
      (Finset.mem_product.mp (hSlot p hp i)).1
    have hColor p (hp : p∈P) i : color (ip p i)=key := by
      fin_cases i
      · exact (hPairData key p (hPairs p hp)).2.2.1
      · exact (hPairData key p (hPairs p hp)).2.2.2.1
    have hYP p (hp : p∈P) i : yp i=(ip p i).1.1 := by
      fin_cases i
      · exact (hPhase p hp).1.symm
      · exact (hPhase p hp).2.symm
    have hPointA p (hp : p∈P) : (ab.1,p.1.1.2)=p.1.1 :=
      Prod.ext (hPhase p hp).1.symm rfl
    have hPointB p (hp : p∈P) : (ab.2,p.2.1.2)=p.2.1 :=
      Prod.ext (hPhase p hp).2.symm rfl
    have hData p (hp : p∈P) i :
        xp p i=z (ip p i).1 ∧
        (∀ n, iteratedDeriv n (fp i) (xp p i)=
          iteratedDeriv n (f (ip p i).1.1) (z (ip p i).1)) ∧
        bp p i-crp p i = offset (ip p i) ∧ cloudp p i=cloud (ip p i) := by
      rcases p with ⟨⟨⟨ya,n⟩,pa⟩,⟨⟨yb,m⟩,pb⟩⟩
      have he := hPhase _ hp
      dsimp only at he
      rcases he with ⟨rfl,rfl⟩
      fin_cases i <;> exact ⟨rfl,fun _ => rfl,rfl,rfl⟩
    have hLoc p (hp : p∈P) i : xp p i-(Ap i:ℝ)=xlocal (ip p i).1 := by
      change xp p i-(A (yp i):ℝ)=z (ip p i).1-(A (ip p i).1.1:ℝ)
      rw [(hData p hp i).1,hYP p hp i]
    have hWp p (hp : p∈P) i : Wp i=W (ip p i).1.1 :=
      congrArg W (hYP p hp i)
    have hNear p (hp : p∈P) d :
        |cloudp p 0 d-cloudp p 1 d| ≤ 2*wideRadius d := by
      rw [(hData p hp 0).2.2.2,(hData p hp 1).2.2.2]
      exact ((Finset.mem_filter.mp (hPairs p hp)).2 d).trans
        (mul_le_mul_of_nonneg_left (hRadius d) (by norm_num))
    have hNearNarrow p (hp : p∈P) :
        |cloudp p 0 1-cloudp p 1 1| ≤ 1/(6*(K₀:ℝ)^2*Vscale) := by
      rw [(hData p hp 0).2.2.2,(hData p hp 1).2.2.2]
      have hn := (Finset.mem_filter.mp (hPairs p hp)).2 (1 : Fin 4)
      change |cloud p.1 1-cloud p.2 1| ≤ 2*(1/(12*(K₀:ℝ)^2*Vscale)) at hn
      convert hn using 1
      all_goals first | rfl | (field_simp; ring)
    have hYa := hY ab.1 (Finset.mem_product.mp hab).1
    have hYb := hY ab.2 (Finset.mem_product.mp hab).2
    have hAp i : M ≤ Ap i := by
      fin_cases i
      · exact hYa.2.1
      · exact hYb.2.1
    have hWpair i : (Ap i:ℝ)+Wp i ≤ 2*M := by
      fin_cases i
      · exact hYa.2.2.1
      · exact hYb.2.2.1
    let Fp := fun i u => (Tsrc/T)*Φ (yp i) u
    have hFp i : Expdb.IsApproximateModelPhaseFunction (Fp i) σ 4 δ := by
      fin_cases i
      · exact hYa.2.2.2
      · exact hYb.2.2.2
    have hFpEq i : (fun w => T*Fp i (w/M))=fp i := by
      funext w
      dsimp only [Fp,fp,f, physicalFirstDifference]
      field_simp
    have hGeoA p (hp : p∈P) :
        N ≤ Nlen (ab.1,p.1.1.2) ∧ Nlen (ab.1,p.1.1.2) ≤ 3*N ∧
        round (z (ab.1,p.1.1.2))+(Nlen (ab.1,p.1.1.2):ℤ)=
          Z ab.1+(N:ℤ)*p.1.1.2+2*(N:ℤ) := by
      have hh := hgeometry p.1.1 (hS p hp 0)
      rw [←hPointA p hp] at hh
      exact hh
    have hGeoB p (hp : p∈P) :
        N ≤ Nlen (ab.2,p.2.1.2) ∧ Nlen (ab.2,p.2.1.2) ≤ 3*N ∧
        round (z (ab.2,p.2.1.2))+(Nlen (ab.2,p.2.1.2):ℤ)=
          Z ab.2+(N:ℤ)*p.2.1.2+2*(N:ℤ) := by
      have hh := hgeometry p.2.1 (hS p hp 1)
      rw [←hPointB p hp] at hh
      exact hh

    have hh := hboundFn Fp ab.1 ab.2 Uref Refs Gaps (Bselect:=Bselect)
      P Mat (fun p => gap p.1.1) Q K₀ N
      (fun n => z (ab.1,n)) (fun n => z (ab.2,n))
      (fun n => Nlen (ab.1,n)) (fun n => Nlen (ab.2,n)) (Z ab.1) (Z ab.2)
      rp vp pp (fun p => anchor p.1.1) e r vRef s
      (δ:=δ) (M:=M) (R:=R) (base:=0) (Bcut:=Bcut)
      (lambda:=lambda) (Uband:=Uband) (θ:=θ) Ap (W:=Wp)
      hPhase
      (fun p hp => by
        change 0 ≤ xp p 0-(Ap 0:ℝ)
        rw [hLoc p hp 0]
        exact le_of_lt (lt_trans (by norm_num) (hx _ (hS p hp 0)).1))
      (fun p hp => hgapMem _ (hS p hp 0))
      hGeoA hGeoB hδ hFp hT hM
      (Nat.cast_pos.mpr hN) hR hRM hQ hscale hmesh hAp hWpair
      (fun p hp i => by
        change xp p i-(Ap i:ℝ)∈Ioo (1/2:ℝ) (Wp i-1/2)
        rw [hLoc p hp i,hWp p hp i]
        exact hx _ (hS p hp i))
      (fun p hp i => hden _ (hS p hp i))
      hlambda hUband hUbandCap hθ hθmax
      (fun p hp i => hcurv _ (hS p hp i))
      (fun p hp i => hinv _ (hS p hp i))
      hchart horientation hBcut hs hrefSet hparentSet hsep
      (fun p hp i => by
        change xp p i-(Ap i:ℝ)-(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (Wp i-1/2)
        rw [hLoc p hp i,hWp p hp i]
        exact hwideL _ (hS p hp i))
      (fun p hp i => by
        change xp p i-(Ap i:ℝ)+(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (Wp i-1/2)
        rw [hLoc p hp i,hWp p hp i]
        exact hwideU _ (hS p hp i))
      hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
      hselectedUpper hscaleTen (fun p hp => hfamilyGap _ (hS p hp 0))
      (fun p hp => (hLargeData key p (hLarge p hp)).1)
      (fun p hp => (hLargeData key p (hLarge p hp)).2.2)
      (fun p hp => (hLargeData key p (hLarge p hp)).2.1)
      hgap hQN hNsqM hUR hrHeight hsHeight heHeight hvHeight
      (fun p hp => by
        have he := congrArg Prod.fst ((hColor p hp 0).trans (hColor p hp 1).symm)
        change (⌊((rp p 0).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
            ⌊((rp p 0).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)=
          (⌊((rp p 1).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
            ⌊((rp p 1).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋) at he
        simpa only [rationalSourceBin,mul_div_assoc] using he)
      (fun p hp i => by
        change iteratedDeriv 2 (fun w => T*Fp i (w/M)) (xp p i)/2=(rp p i:ℝ)
        rw [hFpEq]
        rw [(hData p hp i).2.1 2]
        exact hlevel _ (hS p hp i))
      (fun p hp => by
        simp only [hFpEq]
        change bp p 0-crp p 0=bp p 1-crp p 1
        rw [(hData p hp 0).2.2.1,(hData p hp 1).2.2.1]
        exact congrArg Prod.snd ((hColor p hp 0).trans (hColor p hp 1).symm))
      (fun p hp a => by simpa only [hFpEq] using hNear p hp a)
      (fun p hp => by simpa only [hFpEq] using hNearNarrow p hp)
      hsmall hNR hRN hNcube hminscale
      (fun p hp => (hMatData p (hPairData key p (hPairs p hp)).2.2.2.2).1)
      (fun p hp => (hMatData p (hPairData key p (hPairs p hp)).2.2.2.2).2.1)
      (fun p hp => (hMatData p (hPairData key p (hPairs p hp)).2.2.2.2).2.2.1)
      (fun p hp => (hMatData p (hPairData key p (hPairs p hp)).2.2.2.2).2.2.2)
      hNtwo
      (fun p hp i => by
        change xp p i-(Ap i:ℝ)-H∈Ioo (1/2:ℝ) (Wp i-1/2)
        rw [hLoc p hp i,hWp p hp i]
        exact hLeft _ (hS p hp i))
      (fun p hp i => by
        change xp p i-(Ap i:ℝ)+H∈Ioo (1/2:ℝ) (Wp i-1/2)
        rw [hLoc p hp i,hWp p hp i]
        exact hRight _ (hS p hp i))
      (fun p hp => hanchor _ (hS p hp 0))
      (fun p hp => hcut _ (hS p hp 0))
      (fun p hp => hcount _ (hS p hp 0))
      hsize hD hΔ hBsize
    exact hh
  have hLargeMass key : Vscale*((Large key).card:ℝ) ≤ (Y.card:ℝ)^2*Klarge*T^εloss := by
    let phase := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
      (ij.1.1.1,ij.2.1.1)
    have hmaps : Set.MapsTo phase (Large key : Set _) (Y ×ˢ Y : Finset _) := by
      intro ij hij
      have hd := hPairData key ij (Finset.mem_filter.mp hij).1
      exact Finset.mem_product.mpr
        ⟨Finset.mem_image_of_mem Prod.fst (Finset.mem_product.mp hd.1).1,
          Finset.mem_image_of_mem Prod.fst (Finset.mem_product.mp hd.2.1).1⟩
    have heq ab : (Large key).filter (fun ij => phase ij=ab)=phaseFiber key ab := by
      rcases ab with ⟨a,b⟩
      ext ij
      simp only [phaseFiber,Finset.mem_filter,phase,Prod.mk.injEq]
    have hcards : ((Large key).card:ℝ)=
        ∑ ab∈Y ×ˢ Y, ((phaseFiber key ab).card:ℝ) := by
      have hh := Finset.card_eq_sum_card_fiberwise hmaps
      simp only [heq] at hh
      exact_mod_cast hh
    rw [hcards,Finset.mul_sum]
    calc
      _ ≤ ∑ _ab∈Y ×ˢ Y, Klarge*T^εloss :=
        Finset.sum_le_sum (fun ab hab => hphaseBound key ab hab)
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_product,nsmul_eq_mul,Nat.cast_mul]
        ring
  let smallMass := Dtype*(2+θ*(Uband+1/lambda))*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)
  have hPairCard key : ((Pairs key).card:ℝ) ≤ smallMass+((Large key).card:ℝ) := by
    have hcover : Pairs key ⊆ (Etype ∪ Etri) ∪ Large key := by
      intro ij hij
      have hp := hPairData key ij hij
      have hkey : narrow ij.1.1=narrow ij.2.1 :=
        congrArg Prod.fst (hp.2.2.1.trans hp.2.2.2.1.symm)
      by_cases htr : Mat ij 2=0 ∨ Mat ij 1=0
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨hsub hp.2.2.2.2,hkey,htr⟩))
      · have hn : Mat ij 1≠0 ∧ Mat ij 2≠0 := by tauto
        by_cases hact : |(Mat ij 2:ℝ)| *Uband ≤ L
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr
            ⟨hsub hp.2.2.2.2,hkey,Or.inr ⟨hn.1,hn.2,hact⟩⟩))
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hij,hn.1,hn.2,lt_of_not_ge hact⟩)
    have hh : ((Pairs key).card:ℝ) ≤ (Etype.card:ℝ)+(Etri.card:ℝ)+((Large key).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hcover).trans
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    have ht : (Etype.card:ℝ) ≤ Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep) := htype
    have hu : (Etri.card:ℝ) ≤
        Dtype*(1+θ*(Uband+1/lambda))*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep) := htri
    have hm : Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
        Dtype*(1+θ*(Uband+1/lambda))*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)=smallMass := by
      dsimp only [smallMass]
      ring
    exact hh.trans ((add_le_add (add_le_add ht hu) le_rfl).trans_eq (by rw [hm]))
  have hPairMass key : Vscale*((Pairs key).card:ℝ) ≤
      Vscale*smallMass+(Y.card:ℝ)^2*Klarge*T^εloss := by
    calc
      _ ≤ Vscale*(smallMass+((Large key).card:ℝ)) :=
        mul_le_mul_of_nonneg_left (hPairCard key) (zero_le_one.trans hVscale)
      _ = Vscale*smallMass+Vscale*((Large key).card:ℝ) := by ring
      _ ≤ _ := add_le_add le_rfl (hLargeMass key)
  have hCap : 0 ≤ Cap := (Nat.cast_nonneg _).trans hcard
  refine ⟨hcard,?_⟩
  intro k
  calc
    _ ≤ C*Vscale*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
        ∑ key∈V.image color, ((Fiber key).card:ℝ)^10*((Pairs key).card:ℝ) := hfourier k
    _ = C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
        ∑ key∈V.image color, ((Fiber key).card:ℝ)^10*(Vscale*((Pairs key).card:ℝ)) := by
      rw [show C*Vscale*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11=
        C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*Vscale by ring,mul_assoc,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro key _
      ring
    _ ≤ C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
        ∑ key∈V.image color, ((Fiber key).card:ℝ)^10*
          (Vscale*smallMass+(Y.card:ℝ)^2*Klarge*T^εloss) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun key _ =>
          mul_le_mul_of_nonneg_left (hPairMass key) (pow_nonneg (Nat.cast_nonneg _) 10)))
        (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (pow_nonneg hCap 11))
    _ = _ := by
      dsimp only [smallMass]
      simp only [mul_assoc]

public  theorem double_difference_source_completion_weight
    (Fsrc : ℝ → ℝ) {r s d y w c U σ δ Tsrc T M N R Q q A z : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hd : 0 < d)
    (hy : y∈Icc (1:ℝ) 2) (hprod : r*s=d*y)
    (hshift : r+s ≤ w) (hw : w ≤ 1/4) (hsmall : 2*U*w ≤ c/64)
    (hc : 0 < c) (hU : 0 < U) (hσ : 0 < σ)
    (hTsrc : 0 < Tsrc) (hT : 0 < T) (hMtwo : 2 ≤ M)
    (hN : 0 < N) (hR : 0 < R) (hQ : 0 < Q)
    (hQq : Q ≤ 2*q) (hNA : N ≤ A) (hz : z∈Icc M (2*M))
    (hscale : T*N*R^2=M^3)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hf : ∀ u, 0 < u → ContDiffAt ℝ ∞ Fsrc u)
    (hlower : ∀ u∈Icc (1/2:ℝ) 3, c ≤ iteratedDeriv 5 Fsrc u)
    (hjets : ∀ u∈Icc (1/2:ℝ) 3, ∀ n, 1 ≤ n → n ≤ 7 →
      |iteratedDeriv n Fsrc u| ≤ U) :
    let Φ := fun u => (Fsrc u-Fsrc (u+r)-Fsrc (u+s)+Fsrc (u+r+s))/d
    Expdb.IsApproximateModelPhaseFunction (fun u => (Tsrc/T)*Φ u) σ 2 δ →
    let f := fun v => Tsrc*Φ (v/M)
    let μ := iteratedDeriv 3 f (round z)/6
    0 < μ ∧
      c*modelPhaseThirdLower σ/(36*U*N*R^2) ≤ μ ∧
      Real.sqrt (2*q)/(q*Real.sqrt (μ*A)) ≤
        Real.sqrt ((144*U/(c*modelPhaseThirdLower σ))*(R^2/Q)) := by
  intro Φ hmodel f μ
  have hM : 0 < M := by linarith only [hMtwo]
  have hκ : 0 < modelPhaseThirdLower σ := modelPhaseThirdLower_pos hσ
  have hjet u (hu : u∈Icc (3/4:ℝ) (9/4)) :=
    double_difference_cubic_jet_bounds Fsrc hu hy hr hs hd hU hc
      hprod hshift hw hsmall hf hlower hjets
  have hreg u (hu : 0 < u) : ContDiffAt ℝ ∞ Φ u :=
    (hjet 1 (by norm_num)).1 u hu
  have hAmp : modelPhaseThirdLower σ*T/(3*U) ≤ Tsrc := by
    have hlow : modelPhaseThirdLower σ ≤
        iteratedDeriv 3 (fun u => (Tsrc/T)*Φ u) (3/2) := by
      simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
        (approximateModelPhase_thirdDeriv_bounds hσ hδ hmodel
          (by norm_num : (3/2:ℝ)∈Ioo (1:ℝ) 2)).1
    have hu : |iteratedDeriv 3 Φ (3/2)| ≤ 3*U :=
      (hjet (3/2) (by norm_num)).2.2.1
    rw [iteratedDeriv_const_mul_field] at hlow
    have hb := hlow.trans (mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans hu) (div_pos hTsrc hT).le)
    have hh : modelPhaseThirdLower σ*T ≤ Tsrc*(3*U) := by
      have he : (Tsrc/T)*(3*U)=Tsrc*(3*U)/T := by ring
      rw [he] at hb
      exact (le_div_iff₀ hT).mp hb
    exact (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ) < 3) hU)).mpr hh
  have hround := abs_le.mp (abs_sub_round z)
  have hzround : (0:ℝ) < round z := by linarith only [hround.2,hz.1,hMtwo]
  have hnorm : (round z:ℝ)/M∈Icc (3/4:ℝ) (9/4) := by
    constructor
    · apply (le_div_iff₀ hM).mpr
      linarith only [hround.2,hz.1,hMtwo]
    · apply (div_le_iff₀ hM).mpr
      linarith only [hround.1,hz.2,hMtwo]
  have hphysical : iteratedDeriv 3 f (round z)=
      Tsrc/M^3*iteratedDeriv 3 Φ ((round z:ℝ)/M) := by
    have ha := sargos_iteratedDeriv_comp_affine_local (f:=Φ)
      (l:=0) (r:=(round z:ℝ)+1) (c:=M⁻¹) (d:=0)
      (fun v hv => hreg _ (by
        simpa only [add_zero] using mul_pos (inv_pos.mpr hM) hv.1))
      (show (round z:ℝ)∈Ioo (0:ℝ) ((round z:ℝ)+1) from ⟨hzround,by linarith⟩) 3
    change iteratedDeriv 3 (fun v => Tsrc*Φ (v/M)) (round z)=_
    rw [iteratedDeriv_const_mul_field]
    have he : (fun v => Φ (v/M))=(fun v => Φ (M⁻¹*v+0)) := by
      funext v
      congr 1
      ring
    rw [he,ha]
    simp only [add_zero,inv_pow]
    rw [show M⁻¹*(round z:ℝ)=(round z:ℝ)/M by ring]
    ring
  let μ₀ := c*Tsrc/(12*M^3)
  have hμ₀ : 0 < μ₀ := by dsimp only [μ₀]; positivity
  have hμ : μ₀ ≤ μ := by
    calc
      μ₀ = (Tsrc/M^3)*(c/2)/6 := by dsimp only [μ₀]; ring
      _ ≤ (Tsrc/M^3)*iteratedDeriv 3 Φ ((round z:ℝ)/M)/6 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hjet _ hnorm).2.1 (by positivity)) (by norm_num)
      _ = μ := by dsimp only [μ]; rw [hphysical]
  have hμp : 0 < μ := hμ₀.trans_le hμ
  have hμphysical : c*modelPhaseThirdLower σ/(36*U*R^2) ≤ μ₀*N := by
    calc
      c*modelPhaseThirdLower σ/(36*U*R^2)=
          (c*N/(12*M^3))*(modelPhaseThirdLower σ*T/(3*U)) := by
        rw [←hscale]
        field_simp
        ring
      _ ≤ (c*N/(12*M^3))*Tsrc := mul_le_mul_of_nonneg_left hAmp (by positivity)
      _ = μ₀*N := by dsimp only [μ₀]; ring
  have hq : 0 < q := by linarith only [hQ,hQq]
  have hAp : 0 < A := hN.trans_le hNA
  have hμA : 0 < μ*A := mul_pos hμp hAp
  have hμN : μ₀*N ≤ μ*A := mul_le_mul hμ hNA hN.le hμp.le
  have hden := mul_pos hQ (mul_pos hμ₀ hN)
  have hright : 0 ≤ 4/(Q*(μ₀*N)) := div_nonneg (by norm_num) hden.le
  have hweight : Real.sqrt (2*q)/(q*Real.sqrt (μ*A)) ≤ Real.sqrt (4/(Q*(μ₀*N))) := by
    apply (sq_le_sq₀
      (div_nonneg (Real.sqrt_nonneg _) (mul_nonneg hq.le (Real.sqrt_nonneg _)))
      (Real.sqrt_nonneg _)).mp
    rw [div_pow,mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 2*q),
      Real.sq_sqrt hμA.le,Real.sq_sqrt hright]
    apply (div_le_div_iff₀ (mul_pos (pow_pos hq 2) hμA) hden).mpr
    have hm := mul_le_mul hQq hμN (mul_nonneg hμ₀.le hN.le) (by positivity : 0 ≤ 2*q)
    have hh := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2*q)
    nlinarith only [hh]
  have hμlower : c*modelPhaseThirdLower σ/(36*U*N*R^2) ≤ μ := by
    calc
      _ = (c*modelPhaseThirdLower σ/(36*U*R^2))/N := by ring
      _ ≤ (μ₀*N)/N := div_le_div_of_nonneg_right hμphysical hN.le
      _ = μ₀ := by field_simp
      _ ≤ μ := hμ
  refine ⟨hμp,hμlower,hweight.trans (Real.sqrt_le_sqrt ?_)⟩
  have hi := one_div_le_one_div_of_le
    (by positivity : 0 < c*modelPhaseThirdLower σ/(36*U*R^2)) hμphysical
  calc
    _ = (4/Q)*(1/(μ₀*N)) := by ring
    _ ≤ (4/Q)*(1/(c*modelPhaseThirdLower σ/(36*U*R^2))) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by field_simp; ring

-- Generated closures: source context is replayed in the next part.
end TaoTrudgianYang2025.HuxleyRationalPhase
end
end
