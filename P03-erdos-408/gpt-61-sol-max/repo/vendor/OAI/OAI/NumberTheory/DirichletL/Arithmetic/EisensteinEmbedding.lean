module
public import Mathlib.Tactic
import Batteries.Tactic.Alias

public import OAI.NumberTheory.DirichletL.ChineseRemainder.AdditiveCharacters
public import OAI.NumberTheory.DirichletL.GaussSum.FiniteFourier
public import OAI.NumberTheory.DirichletL.GaussSum.ChineseRemainder

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
 
open Filter Asymptotics MeasureTheory
open scoped Topology
open   Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
 

namespace EisensteinEmbedding

abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K

private instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

noncomputable def ζ  := IsCyclotomicExtension.zeta 3 ℚ K
noncomputable def pb  :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis

noncomputable def omega3  := ((-1 : ℂ) + (Real.sqrt 3 : ℝ) * Complex.I) / 2

theorem omega3_sq : omega3 ^ 2 + omega3 + 1 = 0 := by
  have hs : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs' : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by norm_cast
  have hquad : omega3 ^ 2 + omega3 + 1 =
      (3 + ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 * Complex.I ^ 2) / 4 := by
    unfold omega3
    ring
  simp_all

theorem omega3_im : omega3.im = Real.sqrt 3 / 2 := by
  simp [omega3]

theorem omega3_im_ne_zero : omega3.im ≠ 0 := by
  simp_all [omega3_im]

theorem lam_ne_zero (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    1 + 2 * w ≠ 0 := by solve_by_elim [_root_.SharedProofs.shared_lam_ne_zero]

theorem pb_minpoly : minpoly ℤ pb.gen =
    (Polynomial.X : Polynomial ℤ) ^ 2 + Polynomial.X + 1 := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have hgen : pb.gen = hζ.toInteger := by
    simpa only [pb] using hζ.integralPowerBasis_gen
  rw [hgen]
  calc
    minpoly ℤ (hζ.toInteger : O) =
        minpoly ℤ (hζ.toInteger : K) :=
          (NumberField.RingOfIntegers.minpoly_coe hζ.toInteger).symm
    _ = minpoly ℤ (IsCyclotomicExtension.zeta 3 ℚ K) := congrArg (minpoly ℤ) hζ.coe_toInteger
    _ = Polynomial.cyclotomic 3 ℤ :=
          (Polynomial.cyclotomic_eq_minpoly hζ (by decide)).symm
    _ = _ := Polynomial.cyclotomic_three ℤ

noncomputable def embedding (w : ℂ) (hw : w ^ 2 + w + 1 = 0)  :=
  (pb.lift w (by
    simp_all [pb_minpoly])).toRingHom

theorem embedding_gen  w   hw  :
    embedding w hw pb.gen = w := by
  exact pb.lift_gen w (by
    simp_all [pb_minpoly])

theorem pb_dim : pb.dim = 2 := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have hdim := hζ.integralPowerBasis_dim
  assumption

theorem exists_ab  x  : ∃ a b : ℤ, x = a + b * pb.gen := by
  let i0 : Fin pb.dim := ⟨0, by rw [pb_dim]; decide⟩
  let i1 : Fin pb.dim := ⟨1, by rw [pb_dim]; decide⟩
  let c := pb.basis.repr x
  have h := pb.basis.sum_repr x
  have huniv : (Finset.univ : Finset (Fin pb.dim)) = {i0, i1} := by
    grind [pb_dim]
  rw [huniv, Finset.sum_insert (by simp [i0, i1]), Finset.sum_singleton] at h
  refine ⟨c i0, c i1, ?_⟩
  aesop

section
variable (w : ℂ) (hw : w ^ 2 + w + 1 = 0)
include w hw

theorem embedding_apply_ab    
    (a b : ℤ) :
    embedding w hw (a + b * pb.gen : O) =
      (a : ℂ) + (b : ℂ) * w := by
  simp only [map_add, map_mul, map_intCast, embedding_gen]

theorem embedding_injective    
    (him : w.im ≠ 0) : Function.Injective (embedding w hw) := by
  intro x y hxy
  have hz : embedding w hw (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨a, b, hrepr⟩ := exists_ab (x - y)
  rw [hrepr, embedding_apply_ab] at hz
  have himz := congrArg Complex.im hz
  have hb : b = 0 := by
    simp only [Complex.add_im, Complex.intCast_im, zero_add,
      Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      zero_mul, add_zero, Complex.zero_im] at himz
    simp_all
  have ha : a = 0 := by
    simp_all
  have hzero : x - y = 0 := by rw [hrepr, ha, hb]; simp
  exact sub_eq_zero.mp hzero

theorem trace_period_on_ringOfIntegers
       
    (ψ : AddChar ℂ ℂ)  lam 
    (hperiod : ∀ a b : ℤ,
      ψ (((a : ℂ) + (b : ℂ) * w) / lam) = 1) :
    ∀ x : O, ψ (embedding w hw x / lam) = 1 := by
  intro x
  obtain ⟨a, b, hrepr⟩ := exists_ab x
  rw [hrepr, embedding_apply_ab]
  exact hperiod a b

end

end EisensteinEmbedding

namespace ConcreteTraceCRT

open EisensteinEmbedding IdealGaussCRT

noncomputable def eisEmbedding  := embedding omega3 omega3_sq

theorem eisEmbedding_injective : Function.Injective eisEmbedding :=
  embedding_injective omega3 omega3_sq omega3_im_ne_zero

theorem eisEmbedding_ne_zero  {a}  (ha : a ≠ 0) : eisEmbedding a ≠ 0 := by
  intro h
  exact ha (eisEmbedding_injective (by simpa using h))

noncomputable def eisLam  := 1 + 2 * omega3

theorem eisLam_ne_zero : eisLam ≠ 0 := lam_ne_zero omega3 omega3_sq

theorem eisPeriod (ψ : AddChar ℂ ℂ)
    (hperiod : ∀ a b : ℤ,
      ψ (((a : ℂ) + (b : ℂ) * omega3) / eisLam) = 1) :
    ∀ x : O, ψ (eisEmbedding x / eisLam) = 1 :=
  trace_period_on_ringOfIntegers omega3 omega3_sq ψ eisLam hperiod

def coordinateSubring : Subring ℂ where
  carrier := {z | ∃ a b : ℤ, z = (a : ℂ) + (b : ℂ) * omega3}
  zero_mem' := ⟨0, 0, by simp⟩
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a + c, b + d, ?_⟩
    push_cast
    ring
  neg_mem' := by
    rintro x ⟨a, b, rfl⟩
    refine ⟨-a, -b, ?_⟩
    push_cast
    ring
  mul_mem' := by
    rintro x y ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a * c - b * d, a * d + b * c - b * d, ?_⟩
    grind [omega3_sq]

noncomputable def toCoordinateSubring  :=
  eisEmbedding.codRestrict coordinateSubring (by
    intro x
    obtain ⟨a, b, hrepr⟩ := exists_ab x
    rw [hrepr]
    solve_by_elim [omega3, omega3_sq, O, embedding_apply_ab])

theorem toCoordinateSubring_surjective : Function.Surjective toCoordinateSubring := by
  rintro ⟨z, a, b, hz⟩
  refine ⟨(a + b * pb.gen : O), ?_⟩
  apply Subtype.ext
  change eisEmbedding (a + b * pb.gen : O) = z
  change embedding omega3 omega3_sq (a + b * pb.gen : O) = z
  rw [embedding_apply_ab]
  exact hz.symm

noncomputable def eisTraceModChar
    (ψ : AddChar ℂ ℂ)
    (hperiod : ∀ a b : ℤ,
      ψ (((a : ℂ) + (b : ℂ) * omega3) / eisLam) = 1)
    (a : O) (ha : a ≠ 0)  :=
  traceModChar eisEmbedding ψ eisLam a
    (eisEmbedding_ne_zero ha) eisLam_ne_zero (eisPeriod ψ hperiod)

noncomputable def eisTraceProdChar
    (ψ : AddChar ℂ ℂ)
    (hperiod : ∀ a b : ℤ,
      ψ (((a : ℂ) + (b : ℂ) * omega3) / eisLam) = 1)
    (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)  :=
  traceProdChar eisEmbedding ψ eisLam a b
    (eisEmbedding_ne_zero ha) (eisEmbedding_ne_zero hb)
    eisLam_ne_zero (eisPeriod ψ hperiod)

theorem gauss_sum_actual_O
     ψ 
     hperiod 
     a b   ha   hb 
    (hcop : IsCoprime (Ideal.span {a}) (Ideal.span {b}))
    [Fintype (O ⧸ (Ideal.span {a}) * (Ideal.span {b}))]
    [Fintype (O ⧸ Ideal.span {a})]
    [Fintype (O ⧸ Ideal.span {b})]
     χa 
     χb  :
    (∑ x : O ⧸ (Ideal.span {a}) * (Ideal.span {b}),
      χa (Ideal.Quotient.factor
        (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
      χb (Ideal.Quotient.factor
        (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
      eisTraceProdChar ψ hperiod a b ha hb x) =
      χa (Ideal.Quotient.mk (Ideal.span {a}) b) *
      χb (Ideal.Quotient.mk (Ideal.span {b}) a) *
      gaussSum χa (eisTraceModChar ψ hperiod a ha) *
      gaussSum χb (eisTraceModChar ψ hperiod b hb) := id (OAI.IdealGaussCRT.gauss_sum_trace_crt_of_coprime OAI.ConcreteTraceCRT.eisEmbedding ψ OAI.ConcreteTraceCRT.eisLam a b hcop (OAI.ConcreteTraceCRT.eisEmbedding_ne_zero ha) (OAI.ConcreteTraceCRT.eisEmbedding_ne_zero hb) OAI.ConcreteTraceCRT.eisLam_ne_zero (OAI.ConcreteTraceCRT.eisPeriod ψ hperiod) χa χb)

theorem finite_quotient_span {a : O} (ha : a ≠ 0) :
    Finite (O ⧸ Ideal.span {a}) := Ring.HasFiniteQuotients.finiteQuotient fun h => ha (Ideal.span_singleton_eq_bot.mp h)

theorem finite_quotient_product {a b : O} (ha : a ≠ 0) (hb : b ≠ 0) :
    Finite (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := by
  apply Ring.HasFiniteQuotients.finiteQuotient
  simp_all

end ConcreteTraceCRT

namespace ConcreteBreveE

open EisensteinEmbedding ConcreteTraceCRT

theorem breveE_period_coordinates :
    ∀ c d : ℤ,
      ShortDraftTrace.breveE
        (((c : ℂ) + (d : ℂ) * omega3) / eisLam) = 1 := fun c d => id (OAI.ShortDraftTrace.breveE_period_lam c d)

end ConcreteBreveE

namespace ActualEisensteinCubic

theorem eisEmbedding_conjO  x  :
    ConcreteTraceCRT.eisEmbedding (conjO x) =
      star (ConcreteTraceCRT.eisEmbedding x) := by
  let ι := ConcreteTraceCRT.eisEmbedding
  let z := ι omega
  have hz3 : z ^ 3 = 1 := by
    change ι omega ^ 3 = 1
    rw [← map_pow, omega_primitive.pow_eq_one, map_one]
  have hz0 : z ≠ 0 := by
    aesop
  have hznorm : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz3 (by decide)
  have hzstar : star z = z ^ 2 := by
    apply mul_left_cancel₀ hz0
    calc
      z * star z = 1 := by rw [← starRingEnd_apply, Complex.mul_conj', hznorm]; norm_num
      _ = z * z ^ 2 := by rw [← pow_succ', hz3]
  have hhom : ι.comp conjO.toRingHom = (starRingEnd ℂ).comp ι := by
    apply RingHom.toIntAlgHom_injective
    apply (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis.algHom_ext
    rw [(IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis_gen]
    change ι (conjO omega) = star (ι omega)
    rw [conjO_omega, map_pow]
    exact hzstar.symm
  have hx := congrArg (fun f : O →+* ℂ => f x) hhom
  exact hx

theorem cubicGauss_normalized_cube_eis (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P)  p  (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1)
     ψ  (hψ : ψ.IsPrimitive) :
    (gaussSum ((cubicChar P hgood).ringHomComp ConcreteTraceCRT.eisEmbedding) ψ /
      (‖ConcreteTraceCRT.eisEmbedding p‖ : ℂ)) ^ 3 =
      -(ConcreteTraceCRT.eisEmbedding p) /
        (‖ConcreteTraceCRT.eisEmbedding p‖ : ℂ) := by
  let z := ConcreteTraceCRT.eisEmbedding p
  let g := gaussSum ((cubicChar P hgood).ringHomComp
    ConcreteTraceCRT.eisEmbedding) ψ
  have hnormO := primary_generator_mul_conj_eq_card P hgood p hP hprimary
  have hnormC := congrArg ConcreteTraceCRT.eisEmbedding hnormO
  rw [map_mul, eisEmbedding_conjO, map_natCast] at hnormC
  have hq : (Nat.card (O ⧸ P) : ℂ) = (‖z‖ : ℂ) ^ 2 := by
    simpa only [z, ← starRingEnd_apply, Complex.mul_conj'] using hnormC.symm
  have hqne : (Nat.card (O ⧸ P) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hn0 : (‖z‖ : ℂ) ≠ 0 := by
    aesop
  have hg : g ^ 3 = -z * (Nat.card (O ⧸ P) : ℂ) :=
    cubicGauss_cube ConcreteTraceCRT.eisEmbedding
      ConcreteTraceCRT.eisEmbedding_injective P hgood p hP hprimary ψ hψ
  grind

 

 

noncomputable def canonicalSextic (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : MulChar (O ⧸ P) ℂ :=
  (sexticChar P hgood).ringHomComp ConcreteTraceCRT.eisEmbedding

section
variable (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
include P hgood

theorem canonicalSextic_pow_six    
      : canonicalSextic P hgood ^ 6 = 1 := by
  change ((sexticChar P hgood).ringHomComp ConcreteTraceCRT.eisEmbedding) ^ 6 = 1
  rw [MulChar.ringHomComp_pow, (sexticChar_powers P hgood).2.2,
    MulChar.ringHomComp_one]

section
variable (hchar : ringChar (O ⧸ P) ≠ 2)
include hchar

theorem canonicalSextic_pow_ne_one    
       
     {j}  (hj0 : j ≠ 0) (hj6 : j < 6) :
    canonicalSextic P hgood ^ j ≠ 1 := by
  change ((sexticChar P hgood).ringHomComp ConcreteTraceCRT.eisEmbedding) ^ j ≠ 1
  rw [MulChar.ringHomComp_pow]
  apply (MulChar.ringHomComp_ne_one_iff
    ConcreteTraceCRT.eisEmbedding_injective).2
  apply pow_ne_one_of_lt_orderOf hj0
  rwa [sexticChar_order P hgood hchar]

section
variable (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ ≠ 1) (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P)
include ψ hψ σ ε x

theorem canonical_A5_jfour    
       
       
        :
    let χ := canonicalSextic P hgood
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ 4) t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      (((χ⁻¹) ^ 2) σ) *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        gaussSum (χ ^ 4) (ψ.mulShift (-1)) *
        (if ε * x = 0 then (Fintype.card (O ⧸ P)ˣ : ℂ) else -1)) := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ := canonicalSextic P hgood
  have hχ4 : χ ^ 4 ≠ 1 := canonicalSextic_pow_ne_one P hgood hchar
    (by decide : (4:ℕ) ≠ 0) (by decide : (4:ℕ) < 6)
  have hχ6 : χ ^ 6 = 1 := canonicalSextic_pow_six P hgood
  have hsum :
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ 4) t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      (((χ⁻¹) ^ 2) σ) * gaussSum (χ ^ 4) (ψ.mulShift (-1)) *
        (∑ h : (O ⧸ P)ˣ,
          (((χ⁻¹) ^ 4 * (χ⁻¹) ^ 2) h) *
            ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [ShortDraftLocal.nontrivial_fourier_coefficient (χ ^ 4) ψ hχ4 h,
      map_mul]
    simp only [inv_pow, MulChar.mul_apply]
    ring
  dsimp
  rw [hsum, ShortDraftLocal.sextic_fourth_mask χ ψ hχ6 hψ (ε * x)]
  ring

theorem canonical_A5_jzero_active    
       
       
        :
    let χ := canonicalSextic P hgood
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ 0) t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      -(((χ⁻¹) ^ 2) σ) *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        ((χ ^ 2)⁻¹ ε * gaussSum (χ ^ 2) ψ * (χ ^ 2)⁻¹ x)) := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ := canonicalSextic P hgood
  have hχ2 : χ ^ 2 ≠ 1 := canonicalSextic_pow_ne_one P hgood hchar
    (by decide : (2:ℕ) ≠ 0) (by decide : (2:ℕ) < 6)
  have hsum :
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ 0) t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      -(((χ⁻¹) ^ 2) σ) *
        (∑ h : (O ⧸ P)ˣ,
          ((χ⁻¹) ^ 2) (h : O ⧸ P) *
            ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    have hh : (h : O ⧸ P) ≠ 0 := Units.ne_zero h
    rw [pow_zero, ShortDraftLocal.trivial_fourier_coefficient ψ hψ h,
      ite_eq_right hh, map_mul]
    ring
  dsimp
  rw [hsum, ShortDraftLocal.active_zero_local_row χ ψ hχ2 ε x]
  ring

end

end

end

end ActualEisensteinCubic

namespace PrimitiveTrace

 
open scoped ComplexConjugate
open EisensteinEmbedding ConcreteTraceCRT

private theorem complex_exp_trace_integer  {t} 
    (ht : Complex.exp (2 * Real.pi * Complex.I * t) = 1) :
    ∃ n : ℤ, t = n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp ht
  refine ⟨n, ?_⟩
  have hnonzero : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp_all
  grind

public alias _root_.SharedProofs.complex_exp_trace_integer := complex_exp_trace_integer


private theorem phase_integer  {z} 
    (hz : ShortDraftTrace.breveE (z / eisLam) = 1) :
    ∃ n : ℤ, z / eisLam + conj (z / eisLam) = n := OAI.PrimitiveTrace.complex_exp_trace_integer hz




private theorem omega_conj : conj omega3 = omega3 ^ 2 := by
  have hs : omega3 ^ 2 = -omega3 - 1 := by
    linear_combination omega3_sq
  rw [hs]
  unfold omega3
  simp only [map_div₀, map_add, map_neg, map_one, map_mul,
    Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring




private theorem reconstruction  z  :
    z = (z / eisLam + conj (z / eisLam)) +
      (omega3 * z / eisLam + conj (omega3 * z / eisLam)) +
      (z / eisLam + conj (z / eisLam)) * omega3 := by
  grind [omega3_sq, eisLam, eisLam_ne_zero, omega_conj]




private theorem in_coordinate_lattice_of_two_phases  z 
    (hz : ShortDraftTrace.breveE (z / eisLam) = 1)
    (hwz : ShortDraftTrace.breveE (omega3 * z / eisLam) = 1) :
    z ∈ coordinateSubring := by
  obtain ⟨b, hb⟩ := phase_integer hz
  obtain ⟨c, hc⟩ := phase_integer hwz
  change ∃ a b : ℤ, z = (a : ℂ) + (b : ℂ) * omega3
  refine ⟨b + c, b, ?_⟩
  calc
    z = (z / eisLam + conj (z / eisLam)) +
      (omega3 * z / eisLam + conj (omega3 * z / eisLam)) +
      (z / eisLam + conj (z / eisLam)) * omega3 := reconstruction z
    _ = ((b + c : ℤ) : ℂ) + (b : ℂ) * omega3 := by
      rw [hb, hc]
      push_cast
      ring

public alias _root_.SharedProofs.in_coordinate_lattice_of_two_phases := in_coordinate_lattice_of_two_phases


section
variable (P : Ideal O) [P.IsMaximal] (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0)
include P p hP hp

theorem eisTraceModChar_breveE_ne_one
         
        :
    eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp ≠ 1 := by
  intro hψ
  let ι := eisEmbedding
  let z : ℂ := (ι p)⁻¹
  have hpι : ι p ≠ 0 := eisEmbedding_ne_zero hp
  have hbase1 : ∀ x : O,
      ShortDraftTrace.breveE (ι x / (ι p * eisLam)) = 1 := by
    intro x
    have hpoint := congrArg
      (fun f : AddChar (O ⧸ Ideal.span {p}) ℂ =>
        f (Ideal.Quotient.mk (Ideal.span {p}) x)) hψ
    simpa only [eisTraceModChar, IdealGaussCRT.traceModChar_mk,
      AddChar.one_apply] using hpoint
  have h1 : ShortDraftTrace.breveE (z / eisLam) = 1 := by
    convert hbase1 1 using 1 ; dsimp [z, ι] ; simp ; field_simp
  have hw : ShortDraftTrace.breveE (omega3 * z / eisLam) = 1 := by
    convert hbase1 pb.gen using 1
    · rw [show ι pb.gen = omega3 from embedding_gen omega3 omega3_sq]
      dsimp [z]
      field_simp
  have hz := in_coordinate_lattice_of_two_phases z h1 hw
  obtain ⟨q, hq⟩ := toCoordinateSubring_surjective ⟨z, hz⟩
  have hιq : ι q = z := congrArg Subtype.val hq
  have hpq : p * q = 1 := by
    apply eisEmbedding_injective
    rw [map_mul, map_one, hιq]
    dsimp [z]
    exact mul_inv_cancel₀ hpι
  have hunit : IsUnit p := isUnit_iff_dvd_one.mpr ⟨q, hpq.symm⟩
  have htop : P = ⊤ := by
    rw [hP]
    exact Ideal.span_singleton_eq_top.mpr hunit
  exact (inferInstance : P.IsMaximal).ne_top htop

theorem eisTraceModChar_breveE_primitive
         
        :
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp).IsPrimitive := by
  have : (Ideal.span {p}).IsMaximal := hP ▸ inferInstance
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  exact AddChar.IsPrimitive.of_ne_one
    (eisTraceModChar_breveE_ne_one P p hP hp)

end

end PrimitiveTrace

end

end OAI
