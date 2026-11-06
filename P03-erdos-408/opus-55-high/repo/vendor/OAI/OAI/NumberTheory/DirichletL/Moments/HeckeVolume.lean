module

public import OAI.NumberTheory.DirichletL.Moments.MaskedVolume
public import OAI.NumberTheory.DirichletL.CenteredExceptionalProfile
public import OAI.NumberTheory.DirichletL.Hecke.Euler
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalPair

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap

namespace SevenEighths.CenteredMomentHeckeVolume
open HeckeFamily CompletedGauss ConcreteTraceCRT EisensteinSchwartzPoisson
open CanonicalQuadraticSieve QuadraticInitialBound
open IdealMobiusDivisorSum UniqueFactorizationMonoid CenteredMomentMask
open PrimaryIdealUnitReindex (GoodIdeal)
open CubicEisenstein (PrimaryLower primaryLowerIdealEquiv)

def primaryCoefficient (ψ : Character) : Ideal ActualEisensteinCubic.O →* ℂ where
  toFun I := if primaryGenerator I=0 then 0 else idealCoeff ψ I
  map_one' := by simp only [primaryGenerator_one,one_ne_zero,ite_false,map_one]
  map_mul' := by
    intro I J
    simp only [primaryGenerator_mul,map_mul]
    by_cases hI : primaryGenerator I=0 <;> by_cases hJ : primaryGenerator J=0 <;>
      simp only [hI,hJ,mul_eq_zero,or_false,ite_true,ite_false,zero_mul,mul_zero]

theorem primaryCoefficient_good (ψ : Character) (I : Ideal ActualEisensteinCubic.O) (hI : primaryGenerator I ≠ 0) :
    primaryCoefficient ψ I = elementCoeff ψ (primaryGenerator I) := by
  change (if primaryGenerator I=0 then 0 else idealCoeff ψ I)=_
  rw [ite_eq_right hI]
  conv_lhs => rw [← (primaryGenerator_spec I hI).1,idealCoeff_span ψ hI]

theorem primaryCoefficient_norm (ψ : Character) (I : Ideal ActualEisensteinCubic.O) : ‖primaryCoefficient ψ I‖ ≤ 1 := by
  change ‖if primaryGenerator I=0 then 0 else idealCoeff ψ I‖ ≤ 1
  split_ifs
  · simp
  · exact idealCoeff_norm_le_one ψ I

def periodicValue (c : ActualEisensteinCubic.O) (ψ : Character) (r : ActualEisensteinCubic.O ⧸ Ideal.span {c}) : ℂ :=
  if (3:ActualEisensteinCubic.O) ∣ Quotient.out r-1 then elementCoeff ψ (Quotient.out r) else 0

theorem periodicValue_mk (c : ActualEisensteinCubic.O) (h3 : (3:ActualEisensteinCubic.O) ∣ c) (ψ : Character)
    (hmod : (Ideal.span {c} : Ideal ActualEisensteinCubic.O) ≤ ψ.modulus) (x : ActualEisensteinCubic.O) :
    periodicValue c ψ (Ideal.Quotient.mk (Ideal.span {c}) x) =
      if (3:ActualEisensteinCubic.O) ∣ x-1 then elementCoeff ψ x else 0 := by
  have hc : c ∣ Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) x)-x :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (by simp))
  have hd := h3.trans hc
  have hprimary : (3:ActualEisensteinCubic.O) ∣ Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) x)-1 ↔ (3:ActualEisensteinCubic.O) ∣ x-1 := by
    constructor
    · intro h; convert dvd_sub h hd using 1 ; ring
    · intro h; convert dvd_add hd h using 1 ; ring
  have hres : Ideal.Quotient.mk ψ.modulus (Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) x)) =
      Ideal.Quotient.mk ψ.modulus x :=
    Ideal.Quotient.eq.mpr (hmod (Ideal.mem_span_singleton.mpr hc))
  simp only [periodicValue,hprimary,elementCoeff,hres]

theorem periodicValue_norm (c : ActualEisensteinCubic.O) (ψ : Character) (r : ActualEisensteinCubic.O ⧸ Ideal.span {c}) :
    ‖periodicValue c ψ r‖ ≤ 1 := by
  let : Finite (ActualEisensteinCubic.O ⧸ ψ.modulus) := Ring.HasFiniteQuotients.finiteQuotient ψ.modulus_ne_bot
  let : Fintype (ActualEisensteinCubic.O ⧸ ψ.modulus) := Fintype.ofFinite _
  unfold periodicValue
  split_ifs
  · exact norm_finite_character_le_one ψ.residue _
  simp

theorem lattice_eq_ideal_sum (c : ActualEisensteinCubic.O) (h3 : (3:ActualEisensteinCubic.O) ∣ c) (ψ : Character)
    (hmod : (Ideal.span {c} : Ideal ActualEisensteinCubic.O) ≤ ψ.modulus) (W : ℝ → ℂ) (X : ℝ) :
    (∑' z : ActualEisensteinCubic.O, periodicValue c ψ (Ideal.Quotient.mk (Ideal.span {c}) z)*W (‖eisEmbedding z‖^2/X)) =
      ∑' I : Ideal ActualEisensteinCubic.O, primaryCoefficient ψ I*W ((Ideal.absNorm I:ℝ)/X) := by
  let f : ActualEisensteinCubic.O → ℂ := fun z => elementCoeff ψ z*W (‖eisEmbedding z‖^2/X)
  have hleft : (∑' z : ActualEisensteinCubic.O, periodicValue c ψ (Ideal.Quotient.mk (Ideal.span {c}) z)*W (‖eisEmbedding z‖^2/X)) =
      ∑' z : PrimaryLower, f z.val := by
    calc
      _ = ∑' z : ActualEisensteinCubic.O, ({z : ActualEisensteinCubic.O | (3:ActualEisensteinCubic.O) ∣ z-1} : Set ActualEisensteinCubic.O).indicator f z := by
        apply tsum_congr
        intro z
        rw [periodicValue_mk c h3 ψ hmod z]
        simp only [Set.indicator_apply,Set.mem_ofPred_eq,f]
        simp
      _ = _ := (tsum_subtype {z : ActualEisensteinCubic.O | (3:ActualEisensteinCubic.O) ∣ z-1} f).symm
  have hideal : (∑' I : GoodIdeal, primaryCoefficient ψ I.val*W ((Ideal.absNorm I.val:ℝ)/X)) =
      ∑' I : Ideal ActualEisensteinCubic.O, primaryCoefficient ψ I*W ((Ideal.absNorm I:ℝ)/X) := by
    apply tsum_subtype_eq_of_support_subset (s := {I : Ideal ActualEisensteinCubic.O | primaryGenerator I ≠ 0})
      (f := fun I : Ideal ActualEisensteinCubic.O => primaryCoefficient ψ I*W ((Ideal.absNorm I:ℝ)/X))
    intro I hI
    change primaryGenerator I ≠ 0
    intro hz
    apply hI
    simp only [primaryCoefficient,MonoidHom.coe_mk,OneHom.coe_mk,hz,ite_true,zero_mul]
  rw [hleft,← hideal,← primaryLowerIdealEquiv.symm.tsum_eq]
  apply tsum_congr
  intro I
  change elementCoeff ψ (primaryGenerator I.val)*W (‖eisEmbedding (primaryGenerator I.val)‖^2/X)=_
  rw [primaryGenerator_norm_sq I.val I.property,primaryCoefficient_good ψ I.val I.property]

theorem fixed_period_volume (c : ActualEisensteinCubic.O) (hc : c ≠ 0) (h3 : (3:ActualEisensteinCubic.O) ∣ c)
    (ψ : Character) (hmod : (Ideal.span {c} : Ideal ActualEisensteinCubic.O) ≤ ψ.modulus)
    (W : 𝓢(ℝ,ℂ)) (X : ℝ) (hX : 0 < X) :
    letI : Finite (ActualEisensteinCubic.O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    ‖(∑' I : Ideal ActualEisensteinCubic.O, primaryCoefficient ψ I*W ((Ideal.absNorm I:ℝ)/X)) -
      (X/‖eisEmbedding c‖^2:ℝ) • ((∑ r : ActualEisensteinCubic.O ⧸ Ideal.span {c}, periodicValue c ψ r)*paperRadialFourier W 0)‖ ≤
      (Fintype.card (ActualEisensteinCubic.O ⧸ Ideal.span {c}):ℝ)*pvControl W := by
  let := finite_quotient_span hc
  let : Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  rw [← lattice_eq_ideal_sum c h3 ψ hmod W X]
  have h := CenteredMomentLattice.periodic_lattice_volume_error W X hX c hc (periodicValue c ψ)
  exact h.trans (mul_le_mul_of_nonneg_right (by
    calc
      _ ≤ ∑ _r : ActualEisensteinCubic.O ⧸ Ideal.span {c}, (1:ℝ) := Finset.sum_le_sum (fun r hr => periodicValue_norm c ψ r)
      _ = _ := by simp) (pvControl_nonneg W))

theorem masked_hecke_volume
    (c : ActualEisensteinCubic.O) (hc : c ≠ 0) (h3 : (3 : ActualEisensteinCubic.O) ∣ c)
    (ψ : Character) (hmod : (Ideal.span {c} : Ideal ActualEisensteinCubic.O) ≤ ψ.modulus)
    (R : Ideal ActualEisensteinCubic.O) (hR : R ≠ 0) (W : 𝓢(ℝ, ℂ)) (b X : ℝ) (hX : 0 < X)
    (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Iic b) :
    letI : Finite (ActualEisensteinCubic.O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let Ψ := primaryCoefficient ψ
    let v := (1 / (‖eisEmbedding c‖ ^ 2 : ℂ)) *
      ((∑ r : ActualEisensteinCubic.O ⧸ Ideal.span {c}, periodicValue c ψ r) * paperRadialFourier W 0)
    ‖(∑' I : Ideal ActualEisensteinCubic.O, (if IsCoprime I R then (1 : ℂ) else 0) *
        (Ψ I * W ((Ideal.absNorm I : ℝ) / X))) -
      (X : ℂ) * (∑ D ∈ idealDivisors R, (moebius D : ℂ) * Ψ D / (Ideal.absNorm D : ℂ)) * v‖ ≤
      ((idealDivisors R).card : ℝ) *
        ((Fintype.card (ActualEisensteinCubic.O ⧸ Ideal.span {c}) : ℝ) * pvControl W) := by
  classical
  let : Finite (ActualEisensteinCubic.O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let Ψ := primaryCoefficient ψ
  let v := (1 / (‖eisEmbedding c‖ ^ 2 : ℂ)) *
    ((∑ r : ActualEisensteinCubic.O ⧸ Ideal.span {c}, periodicValue c ψ r) * paperRadialFourier W 0)
  let B := (Fintype.card (ActualEisensteinCubic.O ⧸ Ideal.span {c}) : ℝ) * pvControl W
  let L : ℝ → ℂ := fun Y => ∑' I : Ideal ActualEisensteinCubic.O, Ψ I * W ((Ideal.absNorm I : ℝ) / Y)
  have hB : 0 ≤ B := mul_nonneg (Nat.cast_nonneg _) (pvControl_nonneg W)
  have hnD (D : Ideal ActualEisensteinCubic.O) (hD : D ∈ idealDivisors R) : 0 < (Ideal.absNorm D : ℝ) := by
    have hD0 : D ≠ 0 := ne_zero_of_dvd_ne_zero hR ((mem_idealDivisors hR).mp hD)
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hD0 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hsingle (D : Ideal ActualEisensteinCubic.O) (hD : D ∈ idealDivisors R) :
      ‖L (X / Ideal.absNorm D) - ((X / Ideal.absNorm D : ℝ) : ℂ) * v‖ ≤ B := by
    have h := fixed_period_volume c hc h3 ψ hmod W
      (X / Ideal.absNorm D) (div_pos hX (by grind))
    convert h using 1
    congr 1
    dsimp only [v]
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]
    ring
  have hcoef (D : Ideal ActualEisensteinCubic.O) : ‖(moebius D : ℂ) * Ψ D‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (norm_ideal_moebius_le_one D)
      (primaryCoefficient_norm ψ D) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have heq :
      (∑' I : Ideal ActualEisensteinCubic.O, (if IsCoprime I R then (1 : ℂ) else 0) *
        (Ψ I * W ((Ideal.absNorm I : ℝ) / X))) -
        (X : ℂ) * (∑ D ∈ idealDivisors R, (moebius D : ℂ) * Ψ D / (Ideal.absNorm D : ℂ)) * v =
      ∑ D ∈ idealDivisors R, ((moebius D : ℂ) * Ψ D) *
        (L (X / Ideal.absNorm D) - ((X / Ideal.absNorm D : ℝ) : ℂ) * v) := by
    rw [masked_plain_ideal_sum R hR Ψ W b X hX hs]
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro D _
    simp only [L, Complex.ofReal_div, Complex.ofReal_natCast]
    ring
  change ‖_ - (X : ℂ) * _ * v‖ ≤ ((idealDivisors R).card : ℝ) * B
  rw [heq]
  calc
    _ ≤ ∑ D ∈ idealDivisors R, ‖((moebius D : ℂ) * Ψ D) *
        (L (X / Ideal.absNorm D) - ((X / Ideal.absNorm D : ℝ) : ℂ) * v)‖ := norm_sum_le _ _
    _ ≤ ∑ _D ∈ idealDivisors R, B := by
      apply Finset.sum_le_sum
      intro D hD
      rw [norm_mul]
      exact (mul_le_mul (hcoef D) (by grind) (norm_nonneg _) zero_le_one).trans_eq (one_mul B)
    _ = _ := by simp

def fixedPeriod (Q : Ideal ActualEisensteinCubic.O) : ActualEisensteinCubic.O := 3*ConcretePrimeRowBridge.idealGenerator Q

theorem fixedPeriod_ne_zero (Q : Ideal ActualEisensteinCubic.O) (hQ : Q ≠ 0) : fixedPeriod Q ≠ 0 :=
  mul_ne_zero (by norm_num) (ConcretePrimeRowBridge.idealGenerator_ne_zero Q hQ)

theorem fixedPeriod_three (Q : Ideal ActualEisensteinCubic.O) : (3:ActualEisensteinCubic.O) ∣ fixedPeriod Q := dvd_mul_right _ _

theorem span_fixedPeriod_le (Q : Ideal ActualEisensteinCubic.O) : (Ideal.span {fixedPeriod Q} : Ideal ActualEisensteinCubic.O) ≤ Q := by
  conv_rhs => rw [← ConcretePrimeRowBridge.span_idealGenerator Q]
  exact Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left _ _)

theorem inducedBy_of_elementCoeff_eq (χ χ' ψ : Character)
    (heq : ∀ n, elementCoeff χ' n=elementCoeff χ n)
    (hind : CenteredExceptionalProfile.InducedBy χ ψ) :
    CenteredExceptionalProfile.InducedBy χ' ψ := by
  have hideal (I : Ideal ActualEisensteinCubic.O) : idealCoeff χ' I=idealCoeff χ I := by
    by_cases hI : I=0
    · grind
    · conv_lhs => rw [← ConcretePrimeRowBridge.span_idealGenerator I,
        idealCoeff_span χ' (ConcretePrimeRowBridge.idealGenerator_ne_zero I hI),heq]
      rw [← idealCoeff_span χ (ConcretePrimeRowBridge.idealGenerator_ne_zero I hI),
        ConcretePrimeRowBridge.span_idealGenerator]
  intro I
  by_cases hI : I=0
  · grind
  by_cases hc : IsCoprime I χ'.modulus
  · have hn := CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ' I |>.mpr ⟨hI,hc⟩
    rw [hideal I] at hn
    have hc' := (CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ I).mp hn |>.2
    rw [ite_eq_left hc,hideal I,hind I,ite_eq_left hc']
  · have hz : idealCoeff χ' I=0 := by
      by_contra hn
      exact hc ((CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ' I).mp hn).2
    simp_all

theorem fixedInducingRow_controlled (η : Character) (Q : Ideal ActualEisensteinCubic.O) (m A₀ z : ActualEisensteinCubic.O)
    (hm : m ≠ 0) (hA : A₀ ≠ 0) (hz : z ≠ 0)
    (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:ActualEisensteinCubic.O) ∣ m)
    (hex : CenteredExceptionalProfile.FixedInducingRow η Q m A₀ z) :
    ∃ χ ψ : Character,
      χ.modulus.absNorm ≤ HeckeRowClosure.rowConductorBound η m 1 (A₀*z) ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      CenteredExceptionalProfile.InducedBy χ ψ ∧ Q ≤ ψ.modulus ∧
      ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
        (HeckeRowClosure.elementHom η) m 1 (A₀*z) n := by
  obtain ⟨χ₀,ψ,hprim,hind,hQ,hrow₀⟩ := hex
  obtain ⟨χ,hbound,hrow⟩ := HeckeRowClosure.exists_row_character_with_conductor
    η m 1 (A₀*z) hm one_ne_zero (by positivity) hmLam hm2
  refine ⟨χ,ψ,hbound,hprim,?_,hQ,hrow⟩
  exact inducedBy_of_elementCoeff_eq χ₀ χ ψ (by grind) hind

theorem induced_primaryCoefficient (χ ψ : Character)
    (hind : CenteredExceptionalProfile.InducedBy χ ψ) (I : Ideal ActualEisensteinCubic.O) :
    primaryCoefficient χ I =
      (if IsCoprime I χ.modulus then (1:ℂ) else 0)*primaryCoefficient ψ I := by
  change (if primaryGenerator I=0 then 0 else idealCoeff χ I)=
    (if IsCoprime I χ.modulus then (1:ℂ) else 0)*(if primaryGenerator I=0 then 0 else idealCoeff ψ I)
  rw [hind I]
  simp

theorem primaryCoefficient_actual_row (η χ : Character) (m A₀ z : ActualEisensteinCubic.O)
    (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:ActualEisensteinCubic.O) ∣ m)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n) (I : Ideal ActualEisensteinCubic.O) :
    primaryCoefficient χ I=idealCoeff χ I := by
  change (if primaryGenerator I=0 then 0 else idealCoeff χ I)=_
  by_cases hI : I=0
  · grind
  by_cases hg : primaryGenerator I=0
  · rw [ite_eq_left hg]
    let n := ConcretePrimeRowBridge.idealGenerator I
    have hn : n ≠ 0 := ConcretePrimeRowBridge.idealGenerator_ne_zero I hI
    have hs : Ideal.span {n}=I := ConcretePrimeRowBridge.span_idealGenerator I
    have hbad : ¬Supported (Ideal.span {n}) := by
      intro h
      have hp : primaryGenerator (Ideal.span {n}) ≠ 0 :=
        PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff n |>.mpr ((CanonicalQuadraticSieve.supported_span_iff n).mp h).1
      exact by grind
    rw [← hs,idealCoeff_span χ hn,hrow,
      CanonicalRowCompletion.rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hbad]
  simp_all

def density (c : ActualEisensteinCubic.O) (hc : c ≠ 0) (ψ : Character) (R : Ideal ActualEisensteinCubic.O) : ℂ :=
  letI := finite_quotient_span hc
  letI : Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  (∑ D ∈ idealDivisors R, (moebius D:ℂ)*primaryCoefficient ψ D/(Ideal.absNorm D:ℂ)) *
    (1/(‖eisEmbedding c‖^2:ℂ))*(∑ r : ActualEisensteinCubic.O ⧸ Ideal.span {c}, periodicValue c ψ r)

theorem actual_induced_volume (η χ ψ : Character) (Q : Ideal ActualEisensteinCubic.O) (hQ : Q ≠ 0)
    (hQψ : Q ≤ ψ.modulus) (hind : CenteredExceptionalProfile.InducedBy χ ψ)
    (m A₀ z : ActualEisensteinCubic.O) (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:ActualEisensteinCubic.O) ∣ m)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n)
    (W : 𝓢(ℝ,ℂ)) (b X : ℝ) (hX : 0 < X)
    (hs : Function.support (W:ℝ→ℂ) ⊆ Set.Iic b) :
    ‖(∑' I : Ideal ActualEisensteinCubic.O, idealCoeff χ I*W ((Ideal.absNorm I:ℝ)/X)) -
      (X:ℂ)*(density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus*paperRadialFourier W 0)‖ ≤
      ((idealDivisors χ.modulus).card:ℝ)*(Nat.card (ActualEisensteinCubic.O ⧸ Ideal.span {fixedPeriod Q}):ℝ)*pvControl W := by
  let := finite_quotient_span (fixedPeriod_ne_zero Q hQ)
  let : Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {fixedPeriod Q}) := Fintype.ofFinite _
  have h := masked_hecke_volume (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ)
    (fixedPeriod_three Q) ψ ((span_fixedPeriod_le Q).trans hQψ)
    χ.modulus χ.modulus_ne_bot W b X hX hs
  have he (I : Ideal ActualEisensteinCubic.O) :
      (if IsCoprime I χ.modulus then (1:ℂ) else 0)*primaryCoefficient ψ I=idealCoeff χ I := by
    rw [← induced_primaryCoefficient χ ψ hind I,primaryCoefficient_actual_row η χ m A₀ z hmLam hm2 hrow I]
  simp_rw [show ∀ I : Ideal ActualEisensteinCubic.O, (if IsCoprime I χ.modulus then (1:ℂ) else 0)*
      (primaryCoefficient ψ I*W ((Ideal.absNorm I:ℝ)/X)) =
        idealCoeff χ I*W ((Ideal.absNorm I:ℝ)/X) by grind] at h
  convert h using 1
  · congr 1
    unfold density
    ring
  · rw [Nat.card_eq_fintype_card]
    ring

end SevenEighths.CenteredMomentHeckeVolume

end

end OAI
