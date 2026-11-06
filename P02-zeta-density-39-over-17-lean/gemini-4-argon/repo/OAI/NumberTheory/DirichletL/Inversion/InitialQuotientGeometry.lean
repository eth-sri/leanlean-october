module
public import OAI.NumberTheory.DirichletL.Inversion.InitialArithmetic
public import OAI.NumberTheory.DirichletL.Descent.TripleMass
public import OAI.NumberTheory.DirichletL.Descent.Basic

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic IdealMobiusDivisorSum CompletedGauss CanonicalQuadraticSieve SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
namespace SevenEighths.InverseInitialQuotientGeometry

variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)

def sourceWeight {J : ℕ} (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
    (Z B θ : ℝ) (x : Source (ι:=ι) J) : ℂ :=
  A x * ψC ((Ideal.absNorm (sourceIdeal p x.common) : ℝ)/Z^B) *
    ψd ((Ideal.absNorm (sourceIdeal p x.divisor) : ℝ)/Z^θ)

def retained {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ) (Z B θ : ℝ) : Finset (Source (ι:=ι) J) :=
  S.filter (fun x => sourceWeight p A ψC ψd Z B θ x ≠ 0)

def quotientSet {J : ℕ} (S : Finset (Source (ι:=ι) J)) : Finset (Ideal Eis) :=
  S.image (fun x => sourceIdeal p (x.common\x.divisor))

variable (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem quotientSet_nonzero {J : ℕ} (S : Finset (Source (ι:=ι) J)) :
    ∀ t ∈ quotientSet p S, t ≠ 0 := by
  intro t ht
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
  exact sourceIdeal_ne_zero p hp _

include hp in

theorem quotientSet_eq_initial {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (u : Eisˣ) (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common) :
    initialQuotientSet (S.image (fun x => toTuple p (sectorSource u x))) = quotientSet p S := by
  rw [initialQuotientSet, Finset.image_image]
  apply Finset.image_congr
  intro x hx
  change idealQuotient (sourceIdeal p x.divisor) (sourceIdeal p x.common) = _
  exact source_quotient p hp x.common x.divisor (hdiv x hx)

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem quotient_norm_eq {J : ℕ} (x : Source (ι:=ι) J) (hdiv : x.divisor ⊆ x.common) :
    (Ideal.absNorm (sourceIdeal p (x.common\x.divisor)) : ℝ) =
      (Ideal.absNorm (sourceIdeal p x.common) : ℝ)/Ideal.absNorm (sourceIdeal p x.divisor) := by
  have he : sourceIdeal p x.divisor * sourceIdeal p (x.common\x.divisor) = sourceIdeal p x.common := by
    rw [←sourceIdeal_union p x.divisor (x.common\x.divisor) Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset hdiv]
  have hn := congrArg (fun I : Ideal Eis => (Ideal.absNorm I : ℝ)) he
  simp only [map_mul,Nat.cast_mul] at hn
  have hd : (Ideal.absNorm (sourceIdeal p x.divisor) : ℝ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (sourceIdeal_ne_zero p hp _)
  apply (eq_div_iff hd).mpr
  simpa only [mul_comm] using hn

omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in

theorem retained_norm_windows {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
    (aC bC ad bd Z B θ : ℝ) (hZ : 0 < Z)
    (hC : Function.support ψC ⊆ Set.Icc aC bC)
    (hd : Function.support ψd ⊆ Set.Icc ad bd)
    {x : Source (ι:=ι) J} (hx : x ∈ retained p S A ψC ψd Z B θ) :
    (Ideal.absNorm (sourceIdeal p x.common) : ℝ) ≤ bC*Z^B ∧
      ad*Z^θ ≤ (Ideal.absNorm (sourceIdeal p x.divisor) : ℝ) := by
  have hn := (Finset.mem_filter.mp hx).2
  have hnC : ψC ((Ideal.absNorm (sourceIdeal p x.common) : ℝ)/Z^B) ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).2
  have hnd : ψd ((Ideal.absNorm (sourceIdeal p x.divisor) : ℝ)/Z^θ) ≠ 0 :=
    (mul_ne_zero_iff.mp hn).2
  exact ⟨(div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp (hC hnC).2,
    (le_div_iff₀ (Real.rpow_pos_of_pos hZ _)).mp (hd hnd).1⟩

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem retained_quotient_bound {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
    (aC bC ad bd Z B θ η : ℝ) (hZ : 0 < Z)
    (hC : Function.support ψC ⊆ Set.Icc aC bC)
    (hd : Function.support ψd ⊆ Set.Icc ad bd)
    (hCup : bC ≤ Z^η) (hdlo : Z^(-η) ≤ ad)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common) :
    ∀ t ∈ quotientSet p (retained p S A ψC ψd Z B θ),
      (Ideal.absNorm t : ℝ) ≤ Z^(B-θ+2*η) := by
  intro t ht
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
  have hw := retained_norm_windows p S A ψC ψd aC bC ad bd Z B θ hZ hC hd hx
  rw [quotient_norm_eq p hp x (hdiv x (Finset.mem_filter.mp hx).1)]
  have hc : (Ideal.absNorm (sourceIdeal p x.common) : ℝ) ≤ Z^(B+η) := by
    apply (hw.1.trans (mul_le_mul_of_nonneg_right hCup (Real.rpow_pos_of_pos hZ _).le)).trans_eq
    rw [←Real.rpow_add hZ]
    congr 1
    ring
  have he : Z^(θ-η) ≤ (Ideal.absNorm (sourceIdeal p x.divisor) : ℝ) := by
    apply le_trans _ hw.2
    calc
      _ = Z^(-η)*Z^θ := by rw [←Real.rpow_add hZ]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hdlo (Real.rpow_pos_of_pos hZ _).le
  calc
    _ ≤ Z^(B+η)/Z^(θ-η) := div_le_div₀ (by positivity) hc (Real.rpow_pos_of_pos hZ _) he
    _ = _ := by rw [←Real.rpow_sub hZ]; congr 1; ring

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem nonempty_radius {J : ℕ} (S : Finset (Source (ι:=ι) J)) (Z P η : ℝ)
    (hZ : 1 < Z) (hne : (quotientSet p S).Nonempty)
    (hnorm : ∀ t ∈ quotientSet p S, (Ideal.absNorm t : ℝ) ≤ Z^(P+2*η)) :
    1 ≤ Z^(P+2*η) ∧ 0 ≤ P+2*η := by
  obtain ⟨t,ht⟩ := hne
  have ht0 := quotientSet_nonzero p hp S t ht
  have hn : (1:ℝ) ≤ Ideal.absNorm t := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr ht0)
  have hh := hn.trans (hnorm t ht)
  refine ⟨hh,?_⟩
  exact (Real.rpow_le_rpow_left_iff hZ).mp (by simpa only [Real.rpow_zero] using hh)

def normalizedMass (J : ℕ) (T : Finset (Ideal Eis)) (H : ℝ) : ℝ :=
  H⁻¹ * ∑ t ∈ T, ((idealDivisors t).card : ℝ)^J

theorem normalized_mass_bound (J : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Finset (Ideal Eis)) (H : ℝ), 0 < H →
      (∀ t ∈ T, t ≠ 0) → (∀ t ∈ T, (Ideal.absNorm t : ℝ) ≤ H) →
      normalizedMass J T H ≤ C*H^ε := by
  obtain ⟨C,hC,hb⟩ := ideal_divisor_power_small J ε hε
  refine ⟨128*C,by positivity,?_⟩
  intro T H hH hz hn
  rcases T.eq_empty_or_nonempty with he|⟨t,ht⟩
  · subst T
    simp only [normalizedMass,Finset.sum_empty,mul_zero]
    positivity
  have hH1 : 1 ≤ H := by
    have ht1 : (1:ℝ) ≤ Ideal.absNorm t := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hz t ht))
    exact ht1.trans (hn t ht)
  have hw : ∀ t ∈ T, ((idealDivisors t).card : ℝ)^J ≤ C*H^ε := by
    intro t ht
    exact (hb t (hz t ht)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (hn t ht) hε.le) hC.le)
  have hs : (∑ t ∈ T, ((idealDivisors t).card : ℝ)^J) ≤ (128*H)*(C*H^ε) := by
    calc
      _ ≤ ∑ _t ∈ T, C*H^ε := Finset.sum_le_sum hw
      _ = (T.card:ℝ)*(C*H^ε) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (DescentFiberCost.finite_ideal_count_real T H hH1 hz hn) (by positivity)
  apply (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hH.le)).trans_eq
  field_simp

def assignedCenter {σ : Type*} (slots : Finset σ) (z : σ → ℝ) : ℝ := ∑ i ∈ slots, z i

theorem assigned_register {σ : Type*} [DecidableEq σ]
    (all assigned : Finset σ) (ha : assigned ⊆ all) (z : σ → ℝ)
    (hz : ∀ i ∈ all, 0 ≤ z i) :
    0 ≤ assignedCenter assigned z ∧ 0 ≤ assignedCenter (all\assigned) z ∧
      assignedCenter all z - assignedCenter assigned z = assignedCenter (all\assigned) z := by
  refine ⟨Finset.sum_nonneg (fun i hi => hz i (ha hi)),
    Finset.sum_nonneg (fun i hi => hz i (Finset.mem_sdiff.mp hi).1),?_⟩
  unfold assignedCenter
  have h := Finset.sum_sdiff ha (f := z)
  linarith

def assignedElement {σ : Type*} (slots : Finset σ) (q : σ → Eis) : Eis := ∏ i ∈ slots, q i

theorem assigned_norm_bound {σ : Type*} (slots : Finset σ) (q : σ → Eis)
    (z a b : σ → ℝ) (W : σ → ℝ → ℂ) (Z : ℝ) (hZ : 0 < Z)
    (hW : ∀ i ∈ slots, Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hret : ∀ i ∈ slots, W i ((Ideal.absNorm (Ideal.span {q i}) : ℝ)/Z^(z i)) ≠ 0) :
    (Ideal.absNorm (Ideal.span {assignedElement slots q}) : ℝ) ≤
      (∏ i ∈ slots, b i)*Z^(assignedCenter slots z) := by
  have hb : ∀ i ∈ slots, (Ideal.absNorm (Ideal.span {q i}) : ℝ) ≤ b i*Z^(z i) := by
    intro i hi
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp (hW i hi (hret i hi)).2
  have hp := Finset.prod_le_prod₀ (fun i _ => (Nat.cast_nonneg (Ideal.absNorm (Ideal.span {q i})))) hb
  simpa only [assignedElement,FiniteGaussPhase.span_finset_prod,map_prod,Nat.cast_prod,
    Finset.prod_mul_distrib,←Real.rpow_sum_of_pos hZ,assignedCenter] using hp

theorem assigned_norm_power {σ : Type*} (slots : Finset σ) (q : σ → Eis)
    (z a b : σ → ℝ) (W : σ → ℝ → ℂ) (Z η : ℝ) (hZ : 0 < Z)
    (hW : ∀ i ∈ slots, Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hret : ∀ i ∈ slots, W i ((Ideal.absNorm (Ideal.span {q i}) : ℝ)/Z^(z i)) ≠ 0)
    (hthreshold : (∏ i ∈ slots, b i) ≤ Z^η) :
    (Ideal.absNorm (Ideal.span {assignedElement slots q}) : ℝ) ≤
      Z^(assignedCenter slots z+η) := by
  apply (assigned_norm_bound slots q z a b W Z hZ hW hret).trans
  calc
    _ ≤ Z^η*Z^(assignedCenter slots z) := mul_le_mul_of_nonneg_right hthreshold (by positivity)
    _ = _ := by rw [←Real.rpow_add hZ]; congr 1; ring

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem span_source_puncture {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (hpr : ∀ i, λ₀^2 ∣ p i-1) (j : Eis)
    {t : Ideal Eis} (ht : t ∈ quotientSet p S) :
    Ideal.span {j*primaryGenerator t} = t*Ideal.span {j} := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
  rw [sourceIdeal_gen p hp hpr]
  simp only [sourceIdeal,Ideal.span_singleton_mul_span_singleton,mul_comm]
