module
public import DedekindZetaZeroFree.LargeSieve.Bilinear.Divisors.IdealDivisorBins
public import DedekindZetaZeroFree.LargeSieve.Bilinear.Remainders.DivisorNormAndCardinalityBounds

public import DedekindZetaZeroFree.LargeSieve.Bilinear.DivisorRectangleEnvelopes

@[expose] public section

noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDual

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
    {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

def admissibleRectangles (C : Context Q) (B : ℝ) : Finset (ℝ × ℝ) :=
  (ErrorRectangles.rectangles C).filter (fun P =>
    ErrorRectangles.lowerConstant c * C.N / (norm C.d * Real.sqrt (B * C.M)) *
      Real.rpow (C.M * C.N) C.δ ≤ P.1 * P.2)

def binDivisors (P : ℝ) (u : Ideal (𝓞 F)) : Finset (Ideal (𝓞 F)) :=
  (idealDivisors u).filter (ErrorRectangles.InBin P)

def bucketDensity (C : Context Q) (B : ℝ) (e : Ideal (𝓞 F))
    (P : ℝ × ℝ) (p : Ideal (𝓞 F) × Ideal (𝓞 F)) : ℂ :=
  ∑ f₁ ∈ binDivisors P.1 p.1, ∑ f₂ ∈ binDivisors P.2 p.2,
    if C.Z1 B e < norm (f₁ * f₂) then
      (UniqueFactorizationMonoid.moebius (f₁ * f₂) : ℂ) / (norm (f₁ * f₂) : ℂ)
    else 0

def bucket (C : Context Q) (B : ℝ) (unit : Bool)
    (e : Ideal (𝓞 F)) (P : ℝ × ℝ) : ℂ :=
  C.pairSum fun p hp => C.coefficient p *
    C.prefactor e p hp *
      ∑ a ∈ C.reflectedRows B unit,
        C.primitive p hp a * C.kappa *
          (Real.sqrt (C.dualScale e p / norm a) : ℂ) * C.mass *
          bucketDensity C B e P p

private lemma norm_le_of_dvd {a b : Ideal (𝓞 F)} (hb : b ≠ ⊥) (h : a ∣ b) :
    norm a ≤ norm b := by apply @DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly.LocalTailGeometry.norm_le_of_dvd <;> assumption

private lemma norm_mul (a b : Ideal (𝓞 F)) : norm (a * b) = norm a * norm b := by
  simp [norm, map_mul]

alias DualDyadicRectangles.norm_mul := norm_mul

private alias bin_exists := DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.DivisorBins.bin_exists

private alias bin_unique := DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.DivisorBins.bin_unique

private lemma product_unique {u v a b x y : Ideal (𝓞 F)}
    (huv : u ⊔ v = ⊤) (ha : a ∣ u) (hb : b ∣ v) (hx : x ∣ u) (hy : y ∣ v)
    (heq : a*b = x*y) : a = x ∧ b = y := by
  have hrel : IsRelPrime u v := by
    intro z hz hz'
    apply Ideal.isUnit_iff.mpr
    apply top_unique
    rw [← huv]
    exact sup_le (Ideal.dvd_iff_le.mp hz) (Ideal.dvd_iff_le.mp hz')
  exact ⟨dvd_antisymm ((hrel.of_dvd_left ha |>.of_dvd_right hy).dvd_of_dvd_mul_right
    (heq ▸ dvd_mul_right a b)) ((hrel.of_dvd_left hx |>.of_dvd_right hb).dvd_of_dvd_mul_right
    (heq.symm ▸ dvd_mul_right x y)), dvd_antisymm ((hrel.symm.of_dvd_left hb |>.of_dvd_right hx).dvd_of_dvd_mul_left
    (heq ▸ dvd_mul_left b a)) ((hrel.symm.of_dvd_left hy |>.of_dvd_right ha).dvd_of_dvd_mul_left
    (heq.symm ▸ dvd_mul_left y x))⟩

alias DualDyadicRectangles.product_unique := product_unique

private lemma bin_admissible (C : Context Q) (B : ℝ)
    (hM : 1 ≤ C.M) (hN : 1 ≤ C.N) (hn : 1 ≤ norm C.d)
    {p : Ideal (𝓞 F) × Ideal (𝓞 F)} (hp : p ∈ C.pairs)
    {e : Ideal (𝓞 F)} (he0 : e ≠ ⊥)
    {P : ℝ × ℝ} (hrect : P ∈ ErrorRectangles.rectangles C)
    {a b : Ideal (𝓞 F)} (ha : ErrorRectangles.InBin P.1 a)
    (hb : ErrorRectangles.InBin P.2 b) (hl : C.Z1 B e < norm (a*b)) :
    P ∈ admissibleRectangles C B := by
  have hends := ErrorRectangles.rectangle_endpoints C P hrect
  have hab : norm (a*b) ≤ 4 * (P.1*P.2) := by
    rw [norm_mul]
    have hh := mul_le_mul ha.2.2 hb.2.2 (by unfold norm; positivity)
      (by linarith [hends.1] : 0 ≤ 2 * P.1)
    nlinarith
  have hen : 1 ≤ norm e := by
    unfold norm
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr he0)
  have hesqrt : 1 ≤ Real.sqrt (norm e) := by simpa using Real.sqrt_le_sqrt hen
  let T := C.N / (norm C.d * Real.sqrt (B*C.M)) * Real.rpow (C.M*C.N) C.δ
  have hT : 0 ≤ T := by
    dsimp [T]
    exact mul_nonneg (div_nonneg (by linarith) (mul_nonneg (by linarith) (Real.sqrt_nonneg _)))
      (Real.rpow_nonneg (by nlinarith) _)
  have hZ : C.Z1 B e = T * Real.sqrt (norm e) := by unfold Context.Z1 T; ring
  have htZ : T ≤ C.Z1 B e := by rw [hZ]; exact le_mul_of_one_le_right hT hesqrt
  have hc : ErrorRectangles.lowerConstant c ≤ 1/4 := by
    unfold ErrorRectangles.lowerConstant
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith [le_max_left (1 : ℝ) (norm c)]
  apply Finset.mem_filter.mpr
  refine ⟨hrect, ?_⟩
  have heq : ErrorRectangles.lowerConstant c * C.N / (norm C.d * Real.sqrt (B*C.M)) *
      Real.rpow (C.M*C.N) C.δ = ErrorRectangles.lowerConstant c * T := by dsimp [T]; ring
  rw [heq]
  have hh := mul_le_mul_of_nonneg_right hc hT
  nlinarith

private lemma density_product (C : Context Q) (Z : ℝ)
    (p : Ideal (𝓞 F) × Ideal (𝓞 F)) (hp : C.ValidPair p) :
    Context.largeDensity (p.1*p.2) Z =
      ∑ a ∈ idealDivisors p.1, ∑ b ∈ idealDivisors p.2,
        if Z < norm (a*b) then (UniqueFactorizationMonoid.moebius (a*b) : ℂ) / (norm (a*b) : ℂ) else 0 := by
  rw [Context.largeDensity, Finset.sum_filter]
  symm
  rw [← Finset.sum_product']
  apply Finset.sum_bij (fun ab _ => ab.1*ab.2)
  · intro ab hab
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    exact (mem_idealDivisors (mul_ne_zero hp.hu0 hp.hv0)).mpr
      (mul_dvd_mul ((mem_idealDivisors hp.hu0).mp ha) ((mem_idealDivisors hp.hv0).mp hb))
  · intro ab hab xy hxy heq
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
    obtain ⟨h1,h2⟩ := product_unique hp.huv
      ((mem_idealDivisors hp.hu0).mp ha) ((mem_idealDivisors hp.hv0).mp hb)
      ((mem_idealDivisors hp.hu0).mp hx) ((mem_idealDivisors hp.hv0).mp hy) heq
    exact Prod.ext h1 h2
  · intro f hf
    obtain ⟨a,b,ha,hb,heq⟩ := exists_dvd_and_dvd_of_dvd_mul
      ((mem_idealDivisors (mul_ne_zero hp.hu0 hp.hv0)).mp hf)
    exact ⟨(a,b), Finset.mem_product.mpr
      ⟨(mem_idealDivisors hp.hu0).mpr ha, (mem_idealDivisors hp.hv0).mpr hb⟩, heq.symm⟩
  · intro ab hab
    rfl

private lemma sum_if_out {α : Type*} (s : Finset α) (P : Prop) [Decidable P]
    (f : α → ℂ) : (if P then ∑ i ∈ s, f i else 0) = ∑ i ∈ s, if P then f i else 0 := by
  split_ifs <;> simp [*]

alias DualDyadicRectangles.sum_if_out := sum_if_out

private lemma density_rectangles (C : Context Q) (B : ℝ)
    (hM : 1 ≤ C.M) (hN : 1 ≤ C.N) (hn : 1 ≤ norm C.d)
    (hnN : norm C.d ≤ 2*C.N)
    {p : Ideal (𝓞 F) × Ideal (𝓞 F)} (hp : p ∈ C.pairs)
    {e : Ideal (𝓞 F)} (he : e ∈ C.mobiusDivisors) :
    Context.largeDensity (p.1*p.2) (C.Z1 B e) =
      ∑ P ∈ admissibleRectangles C B, bucketDensity C B e P p := by
  have hpv := (Finset.mem_filter.mp hp).2
  have he0 := ne_bot_of_mem_idealDivisors he
  rw [density_product C _ p hpv]
  simp only [bucketDensity, binDivisors, Finset.sum_filter]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  conv_rhs =>
    simp only [sum_if_out]
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  have had := (mem_idealDivisors hpv.hu0).mp ha
  have hbd := (mem_idealDivisors hpv.hv0).mp hb
  by_cases hl : C.Z1 B e < norm (a*b)
  · obtain ⟨hu,hv⟩ := Finset.mem_product.mp ((Finset.mem_filter.mp hp).1)
    have huN : norm p.1 ≤ 2*C.N / norm C.d :=
      ((Sieve.mem_idealAdmissibleFinset F c _ _).mp (Finset.mem_filter.mp hu).1).2.2
    have hvN : norm p.2 ≤ 2*C.N / norm C.d :=
      ((Sieve.mem_idealAdmissibleFinset F c _ _).mp (Finset.mem_filter.mp hv).1).2.2
    have hX : 1 ≤ 2*(C.N / norm C.d) := by
      rw [← mul_div_assoc, le_div_iff₀ (by linarith : 0 < norm C.d)]
      simpa using hnN
    obtain ⟨P₁,hP₁s,hP₁,hP₁N,hP₁a⟩ := bin_exists _ hX a (ne_bot_of_mem_idealDivisors ha)
      ((norm_le_of_dvd hpv.hu0 had).trans (by simpa [mul_div_assoc] using huN))
    obtain ⟨P₂,hP₂s,hP₂,hP₂N,hP₂b⟩ := bin_exists _ hX b (ne_bot_of_mem_idealDivisors hb)
      ((norm_le_of_dvd hpv.hv0 hbd).trans (by simpa [mul_div_assoc] using hvN))
    have hrect : (P₁,P₂) ∈ ErrorRectangles.rectangles C := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨hP₁s,hP₂s⟩,hP₁,hP₂,?_,?_,p,hp,a,b,had,hbd,hP₁a,hP₂b⟩ <;>
        simpa [mul_div_assoc] using (by assumption : _)
    symm
    rw [Finset.sum_eq_single (P₁,P₂)]
    · simp [hl, hP₁a, hP₂b]
    · intro R hR hne
      have hRs := (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).1)
      by_cases hRa : ErrorRectangles.InBin R.1 a
      · by_cases hRb : ErrorRectangles.InBin R.2 b
        · exact (hne (Prod.ext (bin_unique hRs.1 hP₁s hRa hP₁a) (bin_unique hRs.2 hP₂s hRb hP₂b))).elim
        · simp [hRb]
      · simp [hRa]
    · intro hnmem
      exact (hnmem (bin_admissible C B hM hN hn hp he0 hrect hP₁a hP₂b hl)).elim
  · simp [hl]

theorem finite_rectangle_expansion (C : Context Q) (B : ℝ) (unit : Bool)
    (hM : 1 ≤ C.M) (hN : 1 ≤ C.N) (hδ : 0 < C.δ)
    (hB : 1 ≤ B) (hBK : B ≤ C.K) (hKM : C.K ≤ C.M)
    (hn : 1 ≤ norm C.d) (hnN : norm C.d ≤ 2 * C.N) :
    E1 C B unit =
      ∑ e ∈ C.mobiusDivisors,
        ∑ P ∈ admissibleRectangles C B, bucket C B unit e P := by
  unfold E1 bucket Context.pairSum
  simp only [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs =>
    arg 2
    ext e
    rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs with hpv
  · conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    rw [density_rectangles C B hM hN hn hnN hp he]
    simp only [Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    simp only [mul_assoc]
  · simp

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDual

end
