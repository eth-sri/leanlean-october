module
public import DedekindZetaZeroFree.LargeSieve.Bilinear.Errors.LargeDirectRectangles
public import DedekindZetaZeroFree.LargeSieve.Bilinear.Errors.LargeDualRectangles
public import DedekindZetaZeroFree.LargeSieve.Bilinear.LargeDivisors.DirectExpansionAndRectangleBounds

public import DedekindZetaZeroFree.LargeSieve.Bilinear.Divisors.ShortDivisorDyadicGeometry
public import DedekindZetaZeroFree.LargeSieve.Bilinear.LargeDivisors.RadicalCoprimeColumnExpansion
public import DedekindZetaZeroFree.LargeSieve.Bilinear.Coefficients.PrimitiveProductsAndSupportedPrimeProfiles
public import DedekindZetaZeroFree.LargeSieve.Bilinear.LargeDivisors.SupportedRowsAndReflectedProductBounds

@[expose] public section

section

noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.OriginFinite
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
    {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

def divisorBin (P : ℝ) : Finset (Ideal (𝓞 F)) :=
  (boundedNormIdeals F (2 * P)).filter (ErrorRectangles.InBin P)

def quotientCoefficient (C : Context Q) (u : Ideal (𝓞 F)) : ℂ :=
  C.lam (C.d * u) / (Real.sqrt (norm u) : ℂ)

def weightedDivisorBlock (C : Context Q) (e f g a : Ideal (𝓞 F)) : ℂ :=
  C.pairSum fun p hp =>
    if f ∣ p.1 ∧ g ∣ p.2 then
      quotientCoefficient C p.1 * star (quotientCoefficient C p.2) *
        C.primitive p hp e * C.primitive p hp a
    else 0

private alias bin_unique := DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.DivisorBins.bin_unique

private alias product_unique := DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDual.DualDyadicRectangles.product_unique

private lemma bin_filter_eq (C : Context Q) {B : ℝ} {p : Ideal (𝓞 F) × Ideal (𝓞 F)}
    (hp : p ∈ C.pairs) {P : ℝ × ℝ} (hP : P ∈ Origin.rectangles C B)
    (i : Fin 2) :
    (divisorBin (F := F) (if i = 0 then P.1 else P.2)).filter
        (fun f => f ∣ (if i = 0 then p.1 else p.2)) =
      (idealDivisors (if i = 0 then p.1 else p.2)).filter
        (ErrorRectangles.InBin (if i = 0 then P.1 else P.2)) := by
  have hpv := (Finset.mem_filter.mp hp).2
  have h0 : (if i = 0 then p.1 else p.2) ≠ ⊥ := by split_ifs <;> exact (by first | exact hpv.hu0 | exact hpv.hv0)
  ext f
  simp only [divisorBin, Finset.mem_filter, mem_boundedNormIdeals,
    mem_idealDivisors h0]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.2.2.2, h.2⟩, h.1⟩⟩

private alias sum_if_out := DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDual.DualDyadicRectangles.sum_if_out

private lemma density_rectangles (C : Context Q) (B : ℝ)
    (hgeometry : Origin.ShortGeometry C B)
    {p : Ideal (𝓞 F) × Ideal (𝓞 F)} (hp : p ∈ C.pairs)
    {e : Ideal (𝓞 F)} (he : e ∈ C.mobiusDivisors) :
    Context.originDivisors (p.1 * p.2) (C.Z1 B e) =
      ∑ P ∈ Origin.rectangles C B,
        ∑ f ∈ divisorBin (F := F) P.1, ∑ g ∈ divisorBin (F := F) P.2,
          if f ∣ p.1 ∧ g ∣ p.2 ∧ norm (f*g) ≤ C.Z1 B e then
            (UniqueFactorizationMonoid.moebius (f*g) : ℂ) else 0 := by
  have hpv := (Finset.mem_filter.mp hp).2
  rw [Context.originDivisors, Finset.sum_filter,
    LargeDirectDictionary.sum_divisors_mul _ _ hpv.hu0 hpv.hv0 hpv.huv]
  have hrestrict : ∀ P ∈ Origin.rectangles C B,
      (∑ f ∈ divisorBin P.1, ∑ g ∈ divisorBin P.2,
        if f ∣ p.1 ∧ g ∣ p.2 ∧ norm (f*g) ≤ C.Z1 B e then
          (UniqueFactorizationMonoid.moebius (f*g) : ℂ) else 0) =
      ∑ f ∈ idealDivisors p.1, ∑ g ∈ idealDivisors p.2,
        if ErrorRectangles.InBin P.1 f ∧ ErrorRectangles.InBin P.2 g ∧
            norm (f*g) ≤ C.Z1 B e then
          (UniqueFactorizationMonoid.moebius (f*g) : ℂ) else 0 := by
    intro P hP
    have h1 := bin_filter_eq C hp hP (0 : Fin 2)
    have h2 := bin_filter_eq C hp hP (1 : Fin 2)
    simp only [ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false] at h1 h2
    calc
      _ = ∑ f ∈ (divisorBin P.1).filter (fun f => f ∣ p.1),
          ∑ g ∈ (divisorBin P.2).filter (fun g => g ∣ p.2),
            if norm (f*g) ≤ C.Z1 B e then (UniqueFactorizationMonoid.moebius (f*g) : ℂ) else 0 := by
        simp only [Finset.sum_filter, ← sum_if_out]
        apply Finset.sum_congr rfl
        intro f hf
        by_cases h : f ∣ p.1 <;> simp [h, ite_and]
      _ = _ := by
        rw [h1, h2]
        simp only [Finset.sum_filter, ← sum_if_out]
        apply Finset.sum_congr rfl
        intro f hf
        by_cases h : ErrorRectangles.InBin P.1 f <;> simp [h, ite_and]
  rw [Finset.sum_congr rfl hrestrict]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f hf
  conv_rhs =>
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g hg
  by_cases hshort : norm (f*g) ≤ C.Z1 B e
  · have had := (mem_idealDivisors hpv.hu0).mp hf
    have hbd := (mem_idealDivisors hpv.hv0).mp hg
    obtain ⟨x, y, hxy, hx, hy, P, hP, hPx, hPy⟩ := hgeometry e he p hp (f*g) ((mem_idealDivisors (mul_ne_zero hpv.hu0 hpv.hv0)).mpr (mul_dvd_mul had hbd)) hshort
    obtain ⟨rfl, rfl⟩ := product_unique hpv.huv had hbd hx hy hxy
    symm
    rw [Finset.sum_eq_single P]
    · simp [hshort, hPx, hPy]
    · intro R hR hne
      have hRs := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).1
      have hPs := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hP).1).1
      by_cases hRf : ErrorRectangles.InBin R.1 f
      · by_cases hRg : ErrorRectangles.InBin R.2 g
        · exact (hne (Prod.ext (bin_unique hRs.1 hPs.1 hRf hPx)
            (bin_unique hRs.2 hPs.2 hRg hPy))).elim
        · simp [hRg]
      · simp [hRf]
    · intro hnmem
      exact (hnmem hP).elim
  · simp [hshort]

private lemma coefficient_quotient (C : Context Q) (p : Ideal (𝓞 F) × Ideal (𝓞 F)) :
    C.coefficient p / (Real.sqrt (norm (p.1*p.2)) : ℂ) =
      quotientCoefficient C p.1 * star (quotientCoefficient C p.2) := by
  have hnorm : norm (p.1*p.2) = norm p.1 * norm p.2 := by simp [norm, map_mul]
  rw [hnorm, Real.sqrt_mul (by unfold norm; positivity)]
  simp only [quotientCoefficient, Context.coefficient, star_div₀,
    Complex.star_def, map_mul, Complex.conj_ofReal, div_mul_div_comm, Complex.ofReal_mul]

private alias pairSum_mul := DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDirectAssembly.DirectExpansionAndRectangleBounds.pairSum_mul

private alias pairSum_sum := DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDirectAssembly.DirectExpansionAndRectangleBounds.pairSum_sum

private lemma moebius_norm_le (d : Ideal (𝓞 F)) :
    ‖(UniqueFactorizationMonoid.moebius d : ℂ)‖ ≤ 1 := by apply @DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitAssembly.PairEnergyAndUniformTailBounds.mu_norm <;> assumption

theorem finite_coefficient_rectangles (C : Context Q) (B : ℝ) (unit : Bool)
    (hN : 1 ≤ C.N) (hn : 1 ≤ norm C.d) (hnN : norm C.d ≤ 2 * C.N)
    (hgeometry : Origin.ShortGeometry C B) :
    ‖Origin.coefficientForm C B unit‖ ≤
      ∑ e ∈ C.mobiusDivisors, ∑ P ∈ Origin.rectangles C B,
        ∑ f ∈ divisorBin (F := F) P.1, ∑ g ∈ divisorBin (F := F) P.2,
          ∑ a ∈ C.reflectedRows B unit, ‖weightedDivisorBlock C e f g a‖ := by
  let w : Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ := fun e f g =>
    if norm (f*g) ≤ C.Z1 B e then
      (UniqueFactorizationMonoid.moebius e : ℂ) / (norm e : ℂ) *
        (UniqueFactorizationMonoid.moebius (f*g) : ℂ) else 0
  have heq : Origin.coefficientForm C B unit =
      ∑ e ∈ C.mobiusDivisors, ∑ P ∈ Origin.rectangles C B,
        ∑ f ∈ divisorBin P.1, ∑ g ∈ divisorBin P.2,
          ∑ a ∈ C.reflectedRows B unit, w e f g * weightedDivisorBlock C e f g a := by
    unfold Origin.coefficientForm
    have hrewrite : C.pairSum (fun p hp =>
        (C.coefficient p / (Real.sqrt (norm (p.1*p.2)) : ℂ)) *
          ∑ e ∈ C.mobiusDivisors,
            ((UniqueFactorizationMonoid.moebius e : ℂ) * C.primitive p hp e / (norm e : ℂ)) *
              ∑ a ∈ C.reflectedRows B unit,
                C.primitive p hp a * Context.originDivisors (p.1*p.2) (C.Z1 B e)) =
      C.pairSum (fun p hp =>
        (quotientCoefficient C p.1 * star (quotientCoefficient C p.2)) *
          ∑ e ∈ C.mobiusDivisors,
            ((UniqueFactorizationMonoid.moebius e : ℂ) * C.primitive p hp e / (norm e : ℂ)) *
              ∑ a ∈ C.reflectedRows B unit, C.primitive p hp a *
                ∑ P ∈ Origin.rectangles C B,
                  ∑ f ∈ divisorBin P.1, ∑ g ∈ divisorBin P.2,
                    if f ∣ p.1 ∧ g ∣ p.2 ∧ norm (f*g) ≤ C.Z1 B e then
                      (UniqueFactorizationMonoid.moebius (f*g) : ℂ) else 0) := by
      unfold Context.pairSum
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs with hpv
      · dsimp only
        rw [coefficient_quotient C p]
        congr 1
        apply Finset.sum_congr rfl
        intro e he
        rw [density_rectangles C B hgeometry hp he]
      · rfl
    rw [hrewrite]
    simp only [Finset.mul_sum, pairSum_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro P hP
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f hf
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro g hg
    apply Finset.sum_congr rfl
    intro a ha
    unfold weightedDivisorBlock
    rw [← pairSum_mul]
    unfold Context.pairSum
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hpv : C.ValidPair p
    · simp only [dif_pos hpv]
      by_cases hdiv : f ∣ p.1 ∧ g ∣ p.2
      · by_cases hshort : norm (f*g) ≤ C.Z1 B e
        · simp only [if_pos hdiv, if_pos (And.intro hdiv.1 (And.intro hdiv.2 hshort)), w, if_pos hshort]
          ring
        · simp [hshort, hdiv, w]
      · simp [hdiv, w, show ¬(f ∣ p.1 ∧ g ∣ p.2 ∧ norm (f*g) ≤ C.Z1 B e) by tauto]
    · simp [hpv]
  have hw : ∀ e ∈ C.mobiusDivisors, ∀ f g, ‖w e f g‖ ≤ 1 := by
    intro e he f g
    have hen : 1 ≤ norm e := by
      unfold norm
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (ne_bot_of_mem_idealDivisors he))
    dsimp [w]
    split_ifs
    · rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ norm e)]
      calc
        _ ≤ (1 / norm e) * 1 := mul_le_mul
          (div_le_div_of_nonneg_right (moebius_norm_le e) (by linarith))
          (moebius_norm_le (f*g)) (norm_nonneg _) (by positivity)
        _ ≤ 1 := by rw [mul_one]; exact (div_le_one (by linarith)).mpr hen
    · simp
  rw [heq]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro e he
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro P hP
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro f hf
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro g hg
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a ha
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hw e he f g)

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.OriginFinite

end

end

section

noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.OriginFinite
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
    {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

def divisorIncidence (C : Context Q) (f : Ideal (𝓞 F)) : ℝ :=
  ∑ u ∈ C.columns.filter (fun u => f ∣ u),
    (2 : ℝ) ^ (UniqueFactorizationMonoid.normalizedFactors u).toFinset.card *
      ‖quotientCoefficient C u‖ ^ 2

private alias col_data := DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDirect.LargeDirectRectangles.col_data

private alias valid_iff := DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDirect.LargeDirectRectangles.valid_iff

private alias core_rows := DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.SupportedRows.reflected_core_rows_subset

 def block (C : Context Q) (U V : Finset (Ideal (𝓞 F)))
    (x y : Ideal (𝓞 F) → ℂ) (r : Ideal (𝓞 F)) : ℂ :=
  ∑ u ∈ U, ∑ v ∈ V, if u ⊔ v = ⊤ then
    x u * star (y v) * (Q.χ u) r * star ((Q.χ v) r) else 0

section

variable (C : Context Q)

private lemma block_split (f g : Ideal (𝓞 F))
    (x y : Ideal (𝓞 F) → ℂ) (r : Ideal (𝓞 F)) :
    (∑ p ∈ C.pairs, if f ∣ p.1 ∧ g ∣ p.2 then
      x p.1 * star (y p.2) * (Q.χ p.1) r * star ((Q.χ p.2) r) else 0) =
    block C (C.columns.filter (fun u => f ∣ u ∧ u ≠ ⊤))
      (C.columns.filter (fun v => g ∣ v)) x y r +
    block C (C.columns.filter (fun u => f ∣ u ∧ u = ⊤))
      (C.columns.filter (fun v => g ∣ v ∧ v ≠ ⊤)) x y r := by
  simp only [Context.pairs, Finset.sum_filter, Finset.sum_product, block]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  have hi (v) (hv : v ∈ C.columns) := valid_iff C hu hv
  have hout (P : Prop) [Decidable P] (z : Ideal (𝓞 F) → ℂ) :
      (if P then ∑ v ∈ C.columns, z v else 0) =
        ∑ v ∈ C.columns, if P then z v else 0 := by split_ifs <;> simp
  rw [hout, hout, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  rw [hi v hv]
  by_cases hf : f ∣ u <;> by_cases hg : g ∣ v <;>
    by_cases hut : u = ⊤ <;> by_cases hvt : v = ⊤ <;>
    by_cases hc : u ⊔ v = ⊤ <;> simp [hf, hg, hut, hvt, hc]

private lemma weighted_phase
    (phase : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ)
    (hsplit : ∀ e ∈ C.mobiusDivisors, ∀ t ∈ squarefreeBadPool c,
      ∀ p ∈ C.pairs, ∀ hp : Context.ValidPair C p, ∀ r, r ⊔ c = ⊤ →
      C.primitive p hp e * C.primitive p hp (t * r) =
        (phase p.1 (e * t) * (Q.χ p.1) r) *
          star (phase p.2 (e * t) * (Q.χ p.2) r))
    (e t f g r : Ideal (𝓞 F)) (he : e ∈ C.mobiusDivisors)
    (ht : t ∈ squarefreeBadPool c) (hrc : r ⊔ c = ⊤) :
    weightedDivisorBlock C e f g (t*r) =
      ∑ p ∈ C.pairs, if f ∣ p.1 ∧ g ∣ p.2 then
        (quotientCoefficient C p.1 * phase p.1 (e*t)) *
          star (quotientCoefficient C p.2 * phase p.2 (e*t)) *
            (Q.χ p.1) r * star ((Q.χ p.2) r) else 0 := by
  unfold weightedDivisorBlock Context.pairSum
  apply Finset.sum_congr rfl
  intro p hp
  have hpv := (Finset.mem_filter.mp hp).2
  rw [dif_pos hpv]
  dsimp only
  split_ifs with h
  · rw [mul_assoc, hsplit e he t ht p hp hpv r hrc]
    simp only [star_mul]
    ring
  · rfl

end

local notation "IntegerIdeal" => Ideal (𝓞 F)

private lemma column_operator (D : Sieve.AllIndexNormalizedFamilyData Q)
    (C : Context Q) (hCD : C.D = D) (hN : 1 ≤ C.N)
    (K : ℝ) (hop : ∀ C : Context Q, C.D = D → 1 ≤ C.N →
      ∀ B P : ℝ, 1 ≤ B → 1 ≤ P → ∀ f : IntegerIdeal,
      f ≠ ⊥ → Squarefree f → f ⊔ c = ⊤ → P ≤ norm f →
      ∀ R V : Finset IntegerIdeal, R ⊆ Sieve.idealAdmissibleFinset F c (2*B) →
      V ⊆ C.columns → ∀ r v z : IntegerIdeal → ℂ,
      (∀ a ∈ R, ‖r a‖ ≤ 1) → (∀ u ∈ V, ‖v u‖ ≤ 1) →
      (∑ a ∈ R, ‖∑ u ∈ V, if f ∣ u then r a * (z u * (Q.χ u) a) * v u else 0‖^2) ≤
      K * ErrorRectangles.U Q B (C.N / (norm C.d * P)) *
        ∑ u ∈ V, if f ∣ u then ‖z u‖^2 else 0)
    (B P : ℝ) (hB : 1 ≤ B) (hP : 1 ≤ P) (f : IntegerIdeal)
    (hf : ErrorRectangles.InBin P f) (R V : Finset IntegerIdeal)
    (hR : R ⊆ Sieve.idealAdmissibleFinset F c (2*B))
    (hV : V ⊆ C.columns) (hdvd : ∀ u ∈ V, f ∣ u) :
    ∀ z : IntegerIdeal → ℂ,
      (∑ a ∈ R, ‖∑ u ∈ V, z u * (Q.χ u) a‖^2) ≤
        K * ErrorRectangles.U Q B (C.N / (norm C.d * P)) * ∑ u ∈ V, ‖z u‖^2 := by
  intro z
  by_cases hempty : V = ∅
  · simp [hempty]
  obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hs := (Sieve.mem_idealAdmissibleFinset F c _ u).mp (Finset.mem_filter.mp (hV hu)).1
  have hPf : P ≤ norm f := by
    by_cases hp : P = 1
    · simpa [hp] using hf.2.1
    · exact (by simpa [hp] using hf.2.1 : P < norm f).le
  have hsum (z : IntegerIdeal → ℂ) : (∑ u ∈ V, if f ∣ u then z u else 0) = ∑ u ∈ V, z u := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [if_pos (hdvd u hu)]
  have hsumR (z : IntegerIdeal → ℝ) : (∑ u ∈ V, if f ∣ u then z u else 0) = ∑ u ∈ V, z u := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [if_pos (hdvd u hu)]
  simpa only [one_mul, mul_one, hsum, hsumR] using (hop C hCD hN B P hB hP f hf.1 (hs.1.squarefree_of_dvd (hdvd u hu)) (eq_top_iff.mpr
    (hs.2.1 ▸ sup_le_sup_right (Ideal.dvd_iff_le.mp (hdvd u hu)) c)) hPf R V hR hV
    (fun _ => 1) (fun _ => 1) z (by simp) (by simp))

private lemma block_bound (C : Context Q) (R U V : Finset IntegerIdeal)
    (f g : IntegerIdeal) (hU : U ⊆ C.columns.filter (fun u => f ∣ u))
    (hV : V ⊆ C.columns.filter (fun v => g ∣ v))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hUA : ∀ z : IntegerIdeal → ℂ, (∑ r ∈ R, ‖∑ u ∈ U, z u * (Q.χ u) r‖^2) ≤ A * ∑ u ∈ U, ‖z u‖^2)
    (hVB : ∀ z : IntegerIdeal → ℂ, (∑ r ∈ R, ‖∑ v ∈ V, z v * (Q.χ v) r‖^2) ≤ B * ∑ v ∈ V, ‖z v‖^2)
    (w : IntegerIdeal → ℂ) (hw : ∀ u ∈ C.columns, ‖w u‖ ≤ 1) :
    (∑ r ∈ R, ‖block C U V (fun u => quotientCoefficient C u * w u)
      (fun u => quotientCoefficient C u * w u) r‖) ≤
      Real.sqrt (A*B) * Real.sqrt (divisorIncidence C f * divisorIncidence C g) := by
  have hzero (U : Finset IntegerIdeal) (hU : U ⊆ C.columns) : ∀ u ∈ U, u ≠ ⊥ := fun u hu => (col_data C (hU hu)).1
  have hh := LargeDual.finite_coprime_sum_bound R U V
    (hzero U (hU.trans (Finset.filter_subset _ _)))
    (hzero V (hV.trans (Finset.filter_subset _ _))) A B hA hB hUA hVB
    (fun u => quotientCoefficient C u * w u) (fun u => quotientCoefficient C u * w u)
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Real.sqrt_le_sqrt
  have he (U : Finset IntegerIdeal) (f : IntegerIdeal)
      (hU : U ⊆ C.columns.filter (fun u => f ∣ u)) :
      (∑ u ∈ U, (2:ℝ)^(UniqueFactorizationMonoid.normalizedFactors u).toFinset.card *
        ‖quotientCoefficient C u * w u‖^2) ≤ divisorIncidence C f := by
    calc
      _ ≤ ∑ u ∈ U, (2:ℝ)^(UniqueFactorizationMonoid.normalizedFactors u).toFinset.card *
          ‖quotientCoefficient C u‖^2 := by
        apply Finset.sum_le_sum
        intro u hu
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [norm_mul, mul_pow]
        apply mul_le_of_le_one_right (sq_nonneg _)
        have hh := hw u (Finset.mem_filter.mp (hU hu)).1
        nlinarith [norm_nonneg (w u)]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hU (by intros; positivity)
  exact mul_le_mul (he U f hU) (he V g hV) (by positivity) (by unfold divisorIncidence; positivity)

theorem supported_rectangle_bound
    (D : Sieve.AllIndexNormalizedFamilyData Q) (J : ℕ) (hJ : 0 < J) :
    ∃ L : ℝ, 0 < L ∧
      ∀ C : Context Q, C.D = D →
      ∀ B : ℝ, ∀ unit : Bool, (unit = true → B = 1) →
        1 ≤ C.M → 1 ≤ C.N → 1 ≤ B → B ≤ C.K → C.K ≤ C.M →
        1 ≤ norm C.d → norm C.d ≤ 2 * C.N →
        Origin.SupportedTransport C B unit J →
      ∀ e ∈ C.mobiusDivisors,
      ∀ P ∈ Origin.rectangles C B,
      ∀ f g : IntegerIdeal,
        ErrorRectangles.InBin P.1 f → ErrorRectangles.InBin P.2 g →
        (∑ a ∈ C.reflectedRows B unit, ‖weightedDivisorBlock C e f g a‖) ≤
          L * Real.sqrt
            (ErrorRectangles.U Q B (C.N / (norm C.d * P.1)) *
              ErrorRectangles.U Q B (C.N / (norm C.d * P.2))) *
            Real.sqrt (divisorIncidence C f * divisorIncidence C g) := by
  by_cases hcore : D.bad = c
  · obtain ⟨K, hK, hop⟩ := DivisiblePrefix.realized_divisible_column_U D hcore
    refine ⟨2 * K * (((squarefreeBadPool c).card : ℝ) + 1), by positivity, ?_⟩
    intro C hCD B unit hunit hM hN hB hBK hKM hn hnN htransport e he P hP f g hf hg
    have hK0 : 0 ≤ K := by linarith
    have hR := core_rows C B unit hunit hB
    obtain ⟨hP1, hP2, -⟩ := ErrorRectangles.rectangle_endpoints C P (Finset.mem_filter.mp hP).1
    let U1 := C.columns.filter (fun u => f ∣ u ∧ u ≠ ⊤)
    let U2 := C.columns.filter (fun u => f ∣ u ∧ u = ⊤)
    let V1 := C.columns.filter (fun u => g ∣ u)
    let V2 := C.columns.filter (fun u => g ∣ u ∧ u ≠ ⊤)
    have hU1 : U1 ⊆ C.columns.filter (fun u => f ∣ u) := by
      intro u hu; exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2.1⟩
    have hU2 : U2 ⊆ C.columns.filter (fun u => f ∣ u) := by
      intro u hu; exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2.1⟩
    have hV1 : V1 ⊆ C.columns.filter (fun u => g ∣ u) := Finset.Subset.refl _
    have hV2 : V2 ⊆ C.columns.filter (fun u => g ∣ u) := by
      intro u hu; exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2.1⟩
    have hOp (P : ℝ) (hP : 1 ≤ P) (f : IntegerIdeal) (hf : ErrorRectangles.InBin P f)
        (V : Finset IntegerIdeal) (hV : V ⊆ C.columns.filter (fun u => f ∣ u)) :=
      column_operator D C hCD hN K hop B P hB hP f hf (C.reflectedCoreRows B unit) V hR
        (hV.trans (Finset.filter_subset _ _)) (fun u hu => (Finset.mem_filter.mp (hV hu)).2)
    have hA : 0 ≤ K * ErrorRectangles.U Q B (C.N / (norm C.d * P.1)) :=
      mul_nonneg hK0 (Real.sSup_nonneg' ⟨0, Or.inl rfl, le_rfl⟩)
    have hB' : 0 ≤ K * ErrorRectangles.U Q B (C.N / (norm C.d * P.2)) :=
      mul_nonneg hK0 (Real.sSup_nonneg' ⟨0, Or.inl rfl, le_rfl⟩)
    obtain ⟨phase, hphase, hsplit⟩ := LargeDual.supported_primitive_phase_core C
    let score := Real.sqrt (ErrorRectangles.U Q B (C.N / (norm C.d * P.1)) *
        ErrorRectangles.U Q B (C.N / (norm C.d * P.2))) *
      Real.sqrt (divisorIncidence C f * divisorIncidence C g)
    have hs : 0 ≤ score := by dsimp [score]; positivity
    have hroot : Real.sqrt ((K * ErrorRectangles.U Q B (C.N / (norm C.d * P.1))) *
        (K * ErrorRectangles.U Q B (C.N / (norm C.d * P.2)))) =
        K * Real.sqrt (ErrorRectangles.U Q B (C.N / (norm C.d * P.1)) *
          ErrorRectangles.U Q B (C.N / (norm C.d * P.2))) := by
      rw [show (K * ErrorRectangles.U Q B (C.N / (norm C.d * P.1))) *
        (K * ErrorRectangles.U Q B (C.N / (norm C.d * P.2))) =
        K^2 * (ErrorRectangles.U Q B (C.N / (norm C.d * P.1)) *
          ErrorRectangles.U Q B (C.N / (norm C.d * P.2))) by ring,
        Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK0]
    have htbound (t : IntegerIdeal) (ht : t ∈ squarefreeBadPool c) :
        (∑ r ∈ C.reflectedCoreRows B unit, ‖weightedDivisorBlock C e f g (t*r)‖) ≤
          2 * K * score := by
      let w := fun u => phase u (e*t)
      have hw : ∀ u ∈ C.columns, ‖w u‖ ≤ 1 := fun u hu => hphase u hu _
      have h1 := block_bound C (C.reflectedCoreRows B unit) U1 V1 f g hU1 hV1 _ _ hA hB'
        (hOp P.1 hP1 f hf U1 hU1) (hOp P.2 hP2 g hg V1 hV1) w hw
      have h2 := block_bound C (C.reflectedCoreRows B unit) U2 V2 f g hU2 hV2 _ _ hA hB'
        (hOp P.1 hP1 f hf U2 hU2) (hOp P.2 hP2 g hg V2 hV2) w hw
      rw [hroot] at h1 h2
      calc
        _ ≤ ∑ r ∈ C.reflectedCoreRows B unit,
            (‖block C U1 V1 (fun u => quotientCoefficient C u * w u)
              (fun u => quotientCoefficient C u * w u) r‖ +
            ‖block C U2 V2 (fun u => quotientCoefficient C u * w u)
              (fun u => quotientCoefficient C u * w u) r‖) := by
          apply Finset.sum_le_sum
          intro r hr
          have hrc := ((Sieve.mem_idealAdmissibleFinset F c _ _).mp (hR hr)).2.1
          rw [weighted_phase C phase hsplit e t f g r he ht hrc,
            block_split C f g (fun u => quotientCoefficient C u * phase u (e*t))
              (fun u => quotientCoefficient C u * phase u (e*t)) r]
          exact norm_add_le _ _
        _ ≤ 2 * K * score := by
          rw [Finset.sum_add_distrib]
          dsimp [score]
          nlinarith
    calc
      _ ≤ ∑ tr ∈ C.reflectedRowIndices B unit,
          ‖weightedDivisorBlock C e f g (tr.1 * tr.2)‖ := by
        exact Finset.sum_image_le_of_nonneg (by intros; positivity)
      _ ≤ ∑ tr ∈ (squarefreeBadPool c) ×ˢ C.reflectedCoreRows B unit,
          ‖weightedDivisorBlock C e f g (tr.1 * tr.2)‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; positivity)
      _ ≤ ∑ t ∈ squarefreeBadPool c, 2 * K * score := by
        rw [Finset.sum_product]
        exact Finset.sum_le_sum htbound
      _ ≤ _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        change ((squarefreeBadPool c).card : ℝ) * (2 * K * score) ≤ _
        dsimp [score]
        nlinarith [mul_nonneg hK0 hs]
  · refine ⟨1, zero_lt_one, ?_⟩
    intro C hCD
    exact False.elim (hcore (hCD ▸ C.core))

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.OriginFinite

end

end

section

noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.Origin
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
    {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

def divisorBin (P : ℝ) : Finset (Ideal (𝓞 F)) :=
  (boundedNormIdeals F (2 * P)).filter (ErrorRectangles.InBin P)

section

variable (C : Context Q)

def divisorIncidence (f : Ideal (𝓞 F)) : ℝ :=
  ∑ u ∈ C.columns.filter (fun u => f ∣ u),
    (2 : ℝ) ^ (UniqueFactorizationMonoid.normalizedFactors u).toFinset.card *
      ‖C.lam (C.d * u) / (Real.sqrt (norm u) : ℂ)‖ ^ 2

def binIncidence (P : ℝ) : ℝ :=
  ∑ f ∈ divisorBin (F := F) P, divisorIncidence C f

lemma divisorIncidence_nonneg (f : Ideal (𝓞 F)) :
    0 ≤ divisorIncidence C f := by
  unfold divisorIncidence
  positivity

lemma binIncidence_nonneg (P : ℝ) :
    0 ≤ binIncidence C P := Finset.sum_nonneg fun f _ => divisorIncidence_nonneg C f

lemma binIncidence_le (P : ℝ) :
    binIncidence C P ≤ incidenceEnergy C := by
  unfold binIncidence divisorIncidence incidenceEnergy
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro u hu
  have hu0 : u ≠ ⊥ := by
    exact ((Sieve.mem_idealAdmissibleFinset F c _ u).mp
      (Finset.mem_filter.mp hu).1).1.ne_zero
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  calc
    _ ≤ ((idealDivisors u).card : ℝ) *
        ((2 : ℝ) ^ (UniqueFactorizationMonoid.normalizedFactors u).toFinset.card *
          ‖C.lam (C.d * u) / (Real.sqrt (norm u) : ℂ)‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (by
        exact_mod_cast Finset.card_le_card (fun f hf => (mem_idealDivisors hu0).mpr (Finset.mem_filter.mp hf).2)) (by positivity)
    _ = _ := by ring

end

lemma divisorBin_count :
    ∃ H : ℝ, 1 ≤ H ∧ ∀ P : ℝ, 1 ≤ P →
      ((divisorBin (F := F) P).card : ℝ) ≤ H * P := by
  obtain ⟨H, hH, _, hcount⟩ := DedekindZetaZeroFree.LargeSieve.exists_ideal_count_bound_finset F
  refine ⟨2 * H, by linarith, ?_⟩
  intro P hP
  have hc := hcount (2 * P) (by linarith) (divisorBin P)
    (fun f hf => mem_boundedNormIdeals.mp (Finset.mem_filter.mp hf).1)
  nlinarith

section

variable (C : Context Q)

lemma bin_cauchy (P : ℝ × ℝ) :
    (∑ f ∈ divisorBin (F := F) P.1, ∑ g ∈ divisorBin (F := F) P.2,
      Real.sqrt (divisorIncidence C f * divisorIncidence C g)) ≤
      Real.sqrt (((divisorBin (F := F) P.1).card : ℝ) *
        ((divisorBin (F := F) P.2).card : ℝ)) *
        Real.sqrt (binIncidence C P.1 * binIncidence C P.2) := by
  let S := (divisorBin (F := F) P.1) ×ˢ (divisorBin (F := F) P.2)
  have hc := Real.sum_sqrt_mul_sqrt_le
     S
    (fun _ => zero_le_one)
    (fun fg => mul_nonneg (divisorIncidence_nonneg C fg.1) (divisorIncidence_nonneg C fg.2))
  simp only [Real.sqrt_one, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one,
    S, Finset.card_product, Nat.cast_mul, Finset.sum_product] at hc
  simpa only [binIncidence, Finset.sum_mul_sum] using hc

lemma rectangle_score_le (B : ℝ) (P : ℝ × ℝ)
    (hP : P ∈ rectangles C B) :
    Real.sqrt (P.1 * P.2) *
      Real.sqrt (ErrorRectangles.U Q B (C.N / (norm C.d * P.1)) *
        ErrorRectangles.U Q B (C.N / (norm C.d * P.2))) ≤ envelope C B := by
  unfold envelope ErrorRectangles.finiteSup
  apply le_csSup
  · apply Set.Finite.bddAbove
    apply Set.Finite.union (Set.finite_singleton 0)
    convert (rectangles C B).finite_toSet.image (fun P =>
      Real.sqrt (P.1 * P.2) *
        Real.sqrt (ErrorRectangles.U Q B (C.N / (norm C.d * P.1)) *
          ErrorRectangles.U Q B (C.N / (norm C.d * P.2)))) using 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe]
    exact ⟨fun ⟨P, hP, hx⟩ => ⟨P, hP, hx.symm⟩,
      fun ⟨P, hP, hx⟩ => ⟨P, hP, hx.symm⟩⟩
  · exact Or.inr ⟨P, hP, rfl⟩

lemma rectangles_count (B : ℝ) :
    ((rectangles C B).card : ℝ) ≤
      ((ErrorRectangles.scales (C.N / norm C.d)).card : ℝ) ^ 2 := by
  have hc : (rectangles C B).card ≤
      ((ErrorRectangles.scales (C.N / norm C.d)) ×ˢ
        (ErrorRectangles.scales (C.N / norm C.d))).card := Finset.card_le_card (fun _ h =>
      (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1)
  rw [Finset.card_product, ← pow_two] at hc
  exact_mod_cast hc

end

lemma bin_cauchy_count (H : ℝ) (hH : 0 ≤ H)
    (hcount : ∀ P : ℝ, 1 ≤ P → ((divisorBin (F := F) P).card : ℝ) ≤ H * P)
    (C : Context Q) (P : ℝ × ℝ) (hP1 : 1 ≤ P.1) (hP2 : 1 ≤ P.2) :
    (∑ f ∈ divisorBin (F := F) P.1, ∑ g ∈ divisorBin (F := F) P.2,
      Real.sqrt (divisorIncidence C f * divisorIncidence C g)) ≤
      H * Real.sqrt (P.1 * P.2) * Real.sqrt (binIncidence C P.1 * binIncidence C P.2) := by
  apply (bin_cauchy C P).trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  calc
    _ ≤ Real.sqrt ((H * P.1) * (H * P.2)) := by
      apply Real.sqrt_le_sqrt
      exact mul_le_mul (hcount _ hP1) (hcount _ hP2) (Nat.cast_nonneg _)
        (mul_nonneg hH (by linarith))
    _ = H * Real.sqrt (P.1 * P.2) := by
      rw [show (H * P.1) * (H * P.2) = H ^ 2 * (P.1 * P.2) by ring,
        Real.sqrt_mul (sq_nonneg H), Real.sqrt_sq hH]

lemma rectangle_incidence_aggregation (C : Context Q) (B : ℝ) :
    (∑ P ∈ rectangles C B,
      (Real.sqrt (P.1 * P.2) *
        Real.sqrt (ErrorRectangles.U Q B (C.N / (norm C.d * P.1)) *
          ErrorRectangles.U Q B (C.N / (norm C.d * P.2)))) *
        Real.sqrt (binIncidence C P.1 * binIncidence C P.2)) ≤
      ((ErrorRectangles.scales (C.N / norm C.d)).card : ℝ) ^ 2 *
        envelope C B * incidenceEnergy C := by
  have hi : 0 ≤ incidenceEnergy C := by unfold incidenceEnergy; positivity
  have hs : ∀ P : ℝ × ℝ,
      Real.sqrt (binIncidence C P.1 * binIncidence C P.2) ≤ incidenceEnergy C := by
    intro P
    calc
      _ ≤ Real.sqrt (incidenceEnergy C * incidenceEnergy C) := by
        apply Real.sqrt_le_sqrt
        exact mul_le_mul (binIncidence_le C P.1) (binIncidence_le C P.2)
          (binIncidence_nonneg C P.2) hi
      _ = incidenceEnergy C := by rw [← pow_two, Real.sqrt_sq hi]
  calc
    _ ≤ ∑ P ∈ rectangles C B, envelope C B * incidenceEnergy C := by
      apply Finset.sum_le_sum
      intro P hP
      apply mul_le_mul (rectangle_score_le C B P hP) (hs P)
        (Real.sqrt_nonneg _) (envelope_nonneg C B)
    _ = ((rectangles C B).card : ℝ) * envelope C B * incidenceEnergy C := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (rectangles_count C B) (envelope_nonneg C B)) hi

lemma assembly_of_rectangle_sum (H : ℝ) (hH : 0 ≤ H)
    (C : Context Q) (B : ℝ) (unit : Bool)
    (hfinite : ‖coefficientForm C B unit‖ ≤
      H * ∑ e ∈ C.mobiusDivisors, ∑ P ∈ rectangles C B,
        (Real.sqrt (P.1 * P.2) *
          Real.sqrt (ErrorRectangles.U Q B (C.N / (norm C.d * P.1)) *
            ErrorRectangles.U Q B (C.N / (norm C.d * P.2)))) *
          Real.sqrt (binIncidence C P.1 * binIncidence C P.2)) :
    ‖coefficientForm C B unit‖ ≤
      H * assemblyCost C * envelope C B * incidenceEnergy C := by
  apply hfinite.trans
  calc
    _ ≤ H * ∑ e ∈ C.mobiusDivisors,
        ((ErrorRectangles.scales (C.N / norm C.d)).card : ℝ) ^ 2 *
          envelope C B * incidenceEnergy C := by
      apply mul_le_mul_of_nonneg_left _ hH
      exact Finset.sum_le_sum fun _ _ => rectangle_incidence_aggregation C B
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, assemblyCost]; ring

private lemma assembly_of_divisor_sum (H L : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hcount : ∀ P : ℝ, 1 ≤ P → ((divisorBin (F := F) P).card : ℝ) ≤ H * P)
    (C : Context Q) (B : ℝ) (unit : Bool)
    (hfinite : ‖coefficientForm C B unit‖ ≤
      ∑ e ∈ C.mobiusDivisors, ∑ P ∈ rectangles C B,
        L * Real.sqrt (ErrorRectangles.U Q B (C.N / (norm C.d * P.1)) *
          ErrorRectangles.U Q B (C.N / (norm C.d * P.2))) *
          ∑ f ∈ divisorBin (F := F) P.1, ∑ g ∈ divisorBin (F := F) P.2,
            Real.sqrt (divisorIncidence C f * divisorIncidence C g)) :
    ‖coefficientForm C B unit‖ ≤
      (L * H) * assemblyCost C * envelope C B * incidenceEnergy C := by
  apply assembly_of_rectangle_sum (L * H) (mul_nonneg hL hH) C B unit
  apply hfinite.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro P hP
  obtain ⟨hP1, hP2, _⟩ := ErrorRectangles.rectangle_endpoints C P
    (Finset.mem_filter.mp hP).1
  have hh := mul_le_mul_of_nonneg_left (bin_cauchy_count H hH hcount C P hP1 hP2)
    (mul_nonneg hL (Real.sqrt_nonneg
      (ErrorRectangles.U Q B (C.N / (norm C.d * P.1)) *
        ErrorRectangles.U Q B (C.N / (norm C.d * P.2)))))
  convert hh using 1 <;> ring

theorem actual_prefix_rectangle_assembly
    (D : Sieve.AllIndexNormalizedFamilyData Q) (J : ℕ) (hJ : 0 < J) :
    ∃ H : ℝ, 0 < H ∧
      ∀ C : Context Q, C.D = D →
      ∀ B : ℝ, ∀ unit : Bool, (unit = true → B = 1) →
        1 ≤ C.M → 1 ≤ C.N → 1 ≤ B → B ≤ C.K → C.K ≤ C.M →
        1 ≤ norm C.d → norm C.d ≤ 2 * C.N →
        SupportedTransport C B unit J → ShortGeometry C B →
        ‖coefficientForm C B unit‖ ≤
          H * assemblyCost C * envelope C B * incidenceEnergy C := by
  obtain ⟨L, hL, hcell⟩ := OriginFinite.supported_rectangle_bound D J hJ
  obtain ⟨H, hH, hcount⟩ := divisorBin_count (F := F)
  refine ⟨L * H, mul_pos hL (by linarith), ?_⟩
  intro C hCD B unit hunit hM hN hB hBK hKM hn hnN htransport hgeometry
  apply assembly_of_divisor_sum H L (by linarith) hL.le hcount C B unit
  apply (OriginFinite.finite_coefficient_rectangles C B unit hN hn hnN hgeometry).trans
  apply Finset.sum_le_sum
  intro e he
  apply Finset.sum_le_sum
  intro P hP
  have hc : ∀ f ∈ divisorBin P.1, ∀ g ∈ divisorBin P.2,
      (∑ a ∈ C.reflectedRows B unit, ‖OriginFinite.weightedDivisorBlock C e f g a‖) ≤
        L * Real.sqrt (ErrorRectangles.U Q B (C.N / (norm C.d * P.1)) *
          ErrorRectangles.U Q B (C.N / (norm C.d * P.2))) *
          Real.sqrt (divisorIncidence C f * divisorIncidence C g) := fun f hf g hg => hcell C hCD B unit hunit hM hN hB hBK hKM hn hnN htransport
      e he P hP f g (Finset.mem_filter.mp hf).2 (Finset.mem_filter.mp hg).2
  simp only [Finset.mul_sum]
  exact Finset.sum_le_sum fun f hf => Finset.sum_le_sum fun g hg => hc f hf g hg

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.Origin

end

end

section

noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.Origin
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
    {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

private alias support_le_divisors := DedekindZetaZeroFree.LargeSieve.Sieve.MainBoundaryPrefix.PrefixOperatorsAndIncidenceEnergy.primeSupportCost_le_divisorCount

private alias scales_card_bound := DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.LargeDual.LargeDualRectangles.scales_card_le

set_option maxHeartbeats 1000000 in

theorem energy_epsilon (D : Sieve.AllIndexNormalizedFamilyData Q) :
    ∀ ε : ℝ, 0 < ε → ∃ H : ℝ, 0 < H ∧
      ∀ C : Context Q, C.D = D → 1 ≤ C.M → 1 ≤ C.N →
        1 ≤ norm C.d → norm C.d ≤ 2 * C.N →
        assemblyCost C * incidenceEnergy C ≤
          H * Real.rpow (C.M * C.N * norm C.d) ε * weightedEnergy C := by
  intro ε hε
  let t := ε / 5
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨A, hA, hdiv⟩ := DedekindZetaZeroFree.LargeSieve.ideal_divisor_count_le_rpow F t ht
  let L := 2 + 1 / (t * Real.log 2)
  let q := max 1 (norm c)
  let a := A * Real.rpow q t
  let b := L * Real.rpow 2 t
  let i := A * Real.rpow 2 t
  have hA0 : 0 ≤ A := by linarith
  have hq : 1 ≤ q := le_max_left _ _
  have ha : 0 < a := mul_pos (by linarith) (Real.rpow_pos_of_pos (by linarith) _)
  have hb : 0 < b := mul_pos (Vendor.dyadicLength_small_power_constant_pos ht)
    (Real.rpow_pos_of_pos (by norm_num) _)
  have hi : 0 < i := mul_pos (by linarith) (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨a * b ^ 2 * i ^ 2, by positivity, ?_⟩
  intro C hCD hM hN hn hnN
  let R := C.M * C.N * norm C.d
  have hnpos : 0 < norm C.d := by linarith
  have hNpos : 0 < C.N := by linarith
  have hMN : 1 ≤ C.M * C.N := by nlinarith [mul_nonneg (sub_nonneg.mpr hM) (sub_nonneg.mpr hN)]
  have hR : 1 ≤ R := by dsimp [R]; nlinarith [mul_nonneg (sub_nonneg.mpr hMN) (sub_nonneg.mpr hn)]
  have hRpos : 0 < R := by linarith
  have hnR : norm C.d ≤ R := le_mul_of_one_le_left (by linarith) hMN
  have hNR : C.N ≤ R := by
    dsimp [R]
    nlinarith [mul_le_mul_of_nonneg_right hM hNpos.le,
      mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ C.M * C.N)]
  have hrad0 : (c * C.d).radical ≠ ⊥ := by
    intro h
    have hc : c ≠ ⊥ := by simpa only [C.core] using C.D.bad_ne_bot
    exact (mul_ne_zero hc C.hd0) (bot_unique (h ▸ Ideal.le_radical))
  have hradnorm : norm (c * C.d).radical ≤ q * R := by
    have hc : c ≠ ⊥ := by simpa only [C.core] using C.D.bad_ne_bot
    have hcd : c * C.d ≠ ⊥ := mul_ne_zero hc C.hd0
    have hle : norm (c * C.d).radical ≤ norm (c * C.d) := by
      unfold norm
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero
        (Ideal.absNorm_eq_zero_iff.not.mpr hcd))
        (map_dvd Ideal.absNorm (Ideal.dvd_iff_le.mpr Ideal.le_radical))
    have hmul : norm (c * C.d) = norm c * norm C.d := by
      simp only [norm, map_mul, Nat.cast_mul]
    rw [hmul] at hle
    exact hle.trans ((mul_le_mul_of_nonneg_right (le_max_right _ _) hnpos.le).trans
      (mul_le_mul_of_nonneg_left hnR (by linarith)))
  have hfixed : (C.mobiusDivisors.card : ℝ) ≤ a * Real.rpow R t := by
    calc
      _ ≤ A * Real.rpow (norm (c * C.d).radical) t := hdiv _
      _ ≤ A * Real.rpow (q * R) t := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by unfold norm; positivity) hradnorm ht.le) hA0
      _ = _ := by dsimp [a]; rw [Real.mul_rpow (by linarith) hRpos.le]; ring
  have hmax : max 1 (C.N / norm C.d) ≤ R := by
    apply max_le hR
    exact (div_le_self hNpos.le hn).trans hNR
  have hscales : ((ErrorRectangles.scales (C.N / norm C.d)).card : ℝ) ≤
      b * Real.rpow R t := by
    calc
      _ ≤ (Vendor.dyadicLength (2 * max 1 (C.N / norm C.d)) + 1 : ℝ) :=
        scales_card_bound _
      _ ≤ L * Real.rpow (2 * max 1 (C.N / norm C.d)) t :=
        Vendor.dyadicLength_small_power ht (by nlinarith [le_max_left 1 (C.N / norm C.d)])
      _ ≤ L * Real.rpow (2 * R) t := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by linarith) ht.le)
        (Vendor.dyadicLength_small_power_constant_pos ht).le
      _ = _ := by dsimp [b]; rw [Real.mul_rpow (by norm_num) hRpos.le]; ring
  have hinc : incidenceEnergy C ≤ (i * Real.rpow R t) ^ 2 * weightedEnergy C := by
    unfold incidenceEnergy weightedEnergy
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u hu
    have hu' := (Finset.mem_filter.mp hu).1
    have hu0 : u ≠ ⊥ := fun h => Sieve.bot_not_mem_idealAdmissibleFinset F c _ (h ▸ hu')
    have hunorm : norm u ≤ 2 * R := by
      have hm := (Sieve.mem_idealAdmissibleFinset F c _ u).mp hu'
      have hh : C.N / norm C.d ≤ R := (div_le_self hNpos.le hn).trans hNR
      have hh2 : 2 * C.N / norm C.d ≤ 2 * R := by
        rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hh (by norm_num)
      exact hm.2.2.trans hh2
    have hcount : ((idealDivisors u).card : ℝ) ≤ i * Real.rpow R t := by
      calc
        _ ≤ A * Real.rpow (norm u) t := hdiv u
        _ ≤ A * Real.rpow (2 * R) t := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by unfold norm; positivity) hunorm ht.le) hA0
        _ = _ := by dsimp [i]; rw [Real.mul_rpow (by norm_num) hRpos.le]; ring
    have hsupport := (support_le_divisors u hu0).trans hcount
    have hp : 0 ≤ i * Real.rpow R t := mul_nonneg hi.le (Real.rpow_nonneg hRpos.le _)
    have hh := mul_le_mul hsupport hcount (Nat.cast_nonneg _) hp
    rw [← pow_two] at hh
    exact mul_le_mul_of_nonneg_right hh (sq_nonneg _)
  have hcost : assemblyCost C ≤ (a * Real.rpow R t) * (b * Real.rpow R t) ^ 2 := by
    unfold assemblyCost
    exact mul_le_mul hfixed (pow_le_pow_left₀ (Nat.cast_nonneg _) hscales 2)
      (sq_nonneg _) (mul_nonneg ha.le (Real.rpow_nonneg hRpos.le _))
  have hw : 0 ≤ weightedEnergy C := by unfold weightedEnergy; positivity
  calc
    assemblyCost C * incidenceEnergy C ≤
        ((a * Real.rpow R t) * (b * Real.rpow R t) ^ 2) *
          ((i * Real.rpow R t) ^ 2 * weightedEnergy C) :=
      mul_le_mul hcost hinc (by unfold incidenceEnergy; positivity)
        (mul_nonneg (mul_nonneg ha.le (Real.rpow_nonneg hRpos.le _)) (sq_nonneg _))
    _ = (a * b ^ 2 * i ^ 2) * (Real.rpow R t) ^ 5 * weightedEnergy C := by ring
    _ = _ := by
      have hpow : (Real.rpow R t) ^ 5 = Real.rpow R ε := by
        change (R ^ t) ^ (5 : ℕ) = R ^ ε
        rw [← Real.rpow_mul_natCast hRpos.le t 5]
        congr 1
        dsimp [t]
        ring
      rw [hpow]

theorem coefficient_estimate
    (D : Sieve.AllIndexNormalizedFamilyData Q) (δ : ℝ) (hδ : 0 < δ) :
    ∀ ε : ℝ, 0 < ε → ∃ H : ℝ, 0 < H ∧
      ∀ C : Context Q, C.D = D → C.δ = δ →
      ∀ (B : ℝ) (unit : Bool), (unit = true → B = 1) →
        1 ≤ C.M → 1 ≤ C.N → 1 ≤ B → B ≤ C.K → C.K ≤ C.M →
        1 ≤ norm C.d → norm C.d ≤ 2 * C.N →
        ‖coefficientForm C B unit‖ ≤
          H * Real.rpow (C.M * C.N * norm C.d) ε * envelope C B *
            weightedEnergy C := by
  intro ε hε
  obtain ⟨J, hJ, htransport⟩ := primitive_supported_transport D
  obtain ⟨A, hA, hassembly⟩ := actual_prefix_rectangle_assembly D J hJ
  obtain ⟨E, hE, henergy⟩ := energy_epsilon D ε hε
  refine ⟨A * E, mul_pos hA hE, ?_⟩
  intro C hCD hCδ B unit hunit hM hN hB hBK hKM hn hnN
  calc
    _ ≤ A * assemblyCost C * envelope C B * incidenceEnergy C := (hassembly C hCD B unit hunit hM hN hB hBK hKM hn hnN
      (htransport C hCD B unit hunit hM hN hB hBK hKM)
      (short_divisor_geometry C B hM hN (hCδ ▸ hδ) hB hBK hKM hn hnN))
    _ = (A * envelope C B) * (assemblyCost C * incidenceEnergy C) := by ring
    _ ≤ (A * envelope C B) *
        (E * Real.rpow (C.M * C.N * norm C.d) ε * weightedEnergy C) :=
      mul_le_mul_of_nonneg_left (henergy C hCD hM hN hn hnN) (mul_nonneg hA.le (envelope_nonneg C B))
    _ = _ := by ring

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.Origin

end

end
