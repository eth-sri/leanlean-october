module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.Poisson.NormalConvergence

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawEulerProduct31

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.EulerDomain
open DedekindZetaZeroFree.AllRowEuler.InitialSeparation
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem correctionProduct_differentiableOn (U : RawFrequency D.recipe.A) :
    DifferentiableOn ℂ
      (fun p : Coordinates => correctionProduct D.context U p.1 p.2.1 p.2.2) OmegaStar :=
  (correctionProduct_normal_convergence D U).2.2

private theorem subpower_core (δ' : ℝ) (ε : ℝ) (hε : 0 < ε)
    (hgood : ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ (U : RawFrequency D.recipe.A) (pr : LocalFiniteSums.ExteriorPrime D.recipe.A),
        (U.j pr).val = 0 → ∀ p ∈ OmegaStarMargin δ',
          ‖localCorrection D.context U pr p.1 p.2.1 p.2.2 - 1‖ ≤
            C * LocalFiniteSums.Q pr ^ (-1 - δ))
    (hbad' : ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ (U : RawFrequency D.recipe.A) (pr : LocalFiniteSums.ExteriorPrime D.recipe.A),
        (U.j pr).val ≠ 0 → ∀ p ∈ OmegaStarMargin δ',
          ‖localCorrection D.context U pr p.1 p.2.1 p.2.2 - 1‖ ≤
            C * LocalFiniteSums.Q pr ^ (-δ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : RawFrequency D.recipe.A, ∀ p ∈ OmegaStarMargin δ',
      Multipliable (fun pr : LocalFiniteSums.ExteriorPrime D.recipe.A =>
        localCorrection D.context U pr p.1 p.2.1 p.2.2) →
      ‖∏' pr : LocalFiniteSums.ExteriorPrime D.recipe.A,
        localCorrection D.context U pr p.1 p.2.1 p.2.2‖ ≤
          C * D.recipe.A.exteriorNorm U.ideal ^ ε := by
  obtain ⟨Mg, δg, hMg, hδg, hg⟩ := hgood
  obtain ⟨Bb, δb, hBb, hδb, hb⟩ := hbad'
  obtain ⟨K, hK, hsmall⟩ :=
    fixed_small_prime_subpower F D.recipe.A.cS Bb δb ε hBb.le hδb hε
  have hQ : ∀ p : LocalFiniteSums.ExteriorPrime D.recipe.A, 0 < LocalFiniteSums.Q p :=
    fun p => D.recipe.A.exteriorNorm_pos (LocalFiniteSums.primeIdeal p)
  let g : LocalFiniteSums.ExteriorPrime D.recipe.A → ℝ := fun p =>
    Mg * LocalFiniteSums.Q p ^ (-(1 + δg))
  have hg0 : ∀ p, 0 ≤ g p := fun p =>
    mul_nonneg hMg.le (Real.rpow_nonneg (hQ p).le _)
  have hgs : Summable g :=
    CorrectionFactors.exterior_norm_majorant_summable (A := D.recipe.A) Mg (1 + δg)
      (by linarith)
  have hn (a : ℂ) : ‖a‖ ≤ ‖a - 1‖ + 1 := by
    calc ‖a‖ = ‖(a - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖a - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖a - 1‖ + 1 := by rw [norm_one]
  have hloc : ∀ (U : RawFrequency D.recipe.A) (p : Coordinates), p ∈ OmegaStarMargin δ' →
      ∀ pr : LocalFiniteSums.ExteriorPrime D.recipe.A,
      ‖localCorrection D.context U pr p.1 p.2.1 p.2.2‖ ≤
        Real.exp (g pr) * (if (U.j pr).val ≠ 0 then
          1 + Bb * LocalFiniteSums.Q pr ^ (-δb) else 1) := by
    intro U p hp pr
    by_cases hj : (U.j pr).val = 0
    · have hj' : ¬ ((U.j pr).val ≠ 0) := not_not.mpr hj
      rw [if_neg hj', mul_one]
      have h1 := hg U pr hj p hp
      rw [show (-1 - δg) = -(1 + δg) by ring] at h1
      have h2 : ‖localCorrection D.context U pr p.1 p.2.1 p.2.2 - 1‖ ≤ g pr := h1
      have h3 := hn (localCorrection D.context U pr p.1 p.2.1 p.2.2)
      linarith [Real.add_one_le_exp (g pr)]
    · rw [if_pos hj]
      have h1 := hb U pr hj p hp
      have h3 := hn (localCorrection D.context U pr p.1 p.2.1 p.2.2)
      have h4 : 1 ≤ Real.exp (g pr) := Real.one_le_exp_iff.mpr (hg0 pr)
      have h5 : 0 ≤ 1 + Bb * LocalFiniteSums.Q pr ^ (-δb) :=
        add_nonneg zero_le_one (mul_nonneg hBb.le (Real.rpow_nonneg (hQ pr).le _))
      calc ‖localCorrection D.context U pr p.1 p.2.1 p.2.2‖
          ≤ 1 + Bb * LocalFiniteSums.Q pr ^ (-δb) := by linarith
        _ ≤ Real.exp (g pr) * (1 + Bb * LocalFiniteSums.Q pr ^ (-δb)) :=
          le_mul_of_one_le_left h5 h4
  have hfinite : ∀ (U : RawFrequency D.recipe.A) (p : Coordinates), p ∈ OmegaStarMargin δ' →
      ∀ s : Finset (LocalFiniteSums.ExteriorPrime D.recipe.A),
      ‖∏ pr ∈ s, localCorrection D.context U pr p.1 p.2.1 p.2.2‖ ≤
        (Real.exp (∑' pr, g pr) * K) * D.recipe.A.exteriorNorm U.ideal ^ ε := by
    intro U p hp s
    let b : Ideal (𝓞 F) → ℝ := fun I => 1 + Bb * idealNorm I ^ (-δb)
    have hb1 : ∀ I, 1 ≤ b I := by
      intro I
      have hp0 : 0 ≤ idealNorm I := by unfold idealNorm; positivity
      dsimp [b]
      nlinarith [Real.rpow_nonneg hp0 (-δb)]
    have hinj : Function.Injective
        (fun pr : LocalFiniteSums.ExteriorPrime D.recipe.A => pr.val.asIdeal) := by
      intro p q hpq
      exact Subtype.ext (IsDedekindDomain.HeightOneSpectrum.asIdeal_injective hpq)
    have ht : (s.filter (fun pr => (U.j pr).val ≠ 0)).image (fun pr => pr.val.asIdeal) ⊆
        idealPrimeSupport U.ideal.val := by
      intro I hI
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hI
      exact U.mem_idealPrimeSupport (Finset.mem_filter.mp hq).2
    have hbad : (∏ pr ∈ s, if (U.j pr).val ≠ 0 then
        1 + Bb * LocalFiniteSums.Q pr ^ (-δb) else 1) ≤
        K * D.recipe.A.exteriorNorm U.ideal ^ ε := by
      calc (∏ pr ∈ s, if (U.j pr).val ≠ 0 then
            1 + Bb * LocalFiniteSums.Q pr ^ (-δb) else 1)
          = ∏ pr ∈ s.filter (fun pr => (U.j pr).val ≠ 0),
              (1 + Bb * LocalFiniteSums.Q pr ^ (-δb)) := (Finset.prod_filter _ _).symm
        _ = ∏ pr ∈ s.filter (fun pr => (U.j pr).val ≠ 0), b pr.val.asIdeal :=
          Finset.prod_congr rfl (fun pr _ => rfl)
        _ = ∏ I ∈ (s.filter (fun pr => (U.j pr).val ≠ 0)).image
              (fun pr => pr.val.asIdeal), b I :=
          (Finset.prod_image (fun p _ q _ h => hinj h)).symm
        _ ≤ ∏ I ∈ idealPrimeSupport U.ideal.val, b I := by
          apply Finset.prod_le_prod_of_subset_of_one_le₀ ht
          · intro I _; exact zero_le_one.trans (hb1 I)
          · intro I _ _; exact hb1 I
        _ ≤ K * D.recipe.A.exteriorNorm U.ideal ^ ε := hsmall U.ideal
    calc ‖∏ pr ∈ s, localCorrection D.context U pr p.1 p.2.1 p.2.2‖
        ≤ ∏ pr ∈ s, ‖localCorrection D.context U pr p.1 p.2.1 p.2.2‖ :=
          Finset.norm_prod_le _ _
      _ ≤ ∏ pr ∈ s, Real.exp (g pr) * (if (U.j pr).val ≠ 0 then
          1 + Bb * LocalFiniteSums.Q pr ^ (-δb) else 1) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun pr _ => hloc U p hp pr)
      _ = Real.exp (∑ pr ∈ s, g pr) * (∏ pr ∈ s, if (U.j pr).val ≠ 0 then
          1 + Bb * LocalFiniteSums.Q pr ^ (-δb) else 1) := by
        rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      _ ≤ Real.exp (∑' pr, g pr) * (K * D.recipe.A.exteriorNorm U.ideal ^ ε) := by
        apply mul_le_mul
        · exact Real.exp_le_exp.mpr (hgs.sum_le_tsum s (fun pr _ => hg0 pr))
        · exact hbad
        · refine Finset.prod_nonneg (fun pr _ => ?_)
          split_ifs
          · exact add_nonneg zero_le_one
              (mul_nonneg hBb.le (Real.rpow_nonneg (hQ pr).le _))
          · exact zero_le_one
        · exact (Real.exp_pos _).le
      _ = _ := by ring
  refine ⟨Real.exp (∑' pr, g pr) * K, mul_pos (Real.exp_pos _) hK, ?_⟩
  intro U p hp hm
  apply le_of_tendsto' hm.hasProd.norm
  intro s
  simpa only [norm_prod] using hfinite U p hp s

theorem correctionProduct_subpower (δ : ℝ) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : RawFrequency D.recipe.A), ∀ p ∈ OmegaStarMargin δ,
      Multipliable (fun pr : LocalFiniteSums.ExteriorPrime D.recipe.A =>
        localCorrection D.context U pr p.1 p.2.1 p.2.2) ∧
      ‖∏' pr : LocalFiniteSums.ExteriorPrime D.recipe.A,
        localCorrection D.context U pr p.1 p.2.1 p.2.2‖ ≤
          C * D.recipe.A.exteriorNorm U.ideal ^ ε := by
  obtain ⟨G, hG, hg⟩ := EulerGoodPrime.goodFactor_sub_one_le
    (A := D.recipe.A) (σ := D.recipe.σ) (η := D.recipe.target) (hS := D.recipe.traceBad) δ hδ
  obtain ⟨B, d, hB, hd, hb⟩ := EulerBadPrime.badFactor_sub_one_le
    (A := D.recipe.A) (σ := D.recipe.σ) (η := D.recipe.target) (hS := D.recipe.traceBad) δ hδ
  obtain ⟨C, hC, h⟩ := subpower_core D δ ε hε
    ⟨G, δ, hG, hδ, fun U p hp x hx => by
      simpa only [localCorrection, if_pos hp] using hg D.context p U.u x hx⟩
    ⟨B, d, hB, hd, fun U p hp x hx => by
      simpa only [localCorrection, if_neg hp] using hb D.context p (U.j p) hp (U.theta D.context p) x hx⟩
  refine ⟨C, hC, fun U p hp => ?_⟩
  have hm := (correctionProduct_normal_convergence D U).1 p
    (OmegaStarMargin_subset δ hδ hp)
  exact ⟨hm, h U p hp hm⟩

theorem correctionProduct_subpower_of_subset (T : Set Coordinates) (δ : ℝ) (hδ : 0 < δ)
    (hT : T ⊆ OmegaStarMargin δ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : RawFrequency D.recipe.A), ∀ p ∈ T,
      Multipliable (fun pr : LocalFiniteSums.ExteriorPrime D.recipe.A =>
        localCorrection D.context U pr p.1 p.2.1 p.2.2) ∧
      ‖∏' pr : LocalFiniteSums.ExteriorPrime D.recipe.A,
        localCorrection D.context U pr p.1 p.2.1 p.2.2‖ ≤
          C * D.recipe.A.exteriorNorm U.ideal ^ ε := by
  obtain ⟨C, hC, h⟩ := correctionProduct_subpower D δ hδ ε hε
  exact ⟨C, hC, fun U p hp => h U p (hT hp)⟩

theorem correctionProduct_subpower_paddedBoxes (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : RawFrequency D.recipe.A), ∀ p ∈ paddedBoxes,
      Multipliable (fun pr : LocalFiniteSums.ExteriorPrime D.recipe.A =>
        localCorrection D.context U pr p.1 p.2.1 p.2.2) ∧
      ‖∏' pr : LocalFiniteSums.ExteriorPrime D.recipe.A,
        localCorrection D.context U pr p.1 p.2.1 p.2.2‖ ≤
          C * D.recipe.A.exteriorNorm U.ideal ^ ε := by
  obtain ⟨δ, hδ, hsub⟩ := paddedBoxes_subset_OmegaStarMargin
  exact correctionProduct_subpower_of_subset D paddedBoxes δ hδ hsub ε hε

theorem correctionProduct_subpower_boxes (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : RawFrequency D.recipe.A), ∀ p ∈ boxes,
      Multipliable (fun pr : LocalFiniteSums.ExteriorPrime D.recipe.A =>
        localCorrection D.context U pr p.1 p.2.1 p.2.2) ∧
      ‖∏' pr : LocalFiniteSums.ExteriorPrime D.recipe.A,
        localCorrection D.context U pr p.1 p.2.1 p.2.2‖ ≤
          C * D.recipe.A.exteriorNorm U.ideal ^ ε := by
  obtain ⟨C, hC, h⟩ := correctionProduct_subpower_paddedBoxes D ε hε
  exact ⟨C, hC, fun U p hp => h U p (boxes_subset_paddedBoxes hp)⟩

end

end DedekindZetaZeroFree.Quantitative.RawEulerProduct31

namespace DedekindZetaZeroFree.Quantitative.EulerSubpower

open DedekindZetaZeroFree.Quantitative.EulerDomain

noncomputable section

open DedekindZetaZeroFree NumberField

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

private theorem q_eq_exteriorNorm (u : D.Row) :
    D.q u = D.recipe.A.exteriorNorm u.toFrequency.ideal := by
  unfold FixedData.q
  change (Nat.card (D.recipe.A.R ⧸ Ideal.span {u.toFrequency.u}) : ℝ) = _
  rw [u.toFrequency.generates.2, D.recipe.A.exteriorResidue_card] <;> rfl

theorem Hu_subpower (δ : ℝ) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : D.Row, ∀ p ∈ OmegaStarMargin δ,
      p ∈ HuDomain D u ∧ ‖Hu D u p.1 p.2.1 p.2.2‖ ≤ C * D.q u ^ ε := by
  obtain ⟨C, hC, h⟩ := RawEulerProduct31.correctionProduct_subpower D δ hδ ε hε
  refine ⟨C, hC, fun u p hp => ?_⟩
  rw [q_eq_exteriorNorm]
  exact h u.toFrequency.toRaw p hp

theorem Hu_subpower_of_subset (T : Set Coordinates) (δ : ℝ) (hδ : 0 < δ)
    (hT : T ⊆ OmegaStarMargin δ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : D.Row, ∀ p ∈ T,
      p ∈ HuDomain D u ∧ ‖Hu D u p.1 p.2.1 p.2.2‖ ≤ C * D.q u ^ ε := by
  obtain ⟨C, hC, h⟩ := Hu_subpower D δ hδ ε hε
  exact ⟨C, hC, fun u p hp => h u p (hT hp)⟩

theorem Hu_subpower_paddedBoxes (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : D.Row, ∀ p ∈ paddedBoxes,
      p ∈ HuDomain D u ∧ ‖Hu D u p.1 p.2.1 p.2.2‖ ≤ C * D.q u ^ ε := by
  obtain ⟨δ, hδ, hsub⟩ := paddedBoxes_subset_OmegaStarMargin
  exact Hu_subpower_of_subset D paddedBoxes δ hδ hsub ε hε

theorem Hu_subpower_boxes (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : D.Row, ∀ p ∈ boxes,
      p ∈ HuDomain D u ∧ ‖Hu D u p.1 p.2.1 p.2.2‖ ≤ C * D.q u ^ ε := by
  obtain ⟨C, hC, h⟩ := Hu_subpower_paddedBoxes D ε hε
  exact ⟨C, hC, fun u p hp => h u p (boxes_subset_paddedBoxes hp)⟩

end

end DedekindZetaZeroFree.Quantitative.EulerSubpower
