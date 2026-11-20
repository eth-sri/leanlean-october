module

public import DedekindZetaZeroFree.Arithmetic.Ideals.LinearCountingBound
public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.AdmissibleRangeBoundaryCases
public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.CharacterValues

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

section

variable (F : Type) [Field F] [NumberField F] (c : Ideal (𝓞 F)) (T : ℝ)

private lemma card_paperShell_le {A : ℝ}
    (count : ∀ X : ℝ, 1 ≤ X → ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F X).card : ℝ) ≤ A * X)
    (hT : 1 ≤ 2 * T) :
    ((paperShell F c T).card : ℝ) ≤ A * (2 * T) := by
  exact le_trans (by exact_mod_cast (Finset.card_le_card (by
    intro I hI
    rw [mem_paperShell] at hI
    rw [DedekindZetaZeroFree.LargeSieve.mem_boundedNormIdeals]
    exact hI.2.2.2))) (count (2 * T) hT)

private lemma paperShell_subset_singleton_top (hT : T < 1) :
    paperShell F c T ⊆ {⊤} := by
  intro I hI
  rw [Finset.mem_singleton]
  rw [mem_paperShell] at hI
  obtain ⟨hsf, hcop, -, hle⟩ := hI
  have hlt2 : Ideal.absNorm I < 2 := by
    have h : (Ideal.absNorm I : ℝ) < 2 := lt_of_le_of_lt hle (by linarith)
    exact_mod_cast h
  exact Ideal.absNorm_eq_one_iff.mp (le_antisymm (by omega) (Nat.one_le_iff_ne_zero.mpr (fun h0 =>
    (fun h => bot_not_mem_idealAdmissibleFinset F c (2 * T) (h ▸ ((mem_idealAdmissibleFinset F c (2 * T) I).mpr ⟨hsf, hcop, hle⟩))) ((Ideal.absNorm_eq_zero_iff).mp h0))))

private lemma card_paperShell_le_one (hT : T < 1) : (paperShell F c T).card ≤ 1 := by
  have := Finset.card_le_card (paperShell_subset_singleton_top F c T hT)
  exact this

end

section

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c) {q : Ideal (𝓞 F)} (hcq : c ∣ q)

include hcq in
private lemma inner_paperShell_sq_le (T : ℝ)
    (μ α : Ideal (𝓞 F) → ℂ)
    (hα : ∀ u ∈ paperShell F q T, ‖α u‖ ≤ 1) (v : Ideal (𝓞 F)) :
    ‖∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v‖ ^ 2 ≤
      ((paperShell F q T).card : ℝ) * ∑ u ∈ paperShell F q T, ‖μ u‖ ^ 2 := by
  have hterm : ∀ u ∈ paperShell F q T, ‖μ u * α u * (Q.χ u) v‖ ≤ ‖μ u‖ := by
    intro u hu
    rw [norm_mul, norm_mul]
    have hprod : ‖α u‖ * ‖(Q.χ u) v‖ ≤ 1 := by
      simpa using mul_le_mul (hα u hu) (by
        rw [mem_paperShell] at hu
        obtain ⟨hsf, hcop, -, -⟩ := hu
        exact DedekindZetaZeroFree.LargeSieve.quadraticFamily_norm_le_one Q hsf (top_le_iff.mp (le_trans (le_of_eq hcop.symm) (sup_le_sup_left (by
          obtain ⟨d, rfl⟩ := hcq
          exact Ideal.mul_le_left) u))) v) (norm_nonneg ((Q.χ u) v)) zero_le_one
    calc ‖μ u‖ * ‖α u‖ * ‖(Q.χ u) v‖ = ‖μ u‖ * (‖α u‖ * ‖(Q.χ u) v‖) := by ring
      _ ≤ ‖μ u‖ * 1 := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
      _ = ‖μ u‖ := by ring
  have hsum :=
    le_trans (norm_sum_le _ _) (Finset.sum_le_sum hterm)
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (paperShell F q T)
      (fun u => ‖μ u‖) (fun _ => (1 : ℝ))
  have hCS' : (∑ u ∈ paperShell F q T, ‖μ u‖) ^ 2 ≤
      (∑ u ∈ paperShell F q T, ‖μ u‖ ^ 2) * ((paperShell F q T).card : ℝ) := by
    simpa [Finset.sum_const, nsmul_eq_mul] using hCS
  calc ‖∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v‖ ^ 2
      ≤ (∑ u ∈ paperShell F q T, ‖μ u‖) ^ 2 := by
        nlinarith [hsum, norm_nonneg (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v),
          Finset.sum_nonneg (fun u (_ : u ∈ paperShell F q T) => norm_nonneg (μ u))]
    _ ≤ (∑ u ∈ paperShell F q T, ‖μ u‖ ^ 2) * ((paperShell F q T).card : ℝ) := hCS'
    _ = ((paperShell F q T).card : ℝ) * ∑ u ∈ paperShell F q T, ‖μ u‖ ^ 2 := by ring

include hcq in
private lemma masked_sum_le_card_mul (S T : ℝ)
    (μ α β : Ideal (𝓞 F) → ℂ)
    (hα : ∀ u ∈ paperShell F q T, ‖α u‖ ≤ 1)
    (hβ : ∀ v ∈ paperShell F q S, ‖β v‖ ≤ 1) :
    (∑ v ∈ paperShell F q S, ‖β v * (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)‖ ^ 2)
      ≤ ((paperShell F q S).card : ℝ) *
          (((paperShell F q T).card : ℝ) * ∑ u ∈ paperShell F q T, ‖μ u‖ ^ 2) := by
  have hstep : ∀ v ∈ paperShell F q S,
      ‖β v * (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)‖ ^ 2 ≤
        ((paperShell F q T).card : ℝ) * ∑ u ∈ paperShell F q T, ‖μ u‖ ^ 2 := by
    intro v hv
    have hX : ‖β v * (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)‖ ≤
        ‖∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v‖ := by
      rw [norm_mul]
      calc _ ≤ 1 * _ := mul_le_mul_of_nonneg_right (hβ v hv) (norm_nonneg _)
        _ = _ := one_mul _
    calc ‖β v * (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)‖ ^ 2
        ≤ ‖∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v‖ ^ 2 := by
          nlinarith [hX,
            norm_nonneg (β v * (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)),
            norm_nonneg (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)]
      _ ≤ _ := (inner_paperShell_sq_le Q hcq T μ α hα v)
  calc (∑ v ∈ paperShell F q S, ‖β v * (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)‖ ^ 2)
      ≤ ∑ v ∈ paperShell F q S,
          (((paperShell F q T).card : ℝ) * ∑ u ∈ paperShell F q T, ‖μ u‖ ^ 2) :=
        Finset.sum_le_sum hstep
    _ = ((paperShell F q S).card : ℝ) *
          (((paperShell F q T).card : ℝ) * ∑ u ∈ paperShell F q T, ‖μ u‖ ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]

end

private lemma two_A_scale_le {A C ε x E : ℝ} (hA : 1 ≤ A) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hx : 1 ≤ x) (hE : 0 ≤ E) :
    2 * A * x * E ≤ (C + 2 * A + 1) * x ^ ε * (x + 1) * E := by
  have hr := Real.one_le_rpow hx hε
  have hx0 : 0 ≤ x := by linarith
  have hxl : x ≤ x ^ ε * (x + 1) := by
    calc x = 1 * x := by ring
      _ ≤ x ^ ε * x := mul_le_mul_of_nonneg_right hr hx0
      _ ≤ x ^ ε * (x + 1) := mul_le_mul_of_nonneg_left (by linarith) (le_trans zero_le_one hr)
  calc _ ≤ (C + 2 * A + 1) * x * E := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hx0) hE
    _ ≤ (C + 2 * A + 1) * x ^ ε * (x + 1) * E := by
        apply mul_le_mul_of_nonneg_right _ hE
        calc _ ≤ (C + 2 * A + 1) * (x ^ ε * (x + 1)) :=
              mul_le_mul_of_nonneg_left hxl (by linarith)
          _ = (C + 2 * A + 1) * x ^ ε * (x + 1) := by ring

variable (F : Type) [Field F] [NumberField F] (c : Ideal (𝓞 F))
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c) (q : Ideal (𝓞 F)) (hq : q ≠ ⊥) (hcq : c ∣ q)
    (ε C A : ℝ) (hε : 0 ≤ ε) (hC : 0 ≤ C) (hA : 1 ≤ A)
    (count : ∀ X : ℝ, 1 ≤ X → ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F X).card : ℝ) ≤ A * X)
    (core : ∀ S T : ℝ, 1 ≤ S → 1 ≤ T → ∀ μ : Ideal (𝓞 F) → ℂ, (∑ v ∈ paperShell F q S, ‖∑ u ∈ paperShell F q T, μ u * (Q.χ u) v‖ ^ 2) ≤ C * (S * T) ^ ε * (S + T) * ∑ u ∈ paperShell F q T, ‖μ u‖ ^ 2)

include hq hcq hε hC hA count core in
theorem peeling_masked_small_shells
    (S T : ℝ) (hS : 0 < S) (hT : 0 < T)
    (μ α β : Ideal (𝓞 F) → ℂ)
    (hα : ∀ u ∈ paperShell F q T, ‖α u‖ ≤ 1)
    (hβ : ∀ v ∈ paperShell F q S, ‖β v‖ ≤ 1) :
    (∑ v ∈ paperShell F q S,
      ‖β v * (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)‖ ^ 2) ≤
      (C + 2 * A + 1) * (max 1 S * max 1 T) ^ ε * (max 1 S + max 1 T) *
        ∑ u ∈ paperShell F q T, ‖μ u‖ ^ 2 := by
  set E := ∑ u ∈ paperShell F q T, ‖μ u‖ ^ 2 with hE
  have hE0 : 0 ≤ E := by rw [hE]; exact Finset.sum_nonneg (fun u _ => sq_nonneg _)
  rcases le_or_gt 1 S with hS1 | hS1
  · rcases le_or_gt 1 T with hT1 | hT1
    ·
      have hinner : ∑ u ∈ paperShell F q T, ‖μ u * α u‖ ^ 2 ≤ E := by
        rw [hE]
        apply Finset.sum_le_sum
        intro u hu
        rw [norm_mul, mul_pow]
        calc _ ≤ ‖μ u‖ ^ 2 * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) (hα u hu)) (sq_nonneg _)
          _ = ‖μ u‖ ^ 2 := by ring
      have hstep1 : (∑ v ∈ paperShell F q S,
            ‖β v * (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)‖ ^ 2)
          ≤ ∑ v ∈ paperShell F q S,
            ‖∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro v hv
        have hX : ‖β v * (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)‖ ≤
            ‖∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v‖ := by
          rw [norm_mul]
          calc _ ≤ 1 * _ := mul_le_mul_of_nonneg_right (hβ v hv) (norm_nonneg _)
            _ = _ := one_mul _
        nlinarith [hX,
          norm_nonneg (β v * (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)),
          norm_nonneg (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)]
      calc (∑ v ∈ paperShell F q S,
            ‖β v * (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)‖ ^ 2)
          ≤ (∑ v ∈ paperShell F q S,
              ‖∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v‖ ^ 2) := hstep1
        _ ≤ C * (S * T) ^ ε * (S + T) * ∑ u ∈ paperShell F q T, ‖μ u * α u‖ ^ 2 := (core S T hS1 hT1 (fun u => μ u * α u))
        _ ≤ C * (S * T) ^ ε * (S + T) * E :=
              mul_le_mul_of_nonneg_left hinner (by
                positivity)
        _ ≤ (C + 2 * A + 1) * (max 1 S * max 1 T) ^ ε * (max 1 S + max 1 T) * E := by
              rw [max_eq_right hS1, max_eq_right hT1]
              have hP : 0 ≤ (S * T) ^ ε * (S + T) * E := by
                positivity
              nlinarith [hP, hA, hC, hE0]
    ·
      have hmid : ((paperShell F q S).card : ℝ) * (((paperShell F q T).card : ℝ) * E)
          ≤ (2 * A * S) * E := by
        calc _
            ≤ ((paperShell F q S).card : ℝ) * (1 * E) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by
                exact_mod_cast card_paperShell_le_one F q T hT1) hE0) (Nat.cast_nonneg _)
          _ = ((paperShell F q S).card : ℝ) * E := by ring
          _ ≤ (2 * A * S) * E := mul_le_mul_of_nonneg_right (by nlinarith [(card_paperShell_le F q S count (by linarith))]) hE0
      have htarget : (2 * A * S) * E ≤
          (C + 2 * A + 1) * (max 1 S * max 1 T) ^ ε * (max 1 S + max 1 T) * E := by
        rw [max_eq_right hS1, max_eq_left (le_of_lt hT1), mul_one]
        exact two_A_scale_le hA hC hε hS1 hE0
      calc (∑ v ∈ paperShell F q S,
            ‖β v * (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)‖ ^ 2)
          ≤ ((paperShell F q S).card : ℝ) * (((paperShell F q T).card : ℝ) * E) := (masked_sum_le_card_mul Q hcq S T μ α β hα hβ)
        _ ≤ (2 * A * S) * E := hmid
        _ ≤ (C + 2 * A + 1) * (max 1 S * max 1 T) ^ ε * (max 1 S + max 1 T) * E := htarget
  · rcases le_or_gt 1 T with hT1 | hT1
    ·
      have hmid : ((paperShell F q S).card : ℝ) * (((paperShell F q T).card : ℝ) * E)
          ≤ (2 * A * T) * E := by
        calc _
            ≤ 1 * (((paperShell F q T).card : ℝ) * E) := mul_le_mul_of_nonneg_right (by
              exact_mod_cast card_paperShell_le_one F q S hS1) (by positivity)
          _ = ((paperShell F q T).card : ℝ) * E := by ring
          _ ≤ (2 * A * T) * E := mul_le_mul_of_nonneg_right (by nlinarith [(card_paperShell_le F q T count (by linarith))]) hE0
      have htarget : (2 * A * T) * E ≤
          (C + 2 * A + 1) * (max 1 S * max 1 T) ^ ε * (max 1 S + max 1 T) * E := by
        rw [max_eq_left (le_of_lt hS1), max_eq_right hT1, one_mul, show (1 : ℝ) + T = T + 1 by ring]
        exact two_A_scale_le hA hC hε hT1 hE0
      calc (∑ v ∈ paperShell F q S,
            ‖β v * (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)‖ ^ 2)
          ≤ ((paperShell F q S).card : ℝ) * (((paperShell F q T).card : ℝ) * E) := (masked_sum_le_card_mul Q hcq S T μ α β hα hβ)
        _ ≤ (2 * A * T) * E := hmid
        _ ≤ (C + 2 * A + 1) * (max 1 S * max 1 T) ^ ε * (max 1 S + max 1 T) * E := htarget
    ·
      have hmid : ((paperShell F q S).card : ℝ) * (((paperShell F q T).card : ℝ) * E) ≤ E := by
        calc _
            ≤ 1 * (1 * E) := mul_le_mul (by
              exact_mod_cast card_paperShell_le_one F q S hS1) (mul_le_mul_of_nonneg_right (by
              exact_mod_cast card_paperShell_le_one F q T hT1) hE0) (by positivity) zero_le_one
          _ = E := by ring
      have htarget : E ≤
          (C + 2 * A + 1) * (max 1 S * max 1 T) ^ ε * (max 1 S + max 1 T) * E := by
        rw [max_eq_left (le_of_lt hS1), max_eq_left (le_of_lt hT1)]
        have hmain : (1 : ℝ) ≤ (C + 2 * A + 1) * ((1 : ℝ) * 1) ^ ε * (1 + 1) := by
          calc _ = (1 * 1) * 1 := by ring
            _ ≤ ((C + 2 * A + 1) * ((1 : ℝ) * 1) ^ ε) * (1 + 1) := (mul_le_mul (mul_le_mul (by linarith) (by
              rw [mul_one]; exact Real.one_le_rpow le_rfl hε) zero_le_one (by linarith)) (by norm_num) (by norm_num) (by positivity))
            _ = (C + 2 * A + 1) * ((1 : ℝ) * 1) ^ ε * (1 + 1) := by ring
        calc E = 1 * E := by ring
          _ ≤ (C + 2 * A + 1) * ((1 : ℝ) * 1) ^ ε * (1 + 1) * E :=
              mul_le_mul_of_nonneg_right hmain hE0
      calc (∑ v ∈ paperShell F q S,
            ‖β v * (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)‖ ^ 2)
          ≤ ((paperShell F q S).card : ℝ) * (((paperShell F q T).card : ℝ) * E) := (masked_sum_le_card_mul Q hcq S T μ α β hα hβ)
        _ ≤ E := hmid
        _ ≤ (C + 2 * A + 1) * (max 1 S * max 1 T) ^ ε * (max 1 S + max 1 T) * E := htarget

include hq hcq hε hC hA count core in
theorem peeling_masked_small_shells_rescaled
    (M N R T0 : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) (hR : 1 ≤ R) (hT0 : 1 ≤ T0)
    (μ α β : Ideal (𝓞 F) → ℂ)
    (hα : ∀ u ∈ paperShell F q (N / T0), ‖α u‖ ≤ 1)
    (hβ : ∀ v ∈ paperShell F q (M / R), ‖β v‖ ≤ 1) :
    (∑ v ∈ paperShell F q (M / R),
      ‖β v * (∑ u ∈ paperShell F q (N / T0), μ u * α u * (Q.χ u) v)‖ ^ 2) ≤
      (C + 2 * A + 1) * (M * N) ^ ε * (M + N) *
        ∑ u ∈ paperShell F q (N / T0), ‖μ u‖ ^ 2 := by
  have hRpos : (0 : ℝ) < R := by linarith
  have hT0pos : (0 : ℝ) < T0 := by linarith
  have hSle : max 1 (M / R) ≤ M := by
    apply max_le (by linarith)
    rw [div_le_iff₀ hRpos]
    nlinarith
  have hTle : max 1 (N / T0) ≤ N := by
    apply max_le (by linarith)
    rw [div_le_iff₀ hT0pos]
    nlinarith
  have hT0' : 0 ≤ max 1 (N / T0) := le_trans zero_le_one (le_max_left _ _)
  calc (∑ v ∈ paperShell F q (M / R),
        ‖β v * (∑ u ∈ paperShell F q (N / T0), μ u * α u * (Q.χ u) v)‖ ^ 2)
      ≤ (C + 2 * A + 1) * (max 1 (M / R) * max 1 (N / T0)) ^ ε *
          (max 1 (M / R) + max 1 (N / T0)) * ∑ u ∈ paperShell F q (N / T0), ‖μ u‖ ^ 2 := (peeling_masked_small_shells F c Q q hq hcq ε C A hε hC hA count core
            (M / R) (N / T0) (div_pos (by linarith) hRpos) (div_pos (by linarith) hT0pos) μ α β hα hβ)
    _ ≤ (C + 2 * A + 1) * (M * N) ^ ε * (M + N) *
          ∑ u ∈ paperShell F q (N / T0), ‖μ u‖ ^ 2 := by
        gcongr

end DedekindZetaZeroFree.LargeSieve.Sieve
