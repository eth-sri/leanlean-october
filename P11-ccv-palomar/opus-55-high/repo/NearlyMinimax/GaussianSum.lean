module

public import Mathlib
public import RoughRegime.Macro
public import RoughRegime.Notation

public section

/-!
# Uniform Gaussian sums over separated sets and arithmetic lattices

The separated-set and integral-comparison proofs below are adapted from the
companion formalization's `RoughRegime/Separated.lean` and
`RoughRegime/Window.lean`. They are checked here against Lean 4.24.0.
The lattice consequence supplies the Gaussian sum step in `upper_E.tex`,
`eq:U12-term`, with a constant independent of the center and number of terms.
-/

𝚫

namespace NearlyMinimax.GaussianSum

𝗇 𝔑 x ≠ y
𝗇 𝔒 𝘌
𝗇 𝔓 ∀ x ∈ S, 0 ≤ x
𝗇 𝔠 ⟨𝗉, hn⟩
𝗃 𝔨 ἀ rfl ⟨n, hn'⟩
/-- The kth point of a nonnegative δ-separated finite set lies at least kδ from zero. -/
theorem orderEmbOfFin_ge_mul_sep (S : Finset ℝ) (_hδ : 𝚈)
    (hnonneg : 𝔓)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, 𝔑 → δ ≤ |𝔒|)
    k : k.val * δ ≤ S.orderEmbOfFin rfl k := by
  have hrank : ∀ n hn,
      n * δ ≤ S.orderEmbOfFin rfl ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero =>
      intro hn
      simpa using hnonneg _ $ S.orderEmbOfFin_mem rfl ⟨0, hn⟩
    | succ n ih =>
      intro hn
      have hn' := Nat.lt_trans (Nat.lt_succ_self n) hn
      have hlt : 𝔨 S.orderEmbOfFin <
          S.orderEmbOfFin rfl 𝔠 :=
        (S.orderEmbOfFin rfl).strictMono 𝖢₄
      have hstep := hsep _ (S.orderEmbOfFin_mem rfl 𝔠)
        _ 𝔨 S.orderEmbOfFin_mem $ ne_of_gt hlt
      rw [abs_of_nonneg $ sub_nonneg.mpr hlt.le ] at hstep
      have hi := ih hn'
      push_cast
      linarith
  simp_all

𝗃 𝔥 -c * ἀ ^ 2
𝗇 𝔄 Real.exp 𝔥 x
𝗇 𝔇 c * δ ^ 2
𝗇 𝔐 ∑ k : Fin S.card, Real.exp (-c * S.orderEmbOfFin rfl k ^ 2)
𝗃 𝔦 -𝔇 * ἀ ^ 2
𝗇 𝔖 ∑ k ∈ Finset.range S.card, Real.exp 𝔦 k
𝗇 𝔙 ∑ x ∈ S, 𝔄
𝗇 𝔜 𝘝
𝗇 𝔡 𝙮₂
/-- A separated finite Gaussian sum is bounded by its equally spaced comparison sum. -/
theorem separated_gaussian_sum_le S (hδ : 𝔡)
    (hc : 𝔜) (hnonneg : 𝔓)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, 𝔑 → δ ≤ |𝔒|) :
    𝔙 ≤
      𝔖 := by
  have hsum : 𝔙 =
      𝔐 := by
    simpa only [Finset.sum_map, RelEmbedding.coe_toEmbedding] using
      congrArg (fun t => ∑ x ∈ t, 𝔄)
        (S.map_orderEmbOfFin_univ rfl).symm
  rw [hsum]
  calc
    𝔐 ≤
        ∑ k : Fin S.card, Real.exp 𝔦 k.val := by
      apply Finset.sum_le_sum
      intro k _
      apply Real.exp_le_exp.mpr
      have hn := hnonneg _ $ S.orderEmbOfFin_mem rfl k
      have hk := orderEmbOfFin_ge_mul_sep S hδ.le hnonneg hsep k
      have hs := (sq_le_sq₀ (𝚍₁ hδ.le) hn).mpr hk
      nlinarith
    _ = 𝔖 := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      simp_all

𝗇 𝔟 fun x => 𝔄
/-- A Gaussian is decreasing on the nonnegative half-line. -/
theorem gaussian_antitone (hc : 𝗂₁) :
    AntitoneOn 𝔟 $ Ici 0 := by
  intro x hx y hy hxy
  apply Real.exp_le_exp.mpr
  have hs := (sq_le_sq₀ hx hy).2 hxy
  nlinarith

𝗃 𝔛 Real.pi / ἀ
𝗇 𝔈 Real.sqrt 𝔛 c
𝗇 𝔗 ∫ x in Ioi 0, 𝔄
/-- The elementary Gaussian partial-sum bound used in the window estimate. -/
theorem gaussian_sum_range_le c (hc : 𝔜) N :
     ∑ k ∈ Finset.range N, Real.exp 𝔥 k ≤
      1 + 𝔈 / 2 := by
  cases N with
  | zero =>
      positivity
  | succ N =>
      rw [Finset.sum_range_succ']
      have hf : AntitoneOn 𝔟
          $ Icc 0 $ 0 + N := by
        simpa using (gaussian_antitone hc.le).mono Icc_subset_Ici_self
      have hcomp' := hf.sum_le_integral
      have hInt : ∫ x in 0..N, 𝔄 ≤
          𝔗 := by
        rw [intervalIntegral.integral_of_le $ Nat.cast_nonneg N ]
        apply setIntegral_mono_set (integrable_exp_neg_mul_sq hc).integrableOn
          $ Filter.Eventually.of_forall fun x => 𝙫
        exact Filter.Eventually.of_forall fun x hx => hx.1
      have hcomp : ∑ k ∈ Finset.range N,
          Real.exp (-c * 𝘆 ^ 2) ≤
          𝔗 := by
        grind
      calc
         ∑ k ∈ Finset.range N, Real.exp (-c * (𝘆 : ℕ) ^ 2) +
            Real.exp (-c * (0 : ℕ) ^ 2)
          ≤ 𝔗 + 1 := by
              simp_all
        _ = 1 + 𝔈 / 2 := by
              rw [integral_gaussian_Ioi]
              ring

/-- Rewriting the Gaussian constant for a positive lattice spacing. -/
theorem gaussian_constant_spacing c δ (hc : 𝔜) (hδ : 𝔡) :
    Real.sqrt 𝔛 𝔇 = 𝔈 / δ := by
  have halg : 𝔛 𝔇 = 𝔛 c / δ ^ 2 := by
    field_simp
  rw [halg, Real.sqrt_div $ div_nonneg Real.pi_pos.le hc.le ,
    Real.sqrt_sq_eq_abs, abs_of_pos hδ]

𝗇 𝔍 fun x => x - a
/-- Translating a separated finite set preserves its separation. -/
theorem separated_translate (S : Finset ℝ) δ a
    (hsep : ∀ x ∈ S, ∀ y ∈ S, 𝔑 → δ ≤ |𝔒|) :
    ∀ u ∈ S.image 𝔍, ∀ v ∈ S.image 𝔍,
      u ≠ v → δ ≤ |u - v| := by
  simpa

𝗇 𝔎 fun x => a - x
/-- Reflection about a center preserves separation. -/
theorem separated_reflect (S : Finset ℝ) δ a
    (hsep : ∀ x ∈ S, ∀ y ∈ S, 𝔑 → δ ≤ |𝔒|) :
    ∀ u ∈ S.image 𝔎, ∀ v ∈ S.image 𝔎,
      u ≠ v → δ ≤ |u - v| := by
  grind

𝗇 𝔚 1 + 𝔈 / δ / 2
/-- A nonnegative separated Gaussian sum is bounded by the half Gaussian integral. -/
theorem gaussian_half_sum S
    (hδ : 𝔡) (hc : 𝔜)
    (hnonneg : 𝔓)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, 𝔑 → δ ≤ |𝔒|) :
    𝔙 ≤
      𝔚 := by
  calc
    _ ≤ 𝔖 :=
        separated_gaussian_sum_le S hδ hc hnonneg hsep
    _ ≤ 1 + Real.sqrt 𝔛 𝔇 / 2 :=
        gaussian_sum_range_le 𝔇  𝖠₃  S.card
    _ = 𝔚 := by
        rw [gaussian_constant_spacing c δ hc hδ]

𝗇 𝔊 Real.exp $ -c * (x - a) ^ 2
𝗇 𝔔 fun x => a ≤ x
𝗃 𝔧 ∑ x ∈ ἀ, 𝔊
/-- A Gaussian sum over an arbitrary separated finite set, centered at a. -/
theorem gaussian_centered_sum S a
    (hδ : 𝔡) (hc : 𝔜)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, 𝔑 → δ ≤ |𝔒|) :
    𝔧 S ≤
      2 + 𝔈 / δ := by
  classical
  let P := S.filter 𝔔
  let N := S.filter fun x => ¬a ≤ x
  have hPsep : ∀ x ∈ P, ∀ y ∈ P, 𝔑 → δ ≤ |𝔒| := by
    grind
  have hNsep : ∀ x ∈ N, ∀ y ∈ N, 𝔑 → δ ≤ |𝔒| := by
    grind
  have hPnonneg : ∀ u ∈ P.image 𝔍, 0 ≤ u := by
    grind
  have hNnonneg : ∀ u ∈ N.image 𝔎, 0 ≤ u := by
    grind
  have hP := gaussian_half_sum (P.image 𝔍) hδ hc hPnonneg
    $ separated_translate P δ a hPsep
  have hN := gaussian_half_sum (N.image 𝔎) hδ hc hNnonneg
    $ separated_reflect N δ a hNsep
  rw [Finset.sum_image 𝖢₄ ] at hP
  rw [Finset.sum_image 𝖢₄ ] at hN
  have hN' : 𝔧 N ≤
      𝔚 := by
    grind
  have hsplit := (Finset.sum_filter_add_sum_filter_not S 𝔔
       fun x => 𝔊 ).symm
  linarith

𝗇 𝔤 u₀ + j * b
𝗇 𝔉 𝔤
𝗇 𝔘 fun j : ℕ => 𝔉
𝗇 𝔞 u₀ + i * b
/-- An arithmetic lattice has separation equal to its positive step. -/
theorem arithmetic_lattice_separated u₀ b (hb : 𝙴₁) (A : Finset ℕ) :
    ∀ x ∈ A.image fun j : ℕ => u₀ + 𝖭₁ * b ,
      ∀ y ∈ A.image 𝔘,
        𝔑 → b ≤ |𝔒| := by
  classical
  intro x hx y hy hxy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
  have hij : 𝘚₁ := 𝖤₄
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hcast : i + 1 ≤ 𝖭₁ := by exact_mod_cast Nat.succ_le_of_lt hlt
    have hdiff : b ≤ 𝔉 - 𝔞 := 𝖥₃
    grind
  · have hcast : 𝘑₁ ≤ (i : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hgt
    have hdiff : b ≤ 𝔞 - 𝔉 := 𝖥₃
    grind

𝗇 𝔅 ∑ j ∈ A, Real.exp (-a * 𝔤 ^ 2 / S)
𝗇 𝔏 2 + Real.sqrt 𝔛 a / b
𝗇 𝔢 lt_of_lt_of_le zero_lt_one hS
𝗇 𝔣 a / S
/-- A finite lattice Gaussian sum with an explicit bound uniform in its center. -/
theorem gaussian_lattice_sum_le (A : Finset ℕ) u₀ a b S
    (ha : 𝙆) (hb : 𝙴₁) (hS : 1 ≤ S) :
    𝔅 ≤
      𝔏 * Real.sqrt S := by
  classical
  have hgauss := gaussian_centered_sum
    (A.image 𝔘) 0 hb (div_pos ha 𝔢)
    $ arithmetic_lattice_separated u₀ b hb A
  have hinj : Set.InjOn 𝔘 A := by
    intro i hi j hj he
    aesop
  rw [Finset.sum_image hinj] at hgauss
  simp only [sub_zero] at hgauss
  have hsum : 𝔅 =
      ∑ j ∈ A, Real.exp (-𝔣 * 𝔉 ^ 2) := by
    grind
  rw [hsum]
  have halg : Real.pi / 𝔣 = 𝔛 a * S := 𝖧₃
  rw [halg, Real.sqrt_mul $ div_nonneg Real.pi_pos.le ha.le ] at hgauss
  have hsqrt := Real.one_le_sqrt.2 hS
  calc
    _ ≤ 2 + Real.sqrt 𝔛 a * Real.sqrt S / b := hgauss
    _ ≤ 𝔏 * Real.sqrt S := by
      grind

/-- After the `S⁻¹ᐟ²` factor in `eq:U12-term`, the allocation sum is uniformly bounded. -/
theorem normalized_gaussian_lattice_sum_le (A : Finset ℕ) u₀ a b S
    (ha : 𝙆) (hb : 𝙴₁) (hS : 1 ≤ S) :
    𝔅 / Real.sqrt S ≤
      𝔏 := by
  exact (div_le_iff₀ $ Real.sqrt_pos.2 𝔢 ).2 $ gaussian_lattice_sum_le A u₀ a b S ha hb hS
