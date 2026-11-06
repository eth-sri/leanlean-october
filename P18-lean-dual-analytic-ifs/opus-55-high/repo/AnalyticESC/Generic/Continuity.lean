module

public import AnalyticESC.Dual.Attractor

public section

set_option hygiene false
local notation "𝕵" => Ψ.ofReal_mem_cl hx
local notation "𝕴" => Φ.ofReal_mem_cl hy
local notation "𝕳" => m / 2
local notation "𝕲" => .inf i
local notation "𝕱" => Ψ.f i
local notation "𝕰" => Φ.f i
local notation "𝕯" => 𝔡 Φ i y
local notation "𝕮" => 𝔡 Ψ i y
local notation "𝔷" => .inf j

local notation "𝔶" => norm_nonneg _

local notation "𝔵" => M * K * n + B

local notation "𝔲" => 1 - c

/-!
# Lemma 2.7

The dual natural projection depends Lipschitz-continuously on the system in the `𝒞²` metric,
uniformly in the word (2.6), so the strong separation of the dual is an open condition.

We write `f_i = Φ.f i`, `g_i = Ψ.f i` and `d = d₂(Φ, Ψ)`, with `Φ ∈ 𝔖_N(ε)` and `Ψ ∈ 𝔖_N(ε')`
for arbitrary `ε, ε' > 0`; all constants depend on `Φ` only. The estimates (2.3)–(2.5) are proved
at the real points of `I`, where all compositions take values in `I`. Since `d₂(Φ, Ψ)` small does
not give `|g_i'| ≤ c_max`, the contraction ratio of `Ψ` on `I` is bounded by `c' = c_max + δ₀ < 1`
and `|g_i'|` from below by `c_min / 2`. Auxiliary results are in the namespace `IFS.Continuity`.
-/

namespace AnalyticESC

open Set

local notation "𝔡₂" => d2 Φ Ψ

namespace IFS.Continuity

/-! ## The real points of `I` in `ℂ` -/

/-- A finite family of maps holomorphic on open sets containing `I` is uniformly Lipschitz
on `I`. -/
theorem exists_lipschitz_I_fin {h : Fin N → ℂ → ℂ} (U : Fin N → Set ℂ)
    (hU : ∀ i, IsOpen (U i)) (hIU : ∀ i, Iℂ ⊆ U i)
    (hh : ∀ i, DifferentiableOn ℂ (h i) (U i)) :
    ∃ L, 0 ≤ L ∧ ∀ i, ∀ a ∈ I, ∀ b ∈ I, ‖h i a - h i b‖ ≤ L * ‖(a : ℂ) - b‖ := by
  choose L hL using fun i => isCompact_image_I.exists_bound_of_continuousOn
    (((hh i).deriv (hU i)).continuousOn.mono (hIU i))
  refine ⟨∑ i, max (L i) 0, Finset.sum_nonneg fun i _ => le_max_right _ _, fun i a ha b hb =>
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (hh i).differentiableAt ((hU i).mem_nhds (hIU i hz)))
      (fun z hz => (hL i z hz).trans ((le_max_left _ _).trans
        (Finset.single_le_sum (f := fun j => max (L j) 0) (fun j _ => le_max_right _ _)
          (Finset.mem_univ i)))) convex_image_I (mem_image_of_mem _ hb) (mem_image_of_mem _ ha)⟩

theorem bddAbove_range_norm_sub {F G : ℂ → ℂ} (hIU : Iℂ ⊆ U)
    (hF : ContinuousOn F U) (hG : ContinuousOn G U) :
    BddAbove (range fun x : I => ‖F x - G x‖) := by
  have h1 : Continuous fun x : I => (x : ℂ) :=
    Complex.continuous_ofReal.comp continuous_subtype_val
  exact (isCompact_range ((hF.comp_continuous h1 (fun x => hIU (mem_image_of_mem _ x.2))).sub (hG.comp_continuous h1 (fun x => hIU (mem_image_of_mem _ x.2)))).norm).bddAbove

/-- The `𝒞²` distance on `I` is nonnegative. -/
theorem d2Map_nonneg f g : 0 ≤ d2Map f g :=
  add_nonneg (add_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _)
    (Real.iSup_nonneg fun _ => norm_nonneg _)) (Real.iSup_nonneg fun _ => norm_nonneg _)


/-! ## Pointwise bounds from `d₂` -/

variable (Φ : IFS N ε) (Ψ : IFS N ε')

theorem d2_nonneg : 0 ≤ 𝔡₂ :=
  Real.iSup_nonneg fun _ => d2Map_nonneg _ _

/-- At a point of `I`, the maps, their derivatives and their second derivatives differ by at
most `d₂(Φ, Ψ)`. -/
theorem norm_sub_le_d2 i {x : ℝ} (hx : x ∈ I) :
    ‖Φ.f i x - Ψ.f i x‖ ≤ 𝔡₂ ∧ ‖𝔡 Φ i x - 𝔡 Ψ i x‖ ≤ 𝔡₂ ∧
      ‖𝔇 𝕰 x - 𝔇 𝕱 x‖ ≤ 𝔡₂ := by
  -- Both systems are holomorphic on `U = B_{2ε} ∩ B_{2ε'}`, which contains `I`.
  have hU : Iℂ ⊆ 𝔑 ε ∩ 𝔑 ε' :=
    subset_inter Φ.image_I_subset_nbhd2
      Ψ.image_I_subset_nbhd2
  have hf := ((Φ.inClass i).differentiableOn).mono (inter_subset_left (t := 𝔑 ε'))
  have hg := ((Ψ.inClass i).differentiableOn).mono (inter_subset_right (s := 𝔑 ε))
  have hO := (isOpen_nbhd (δ := 2 * ε)).inter (isOpen_nbhd (δ := 2 * ε'))
  have e0 := le_ciSup (bddAbove_range_norm_sub hU hf.continuousOn hg.continuousOn) ⟨x, hx⟩
  have e1 := le_ciSup (bddAbove_range_norm_sub hU (hf.deriv hO).continuousOn
    (hg.deriv hO).continuousOn) ⟨x, hx⟩
  have e2 := le_ciSup (bddAbove_range_norm_sub hU ((hf.deriv hO).deriv hO).continuousOn
    ((hg.deriv hO).deriv hO).continuousOn) ⟨x, hx⟩
  have hd : d2Map 𝕰 𝕱 ≤ 𝔡₂ := le_ciSup (f := fun i => d2Map 𝕰 𝕱) (Set.finite_range _).bddAbove i
  simp [d2Map] at hd e0 e1 e2
  exact ⟨by linarith [(norm_nonneg _).trans e1, (norm_nonneg _).trans e2],
    by linarith [(norm_nonneg _).trans e0, (norm_nonneg _).trans e2],
    by linarith [(norm_nonneg _).trans e0, (norm_nonneg _).trans e1]⟩

theorem norm_mul_sub_mul_le (a b x y : ℂ) : ‖a * x - b * y‖ ≤ ‖a‖ * ‖x - y‖ + ‖a - b‖ * ‖y‖ := by
  rw [← norm_mul, ← norm_mul]
  exact (norm_add_le _ _).trans_eq' (by ring_nf)

end IFS.Continuity

namespace IFS


/-- (2.6): `|H_w(x) - Ĥ_w(x)| ≤ C' d₂(Φ, Ψ)` on `I`, for all words, when `Ψ` is close to `Φ`.
We use (2.3)–(2.5) at the real points of `I`. -/
theorem exists_dualProj_sub_le_d2 (Φ : IFS N ε) :
    ∃ C' δ₀, 0 < δ₀ ∧ ∀ {ε' : ℝ} (Ψ : IFS N ε'), 𝔡₂ < δ₀ → ∀ (w : Word N), Ɐ
      ‖Φ.dualProj w x - Ψ.dualProj w x‖ ≤ C' * 𝔡₂ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · -- Without letters, every dual projection vanishes.
    refine ⟨0, 1, one_pos, fun Ψ _ w x _ => ?_⟩
    have (n : ℕ) : w.get? n = none := Subsingleton.elim _ _
    simp [dualProj, dualTerm, this]
  have hc0 := Φ.cmax_nonneg
  have hc1 := Φ.cmax_lt_one
  have hm := Φ.cmin_pos hN
  obtain ⟨M, hM0, hM⟩ := Φ.exists_nonlin_bound
  obtain ⟨L₁, hL₁0, hL₁⟩ := Continuity.exists_lipschitz_I_fin
    (fun _ => 𝔑 ε) (fun _ => isOpen_nbhd)
    (fun _ => Φ.image_I_subset_nbhd2)
    (fun i => (Φ.differentiableOn_f i).deriv isOpen_nbhd)
  choose U hUo hUc hUd using Φ.exists_differentiableOn_nonlin
  obtain ⟨L₂, hL₂0, hL₂⟩ := Continuity.exists_lipschitz_I_fin U hUo
    (fun i => ((image_I_subset_nbhd Φ.ε_pos).trans subset_closure).trans (hUc i)) hUd
  set c := Φ.cmax
  set m := Φ.cmin
  set δ₀ := min (𝔲 / 2) 𝕳
  have hδ₀1 : δ₀ ≤ 𝔲 / 2 := min_le_left _ _
  have hδ₀2 : δ₀ ≤ m / 2 := min_le_right _ _
  have hδ₀ : 0 < δ₀ := lt_min (by linarith) (by linarith)
  set c' := c + δ₀
  have hc'0 : 0 < c' := by linarith
  have hc1' : 0 < 1 - c := by linarith
  set K := (L₁ / 𝔲 + 1) / c' with hK
  set B := L₂ / 𝔲 + (1 + M) / 𝕳 with hB
  have hsum : Summable fun n : ℕ => 𝔵 * c' ^ n := by
    convert ((summable_pow_mul_geometric_of_norm_lt_one 1 (by
      rw [Real.norm_eq_abs, abs_of_pos hc'0]; linarith)).mul_left (M * K)).add
      ((summable_geometric_of_lt_one hc'0.le (by linarith)).mul_left B) using 1
    ext n; ring
  refine ⟨∑' n : ℕ, 𝔵 * c' ^ n, δ₀, hδ₀, fun {ε'} Ψ hΨ w x hx => ?_⟩
  have hd := Continuity.d2_nonneg Φ Ψ
  have hP1 : ∀ i, ∀ y ∈ I, ‖𝔡 Ψ i (y : ℂ)‖ ≤ c' := by
    intro i y hy
    linarith [(Continuity.norm_sub_le_d2 Φ Ψ i hy).2.1,
      Φ.norm_deriv_le_cmax i 𝕴,
      norm_sub_norm_le 𝕮 𝕯,
      norm_sub_rev 𝕮 𝕯]
  have hP2 : ∀ i, ∀ y ∈ I, m / 2 ≤ ‖𝔡 Ψ i y‖ := by
    intro i y hy
    linarith [(Continuity.norm_sub_le_d2 Φ Ψ i hy).2.1,
      Φ.cmin_le_norm_deriv i 𝕴,
      norm_sub_norm_le 𝕯 𝕮]
  have hre : ∀ {η} (Θ : IFS N η) (v : 𝔚 N), ∃ a ∈ I, Θ.comp v x = a :=
    fun Θ v => ⟨_, Θ.re_comp_mem_I v hx, Θ.comp_ofReal v hx⟩
  -- (2.4): `|f_v(x) - g_v(x)| ≤ d / (1 - c_max)`.
  have h24 : ∀ v, ‖Φ.comp v x - Ψ.comp v x‖ ≤ 𝔡₂ / 𝔲 := by
    intro v
    induction v with
    | nil => simp; positivity
    | cons i u ih =>
      obtain ⟨a, ha, hae⟩ := hre Φ u
      obtain ⟨b, hb, hbe⟩ := hre Ψ u
      rw [hae, hbe] at ih
      simp [hae, hbe]
      have h1 := Φ.norm_comp_sub_le [i] (ofReal_mem_nbhd Φ.ε_pos ha) (ofReal_mem_nbhd Φ.ε_pos hb)
      simp at h1
      linarith [norm_sub_le_norm_sub_add_norm_sub (Φ.f i a) (Φ.f i b) (Ψ.f i b),
        (Continuity.norm_sub_le_d2 Φ Ψ i hb).1, mul_le_mul_of_nonneg_left ih hc0,
        mul_div_cancel₀ 𝔡₂ hc1'.ne']
  -- `|g_v'(x)| ≤ c'^{|v|}`.
  have hpow : ∀ v, ‖𝔡ᶜ Ψ v x‖ ≤ c' ^ v.length := by
    intro v
    induction v with
    | nil => simp
    | cons i u ih =>
      obtain ⟨b, hb, hbe⟩ := hre Ψ u
      rw [Ψ.deriv_comp_cons i u 𝕵, hbe, norm_mul,
        List.length_cons, pow_succ']
      exact mul_le_mul (hP1 i b hb) ih 𝔶 hc'0.le
  -- (2.5): `|f_v'(x) - g_v'(x)| ≤ |v| c'^{|v|} K d`.
  have h25 : ∀ v, ‖𝔡ᶜ Φ v x - 𝔡ᶜ Ψ v x‖ ≤
      v.length * c' ^ v.length * K * 𝔡₂ := by
    intro v
    induction v with
    | nil => simp
    | cons i u ih =>
      obtain ⟨a, ha, hae⟩ := hre Φ u
      obtain ⟨b, hb, hbe⟩ := hre Ψ u
      have hab := h24 u
      rw [hae, hbe] at hab
      rw [Φ.deriv_comp_cons i u (Φ.ofReal_mem_cl hx),
        Ψ.deriv_comp_cons i u 𝕵, hae, hbe]
      have hB : ‖𝔡 Φ i a - 𝔡 Ψ i b‖ ≤ K * c' * 𝔡₂ := by
        calc _ ≤ ‖𝔡 Φ i a - 𝔡 Φ i b‖ + ‖𝔡 Φ i b - 𝔡 Ψ i b‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ L₁ * (𝔡₂ / 𝔲) + 𝔡₂ :=
              add_le_add ((hL₁ i a ha b hb).trans (mul_le_mul_of_nonneg_left hab hL₁0))
                (Continuity.norm_sub_le_d2 Φ Ψ i hb).2.1
          _ = K * c' * 𝔡₂ := by rw [hK]; field_simp
      rw [List.length_cons, pow_succ]
      push_cast
      linarith [Continuity.norm_mul_sub_mul_le (𝔡 Φ i a) (𝔡 Ψ i b)
        (𝔡ᶜ Φ u x) (𝔡ᶜ Ψ u x),
        mul_le_mul ((Φ.norm_deriv_le_cmax i (Φ.ofReal_mem_cl ha)).trans
          (by linarith)) ih 𝔶 hc'0.le,
        mul_le_mul hB (hpow u) 𝔶 (by positivity)]
  have hterm : ∀ n, ‖Φ.dualTerm w n x - Ψ.dualTerm w n x‖ ≤
      𝔵 * c' ^ n * 𝔡₂ := fun n => by
    unfold dualTerm
    cases h : w.get? n with
    | none => simp; positivity
    | some i =>
      have hlen : (𝔱).length = n := by
        rw [List.length_reverse, length_take_of_get?_eq_some h]
      obtain ⟨a, ha, hae⟩ := hre Φ 𝔱
      obtain ⟨b, hb, hbe⟩ := hre Ψ 𝔱
      have hab := h24 𝔱
      rw [hae, hbe] at hab
      rw [hae, hbe]
      -- (2.3): `|f_i''/f_i' - g_i''/g_i'| ≤ (1 + M) / (m / 2) · d` at `b`.
      have h23 : ‖Φ.nonlin i b - Ψ.nonlin i b‖ ≤ (1 + M) / 𝕳 * 𝔡₂ := by
        have hf := (Φ.inClass i).deriv_ne_zero _ (Φ.ofReal_mem_cl hb)
        have hg := (Ψ.inClass i).deriv_ne_zero _ (Ψ.ofReal_mem_cl hb)
        obtain ⟨-, h1, h2⟩ := Continuity.norm_sub_le_d2 Φ Ψ i hb
        rw [show Φ.nonlin i b - Ψ.nonlin i b = (𝔇 𝕰 b -
            𝔇 𝕱 b - Φ.nonlin i b * (𝔡 Φ i b - 𝔡 Ψ i b)) /
              𝔡 Ψ i b by simp [nonlin]; field_simp; ring, norm_div]
        exact (div_le_div₀ (by positivity) ((norm_sub_le _ _).trans (add_le_add h2
          ((norm_mul_le _ _).trans (mul_le_mul ((fun i y hy => hM i _ 𝕴) i b hb) h1 𝔶 hM0))))
          (by positivity) (hP2 i b hb)).trans_eq (by ring)
      have := Continuity.norm_mul_sub_mul_le (Φ.nonlin i a) (Ψ.nonlin i b)
        (𝔡ᶜ Φ 𝔱 x) (𝔡ᶜ Ψ 𝔱 x)
      have h1 := mul_le_mul ((fun i y hy => hM i _ 𝕴) i a ha) (h25 𝔱) 𝔶 hM0
      have h2 := mul_le_mul (show ‖Φ.nonlin i a - Ψ.nonlin i b‖ ≤ B * 𝔡₂ by
        rw [hB]
        linarith [norm_sub_le_norm_sub_add_norm_sub (Φ.nonlin i a) (Φ.nonlin i b) (Ψ.nonlin i b),
          hL₂ i a ha b hb, mul_le_mul_of_nonneg_left hab hL₂0,
          show L₂ * (𝔡₂ / 𝔲) = L₂ / 𝔲 * 𝔡₂ by ring])
        (hpow 𝔱) 𝔶 (by positivity)
      rw [hlen] at h1 h2
      linarith
  rw [dualProj, dualProj, ← (Φ.summable_dualTerm w (Φ.ofReal_mem_cl hx)).tsum_sub
    (Ψ.summable_dualTerm w 𝕵)]
  exact tsum_of_norm_bounded (hsum.hasSum.mul_right _) hterm

/-- Lemma 2.7 for `𝔖_N`: if the dual of `Φ` satisfies the SSC, so does the dual of every
`Ψ ∈ 𝔖_N` close to `Φ` in the `𝒞²` metric. The radius depends only on `Φ`, and `Ψ` may lie in
`𝔖_N(ε')` for any `ε'`. -/
theorem lemma_2_7_union (Φ : IFS N ε) (h : Φ.DualSSC) :
    ∃ δ > 0, ∀ {ε' : ℝ} (Ψ : IFS N ε'), 𝔡₂ < δ → Ψ.DualSSC := by
  obtain ⟨δ, hδ, hsep⟩ := Φ.dualSSC_iff_exists_delta.1 h
  obtain ⟨C', δ₀, hδ₀, hC'⟩ := Φ.exists_dualProj_sub_le_d2
  refine ⟨min δ₀ (δ / (3 * (|C'| + 1))), lt_min hδ₀ (by positivity), fun {ε'} Ψ hΨ => ?_⟩
  have hd := Continuity.d2_nonneg Φ Ψ
  have h1 := (lt_div_iff₀ (by positivity)).1 (hΨ.trans_le (min_le_right _ _))
  refine Ψ.dualSSC_iff_exists_delta.2 ⟨δ / 3, by positivity, fun i j hij => ?_⟩
  obtain ⟨⟨x, hx⟩, hxδ⟩ := exists_lt_of_lt_ciSup (hsep i j hij)
  refine lt_of_lt_of_le ?_ (le_ciSup (Continuity.bddAbove_range_norm_sub
    (image_I_subset_nbhd Ψ.ε_pos) (Ψ.differentiableOn_dualProj _).continuousOn
    (Ψ.differentiableOn_dualProj _).continuousOn) ⟨x, hx⟩)
  have tri := norm_sub_le_norm_sub_add_norm_sub (Φ.dualProj 𝕲 x)
    (Ψ.dualProj 𝕲 x) (Φ.dualProj 𝔷 x)
  have tri' := norm_sub_le_norm_sub_add_norm_sub (Ψ.dualProj 𝕲 x)
    (Ψ.dualProj 𝔷 x) (Φ.dualProj 𝔷 x)
  rw [norm_sub_rev (Ψ.dualProj 𝔷 x)] at tri'
  simp only at hxδ ⊢
  linarith [hC' Ψ (by simp_all) 𝕲 x hx, hC' Ψ (by simp_all) 𝔷 x hx,
    mul_le_mul_of_nonneg_right (le_abs_self C') hd]

end IFS

end AnalyticESC
