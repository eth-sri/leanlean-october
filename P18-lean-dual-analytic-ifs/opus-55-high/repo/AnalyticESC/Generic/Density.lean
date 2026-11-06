module

public import AnalyticESC.Generic.Continuity
public import AnalyticESC.Generic.Agreement
public import AnalyticESC.Generic.MultiplicativeBump
public import AnalyticESC.Generic.Points

public section

set_option hygiene false
local notation "𝕿" => x p
local notation "𝕾" => x (i, j)
local notation "𝕽" => 1 - Φ.cmax
local notation "𝕼" => B + 1
local notation "𝕻" => i 0
local notation "𝖆" => n + 1

local notation "𝔜" => -K

/-!
# The density step of Theorem 1.4

The proof of Theorem 1.4 in Section 4.2, after the interpolation `IFS.exists_noCoincidence_near`: an IFS whose maps
send `[0,1]` into `(0,1)` and whose compositions along distinct finite words differ on `[0,1]` has
arbitrarily `d₂`-close perturbations whose dual IFS satisfies the SSC.

The proof follows the paper with words of length `n + 1`, to match Lemma 2.6. The points of
Lemma 4.1 and their orbits are split, for each letter `ℓ`, into the set `𝒴_ℓ` of the points
`x_{i,j}` of the bad pairs with `i₁ = ℓ` and the set `𝒵_ℓ` of the remaining orbit points, and
Proposition 4.2 perturbs each map accordingly. A strictly invariant cylinder is fixed first;
uniform continuity estimates in the `d₂` metric give a neighbourhood where its strict
inclusions persist. Only then are `δ` and the word length chosen.
-/

namespace AnalyticESC

open Set Filter

namespace IFS


/-! ## Bounds for the perturbation -/

/-- A strictly invariant cylinder persists in a `d₂` neighbourhood. This is the continuity
step in Section 4.2, before choosing the perturbation size and the word length. -/
theorem exists_invariant_cylinder_near (Φ : IFS N ε) :
    ∃ K > 0, ∃ η > 0, ∀ {ε' : ℝ} (Ψ : IFS N ε'), d2 Φ Ψ < η →
      ∀ i, MapsTo (Ψ.dualOp i) (dualCylClosed ε' 𝔜 K) (dualCyl ε' 𝔜 K) := by
  obtain ⟨B, hB0, hB⟩ := Φ.exists_nonlin_bound
  obtain ⟨A, η₀, hη₀, hcont⟩ := Φ.exists_dualProj_sub_le_d2
  obtain ⟨η₁, hη₁, hA⟩ := exists_pos_mul_lt one_pos |A|
  have hc := Φ.cmax_lt_one
  have he := mul_div_cancel₀ 𝕼 (sub_pos.2 hc).ne'
  have hQ : 0 < 𝕼 / 𝕽 := by positivity
  refine ⟨2 * (𝕼 / 𝕽) + 1, by linarith, min η₀ (min (𝕽 / 2) η₁),
    lt_min hη₀ (lt_min (by linarith) hη₁), fun Ψ hΨ => Ψ.mapsTo_dualOp_dualCylClosed
      (c := (1 + Φ.cmax) / 2) (M := B + 1) (fun i x hx => ?_) (fun i x hx => ?_) (by linarith)⟩ <;>
    simp at hΨ
  · linarith [(Continuity.norm_sub_le_d2 Φ Ψ i hx).2.1, norm_le_norm_add_norm_sub
      (𝔡 Φ i x) (𝔡 Ψ i x),
      Φ.norm_deriv_le_cmax i (Φ.ofReal_mem_cl hx)]
  · have := hcont Ψ hΨ.1 (.fin [i]) x hx
    simp [Φ.dualProj_singleton, Ψ.dualProj_singleton] at this
    linarith [hB i x (Φ.ofReal_mem_cl hx), mul_le_mul_of_nonneg_left
      hΨ.2.2.le (abs_nonneg A), mul_le_mul_of_nonneg_right (le_abs_self A)
        (Continuity.d2_nonneg Φ Ψ), norm_le_norm_add_norm_sub (Φ.nonlin i x) (Ψ.nonlin i x)]

/-- The `d₂` distance from bounds on the three differences on `I`. -/
theorem d2_le (hN : 0 < N) (Φ : IFS N ε) (Ψ : IFS N ε')
    (h0 : ∀ i, Ɐ ‖Ψ.f i x - Φ.f i x‖ ≤ a)
    (h1 : ∀ i, Ɐ ‖𝔡 Ψ i x - 𝔡 Φ i x‖ ≤ b)
    (h2 : ∀ i, Ɐ ‖𝔇 (Ψ.f i) x - 𝔇 (Φ.f i) x‖ ≤ e) :
    d2 Φ Ψ ≤ a + b + e := by
  have : Nonempty (Fin N) := by tauto
  refine ciSup_le fun i => add_le_add (add_le_add ?_ ?_) ?_ <;>
    refine ciSup_le fun x => (norm_sub_rev _ _).trans_le ?_
  exacts [h0 i x x.2, h1 i x x.2, h2 i x x.2]

/-! ## The density step -/

/-- The density step in the proof of Theorem 1.4. -/
theorem exists_dualSSC_near (hN : 0 < N) (Φ : IFS N ε)
    (hI : ∀ i, Ɐ (Φ.f i x).re ∈ Ioo 0 1) (hnc : Φ.NoCoincidence) (hr : 0 < r) :
    ∃ ε', ∃ Ψ : IFS N ε', d2 Φ Ψ < r ∧ Ψ.DualSSC := by
  classical
  -- the constants of Proposition 4.2 and their sum `C`
  choose C₀ hC₀ hbump using fun i => proposition_4_2 Φ.ε_pos (Φ.inClass i) (hI i)
  -- Fix an invariant cylinder, then choose `δ` within its continuity neighbourhood.
  obtain ⟨K, hK0, η, hη, hstable⟩ := Φ.exists_invariant_cylinder_near
  obtain ⟨δ, hδ, hδr⟩ := exists_pos_mul_lt (lt_min hr hη) (∑ i, C₀ i + 3)
  -- the length `n + 1` of the words
  obtain ⟨n, hn⟩ := ((((tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).comp
    (tendsto_add_atTop_nat 1)).mul_const (K - -K)).eventually
      (gt_mem_nhds (by linarith : 0 * (K - -K) < δ / 3))).exists
  -- the points of Lemma 4.1
  obtain ⟨x, hx⟩ := Φ.lemma_4_1 hnc 𝔜 K 𝖆 Finset.univ
  replace hx := fun p => hx p (Finset.mem_univ _)
  -- the sets `𝒴_ℓ` of the points of the bad pairs `(i, j)` with `i₁ = ℓ`, and `𝒵_ℓ` of the
  -- remaining orbit points
  let Y : Fin N → Finset ℝ := fun ℓ => (Finset.univ.filter fun p : (Fin 𝖆 → Fin N) ×
    (Fin 𝖆 → Fin N) => ¬ Φ.DualCylDisjoint 𝔜 K (List.ofFn p.1) (List.ofFn p.2) ∧
      p.1 0 = ℓ).image x
  have hfin : (⋃ p, (fun v => (Φ.comp v 𝕿).re) ''
    {v | v.length ≤ n + 1}).Finite := finite_iUnion fun p => (List.finite_length_le _ _).image _
  -- the perturbation of Proposition 4.2
  choose g hg using fun i => hbump i (Y i) (hfin.toFinset \ Y i)
    (fun y hy => by grind)
    (fun z hz => by
      obtain ⟨p, v, -, rfl⟩ := mem_iUnion.1 (hfin.mem_toFinset.1 (Finset.mem_sdiff.1 hz).1)
      exact Φ.re_comp_mem_I v (hx p).1)
    Finset.disjoint_sdiff δ hδ δ hδ
  obtain ⟨ε', hε', hgε'⟩ := exists_inClass_forall fun i => (hg i).1
  obtain ⟨Ψ, rfl⟩ : ∃ Ψ : IFS N ε', Ψ.f = g := ⟨⟨g, hε', hgε'⟩, rfl⟩
  have hd : d2 Φ Ψ < min r η := by
    refine lt_of_le_of_lt (d2_le hN Φ Ψ (e := (∑ i, C₀ i) * δ + δ)
      (fun i y hy => ((hg i).2.2.2.2.1 y hy).le) (fun i y hy => ((hg i).2.2.2.2.2.1 y hy).le)
      (fun i y hy => ((hg i).2.2.2.2.2.2 y hy).le.trans ?_)) ?_
    · linarith [mul_le_mul_of_nonneg_right (Finset.single_le_sum
        (fun j _ => (hC₀ j).le) (Finset.mem_univ i)) hδ.le]
    · linarith
  refine ⟨ε', Ψ, hd.trans_le (min_le_left _ _), ?_⟩
  -- agreement to second order at the orbit points `f_v(x_p)`, except at the base points of the
  -- bad pairs `p` with first letter `ℓ`
  have hgood : ∀ p (v : 𝔚 N) ℓ, v.length ≤ n + 1 → (v = [] →
      ¬ (¬ Φ.DualCylDisjoint 𝔜 K (List.ofFn p.1) (List.ofFn p.2) ∧ p.1 0 = ℓ)) →
      AgreeAt (Φ.f ℓ) (Ψ.f ℓ) (Φ.comp v 𝕿) := by
    intro p v ℓ hv h
    have hz : (Φ.comp v 𝕿).re ∈ hfin.toFinset \ Y ℓ := by
      refine Finset.mem_sdiff.2 ⟨hfin.mem_toFinset.2 (mem_iUnion.2 ⟨p, v, hv, rfl⟩), fun hy => ?_⟩
      obtain ⟨q, hq, hxq⟩ := Finset.mem_image.1 hy
      by_cases hqv : (q, ([] : 𝔚 N)) = (p, v)
      · grind
      · exact (hx q).2.2 p (Finset.mem_univ _) [] v (by simp) hv hqv
          (by tauto)
    exact Φ.comp_ofReal v (hx p).1 ▸ ⟨((hg ℓ).2.1 _ (Finset.mem_union_right _ hz)).1,
      ((hg ℓ).2.1 _ (Finset.mem_union_right _ hz)).2, (hg ℓ).2.2.1 _ hz⟩
  refine Ψ.lemma_2_6.1.2 ⟨-K, K, by linarith, n,
    hstable Ψ (hd.trans_le (min_le_right _ _)), fun i j hij => ⟨x (i, j), (hx (i, j)).1, ?_⟩⟩
  have ht := (hx (i, j)).1
  have hl : ∀ (w : Fin 𝖆 → Fin N) m, ((List.ofFn w).take m).reverse.length ≤ n + 1 := by
    simp
  by_cases hb : Φ.DualCylDisjoint 𝔜 K (List.ofFn i) (List.ofFn j)
  · -- a pair that is not bad: all orbit points lie in `𝒵`
    rw [dualCylAt_eq_of_agreeAt Φ Ψ _ _ fun m _ => hgood _ _ _ (hl i m) fun _ h => h.1 hb,
      dualCylAt_eq_of_agreeAt Φ Ψ _ _ fun m _ => hgood _ _ _ (hl j m) fun _ h => h.1 hb]
    grind
  -- a bad pair: `x_{i,j} ∈ 𝒴_{i₁}`, and the cylinders become disjoint after the shift
  have hY : x (i, j) ∈ Y 𝕻 := by grind
  have hbad : ¬ Disjoint (Φ.dualCylAt 𝔜 K (List.ofFn i) 𝕾)
      (Φ.dualCylAt 𝔜 K (List.ofFn j) 𝕾) := fun hd => hb ⟨_, ht, hd⟩
  rw [List.ofFn_succ] at hbad ⊢
  rw [dualCylAt_cons_eq_of_agreeAt Φ Ψ _ _ ((hg 𝕻).2.1 _ (Finset.mem_union_left _ hY)).1
    ((hg 𝕻).2.1 _ (Finset.mem_union_left _ hY)).2 fun m hm => by
      simpa [Φ.comp_append, -List.getElem_ofFn] using hgood (i, j) (((List.ofFn fun k => i k.succ).take m).reverse ++
        [i 0]) (List.ofFn fun k => i k.succ)[m] (by simp) (by simp),
    dualCylAt_eq_of_agreeAt Φ Ψ _ _ fun m _ => hgood _ _ _ (hl j m) fun h0 h => hij (by
      simp at h0; simpa [h0] using h.2)]
  refine disjoint_image_add_of_abs_sub_lt (fun a ha a' ha' =>
    (Φ.abs_sub_le_cmax_pow_of_mem_dualCylAt (by linarith) _ ht ha ha').trans_lt (by simpa using hn))
    (fun b hb b' hb' => (Φ.abs_sub_le_cmax_pow_of_mem_dualCylAt (by linarith) _ ht hb hb').trans_lt
      (by simpa using hn)) (not_disjoint_iff_nonempty_inter.1 hbad) ?_
  rw [Complex.abs_re_eq_norm.2 (by simp [Ψ.im_nonlin_ofReal _ (ofReal_mem_nbhd Ψ.ε_pos ht),
    Φ.im_nonlin_ofReal _ (ofReal_mem_nbhd Φ.ε_pos ht)])]
  exact (hg 𝕻).2.2.2.1 _ hY

end IFS

end AnalyticESC
