module

public import AnalyticESC.Conjugation.ExactOverlaps
public import AnalyticESC.Conjugation.Zeros

public section

set_option hygiene false
local notation "𝔠" => k n
local notation "𝔞" => (i₀ 0).pos
local notation "𝕱" => .inf i
local notation "𝕰" => hmem hp
local notation "𝕯" => Ico_subset_Icc_self hx
local notation "𝕮" => .inf (periodic hm j)
local notation "𝕭" => .inf (periodic hm i)
local notation "𝕬" => .fin (k n).reverse
local notation "𝖟" => j ∘ Fin.rev
local notation "𝖞" => i ∘ Fin.rev
local notation "𝖝" => Φ.realMaps k x
local notation "𝖜" => hUx hx
local notation "𝔨" => hp n

local notation "𝔧" => n + 1

local notation "𝔤" => .inf j

local notation "𝔣" => Φ.natProj i

local notation "𝔟" => p n

/-!
# Theorem 1.12 (a) along periodic points

The paper's proof of Theorem 1.12 (a). Let `g` be analytic and injective on `[0,1]` with
`g ∘ f_k = λ_k g + t_k` there for every letter `k`, so that `g ∘ f_w = λ_w g + t_w` for every
finite word `w`.

1. Differentiating gives `g'(f_k(x)) f_k'(x) = λ_k g'(x)`, so every `f_k` maps the zero set of
   `g'` in `[0,1]` into itself. This set is closed and `π(i) = lim f_{i₁ ⋯ iₙ}(x)` for every
   `x ∈ [0,1]`, so it contains the attractor once it is nonempty. A non-singleton attractor is
   infinite, and the identity theorem would give `g' ≡ 0`, against injectivity. Hence `g' ≠ 0`
   on `[0,1]`.
2. At the fixed point `p` of `f_w`, `f_w'(p) = λ_w`, and differentiating twice with (2.7) gives
   `g''(p)/g'(p) = H_{w^←}(p)/(1 - f_w'(p))`.
3. For `i, j ∈ Σ` let `kₙ = i₁ ⋯ iₙ jₙ ⋯ j₁`. The fixed point `p_{kₙ}` lies in
   `f_{i₁ ⋯ iₙ}([0,1])`, so `p_{kₙ} → π(i)`; `f_{kₙ}'(p_{kₙ}) → 0`; and
   `H_{j₁ ⋯ jₙ iₙ ⋯ i₁}(p_{kₙ}) → H_j(π(i))` by `exists_dualProj_bounds`, used to prove Lemma 2.5, uniformly on
   `cl B_ε` and holds for a finite and an infinite word with a common prefix, and the continuity
   of `H_j`. As `g''/g'` is continuous at `π(i)`, `g''/g' = H_j` on the attractor for every `j`,
   and the identity theorem gives `H_j = H_k` on `[0,1]`.

The converse follows the paper as well: `H = H_{k^∞} = Ĥ_{f_k}` for every letter `k`, Lemma 5.1
gives an invertible `g` with `g'' = H g'`, and the second part of Lemma 5.1 conjugates each `f_k`
to `y ↦ f_k'(p_k) y + g(p_k)(1 - f_k'(p_k))`. `theorem_1_12` states Theorem 1.12 (a) and (b) for
systems whose attractor is not a singleton.
-/

namespace AnalyticESC

variable {a b x : ℝ} {g : ℝ → ℝ}

open Set Filter Topology

/-! ## Analytic maps on `[0,1]` -/

/-- Maps that agree on `[0,1]` and have derivatives at a point of `[0,1]` have the same
derivative there. -/
theorem periodic_hasDerivAt_unique (hx : x ∈ I)
    (hu : HasDerivAt u a x) (hv : HasDerivAt v b x) (huv : ∀ y ∈ I, u y = v y) : a = b :=
  (uniqueDiffOn_Icc zero_lt_one x hx).eq_deriv _ hu.hasDerivWithinAt
    (hv.hasDerivWithinAt.congr huv (huv x hx))

namespace IFS

variable (Φ : IFS N ε) (k : Fin N) {lam t : Fin N → ℝ}

/-! ## Compositions on `[0,1]` -/

/-- `f_{k w} = f_k ∘ f_w` on `[0,1]`, for the real maps. -/
theorem periodic_re_comp_cons w (hx : x ∈ I) :
    (Φ.comp (k :: w) x).re = Φ.realMaps k (Φ.comp w x).re := by
  show (Φ.f k (Φ.comp w x)).re = (Φ.f k ((Φ.comp w x).re : ℂ)).re
  rw [← Φ.comp_ofReal w hx]

/-- `π(i) = lim f_{i₁ ⋯ i_{mₙ}}(zₙ)` for points `zₙ ∈ [0,1]` and lengths `mₙ → ∞`. -/
theorem tendsto_re_comp_natProj i {m : ℕ → ℕ} (hm : Tendsto m atTop atTop)
    {z : ℕ → ℝ} (hz : ∀ n, z n ∈ I) :
    Tendsto (fun n => (Φ.comp (List.ofFn fun k : Fin (m n) => i k) (z n)).re) atTop
      (𝓝 𝔣) := by
  refine ((Φ.tendsto_natProj i).comp hm).congr_dist (squeeze_zero (fun n => dist_nonneg)
    (fun n => (Complex.abs_re_le_norm _).trans ((Φ.norm_comp_sub_le _ (ofReal_mem_nbhd Φ.ε_pos
      zero_mem_I) (ofReal_mem_nbhd Φ.ε_pos (hz n))).trans ?_))
    ((tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).comp hm))
  rw [List.length_ofFn, ← Complex.ofReal_sub, Complex.norm_real]
  exact mul_le_of_le_one_right (pow_nonneg Φ.cmax_nonneg _)
    (abs_le.2 ⟨by simp_all, by grind⟩)

/-- `g ∘ f_w = λ_w g + t_w` on `[0,1]` for every finite word `w` if `g ∘ f_k = λ_k g + t_k` on
`[0,1]` for every letter `k`. -/
theorem exists_conj_comp
    (hconj : ∀ k, Ɐ g 𝖝 = lam k * g x + t k) w :
    ∃ a b, Ɐ g (Φ.comp w x).re = a * g x + b := by
  induction w with
  | nil => exact ⟨1, 0, fun x _ => by simp⟩
  | cons k w ih =>
    obtain ⟨a, b, h⟩ := ih
    refine ⟨lam k * a, lam k * b + t k, fun x hx => ?_⟩
    rw [Φ.periodic_re_comp_cons k w hx, hconj k _ (Φ.re_comp_mem_I w hx), h x hx]
    ring

/-! ## The first step: `g'` has no zero -/

/-- Theorem 1.12 (a), first step of the proof: if `g` is analytic and injective on `[0,1]`,
`g ∘ f_k = λ_k g + t_k` on `[0,1]` for every `k`, and the attractor is not a singleton, then `g'`
has no zero in `[0,1]`. -/
theorem deriv_ne_zero_of_conj_of_nonsingleton (hN : 0 < N) (hnd : ¬ ∃ x, Φ.attractor = {x})
    (hg : IsAnalyticCoord g)
    (hconj : ∀ k, Ɐ g 𝖝 = lam k * g x + t k) :
    Ɐ deriv g x ≠ 0 := by
  obtain ⟨hga, hinj⟩ := hg
  intro z hz hgz
  set Z := I ∩ deriv g ⁻¹' {0}
  -- `g'(f_k(x)) f_k'(x) = λ_k g'(x)` and `f_k' ≠ 0`, so every `f_k` maps `Z` into itself
  have hinv : ∀ k, MapsTo (Φ.realMaps k) Z Z := by
    rintro k x ⟨hx, hx0⟩
    have hd : HasDerivAt (Φ.realMaps k) (𝔡 Φ k x).re x :=
      hasDerivAt_re_ofReal (Φ.differentiableAt_f k (Φ.ofReal_mem_cl hx))
    have hid := periodic_hasDerivAt_unique hx ((hga _ ((Φ.inClass k).re_mem_I x hx)).differentiableAt.hasDerivAt.comp x hd)
      (((hga x hx).differentiableAt.hasDerivAt.const_mul (lam k)).add_const (t k)) (hconj k)
    refine ⟨(Φ.inClass k).re_mem_I x hx, ?_⟩
    rw [hx0, mul_zero] at hid
    exact (mul_eq_zero.1 hid).resolve_right
      (char_re_deriv_ne_zero_abs_lt_one Φ.ε_pos (Φ.inClass k) hx).1
  -- hence so does every composition `f_w`
  have hinvw (w : 𝔚 N) : MapsTo (fun x : ℝ => (Φ.comp w x).re) Z Z := by
    induction w with
    | nil => exact fun x hx => by simpa using hx
    | cons k w ih => exact fun x hx => by simpa only [Φ.periodic_re_comp_cons k w hx.1] using hinv k (ih hx)
  -- `Z` is closed and contains `z`, so it contains `π(i) = lim f_{i₁ ⋯ iₙ}(z)` for every `i`
  have hΛ : Φ.attractor ⊆ Z := by
    rintro _ ⟨i, rfl⟩
    exact (ContinuousOn.preimage_isClosed_of_isClosed (fun x hx => (hga x hx).deriv.continuousAt.continuousWithinAt) isClosed_Icc isClosed_singleton).mem_of_tendsto (Φ.tendsto_re_comp_natProj i tendsto_id fun _ => hz)
      (Eventually.of_forall fun n => hinvw _ ⟨hz, hgz⟩)
  -- the attractor is infinite, so `g' ≡ 0` on `[0,1]` and `g` is constant there
  obtain ⟨x₀, hx₀, hacc⟩ := ((Φ.attractor_infinite hN hnd).mono hΛ).exists_accPt_of_subset_isCompact
    isCompact_Icc inter_subset_left
  exact one_ne_zero (hinj one_mem_I zero_mem_I
    (constant_of_derivWithin_zero (fun x hx => (hga x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => by
        rw [(hga x 𝕯).differentiableAt.derivWithin
          (uniqueDiffOn_Icc zero_lt_one x 𝕯)]
        exact (AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero (fun x hx => (hga x hx).deriv) isPreconnected_Icc hx₀ ((accPt_iff_frequently_nhdsNE.1 hacc).mono fun z hz => hz.2)) 𝕯) 1 one_mem_I))

/-! ## The second step: periodic points -/

/-- Theorem 1.12 (a), second step of the proof: if `g ∘ f_w = λ g + t` on `[0,1]` for a nonempty
word `w` and `g'` does not vanish at the fixed point `p` of `f_w`, then `f_w'(p) = λ` and
`g''(p)/g'(p) = H_{w^←}(p)/(1 - f_w'(p))`. -/
theorem deriv_deriv_div_deriv_eq_of_fixedPoint (hg : AnalyticOnNhd ℝ g I)
    (hw : w ≠ [])
    (hconj : Ɐ g (Φ.comp w x).re = a * g x + b) (hp : p ∈ I)
    (hfp : Φ.comp w p = p) (hgp : deriv g p ≠ 0) :
    (𝔡ᶜ Φ w p).re = a ∧
      ((𝔇 g p / deriv g p : ℝ) : ℂ) =
        Φ.dualProj (.fin w.reverse) p / (1 - 𝔡ᶜ Φ w p) := by
  have hmem : ∀ {x : ℝ}, x ∈ I → (x : ℂ) ∈ nbhd ε := ofReal_mem_nbhd Φ.ε_pos
  obtain ⟨U, hUo, hU, hd⟩ := Φ.exists_differentiableOn_comp w
  have hUx : ∀ {x : ℝ}, x ∈ I → (x : ℂ) ∈ U := fun hx => hU (subset_closure (hmem hx))
  -- the real maps `F = Re f_w`, `F₁ = Re f_w'` and `F₂ = Re f_w''`
  set F : ℝ → ℝ := fun y => (Φ.comp w y).re with hF
  set F₁ : ℝ → ℝ := fun y => (𝔡ᶜ Φ w y).re with hF₁
  set F₂ : ℝ → ℝ := fun y => (𝔇 (Φ.comp w) y).re
  have hFd : Ɐ HasDerivAt F (F₁ x) x := fun x hx =>
    hasDerivAt_re_ofReal ((hd _ 𝖜).differentiableAt (hUo.mem_nhds 𝖜))
  -- `g'(f_w(x)) f_w'(x) = λ g'(x)` on `[0,1]`
  have hA := fun x hx =>
    periodic_hasDerivAt_unique hx ((hg _ (Φ.re_comp_mem_I w hx)).differentiableAt.hasDerivAt.comp
      x (hFd x hx)) (((hg x hx).differentiableAt.hasDerivAt.const_mul a).add_const b) hconj
  -- `g''(f_w(p)) f_w'(p)² + g'(f_w(p)) f_w''(p) = λ g''(p)`
  have hB : 𝔇 g (F p) * F₁ p * F₁ p + deriv g (F p) * F₂ p =
      a * 𝔇 g p :=
    periodic_hasDerivAt_unique hp (((hg _ (Φ.re_comp_mem_I w hp)).deriv.differentiableAt.hasDerivAt.comp
      p (hFd p hp)).mul ((fun x hx => hasDerivAt_re_ofReal (((hd.deriv hUo) _ 𝖜).differentiableAt (hUo.mem_nhds 𝖜))) p hp)) ((hg p hp).deriv.differentiableAt.hasDerivAt.const_mul a) hA
  have hFp : F p = p := by simp_all
  -- `f_w'(p) = λ`, as `g'(p) ≠ 0`
  refine ⟨(by grind), ?_⟩
  -- `f_w'(p)` and `f_w''(p)` are real, with `0 < |f_w'(p)| < 1`
  have h₁ : 𝔡ᶜ Φ w p = (F₁ p : ℂ) :=
    Complex.ext (by simp_all) (by simp [Φ.im_deriv_comp_ofReal w 𝕰])
  have h₂ : 𝔇 (Φ.comp w) p = (F₂ p : ℂ) :=
    Complex.ext (by tauto) (by simp [im_deriv_eq_zero isOpen_nbhd
      ((Φ.differentiableOn_comp w).deriv isOpen_nbhd)
        (fun s hs => Φ.im_deriv_comp_ofReal w hs) 𝕰])
  have hne : F₁ p ≠ 0 := fun h0 =>
    Φ.deriv_comp_ne_zero w (subset_closure 𝕰) (by rw [h₁, h0, Complex.ofReal_zero])
  have hne' := (sub_pos.2 ((le_abs_self _).trans_lt ((Complex.abs_re_le_norm _).trans_lt
    ((Φ.norm_deriv_comp_le w (subset_closure 𝕰)).trans_lt (pow_lt_one₀ Φ.cmax_nonneg Φ.cmax_lt_one
      (List.length_pos_iff.2 hw).ne'))))).ne'
  -- (2.7): `H_{w^←}(p) = f_w''(p)/f_w'(p)`
  rw [Φ.dualProj_fin_reverse w (subset_closure 𝕰), h₁, h₂,
    show (F₂ p : ℂ) / (F₁ p : ℂ) / (1 - (F₁ p : ℂ)) = ((F₂ p / F₁ p / (1 - F₁ p) : ℝ) : ℂ) by
      push_cast; ring]
  congr 1
  grind

/-! ## The third step: the limit along periodic points -/

/-- Theorem 1.12 (a), third step of the proof: if `Φ` is conjugated to a self-similar IFS and its
attractor is not a singleton, then all dual natural projections agree on `[0,1]`. -/
theorem dualProj_eq_of_conjSelfSimilar (hnd : ¬ ∃ x, Φ.attractor = {x})
    (h : ConjSelfSimilar Φ.realMaps) :
    ∀ i j, Ɐ Φ.dualProj 𝕱 x = Φ.dualProj 𝔤 x := by
  intro i₀ j₀
  have hε := Φ.ε_pos
  obtain ⟨g, hg, lam, t, hconj⟩ := h
  -- the first step
  have hg' := Φ.deriv_ne_zero_of_conj_of_nonsingleton 𝔞 hnd hg (fun k => (hconj k).2.2)
  obtain ⟨M, hM⟩ := Φ.exists_dualProj_bounds
  have hc : Tendsto (fun n => Φ.cmax ^ 𝔧) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).comp
      (tendsto_add_atTop_nat 1)
  -- `g''/g' = H_j` at `π(i)`
  have key : ∀ i j,
      ((𝔇 g 𝔣 / deriv g 𝔣 : ℝ) : ℂ) =
        Φ.dualProj 𝔤 𝔣 := by
    intro i j
    have hπ := Φ.attractor_subset_I ⟨i, rfl⟩
    -- the words `kₙ = i₁ ⋯ i_{n+1} j_{n+1} ⋯ j₁`
    set u : ℕ → 𝔚 N := fun n => List.ofFn fun m : Fin 𝔧 => i m with hu
    set v : ℕ → 𝔚 N := fun n => List.ofFn fun m : Fin 𝔧 => j m with hv
    set k : ℕ → 𝔚 N := fun n => u n ++ (v n).reverse with hk
    have hkne : ∀ n, k n ≠ [] := fun n => by simp [hk, hu]
    -- the fixed points `pₙ` of `f_{kₙ}`
    choose p hp hfp using fun n =>
      (existsUnique_fixedPoint (by positivity) (Φ.inClass_comp (hkne n))).exists
    -- the second step at `pₙ`
    have hid : ∀ n, ((𝔇 g 𝔟 / deriv g 𝔟 : ℝ) : ℂ) =
        Φ.dualProj 𝕬 𝔟 / (1 - 𝔡ᶜ Φ 𝔠 𝔟) := fun n => by
      obtain ⟨a, b, hab⟩ := Φ.exists_conj_comp (fun k => (hconj k).2.2) 𝔠
      exact (Φ.deriv_deriv_div_deriv_eq_of_fixedPoint hg.1 (hkne n) hab 𝔨 (hfp n)
        (hg' _ 𝔨)).2
    -- `pₙ = f_{i₁ ⋯ i_{n+1}}(f_{j_{n+1} ⋯ j₁}(pₙ)) → π(i)`
    have hplim : Tendsto p atTop (𝓝 𝔣) := by
      refine (Φ.tendsto_re_comp_natProj i (tendsto_add_atTop_nat 1)
        (z := fun n => (Φ.comp (v n).reverse 𝔟).re)
        fun n => Φ.re_comp_mem_I _ 𝔨).congr fun n => ?_
      show (Φ.comp (u n) ((Φ.comp (v n).reverse 𝔟).re : ℂ)).re = p n
      rw [← Φ.comp_ofReal _ 𝔨, ← Function.comp_apply (f := Φ.comp (u n)), ← Φ.comp_append]
      simp_all
    -- the left-hand side tends to `g''(π(i))/g'(π(i))`
    have hL : Tendsto (fun n => ((𝔇 g 𝔟 / deriv g 𝔟 : ℝ) : ℂ)) atTop
        (𝓝 ((𝔇 g 𝔣 / deriv g 𝔣 : ℝ) : ℂ)) :=
      (((hg.1 _ hπ).deriv.deriv.continuousAt.div (hg.1 _ hπ).deriv.continuousAt
        (hg' _ hπ)).tendsto.comp hplim).ofReal
    -- `f_{kₙ}'(pₙ) → 0`
    have hD : Tendsto (fun n => 𝔡ᶜ Φ 𝔠 𝔟) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => (Φ.norm_deriv_comp_le _ ((fun n => ofReal_mem_closure hε 𝔨) n)).trans
        (pow_le_pow_of_le_one Φ.cmax_nonneg Φ.cmax_lt_one.le ?_)) hc
      simp_all
    -- `H_{j₁ ⋯ j_{n+1} i_{n+1} ⋯ i₁}(pₙ) - H_j(pₙ) → 0`, by `exists_dualProj_bounds` for words
    -- with a common prefix of length `n + 1`
    have hH₁ : Tendsto (fun n => Φ.dualProj 𝕬 𝔟 -
        Φ.dualProj 𝔤 𝔟) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => hM _ _ 𝔧 ?_ _ ((fun n => ofReal_mem_closure hε 𝔨) n))
        (by simpa using hc.const_mul (2 * M))
      rw [Word.le_commonPrefixLength_iff]
      intro l hl
      simp [hk, List.getElem?_append_left (by simpa [hv] using hl : l < (v n).length)]
      simp [hv, hl, -List.ofFn_succ]
    -- `H_j(pₙ) → H_j(π(i))`, as `H_j` is continuous
    have hH₂ : Tendsto (fun n => Φ.dualProj 𝔤 𝔟) atTop
        (𝓝 (Φ.dualProj 𝔤 𝔣)) :=
      (((Φ.differentiableOn_dualProj _).differentiableAt (isOpen_nbhd.mem_nhds
        (ofReal_mem_nbhd hε hπ))).continuousAt.tendsto).comp hplim.ofReal
    refine tendsto_nhds_unique hL ?_
    simp_rw [hid]
    simpa [Pi.div_def] using (hH₁.add hH₂).div ((tendsto_const_nhds (x := 1)).sub hD) (by simp)
  -- `H_{i₀} = H_{j₀}` on the infinite attractor, so on `[0,1]` by the identity theorem
  intro x hx
  by_contra hne
  refine Φ.attractor_infinite 𝔞 hnd ((finite_zeros hε ((Φ.differentiableOn_dualProj (.inf i₀)).sub
    (Φ.differentiableOn_dualProj (.inf j₀))) ⟨x, hx, sub_ne_zero.2 hne⟩).subset ?_)
  rintro _ ⟨i, rfl⟩
  exact ⟨Φ.attractor_subset_I ⟨i, rfl⟩, sub_eq_zero.2 ((key i i₀).symm.trans (key i j₀))⟩

/-! ## The converse -/

/-- `Ĥ_{f_k} = H_{k^∞}` on `[0,1]`. -/
theorem periodic_hatH_f_eq_dualProj_const :
    Ɐ hatH (Φ.f k) x = Φ.dualProj (.inf fun _ => k) x := by
  intro x hx
  have h := Φ.hatH_comp_eq_dualProj one_pos ![k] x hx
  have hw : periodic one_pos (![k] ∘ Fin.rev) = fun _ => k := by continuity
  simp_all

/-- Theorem 1.12 (a), the converse, along the paper: if all dual natural projections agree on
`[0,1]`, then Lemma 5.1 for `f_{k₀}` gives an invertible `g` with `g'' = H g'`, and the second
part of Lemma 5.1 conjugates each `f_k` by `g` to a similarity. -/
theorem conjSelfSimilar_of_dualProj_eq
    (h : ∀ i j, Ɐ Φ.dualProj 𝕱 x = Φ.dualProj 𝔤 x) :
    ConjSelfSimilar Φ.realMaps := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact ⟨id, ⟨analyticOnNhd_id, injOn_id _⟩, 0, 0, fun j => j.elim0⟩
  obtain ⟨g, hg, -, lam, t, h⟩ := Φ.exists_conj_of_hatH_eq ⟨0, hN⟩ fun k x hx => by
    rw [Φ.periodic_hatH_f_eq_dualProj_const k x hx, Φ.periodic_hatH_f_eq_dualProj_const _ x hx]
    grind
  exact ⟨g, hg, lam, t, h⟩

/-- Theorem 1.12 (b), for every system. -/
theorem subConjSelfSimilar_iff :
    Φ.SubConjSelfSimilar ↔
      ∃ (m : ℕ) (hm : 0 < m) (i j : Fin m → Fin N), i ≠ j ∧
        Ɐ Φ.dualProj 𝕭 x = Φ.dualProj 𝕮 x := by
  have h4 : 0 < ε / 4 := by linarith [Φ.ε_pos]
  have hne : ∀ {m : ℕ} (w : Fin m → Fin N), 0 < m → List.ofFn w ≠ [] := fun w hm h =>
    hm.ne' (List.ofFn_eq_nil_iff.1 h)
  have hrev : ∀ {m : ℕ} (w : Fin m → Fin N), (w ∘ Fin.rev) ∘ Fin.rev = w := fun w =>
    funext fun k => by simp
  have hrev_ne : ∀ {m : ℕ} {u v : Fin m → Fin N}, u ≠ v → u ∘ Fin.rev ≠ v ∘ Fin.rev := by grind
  constructor
  · rintro ⟨m, i, j, hij, g, ⟨hg, hinj⟩, lam, t, hconj⟩
    have hm : 0 < m := Nat.pos_of_ne_zero fun h => hij (by subst h; exact Subsingleton.elim _ _)
    have hf₁ := Φ.inClass_comp (hne i hm)
    have hf₂ := Φ.inClass_comp (hne j hm)
    obtain ⟨p₁, ⟨hp₁, hfp₁⟩, -⟩ := existsUnique_fixedPoint h4 hf₁
    obtain ⟨p₂, ⟨hp₂, hfp₂⟩, -⟩ := existsUnique_fixedPoint h4 hf₂
    by_cases hpq : p₁ = p₂
    · -- a common fixed point: `f_i` and `f_j` commute on `[0,1]`, so `f_{ij} = f_{ji}` there
      have hcomm := comp_comm_of_conj hinj (hf₁.re_mem_I)
        (hf₂.re_mem_I) (hconj 0).2.2 (hconj 1).2.2 hp₁
        (by simp_all) (by simp_all)
      have hm' : 0 < m + m := by omega
      have hcomp : ∀ {u v : Fin m → Fin N}, ∀ y ∈ I, Φ.comp (List.ofFn (Fin.append u v)) y =
          ((Φ.comp (List.ofFn u) ((Φ.comp (List.ofFn v) y).re : ℂ)).re : ℂ) := fun y hy => by
        rw [List.ofFn_fin_append, Φ.comp_append, Function.comp_apply]
        conv_lhs => rw [Φ.comp_ofReal _ hy]
        exact Φ.comp_ofReal _ (Φ.re_comp_mem_I _ hy)
      have hH := hatH_eq_of_eqOn_I h4 (Φ.inClass_comp (hne (Fin.append i j) hm')) h4 (Φ.inClass_comp (hne (Fin.append j i) hm')) fun y hy => by simp_all
      refine ⟨m + m, hm', Fin.append i j ∘ Fin.rev, Fin.append j i ∘ Fin.rev,
        hrev_ne fun h => hij (funext fun k => by simpa using congrFun h (Fin.castAdd m k)),
        fun x hx => (Φ.hatH_comp_eq_dualProj hm' _ x hx).symm.trans
          ((hH x hx).trans (Φ.hatH_comp_eq_dualProj hm' _ x hx))⟩
    · -- Apply part (a) to the two-map subsystem, whose fixed points differ.
      let Ψ : IFS 2 (ε / 4) := ⟨![Φ.comp (List.ofFn i), Φ.comp (List.ofFn j)],
        h4, Fin.forall_fin_two.2 ⟨hf₁, hf₂⟩⟩
      have hnd : ¬ ∃ x, Ψ.attractor = {x} := by
        rintro ⟨x, hx⟩
        have hfix := Ψ.fixedPoint_of_attractor_singleton hx
        exact hpq (((existsUnique_fixedPoint h4 hf₁).unique ⟨hp₁, hfp₁⟩
          ⟨Ψ.attractor_subset_I (hx ▸ mem_singleton x), by continuity⟩).trans
          ((existsUnique_fixedPoint h4 hf₂).unique ⟨Ψ.attractor_subset_I (hx ▸ mem_singleton x), by continuity⟩ ⟨hp₂, hfp₂⟩))
      have hH : Ɐ hatH (Φ.comp (List.ofFn i)) x =
          hatH (Φ.comp (List.ofFn j)) x := fun x hx => by
        simpa [Ψ] using (Ψ.periodic_hatH_f_eq_dualProj_const 0 x hx).trans
          (((Ψ.dualProj_eq_of_conjSelfSimilar hnd ⟨g, ⟨hg, hinj⟩, lam, t, Fin.forall_fin_two.2 ⟨by solve_by_elim, by simpa [Ψ, realMaps] using hconj 1⟩⟩) _ _ x hx).trans (Ψ.periodic_hatH_f_eq_dualProj_const 1 x hx).symm)
      exact ⟨m, hm, i ∘ Fin.rev, j ∘ Fin.rev, hrev_ne hij, fun x hx =>
        (Φ.hatH_comp_eq_dualProj hm _ x hx).symm.trans
          ((hH x hx).trans (Φ.hatH_comp_eq_dualProj hm _ x hx))⟩
  · rintro ⟨m, hm, i, j, hij, h⟩
    have hH : Ɐ hatH (Φ.comp (List.ofFn 𝖞)) x =
        hatH (Φ.comp (List.ofFn 𝖟)) x := fun x hx => by
      rw [Φ.hatH_comp_eq_dualProj hm _ x hx, Φ.hatH_comp_eq_dualProj hm _ x hx, hrev, hrev]
      exact h x hx
    obtain ⟨g, hg, -, lam, t, h⟩ := IFS.exists_conj_of_hatH_eq ⟨![Φ.comp (List.ofFn 𝖞),
      Φ.comp (List.ofFn 𝖟)], h4, Fin.forall_fin_two.2 ⟨Φ.inClass_comp
        (hne 𝖞 hm), Φ.inClass_comp (hne 𝖟 hm)⟩⟩ 0
      (Fin.forall_fin_two.2 ⟨fun _ _ => rfl, fun x hx => (hH x hx).symm⟩)
    exact ⟨m, i ∘ Fin.rev, j ∘ Fin.rev, hrev_ne hij, g, hg, lam, t, Fin.forall_fin_two.2 ⟨h 0, h 1⟩⟩

/-! ## Theorem 1.12 -/

/-- Theorem 1.12 (a) and (b), for systems whose attractor is not a singleton. -/
theorem theorem_1_12 (hnd : ¬ ∃ x, Φ.attractor = {x}) :
    (ConjSelfSimilar Φ.realMaps ↔
      ∀ i j, Ɐ Φ.dualProj 𝕱 x = Φ.dualProj 𝔤 x) ∧
    (Φ.SubConjSelfSimilar ↔
      ∃ (m : ℕ) (hm : 0 < m) (i j : Fin m → Fin N), i ≠ j ∧
        Ɐ Φ.dualProj 𝕭 x = Φ.dualProj 𝕮 x) :=
  ⟨⟨Φ.dualProj_eq_of_conjSelfSimilar hnd, Φ.conjSelfSimilar_of_dualProj_eq⟩,
    Φ.subConjSelfSimilar_iff⟩

end IFS

end AnalyticESC
