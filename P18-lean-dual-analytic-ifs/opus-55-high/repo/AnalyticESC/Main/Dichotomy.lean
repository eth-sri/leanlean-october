module

public import AnalyticESC.Separation
public import AnalyticESC.Main.Closeness
public import AnalyticESC.Dual.Attractor

public section

set_option hygiene false
local notation "𝕯" => S.q k
local notation "𝕮" => S.p k
local notation "𝕭" => ‖g S.p₀‖ / 2
local notation "𝕬" => ofReal_mem_nbhd Φ.ε_pos hx
local notation "𝖟" => A + 1
local notation "𝖞" => Φ.differentiableOn_dualProj _
local notation "𝖝" => p k
local notation "𝖜" => nbhd ε
local notation "𝔧" => .inf j

local notation "𝔤" => .inf i

local notation "𝔣" => φ k

local notation "𝔟" => Nat.one_le_iff_ne_zero.1 (hn k)

/-!
# Theorems 1.5 and 2.2

The three cases in the proof of Theorem 2.2, after extracting pairs `a_k u_k`, `b_k u_k`
whose compositions are super-exponentially close:

1. Bounded common suffixes: fix `u_k = u`, pass to the limit on the nondegenerate interval
   `f_u(I)`, and apply the identity theorem.
2. Unbounded suffixes and finite limit words: finite order of vanishing at the limiting point
   contradicts the interval-length lower bound unless the two fixed compositions coincide.
3. Infinite limit words: (3.2), Lemma 3.1 and Lemma 2.9 give (3.3), including the denominator
   `|f_u'|^k`; Lemma 2.11 and analyticity then identify the limiting dual projections.

Theorem 1.5 follows from compactness, Lemma 2.6(c) and Theorem 2.2.
-/

namespace AnalyticESC

open Set Filter Topology

/-! ## Super-exponentially small sequences -/

/-- `η k` is eventually below `θ ^ n k`, for every `θ > 0`. -/
def SupExpSmall (n : ℕ → ℕ) (η : ℕ → ℝ) : Prop :=
  ∀ θ > 0, ∀ᶠ k in atTop, η k ≤ θ ^ n k

namespace SupExpSmall

variable {n : ℕ → ℕ} {η : ℕ → ℝ} (h : SupExpSmall n η)
include h

theorem comp (hφ : Tendsto φ atTop atTop) :
    SupExpSmall (n ∘ φ) (η ∘ φ) := fun θ hθ => hφ.eventually (h θ hθ)

variable (hn : ∀ k, 1 ≤ n k)
include hn

theorem eventually_le (hδ : 0 < δ) :
    ∀ᶠ k in atTop, η k ≤ δ := by
  filter_upwards [h (min δ 1) (lt_min hδ one_pos)] with k hk
  exact hk.trans ((pow_le_of_le_one (le_min hδ.le zero_le_one) (min_le_right _ _)
    𝔟).trans (min_le_left _ _))

theorem eventually_lt_pow (hc : 0 < c) :
    ∀ᶠ k in atTop, η k < c ^ n k := by
  filter_upwards [h (c / 2) (half_pos hc)] with k hk
  exact hk.trans_lt (pow_lt_pow_left₀ (half_lt_self hc) (half_pos hc).le
    𝔟)

/-- `K A^{n_k} η_k^s` is super-exponentially small along with `η_k`. -/
theorem mul_pow_rpow (hη : ∀ k, 0 ≤ η k) K
    {A s : ℝ} (hA : 0 ≤ A) (hs : 0 < s) :
    SupExpSmall n fun k => K * A ^ n k * η k ^ s := by
  intro θ hθ
  have hL : 0 < max K 1 * 𝖟 := by positivity
  have hθL := div_pos hθ hL
  filter_upwards [h _ (Real.rpow_pos_of_pos hθL s⁻¹)] with k hk
  calc _ ≤ max K 1 ^ n k * 𝖟 ^ n k * (θ / (max K 1 * 𝖟)) ^ n k :=
        mul_le_mul (mul_le_mul ((le_max_left _ _).trans (le_self_pow₀ (le_max_right _ _)
          𝔟)) (pow_le_pow_left₀ hA (by linarith) _)
          (by positivity) (by positivity))
          ((Real.rpow_le_rpow (hη k) hk hs.le).trans_eq (by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hθL.le, ← Real.rpow_mul hθL.le,
              show s⁻¹ * (n k : ℝ) * s = n k by field_simp, Real.rpow_natCast]))
          (Real.rpow_nonneg (hη k) _) (by positivity)
    _ = θ ^ n k := by rw [← mul_pow, ← mul_pow, mul_div_cancel₀ _ hL.ne']

end SupExpSmall

/-! ## Two elementary lemmas -/

/-- Pigeonhole: a sequence frequently in a finite set frequently takes one value. -/
theorem exists_frequently_eq_of_frequently_mem {s : Set α} (hs : s.Finite)
    {f : ℕ → α} (h : ∃ᶠ k in atTop, f k ∈ s) : ∃ a ∈ s, ∃ᶠ k in atTop, f k = a := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  exact h (((eventually_all_finite hs).2 fun a ha => not_frequently.1 (hcon a ha)).mono
    fun k hk hks => hk _ hks rfl)

theorem norm_sub_le_three {a b c d : ℂ} (h1 : ‖a - c‖ ≤ x) (h2 : ‖a - b‖ ≤ y)
    (h3 : ‖b - d‖ ≤ z) : ‖c - d‖ ≤ x + y + z := by
  linarith [norm_sub_le_norm_sub_add_norm_sub c a d, norm_sub_le_norm_sub_add_norm_sub a b d,
    norm_sub_rev a c]

/-- Identity theorem along a convergent sequence: if all derivatives of two holomorphic maps are
asymptotically equal along points `p_k → p₀ ∈ I`, the maps agree on `B_ε`. -/
theorem eqOn_nbhd_of_iteratedDeriv_close (hε : 0 < ε) {g h : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g 𝖜) (hh : DifferentiableOn ℂ h 𝖜) {p : ℕ → ℝ}
    (hp₀ : p₀ ∈ I) (hp : Tendsto p atTop (𝓝 p₀))
    (hclose : ∀ r, ∀ δ > 0, ∀ᶠ k in atTop,
      ‖iteratedDeriv r g 𝖝 - iteratedDeriv r h 𝖝‖ ≤ δ) :
    EqOn g h 𝖜 := by
  refine eqOn_nbhd_of_iteratedDeriv_eq hε hg hh hp₀ fun r => eq_of_forall_dist_le fun δ hδ => ?_
  have hcont : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f 𝖜 →
      Tendsto (fun k => iteratedDeriv r f 𝖝) atTop (𝓝 (iteratedDeriv r f p₀)) := by
    intro f hf
    rw [iteratedDeriv_eq_iterate]
    exact ((hf.analyticOnNhd isOpen_nbhd).iterated_deriv r _
      (ofReal_mem_nbhd hε hp₀)).continuousAt.tendsto.comp
        ((Complex.continuous_ofReal.tendsto p₀).comp hp)
  rw [dist_eq_norm]
  exact le_of_tendsto ((hcont g hg).sub (hcont h hh)).norm (hclose r δ hδ)

namespace IFS

variable (Φ : IFS N ε) {i j : 𝔖 N}

/-! ## Condensing sequences -/

local notation "𝔫" => (a k).length + (u k).length

/-- A condensing sequence, extracted from the failure of the SESC: words `a_k u_k` and `b_k u_k`
of length `n_k = |a_k| + |u_k|`, with `|a_k| = |b_k| ≥ 1` and different last letters of `a_k`
and `b_k`, whose compositions are `η_k`-close on `I`, where `η_k` is super-exponentially small
in `n_k`; together with `f_{u_k}(I) = [p_k, q_k]` and a limit `p_k → p₀`. -/
structure CondSeq where
  /-- The first words. -/
  a : ℕ → 𝔚 N
  /-- The second words. -/
  b : ℕ → 𝔚 N
  /-- The common suffixes. -/
  u : ℕ → 𝔚 N
  /-- The distances. -/
  η : ℕ → ℝ
  /-- The left endpoints of `f_{u_k}(I)`. -/
  p : ℕ → ℝ
  /-- The right endpoints of `f_{u_k}(I)`. -/
  q : ℕ → ℝ
  /-- The limit of the left endpoints. -/
  p₀ : ℝ
  length_eq : ∀ k, (a k).length = (b k).length
  length_pos : ∀ k, 0 < (a k).length
  getLast?_ne : ∀ k, (a k).getLast? ≠ (b k).getLast?
  η_pos : ∀ k, 0 < η k
  close : ∀ k, Ɐ ‖Φ.comp (a k ++ u k) x - Φ.comp (b k ++ u k) x‖ ≤ η k
  small : SupExpSmall (fun k => 𝔫) η
  length_tendsto : Tendsto (fun k => 𝔫) atTop atTop
  p_nonneg : ∀ k, 0 ≤ p k
  p_lt_q : ∀ k, p k < q k
  q_le_one : ∀ k, q k ≤ 1
  cmin_pow_le : ∀ k, Φ.cmin ^ 𝔫 ≤ q k - p k
  cmax_pow_ge : ∀ k, q k - p k ≤ Φ.cmax ^ (u k).length
  image_eq : ∀ k, (fun x : ℝ => (Φ.comp (u k) x).re) '' I = Icc 𝖝 (q k)
  p₀_mem : p₀ ∈ I
  tendsto_p : Tendsto p atTop (𝓝 p₀)

/-- The failure of the SESC gives a condensing sequence. -/
theorem nonempty_condSeq (h : ¬ Φ.SESC) : Nonempty Φ.CondSeq := by
  have h₂ : ∀ k, ∃ a b u : 𝔚 N, a.length = b.length ∧ 0 < a.length ∧
      a.getLast? ≠ b.getLast? ∧ k ≤ a.length + u.length ∧ Ɐ
        ‖Φ.comp (a ++ u) x - Φ.comp (b ++ u) x‖ ≤ ((k : ℝ) + 2)⁻¹ ^ (a.length + u.length) := by
    intro k
    obtain ⟨n, hnk, i, j, hij, hlt⟩ := Φ.exists_close_pair_ge h (c := (k + 2)⁻¹) (by positivity) k
    obtain ⟨a, b, u, hi, hj, hlen, hpos, hlast⟩ :=
      List.exists_decomp_of_ne (by simp)
        fun h => hij (List.ofFn_injective h)
    have hn : a.length + u.length = n := by rw [← List.length_append, ← hi, List.length_ofFn]
    refine ⟨a, b, u, hlen, hpos, hlast, hn ▸ hnk, fun x hx => ?_⟩
    rw [← hi, ← hj, hn]
    exact (Φ.norm_le_supDist _ _ hx).trans hlt.le
  choose a b u hlen hpos hlast hnk hclose using h₂
  have hN := ((a 0).head (List.ne_nil_of_length_pos (hpos 0))).pos
  choose p q hp0 hpq hq1 hmin hmax himg using fun k => Φ.exists_image_comp_eq_Icc (u k)
  have hsmall : SupExpSmall (fun k => 𝔫)
      fun k => ((k : ℝ) + 2)⁻¹ ^ 𝔫 := fun θ hθ => by
    obtain ⟨m, hm⟩ := exists_nat_gt θ⁻¹
    filter_upwards [eventually_ge_atTop m] with k hk
    exact pow_le_pow_left₀ (by positivity)
      ((inv_le_comm₀ (by positivity) hθ).2 (by linarith [(Nat.cast_le (α := ℝ)).2 hk])) _
  obtain ⟨p₀, hp₀, φ, hφ, hlim⟩ :=
    isCompact_Icc.tendsto_subseq fun k => ⟨hp0 k, (hpq k).trans (hq1 k)⟩
  exact ⟨⟨a ∘ φ, b ∘ φ, u ∘ φ,
    fun k => ((φ k : ℝ) + 2)⁻¹ ^ ((a 𝔣).length + (u 𝔣).length), p ∘ φ, q ∘ φ, p₀,
    fun _ => hlen _, fun _ => hpos _, fun _ => hlast _, fun _ => by positivity,
    fun _ => hclose _, hsmall.comp hφ.tendsto_atTop,
    tendsto_atTop_mono (fun k => (hφ.id_le k).trans (hnk 𝔣)) tendsto_id, fun _ => hp0 _,
    fun k => sub_pos.1 ((pow_pos (Φ.cmin_pos hN) _).trans_le (hmin 𝔣)), fun _ => hq1 _,
    fun k => (pow_le_pow_of_le_one (Φ.cmin_pos hN).le ((Φ.cmin_le_cmax hN).trans Φ.cmax_lt_one.le)
      (Nat.le_add_left _ _)).trans (hmin 𝔣), fun _ => hmax _, fun _ => himg _, hp₀, hlim⟩⟩

namespace CondSeq

variable {Φ} (S : Φ.CondSeq)

/-- Reindexing a condensing sequence along a strictly increasing map. -/
def comp (φ : ℕ → ℕ) (hφ : StrictMono φ) : Φ.CondSeq :=
  ⟨S.a ∘ φ, S.b ∘ φ, S.u ∘ φ, S.η ∘ φ, S.p ∘ φ, S.q ∘ φ, S.p₀, fun _ => S.length_eq _,
    fun _ => S.length_pos _, fun _ => S.getLast?_ne _, fun _ => S.η_pos _, fun _ => S.close _,
    S.small.comp hφ.tendsto_atTop, S.length_tendsto.comp hφ.tendsto_atTop, fun _ => S.p_nonneg _,
    fun _ => S.p_lt_q _, fun _ => S.q_le_one _, fun _ => S.cmin_pow_le _,
    fun _ => S.cmax_pow_ge _, fun _ => S.image_eq _, S.p₀_mem,
    S.tendsto_p.comp hφ.tendsto_atTop⟩

theorem pos_N (S : Φ.CondSeq) : 0 < N :=
  ((S.a 0).head (List.ne_nil_of_length_pos (S.length_pos 0))).pos

local notation "𝔪" => (S.a k).length + (S.u k).length

theorem one_le_length k : 1 ≤ 𝔪 :=
  (S.length_pos k).trans_le (Nat.le_add_right _ _)

theorem p_mem k : S.p k ∈ I :=
  ⟨S.p_nonneg k, (S.p_lt_q k).le.trans (S.q_le_one k)⟩

theorem mem_image k y (hy : y ∈ Icc 𝕮 𝕯) :
    ∃ x ∈ I, y = Φ.comp (S.u k) x := by
  obtain ⟨x, hx, rfl⟩ := S.image_eq k ▸ hy
  exact ⟨x, hx, (Φ.comp_ofReal _ hx).symm⟩

/-- Finite limit words: finite order of vanishing contradicts super-exponential
closeness on intervals whose lengths are at least `c_min^{n_k}`. -/
theorem comp_eq_comp {a b : 𝔚 N} (ha : ∀ k, S.a k = a)
    (hb : ∀ k, S.b k = b) : Ɐ Φ.comp a x = Φ.comp b x := by
  have hcmin := Φ.cmin_pos S.pos_N
  have hz := ofReal_mem_nbhd Φ.ε_pos S.p₀_mem
  have hA := (Φ.differentiableOn_comp a).analyticOnNhd isOpen_nbhd
  have hB := (Φ.differentiableOn_comp b).analyticOnNhd isOpen_nbhd
  suffices heq : Φ.comp a =ᶠ[𝓝 (S.p₀ : ℂ)] Φ.comp b from
    fun x hx => hA.eqOn_of_preconnected_of_eventuallyEq hB (isPreconnected_nbhd ε) hz heq
      𝕬
  by_contra hne
  obtain ⟨m, g, hg, hg0, hfactor⟩ :=
    ((hA _ hz).sub (hB _ hz)).exists_eventuallyEq_pow_smul_nonzero_iff.2
      (by simpa [Filter.EventuallyEq, sub_eq_zero] using hne)
  have hq : Tendsto S.q atTop (𝓝 S.p₀) := by
    simpa using (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ((tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).comp
        (tendsto_atTop_mono (fun k => by simp_all)
          ((tendsto_sub_atTop_nat a.length).comp S.length_tendsto)))
      (fun k => (sub_pos.2 (S.p_lt_q k)).le) S.cmax_pow_ge).add S.tendsto_p
  let r k := if |S.q k - S.p₀| ≤ |S.p k - S.p₀| then S.p k else S.q k
  have hrmem : ∀ k, r k ∈ Icc 𝕮 𝕯 := by
    intro k
    dsimp [r]; split_ifs <;> constructor <;> linarith [S.p_lt_q k]
  obtain ⟨k, ⟨hkfac, hkg⟩, hksmall⟩ :=
    ((tendsto_of_tendsto_of_tendsto_of_le_of_le
      S.tendsto_p hq (fun k => (hrmem k).1) (fun k => (hrmem k).2)).ofReal.eventually
      (hfactor.and (hg.continuousAt.norm.eventually
        (le_mem_nhds (half_lt_self (norm_pos_iff.2 hg0)))))).and
      ((S.small.mul_pow_rpow S.one_le_length (fun k => (S.η_pos k).le) (2 ^ m / 𝕭)
        zero_le_one one_pos).eventually_lt_pow S.one_le_length (pow_pos hcmin m)) |>.exists
  obtain ⟨x, hx, hxy⟩ := S.mem_image k _ (hrmem k)
  have hclose := S.close k x hx
  simp [ha k, hb k, Φ.comp_append, ← hxy] at hclose
  have hlower : (Φ.cmin ^ 𝔪 / 2) ^ m * 𝕭 ≤
      S.η k := by
    refine le_trans ?_ hclose
    rw [← Pi.sub_apply, hkfac, norm_smul, norm_pow, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    gcongr
    dsimp [r]
    split_ifs <;> linarith [S.cmin_pow_le k, le_abs_self (S.q k - S.p₀), neg_le_abs (S.p k - S.p₀)]
  rw [one_pow, mul_one, Real.rpow_one, pow_right_comm, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    at hksmall
  rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at hlower
  linarith

/-- Equation (3.2), with a positive super-exponentially small bound on the image interval. -/
theorem exists_dualProj_small :
    ∃ η', (∀ k, 0 < η' k) ∧
      SupExpSmall (fun k => 𝔪) η' ∧
      ∀ᶠ k in atTop, ∀ y ∈ Icc 𝕮 𝕯,
        ‖Φ.dualProj (.fin (S.a k).reverse) y - Φ.dualProj (.fin (S.b k).reverse) y‖ ≤ η' k := by
  have hcmin := Φ.cmin_pos S.pos_N
  obtain ⟨K₀, η₀, hη₀, hK₀⟩ := Φ.exists_dualProj_closeness
  refine ⟨fun k => max K₀ 1 * (Φ.cmin⁻¹ ^ 2) ^ 𝔪 *
    S.η k ^ (1 / 4), fun k => by have := S.η_pos k; positivity,
    S.small.mul_pow_rpow S.one_le_length (fun k => (S.η_pos k).le) _ (by positivity)
      (by norm_num), ?_⟩
  filter_upwards [S.small.eventually_le S.one_le_length hη₀] with k hk y hy
  obtain ⟨x, hx, hxy⟩ := S.mem_image k y hy
  have := S.η_pos k
  rw [hxy, ← pow_mul]
  exact (hK₀ _ _ _ (S.length_eq k) (S.length_pos k) (S.getLast?_ne k) _ (S.η_pos k) hk
    (S.close k) x hx).trans (by gcongr; apply le_max_left)

/-- Bounded common suffixes: pass to the limit on the fixed nondegenerate image
interval using Lemma 2.11, then use the analytic identity theorem. -/
theorem dualProj_eq_of_fixed_suffix {u : 𝔚 N}
    (hu : ∀ k, S.u k = u)
    (hi : Word.TendstoPrefix (fun k => .fin (S.a k).reverse) 𝔤)
    (hj : Word.TendstoPrefix (fun k => .fin (S.b k).reverse) 𝔧) :
    Ɐ Φ.dualProj 𝔤 x = Φ.dualProj 𝔧 x := by
  obtain ⟨η', -, hη'small, hη'close⟩ := S.exists_dualProj_small
  obtain ⟨C, -, -, hC⟩ := Φ.exists_iteratedDeriv_bounds
  have hsub := Icc_subset_Icc (S.p_nonneg 0) (S.q_le_one 0)
  refine fun x hx => eqOn_nbhd_of_eqOn_Icc Φ.ε_pos 𝖞
    𝖞 (S.p_lt_q 0) hsub (fun y hy => eq_of_forall_dist_le
      fun δ hδ => ?_) 𝕬
  obtain ⟨m, hm⟩ := (((tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg
    Φ.cmax_lt_one).const_mul (2 * C 0)).eventually
      (ge_mem_nhds (by linarith : 2 * C 0 * 0 < δ / 3))).exists
  obtain ⟨k, hkη, hkclose, hki, hkj⟩ := ((hη'small.eventually_le S.one_le_length
    (by linarith : 0 < δ / 3)).and (hη'close.and ((hi.eventually_le_commonPrefixLength rfl m).and
      (hj.eventually_le_commonPrefixLength rfl m)))).exists
  rw [dist_eq_norm]
  exact (norm_sub_le_three (hC 0 y (hsub hy) _ _ m hki) (hkclose y (by rwa [← S.image_eq k, hu k, ← hu 0, S.image_eq 0]))
    (hC 0 y (hsub hy) _ _ m hkj)).trans (by linarith)

/-- Unbounded case: if `a_k^← → i` and `b_k^← → j`, then `H_i = H_j` on `I`. -/
theorem dualProj_eq
    (hi : Word.TendstoPrefix (fun k => .fin (S.a k).reverse) 𝔤)
    (hj : Word.TendstoPrefix (fun k => .fin (S.b k).reverse) 𝔧) :
    Ɐ Φ.dualProj 𝔤 x = Φ.dualProj 𝔧 x := by
  have hcmin := Φ.cmin_pos S.pos_N
  obtain ⟨η', hη'pos, hη'small, hη'close⟩ := S.exists_dualProj_small
  have hη'nonneg := fun k => (hη'pos k).le
  obtain ⟨C, -, -, hC⟩ := Φ.exists_iteratedDeriv_bounds
  refine fun x hx => eqOn_nbhd_of_iteratedDeriv_close Φ.ε_pos 𝖞
    𝖞 S.p₀_mem S.tendsto_p (fun r δ hδ => ?_)
    𝕬
  obtain ⟨K, Q, -, hKQ⟩ := Φ.exists_iteratedDeriv_dualProj_closeness r
  have hs : (0 : ℝ) < 2⁻¹ ^ r := by positivity
  obtain ⟨m, hm⟩ := (((tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg
    Φ.cmax_lt_one).const_mul (2 * C r)).eventually
      (ge_mem_nhds (by linarith : 2 * C r * 0 < δ / 3))).exists
  filter_upwards [hη'small.eventually_le S.one_le_length one_pos,
    (hη'small.mul_pow_rpow S.one_le_length hη'nonneg (2 * (2 + Q)) zero_le_one hs).eventually_lt_pow S.one_le_length hcmin,
    (hη'small.mul_pow_rpow S.one_le_length hη'nonneg (max K 0) (pow_nonneg (inv_nonneg.2 hcmin.le) r)
      hs).eventually_le S.one_le_length (by linarith : 0 < δ / 3), hη'close,
    hi.eventually_le_commonPrefixLength rfl m, hj.eventually_le_commonPrefixLength rfl m]
    with k h1 h2 h3 h4 h5 h6
  simp only [one_pow, mul_one] at h2
  obtain ⟨x, hx, hxp⟩ := S.mem_image k _ (left_mem_Icc.2 (S.p_lt_q k).le)
  obtain ⟨e3a, e3b⟩ := Φ.norm_iteratedDeriv_sub_le_on_image S.pos_N r (S.u k)
    (le_max_right K 0) (Real.rpow_nonneg (hη'nonneg k) (2⁻¹ ^ r))
    (fun y hy => ((hKQ _ _ _ _ _ (S.p_nonneg k) (S.p_lt_q k) (S.q_le_one k) (hη'pos k) h1 (h2.trans_le (S.cmin_pow_le k)) h4) y (S.image_eq k ▸ hy)).trans (mul_le_mul_of_nonneg_right
      (le_max_left _ _) (Real.rpow_nonneg (hη'nonneg k) _))) hx
  rw [← hxp] at e3a
  refine (norm_sub_le_three (hC r _ (S.p_mem k) _ _ m h5) (e3a.trans (e3b.trans (le_trans ?_ h3)))
    (hC r _ (S.p_mem k) _ _ m h6)).trans (by linarith)
  have := hη'pos k
  gcongr
  exacts [one_le_pow₀ ((one_le_inv₀ hcmin).2 ((Φ.cmin_le_cmax S.pos_N).trans
    Φ.cmax_lt_one.le)), Nat.le_add_left _ _]

/-- Unbounded case: if `|a_k| → ∞`, then two infinite words with different first letters have
equal dual natural projections on `I`. -/
theorem exists_dualProj_eq (hd : Φ.DualSSC)
    (h : Tendsto (fun k => (S.a k).length) atTop atTop)
    (hcase : (∃ u, ∀ k, S.u k = u) ∨ Tendsto (fun k => (S.u k).length) atTop atTop) : False := by
  obtain ⟨φ₁, hφ₁, w₁, hw₁⟩ := Word.exists_subseq_tendstoPrefix fun k => Word.fin (S.a k).reverse
  obtain ⟨φ₂, hφ₂, w₂, hw₂⟩ :=
    Word.exists_subseq_tendstoPrefix fun k => Word.fin (S.b (φ₁ k)).reverse
  set T := S.comp (φ₁ ∘ φ₂) (hφ₁.comp hφ₂)
  have hT1 : Word.TendstoPrefix (fun k => Word.fin (T.a k).reverse) w₁ := hw₁.comp hφ₂
  have hT2 : Word.TendstoPrefix (fun k => Word.fin (T.b k).reverse) w₂ := hw₂
  have hlen₁ : w₁.length = ⊤ := by
    refine hT1.tendsto_length (ENat.tendsto_nhds_top_iff_natCast_lt.2 fun n => ?_)
    filter_upwards [(h.comp (hφ₁.comp hφ₂).tendsto_atTop).eventually_gt_atTop n] with k hk
    simp
    exact hk
  obtain ⟨i, rfl⟩ := Word.eq_inf_of_length_eq_top hlen₁
  obtain ⟨j, rfl⟩ := Word.eq_inf_of_length_eq_top
    ((hT1.length_eq hT2 fun k => by simp [T.length_eq k]).symm.trans hlen₁)
  obtain ⟨x, hx, hne⟩ := hd i j fun hij => by
    obtain ⟨k, hk1, hk2⟩ := ((hT1.eventually_get?_eq 0).and (hT2.eventually_get?_eq 0)).exists
    apply T.getLast?_ne k
    simp [← List.head?_eq_getElem?]
      at hk1 hk2
    rw [hk1, hk2, hij]
  rcases hcase with ⟨u, hu⟩ | hu
  · exact hne (T.dualProj_eq_of_fixed_suffix (fun k => hu ((φ₁ ∘ φ₂) k)) hT1 hT2 x hx)
  · exact hne (T.dualProj_eq hT1 hT2 x hx)

end CondSeq

/-- Theorem 2.2: if the dual IFS satisfies the SSC, then `Φ` satisfies the SESC. -/
theorem theorem_2_2 (h : Φ.DualSSC) : Φ.SESC := by
  by_contra hS
  obtain ⟨S⟩ := Φ.nonempty_condSeq hS
  by_cases hU : Tendsto (fun k => (S.u k).length) atTop atTop
  · by_cases hB : Tendsto (fun k => (S.a k).length) atTop atTop
    · exact S.exists_dualProj_eq h hB (.inr hU)
    simp only [Filter.tendsto_atTop, not_forall, not_eventually, not_le] at hB
    obtain ⟨B, hB⟩ := hB
    obtain ⟨⟨a, b⟩, -, hab⟩ := exists_frequently_eq_of_frequently_mem
      ((List.finite_length_lt _ B).prod (List.finite_length_lt _ B)) (f := fun k => (S.a k, S.b k))
      (hB.mono fun k hk => ⟨hk, (S.length_eq k ▸ hk : (S.b k).length < B)⟩)
    obtain ⟨φ, hφ, hφab⟩ := extraction_of_frequently_atTop hab
    simp at hφab
    exact Φ.not_dualSSC_of_comp_eq (by simpa [(hφab 0).1, (hφab 0).2] using S.length_eq (φ 0))
      (by simpa [(hφab 0).1, (hφab 0).2] using S.getLast?_ne (φ 0))
      ((S.comp φ hφ).comp_eq_comp (fun k => (hφab k).1) fun k => (hφab k).2) h
  simp only [Filter.tendsto_atTop, not_forall, not_eventually, not_le] at hU
  obtain ⟨B, hB⟩ := hU
  obtain ⟨u, -, hu⟩ := exists_frequently_eq_of_frequently_mem (List.finite_length_lt _ B) hB
  obtain ⟨φ, hφ, hφu⟩ := extraction_of_frequently_atTop hu
  have hTu : ∀ k, (S.comp φ hφ).u k = u := hφu
  exact (S.comp φ hφ).exists_dualProj_eq h (tendsto_atTop_mono (fun k => by simp_all)
    ((tendsto_sub_atTop_nat u.length).comp (S.comp φ hφ).length_tendsto)) (.inl ⟨u, hTu⟩)

/-- Theorem 1.5: if `sup_{x ∈ [0,1]} |H_i(x) - H_j(x)| > 0` for all distinct `i, j ∈ Σ ∪ Σ_*` with
`|i| = |j|`, then `Φ` satisfies the SESC. -/
theorem theorem_1_5 (h : ∀ i j, i ≠ j →
      0 < ⨆ x : I, ‖Φ.dualProj 𝔤 x - Φ.dualProj 𝔧 x‖) :
    Φ.SESC := by
  refine Φ.theorem_2_2 fun i j hij => ?_
  by_contra! heq
  exact (h i j fun e => hij (congrFun e 0)).ne' (by simp [heq])

end IFS

end AnalyticESC
