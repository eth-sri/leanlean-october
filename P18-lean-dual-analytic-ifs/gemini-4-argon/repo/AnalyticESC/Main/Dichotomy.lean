module

public import AnalyticESC.Separation
public import AnalyticESC.Main.Closeness
public import AnalyticESC.Dual.Attractor

@[expose] public section

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

open Set Metric Filter Topology

/-! ## Super-exponentially small sequences -/

/-- `η k > 0` is eventually below `θ ^ n k`, for every `θ > 0`. -/
def SupExpSmall (n : ℕ → ℕ) (η : ℕ → ℝ) : Prop :=
  (∀ k, 0 < η k) ∧ ∀ θ > 0, ∀ᶠ k in atTop, η k ≤ θ ^ n k

namespace SupExpSmall

variable {n : ℕ → ℕ} {η : ℕ → ℝ}

theorem comp (h : SupExpSmall n η) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    SupExpSmall (n ∘ φ) (η ∘ φ) := ⟨fun k => h.1 (φ k), fun θ hθ => hφ.eventually (h.2 θ hθ)⟩

theorem eventually_le (hn : ∀ k, 1 ≤ n k) (h : SupExpSmall n η) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ k in atTop, η k ≤ δ := by
  filter_upwards [h.2 (min δ 1) (lt_min hδ one_pos)] with k hk
  exact (hk.trans (pow_le_of_le_one (le_min hδ.le zero_le_one) (min_le_right _ _)
    (by have := hn k; omega))).trans (min_le_left _ _)

theorem eventually_lt_pow (hn : ∀ k, 1 ≤ n k) (h : SupExpSmall n η) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ k in atTop, η k < c ^ n k := by
  filter_upwards [h.2 (c / 2) (half_pos hc)] with k hk
  exact hk.trans_lt (pow_lt_pow_left₀ (half_lt_self hc) (half_pos hc).le (by have := hn k; omega))

/-- `K A^{n_k} η_k^s` is super-exponentially small along with `η_k`. -/
theorem mul_pow_rpow (hn : ∀ k, 1 ≤ n k) (h : SupExpSmall n η) {K A s : ℝ}
    (hK : 0 < K) (hA : 0 < A) (hs : 0 < s) :
    SupExpSmall n fun k => K * A ^ n k * η k ^ s := by
  refine ⟨fun k => by have := h.1 k; positivity, fun θ hθ => ?_⟩
  set L := max K 1 * (A + 1) with hL_def
  have hL : 0 < L := by positivity
  have hθL : 0 < θ / L := div_pos hθ hL
  filter_upwards [h.2 _ (Real.rpow_pos_of_pos hθL s⁻¹)] with k hk
  have hη0 := (h.1 k).le
  have h1 : η k ^ s ≤ (θ / L) ^ n k :=
    (Real.rpow_le_rpow hη0 hk hs.le).trans_eq (by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hθL.le, ← Real.rpow_mul hθL.le,
        show s⁻¹ * (n k : ℝ) * s = n k by field_simp, Real.rpow_natCast])
  have h2 : K ≤ max K 1 ^ n k :=
    (le_max_left _ _).trans (le_self_pow₀ (le_max_right _ _) (by have := hn k; omega))
  exact (mul_le_mul (mul_le_mul h2 (pow_le_pow_left₀ hA.le (le_add_of_nonneg_right zero_le_one) _)
    (by positivity) (by positivity)) h1 (Real.rpow_nonneg hη0 _) (by positivity)).trans_eq
    (by rw [← mul_pow, ← mul_pow, ← hL_def, mul_div_cancel₀ _ hL.ne'])

end SupExpSmall

/-! ## Two elementary lemmas -/

/-- Pigeonhole: a sequence frequently in a finite set frequently takes one value. -/
private theorem exists_frequently_eq_of_frequently_mem {α : Type*} {s : Set α} (hs : s.Finite)
    {f : ℕ → α} (h : ∃ᶠ k in atTop, f k ∈ s) : ∃ a ∈ s, ∃ᶠ k in atTop, f k = a := by
  by_contra! hcon
  exact h (((eventually_all_finite hs).2 hcon).mono fun _ hk hks => hk _ hks rfl)

/-- Identity theorem along a convergent sequence: if all derivatives of two holomorphic maps are
asymptotically equal along points `p_k → p₀ ∈ I`, the maps agree on `B_ε`. -/
theorem eqOn_nbhd_of_iteratedDeriv_close {ε : ℝ} (hε : 0 < ε) {g h : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (nbhd ε)) (hh : DifferentiableOn ℂ h (nbhd ε)) {p : ℕ → ℝ}
    {p₀ : ℝ} (hp₀ : p₀ ∈ I) (hp : Tendsto p atTop (𝓝 p₀))
    (hclose : ∀ r, ∀ δ > 0, ∀ᶠ k in atTop,
      ‖iteratedDeriv r g (p k) - iteratedDeriv r h (p k)‖ ≤ δ) :
    EqOn g h (nbhd ε) :=
  eqOn_nbhd_of_iteratedDeriv_eq hε hg hh hp₀ fun r => by
    have hcont {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (nbhd ε)) :
        Tendsto (fun k => iteratedDeriv r f (p k)) atTop (𝓝 (iteratedDeriv r f p₀)) := by
      have : ContinuousAt (iteratedDeriv r f) p₀ :=
        ((differentiableOn_iteratedDeriv_of_isOpen (isOpen_nbhd ε) hf r).differentiableAt
          ((isOpen_nbhd ε).mem_nhds (ofReal_mem_nbhd hε hp₀))).continuousAt
      exact this.tendsto.comp ((Complex.continuous_ofReal.tendsto p₀).comp hp)
    rw [← sub_eq_zero, ← norm_le_zero_iff]
    exact le_of_forall_pos_le_add fun δ hδ => by
      simpa using le_of_tendsto ((hcont hg).sub (hcont hh)).norm (hclose r δ hδ)

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-! ## Condensing sequences -/

/-- A condensing sequence, extracted from the failure of the SESC: words `a_k u_k` and `b_k u_k`
of length `n_k = |a_k| + |u_k|`, with `|a_k| = |b_k| ≥ 1` and different last letters of `a_k`
and `b_k`, whose compositions are `η_k`-close on `I`, where `η_k` is super-exponentially small
in `n_k`. -/
structure CondSeq where
  /-- The first words. -/
  a : ℕ → List (Fin N)
  /-- The second words. -/
  b : ℕ → List (Fin N)
  /-- The common suffixes. -/
  u : ℕ → List (Fin N)
  /-- The distances. -/
  η : ℕ → ℝ
  length_eq : ∀ k, (a k).length = (b k).length
  length_pos : ∀ k, 0 < (a k).length
  getLast?_ne : ∀ k, (a k).getLast? ≠ (b k).getLast?
  close : ∀ k, ∀ x ∈ I, ‖Φ.comp (a k ++ u k) x - Φ.comp (b k ++ u k) x‖ ≤ η k
  small : SupExpSmall (fun k => (a k).length + (u k).length) η
  length_tendsto : Tendsto (fun k => (a k).length + (u k).length) atTop atTop

/-- The failure of the SESC gives a condensing sequence. -/
theorem nonempty_condSeq (h : ¬ Φ.SESC) : Nonempty Φ.CondSeq := by
  have h₂ (k : ℕ) : ∃ a b u : List (Fin N), a.length = b.length ∧ 0 < a.length ∧
      a.getLast? ≠ b.getLast? ∧ k ≤ a.length + u.length ∧ ∀ x ∈ I,
        ‖Φ.comp (a ++ u) x - Φ.comp (b ++ u) x‖ ≤ ((k : ℝ) + 2)⁻¹ ^ (a.length + u.length) := by
    obtain ⟨n, hnk, i, j, hij, hlt⟩ :=
      Φ.exists_close_pair_ge h (show 0 < ((k : ℝ) + 2)⁻¹ by positivity) k
    obtain ⟨a, b, u, hi, hj, hlen, hpos, hlast⟩ :=
      List.exists_decomp_of_ne (i := List.ofFn i) (j := List.ofFn j) (by simp)
        fun h => hij (List.ofFn_injective h)
    have hn : a.length + u.length = n := by rw [← List.length_append, ← hi, List.length_ofFn]
    exact ⟨a, b, u, hlen, hpos, hlast, hn ▸ hnk, fun x hx => by
      rw [← hi, ← hj, hn]; exact (Φ.norm_le_supDist _ _ hx).trans hlt.le⟩
  choose a b u hlen hpos hlast hnk hclose using h₂
  have hsmall : SupExpSmall (fun k => (a k).length + (u k).length)
      fun k => ((k : ℝ) + 2)⁻¹ ^ ((a k).length + (u k).length) :=
    ⟨fun _ => by positivity, fun θ hθ => by
      obtain ⟨m, hm⟩ := exists_nat_gt θ⁻¹
      filter_upwards [eventually_ge_atTop m] with k hk
      have : (m : ℝ) ≤ k := by exact_mod_cast hk
      exact pow_le_pow_left₀ (by positivity) ((inv_le_comm₀ (by positivity) hθ).2 (by linarith)) _⟩
  exact ⟨⟨a, b, u, _, hlen, hpos, hlast, hclose, hsmall, tendsto_atTop_mono hnk tendsto_id⟩⟩

namespace CondSeq

variable {Φ}

/-- Reindexing a condensing sequence along a strictly increasing map. -/
def comp (S : Φ.CondSeq) (φ : ℕ → ℕ) (hφ : StrictMono φ) : Φ.CondSeq where
  a := S.a ∘ φ
  b := S.b ∘ φ
  u := S.u ∘ φ
  η := S.η ∘ φ
  length_eq k := S.length_eq (φ k)
  length_pos k := S.length_pos (φ k)
  getLast?_ne k := S.getLast?_ne (φ k)
  close k := S.close (φ k)
  small := S.small.comp hφ.tendsto_atTop
  length_tendsto := S.length_tendsto.comp hφ.tendsto_atTop

theorem pos_N (S : Φ.CondSeq) : 0 < N :=
  ((S.a 0).head (List.ne_nil_of_length_pos (S.length_pos 0))).pos

theorem one_le_length (S : Φ.CondSeq) (k : ℕ) : 1 ≤ (S.a k).length + (S.u k).length := by
  have := S.length_pos k; omega

/-- The left endpoints of `f_{u_k}(I)`. -/
noncomputable abbrev p (S : Φ.CondSeq) (k : ℕ) :=
  (Φ.exists_image_comp_eq_Icc (S.u k)).choose

/-- The right endpoints of `f_{u_k}(I)`. -/
noncomputable abbrev q (S : Φ.CondSeq) (k : ℕ) :=
  (Φ.exists_image_comp_eq_Icc (S.u k)).choose_spec.choose

private abbrev pq_spec (S : Φ.CondSeq) (k : ℕ) :=
  (Φ.exists_image_comp_eq_Icc (S.u k)).choose_spec.choose_spec

theorem cmin_pow_le (S : Φ.CondSeq) (k : ℕ) :
    Φ.cmin ^ ((S.a k).length + (S.u k).length) ≤ S.q k - S.p k :=
  (pow_le_pow_of_le_one Φ.cmin_nonneg
    ((Φ.cmin_le_cmax S.pos_N).trans Φ.cmax_lt_one.le) (Nat.le_add_left _ _)).trans
    (S.pq_spec k).2.2.1

theorem p_lt_q (S : Φ.CondSeq) (k : ℕ) : S.p k < S.q k :=
  sub_pos.1 ((pow_pos (Φ.cmin_pos S.pos_N) _).trans_le (S.cmin_pow_le k))

theorem p_mem (S : Φ.CondSeq) (k : ℕ) : S.p k ∈ I :=
  ⟨(S.pq_spec k).1, (S.p_lt_q k).le.trans (S.pq_spec k).2.1⟩

/-- Finite limit words: finite order of vanishing contradicts super-exponential
closeness on intervals whose lengths are at least `c_min^{n_k}`. -/
theorem comp_eq_comp (S₀ : Φ.CondSeq) {a b : List (Fin N)} (ha : ∀ k, S₀.a k = a)
    (hb : ∀ k, S₀.b k = b) : ∀ x ∈ I, Φ.comp a x = Φ.comp b x := by
  obtain ⟨p₀, hp₀, φ, hφ, htp⟩ := isCompact_Icc.tendsto_subseq S₀.p_mem
  set S := S₀.comp φ hφ
  change Tendsto S.p atTop (𝓝 p₀) at htp
  have hcmin := Φ.cmin_pos S.pos_N
  have hz := ofReal_mem_nbhd Φ.ε_pos hp₀
  have hA := (Φ.differentiableOn_comp a).analyticOnNhd (isOpen_nbhd ε)
  have hB := (Φ.differentiableOn_comp b).analyticOnNhd (isOpen_nbhd ε)
  suffices heq : Φ.comp a =ᶠ[𝓝 (p₀ : ℂ)] Φ.comp b from
    fun x hx => hA.eqOn_of_preconnected_of_eventuallyEq hB (isPreconnected_nbhd ε) hz heq
      (ofReal_mem_nbhd Φ.ε_pos hx)
  by_contra hne
  have hne' : ¬ ∀ᶠ z in 𝓝 (p₀ : ℂ), Φ.comp a z - Φ.comp b z = 0 := by
    simpa only [Filter.EventuallyEq, sub_eq_zero] using hne
  obtain ⟨m, g, hg, hg0, hfactor⟩ :=
    ((hA _ hz).sub (hB _ hz)).exists_eventuallyEq_pow_smul_nonzero_iff.2 hne'
  let D := ‖g p₀‖ / 2
  have hD : 0 < D := half_pos (norm_pos_iff.2 hg0)
  have hgne : ∀ᶠ z in 𝓝 (p₀ : ℂ), D ≤ ‖g z‖ :=
    hg.continuousAt.norm.eventually (le_mem_nhds (half_lt_self (norm_pos_iff.2 hg0)))
  have hu : Tendsto (fun k => (S.u k).length) atTop atTop :=
    Filter.tendsto_atTop.2 fun B =>
      (S.length_tendsto.eventually_ge_atTop (B + a.length)).mono fun k hk => by
        rw [show S.a k = a from ha (φ k)] at hk; omega
  have hq : Tendsto S.q atTop (𝓝 p₀) := by
    simpa using (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ((tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).comp hu)
      (fun k => (sub_pos.2 (S.p_lt_q k)).le) (fun k => (S.pq_spec k).2.2.2.1)).add htp
  let r (k : ℕ) := if |S.q k - p₀| ≤ |S.p k - p₀| then S.p k else S.q k
  have hrmem (k : ℕ) : r k ∈ Icc (S.p k) (S.q k) := by
    dsimp [r]; split_ifs <;> exact ⟨by linarith [S.p_lt_q k], by linarith [S.p_lt_q k]⟩
  have hrlim : Tendsto (fun k => (r k : ℂ)) atTop (𝓝 (p₀ : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_of_tendsto_of_tendsto_of_le_of_le htp hq
        (fun k => (hrmem k).1) (fun k => (hrmem k).2))
  have hfar (k : ℕ) : (S.q k - S.p k) / 2 ≤ |r k - p₀| := by
    have ht : S.q k - S.p k ≤ |S.q k - p₀| + |S.p k - p₀| :=
      (by ring : S.q k - S.p k = (S.q k - p₀) + -(S.p k - p₀)).trans_le
        (add_le_add (le_abs_self _) (neg_le_abs _))
    dsimp [r]; split_ifs <;> linarith
  have hsmall := (S.small.mul_pow_rpow S.one_le_length
    (by positivity : 0 < (2 : ℝ) ^ m / D) one_pos one_pos).eventually_lt_pow
    S.one_le_length (pow_pos hcmin m)
  obtain ⟨k, hkfac, hkg, hksmall⟩ :=
    ((hrlim.eventually hfactor).and ((hrlim.eventually hgne).and hsmall)).exists
  have hclose : ‖Φ.comp a (r k) - Φ.comp b (r k)‖ ≤ S.η k := by
    obtain ⟨x, hx, hxy⟩ := (S.pq_spec k).2.2.2.2 _ (hrmem k)
    rw [hxy]
    simpa only [show S.a k = a from ha (φ k), show S.b k = b from hb (φ k),
      Φ.comp_append, Function.comp_apply] using S.close k x hx
  have hlower : D * (Φ.cmin ^ ((S.a k).length + (S.u k).length) / 2) ^ m ≤ S.η k := by
    calc _ ≤ ‖g (r k)‖ * |r k - p₀| ^ m :=
        mul_le_mul hkg (pow_le_pow_left₀ (by positivity)
          ((div_le_div_of_nonneg_right (S.cmin_pow_le k) (by norm_num)).trans (hfar k)) _)
          (by positivity) (norm_nonneg _)
      _ = ‖Φ.comp a (r k) - Φ.comp b (r k)‖ := by
        change ‖g (r k)‖ * |r k - p₀| ^ m = ‖(Φ.comp a - Φ.comp b) (r k)‖
        rw [hkfac, norm_smul, norm_pow, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact mul_comm _ _
      _ ≤ S.η k := hclose
  simp only [one_pow, mul_one, Real.rpow_one] at hksmall
  rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)] at hlower
  rw [← pow_right_comm, div_mul_eq_mul_div, div_lt_iff₀ hD] at hksmall
  linarith

/-- Equation (3.2), with a positive super-exponentially small bound on the image interval. -/
theorem exists_dualProj_small (S : Φ.CondSeq) :
    ∃ η' : ℕ → ℝ, SupExpSmall (fun k => (S.a k).length + (S.u k).length) η' ∧
      ∀ᶠ k in atTop, ∀ y ∈ Icc (S.p k) (S.q k),
        ‖Φ.dualProj (.fin (S.a k).reverse) y - Φ.dualProj (.fin (S.b k).reverse) y‖ ≤ η' k := by
  have hcmin := Φ.cmin_pos S.pos_N
  have hn := S.one_le_length
  obtain ⟨K₀, η₀, hη₀, hK₀⟩ := Φ.exists_dualProj_closeness
  refine ⟨_, S.small.mul_pow_rpow hn (lt_max_of_lt_right one_pos : 0 < max K₀ 1)
    (show 0 < Φ.cmin⁻¹ ^ 2 by positivity) (by norm_num : (0 : ℝ) < 1 / 4), ?_⟩
  filter_upwards [S.small.eventually_le hn hη₀] with k hk y hy
  obtain ⟨x, hx, hxy⟩ := (S.pq_spec k).2.2.2.2 y hy
  rw [hxy]
  have := S.small.1 k
  exact (hK₀ _ _ _ (S.length_eq k) (S.length_pos k) (S.getLast?_ne k) _ this hk
    (S.close k) x hx).trans (pow_mul Φ.cmin⁻¹ 2 _ ▸
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (by positivity)) (by positivity))

/-- Unbounded case: if `a_k^← → i` and `b_k^← → j`, then `H_i = H_j` on `I`. -/
theorem dualProj_eq (S₀ : Φ.CondSeq) {i j : ℕ → Fin N}
    (hi : Word.TendstoPrefix (fun k => .fin (S₀.a k).reverse) (.inf i))
    (hj : Word.TendstoPrefix (fun k => .fin (S₀.b k).reverse) (.inf j)) :
    ∀ x ∈ I, Φ.dualProj (.inf i) x = Φ.dualProj (.inf j) x := by
  obtain ⟨p₀, hp₀, φ, hφ, htp⟩ := isCompact_Icc.tendsto_subseq S₀.p_mem
  set S := S₀.comp φ hφ
  replace hi : Word.TendstoPrefix (fun k => .fin (S.a k).reverse) (.inf i) := hi.comp hφ
  replace hj : Word.TendstoPrefix (fun k => .fin (S.b k).reverse) (.inf j) := hj.comp hφ
  have hcmin := Φ.cmin_pos S.pos_N
  have hn := S.one_le_length
  obtain ⟨η', hη'small, hη'close⟩ := S.exists_dualProj_small
  obtain ⟨C, -, -, hC⟩ := Φ.exists_iteratedDeriv_bounds
  have heq : EqOn (Φ.dualProj (.inf i)) (Φ.dualProj (.inf j)) (nbhd ε) := by
    refine eqOn_nbhd_of_iteratedDeriv_close Φ.ε_pos (Φ.differentiableOn_dualProj _)
      (Φ.differentiableOn_dualProj _) (p := S.p) hp₀ htp fun r δ hδ => ?_
    obtain ⟨K, Q, hQ0, hKQ⟩ := Φ.exists_iteratedDeriv_dualProj_closeness r
    have hs : (0 : ℝ) < (2 : ℝ)⁻¹ ^ r := by positivity
    have hδ3 : 0 < δ / 3 := by positivity
    obtain ⟨m, hm⟩ : ∃ m : ℕ, 2 * C r * Φ.cmax ^ m ≤ δ / 3 := by
      have : Tendsto (fun m : ℕ => 2 * C r * Φ.cmax ^ m) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg
          Φ.cmax_lt_one).const_mul (2 * C r)
      exact (this.eventually (ge_mem_nhds hδ3)).exists
    have h1 := hη'small.eventually_le hn one_pos
    have h2 := (hη'small.mul_pow_rpow hn (by positivity : 0 < 2 * (2 + Q)) one_pos
      hs).eventually_lt_pow hn hcmin
    have h3 := (hη'small.mul_pow_rpow hn (lt_max_of_lt_right one_pos : 0 < max K 1) one_pos
      hs).eventually_le hn hδ3
    filter_upwards [h1, h2, h3, hη'close, hi.eventually_le_commonPrefixLength m,
      hj.eventually_le_commonPrefixLength m] with k h1 h2 h3 h4 h5 h6
    simp only [one_pow, mul_one] at h2 h3
    have e1 := hC r _ (S.p_mem k) _ _ m h5
    have e2 := hC r _ (S.p_mem k) _ _ m h6
    have e3 := (hKQ _ _ _ _ _ (S.pq_spec k).1 (S.pq_spec k).2.1 (hη'small.1 k) h1
      (h2.trans_le (S.cmin_pow_le k)) h4 (S.p k) (left_mem_Icc.2 (S.p_lt_q k).le)).trans
      ((mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (hη'small.1 k).le _)).trans h3)
    set A := iteratedDeriv r (Φ.dualProj (.fin (S.a k).reverse)) (S.p k)
    set B := iteratedDeriv r (Φ.dualProj (.fin (S.b k).reverse)) (S.p k)
    set Hi := iteratedDeriv r (Φ.dualProj (.inf i)) (S.p k)
    set Hj := iteratedDeriv r (Φ.dualProj (.inf j)) (S.p k)
    have htri := norm_add₃_le (a := -(A - Hi)) (b := A - B) (c := B - Hj)
    rw [show -(A - Hi) + (A - B) + (B - Hj) = Hi - Hj by ring, norm_neg] at htri
    linarith
  exact fun _ hx => heq (ofReal_mem_nbhd Φ.ε_pos hx)

/-- Unbounded case: if `|a_k| → ∞`, then two infinite words with different first letters have
equal dual natural projections on `I`. -/
theorem exists_dualProj_eq (S : Φ.CondSeq) (h : Tendsto (fun k => (S.a k).length) atTop atTop) :
    ∃ i j : ℕ → Fin N, i 0 ≠ j 0 ∧ ∀ x ∈ I, Φ.dualProj (.inf i) x = Φ.dualProj (.inf j) x := by
  obtain ⟨φ₁, hφ₁, i, hw₁⟩ := Word.exists_subseq_tendstoPrefix S.pos_N (l := fun k => (S.a k).reverse)
    (by simpa using h)
  obtain ⟨φ₂, hφ₂, j, hw₂⟩ := Word.exists_subseq_tendstoPrefix S.pos_N
    (l := fun k => (S.b (φ₁ k)).reverse)
    (by simpa [Function.comp_def, ← S.length_eq] using h.comp hφ₁.tendsto_atTop)
  set T := S.comp (φ₁ ∘ φ₂) (hφ₁.comp hφ₂)
  have hT1 : Word.TendstoPrefix (fun k => Word.fin (T.a k).reverse) (.inf i) := hw₁.comp hφ₂
  have hT2 : Word.TendstoPrefix (fun k => Word.fin (T.b k).reverse) (.inf j) := hw₂
  refine ⟨i, j, fun hij => ?_, T.dualProj_eq hT1 hT2⟩
  obtain ⟨k, hk1, hk2⟩ := ((hT1 0).and (hT2 0)).exists
  apply T.getLast?_ne k
  simp only [Word.get?_fin, Word.get?_inf, ← List.head?_eq_getElem?, List.head?_reverse]
    at hk1 hk2
  rw [hk1, hk2, hij]

end CondSeq

/-- The condensation dichotomy behind the proofs of Theorems 1.5 and 2.2. -/
theorem condensation_dichotomy (h : ¬ Φ.SESC) :
    (∃ i j : ℕ → Fin N, i 0 ≠ j 0 ∧ ∀ x ∈ I, Φ.dualProj (.inf i) x = Φ.dualProj (.inf j) x) ∨
      ∃ a b : List (Fin N), a.length = b.length ∧ 0 < a.length ∧ a.getLast? ≠ b.getLast? ∧
        ∀ x ∈ I, Φ.comp a x = Φ.comp b x := by
  obtain ⟨S⟩ := Φ.nonempty_condSeq h
  by_cases hB : ∃ B, ∃ᶠ k in atTop, (S.a k).length ≤ B
  · right
    obtain ⟨B, hB⟩ := hB
    have hfin := (List.finite_length_le (Fin N) B).prod (List.finite_length_le (Fin N) B)
    obtain ⟨⟨a, b⟩, -, hab⟩ := exists_frequently_eq_of_frequently_mem hfin
      (f := fun k => (S.a k, S.b k))
      (hB.mono fun k hk => ⟨hk, (S.length_eq k ▸ hk : (S.b k).length ≤ B)⟩)
    obtain ⟨φ, hφ, hφab⟩ := extraction_of_frequently_atTop hab
    set T := S.comp φ hφ
    have ha : ∀ k, T.a k = a := fun k => congrArg Prod.fst (hφab k)
    have hb : ∀ k, T.b k = b := fun k => congrArg Prod.snd (hφab k)
    exact ⟨a, b, ha 0 ▸ hb 0 ▸ T.length_eq 0, ha 0 ▸ T.length_pos 0,
      ha 0 ▸ hb 0 ▸ T.getLast?_ne 0, T.comp_eq_comp ha hb⟩
  · left
    simp only [not_exists, not_frequently, not_le] at hB
    exact S.exists_dualProj_eq (Filter.tendsto_atTop.2 fun B => (hB B).mono fun k hk => hk.le)

/-- Theorem 2.2: if the dual IFS satisfies the SSC, then `Φ` satisfies the SESC. -/
theorem theorem_2_2 (h : Φ.DualSSC) : Φ.SESC := by
  by_contra hS
  rcases Φ.condensation_dichotomy hS with ⟨i, j, hij, heq⟩ | ⟨a, b, hlen, -, hlast, heq⟩
  · obtain ⟨x, hx, hne⟩ := h i j hij
    exact hne (heq x hx)
  · exact Φ.not_dualSSC_of_comp_eq hlen hlast heq h

/-- Theorem 1.5: if `sup_{x ∈ [0,1]} |H_i(x) - H_j(x)| > 0` for all distinct `i, j ∈ Σ ∪ Σ_*` with
`|i| = |j|`, then `Φ` satisfies the SESC. -/
theorem theorem_1_5
    (h : ∀ i j : Word N, i ≠ j → i.length = j.length →
      0 < ⨆ x : I, ‖Φ.dualProj i ((x : ℝ) : ℂ) - Φ.dualProj j ((x : ℝ) : ℂ)‖) :
    Φ.SESC := by
  refine Φ.theorem_2_2 fun i j hij => ?_
  by_contra! heq
  simpa [heq] using (h (.inf i) (.inf j) (fun hw => hij (congrFun (Word.inf.inj hw) 0)) rfl).ne'

end IFS

end AnalyticESC
