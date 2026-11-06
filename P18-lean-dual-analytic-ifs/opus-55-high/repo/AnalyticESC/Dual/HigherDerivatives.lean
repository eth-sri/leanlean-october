module

public import AnalyticESC.Dual.Projection
set_option hygiene false
local notation "𝕸" => subset_closure hz
local notation "𝕷" => Φ.dualProj w
local notation "𝕶" => gPoly k
local notation "𝕵" => Φ.comp w.reverse
local notation "𝕴" => Φ.dualProj (.fin (w.take n))
local notation "𝔈" => .fin w

local notation "𝔷" => k + 1

local notation "𝔶" => f z


@[expose] public section

/-!
# Lemma 2.8

The higher derivatives of the dual natural projection: the identity (2.10),
`f_v^{(k+1)}/f_v' = g_k(H_{v^←}^{(k-1)}, …, H_{v^←})`, and the formula of Lemma 2.8 for
`H_w^{(k)}`, obtained from (2.8) and Faà di Bruno's formula. The set partitions `Π_{k+1}` of the
paper are Mathlib's `OrderedFinpartition (k + 1)`, the partitions of `Fin (k + 1)` with blocks
ordered by their greatest element.
-/

namespace AnalyticESC
variable {s : Set ℕ}

variable {U : Set ℂ} {z : ℂ}

open Metric Filter Topology

/-- The polynomials `g_k` of Section 2.2. The variable `X ℓ` stands for `y_{ℓ+1}`, which is
evaluated at `H^{(ℓ)}`: `g_0 = 1` and `g_{k+1} = ∑_{ℓ < k} ∂g_k/∂X_ℓ · X_{ℓ+1} + g_k · X_0`, so
that `g_1 = X_0`, `g_2 = X_1 + X_0²` and `g_3 = X_2 + 3 X_0 X_1 + X_0³`. -/
noncomputable def gPoly : ℕ → MvPolynomial ℕ ℤ
  | 0 => 1
  | k + 1 => (∑ ℓ ∈ Finset.range k, MvPolynomial.pderiv ℓ 𝕶 * MvPolynomial.X (ℓ + 1)) +
      gPoly k * MvPolynomial.X 0

/-! ## Polynomials along curves -/

/-- Partial derivatives preserve the polynomials in the variables of `s`. -/
theorem pderiv_mem_supported
    (hp : p ∈ MvPolynomial.supported ℤ s) ℓ :
    MvPolynomial.pderiv ℓ p ∈ MvPolynomial.supported ℤ s := by
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, -, rfl⟩ := hx
    by_cases h : m = ℓ
    · simp_all
    · simp_all
  | algebraMap r =>
    rw [Derivation.map_algebraMap]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | mul x y hx' hy' hx hy =>
    rw [MvPolynomial.pderiv_mul]
    exact add_mem (mul_mem hx hy') (mul_mem hx' hy)

/-- `g_k` is a polynomial in `X 0, …, X (k-1)`, that is, in `y_1, …, y_k`. -/
theorem gPoly_mem_supported k :
    gPoly k ∈ MvPolynomial.supported ℤ (↑(Finset.range k) : Set ℕ) := by
  induction k with
  | zero => exact one_mem _
  | succ k ih =>
    have hmono : MvPolynomial.supported ℤ (↑(Finset.range k) : Set ℕ) ≤
        MvPolynomial.supported ℤ ↑(Finset.range 𝔷) :=
      MvPolynomial.supported_mono (Finset.coe_subset.2 (Finset.range_subset_range.2 k.le_succ))
    have hX : ∀ m ≤ k,
        MvPolynomial.X m ∈ MvPolynomial.supported ℤ (↑(Finset.range 𝔷) : Set ℕ) :=
      fun m hm => MvPolynomial.X_mem_supported.2 (Finset.mem_range.2 (Nat.lt_succ_of_le hm))
    exact add_mem (Subalgebra.sum_mem _ fun ℓ hℓ => mul_mem (hmono (pderiv_mem_supported ih ℓ))
      (hX _ (Finset.mem_range.1 hℓ))) (mul_mem (hmono ih) (hX 0 k.zero_le))

/-- The chain rule for a polynomial in the variables of `s` along a curve `y`: if each `y_ℓ`,
`ℓ ∈ s`, has derivative `y'_ℓ` at `z`, then `u ↦ p(y(u))` has derivative
`∑_{ℓ ∈ s} ∂_ℓ p(y(z)) · y'_ℓ` at `z`. -/
theorem hasDerivAt_aeval_of_mem_supported {s : Finset ℕ}
    (hp : p ∈ MvPolynomial.supported ℤ (s : Set ℕ)) {y : ℕ → ℂ → ℂ} {y' : ℕ → ℂ}
    (hy : ∀ ℓ ∈ s, HasDerivAt (y ℓ) (y' ℓ) z) :
    HasDerivAt (fun u => MvPolynomial.aeval (fun ℓ => y ℓ u) p)
      (∑ ℓ ∈ s, MvPolynomial.aeval (fun ℓ => y ℓ z) (MvPolynomial.pderiv ℓ p) * y' ℓ) z := by
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    rw [Finset.sum_eq_single m (fun ℓ _ hℓ => by rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hℓ),
      map_zero, zero_mul]) (absurd hm)]
    simpa using hy m hm
  | algebraMap r =>
    simp
    exact hasDerivAt_const z _
  | add p q _ _ hp hq =>
    simp [add_mul, Finset.sum_add_distrib]
    exact hp.fun_add hq
  | mul p q _ _ hp hq =>
    simp only [map_mul]
    convert hp.fun_mul hq using 1
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul]
    ring

/-! ## Holomorphic maps -/

/-- A polynomial in finitely many bounded variables is uniformly bounded. This supplies the
constants `E_k` used after (2.10), without estimating derivatives by Cauchy's formula. -/
theorem exists_norm_aeval_le_of_supported
    (hp : p ∈ MvPolynomial.supported ℤ s) (C : ℕ → ℝ) (hC : ∀ ℓ ∈ s, 0 ≤ C ℓ) :
    ∃ E ≥ 0, ∀ y : ℕ → ℂ, (∀ ℓ ∈ s, ‖y ℓ‖ ≤ C ℓ) → ‖MvPolynomial.aeval y p‖ ≤ E := by
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨ℓ, hℓ, rfl⟩ := hx
    exact ⟨C ℓ, hC ℓ hℓ, fun y hy => by simp_all⟩
  | algebraMap r =>
    refine ⟨‖(r : ℂ)‖, norm_nonneg _, fun y _ => ?_⟩
    simp
  | add p q _ _ hp hq =>
    obtain ⟨E, hE, hp⟩ := hp
    obtain ⟨F, hF, hq⟩ := hq
    refine ⟨E + F, add_nonneg hE hF, fun y hy => ?_⟩
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add (hp y hy) (hq y hy))
  | mul p q _ _ hp hq =>
    obtain ⟨E, hE, hp⟩ := hp
    obtain ⟨F, hF, hq⟩ := hq
    refine ⟨E * F, mul_nonneg hE hF, fun y hy => ?_⟩
    rw [map_mul, norm_mul]
    exact mul_le_mul (hp y hy) (hq y hy) (norm_nonneg _) hE

/-- Iterated derivatives of a map holomorphic on an open set are holomorphic there. -/
theorem differentiableAt_iteratedDeriv {g : ℂ → ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) k (hz : z ∈ U) :
    DifferentiableAt ℂ (iteratedDeriv k g) z := by
  rw [iteratedDeriv_eq_iterate]
  exact ((hg.analyticOnNhd hU).iterated_deriv k z hz).differentiableAt

/-- Termwise iterated differentiation of a series of holomorphic maps on an open set whose terms
are bounded by a summable sequence. -/
theorem hasSum_iteratedDeriv_of_summable_norm {ι : Type*} {F : ι → ℂ → ℂ}
    {u : ι → ℝ} (hu : Summable u) (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hU : IsOpen U)
    (hF_le : ∀ i, ∀ z ∈ U, ‖F i z‖ ≤ u i) k (hz : z ∈ U) :
    HasSum (fun i => iteratedDeriv k (F i) z) (iteratedDeriv k (fun w => ∑' i, F i w) z) := by
  have hG : ∀ s, DifferentiableOn ℂ (fun w => ∑ i ∈ s, F i w) U := by fun_prop
  have hlim : ∀ m, TendstoLocallyUniformlyOn
      (fun s => iteratedDeriv m fun w => ∑ i ∈ s, F i w)
      (iteratedDeriv m fun w => ∑' i, F i w) atTop U := by
    intro m
    induction m with
    | zero => simpa using (tendstoUniformlyOn_tsum hu hF_le).tendstoLocallyUniformlyOn
    | succ m ih =>
      simp [iteratedDeriv_succ]
      exact ih.deriv (Eventually.of_forall fun s w hw =>
        (differentiableAt_iteratedDeriv hU (hG s) m hw).differentiableWithinAt) hU
  exact ((hlim k).tendsto_at hz).congr fun s => iteratedDeriv_fun_sum fun i _ =>
    ((hF i).analyticAt (hU.mem_nhds hz)).contDiffAt

/-- The `k`-th derivative of `(h ∘ f) · f'` is the Faà di Bruno sum for the `(k+1)`-th derivative
of `Ψ ∘ f`, where `Ψ` is a primitive of `h` near `f(z)`, so that `Ψ^{(m)} = h^{(m-1)}`. -/
theorem iteratedDeriv_comp_mul_deriv {h f : ℂ → ℂ} (hr : 0 < r)
    (hh : DifferentiableOn ℂ h (ball 𝔶 r)) (hf : AnalyticAt ℂ f z) k :
    iteratedDeriv k (fun u => h (f u) * deriv f u) z =
      ∑ c : OrderedFinpartition 𝔷,
        iteratedDeriv (c.length - 1) h 𝔶 * ∏ j, iteratedDeriv (c.partSize j) f z := by
  obtain ⟨Ψ, hΨ⟩ := hh.isExactOn_ball
  have heq : (fun u => h (f u) * deriv f u) =ᶠ[𝓝 z] deriv (Ψ ∘ f) := by
    filter_upwards [hf.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hr), hf.eventually_analyticAt]
      with u hu hfu
    exact ((hΨ _ hu).comp u hfu.differentiableAt.hasDerivAt).deriv.symm
  have hΨd : deriv Ψ =ᶠ[𝓝 𝔶] h := by
    filter_upwards [ball_mem_nhds _ hr] with v hv using (hΨ v hv).deriv
  have hΨa : AnalyticAt ℂ Ψ 𝔶 :=
    DifferentiableOn.analyticAt (fun v hv => (hΨ v hv).differentiableAt.differentiableWithinAt)
      (ball_mem_nhds _ hr)
  have hΨm : ∀ m, 0 < m → iteratedDeriv m Ψ 𝔶 = iteratedDeriv (m - 1) h 𝔶 := by
    intro m hm
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    rw [iteratedDeriv_succ', hΨd.iteratedDeriv_eq m, Nat.succ_sub_one]
  rw [heq.iteratedDeriv_eq k, ← iteratedDeriv_succ',
    iteratedDeriv_comp_eq_sum_orderedFinpartition hΨa.contDiffAt hf.contDiffAt le_rfl]
  exact Finset.sum_congr rfl fun c _ => by rw [hΨm _ (c.length_pos k.succ_pos)]

namespace IFS

variable (Φ : IFS N ε) (w : Word N)

/-- The term with index `n` (from `0`) of the formula of Lemma 2.8 for `H_w^{(k)}`: with `v` the
first `n` letters of `w` and `i` the next one, the sum over partitions `π` of `{1, …, k+1}` of
`φ_i^{(|π|)}(f_{v^←}(z)) · (f_{v^←}'(z))^{|π|} · ∏_{B ∈ π} g_{|B|-1}(H_v^{(|B|-2)}(z), …, H_v(z))`,
where `φ_i^{(m)} = (f_i''/f_i')^{(m-1)}` for `m ≥ 1`. Zero if `|w| ≤ n`. -/
noncomputable def dualDerivTerm (k n : ℕ) (z : ℂ) : ℂ :=
  match w.get? n with
  | none => 0
  | some i => ∑ c : OrderedFinpartition 𝔷,
      iteratedDeriv (c.length - 1) (Φ.nonlin i) (Φ.comp 𝔱 z) *
        𝔡ᶜ Φ 𝔱 z ^ c.length *
        ∏ j, MvPolynomial.aeval (fun ℓ => iteratedDeriv ℓ 𝕴 z)
          (gPoly (c.partSize j - 1))

/-! ## The identity (2.10) -/

/-- `H_w^{(ℓ)}` has derivative `H_w^{(ℓ+1)}` on `B_ε`. -/
theorem hasDerivAt_iteratedDeriv_dualProj ℓ (hz : z ∈ nbhd ε) :
    HasDerivAt (iteratedDeriv ℓ 𝕷) (iteratedDeriv (ℓ + 1) 𝕷 z) z := by
  rw [iteratedDeriv_succ]
  exact (differentiableAt_iteratedDeriv isOpen_nbhd (Φ.differentiableOn_dualProj w) ℓ
    hz).hasDerivAt

/-- (2.10) in product form on `B_ε`: `f_v^{(k+1)} = f_v' · g_k(H_{v^←}^{(k-1)}, …, H_{v^←})`,
where `f_v = Φ.comp w.reverse` and `H_{v^←} = Φ.dualProj (.fin w)`. -/
theorem iteratedDeriv_succ_comp_reverse w k (hz : z ∈ nbhd ε) :
    iteratedDeriv 𝔷 𝕵 z = 𝔡ᶜ Φ w.reverse z *
      MvPolynomial.aeval (fun ℓ => iteratedDeriv ℓ (Φ.dualProj 𝔈) z) 𝕶 := by
  induction k generalizing z with
  | zero => simp [gPoly]
  | succ k ih =>
    have heq : iteratedDeriv 𝔷 𝕵 =ᶠ[𝓝 z] fun u =>
        𝔡ᶜ Φ w.reverse u *
          MvPolynomial.aeval (fun ℓ => iteratedDeriv ℓ (Φ.dualProj 𝔈) u) 𝕶 := by
      filter_upwards [isOpen_nbhd.mem_nhds hz] with u hu using ih hu
    have hf' : HasDerivAt (𝔡ᶜ Φ w.reverse) (𝔇 𝕵 z) z :=
      ((((Φ.differentiableOn_comp _).deriv isOpen_nbhd) z hz).differentiableAt
        (isOpen_nbhd.mem_nhds hz)).hasDerivAt
    -- (2.7): `f_v'' = f_v' · H_{v^←}`
    have hH : 𝔇 𝕵 z =
        𝔡ᶜ Φ w.reverse z * Φ.dualProj 𝔈 z := by
      have h := Φ.dualProj_fin_reverse w.reverse 𝕸
      rw [List.reverse_reverse] at h
      rw [h, mul_div_cancel₀ _ (Φ.deriv_comp_ne_zero _ 𝕸)]
    rw [iteratedDeriv_succ, heq.deriv_eq, (hf'.fun_mul (hasDerivAt_aeval_of_mem_supported (gPoly_mem_supported k) (y := fun ℓ => iteratedDeriv ℓ (Φ.dualProj 𝔈)) (fun ℓ _ => Φ.hasDerivAt_iteratedDeriv_dualProj 𝔈 ℓ hz))).deriv, hH]
    simp [gPoly]
    ring

/-! ## Lemma 2.8 -/

/-- Lemma 2.8 termwise, on `B_ε`: the `k`-th derivative of the term with index `n` of (1.4) is
`dualDerivTerm w k n`, by Faà di Bruno's formula and (2.10). A local primitive of `f_i''/f_i'`
takes the place of `φ_i = log|f_i'|` in (2.8). -/
theorem iteratedDeriv_dualTerm k n (hz : z ∈ nbhd ε) :
    iteratedDeriv k (Φ.dualTerm w n) z = Φ.dualDerivTerm w k n z := by
  cases h : w.get? n with
  | none =>
    have hT := funext (Φ.dualTerm_of_get?_eq_none h)
    simp [hT, dualDerivTerm, h]
  | some i =>
    have hT : Φ.dualTerm w n = fun u => Φ.nonlin i (Φ.comp 𝔱 u) *
        𝔡ᶜ Φ 𝔱 u := funext (Φ.dualTerm_of_get?_eq_some h)
    obtain ⟨U, hUo, hU, hnl⟩ := Φ.exists_differentiableOn_nonlin i
    obtain ⟨r, hr, hrU⟩ :=
      Metric.isOpen_iff.1 hUo _ (hU (subset_closure (Φ.mapsTo_comp 𝔱 hz)))
    have hfa : AnalyticAt ℂ (Φ.comp 𝔱) z :=
      (Φ.differentiableOn_comp _).analyticAt (isOpen_nbhd.mem_nhds hz)
    -- each block contributes `f_v' · g_{|B|-1}(…)`, by (2.10)
    have hpart : ∀ m, 0 < m → iteratedDeriv m (Φ.comp 𝔱) z =
        𝔡ᶜ Φ 𝔱 z * MvPolynomial.aeval
          (fun ℓ => iteratedDeriv ℓ 𝕴 z) (gPoly (m - 1)) := by
      intro m hm
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
      exact Φ.iteratedDeriv_succ_comp_reverse _ m hz
    rw [hT, iteratedDeriv_comp_mul_deriv hr (hnl.mono hrU) hfa k]
    simp [dualDerivTerm, h]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.prod_congr rfl fun j _ => hpart _ (c.partSize_pos j), Finset.prod_mul_distrib,
      Fin.prod_const, mul_assoc]

/-- Lemma 2.8: for every finite or infinite word `w` and `k ≥ 0`, the series of
`dualDerivTerm` converges and sums to `H_w^{(k)}` on `[0,1]`. -/
theorem lemma_2_8 k (hx : x ∈ I) :
    Summable (fun n => Φ.dualDerivTerm w k n x) ∧
      iteratedDeriv k 𝕷 x = ∑' n, Φ.dualDerivTerm w k n x := by
  obtain ⟨C, -, hC⟩ := Φ.exists_dualTerm_bound
  have hx' := ofReal_mem_nbhd Φ.ε_pos hx
  have h := hasSum_iteratedDeriv_of_summable_norm
    ((summable_geometric_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_left C)
    (Φ.differentiableOn_dualTerm w) isOpen_nbhd
    (fun n z hz => hC w n z 𝕸) k hx'
  simp [Φ.iteratedDeriv_dualTerm w k _ hx'] at h
  exact ⟨h.summable, h.tsum_eq.symm⟩

end IFS

end AnalyticESC
