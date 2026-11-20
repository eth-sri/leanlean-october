module

import OAI.RpowArithmetic
public import Erdos408.OneSided.Bands
public import Erdos408.OneSided.Decomposition.Pair
public import Erdos408.OneSided.Moment.Edge.Adjoint
public import Erdos408.OneSided.Moment.Phased.Neighbor

/-!
# The crude edge bound

The ingredients of M4 for the edge (`exists_phasedEdge_normLe` in `Moment/Phased.lean`,
PD `mem:edge-crude`): every choice operator with the edge output and coefficients bounded by
those of `ℰ` has norm `L^{O(1)}` for the chain measure. This is the weighted Schur test with
weight `1`.

* `crudeKernel`: the kernel `ψ(t/Y) |[t = b - a] - ∫_𝔐 e(θ(t - b + a))|` at a determinant
  value, with `t = det/D`, and zero unless `D ∣ det`. `sum_crudeKernel_le` and
  `sum_crudeKernel_le'`: summed over the positions of the root box against a fixed position
  it is at most `16 (1 + 52 L^{3A₀})` (`mem:neighbor`, and `|∫_𝔐| ≤ 4 L^{3A₀}/Y` over
  `|t| ≤ 5Y`).
* `norm_chainEdgeCoef_le_crude`: the edge coefficient is at most `M!^{-2K} ∏_i w_i` times the
  kernel, where `w_i` is `S(x_i)/V(p_i)` for a promotion and `ν(p_i)` for a fresh prime
  (`rawWeight`).
* `sum_norm_chainEdgeCoef_le`: the row sums are at most `2^K (2B + 4)^K` times the kernel
  bound. The fresh labels carry `∑_{p ∈ 𝒫_i} ν(p) ≤ 4`, the promotions `∑_p S(p, ·)/V(p) ≤ 2B`.
* `crudeWeight_le_col`: the adjoint calculation. The chain measure carries `∏ ν(act)` and the
  memory weight, so `μ(s) ∏_i w_i ≤ μ(s') ∏_i (ν(b_i) or S'(b_i, ·)) (1 or 2)` for an
  admissible edge `s → s'` with unshared source primes `b_i`: a stored group trades `ν(b_i)` for
  the multiplicity in `S'`, and a promotion trades `S(x_i)` for `ν(a_i)`.
* `sum_col_chainEdgeCoef_le`: the column sums are at most `3^K (B + 4)^K` times the kernel
  bound times `μ(s')`. An admissible choice reaching `s'` is determined by the two
  symmetrizations, the stored groups, the promotion flags, the unshared source primes, and the
  source position.
* `exists_edgeChoiceOp_normLe`: eventually, for `B ≤ L³` and `N = 2R`, the norm is at most
  `L^{C_e}` uniformly in the root box.
-/

@[expose] public section

noncomputable section

namespace Erdos408.OneSided

open Filter Finset Real

variable {K : ℕ}

/-! ### The kernel -/

/-- The kernel term `ψ(t/Y) |[t = b - a] - ∫_𝔐 e(θ(t - b + a))|`. -/
def crudeTerm (A₀ x Y : ℝ) (b a : ℕ) (t : ℤ) : ℝ :=
  plateau (t / Y) * ‖(if t = (b : ℤ) - a then (1 : ℂ) else 0) - arcIntegral A₀ x Y (t - b + a)‖

/-- The kernel at the determinant value `n`: the kernel term at `t = n/D` if `D ∣ n`, and zero
otherwise. -/
def crudeKernel (A₀ x Y : ℝ) (D b a : ℕ) (n : ℤ) : ℝ :=
  if (D : ℤ) ∣ n then crudeTerm A₀ x Y b a (n / D) else 0

/-- The kernel term is nonnegative. -/
theorem crudeTerm_nonneg (A₀ x Y : ℝ) (b a : ℕ) (t : ℤ) : 0 ≤ crudeTerm A₀ x Y b a t :=
  mul_nonneg (smoothTransition.nonneg _) (norm_nonneg _)

/-- The kernel is nonnegative. -/
theorem crudeKernel_nonneg (A₀ x Y : ℝ) (D b a : ℕ) (n : ℤ) : 0 ≤ crudeKernel A₀ x Y D b a n := by
  unfold crudeKernel
  split_ifs
  exacts [crudeTerm_nonneg _ _ _ _ _ _, le_rfl]

/-- The kernel terms over `|t| ≤ ⌈5Y⌉` sum to at most `1 + 52 L^{3A₀}`: the raw term is one
value of `t`, and the arcs have measure at most `4 L^{3A₀}/Y` at each of the `≤ 13 Y` values. -/
theorem sum_crudeTerm_le (A₀ : ℝ) {x Y : ℝ} (hL : 0 < Real.log x) (hY : 1 ≤ Y) (b a : ℕ) :
    ∑ t ∈ Icc (-(⌈5 * Y⌉₊ : ℤ)) ⌈5 * Y⌉₊, crudeTerm A₀ x Y b a t ≤
      1 + 52 * Real.log x ^ (3 * A₀) := by
  set M := ⌈5 * Y⌉₊ with hM
  have hY0 : 0 < Y := by linarith
  -- each term is at most `[t = b - a] + 4 L^{3A₀}/Y`
  have hpt : ∀ t : ℤ, crudeTerm A₀ x Y b a t ≤
      (if t = (b : ℤ) - a then 1 else 0) + 4 * Real.log x ^ (3 * A₀) / Y := by
    intro t
    have hψ : plateau (t / Y) ≤ 1 := smoothTransition.le_one _
    have hn : ‖(if t = (b : ℤ) - a then (1 : ℂ) else 0) - arcIntegral A₀ x Y (t - b + a)‖ ≤
        (if t = (b : ℤ) - a then 1 else 0) + 4 * Real.log x ^ (3 * A₀) / Y := by
      refine (norm_sub_le _ _).trans (add_le_add (le_of_eq ?_) (norm_arcIntegral_le A₀ hL hY0 _))
      split_ifs <;> simp
    calc crudeTerm A₀ x Y b a t
        ≤ 1 * ‖(if t = (b : ℤ) - a then (1 : ℂ) else 0) - arcIntegral A₀ x Y (t - b + a)‖ :=
          mul_le_mul_of_nonneg_right hψ (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hn
  -- `2M + 1 ≤ 13 Y`
  have hcard : ((Icc (-(M : ℤ)) M).card : ℝ) ≤ 13 * Y := by
    have hM' : (M : ℝ) < 5 * Y + 1 := Nat.ceil_lt_add_one (by linarith)
    rw [Int.card_Icc, show (M : ℤ) + 1 - -(M : ℤ) = ((2 * M + 1 : ℕ) : ℤ) by push_cast; ring,
      Int.toNat_natCast]
    push_cast
    linarith
  calc ∑ t ∈ Icc (-(M : ℤ)) M, crudeTerm A₀ x Y b a t
      ≤ ∑ t ∈ Icc (-(M : ℤ)) M,
          ((if t = (b : ℤ) - a then 1 else 0) + 4 * Real.log x ^ (3 * A₀) / Y) :=
        sum_le_sum fun t _ => hpt t
    _ = (if (b : ℤ) - a ∈ Icc (-(M : ℤ)) M then 1 else 0) +
          ((Icc (-(M : ℤ)) M).card : ℝ) * (4 * Real.log x ^ (3 * A₀) / Y) := by
        rw [sum_add_distrib, sum_ite_eq', sum_const, nsmul_eq_mul]
    _ ≤ 1 + 13 * Y * (4 * Real.log x ^ (3 * A₀) / Y) := by
        gcongr
        split_ifs <;> norm_num
    _ = 1 + 52 * Real.log x ^ (3 * A₀) := by field_simp; ring

/-- A kernel term vanishes unless `|t| ≤ ⌈5Y⌉`. -/
theorem mem_Icc_of_crudeTerm_ne_zero {A₀ x Y : ℝ} (hY : 0 < Y) {b a : ℕ} {t : ℤ}
    (h : crudeTerm A₀ x Y b a t ≠ 0) : t ∈ Icc (-(⌈5 * Y⌉₊ : ℤ)) ⌈5 * Y⌉₊ := by
  have hψ : plateau (t / Y) ≠ 0 := fun h0 => h (by rw [crudeTerm, h0, zero_mul])
  have h5 := abs_lt_of_plateau_ne_zero hψ
  rw [abs_div, abs_of_pos hY, div_lt_iff₀ hY] at h5
  have hle  := h5.le.trans (Nat.le_ceil _)
  rw [abs_le] at hle
  exact mem_Icc.2 ⟨by exact_mod_cast hle.1, by exact_mod_cast hle.2⟩

section

variable (A₀ : ℝ) {x Y U V u v r : ℝ}

/-- **The kernel against a fixed first position**: summed over the positions `z` of the root
box, the kernel at `det(w, z)` is at most `16 (1 + 52 L^{3A₀})`. -/
theorem sum_crudeKernel_le (hL : 0 < Real.log x) (hY : 1 ≤ Y)
    (hU : 0 < U) {w : ℤ × ℤ} (hw : w ∈ rootPositions U V u v r) {D : ℕ} (hD : 0 < D)
    (b a : ℕ) :
    ∑ z : ↥(rootPositions U V u v r), crudeKernel A₀ x Y D b a (w.1 * z.1.2 - w.2 * z.1.1) ≤
      16 * (1 + 52 * Real.log x ^ (3 * A₀)) := by
  rw [sum_coe_sort (rootPositions U V u v r)
    (fun z => crudeKernel A₀ x Y D b a (w.1 * z.2 - w.2 * z.1))]
  refine (sum_dvd_le_of_card_le (card_filter_det_le hU hw) hD (crudeTerm_nonneg A₀ x Y b a)
    (fun t ht => mem_Icc_of_crudeTerm_ne_zero (by linarith) ht)).trans ?_
  exact mul_le_mul_of_nonneg_left (sum_crudeTerm_le A₀ hL hY b a) (by norm_num)

/-- **The kernel against a fixed second position**: summed over the positions `z` of the root
box, the kernel at `det(z, w)` is at most `16 (1 + 52 L^{3A₀})`. -/
theorem sum_crudeKernel_le' (hL : 0 < Real.log x) (hY : 1 ≤ Y)
    (hU : 0 < U) {w : ℤ × ℤ} (hw : w ∈ rootPositions U V u v r) {D : ℕ} (hD : 0 < D)
    (b a : ℕ) :
    ∑ z : ↥(rootPositions U V u v r), crudeKernel A₀ x Y D b a (z.1.1 * w.2 - z.1.2 * w.1) ≤
      16 * (1 + 52 * Real.log x ^ (3 * A₀)) := by
  rw [sum_coe_sort (rootPositions U V u v r)
    (fun z => crudeKernel A₀ x Y D b a (z.1 * w.2 - z.2 * w.1))]
  refine (sum_dvd_le_of_card_le (card_filter_det_le' hU hw) hD (crudeTerm_nonneg A₀ x Y b a)
    (fun t ht => mem_Icc_of_crudeTerm_ne_zero (by linarith) ht)).trans ?_
  exact mul_le_mul_of_nonneg_left (sum_crudeTerm_le A₀ hL hY b a) (by norm_num)

end

/-! ### Band facts -/

section Facts


end Facts

/-! ### The coefficient bound -/

section Coef

variable {q A₀ x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B N : ℕ}

/-- The weight product is nonnegative. -/
theorem crudeWeight_nonneg (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) :
    0 ≤ rawWeight q N s c :=
  prod_nonneg fun i _ => by
    split_ifs
    · exact div_nonneg (sum_nonneg fun xp _ => by split_ifs <;> positivity) (primeMass_nonneg _)
    · exact hν _

/-- `|η| ≤ 1`. -/
private theorem abs_dyadicBump_le (y : ℝ) : |dyadicBump y| ≤ 1 := by
  unfold dyadicBump
  have h₁ := smoothTransition.nonneg (y - 1)
  have h₂ := smoothTransition.le_one (y - 1)
  have h₃ := smoothTransition.nonneg (y / 2 - 1)
  have h₄ := smoothTransition.le_one (y / 2 - 1)
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- A product of a number at most one and a number in `[0, 1]` is at most one. -/
private theorem mul_le_one_of_le {a b : ℝ} (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
  (mul_le_mul_of_nonneg_right ha hb0).trans (by simpa using hb)

/-- **The coefficient bound**: `|ℰ(s, c)| ≤ M!^{-2K} ∏_i w_i κ`, where `κ` is the kernel at
`det(z, z')` with the pad product `D` and the label products `b, a`. The pending weights, the
ratio `d₀/D` and the bumps are at most one. -/
theorem norm_chainEdgeCoef_le_crude (hq : 0 < q) (hq₁ : q < 1) (hd₀ : 0 < d₀)
    (hν : ∀ p, 0 ≤ primeWeight q x d N p) (s : ChainState x d Y d₀ u v r B)
    (c : EdgeChoice x d Y d₀ u v r) :
    ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N s c‖ ≤
      (((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 * rawWeight q N s c *
        crudeKernel A₀ x Y (edgePad s c) (∏ i, edgeSrc s c i (Fin.last _))
          (∏ i, (c.2.2.2.1 i).1) (edgeDet s c) := by
  classical
  have hW := crudeWeight_nonneg hν s c
  have hρ0 : 0 ≤ pendingWeight q := (Real.rpow_pos_of_pos hq _).le
  have hρ1 : pendingWeight q ≤ 1 := Real.rpow_le_one hq.le hq₁.le (by norm_num)
  have hR : 0 ≤ (((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 *
      rawWeight q N s c *
        crudeKernel A₀ x Y (edgePad s c) (∏ i, edgeSrc s c i (Fin.last _))
          (∏ i, (c.2.2.2.1 i).1) (edgeDet s c) :=
    mul_nonneg (mul_nonneg (by positivity) hW) (crudeKernel_nonneg _ _ _ _ _ _ _)
  unfold chainEdgeCoef
  split_ifs with hv
  · obtain ⟨-, -, hD₀, -, hdvd, -⟩ := hv
    have hD  := hd₀.trans_le hD₀
    rw [crudeKernel, ite_eq_left hdvd, crudeTerm]
    unfold rawWeight at hW ⊢
    dsimp only
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    set r₀ := (((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 with hr₀
    set W := ∏ i, if (c.2.2.2.1 i).2 then
      (∑ xp : Particle x d, if xp.1 = edgePromoted c i then (s.2.2.1 xp : ℝ) else 0) /
        primeMass x d (c.2.2.2.1 i).1
      else primeWeight q x d N (c.2.2.2.1 i).1 with hWdef
    set ψ := plateau ((edgeDet s c / edgePad s c : ℤ) / Y) with hψ
    set k := ‖(if edgeDet s c / (edgePad s c : ℤ) = ((∏ i, edgeSrc s c i (Fin.last _) : ℕ) : ℤ) -
        ((∏ i, (c.2.2.2.1 i).1 : ℕ) : ℤ) then (1 : ℂ) else 0) -
      arcIntegral A₀ x Y (edgeDet s c / (edgePad s c : ℤ) -
        ((∏ i, edgeSrc s c i (Fin.last _) : ℕ) : ℤ) + ((∏ i, (c.2.2.2.1 i).1 : ℕ) : ℤ))‖ with hk
    have hr0 : 0 ≤ r₀ := by positivity
    have hψ0 : 0 ≤ ψ := smoothTransition.nonneg _
    have hdD0  := div_nonneg hd₀.le hD.le
    have hdD1  := (div_le_one hD).2 hD₀
    simp only [abs_mul, abs_of_nonneg hr0, abs_of_nonneg hW, abs_of_nonneg hψ0,
      abs_of_nonneg hdD0, abs_of_nonneg (pow_nonneg hρ0 _)]
    have h1 : pendingWeight q ^ pendingHits x d s.1.1 s.2.2.1 *
        pendingWeight q ^ pendingHits x d c.2.2.1.1 (edgeMem s c) * (d₀ / (edgePad s c : ℝ)) *
          |dyadicBump ((∏ i, edgeSrc s c i (Fin.last _) : ℕ) / Y)| *
            |dyadicBump ((∏ i, (c.2.2.2.1 i).1 : ℕ) / Y)| ≤ 1 :=
      mul_le_one_of_le (mul_le_one_of_le (mul_le_one_of_le (mul_le_one_of_le
        (pow_le_one₀ hρ0 hρ1) (pow_nonneg hρ0 _) (pow_le_one₀ hρ0 hρ1)) hdD0 hdD1)
          (abs_nonneg _) (abs_dyadicBump_le _)) (abs_nonneg _) (abs_dyadicBump_le _)
    calc r₀ * pendingWeight q ^ pendingHits x d s.1.1 s.2.2.1 *
          pendingWeight q ^ pendingHits x d c.2.2.1.1 (edgeMem s c) * W *
            (d₀ / (edgePad s c : ℝ)) *
            |dyadicBump ((∏ i, edgeSrc s c i (Fin.last _) : ℕ) / Y)| *
            |dyadicBump ((∏ i, (c.2.2.2.1 i).1 : ℕ) / Y)| * ψ * k
        = r₀ * W * (ψ * k) * (pendingWeight q ^ pendingHits x d s.1.1 s.2.2.1 *
            pendingWeight q ^ pendingHits x d c.2.2.1.1 (edgeMem s c) *
              (d₀ / (edgePad s c : ℝ)) *
              |dyadicBump ((∏ i, edgeSrc s c i (Fin.last _) : ℕ) / Y)| *
              |dyadicBump ((∏ i, (c.2.2.2.1 i).1 : ℕ) / Y)|) := by ring
      _ ≤ r₀ * W * (ψ * k) * 1 :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg (mul_nonneg hr0 hW)
            (mul_nonneg hψ0 (norm_nonneg _)))
      _ = r₀ * W * (ψ * k) := mul_one _
  · rw [norm_zero]
    exact hR

end Coef

/-! ### The row sums -/

section Row

variable {q A₀ x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B N : ℕ}

variable (x d) in
/-- The multiplicity `S(p, ·) = ∑_ℓ S(p, ℓ)` of the prime `p` in the memory `S`. -/
def primeMult (S : Particle x d → ℕ) (p : ℕ) : ℝ :=
  ∑ xp : Particle x d, if xp.1.1 = p then (S xp : ℝ) else 0

/-- The multiplicity of a prime is nonnegative. -/
theorem primeMult_nonneg (S : Particle x d → ℕ) (p : ℕ) : 0 ≤ primeMult x d S p :=
  sum_nonneg fun xp _ => by split_ifs <;> positivity

/-- The multiplicities of distinct primes sum to at most the size of the memory. -/
theorem sum_primeMult_le (S : Particle x d → ℕ) (T : Finset ℕ) :
    ∑ p ∈ T, primeMult x d S p ≤ memSize S := by
  classical
  unfold primeMult memSize
  rw [sum_comm, Nat.cast_sum]
  refine sum_le_sum fun xp _ => ?_
  rw [sum_ite_eq]
  split_ifs
  exacts [le_rfl, by positivity]

/-- An envelope for one fresh or promoted edge label. -/
def edgeLabelWeight (q x : ℝ) (d : Data K) (N : ℕ) (S : Particle x d → ℕ)
    (pf : ℕ × Bool) : ℝ :=
  if pf.2 then 2 * primeMult x d S pf.1 else primeWeight q x d N pf.1

theorem sum_edgeLabelWeight_le (s : ChainState x d Y d₀ u v r B) (i : Fin K)
    (hνi : ∑ p ∈ band x (d.a i), primeWeight q x d N p ≤ 4) :
    ∑ pf ∈ band x (d.a i) ×ˢ (univ : Finset Bool), edgeLabelWeight q x d N s.2.2.1 pf ≤ 2*B+4 := by
  rw [sum_product]
  simp only [Fintype.sum_bool, edgeLabelWeight, ite_true, Bool.false_eq_true, ite_false, sum_add_distrib, ← mul_sum]
  have h₁ := sum_primeMult_le s.2.2.1 (band x (d.a i))
  have h₂ : (memSize s.2.2.1 : ℝ) ≤ B := by exact_mod_cast mem_memStates.1 s.2.2.2
  linarith

/-- The target kernel bound is independent of the label weights. -/
theorem sum_norm_chainEdgeCoef_weighted_le (hq : 0 < q) (hq₁ : q < 1) (hd₀ : 0 < d₀) (hY : 1 ≤ Y)
    (hU : 0 < d₀ * Y * d.Hm) (hL : 0 < Real.log x) (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    (hV : ∀ i, ∀ p ∈ band x (d.a i), 1 / 2 ≤ primeMass x d p)
    (s : ChainState x d Y d₀ u v r B) (f : Fin K → ℕ × Bool → ℝ) (budget : Fin K → ℝ)
    (hf : ∀ i pf, 0 ≤ f i pf)
    (hlab : ∀ i, ∑ pf ∈ band x (d.a i) ×ˢ (univ : Finset Bool),
      edgeLabelWeight q x d N s.2.2.1 pf * f i pf ≤ (2*B+4)*budget i) :
    ∑ c ∈ edgeChoices x d Y d₀ u v r, ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N s c‖ *
        (∏ i, f i (c.2.2.2.1 i)) ≤
      2 ^ K * (2*B+4)^K * (16 * (1 + 52 * Real.log x ^ (3 * A₀))) * ∏ i, budget i := by
  classical
  set M := padCount x with hM
  set r₀ := (((M + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 with hr₀
  set Kz := 16 * (1 + 52 * Real.log x ^ (3 * A₀)) with hKz
  let ω := edgeLabelWeight q x d N s.2.2.1
  set Dσ : (Fin K → Equiv.Perm (Fin (M + 1))) → ℕ :=
    fun σ => ∏ i, ∏ h : Fin M, s.2.1.1 i (σ i h.castSucc) with hDσ
  set bσ : (Fin K → Equiv.Perm (Fin (M + 1))) → ℕ :=
    fun σ => ∏ i, s.2.1.1 i (σ i (Fin.last M)) with hbσ
  let G : (Fin K → Equiv.Perm (Fin (M + 1))) → ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) →
      (Fin K → ℕ × Bool) → ℝ := fun σ z' lab =>
    r₀ * (∏ i, ω (lab i)) * crudeKernel A₀ x Y (Dσ σ) (bσ σ) (∏ i, (lab i).1)
      (s.1.1.1 * z'.1.2 - s.1.1.2 * z'.1.1)
  let F : (Fin K → Equiv.Perm (Fin (M + 1))) → ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) →
      (Fin K → ℕ × Bool) → ℝ := fun σ z lab => r₀ * (∏ i, ω (lab i) * f i (lab i)) *
    crudeKernel A₀ x Y (Dσ σ) (bσ σ) (∏ i, (lab i).1) (s.1.1.1 * z.1.2 - s.1.1.2 * z.1.1)
  have hr0 : 0 ≤ r₀ := by positivity
  have hω0 : ∀ pf, 0 ≤ ω pf := fun pf => by
    simp only [ω, edgeLabelWeight]
    split_ifs
    exacts [mul_nonneg (by norm_num) (primeMult_nonneg _ _), hν _]
  have hD0 : ∀ σ, 0 < Dσ σ := fun σ =>
    prod_pos fun i _ => prod_pos fun h _ =>
      (TypeII.band_prime (mem_band_of_mem_lists s.2.1.2 i _)).pos
  -- the pointwise bound
  have hpt0 : ∀ c ∈ edgeChoices x d Y d₀ u v r,
      ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N s c‖ ≤ G c.1 c.2.2.1 c.2.2.2.1 := by
    intro c hc
    refine (norm_chainEdgeCoef_le_crude hq hq₁ hd₀ hν s c).trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hr0)
      (crudeKernel_nonneg _ _ _ _ _ _ _)
    refine prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
    · split_ifs
      · exact div_nonneg (sum_nonneg fun xp _ => by split_ifs <;> positivity)
          (primeMass_nonneg _)
      · exact hν _
    · have hVi := hV i _ (mem_band_lab hc i)
      simp only [ω, edgeLabelWeight]
      split_ifs with hf
      · have hnum : (∑ xp : Particle x d,
            if xp.1 = edgePromoted c i then (s.2.2.1 xp : ℝ) else 0) ≤
              primeMult x d s.2.2.1 (c.2.2.2.1 i).1 := by
          refine sum_le_sum fun xp _ => ?_
          split_ifs with h₁ h₂ h₂
          · exact le_rfl
          · exact absurd (congrArg Prod.fst h₁) h₂
          · positivity
          rfl
        rw [div_le_iff₀ (by linarith)]
        have hm := primeMult_nonneg s.2.2.1 (c.2.2.2.1 i).1
        calc (∑ xp : Particle x d, if xp.1 = edgePromoted c i then (s.2.2.1 xp : ℝ) else 0)
            ≤ primeMult x d s.2.2.1 (c.2.2.2.1 i).1 * 1 := by rw [mul_one]; exact hnum
          _ ≤ primeMult x d s.2.2.1 (c.2.2.2.1 i).1 * (2 * primeMass x d (c.2.2.2.1 i).1) :=
              mul_le_mul_of_nonneg_left (by linarith) hm
          _ = 2 * primeMult x d s.2.2.1 (c.2.2.2.1 i).1 * primeMass x d (c.2.2.2.1 i).1 := by
              ring
      rfl
  have hpt (c : EdgeChoice x d Y d₀ u v r) (hc : c∈edgeChoices x d Y d₀ u v r) :
      ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N s c‖ * (∏ i, f i (c.2.2.2.1 i)) ≤ F c.1 c.2.2.1 c.2.2.2.1 := by
    refine (mul_le_mul_of_nonneg_right (hpt0 c hc) (prod_nonneg fun i _ => hf i _)).trans_eq ?_
    dsimp only [F, G]
    rw [prod_mul_distrib]
    ring
  -- the inner sum over the target, the labels and `σ'`
  have hinner : ∀ σ, ∑ z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r),
      ∑ lab ∈ Fintype.piFinset (fun i => band x (d.a i) ×ˢ (univ : Finset Bool)),
        ∑ _σ' : Fin K → Equiv.Perm (Fin (M + 1)), F σ z' lab ≤
          (((M + 1).factorial ^ K : ℕ) : ℝ) * (r₀ * ((2 * B + 4) ^ K * Kz * ∏ i, budget i)) := by
    intro σ
    have hcard : (Fintype.card (Fin K → Equiv.Perm (Fin (M + 1))) : ℝ) =
        (((M + 1).factorial ^ K : ℕ) : ℝ) := by
      simp [Fintype.card_perm]
    simp only [sum_const, card_univ, nsmul_eq_mul, hcard]
    rw [sum_comm]
    simp only [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ∑ lab ∈ Fintype.piFinset (fun i => band x (d.a i) ×ˢ (univ : Finset Bool)),
          ∑ z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r), F σ z' lab
        ≤ ∑ lab ∈ Fintype.piFinset (fun i => band x (d.a i) ×ˢ (univ : Finset Bool)),
            r₀ * (∏ i, ω (lab i) * f i (lab i)) * Kz := by
          refine sum_le_sum fun lab _ => ?_
          simp only [F, ← mul_sum]
          exact mul_le_mul_of_nonneg_left
            (sum_crudeKernel_le A₀ hL hY hU s.1.2 (hD0 σ) _ _)
            (mul_nonneg hr0 (prod_nonneg fun i _ => mul_nonneg (hω0 _) (hf i _)))
      _ = r₀ * Kz * ∏ i, ∑ pf ∈ band x (d.a i) ×ˢ (univ : Finset Bool), ω pf * f i pf := by
          rw [prod_univ_sum, mul_sum]
          exact sum_congr rfl fun lab _ => by ring
      _ ≤ r₀ * Kz * ∏ i : Fin K, (2 * (B : ℝ) + 4) * budget i :=
          mul_le_mul_of_nonneg_left (prod_le_prod₀ (fun i _ => sum_nonneg fun pf _ => mul_nonneg (hω0 pf) (hf i pf))
            fun i _ => hlab i) (mul_nonneg hr0 (by positivity))
      _ = r₀ * ((2 * B + 4) ^ K * Kz * ∏ i, budget i) := by
          rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
          ring
  calc ∑ c ∈ edgeChoices x d Y d₀ u v r, ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N s c‖ * (∏ i, f i (c.2.2.2.1 i))
      ≤ ∑ c ∈ edgeChoices x d Y d₀ u v r, F c.1 c.2.2.1 c.2.2.2.1 := sum_le_sum hpt
    _ = ∑ σ : Fin K → Equiv.Perm (Fin (M + 1)), ∑ _st : Finset (Fin K),
          ∑ z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r),
            ∑ lab ∈ Fintype.piFinset (fun i => band x (d.a i) ×ˢ (univ : Finset Bool)),
              ∑ _σ' : Fin K → Equiv.Perm (Fin (M + 1)), F σ z' lab := by
        simp only [edgeChoices, sum_product]
        rfl
    _ ≤ ∑ _σ : Fin K → Equiv.Perm (Fin (M + 1)), ∑ _st : Finset (Fin K),
          (((M + 1).factorial ^ K : ℕ) : ℝ) * (r₀ * ((2 * B + 4) ^ K * Kz * ∏ i, budget i)) :=
        sum_le_sum fun σ _ => sum_le_sum fun _ _ => hinner σ
    _ = 2 ^ K * (2 * B + 4) ^ K * Kz * ∏ i, budget i := by
        have hf : (((M + 1).factorial ^ K : ℕ) : ℝ) ≠ 0 := by positivity
        simp only [sum_const, card_univ, nsmul_eq_mul, Fintype.card_finset, Fintype.card_fin,
          hr₀]
        rw [show (Fintype.card (Fin K → Equiv.Perm (Fin (M + 1))) : ℝ) =
          (((M + 1).factorial ^ K : ℕ) : ℝ) by simp [Fintype.card_perm]]
        field_simp
        push_cast
        ring

/-- **The row bound**: for a fixed source, the absolute edge coefficients sum to at most
`2^K (2B + 4)^K · 16 (1 + 52 L^{3A₀})`. The symmetrizations cancel `M!^{-2K}`, the stored
groups give `2^K`, each group's label gives `∑_p (2 S(p, ·) + ν(p)) ≤ 2B + 4`, and the targets
give the kernel bound. -/
theorem sum_norm_chainEdgeCoef_le (hq : 0 < q) (hq₁ : q < 1) (hd₀ : 0 < d₀) (hY : 1 ≤ Y)
    (hU : 0 < d₀ * Y * d.Hm) (hL : 0 < Real.log x) (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    (hνi : ∀ i, ∑ p ∈ band x (d.a i), primeWeight q x d N p ≤ 4)
    (hV : ∀ i, ∀ p ∈ band x (d.a i), 1 / 2 ≤ primeMass x d p) (s : ChainState x d Y d₀ u v r B) :
    ∑ c ∈ edgeChoices x d Y d₀ u v r, ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N s c‖ ≤
      2 ^ K * (2 * B + 4) ^ K * (16 * (1 + 52 * Real.log x ^ (3 * A₀))) := by
  simpa using sum_norm_chainEdgeCoef_weighted_le hq hq₁ hd₀ hY hU hL hν hV s (fun _ _ => 1) (fun _ => 1)
    (fun _ _ => zero_le_one) (fun i => by simpa using sum_edgeLabelWeight_le s i (hνi i))

end Row

/-! ### The column sums -/

section Col

variable {q A₀ x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B N : ℕ}

variable (q x d N) in
/-- The factor of a group in the column bound: the multiplicity `S'(b, ·)` of the unshared
source prime `b` for a stored group and `ν(b)` otherwise, times `2` for a promotion. -/
def colFactor (S' : Particle x d → ℕ) (st f : Bool) (b : ℕ) : ℝ :=
  (if st then primeMult x d S' b else primeWeight q x d N b) * (if f then 2 else 1)

/-- **The adjoint calculation** (PD `mem:edge-crude`): for an admissible edge `s → s'`,
`μ(s) ∏_i w_i ≤ μ(s') ∏_i (S'(b_i, ·) or ν(b_i)) (2 or 1)`. Removing a promoted particle `x_i`
from `S` trades its weight `S(x_i)` for `ν(a_i)`, which cancels the target label, and leaves
`1/V(a_i) ≤ 2`; storing `b_i` trades the source label `ν(b_i)` for the multiplicity in `S'`. -/
theorem crudeWeight_le_col
    (hdisj : d.BandsDisjoint x)
    (hV : ∀ i, ∀ p ∈ band x (d.a i), 1 / 2 ≤ primeMass x d p)
    (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    (hνpos : ∀ i, ∀ p ∈ band x (d.a i), 0 < primeWeight q x d N p)
    {s : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (hc : c ∈ edgeChoices x d Y d₀ u v r) (hv : EdgeValid x d Y d₀ u v r B s c) :
    (∏ i, ∏ h, primeWeight q x d N (s.2.1.1 i h)) *
        memWeight (fun xp : Particle x d => primeWeight q x d N xp.1.1) s.2.2.1 *
        rawWeight q N s c ≤
      (∏ i, ∏ h, primeWeight q x d N (edgeTgt s c i h)) *
        memWeight (fun xp : Particle x d => primeWeight q x d N xp.1.1) (edgeMem s c) *
        ∏ i, colFactor q x d N (edgeMem s c) (decide (i ∈ c.2.1)) (c.2.2.2.1 i).2
          (edgeSrc s c i (Fin.last _)) := by
  classical
  rw [edge_weight_transport hdisj hνpos hc hv]
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (prod_nonneg fun _ _ => prod_nonneg fun _ _ => hν _)
      (memWeight_nonneg (fun _ => hν _) _))
  refine prod_le_prod₀ (fun i _ => ?_) fun i _ => ?_
  · unfold reverseLabelWeight
    exact mul_nonneg (by split_ifs <;> first | positivity | apply hν)
      (by split_ifs; exacts [inv_nonneg.2 (primeMass_nonneg _), zero_le_one])
  · simp only [reverseLabelWeight, colFactor, decide_eq_true_eq]
    apply mul_le_mul
    · split_ifs with hi
      · rw [memAt_eq, dite_eq_left (hv.2.2.2.2.2.2.2.2.1 i hi)]
        unfold primeMult
        have hh := single_le_sum (f := fun xp : Particle x d =>
          if xp.1.1 = edgeSrc s c i (Fin.last _) then (edgeMem s c xp : ℝ) else 0)
          (fun _ _ => by split_ifs <;> positivity)
          (mem_univ (⟨_, hv.2.2.2.2.2.2.2.2.1 i hi⟩ : Particle x d))
        simpa [edgeStored] using hh
      · rfl
    · split_ifs
      · exact promotionFactor_le_two (hV i _ (mem_band_lab hc i))
      · rfl
    · split_ifs; exacts [inv_nonneg.2 (primeMass_nonneg _), zero_le_one]
    · split_ifs; exacts [primeMult_nonneg _ _, hν _]

open scoped Classical in
/-- **The column bound**: for a fixed output `s'`, the measure-weighted absolute edge
coefficients reaching `s'` sum to at most `3^K (B + 4)^K · 16 (1 + 52 L^{3A₀}) · μ(s')`. An
admissible choice reaching `s'` is determined by `σ`, `σ'`, the stored groups, the promotion
flags, the unshared source primes `b_i` and the source position `z`; the adjoint calculation
bounds its term by `μ(s') M!^{-2K} ∏_i (S'(b_i, ·) or ν(b_i)) (2 or 1)` times the kernel, and the
sources are counted by the kernel bound. -/
theorem sum_col_chainEdgeCoef_le (hq : 0 < q) (hq₁ : q < 1) (hd₀ : 0 < d₀) (hY : 1 ≤ Y)
    (hU : 0 < d₀ * Y * d.Hm) (hL : 0 < Real.log x)
    (hdisj : d.BandsDisjoint x)
    (hV : ∀ i, ∀ p ∈ band x (d.a i), 1 / 2 ≤ primeMass x d p)
    (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    (hνpos : ∀ i, ∀ p ∈ band x (d.a i), 0 < primeWeight q x d N p)
    (hνi : ∀ i, ∑ p ∈ band x (d.a i), primeWeight q x d N p ≤ 4)
    (s' : ChainState x d Y d₀ u v r B) :
    ∑ s, ∑ c ∈ edgeChoices x d Y d₀ u v r with chainEdgeOut x d Y d₀ u v r B s c = s',
        chainMeasure q x d Y d₀ u v r B N s * ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N s c‖ ≤
      3 ^ K * (B + 4) ^ K * (16 * (1 + 52 * Real.log x ^ (3 * A₀))) *
        chainMeasure q x d Y d₀ u v r B N s' := by
  classical
  set r₀ := (((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 with hr₀
  set Kz := 16 * (1 + 52 * Real.log x ^ (3 * A₀)) with hKz
  have hr0 : 0 ≤ r₀ := by positivity
  have hμ0 : ∀ s : ChainState x d Y d₀ u v r B, 0 ≤ chainMeasure q x d Y d₀ u v r B N s :=
    fun s => mul_nonneg (prod_nonneg fun i _ => prod_nonneg fun h _ => hν _)
      (memWeight_nonneg (fun xp => hν _) _)
  -- the parameters: `σ`, `σ'`, (stored, promoted, `b_i`) per group, and the source position
  let Dp : (Fin K → Equiv.Perm (Fin (padCount x + 1))) → ℕ :=
    fun σ' => ∏ i, ∏ h : Fin (padCount x), s'.2.1.1 i ((σ' i).symm h.castSucc)
  let ap : (Fin K → Equiv.Perm (Fin (padCount x + 1))) → ℕ :=
    fun σ' => ∏ i, s'.2.1.1 i ((σ' i).symm (Fin.last _))
  let F : (Fin K → Equiv.Perm (Fin (padCount x + 1))) ×
      (Fin K → Equiv.Perm (Fin (padCount x + 1))) × (Fin K → Bool × Bool × ℕ) ×
        ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) → ℝ := fun y =>
    chainMeasure q x d Y d₀ u v r B N s' * r₀ *
      (∏ i, colFactor q x d N s'.2.2.1 (y.2.2.1 i).1 (y.2.2.1 i).2.1 (y.2.2.1 i).2.2) *
      crudeKernel A₀ x Y (Dp y.2.1) (∏ i, (y.2.2.1 i).2.2) (ap y.2.1)
        (y.2.2.2.1.1 * s'.1.1.2 - y.2.2.2.1.2 * s'.1.1.1)
  let φ : ChainState x d Y d₀ u v r B × EdgeChoice x d Y d₀ u v r →
      (Fin K → Equiv.Perm (Fin (padCount x + 1))) ×
        (Fin K → Equiv.Perm (Fin (padCount x + 1))) × (Fin K → Bool × Bool × ℕ) ×
          ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) := fun p =>
    (p.2.1, p.2.2.2.2.2, fun i => (decide (i ∈ p.2.2.1), (p.2.2.2.2.1 i).2,
      edgeSrc p.1 p.2 i (Fin.last _)), p.1.1)
  let A := ((univ ×ˢ edgeChoices x d Y d₀ u v r).filter fun p =>
      chainEdgeOut x d Y d₀ u v r B p.1 p.2 = s').filter fun p =>
    EdgeValid x d Y d₀ u v r B p.1 p.2
  let Params := (univ : Finset (Fin K → Equiv.Perm (Fin (padCount x + 1)))) ×ˢ
    (univ : Finset (Fin K → Equiv.Perm (Fin (padCount x + 1)))) ×ˢ
      Fintype.piFinset (fun i => (univ : Finset Bool) ×ˢ (univ : Finset Bool) ×ˢ
        band x (d.a i)) ×ˢ (univ : Finset ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r))
  have hcolF0 : ∀ st f b, 0 ≤ colFactor q x d N s'.2.2.1 st f b := fun st f b =>
    mul_nonneg (by split_ifs; exacts [primeMult_nonneg _ _, hν _]) (by split_ifs <;> norm_num)
  have hF0 : ∀ y, 0 ≤ F y := fun y =>
    mul_nonneg (mul_nonneg (mul_nonneg (hμ0 s') hr0) (prod_nonneg fun i _ => hcolF0 _ _ _))
      (crudeKernel_nonneg _ _ _ _ _ _ _)
  -- an admissible choice reaching `s'`
  have hfacts : ∀ p ∈ A, p.2 ∈ edgeChoices x d Y d₀ u v r ∧ EdgeValid x d Y d₀ u v r B p.1 p.2 ∧
      s'.1 = p.2.2.2.1 ∧ s'.2.1.1 = edgeTgt p.1 p.2 ∧ s'.2.2.1 = edgeMem p.1 p.2 := by
    intro p hp
    simp only [A, mem_filter, mem_product, mem_univ, true_and] at hp
    obtain ⟨⟨hc, hout⟩, hv⟩ := hp
    have he := hout.symm.trans (chainEdgeOut_of_valid hv)
    exact ⟨hc, hv, congrArg (fun t => t.1) he, congrArg (fun t => t.2.1.1) he,
      congrArg (fun t => t.2.2.1) he⟩
  -- the parameters determine the choice
  have hinj : Set.InjOn φ A := by
    rintro ⟨s₁, c₁⟩ hp₁ ⟨s₂, c₂⟩ hp₂ h
    obtain ⟨hc₁, hv₁, hz₁, htgt₁, hmem₁⟩ : c₁ ∈ edgeChoices x d Y d₀ u v r ∧
        EdgeValid x d Y d₀ u v r B s₁ c₁ ∧ s'.1 = c₁.2.2.1 ∧ s'.2.1.1 = edgeTgt s₁ c₁ ∧
          s'.2.2.1 = edgeMem s₁ c₁ := hfacts _ hp₁
    obtain ⟨-, hv₂, hz₂, htgt₂, hmem₂⟩ : c₂ ∈ edgeChoices x d Y d₀ u v r ∧
        EdgeValid x d Y d₀ u v r B s₂ c₂ ∧ s'.1 = c₂.2.2.1 ∧ s'.2.1.1 = edgeTgt s₂ c₂ ∧
          s'.2.2.1 = edgeMem s₂ c₂ := hfacts _ hp₂
    simp only [φ, Prod.mk.injEq] at h
    obtain ⟨hσ, hσ', htr, hz⟩ := h
    have htr' := fun i => congrFun htr i
    simp only [Prod.mk.injEq] at htr'
    have hst  := Finset.ext fun i => by simpa using (htr' i).1
    have hb  :=
      fun i => (htr' i).2.2
    have htgt  := htgt₁.symm.trans htgt₂
    have hlab  := funext fun i => Prod.ext
      (by rw [label_eq_tgt s₁ c₁, label_eq_tgt s₂ c₂, htgt, hσ']) (htr' i).2.1
    have hc  :=
      Prod.ext hσ (Prod.ext hst (Prod.ext (hz₁.symm.trans hz₂) (Prod.ext hlab hσ')))
    subst hc
    -- the source lists: the pads are target labels and the last slots are the `b_i`
    have hact : s₁.2.1.1 = s₂.2.1.1 := by
      funext i h
      have key : ∀ s : ChainState x d Y d₀ u v r B,
          s.2.1.1 i h = edgeSrc s c₁ i ((c₁.1 i).symm h) := fun s => by
        simp only [edgeSrc, Equiv.apply_symm_apply]
      rw [key s₁, key s₂]
      by_cases hl : (c₁.1 i).symm h = Fin.last _
      · rw [hl]
        exact hb i
      · rw [edgeSrc_eq_tgt s₁ c₁ i hl, edgeSrc_eq_tgt s₂ c₁ i hl, htgt]
    -- the memories: the same particles are promoted and stored
    have hS : ∀ xp, s₁.2.2.1 xp = s₂.2.2.1 xp := by
      intro xp
      have h₁ := congrFun (hmem₁.symm.trans hmem₂) xp
      have hQ : (c₁.2.1.filter fun i => edgeStored s₁ c₁ i = xp.1) =
          (c₁.2.1.filter fun i => edgeStored s₂ c₁ i = xp.1) :=
        filter_congr fun i _ => by simp only [edgeStored, hb i, hz]
      simp only [edgeMem, hQ] at h₁
      have hP₁ := card_promoted_le hdisj hc₁ hv₁ xp
      have hP₂ := card_promoted_le hdisj hc₁ hv₂ xp
      omega
    exact Prod.ext (Prod.ext hz (Prod.ext (Subtype.ext hact) (Subtype.ext (funext hS)))) rfl
  -- the pointwise bound
  have hpt : ∀ p ∈ A, chainMeasure q x d Y d₀ u v r B N p.1 *
      ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N p.1 p.2‖ ≤ F (φ p) := by
    rintro ⟨s, c⟩ hp
    obtain ⟨hc, hv, hz, htgt, hmem⟩ : c ∈ edgeChoices x d Y d₀ u v r ∧
        EdgeValid x d Y d₀ u v r B s c ∧ s'.1 = c.2.2.1 ∧ s'.2.1.1 = edgeTgt s c ∧
          s'.2.2.1 = edgeMem s c := hfacts _ hp
    have hD : edgePad s c = Dp c.2.2.2.2 := by
      rw [edgePad_eq_tgt]
      simp only [Dp, htgt]
    have ha : ∏ i, (c.2.2.2.1 i).1 = ap c.2.2.2.2 := by
      simp only [ap, htgt]
      exact prod_congr rfl fun i _ => label_eq_tgt s c i
    have hdet : edgeDet s c = s.1.1.1 * s'.1.1.2 - s.1.1.2 * s'.1.1.1 := by
      rw [hz]
      rfl
    have hμ' : chainMeasure q x d Y d₀ u v r B N s' =
        (∏ i, ∏ h, primeWeight q x d N (edgeTgt s c i h)) *
          memWeight (fun xp : Particle x d => primeWeight q x d N xp.1.1) (edgeMem s c) := by
      rw [chainMeasure, htgt, hmem]
    have hw := crudeWeight_le_col hdisj hV hν hνpos hc hv
    rw [← hμ', ← hmem] at hw
    calc chainMeasure q x d Y d₀ u v r B N s * ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N s c‖
        ≤ chainMeasure q x d Y d₀ u v r B N s *
            (r₀ * rawWeight q N s c *
              crudeKernel A₀ x Y (edgePad s c) (∏ i, edgeSrc s c i (Fin.last _))
                (∏ i, (c.2.2.2.1 i).1) (edgeDet s c)) :=
          mul_le_mul_of_nonneg_left (norm_chainEdgeCoef_le_crude hq hq₁ hd₀ hν s c) (hμ0 s)
      _ = r₀ * (chainMeasure q x d Y d₀ u v r B N s * rawWeight q N s c) *
            crudeKernel A₀ x Y (Dp c.2.2.2.2) (∏ i, edgeSrc s c i (Fin.last _))
              (ap c.2.2.2.2) (s.1.1.1 * s'.1.1.2 - s.1.1.2 * s'.1.1.1) := by
          rw [hD, ha, hdet]
          ring
      _ ≤ r₀ * (chainMeasure q x d Y d₀ u v r B N s' *
            ∏ i, colFactor q x d N s'.2.2.1 (decide (i ∈ c.2.1)) (c.2.2.2.1 i).2
              (edgeSrc s c i (Fin.last _))) *
            crudeKernel A₀ x Y (Dp c.2.2.2.2) (∏ i, edgeSrc s c i (Fin.last _))
              (ap c.2.2.2.2) (s.1.1.1 * s'.1.1.2 - s.1.1.2 * s'.1.1.1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw hr0)
            (crudeKernel_nonneg _ _ _ _ _ _ _)
      _ = F (φ (s, c)) := by
          simp only [F, φ]
          ring
  -- the image of the parameters
  have himage : A.image φ ⊆ Params := by
    intro y hy
    obtain ⟨⟨s, c⟩, -, rfl⟩ := mem_image.1 hy
    simp only [Params, φ, mem_product, mem_univ, true_and, and_true, Fintype.mem_piFinset]
    exact fun i => mem_band_edgeSrc s c i (Fin.last _)
  -- the sum over the parameters
  have hDp : ∀ σ', 0 < Dp σ' := fun σ' =>
    prod_pos fun i _ => prod_pos fun h _ =>
      (TypeII.band_prime (mem_band_of_mem_lists s'.2.1.2 i _)).pos
  have hgroup : ∀ i, ∑ t ∈ (univ : Finset Bool) ×ˢ (univ : Finset Bool) ×ˢ band x (d.a i),
      colFactor q x d N s'.2.2.1 t.1 t.2.1 t.2.2 ≤ 3 * (B + 4) := by
    intro i
    have h₁ := sum_primeMult_le s'.2.2.1 (band x (d.a i))
    have h₂ : (memSize s'.2.2.1 : ℝ) ≤ B := by exact_mod_cast mem_memStates.1 s'.2.2.2
    have h₃ := hνi i
    rw [sum_product, Fintype.sum_bool, sum_product, sum_product, Fintype.sum_bool,
      Fintype.sum_bool]
    simp only [colFactor, ↓reduceIte, Bool.false_eq_true, ← sum_mul]
    linarith
  have hparams : ∑ y ∈ Params, F y ≤
      3 ^ K * (B + 4) ^ K * Kz * chainMeasure q x d Y d₀ u v r B N s' := by
    have hinner : ∀ σ σ', ∑ tr ∈ Fintype.piFinset (fun i => (univ : Finset Bool) ×ˢ
        (univ : Finset Bool) ×ˢ band x (d.a i)),
        ∑ z : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r), F (σ, σ', tr, z) ≤
          chainMeasure q x d Y d₀ u v r B N s' * r₀ * (Kz * (3 * (B + 4)) ^ K) := by
      intro σ σ'
      calc ∑ tr ∈ Fintype.piFinset (fun i => (univ : Finset Bool) ×ˢ
            (univ : Finset Bool) ×ˢ band x (d.a i)),
            ∑ z : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r), F (σ, σ', tr, z)
          ≤ ∑ tr ∈ Fintype.piFinset (fun i => (univ : Finset Bool) ×ˢ
              (univ : Finset Bool) ×ˢ band x (d.a i)),
              chainMeasure q x d Y d₀ u v r B N s' * r₀ *
                (∏ i, colFactor q x d N s'.2.2.1 (tr i).1 (tr i).2.1 (tr i).2.2) * Kz := by
            refine sum_le_sum fun tr _ => ?_
            simp only [F, ← mul_sum]
            exact mul_le_mul_of_nonneg_left (sum_crudeKernel_le' A₀ hL hY hU s'.1.2 (hDp σ') _ _)
              (mul_nonneg (mul_nonneg (hμ0 s') hr0) (prod_nonneg fun i _ => hcolF0 _ _ _))
        _ = chainMeasure q x d Y d₀ u v r B N s' * r₀ * Kz *
              ∏ i, ∑ t ∈ (univ : Finset Bool) ×ˢ (univ : Finset Bool) ×ˢ band x (d.a i),
                colFactor q x d N s'.2.2.1 t.1 t.2.1 t.2.2 := by
            rw [prod_univ_sum, mul_sum]
            exact sum_congr rfl fun tr _ => by ring
        _ ≤ chainMeasure q x d Y d₀ u v r B N s' * r₀ * Kz * ∏ _i : Fin K, (3 * ((B : ℝ) + 4)) :=
            mul_le_mul_of_nonneg_left (prod_le_prod₀ (fun i _ => sum_nonneg fun t _ =>
              hcolF0 _ _ _) fun i _ => hgroup i)
              (mul_nonneg (mul_nonneg (hμ0 s') hr0) (by positivity))
        _ = chainMeasure q x d Y d₀ u v r B N s' * r₀ * (Kz * (3 * (B + 4)) ^ K) := by
            rw [prod_const, card_univ, Fintype.card_fin]
            ring
    have hcard : (Fintype.card (Fin K → Equiv.Perm (Fin (padCount x + 1))) : ℝ) =
        (((padCount x + 1).factorial ^ K : ℕ) : ℝ) := by
      simp [Fintype.card_perm]
    have hf : (((padCount x + 1).factorial ^ K : ℕ) : ℝ) ≠ 0 := by positivity
    calc ∑ y ∈ Params, F y
        = ∑ σ : Fin K → Equiv.Perm (Fin (padCount x + 1)),
            ∑ σ' : Fin K → Equiv.Perm (Fin (padCount x + 1)),
              ∑ tr ∈ Fintype.piFinset (fun i => (univ : Finset Bool) ×ˢ
                (univ : Finset Bool) ×ˢ band x (d.a i)),
                ∑ z : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r), F (σ, σ', tr, z) := by
          simp only [Params, sum_product]
      _ ≤ ∑ _σ : Fin K → Equiv.Perm (Fin (padCount x + 1)),
            ∑ _σ' : Fin K → Equiv.Perm (Fin (padCount x + 1)),
              chainMeasure q x d Y d₀ u v r B N s' * r₀ * (Kz * (3 * (B + 4)) ^ K) :=
          sum_le_sum fun σ _ => sum_le_sum fun σ' _ => hinner σ σ'
      _ = 3 ^ K * (B + 4) ^ K * Kz * chainMeasure q x d Y d₀ u v r B N s' := by
          simp only [sum_const, card_univ, nsmul_eq_mul, hcard, hr₀, mul_pow]
          field_simp
  calc ∑ s, ∑ c ∈ edgeChoices x d Y d₀ u v r with chainEdgeOut x d Y d₀ u v r B s c = s',
        chainMeasure q x d Y d₀ u v r B N s * ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N s c‖
      = ∑ p ∈ A, chainMeasure q x d Y d₀ u v r B N p.1 *
          ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N p.1 p.2‖ := by
        have hne : ∀ p ∈ (univ ×ˢ edgeChoices x d Y d₀ u v r).filter
            (fun p => chainEdgeOut x d Y d₀ u v r B p.1 p.2 = s'),
            chainMeasure q x d Y d₀ u v r B N p.1 *
              ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N p.1 p.2‖ ≠ 0 →
            EdgeValid x d Y d₀ u v r B p.1 p.2 := by
          intro p _ h
          by_contra hnv
          apply h
          rw [chainEdgeCoef, ite_eq_right hnv, norm_zero, mul_zero]
        simp only [A]
        rw [sum_filter_of_ne hne, sum_filter, sum_product]
        simp only [sum_filter]
        congr! 3
    _ ≤ ∑ p ∈ A, F (φ p) := sum_le_sum hpt
    _ = ∑ y ∈ A.image φ, F y := (sum_image hinj).symm
    _ ≤ ∑ y ∈ Params, F y := sum_le_sum_of_subset_of_nonneg himage fun y _ _ => hF0 y
    _ ≤ _ := hparams

end Col

/-! ### The crude edge bound -/

section Assembly

variable {q A₀ x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B N : ℕ}

/-- **The crude edge bound on the chain states**: a choice operator with the edge output and
coefficients bounded by those of `ℰ` has norm at most `√(R C)` for the chain measure, with the
row bound `R = 2^K (2B + 4)^K κ₀` and the column bound `C = 3^K (B + 4)^K κ₀`, where
`κ₀ = 16 (1 + 52 L^{3A₀})` is the kernel bound. This is the weighted Schur test with weight
`1`. -/
theorem normLe_edgeChoiceOp (hq : 0 < q) (hq₁ : q < 1) (hd₀ : 0 < d₀) (hY : 1 ≤ Y)
    (hU : 0 < d₀ * Y * d.Hm) (hL : 0 < Real.log x)
    (hdisj : d.BandsDisjoint x)
    (hV : ∀ i, ∀ p ∈ band x (d.a i), 1 / 2 ≤ primeMass x d p)
    (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    (hνpos : ∀ i, ∀ p ∈ band x (d.a i), 0 < primeWeight q x d N p)
    (hνi : ∀ i, ∑ p ∈ band x (d.a i), primeWeight q x d N p ≤ 4)
    {a : ChainState x d Y d₀ u v r B → EdgeChoice x d Y d₀ u v r → ℂ}
    (ha : ∀ s c, ‖a s c‖ ≤ ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N s c‖) :
    NormLe (fun s => chainMeasure q x d Y d₀ u v r B N s)
      (fun s => chainMeasure q x d Y d₀ u v r B N s)
      (choiceOp (edgeChoices x d Y d₀ u v r) a (chainEdgeOut x d Y d₀ u v r B))
      (Real.sqrt ((2 ^ K * (2 * B + 4) ^ K * (16 * (1 + 52 * Real.log x ^ (3 * A₀)))) *
        (3 ^ K * (B + 4) ^ K * (16 * (1 + 52 * Real.log x ^ (3 * A₀)))))) := by
  classical
  have hμ0 : ∀ s : ChainState x d Y d₀ u v r B, 0 ≤ chainMeasure q x d Y d₀ u v r B N s :=
    fun s => mul_nonneg (prod_nonneg fun i _ => prod_nonneg fun h _ => hν _)
      (memWeight_nonneg (fun xp => hν _) _)
  refine normLe_choiceOp (h := fun _ => 1) (h' := fun _ => 1) (by positivity) (by positivity)
    hμ0 (fun _ => one_pos) (fun s => ?_) (fun s' => ?_)
  · -- the rows
    simp only [mul_one]
    exact (sum_le_sum fun c _ => ha s c).trans
      (sum_norm_chainEdgeCoef_le hq hq₁ hd₀ hY hU hL hν hνi hV s)
  · -- the columns
    simp only [mul_one]
    refine le_trans (le_of_eq ?_) ((sum_le_sum fun s _ => sum_le_sum fun c _ =>
      mul_le_mul_of_nonneg_left (ha s c) (hμ0 s)).trans
        (sum_col_chainEdgeCoef_le (A₀ := A₀) hq hq₁ hd₀ hY hU hL hdisj hV hν hνpos hνi s'))
    congr! 3

/-- **The crude edge bound** (PD `mem:edge-crude`): there is a `C_e`, depending only on `K`
and `A₀`, such that eventually, for `B ≤ L³` and `N = 2R`, every choice operator with the edge
output and coefficients bounded by those of `ℰ` has norm at most `L^{C_e}` for the chain
measure, uniformly in `Y ≥ 1`, `d₀ > 0` and the root box. Here `C_e = 3K + 3 max(A₀, 0) + 1`:
the row and column bounds are at most `12^K L^{3K}` and `15^K L^{3K}` times
`κ₀ ≤ 848 L^{3 max(A₀, 0)}`. -/
theorem exists_edgeChoiceOp_normLe {q C CX alo ahi g : ℝ} (A₀ : ℝ) (hq : 0 < q) (hq₁ : q < 1)
    (halo : 1 / 10 < alo) (hg : 0 < g) :
    ∃ Ce : ℝ, ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d →
      ∀ (Y d₀ u v r : ℝ) (B : ℕ), 1 ≤ Y → 0 < d₀ → (B : ℝ) ≤ Real.log x ^ 3 →
      ∀ a : ChainState x d Y d₀ u v r B → EdgeChoice x d Y d₀ u v r → ℂ,
        (∀ s c, ‖a s c‖ ≤
          ‖chainEdgeCoef q A₀ x d Y d₀ u v r B (2 * momentPower x) s c‖) →
        NormLe (fun s => chainMeasure q x d Y d₀ u v r B (2 * momentPower x) s)
          (fun s => chainMeasure q x d Y d₀ u v r B (2 * momentPower x) s)
          (choiceOp (edgeChoices x d Y d₀ u v r) a (chainEdgeOut x d Y d₀ u v r B))
          (Real.log x ^ Ce) := by
  set A := max A₀ 0 with hA
  set c₀ : ℝ := 180 ^ K * 848 ^ 2 with hc₀
  have hc₀1 : 1 ≤ c₀ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
    (by norm_num)
  refine ⟨3 * K + 3 * A + 1, ?_⟩
  filter_upwards [eventually_harmonicMass_band halo.le, eventually_band_disjoint hg,
    eventually_two_mul_add_one_le halo, Real.tendsto_log_atTop.eventually_ge_atTop c₀,
    eventually_gt_atTop 0] with x hV hdisj hbig hLc hx d hd Y d₀ u v r B hY hd₀ hB a ha
  set N := 2 * momentPower x with hN
  set L := Real.log x with hLdef
  have hL1  := hc₀1.trans hLc
  have hL0 : 0 < L := by linarith
  -- the band facts
  have hV₀  := fun i => (hV _ (hd.window i).1).1
  have hV₁  := fun i => (hV _ (hd.window i).1).2
  have hb  :=
    fun p hp => half_le_baseline hq.le (hbig d hd p hp)
  have hdisj' : d.BandsDisjoint x := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hdisj _ _ (hd.gap i j h)
    · exact (hdisj _ _ (hd.gap j i h)).symm
  have hHm  := (Real.rpow_pos_of_pos hx _).trans_le hd.Hm_ge
  have hU : 0 < d₀ * Y * d.Hm := by positivity
  have hnorm := normLe_edgeChoiceOp (A₀ := A₀) hq hq₁ hd₀ hY hU hL0 hdisj'
    (fun i p hp => half_le_primeMass hV₀ hp) (primeWeight_nonneg_of_baseline hb)
    (fun i p hp => (primeWeight_pos_le hV₀ hb hp).1)
    (fun i => (sum_primeWeight_band_le_two hV₀ hb i).trans (by norm_num)) ha
  -- `√(R C) ≤ L^{C_e}`
  have hLA : L ^ (3 * A₀) ≤ L ^ (3 * A) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by rw [hA]; linarith [le_max_left A₀ 0])
  have hLA1 : 1 ≤ L ^ (3 * A) := Real.one_le_rpow hL1 (by rw [hA]; linarith [le_max_right A₀ 0])
  have hκ : 16 * (1 + 52 * L ^ (3 * A₀)) ≤ 848 * L ^ (3 * A) := by linarith
  have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL1
  have hR : 2 ^ K * (2 * (B : ℝ) + 4) ^ K * (16 * (1 + 52 * L ^ (3 * A₀))) ≤
      2 ^ K * (6 * L ^ 3) ^ K * (848 * L ^ (3 * A)) := by
    gcongr
    linarith
  have hC : 3 ^ K * ((B : ℝ) + 4) ^ K * (16 * (1 + 52 * L ^ (3 * A₀))) ≤
      3 ^ K * (5 * L ^ 3) ^ K * (848 * L ^ (3 * A)) := by
    gcongr
    linarith
  have hpow : L ^ (3 * (K : ℝ) + 3 * A + 1) = (L ^ 3) ^ K * L ^ (3 * A) * L := by rpow_ring hL0
  have hfin : (2 ^ K * (2 * (B : ℝ) + 4) ^ K * (16 * (1 + 52 * L ^ (3 * A₀)))) *
      (3 ^ K * ((B : ℝ) + 4) ^ K * (16 * (1 + 52 * L ^ (3 * A₀)))) ≤
        (L ^ (3 * (K : ℝ) + 3 * A + 1)) ^ 2 := by
    calc (2 ^ K * (2 * (B : ℝ) + 4) ^ K * (16 * (1 + 52 * L ^ (3 * A₀)))) *
          (3 ^ K * ((B : ℝ) + 4) ^ K * (16 * (1 + 52 * L ^ (3 * A₀))))
        ≤ (2 ^ K * (6 * L ^ 3) ^ K * (848 * L ^ (3 * A))) *
            (3 ^ K * (5 * L ^ 3) ^ K * (848 * L ^ (3 * A))) :=
          mul_le_mul hR hC (by positivity) (by positivity)
      _ = c₀ * ((L ^ 3) ^ K * L ^ (3 * A)) ^ 2 := by
          rw [hc₀, mul_pow, mul_pow, show (180 : ℝ) = 2 * 6 * 3 * 5 by norm_num, mul_pow,
            mul_pow, mul_pow]
          ring
      _ ≤ L ^ 2 * ((L ^ 3) ^ K * L ^ (3 * A)) ^ 2 := by
          gcongr
          calc c₀ ≤ L := hLc
            _ ≤ L ^ 2 := by
                rw [sq]
                exact le_mul_of_one_le_left hL0.le hL1
      _ = (L ^ (3 * (K : ℝ) + 3 * A + 1)) ^ 2 := by rw [hpow]; ring
  intro f
  refine (hnorm f).trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · rw [Real.sq_sqrt (mul_nonneg (by positivity) (by positivity))]
    exact hfin
  · exact sum_nonneg fun s _ => mul_nonneg (mul_nonneg
      (prod_nonneg fun i _ => prod_nonneg fun h _ => primeWeight_nonneg_of_baseline hb _)
      (memWeight_nonneg (fun xp => primeWeight_nonneg_of_baseline hb _) _)) (sq_nonneg _)

end Assembly

end Erdos408.OneSided
