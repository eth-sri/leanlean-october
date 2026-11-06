module

public import HK.Defs

/-!
# Generic lemmas about the models

The engine of the development: the mean form of a step and of `A(y) z`, powers of a negative rate, the
generic geometric trajectory `f + qᵗ c • v` together with its consequences (convergence, no fixed
state, no pseudo-stable behaviour after any time, the final value at constant topology, the per-step
convergence factor, constancy of the proximity digraph), and the command `challenge` that restates
the protected theorems from their internal counterparts.
-/

@[expose] public section

namespace HK

open Filter Topology

/-- One step, coordinatewise: the average of the out-neighbours' opinions. -/
theorem step_apply (m : Model) {n : ℕ} (r y : Fin n → ℝ) (i : Fin n) :
    step m r y i = (∑ j ∈ neighbors m r y i, y j) / (neighbors m r y i).card := by
  simp only [step, adjMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_div]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- `A(y) z` coordinatewise: the average of the out-neighbours' entries of `z`. -/
theorem adj_mulVec (m : Model) {n : ℕ} (r y z : Fin n → ℝ) (i : Fin n) :
    (adjMatrix m r y).mulVec z i = (∑ j ∈ neighbors m r y i, z j) / (neighbors m r y i).card := by
  simp only [adjMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_div]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- `traj` one step forward. -/
theorem traj_succ {n : ℕ} (m : Model) (r x₀ : Fin n → ℝ) (t : ℕ) :
    traj m r x₀ (t + 1) = step m r (traj m r x₀ t) := by
  simp only [traj]
  exact Function.iterate_succ_apply' _ _ _

theorem neighbors_eq_of_digraph_eq (m : Model) {n : ℕ} (r y z : Fin n → ℝ)
    (hd : proximityDigraph m r y = proximityDigraph m r z) : neighbors m r y = neighbors m r z := by
  funext i
  ext j
  have := congrFun (congrFun (congrArg Digraph.Adj hd) i) j
  simp only [proximityDigraph] at this
  exact Iff.of_eq this

/-! ### Powers of a rate in `[−1, 0)` -/

theorem pow_bounds_of_neg {q : ℝ} (h0 : -1 < q) (h1 : q < 0) (t : ℕ) :
    q ≤ q ^ t ∧ q ^ t ≤ 1 := by
  have h2 : 0 < -q := by linarith
  have h3 : -q ≤ 1 := by linarith
  have h4 : 0 < (-q) ^ t := pow_pos h2 t
  rw [show q = -(-q) from by ring]
  rcases Nat.even_or_odd t with ht | ht
  · rw [ht.neg_pow]
    constructor <;> linarith [pow_le_one₀ h2.le h3 (n := t)]
  · rw [ht.neg_pow]
    have h5 : (-q) ^ t ≤ -q := pow_le_of_le_one h2.le h3 (by rintro rfl; simp at ht)
    constructor <;> linarith

theorem pow_pos_of_even {q : ℝ} (h1 : q < 0) {t : ℕ} (ht : Even t) : 0 < q ^ t := by
  rw [show q = -(-q) from by ring, ht.neg_pow]
  have := pow_pos (show (0:ℝ) < -q by linarith) t
  linarith

theorem pow_neg_of_odd {q : ℝ} (h1 : q < 0) {t : ℕ} (ht : Odd t) : q ^ t < 0 := by
  rw [show q = -(-q) from by ring, ht.neg_pow]
  have := pow_pos (show (0:ℝ) < -q by linarith) t
  linarith

theorem pos_pow_bounds {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) (t : ℕ) : 0 ≤ a ^ t ∧ a ^ t ≤ 1 :=
  ⟨pow_nonneg h0 t, pow_le_one₀ h0 h1⟩

theorem tendsto_pow_of_neg {q : ℝ} (h0 : -1 < q) (h1 : q < 0) :
    Tendsto (fun t : ℕ => q ^ t) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_abs_lt_one (abs_lt.mpr ⟨h0, by linarith⟩)

theorem tendsto_pow_mul_of_neg {q : ℝ} (h0 : -1 < q) (h1 : q < 0) (c : ℝ) :
    Tendsto (fun t : ℕ => q ^ t * c) atTop (𝓝 0) := by
  simpa using (tendsto_pow_of_neg h0 h1).mul_const c

/-- `a t · a (t+1) < 0` for `a t = qᵗ c` with `q < 0`, `c ≠ 0`. -/
theorem alternating (q c : ℝ) (hq : q < 0) (hc : c ≠ 0) (t : ℕ) :
    q ^ t * c * (q ^ (t + 1) * c) < 0 := by
  have h : q ^ t * c * (q ^ (t + 1) * c) = q * (q ^ t * c) ^ 2 := by ring
  rw [h]
  refine mul_neg_of_neg_of_pos hq ?_
  rw [sq]
  exact mul_self_pos.mpr (mul_ne_zero (pow_ne_zero _ hq.ne) hc)

/-! ### The geometric trajectory `f + qᵗ c v` -/

/-- If one step maps `f + u v` to `f + (q u) v` throughout an interval containing every `qᵗ c`, the
trajectory from `f + c v` is `f + qᵗ c v`. -/
theorem traj_geom {n : ℕ} (m : Model) (r x₀ f v : Fin n → ℝ) (q c a b : ℝ)
    (hs : ∀ u, a ≤ u → u ≤ b → step m r (fun i => f i + u * v i) = fun i => f i + (q * u) * v i)
    (h0 : x₀ = (fun i => f i + c * v i)) (hb : ∀ t, a ≤ q ^ t * c ∧ q ^ t * c ≤ b) :
    ∀ t, traj m r x₀ t = fun i => f i + (q ^ t * c) * v i := by
  intro t
  induction t with
  | zero => rw [h0]; simp only [traj, Function.iterate_zero, id_eq, pow_zero, one_mul]
  | succ t ih =>
    rw [traj_succ, ih, hs _ (hb t).1 (hb t).2]
    funext i
    rw [pow_succ]
    ring

/-- `traj_geom` with `c = 1`. -/
theorem traj_geom1 {n : ℕ} (m : Model) (r x₀ f v : Fin n → ℝ) (q a b : ℝ)
    (hs : ∀ u, a ≤ u → u ≤ b → step m r (fun i => f i + u * v i) = fun i => f i + (q * u) * v i)
    (h0 : x₀ = (fun i => f i + v i)) (hb : ∀ t, a ≤ q ^ t ∧ q ^ t ≤ b) :
    ∀ t, traj m r x₀ t = fun i => f i + q ^ t * v i := by
  intro t
  simpa using traj_geom m r x₀ f v q 1 a b hs (by simpa using h0) (fun t => by simpa using hb t) t

/-- A trajectory alternating between two parity intervals of offsets: `f + u v` maps to
`f + (q u) v` for `0 < u ≤ c` and for `q c ≤ u < 0`. -/
theorem traj_alt {n : ℕ} (m : Model) (r x₀ f v : Fin n → ℝ) (q c : ℝ)
    (hq : -1 < q) (hq0 : q < 0) (hc : 0 < c)
    (hs : ∀ u, 0 < u → u ≤ c → step m r (fun i => f i + u * v i) = fun i => f i + (q * u) * v i)
    (hs' : ∀ u, q * c ≤ u → u < 0 → step m r (fun i => f i + u * v i) = fun i => f i + (q * u) * v i)
    (h0 : x₀ = fun i => f i + c * v i) :
    ∀ t, traj m r x₀ t = fun i => f i + (q ^ t * c) * v i := by
  intro t
  induction t with
  | zero => rw [h0]; simp [traj]
  | succ t ih =>
    obtain ⟨hb0, hb1⟩ := pow_bounds_of_neg hq hq0 t
    have hc0 : 0 ≤ c := hc.le
    have hl : q * c ≤ q ^ t * c := mul_le_mul_of_nonneg_right hb0 hc0
    have hr : q ^ t * c ≤ c := by simpa using mul_le_mul_of_nonneg_right hb1 hc0
    have hne : q ^ t * c ≠ 0 := mul_ne_zero (pow_ne_zero t hq0.ne) hc.ne'
    rcases lt_or_gt_of_ne hne with h | h
    · rw [traj_succ, ih, hs' _ hl h]
      funext i; rw [pow_succ]; ring
    · rw [traj_succ, ih, hs _ h hr]
      funext i; rw [pow_succ]; ring

/-- The same for a trajectory driven by two atoms, `F u w` with `(u, w) ↦ (q u, s w)`. -/
theorem traj_geom2 {n : ℕ} (m : Model) (r x₀ : Fin n → ℝ) (F : ℝ → ℝ → Fin n → ℝ)
    (q s a b : ℝ)
    (hs : ∀ u w, a ≤ u → u ≤ b → 0 ≤ w → w ≤ 1 → step m r (F u w) = F (q * u) (s * w))
    (h0 : x₀ = F 1 1) (hb : ∀ t, a ≤ q ^ t ∧ q ^ t ≤ b) (hw : ∀ t, 0 ≤ s ^ t ∧ s ^ t ≤ 1) :
    ∀ t, traj m r x₀ t = F (q ^ t) (s ^ t) := by
  intro t
  induction t with
  | zero => rw [h0]; simp [traj]
  | succ t ih =>
    rw [traj_succ, ih, hs _ _ (hb t).1 (hb t).2 (hw t).1 (hw t).2, pow_succ', pow_succ']

theorem tendsto_of_geom {n : ℕ} (x : ℕ → Fin n → ℝ) (f v : Fin n → ℝ) (a : ℕ → ℝ)
    (ha : Tendsto a atTop (𝓝 0)) (hx : ∀ t, x t = fun i => f i + a t * v i) :
    Tendsto x atTop (𝓝 f) := by
  rw [tendsto_pi_nhds]
  intro i
  simpa [hx] using (ha.mul_const (v i)).const_add (f i)

theorem tendsto_of_geom1 {n : ℕ} (x : ℕ → Fin n → ℝ) (f v : Fin n → ℝ) (q : ℝ)
    (h0 : -1 < q) (h1 : q < 0) (hx : ∀ t, x t = fun i => f i + q ^ t * v i) :
    Tendsto x atTop (𝓝 f) :=
  tendsto_of_geom x f v (fun t => q ^ t) (tendsto_pow_of_neg h0 h1) hx

theorem not_monotone_side (l p q c : ℝ) (hpq : p * q < 0) :
    ¬ ((l + p * c < l + q * c ∧ l + q * c < l) ∨ (l + p * c > l + q * c ∧ l + q * c > l)) := by
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> nlinarith [sq_nonneg c, sq_nonneg (q * c)]

theorem not_fixedFrom_of_geom {n : ℕ} (x : ℕ → Fin n → ℝ) (f v : Fin n → ℝ) (a : ℕ → ℝ)
    (hx : ∀ t, x t = fun i => f i + a t * v i) (hab : ∀ t, a t * a (t + 1) < 0)
    (i : Fin n) (hv : v i ≠ 0) (τ : ℕ) : ¬ FixedFrom x τ := by
  intro h
  have h1 := congrFun (h (τ + 1) (Nat.le_succ τ)) i
  simp only [hx] at h1
  have h2 : a (τ + 1) = a τ := mul_right_cancel₀ hv (by simpa using h1)
  have h3 := hab τ
  rw [h2] at h3
  nlinarith [sq_nonneg (a τ)]

theorem not_fixedFrom_of_geom1 {n : ℕ} (x : ℕ → Fin n → ℝ) (f v : Fin n → ℝ) (q : ℝ)
    (hq : q < 0) (hx : ∀ t, x t = fun i => f i + q ^ t * v i) (i : Fin n) (hv : v i ≠ 0) (τ : ℕ) :
    ¬ FixedFrom x τ :=
  not_fixedFrom_of_geom x f v (fun t => q ^ t) hx (by simpa using alternating q 1 hq one_ne_zero) i
    (by simpa using hv) τ



theorem not_pseudoStable_of_geom {n : ℕ} (x : ℕ → Fin n → ℝ) (f v : Fin n → ℝ) (a : ℕ → ℝ)
    (ha : Tendsto a atTop (𝓝 0)) (hx : ∀ t, x t = fun i => f i + a t * v i)
    (hab : ∀ t, a t * a (t + 1) < 0) (xinf : Fin n → ℝ) (τ : ℕ) :
    ¬ PseudoStableAfter x xinf τ := by
  rintro ⟨hlim, F, C, -, ⟨i, hi⟩, -, -, h⟩
  have hx' : xinf = f := tendsto_nhds_unique hlim (tendsto_of_geom x f v a ha hx)
  subst hx'
  have hc := (h τ le_rfl).2 i hi
  simp only [hx] at hc
  exact not_monotone_side _ _ _ _ (hab τ) hc

theorem not_pseudoStable_of_geom1 {n : ℕ} (x : ℕ → Fin n → ℝ) (f v : Fin n → ℝ) (q : ℝ)
    (h0 : -1 < q) (h1 : q < 0) (hx : ∀ t, x t = fun i => f i + q ^ t * v i)
    (xinf : Fin n → ℝ) (τ : ℕ) : ¬ PseudoStableAfter x xinf τ :=
  not_pseudoStable_of_geom x f v (fun t => q ^ t) (tendsto_pow_of_neg h0 h1) hx
    (by simpa using alternating q 1 h1 one_ne_zero) xinf τ



/-- Each coordinate of a pseudo-stable trajectory sits at its limit, or stays strictly below it, or
stays strictly above it, from `τ` on. -/
theorem pseudoStableAfter_coordinate_side {n : ℕ} (x : ℕ → Fin n → ℝ)
    (L : Fin n → ℝ) (τ : ℕ) (hps : PseudoStableAfter x L τ) (i : Fin n) :
    (∀ t, τ ≤ t → x t i = L i) ∨
    (∀ t, τ ≤ t → x t i < L i) ∨ (∀ t, τ ≤ t → L i < x t i) := by
  obtain ⟨-, F, C, -, -, -, hFC, h⟩ := hps
  have himem : i ∈ F ∨ i ∈ C := by
    rw [← Finset.mem_union, hFC]
    exact Finset.mem_univ i
  rcases himem with hi | hi
  · exact Or.inl fun t ht => (h t ht).1 i hi
  · rcases (h τ le_rfl).2 i hi with hb | ha
    · right; left
      intro t ht
      induction t, ht using Nat.le_induction with
      | base => exact lt_trans hb.1 hb.2
      | succ t ht ih =>
        rcases (h t ht).2 i hi with h' | h'
        · exact h'.2
        · linarith [h'.1]
    · right; right
      intro t ht
      induction t, ht using Nat.le_induction with
      | base => exact lt_trans ha.2 ha.1
      | succ t ht ih =>
        rcases (h t ht).2 i hi with h' | h'
        · linarith [h'.1, h'.2]
        · exact h'.2

/-! ### The final value at constant topology and the per-step factor -/

/-! ### The final value at constant topology and the per-step factor -/

/-- The limit of `f + qᵏ c v` for `|q| < 1`. -/
theorem limUnder_geom {n : ℕ} (f v : Fin n → ℝ) (q c : ℝ) (hq : |q| < 1) :
    limUnder atTop (fun k : ℕ => f + (q ^ k * c) • v) = f := by
  have h0 := ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq).mul_const c).smul_const v
  have h2 := h0.const_add f
  rw [zero_mul, zero_smul, add_zero] at h2
  exact h2.limUnder_eq

/-- If the adjacency matrix of `y = f + c v` fixes `f` and scales `v` by `q` with `|q| < 1`, the final
value at constant topology of `y` is `f`. -/
theorem fvct_of_adj {n : ℕ} (m : Model) (r : Fin n → ℝ) (y f v : Fin n → ℝ) (q c : ℝ)
    (hy : y = f + c • v)
    (hf : (adjMatrix m r y).mulVec f = f) (hv : (adjMatrix m r y).mulVec v = q • v)
    (hq : |q| < 1) : fvct m r y = f := by
  have key : ∀ k : ℕ, ((adjMatrix m r y) ^ k).mulVec y = f + (q ^ k * c) • v := by
    intro k
    induction k with
    | zero => simp [hy]
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_add, Matrix.mulVec_smul,
        hf, hv, smul_smul, pow_succ]
      congr 1
      ring
  unfold fvct
  simp only [key]
  exact limUnder_geom f v q c hq

/-- The final value at constant topology of `y = f + c v`, when the table is constant along the
line and one step scales the offset by `q`. -/
theorem fvct_of_step {n : ℕ} (m : Model) (r : Fin n → ℝ) (y f v : Fin n → ℝ) (q c a b : ℝ)
    (hy : y = fun i => f i + c * v i)
    (hT : ∀ u, a ≤ u → u ≤ b → neighbors m r (fun i => f i + u * v i) = neighbors m r y)
    (hs : ∀ u, a ≤ u → u ≤ b → step m r (fun i => f i + u * v i) = fun i => f i + (q * u) * v i)
    (hb : ∀ t, a ≤ q ^ t * c ∧ q ^ t * c ≤ b) (hq : |q| < 1) : fvct m r y = f := by
  have key : ∀ k : ℕ, ((adjMatrix m r y) ^ k).mulVec y = fun i => f i + (q ^ k * c) * v i := by
    intro k
    induction k with
    | zero => rw [hy]; simp
    | succ k ih =>
      obtain ⟨h1, h2⟩ := hb k
      have hA : adjMatrix m r (fun i => f i + (q ^ k * c) * v i) = adjMatrix m r y := by
        simp only [adjMatrix, hT _ h1 h2]
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, ← hA]
      change step m r (fun i => f i + (q ^ k * c) * v i) = fun i => f i + (q ^ (k + 1) * c) * v i
      rw [hs _ h1 h2]
      funext i
      rw [pow_succ]
      ring
  unfold fvct
  simp only [key]
  exact limUnder_geom f v q c hq

theorem perStepFactor_geom1 {n : ℕ} (m : Model) (r : Fin n → ℝ) (x : ℕ → Fin n → ℝ)
    (f v : Fin n → ℝ) (q : ℝ) (hq : q ≠ 0)
    (hx : ∀ t, x t = fun i => f i + q ^ t * v i)
    (hfv : ∀ t, fvct m r (x t) = f)
    (i : Fin n) (hv : v i ≠ 0) (t : ℕ) : perStepFactor m r x i t = q := by
  rw [perStepFactor, hfv t]
  simp only [hx, Pi.add_apply, add_sub_cancel_left, pow_succ]
  field_simp

theorem perStepFactor_not_tendsto {n : ℕ} (m : Model) (r : Fin n → ℝ) (x : ℕ → Fin n → ℝ)
    (i : Fin n) (q : ℝ) (hq : q < 0) (h : ∀ t, perStepFactor m r x i t = q)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ¬ Tendsto (fun t => perStepFactor m r x i t) atTop (𝓝 ρ) := by
  intro ht
  have hc : Tendsto (fun t => perStepFactor m r x i t) atTop (𝓝 q) := by
    simp [funext h]
  have := tendsto_nhds_unique ht hc
  linarith

/-! ### Constant and alternating proximity digraphs -/

theorem digraph_constant_of_table {n : ℕ} (m : Model) (r x₀ : Fin n → ℝ)
    (T : Fin n → Finset (Fin n)) (h : ∀ t, neighbors m r (traj m r x₀ t) = T) (t : ℕ) :
    proximityDigraph m r (traj m r x₀ t) = proximityDigraph m r x₀ := by
  have h0 : neighbors m r x₀ = T := h 0
  simp only [proximityDigraph, h t, h0]

/-- A table that differs at each time from the previous one makes the proximity digraph
non-constant on every tail. -/
theorem digraph_not_const_of_alt {n : ℕ} (m : Model) (r x₀ : Fin n → ℝ)
    (T : ℕ → Fin n → Finset (Fin n)) (h : ∀ t, neighbors m r (traj m r x₀ t) = T t)
    (hT : ∀ t, T (t + 1) ≠ T t) (τ : ℕ) :
    ∃ t, τ ≤ t ∧ proximityDigraph m r (traj m r x₀ t) ≠ proximityDigraph m r (traj m r x₀ τ) := by
  refine ⟨τ + 1, Nat.le_succ τ, fun hd => hT τ ?_⟩
  have h2 := neighbors_eq_of_digraph_eq m r _ _ hd
  rw [h (τ + 1), h τ] at h2
  exact h2

/-! ### The rates of the systems -/

theorem sbiRate_eq : sbiRate = (1 - Real.goldenRatio) / 4 := by
  unfold sbiRate Real.goldenRatio
  ring

theorem sbiRate_mem : -1 < sbiRate ∧ sbiRate < 0 := by
  have h1 := Real.one_lt_goldenRatio
  have h2 := Real.goldenRatio_lt_two
  rw [sbiRate_eq]
  constructor <;> linarith

theorem sqrt_two_bounds : 1.4 < Real.sqrt 2 ∧ Real.sqrt 2 < 1.5 :=
  ⟨(Real.lt_sqrt (by norm_num)).2 (by norm_num), (Real.sqrt_lt' (by norm_num)).2 (by norm_num)⟩

theorem sqrt249_bounds : 15 < Real.sqrt 249 ∧ Real.sqrt 249 < 16 :=
  ⟨(Real.lt_sqrt (by norm_num)).2 (by norm_num), (Real.sqrt_lt' (by norm_num)).2 (by norm_num)⟩

theorem sqrt249_sq : Real.sqrt 249 ^ 2 = 249 := Real.sq_sqrt (by norm_num)

theorem sbc5Rate_mem : -1 < sbc5Rate ∧ sbc5Rate < 0 := by
  obtain ⟨h1, h2⟩ := sqrt_two_bounds
  unfold sbc5Rate
  constructor <;> linarith

theorem sbi6Rate_mem : -1 < sbi6Rate ∧ sbi6Rate < 0 := by
  obtain ⟨h1, h2⟩ := sqrt249_bounds
  unfold sbi6Rate
  constructor <;> linarith

theorem sbiRate_abs_lt_quarter : |sbiRate| < 1 / 4 := by
  have h1 := Real.one_lt_goldenRatio
  have h2 := Real.goldenRatio_lt_two
  rw [abs_lt, sbiRate_eq]
  constructor <;> linarith

/-! ### Tactics and commands -/

/-- `tab a, b`: the neighbourhood table of a system whose data are `a`, `b`, … -/
macro "tab " xs:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic| (funext i; ext j; fin_cases i <;> fin_cases j <;>
    simp [neighbors, Model.bound, abs_le, $xs,*] <;> (try constructor) <;> (try intro) <;> linarith))

/-- `tabn a, b`: the neighbourhood table of a system with nonlinear side conditions. -/
macro "tabn " xs:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic| (funext i; ext j; fin_cases i <;> fin_cases j <;>
    simp [neighbors, Model.bound, abs_le, $xs,*] <;> (try constructor) <;> (try intro) <;> nlinarith))

/-- `sq n`: the ring normal form of a goal whose only algebraic relation is `√n ^ 2 = n`. -/
macro "sq " n:term : tactic =>
  `(tactic| (ring_nf; try rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ $n)]; ring))

/-- `stps e | a, b | n`: the step of a system with a square-root relation. -/
macro "stps " e:Lean.Parser.Tactic.rwRule " | " xs:Lean.Parser.Tactic.simpLemma,* " | " n:term : tactic =>
  `(tactic| (funext i; rw [step_apply, $e]; fin_cases i <;>
    simp [Finset.sum_insert, $xs,*] <;> sq $n))

/-- `init a, b`: the initial vector is `f + v` for the data `a`, `b`, … -/
macro "init " xs:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic| (funext i; fin_cases i <;> simp [$xs,*] <;> ring_nf))

/-- `stp e | a, b`: the step of a system, with `e` the neighbourhood table and `a`, `b` its data. -/
macro "stp " e:Lean.Parser.Tactic.rwRule " | " xs:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic| (funext i; rw [step_apply, $e]; fin_cases i <;>
    simp [Finset.sum_insert, $xs,*] <;> ring))

syntax "chall " (ident str)* : command

open Lean Elab Command in
/-- `chall name "tactic"`: declare `name_internal` with the protected statement of `name` from
`Challenge.lean` and the given tactic script (written as a string). With no arguments, declare every
protected theorem from its `_internal` counterpart. -/
elab_rules : command
  | `(chall $[$xs:ident $ts:str]*) => do
    let src := "\n" ++ (← IO.FS.readFile "Challenge.lean")
    let env ← getEnv
    let hd : String → String := fun blk =>
      String.join (List.intersperse ":=" (((blk.splitOn "sorry").head!).splitOn ":=").dropLast)
    let run (cmd : String) : CommandElabM Unit := do
      let stx ← match Parser.runParserCategory env `command cmd with
        | .ok s => pure s
        | .error e => throwError "chall: {e}\n{cmd}"
      elabCommand stx
    if xs.isEmpty then
      for blk in (src.splitOn "\ntheorem ").drop 1 do
        run s!"theorem {hd blk} := by apply {(blk.splitOn " ").head!}_internal <;> assumption"
    else
      for a in xs, t in ts do
        let base := a.getId
        let some blk := (src.splitOn s!"\ntheorem {base}").drop 1 |>.head? | throwError "chall: no {base}"
        let ind : String → Nat := fun l => (l.toList.takeWhile (fun c => c == ' ')).length
        let lines := (t.getString).splitOn "\n"
        let n : Nat := ((lines.drop 1).filter (fun l => ind l < l.length)).map ind |>.foldr min 1000
        let out : String → String := fun l => String.ofList (l.toList.drop (min n (ind l)))
        let tac := String.join (List.intersperse "\n" (List.map (fun l => s!"  {out l}") lines))
        run s!"theorem {base}_internal {hd blk} := by\n{tac}"
end HK
