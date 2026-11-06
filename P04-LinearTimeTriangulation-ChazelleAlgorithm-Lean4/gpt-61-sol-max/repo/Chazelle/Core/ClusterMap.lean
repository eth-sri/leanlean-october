module

public meta import Chazelle.Arithmetic

public import Chazelle.Programs.Tactics

/-!
# WP-I, part 1: rotation systems stored in memory

Pure mathematics used by the RAM programs of the cluster algorithm (`ClusterSpec`).

* `view m b n`: the array of length `n` at `b` in the memory `m`, clamped to `0` outside
  `[0, n)`; writes outside `[b, b + n)` do not change it (`view_upd_out`), a write inside
  is a `Function.update` (`view_upd_in`).
* Iterating an injective self-map `f` of `[0, N)`: every point returns (`exists_iterate_eq_self`);
  its minimal period `per f N x` (`iterate_per`, `iterate_ne_of_lt_per`,
  `iterate_inj_of_lt_per`), and every iterate is an iterate below the period
  (`exists_lt_per_of_iterate`).
* `Env`: arrays `opp`, `rot`, `vert`, `first` (a dart at every vertex) and the flag arrays `db`
  (blocked darts) and `vb` (blocked vertices), with `nv` vertices and `N` darts; `Env.OK`: `rot`
  is a permutation of the darts whose cycles are the vertex fibres.  `Env.deg`, the degree;
  `Env.sum_deg` (`Σ deg = N`); `Env.orbit_iff` / `Env.per_first` (the rotation orbit of `first u`
  is the fibre of `u`, of length `deg u`).
* `Env.Step`, `Env.Reach`: the graph of the unblocked darts between unblocked vertices.

A flag is *set* when it equals `1`.
-/

namespace Chazelle.Core.Cluster

@[expose] public section

/-! ## Clamped views of memory -/

/-- The array of length `n` at `b`: `m (b + i)` for `i < n`, `0` elsewhere. -/
def view (m : ℕ → ℕ) (b n : ℕ) : ℕ → ℕ := fun i => if i < n then m (b + i) else 0

theorem view_lt {m : ℕ → ℕ} {b n i : ℕ} (h : i < n) : view m b n i = m (b + i) := by
  core_grind

section
variable (m : ℕ → ℕ)
/-- A write outside the array does not change its view. -/
theorem view_upd_out (b n a x : ℕ) (h : a < b ∨ b + n ≤ a) :
    view (upd m a x) b n = view m b n := by
  funext i
  unfold view
  ram_simp 

/-- A write inside the array updates its view. -/
theorem view_upd_in (b n w x : ℕ) (hw : w < n) :
    view (upd m (b + w) x) b n = Function.update (view m b n) w x := by
  funext i
  unfold view
  by_cases hiw : i = w
  all_goals simp_all


end

/-- Views agreeing memories: agreement on `[b, b + n)` gives equal views. -/
theorem view_congr {m m' : ℕ → ℕ} {b n : ℕ} (h : ∀ i, i < n → m' (b + i) = m (b + i)) :
    view m' b n = view m b n := by
  core_grind

/-! ## Iterating an injective self-map of `[0, N)` -/

section Iter

variable (f : ℕ → ℕ) (N : ℕ)

/-- `f` maps `[0, N)` injectively into itself. -/
def InjOn : Prop := (∀ x, x < N → f x < N) ∧ ∀ x, x < N → ∀ y, y < N → f x = f y → x = y

variable {f N}

section
variable (hf : InjOn f N) (n : ℕ)
include hf
theorem InjOn.iterate_lt {x : ℕ} (hx : x < N) : f^[n] x < N := by
  induction n generalizing x with
  | zero => exact hx
  | succ n ih => simp_all [Function.iterate_succ_apply] <;> omega_nf

theorem InjOn.iterate_inj {x y : ℕ} (hx : x < N) (hy : y < N)
    (h : f^[n] x = f^[n] y) : x = y := by
  induction n generalizing x y with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply] at h
    exact hf.2 x hx y hy (ih (hf.1 x hx) (hf.1 y hy) h)


end

section
variable (hf : InjOn f N) {x : ℕ} (hx : x < N)
include hf hx
/-- Cancel a common prefix of iterations. -/
theorem InjOn.iterate_cancel {i j : ℕ} (hij : i ≤ j)
    (h : f^[i] x = f^[j] x) : f^[j - i] x = x := by
  have : f^[j] x = f^[i] (f^[j - i] x) := by
    rw [← Function.iterate_add_apply]; simp_all
  rw [this] at h
  exact (hf.iterate_inj i hx (hf.iterate_lt _ hx) h).symm

/-- **Every point returns** within `N` steps. -/
theorem exists_iterate_eq_self :
    ∃ p, 0 < p ∧ p ≤ N ∧ f^[p] x = x := by
  classical
  have hmaps : ∀ i ∈ Finset.range (N + 1), f^[i] x ∈ Finset.range N := fun i _ =>
    Finset.mem_range.mpr (hf.iterate_lt i hx)
  obtain ⟨i, hi, j, hj, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (by simp) hmaps
  rw [Finset.mem_range] at hi hj
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact ⟨j - i, by omega, by omega, hf.iterate_cancel hx h.le heq⟩
  · exact ⟨i - j, by omega, by omega, hf.iterate_cancel hx h.le heq.symm⟩


end

open Classical in
/-- The minimal period of `x` (`1` if `x` is out of range). -/
noncomputable def per (f : ℕ → ℕ) (_N x : ℕ) : ℕ :=
  if h : ∃ p, 0 < p ∧ f^[p] x = x then Nat.find h else 1

section
variable (hf : InjOn f N) {x : ℕ} (hx : x < N)
include hf hx
theorem per_spec :
    0 < per f N x ∧ per f N x ≤ N ∧ f^[per f N x] x = x := by
  classical
  obtain ⟨p, hp, hpN, hpx⟩ := exists_iterate_eq_self hf hx
  have hex : ∃ p, 0 < p ∧ f^[p] x = x := ⟨p, hp, hpx⟩
  have hper : per f N x = Nat.find hex := by
    grind [per]
  rw [hper]
  refine ⟨(Nat.find_spec hex).1, le_trans (Nat.find_min' hex ⟨hp, hpx⟩) hpN,
    (Nat.find_spec hex).2⟩

theorem iterate_per : f^[per f N x] x = x :=
  (per_spec hf hx).2.2

theorem per_pos : 0 < per f N x := (per_spec hf hx).1

theorem per_le : per f N x ≤ N := (per_spec hf hx).2.1


end

/-- No return before the period. -/
theorem iterate_ne_of_lt_per (_hf : InjOn f N) {x : ℕ} (_hx : x < N) {j : ℕ} (hj0 : 0 < j)
    (hj : j < per f N x) : f^[j] x ≠ x := by
  classical
  intro h
  have hex : ∃ p, 0 < p ∧ f^[p] x = x := ⟨j, hj0, h⟩
  simp_all [per] 

section
variable (hf : InjOn f N) {x : ℕ} (hx : x < N)
include hf hx
/-- The iterates below the period are distinct. -/
theorem iterate_inj_of_lt_per {i j : ℕ}
    (hi : i < per f N x) (hj : j < per f N x) (h : f^[i] x = f^[j] x) : i = j := by
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · exact absurd (hf.iterate_cancel hx hij.le h) (iterate_ne_of_lt_per hf hx (by omega) (by omega))
  · exact hij
  · exact absurd (hf.iterate_cancel hx hij.le h.symm)
      (iterate_ne_of_lt_per hf hx (by omega) (by omega))

/-- Iterates reduce modulo the period. -/
theorem iterate_mod_per (n : ℕ) :
    f^[n] x = f^[n % per f N x] x := by
  conv_lhs => rw [← Nat.mod_add_div n (per f N x)]
  rw [Function.iterate_add_apply]
  congr 1
  induction n / per f N x with
  | zero => rfl
  | succ q ih =>
    rw [Nat.mul_succ, Function.iterate_add_apply, iterate_per hf hx, ih]

/-- Every iterate is an iterate below the period. -/
theorem exists_lt_per_of_iterate (n : ℕ) :
    ∃ j, j < per f N x ∧ f^[n] x = f^[j] x :=
  ⟨n % per f N x, Nat.mod_lt _ (per_pos hf hx), iterate_mod_per hf hx n⟩


end

end Iter

/-! ## Rotation systems in memory -/

/-- The data read by the graph searches: darts `[0, N)`, vertices `[0, nv)`; `opp`, `rot`,
`vert` (arrays on the darts), `first` (a dart at each vertex), `db` (blocked darts, flag `1`),
`vb` (blocked vertices, flag `1`). -/
structure Env where
  /-- opposite dart -/
  opp : ℕ → ℕ
  /-- rotation around the tail -/
  rot : ℕ → ℕ
  /-- tail vertex -/
  vert : ℕ → ℕ
  /-- a dart at each vertex -/
  first : ℕ → ℕ
  /-- blocked darts -/
  db : ℕ → ℕ
  /-- blocked vertices -/
  vb : ℕ → ℕ
  /-- number of vertices -/
  nv : ℕ
  /-- number of darts -/
  N : ℕ

namespace Env

variable (G : Env)

/-- **Well-formed rotation system**: `opp`, `rot` map darts to darts, `vert` darts to vertices,
`rot` is injective, preserves the tail, and its orbits are the vertex fibres; `first u` is a dart
at `u`. -/
structure OK : Prop where
  opp_lt : ∀ d, d < G.N → G.opp d < G.N
  rot_lt : ∀ d, d < G.N → G.rot d < G.N
  vert_lt : ∀ d, d < G.N → G.vert d < G.nv
  rot_inj : ∀ d, d < G.N → ∀ e, e < G.N → G.rot d = G.rot e → d = e
  vert_rot : ∀ d, d < G.N → G.vert (G.rot d) = G.vert d
  orbit : ∀ d, d < G.N → ∀ e, e < G.N → G.vert d = G.vert e → ∃ n, G.rot^[n] d = e
  first_lt : ∀ u, u < G.nv → G.first u < G.N
  vert_first : ∀ u, u < G.nv → G.vert (G.first u) = u

variable {G}

theorem OK.injOn (h : G.OK) : InjOn G.rot G.N := ⟨h.rot_lt, h.rot_inj⟩

theorem OK.vert_iterate (h : G.OK) (n : ℕ) {d : ℕ} (hd : d < G.N) :
    G.vert (G.rot^[n] d) = G.vert d := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih (h.rot_lt d hd), h.vert_rot d hd]

variable (G)

/-- The degree of a vertex: the number of darts at it. -/
def deg (u : ℕ) : ℕ := ((Finset.range G.N).filter (fun d => G.vert d = u)).card

variable {G}

/-- **The degrees sum to the number of darts.** -/
theorem OK.sum_deg (h : G.OK) : ∑ u ∈ Finset.range G.nv, G.deg u = G.N := by
  unfold deg
  rw [← Finset.card_biUnion]
  · have : (Finset.range G.nv).biUnion (fun u => (Finset.range G.N).filter (fun d => G.vert d = u))
        = Finset.range G.N := by
      ext d
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
      ram_all <;> ram_grind
    simp_all
  · intro u _ v _ huv
    simp_all [Function.onFun, Finset.disjoint_left, Finset.mem_filter] 

/-- The degree sum over a set of distinct vertices is at most `N`. -/
theorem OK.sum_deg_le (h : G.OK) (S : Finset ℕ) (hS : ∀ u ∈ S, u < G.nv) :
    ∑ u ∈ S, G.deg u ≤ G.N := by
  calc ∑ u ∈ S, G.deg u ≤ ∑ u ∈ Finset.range G.nv, G.deg u :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun u hu => Finset.mem_range.mpr (hS u hu))
          (fun _ _ _ => Nat.zero_le _)
    _ = G.N := h.sum_deg

section
variable (h : G.OK) {u : ℕ} (hu : u < G.nv)
include h hu
/-- **The rotation orbit of `first u` is the fibre of `u`.** -/
theorem OK.orbit_iff {e : ℕ} :
    (e < G.N ∧ G.vert e = u) ↔ ∃ j, j < per G.rot G.N (G.first u) ∧
      G.rot^[j] (G.first u) = e := by
  have hf := h.first_lt u hu
  constructor
  · rintro ⟨he, hve⟩
    obtain ⟨n, hn⟩ := h.orbit _ hf e he (by rw [h.vert_first u hu, hve])
    obtain ⟨j, hj, hjn⟩ := exists_lt_per_of_iterate h.injOn hf n
    ram_grind
  · rintro ⟨j, -, rfl⟩
    exact ⟨h.injOn.iterate_lt j hf, by rw [h.vert_iterate j hf, h.vert_first u hu]⟩

/-- **The period of `first u` is the degree of `u`.** -/
theorem OK.per_first :
    per G.rot G.N (G.first u) = G.deg u := by
  have hf := h.first_lt u hu
  unfold deg
  have : (Finset.range G.N).filter (fun d => G.vert d = u) =
      (Finset.range (per G.rot G.N (G.first u))).image (fun j => G.rot^[j] (G.first u)) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    rw [h.orbit_iff hu]
  rw [this, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  exact iterate_inj_of_lt_per h.injOn hf hi hj hij

/-! ## The graph of unblocked darts -/


end

variable (G)

/-- The head of a dart. -/
def head (d : ℕ) : ℕ := G.vert (G.opp d)

/-- One step: an unblocked dart from `u` to `w`, both unblocked. -/
def Step (u w : ℕ) : Prop :=
  ∃ d, d < G.N ∧ G.db d ≠ 1 ∧ G.vert d = u ∧ G.head d = w ∧ G.vb u ≠ 1 ∧ G.vb w ≠ 1

/-- Reachability through steps. -/
def Reach (s w : ℕ) : Prop := Relation.ReflTransGen G.Step s w

end Env

end

end Chazelle.Core.Cluster
