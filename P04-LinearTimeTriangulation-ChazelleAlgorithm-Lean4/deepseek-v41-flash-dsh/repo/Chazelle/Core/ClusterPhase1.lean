module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.ClusterAlloc

/-!
# WP-I, part 67: the first phase (setup and stages A–D)

`phase1 = setupStmt; stageA; stageB1; stageB2; stageC; stageD`. From a robust planar map at
the handle, it reaches a memory with the facts `PostD`: the static facts of the split driver,
the level tables for the least frequent residue, and the placement of the items.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs Chazelle.Separator Chazelle.Separator.CombMap

@[expose] public section

/-- **The first phase.** -/
def phase1 : Stmt := .seq setupStmt (.seq stageA (.seq stageB1 (.seq stageB2 (.seq stageC stageD))))

/-- The cost bound of the first phase. -/
def cost1 (g : GV) : ℕ := (7 * g.μ + 8 * g.L + 100) +
  ((62 * g.N + 84 * g.μ + 12 * g.μ * g.L + 7 * g.L + 72) + ((172 * g.N + 11 * g.μ + 150) +
  ((280 * g.N + 12 * g.N * g.L + 7 * g.L + 120) + ((80 * g.μ + 6 * g.L + 60) +
  (40 * (g.μ + g.N) + 40)))))

/-- The block of a vertex, read from memory. -/
def boOf (g : GV) (m : ℕ → ℕ) : ℕ → ℕ :=
  blkOf g.μ (fun v => m (g.base 3 + v)) (fun l => m (g.base 36 + l)) (fun l => m (g.base 35 + l))

/-- The key of a vertex, read from memory. -/
def keyOf' (g : GV) (m : ℕ → ℕ) : ℕ → ℕ := fun v => m (g.base 29 + m (g.base 0 + v))

/-- **The facts after the first phase.** -/
structure PostD (g : GV) {F : Type} [Fintype F] [DecidableEq F]
    (M : CombMap (Fin g.μ) F (Fin g.N)) (T : SpanTree M) (a : F → Fin g.N)
    (ha : ∀ f, M.face (a f) = f) (C : CoTree (starTree T a ha)) (R : BTree)
    (first : Fin g.μ → Fin g.N) (preE slot : ℕ → ℕ) (ρ : ℕ) (W : ℕ) (m : ℕ → ℕ) : Prop where
  sf : SFacts M T a ha C R first preE slot (upTf T) g.k' (g.k' - 1 - ρ) (ssOf g) g.A0 g.U W m
  head : ∀ d : Fin g.N, T.level (M.head d) ≤ T.level (M.vert d) + 1
  lv : ∀ l, l < g.μ → LvOK g m (g.k' - 1 - ρ) l
  ρ_lt : ρ < g.k'
  rmin : ∀ r, r < g.k' → cntBelow (fun v => m (g.base 3 + v) % g.k') g.μ ρ ≤
    cntBelow (fun v => m (g.base 3 + v) % g.k') g.μ r
  cnt : ∀ b, b < g.μ → m (g.base 42 + b) = cntLt (boOf g m) g.μ (b + 1)
  pos : ∀ v, v < g.μ → m (g.base 44 + v) =
    if boOf g m v < g.μ then plPos g.μ (boOf g m) (keyOf' g m) v else g.μ
  act : ∀ v, v < g.μ → boOf g m v < g.μ → m (g.base 43 + plPos g.μ (boOf g m) (keyOf' g m) v) = v
  df : ∀ v, v < g.μ → m (g.base 48 + v) = 0
  map : MapArrays m g.bO g.bR g.bV g.μ g.N M
  firstF : ∀ u, u < g.μ → m (g.base 0 + u) < g.N ∧ m (g.bV + m (g.base 0 + u)) = u
  zero : ∀ d, d < g.N → m (g.base 1 + d) = 0

theorem B2F.congr {g : GV} {F : Type} [Fintype F] [DecidableEq F]
    {M : CombMap (Fin g.μ) F (Fin g.N)} {T : SpanTree M} {a : F → Fin g.N}
    {ha : ∀ f, M.face (a f) = f} {C : CoTree (starTree T a ha)} {R : BTree} {preE slot : ℕ → ℕ}
    {m m' : ℕ → ℕ} (h : B2F g C R preE slot m)
    (he : ∀ x, (g.base 26 ≤ x ∧ x < g.base 30) ∨
      (g.A0 + 54 * g.U + g.L * g.U ≤ x ∧ x < g.A0 + 54 * g.U + 2 * (g.L * g.U)) → m' x = m x) :
    B2F g C R preE slot m' := by
  have hU := g.U_ge
  have b26 := g.base_eq 26; have b28 := g.base_eq 28; have b29 := g.base_eq 29
  have b30 := g.base_eq 30
  have hLN : ∀ j, j < g.L → ∀ x, x < g.N → j * g.N + x < g.L * g.U := fun j hj x hx => by
    have : (j + 1) * g.N ≤ g.L * g.U := Nat.mul_le_mul (⋄) (⋄)
    rw [Nat.succ_mul] at this; omega
  refine ⟨fun x hx => ?_, fun x hx => ?_, h.r0, fun x hx => ?_, fun x hx => ?_, h.R_ok, h.R_n,
    h.R_up, h.R_root, h.R_pre, fun j hj x hx => ?_⟩
  · have := x.2; rw [he _ (Or.inl ⟨⋄, ⋄⟩)]; exact h.fpar x hx
  · rw [he _ (Or.inl ⟨⋄, ⋄⟩)]; exact h.fpar_lt x hx
  · rw [he _ (Or.inl ⟨⋄, ⋄⟩)]; exact h.pre x hx
  · rw [he _ (Or.inl ⟨⋄, ⋄⟩)]; exact h.sz x hx
  · have := hLN j hj x hx
    rw [he _ (Or.inr ⟨⋄, ⋄⟩)]; exact h.up_tab j hj x hx

/-- The block of a light-free level is a block index. -/
theorem shift_div_lt {l cs k μ : ℕ} (hk : 0 < k) (hcs : cs < k) (_hkμ : k ≤ μ) (hl : l < μ) :
    (l + cs) / k < μ := by
  Ξ Nat.div_lt_iff_lt_mul hk
  obtain ⟨t, ht⟩ : ∃ t, μ = t + 1 := ⟨μ - 1, ⋄⟩
  Ξ ht, Nat.succ_mul
  have : t ≤ t * k := Nat.le_mul_of_pos_right _ hk
  omega

theorem cntBelow_congr {f f' : ℕ → ℕ} {n r : ℕ} (h : ∀ v, v < n → f v = f' v) :
    cntBelow f n r = cntBelow f' n r := by
  unfold cntBelow; congr 1
  exact Finset.filter_congr (fun v hv => Ρ h v (Finset.mem_range.mp hv))

theorem cntLt_congr {f f' : ℕ → ℕ} {n j : ℕ} (h : ∀ v, v < n → f v = f' v) :
    cntLt f n j = cntLt f' n j := by
  unfold cntLt; congr 1
  exact Finset.filter_congr (fun v hv => Ρ h v (Finset.mem_range.mp hv))

theorem plPos_congr {μ : ℕ} {bo bo' key key' : ℕ → ℕ} (hb : ∀ w, w < μ → bo w = bo' w)
    (hk : ∀ w, w < μ → key w = key' w) {v : ℕ} (hv : v < μ) :
    plPos μ bo key v = plPos μ bo' key' v := by
  unfold plPos rk
  Ξ cntLt_congr hb, hb v hv
  congr 2
  exact Finset.filter_congr (fun w hw => by
    simp only [hb w (Finset.mem_range.mp hw), hk w (Finset.mem_range.mp hw), hk v hv])

end

end Chazelle.Core.Cluster
