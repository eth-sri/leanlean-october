module

public import RequestProject.GenusLoops
public import RequestProject.PresPosetReading
public import Mathlib
public import Mathlib.Order.Extension.Linear
public import RequestProject.CombPi1

@[expose] public section
noncomputable section
namespace FiniteChains

namespace ASC

universe u

variable {P : Type u} [PartialOrder P]

/-- **The local conditions of a two-dimensional closed cell structure**, read on its face
poset: a rank function which is strictly monotone and at most two, exactly two vertices on
every edge, exactly two faces through every edge, and exactly two edges of a face through a
vertex of that face. -/
structure SurfaceRank (P : Type u) [PartialOrder P] where
  /-- The dimension of a cell. -/
  rk : P → ℕ
  /-- The rank increases strictly along the face order. -/
  rk_lt_of_lt : ∀ {x y : P}, x < y → rk x < rk y
  /-- The cell structure is two-dimensional. -/
  rk_le_two : ∀ x : P, rk x ≤ 2
  /-- Every edge has exactly two endpoints. -/
  two_vertices : ∀ e : P, rk e = 1 → ExactlyTwo (fun v : P => v < e)
  /-- Every edge lies in exactly two faces. -/
  two_faces : ∀ e : P, rk e = 1 → ExactlyTwo (fun f : P => e < f)
  /-- Every vertex of a face lies in exactly two edges of that face. -/
  two_edges : ∀ v f : P, rk v = 0 → rk f = 2 → v < f →
    ExactlyTwo (fun e : P => v < e ∧ e < f)
  /-- Every cell is a face of a two-dimensional cell. -/
  exists_face : ∀ x : P, ∃ f : P, rk f = 2 ∧ x ≤ f
  /-- Every two-dimensional cell has a vertex. -/
  exists_vertex : ∀ f : P, rk f = 2 → ∃ v : P, rk v = 0 ∧ v < f

namespace SurfaceRank

variable (S : SurfaceRank P)

theorem rk_eq_of_le_of_rk_le {x y : P} (S : SurfaceRank P) (h : x ≤ y) (hxy : S.rk y ≤ S.rk x) :
    x = y := by
  rcases h.lt_or_eq with hlt | rfl
  · exact absurd (S.rk_lt_of_lt hlt) (by omega)
  · rfl

/-- A cell of rank two is maximal. -/
theorem not_lt_of_rk_two {f x : P} (S : SurfaceRank P) (hf : S.rk f = 2) : ¬ f < x :=
  fun h => absurd (S.rk_lt_of_lt h) (by have := S.rk_le_two x; omega)

end SurfaceRank

/-! ### Transfer of `ExactlyTwo` along an equivalence of predicates -/

theorem ExactlyTwo.congr {α : Sort*} {P Q : α → Prop} (h : ExactlyTwo P)
    (hPQ : ∀ x, P x ↔ Q x) : ExactlyTwo Q := by
  obtain ⟨x, y, hxy, hx, hy, huniq⟩ := h
  exact ⟨x, y, hxy, (hPQ x).1 hx, (hPQ y).1 hy, fun z hz => huniq z ((hPQ z).2 hz)⟩

/-! ### The order complex of a surface poset -/

section OrderComplex

variable [DecidableEq P]

theorem isChain_pair_iff {x y : P} :
    IsChain (· ≤ ·) (({x, y} : Finset P) : Set P) ↔ (x ≤ y ∨ y ≤ x) := by
  constructor
  · intro h
    by_cases hxy : x = y
    · exact Or.inl (le_of_eq hxy)
    · exact h (by simp) (by simp) hxy
  · intro h
    rintro a ha b hb hab
    simp at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact h
    · exact h.symm
    · exact absurd rfl hab


namespace SurfaceRank

/-- The neighbours of an edge of the order complex, described by the ranks of its two cells. -/
theorem neighbours_iff (_S : SurfaceRank P) {x y z : P} (hxy : x < y) :
    (z ∉ ({x, y} : Finset P) ∧ insert z ({x, y} : Finset P) ∈ (orderComplex P).faces) ↔
      (z ≠ x ∧ z ≠ y ∧ (z ≤ x ∨ x ≤ z) ∧ (z ≤ y ∨ y ≤ z)) := by
  rw [(show insert z ({x, y} : Finset P) ∈ (orderComplex P).faces ↔
      ((z ≤ x ∨ x ≤ z) ∧ (z ≤ y ∨ y ≤ z)) by
    rw [mem_orderComplex]
    constructor
    · intro h
      rw [show ((insert z ({x, y} : Finset P) : Finset P) : Set P) = {z, x, y} by simp] at h
      have hz : z ∈ ({z, x, y} : Set P) := by simp
      have hx : x ∈ ({z, x, y} : Set P) := by simp
      have hy : y ∈ ({z, x, y} : Set P) := by simp
      exact ⟨le_or_le_of_isChain h hz hx, le_or_le_of_isChain h hz hy⟩
    · rintro ⟨hzx, hzy⟩
      rw [show ((insert z ({x, y} : Finset P) : Finset P) : Set P) = {z, x, y} by simp]
      exact isChain_triple hzx hzy (Or.inl (hxy.le)))]
  grind

theorem neighbours_zero_one (S : SurfaceRank P) {x y z : P} (hxy : x < y) (hx : S.rk x = 0)
    (hy : S.rk y = 1) :
    (z ∉ ({x, y} : Finset P) ∧ insert z ({x, y} : Finset P) ∈ (orderComplex P).faces) ↔
      y < z := by
  rw [neighbours_iff S hxy]
  constructor
  · rintro ⟨hzx, hzy, hcx, hcy⟩
    have hxz : x < z := by
      rcases hcx with h | h
      · exact absurd h (fun hh => hzx (S.rk_eq_of_le_of_rk_le hh (by omega)))
      · exact lt_of_le_of_ne h (Ne.symm hzx)
    rcases hcy with h | h
    · -- `z < y` would force `rk z = 0`, contradicting `x < z`
      have hzlt  := lt_of_le_of_ne h hzy
      have h1 := S.rk_lt_of_lt hxz
      have h2 := S.rk_lt_of_lt hzlt
      omega
    · exact lt_of_le_of_ne h (Ne.symm hzy)
  · grind

theorem neighbours_one_two (S : SurfaceRank P) {x y z : P} (hxy : x < y) (hx : S.rk x = 1)
    (hy : S.rk y = 2) :
    (z ∉ ({x, y} : Finset P) ∧ insert z ({x, y} : Finset P) ∈ (orderComplex P).faces) ↔
      z < x := by
  rw [neighbours_iff S hxy]
  constructor
  · rintro ⟨hzx, hzy, hcx, hcy⟩
    rcases hcx with h | h
    · exact lt_of_le_of_ne h hzx
    · -- `x < z` forces `rk z = 2`, and then `z` and `y` are two comparable maximal cells
      have hxz  := lt_of_le_of_ne h (Ne.symm hzx)
      have hrz : S.rk z = 2 := by
        have := S.rk_lt_of_lt hxz
        have := S.rk_le_two z
        omega
      rcases hcy with h' | h'
      · exact absurd (S.rk_eq_of_le_of_rk_le h' (by omega)) hzy
      · exact absurd (S.rk_eq_of_le_of_rk_le h' (by omega)) (Ne.symm hzy)
  · grind

theorem neighbours_zero_two (S : SurfaceRank P) {x y z : P} (hxy : x < y) (hx : S.rk x = 0)
    (hy : S.rk y = 2) :
    (z ∉ ({x, y} : Finset P) ∧ insert z ({x, y} : Finset P) ∈ (orderComplex P).faces) ↔
      (x < z ∧ z < y) := by
  rw [neighbours_iff S hxy]
  constructor
  · rintro ⟨hzx, hzy, hcx, hcy⟩
    have hxz : x < z := by
      rcases hcx with h | h
      · exact absurd h (fun hh => hzx (S.rk_eq_of_le_of_rk_le hh (by omega)))
      · exact lt_of_le_of_ne h (Ne.symm hzx)
    refine ⟨hxz, ?_⟩
    rcases hcy with h | h
    · exact lt_of_le_of_ne h hzy
    · exact absurd (lt_of_le_of_ne h (Ne.symm hzy)) (S.not_lt_of_rk_two hy)
  · grind

omit [DecidableEq P] in
/-- The rank of the smaller cell of an edge of the order complex is `0` or `1`, and the possible
pairs of ranks are `(0,1)`, `(1,2)` and `(0,2)`. -/
theorem rk_cases (S : SurfaceRank P) {x y : P} (hxy : x < y) :
    (S.rk x = 0 ∧ S.rk y = 1) ∨ (S.rk x = 1 ∧ S.rk y = 2) ∨ (S.rk x = 0 ∧ S.rk y = 2) := by
  have h1 := S.rk_lt_of_lt hxy
  have h2 := S.rk_le_two y
  omega

/-- **Every edge of the order complex lies in exactly two triangles.** -/
theorem edgeInTwoTriangles (S : SurfaceRank P) : EdgeInTwoTriangles (orderComplex P) := by
  have key : ∀ x y : P, x < y →
      ExactlyTwo (fun z : P => z ∉ ({x, y} : Finset P) ∧
        insert z ({x, y} : Finset P) ∈ (orderComplex P).faces) := by
    intro x y hxy
    rcases S.rk_cases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact (S.two_faces y hy).congr (fun z => (S.neighbours_zero_one hxy hx hy).symm)
    · exact (S.two_vertices x hx).congr (fun z => (S.neighbours_one_two hxy hx hy).symm)
    · exact (S.two_edges x y hx hy hxy).congr (fun z => (S.neighbours_zero_two hxy hx hy).symm)
  intro s hs hcard
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hcard
  have hcomp  := isChain_pair_iff.1 hs
  rcases hcomp with h | h
  · exact key x y (lt_of_le_of_ne h hxy)
  · have hpair  := Finset.pair_comm x y
    rw [hpair]
    exact key y x (lt_of_le_of_ne h (Ne.symm hxy))

omit [DecidableEq P] in
/-- The order complex of a two-dimensional cell poset is two-dimensional. -/
theorem chain_card_le_three (S : SurfaceRank P) {s : Finset P}
    (hs : s ∈ (orderComplex P).faces) : s.card ≤ 3 := by
  have hinj : Set.InjOn S.rk (s : Set P) := by
    intro a ha b hb hab
    rcases le_or_le_of_isChain hs ha hb with h | h
    · exact S.rk_eq_of_le_of_rk_le h (le_of_eq hab.symm)
    · exact (S.rk_eq_of_le_of_rk_le h (le_of_eq hab)).symm
  have hsub : s.image S.rk ⊆ ({0, 1, 2} : Finset ℕ) := by
    intro n hn
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hn
    have := S.rk_le_two a
    interval_cases h : S.rk a <;> simp
  have hcard  :=
    Finset.card_image_of_injOn (by intro a ha b hb hab; exact hinj ha hb hab)
  calc s.card = (s.image S.rk).card := hcard.symm
    _ ≤ ({0, 1, 2} : Finset ℕ).card := Finset.card_le_card hsub
    _ = 3 := by decide

/-- **Every cell is a vertex of a triangle of the order complex.** -/
theorem vertexInTriangle (S : SurfaceRank P) (x : P) :
    ∃ s ∈ (orderComplex P).faces, s.card = 3 ∧ x ∈ s := by
  -- a two-cell above `x`, a vertex of it and an edge between them
  obtain ⟨f, hf, hxf⟩ := S.exists_face x
  obtain ⟨v, hv, hvf⟩ := S.exists_vertex f hf
  obtain ⟨e, -, -, ⟨hve, hef⟩, -, -⟩ := S.two_edges v f hv hf hvf
  have hchain : ({v, e, f} : Finset P) ∈ (orderComplex P).faces := by
    rw [mem_orderComplex]
    have : IsChain (· ≤ ·) ({v, e, f} : Set P) :=
      isChain_triple (Or.inl hve.le) (Or.inl (hve.trans hef).le) (Or.inl hef.le)
    simpa [Finset.coe_insert] using this
  have hcard : ({v, e, f} : Finset P).card = 3 := by
    have h1  := hve.ne
    have h2  := (hve.trans hef).ne
    have h3  := hef.ne
    rw [Finset.card_insert_of_notMem (by simp [h1, h2]),
      Finset.card_insert_of_notMem (by simp [h3])]
    simp
  -- `x` is a face of `f`; it is `f` itself, or a vertex or an edge of `f`
  rcases eq_or_lt_of_le hxf with rfl | hlt
  · grind
  · have hrx : S.rk x = 0 ∨ S.rk x = 1 := by
      have := S.rk_lt_of_lt hlt
      omega
    rcases hrx with hrx | hrx
    · -- `x` is a vertex of `f`
      obtain ⟨e', -, -, ⟨hxe, he'f⟩, -, -⟩ := S.two_edges x f hrx hf hlt
      refine ⟨{x, e', f}, ?_, ?_, by simp⟩
      · rw [mem_orderComplex]
        have : IsChain (· ≤ ·) ({x, e', f} : Set P) :=
          isChain_triple (Or.inl hxe.le) (Or.inl (hxe.trans he'f).le) (Or.inl he'f.le)
        simpa [Finset.coe_insert] using this
      · grind
    · -- `x` is an edge of `f`
      obtain ⟨w, -, -, hwx, -, -⟩ := S.two_vertices x hrx
      refine ⟨{w, x, f}, ?_, ?_, by simp⟩
      · rw [mem_orderComplex]
        have : IsChain (· ≤ ·) ({w, x, f} : Set P) :=
          isChain_triple (Or.inl hwx.le) (Or.inl (hwx.trans hlt).le) (Or.inl hlt.le)
        simpa [Finset.coe_insert] using this
      · grind

end SurfaceRank

end OrderComplex

/-! ### Connected links -/

/-- The link graph of the cell `v`: the cells strictly above `v`, joined when comparable. -/
def LinkAdj (v : P) (x y : P) : Prop := v < x ∧ v < y ∧ (x ≤ y ∨ y ≤ x)

/-- **The link of every vertex is connected.**  Together with the degree conditions of
`FiniteChains.ASC.SurfaceRank` — which make every link a disjoint union of cycles — this is the
condition which distinguishes a closed surface from a pinched one. -/
def LinkConnected (S : SurfaceRank P) : Prop :=
  ∀ v : P, S.rk v = 0 → ∀ x y : P, v < x → v < y → Relation.ReflTransGen (LinkAdj v) x y

/-- **A closed surface, as a cell poset**: the local conditions of a two-dimensional closed cell
structure together with connectedness of all vertex links. -/
structure ClosedSurfacePoset (P : Type u) [PartialOrder P] where
  /-- The local incidence conditions. -/
  toSurfaceRank : SurfaceRank P
  /-- All vertex links are connected. -/
  link_connected : LinkConnected toSurfaceRank

end ASC

end FiniteChains

namespace FiniteChains
namespace Davis

open Cell ASC

universe u

/-! ### Arithmetic of the boundary cycle -/

section FinAux

variable {M : ℕ} [NeZero M]

theorem succ_mod_eq (n m : ℕ) (h : n < m) : (n + 1) % m = if n + 1 = m then 0 else n + 1 := by
  split
  · next he => rw [he, Nat.mod_self]
  · next he => exact Nat.mod_eq_of_lt (by omega)

/-- The predecessor of a position of the boundary cycle. -/
def fpred (p : Fin M) : Fin M := ⟨(p.val + (M - 1)) % M, Nat.mod_lt _ (Nat.pos_of_neZero M)⟩

theorem fpred_val (p : Fin M) : (fpred p).val = if p.val = 0 then M - 1 else p.val - 1 := by
  have hM := Nat.pos_of_neZero M
  have h := p.isLt
  show (p.val + (M - 1)) % M = _
  split
  · next he => rw [he, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
  · next he =>
      have hrw : p.val + (M - 1) = M + (p.val - 1) := by omega
      rw [hrw, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

theorem fpred_add_one (p : Fin M) : fpred p + 1 = p := by
  have hM := Nat.pos_of_neZero M
  have h := p.isLt
  ext
  rw [fin_succ_val, fpred_val]
  split
  · next he => rw [succ_mod_eq _ _ (by omega), if_pos (by omega)]; omega
  · next he => rw [succ_mod_eq _ _ (by omega), if_neg (by omega)]; omega

theorem fin_add_one_injective (a b : Fin M) (hab : a + 1 = b + 1) : a = b := by simp_all

theorem fpred_succ (p : Fin M) : fpred (p + 1) = p :=
  fin_add_one_injective _ _ (fpred_add_one (p + 1))

theorem fin_succ_ne_self (hM : 2 ≤ M) (p : Fin M) : p + 1 ≠ p := by
  intro h
  simp_all

end FinAux

section Regular

variable {κ ι : Type u} {M : ℕ} [NeZero M] {vc : Fin M → κ} {ec : Fin M → ι}

/-- **The sides of the polygon are glued in pairs**: every edge of the surface comes from
exactly two positions of the boundary. -/
def EdgePairs (ec : Fin M → ι) : Prop :=
  ∀ i : Fin M, ∃ j : Fin M, j ≠ i ∧ ec j = ec i ∧ ∀ k : Fin M, ec k = ec i → k = i ∨ k = j

/-- **No side of the polygon becomes a loop**: the two endpoints of a side stay distinct after
the identification. -/
def NoLoopSide (vc : Fin M → κ) : Prop := ∀ i : Fin M, vc i ≠ vc (i + 1)

/-- The identification data of a polygon whose sides are glued in pairs. -/
structure PolygonData (vc : Fin M → κ) (ec : Fin M → ι) : Prop where
  /-- The polygon has at least three positions. -/
  three_le : 3 ≤ M
  /-- The sides are glued in pairs. -/
  pairs : EdgePairs ec
  /-- No side becomes a loop. -/
  noLoop : NoLoopSide vc
  /-- Every vertex of the surface occurs on the boundary. -/
  vc_surj : Function.Surjective vc
  /-- Every edge of the surface occurs on the boundary. -/
  ec_surj : Function.Surjective ec

variable (hc : Compat vc ec)

/-- In the face poset, `x < y` means that `x` is a proper face of `y`. -/
theorem lt_iff_plt {x y : Cell κ ι M} :
    (toS vc ec hc x < toS vc ec hc y) ↔ plt vc ec x y := by
  constructor
  · rintro ⟨hle, hnle⟩
    rcases hle with h | h
    · exact absurd (Or.inl h.symm) hnle
    · exact h
  · intro h
    refine lt_of_le_of_ne (Or.inr h) ?_
    intro he
    have hxy : x = y := he
    exact plt_irrefl (vc := vc) (ec := ec) x (hxy ▸ h)

/-! ### The faces of a cell -/

/-- The vertices of a boundary edge. -/
theorem lt_bed_iff {i : Fin M} {x : Cell κ ι M} :
    (toS vc ec hc x < toS vc ec hc (bed (ec i))) ↔ (x = vtx (vc i) ∨ x = vtx (vc (i + 1))) := by
  rw [lt_iff_plt]
  cases x with
  | vtx v =>
      simp
      constructor
      · rintro ⟨j, hj, hv⟩
        rcases hc j i hj with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hv with hv | hv
        · exact Or.inl (hv ▸ h1)
        · exact Or.inr (hv ▸ h2)
        · exact Or.inr (hv ▸ h1)
        · exact Or.inl (hv ▸ h2)
      · rintro (rfl | rfl)
        · exact ⟨i, rfl, Or.inl rfl⟩
        · exact ⟨i, rfl, Or.inr rfl⟩
  | _ => simp [plt]

/-- The vertices of a collar edge. -/
theorem lt_ced_iff {p : Fin M} {x : Cell κ ι M} :
    (toS vc ec hc x < toS vc ec hc (ced p)) ↔ (x = cvx p ∨ x = cvx (p + 1)) := by
  rw [lt_iff_plt]
  cases x <;> simp [plt]

/-- The vertices of the edge `dia p`. -/
theorem lt_dia_iff {p : Fin M} {x : Cell κ ι M} :
    (toS vc ec hc x < toS vc ec hc (dia p)) ↔ (x = vtx (vc p) ∨ x = cvx p) := by
  rw [lt_iff_plt]
  cases x <;> simp [plt, eq_comm]

/-- The vertices of the edge `gdi p`. -/
theorem lt_gdi_iff {p : Fin M} {x : Cell κ ι M} :
    (toS vc ec hc x < toS vc ec hc (gdi p)) ↔ (x = vtx (vc p) ∨ x = cvx (p + 1)) := by
  rw [lt_iff_plt]
  cases x <;> simp [plt, eq_comm]

/-- The vertices of a radius. -/
theorem lt_rad_iff {p : Fin M} {x : Cell κ ι M} :
    (toS vc ec hc x < toS vc ec hc (rad p)) ↔ (x = ctr ∨ x = cvx p) := by
  rw [lt_iff_plt]
  cases x <;> simp [plt]

/-- The faces through a boundary edge: the outer triangles at the positions carrying it. -/
theorem bed_lt_iff {i : Fin M} {y : Cell κ ι M} :
    (toS vc ec hc (bed (ec i)) < toS vc ec hc y) ↔ ∃ p : Fin M, ec p = ec i ∧ y = tr1 p := by
  rw [lt_iff_plt]
  cases y with
  | tr1 p =>
      constructor
      · intro h
        exact ⟨p, h.symm, rfl⟩
      · rintro ⟨p', hp', hy⟩
        have : p = p' := by injection hy
        exact (this ▸ hp').symm
  | _ => simp [plt]

/-- The faces through a collar edge. -/
theorem ced_lt_iff {p : Fin M} {y : Cell κ ι M} :
    (toS vc ec hc (ced p) < toS vc ec hc y) ↔ (y = tr2 p ∨ y = inn p) := by
  rw [lt_iff_plt]
  cases y <;> simp [plt, eq_comm]

/-- The faces through the edge `dia p`. -/
theorem dia_lt_iff {p : Fin M} {y : Cell κ ι M} :
    (toS vc ec hc (dia p) < toS vc ec hc y) ↔ (y = tr2 p ∨ y = tr1 (fpred p)) := by
  rw [lt_iff_plt]
  cases y with
  | tr1 s =>
      simp only [plt, Cell.tr1.injEq, reduceCtorEq, false_or]
      constructor
      · intro h; rw [h, fpred_succ]
      · intro h; rw [h, fpred_add_one]
  | tr2 s => simp [plt, eq_comm]
  | _ => simp [plt]

/-- The faces through the edge `gdi p`. -/
theorem gdi_lt_iff {p : Fin M} {y : Cell κ ι M} :
    (toS vc ec hc (gdi p) < toS vc ec hc y) ↔ (y = tr1 p ∨ y = tr2 p) := by
  rw [lt_iff_plt]
  cases y <;> simp [plt, eq_comm]

/-- The faces through a radius. -/
theorem rad_lt_iff {p : Fin M} {y : Cell κ ι M} :
    (toS vc ec hc (rad p) < toS vc ec hc y) ↔ (y = inn p ∨ y = inn (fpred p)) := by
  rw [lt_iff_plt]
  cases y with
  | inn s =>
      simp
      constructor
      · rintro (h | h)
        · exact Or.inl h.symm
        · exact Or.inr (by rw [h, fpred_succ])
      · rintro (h | h)
        · exact Or.inl h.symm
        · exact Or.inr (by rw [h, fpred_add_one])
  | _ => simp [plt]

/-- The proper faces of an outer triangle. -/
theorem lt_tr1_iff {p : Fin M} {x : Cell κ ι M} :
    (toS vc ec hc x < toS vc ec hc (tr1 p)) ↔
      (x = bed (ec p) ∨ x = dia (p + 1) ∨ x = gdi p ∨
        x = vtx (vc p) ∨ x = vtx (vc (p + 1)) ∨ x = cvx (p + 1)) := by
  rw [lt_iff_plt]
  cases x <;> simp [plt, eq_comm]

/-- The proper faces of an inner triangle of the collar. -/
theorem lt_tr2_iff {p : Fin M} {x : Cell κ ι M} :
    (toS vc ec hc x < toS vc ec hc (tr2 p)) ↔
      (x = ced p ∨ x = dia p ∨ x = gdi p ∨
        x = vtx (vc p) ∨ x = cvx p ∨ x = cvx (p + 1)) := by
  rw [lt_iff_plt]
  cases x <;> simp [plt, eq_comm]

/-- The proper faces of a triangle of the fan. -/
theorem lt_inn_iff {p : Fin M} {x : Cell κ ι M} :
    (toS vc ec hc x < toS vc ec hc (inn p)) ↔
      (x = ced p ∨ x = rad p ∨ x = rad (p + 1) ∨
        x = ctr ∨ x = cvx p ∨ x = cvx (p + 1)) := by
  rw [lt_iff_plt]
  cases x <;> simp [plt, eq_comm]

/-! ### The local closed surface conditions -/

/-! ### The incidence counts -/

theorem toS_inj {x y : Cell κ ι M} (h : toS vc ec hc x = toS vc ec hc y) : x = y := h

theorem fpred_ne_self (hM : 2 ≤ M) (p : Fin M) : fpred p ≠ p := by
  intro h
  have hp := fpred_add_one p
  simp_all

theorem not_lt_rk_zero {v z : Cell κ ι M} (hv : Cell.rk v = 0) (hz : Cell.rk z = 0)
    (h : toS vc ec hc v < toS vc ec hc z) : False := by
  have := rk_lt_of_plt ((lt_iff_plt hc).1 h)
  omega

/-- **Every edge of the surface has exactly two endpoints.** -/
theorem two_vertices_SCell (hd : PolygonData vc ec) :
    ∀ e : SCell vc ec hc, Cell.rk e = 1 → ExactlyTwo (fun v : SCell vc ec hc => v < e) := by
  have hM2 : 2 ≤ M := by have := hd.three_le; omega
  intro e he
  cases e with
  | bed e' =>
      obtain ⟨i, rfl⟩ := hd.ec_surj e'
      refine ⟨vtx (vc i), vtx (vc (i + 1)), ?_, (lt_bed_iff hc).2 (Or.inl rfl),
        (lt_bed_iff hc).2 (Or.inr rfl), fun z hz => (lt_bed_iff hc).1 hz⟩
      intro h
      exact hd.noLoop i (by injection toS_inj hc h)
  | ced p =>
      refine ⟨cvx p, cvx (p + 1), ?_, (lt_ced_iff hc).2 (Or.inl rfl),
        (lt_ced_iff hc).2 (Or.inr rfl), fun z hz => (lt_ced_iff hc).1 hz⟩
      intro h
      have h'  := toS_inj hc h
      injection h' with h''
      exact fin_succ_ne_self hM2 p h''.symm
  | dia p =>
      refine ⟨vtx (vc p), cvx p, ?_, (lt_dia_iff hc).2 (Or.inl rfl),
        (lt_dia_iff hc).2 (Or.inr rfl), fun z hz => (lt_dia_iff hc).1 hz⟩
      intro h
      exact absurd (toS_inj hc h) (by simp)
  | gdi p =>
      refine ⟨vtx (vc p), cvx (p + 1), ?_, (lt_gdi_iff hc).2 (Or.inl rfl),
        (lt_gdi_iff hc).2 (Or.inr rfl), fun z hz => (lt_gdi_iff hc).1 hz⟩
      intro h
      exact absurd (toS_inj hc h) (by simp)
  | rad p =>
      refine ⟨ctr, cvx p, ?_, (lt_rad_iff hc).2 (Or.inl rfl),
        (lt_rad_iff hc).2 (Or.inr rfl), fun z hz => (lt_rad_iff hc).1 hz⟩
      intro h
      exact absurd (toS_inj hc h) (by simp)
  | _ => simp [Cell.rk] at he

/-- **Every edge of the surface lies in exactly two triangles.** -/
theorem two_faces_SCell (hd : PolygonData vc ec) :
    ∀ e : SCell vc ec hc, Cell.rk e = 1 → ExactlyTwo (fun f : SCell vc ec hc => e < f) := by
  have hM2 : 2 ≤ M := by have := hd.three_le; omega
  intro e he
  cases e with
  | bed e' =>
      obtain ⟨i, rfl⟩ := hd.ec_surj e'
      obtain ⟨j, hji, hecj, huniq⟩ := hd.pairs i
      refine ⟨tr1 i, tr1 j, ?_, (bed_lt_iff hc).2 ⟨i, rfl, rfl⟩,
        (bed_lt_iff hc).2 ⟨j, hecj, rfl⟩, ?_⟩
      · intro h
        have h'  := toS_inj hc h
        injection h' with h''
        exact hji h''.symm
      · intro z hz
        obtain ⟨p, hp, rfl⟩ := (bed_lt_iff hc).1 hz
        rcases huniq p hp with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
  | ced p =>
      refine ⟨tr2 p, inn p, ?_, (ced_lt_iff hc).2 (Or.inl rfl),
        (ced_lt_iff hc).2 (Or.inr rfl), fun z hz => (ced_lt_iff hc).1 hz⟩
      intro h
      exact absurd (toS_inj hc h) (by simp)
  | dia p =>
      refine ⟨tr2 p, tr1 (fpred p), ?_, (dia_lt_iff hc).2 (Or.inl rfl),
        (dia_lt_iff hc).2 (Or.inr rfl), fun z hz => (dia_lt_iff hc).1 hz⟩
      intro h
      exact absurd (toS_inj hc h) (by simp)
  | gdi p =>
      refine ⟨tr1 p, tr2 p, ?_, (gdi_lt_iff hc).2 (Or.inl rfl),
        (gdi_lt_iff hc).2 (Or.inr rfl), fun z hz => (gdi_lt_iff hc).1 hz⟩
      intro h
      exact absurd (toS_inj hc h) (by simp)
  | rad p =>
      refine ⟨inn p, inn (fpred p), ?_, (rad_lt_iff hc).2 (Or.inl rfl),
        (rad_lt_iff hc).2 (Or.inr rfl), fun z hz => (rad_lt_iff hc).1 hz⟩
      intro h
      have h'  := toS_inj hc h
      injection h' with h''
      exact fpred_ne_self hM2 p h''.symm
  | _ => simp [Cell.rk] at he

/-- **Every vertex of a triangle lies in exactly two of its edges.** -/
theorem two_edges_SCell (hd : PolygonData vc ec) :
    ∀ v f : SCell vc ec hc, Cell.rk v = 0 → Cell.rk f = 2 → v < f →
      ExactlyTwo (fun e : SCell vc ec hc => v < e ∧ e < f) := by
  have hM2 : 2 ≤ M := by have := hd.three_le; omega
  have hsucc : ∀ p : Fin M, (cvx p : SCell vc ec hc) ≠ cvx (p + 1) := by
    intro p h
    have h'  := toS_inj hc h
    injection h' with h3
    exact absurd h3.symm (fin_succ_ne_self hM2 p)
  intro v f hv hf hvf
  cases f with
  | tr1 p =>
      rcases (lt_tr1_iff hc).1 hvf with h | h | h | h | h | h <;> subst h
      · simp [Cell.rk] at hv
      · simp [Cell.rk] at hv
      · simp [Cell.rk] at hv
      · -- `v` is the initial vertex of the boundary edge
        refine ⟨bed (ec p), gdi p, by intro h; exact absurd (toS_inj hc h) (by simp),
          ⟨(lt_bed_iff hc).2 (Or.inl rfl), (lt_tr1_iff hc).2 (Or.inl rfl)⟩,
          ⟨(lt_gdi_iff hc).2 (Or.inl rfl), (lt_tr1_iff hc).2 (Or.inr (Or.inr (Or.inl rfl)))⟩, ?_⟩
        rintro z ⟨hz1, hz2⟩
        rcases (lt_tr1_iff hc).1 hz2 with h | h | h | h | h | h <;> subst h
        · exact Or.inl rfl
        · rcases (lt_dia_iff hc).1 hz1 with h' | h'
          · exact absurd (hd.noLoop p) (by simpa using (toS_inj hc h'))
          · exact absurd (toS_inj hc h') (by simp)
        · exact Or.inr rfl
        · exact absurd hz1 (lt_irrefl _)
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
      · -- `v` is the terminal vertex of the boundary edge
        refine ⟨bed (ec p), dia (p + 1), by intro h; exact absurd (toS_inj hc h) (by simp),
          ⟨(lt_bed_iff hc).2 (Or.inr rfl), (lt_tr1_iff hc).2 (Or.inl rfl)⟩,
          ⟨(lt_dia_iff hc).2 (Or.inl rfl), (lt_tr1_iff hc).2 (Or.inr (Or.inl rfl))⟩, ?_⟩
        rintro z ⟨hz1, hz2⟩
        rcases (lt_tr1_iff hc).1 hz2 with h | h | h | h | h | h <;> subst h
        · exact Or.inl rfl
        · exact Or.inr rfl
        · rcases (lt_gdi_iff hc).1 hz1 with h' | h'
          · exact absurd (hd.noLoop p) (by simpa using (toS_inj hc h').symm)
          · exact absurd (toS_inj hc h') (by simp)
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
        · exact absurd hz1 (lt_irrefl _)
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
      · -- `v` is the collar vertex
        refine ⟨dia (p + 1), gdi p, by intro h; exact absurd (toS_inj hc h) (by simp),
          ⟨(lt_dia_iff hc).2 (Or.inr rfl), (lt_tr1_iff hc).2 (Or.inr (Or.inl rfl))⟩,
          ⟨(lt_gdi_iff hc).2 (Or.inr rfl), (lt_tr1_iff hc).2 (Or.inr (Or.inr (Or.inl rfl)))⟩, ?_⟩
        rintro z ⟨hz1, hz2⟩
        rcases (lt_tr1_iff hc).1 hz2 with h | h | h | h | h | h <;> subst h
        · rcases (lt_bed_iff hc).1 hz1 with h' | h' <;> exact absurd (toS_inj hc h') (by simp)
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
        · exact absurd hz1 (lt_irrefl _)
  | tr2 p =>
      rcases (lt_tr2_iff hc).1 hvf with h | h | h | h | h | h <;> subst h
      · simp [Cell.rk] at hv
      · simp [Cell.rk] at hv
      · simp [Cell.rk] at hv
      · -- `v` is the boundary vertex
        refine ⟨dia p, gdi p, by intro h; exact absurd (toS_inj hc h) (by simp),
          ⟨(lt_dia_iff hc).2 (Or.inl rfl), (lt_tr2_iff hc).2 (Or.inr (Or.inl rfl))⟩,
          ⟨(lt_gdi_iff hc).2 (Or.inl rfl), (lt_tr2_iff hc).2 (Or.inr (Or.inr (Or.inl rfl)))⟩, ?_⟩
        rintro z ⟨hz1, hz2⟩
        rcases (lt_tr2_iff hc).1 hz2 with h | h | h | h | h | h <;> subst h
        · rcases (lt_ced_iff hc).1 hz1 with h' | h' <;> exact absurd (toS_inj hc h') (by simp)
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd hz1 (lt_irrefl _)
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
      · -- `v` is the collar vertex at `p`
        refine ⟨ced p, dia p, by intro h; exact absurd (toS_inj hc h) (by simp),
          ⟨(lt_ced_iff hc).2 (Or.inl rfl), (lt_tr2_iff hc).2 (Or.inl rfl)⟩,
          ⟨(lt_dia_iff hc).2 (Or.inr rfl), (lt_tr2_iff hc).2 (Or.inr (Or.inl rfl))⟩, ?_⟩
        rintro z ⟨hz1, hz2⟩
        rcases (lt_tr2_iff hc).1 hz2 with h | h | h | h | h | h <;> subst h
        · exact Or.inl rfl
        · exact Or.inr rfl
        · rcases (lt_gdi_iff hc).1 hz1 with h' | h'
          · exact absurd (toS_inj hc h') (by simp)
          · exact absurd h' (hsucc p)
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
        · exact absurd hz1 (lt_irrefl _)
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
      · -- `v` is the collar vertex at `p+1`
        refine ⟨ced p, gdi p, by intro h; exact absurd (toS_inj hc h) (by simp),
          ⟨(lt_ced_iff hc).2 (Or.inr rfl), (lt_tr2_iff hc).2 (Or.inl rfl)⟩,
          ⟨(lt_gdi_iff hc).2 (Or.inr rfl), (lt_tr2_iff hc).2 (Or.inr (Or.inr (Or.inl rfl)))⟩, ?_⟩
        rintro z ⟨hz1, hz2⟩
        rcases (lt_tr2_iff hc).1 hz2 with h | h | h | h | h | h <;> subst h
        · exact Or.inl rfl
        · rcases (lt_dia_iff hc).1 hz1 with h' | h'
          · exact absurd (toS_inj hc h') (by simp)
          · exact absurd h'.symm (hsucc p)
        · exact Or.inr rfl
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
        · exact absurd hz1 (lt_irrefl _)
  | inn p =>
      rcases (lt_inn_iff hc).1 hvf with h | h | h | h | h | h <;> subst h
      · simp [Cell.rk] at hv
      · simp [Cell.rk] at hv
      · simp [Cell.rk] at hv
      · -- `v` is the centre
        refine ⟨rad p, rad (p + 1), ?_,
          ⟨(lt_rad_iff hc).2 (Or.inl rfl), (lt_inn_iff hc).2 (Or.inr (Or.inl rfl))⟩,
          ⟨(lt_rad_iff hc).2 (Or.inl rfl), (lt_inn_iff hc).2 (Or.inr (Or.inr (Or.inl rfl)))⟩, ?_⟩
        · intro h
          have h'  := toS_inj hc h
          injection h' with h3
          exact absurd h3.symm (fin_succ_ne_self hM2 p)
        rintro z ⟨hz1, hz2⟩
        rcases (lt_inn_iff hc).1 hz2 with h | h | h | h | h | h <;> subst h
        · rcases (lt_ced_iff hc).1 hz1 with h' | h' <;> exact absurd (toS_inj hc h') (by simp)
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd hz1 (lt_irrefl _)
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
      · -- `v` is the collar vertex at `p`
        refine ⟨ced p, rad p, by intro h; exact absurd (toS_inj hc h) (by simp),
          ⟨(lt_ced_iff hc).2 (Or.inl rfl), (lt_inn_iff hc).2 (Or.inl rfl)⟩,
          ⟨(lt_rad_iff hc).2 (Or.inr rfl), (lt_inn_iff hc).2 (Or.inr (Or.inl rfl))⟩, ?_⟩
        rintro z ⟨hz1, hz2⟩
        rcases (lt_inn_iff hc).1 hz2 with h | h | h | h | h | h <;> subst h
        · exact Or.inl rfl
        · exact Or.inr rfl
        · rcases (lt_rad_iff hc).1 hz1 with h' | h'
          · exact absurd (toS_inj hc h') (by simp)
          · exact absurd h' (hsucc p)
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
        · exact absurd hz1 (lt_irrefl _)
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
      · -- `v` is the collar vertex at `p+1`
        refine ⟨ced p, rad (p + 1), by intro h; exact absurd (toS_inj hc h) (by simp),
          ⟨(lt_ced_iff hc).2 (Or.inr rfl), (lt_inn_iff hc).2 (Or.inl rfl)⟩,
          ⟨(lt_rad_iff hc).2 (Or.inr rfl), (lt_inn_iff hc).2 (Or.inr (Or.inr (Or.inl rfl)))⟩, ?_⟩
        rintro z ⟨hz1, hz2⟩
        rcases (lt_inn_iff hc).1 hz2 with h | h | h | h | h | h <;> subst h
        · exact Or.inl rfl
        · rcases (lt_rad_iff hc).1 hz1 with h' | h'
          · exact absurd (toS_inj hc h') (by simp)
          · exact absurd h'.symm (hsucc p)
        · exact Or.inr rfl
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
        · exact absurd (not_lt_rk_zero hc hv rfl hz1) not_false
        · exact absurd hz1 (lt_irrefl _)
  | _ => simp [Cell.rk] at hf

/-- Every cell of the surface is a face of a triangle. -/
theorem exists_face_SCell (hd : PolygonData vc ec) :
    ∀ x : SCell vc ec hc, ∃ f : SCell vc ec hc, Cell.rk f = 2 ∧ x ≤ f := by
  intro x
  cases x with
  | vtx v =>
      obtain ⟨i, rfl⟩ := hd.vc_surj v
      exact ⟨tr1 i, rfl, le_of_lt ((lt_tr1_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩
  | bed e =>
      obtain ⟨i, rfl⟩ := hd.ec_surj e
      exact ⟨tr1 i, rfl, le_of_lt ((lt_tr1_iff hc).2 (Or.inl rfl))⟩
  | cvx p =>
      exact ⟨tr2 p, rfl,
        le_of_lt ((lt_tr2_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))⟩
  | ced p => exact ⟨tr2 p, rfl, le_of_lt ((lt_tr2_iff hc).2 (Or.inl rfl))⟩
  | dia p => exact ⟨tr2 p, rfl, le_of_lt ((lt_tr2_iff hc).2 (Or.inr (Or.inl rfl)))⟩
  | gdi p => exact ⟨tr2 p, rfl, le_of_lt ((lt_tr2_iff hc).2 (Or.inr (Or.inr (Or.inl rfl))))⟩
  | tr1 p => exact ⟨tr1 p, rfl, le_refl _⟩
  | tr2 p => exact ⟨tr2 p, rfl, le_refl _⟩
  | ctr =>
      exact ⟨inn 0, rfl, le_of_lt ((lt_inn_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩
  | rad p => exact ⟨inn p, rfl, le_of_lt ((lt_inn_iff hc).2 (Or.inr (Or.inl rfl)))⟩
  | inn p => exact ⟨inn p, rfl, le_refl _⟩

/-- Every triangle of the surface has a vertex. -/
theorem exists_vertex_SCell :
    ∀ f : SCell vc ec hc, Cell.rk f = 2 → ∃ v : SCell vc ec hc, Cell.rk v = 0 ∧ v < f := by
  intro f hf
  cases f with
  | tr1 p =>
      exact ⟨vtx (vc p), rfl, (lt_tr1_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
  | tr2 p =>
      exact ⟨vtx (vc p), rfl, (lt_tr2_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
  | inn p => exact ⟨ctr, rfl, (lt_inn_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
  | _ => simp [Cell.rk] at hf

/-- **The face poset of a polygon with identified sides satisfies the local conditions of a
two-dimensional closed cell structure**: every edge has exactly two endpoints, every edge lies
in exactly two triangles, and every vertex of a triangle lies in exactly two of its edges. -/
def surfaceRank_SCell (hd : PolygonData vc ec) : SurfaceRank (SCell vc ec hc) where
  rk := Cell.rk
  rk_lt_of_lt := by
    intro x y h
    exact rk_lt_of_plt ((lt_iff_plt hc).1 h)
  rk_le_two := rk_le_two
  two_vertices := two_vertices_SCell hc hd
  two_faces := two_faces_SCell hc hd
  two_edges := two_edges_SCell hc hd
  exists_face := exists_face_SCell hc hd
  exists_vertex := exists_vertex_SCell hc

/-- **Every edge of the subdivision of the surface lies in exactly two triangles.** -/
theorem edgeInTwoTriangles_SCell [DecidableEq κ] [DecidableEq ι] (hd : PolygonData vc ec) :
    EdgeInTwoTriangles (orderComplex (SCell vc ec hc)) :=
  (surfaceRank_SCell hc hd).edgeInTwoTriangles

end Regular

end Davis
end FiniteChains

namespace FiniteChains
namespace Davis

open Cell ASC Relation

universe u

section Link

variable {κ ι : Type u} {M : ℕ} [NeZero M] {vc : Fin M → κ} {ec : Fin M → ι}
variable (hc : Compat vc ec)

/-! ### Elementary steps of a link -/

theorem linkAdj_symmetric (v : SCell vc ec hc) : Symmetric (LinkAdj v) := by
  rintro x y ⟨h1, h2, h3⟩
  exact ⟨h2, h1, h3.symm⟩

theorem linkAdj_of_lt {v x y : SCell vc ec hc} (hx : v < x) (hy : v < y) (h : x ≤ y) :
    LinkAdj v x y := ⟨hx, hy, Or.inl h⟩

/-! ### The link of the centre -/

theorem ctr_lt_iff {y : Cell κ ι M} :
    (toS vc ec hc ctr < toS vc ec hc y) ↔ (∃ p : Fin M, y = rad p ∨ y = inn p) := by
  rw [lt_iff_plt]
  cases y <;> simp [plt]

theorem ctr_lt_rad (r : Fin M) : toS vc ec hc ctr < toS vc ec hc (rad r) :=
  (lt_rad_iff hc).2 (Or.inl rfl)

theorem ctr_lt_inn (r : Fin M) : toS vc ec hc ctr < toS vc ec hc (inn r) :=
  (lt_inn_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))


theorem conn_rad (n : ℕ) : ∀ p : Fin M, p.val = n →
    ReflTransGen (LinkAdj (toS vc ec hc ctr)) (toS vc ec hc (rad 0)) (toS vc ec hc (rad p)) := by
  induction n with
  | zero => grind
  | succ n ih =>
      intro p hp
      have hM := Nat.pos_of_neZero M
      have h1 : (fpred p).val = n := by
        rw [fpred_val, if_neg (by omega)]
        omega
      have h2 := ih (fpred p) h1
      have h3  := fpred_add_one p
      have h4 := (by
        have s1  :=
          linkAdj_of_lt hc (ctr_lt_rad hc (fpred p)) (ctr_lt_inn hc (fpred p))
            (le_of_lt ((lt_inn_iff hc).2 (Or.inr (Or.inl rfl))))
        have s2 : LinkAdj (toS vc ec hc ctr) (toS vc ec hc (inn (fpred p))) (toS vc ec hc (rad ((fpred p) + 1))) :=
          ⟨ctr_lt_inn hc (fpred p), ctr_lt_rad hc _,
            Or.inr (le_of_lt ((lt_inn_iff hc).2 (Or.inr (Or.inr (Or.inl rfl)))))⟩
        exact (ReflTransGen.single s1).tail s2)
      rw [h3] at h4
      exact h2.trans h4

theorem reflTransGen_symm {α : Type*} {r : α → α → Prop}
    (hr : Symmetric r) {a b : α} (h : ReflTransGen r a b) : ReflTransGen r b a := by
  letI : Std.Symm r := ⟨fun _ _ h => hr h⟩
  exact Relation.ReflTransGen.stdSymm.symm _ _ h

/-- **The link of the centre of the polygon is connected**: it is the cycle of the collar. -/
theorem link_connected_ctr (x y : SCell vc ec hc) (hx : toS vc ec hc ctr < x)
    (hy : toS vc ec hc ctr < y) : ReflTransGen (LinkAdj (toS vc ec hc ctr)) x y := by
  have key : ∀ z : Cell κ ι M, toS vc ec hc ctr < toS vc ec hc z →
      ReflTransGen (LinkAdj (toS vc ec hc ctr)) (toS vc ec hc (rad 0)) (toS vc ec hc z) := by
    intro z hz
    obtain ⟨p, hp | hp⟩ := (ctr_lt_iff hc).1 hz
    · subst hp; exact conn_rad hc p.val p rfl
    · subst hp
      refine (conn_rad hc p.val p rfl).tail ?_
      exact linkAdj_of_lt hc (ctr_lt_rad hc p) (ctr_lt_inn hc p)
        (le_of_lt ((lt_inn_iff hc).2 (Or.inr (Or.inl rfl))))
  exact (reflTransGen_symm (linkAdj_symmetric hc _) (key x hx)).trans (key y hy)

/-! ### The link of a collar vertex -/

theorem cvx_lt_iff {p : Fin M} {y : Cell κ ι M} :
    (toS vc ec hc (cvx p) < toS vc ec hc y) ↔
      (y = ced p ∨ y = ced (fpred p) ∨ y = dia p ∨ y = gdi (fpred p) ∨ y = rad p ∨
        y = tr1 (fpred p) ∨ y = tr2 p ∨ y = tr2 (fpred p) ∨ y = inn p ∨ y = inn (fpred p)) := by
  rw [lt_iff_plt]
  have key : ∀ r : Fin M, (p = r + 1) ↔ (r = fpred p) := by
    intro r
    constructor
    · intro h; rw [h, fpred_succ]
    · intro h; rw [h, fpred_add_one]
  cases y <;> simp [plt, key, eq_comm]

/-- **The link of a collar vertex is connected**: it is the cycle of the ten cells through it. -/
theorem link_connected_cvx (q : Fin M) (x y : SCell vc ec hc)
    (hx : toS vc ec hc (cvx (q + 1)) < x) (hy : toS vc ec hc (cvx (q + 1)) < y) :
    ReflTransGen (LinkAdj (toS vc ec hc (cvx (q + 1)))) x y := by
  set v : SCell vc ec hc := toS vc ec hc (cvx (q + 1)) with hv
  have hced1 : v < toS vc ec hc (ced (q + 1)) := (lt_ced_iff hc).2 (Or.inl rfl)
  have hced0 : v < toS vc ec hc (ced q) := (lt_ced_iff hc).2 (Or.inr rfl)
  have hdia : v < toS vc ec hc (dia (q + 1)) := (lt_dia_iff hc).2 (Or.inr rfl)
  have hgdi : v < toS vc ec hc (gdi q) := (lt_gdi_iff hc).2 (Or.inr rfl)
  have hrad : v < toS vc ec hc (rad (q + 1)) := (lt_rad_iff hc).2 (Or.inr rfl)
  have htr1 : v < toS vc ec hc (tr1 q) :=
    (lt_tr1_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  have htr2a : v < toS vc ec hc (tr2 (q + 1)) :=
    (lt_tr2_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have htr2b : v < toS vc ec hc (tr2 q) :=
    (lt_tr2_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  have hinna : v < toS vc ec hc (inn (q + 1)) :=
    (lt_inn_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hinnb : v < toS vc ec hc (inn q) :=
    (lt_inn_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  have key : ∀ z : Cell κ ι M, v < toS vc ec hc z →
      ReflTransGen (LinkAdj v) (toS vc ec hc z) (toS vc ec hc (ced (q + 1))) := by
    intro z hz
    have e_tr2a : ReflTransGen (LinkAdj v) (toS vc ec hc (tr2 (q + 1)))
        (toS vc ec hc (ced (q + 1))) :=
      ReflTransGen.single ((linkAdj_symmetric hc v)
        (linkAdj_of_lt hc hced1 htr2a (le_of_lt ((lt_tr2_iff hc).2 (Or.inl rfl)))))
    have e_dia : ReflTransGen (LinkAdj v) (toS vc ec hc (dia (q + 1)))
        (toS vc ec hc (ced (q + 1))) :=
      (ReflTransGen.single (linkAdj_of_lt hc hdia htr2a
        (le_of_lt ((lt_tr2_iff hc).2 (Or.inr (Or.inl rfl)))))).trans e_tr2a
    have e_inna : ReflTransGen (LinkAdj v) (toS vc ec hc (inn (q + 1)))
        (toS vc ec hc (ced (q + 1))) :=
      ReflTransGen.single ((linkAdj_symmetric hc v)
        (linkAdj_of_lt hc hced1 hinna (le_of_lt ((lt_inn_iff hc).2 (Or.inl rfl)))))
    have e_rad : ReflTransGen (LinkAdj v) (toS vc ec hc (rad (q + 1)))
        (toS vc ec hc (ced (q + 1))) :=
      (ReflTransGen.single (linkAdj_of_lt hc hrad hinna
        (le_of_lt ((lt_inn_iff hc).2 (Or.inr (Or.inl rfl)))))).trans e_inna
    have e_innb : ReflTransGen (LinkAdj v) (toS vc ec hc (inn q))
        (toS vc ec hc (ced (q + 1))) :=
      (ReflTransGen.single ((linkAdj_symmetric hc v) (linkAdj_of_lt hc hrad hinnb
        (le_of_lt ((lt_inn_iff hc).2 (Or.inr (Or.inr (Or.inl rfl)))))))).trans e_rad
    have e_ced0 : ReflTransGen (LinkAdj v) (toS vc ec hc (ced q))
        (toS vc ec hc (ced (q + 1))) :=
      (ReflTransGen.single (linkAdj_of_lt hc hced0 hinnb
        (le_of_lt ((lt_inn_iff hc).2 (Or.inl rfl))))).trans e_innb
    have e_tr2b : ReflTransGen (LinkAdj v) (toS vc ec hc (tr2 q))
        (toS vc ec hc (ced (q + 1))) :=
      (ReflTransGen.single ((linkAdj_symmetric hc v) (linkAdj_of_lt hc hced0 htr2b
        (le_of_lt ((lt_tr2_iff hc).2 (Or.inl rfl)))))).trans e_ced0
    have e_gdi : ReflTransGen (LinkAdj v) (toS vc ec hc (gdi q))
        (toS vc ec hc (ced (q + 1))) :=
      (ReflTransGen.single (linkAdj_of_lt hc hgdi htr2b
        (le_of_lt ((lt_tr2_iff hc).2 (Or.inr (Or.inr (Or.inl rfl))))))).trans e_tr2b
    have e_tr1 : ReflTransGen (LinkAdj v) (toS vc ec hc (tr1 q))
        (toS vc ec hc (ced (q + 1))) :=
      (ReflTransGen.single ((linkAdj_symmetric hc v) (linkAdj_of_lt hc hgdi htr1
        (le_of_lt ((lt_tr1_iff hc).2 (Or.inr (Or.inr (Or.inl rfl)))))))).trans e_gdi
    have hcases := (cvx_lt_iff hc).1 hz
    rw [fpred_succ] at hcases
    rcases hcases with h | h | h | h | h | h | h | h | h | h <;> subst h
    · rfl
    · exact e_ced0
    · exact e_dia
    · exact e_gdi
    · exact e_rad
    · exact e_tr1
    · exact e_tr2a
    · exact e_tr2b
    · exact e_inna
    · exact e_innb
  exact (key x hx).trans (reflTransGen_symm (linkAdj_symmetric hc v) (key y hy))

/-! ### The cells at a corner of the polygon -/



theorem vtx_lt_tr1_out {w : κ} {i : Fin M} (hi : vc i = w) :
    toS vc ec hc (vtx w) < toS vc ec hc (tr1 i) :=
  (lt_tr1_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hi])))))

theorem vtx_lt_tr1_in {w : κ} {i : Fin M} (hi : vc i = w) :
    toS vc ec hc (vtx w) < toS vc ec hc (tr1 (fpred i)) := by simp_all [fpred_add_one, hi, lt_tr1_iff]

theorem vtx_lt_gdi {w : κ} {i : Fin M} (hi : vc i = w) :
    toS vc ec hc (vtx w) < toS vc ec hc (gdi i) :=
  (lt_gdi_iff hc).2 (Or.inl (by rw [hi]))

theorem vtx_lt_dia {w : κ} {i : Fin M} (hi : vc i = w) :
    toS vc ec hc (vtx w) < toS vc ec hc (dia i) :=
  (lt_dia_iff hc).2 (Or.inl (by rw [hi]))

theorem vtx_lt_tr2 {w : κ} {i : Fin M} (hi : vc i = w) :
    toS vc ec hc (vtx w) < toS vc ec hc (tr2 i) :=
  (lt_tr2_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hi])))))

/-! ### Going around one corner of the polygon -/

theorem conn_tr1_bed {w : κ} {i : Fin M} (hi : vc i = w) :
    ReflTransGen (LinkAdj (toS vc ec hc (vtx w))) (toS vc ec hc (tr1 i))
      (toS vc ec hc (bed (ec i))) :=
  ReflTransGen.single ((linkAdj_symmetric hc _)
    (linkAdj_of_lt hc ((lt_bed_iff hc).2 (Or.inl (by rw [hi]))) (vtx_lt_tr1_out hc hi)
      (le_of_lt ((lt_tr1_iff hc).2 (Or.inl rfl)))))

theorem conn_gdi_bed {w : κ} {i : Fin M} (hi : vc i = w) :
    ReflTransGen (LinkAdj (toS vc ec hc (vtx w))) (toS vc ec hc (gdi i))
      (toS vc ec hc (bed (ec i))) :=
  (ReflTransGen.single (linkAdj_of_lt hc (vtx_lt_gdi hc hi) (vtx_lt_tr1_out hc hi)
    (le_of_lt ((lt_tr1_iff hc).2 (Or.inr (Or.inr (Or.inl rfl))))))).trans (conn_tr1_bed hc hi)

theorem conn_tr2_bed {w : κ} {i : Fin M} (hi : vc i = w) :
    ReflTransGen (LinkAdj (toS vc ec hc (vtx w))) (toS vc ec hc (tr2 i))
      (toS vc ec hc (bed (ec i))) :=
  (ReflTransGen.single ((linkAdj_symmetric hc _) (linkAdj_of_lt hc (vtx_lt_gdi hc hi)
    (vtx_lt_tr2 hc hi)
    (le_of_lt ((lt_tr2_iff hc).2 (Or.inr (Or.inr (Or.inl rfl)))))))).trans (conn_gdi_bed hc hi)

theorem conn_dia_bed {w : κ} {i : Fin M} (hi : vc i = w) :
    ReflTransGen (LinkAdj (toS vc ec hc (vtx w))) (toS vc ec hc (dia i))
      (toS vc ec hc (bed (ec i))) :=
  (ReflTransGen.single (linkAdj_of_lt hc (vtx_lt_dia hc hi) (vtx_lt_tr2 hc hi)
    (le_of_lt ((lt_tr2_iff hc).2 (Or.inr (Or.inl rfl)))))).trans (conn_tr2_bed hc hi)

theorem conn_tr1in_bed {w : κ} {i : Fin M} (hi : vc i = w) :
    ReflTransGen (LinkAdj (toS vc ec hc (vtx w))) (toS vc ec hc (tr1 (fpred i)))
      (toS vc ec hc (bed (ec i))) := by
  refine (ReflTransGen.single ((linkAdj_symmetric hc _) (linkAdj_of_lt hc (vtx_lt_dia hc hi)
    (vtx_lt_tr1_in hc hi) ?_))).trans (conn_dia_bed hc hi)
  refine le_of_lt ((lt_tr1_iff hc).2 (Or.inr (Or.inl ?_)))
  rw [fpred_add_one]

/-- **The two sides of the polygon at one corner are joined inside the link.** -/
theorem conn_bedin_bed {w : κ} {i : Fin M} (hi : vc i = w) :
    ReflTransGen (LinkAdj (toS vc ec hc (vtx w))) (toS vc ec hc (bed (ec (fpred i))))
      (toS vc ec hc (bed (ec i))) :=
  (ReflTransGen.single (linkAdj_of_lt hc (by
    refine (lt_bed_iff hc).2 (Or.inr ?_)
    rw [fpred_add_one, hi]) (vtx_lt_tr1_in hc hi)
    (le_of_lt ((lt_tr1_iff hc).2 (Or.inl rfl))))).trans (conn_tr1in_bed hc hi)

/-- Every cell through a vertex of the identified boundary is joined, inside the link, to the
side of the polygon at one of the corners over that vertex. -/
theorem conn_to_bed {w : κ} (z : Cell κ ι M) (hz : toS vc ec hc (vtx w) < toS vc ec hc z) :
    ∃ i : Fin M, vc i = w ∧ ReflTransGen (LinkAdj (toS vc ec hc (vtx w))) (toS vc ec hc z)
      (toS vc ec hc (bed (ec i))) := by
  rw [lt_iff_plt] at hz
  cases z with
  | bed e =>
      obtain ⟨j, hj, hv⟩ := hz
      subst hj
      rcases hv with hv | hv
      · grind
      · refine ⟨j + 1, hv, ?_⟩
        have hb := conn_bedin_bed hc hv
        rwa [fpred_succ] at hb
  | dia p => exact ⟨p, hz, conn_dia_bed hc hz⟩
  | gdi p => exact ⟨p, hz, conn_gdi_bed hc hz⟩
  | tr2 p => exact ⟨p, hz, conn_tr2_bed hc hz⟩
  | tr1 p =>
      rcases hz with hv | hv
      · exact ⟨p, hv, conn_tr1_bed hc hv⟩
      · refine ⟨p + 1, hv, ?_⟩
        have hb := conn_tr1in_bed hc hv
        rwa [fpred_succ] at hb
  | _ => simp [plt] at hz

/-! ### Passing from one corner to the next -/

/-- **Two corners of the polygon at the same vertex sharing a side**: the positions `i` and `j`
carry the same vertex, and one of the two sides through `i` is identified with one of the two
sides through `j`. -/
def CornerAdj (vc : Fin M → κ) (ec : Fin M → ι) (i j : Fin M) : Prop :=
  vc i = vc j ∧ (ec i = ec j ∨ ec i = ec (fpred j) ∨ ec (fpred i) = ec j ∨
    ec (fpred i) = ec (fpred j))

theorem cornerAdj_symm {i j : Fin M} (h : CornerAdj vc ec i j) : CornerAdj vc ec j i := by grind [CornerAdj]

theorem vc_eq_of_reflTransGen {i j : Fin M} (h : ReflTransGen (CornerAdj vc ec) i j) :
    vc i = vc j := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans hstep.1

/-- **The corners of the polygon over one vertex of the surface form a single cycle.** -/
def CornersConnected (vc : Fin M → κ) (ec : Fin M → ι) : Prop :=
  ∀ i j : Fin M, vc i = vc j → ReflTransGen (CornerAdj vc ec) i j


theorem conn_corner {w : κ} {i j : Fin M} (hi : vc i = w)
    (h : ReflTransGen (CornerAdj vc ec) i j) :
    ReflTransGen (LinkAdj (toS vc ec hc (vtx w))) (toS vc ec hc (bed (ec i)))
      (toS vc ec hc (bed (ec j))) := by
  induction h with
  | refl => rfl
  | @tail b c hib hbc ih =>
      have hb  := (vc_eq_of_reflTransGen hib).symm.trans hi
      have hcv  := hbc.1.symm.trans hb
      exact (ih).trans (by
        obtain ⟨-, hh⟩ := hbc
        rcases hh with hbc | hbc | hbc | hbc
        · grind
        · rw [hbc]
          exact conn_bedin_bed hc hcv
        · have hb := conn_bedin_bed hc hb
          rw [hbc] at hb
          exact reflTransGen_symm (linkAdj_symmetric hc _) hb
        · have hb := conn_bedin_bed hc hb
          rw [hbc] at hb
          exact (reflTransGen_symm (linkAdj_symmetric hc _) hb).trans (conn_bedin_bed hc hcv))

/-- **The link of a vertex of the identified boundary is connected.** -/
theorem link_connected_vtx (hcorners : CornersConnected vc ec) (w : κ) (x y : SCell vc ec hc)
    (hx : toS vc ec hc (vtx w) < x) (hy : toS vc ec hc (vtx w) < y) :
    ReflTransGen (LinkAdj (toS vc ec hc (vtx w))) x y := by
  obtain ⟨i, hi, hxi⟩ := conn_to_bed hc x hx
  obtain ⟨j, hj, hyj⟩ := conn_to_bed hc y hy
  have hij  := hcorners i j (by rw [hi, hj])
  exact (hxi.trans (conn_corner hc hi hij)).trans
    (reflTransGen_symm (linkAdj_symmetric hc _) hyj)

/-! ### The closed surface -/

/-- **Every vertex link of the subdivision of the surface is connected.** -/
theorem linkConnected_SCell (hd : PolygonData vc ec) (hcorners : CornersConnected vc ec) :
    LinkConnected (surfaceRank_SCell hc hd) := by
  intro v hv x y hx hy
  cases v with
  | vtx w => exact link_connected_vtx hc hcorners w x y hx hy
  | cvx p =>
      have hp  := fpred_add_one p
      rw [← hp] at hx hy ⊢
      exact link_connected_cvx hc (fpred p) x y hx hy
  | ctr => exact link_connected_ctr hc x y hx hy
  | _ => simp [surfaceRank_SCell, Cell.rk] at hv

/-- **The polygon with identified sides is a closed surface**: the local incidence conditions
hold and all vertex links are connected. -/
def closedSurfacePoset_SCell (hd : PolygonData vc ec) (hcorners : CornersConnected vc ec) :
    ClosedSurfacePoset (SCell vc ec hc) where
  toSurfaceRank := surfaceRank_SCell hc hd
  link_connected := linkConnected_SCell hc hd hcorners

end Link

end Davis
end FiniteChains

namespace FiniteChains
namespace Davis

open Cell ASC Relation Genus

section GenusSurface

variable (q : ℕ) [NeZero q]

/-! ### Reading the labels -/

omit [NeZero q] in
/-- Two positions of the boundary carry the same edge of the surface exactly when they agree on
the commutator, on the letter, and on the half of the side. -/
theorem gec_eq_iff' (m n : Fin (8 * q)) :
    gec q m = gec q n ↔
      (m.val / 2 / 4 = n.val / 2 / 4 ∧
        m.val / 2 % 4 % 2 = n.val / 2 % 4 % 2 ∧
        (m.val % 2 + (if 2 ≤ m.val / 2 % 4 then 1 else 0)) % 2
          = (n.val % 2 + (if 2 ≤ n.val / 2 % 4 then 1 else 0)) % 2) := by
  have hm2 : m.val % 2 = 0 ∨ m.val % 2 = 1 := by omega
  have hn2 : n.val % 2 = 0 ∨ n.val % 2 = 1 := by omega
  by_cases h2 : 2 ≤ m.val / 2 % 4 <;> by_cases h4 : 2 ≤ n.val / 2 % 4 <;>
    rcases hm2 with h1 | h1 <;> rcases hn2 with h3 | h3 <;>
    simp [gec, Prod.ext_iff, Fin.ext_iff, decide_eq_decide, h1, h2, h3, h4] <;> omega

omit [NeZero q] in
/-- An even position of the boundary is a corner of the polygon. -/
theorem gvc_even {p : Fin (8 * q)} (h : p.val % 2 = 0) : gvc q p = none := by
  rw [gvc, if_pos h]

omit [NeZero q] in
/-- An odd position of the boundary is the midpoint of a side. -/
theorem gvc_odd {p : Fin (8 * q)} (h : p.val % 2 ≠ 0) :
    gvc q p = some (⟨p.val / 2 / 4, genus_hlt q p⟩, decide (p.val / 2 % 4 % 2 = 1)) := by
  rw [gvc, if_neg h]

theorem fpred_val_pos {n : Fin (8 * q)} {a : ℕ} (hv : n.val = a) (hpos : 0 < a) :
    (fpred n).val = a - 1 := by
  rw [fpred_val, hv, if_neg (by omega)]

/-! ### The polygon data of the surface of genus `q` -/





/-- **The identification of the boundary of the `4q`-gon is a polygon gluing**: the sides are
glued in pairs, no side becomes a loop, and every vertex and every edge occurs. -/
theorem genus_polygonData : PolygonData (gvc q) (gec q) where
  three_le := by have := Nat.pos_of_neZero q; omega
  pairs := (by
    intro i
    have hq := Nat.pos_of_neZero q
    have hi := i.isLt
    have hh : i.val / 2 / 4 < q := by omega
    have hmlt : 8 * (i.val / 2 / 4) + 2 * (if i.val / 2 % 4 < 2 then i.val / 2 % 4 + 2
        else i.val / 2 % 4 - 2) + (1 - i.val % 2) < 8 * q := by
      split_ifs <;> omega
    refine ⟨⟨_, hmlt⟩, ?_, ?_, ?_⟩
    · grind
    · rw [gec_eq_iff']
      refine ⟨?_, ?_, ?_⟩ <;> simp <;> split_ifs <;> omega
    · intro k hk
      rw [gec_eq_iff'] at hk
      obtain ⟨h1, h2, h3⟩ := hk
      have hk8 := k.isLt
      rw [Fin.ext_iff, Fin.ext_iff]
      simp
      split_ifs at h3 ⊢ <;> omega)
  noLoop := (by
    intro p
    have hq := Nat.pos_of_neZero q
    have hp := p.isLt
    have hs  := fin_succ_val p
    have hpar : (p + 1).val % 2 = (p.val + 1) % 2 := by
      rw [hs]
      rcases Nat.lt_or_ge (p.val + 1) (8 * q) with h | h
      · rw [Nat.mod_eq_of_lt h]
      · have he : p.val + 1 = 8 * q := by omega
        rw [he, Nat.mod_self]
        omega
    by_cases h : p.val % 2 = 0
    · rw [gvc, if_pos h, gvc, if_neg (by omega)]
      simp
    · rw [gvc, if_neg h, gvc, if_pos (by omega)]
      simp)
  vc_surj := (by
    have hq := Nat.pos_of_neZero q
    rintro (_ | ⟨h, i⟩)
    · exact ⟨⟨0, by omega⟩, by rw [gvc]; simp⟩
    · have hh := h.isLt
      refine ⟨⟨2 * (4 * h.val + (if i then 1 else 0)) + 1, by split_ifs <;> omega⟩, ?_⟩
      have hval : (⟨2 * (4 * h.val + (if i then 1 else 0)) + 1, by split_ifs <;> omega⟩ :
          Fin (8 * q)).val = 2 * (4 * h.val + (if i then 1 else 0)) + 1 := rfl
      rw [gvc, if_neg (by rw [hval]; split_ifs <;> omega)]
      simp
      constructor
      · grind
      · grind)
  ec_surj := (by
    have hq := Nat.pos_of_neZero q
    rintro ⟨h, i, b⟩
    have hh := h.isLt
    refine ⟨⟨2 * (4 * h.val + (if i then 1 else 0)) + (if b then 1 else 0), by
      split_ifs <;> omega⟩, ?_⟩
    have e1 : (2 * (4 * h.val + (if i then 1 else 0)) + (if b then 1 else 0)) / 2 / 4 = h.val := by
      split_ifs <;> omega
    have e2 : (2 * (4 * h.val + (if i then 1 else 0)) + (if b then 1 else 0)) / 2 % 4 =
        (if i then 1 else 0) := by
      split_ifs <;> omega
    have e3 : (2 * (4 * h.val + (if i then 1 else 0)) + (if b then 1 else 0)) % 2 =
        (if b then 1 else 0) := by
      split_ifs <;> omega
    simp only [gec, Prod.mk.injEq]
    refine ⟨Fin.ext ?_, ?_, ?_⟩
    · omega
    · grind
    · grind)

/-! ### The corners of the polygon form one cycle -/

/-- Two positions of the boundary are corners at the same vertex sharing a side, when the side
going out of the first is glued to the side coming into the second. -/
theorem cornerAdj_of_vals {m n : Fin (8 * q)} {a b : ℕ} (hvc : gvc q m = gvc q n)
    (ha : m.val = a) (hb : (fpred n).val = b)
    (h1 : a / 2 / 4 = b / 2 / 4) (h2 : a / 2 % 4 % 2 = b / 2 % 4 % 2)
    (h3 : (a % 2 + (if 2 ≤ a / 2 % 4 then 1 else 0)) % 2
        = (b % 2 + (if 2 ≤ b / 2 % 4 then 1 else 0)) % 2) :
    CornerAdj (gvc q) (gec q) m n := by
  refine ⟨hvc, Or.inr (Or.inl ((gec_eq_iff' q m (fpred n)).2 ?_))⟩
  rw [ha, hb]
  exact ⟨h1, h2, h3⟩

theorem cornerAdj_step1 (h : ℕ) (hh : h < q) :
    CornerAdj (gvc q) (gec q) ⟨8 * h, by omega⟩ ⟨8 * h + 6, by omega⟩ := by
  refine cornerAdj_of_vals q (a := 8 * h)
    (by rw [gvc_even q (by simp; omega), gvc_even q (by simp; omega)]) rfl
    (fpred_val_pos q (a := 8 * h + 6) rfl (by omega)) (by omega) (by omega) ?_
  rw [if_neg (by omega), if_pos (by omega)]
  omega

theorem cornerAdj_step2 (h : ℕ) (hh : h < q) :
    CornerAdj (gvc q) (gec q) ⟨8 * h + 6, by omega⟩ ⟨8 * h + 4, by omega⟩ := by
  refine cornerAdj_of_vals q (a := 8 * h + 6)
    (by rw [gvc_even q (by simp; omega), gvc_even q (by simp; omega)]) rfl
    (fpred_val_pos q (a := 8 * h + 4) rfl (by omega)) (by omega) (by omega) ?_
  rw [if_pos (by omega), if_neg (by omega)]
  omega



/-- Inside one commutator all four corners of the polygon are joined. -/
theorem conn_within_block (h : ℕ) (hh : h < q) (t : ℕ) (ht : t < 4) :
    ReflTransGen (CornerAdj (gvc q) (gec q)) ⟨8 * h, by omega⟩ ⟨8 * h + 2 * t, by omega⟩ := by
  have e1 := ReflTransGen.single (cornerAdj_step1 q h hh)
  have e2 := e1.tail (cornerAdj_step2 q h hh)
  have e3 := e2.tail (show CornerAdj (gvc q) (gec q) ⟨8 * h + 4, by omega⟩ ⟨8 * h + 2, by omega⟩ by
    refine cornerAdj_of_vals q (a := 8 * h + 4)
      (by rw [gvc_even q (by simp; omega), gvc_even q (by simp; omega)]) rfl
      (fpred_val_pos q (a := 8 * h + 2) rfl (by omega)) (by omega) (by omega) ?_
    rw [if_pos (by omega), if_neg (by omega)]
    omega)
  interval_cases t
  · rfl
  · simpa using e3
  · simpa using e2
  · simpa using e1

/-- **The corner `8h` of every commutator is joined to the corner `0`.** -/
theorem conn_block_zero (h : ℕ) (hh : h < q) :
    ReflTransGen (CornerAdj (gvc q) (gec q)) ⟨0, by have := Nat.pos_of_neZero q; omega⟩
      ⟨8 * h, by omega⟩ := by
  induction h with
  | zero => rfl
  | succ n ih =>
      have hn : n < q := by omega
      have h1 := ih hn
      have h2 := conn_within_block q n hn 1 (by omega)
      have h3 := ReflTransGen.single (show CornerAdj (gvc q) (gec q) ⟨8 * n + 2, by omega⟩ ⟨8 * (n + 1), by omega⟩ by
        refine cornerAdj_of_vals q (a := 8 * n + 2)
          (by rw [gvc_even q (by simp; omega), gvc_even q (by simp; omega)]) rfl
          (fpred_val_pos q (a := 8 * (n + 1)) rfl (by omega)) (by omega) (by omega) ?_
        rw [if_neg (by omega), if_pos (by omega)]
        omega)
      have h2' : ReflTransGen (CornerAdj (gvc q) (gec q)) ⟨8 * n, by omega⟩
          ⟨8 * n + 2, by omega⟩ := by simpa using h2
      exact (h1.trans h2').trans h3

/-- Every corner of the polygon is joined to the corner `0`. -/
theorem conn_even_zero (p : Fin (8 * q)) (hp : p.val % 2 = 0) :
    ReflTransGen (CornerAdj (gvc q) (gec q)) ⟨0, by have := Nat.pos_of_neZero q; omega⟩ p := by
  have hq := Nat.pos_of_neZero q
  have hlt := p.isLt
  have hh : p.val / 8 < q := by omega
  have hblock := conn_block_zero q (p.val / 8) hh
  have hwithin := conn_within_block q (p.val / 8) hh (p.val % 8 / 2) (by omega)
  have hval : ⟨8 * (p.val / 8) + 2 * (p.val % 8 / 2), by omega⟩ = p := by
    ext
    simp
    omega
  rw [hval] at hwithin
  exact hblock.trans hwithin

/-- **The corners of the `4q`-gon are glued in a single cycle**, and the two midpoints of a pair
of identified sides are glued to each other. -/
theorem genus_cornersConnected : CornersConnected (gvc q) (gec q) := by
  have hq := Nat.pos_of_neZero q
  intro i j hij
  have hi8 := i.isLt
  have hj8 := j.isLt
  by_cases hi : i.val % 2 = 0
  · -- both positions are corners of the polygon
    have hj : j.val % 2 = 0 := by
      by_contra hj
      rw [gvc_even q hi, gvc_odd q hj] at hij
      simp at hij
    letI : Std.Symm (CornerAdj (gvc q) (gec q)) := ⟨fun _ _ h => cornerAdj_symm h⟩
    exact (ReflTransGen.stdSymm.symm _ _ (conn_even_zero q i hi)).trans
      (conn_even_zero q j hj)
  · -- both positions are midpoints of sides
    have hj : j.val % 2 ≠ 0 := by
      intro hj
      rw [gvc_even q hj, gvc_odd q hi] at hij
      simp at hij
    rw [gvc_odd q hi, gvc_odd q hj] at hij
    simp at hij
    obtain ⟨h1, h2⟩ := hij
    have h2' : i.val / 2 % 4 % 2 = j.val / 2 % 4 % 2 := by
      by_cases ha : i.val / 2 % 4 % 2 = 1 <;> by_cases hb : j.val / 2 % 4 % 2 = 1 <;>
        simp [ha, hb] at h2 ⊢ <;> omega
    by_cases heq : i.val = j.val
    · grind
    -- the two positions are the midpoints of a pair of glued sides
    rcases Nat.lt_or_ge (i.val / 2 % 4) 2 with hr | hr
    · have hjv : j.val = i.val + 4 := by omega
      refine ReflTransGen.single ?_
      refine cornerAdj_of_vals q (b := i.val + 3)
        (by rw [gvc_odd q hi, gvc_odd q hj]
            simp
            exact ⟨h1, by omega⟩) rfl
        (by rw [fpred_val_pos q rfl (by omega)]; omega) (by omega) (by omega) ?_
      rw [if_neg (by omega), if_pos (by omega)]
      omega
    · have hjv : j.val = i.val - 4 := by omega
      refine ReflTransGen.single (cornerAdj_symm ?_)
      refine cornerAdj_of_vals q (b := j.val + 3)
        (by rw [gvc_odd q hi, gvc_odd q hj]
            simp
            exact ⟨h1.symm, by omega⟩) rfl
        (by rw [fpred_val_pos q (a := i.val) rfl (by omega)]; omega) (by omega) (by omega) ?_
      rw [if_neg (by omega), if_pos (by omega)]
      omega

/-! ### The closed surface -/

/-- **The nerve of the block of genus `q` is a closed surface.** -/
def genusClosedSurface : ClosedSurfacePoset (SCell (gvc q) (gec q) (gc q)) :=
  closedSurfacePoset_SCell (gc q) (genus_polygonData q) (genus_cornersConnected q)

/-- The triangulation of the surface of genus `q` is two-dimensional. -/
theorem genus_chain_card_le_three {s : Finset (SCell (gvc q) (gec q) (gc q))}
    (hs : s ∈ (orderComplex (SCell (gvc q) (gec q) (gc q))).faces) : s.card ≤ 3 :=
  (genusClosedSurface q).toSurfaceRank.chain_card_le_three hs

end GenusSurface

end Davis
end FiniteChains

namespace FiniteChains.Comb
variable {P : Type} [PartialOrder P]

theorem injIn_delete_free_face {C : P → Prop} {f t : P}
    (ht : C t) (hft : f ≤ t) (hne : t ≠ f)
    (hunique : ∀ x, C x → f ≤ x → x ≠ f → x = t) :
    InjIn C (fun x => C x ∧ x ≠ f) := by
  classical
  let r : {x : P // C x} → P := fun x => if x.1 = f then t else x.1
  have hr : Monotone r := by
    intro x y hxy
    by_cases hx : x.1 = f
    · by_cases hy : y.1 = f
      · simp [r, hx, hy]
      · have hyt  := hunique y.1 y.2 (hx ▸ hxy) hy
        simp [r, hx, hyt]
    · by_cases hy : y.1 = f
      · have hxf : x.1 ≤ f := hy ▸ hxy
        simpa [r, hx, hy] using hxf.trans hft
      · simpa [r, hx, hy] using hxy
  apply injIn_of_monotone_retraction (fun _ h => h.1) r hr
  · grind
  · grind

/-- Deleting a maximal cell reflects homotopies when its remaining boundary is connected
and simply connected. The boundary is the actual strict lower face poset in the stage. -/
theorem injIn_delete_maximal {C : P → Prop} {t : P}
    (hmax : ∀ x, C x → t ≤ x → x = t)
    (hne : ∃ x, C x ∧ x < t)
    (hconn : ConnectedIn (fun x => C x ∧ x < t))
    (hsc : SimplyConnectedIn (fun x => C x ∧ x < t)) :
    InjIn C (fun x => C x ∧ x ≠ t) := by
  obtain ⟨j, hj⟩ := hne
  apply injIn_union_of_unmixed
    (B := fun x => C x ∧ x ≤ t)
    (hJconn := hconn) (hJsc := hsc) (hj0 := hj)
  · grind
  · intro x
    constructor
    · rintro ⟨hx, hxt⟩
      exact ⟨⟨hx, hxt.ne⟩, ⟨hx, hxt.le⟩⟩
    · rintro ⟨⟨hx, hne⟩, ⟨_, hle⟩⟩
      exact ⟨hx, lt_of_le_of_ne hle hne⟩

end FiniteChains.Comb

namespace FiniteChains

namespace ASC

open Relation

variable {P : Type} [PartialOrder P] [Fintype P] [DecidableEq P]

/-! ### Flags -/

omit [Fintype P] [DecidableEq P] in
/-- The ranks of a two-step chain in a two-dimensional cell poset are `0, 1, 2`. -/
theorem SurfaceRank.rk_flag (S : SurfaceRank P) {x y z : P} (hxy : x < y) (hyz : y < z) :
    S.rk x = 0 ∧ S.rk y = 1 ∧ S.rk z = 2 := by
  have h1 := S.rk_lt_of_lt hxy
  have h2 := S.rk_lt_of_lt hyz
  have h3 := S.rk_le_two z
  omega

omit [Fintype P] in
/-- A flag spans a triangle of the order complex. -/
theorem isTri_of_flag {v e f : P} (hve : v < e) (hef : e < f) :
    IsTri (orderComplex P) ({v, e, f} : Finset P) := by
  refine ⟨?_, ?_⟩
  · rw [mem_orderComplex]
    have : IsChain (· ≤ ·) ({v, e, f} : Set P) :=
      isChain_triple (Or.inl hve.le) (Or.inl (hve.trans hef).le) (Or.inl hef.le)
    simpa [Finset.coe_insert] using this
  · grind

omit [Fintype P] in
/-- **Every triangle of the order complex is a flag.** -/
theorem orderComplex_exists_flag_of_isTri {σ : Finset P}
    (h : IsTri (orderComplex P) σ) :
    ∃ v e f : P, v < e ∧ e < f ∧ σ = ({v, e, f} : Finset P) := by
  obtain ⟨hface, hcard⟩ := h
  have hchain  := (mem_orderComplex).1 hface
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 hcard
  have hmem : ∀ x ∈ ({a, b, c} : Finset P), x ∈ (({a, b, c} : Finset P) : Set P) := by
    intro x hx; exact_mod_cast hx
  have cmp : ∀ x ∈ ({a, b, c} : Finset P), ∀ y ∈ ({a, b, c} : Finset P), x ≠ y →
      x < y ∨ y < x := by
    intro x hx y hy hxy
    rcases hchain (hmem x hx) (hmem y hy) hxy with h | h
    · exact Or.inl (lt_of_le_of_ne h hxy)
    · exact Or.inr (lt_of_le_of_ne h (Ne.symm hxy))
  have ha : a ∈ ({a, b, c} : Finset P) := by simp
  have hb : b ∈ ({a, b, c} : Finset P) := by simp
  have hc : c ∈ ({a, b, c} : Finset P) := by simp
  have perm : ∀ x y z : P, ({a, b, c} : Finset P) = {x, y, z} →
      x < y → y < z → ∃ v e f : P, v < e ∧ e < f ∧ ({a, b, c} : Finset P) = {v, e, f} :=
    fun x y z hxyz h1 h2 => ⟨x, y, z, h1, h2, hxyz⟩
  rcases cmp a ha b hb hab with h1 | h1 <;> rcases cmp b hb c hc hbc with h2 | h2 <;>
    rcases cmp a ha c hc hac with h3 | h3
  · simp_all
  · simp_all
  · grind
  · grind
  · grind
  · grind
  · grind
  · grind

/-! ### Adjacent flags -/


omit [Fintype P] in
/-- Two flags over the same edge and face, with different vertices, are adjacent. -/
theorem triAdj_vtx {v v' e f : P} (hve : v < e) (hef : e < f) (hv'e : v' < e) (hvv' : v ≠ v') :
    TriAdj (orderComplex P) ({v, e, f} : Finset P) ({v', e, f} : Finset P) := by
  refine ⟨isTri_of_flag hve hef, isTri_of_flag hv'e hef, ?_⟩
  grind

omit [Fintype P] in
/-- Two flags over the same vertex and face, with different edges, are adjacent. -/
theorem triAdj_edge {v e e' f : P} (hve : v < e) (hef : e < f) (hve' : v < e') (he'f : e' < f)
    (hee' : e ≠ e') :
    TriAdj (orderComplex P) ({v, e, f} : Finset P) ({v, e', f} : Finset P) := by
  refine ⟨isTri_of_flag hve hef, isTri_of_flag hve' he'f, ?_⟩
  grind

omit [Fintype P] in
/-- Two flags over the same vertex and edge, with different faces, are adjacent. -/
theorem triAdj_face {v e f f' : P} (hve : v < e) (hef : e < f) (hef' : e < f') (hff' : f ≠ f') :
    TriAdj (orderComplex P) ({v, e, f} : Finset P) ({v, e, f'} : Finset P) := by
  refine ⟨isTri_of_flag hve hef, isTri_of_flag hve hef', ?_⟩
  grind

/-! ### The two global conditions -/

/-- Two faces are adjacent when they share an edge. -/
def FaceAdj (S : SurfaceRank P) (f f' : P) : Prop := ∃ e : P, S.rk e = 1 ∧ e < f ∧ e < f'

/-- **The faces of the cell structure are connected through shared edges.** -/
def FacesConnected (S : SurfaceRank P) : Prop :=
  ∀ f f' : P, S.rk f = 2 → S.rk f' = 2 → ReflTransGen (FaceAdj S) f f'

/-- **Two distinct vertices of a face are joined by an edge of that face.**  This holds for a
face with three vertices; it is what makes the flags of a fixed face connected. -/
def FaceEdges (S : SurfaceRank P) : Prop :=
  ∀ v v' f : P, S.rk v = 0 → S.rk v' = 0 → S.rk f = 2 → v < f → v' < f → v ≠ v' →
    ∃ e : P, v < e ∧ v' < e ∧ e < f

namespace SurfaceRank

variable (S : SurfaceRank P)

omit [Fintype P] [DecidableEq P] in
/-- A face of rank two carries a flag. -/
theorem exists_flag_of_rk_two {f : P} (hf : S.rk f = 2) :
    ∃ v e : P, S.rk v = 0 ∧ v < e ∧ e < f := by
  obtain ⟨v, hv, hvf⟩ := S.exists_vertex f hf
  obtain ⟨e, -, -, ⟨hve, hef⟩, -, -⟩ := S.two_edges v f hv hf hvf
  grind

omit [Fintype P] in
/-- **The flags of a fixed face are connected in the dual graph.** -/
theorem conn_in_face (hfe : FaceEdges S) {f v e v' e' : P} (hf : S.rk f = 2)
    (hv : S.rk v = 0) (hve : v < e) (hef : e < f)
    (hv' : S.rk v' = 0) (hv'e' : v' < e') (he'f : e' < f) :
    ReflTransGen (TriAdj (orderComplex P)) ({v, e, f} : Finset P) ({v', e', f} : Finset P) := by
  by_cases hvv' : v = v'
  · subst hvv'
    by_cases hee' : e = e'
    · subst hee'; exact ReflTransGen.refl
    · exact ReflTransGen.single (triAdj_edge hve hef hv'e' he'f hee')
  · obtain ⟨e'', hve'', hv'e'', he''f⟩ :=
      hfe v v' f hv hv' hf (hve.trans hef) (hv'e'.trans he'f) hvv'
    have s1 : ReflTransGen (TriAdj (orderComplex P)) ({v, e, f} : Finset P)
        ({v, e'', f} : Finset P) := by
      by_cases h : e = e''
      · grind
      · exact ReflTransGen.single (triAdj_edge hve hef hve'' he''f h)
    have s2  :=
      ReflTransGen.single (triAdj_vtx hve'' he''f hv'e'' hvv')
    have s3 : ReflTransGen (TriAdj (orderComplex P)) ({v', e'', f} : Finset P)
        ({v', e', f} : Finset P) := by
      by_cases h : e'' = e'
      · grind
      · exact ReflTransGen.single (triAdj_edge hv'e'' he''f hv'e' he'f h)
    exact (s1.trans s2).trans s3

omit [Fintype P] in
/-- Crossing a shared edge: any flag of `f` is connected to any flag of an adjacent face `f'`. -/
theorem conn_face_step (hfe : FaceEdges S) {f f' v e v' e' : P} (hadj : FaceAdj S f f')
    (hv : S.rk v = 0) (hve : v < e) (hef : e < f)
    (hv' : S.rk v' = 0) (hv'e' : v' < e') (he'f' : e' < f') :
    ReflTransGen (TriAdj (orderComplex P)) ({v, e, f} : Finset P) ({v', e', f'} : Finset P) := by
  obtain ⟨d, hd, hdf, hdf'⟩ := hadj
  have hf : S.rk f = 2 := by have := S.rk_lt_of_lt hdf; have := S.rk_le_two f; omega
  have hf' : S.rk f' = 2 := by have := S.rk_lt_of_lt hdf'; have := S.rk_le_two f'; omega
  obtain ⟨w, -, -, hwd, -, -⟩ := S.two_vertices d hd
  have hw : S.rk w = 0 := by have := S.rk_lt_of_lt hwd; omega
  have s1  := S.conn_in_face hfe hf hv hve hef hw hwd hdf
  have s2 : ReflTransGen (TriAdj (orderComplex P)) ({w, d, f} : Finset P)
      ({w, d, f'} : Finset P) := by
    by_cases hff' : f = f'
    · grind
    · exact ReflTransGen.single (triAdj_face hwd hdf hdf' hff')
  have s3  := S.conn_in_face hfe hf' hw hwd hdf' hv' hv'e' he'f'
  exact (s1.trans s2).trans s3

omit [Fintype P] in
/-- Flags over faces joined by a chain of adjacent faces are connected. -/
theorem conn_along_faces (hfe : FaceEdges S) {f f' : P} (hchain : ReflTransGen (FaceAdj S) f f')
    (hf : S.rk f = 2) {v e v' e' : P}
    (hv : S.rk v = 0) (hve : v < e) (hef : e < f)
    (hv' : S.rk v' = 0) (hv'e' : v' < e') (he'f' : e' < f') :
    ReflTransGen (TriAdj (orderComplex P)) ({v, e, f} : Finset P) ({v', e', f'} : Finset P) := by
  have key : ∀ {b : P}, ReflTransGen (FaceAdj S) f b → ∀ x y : P, S.rk x = 0 → x < y → y < b →
      ReflTransGen (TriAdj (orderComplex P)) ({v, e, f} : Finset P) ({x, y, b} : Finset P) := by
    intro b hb
    induction hb with
    | refl =>
        intro x y hx hxy hyb
        exact S.conn_in_face hfe hf hv hve hef hx hxy hyb
    | @tail c d hfc hcd ih =>
        intro x y hx hxy hyd
        obtain ⟨g, hg, hgc, -⟩ := id hcd
        have hc : S.rk c = 2 := by
          have := S.rk_lt_of_lt hgc
          have := S.rk_le_two c
          omega
        obtain ⟨w, d', hw, hwd', hd'c⟩ := S.exists_flag_of_rk_two hc
        exact (ih w d' hw hwd' hd'c).trans
          (S.conn_face_step hfe hcd hw hwd' hd'c hx hxy hyd)
  simp_all

omit [Fintype P] in
/-- **The dual graph of the order complex is connected.** -/
theorem dual_connected (hfe : FaceEdges S) (hfc : FacesConnected S) :
    ∀ σ σ' : Finset P, IsTri (orderComplex P) σ → IsTri (orderComplex P) σ' →
      ReflTransGen (TriAdj (orderComplex P)) σ σ' := by
  intro σ σ' hσ hσ'
  obtain ⟨v, e, f, hve, hef, rfl⟩ := orderComplex_exists_flag_of_isTri hσ
  obtain ⟨v', e', f', hv'e', he'f', rfl⟩ := orderComplex_exists_flag_of_isTri hσ'
  obtain ⟨hv, -, hf⟩ := S.rk_flag hve hef
  obtain ⟨hv', -, hf'⟩ := S.rk_flag hv'e' he'f'
  exact S.conn_along_faces hfe (hfc f f' hf hf') hf hv hve hef hv' hv'e' he'f'

end SurfaceRank

end ASC

end FiniteChains

namespace FiniteChains
namespace Davis

open Cell ASC Relation

section Dual

variable {κ ι : Type} {M : ℕ} [NeZero M] [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)

/-! ### Two vertices of a triangle are joined by a side -/

omit [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] in
/-- The vertices of the triangle `tr1 p`. -/
theorem vtx_of_lt_tr1 {p : Fin M} {v : SCell vc ec hc} (hv : Cell.rk v = 0)
    (h : v < toS vc ec hc (tr1 p)) :
    v = vtx (vc p) ∨ v = vtx (vc (p + 1)) ∨ v = cvx (p + 1) := by
  rcases (lt_tr1_iff hc).1 h with rfl | rfl | rfl | rfl | rfl | rfl
  · simp [Cell.rk] at hv
  · simp [Cell.rk] at hv
  · simp [Cell.rk] at hv
  · grind
  · grind
  · grind

omit [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] in
/-- The vertices of the triangle `tr2 p`. -/
theorem vtx_of_lt_tr2 {p : Fin M} {v : SCell vc ec hc} (hv : Cell.rk v = 0)
    (h : v < toS vc ec hc (tr2 p)) :
    v = vtx (vc p) ∨ v = cvx p ∨ v = cvx (p + 1) := by
  rcases (lt_tr2_iff hc).1 h with rfl | rfl | rfl | rfl | rfl | rfl
  · simp [Cell.rk] at hv
  · simp [Cell.rk] at hv
  · simp [Cell.rk] at hv
  · grind
  · grind
  · grind

omit [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] in
/-- The vertices of the triangle `inn p`. -/
theorem vtx_of_lt_inn {p : Fin M} {v : SCell vc ec hc} (hv : Cell.rk v = 0)
    (h : v < toS vc ec hc (inn p)) :
    v = ctr ∨ v = cvx p ∨ v = cvx (p + 1) := by
  rcases (lt_inn_iff hc).1 h with rfl | rfl | rfl | rfl | rfl | rfl
  · simp [Cell.rk] at hv
  · simp [Cell.rk] at hv
  · simp [Cell.rk] at hv
  · grind
  · grind
  · grind

omit [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] in
/-- **Two distinct vertices of a triangle of the surface lie on a common side of it.** -/
theorem faceEdges_SCell (hd : PolygonData vc ec) : FaceEdges (surfaceRank_SCell hc hd) := by
  intro v v' f hv hv' hf hvf hv'f hne
  -- the three sides of `tr1 p`
  have Ebed : ∀ p : Fin M, toS vc ec hc (vtx (vc p)) < toS vc ec hc (bed (ec p)) ∧
      toS vc ec hc (vtx (vc (p + 1))) < toS vc ec hc (bed (ec p)) ∧
      toS vc ec hc (bed (ec p)) < toS vc ec hc (tr1 p) := fun p =>
    ⟨(lt_bed_iff hc).2 (Or.inl rfl), (lt_bed_iff hc).2 (Or.inr rfl),
      (bed_lt_iff hc).2 ⟨p, rfl, rfl⟩⟩
  have Egdi : ∀ p : Fin M, toS vc ec hc (vtx (vc p)) < toS vc ec hc (gdi p) ∧
      toS vc ec hc (cvx (p + 1)) < toS vc ec hc (gdi p) := fun p =>
    ⟨(lt_gdi_iff hc).2 (Or.inl rfl), (lt_gdi_iff hc).2 (Or.inr rfl)⟩
  have Edia : ∀ p : Fin M, toS vc ec hc (vtx (vc p)) < toS vc ec hc (dia p) ∧
      toS vc ec hc (cvx p) < toS vc ec hc (dia p) := fun p =>
    ⟨(lt_dia_iff hc).2 (Or.inl rfl), (lt_dia_iff hc).2 (Or.inr rfl)⟩
  have Eced : ∀ p : Fin M, toS vc ec hc (cvx p) < toS vc ec hc (ced p) ∧
      toS vc ec hc (cvx (p + 1)) < toS vc ec hc (ced p) := fun p =>
    ⟨(lt_ced_iff hc).2 (Or.inl rfl), (lt_ced_iff hc).2 (Or.inr rfl)⟩
  have Erad : ∀ p : Fin M, toS vc ec hc ctr < toS vc ec hc (rad p) ∧
      toS vc ec hc (cvx p) < toS vc ec hc (rad p) := fun p =>
    ⟨(lt_rad_iff hc).2 (Or.inl rfl), (lt_rad_iff hc).2 (Or.inr rfl)⟩
  cases f with
  | tr1 p =>
      have hdia : toS vc ec hc (dia (p + 1)) < toS vc ec hc (tr1 p) :=
        (dia_lt_iff hc).2 (Or.inr (by rw [fpred_succ]))
      have hgdi : toS vc ec hc (gdi p) < toS vc ec hc (tr1 p) := (gdi_lt_iff hc).2 (Or.inl rfl)
      rcases vtx_of_lt_tr1 hc hv hvf with rfl | rfl | rfl <;>
        rcases vtx_of_lt_tr1 hc hv' hv'f with rfl | rfl | rfl
      · grind
      · exact ⟨bed (ec p), (Ebed p).1, (Ebed p).2.1, (Ebed p).2.2⟩
      · exact ⟨gdi p, (Egdi p).1, (Egdi p).2, hgdi⟩
      · exact ⟨bed (ec p), (Ebed p).2.1, (Ebed p).1, (Ebed p).2.2⟩
      · grind
      · exact ⟨dia (p + 1), (Edia (p + 1)).1, (Edia (p + 1)).2, hdia⟩
      · exact ⟨gdi p, (Egdi p).2, (Egdi p).1, hgdi⟩
      · exact ⟨dia (p + 1), (Edia (p + 1)).2, (Edia (p + 1)).1, hdia⟩
      · grind
  | tr2 p =>
      have hced : toS vc ec hc (ced p) < toS vc ec hc (tr2 p) := (ced_lt_iff hc).2 (Or.inl rfl)
      have hdia : toS vc ec hc (dia p) < toS vc ec hc (tr2 p) := (dia_lt_iff hc).2 (Or.inl rfl)
      have hgdi : toS vc ec hc (gdi p) < toS vc ec hc (tr2 p) := (gdi_lt_iff hc).2 (Or.inr rfl)
      rcases vtx_of_lt_tr2 hc hv hvf with rfl | rfl | rfl <;>
        rcases vtx_of_lt_tr2 hc hv' hv'f with rfl | rfl | rfl
      · grind
      · exact ⟨dia p, (Edia p).1, (Edia p).2, hdia⟩
      · exact ⟨gdi p, (Egdi p).1, (Egdi p).2, hgdi⟩
      · exact ⟨dia p, (Edia p).2, (Edia p).1, hdia⟩
      · grind
      · exact ⟨ced p, (Eced p).1, (Eced p).2, hced⟩
      · exact ⟨gdi p, (Egdi p).2, (Egdi p).1, hgdi⟩
      · exact ⟨ced p, (Eced p).2, (Eced p).1, hced⟩
      · grind
  | inn p =>
      have hced : toS vc ec hc (ced p) < toS vc ec hc (inn p) := (ced_lt_iff hc).2 (Or.inr rfl)
      have hrad : toS vc ec hc (rad p) < toS vc ec hc (inn p) := (rad_lt_iff hc).2 (Or.inl rfl)
      have hrad' : toS vc ec hc (rad (p + 1)) < toS vc ec hc (inn p) :=
        (rad_lt_iff hc).2 (Or.inr (by rw [fpred_succ]))
      rcases vtx_of_lt_inn hc hv hvf with rfl | rfl | rfl <;>
        rcases vtx_of_lt_inn hc hv' hv'f with rfl | rfl | rfl
      · grind
      · exact ⟨rad p, (Erad p).1, (Erad p).2, hrad⟩
      · exact ⟨rad (p + 1), (Erad (p + 1)).1, (Erad (p + 1)).2, hrad'⟩
      · exact ⟨rad p, (Erad p).2, (Erad p).1, hrad⟩
      · grind
      · exact ⟨ced p, (Eced p).1, (Eced p).2, hced⟩
      · exact ⟨rad (p + 1), (Erad (p + 1)).2, (Erad (p + 1)).1, hrad'⟩
      · exact ⟨ced p, (Eced p).2, (Eced p).1, hced⟩
      · grind
  | _ => simp [surfaceRank_SCell, Cell.rk] at hf

/-! ### The triangles of the surface are connected through shared edges -/

variable (hd : PolygonData vc ec)

omit [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] in
/-- The two triangles of the collar at the position `p` share the edge `gdi p`. -/
theorem faceAdj_tr1_tr2 (p : Fin M) :
    FaceAdj (surfaceRank_SCell hc hd) (tr1 p) (tr2 p) :=
  ⟨gdi p, rfl, (gdi_lt_iff hc).2 (Or.inl rfl), (gdi_lt_iff hc).2 (Or.inr rfl)⟩

omit [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] in
/-- The inner triangle of the collar and the triangle of the fan at `p` share the edge `ced p`. -/
theorem faceAdj_tr2_inn (p : Fin M) :
    FaceAdj (surfaceRank_SCell hc hd) (tr2 p) (inn p) :=
  ⟨ced p, rfl, (ced_lt_iff hc).2 (Or.inl rfl), (ced_lt_iff hc).2 (Or.inr rfl)⟩

omit [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] in
/-- Consecutive triangles of the fan share a radius. -/
theorem faceAdj_inn_inn (p : Fin M) :
    FaceAdj (surfaceRank_SCell hc hd) (inn p) (inn (p + 1)) :=
  ⟨rad (p + 1), rfl, (rad_lt_iff hc).2 (Or.inr (by rw [fpred_succ])),
    (rad_lt_iff hc).2 (Or.inl rfl)⟩

omit [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] in
/-- Face adjacency is symmetric. -/
theorem faceAdj_symm {f f' : SCell vc ec hc} (h : FaceAdj (surfaceRank_SCell hc hd) f f') :
    FaceAdj (surfaceRank_SCell hc hd) f' f := by
  obtain ⟨e, he, h1, h2⟩ := h
  exact ⟨e, he, h2, h1⟩

omit [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] in
/-- Every triangle of the fan is reached from the one at the position `0`. -/
theorem conn_inn_zero (p : Fin M) :
    ReflTransGen (FaceAdj (surfaceRank_SCell hc hd)) (inn 0) (inn p) := by
  have key : ∀ k : ℕ, ∀ r : Fin M, r.val = k →
      ReflTransGen (FaceAdj (surfaceRank_SCell hc hd)) (inn 0) (inn r) := by
    intro k
    induction k with
    | zero => grind
    | succ n ih =>
        intro r hr
        have hval : (fpred r).val = n := by
          rw [fpred_val, if_neg (by omega)]
          omega
        have hstep : FaceAdj (surfaceRank_SCell hc hd) (inn (fpred r)) (inn r) := by
          have := faceAdj_inn_inn hc hd (fpred r)
          rwa [fpred_add_one] at this
        exact (ih (fpred r) hval).tail hstep
  exact key p.val p rfl

omit [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] in
/-- Every triangle of the surface is reached from the triangle `inn 0` of the fan. -/
theorem conn_from_inn_zero (f : SCell vc ec hc) (hf : Cell.rk f = 2) :
    ReflTransGen (FaceAdj (surfaceRank_SCell hc hd)) (inn 0) f := by
  cases f with
  | tr1 p =>
      exact ((conn_inn_zero hc hd p).tail
        (faceAdj_symm hc hd (faceAdj_tr2_inn hc hd p))).tail
        (faceAdj_symm hc hd (faceAdj_tr1_tr2 hc hd p))
  | tr2 p =>
      exact (conn_inn_zero hc hd p).tail (faceAdj_symm hc hd (faceAdj_tr2_inn hc hd p))
  | inn p => exact conn_inn_zero hc hd p
  | _ => simp [Cell.rk] at hf

omit [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] in
/-- **The triangles of the surface are connected through shared edges.** -/
theorem facesConnected_SCell (hd : PolygonData vc ec) : FacesConnected (surfaceRank_SCell hc hd) := by
  intro f f' hf hf'
  have hsymm : Symmetric (FaceAdj (surfaceRank_SCell hc hd)) :=
    fun _ _ h => faceAdj_symm hc hd h
  letI : Std.Symm (FaceAdj (surfaceRank_SCell hc hd)) := ⟨fun _ _ h => hsymm h⟩
  exact (ReflTransGen.stdSymm.symm _ _ (conn_from_inn_zero hc hd f hf)).trans
    (conn_from_inn_zero hc hd f' hf')

/-! ### The dual graph of the triangulation, and the collapse -/

omit [Fintype κ] [Fintype ι] in
/-- **The dual graph of the triangulation of the surface is connected.** -/
theorem dual_connected_SCell (hd : PolygonData vc ec) :
    ∀ σ σ' : Finset (SCell vc ec hc), IsTri (orderComplex (SCell vc ec hc)) σ →
      IsTri (orderComplex (SCell vc ec hc)) σ' →
      ReflTransGen (TriAdj (orderComplex (SCell vc ec hc))) σ σ' :=
  (surfaceRank_SCell hc hd).dual_connected (faceEdges_SCell hc hd) (facesConnected_SCell hc hd)

omit [Fintype κ] [Fintype ι] in
/-- Every cell of the surface is a vertex of a triangle of the triangulation. -/
theorem cover_SCell (hd : PolygonData vc ec) (v : SCell vc ec hc) :
    ∃ σ, IsTri (orderComplex (SCell vc ec hc)) σ ∧ v ∈ σ := by
  obtain ⟨s, hs, hcard, hv⟩ := (surfaceRank_SCell hc hd).vertexInTriangle v
  exact ⟨s, ⟨hs, hcard⟩, hv⟩

omit [Fintype κ] [Fintype ι] in
/-- The flag `ctr < rad 0 < inn 0` is a triangle of the triangulation. -/
theorem isTri_base_SCell :
    IsTri (orderComplex (SCell vc ec hc)) ({ctr, rad 0, inn 0} : Finset (SCell vc ec hc)) :=
  isTri_of_flag ((lt_rad_iff hc).2 (Or.inl rfl)) ((rad_lt_iff hc).2 (Or.inl rfl))

/-- **Lemma 3.2 (ii) for the surface of the block.**  All three-cubes of the truncated cube
complex over the triangulation of the closed surface `SCell vc ec hc` are removed by elementary
collapses, leaving a two-dimensional spine. -/
theorem exists_spine_collapse_SCell (hd : PolygonData vc ec) :
    ∃ l : List (Cube (SCell vc ec hc)),
      Collapse.IsCollapse (spineInc (orderComplex (SCell vc ec hc))) l
        (topCubes (orderComplex (SCell vc ec hc))) :=
  exists_spine_collapse_of_surface (edgeInTwoTriangles_SCell hc hd) (dual_connected_SCell hc hd)
    (cover_SCell hc hd) (isTri_base_SCell hc)

end Dual

end Davis
end FiniteChains

namespace FiniteChains
namespace Davis
namespace Genus

open Cell ASC Relation

variable (q : ℕ) [NeZero q]

/-- **Lemma 3.2 (ii) for the block of genus `q`.**  All three-cubes of the truncated cube complex
over the triangulation of the closed surface of genus `q` are removed by elementary collapses,
leaving a two-dimensional spine. -/
theorem genus_spine_collapse :
    ∃ l : List (Cube (SCell (gvc q) (gec q) (gc q))),
      Collapse.IsCollapse (spineInc (orderComplex (SCell (gvc q) (gec q) (gc q)))) l
        (topCubes (orderComplex (SCell (gvc q) (gec q) (gc q)))) :=
  exists_spine_collapse_SCell (gc q) (genus_polygonData q)

end Genus
end Davis
end FiniteChains

namespace FiniteChains
namespace CollapseChain

variable {T F R : Type*} [Ring R]

/-- The Whitehead retraction of an elementary collapse removing the top cell `t` across its
free face `f`: subtract the multiple of the boundary `d t` which kills the `f`-coordinate. -/
def retr (d : T → F → R) (t : T) (f : F) (x : F → R) : F → R :=
  fun g => x g - x f * Ring.inverse (d t f) * d t g

/-- The chain map of a sequence of elementary collapses: the composite of the retractions of
its steps, each step being recorded as the removed top cell together with the face it is
collapsed across. -/
def cmap (d : T → F → R) : List (T × F) → (F → R) → (F → R)
  | [], x => x
  | (t, f) :: l, x => cmap d l (retr d t f x)

/-- The hypotheses under which a list of (top cell, face) pairs is a sequence of elementary
collapses on the chain level: the face is a *unit* face of the cell it is collapsed across,
and it is *free*, i.e. no cell removed later meets it. -/
def IsChainCollapse (d : T → F → R) : List (T × F) → Prop
  | [] => True
  | (t, f) :: l => IsUnit (d t f) ∧ (∀ p ∈ l, d p.1 f = 0) ∧ IsChainCollapse d l

variable {d : T → F → R}

@[simp] theorem retr_zero (t : T) (f : F) : retr d t f 0 = 0 := by
  funext g; simp [retr]



@[simp] theorem cmap_zero (l : List (T × F)) : cmap d l 0 = 0 := by
  induction l with
  | nil => rfl
  | cons p l ih => obtain ⟨t, f⟩ := p; simp [cmap, ih]

theorem cmap_add (l : List (T × F)) (x y : F → R) :
    cmap d l (x + y) = cmap d l x + cmap d l y := by
  induction l generalizing x y with
  | nil => rfl
  | cons p l ih => obtain ⟨t, f⟩ := p; simp [cmap, (show retr d t f (x + y) = retr d t f x + retr d t f y by
    funext g
    simp only [retr, Pi.add_apply, add_mul]
    abel), ih]

theorem cmap_leftMul (l : List (T × F)) (a : R) (x : F → R) :
    cmap d l (fun g => a * x g) = fun g => a * cmap d l x g := by
  induction l generalizing x with
  | nil => rfl
  | cons p l ih =>
      obtain ⟨t, f⟩ := p
      show cmap d l (retr d t f fun g => a * x g) = fun g => a * cmap d l (retr d t f x) g
      rw [(show retr d t f (fun g => a * x g) = fun g => a * retr d t f x g by
        funext g
        simp only [retr, mul_sub, mul_assoc]), ih]

/-- The retraction of an elementary collapse kills the boundary of the cell it removes. -/
theorem retr_self {t : T} {f : F} (h : IsUnit (d t f)) : retr d t f (d t) = 0 := by
  funext g
  simp [retr, Ring.mul_inverse_cancel _ h]

/-- The retraction of an elementary collapse fixes the boundary of a cell which does not
meet the face it is collapsed across. -/
theorem retr_of_notMem {t t' : T} {f : F} (h : d t' f = 0) : retr d t f (d t') = d t' := by
  funext g; simp [retr, h]

/-- **The chain map of a collapse kills the boundary of every collapsed cell.** -/
theorem cmap_bdry_eq_zero {l : List (T × F)} (hl : IsChainCollapse d l) :
    ∀ p ∈ l, cmap d l (d p.1) = 0 := by
  induction l with
  | nil => simp
  | cons p l ih =>
      obtain ⟨t, f⟩ := p
      obtain ⟨hunit, hfree, hrest⟩ := hl
      intro r hr
      rcases List.mem_cons.1 hr with rfl | hrl
      · show cmap d l (retr d t f (d t)) = 0
        rw [retr_self hunit, cmap_zero]
      · show cmap d l (retr d t f (d r.1)) = 0
        rw [retr_of_notMem (hfree r hrl)]
        exact ih hrest r hrl

/-- The chain map of a collapse, applied to a combination of boundaries of top cells. -/
theorem cmap_sum (l : List (T × F)) [DecidableEq T] (s : Finset T) (c : T → R) :
    cmap d l (fun g => ∑ t ∈ s, c t * d t g) = fun g => ∑ t ∈ s, c t * cmap d l (d t) g := by
  induction s using Finset.induction with
  | empty =>
      have hz : (fun g => ∑ t ∈ (∅), c t * d t g) = 0 := by
        funext g; simp
      rw [hz, cmap_zero]
      funext g; simp
  | insert t s ht ih =>
      have hsplit : (fun g => ∑ u ∈ insert t s, c u * d u g)
          = (fun g => c t * d t g) + (fun g => ∑ u ∈ s, c u * d u g) := by
        funext g
        simp
        rw [Finset.sum_insert ht]
      rw [hsplit, cmap_add, cmap_leftMul, ih]
      funext g
      simp
      rw [Finset.sum_insert ht]

/-- **The chain map of a collapse kills every combination of boundaries of collapsed
cells.** -/
theorem cmap_sum_eq_zero {l : List (T × F)} (hl : IsChainCollapse d l) [DecidableEq T]
    (s : Finset T) (c : T → R) (hs : ∀ t ∈ s, ∃ f, (t, f) ∈ l) :
    cmap d l (fun g => ∑ t ∈ s, c t * d t g) = 0 := by
  rw [cmap_sum]
  funext g
  refine Finset.sum_eq_zero fun t htt => ?_
  obtain ⟨f, hf⟩ := hs t htt
  rw [cmap_bdry_eq_zero hl (t, f) hf]
  simp

/-- **The chain map of a collapse fixes the chains of the spine**: a chain which already
vanishes on every collapsed face is left unchanged. -/
theorem cmap_of_forall_eq_zero {l : List (T × F)} (x : F → R) (hx : ∀ p ∈ l, x p.2 = 0) :
    cmap d l x = x := by
  induction l generalizing x with
  | nil => rfl
  | cons p l ih =>
      obtain ⟨t, f⟩ := p
      have hf  := hx (t, f) List.mem_cons_self
      have hretr : retr d t f x = x := by
        funext g; simp [retr, hf]
      show cmap d l (retr d t f x) = x
      rw [hretr]
      exact ih x fun q hq => hx q (List.mem_cons_of_mem _ hq)

/-- **A boundary collapses to the zero chain of the spine.**  If every top cell is collapsed
away, then the cellular chain obtained from a boundary is zero: this is the step "in a
two-complex a homologically zero two-cycle is the zero cellular chain". -/
theorem cmap_eq_zero_of_isBoundary {l : List (T × F)} (hl : IsChainCollapse d l)
    [DecidableEq T] {s : Finset T} {c : T → R} (hs : ∀ t ∈ s, ∃ f, (t, f) ∈ l)
    {x : F → R} (hx : ∀ g, x g = ∑ t ∈ s, c t * d t g) :
    cmap d l x = 0 := by
  have hxe  := funext hx
  rw [hxe]
  exact cmap_sum_eq_zero hl s c hs

/-! ### The surviving three-cell -/

/-! ### Chain complexes presented by linear maps -/

end CollapseChain
end FiniteChains

namespace FiniteChains

open Finset

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- The cellular boundary of the three-cube `t` in the truncated complex, as a coefficient
function on the codimension one faces used by the collapse (squares and cut cells). -/
def cubeBdry (t : Cube V) : Cube V ⊕ Finset V → ℤ :=
  Sum.elim (fun g => bdry (fun f => if f = t then 1 else 0) g)
    (fun τ => cutSign τ * (if posCube τ = t then 1 else 0))

theorem cubeBdry_inl (t g : Cube V) :
    cubeBdry t (Sum.inl g)
      = ∑ j ∈ univ.filter (fun j => g j ≠ CubeCoord.free),
          incid g j * (if Function.update g j CubeCoord.free = t then 1 else 0) := rfl

theorem cubeBdry_inr (t : Cube V) (τ : Finset V) :
    cubeBdry t (Sum.inr τ) = cutSign τ * (if posCube τ = t then 1 else 0) := rfl

omit [Fintype V] [LinearOrder V] in
/-- Freeing a coordinate of a square determines that coordinate: distinct coordinates give
distinct cubes above it. -/
theorem update_free_injective {g : Cube V} {j k : V} (hj : g j ≠ CubeCoord.free)
    (h : Function.update g j CubeCoord.free = Function.update g k CubeCoord.free) : j = k := by
  by_contra hjk
  have hval := congrFun h j
  simp_all

omit [DecidableEq V] in
/-- The incidence number of a cube with a codimension one face is a unit. -/
theorem incid_eq_unit {g : Cube V} {j : V} (hj : g j ≠ CubeCoord.free) :
    incid g j = 1 ∨ incid g j = -1 := by
  have hs : (g j).sgn = 1 ∨ (g j).sgn = -1 := by
    rcases h : g j with _ | _ | _
    · simp_all
    · decide
    · decide
  rcases Nat.even_or_odd ((freeSet g).filter (fun i => i < j)).card with he | ho
  · rw [incid, he.neg_one_pow, one_mul]
    exact hs
  · rw [incid, ho.neg_one_pow]
    rcases hs with h | h <;> rw [h] <;> simp

/-- **The boundary of a three-cube on a square face is `±1` when the cube lies above that
face.** -/
theorem cubeBdry_inl_eq_unit {L : ASC V} {g t : Cube V} (ht : t ∈ cofaces L g) :
    cubeBdry t (Sum.inl g) = 1 ∨ cubeBdry t (Sum.inl g) = -1 := by
  obtain ⟨j, hj, -, rfl⟩ := mem_cofaces.1 ht
  have hmem : j ∈ univ.filter (fun k => g k ≠ CubeCoord.free) := by simp [hj]
  rw [cubeBdry_inl, Finset.sum_eq_single j]
  · rw [if_pos rfl, mul_one]
    exact incid_eq_unit hj
  · intro k hk hkj
    have hk' : g k ≠ CubeCoord.free := by simpa using hk
    rw [if_neg, mul_zero]
    intro hcon
    exact hkj (update_free_injective hk' hcon)
  · simp_all

/-- **A three-cube not lying above a square has zero boundary coefficient there.** -/
theorem cubeBdry_inl_eq_zero {L : ASC V} {g t : Cube V} (htop : t ∈ topCubes L)
    (ht : t ∉ cofaces L g) : cubeBdry t (Sum.inl g) = 0 := by
  rw [cubeBdry_inl]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hj' : g j ≠ CubeCoord.free := by simpa using hj
  rw [if_neg, mul_zero]
  intro hcon
  refine ht (mem_cofaces.2 ⟨j, hj', ?_, hcon.symm⟩)
  have hfree : freeSet (Function.update g j CubeCoord.free) = insert j (freeSet g) := by
    ext i
    by_cases hij : i = j <;> simp [hij]
  rw [← hfree, hcon]
  exact (mem_topCubes.1 htop).1

/-- **The boundary of the truncated corner cube over a triangle on its cut face is `-1`.** -/
theorem cubeBdry_inr_eq_neg_one {τ : Finset V} (hτ : τ.card = 3) :
    cubeBdry (posCube τ) (Sum.inr τ) = -1 := by
  rw [cubeBdry_inr, if_pos rfl, mul_one, cutSign, hτ]
  norm_num

/-- A three-cube other than the truncated corner cube over `τ` has zero coefficient on the
cut face of `τ`. -/
theorem cubeBdry_inr_eq_zero {t : Cube V} {τ : Finset V} (h : t ≠ posCube τ) :
    cubeBdry t (Sum.inr τ) = 0 := by
  rw [cubeBdry_inr, if_neg (Ne.symm h), mul_zero]

/-! ### From a combinatorial collapse to a chain collapse -/

/-- A collapse removes every cell of the collapsed set. -/
theorem Collapse.mem_list_of_isCollapse {T F : Type*} [DecidableEq T] {inc : F → Finset T}
    {l : List T} {S : Finset T} (h : Collapse.IsCollapse inc l S) : ∀ t ∈ S, t ∈ l := by
  induction l generalizing S with
  | nil =>
      intro t ht
      rw [show S = ∅ from h] at ht
      exact absurd ht (Finset.notMem_empty t)
  | cons u l ih =>
      obtain ⟨huS, -, hrest⟩ := h
      intro t ht
      by_cases htu : t = u
      · simp_all
      · exact List.mem_cons_of_mem _ (ih hrest t (Finset.mem_erase.2 ⟨htu, ht⟩))

/-! ### The boundary of a three-chain, cell by cell -/

/-- The boundary of a three-chain of the truncated complex, written as the combination of the
boundaries of its three-cubes. -/
theorem bdryT_eq_sum {c : Cube V → ℤ} {S : Finset (Cube V)} (hc : ∀ t, c t ≠ 0 → t ∈ S)
    (f : Cube V ⊕ Finset V) :
    Sum.elim (bdryT (c, 0)).1 (bdryT (c, 0)).2 f = ∑ t ∈ S, c t * cubeBdry t f := by
  cases f with
  | inl g =>
      show bdry c g = _
      rw [bdry]
      have hswap : ∑ t ∈ S, c t * cubeBdry t (Sum.inl g)
          = ∑ j ∈ univ.filter (fun j => g j ≠ CubeCoord.free),
              incid g j * c (Function.update g j CubeCoord.free) := by
        simp only [cubeBdry_inl, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        have : ∀ t ∈ S, c t * (incid g j * if Function.update g j CubeCoord.free = t then 1
            else 0) = if t = Function.update g j CubeCoord.free then
              c t * incid g j else 0 := by
          intro t _
          by_cases htj : t = Function.update g j CubeCoord.free
          · simp_all
          · grind
        rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' S
          (Function.update g j CubeCoord.free) (fun t => c t * incid g j)]
        by_cases hmem : Function.update g j CubeCoord.free ∈ S
        · grind
        · grind
      rw [hswap]
  | inr τ =>
      show cutSign τ * c (posCube τ) + simpBdry 0 τ = _
      have hz : simpBdry 0 τ = 0 := by simp [simpBdry]
      rw [hz, add_zero]
      have : ∀ t ∈ S, c t * cubeBdry t (Sum.inr τ)
          = if t = posCube τ then cutSign τ * c t else 0 := by
        intro t _
        rw [cubeBdry_inr]
        by_cases htp : t = posCube τ
        · grind
        · grind
      rw [Finset.sum_congr rfl this,
        Finset.sum_ite_eq' S (posCube τ) (fun t => cutSign τ * c t)]
      by_cases hmem : posCube τ ∈ S
      · simp_all
      · grind

/-! ### Lemma 3.3 (iii) after the collapse -/

/-- **The cut surface collapses to the zero chain.**  Let `o` be the fundamental cycle of an
oriented triangulated closed surface `L`, so that the cut surface of the truncated complex
`M = C(L) ∖ (neighbourhood of the corner)` carries the cycle `-o` on its cut cells.  Then
after the collapse of all three-cubes of `M` — the collapse of Lemma 3.3 (ii) — the cellular
chain of the cut surface is zero.  This is Lemma 3.3 (iii) in the form used by the capping
argument of (B3): the image of `[Σ_q]` in the two-dimensional spine is the zero chain. -/
theorem cutSurface_cmap_eq_zero {L : ASC V} {o : Finset V → ℤ} (hcyc : simpBdry o = 0)
    (hsupp : ∀ σ : Finset V, σ.card ≠ 3 → o σ = 0)
    (hfaces : ∀ σ : Finset V, σ ∉ L.faces → o σ = 0)
    {l : List (Cube V)} (hl : Collapse.IsCollapse (spineInc L) l (topCubes L))
    {lp : List (Cube V × (Cube V ⊕ Finset V))} (hmap : lp.map Prod.fst = l)
    (hchain : CollapseChain.IsChainCollapse (cubeBdry (V := V)) lp) :
    CollapseChain.cmap (cubeBdry (V := V)) lp (Sum.elim 0 (fun τ => -o τ)) = 0 := by
  have hc : ∀ t : Cube V, cubeChain o t ≠ 0 → t ∈ topCubes L := by
    intro t ht
    rw [mem_topCubes]
    refine ⟨?_, ?_⟩
    · by_contra hcon
      exact ht (by simp [cubeChain, hfaces _ hcon])
    · by_contra hcon
      exact ht (by simp [cubeChain, hsupp _ hcon])
  have hx : ∀ f : Cube V ⊕ Finset V,
      Sum.elim (0 : Cube V → ℤ) (fun τ => -o τ) f
        = ∑ t ∈ topCubes L, cubeChain o t * cubeBdry t f := by
    intro f
    rw [← bdryT_eq_sum hc f, cutSurface_isBoundary hcyc hsupp]
    cases f with
    | inl g => rfl
    | inr τ => rfl
  have hsub : ∀ t ∈ topCubes L, ∃ f, (t, f) ∈ lp := by
    intro t ht
    have htl  := Collapse.mem_list_of_isCollapse hl t ht
    rw [← hmap] at htl
    obtain ⟨p, hp, hp1⟩ := List.mem_map.1 htl
    exact ⟨p.2, by rw [← hp1]; simpa using hp⟩
  exact CollapseChain.cmap_eq_zero_of_isBoundary hchain hsub hx

end FiniteChains

namespace FiniteChains.Collapse
variable {T F : Type*} [DecidableEq T] (inc : F → Finset T)

/-- Each pair records the actual free face at the time its top cell is removed. -/
def IsPairCollapse : List (T × F) → Finset T → Prop
  | [], S => S = ∅
  | (t, f) :: lp, S => t ∈ S ∧ IsFree inc S f t ∧ IsPairCollapse lp (S.erase t)

variable {inc}

/-- The actual top cells left after deleting a prefix of recorded cell pairs. -/
def remainingTops : Finset T → List (T × F) → Finset T
  | S, [] => S
  | S, p :: lp => remainingTops (S.erase p.1) lp

theorem mem_remainingTops (S : Finset T) (lp : List (T × F)) (t : T) :
    t ∈ remainingTops S lp ↔ t ∈ S ∧ t ∉ lp.map Prod.fst := by
  induction lp generalizing S with
  | nil => simp [remainingTops]
  | cons p lp ih =>
    simp only [remainingTops, ih, Finset.mem_erase, List.map_cons, List.mem_cons]
    tauto

theorem IsPairCollapse.suffix {left right : List (T × F)} {S : Finset T}
    (h : IsPairCollapse inc (left ++ right) S) :
    IsPairCollapse inc right (remainingTops S left) := by
  induction left generalizing S with
  | nil => exact h
  | cons p left ih => exact ih h.2.2

theorem IsPairCollapse.top_mem {lp : List (T × F)} {S : Finset T}
    (h : IsPairCollapse inc lp S) {p : T × F} (hp : p ∈ lp) : p.1 ∈ S := by
  induction lp generalizing S with
  | nil => simp at hp
  | cons q lp ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.1
    · exact Finset.mem_of_mem_erase (ih h.2.2 hp)

theorem IsPairCollapse.map_fst {lp : List (T × F)} {S : Finset T}
    (h : IsPairCollapse inc lp S) : IsCollapse inc (lp.map Prod.fst) S := by
  induction lp generalizing S with
  | nil => exact h
  | cons p lp ih => exact ⟨h.1, ⟨p.2, h.2.1⟩, ih h.2.2⟩

theorem IsPairCollapse.pair_inc {lp : List (T × F)} {S : Finset T}
    (h : IsPairCollapse inc lp S) {p : T × F} (hp : p ∈ lp) : p.1 ∈ inc p.2 := by
  induction lp generalizing S with
  | nil => simp at hp
  | cons q lp ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · have hm : p.1 ∈ inc p.2 ∩ S := by
        rw [h.2.1]
        exact Finset.mem_singleton_self _
      exact (Finset.mem_inter.mp hm).1
    · exact ih h.2.2 hp

/-- No later top cell meets the face deleted by the first elementary collapse. -/
theorem IsPairCollapse.later_top_not_inc {t : T} {f : F} {lp : List (T × F)}
    {S : Finset T} (h : IsPairCollapse inc ((t, f) :: lp) S)
    {p : T × F} (hp : p ∈ lp) : p.1 ∉ inc f := by
  intro hi
  have hs := h.2.2.top_mem hp
  have hm := Finset.mem_inter.mpr ⟨hi, Finset.mem_of_mem_erase hs⟩
  rw [h.2.1] at hm
  simp_all

/-- Earlier deleted faces never occur on the boundary of any later top cell. -/
theorem IsPairCollapse.prefix_faces_avoid_suffix_tops {left right : List (T × F)}
    {S : Finset T} (h : IsPairCollapse inc (left ++ right) S)
    {p r : T × F} (hp : p ∈ left) (hr : r ∈ right) : r.1 ∉ inc p.2 := by
  induction left generalizing S with
  | nil => simp at hp
  | cons a left ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.later_top_not_inc (List.mem_append.mpr (Or.inr hr))
    · exact ih h.2.2 hp

theorem IsPairCollapse.covers {lp : List (T × F)} {S : Finset T}
    (h : IsPairCollapse inc lp S) {t : T} (ht : t ∈ S) : ∃ f, (t, f) ∈ lp := by
  have hm := mem_list_of_isCollapse h.map_fst t ht
  simp_all

/-- Choose the free faces without losing their geometric certificates. -/
theorem exists_pairCollapse {l : List T} {S : Finset T} (h : IsCollapse inc l S) :
    ∃ lp : List (T × F), lp.map Prod.fst = l ∧ IsPairCollapse inc lp S := by
  induction l generalizing S with
  | nil => exact ⟨[], rfl, h⟩
  | cons t l ih =>
    obtain ⟨ht, ⟨f, hf⟩, hr⟩ := h
    obtain ⟨lp, hm, hp⟩ := ih hr
    exact ⟨(t, f) :: lp, by simp [hm], ht, hf, hp⟩

/-- A genuine free-face collapse is also an oriented chain collapse whenever the
differential has unit incidences and vanishes outside actual face incidences. -/
theorem IsPairCollapse.chainCollapse {R : Type*} [Ring R]
    {d : T → F → R} {tops S : Finset T} {lp : List (T × F)}
    (hunit : ∀ t ∈ tops, ∀ f, t ∈ inc f → IsUnit (d t f))
    (hzero : ∀ t ∈ tops, ∀ f, t ∉ inc f → d t f = 0)
    (hS : S ⊆ tops) (h : IsPairCollapse inc lp S) : CollapseChain.IsChainCollapse d lp := by
  induction lp generalizing S with
  | nil => trivial
  | cons p lp ih =>
    have hpinc : p.1 ∈ inc p.2 := by
      have hm : p.1 ∈ inc p.2 ∩ S := by
        rw [h.2.1]
        exact Finset.mem_singleton_self _
      exact (Finset.mem_inter.mp hm).1
    refine ⟨hunit p.1 (hS h.1) p.2 hpinc, ?_,
      ih (fun t ht => hS (Finset.mem_of_mem_erase ht)) h.2.2⟩
    intro q hq
    have hqS := h.2.2.top_mem hq
    apply hzero q.1 (hS (Finset.mem_of_mem_erase hqS)) p.2
    intro hqi
    have hqt : q.1 = p.1 := by
      have hm  :=
        Finset.mem_inter.mpr ⟨hqi, Finset.mem_of_mem_erase hqS⟩
      rw [h.2.1] at hm
      exact Finset.mem_singleton.mp hm
    exact (Finset.mem_erase.mp hqS).1 hqt

end FiniteChains.Collapse

namespace FiniteChains
variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- Both geometric and chain certificates for the very same chosen cubical collapse. -/
theorem exists_geometric_chainCollapse {L : ASC V} {l : List (Cube V)}
    {S : Finset (Cube V)} (hS : S ⊆ topCubes L)
    (h : Collapse.IsCollapse (spineInc L) l S) :
    ∃ lp : List (Cube V × (Cube V ⊕ Finset V)), lp.map Prod.fst = l ∧
      Collapse.IsPairCollapse (spineInc L) lp S ∧
      CollapseChain.IsChainCollapse (cubeBdry (V := V)) lp := by
  obtain ⟨lp, hm, hp⟩ := Collapse.exists_pairCollapse h
  refine ⟨lp, hm, hp, hp.chainCollapse ?_ ?_ hS⟩
  · intro t ht f htf
    cases f with
    | inl g =>
      by_cases hg : (freeSet g).card = 2
      · rw [spineInc, if_pos hg] at htf
        rcases cubeBdry_inl_eq_unit htf with h | h <;> rw [h] <;> simp
      · simp [spineInc, hg] at htf
    | inr σ =>
      by_cases hσ : IsTri L σ
      · rw [spineInc, if_pos hσ, Finset.mem_singleton] at htf
        subst t
        rw [cubeBdry_inr_eq_neg_one hσ.2]
        simp
      · simp [spineInc, hσ] at htf
  · intro t ht f htf
    cases f with
    | inl g =>
      apply cubeBdry_inl_eq_zero ht
      intro hg
      have hcard : (freeSet g).card = 2 := by
        obtain ⟨j, hj, _, he⟩ := mem_cofaces.mp hg
        have hfree : freeSet t = insert j (freeSet g) := by
          rw [he]
          exact freeSet_update_free g j
        have htop := (mem_topCubes.mp ht).2
        rw [hfree, Finset.card_insert_of_notMem (by simpa [mem_freeSet] using hj)] at htop
        omega
      exact htf (by simpa [spineInc, hcard] using hg)
    | inr σ =>
      apply cubeBdry_inr_eq_zero
      intro he
      have hσ : IsTri L σ := by simpa [he] using mem_topCubes.mp ht
      exact htf (by simp [spineInc, hσ, he])

end FiniteChains

namespace FiniteChains
variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

def preferCutFace (p : Cube V × (Cube V ⊕ Finset V)) :
    Cube V × (Cube V ⊕ Finset V) := by
  classical
  exact if p.1 = posCube (freeSet p.1) then (p.1, Sum.inr (freeSet p.1)) else p

def preferCutFaces (lp : List (Cube V × (Cube V ⊕ Finset V))) :=
  lp.map preferCutFace

omit [LinearOrder V] in
theorem preferCutFaces_positive_pair {lp : List (Cube V × (Cube V ⊕ Finset V))}
    {p : Cube V × (Cube V ⊕ Finset V)} (hp : p ∈ preferCutFaces lp)
    (hpos : p.1 = posCube (freeSet p.1)) : p.2 = Sum.inr (freeSet p.1) := by
  obtain ⟨r, _, he⟩ := List.mem_map.mp hp
  subst p
  by_cases hr : r.1 = posCube (freeSet r.1)
  · simp only [preferCutFace, if_pos hr]
  · have hbad : r.1 = posCube (freeSet r.1) := by
      simpa [Collapse.IsPairCollapse,preferCutFace, if_neg hr] using hpos
    exact False.elim (hr hbad)

omit [LinearOrder V] in
theorem preferCutFaces_isPairCollapse {L : ASC V}
    {lp : List (Cube V × (Cube V ⊕ Finset V))} {S : Finset (Cube V)}
    (hS : S ⊆ topCubes L) (h : Collapse.IsPairCollapse (spineInc L) lp S) :
    Collapse.IsPairCollapse (spineInc L) (preferCutFaces lp) S := by
  induction lp generalizing S with
  | nil => exact h
  | cons p lp ih =>
    have ht := mem_topCubes.mp (hS h.1)
    have hrest := ih (fun t ht => hS (Finset.mem_of_mem_erase ht)) h.2.2
    by_cases hp : p.1 = posCube (freeSet p.1)
    · simp only [preferCutFaces, List.map_cons, preferCutFace, if_pos hp]
      refine ⟨h.1, ?_, hrest⟩
      change spineInc L (Sum.inr (freeSet p.1)) ∩ S = {p.1}
      rw [spineInc, if_pos ht, ← hp]
      exact Finset.singleton_inter_of_mem h.1
    · simpa [Collapse.IsPairCollapse,preferCutFaces, List.map_cons, preferCutFace, if_neg hp] using
        And.intro h.1 (And.intro h.2.1 hrest)

/-- The oriented chain certificate is determined by the actual free-face incidences. -/

theorem preferCutFaces_isChainCollapse {L : ASC V}
    {lp : List (Cube V × (Cube V ⊕ Finset V))} {S : Finset (Cube V)}
    (hS : S ⊆ topCubes L) (h : Collapse.IsPairCollapse (spineInc L) lp S) :
    CollapseChain.IsChainCollapse (cubeBdry (V := V)) (preferCutFaces lp) :=
  (by
    apply (preferCutFaces_isPairCollapse hS h).chainCollapse (tops := topCubes L) ?_ ?_ hS
    · intro t ht f htf
      cases f with
      | inl g =>
        by_cases hg : (freeSet g).card = 2
        · rw [spineInc, if_pos hg] at htf
          rcases cubeBdry_inl_eq_unit htf with hh | hh <;> rw [hh] <;> simp
        · simp [spineInc, hg] at htf
      | inr σ =>
        by_cases hσ : IsTri L σ
        · rw [spineInc, if_pos hσ, Finset.mem_singleton] at htf
          subst t
          rw [cubeBdry_inr_eq_neg_one hσ.2]
          simp
        · simp [spineInc, hσ] at htf
    · intro t ht f htf
      cases f with
      | inl g =>
        apply cubeBdry_inl_eq_zero ht
        intro hg
        have hcard : (freeSet g).card = 2 := by
          obtain ⟨j, hj, _, he⟩ := mem_cofaces.mp hg
          have hfree : freeSet t = insert j (freeSet g) := by
            rw [he]
            exact freeSet_update_free g j
          have htop := (mem_topCubes.mp ht).2
          rw [hfree, Finset.card_insert_of_notMem (by simpa [mem_freeSet] using hj)] at htop
          omega
        exact htf (by simpa [spineInc, hcard] using hg)
      | inr σ =>
        apply cubeBdry_inr_eq_zero
        intro he
        have hσ : IsTri L σ := by simpa [he] using mem_topCubes.mp ht
        exact htf (by simp [spineInc, hσ, he]))

end FiniteChains

namespace FiniteChains.Davis.Genus
open ASC
variable (q : ℕ) [NeZero q]

abbrev GenusVertex := SCell (gvc q) (gec q) (gc q)

instance genusVertexLinearOrder : LinearOrder (GenusVertex q) := by
  classical
  exact LinearOrder.lift' (toLinearExtension : GenusVertex q → LinearExtension (GenusVertex q))
    (fun _ _ h => h)

/-- The actual sequence of oriented cellular cancellation pairs. -/
theorem exists_genus_geometric_chainCollapse :
    ∃ lp : List (Cube (GenusVertex q) ×
        (Cube (GenusVertex q) ⊕ Finset (GenusVertex q))),
      Collapse.IsPairCollapse (spineInc (orderComplex (GenusVertex q))) lp
        (topCubes (orderComplex (GenusVertex q))) ∧
      CollapseChain.IsChainCollapse (cubeBdry (V := GenusVertex q)) lp ∧
      ∀ o : Finset (GenusVertex q) → ℤ,
        simpBdry o = 0 →
        (∀ σ, σ.card ≠ 3 → o σ = 0) →
        (∀ σ, σ ∉ (orderComplex (GenusVertex q)).faces → o σ = 0) →
        CollapseChain.cmap (cubeBdry (V := GenusVertex q)) lp
          (Sum.elim 0 (fun τ => -o τ)) = 0 := by
  obtain ⟨l, hl⟩ := genus_spine_collapse q
  obtain ⟨lp, hm, hp, hc⟩ := exists_geometric_chainCollapse (Finset.Subset.refl _) hl
  exact ⟨lp, hp, hc, fun o hcyc hsupp hfaces =>
    cutSurface_cmap_eq_zero hcyc hsupp hfaces hl hm hc⟩

/-- Choose cut facets for all positive corner cubes while retaining both certificates and
the proved vanishing of the cut-surface cycle. -/
theorem exists_genus_cut_geometric_chainCollapse :
    ∃ lp : List (Cube (GenusVertex q) ×
        (Cube (GenusVertex q) ⊕ Finset (GenusVertex q))),
      Collapse.IsPairCollapse (spineInc (orderComplex (GenusVertex q))) lp
        (topCubes (orderComplex (GenusVertex q))) ∧
      CollapseChain.IsChainCollapse (cubeBdry (V := GenusVertex q)) lp ∧
      (∀ o : Finset (GenusVertex q) → ℤ,
        simpBdry o = 0 →
        (∀ σ, σ.card ≠ 3 → o σ = 0) →
        (∀ σ, σ ∉ (orderComplex (GenusVertex q)).faces → o σ = 0) →
        CollapseChain.cmap (cubeBdry (V := GenusVertex q)) lp
          (Sum.elim 0 (fun τ => -o τ)) = 0) ∧
      ∀ p ∈ lp, p.1 = posCube (freeSet p.1) → p.2 = Sum.inr (freeSet p.1) := by
  obtain ⟨lp, hp, _⟩ := exists_genus_geometric_chainCollapse q
  have hn := preferCutFaces_isPairCollapse (Finset.Subset.refl _) hp
  have hc := preferCutFaces_isChainCollapse (Finset.Subset.refl _) hp
  refine ⟨preferCutFaces lp, hn, hc, ?_, ?_⟩
  · intro o hcyc hsupp hfaces
    exact cutSurface_cmap_eq_zero hcyc hsupp hfaces hn.map_fst rfl hc
  · intro p hp hpos
    exact preferCutFaces_positive_pair hp hpos

/-- The actual sequence retains geometric and oriented certificates and uses the cut facet
of every positive corner cube. -/
def genusChainCollapse := Classical.choose (exists_genus_cut_geometric_chainCollapse q)

theorem genusChainCollapse_isPairCollapse :
    Collapse.IsPairCollapse (spineInc (orderComplex (GenusVertex q))) (genusChainCollapse q)
      (topCubes (orderComplex (GenusVertex q))) :=
  (Classical.choose_spec (exists_genus_cut_geometric_chainCollapse q)).1

theorem genusChainCollapse_isChainCollapse :
    CollapseChain.IsChainCollapse (cubeBdry (V := GenusVertex q)) (genusChainCollapse q) :=
  (Classical.choose_spec (exists_genus_cut_geometric_chainCollapse q)).2.1

theorem genusChainCollapse_cutSurface_eq_zero
    (o : Finset (GenusVertex q) → ℤ) (hcyc : simpBdry o = 0)
    (hsupp : ∀ σ, σ.card ≠ 3 → o σ = 0)
    (hfaces : ∀ σ, σ ∉ (orderComplex (GenusVertex q)).faces → o σ = 0) :
    CollapseChain.cmap (cubeBdry (V := GenusVertex q)) (genusChainCollapse q)
      (Sum.elim 0 (fun τ => -o τ)) = 0 :=
  (Classical.choose_spec (exists_genus_cut_geometric_chainCollapse q)).2.2.1 o hcyc hsupp hfaces

theorem genusChainCollapse_positive_pair
    (p : Cube (GenusVertex q) × (Cube (GenusVertex q) ⊕ Finset (GenusVertex q)))
    (hp : p ∈ genusChainCollapse q) (hpos : p.1 = posCube (freeSet p.1)) :
    p.2 = Sum.inr (freeSet p.1) :=
  (Classical.choose_spec (exists_genus_cut_geometric_chainCollapse q)).2.2.2 p hp hpos

theorem genusChainCollapse_old_face_nonpositive
    (t g : Cube (GenusVertex q))
    (hp : (t, Sum.inl g) ∈ genusChainCollapse q) : t ≠ posCube (freeSet t) := by
  intro ht
  have hh := genusChainCollapse_positive_pair q (t, Sum.inl g) hp ht
  cases hh

/-- Every cut triangle is removed by its own positive corner cube. -/
theorem genusChainCollapse_removes_cut_triangle (σ : Finset (GenusVertex q))
    (hσ : IsTri (orderComplex (GenusVertex q)) σ) :
    Sum.inr σ ∈ (genusChainCollapse q).map Prod.snd := by
  have ht : posCube σ ∈ topCubes (orderComplex (GenusVertex q)) := by
    apply mem_topCubes.mpr
    simpa using hσ
  obtain ⟨f, hf⟩ := (genusChainCollapse_isPairCollapse q).covers ht
  have he : f = Sum.inr σ := by
    simpa using genusChainCollapse_positive_pair q (posCube σ, f) hf (by simp)
  subst f
  exact List.mem_map.mpr ⟨(posCube σ, Sum.inr σ), hf, rfl⟩

end FiniteChains.Davis.Genus

namespace FiniteChains
namespace Comb

open MonoidAlgebra

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]
variable {J : Type u} [Fintype J] [DecidableEq J]

/-! ### Paths in a complex with one vertex -/

theorem isPath_of_subsingleton {V E : Type*} [Subsingleton V] (src tgt : E → V)
    (p : List (E × Bool)) (a b : V) : IsPath src tgt p a b := by
  induction p generalizing a with
  | nil => exact Subsingleton.elim _ _
  | cons e p ih => exact ⟨Subsingleton.elim _ _, ih _⟩

/-! ### The presentation complex -/

/-- The two-complex of the presentation `⟨x_i | r_j⟩`: one vertex, an edge for every
generator and a two-cell for every relator, attached along the relator word. -/
abbrev presComplex (ρ : J → FreeGroup α) : Complex2.{u} where
  V := PUnit.{u + 1}
  E := α
  F := J
  src _ := PUnit.unit
  tgt _ := PUnit.unit
  base _ := PUnit.unit
  att j := FreeGroup.toWord (ρ j)
  att_isLoop _ := isPath_of_subsingleton _ _ _ _ _

/-! ### The cover attached to a normal subgroup of the free group -/

variable (Nsub : Subgroup (FreeGroup α)) [Nsub.Normal]

/-- The image of a generator in the deck group `Q = F/Ñ`. -/
def qof (i : α) : FreeGroup α ⧸ Nsub := QuotientGroup.mk (FreeGroup.of i)

variable {Nsub}

/-- The lift at the vertex `q` of the edge path spelled by a word. -/
def liftPath : List (α × Bool) → (FreeGroup α ⧸ Nsub) →
    List (((FreeGroup α ⧸ Nsub) × α) × Bool)
  | [], _ => []
  | (i, true) :: L, q => ((q, i), true) :: liftPath L (q * qof Nsub i)
  | (i, false) :: L, q => ((q * (qof Nsub i)⁻¹, i), false) :: liftPath L (q * (qof Nsub i)⁻¹)

omit [Fintype α] [DecidableEq α] in
@[simp] theorem liftPath_nil (q : FreeGroup α ⧸ Nsub) : liftPath [] q = [] := rfl

omit [Fintype α] [DecidableEq α] in
@[simp] theorem liftPath_cons_true (i : α) (L : List (α × Bool)) (q : FreeGroup α ⧸ Nsub) :
    liftPath ((i, true) :: L) q = ((q, i), true) :: liftPath L (q * qof Nsub i) := rfl

omit [Fintype α] [DecidableEq α] in
@[simp] theorem liftPath_cons_false (i : α) (L : List (α × Bool)) (q : FreeGroup α ⧸ Nsub) :
    liftPath ((i, false) :: L) q
      = ((q * (qof Nsub i)⁻¹, i), false) :: liftPath L (q * (qof Nsub i)⁻¹) := rfl

omit [Fintype α] in
theorem mk_cons_true (i : α) (L : List (α × Bool)) :
    FreeGroup.mk ((i, true) :: L) = FreeGroup.of i * FreeGroup.mk L :=
  FreeGroup.toWord_inj.mp rfl

omit [Fintype α] in
theorem mk_cons_false (i : α) (L : List (α × Bool)) :
    FreeGroup.mk ((i, false) :: L) = (FreeGroup.of i)⁻¹ * FreeGroup.mk L :=
  FreeGroup.toWord_inj.mp rfl

omit [Fintype α] [DecidableEq α] in
/-- The projection of the lift of a word is the word itself. -/
theorem map_liftPath (L : List (α × Bool)) (q : FreeGroup α ⧸ Nsub) :
    (liftPath L q).map (fun eb => (eb.1.2, eb.2)) = L := by
  induction L generalizing q with
  | nil => rfl
  | cons a L ih =>
      obtain ⟨i, b⟩ := a
      cases b
      · simp_all
      · simp_all


variable (Nsub)

omit [Fintype α] in
/-- The lift at `q` of the word `w` is an edge path from `q` to `q · w`. -/
theorem liftPath_isPath (L : List (α × Bool)) (q : FreeGroup α ⧸ Nsub) :
    IsPath (fun e : (FreeGroup α ⧸ Nsub) × α => e.1)
      (fun e : (FreeGroup α ⧸ Nsub) × α => e.1 * qof Nsub e.2) (liftPath L q) q
      (q * QuotientGroup.mk (FreeGroup.mk L)) := by
  induction L generalizing q with
  | nil =>
      rw [show FreeGroup.mk [] = 1 from rfl]
      simp
  | cons a L ih =>
      obtain ⟨i, b⟩ := a
      cases b
      · have hmk : (QuotientGroup.mk (FreeGroup.mk ((i, false) :: L)))
            = (qof Nsub i)⁻¹ * QuotientGroup.mk (FreeGroup.mk L) := by
          rw [mk_cons_false, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
          rfl
        refine ⟨?_, ?_⟩
        · simp
        · have h := ih (q * (qof Nsub i)⁻¹)
          rw [hmk, ← mul_assoc]
          exact h
      · have hmk : (QuotientGroup.mk (FreeGroup.mk ((i, true) :: L)))
            = qof Nsub i * QuotientGroup.mk (FreeGroup.mk L) := by
          rw [mk_cons_true, QuotientGroup.mk_mul]
          rfl
        refine ⟨rfl, ?_⟩
        have h := ih (q * qof Nsub i)
        rw [hmk, ← mul_assoc]
        exact h

variable (ρ : J → FreeGroup α)

/-- The cover `K_N` of the presentation complex attached to `Ñ ◁ F`: vertices the deck
group `Q = F/Ñ`, one edge `(q, x_i)` from `q` to `q x_i` for every `q` and every generator,
one two-cell `(q, r_j)` attached along the lift at `q` of the relator `r_j`. -/
abbrev coverComplex (hρ : ∀ j, ρ j ∈ Nsub) : Complex2.{u} where
  V := FreeGroup α ⧸ Nsub
  E := (FreeGroup α ⧸ Nsub) × α
  F := (FreeGroup α ⧸ Nsub) × J
  src e := e.1
  tgt e := e.1 * qof Nsub e.2
  base f := f.1
  att f := liftPath (FreeGroup.toWord (ρ f.2)) f.1
  att_isLoop f := by
    have h := liftPath_isPath Nsub (FreeGroup.toWord (ρ f.2)) f.1
    rw [FreeGroup.mk_toWord] at h
    rwa [(QuotientGroup.eq_one_iff (ρ f.2)).2 (hρ f.2), mul_one] at h

variable {Nsub ρ}

/-! ### Coordinates: the cellular chains of the cover as free `ℤ[Q]`-modules -/

variable (Nsub)

/-- The cellular chains on the cells `Q × β` of the cover, read as the free `ℤ[Q]`-module
on `β`. -/
def coords (β : Type u) [Fintype β] [DecidableEq β] :
    (((FreeGroup α ⧸ Nsub) × β) →₀ ℤ) ≃ₗ[ℤ] (β → CoverRing Nsub) :=
  (Finsupp.domLCongr (Equiv.prodComm (FreeGroup α ⧸ Nsub) β)).trans
    ((Finsupp.curryLinearEquiv (R := ℤ)).trans
      ((Finsupp.linearEquivFunOnFinite ℤ ((FreeGroup α ⧸ Nsub) →₀ ℤ) β).trans
        (LinearEquiv.piCongrRight (fun _ => (MonoidAlgebra.coeffLinearEquiv ℤ).symm))))

variable {Nsub}

omit [Fintype α] [DecidableEq α] [Nsub.Normal] in
/-- The coordinates of a cellular chain: the coefficient of the cell `(q, i)`. -/
theorem coords_apply (β : Type u) [Fintype β] [DecidableEq β]
    (c : ((FreeGroup α ⧸ Nsub) × β) →₀ ℤ) (i : β) (q : FreeGroup α ⧸ Nsub) :
    ((coords Nsub β c) i).coeff q = c (q, i) := rfl

omit [Fintype α] [DecidableEq α] in
theorem coords_single (β : Type u) [Fintype β] [DecidableEq β] (q : FreeGroup α ⧸ Nsub)
    (i : β) (n : ℤ) :
    coords Nsub β (Finsupp.single (q, i) n) = Pi.single i (MonoidAlgebra.single q n) := by
  classical
  funext k
  apply MonoidAlgebra.coeff_injective
  refine Finsupp.ext fun q' => ?_
  rw [coords_apply, Finsupp.single_apply]
  by_cases h : k = i
  · subst h
    rw [Pi.single_eq_same, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hq : q = q'
    · simp [hq]
    · simp [hq]
  · rw [Pi.single_eq_of_ne h]
    simp [Ne.symm h]

/-- **The dictionary between the cellular boundary and the Fox derivative.**  In the
coordinates above, the cellular chain carried by the lift at `q` of the word `w` is the
Fox vector `q · (∂w/∂x_i)_i`. -/
theorem coords_pathChain_liftPath (L : List (α × Bool)) (q : FreeGroup α ⧸ Nsub) :
    coords Nsub α (pathChain (liftPath L q))
      = fun i => (MonoidAlgebra.single q (1 : ℤ) : CoverRing Nsub) *
          proj Nsub (fox i (FreeGroup.mk L)) := by
  induction L generalizing q with
  | nil =>
      funext i
      rw [show FreeGroup.mk [] = 1 from rfl]
      simp
  | cons a L ih =>
      obtain ⟨i₀, b⟩ := a
      cases b
      · -- the letter `x_{i₀}⁻¹`
        have hq : (MonoidAlgebra.single (q * (qof Nsub i₀)⁻¹) 1)
            = (MonoidAlgebra.single q 1) *
              proj Nsub (grp (FreeGroup.of i₀)⁻¹) := by
          rw [proj_grp, qgrp, QuotientGroup.mk_inv, MonoidAlgebra.single_mul_single, mul_one]
          rfl
        rw [liftPath_cons_false, pathChain_cons]
        simp
        rw [ih (q * (qof Nsub i₀)⁻¹)]
        funext i
        rw [Pi.add_apply, Pi.neg_apply, coords_single, mk_cons_false, fox_mul, fox_inv,
          map_add, map_neg, map_mul, map_mul, mul_add, mul_neg, ← mul_assoc, ← mul_assoc, ← hq]
        congr 1
        by_cases h : i = i₀
        · simp_all
        · simp_all
      · -- the letter `x_{i₀}`
        have hq : (MonoidAlgebra.single (q * qof Nsub i₀) 1)
            = (MonoidAlgebra.single q 1) *
              proj Nsub (grp (FreeGroup.of i₀)) := by
          rw [proj_grp, qgrp, MonoidAlgebra.single_mul_single, mul_one]
          rfl
        rw [liftPath_cons_true, pathChain_cons]
        simp
        rw [ih (q * qof Nsub i₀)]
        funext i
        rw [Pi.add_apply, coords_single, mk_cons_true, fox_mul, map_add, map_mul, mul_add,
          ← mul_assoc, ← hq]
        congr 1
        by_cases h : i = i₀
        · simp_all
        · simp_all

/-! ### The cellular chain complex of the cover is the Fox complex -/

variable (hρ : ∀ j, ρ j ∈ Nsub)

include hρ in
/-- `∂₂` of the cover complex is the Fox boundary `∂₂(e_j) = (∂r_j/∂x_i)_i`. -/
theorem coverComplex_bdry2 (u : ((FreeGroup α ⧸ Nsub) × J) →₀ ℤ) :
    _root_.FiniteChains.bdry2 Nsub ρ (coords Nsub J u)
      = coords Nsub α (Comb.bdry2 (coverComplex Nsub ρ hρ) u) := by
  induction u using Finsupp.induction_linear with
  | zero => rw [map_zero, _root_.FiniteChains.bdry2_zero, map_zero, map_zero]
  | add u₁ u₂ h₁ h₂ =>
      rw [map_add, _root_.FiniteChains.bdry2_add, h₁, h₂, map_add, ← map_add]
  | single f n =>
      obtain ⟨q, j⟩ := f
      rw [coords_single, bdry2_single, map_smul, coords_pathChain_liftPath, FreeGroup.mk_toWord]
      funext i
      show ∑ j' : J, (Pi.single j (MonoidAlgebra.single q n) : J → CoverRing Nsub) j' *
          proj Nsub (fox i (ρ j')) = _
      rw [Finset.sum_eq_single j (fun j' _ h => by simp [Pi.single_eq_of_ne h])
        (fun h => absurd (Finset.mem_univ j) h)]
      simp only [Pi.single_eq_same, Pi.smul_apply]
      rw [show (MonoidAlgebra.single q n)
          = n • (MonoidAlgebra.single q 1) by
        rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one], smul_mul_assoc]

/-! ### Acyclicity of the cover -/

/-! ### The cover is connected -/

/-! ### The covering map and the deck action -/

/-- The projection of the cover onto the presentation complex. -/
def coverProj : Hom (coverComplex Nsub ρ hρ) (presComplex ρ) where
  onV _ := PUnit.unit
  onE e := e.2
  onF f := f.2
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF f := (map_liftPath (FreeGroup.toWord (ρ f.2)) f.1).symm

end Comb
end FiniteChains

namespace FiniteChains
namespace Comb

open MonoidAlgebra

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]
variable {J : Type u} [Fintype J] [DecidableEq J] (ρ : J → FreeGroup α)

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] in
theorem rel_mem_relSub (j : J) : ρ j ∈ relSub ρ :=
  Subgroup.subset_normalClosure (Set.mem_range_self j)

/-- The universal cover of the presentation complex: the cover attached to the relator
subgroup, with deck group `G = π₁(K)`. -/
abbrev univCover : Complex2.{u} :=
  coverComplex (relSub ρ) ρ (rel_mem_relSub ρ)

/-- **The two-cycles of the universal cover.**  A cellular two-chain of `K̃` is a cycle
exactly when its coordinate vector over `ℤ[G]` is killed by the Fox matrix of the
presentation; that is, `π₂(K) = ker ∂₂` in explicit coordinates. -/
theorem univCover_bdry2_eq_zero_iff (u : ((FreeGroup α ⧸ relSub ρ) × J) →₀ ℤ) :
    Comb.bdry2 (univCover ρ) u = 0 ↔
      ∀ i : α, ∑ j : J, (coords (relSub ρ) J u) j * foxMatrixPres ρ i j = 0 := by
  constructor
  · intro h
    have h' : _root_.FiniteChains.bdry2 (relSub ρ) ρ (coords (relSub ρ) J u) = 0 := by
      rw [coverComplex_bdry2 (rel_mem_relSub ρ), h, map_zero]
    intro i
    have := congrFun h' i
    simpa [_root_.FiniteChains.bdry2, foxMatrixPres, proj_eq_quotRingHom] using this
  · intro h
    have h' : _root_.FiniteChains.bdry2 (relSub ρ) ρ (coords (relSub ρ) J u) = 0 := by
      funext i
      simpa [_root_.FiniteChains.bdry2, foxMatrixPres, proj_eq_quotRingHom] using h i
    rw [coverComplex_bdry2 (rel_mem_relSub ρ)] at h'
    refine (coords (relSub ρ) α).injective ?_
    rw [h']
    exact (map_zero _).symm

end Comb
end FiniteChains

namespace FiniteChains

open MonoidAlgebra

variable {β : Type*} [Fintype β] [DecidableEq β]
variable {K : Type*} [Fintype K] [DecidableEq K] (σ : K → FreeGroup β)

omit [Fintype β] [DecidableEq β] [Fintype K] [DecidableEq K] in
/-- The relators lie in the relator subgroup. -/
theorem rel_mem_relSub' (j : K) : σ j ∈ relSub σ :=
  Subgroup.subset_normalClosure (Set.mem_range_self j)

omit [Fintype β] [DecidableEq β] [Fintype K] [DecidableEq K] in
/-- A group ring over `ℤ` has no additive torsion. -/
theorem nsmul_eq_zero_iff_of_ne {G : Type*} (m : ℕ) (hm : m ≠ 0) (x : MonoidAlgebra ℤ G) :
    m • x = 0 ↔ x = 0 := by simp_all

end FiniteChains

namespace FiniteChains
namespace Comb

open MonoidAlgebra

universe u

variable {α : Type u} [DecidableEq α] {J : Type u} [Fintype J] [DecidableEq J]
variable {Nsub : Subgroup (FreeGroup α)} [Nsub.Normal]
variable {Q : Type u} [Group Q] {K : Type u}

omit [DecidableEq α] [Fintype J] [DecidableEq J] in
/-- The same statement in Fox coordinates: the image of a coefficient vector vanishes iff
each coefficient dies in the group ring of the next stage. -/
theorem mapDomain_mapRange_eq_zero_iff (Φ : (FreeGroup α ⧸ Nsub) →* Q) (g : J → K)
    (hg : Function.Injective g) (v : J →₀ CoverRing Nsub) :
    Finsupp.mapDomain g
        (Finsupp.mapRange (MonoidAlgebra.mapDomainRingHom ℤ Φ) (map_zero _) v) = 0 ↔
      ∀ j, MonoidAlgebra.mapDomainRingHom ℤ Φ (v j) = 0 := by
  constructor
  · intro h j
    have h0 : Finsupp.mapRange (MonoidAlgebra.mapDomainRingHom ℤ Φ) (map_zero _) v = 0 := by
      refine Finsupp.mapDomain_injective hg ?_
      rw [h, Finsupp.mapDomain_zero]
    have := congrArg (fun w : J →₀ MonoidAlgebra ℤ Q => w j) h0
    simpa using this
  · intro h
    have h0 : Finsupp.mapRange (MonoidAlgebra.mapDomainRingHom ℤ Φ) (map_zero _) v = 0 := by
      refine Finsupp.ext fun j => ?_
      simpa using h j
    rw [h0, Finsupp.mapDomain_zero]

variable [Fintype α]

end Comb
end FiniteChains

namespace FiniteChains

open List

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The reduced word of the image of `w` under an injective map of generating sets is the
image of the reduced word of `w`. -/
theorem toWord_map (f : α → β) (hf : Function.Injective f) (w : FreeGroup α) :
    (FreeGroup.map f w).toWord = w.toWord.map (fun p => (f p.1, p.2)) := by
  have hmk : FreeGroup.map f w = FreeGroup.mk (w.toWord.map (fun p => (f p.1, p.2))) := by
    conv_lhs => rw [← FreeGroup.mk_toWord (x := w)]
    rfl
  have hred : FreeGroup.IsReduced (w.toWord.map (fun p => (f p.1, p.2))) :=
    isChain_map_of_isChain _ (fun a b hab hfa => hab (hf hfa))
      (FreeGroup.isReduced_toWord)
  rw [hmk, FreeGroup.toWord_mk, hred.reduce_eq]

namespace Comb

universe u

variable {α β : Type u} [DecidableEq α] [DecidableEq β] {J K : Type u}

/-- An inclusion of presentations — an injective map of generators and an injective map of
two-cells carrying a two-cell to one attached along the same word — is a cellular map of
the presentation complexes. -/
def presInclHom (f : α → β) (hf : Function.Injective f) (ρ : J → FreeGroup α)
    (σ : K → FreeGroup β) (g : J → K) (hg : ∀ j, σ (g j) = FreeGroup.map f (ρ j)) :
    Hom (presComplex ρ) (presComplex σ) where
  onV _ := PUnit.unit
  onE := f
  onF := g
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF j := by
    show FreeGroup.toWord (σ (g j)) = (FreeGroup.toWord (ρ j)).map (fun p => (f p.1, p.2))
    rw [hg j, toWord_map f hf]

@[simp] theorem presInclHom_onE (f : α → β) (hf : Function.Injective f) (ρ : J → FreeGroup α)
    (σ : K → FreeGroup β) (g : J → K) (hg : ∀ j, σ (g j) = FreeGroup.map f (ρ j)) :
    (presInclHom f hf ρ σ g hg).onE = f := rfl

@[simp] theorem presInclHom_onF (f : α → β) (hf : Function.Injective f) (ρ : J → FreeGroup α)
    (σ : K → FreeGroup β) (g : J → K) (hg : ∀ j, σ (g j) = FreeGroup.map f (ρ j)) :
    (presInclHom f hf ρ σ g hg).onF = g := rfl

end Comb
end FiniteChains

namespace FiniteChains
namespace Comb

open MonoidAlgebra

universe u

/-! ### The chain map induced by a cellular map -/

variable {X Y : Complex2.{u}}

/-- The one-chains carried by the image of an edge path. -/
theorem pathChain_map (p : Hom X Y) (l : List (X.E × Bool)) :
    pathChain (l.map (fun eb => (p.onE eb.1, eb.2)))
      = Finsupp.mapDomain p.onE (pathChain l) := by
  induction l with
  | nil => simp
  | cons e l ih =>
      rw [List.map_cons, pathChain_cons, pathChain_cons, ih, Finsupp.mapDomain_add]
      congr 1
      by_cases hb : e.2
      · simp_all
      · have hneg : Finsupp.mapDomain p.onE (-Finsupp.single e.1 1)
            = -Finsupp.mapDomain p.onE (Finsupp.single e.1 (1 : ℤ)) := by
          simpa using (Finsupp.lmapDomain ℤ ℤ p.onE).map_neg (Finsupp.single e.1 1)
        simp [hb, hneg]

/-- The map of one-chains induced by a cellular map. -/
def chain1 (p : Hom X Y) : (X.E →₀ ℤ) →ₗ[ℤ] (Y.E →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ p.onE

/-- The map of two-chains induced by a cellular map. -/
def chain2 (p : Hom X Y) : (X.F →₀ ℤ) →ₗ[ℤ] (Y.F →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ p.onF

@[simp] theorem chain2_apply (p : Hom X Y) (u : X.F →₀ ℤ) :
    chain2 p u = Finsupp.mapDomain p.onF u := rfl

/-- **A cellular map is a chain map**: it commutes with the second boundary. -/
theorem bdry2_chain2 (p : Hom X Y) (u : X.F →₀ ℤ) :
    bdry2 Y (chain2 p u) = chain1 p (bdry2 X u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u₁ u₂ h₁ h₂ => grind
  | single f n =>
      show bdry2 Y (Finsupp.mapDomain p.onF (Finsupp.single f n))
        = Finsupp.mapDomain p.onE (bdry2 X (Finsupp.single f n))
      rw [Finsupp.mapDomain_single, bdry2_single, bdry2_single, p.att_onF f, pathChain_map,
        Finsupp.mapDomain_smul]

/-! ### The lift of an inclusion of presentations to the universal covers -/

variable {α β : Type u} [DecidableEq α] [DecidableEq β] {J K : Type u}

omit [DecidableEq α] [DecidableEq β] in
/-- The lift of an edge path is natural in the generating set. -/
theorem liftPath_map {Nsub : Subgroup (FreeGroup α)} [Nsub.Normal]
    {Msub : Subgroup (FreeGroup β)} [Msub.Normal] (f : α → β)
    (Ψ : (FreeGroup α ⧸ Nsub) →* (FreeGroup β ⧸ Msub))
    (hΨ : ∀ i, Ψ (qof Nsub i) = qof Msub (f i))
    (L : List (α × Bool)) (q : FreeGroup α ⧸ Nsub) :
    liftPath (L.map (fun p => (f p.1, p.2))) (Ψ q)
      = (liftPath L q).map (fun eb => ((Ψ eb.1.1, f eb.1.2), eb.2)) := by
  induction L generalizing q with
  | nil => rfl
  | cons a L ih =>
      obtain ⟨i, b⟩ := a
      cases b
      · have hq : Ψ (q * (qof Nsub i)⁻¹) = Ψ q * (qof Msub (f i))⁻¹ := by
          rw [map_mul, map_inv, hΨ]
        simp only [List.map_cons, liftPath_cons_false]
        rw [← hq, ih (q * (qof Nsub i)⁻¹)]
      · have hq : Ψ (q * qof Nsub i) = Ψ q * qof Msub (f i) := by rw [map_mul, hΨ]
        simp
        rw [← hq, ih (q * qof Nsub i)]

/-- The map of fundamental groups induced by an inclusion of presentations. -/
def presInclGroupHom (f : α → β) (ρ : J → FreeGroup α) (σ : K → FreeGroup β) (g : J → K)
    (hg : ∀ j, σ (g j) = FreeGroup.map f (ρ j)) : PresGroup ρ →* PresGroup σ :=
  QuotientGroup.map _ _ (FreeGroup.map f) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    refine Subgroup.mem_comap.2 ?_
    rw [← hg j]
    exact Subgroup.subset_normalClosure (Set.mem_range_self _))

omit [DecidableEq α] [DecidableEq β] in
@[simp] theorem presInclGroupHom_mk (f : α → β) (ρ : J → FreeGroup α) (σ : K → FreeGroup β)
    (g : J → K) (hg : ∀ j, σ (g j) = FreeGroup.map f (ρ j)) (w : FreeGroup α) :
    presInclGroupHom f ρ σ g hg (QuotientGroup.mk w) =
      QuotientGroup.mk (FreeGroup.map f w) := rfl

/-- **The inclusion of presentations lifts to the universal covers**: the cellular map of
the universal covers whose action on cells is `(q, c) ↦ (Ψ q, c)`. -/
def univCoverInclHom (f : α → β) (hf : Function.Injective f) (ρ : J → FreeGroup α)
    (σ : K → FreeGroup β) (g : J → K) (hg : ∀ j, σ (g j) = FreeGroup.map f (ρ j)) :
    Hom (univCover ρ) (univCover σ) where
  onV := presInclGroupHom f ρ σ g hg
  onE := Prod.map (presInclGroupHom f ρ σ g hg) f
  onF := Prod.map (presInclGroupHom f ρ σ g hg) g
  src_onE _ := rfl
  tgt_onE e := by
    show (presInclGroupHom f ρ σ g hg) e.1 * qof (relSub σ) (f e.2)
      = presInclGroupHom f ρ σ g hg (e.1 * qof (relSub ρ) e.2)
    rw [map_mul]
    rfl
  base_onF _ := rfl
  att_onF c := by
    obtain ⟨q, j⟩ := c
    show liftPath (FreeGroup.toWord (σ (g j))) (presInclGroupHom f ρ σ g hg q)
      = (liftPath (FreeGroup.toWord (ρ j)) q).map
          (fun eb => ((presInclGroupHom f ρ σ g hg eb.1.1, f eb.1.2), eb.2))
    rw [hg j, toWord_map f hf]
    exact liftPath_map f (presInclGroupHom f ρ σ g hg) (fun _ => rfl) _ q

@[simp] theorem univCoverInclHom_onF (f : α → β) (hf : Function.Injective f)
    (ρ : J → FreeGroup α) (σ : K → FreeGroup β) (g : J → K)
    (hg : ∀ j, σ (g j) = FreeGroup.map f (ρ j)) :
    (univCoverInclHom f hf ρ σ g hg).onF = Prod.map (presInclGroupHom f ρ σ g hg) g := rfl

end Comb
end FiniteChains

namespace FiniteChains
namespace Comb

universe u

variable {X Y Z : Complex2.{u}}

/-! ### Functoriality of the universal cover -/

theorem endpt_mapPath (h : Hom X Y) : ∀ (q : List (X.E × Bool)) (a : X.V),
    endpt Y (h.onV a) (mapPath h q) = h.onV (endpt X a q) := by
  intro q
  induction q with
  | nil => simp
  | cons eb t ih =>
      intro a
      show endpt Y (germTgt Y.src Y.tgt (h.onE eb.1, eb.2)) (mapPath h t) = _
      rw [germTgt_onE h eb]
      exact ih (germTgt X.src X.tgt eb)

variable (x₀ : X.V)

/-- The image of a path from `x₀` under a cellular map. -/
def mapPathFrom (h : Hom X Y) (p : PathFrom X x₀) : PathFrom Y (h.onV x₀) :=
  ⟨mapPath h p.1, by
    rw [endpt_mapPath h p.1 x₀]
    exact isPath_mapPath h p.2⟩

theorem endpt_mapPathFrom (h : Hom X Y) (p : PathFrom X x₀) :
    endpt Y (h.onV x₀) (mapPathFrom x₀ h p).1 = h.onV (endpt X x₀ p.1) :=
  endpt_mapPath h p.1 x₀

/-- The map of universal covers induced by a cellular map, on vertices. -/
def univLiftV (h : Hom X Y) (c : UV X x₀) : UV Y (h.onV x₀) :=
  Quotient.map (mapPathFrom x₀ h) (by
    intro p q hpq
    show Htpy Y (h.onV x₀) (endpt Y (h.onV x₀) (mapPathFrom x₀ h p).1)
      (mapPathFrom x₀ h p).1 (mapPathFrom x₀ h q).1
    rw [endpt_mapPathFrom]
    exact mapPath_htpy h hpq) c

@[simp] theorem univLiftV_mk (h : Hom X Y) (p : PathFrom X x₀) :
    univLiftV x₀ h (UV.mk p) = UV.mk (mapPathFrom x₀ h p) := rfl

@[simp] theorem endV_univLiftV (h : Hom X Y) (c : UV X x₀) :
    endV (univLiftV x₀ h c) = h.onV (endV c) := by
  induction c using UV.ind with
  | h p => exact endpt_mapPathFrom x₀ h p

/-- On germs issued from the endpoint, the lift commutes with extension of classes. -/
theorem univLiftV_extend (h : Hom X Y) {eb : X.E × Bool} {c : UV X x₀}
    (hc : endV c = germSrc X.src X.tgt eb) :
    univLiftV x₀ h (extend eb c) = extend (h.onE eb.1, eb.2) (univLiftV x₀ h c) := by
  induction c using UV.ind with
  | h p =>
      have hpos : endpt X x₀ p.1 = germSrc X.src X.tgt eb := hc
      have hgerm  :=
        germSrc_onE h eb
      have hpos' : endpt Y (h.onV x₀) (mapPathFrom x₀ h p).1
          = germSrc Y.src Y.tgt (h.onE eb.1, eb.2) := by
        rw [endpt_mapPathFrom, hgerm, hpos]
      have hl : (mapPathFrom x₀ h (extendP eb p)).1
          = (extendP (h.onE eb.1, eb.2) (mapPathFrom x₀ h p)).1 := by
        rw [extendP_pos hpos']
        show mapPath h (extendP eb p).1 = mapPath h p.1 ++ [(h.onE eb.1, eb.2)]
        rw [extendP_pos hpos]
        simp [mapPath]
      refine Quotient.sound ?_
      show Htpy Y (h.onV x₀) (endpt Y (h.onV x₀) (mapPathFrom x₀ h (extendP eb p)).1)
        (mapPathFrom x₀ h (extendP eb p)).1 (extendP (h.onE eb.1, eb.2) (mapPathFrom x₀ h p)).1
      rw [hl]
      exact Htpy.refl _

/-- The map of universal covers induced by a cellular map, on edges. -/
def univLiftE (h : Hom X Y) (E : UE X x₀) : UE Y (h.onV x₀) :=
  ⟨(univLiftV x₀ h E.1.1, h.onE E.1.2), by
    rw [endV_univLiftV, E.2, h.src_onE]⟩

/-- The map of universal covers induced by a cellular map, on two-cells. -/
def univLiftF (h : Hom X Y) (F : UF X x₀) : UF Y (h.onV x₀) :=
  ⟨(univLiftV x₀ h F.1.1, h.onF F.1.2), by
    rw [endV_univLiftV, F.2, h.base_onF]⟩


theorem uLiftPath_univLiftV (h : Hom X Y) : ∀ (q : List (X.E × Bool)) (c : UV X x₀) (w : X.V),
    IsPath X.src X.tgt q (endV c) w →
      uLiftPath (mapPath h q) (univLiftV x₀ h c)
        = (uLiftPath q c).map (fun Eb => (univLiftE x₀ h Eb.1, Eb.2)) := by
  intro q
  induction q with
  | nil => simp
  | cons eb t ih =>
      intro c w hq
      have hc  := hq.1
      have hc' : endV (univLiftV x₀ h c) = germSrc Y.src Y.tgt (h.onE eb.1, eb.2) := by
        rw [endV_univLiftV, germSrc_onE h eb, hc]
      have hnext : IsPath X.src X.tgt t (endV (extend eb c)) w := by
        rw [endV_extend hc]; exact hq.2
      show uLiftPath ((h.onE eb.1, eb.2) :: mapPath h t) (univLiftV x₀ h c) = _
      rw [uLiftPath_cons hc', uLiftPath_cons hc, List.map_cons,
        (show liftGerm (univLiftV x₀ h c) (h.onE eb.1, eb.2) hc'
      = (univLiftE x₀ h (liftGerm c eb hc).1, (liftGerm c eb hc).2) by
          obtain ⟨e, b⟩ := eb
          cases b with
          | true => rfl
          | false =>
              refine Prod.ext ?_ rfl
              refine Subtype.ext (Prod.ext ?_ rfl)
              exact (univLiftV_extend x₀ h hc).symm), ← univLiftV_extend x₀ h hc,
        ih (extend eb c) w hnext]

variable (X) in
/-- **The lift of a cellular map to the universal covers.** -/
def univLift (h : Hom X Y) (x₀ : X.V) :
    Hom (uCover X x₀) (uCover Y (h.onV x₀)) where
  onV := univLiftV x₀ h
  onE := univLiftE x₀ h
  onF := univLiftF x₀ h
  src_onE := fun _ => rfl
  tgt_onE := by
    intro E
    show extend (h.onE E.1.2, true) (univLiftV x₀ h E.1.1)
      = univLiftV x₀ h (extend (E.1.2, true) E.1.1)
    exact (univLiftV_extend x₀ h (eb := (E.1.2, true)) E.2).symm
  base_onF := fun _ => rfl
  att_onF := by
    intro F
    have hbase : endV F.1.1 = X.base F.1.2 := F.2
    have hatt : IsPath X.src X.tgt (X.att F.1.2) (endV F.1.1) (X.base F.1.2) := by
      rw [hbase]; exact X.att_isLoop F.1.2
    show uLiftPath (Y.att (h.onF F.1.2)) (univLiftV x₀ h F.1.1) = _
    rw [h.att_onF F.1.2]
    exact uLiftPath_univLiftV x₀ h (X.att F.1.2) F.1.1 (X.base F.1.2) hatt

/-! ### `π₂`, the Hurewicz map and the Cockcroft property -/

variable (X) in
/-- **The second homotopy module** of a two-complex at a base vertex: the two-cycles of its
universal cover.  (A two-complex has no three-cells, so `π₂ = H₂` of the universal cover is
the kernel of `∂₂`.) -/
def Pi2 (x₀ : X.V) : Submodule ℤ ((uCover X x₀).F →₀ ℤ) :=
  LinearMap.ker (bdry2 (uCover X x₀))

variable (X) in
/-- **The Hurewicz map** `π₂(X) → H₂(X)`: push a two-cycle of the universal cover down to the
complex. -/
def hurewicz (x₀ : X.V) : ((uCover X x₀).F →₀ ℤ) →ₗ[ℤ] (X.F →₀ ℤ) :=
  chain2 (univProj X x₀)


/-- **A cellular map is zero on `π₂`**: the induced map of two-chains of the universal covers
kills every two-cycle. -/
def ZeroPi2 (h : Hom X Y) : Prop :=
  ∀ (x₀ : X.V) (c : (uCover X x₀).F →₀ ℤ), c ∈ Pi2 X x₀ → chain2 (univLift X h x₀) c = 0

/-- The lift of a cellular map carries `π₂` into `π₂`. -/
theorem mem_pi2_chain2_univLift (h : Hom X Y) {x₀ : X.V} {c : (uCover X x₀).F →₀ ℤ}
    (hc : c ∈ Pi2 X x₀) : chain2 (univLift X h x₀) c ∈ Pi2 Y (h.onV x₀) := by
  have hchain := bdry2_chain2 (univLift X h x₀) c
  have hzero : bdry2 (uCover X x₀) c = 0 := hc
  show bdry2 (uCover Y (h.onV x₀)) (chain2 (univLift X h x₀) c) = 0
  simp_all

end Comb
end FiniteChains

namespace FiniteChains
namespace Comb

universe u

/-! ### Identity and composition of cellular maps -/

/-- The identity cellular map. -/
def Hom.id (X : Complex2.{u}) : Hom X X where
  onV := _root_.id
  onE := _root_.id
  onF := _root_.id
  src_onE := fun _ => rfl
  tgt_onE := fun _ => rfl
  base_onF := fun _ => rfl
  att_onF := fun f => by simp

/-- The composition of cellular maps. -/
def Hom.comp {X Y Z : Complex2.{u}} (g : Hom Y Z) (h : Hom X Y) : Hom X Z where
  onV := g.onV ∘ h.onV
  onE := g.onE ∘ h.onE
  onF := g.onF ∘ h.onF
  src_onE := fun e => by
    show Z.src (g.onE (h.onE e)) = g.onV (h.onV (X.src e))
    rw [g.src_onE, h.src_onE]
  tgt_onE := fun e => by
    show Z.tgt (g.onE (h.onE e)) = g.onV (h.onV (X.tgt e))
    rw [g.tgt_onE, h.tgt_onE]
  base_onF := fun f => by
    show Z.base (g.onF (h.onF f)) = g.onV (h.onV (X.base f))
    rw [g.base_onF, h.base_onF]
  att_onF := fun f => by
    show Z.att (g.onF (h.onF f)) = (X.att f).map (fun eb => (g.onE (h.onE eb.1), eb.2))
    rw [g.att_onF, h.att_onF]
    simp


end Comb


end FiniteChains

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable (P : Type u) [PartialOrder P]

def StrictOrdEdge := {p : P × P // p.1 < p.2}
def StrictOrdTri := {p : P × P × P // p.1 < p.2.1 ∧ p.2.1 < p.2.2}

def strictOrderCx : Complex2.{u} where
  V := P
  E := StrictOrdEdge P
  F := StrictOrdTri P
  src e := e.1.1
  tgt e := e.1.2
  base t := t.1.1
  att t := [((⟨(t.1.1, t.1.2.1), t.2.1⟩ : StrictOrdEdge P), true),
    ((⟨(t.1.2.1, t.1.2.2), t.2.2⟩ : StrictOrdEdge P), true),
    ((⟨(t.1.1, t.1.2.2), t.2.1.trans t.2.2⟩ : StrictOrdEdge P), false)]
  att_isLoop := fun _ => ⟨rfl, rfl, rfl, rfl⟩

/-- The inclusion of nondegenerate simplices into the unnormalized cellular model. -/
def strictOrderIncl : Hom (strictOrderCx P) (orderCx P) where
  onV := id
  onE e := ⟨e.1, e.2.le⟩
  onF t := ⟨t.1, t.2.1.le, t.2.2.le⟩
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF _ := rfl

instance [Finite P] : Finite (strictOrderCx P).E :=
  inferInstanceAs (Finite {p : P × P // p.1 < p.2})
instance [Finite P] : Finite (strictOrderCx P).F :=
  inferInstanceAs (Finite {p : P × P × P // p.1 < p.2.1 ∧ p.2.1 < p.2.2})

variable {P}

/-- Erase a degenerate germ, retaining each genuine edge with its orientation. -/
def normalizeOrdGerm (e : (orderCx P).E × Bool) :
    List ((strictOrderCx P).E × Bool) := by
  classical
  exact if h : e.1.1.1 = e.1.1.2 then [] else
    [(⟨e.1.1, lt_of_le_of_ne e.1.2 h⟩, e.2)]

def normalizeOrdPath (p : List ((orderCx P).E × Bool)) :
    List ((strictOrderCx P).E × Bool) := p.flatMap normalizeOrdGerm

theorem normalizeOrdGerm_isPath (e : (orderCx P).E × Bool) :
    IsPath (strictOrderCx P).src (strictOrderCx P).tgt (normalizeOrdGerm e)
      (germSrc (orderCx P).src (orderCx P).tgt e)
      (germTgt (orderCx P).src (orderCx P).tgt e) := by
  unfold normalizeOrdGerm
  split_ifs with h
  · obtain ⟨e, b⟩ := e
    cases b with
    | false => exact h.symm
    | true => exact h
  · exact isPath_single _

/-- Normalizing an edge path preserves both endpoints. -/
theorem normalizeOrdPath_isPath {p : List ((orderCx P).E × Bool)} {a b : P}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b) :
    IsPath (strictOrderCx P).src (strictOrderCx P).tgt (normalizeOrdPath p) a b := by
  induction p generalizing a with
  | nil => exact hp
  | cons e p ih =>
    obtain ⟨ha, hp⟩ := hp
    subst a
    exact (normalizeOrdGerm_isPath e).append (ih hp)

/-- Removing degenerate simplices preserves connectedness. -/
theorem strictOrderCx_isConnected (h : IsConnected (orderCx P)) :
    IsConnected (strictOrderCx P) := by
  intro a b
  obtain ⟨p, hp⟩ := h a b
  exact ⟨normalizeOrdPath p, normalizeOrdPath_isPath hp⟩

/-- The degenerate loop edge is null-homotopic, by its triangular relation. -/
theorem htpy_ordSelf_nil (a : P) :
    Htpy (orderCx P) a a [ordPos (le_refl a)] [] := by
  let e : Loop (orderCx P) a := ⟨[ordPos (le_refl a)], isPath_ordPos _⟩
  have hmul : Pi1.mk e * Pi1.mk e = Pi1.mk e :=
    Quotient.sound (htpy_orderCx_tri (le_refl a) (le_refl a))
  have hone  := (mul_eq_left).mp hmul
  exact Quotient.exact hone

/-- The normalized single-germ path has the same homotopy class in the weak model. -/
theorem normalizeOrdGerm_htpy (e : (orderCx P).E × Bool) :
    Htpy (orderCx P)
      (germSrc (orderCx P).src (orderCx P).tgt e)
      (germTgt (orderCx P).src (orderCx P).tgt e)
      (mapPath (strictOrderIncl P) (normalizeOrdGerm e)) [e] := by
  unfold normalizeOrdGerm
  split_ifs with h
  · obtain ⟨⟨⟨a, b⟩, hab⟩, o⟩ := e
    change a = b at h
    subst b
    cases o with
    | false =>
      have he := htpy_revPath (isPath_ordPos (le_refl a)) (htpy_ordSelf_nil a)
      simpa [mapPath, revPath, revGerm, ordPos, ordNeg, Bool.not, orderCx] using he.symm
    | true => exact (htpy_ordSelf_nil a).symm
  · exact Htpy.refl _

/-- Erasing degenerate edges does not change an edge path's homotopy class. -/
theorem normalizeOrdPath_htpy {p : List ((orderCx P).E × Bool)} {a b : P}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b) :
    Htpy (orderCx P) a b (mapPath (strictOrderIncl P) (normalizeOrdPath p)) p := by
  induction p generalizing a with
  | nil => exact Htpy.refl _
  | cons e p ih =>
    obtain ⟨ha, hp⟩ := hp
    subst a
    change Htpy (orderCx P) _ _
      (mapPath (strictOrderIncl P) (normalizeOrdGerm e ++ normalizeOrdPath p)) ([e] ++ p)
    rw [mapPath_append]
    exact Htpy.append_congr
      (isPath_mapPath (strictOrderIncl P) (normalizeOrdGerm_isPath e))
      (isPath_mapPath (strictOrderIncl P) (normalizeOrdPath_isPath hp))
      (normalizeOrdGerm_htpy e) (ih hp)

@[simp] theorem normalizeOrdPath_append (p q : List ((orderCx P).E × Bool)) :
    normalizeOrdPath (p ++ q) = normalizeOrdPath p ++ normalizeOrdPath q := by
  simp [normalizeOrdPath]


/-- Each unnormalized triangular relation becomes a genuine triangular relation or a backtrack. -/
theorem normalizeOrdTri_nullhomotopic (f : (orderCx P).F) :
    Htpy (strictOrderCx P) ((orderCx P).base f) ((orderCx P).base f)
      (normalizeOrdPath ((orderCx P).att f)) [] := by
  obtain ⟨⟨a, b, c⟩, hab, hbc⟩ := f
  by_cases he : a = b
  · subst b
    by_cases hf : a = c
    · subst c
      simpa [orderCx, normalizeOrdPath, normalizeOrdGerm] using
        (Htpy.refl (X := strictOrderCx P) (a := a) (b := a) [])
    · have hg : IsPath (strictOrderCx P).src (strictOrderCx P).tgt
          [(⟨(a, c), lt_of_le_of_ne hbc hf⟩, true)] a c := ⟨rfl, rfl⟩
      simpa [orderCx, normalizeOrdPath, normalizeOrdGerm, hf, revPath, revGerm] using
        htpy_append_revPath hg
  · by_cases hf : b = c
    · subst c
      have hg : IsPath (strictOrderCx P).src (strictOrderCx P).tgt
          [(⟨(a, b), lt_of_le_of_ne hab he⟩, true)] a b := ⟨rfl, rfl⟩
      simpa [orderCx, normalizeOrdPath, normalizeOrdGerm, he, revPath, revGerm] using
        htpy_append_revPath hg
    · have hac  := (lt_of_le_of_ne hab he |>.trans (lt_of_le_of_ne hbc hf)).ne
      let t : (strictOrderCx P).F := ⟨(a, b, c), lt_of_le_of_ne hab he, lt_of_le_of_ne hbc hf⟩
      have ht : Htpy (strictOrderCx P) a a ((strictOrderCx P).att t) [] :=
        Htpy.of_step ⟨(strictOrderCx P).att_isLoop t, rfl,
          Or.inr ⟨[], [], t, rfl, rfl⟩⟩
      simpa [t, strictOrderCx, orderCx, normalizeOrdPath, normalizeOrdGerm, he, hf, hac] using ht

/-- Normalize an elementary cancellation while retaining its endpoints. -/
theorem normalizeOrdPath_step {a b : P} {l l' : List ((orderCx P).E × Bool)}
    (h : Step (orderCx P) a b l l') :
    Htpy (strictOrderCx P) a b (normalizeOrdPath l) (normalizeOrdPath l') := by
  obtain ⟨hl, _, hc⟩ := h
  rcases hc with ⟨p, q, e, rfl, rfl⟩ | ⟨p, q, f, rfl, rfl⟩
  · obtain ⟨v, hp, hh⟩ := isPath_append_iff.mp hl
    obtain ⟨hv, hr⟩ := hh
    subst v
    have hq : IsPath (orderCx P).src (orderCx P).tgt q
        (germSrc (orderCx P).src (orderCx P).tgt e) b := by
      simpa using hr.2
    have he := htpy_append_revPath (normalizeOrdGerm_isPath e)
    have ht := he.congr_append (normalizeOrdPath_isPath hp) (normalizeOrdPath_isPath hq)
    simpa only [normalizeOrdPath_append, normalizeOrdPath, List.flatMap_append, List.flatMap_cons,
      (show normalizeOrdGerm (revGerm e) = revPath (normalizeOrdGerm e) by
        unfold normalizeOrdGerm
        simp only [revGerm]
        split_ifs <;> simp [revPath, revGerm]), List.append_assoc, List.append_nil] using ht
  · rw [List.append_assoc] at hl
    obtain ⟨v, hp, hh⟩ := isPath_append_iff.mp hl
    have hv  := hh.1
    subst v
    have hq  := hh.2.2.2
    have ht := (normalizeOrdTri_nullhomotopic f).congr_append
      (normalizeOrdPath_isPath hp) (normalizeOrdPath_isPath hq)
    simpa using ht

/-- Normalization preserves edge-path homotopy. -/
theorem normalizeOrdPath_homotopic {a b : P} {p q : List ((orderCx P).E × Bool)}
    (h : Htpy (orderCx P) a b p q) :
    Htpy (strictOrderCx P) a b (normalizeOrdPath p) (normalizeOrdPath q) := by
  induction h with
  | refl => exact Htpy.refl _
  | tail _ hs ih =>
    rcases hs with hs | hs
    · exact ih.trans (normalizeOrdPath_step hs)
    · exact ih.trans (normalizeOrdPath_step hs).symm

/-- Normalization on edge-loop classes. -/
def strictPi1Normalize (a : P) : Pi1 (orderCx P) a →* Pi1 (strictOrderCx P) a where
  toFun := Quotient.map (fun p =>
    ⟨normalizeOrdPath p.1, normalizeOrdPath_isPath p.2⟩)
    (fun _ _ h => normalizeOrdPath_homotopic h)
  map_one' := rfl
  map_mul' := by
    rintro ⟨p⟩ ⟨q⟩
    apply Quotient.sound
    change Htpy (strictOrderCx P) _ _ (normalizeOrdPath (p.val ++ q.val))
      (normalizeOrdPath p.val ++ normalizeOrdPath q.val)
    rw [normalizeOrdPath_append]
    exact Htpy.refl _


theorem normalizeOrdPath_map_strict (p : List ((strictOrderCx P).E × Bool)) :
    normalizeOrdPath (mapPath (strictOrderIncl P) p) = p := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    change normalizeOrdGerm ((strictOrderIncl P).onE e.1, e.2) ++
      normalizeOrdPath (mapPath (strictOrderIncl P) p) = e :: p
    rw [(show normalizeOrdGerm ((strictOrderIncl P).onE e.1, e.2) = [e] by
      have hn := e.1.2.ne
      simp [normalizeOrdGerm, strictOrderIncl, hn]), ih]
    rfl

/-- The genuine simplicial two-skeleton has exactly the same edge-path fundamental group
as the weak-chain model. No group comparison is supplied as a hypothesis. -/
def strictOrderPi1Equiv (a : P) :
    Pi1 (strictOrderCx P) a ≃* Pi1 (orderCx P) a where
  toFun := pi1Map (strictOrderIncl P) a
  invFun := strictPi1Normalize a
  left_inv := by
    intro z
    induction z using Quotient.inductionOn with
    | h p =>
      apply Quotient.sound
      change Htpy (strictOrderCx P) a a
        (normalizeOrdPath (mapPath (strictOrderIncl P) p.1)) p.1
      rw [normalizeOrdPath_map_strict]
      exact Htpy.refl _
  right_inv := by
    intro z
    induction z using Quotient.inductionOn with
    | h p => exact Quotient.sound (normalizeOrdPath_htpy p.2)
  map_mul' := (pi1Map (strictOrderIncl P) a).map_mul

section Maps
variable {Q : Type u} [PartialOrder Q]

/-- A strict monotone map induces a cellular map on genuine simplicial two-skeleta. -/
def strictOrderCxMap (f : P → Q) (hf : StrictMono f) :
    Hom (strictOrderCx P) (strictOrderCx Q) where
  onV := f
  onE e := ⟨(f e.1.1, f e.1.2), hf e.2⟩
  onF t := ⟨(f t.1.1, f t.1.2.1, f t.1.2.2), hf t.2.1, hf t.2.2⟩
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF _ := rfl

end Maps
end FiniteChains.Comb
end

namespace FiniteChains.Davis.Genus
open RACG Mirror ASC
variable (q : ℕ) [NeZero q]

abbrev GenusTruncatedCell := TruncatedCell (cmpRel (GenusVertex q))

def genusSpineCellSet : Set (GenusTruncatedCell q) :=
  {c | truncatedCellDimension c ≤ 2 ∧
    truncatedFaceIndex c ∉ (genusChainCollapse q).map Prod.snd}

/-- The cells of the actual spine, retaining their face order. -/
def GenusSpineCell := {c : GenusTruncatedCell q // c ∈ genusSpineCellSet q}

instance : PartialOrder (GenusSpineCell q) := Subtype.partialOrder _

instance : Finite (GenusSpineCell q) :=
  Finite.of_injective (fun c : GenusSpineCell q => truncatedFaceIndex c.1)
    (fun _ _ h => Subtype.ext (truncatedFaceIndex_injective h))

theorem genus_removedFace_dimension (c : GenusTruncatedCell q)
    (hc : truncatedFaceIndex c ∈ (genusChainCollapse q).map Prod.snd) :
    truncatedCellDimension c = 2 := by
  obtain ⟨p, hp, he⟩ := List.mem_map.mp hc
  have hi := (genusChainCollapse_isPairCollapse q).pair_inc hp
  rw [he] at hi
  cases c with
  | inl c =>
    have hd : (freeSet (qCubeToCoordinate c.1)).card = 2 := by
      by_contra hn
      rw [freeSet_qCubeToCoordinate] at hn
      simp [truncatedFaceIndex, spineInc, hn] at hi
    simpa [truncatedCellDimension] using hd
  | inr σ =>
    have hs : IsTri (orderComplex (GenusVertex q)) σ.1 := by
      by_contra hn
      simp [truncatedFaceIndex, spineInc, hn] at hi
    change σ.1.card - 1 = 2
    rw [hs.2]

/-- Every vertex and edge survives, since all chosen faces have dimension two. -/
theorem genusSpineCellSet_of_dimension_lt_two (c : GenusTruncatedCell q)
    (hc : truncatedCellDimension c < 2) : c ∈ genusSpineCellSet q := by
  refine ⟨Nat.le_of_lt hc, ?_⟩
  intro hm
  have hd := genus_removedFace_dimension q c hm
  omega

theorem genusSpineCell_dimension_le_two (c : GenusSpineCell q) :
    truncatedCellDimension c.1 ≤ 2 := c.2.1

theorem genus_simplex_mem_faces {σ : Finset (GenusVertex q)}
    (hσ : IsSimplex (cmpRel (GenusVertex q)) σ) :
    σ ∈ (orderComplex (GenusVertex q)).faces := by
  intro a ha b hb _
  exact (isSimplex_cmpRel_iff.mp hσ) a ha b hb

theorem genus_oldCell_removed_iff_dimension_three
    (c : QOld (cmpRel (GenusVertex q))) :
    qCubeToCoordinate c.1 ∈ (genusChainCollapse q).map Prod.fst ↔
      truncatedCellDimension (Sum.inl c : GenusTruncatedCell q) = 3 := by
  constructor
  · intro hm
    obtain ⟨p, hp, he⟩ := List.mem_map.mp hm
    have ht := (genusChainCollapse_isPairCollapse q).top_mem hp
    rw [he] at ht
    simpa [truncatedCellDimension] using (mem_topCubes.mp ht).2
  · intro hd
    have ht : qCubeToCoordinate c.1 ∈ topCubes (orderComplex (GenusVertex q)) := by
      apply mem_topCubes.mpr
      rw [freeSet_qCubeToCoordinate]
      exact ⟨genus_simplex_mem_faces q c.1.isSimplex, hd⟩
    obtain ⟨f, hf⟩ := (genusChainCollapse_isPairCollapse q).covers ht
    exact List.mem_map.mpr ⟨(qCubeToCoordinate c.1, f), hf, rfl⟩

theorem genusTruncatedCell_dimension_le_three (c : GenusTruncatedCell q) :
    truncatedCellDimension c ≤ 3 := by
  cases c with
  | inl c => exact genus_chain_card_le_three q (genus_simplex_mem_faces q c.1.isSimplex)
  | inr σ =>
    have hs := genus_chain_card_le_three q (genus_simplex_mem_faces q σ.2.2)
    change σ.1.card - 1 ≤ 3
    omega

theorem genus_cutCell_dimension_le_two (σ : CutCell (cmpRel (GenusVertex q))) :
    truncatedCellDimension (Sum.inr σ : GenusTruncatedCell q) ≤ 2 := by
  have hs := genus_chain_card_le_three q (genus_simplex_mem_faces q σ.2.2)
  change σ.1.card - 1 ≤ 2
  omega

/-- Exact survival criterion: remove precisely the chosen top cells and their chosen faces. -/
theorem genusSpineCellSet_iff_survives (c : GenusTruncatedCell q) :
    c ∈ genusSpineCellSet q ↔
      truncatedFaceIndex c ∉ (genusChainCollapse q).map Prod.snd ∧
      (match c with
        | .inl d => qCubeToCoordinate d.1 ∉ (genusChainCollapse q).map Prod.fst
        | .inr _ => True) := by
  cases c with
  | inl c =>
    have hmax := genusTruncatedCell_dimension_le_three q (Sum.inl c)
    dsimp only
    rw [genus_oldCell_removed_iff_dimension_three]
    constructor
    · intro h
      exact ⟨h.2, by have := h.1; omega⟩
    · rintro ⟨hf, ht⟩
      exact ⟨by omega, hf⟩
  | inr σ =>
    constructor
    · intro h
      exact ⟨h.2, trivial⟩
    · rintro ⟨hf, _⟩
      exact ⟨genus_cutCell_dimension_le_two q σ, hf⟩

theorem genusSpineCellDimension_strictMono :
    StrictMono (fun c : GenusSpineCell q => truncatedCellDimension c.1) := by
  intro c d hcd
  apply truncatedCellDimension_strictMono
  exact hcd

/-- The genuine finite simplicial two-complex associated with the surviving cells. -/
def genusSpineCx : Comb.Complex2 := Comb.strictOrderCx (GenusSpineCell q)

instance : Finite (genusSpineCx q).E :=
  inferInstanceAs (Finite (Comb.strictOrderCx (GenusSpineCell q)).E)
instance : Finite (genusSpineCx q).F :=
  inferInstanceAs (Finite (Comb.strictOrderCx (GenusSpineCell q)).F)

def genusSpineCellToOld (c : GenusSpineCell q) : QOld (cmpRel (GenusVertex q)) :=
  truncatedCellRetraction c.1

theorem genusSpineCellToOld_monotone : Monotone (genusSpineCellToOld q) :=
  fun _ _ h => truncatedCellRetraction_monotone h

/-- The comparison to the older cube-poset block is constructed from the actual cells. -/
def genusSpineToOld : Comb.Hom (genusSpineCx q) (Comb.orderCx (QOld (cmpRel (GenusVertex q)))) :=
  Comb.Hom.comp (Comb.orderCxMap (genusSpineCellToOld q) (genusSpineCellToOld_monotone q))
    (Comb.strictOrderIncl (GenusSpineCell q))

/-- The full cut one-skeleton survives. This supplies the cells of the canonical markings. -/
def genusSpineCutCell (σ : NeSpx (cmpRel (GenusVertex q))) (hσ : σ.1.card ≤ 2) :
    GenusSpineCell q :=
  ⟨Sum.inr ⟨σ.1, σ.2⟩, genusSpineCellSet_of_dimension_lt_two q _ (by
    change σ.1.card - 1 < 2
    omega)⟩

@[simp] theorem genusSpineCellToOld_cutCell (σ : NeSpx (cmpRel (GenusVertex q)))
    (hσ : σ.1.card ≤ 2) :
    genusSpineCellToOld q (genusSpineCutCell q σ hσ) = posQCube σ := rfl


end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem genus_top_cell_maximal (t : QOld (cmpRel (GenusVertex q)))
    (ht : t.1.spx.card = 3) (x : GenusTruncatedCell q)
    (htx : (Sum.inl t : GenusTruncatedCell q) ≤ x) : x = Sum.inl t := by
  have hmax := genusTruncatedCell_dimension_le_three q x
  have hmono := truncatedCellDimension_monotone htx
  change t.1.spx.card ≤ truncatedCellDimension x at hmono
  have he : truncatedCellDimension (Sum.inl t) =
      truncatedCellDimension x := by
    change t.1.spx.card = truncatedCellDimension x
    omega
  exact (truncatedCell_eq_of_le_of_dimension_eq htx he).symm

/-- A top cube has a genuine old vertex on its boundary different from any deleted two-face.
Use the negative value on every free coordinate, so the removed positive vertex is avoided. -/
theorem genus_top_boundary_nonempty (f : GenusTruncatedCell q)
    (hf : truncatedCellDimension f = 2) (t : QOld (cmpRel (GenusVertex q)))
    (ht : t.1.spx.card = 3) :
    ∃ x : GenusTruncatedCell q, x ≠ f ∧ x < Sum.inl t := by
  let v : QCube (cmpRel (GenusVertex q)) := {
    spx := ∅
    sgn := fun j => if j ∈ t.1.spx then 1 else t.1.sgn j
    isSimplex := isSimplex_empty
    sgn_eq_zero := by simp }
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (by omega : 0 < t.1.spx.card)
  have hv : ¬ (v.spx = ∅ ∧ v.sgn = 0) := by
    rintro ⟨_, hs⟩
    have hh := congrFun hs j
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    change (if j ∈ t.1.spx then 1 else t.1.sgn j) = 0 at hh
    rw [if_pos hj] at hh
    exact h10 hh
  let w : QOld (cmpRel (GenusVertex q)) := ⟨v, hv⟩
  have hw : (Sum.inl w : GenusTruncatedCell q) ≤ Sum.inl t := by
    refine ⟨Finset.empty_subset _, ?_⟩
    intro k hk
    simp [w, v, hk]
  have hdim : truncatedCellDimension (Sum.inl w) = 0 := rfl
  refine ⟨Sum.inl w, ?_, lt_of_le_of_ne hw ?_⟩
  · grind
  · grind

theorem genus_free_face_deletion_injIn
    (C : GenusTruncatedCell q → Prop) (S : Finset (Cube (GenusVertex q)))
    (f : GenusTruncatedCell q) (t : QOld (cmpRel (GenusVertex q)))
    (hf : truncatedCellDimension f = 2) (ht : t.1.spx.card = 3)
    (htC : C (Sum.inl t))
    (hactive : ∀ d : QOld (cmpRel (GenusVertex q)), C (Sum.inl d) →
      d.1.spx.card = 3 → qCubeToCoordinate d.1 ∈ S)
    (hfree : Collapse.IsFree (spineInc (ASC.orderComplex (GenusVertex q))) S
      (truncatedFaceIndex f) (qCubeToCoordinate t.1)) :
    InjIn C (fun x => C x ∧ x ≠ f) := by
  have hinc : qCubeToCoordinate t.1 ∈
      spineInc (ASC.orderComplex (GenusVertex q)) (truncatedFaceIndex f) := by
    have hm : qCubeToCoordinate t.1 ∈
        spineInc (ASC.orderComplex (GenusVertex q)) (truncatedFaceIndex f) ∩ S := by
      rw [hfree]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_inter.mp hm).1
  have hft := truncatedCell_le_of_inc f t hinc
  have hne : (Sum.inl t) ≠ f := by
    intro he
    have hh := congrArg truncatedCellDimension he
    change t.1.spx.card = truncatedCellDimension f at hh
    omega
  apply injIn_delete_free_face htC hft hne
  intro x hx hfx hxf
  have hdim : truncatedCellDimension x = 3 := by
    have hlt := truncatedCellDimension_strictMono (lt_of_le_of_ne hfx hxf.symm)
    have hmax := genusTruncatedCell_dimension_le_three q x
    omega
  cases x with
  | inr σ =>
    have hh := genus_cutCell_dimension_le_two q σ
    omega
  | inl d =>
    have hd  := hdim
    have hL : d.1.spx ∈ (ASC.orderComplex (GenusVertex q)).faces := by
      intro a ha b hb _
      exact (isSimplex_cmpRel_iff.mp d.1.isSimplex) a ha b hb
    have hi := truncatedCell_inc_of_le f d hfx hf hd hL
    have hm := Finset.mem_inter.mpr ⟨hi, hactive d hx hd⟩
    rw [hfree] at hm
    have he  :=
      Finset.mem_singleton.mp hm
    have hc  := qCubeCoordinateEquiv.injective (Subtype.ext he)
    exact congrArg Sum.inl (Subtype.ext hc)

/-- The boundary of a later cube contains no face deleted in the prefix of the actual
chosen collapse. This prevents earlier steps from puncturing the next cube's boundary. -/
theorem genus_later_top_boundary_avoids_prefix_faces
    (left right : List (Cube (GenusVertex q) ×
      (Cube (GenusVertex q) ⊕ Finset (GenusVertex q))))
    (hl : genusChainCollapse q = left ++ right)
    (f : GenusTruncatedCell q) (t : QOld (cmpRel (GenusVertex q)))
    (ht : qCubeToCoordinate t.1 ∈ right.map Prod.fst)
    (hft : f ≤ Sum.inl t) : truncatedFaceIndex f ∉ left.map Prod.snd := by
  intro hf
  obtain ⟨p, hp, hpf⟩ := List.mem_map.mp hf
  obtain ⟨r, hr, hrt⟩ := List.mem_map.mp ht
  have hfullf : truncatedFaceIndex f ∈ (genusChainCollapse q).map Prod.snd := by
    rw [hl]
    exact List.mem_map.mpr ⟨p, List.mem_append.mpr (Or.inl hp), hpf⟩
  have hfullt : qCubeToCoordinate t.1 ∈ (genusChainCollapse q).map Prod.fst := by
    rw [hl]
    exact List.mem_map.mpr ⟨r, List.mem_append.mpr (Or.inr hr), hrt⟩
  have hdimf := genus_removedFace_dimension q f hfullf
  have hdimt  :=
    (genus_oldCell_removed_iff_dimension_three q t).mp hfullt
  have hL : t.1.spx ∈ (ASC.orderComplex (GenusVertex q)).faces := by
    intro a ha b hb _
    exact (isSimplex_cmpRel_iff.mp t.1.isSimplex) a ha b hb
  have hi := truncatedCell_inc_of_le f t hft hdimf hdimt hL
  have hc := genusChainCollapse_isPairCollapse q
  rw [hl] at hc
  have hn := hc.prefix_faces_avoid_suffix_tops hp hr
  rw [hpf, hrt] at hn
  exact hn hi

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

abbrev GenusCollapsePair := Cube (GenusVertex q) ×
  (Cube (GenusVertex q) ⊕ Finset (GenusVertex q))

def genusCollapseStage (left : List (GenusCollapsePair q)) (c : GenusTruncatedCell q) : Prop :=
  truncatedFaceIndex c ∉ left.map Prod.snd ∧
    match c with
    | .inl d => qCubeToCoordinate d.1 ∉ left.map Prod.fst
    | .inr _ => True

theorem genusCollapseStage_nil (c : GenusTruncatedCell q) : genusCollapseStage q [] c := by
  cases c <;> simp [genusCollapseStage]

theorem genusCollapseStage_final_iff (c : GenusTruncatedCell q) :
    genusCollapseStage q (genusChainCollapse q) c ↔ c ∈ genusSpineCellSet q :=
  (genusSpineCellSet_iff_survives q c).symm

theorem genusCollapseStage_active_top (left : List (GenusCollapsePair q))
    (t : QOld (cmpRel (GenusVertex q))) (hc : genusCollapseStage q left (Sum.inl t))
    (ht : t.1.spx.card = 3) :
    qCubeToCoordinate t.1 ∈ Collapse.remainingTops
      (topCubes (ASC.orderComplex (GenusVertex q))) left := by
  apply (Collapse.mem_remainingTops _ _ _).mpr
  refine ⟨mem_topCubes.mpr ⟨?_, by simpa using ht⟩, hc.2⟩
  rw [freeSet_qCubeToCoordinate]
  intro a ha b hb _
  exact (isSimplex_cmpRel_iff.mp t.1.isSimplex) a ha b hb

/-- Every strict boundary cell of a remaining top cube is still present at that stage. -/
theorem genusCollapseStage_boundary_mem (left right : List (GenusCollapsePair q))
    (hl : genusChainCollapse q = left ++ right)
    (t : QOld (cmpRel (GenusVertex q)))
    (ht : qCubeToCoordinate t.1 ∈ right.map Prod.fst)
    (c : GenusTruncatedCell q) (hct : c < Sum.inl t) : genusCollapseStage q left c := by
  refine ⟨genus_later_top_boundary_avoids_prefix_faces q left right hl c t ht hct.le, ?_⟩
  cases c with
  | inr σ => trivial
  | inl d =>
    intro hm
    have hfull : qCubeToCoordinate d.1 ∈ (genusChainCollapse q).map Prod.fst := by
      rw [hl, List.map_append]
      exact List.mem_append.mpr (Or.inl hm)
    have hd := (genus_oldCell_removed_iff_dimension_three q d).mp hfull
    have hlt := truncatedCellDimension_strictMono hct
    have hmax := genusTruncatedCell_dimension_le_three q (Sum.inl t)
    omega

theorem genusCollapseStage_suffix_certificate (left right : List (GenusCollapsePair q))
    (hl : genusChainCollapse q = left ++ right) :
    Collapse.IsPairCollapse (spineInc (ASC.orderComplex (GenusVertex q))) right
      (Collapse.remainingTops (topCubes (ASC.orderComplex (GenusVertex q))) left) := by
  have hc := genusChainCollapse_isPairCollapse q
  rw [hl] at hc
  exact hc.suffix

theorem genusCollapseStage_ordinary_step_iff (left : List (GenusCollapsePair q))
    (f t : QOld (cmpRel (GenusVertex q))) (c : GenusTruncatedCell q) :
    genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1))]) c ↔
      (genusCollapseStage q left c ∧ c ≠ Sum.inl f) ∧ c ≠ Sum.inl t := by
  have hinj : Function.Injective
      (fun d : QOld (cmpRel (GenusVertex q)) => qCubeToCoordinate d.1) := by
    intro d e h
    exact Subtype.ext (qCubeCoordinateEquiv.injective (Subtype.ext h))
  cases c with
  | inl d =>
    simp only [genusCollapseStage, truncatedFaceIndex, List.map_append, List.map_cons,
      List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      ne_eq, Sum.inl.injEq, hinj.eq_iff]
    tauto
  | inr σ => simp [genusCollapseStage, truncatedFaceIndex]

end FiniteChains.Davis.Genus

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

def spineCutSingleton (x : GenusVertex q) : GenusSpineCell q :=
  genusSpineCutCell q (spx1 x) (by simp [spx1_val])

def spineCutPair {x y : GenusVertex q} (h : x ≤ y) : GenusSpineCell q :=
  genusSpineCutCell q (spx2 h) (by
    simpa [spx2_val] using Finset.card_insert_le x ({y} : Finset (GenusVertex q)))

theorem spineCutSingleton_le_pair_left {x y : GenusVertex q} (h : x ≤ y) :
    spineCutSingleton q x ≤ spineCutPair q h := spx1_le_spx2_left h

theorem spineCutSingleton_le_pair_right {x y : GenusVertex q} (h : x ≤ y) :
    spineCutSingleton q y ≤ spineCutPair q h := spx1_le_spx2_right h

/-- Cross the surviving cut edge, normalizing away any degenerate germs. -/
def spineEdgeHop {x y : GenusVertex q} (h : x ≤ y) :
    List ((genusSpineCx q).E × Bool) :=
  normalizeOrdPath [ordPos (spineCutSingleton_le_pair_left q h),
    ordNeg (spineCutSingleton_le_pair_right q h)]

theorem isPath_spineEdgeHop {x y : GenusVertex q} (h : x ≤ y) :
    IsPath (genusSpineCx q).src (genusSpineCx q).tgt (spineEdgeHop q h)
      (spineCutSingleton q x) (spineCutSingleton q y) := by
  apply normalizeOrdPath_isPath
  exact ⟨rfl, rfl, rfl⟩

/-- The actual spine crossing reads the same marked path in the older block model. -/
theorem spineEdgeHop_toOld_htpy {x y : GenusVertex q} (h : x ≤ y) :
    Htpy (orderCx (QOld (cmpRel (GenusVertex q)))) (posQCube (spx1 x)) (posQCube (spx1 y))
      (mapPath (genusSpineToOld q) (spineEdgeHop q h))
      (mapPath (surfCx (cmpRel (GenusVertex q))) (edgeHop h)) := by
  let p  :=
    [ordPos (spineCutSingleton_le_pair_left q h), ordNeg (spineCutSingleton_le_pair_right q h)]
  have hp : IsPath (orderCx (GenusSpineCell q)).src (orderCx (GenusSpineCell q)).tgt p
      (spineCutSingleton q x) (spineCutSingleton q y) := ⟨rfl, rfl, rfl⟩
  let g := orderCxMap (genusSpineCellToOld q) (genusSpineCellToOld_monotone q)
  have hh := mapPath_htpy g (normalizeOrdPath_htpy hp)
  convert hh using 1 <;> simp [p, g, genusSpineToOld, spineEdgeHop, mapPath, Hom.comp,
    spineCutSingleton, spineCutPair, genusSpineCellToOld, genusSpineCutCell,
    truncatedCellRetraction, surfCx, edgeHop, hop, orderCxMap, spx1, spx2, Function.comp_def, ordPos, ordNeg]

/-- A polygon boundary edge, in the genuine simplicial spine. -/
def spineBdEdge (p : Fin (8 * q)) : List ((genusSpineCx q).E × Bool) :=
  spineEdgeHop q (cV_le_cE (gc q) p) ++
    revPath (spineEdgeHop q (cV1_le_cE (gc q) p))

theorem isPath_spineBdEdge (p : Fin (8 * q)) :
    IsPath (genusSpineCx q).src (genusSpineCx q).tgt (spineBdEdge q p)
      (spineCutSingleton q (cV (gc q) p)) (spineCutSingleton q (cV (gc q) (p + 1))) :=
  (isPath_spineEdgeHop q _).append (isPath_revPath (isPath_spineEdgeHop q _))

theorem marking_mapPath_rev {X Y : Complex2} (f : Hom X Y)
    (p : List (X.E × Bool)) : mapPath f (revPath p) = revPath (mapPath f p) := by
  simp [mapPath, revPath, revGerm, List.map_map, Function.comp_def, List.map_reverse]

theorem spineBdEdge_toOld_htpy (p : Fin (8 * q)) :
    Htpy (orderCx (QOld (cmpRel (GenusVertex q))))
      (posQCube (spx1 (cV (gc q) p))) (posQCube (spx1 (cV (gc q) (p + 1))))
      (mapPath (genusSpineToOld q) (spineBdEdge q p))
      (mapPath (surfCx (cmpRel (GenusVertex q))) (bdEdge (gc q) p)) := by
  have h1 := spineEdgeHop_toOld_htpy q (cV_le_cE (gc q) p)
  have h2 := spineEdgeHop_toOld_htpy q (cV1_le_cE (gc q) p)
  have hp1 := h1.symm.isPath (isPath_mapPath (surfCx _) (isPath_edgeHop (cV_le_cE (gc q) p)))
  have hp2 := h2.symm.isPath (isPath_mapPath (surfCx _) (isPath_edgeHop (cV1_le_cE (gc q) p)))
  have hh := Htpy.append_congr hp1 (isPath_revPath hp2) h1 (htpy_revPath hp2 h2)
  simpa only [spineBdEdge, bdEdge, mapPath_append, ← revPath_edgeHop, marking_mapPath_rev] using hh

def spineSidePath (m : ℕ) : List ((genusSpineCx q).E × Bool) :=
  spineBdEdge q (cyc (8 * q) m) ++ spineBdEdge q (cyc (8 * q) (m + 1))


def spineBase : (genusSpineCx q).V :=
  spineCutSingleton q (cV (gc q) (cyc (8 * q) 0))

theorem isPath_spineSidePath {m : ℕ} (hm : m % 2 = 0) :
    IsPath (genusSpineCx q).src (genusSpineCx q).tgt (spineSidePath q m)
      (spineBase q) (spineBase q) := by
  have h1 := isPath_spineBdEdge q (cyc (8 * q) m)
  rw [← cyc_succ] at h1
  have h2 := isPath_spineBdEdge q (cyc (8 * q) (m + 1))
  rw [← cyc_succ] at h2
  have h3 := h1.append h2
  rw [cV_even q hm, cV_even q (k := m + 1 + 1) (by omega)] at h3
  exact h3

/-- The canonical `2q` marked loops, constructed on surviving cells. -/
def spineMarkedLoop (x : Fin q × Bool) : Loop (genusSpineCx q) (spineBase q) :=
  ⟨spineSidePath q (8 * x.1.val + if x.2 then 2 else 0),
    isPath_spineSidePath q (by cases x.2 <;> dsimp <;> omega)⟩

theorem spineMarkedLoop_toOld_htpy (x : Fin q × Bool) :
    Htpy (orderCx (QOld (cmpRel (GenusVertex q)))) (posQCube (gBase q)) (posQCube (gBase q))
      (mapPath (genusSpineToOld q) (spineMarkedLoop q x).1)
      (mapPath (surfCx (cmpRel (GenusVertex q))) (gSig q (x.1.val, x.2))) := by
  let m := 8 * x.1.val + if x.2 then 2 else 0
  have hm : m % 2 = 0 := gIdx_even (x.1.val, x.2)
  have hh := (show Htpy (orderCx (QOld (cmpRel (GenusVertex q))))
      (posQCube (spx1 (cV (gc q) (cyc (8 * q) m))))
      (posQCube (spx1 (cV (gc q) (cyc (8 * q) (m + 1 + 1)))))
      (mapPath (genusSpineToOld q) (spineSidePath q m))
      (mapPath (surfCx (cmpRel (GenusVertex q))) (gPath q m)) by
    have h1 := spineBdEdge_toOld_htpy q (cyc (8 * q) m)
    have h2 := spineBdEdge_toOld_htpy q (cyc (8 * q) (m + 1))
    rw [← cyc_succ] at h1 h2
    have hp1 := h1.symm.isPath (by
      have hp := isPath_mapPath (surfCx _) (isPath_bdEdge (gc q) (cyc (8 * q) m))
      rw [← cyc_succ] at hp
      exact hp)
    have hp2 := h2.symm.isPath (by
      have hp := isPath_mapPath (surfCx _) (isPath_bdEdge (gc q) (cyc (8 * q) (m + 1)))
      rw [← cyc_succ] at hp
      exact hp)
    simpa only [spineSidePath, gPath, pPath, mapPath_append] using
      Htpy.append_congr hp1 hp2 h1 h2)
  rw [cV_even q hm, cV_even q (k := m + 1 + 1) (by omega)] at hh
  simpa [spineMarkedLoop, gSig, Nat.mod_eq_of_lt x.1.isLt, gBase, m] using hh

/-- The actual spine marking maps to precisely the previously verified block marking. -/
theorem spineMarkedLoop_toOld_class (x : Fin q × Bool) :
    pi1Map (genusSpineToOld q) (spineBase q) (Pi1.mk (spineMarkedLoop q x)) =
      Pi1.mk ⟨mapPath (surfCx (cmpRel (GenusVertex q))) (gSig q (x.1.val, x.2)),
        isPath_mapPath (surfCx _) (isPath_gSig q (x.1.val, x.2))⟩ := Quotient.sound (spineMarkedLoop_toOld_htpy q x)

end FiniteChains.Davis.Genus
end

namespace FiniteChains.Comb
variable {P : Type} [PartialOrder P]

/-- Every loop based in `B` has a representative in `B` under an increasing order map
from `C` to `B`. The connecting germs at its base are included explicitly. -/
theorem loop_representative_of_monotone_map {C B : P → Prop}
    (hBC : ∀ x, B x → C x) (r : {x : P // C x} → P) (hr : Monotone r)
    (hrB : ∀ x, B (r x)) (hle : ∀ x, x.1 ≤ r x)
    {a : P} {p : List ((orderCx P).E × Bool)} (ha : B a)
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a a) (hC : PathIn C p) :
    ∃ l, IsPath (orderCx P).src (orderCx P).tgt l a a ∧ PathIn B l ∧
      Htpy (orderCx P) a a p l := by
  let aC : {x : P // C x} := ⟨a, hBC a ha⟩
  let l := mapPath (orderCxMap r hr) (liftPathIn p hC)
  have hl  :=
    isPath_mapPath (orderCxMap r hr) (isPath_liftPathIn p hC aC.2 aC.2 hp)
  have hlB : PathIn B l := by
    intro e he
    obtain ⟨eb, _, rfl⟩ := List.mem_map.mp he
    exact ⟨hrB eb.1.1.1, hrB eb.1.1.2⟩
  let e := [ordPos (hle aC)]
  let en := [ordNeg (hle aC)]
  have he : IsPath (orderCx P).src (orderCx P).tgt e a (r aC) := isPath_ordPos _
  have hen : IsPath (orderCx P).src (orderCx P).tgt en (r aC) a := isPath_ordNeg _
  have heB : PathIn B e := pathIn_cons ⟨ha, hrB aC⟩ (pathIn_nil B)
  have henB : PathIn B en := pathIn_cons ⟨ha, hrB aC⟩ (pathIn_nil B)
  have hnat := htpy_mapPath_le monotone_subtypeVal hr hle
    (liftPathIn p hC) (isPath_liftPathIn p hC aC.2 aC.2 hp)
  change Htpy (orderCx P) a (r aC)
    (mapPath (subposetHom C) (liftPathIn p hC) ++ e) (e ++ l) at hnat
  rw [mapPath_liftPathIn] at hnat
  have hpush := hnat.congr_append (show IsPath (orderCx P).src (orderCx P).tgt [] a a from rfl) hen
  have hkill := (htpy_ordPos_ordNeg (hle aC)).congr_append hp
    (show IsPath (orderCx P).src (orderCx P).tgt [] a a from rfl)
  refine ⟨e ++ l ++ en, (he.append hl).append hen,
    pathIn_append (pathIn_append heB hlB) henB, ?_⟩
  have hstrip : Htpy (orderCx P) a a p ((p ++ e) ++ en) := by
    simpa [e, en, List.append_assoc] using hkill.symm
  exact hstrip.trans (by simpa only [List.nil_append] using hpush)

/-- Deleting an actual free face preserves representatives of all loops based away from it. -/
theorem loop_representative_delete_free_face {C : P → Prop} {f t a : P}
    (ht : C t) (hft : f ≤ t) (hne : t ≠ f)
    (hunique : ∀ x, C x → f ≤ x → x ≠ f → x = t)
    {p : List ((orderCx P).E × Bool)} (ha : C a ∧ a ≠ f)
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a a) (hC : PathIn C p) :
    ∃ l, IsPath (orderCx P).src (orderCx P).tgt l a a ∧
      PathIn (fun x => C x ∧ x ≠ f) l ∧ Htpy (orderCx P) a a p l := by
  classical
  let r : {x : P // C x} → P := fun x => if x.1 = f then t else x.1
  have hr : Monotone r := by
    intro x y hxy
    by_cases hx : x.1 = f
    · by_cases hy : y.1 = f
      · simp [r, hx, hy]
      · have hyt  := hunique y.1 y.2 (hx ▸ hxy) hy
        simp [r, hx, hyt]
    · by_cases hy : y.1 = f
      · have hxf : x.1 ≤ f := hy ▸ hxy
        simpa [r, hx, hy] using hxf.trans hft
      · simpa [r, hx, hy] using hxy
  apply loop_representative_of_monotone_map (fun _ h => h.1) r hr ?_ ?_ ha hp hC
  · grind
  · grind

end FiniteChains.Comb

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
variable {P : Type} [PartialOrder P]

theorem germ_into_maximal_lt {C : P → Prop} {t : P}
    (hmax : ∀ x, C x → t ≤ x → x = t) (e : (orderCx P).E × Bool)
    (he : C e.1.1.1 ∧ C e.1.1.2)
    (ht : germTgt (orderCx P).src (orderCx P).tgt e = t)
    (hne : germSrc (orderCx P).src (orderCx P).tgt e ≠ t) :
    (germSrc (orderCx P).src (orderCx P).tgt e : P) < t := by
  obtain ⟨e, b⟩ := e
  cases b with
  | true =>
    change e.1.2 = t at ht
    change e.1.1 ≠ t at hne
    change e.1.1 < t
    exact lt_of_le_of_ne (ht ▸ e.2) hne
  | false =>
    change e.1.1 = t at ht
    change e.1.2 ≠ t at hne
    exact False.elim (hne (hmax e.1.2 he.2 (ht ▸ e.2)))

 theorem maximal_detour_germs {C : P → Prop} {t u v : P}
    (hmax : ∀ x, C x → t ≤ x → x = t)
    (hconn : ConnectedIn (fun x => C x ∧ x < t))
    (e f : (orderCx P).E × Bool)
    (he : IsPath (orderCx P).src (orderCx P).tgt [e] u t)
    (hf : IsPath (orderCx P).src (orderCx P).tgt [f] t v)
    (hC : PathIn C [e, f]) (hu : u ≠ t) (hv : v ≠ t) :
    ∃ l, IsPath (orderCx P).src (orderCx P).tgt l u v ∧
      PathIn (fun x => C x ∧ x ≠ t) l ∧ Htpy (orderCx P) u v [e, f] l := by
  have heC := (pathIn_of_cons hC).1
  have hfC := (pathIn_of_cons (pathIn_of_cons hC).2).1
  have heends := germ_ends heC
  have hfends := germ_ends hfC
  have hes : germSrc (orderCx P).src (orderCx P).tgt e = u := he.1.symm
  have het : germTgt (orderCx P).src (orderCx P).tgt e = t := he.2
  have hfs : germSrc (orderCx P).src (orderCx P).tgt f = t := hf.1.symm
  have hft : germTgt (orderCx P).src (orderCx P).tgt f = v := hf.2
  have hut : u < t := by
    simpa only [hes] using germ_into_maximal_lt hmax e heC het (hes ▸ hu)
  have hvt : v < t := by
    have hrC : C (revGerm f).1.1.1 ∧ C (revGerm f).1.1.2 := hfC
    have hr := germ_into_maximal_lt hmax (revGerm f) hrC
      (by simpa using hfs) (by simpa [hft] using hv)
    rwa [germSrc_revGerm, hft] at hr
  obtain ⟨l, hl, hB⟩ := hconn u v ⟨hes ▸ heends.1, hut⟩ ⟨hft ▸ hfends.2, hvt⟩
  have hp : IsPath (orderCx P).src (orderCx P).tgt [e, f] u v := he.append hf
  have hT : PathIn (fun x : P => x ≤ t) [e, f] := by
    apply pathIn_cons
    · obtain ⟨e, b⟩ := e
      cases b with
      | false =>
        change e.1.2 = u at hes
        change e.1.1 = t at het
        exact ⟨het ▸ le_refl t, hes ▸ hut.le⟩
      | true =>
        change e.1.1 = u at hes
        change e.1.2 = t at het
        exact ⟨hes ▸ hut.le, het ▸ le_refl t⟩
    · apply pathIn_cons
      · obtain ⟨f, b⟩ := f
        cases b with
        | false =>
          change f.1.2 = t at hfs
          change f.1.1 = v at hft
          exact ⟨hft ▸ hvt.le, hfs ▸ le_refl t⟩
        | true =>
          change f.1.1 = t at hfs
          change f.1.2 = v at hft
          exact ⟨hfs ▸ le_refl t, hft ▸ hvt.le⟩
      · exact pathIn_nil _
  refine ⟨l, hl, pathIn_mono (fun _ hx => ⟨hx.1, hx.2.ne⟩) hB, ?_⟩
  apply Davis.htpy_of_loop_nil hp hl
  exact htpy_nil_of_pathIn_le_top (A := fun x : P => x ≤ t) (le_refl t)
    (fun _ h => h) hut.le (hp.append (isPath_revPath hl))
    (pathIn_append hT (pathIn_revPath (pathIn_mono (fun _ hx => hx.2.le) hB)))

theorem germ_ends_iff {B : P → Prop} (e : (orderCx P).E × Bool) :
    (B e.1.1.1 ∧ B e.1.1.2) ↔
      (B (germSrc (orderCx P).src (orderCx P).tgt e) ∧
        B (germTgt (orderCx P).src (orderCx P).tgt e)) := by
  obtain ⟨e, b⟩ := e
  cases b <;> simp only [germSrc, germTgt, Bool.false_eq_true, if_false, if_true]
  · exact and_comm
  · rfl

/-- A nondegenerate path with endpoints away from a maximal cell has a homotopic
representative avoiding that cell. -/
theorem maximal_path_representative_nondegenerate {C : P → Prop} {t : P}
    (hmax : ∀ x, C x → t ≤ x → x = t)
    (hconn : ConnectedIn (fun x => C x ∧ x < t))
    (p : List ((orderCx P).E × Bool)) {a b : P}
    (ha : C a ∧ a ≠ t) (hb : C b ∧ b ≠ t)
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b) (hC : PathIn C p)
    (hnd : ∀ e ∈ p, germSrc (orderCx P).src (orderCx P).tgt e ≠
      germTgt (orderCx P).src (orderCx P).tgt e) :
    ∃ l, IsPath (orderCx P).src (orderCx P).tgt l a b ∧
      PathIn (fun x => C x ∧ x ≠ t) l ∧ Htpy (orderCx P) a b p l := by
  induction p using List.twoStepInduction generalizing a with
  | nil => exact ⟨[], hp, pathIn_nil _, Htpy.refl _⟩
  | singleton e =>
    refine ⟨[e], hp, pathIn_cons ?_ (pathIn_nil _), Htpy.refl _⟩
    apply (germ_ends_iff (B := fun x => C x ∧ x ≠ t) e).mpr
    exact ⟨hp.1 ▸ ha, hp.2.symm ▸ hb⟩
  | cons_cons e f p ih ihTail =>
    have heC := (pathIn_of_cons hC).1
    have htail := (pathIn_of_cons hC).2
    have hfC := (pathIn_of_cons htail).1
    have hrest := (pathIn_of_cons htail).2
    have he : IsPath (orderCx P).src (orderCx P).tgt [e] a
        (germTgt (orderCx P).src (orderCx P).tgt e) := ⟨hp.1, rfl⟩
    have hwC := (germ_ends heC).2
    by_cases hw : germTgt (orderCx P).src (orderCx P).tgt e = t
    · have hf : IsPath (orderCx P).src (orderCx P).tgt [f] t
          (germTgt (orderCx P).src (orderCx P).tgt f) := ⟨hw ▸ hp.2.1, rfl⟩
      have hv : germTgt (orderCx P).src (orderCx P).tgt f ≠ t := by
        intro hvt
        exact hnd f (by simp) (by rw (config := { transparency := .default }) [← hf.1, hvt])
      have hpair : PathIn C [e, f] := pathIn_cons heC (pathIn_cons hfC (pathIn_nil _))
      obtain ⟨l, hl, hB, hh⟩ := maximal_detour_germs hmax hconn e f
        (hw ▸ he) hf hpair ha.2 hv
      obtain ⟨r, hr, hrB, hhr⟩ := ih ⟨(germ_ends hfC).2, hv⟩ hp.2.2 hrest
        (fun g hg => hnd g (by simp [hg]))
      exact ⟨l ++ r, hl.append hr, pathIn_append hB hrB,
        Htpy.append_congr (he.append (by simpa only [hw] using hf)) hp.2.2 hh hhr⟩
    · obtain ⟨r, hr, hrB, hh⟩ := ihTail f ⟨hwC, hw⟩ hp.2 htail
        (fun g hg => hnd g (List.mem_cons_of_mem e hg))
      have heB : PathIn (fun x => C x ∧ x ≠ t) [e] := by
        apply pathIn_cons
        · exact (germ_ends_iff (B := fun x => C x ∧ x ≠ t) e).mpr ⟨hp.1 ▸ ha, ⟨hwC, hw⟩⟩
        · exact pathIn_nil _
      exact ⟨[e] ++ r, he.append hr, pathIn_append heB hrB,
        Htpy.append_congr he hp.2 (Htpy.refl _) hh⟩

theorem normalizeOrdGerm_properties {C : P → Prop} (e : (orderCx P).E × Bool)
    (hC : C e.1.1.1 ∧ C e.1.1.2) :
    PathIn C (mapPath (strictOrderIncl P) (normalizeOrdGerm e)) ∧
      ∀ g ∈ mapPath (strictOrderIncl P) (normalizeOrdGerm e),
        germSrc (orderCx P).src (orderCx P).tgt g ≠
          germTgt (orderCx P).src (orderCx P).tgt g := by
  classical
  unfold normalizeOrdGerm
  split_ifs with h
  · exact ⟨pathIn_nil _, by simp [mapPath]⟩
  · constructor
    · exact pathIn_cons hC (pathIn_nil _)
    · intro g hg
      have hg' : g = (⟨e.1.1, e.1.2⟩, e.2) := by simpa [mapPath, strictOrderIncl] using hg
      subst g
      obtain ⟨e, b⟩ := e
      cases b with
      | false => exact Ne.symm h
      | true => exact h

theorem normalizeOrdPath_properties {C : P → Prop}
    (p : List ((orderCx P).E × Bool)) (hC : PathIn C p) :
    PathIn C (mapPath (strictOrderIncl P) (normalizeOrdPath p)) ∧
      ∀ g ∈ mapPath (strictOrderIncl P) (normalizeOrdPath p),
        germSrc (orderCx P).src (orderCx P).tgt g ≠
          germTgt (orderCx P).src (orderCx P).tgt g := by
  induction p with
  | nil => exact ⟨pathIn_nil _, by simp [normalizeOrdPath, mapPath]⟩
  | cons e p ih =>
    have he := normalizeOrdGerm_properties e (pathIn_of_cons hC).1
    have hp := ih (pathIn_of_cons hC).2
    change PathIn C (mapPath (strictOrderIncl P) (normalizeOrdGerm e ++ normalizeOrdPath p)) ∧ _
    rw (config := { transparency := .default }) [mapPath_append]
    refine ⟨pathIn_append he.1 hp.1, ?_⟩
    intro g hg
    have hg' : g ∈ mapPath (strictOrderIncl P) (normalizeOrdGerm e) ++
        mapPath (strictOrderIncl P) (normalizeOrdPath p) := by
      simpa only [normalizeOrdPath, List.flatMap_cons, mapPath_append] using hg
    exact (List.mem_append.mp hg').elim (he.2 g) (hp.2 g)

/-- Complete maximal-cell path replacement, with no nondegeneracy assumption. -/
theorem maximal_path_representative {C : P → Prop} {t : P}
    (hmax : ∀ x, C x → t ≤ x → x = t)
    (hconn : ConnectedIn (fun x => C x ∧ x < t))
    (p : List ((orderCx P).E × Bool)) {a b : P}
    (ha : C a ∧ a ≠ t) (hb : C b ∧ b ≠ t)
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b) (hC : PathIn C p) :
    ∃ l, IsPath (orderCx P).src (orderCx P).tgt l a b ∧
      PathIn (fun x => C x ∧ x ≠ t) l ∧ Htpy (orderCx P) a b p l := by
  have hn := normalizeOrdPath_properties p hC
  have hpath := isPath_mapPath (strictOrderIncl P) (normalizeOrdPath_isPath hp)
  obtain ⟨l, hl, hB, hh⟩ := maximal_path_representative_nondegenerate hmax hconn
    _ ha hb hpath hn.1 hn.2
  exact ⟨l, hl, hB, (normalizeOrdPath_htpy hp).symm.trans hh⟩

end FiniteChains.Comb

namespace FiniteChains.Comb

theorem htpy_nil_of_conjugate {X : Complex2} {a b : X.V}
    {e p : List (X.E × Bool)} (he : IsPath X.src X.tgt e a b)
    (hp : IsPath X.src X.tgt p a a)
    (h : Htpy X b b (revPath e ++ p ++ e) []) : Htpy X a a p [] := by
  have hc := htpy_append_revPath he
  have hA := hc.congr_append (show IsPath X.src X.tgt [] a a from rfl)
    (hp.append (he.append (isPath_revPath he)))
  have hB := hc.congr_append hp (show IsPath X.src X.tgt [] a a from rfl)
  have hstrip : Htpy X a a (e ++ (revPath e ++ p ++ e) ++ revPath e) p := by
    simpa [List.append_assoc] using hA.trans (by simpa using hB)
  have hstep := h.congr_append he (isPath_revPath he)
  have hkill  :=
    hstep.trans (by simpa using hc)
  exact hstrip.symm.trans hkill

variable {P Q : Type} [Preorder P] [Preorder Q]

/-- Pointwise comparable monotone maps preserve and reflect null homotopy of their images.
The proof uses the connecting edge at the base and cancels it, so fixed bases are unnecessary. -/
theorem htpy_nil_mapPath_le_iff {f g : P → Q} (hf : Monotone f) (hg : Monotone g)
    (hfg : ∀ x, f x ≤ g x) {a : P} {p : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a a) :
    Htpy (orderCx Q) (f a) (f a) (mapPath (orderCxMap f hf) p) [] ↔
      Htpy (orderCx Q) (g a) (g a) (mapPath (orderCxMap g hg) p) [] := by
  have hnat := htpy_loop_mapPath_le hf hg hfg hp
  constructor
  · intro h
    have hh := h.congr_append (isPath_ordNeg (hfg a)) (isPath_ordPos (hfg a))
    exact hnat.trans (hh.trans (by simpa using htpy_ordNeg_ordPos (hfg a)))
  · intro h
    apply htpy_nil_of_conjugate (isPath_ordPos (hfg a))
      (isPath_mapPath (orderCxMap f hf) hp)
    simpa [revPath, revGerm, ordPos, ordNeg, Bool.not] using hnat.symm.trans h

/-- An explicit three-step order contraction gives simple connectedness. -/
theorem simplyConnected_orderCx_of_zigzag {f g : P → P}
    (hf : Monotone f) (hg : Monotone g) (hig : ∀ x, x ≤ g x)
    (hfg : ∀ x, f x ≤ g x) (d : P) (hfd : ∀ x, f x ≤ d) :
    SimplyConnected (orderCx P) := by
  intro a p hp
  have hc := htpy_nil_mapPath_const d hp
  have hfnil := (htpy_nil_mapPath_le_iff hf monotone_const hfd hp).mpr hc
  have hgnil := (htpy_nil_mapPath_le_iff hf hg hfg hp).mp hfnil
  have hinil := (htpy_nil_mapPath_le_iff monotone_id hg hig hp).mpr hgnil
  simpa [mapPath, orderCxMap] using hinil

/-- The same contraction supplies paths to the common point, hence connectedness. -/
theorem isConnected_orderCx_of_zigzag {f g : P → P}
    (hig : ∀ x, x ≤ g x) (hfg : ∀ x, f x ≤ g x)
    (d : P) (hfd : ∀ x, f x ≤ d) : IsConnected (orderCx P) := by
  let p a : List ((orderCx P).E × Bool) :=
    [ordPos (hig a), ordNeg (hfg a), ordPos (hfd a)]
  have hp a : IsPath (orderCx P).src (orderCx P).tgt (p a) a d :=
    ⟨rfl, rfl, rfl, rfl⟩
  intro a b
  exact ⟨p a ++ revPath (p b), (hp a).append (isPath_revPath (hp b))⟩

end FiniteChains.Comb
end

namespace FiniteChains.Davis
variable {V : Type} [DecidableEq V]

def coordinateFix (j : V) (z : CubeCoord) (c : Cube V) : Cube V :=
  Function.update c j z

/-- Open the selected coordinate, except on the opposite facet, which stays fixed. -/
def coordinateOpen (j : V) (z : CubeCoord) (c : Cube V) : Cube V :=
  if c j = z then c else Function.update c j CubeCoord.free

theorem coordinateFix_face_mono (j : V) (z : CubeCoord) {c d : Cube V}
    (h : CoordinateFace c d) : CoordinateFace (coordinateFix j z c) (coordinateFix j z d) := by
  intro v
  by_cases hv : v = j
  · subst v
    right
    simp only [coordinateFix, Function.update_self]
  · simpa only [coordinateFix, Function.update_of_ne hv] using h v

theorem coordinateOpen_face_mono (j : V) (z : CubeCoord) (hz : z ≠ CubeCoord.free)
    {c d : Cube V} (h : CoordinateFace c d) :
    CoordinateFace (coordinateOpen j z c) (coordinateOpen j z d) := by
  intro v
  by_cases hv : v = j
  · subst v
    by_cases hd : d j = z
    · have hc : c j = z := by
        rcases h j with hf | he
        · exact False.elim (hz (hd.symm.trans hf))
        · exact he.trans hd
      right
      simp [coordinateOpen, hc, hd]
    · left
      simp only [coordinateOpen, if_neg hd, Function.update_self]
  · have hc : coordinateOpen j z c v = c v := by
      unfold coordinateOpen
      split
      · rfl
      · exact Function.update_of_ne hv _ _
    have hd : coordinateOpen j z d v = d v := by
      unfold coordinateOpen
      split
      · rfl
      · exact Function.update_of_ne hv _ _
    rw [hc, hd]
    exact h v

theorem coordinate_face_open (j : V) (z : CubeCoord) (c : Cube V) :
    CoordinateFace c (coordinateOpen j z c) := by
  intro v
  unfold coordinateOpen
  grind

theorem coordinate_fix_face_open (j : V) (z : CubeCoord) (c : Cube V) :
    CoordinateFace (coordinateFix j z c) (coordinateOpen j z c) := by
  intro v
  by_cases hv : v = j
  · subst v
    by_cases hc : c j = z
    · right
      simp [coordinateFix, coordinateOpen, hc, Function.update_self]
    · left
      simp only [coordinateOpen, if_neg hc, Function.update_self]
  · have ho : coordinateOpen j z c v = c v := by
      unfold coordinateOpen
      split
      · rfl
      · exact Function.update_of_ne hv _ _
    right
    simp only [coordinateFix, Function.update_of_ne hv, ho]

theorem coordinateFix_face_opposite_facet (j : V) (z : CubeCoord)
    {c t : Cube V} (h : CoordinateFace c t) :
    CoordinateFace (coordinateFix j z c) (coordinateFix j z t) :=
  coordinateFix_face_mono j z h

theorem coordinateOpen_face_top (j : V) (z : CubeCoord)
    {c t : Cube V} (ht : t j = CubeCoord.free) (h : CoordinateFace c t) :
    CoordinateFace (coordinateOpen j z c) t := by
  intro v
  by_cases hv : v = j
  · simp_all
  · have ho : coordinateOpen j z c v = c v := by
      unfold coordinateOpen
      split
      · rfl
      · exact Function.update_of_ne hv _ _
    rw [ho]
    exact h v


theorem coordinateOpen_ne_top (j : V) (b z : CubeCoord)
    (hb : b ≠ CubeCoord.free) (hz : z ≠ CubeCoord.free) (hbz : b ≠ z)
    {c t : Cube V} (ht : t j = CubeCoord.free) (hct : c ≠ t)
    (hcf : c ≠ coordinateFix j b t) : coordinateOpen j z c ≠ t := by
  intro he
  by_cases hc : c j = z
  · exact hct (by simpa [coordinateOpen, hc] using he)
  · have hrest : ∀ v, v ≠ j → c v = t v := by
      intro v hv
      have hh := congrFun he v
      simpa only [coordinateOpen, if_neg hc, Function.update_of_ne hv] using hh
    rcases (show (c j) = CubeCoord.free ∨ (c j) = b ∨ (c j) = z by
      cases b <;> cases z <;> cases (c j) <;> simp_all) with hfree | hval | hval
    · grind
    · apply hcf
      funext v
      by_cases hv : v = j
      · subst v
        simpa only [coordinateFix, Function.update_self] using hval
      · simpa only [coordinateFix, Function.update_of_ne hv] using hrest v hv
    · exact hc hval

theorem coordinateFix_ne_top (j : V) (z : CubeCoord) (hz : z ≠ CubeCoord.free)
    {c t : Cube V} (ht : t j = CubeCoord.free) : coordinateFix j z c ≠ t := by
  intro he
  have hh := congrFun he j
  simp only [coordinateFix, Function.update_self, ht] at hh
  exact hz hh

theorem coordinateFix_ne_facet (j : V) (b z : CubeCoord) (hbz : b ≠ z)
    (c t : Cube V) : coordinateFix j z c ≠ coordinateFix j b t := by
  intro he
  have hh := congrFun he j
  simp only [coordinateFix, Function.update_self] at hh
  exact hbz hh.symm

theorem coordinateOpen_ne_facet (j : V) (b z : CubeCoord)
    (hb : b ≠ CubeCoord.free) (hbz : b ≠ z) (c t : Cube V) :
    coordinateOpen j z c ≠ coordinateFix j b t := by
  intro he
  have hh := congrFun he j
  by_cases hc : c j = z
  · simp only [coordinateOpen, if_pos hc, coordinateFix, Function.update_self] at hh
    exact hbz (hh.symm.trans hc)
  · simp only [coordinateOpen, if_neg hc, coordinateFix, Function.update_self] at hh
    exact hb hh.symm

end FiniteChains.Davis

namespace FiniteChains.Davis
open Comb
variable {V : Type} [DecidableEq V]

def PuncturedCubeFace (t : Cube V) (j : V) (b : CubeCoord) :=
  {c : Cube V // CoordinateFace c t ∧ c ≠ t ∧ c ≠ coordinateFix j b t}

instance (t : Cube V) (j : V) (b : CubeCoord) : PartialOrder (PuncturedCubeFace t j b) where
  le c d := CoordinateFace c.1 d.1
  le_refl c v := Or.inr rfl
  le_trans c d e hcd hde v := by
    rcases hde v with he | he
    · simp_all
    · rcases hcd v with hd | hd
      · exact Or.inl (he.symm.trans hd)
      · exact Or.inr (hd.trans he)
  le_antisymm c d hcd hdc := by
    apply Subtype.ext
    funext v
    rcases hcd v with hd | hd
    · rcases hdc v with hc | hc
      · exact hc.trans hd.symm
      · exact hc.symm
    · exact hd

omit [DecidableEq V] in
theorem face_trans {c d e : Cube V} (hcd : CoordinateFace c d)
    (hde : CoordinateFace d e) : CoordinateFace c e := by
  intro v
  rcases hde v with he | he
  · simp_all
  · rcases hcd v with hd | hd
    · exact Or.inl (he.symm.trans hd)
    · exact Or.inr (hd.trans he)

variable (t : Cube V) (j : V) (b z : CubeCoord)
  (hb : b ≠ CubeCoord.free) (hz : z ≠ CubeCoord.free) (hbz : b ≠ z)
  (ht : t j = CubeCoord.free)

def punctureProject (c : PuncturedCubeFace t j b) : PuncturedCubeFace t j b :=
  ⟨coordinateFix j z c.1,
    face_trans (coordinate_fix_face_open j z c.1)
      (coordinateOpen_face_top j z ht c.2.1),
    coordinateFix_ne_top j z hz ht, coordinateFix_ne_facet j b z hbz c.1 t⟩

def punctureOpen (c : PuncturedCubeFace t j b) : PuncturedCubeFace t j b :=
  ⟨coordinateOpen j z c.1,
    coordinateOpen_face_top j z ht c.2.1,
    coordinateOpen_ne_top j b z hb hz hbz ht c.2.2.1 c.2.2.2,
    coordinateOpen_ne_facet j b z hb hbz c.1 t⟩

def punctureOpposite : PuncturedCubeFace t j b :=
  ⟨coordinateFix j z t,
    face_trans (coordinate_fix_face_open j z t)
      (coordinateOpen_face_top j z ht (fun _ => Or.inr rfl)),
    coordinateFix_ne_top j z hz ht, coordinateFix_ne_facet j b z hbz t t⟩

theorem punctureProject_monotone : Monotone (punctureProject t j b z hz hbz ht) := by
  intro c d h
  exact coordinateFix_face_mono j z h

theorem punctureOpen_monotone : Monotone (punctureOpen t j b z hb hz hbz ht) := by
  intro c d h
  exact coordinateOpen_face_mono j z hz h

include z hb hz hbz ht in
/-- Every based edge loop of the ordinary punctured cube boundary is null homotopic. -/
theorem puncturedCubeBoundary_simplyConnected :
    SimplyConnected (orderCx (PuncturedCubeFace t j b)) := by
  apply simplyConnected_orderCx_of_zigzag
    (punctureProject_monotone t j b z hz hbz ht)
    (punctureOpen_monotone t j b z hb hz hbz ht)
    (fun c => coordinate_face_open j z c.1)
    (fun c => coordinate_fix_face_open j z c.1)
    (punctureOpposite t j b z hz hbz ht)
  intro c
  exact coordinateFix_face_opposite_facet j z c.2.1

include z hb hz hbz ht in
theorem puncturedCubeBoundary_isConnected :
    IsConnected (orderCx (PuncturedCubeFace t j b)) := by
  apply isConnected_orderCx_of_zigzag
    (f := punctureProject t j b z hz hbz ht)
    (g := punctureOpen t j b z hb hz hbz ht)
    (fun c => coordinate_face_open j z c.1)
    (fun c => coordinate_fix_face_open j z c.1)
    (punctureOpposite t j b z hz hbz ht)
  intro c
  exact coordinateFix_face_opposite_facet j z c.2.1

/-- Every genuine facet puncture is connected; no contraction data are assumed. -/
theorem ordinary_puncturedCubeBoundary_connected (t : Cube V) (j : V) (b : CubeCoord)
    (hb : b ≠ CubeCoord.free) (ht : t j = CubeCoord.free) :
    IsConnected (orderCx (PuncturedCubeFace t j b)) := by
  cases b with
  | free => simp_all
  | pos => exact puncturedCubeBoundary_isConnected t j .pos .neg hb (by decide) (by decide) ht
  | neg => exact puncturedCubeBoundary_isConnected t j .neg .pos hb (by decide) (by decide) ht

/-- Every genuine facet puncture is simply connected; no homotopy property is assumed. -/
theorem ordinary_puncturedCubeBoundary_simplyConnected (t : Cube V) (j : V) (b : CubeCoord)
    (hb : b ≠ CubeCoord.free) (ht : t j = CubeCoord.free) :
    SimplyConnected (orderCx (PuncturedCubeFace t j b)) := by
  cases b with
  | free => simp_all
  | pos => exact puncturedCubeBoundary_simplyConnected t j .pos .neg hb (by decide) (by decide) ht
  | neg => exact puncturedCubeBoundary_simplyConnected t j .neg .pos hb (by decide) (by decide) ht

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [Fintype V] [DecidableEq V] {A : CommRel V}

def OldPuncturedBoundary (f t : QOld A) :=
  {c : TruncatedCell A // c < Sum.inl t ∧ c ≠ Sum.inl f}

instance (f t : QOld A) : PartialOrder (OldPuncturedBoundary f t) := Subtype.partialOrder _

def boundaryOldCell {f t : QOld A} (ht : t.1.sgn ≠ 0)
    (c : OldPuncturedBoundary f t) : QOld A := by
  rcases c with ⟨c, hc⟩
  cases c with
  | inl d => exact d
  | inr σ => exact False.elim (ht hc.1.le.2)

omit [Fintype V] in
theorem boundaryOldCell_eq {f t : QOld A} (ht : t.1.sgn ≠ 0)
    (c : OldPuncturedBoundary f t) : c.1 = Sum.inl (boundaryOldCell ht c) := by
  rcases c with ⟨c, hc⟩
  cases c with
  | inl d => rfl
  | inr σ => exact False.elim (ht hc.1.le.2)

def ordinaryBoundaryToCoordinate {f t : QOld A} (ht : t.1.sgn ≠ 0)
    (j : V) (b : CubeCoord) (hf : qCubeToCoordinate f.1 = coordinateFix j b (qCubeToCoordinate t.1))
    (c : OldPuncturedBoundary f t) : PuncturedCubeFace (qCubeToCoordinate t.1) j b := by
  let d := boundaryOldCell ht c
  have hd := boundaryOldCell_eq ht c
  have hle : d.1 ≤ t.1 := by
    have h := c.2.1.le
    rw [hd] at h
    exact h
  refine ⟨qCubeToCoordinate d.1, (qCubeToCoordinate_face_iff d.1 t.1).mp hle, ?_, ?_⟩
  · intro he
    have hdt : d = t := Subtype.ext
      (qCubeCoordinateEquiv.injective (Subtype.ext he))
    exact c.2.1.ne (hd.trans (congrArg Sum.inl hdt))
  · intro he
    have hdf : d = f := Subtype.ext
      (qCubeCoordinateEquiv.injective (Subtype.ext (he.trans hf.symm)))
    exact c.2.2 (hd.trans (congrArg Sum.inl hdf))

def coordinateBoundaryToOrdinary {f t : QOld A} (ht : t.1.sgn ≠ 0)
    (j : V) (b : CubeCoord) (hf : qCubeToCoordinate f.1 = coordinateFix j b (qCubeToCoordinate t.1))
    (c : PuncturedCubeFace (qCubeToCoordinate t.1) j b) : OldPuncturedBoundary f t := by
  have hs : freeSet c.1 ⊆ t.1.spx := by
    intro v hv
    have hvc := mem_freeSet.mp hv
    have hvt : v ∈ freeSet (qCubeToCoordinate t.1) := by
      rcases c.2.1 v with he | he
      · exact mem_freeSet.mpr he
      · exact mem_freeSet.mpr (he.symm.trans hvc)
    simpa using hvt
  let d : QCube A := coordinateToQCube ⟨c.1, isSimplex_subset A hs t.1.isSimplex⟩
  have hd : qCubeToCoordinate d = c.1 := coordinateToQCube_toCoordinate _
  have hdt : d ≤ t.1 := (qCubeToCoordinate_face_iff d t.1).mpr (hd ▸ c.2.1)
  have hold : ¬ (d.spx = ∅ ∧ d.sgn = 0) := by
    rintro ⟨_, hz⟩
    exact ht (qCube_sgn_zero_of_face hdt hz)
  let w : QOld A := ⟨d, hold⟩
  refine ⟨Sum.inl w, lt_of_le_of_ne hdt ?_, ?_⟩
  · intro he
    have hw : w = t := Sum.inl.inj he
    have hh : c.1 = qCubeToCoordinate t.1 := hd.symm.trans
      (congrArg (fun x : QOld A => qCubeToCoordinate x.1) hw)
    exact c.2.2.1 hh
  · intro he
    have hw : w = f := Sum.inl.inj he
    have hh : c.1 = coordinateFix j b (qCubeToCoordinate t.1) := hd.symm.trans
      ((congrArg (fun x : QOld A => qCubeToCoordinate x.1) hw).trans hf)
    exact c.2.2.2 hh

theorem coordinateBoundaryToOrdinary_coordinate {f t : QOld A} (ht : t.1.sgn ≠ 0)
    (j : V) (b : CubeCoord) (hf : qCubeToCoordinate f.1 = coordinateFix j b (qCubeToCoordinate t.1))
    (c : PuncturedCubeFace (qCubeToCoordinate t.1) j b) :
    qCubeToCoordinate (boundaryOldCell ht (coordinateBoundaryToOrdinary ht j b hf c)).1 = c.1 :=
  coordinateToQCube_toCoordinate _

/-- The actual boundary of a cube away from the cut corner has exactly the ordinary
coordinate faces, with their actual incidence order. -/
def ordinaryTruncatedBoundaryOrderIso {f t : QOld A} (ht : t.1.sgn ≠ 0)
    (j : V) (b : CubeCoord) (hf : qCubeToCoordinate f.1 = coordinateFix j b (qCubeToCoordinate t.1)) :
    OldPuncturedBoundary f t ≃o PuncturedCubeFace (qCubeToCoordinate t.1) j b where
  toFun := ordinaryBoundaryToCoordinate ht j b hf
  invFun := coordinateBoundaryToOrdinary ht j b hf
  left_inv c := by
    apply Subtype.ext
    rw [boundaryOldCell_eq ht (coordinateBoundaryToOrdinary ht j b hf
      (ordinaryBoundaryToCoordinate ht j b hf c)), boundaryOldCell_eq ht c]
    apply congrArg Sum.inl
    apply Subtype.ext
    apply qCubeCoordinateEquiv.injective
    apply Subtype.ext
    exact coordinateBoundaryToOrdinary_coordinate ht j b hf
      (ordinaryBoundaryToCoordinate ht j b hf c)
  right_inv c := by
    apply Subtype.ext
    exact coordinateBoundaryToOrdinary_coordinate ht j b hf c
  map_rel_iff' := by
    intro c d
    change CoordinateFace (qCubeToCoordinate (boundaryOldCell ht c).1)
      (qCubeToCoordinate (boundaryOldCell ht d).1) ↔ c.1 ≤ d.1
    rw [boundaryOldCell_eq ht c, boundaryOldCell_eq ht d]
    exact (qCubeToCoordinate_face_iff (boundaryOldCell ht c).1 (boundaryOldCell ht d).1).symm



theorem exists_facet_coordinates_of_inc {L : ASC V} (f t : QOld A)
    (hi : qCubeToCoordinate t.1 ∈ spineInc L (Sum.inl (qCubeToCoordinate f.1))) :
    ∃ j : V, ∃ b : CubeCoord, b ≠ CubeCoord.free ∧
      qCubeToCoordinate t.1 j = CubeCoord.free ∧
      qCubeToCoordinate f.1 = coordinateFix j b (qCubeToCoordinate t.1) := by
  have hm : qCubeToCoordinate t.1 ∈ cofaces L (qCubeToCoordinate f.1) := by
    simp only [spineInc] at hi
    split at hi
    · exact hi
    · simp at hi
  obtain ⟨j, hj, _, he⟩ := mem_cofaces.mp hm
  refine ⟨j, qCubeToCoordinate f.1 j, hj, ?_, ?_⟩
  · simp_all
  · funext v
    by_cases hv : v = j
    · subst v
      exact (Function.update_self j (qCubeToCoordinate f.1 j) (qCubeToCoordinate t.1)).symm
    · simp only [coordinateFix, Function.update_of_ne hv, he]



def swappedBoundaryOrderIso (f t : QOld A) :
    {x : TruncatedCell A // x ≠ Sum.inl f ∧ x < Sum.inl t} ≃o OldPuncturedBoundary f t where
  toFun x := ⟨x.1, x.2.2, x.2.1⟩
  invFun x := ⟨x.1, x.2.2, x.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by intros; rfl

theorem ordinaryTruncatedBoundary_connectedIn {L : ASC V} {f t : QOld A}
    (ht : t.1.sgn ≠ 0)
    (hi : qCubeToCoordinate t.1 ∈ spineInc L (Sum.inl (qCubeToCoordinate f.1))) :
    ConnectedIn (fun x : TruncatedCell A => x ≠ Sum.inl f ∧ x < Sum.inl t) := by
  apply connectedIn_of_isConnected
  exact isConnected_orderCx_of_orderIso (swappedBoundaryOrderIso f t)
    (by
      obtain ⟨j, b, hb, htj, hf⟩ := exists_facet_coordinates_of_inc f t hi
      exact (isConnected_orderCx_of_orderIso (ordinaryTruncatedBoundaryOrderIso ht j b hf)
    (ordinary_puncturedCubeBoundary_connected _ j b hb htj)))

theorem ordinaryTruncatedBoundary_simplyConnectedIn {L : ASC V} {f t : QOld A}
    (ht : t.1.sgn ≠ 0)
    (hi : qCubeToCoordinate t.1 ∈ spineInc L (Sum.inl (qCubeToCoordinate f.1))) :
    SimplyConnectedIn (fun x : TruncatedCell A => x ≠ Sum.inl f ∧ x < Sum.inl t) := by
  apply simplyConnectedIn_of_simplyConnected
  exact simplyConnected_orderCx_of_orderIso (swappedBoundaryOrderIso f t)
    (by
      obtain ⟨j, b, hb, htj, hf⟩ := exists_facet_coordinates_of_inc f t hi
      exact (simplyConnected_orderCx_of_orderIso (ordinaryTruncatedBoundaryOrderIso ht j b hf)
    (ordinary_puncturedCubeBoundary_simplyConnected _ j b hb htj)))

end FiniteChains.Davis

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

/-- An ordinary pair anywhere in the chosen collapse reflects null homotopies between
the actual consecutive stages. Earlier deletions impose no extra boundary hypothesis. -/
theorem genus_ordinary_pair_stage_injIn
    (left right : List (GenusCollapsePair q))
    (f t : QOld (cmpRel (GenusVertex q)))
    (hf : f.1.spx.card = 2) (ht : t.1.spx.card = 3) (hordinary : t.1.sgn ≠ 0)
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1)) :: right)) :
    InjIn (genusCollapseStage q left)
      (genusCollapseStage q
        (left ++ [(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1))])) := by
  let p : GenusCollapsePair q := (qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1))
  have htail : qCubeToCoordinate t.1 ∈ (p :: right).map Prod.fst := by simp [p]
  have hc := genusCollapseStage_suffix_certificate q left (p :: right) hsplit
  have hfree := hc.2.1
  have hi : qCubeToCoordinate t.1 ∈ spineInc (ASC.orderComplex (GenusVertex q))
      (Sum.inl (qCubeToCoordinate f.1)) := by
    have hm : qCubeToCoordinate t.1 ∈
        spineInc (ASC.orderComplex (GenusVertex q)) (Sum.inl (qCubeToCoordinate f.1)) ∩
          Collapse.remainingTops (topCubes (ASC.orderComplex (GenusVertex q))) left := by
      rw [hfree]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_inter.mp hm).1
  have htC : genusCollapseStage q left (Sum.inl t) :=
    ⟨genus_later_top_boundary_avoids_prefix_faces q left (p :: right) hsplit
        (Sum.inl t) t htail (le_refl _),
      ((Collapse.mem_remainingTops _ _ _).mp hc.1).2⟩
  have hface := genus_free_face_deletion_injIn q (genusCollapseStage q left)
    (Collapse.remainingTops (topCubes (ASC.orderComplex (GenusVertex q))) left)
    (Sum.inl f) t hf ht htC
    (fun d hd hdim => genusCollapseStage_active_top q left d hd hdim) hfree
  have hJ x :
      x ≠ Sum.inl f ∧ x < Sum.inl t ↔
        (genusCollapseStage q left x ∧ x ≠ Sum.inl f) ∧ x < Sum.inl t := by
    constructor
    · rintro ⟨hne, hlt⟩
      exact ⟨⟨genusCollapseStage_boundary_mem q left (p :: right) hsplit t htail x hlt, hne⟩, hlt⟩
    · simp_all
  have htop : InjIn (fun x => genusCollapseStage q left x ∧ x ≠ Sum.inl f)
      (fun x => (genusCollapseStage q left x ∧ x ≠ Sum.inl f) ∧ x ≠ Sum.inl t) := by
    apply injIn_delete_maximal
    · intro x _ htx
      exact genus_top_cell_maximal q t ht x htx
    · obtain ⟨x, hxf, hxt⟩ := genus_top_boundary_nonempty q (Sum.inl f) hf t ht
      exact ⟨x, (hJ x).mp ⟨hxf, hxt⟩⟩
    · exact connectedIn_congr hJ (ordinaryTruncatedBoundary_connectedIn hordinary hi)
    · intro v l hv hp hl
      have hnull := ordinaryTruncatedBoundary_simplyConnectedIn hordinary hi v l
        ((hJ v).mpr hv) hp (pathIn_mono (fun x hx => (hJ x).mpr hx) hl)
      exact hnull.mono (fun x hx => (hJ x).mp hx)
  have hpair := injIn_trans (fun _ h => h.1) hface htop
  intro v l hv hp hl hh
  have hnull := hpair v l
    ((genusCollapseStage_ordinary_step_iff q left f t v).mp hv) hp
    (pathIn_mono (fun x hx => (genusCollapseStage_ordinary_step_iff q left f t x).mp hx) hl) hh
  exact hnull.mono (fun x hx => (genusCollapseStage_ordinary_step_iff q left f t x).mpr hx)

/-- Every old-face pair in the chosen collapse satisfies the ordinary comparison, with
dimension and nonpositive-corner conditions derived from the actual recorded pair. -/
theorem genus_old_pair_stage_injIn
    (left right : List (GenusCollapsePair q))
    (f t : QOld (cmpRel (GenusVertex q)))
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1)) :: right)) :
    InjIn (genusCollapseStage q left)
      (genusCollapseStage q
        (left ++ [(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1))])) := by
  have hp : (qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1)) ∈ genusChainCollapse q := by
    rw [hsplit]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have hf  := genus_removedFace_dimension q (Sum.inl f)
    (List.mem_map.mpr ⟨(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1)), hp, rfl⟩)
  have ht  := (genus_oldCell_removed_iff_dimension_three q t).mp
    (List.mem_map.mpr ⟨(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1)), hp, rfl⟩)
  have hordinary : t.1.sgn ≠ 0 := by
    intro hs
    apply genusChainCollapse_old_face_nonpositive q (qCubeToCoordinate t.1)
      (qCubeToCoordinate f.1) hp
    simpa using qCubeToCoordinate_sgn_zero t.1 hs
  exact genus_ordinary_pair_stage_injIn q left right f t hf ht hordinary hsplit

end FiniteChains.Davis.Genus

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def truncatedRetractionHom :
    Hom (orderCx (TruncatedCell A)) (orderCx (QOld A)) :=
  orderCxMap truncatedCellRetraction truncatedCellRetraction_monotone

def truncatedSectionHom :
    Hom (orderCx (QOld A)) (orderCx (TruncatedCell A)) :=
  orderCxMap oldCellIncl oldCellIncl_monotone

/-- The retraction also reflects null homotopies at a new cut-cell basepoint. -/
theorem truncatedRetraction_pi1_injective_at (a : TruncatedCell A) :
    Function.Injective (pi1Map truncatedRetractionHom a) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨p⟩ hp
  let g : TruncatedCell A → TruncatedCell A := fun c =>
    oldCellIncl (truncatedCellRetraction c)
  have hg : Monotone g := oldCellIncl_monotone.comp truncatedCellRetraction_monotone
  have hnat := htpy_loop_mapPath_le monotone_id hg
    truncatedCell_le_retraction p.2
  have hnull  :=
    Quotient.exact hp
  have hsec := mapPath_htpy truncatedSectionHom hnull
  have hgnil : Htpy (orderCx (TruncatedCell A)) (g a) (g a)
      (mapPath (orderCxMap g hg) p.1) [] := by
    simpa [g, truncatedSectionHom, truncatedRetractionHom, mapPath, orderCxMap,
      List.map_map, Function.comp_def] using hsec
  have hconj : Htpy (orderCx (TruncatedCell A)) (g a) (g a)
      ([ordNeg (truncatedCell_le_retraction a)] ++ p.1 ++
        [ordPos (truncatedCell_le_retraction a)]) [] := by
    simpa [mapPath, orderCxMap] using hnat.symm.trans hgnil
  have hstep := hconj.congr_append (isPath_ordPos (truncatedCell_le_retraction a))
    (isPath_ordNeg (truncatedCell_le_retraction a))
  have hc := htpy_ordPos_ordNeg (truncatedCell_le_retraction a)
  have hA := hc.congr_append (isPath_nil' a)
    (p.2.append (show IsPath (orderCx (TruncatedCell A)).src
      (orderCx (TruncatedCell A)).tgt
      [ordPos (truncatedCell_le_retraction a), ordNeg (truncatedCell_le_retraction a)]
      a a from ⟨rfl, rfl, rfl⟩))
  have hB := hc.congr_append p.2 (isPath_nil' a)
  have hstrip : Htpy (orderCx (TruncatedCell A)) a a
      ([ordPos (truncatedCell_le_retraction a)] ++
        ([ordNeg (truncatedCell_le_retraction a)] ++ p.1 ++
          [ordPos (truncatedCell_le_retraction a)]) ++
        [ordNeg (truncatedCell_le_retraction a)]) p.1 := by
    simpa [List.append_assoc] using hA.trans (by simpa using hB)
  have hkill : Htpy (orderCx (TruncatedCell A)) a a
      ([ordPos (truncatedCell_le_retraction a)] ++
        ([ordNeg (truncatedCell_le_retraction a)] ++ p.1 ++
          [ordPos (truncatedCell_le_retraction a)]) ++
        [ordNeg (truncatedCell_le_retraction a)]) [] := by
    exact hstep.trans (by simpa using hc)
  exact Quotient.sound (hstrip.symm.trans hkill)

theorem truncatedRetraction_pi1_surjective_at (a : TruncatedCell A) :
    Function.Surjective (pi1Map truncatedRetractionHom a) := by
  rintro ⟨p⟩
  let e := truncatedCell_le_retraction a
  let lp : Loop (orderCx (TruncatedCell A)) a :=
    ⟨[ordPos e] ++ mapPath truncatedSectionHom p.1 ++ [ordNeg e],
      ((isPath_ordPos e).append (isPath_mapPath truncatedSectionHom p.2)).append
        (isPath_ordNeg e)⟩
  refine ⟨Pi1.mk lp, Quotient.sound ?_⟩
  change Htpy (orderCx (QOld A)) (truncatedCellRetraction a) (truncatedCellRetraction a)
    (mapPath truncatedRetractionHom lp.val) p.val
  have hs := htpy_ordSelf_nil (truncatedCellRetraction a)
  have hn := htpy_revPath (isPath_ordPos (le_refl (truncatedCellRetraction a))) hs
  have hA := hs.congr_append (isPath_nil' (truncatedCellRetraction a))
    (p.2.append (isPath_ordNeg (le_refl (truncatedCellRetraction a))))
  have hB := hn.congr_append p.2 (isPath_nil' (truncatedCellRetraction a))
  simp at hA hB
  have hh := hA.trans hB
  simpa [loopSetoid, ordPos, ordNeg, lp, e, truncatedRetractionHom, truncatedSectionHom, mapPath, orderCxMap,
    List.map_map, Function.comp_def, revPath, revGerm] using hh

end FiniteChains.Davis

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

def genusSpineToTruncated :
    Hom (genusSpineCx q) (orderCx (GenusTruncatedCell q)) :=
  Hom.comp (orderCxMap (fun c : GenusSpineCell q => c.val) monotone_subtypeVal)
    (strictOrderIncl (GenusSpineCell q))

theorem genusSpineToOld_factor :
    genusSpineToOld q = Hom.comp truncatedRetractionHom (genusSpineToTruncated q) := rfl

theorem genusSpine_pi1_factor (z : Pi1 (genusSpineCx q) (spineBase q)) :
    pi1Map (genusSpineToOld q) (spineBase q) z =
      pi1Map truncatedRetractionHom ((genusSpineToTruncated q).onV (spineBase q))
        (pi1Map (genusSpineToTruncated q) (spineBase q) z) := by
  rcases z with ⟨p⟩
  apply congrArg Pi1.mk
  apply Subtype.ext
  simp [genusSpineToOld_factor, mapPath, Hom.comp, List.map_map, Function.comp_def]

/-- The remaining injectivity obligation is precisely the inclusion of the surviving spine
into the truncated complex, since truncation itself has already been proved harmless. -/
theorem genusSpine_pi1_injective_iff :
    Function.Injective (pi1Map (genusSpineToOld q) (spineBase q)) ↔
      Function.Injective (pi1Map (genusSpineToTruncated q) (spineBase q)) := by
  constructor
  · intro h x y hxy
    apply h
    rw [genusSpine_pi1_factor, genusSpine_pi1_factor, hxy]
  · intro h x y hxy
    apply h
    apply truncatedRetraction_pi1_injective_at
      ((genusSpineToTruncated q).onV (spineBase q))
    convert hxy using 1 <;> simp only [← genusSpine_pi1_factor]

end FiniteChains.Davis.Genus
end

namespace FiniteChains.Davis
open Comb

def VertexPuncturedCube :=
  {c : Cube (Fin 3) // c ≠ (fun _ => CubeCoord.free) ∧ c ≠ (fun _ => CubeCoord.pos)}

instance : PartialOrder VertexPuncturedCube where
  le c d := CoordinateFace c.1 d.1
  le_refl c v := Or.inr rfl
  le_trans c d e hcd hde v := by
    rcases hde v with he | he
    · simp_all
    · rcases hcd v with hd | hd
      · exact Or.inl (he.symm.trans hd)
      · exact Or.inr (hd.trans he)
  le_antisymm c d hcd hdc := by
    apply Subtype.ext
    funext v
    rcases hcd v with hd | hd
    · rcases hdc v with hc | hc
      · exact hc.trans hd.symm
      · exact hc.symm
    · exact hd

def vertexPunctureRight (c : VertexPuncturedCube) : Prop := c.1 0 ≠ CubeCoord.pos

def vertexPunctureRightPole : {c : VertexPuncturedCube // vertexPunctureRight c} :=
  ⟨⟨coordinateFix 0 CubeCoord.neg (fun _ => CubeCoord.free), by
      constructor
      · intro h
        have hh := congrFun h 0
        simp only [coordinateFix, Function.update_self] at hh
        cases hh
      · intro h
        have hh := congrFun h 0
        simp only [coordinateFix, Function.update_self] at hh
        cases hh⟩, by
    change coordinateFix 0 CubeCoord.neg (fun _ : Fin 3 => CubeCoord.free) 0 ≠ CubeCoord.pos
    simp only [coordinateFix, Function.update_self]
    decide⟩

def vertexPunctureRightProjection (c : {c : VertexPuncturedCube // vertexPunctureRight c}) :
    {c : VertexPuncturedCube // vertexPunctureRight c} :=
  ⟨⟨coordinateFix 0 CubeCoord.neg c.1.1, by
      constructor
      · intro h
        have hh := congrFun h 0
        simp only [coordinateFix, Function.update_self] at hh
        cases hh
      · intro h
        have hh := congrFun h 0
        simp only [coordinateFix, Function.update_self] at hh
        cases hh⟩, by
    change coordinateFix 0 CubeCoord.neg c.1.1 0 ≠ CubeCoord.pos
    simp only [coordinateFix, Function.update_self]
    decide⟩

theorem vertexPunctureRightProjection_le
    (c : {c : VertexPuncturedCube // vertexPunctureRight c}) :
    vertexPunctureRightProjection c ≤ c := by
  intro v
  by_cases hv : v = 0
  · subst v
    have hc : c.1.1 0 ≠ CubeCoord.pos := c.2
    cases he : c.1.1 0 with
    | free => simp
    | pos => simp_all
    | neg =>
      right
      simp only [vertexPunctureRightProjection, coordinateFix, Function.update_self]
  · right
    exact Function.update_of_ne hv _ _

theorem vertexPunctureRightProjection_le_pole
    (c : {c : VertexPuncturedCube // vertexPunctureRight c}) :
    vertexPunctureRightProjection c ≤ vertexPunctureRightPole :=
  coordinateFix_face_mono 0 CubeCoord.neg (fun _ => Or.inl rfl)

theorem vertexPunctureRightProjection_monotone : Monotone vertexPunctureRightProjection := by
  intro c d h
  exact coordinateFix_face_mono 0 CubeCoord.neg h

theorem vertexPunctureRight_simplyConnected :
    SimplyConnected (orderCx {c : VertexPuncturedCube // vertexPunctureRight c}) :=
  simplyConnected_orderCx vertexPunctureRightPole vertexPunctureRightProjection
    vertexPunctureRightProjection_le vertexPunctureRightProjection_le_pole
    (fun h => vertexPunctureRightProjection_monotone h)

theorem vertexPunctureRight_connected :
    IsConnected (orderCx {c : VertexPuncturedCube // vertexPunctureRight c}) :=
  isConnected_orderCx vertexPunctureRightPole vertexPunctureRightProjection
    vertexPunctureRightProjection_le vertexPunctureRightProjection_le_pole

def vertexPunctureCornerEdge : Cube (Fin 3) := coordinateFix 0 CubeCoord.free (fun _ => CubeCoord.pos)

def vertexPunctureLeft (c : VertexPuncturedCube) : Prop :=
  c.1 0 ≠ CubeCoord.neg ∧ c.1 ≠ vertexPunctureCornerEdge


def vertexPunctureLeftPole : {c : VertexPuncturedCube // vertexPunctureLeft c} :=
  ⟨⟨coordinateFix 0 CubeCoord.pos (fun _ => CubeCoord.free), by
      constructor
      · intro h
        have hh := congrFun h 0
        simp only [coordinateFix, Function.update_self] at hh
        cases hh
      · intro h
        have hh := congrFun h (1 : Fin 3)
        simp only [coordinateFix, Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0)] at hh
        cases hh⟩, by
    constructor
    · change coordinateFix 0 CubeCoord.pos (fun _ : Fin 3 => CubeCoord.free) 0 ≠ CubeCoord.neg
      simp only [coordinateFix, Function.update_self]
      decide
    · intro h
      have hh := congrFun h 0
      simp only [vertexPunctureCornerEdge, coordinateFix, Function.update_self] at hh
      cases hh⟩

def vertexPunctureLeftProjection (c : {c : VertexPuncturedCube // vertexPunctureLeft c}) :
    {c : VertexPuncturedCube // vertexPunctureLeft c} :=
  ⟨⟨coordinateFix 0 CubeCoord.pos c.1.1, by
      constructor
      · intro h
        have hh := congrFun h 0
        simp only [coordinateFix, Function.update_self] at hh
        cases hh
      · exact (by
        intro h
        have hrest (v : Fin 3) (hv : v ≠ 0) : c.1.1 v = CubeCoord.pos := by
          have hh := congrFun h v
          simpa only [coordinateFix, Function.update_of_ne hv] using hh
        cases he : c.1.1 0 with
        | neg => exact c.2.1 he
        | pos => grind
        | free =>
          apply c.2.2
          funext v
          by_cases hv : v = 0
          · subst v
            simpa only [vertexPunctureCornerEdge, coordinateFix, Function.update_self] using he
          · simpa only [vertexPunctureCornerEdge, coordinateFix, Function.update_of_ne hv] using hrest v hv)⟩, by
    constructor
    · change coordinateFix 0 CubeCoord.pos c.1.1 0 ≠ CubeCoord.neg
      simp only [coordinateFix, Function.update_self]
      decide
    · intro h
      have hh := congrFun h 0
      simp only [vertexPunctureCornerEdge, coordinateFix, Function.update_self] at hh
      cases hh⟩

theorem vertexPunctureLeftProjection_le
    (c : {c : VertexPuncturedCube // vertexPunctureLeft c}) :
    vertexPunctureLeftProjection c ≤ c := by
  intro v
  by_cases hv : v = 0
  · subst v
    cases he : c.1.1 0 with
    | free => simp
    | neg => exact False.elim (c.2.1 he)
    | pos =>
      right
      simp only [vertexPunctureLeftProjection, coordinateFix, Function.update_self]
  · right
    exact Function.update_of_ne hv _ _

theorem vertexPunctureLeftProjection_le_pole
    (c : {c : VertexPuncturedCube // vertexPunctureLeft c}) :
    vertexPunctureLeftProjection c ≤ vertexPunctureLeftPole :=
  coordinateFix_face_mono 0 CubeCoord.pos (fun _ => Or.inl rfl)

theorem vertexPunctureLeftProjection_monotone : Monotone vertexPunctureLeftProjection := by
  intro c d h
  exact coordinateFix_face_mono 0 CubeCoord.pos h

theorem vertexPunctureLeft_simplyConnected :
    SimplyConnected (orderCx {c : VertexPuncturedCube // vertexPunctureLeft c}) :=
  simplyConnected_orderCx vertexPunctureLeftPole vertexPunctureLeftProjection
    vertexPunctureLeftProjection_le vertexPunctureLeftProjection_le_pole
    (fun h => vertexPunctureLeftProjection_monotone h)

theorem vertexPunctureLeft_connected :
    IsConnected (orderCx {c : VertexPuncturedCube // vertexPunctureLeft c}) :=
  isConnected_orderCx vertexPunctureLeftPole vertexPunctureLeftProjection
    vertexPunctureLeftProjection_le vertexPunctureLeftProjection_le_pole

theorem vertexPuncture_positive_mem_left (c : VertexPuncturedCube)
    (hc : c.1 0 = CubeCoord.pos) : vertexPunctureLeft c := by
  constructor
  · simp_all
  · intro h
    have hh := congrFun h 0
    simp only [vertexPunctureCornerEdge, coordinateFix, Function.update_self, hc] at hh
    cases hh

theorem vertexPuncture_cover (c : VertexPuncturedCube) :
    vertexPunctureLeft c ∨ vertexPunctureRight c := by
  by_cases hc : c.1 0 = CubeCoord.pos
  · exact Or.inl (vertexPuncture_positive_mem_left c hc)
  · exact Or.inr hc

theorem vertexPuncture_positive_not_below_edge (c : VertexPuncturedCube)
    (hc : c.1 0 = CubeCoord.pos) : ¬ CoordinateFace c.1 vertexPunctureCornerEdge := by
  intro h
  apply c.2.2
  funext v
  by_cases hv : v = 0
  · simp_all
  · have he : vertexPunctureCornerEdge v = CubeCoord.pos := by
      simp only [vertexPunctureCornerEdge, coordinateFix, Function.update_of_ne hv]
    have hh := h v
    rw [he] at hh
    rcases hh with hh | hh
    · cases hh
    · exact hh

theorem vertexPuncture_unmixed (c d : VertexPuncturedCube) (h : c ≤ d) :
    (vertexPunctureLeft c ∧ vertexPunctureLeft d) ∨
      (vertexPunctureRight c ∧ vertexPunctureRight d) := by
  cases hd : d.1 0 with
  | pos =>
    have hc : c.1 0 = CubeCoord.pos := by
      have hh := h 0
      rw [hd] at hh
      rcases hh with hh | hh
      · cases hh
      · exact hh
    exact Or.inl ⟨vertexPuncture_positive_mem_left c hc, vertexPuncture_positive_mem_left d hd⟩
  | neg =>
    have hc : c.1 0 = CubeCoord.neg := by
      have hh := h 0
      rw [hd] at hh
      rcases hh with hh | hh
      · cases hh
      · exact hh
    right
    constructor <;> change _ ≠ CubeCoord.pos
    · simp_all
    · simp_all
  | free =>
    have hdr : vertexPunctureRight d := by
      change d.1 0 ≠ CubeCoord.pos
      rw [hd]
      decide
    by_cases hcr : vertexPunctureRight c
    · simp_all
    · have hc  := not_ne_iff.mp hcr
      left
      refine ⟨vertexPuncture_positive_mem_left c hc, ?_⟩
      constructor
      · rw [hd]
        decide
      · intro he
        exact vertexPuncture_positive_not_below_edge c hc (he ▸ h)

theorem vertexPuncture_intersection_iff (c : VertexPuncturedCube) :
    vertexPunctureLeft c ∧ vertexPunctureRight c ↔
      c.1 0 = CubeCoord.free ∧ c.1 ≠ vertexPunctureCornerEdge := by
  constructor
  · rintro ⟨⟨hn, he⟩, hp⟩
    refine ⟨?_, he⟩
    cases hc : c.1 0 with
    | free => rfl
    | pos => exact False.elim (hp hc)
    | neg => simp_all
  · rintro ⟨hf, he⟩
    constructor
    · refine ⟨?_, he⟩
      rw [hf]
      decide
    · change c.1 0 ≠ CubeCoord.pos
      rw [hf]
      decide

end FiniteChains.Davis

namespace FiniteChains.Davis
open Comb

def vertexIntersectionCoordinates (i : Fin 7) : Cube (Fin 3) :=
  ![![CubeCoord.free, .neg, .neg], ![CubeCoord.free, .neg, .free],
    ![CubeCoord.free, .neg, .pos], ![CubeCoord.free, .pos, .neg],
    ![CubeCoord.free, .free, .neg], ![CubeCoord.free, .pos, .free],
    ![CubeCoord.free, .free, .pos]] i

def vertexIntersectionCell (i : Fin 7) : VertexPuncturedCube :=
  ⟨vertexIntersectionCoordinates i, by fin_cases i <;> decide⟩

theorem vertexIntersectionCell_mem (i : Fin 7) :
    vertexPunctureLeft (vertexIntersectionCell i) ∧
      vertexPunctureRight (vertexIntersectionCell i) := by
  unfold vertexPunctureLeft vertexPunctureRight
  fin_cases i <;> decide

theorem vertexIntersection_classify (c : VertexPuncturedCube)
    (hc : vertexPunctureLeft c ∧ vertexPunctureRight c) :
    ∃ i : Fin 7, c = vertexIntersectionCell i := by
  obtain ⟨h0, hne⟩ := (vertexPuncture_intersection_iff c).mp hc
  have hv : c.1 = ![CubeCoord.free, c.1 1, c.1 2] := by
    funext v
    fin_cases v
    · exact h0
    · rfl
    · rfl
  cases h1 : c.1 1 <;> cases h2 : c.1 2 <;> rw [h1, h2] at hv
  case free.free =>
    exact False.elim (c.2.1 (hv.trans (by decide)))
  case free.pos => exact ⟨6, Subtype.ext hv⟩
  case free.neg => exact ⟨4, Subtype.ext hv⟩
  case pos.free => exact ⟨5, Subtype.ext hv⟩
  case pos.pos => exact False.elim (hne (hv.trans (by decide)))
  case pos.neg => exact ⟨3, Subtype.ext hv⟩
  case neg.free => exact ⟨1, Subtype.ext hv⟩
  case neg.pos => exact ⟨2, Subtype.ext hv⟩
  case neg.neg => exact ⟨0, Subtype.ext hv⟩

def vertexIntersectionAdjacent (i j : Fin 7) : Prop :=
  CoordinateFace (vertexIntersectionCoordinates i) (vertexIntersectionCoordinates j) ∨
    CoordinateFace (vertexIntersectionCoordinates j) (vertexIntersectionCoordinates i)

instance (i j : Fin 7) : Decidable (vertexIntersectionAdjacent i j) := by
  unfold vertexIntersectionAdjacent CoordinateFace
  infer_instance

/-- A finite, kernel-checked reachability certificate for the seven actual intersection cells. -/
theorem vertexIntersection_links : ∀ i : Fin 7, ∃ j k : Fin 7,
    vertexIntersectionAdjacent i j ∧ vertexIntersectionAdjacent j k ∧
      vertexIntersectionAdjacent k 0 := by decide

theorem intersection_path_of_adjacent (i j : Fin 7)
    (h : vertexIntersectionAdjacent i j) :
    ∃ p, IsPath (orderCx VertexPuncturedCube).src (orderCx VertexPuncturedCube).tgt
      p (vertexIntersectionCell i) (vertexIntersectionCell j) ∧
      PathIn (fun c => vertexPunctureLeft c ∧ vertexPunctureRight c) p := by
  rcases h with h | h
  · exact ⟨[ordPos h], isPath_ordPos h,
      pathIn_cons ⟨vertexIntersectionCell_mem i, vertexIntersectionCell_mem j⟩ (pathIn_nil _)⟩
  · exact ⟨[ordNeg h], isPath_ordNeg h,
      pathIn_cons ⟨vertexIntersectionCell_mem j, vertexIntersectionCell_mem i⟩ (pathIn_nil _)⟩

theorem vertexPuncture_intersection_connected :
    ConnectedIn (fun c : VertexPuncturedCube => vertexPunctureLeft c ∧ vertexPunctureRight c) := by
  have reach i : ∃ p,
      IsPath (orderCx VertexPuncturedCube).src (orderCx VertexPuncturedCube).tgt
        p (vertexIntersectionCell i) (vertexIntersectionCell 0) ∧
      PathIn (fun c => vertexPunctureLeft c ∧ vertexPunctureRight c) p := by
    obtain ⟨j, k, hij, hjk, hk0⟩ := vertexIntersection_links i
    obtain ⟨p, hp, hpin⟩ := intersection_path_of_adjacent i j hij
    obtain ⟨r, hr, hrin⟩ := intersection_path_of_adjacent j k hjk
    obtain ⟨s, hs, hsin⟩ := intersection_path_of_adjacent k 0 hk0
    exact ⟨p ++ r ++ s, (hp.append hr).append hs,
      pathIn_append (pathIn_append hpin hrin) hsin⟩
  intro a b ha hb
  obtain ⟨i, rfl⟩ := vertexIntersection_classify a ha
  obtain ⟨j, rfl⟩ := vertexIntersection_classify b hb
  obtain ⟨p, hp, hpin⟩ := reach i
  obtain ⟨r, hr, hrin⟩ := reach j
  exact ⟨p ++ revPath r, hp.append (isPath_revPath hr),
    pathIn_append hpin (pathIn_revPath hrin)⟩

theorem vertexPuncturedCube_simplyConnected : SimplyConnected (orderCx VertexPuncturedCube) := by
  have hnull := htpy_nil_of_pathIn_union
    (U := fun _ : VertexPuncturedCube => True)
    (A := vertexPunctureLeft) (B := vertexPunctureRight)
    (fun c => ⟨fun _ => vertexPuncture_cover c, fun _ => trivial⟩)
    (fun c d h _ _ => vertexPuncture_unmixed c d h)
    (nullIn_of_simplyConnected vertexPunctureLeft_simplyConnected)
    (nullIn_of_simplyConnected vertexPunctureRight_simplyConnected)
    (connectedIn_of_isConnected vertexPunctureLeft_connected)
    (connectedIn_of_isConnected vertexPunctureRight_connected)
    vertexPuncture_intersection_connected (vertexIntersectionCell_mem 0)
  intro a p hp
  exact hnull a p trivial hp (fun _ _ => ⟨trivial, trivial⟩)

theorem vertexPuncturedCube_connected : IsConnected (orderCx VertexPuncturedCube) := by
  have reach c : ∃ p,
      IsPath (orderCx VertexPuncturedCube).src (orderCx VertexPuncturedCube).tgt
        p c (vertexIntersectionCell 0) := by
    rcases vertexPuncture_cover c with hc | hc
    · obtain ⟨p, hp, _⟩ := (connectedIn_of_isConnected vertexPunctureLeft_connected)
        c (vertexIntersectionCell 0) hc (vertexIntersectionCell_mem 0).1
      exact ⟨p, hp⟩
    · obtain ⟨p, hp, _⟩ := (connectedIn_of_isConnected vertexPunctureRight_connected)
        c (vertexIntersectionCell 0) hc (vertexIntersectionCell_mem 0).2
      exact ⟨p, hp⟩
  intro a b
  obtain ⟨p, hp⟩ := reach a
  obtain ⟨r, hr⟩ := reach b
  exact ⟨p ++ revPath r, hp.append (isPath_revPath hr)⟩

end FiniteChains.Davis

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def fullCutCell (t : QOld A) (hne : t.1.spx.Nonempty) : CutCell A :=
  ⟨t.1.spx, hne, t.1.isSimplex⟩

def CutPuncturedBoundary (t : QOld A) (hne : t.1.spx.Nonempty) :=
  {c : TruncatedCell A // c < Sum.inl t ∧ c ≠ Sum.inr (fullCutCell t hne)}

def RetainedProperBoundary (t : QOld A) := {c : QOld A // c < t}

instance (t : QOld A) (hne : t.1.spx.Nonempty) :
    PartialOrder (CutPuncturedBoundary t hne) := Subtype.partialOrder _
instance (t : QOld A) : PartialOrder (RetainedProperBoundary t) := Subtype.partialOrder _

def cutBoundaryRetraction (t : QOld A) (hne : t.1.spx.Nonempty)
    (c : CutPuncturedBoundary t hne) : RetainedProperBoundary t := by
  have hle : truncatedCellRetraction c.1 ≤ t :=
    truncatedCellRetraction_monotone c.2.1.le
  refine ⟨truncatedCellRetraction c.1, lt_of_le_of_ne hle ?_⟩
  intro he
  rcases c with ⟨c, hc⟩
  cases c with
  | inl d => exact hc.1.ne (congrArg Sum.inl he)
  | inr σ =>
    have hs : σ.1 = t.1.spx := congrArg (fun d : QOld A => d.1.spx) he
    exact hc.2 (congrArg Sum.inr (Subtype.ext hs))

def cutBoundarySection (t : QOld A) (hne : t.1.spx.Nonempty)
    (c : RetainedProperBoundary t) : CutPuncturedBoundary t hne :=
  ⟨Sum.inl c.1, lt_of_le_of_ne c.2.le (fun h => c.2.ne (Sum.inl.inj h)), by simp⟩

theorem cutBoundaryRetraction_monotone (t : QOld A) (hne : t.1.spx.Nonempty) :
    Monotone (cutBoundaryRetraction t hne) := by
  intro c d h
  exact truncatedCellRetraction_monotone h

theorem cutBoundarySection_monotone (t : QOld A) (hne : t.1.spx.Nonempty) :
    Monotone (cutBoundarySection t hne) := fun _ _ h => h

theorem cutBoundary_le_section_retraction (t : QOld A) (hne : t.1.spx.Nonempty)
    (c : CutPuncturedBoundary t hne) :
    c ≤ cutBoundarySection t hne (cutBoundaryRetraction t hne c) :=
  truncatedCell_le_retraction c.1

/-- The remaining simple-connectedness problem is exactly the retained proper-face boundary.
The retraction and its order homotopy are constructed, not assumed. -/
theorem cutPuncturedBoundary_simplyConnected_of_retained (t : QOld A)
    (hne : t.1.spx.Nonempty) (hsc : SimplyConnected (orderCx (RetainedProperBoundary t))) :
    SimplyConnected (orderCx (CutPuncturedBoundary t hne)) := by
  intro a p hp
  let r := cutBoundaryRetraction t hne
  let s := cutBoundarySection t hne
  have hr := cutBoundaryRetraction_monotone t hne
  have hs := cutBoundarySection_monotone t hne
  have hn := hsc (r a) (mapPath (orderCxMap r hr) p) (isPath_mapPath (orderCxMap r hr) hp)
  have hpush := mapPath_htpy (orderCxMap s hs) hn
  have hnil : Htpy (orderCx (CutPuncturedBoundary t hne)) (s (r a)) (s (r a))
      (mapPath (orderCxMap (s ∘ r) (hs.comp hr)) p) [] := by
    simpa [mapPath, orderCxMap, List.map_map, Function.comp_def] using hpush
  have hid := (htpy_nil_mapPath_le_iff monotone_id (hs.comp hr)
    (cutBoundary_le_section_retraction t hne) hp).mpr hnil
  simpa [mapPath, orderCxMap] using hid

theorem cutPuncturedBoundary_connected_of_retained (t : QOld A)
    (hne : t.1.spx.Nonempty) (hconn : IsConnected (orderCx (RetainedProperBoundary t))) :
    IsConnected (orderCx (CutPuncturedBoundary t hne)) := by
  intro a b
  obtain ⟨p, hp⟩ := hconn (cutBoundaryRetraction t hne a) (cutBoundaryRetraction t hne b)
  have hs := isPath_mapPath (orderCxMap (cutBoundarySection t hne)
    (cutBoundarySection_monotone t hne)) hp
  exact ⟨[ordPos (cutBoundary_le_section_retraction t hne a)] ++
      mapPath (orderCxMap (cutBoundarySection t hne) (cutBoundarySection_monotone t hne)) p ++
      [ordNeg (cutBoundary_le_section_retraction t hne b)],
    ((isPath_ordPos (cutBoundary_le_section_retraction t hne a)).append hs).append
      (isPath_ordNeg (cutBoundary_le_section_retraction t hne b))⟩

end FiniteChains.Davis
end

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [Fintype V] [DecidableEq V] {A : CommRel V}

omit [Fintype V] in
theorem retainedBoundary_coordinate_outside (t : QOld A) (ht : t.1.sgn = 0)
    (c : RetainedProperBoundary t) {v : V} (hv : v ∉ t.1.spx) :
    qCubeToCoordinate c.1.1 v = CubeCoord.pos := by
  have hc : v ∉ c.1.1.spx := fun h => hv (c.2.le.1 h)
  have hs  := (c.2.le.2 v hv).trans (congrFun ht v)
  simp [qCubeToCoordinate, hc, hs]

theorem old_coordinate_not_all_positive (c : QOld A) :
    qCubeToCoordinate c.1 ≠ (fun _ => CubeCoord.pos) := by
  intro he
  have hspx : c.1.spx = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hh := congrFun he v
    simp only [qCubeToCoordinate, if_pos hv] at hh
    cases hh
  have hs : c.1.sgn = 0 := by
    funext v
    have hh := qCubeToCoordinate_parity c.1 v
    rw [he] at hh
    exact hh.symm
  grind

def positiveBoundaryRestriction (t : QOld A) (ht : t.1.sgn = 0)
    (e : Fin 3 ≃ {v : V // v ∈ t.1.spx}) (c : RetainedProperBoundary t) :
    VertexPuncturedCube := by
  let f : Cube (Fin 3) := fun i => qCubeToCoordinate c.1.1 (e i).1
  refine ⟨f, ?_, ?_⟩
  · intro he
    have hc : qCubeToCoordinate c.1.1 = qCubeToCoordinate t.1 := by
      funext v
      by_cases hv : v ∈ t.1.spx
      · obtain ⟨i, hi⟩ := e.surjective ⟨v, hv⟩
        have hh := congrFun he i
        have hiv : (e i).1 = v := congrArg Subtype.val hi
        change qCubeToCoordinate c.1.1 (e i).1 = CubeCoord.free at hh
        rw [hiv] at hh
        simpa only [qCubeToCoordinate, if_pos hv] using hh
      · rw [retainedBoundary_coordinate_outside t ht c hv]
        simp [qCubeToCoordinate, hv, ht]
    exact c.2.ne (Subtype.ext (qCubeCoordinateEquiv.injective (Subtype.ext hc)))
  · intro he
    apply old_coordinate_not_all_positive c.1
    funext v
    by_cases hv : v ∈ t.1.spx
    · obtain ⟨i, hi⟩ := e.surjective ⟨v, hv⟩
      have hh := congrFun he i
      have hiv : (e i).1 = v := congrArg Subtype.val hi
      change qCubeToCoordinate c.1.1 (e i).1 = CubeCoord.pos at hh
      rwa [hiv] at hh
    · exact retainedBoundary_coordinate_outside t ht c hv

def extendPositiveCoordinates (t : QOld A)
    (e : Fin 3 ≃ {v : V // v ∈ t.1.spx}) (c : Cube (Fin 3)) : Cube V :=
  fun v => if hv : v ∈ t.1.spx then c (e.symm ⟨v, hv⟩) else CubeCoord.pos

omit [Fintype V] in
theorem extendPositiveCoordinates_inside (t : QOld A)
    (e : Fin 3 ≃ {v : V // v ∈ t.1.spx}) (c : Cube (Fin 3)) (i : Fin 3) :
    extendPositiveCoordinates t e c (e i).1 = c i := by
  simp [extendPositiveCoordinates, (e i).2]

def positiveBoundaryExtension (t : QOld A) (ht : t.1.sgn = 0)
    (e : Fin 3 ≃ {v : V // v ∈ t.1.spx}) (c : VertexPuncturedCube) :
    RetainedProperBoundary t := by
  classical
  let f := extendPositiveCoordinates t e c.1
  have hsub : freeSet f ⊆ t.1.spx := by
    intro v hv
    by_contra hn
    have hh := mem_freeSet.mp hv
    simp only [f, extendPositiveCoordinates, dif_neg hn] at hh
    cases hh
  let d : QCube A := coordinateToQCube ⟨f, isSimplex_subset A hsub t.1.isSimplex⟩
  have hd : qCubeToCoordinate d = f := coordinateToQCube_toCoordinate _
  have hdt : d ≤ t.1 := by
    apply (qCubeToCoordinate_face_iff d t.1).mpr
    intro v
    rw [hd, qCubeToCoordinate_sgn_zero t.1 ht]
    by_cases hv : v ∈ t.1.spx
    · left
      simp [posCube, hv]
    · right
      simp [f, extendPositiveCoordinates, posCube, hv]
  have hold : ¬ (d.spx = ∅ ∧ d.sgn = 0) := by
    rintro ⟨hspx, hs⟩
    apply c.2.2
    funext i
    have hi := extendPositiveCoordinates_inside t e c.1 i
    change f (e i).1 = c.1 i at hi
    rw [← hd] at hi
    rw [← hi]
    simp [qCubeToCoordinate, hspx, hs]
  let w : QOld A := ⟨d, hold⟩
  refine ⟨w, lt_of_le_of_ne hdt ?_⟩
  intro he
  apply c.2.1
  funext i
  have hi := extendPositiveCoordinates_inside t e c.1 i
  change f (e i).1 = c.1 i at hi
  rw [← hd] at hi
  have hraw : d = t.1 := congrArg Subtype.val he
  rw [hraw] at hi
  rw [← hi]
  simp [qCubeToCoordinate, (e i).2]

theorem positiveBoundaryExtension_coordinates (t : QOld A) (ht : t.1.sgn = 0)
    (e : Fin 3 ≃ {v : V // v ∈ t.1.spx}) (c : VertexPuncturedCube) :
    qCubeToCoordinate (positiveBoundaryExtension t ht e c).1.1 =
      extendPositiveCoordinates t e c.1 := coordinateToQCube_toCoordinate _

def positiveBoundaryOrderIso (t : QOld A) (ht : t.1.sgn = 0)
    (e : Fin 3 ≃ {v : V // v ∈ t.1.spx}) :
    RetainedProperBoundary t ≃o VertexPuncturedCube where
  toFun := positiveBoundaryRestriction t ht e
  invFun := positiveBoundaryExtension t ht e
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    apply qCubeCoordinateEquiv.injective
    apply Subtype.ext
    funext v
    change qCubeToCoordinate (positiveBoundaryExtension t ht e
      (positiveBoundaryRestriction t ht e c)).1.1 v = qCubeToCoordinate c.1.1 v
    rw [positiveBoundaryExtension_coordinates]
    by_cases hv : v ∈ t.1.spx
    · obtain ⟨i, hi⟩ := e.surjective ⟨v, hv⟩
      have hiv : (e i).1 = v := congrArg Subtype.val hi
      rw [← hiv, extendPositiveCoordinates_inside]
      rfl
    · rw [retainedBoundary_coordinate_outside t ht c hv]
      simp [extendPositiveCoordinates, hv]
  right_inv c := by
    apply Subtype.ext
    funext i
    change qCubeToCoordinate (positiveBoundaryExtension t ht e c).1.1 (e i).1 = c.1 i
    rw [positiveBoundaryExtension_coordinates, extendPositiveCoordinates_inside]
  map_rel_iff' := by
    intro c d
    change CoordinateFace (positiveBoundaryRestriction t ht e c).1
      (positiveBoundaryRestriction t ht e d).1 ↔ c.1.1 ≤ d.1.1
    rw [qCubeToCoordinate_face_iff]
    constructor
    · intro h v
      by_cases hv : v ∈ t.1.spx
      · obtain ⟨i, hi⟩ := e.surjective ⟨v, hv⟩
        have hh := h i
        have hiv : (e i).1 = v := congrArg Subtype.val hi
        change qCubeToCoordinate d.1.1 (e i).1 = CubeCoord.free ∨
          qCubeToCoordinate c.1.1 (e i).1 = qCubeToCoordinate d.1.1 (e i).1 at hh
        rwa [hiv] at hh
      · right
        rw [retainedBoundary_coordinate_outside t ht c hv,
          retainedBoundary_coordinate_outside t ht d hv]
    · intro h i
      exact h (e i).1

def positiveThreeCubeCoordinates (t : QOld A) (hcard : t.1.spx.card = 3) :
    Fin 3 ≃ {v : V // v ∈ t.1.spx} :=
  (Fintype.equivFinOfCardEq (by simpa using hcard)).symm





def swappedCutBoundaryOrderIso (t : QOld A) (hne : t.1.spx.Nonempty) :
    {x : TruncatedCell A // x ≠ Sum.inr (fullCutCell t hne) ∧ x < Sum.inl t} ≃o
      CutPuncturedBoundary t hne where
  toFun x := ⟨x.1, x.2.2, x.2.1⟩
  invFun x := ⟨x.1, x.2.2, x.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by intros; rfl

theorem positiveCutPuncturedBoundary_connectedIn (t : QOld A)
    (hne : t.1.spx.Nonempty) (ht : t.1.sgn = 0) (hcard : t.1.spx.card = 3) :
    ConnectedIn (fun x : TruncatedCell A =>
      x ≠ Sum.inr (fullCutCell t hne) ∧ x < Sum.inl t) := by
  apply connectedIn_of_isConnected
  exact isConnected_orderCx_of_orderIso (swappedCutBoundaryOrderIso t hne)
    (cutPuncturedBoundary_connected_of_retained t hne
    (isConnected_orderCx_of_orderIso
    (positiveBoundaryOrderIso t ht (positiveThreeCubeCoordinates t hcard))
    vertexPuncturedCube_connected))

theorem positiveCutPuncturedBoundary_simplyConnectedIn (t : QOld A)
    (hne : t.1.spx.Nonempty) (ht : t.1.sgn = 0) (hcard : t.1.spx.card = 3) :
    SimplyConnectedIn (fun x : TruncatedCell A =>
      x ≠ Sum.inr (fullCutCell t hne) ∧ x < Sum.inl t) := by
  apply simplyConnectedIn_of_simplyConnected
  exact simplyConnected_orderCx_of_orderIso (swappedCutBoundaryOrderIso t hne)
    (cutPuncturedBoundary_simplyConnected_of_retained t hne
    (simplyConnected_orderCx_of_orderIso
    (positiveBoundaryOrderIso t ht (positiveThreeCubeCoordinates t hcard))
    vertexPuncturedCube_simplyConnected))

end FiniteChains.Davis

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem genusCollapseStage_cut_step_iff (left : List (GenusCollapsePair q))
    (t : QOld (cmpRel (GenusVertex q))) (hne : t.1.spx.Nonempty)
    (c : GenusTruncatedCell q) :
    genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, Sum.inr t.1.spx)]) c ↔
      (genusCollapseStage q left c ∧ c ≠ Sum.inr (fullCutCell t hne)) ∧ c ≠ Sum.inl t := by
  have hinj : Function.Injective
      (fun d : QOld (cmpRel (GenusVertex q)) => qCubeToCoordinate d.1) := by
    intro d e h
    exact Subtype.ext (qCubeCoordinateEquiv.injective (Subtype.ext h))
  cases c with
  | inl d =>
    simp only [genusCollapseStage, truncatedFaceIndex, List.map_append, List.map_cons,
      List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      ne_eq, Sum.inl.injEq, Sum.inl_ne_inr, hinj.eq_iff]
    tauto
  | inr σ =>
    have he : σ.1 = t.1.spx ↔ σ = fullCutCell t hne :=
      ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    simp [genusCollapseStage, truncatedFaceIndex, he]

theorem genus_cut_pair_stage_injIn
    (left right : List (GenusCollapsePair q))
    (t : QOld (cmpRel (GenusVertex q)))
    (hne : t.1.spx.Nonempty) (ht : t.1.spx.card = 3) (hpositive : t.1.sgn = 0)
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inr t.1.spx) :: right)) :
    InjIn (genusCollapseStage q left)
      (genusCollapseStage q
        (left ++ [(qCubeToCoordinate t.1, Sum.inr t.1.spx)])) := by
  let p : GenusCollapsePair q := (qCubeToCoordinate t.1, Sum.inr t.1.spx)
  have htail : qCubeToCoordinate t.1 ∈ (p :: right).map Prod.fst := by simp [p]
  have hc := genusCollapseStage_suffix_certificate q left (p :: right) hsplit
  have hfree := hc.2.1
  have hi : qCubeToCoordinate t.1 ∈ spineInc (ASC.orderComplex (GenusVertex q))
      (Sum.inr t.1.spx) := by
    have hm : qCubeToCoordinate t.1 ∈
        spineInc (ASC.orderComplex (GenusVertex q)) (Sum.inr t.1.spx) ∩
          Collapse.remainingTops (topCubes (ASC.orderComplex (GenusVertex q))) left := by
      rw [hfree]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_inter.mp hm).1
  have htC : genusCollapseStage q left (Sum.inl t) :=
    ⟨genus_later_top_boundary_avoids_prefix_faces q left (p :: right) hsplit
        (Sum.inl t) t htail (le_refl _),
      ((Collapse.mem_remainingTops _ _ _).mp hc.1).2⟩
  have hf : truncatedCellDimension (Sum.inr (fullCutCell t hne)) = 2 := by
    change t.1.spx.card - 1 = 2
    omega
  have hface := genus_free_face_deletion_injIn q (genusCollapseStage q left)
    (Collapse.remainingTops (topCubes (ASC.orderComplex (GenusVertex q))) left)
    (Sum.inr (fullCutCell t hne)) t hf ht htC
    (fun d hd hdim => genusCollapseStage_active_top q left d hd hdim) hfree
  have hJ (x : GenusTruncatedCell q) :
      x ≠ Sum.inr (fullCutCell t hne) ∧ x < Sum.inl t ↔
        (genusCollapseStage q left x ∧ x ≠ Sum.inr (fullCutCell t hne)) ∧ x < Sum.inl t := by
    constructor
    · rintro ⟨hne, hlt⟩
      exact ⟨⟨genusCollapseStage_boundary_mem q left (p :: right) hsplit t htail x hlt, hne⟩, hlt⟩
    · simp_all
  have htop : InjIn (fun x => genusCollapseStage q left x ∧ x ≠ Sum.inr (fullCutCell t hne))
      (fun x => (genusCollapseStage q left x ∧ x ≠ Sum.inr (fullCutCell t hne)) ∧ x ≠ Sum.inl t) := by
    apply injIn_delete_maximal
    · intro x _ htx
      exact genus_top_cell_maximal q t ht x htx
    · obtain ⟨x, hxf, hxt⟩ := genus_top_boundary_nonempty q (Sum.inr (fullCutCell t hne)) hf t ht
      exact ⟨x, (hJ x).mp ⟨hxf, hxt⟩⟩
    · exact connectedIn_congr hJ (positiveCutPuncturedBoundary_connectedIn t hne hpositive ht)
    · intro v l hv hp hl
      have hnull := positiveCutPuncturedBoundary_simplyConnectedIn t hne hpositive ht v l
        ((hJ v).mpr hv) hp (pathIn_mono (fun x hx => (hJ x).mpr hx) hl)
      exact hnull.mono (fun x hx => (hJ x).mp hx)
  have hpair := injIn_trans (fun _ h => h.1) hface htop
  intro v l hv hp hl hh
  have hnull := hpair v l
    ((genusCollapseStage_cut_step_iff q left t hne v).mp hv) hp
    (pathIn_mono (fun x hx => (genusCollapseStage_cut_step_iff q left t hne x).mp hx) hl) hh
  exact hnull.mono (fun x hx => (genusCollapseStage_cut_step_iff q left t hne x).mpr hx)


/-- Every recorded cut-face pair satisfies the local collapse comparison. -/
theorem genus_recorded_cut_pair_stage_injIn
    (left right : List (GenusCollapsePair q))
    (σ : CutCell (cmpRel (GenusVertex q))) (t : QOld (cmpRel (GenusVertex q)))
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inr σ.1) :: right)) :
    InjIn (genusCollapseStage q left)
      (genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, Sum.inr σ.1)])) := by
  have hp : (qCubeToCoordinate t.1, Sum.inr σ.1) ∈ genusChainCollapse q := by
    rw [hsplit]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have ht  := (genus_oldCell_removed_iff_dimension_three q t).mp
    (List.mem_map.mpr ⟨(qCubeToCoordinate t.1, Sum.inr σ.1), hp, rfl⟩)
  have hc := genusCollapseStage_suffix_certificate q left
    ((qCubeToCoordinate t.1, Sum.inr σ.1) :: right) hsplit
  have hi : qCubeToCoordinate t.1 ∈ spineInc (ASC.orderComplex (GenusVertex q))
      (Sum.inr σ.1) := by
    have hm : qCubeToCoordinate t.1 ∈ spineInc (ASC.orderComplex (GenusVertex q))
        (Sum.inr σ.1) ∩
        Collapse.remainingTops (topCubes (ASC.orderComplex (GenusVertex q))) left := by
      rw [hc.2.1]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_inter.mp hm).1
  have he : qCubeToCoordinate t.1 = posCube σ.1 := by
    simp only [spineInc] at hi
    split at hi
    · simp_all
    · simp at hi
  have hs : t.1.spx = σ.1 := by
    have hh := congrArg freeSet he
    simpa using hh
  have hpositive : t.1.sgn = 0 := by
    funext v
    have hh := qCubeToCoordinate_parity t.1 v
    rw [he] at hh
    by_cases hv : v ∈ σ.1
    · simpa [posCube, hv] using hh.symm
    · simpa [posCube, hv] using hh.symm
  have hne  := hs.symm ▸ σ.2.1
  have hstep := genus_cut_pair_stage_injIn q left right t hne ht hpositive
    (by simpa only [hs] using hsplit)
  simpa only [hs] using hstep

end FiniteChains.Davis.Genus

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

/-- Every admissible coordinate cube of positive dimension is an actual retained cell. -/
theorem exists_oldCell_of_coordinate (c : Cube (GenusVertex q))
    (hc : freeSet c ∈ (ASC.orderComplex (GenusVertex q)).faces)
    (hne : (freeSet c).Nonempty) :
    ∃ d : QOld (cmpRel (GenusVertex q)), qCubeToCoordinate d.1 = c := by
  have hs : IsSimplex (cmpRel (GenusVertex q)) (freeSet c) := by
    apply isSimplex_cmpRel_iff.mpr
    intro a ha b hb
    by_cases hab : a = b
    · simp_all
    · exact hc ha hb hab
  let d := coordinateToQCube ⟨c, hs⟩
  have hd : qCubeToCoordinate d = c := coordinateToQCube_toCoordinate _
  have hold : ¬ (d.spx = ∅ ∧ d.sgn = 0) := by
    rintro ⟨he, _⟩
    exact Finset.nonempty_iff_ne_empty.mp hne he
  exact ⟨⟨d, hold⟩, hd⟩

/-- Every coordinate pair in the certificate decodes to a genuine top and facet. -/
theorem genus_pair_cells (p : GenusCollapsePair q)
    (hp : p ∈ genusChainCollapse q) :
    ∃ (t : QOld (cmpRel (GenusVertex q))) (f : GenusTruncatedCell q),
      qCubeToCoordinate t.1 = p.1 ∧ truncatedFaceIndex f = p.2 := by
  have hc := genusChainCollapse_isPairCollapse q
  have ht := mem_topCubes.mp (hc.top_mem hp)
  obtain ⟨t, htc⟩ := exists_oldCell_of_coordinate q p.1 ht.1
    (Finset.card_pos.mp (by have hh := ht.2; omega))
  have hi := hc.pair_inc hp
  cases hf : p.2 with
  | inl g =>
    rw [hf] at hi
    simp only [spineInc] at hi
    split at hi
    next hg =>
      obtain ⟨j, _, hjL, _⟩ := mem_cofaces.mp hi
      have hgL : freeSet g ∈ (ASC.orderComplex (GenusVertex q)).faces := by
        intro a ha b hb hab
        exact hjL (Finset.mem_insert_of_mem ha) (Finset.mem_insert_of_mem hb) hab
      obtain ⟨f, hfc⟩ := exists_oldCell_of_coordinate q g hgL
        (Finset.card_pos.mp (by omega))
      exact ⟨t, Sum.inl f, htc, by simp only [truncatedFaceIndex, hfc]⟩
    next => simp at hi
  | inr σ =>
    rw [hf] at hi
    simp only [spineInc] at hi
    split at hi
    next hσ =>
      have hs : IsSimplex (cmpRel (GenusVertex q)) σ := by
        apply isSimplex_cmpRel_iff.mpr
        intro a ha b hb
        by_cases hab : a = b
        · simp_all
        · exact hσ.1 ha hb hab
      let f : CutCell (cmpRel (GenusVertex q)) :=
        ⟨σ, Finset.card_pos.mp (by have hh := hσ.2; omega), hs⟩
      exact ⟨t, Sum.inr f, htc, rfl⟩
    next => simp at hi

/-- Each pair in the chosen coordinate list reflects null homotopies at its stage. -/

theorem genusCollapseStage_append_subset (left right : List (GenusCollapsePair q))
    (c : GenusTruncatedCell q) (hc : genusCollapseStage q (left ++ right) c) :
    genusCollapseStage q left c := by
  constructor
  · intro hm
    exact hc.1 (by simpa using Or.inl hm)
  · cases c with
    | inl d =>
      intro hm
      exact hc.2 (by simpa using Or.inl hm)
    | inr σ => trivial

/-- Null homotopy reflection through the entire genuine geometric collapse. -/
theorem genus_collapse_suffix_injIn (right left : List (GenusCollapsePair q))
    (hsplit : genusChainCollapse q = left ++ right) :
    InjIn (genusCollapseStage q left) (genusCollapseStage q (left ++ right)) := by
  induction right generalizing left with
  | nil => simpa using injIn_self (genusCollapseStage q left)
  | cons p right ih =>
    have hfirst := (show InjIn (genusCollapseStage q left) (genusCollapseStage q (left ++ [p])) by
      have hp : p ∈ genusChainCollapse q := by
        rw [hsplit]
        exact List.mem_append.mpr (Or.inr List.mem_cons_self)
      obtain ⟨t, f, ht, hf⟩ := genus_pair_cells q p hp
      have he : p = (qCubeToCoordinate t.1, truncatedFaceIndex f) :=
        Prod.ext ht.symm hf.symm
      rw [he] at hsplit ⊢
      cases f with
      | inl f => exact genus_old_pair_stage_injIn q left right f t hsplit
      | inr σ => exact genus_recorded_cut_pair_stage_injIn q left right σ t hsplit)
    have htail := ih (left ++ [p]) (by simpa using hsplit)
    have hcombined := injIn_trans
      (genusCollapseStage_append_subset q (left ++ [p]) right) hfirst htail
    simpa using hcombined

/-- The actual surviving spine reflects all based null homotopies of the truncated block. -/


theorem genusSpineToOld_pi1_injective :
    Function.Injective (pi1Map (genusSpineToOld q) (spineBase q)) :=
  (genusSpine_pi1_injective_iff q).mpr (by
    have hincl : Function.Injective
        (pi1Map (orderCxMap (fun c : GenusSpineCell q => c.1) monotone_subtypeVal)
          (spineBase q)) :=
      pi1Map_injective_of_injIn (by
        have h := genus_collapse_suffix_injIn q (genusChainCollapse q) [] (by simp)
        intro v l hv hp hl hh
        have hnull := h v l
          (by simpa only [List.nil_append, genusCollapseStage_final_iff] using hv) hp
          (pathIn_mono (fun c hc => (genusCollapseStage_final_iff q c).mpr hc) hl)
          (hh.mono (fun c _ => genusCollapseStage_nil q c))
        exact hnull.mono (fun c hc => (genusCollapseStage_final_iff q c).mp hc)) monotone_subtypeVal
        (fun c => c.2) monotone_id (fun _ => rfl) (spineBase q)
    have hfactor (z : Pi1 (genusSpineCx q) (spineBase q)) :
        pi1Map (genusSpineToTruncated q) (spineBase q) z =
          pi1Map (orderCxMap (fun c : GenusSpineCell q => c.1) monotone_subtypeVal)
            (spineBase q) (strictOrderPi1Equiv (P := GenusSpineCell q) (spineBase q) z) := by
      induction z using Quotient.inductionOn with
      | h p =>
        apply congrArg Pi1.mk
        apply Subtype.ext
        simp [genusSpineToTruncated, mapPath, Hom.comp, List.map_map, Function.comp_def]
    intro z w he
    apply (strictOrderPi1Equiv (P := GenusSpineCell q) (spineBase q)).injective
    apply hincl
    rwa [← hfactor z, ← hfactor w])

end FiniteChains.Davis.Genus
end
