module

public import PottsDiscontinuity.FK.Lattice
public import PottsDiscontinuity.TorusTopology.PlanarFiniteCompassFan
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology
open SimpleGraph Planar.Medial

def squareDartCompass (d : FK.squareLattice.Dart) : Fin 4 :=
  if d.fst.1 < d.snd.1 then 0 else if d.fst.2 < d.snd.2 then 1
  else if d.snd.1 < d.fst.1 then 2 else 3

def squareWalkCompassDirections {u v : ℤ × ℤ} (p : FK.squareLattice.Walk u v) :
    List (Fin 4) := p.darts.map squareDartCompass

def squareWalkCyclicTurn {u : ℤ × ℤ} (p : FK.squareLattice.Walk u u) : ℤ :=
  ((squareWalkCompassDirections p).zipWith primalCompassQuarterTurn
    ((squareWalkCompassDirections p).rotate 1)).sum

private abbrev V := ℤ × ℤ

lemma grid_zmod2_two (a : ZMod 2) : a + a = 0 := by fin_cases a <;> decide
private lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact .inl rfl
  · exact .inr rfl

def gridVEdge (x y : ℤ) : Sym2 (ℤ × ℤ) := s((x, y), (x, y + 1))
def gridHEdge (x y : ℤ) : Sym2 (ℤ × ℤ) := s((x, y), (x + 1, y))

private lemma gridVEdge_inj {x₁ y₁ x₂ y₂ : ℤ} (h : gridVEdge x₁ y₁ = gridVEdge x₂ y₂) :
    x₁ = x₂ ∧ y₁ = y₂ := by simp only [gridVEdge, Sym2.eq_iff, Prod.ext_iff] at h; omega

private lemma gridHEdge_inj {x₁ y₁ x₂ y₂ : ℤ} (h : gridHEdge x₁ y₁ = gridHEdge x₂ y₂) :
    x₁ = x₂ ∧ y₁ = y₂ := by simp only [gridHEdge, Sym2.eq_iff, Prod.ext_iff] at h; omega

private lemma gridVEdge_ne_hEdge (x₁ y₁ x₂ y₂ : ℤ) : gridVEdge x₁ y₁ ≠ gridHEdge x₂ y₂ := by
  intro h; simp only [gridVEdge, gridHEdge, Sym2.eq_iff, Prod.ext_iff] at h; omega

private lemma adj_edge_cases {u v : V} (h : FK.squareLattice.Adj u v) :
    (∃ x y, s(u, v) = gridVEdge x y) ∨ (∃ x y, s(u, v) = gridHEdge x y) := by
  rcases (FK.squareLattice_adj_iff u v).mp h with ⟨hx | hx, hy⟩ | ⟨hx, hy | hy⟩
  · exact .inr ⟨u.1, u.2, by simp [gridHEdge, Prod.ext_iff]; omega⟩
  · exact .inr ⟨v.1, v.2, by simp [gridHEdge, Prod.ext_iff]; omega⟩
  · exact .inl ⟨u.1, u.2, by simp [gridVEdge, Prod.ext_iff]; omega⟩
  · exact .inl ⟨v.1, v.2, by simp [gridVEdge, Prod.ext_iff]; omega⟩

private def rayEdge (v : V) : Fin 4 → Sym2 V
  | 0 => gridHEdge v.1 v.2 | 1 => gridVEdge v.1 v.2 | 2 => gridHEdge (v.1 - 1) v.2 | 3 => gridVEdge v.1 (v.2 - 1)

private lemma rayEdge_mem_self (v : V) (d : Fin 4) : v ∈ rayEdge v d := by
  fin_cases d <;> simp [rayEdge, gridHEdge, gridVEdge]

private lemma rayEdge_inj (v : V) : Function.Injective (rayEdge v) := by
  intro d₁ d₂ h; fin_cases d₁ <;> fin_cases d₂ <;> try rfl
  all_goals exfalso; first
    | exact gridVEdge_ne_hEdge _ _ _ _ h | exact gridVEdge_ne_hEdge _ _ _ _ h.symm
    | (have := gridHEdge_inj h; omega) | (have := gridVEdge_inj h; omega)

private lemma dart_cases (dt : FK.squareLattice.Dart) :
    (dt.snd = (dt.fst.1 + 1, dt.fst.2) ∧ squareDartCompass dt = 0) ∨
    (dt.snd = (dt.fst.1, dt.fst.2 + 1) ∧ squareDartCompass dt = 1) ∨
    (dt.fst = (dt.snd.1 + 1, dt.snd.2) ∧ squareDartCompass dt = 2) ∨
    (dt.fst = (dt.snd.1, dt.snd.2 + 1) ∧ squareDartCompass dt = 3) := by
  obtain ⟨⟨a, b⟩, hadj⟩ := dt; unfold squareDartCompass; dsimp only
  rcases (FK.squareLattice_adj_iff a b).mp hadj with ⟨hx | hx, hy⟩ | ⟨hx, hy | hy⟩
  · exact .inl ⟨by ext <;> omega, ite_eq_left (by omega)⟩
  · exact .inr (.inr (.inl ⟨by ext <;> omega, by rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]⟩))
  · exact .inr (.inl ⟨by ext <;> omega, by rw [ite_eq_right (by omega), ite_eq_left (by omega)]⟩)
  · exact .inr (.inr (.inr ⟨by ext <;> omega, by rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]⟩))

private lemma dart_edge_eq_rayEdge (dt : FK.squareLattice.Dart) :
    dt.edge = rayEdge dt.fst (squareDartCompass dt) ∧ dt.edge = rayEdge dt.snd (squareDartCompass dt + 2) := by
  rcases dart_cases dt with ⟨h, hc⟩ | ⟨h, hc⟩ | ⟨h, hc⟩ | ⟨h, hc⟩ <;> rw [hc] <;>
    change s(dt.fst, dt.snd) = _ ∧ s(dt.fst, dt.snd) = _ <;> rw [h] <;>
    simp [rayEdge, gridHEdge, gridVEdge, Sym2.eq_swap]

noncomputable def gridWalkInd {a b : ℤ × ℤ} : FK.squareLattice.Walk a b → Sym2 (ℤ × ℤ) → ZMod 2
  | .nil => fun _ => 0
  | @Walk.cons _ _ a c _ _ rest => fun e => (if e = s(a, c) then 1 else 0) + gridWalkInd rest e

private lemma gridWalkInd_eq_ite {a b : ℤ × ℤ} (w : FK.squareLattice.Walk a b) (hnodup : w.edges.Nodup) (e : Sym2 (ℤ × ℤ)) :
    gridWalkInd w e = if e ∈ w.edges then 1 else 0 := by
  induction w with
  | nil => simp [gridWalkInd]
  | @cons a c _ _ rest ih =>
    rw [Walk.edges_cons, List.nodup_cons] at hnodup
    simp only [gridWalkInd, Walk.edges_cons, List.mem_cons, ih hnodup.2]
    by_cases he : e = s(a, c) <;> simp_all

lemma gridWalkInd_eq_zero_of_not_mem {a b : ℤ × ℤ} (w : FK.squareLattice.Walk a b)
    {e : Sym2 (ℤ × ℤ)} (he : e ∉ w.edges) : gridWalkInd w e = 0 := by
  induction w with
  | nil => rfl
  | cons _ rest ih =>
    rw [Walk.edges_cons, List.mem_cons, not_or] at he
    simp [gridWalkInd, he.1, ih he.2]

private def gridVDeg (f : Sym2 V → ZMod 2) (z : V) : ZMod 2 := ∑ d : Fin 4, f (rayEdge z d)

private lemma z2_chain (xa xc xb : ZMod 2) : (xa + xc) + (xc + xb) = xa + xb := by revert xa xc xb; decide

private lemma gridVDeg_walkInd {a b : V} (w : FK.squareLattice.Walk a b) (z : V) :
    gridVDeg (gridWalkInd w) z = (if z = a then 1 else 0) + (if z = b then 1 else 0) := by
  induction w with
  | nil => unfold gridVDeg gridWalkInd; simp [grid_zmod2_two]
  | @cons a c b hadj rest ih =>
    let dt : FK.squareLattice.Dart := ⟨⟨a, c⟩, hadj⟩
    have hs : gridVDeg (fun e => if e = s(a, c) then (1 : ZMod 2) else 0) z =
        (if z = a then 1 else 0) + (if z = c then 1 else 0) := by
      unfold gridVDeg
      by_cases hza : z = a
      · subst hza; rw [ite_eq_right (FK.squareLattice.ne_of_adj hadj), ite_eq_left rfl, add_zero,
          Finset.sum_eq_single (squareDartCompass dt)
            (fun d _ hd => ite_eq_right fun h => hd (rayEdge_inj z (h.trans (dart_edge_eq_rayEdge dt).1))) (by simp),
          ite_eq_left (show rayEdge z (squareDartCompass dt) = s(z, c) from (dart_edge_eq_rayEdge dt).1.symm)]
      · by_cases hzc : z = c
        · subst hzc; rw [ite_eq_right hza, ite_eq_left rfl, zero_add,
            Finset.sum_eq_single (squareDartCompass dt + 2)
              (fun d _ hd => ite_eq_right fun h => hd (rayEdge_inj z (h.trans (dart_edge_eq_rayEdge dt).2))) (by simp),
            ite_eq_left (show rayEdge z (squareDartCompass dt + 2) = s(a, z) from (dart_edge_eq_rayEdge dt).2.symm)]
        · rw [ite_eq_right hza, ite_eq_right hzc, add_zero]
          exact Finset.sum_eq_zero fun d _ => ite_eq_right fun h =>
            (Sym2.mem_iff.mp (h ▸ rayEdge_mem_self z d)).elim hza hzc
    change (∑ d : Fin 4, ((if rayEdge z d = s(a, c) then 1 else 0) + gridWalkInd rest (rayEdge z d))) = _
    rw [Finset.sum_add_distrib]; exact (congrArg₂ _ hs ih).trans (z2_chain _ _ _)

lemma gridRowVEdgeSum (x₀ x₁ y : ℤ) {a b : ℤ × ℤ} (w : FK.squareLattice.Walk a b)
    (hsupp : ∀ v ∈ w.support, x₀ ≤ v.1 ∧ v.1 ≤ x₁) :
    ∑ x ∈ Finset.Icc x₀ x₁, gridWalkInd w (gridVEdge x y) =
      (if y < a.2 then 1 else 0) + (if y < b.2 then 1 else 0) := by
  have hv_one (u c : V) (huc : s(u, c) = gridVEdge u.1 u.2) (hu : x₀ ≤ u.1 ∧ u.1 ≤ x₁) (huy : u.2 < c.2) :
      (∑ x ∈ Finset.Icc x₀ x₁, if gridVEdge x y = s(u, c) then (1 : ZMod 2) else 0) =
        (if y < u.2 then 1 else 0) + (if y < c.2 then 1 else 0) := by
    rw [huc]
    have hcy : c.2 = u.2 + 1 := by have := Sym2.eq_iff.mp huc; simp only [Prod.ext_iff] at this; omega
    by_cases hy' : y = u.2
    · subst hy'
      rw [Finset.sum_eq_single u.1 (fun x _ hx' => ite_eq_right fun h => hx' (gridVEdge_inj h).1)
        (fun h => absurd (Finset.mem_Icc.mpr hu) h)]; simp [huy]
    · rw [Finset.sum_eq_zero fun x _ => ite_eq_right fun h => hy' (gridVEdge_inj h).2]
      by_cases hlt : y < u.2 <;> simp [hlt, show (y < c.2) ↔ (y < u.2) by omega, grid_zmod2_two]
  induction w with
  | nil => simp [gridWalkInd, grid_zmod2_two]
  | @cons a c b hadj rest ih =>
    simp only [gridWalkInd, Finset.sum_add_distrib, ih fun v hv => hsupp v (List.mem_cons_of_mem _ hv)]
    have hsingle : (∑ x ∈ Finset.Icc x₀ x₁, if gridVEdge x y = s(a, c) then (1 : ZMod 2) else 0) =
        (if y < a.2 then 1 else 0) + (if y < c.2 then 1 else 0) := by
      rcases (FK.squareLattice_adj_iff a c).mp hadj with ⟨_, hy⟩ | ⟨hx, hy | hy⟩
      · rw [Finset.sum_eq_zero fun x _ => ite_eq_right fun h => gridVEdge_ne_hEdge x y (min a.1 c.1) a.2
          (h.trans (by simp [gridHEdge, Prod.ext_iff]; omega)), show c.2 = a.2 by omega, grid_zmod2_two]
      · exact hv_one a c (by simp [gridVEdge, Prod.ext_iff]; omega) (hsupp a (by simp)) (by omega)
      · rw [Sym2.eq_swap, add_comm]
        exact hv_one c a (by simp [gridVEdge, Prod.ext_iff]; omega) (hsupp c (by simp)) (by omega)
    rw [hsingle]; exact z2_chain _ _ _

noncomputable def gridRayPot (x₀ : ℤ) {a b : ℤ × ℤ} (w : FK.squareLattice.Walk a b) (x y : ℤ) : ZMod 2 :=
  ∑ x' ∈ Finset.Icc x₀ x, gridWalkInd w (gridVEdge x' y)

lemma gridRayPot_step_x (x₀ : ℤ) {a b : ℤ × ℤ} (w : FK.squareLattice.Walk a b) {x : ℤ} (hx : x₀ ≤ x) (y : ℤ) :
    gridRayPot x₀ w x y + gridRayPot x₀ w (x - 1) y = gridWalkInd w (gridVEdge x y) := by
  unfold gridRayPot
  rw [show Finset.Icc x₀ x = insert x (Finset.Icc x₀ (x - 1)) by
    ext t; simp only [Finset.mem_Icc, Finset.mem_insert]; omega, Finset.sum_insert (by simp),
    add_assoc, grid_zmod2_two, add_zero]

private lemma z2_step0 {x1 x2 x3 : ZMod 2} (h : x3 + x1 + 0 + x2 = 0) : x1 + x2 = x3 := by
  revert x1 x2 x3 h; decide

private lemma z2_stepS {i1 i0 j1 j0 v1 v0 h1 h0 : ZMod 2}
    (hx1 : i1 + i0 = v1) (hx2 : j1 + j0 = v0) (hd : h1 + v1 + h0 + v0 = 0) (ih : i0 + j0 = h0) :
    i1 + j1 = h1 := by revert i1 i0 j1 j0 v1 v0 h1 h0 hx1 hx2 hd ih; decide

lemma gridRayPot_step_y (x₀ : ℤ) {u : ℤ × ℤ} (p : FK.squareLattice.Walk u u)
    (hleft : ∀ y', gridWalkInd p (gridHEdge (x₀ - 1) y') = 0) {x : ℤ} (hx : x₀ ≤ x) (y : ℤ) :
    gridRayPot x₀ p x y + gridRayPot x₀ p x (y - 1) = gridWalkInd p (gridHEdge x y) := by
  have hdeg (x' : ℤ) : gridWalkInd p (gridHEdge x' y) + gridWalkInd p (gridVEdge x' y) +
      gridWalkInd p (gridHEdge (x' - 1) y) + gridWalkInd p (gridVEdge x' (y - 1)) = 0 := by
    have hd := gridVDeg_walkInd p (x', y)
    rw [grid_zmod2_two] at hd; unfold gridVDeg at hd; rw [Fin.sum_univ_four] at hd
    simpa [rayEdge, add_assoc] using hd
  have htel (k : ℕ) : gridRayPot x₀ p (x₀ + k) y + gridRayPot x₀ p (x₀ + k) (y - 1) =
      gridWalkInd p (gridHEdge (x₀ + k) y) := by
    induction k with
    | zero =>
      simp only [Nat.cast_zero, add_zero, gridRayPot, Finset.Icc_self, Finset.sum_singleton]
      have hd := hdeg x₀; rw [hleft y] at hd; exact z2_step0 hd
    | succ k ih =>
      have heq : x₀ + ((k + 1 : ℕ) : ℤ) - 1 = x₀ + (k : ℤ) := by push_cast; ring
      have hx1 := gridRayPot_step_x x₀ p (x := x₀ + ((k + 1 : ℕ) : ℤ)) (by omega) y
      have hx2 := gridRayPot_step_x x₀ p (x := x₀ + ((k + 1 : ℕ) : ℤ)) (by omega) (y - 1)
      have hd := hdeg (x₀ + ((k + 1 : ℕ) : ℤ))
      rw [heq] at hx1 hx2 hd
      exact z2_stepS hx1 hx2 hd ih
  have ht := htel (x - x₀).toNat
  rwa [show x₀ + ((x - x₀).toNat : ℤ) = x by omega] at ht

private def walkBound {a b : V} (w : FK.squareLattice.Walk a b) : ℤ :=
  (w.support.foldr (fun u m => max m (max u.1.natAbs u.2.natAbs)) 0 : ℕ) + 1

private lemma mem_support_lt_walkBound {a b : V} (w : FK.squareLattice.Walk a b) {v : V} (hv : v ∈ w.support) :
    -walkBound w < v.1 ∧ v.1 < walkBound w ∧ -walkBound w < v.2 ∧ v.2 < walkBound w := by
  let M : ℕ := w.support.foldr (fun u m => max m (max u.1.natAbs u.2.natAbs)) 0
  have hle : ∀ l : List V, v ∈ l → max v.1.natAbs v.2.natAbs ≤ l.foldr (fun u m => max m (max u.1.natAbs u.2.natAbs)) 0 := by
    intro l hl; induction l with
    | nil => simp at hl
    | cons u rest ih => rcases List.mem_cons.mp hl with rfl | hl; exact le_max_right _ _; exact (ih hl).trans (le_max_left _ _)
  have h : max v.1.natAbs v.2.natAbs ≤ M := hle w.support hv
  have h1 : v.1.natAbs ≤ M := (le_max_left _ _).trans h
  have h2 : v.2.natAbs ≤ M := (le_max_right _ _).trans h
  change -((M : ℤ) + 1) < v.1 ∧ v.1 < (M : ℤ) + 1 ∧ -((M : ℤ) + 1) < v.2 ∧ v.2 < (M : ℤ) + 1; omega

private lemma wInd_outside {a b : V} (w : FK.squareLattice.Walk a b) {e : Sym2 V}
    (hout : ∃ v ∈ e, v.1 ≤ -walkBound w ∨ walkBound w ≤ v.1 ∨ v.2 ≤ -walkBound w ∨ walkBound w ≤ v.2) :
    gridWalkInd w e = 0 := by
  apply gridWalkInd_eq_zero_of_not_mem; intro hm
  obtain ⟨dt, hdt, hdt_eq⟩ := List.mem_map.mp hm; obtain ⟨v, hv, ho⟩ := hout
  rcases Sym2.mem_iff.mp (hdt_eq ▸ hv) with rfl | rfl
  · have := mem_support_lt_walkBound w (Walk.dart_fst_mem_support_of_mem_darts w hdt); omega
  · have := mem_support_lt_walkBound w (Walk.dart_snd_mem_support_of_mem_darts w hdt); omega

private noncomputable def insideZ {u : V} (p : FK.squareLattice.Walk u u) (x y : ℤ) : ZMod 2 :=
  gridRayPot (-walkBound p) p x y

private lemma insideZ_outside {u : V} (p : FK.squareLattice.Walk u u) {x y : ℤ}
    (ho : x < -walkBound p ∨ walkBound p ≤ x ∨ y ≤ -walkBound p ∨ walkBound p ≤ y) :
    insideZ p x y = 0 := by
  unfold insideZ gridRayPot
  rcases ho with hx | hx | hy | hy
  · rw [Finset.Icc_eq_empty (by omega)]; simp
  · rw [← Finset.sum_subset (s₁ := Finset.Icc (-walkBound p) (walkBound p))
      (fun a ha => by simp only [Finset.mem_Icc] at ha ⊢; omega)
      (fun a ha hna => by simp only [Finset.mem_Icc] at ha hna; exact wInd_outside p ⟨(a, y), by simp [gridVEdge], by omega⟩),
      gridRowVEdgeSum (-walkBound p) (walkBound p) y p
        (fun v hv => by have := mem_support_lt_walkBound p hv; omega), grid_zmod2_two]
  · exact Finset.sum_eq_zero fun x' _ => wInd_outside p ⟨(x', y), by simp [gridVEdge], by omega⟩
  · exact Finset.sum_eq_zero fun x' _ => wInd_outside p ⟨(x', y + 1), by simp [gridVEdge], by omega⟩

private lemma insideZ_step_x {u : V} (p : FK.squareLattice.Walk u u) (x y : ℤ) :
    insideZ p x y + insideZ p (x - 1) y = gridWalkInd p (gridVEdge x y) := by
  by_cases hx : -walkBound p ≤ x
  · exact gridRayPot_step_x (-walkBound p) p hx y
  · rw [insideZ_outside p (by omega), insideZ_outside p (by omega), add_zero]
    exact (wInd_outside p ⟨(x, y), by simp [gridVEdge], by omega⟩).symm

private lemma insideZ_step_y {u : V} (p : FK.squareLattice.Walk u u) (x y : ℤ) :
    insideZ p x y + insideZ p x (y - 1) = gridWalkInd p (gridHEdge x y) := by
  by_cases hx : -walkBound p ≤ x
  · exact gridRayPot_step_y (-walkBound p) p
      (fun y' => wInd_outside p ⟨(-walkBound p - 1, y'), by simp [gridHEdge], by omega⟩) hx y
  · rw [insideZ_outside p (by omega), insideZ_outside p (by omega), add_zero]
    exact (wInd_outside p ⟨(x, y), by simp [gridHEdge], by omega⟩).symm

private noncomputable def fillSet {u : V} (p : FK.squareLattice.Walk u u) : Finset V :=
  (Finset.Icc (-walkBound p) (walkBound p) ×ˢ Finset.Icc (-walkBound p) (walkBound p)).filter
    fun s => insideZ p s.1 s.2 = 1

private lemma mem_fillSet {u : V} (p : FK.squareLattice.Walk u u) (s : V) :
    s ∈ fillSet p ↔ insideZ p s.1 s.2 = 1 := by
  unfold fillSet; rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  by_contra hout
  exact absurd (insideZ_outside p (by omega : s.1 < -walkBound p ∨ walkBound p ≤ s.1 ∨ s.2 ≤ -walkBound p ∨ walkBound p ≤ s.2) ▸ h) (by decide)

private lemma fillSet_bounds {u : V} (p : FK.squareLattice.Walk u u) {s : V} (hs : s ∈ fillSet p) :
    -walkBound p ≤ s.1 ∧ s.1 < walkBound p ∧ -walkBound p < s.2 ∧ s.2 < walkBound p := by
  have h := (mem_fillSet p s).mp hs
  by_contra hout
  exact absurd (insideZ_outside p (by omega : s.1 < -walkBound p ∨ walkBound p ≤ s.1 ∨ s.2 ≤ -walkBound p ∨ walkBound p ≤ s.2) ▸ h) (by decide)

private lemma fillSet_nonempty {u : V} (p : FK.squareLattice.Walk u u) (hp : p.IsCycle) :
    (fillSet p).Nonempty := by
  cases p with
  | nil => exact absurd rfl hp.ne_nil
  | @cons _ c _ hadj rest =>
    have hw : gridWalkInd (Walk.cons hadj rest) s(u, c) = 1 := by rw [gridWalkInd_eq_ite _ hp.edges_nodup]; simp
    have hsp (a b : V) (hab : insideZ (Walk.cons hadj rest) a.1 a.2 + insideZ (Walk.cons hadj rest) b.1 b.2 = 1) :
        (fillSet (Walk.cons hadj rest)).Nonempty := by
      rcases zmod2_cases (insideZ (Walk.cons hadj rest) a.1 a.2) with h0 | h1
      · rw [h0, zero_add] at hab; exact ⟨b, (mem_fillSet _ _).mpr hab⟩
      · exact ⟨a, (mem_fillSet _ _).mpr h1⟩
    rcases adj_edge_cases hadj with ⟨x, y, he⟩ | ⟨x, y, he⟩
    · rw [he, ← insideZ_step_x] at hw; exact hsp (x, y) (x - 1, y) hw
    · rw [he, ← insideZ_step_y] at hw; exact hsp (x, y) (x, y - 1) hw

private def sectorSq (v : V) : Fin 4 → V
  | 0 => (v.1, v.2) | 1 => (v.1 - 1, v.2) | 2 => (v.1 - 1, v.2 - 1) | 3 => (v.1, v.2 - 1)

private def vertexSectors (S : Finset V) (v : V) : Finset (Fin 4) :=
  Finset.univ.filter fun d => sectorSq v d ∈ S

private lemma sector_boundary_zmod2 {u : V} (p : FK.squareLattice.Walk u u) (v : V) (d : Fin 4) :
    (compassSectorBoundary (vertexSectors (fillSet p) v) d : ZMod 2) = gridWalkInd p (rayEdge v d) := by
  have hmem (s : Fin 4) : (if s ∈ vertexSectors (fillSet p) v then (1 : ZMod 2) else 0) =
      insideZ p (sectorSq v s).1 (sectorSq v s).2 := by
    simp only [vertexSectors, Finset.mem_filter, Finset.mem_univ, true_and, mem_fillSet]
    rcases zmod2_cases (insideZ p (sectorSq v s).1 (sectorSq v s).2) with h | h <;> simp [h]
  have hsub (a b : ZMod 2) : a - b = a + b ∧ b - a = a + b := by revert a b; decide
  unfold compassSectorBoundary; push_cast; rw [hmem d, hmem (d - 1)]
  fin_cases d
  · exact (hsub _ _).1.trans (insideZ_step_y p v.1 v.2)
  · exact (hsub _ _).2.trans (insideZ_step_x p v.1 v.2)
  · exact (hsub _ _).2.trans (insideZ_step_y p (v.1 - 1) v.2)
  · exact (hsub _ _).1.trans (insideZ_step_x p v.1 (v.2 - 1))

private lemma sector_boundary_vals (Q : Finset (Fin 4)) (d : Fin 4) :
    compassSectorBoundary Q d = 0 ∨ compassSectorBoundary Q d = 1 ∨ compassSectorBoundary Q d = -1 := by
  unfold compassSectorBoundary; by_cases h1 : d ∈ Q <;> by_cases h2 : d - 1 ∈ Q <;> simp [h1, h2]

private lemma sector_boundary_opp (S : Finset V) (dt : FK.squareLattice.Dart) :
    compassSectorBoundary (vertexSectors S dt.snd) (squareDartCompass dt + 2) =
      -compassSectorBoundary (vertexSectors S dt.fst) (squareDartCompass dt) := by
  have hmem (v s) : (if s ∈ vertexSectors S v then (1 : ℤ) else 0) = if sectorSq v s ∈ S then 1 else 0 := by simp [vertexSectors]
  rcases dart_cases dt with ⟨h, hc⟩ | ⟨h, hc⟩ | ⟨h, hc⟩ | ⟨h, hc⟩ <;>
    rw [hc] <;> unfold compassSectorBoundary <;> rw [hmem, hmem, hmem, hmem, h] <;>
    simp only [show (0 : Fin 4) + 2 = 2 by decide, show (1 : Fin 4) + 2 = 3 by decide,
      show (2 : Fin 4) + 2 = 0 by decide, show (3 : Fin 4) + 2 = 1 by decide,
      show (0 : Fin 4) - 1 = 3 by decide, show (1 : Fin 4) - 1 = 0 by decide,
      show (2 : Fin 4) - 1 = 1 by decide, show (3 : Fin 4) - 1 = 2 by decide,
      sectorSq, add_sub_cancel_right] <;> abel

private lemma cycle_dart_rays {u : V} (p : FK.squareLattice.Walk u u) (hp : p.IsCycle)
    (i : ℕ) (hi : i < p.darts.length) :
    let d_in := p.darts[i]
    let d_out := (p.darts.rotate 1)[i]'(by simpa using hi)
    d_in.snd = d_out.fst ∧ squareDartCompass d_in + 2 ≠ squareDartCompass d_out ∧
      ∀ d : Fin 4, rayEdge d_in.snd d ∈ p.edges ↔
        d = squareDartCompass d_out ∨ d = squareDartCompass d_in + 2 := by
  have hlen3 : 3 ≤ p.darts.length := Walk.length_darts p ▸ hp.three_le_length
  intro d_in d_out
  have hrot_fst : (p.darts.rotate 1).map (·.fst) = p.darts.map (·.snd) := by
    rw [List.map_rotate, Walk.map_fst_darts, Walk.map_snd_darts]
    cases p with
    | nil => exact absurd rfl hp.ne_nil
    | cons _ rest =>
      simp only [Walk.support_cons, List.tail_cons, List.dropLast_cons_of_ne_nil (Walk.support_ne_nil rest),
        List.rotate_cons_succ, List.rotate_zero]
      have hinit := (List.dropLast_append_getLast (Walk.support_ne_nil rest)).symm
      rw [Walk.getLast_support rest] at hinit; exact hinit.symm
  have hv_eq : d_in.snd = d_out.fst := by
    have hget := congrArg (·[i]?) hrot_fst
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem (by simpa using hi : i < (p.darts.rotate 1).length), Option.map_some, Option.some.injEq] at hget
    exact hget.symm
  have hj_lt : (i + 1) % p.darts.length < p.darts.length := Nat.mod_lt _ (by omega)
  have hd_out_eq : d_out = p.darts[(i + 1) % p.darts.length] := @List.getElem_rotate _ p.darts 1 i (by simpa using hi)
  have hij_ne : i ≠ (i + 1) % p.darts.length := by
    by_cases hlt : i + 1 < p.darts.length
    · rw [Nat.mod_eq_of_lt hlt]; omega
    · rw [show i + 1 = p.darts.length by omega, Nat.mod_self]; omega
  have hab_ne : squareDartCompass d_in + 2 ≠ squareDartCompass d_out := fun hab =>
    hij_ne <| (List.Nodup.getElem_inj_iff hp.edges_nodup).mp <| by
      change (p.darts.map Dart.edge)[i]'(by simpa using hi) =
        (p.darts.map Dart.edge)[(i + 1) % p.darts.length]'(by simpa using hj_lt)
      simp only [List.getElem_map]; rw [← hd_out_eq]
      exact (dart_edge_eq_rayEdge d_in).2.trans (by rw [hab, hv_eq, ← (dart_edge_eq_rayEdge d_out).1])
  have hsnd_nodup : (p.darts.map (·.snd)).Nodup := Walk.map_snd_darts p ▸ hp.support_nodup
  have hfst_nodup : (p.darts.map (·.fst)).Nodup := by rw [← List.nodup_rotate (n := 1), ← List.map_rotate, hrot_fst]; exact hsnd_nodup
  refine ⟨hv_eq, hab_ne, fun d => ⟨fun hmem => ?_, ?_⟩⟩
  · obtain ⟨dt, hdt_mem, hdt_eq⟩ := List.mem_map.mp hmem
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hdt_mem
    rcases Sym2.mem_iff.mp (hdt_eq ▸ rayEdge_mem_self d_in.snd d) with hfst | hsnd
    · have hkj := (List.Nodup.getElem_inj_iff hfst_nodup).mp
        (show (p.darts.map (·.fst))[k]'(by simpa using hk) = (p.darts.map (·.fst))[(i + 1) % p.darts.length]'(by simpa using hj_lt) by
          simp only [List.getElem_map]; rw [← hfst, hv_eq, hd_out_eq])
      subst hkj; exact .inl (rayEdge_inj _ (by rw [← hdt_eq, ← hd_out_eq, hv_eq, (dart_edge_eq_rayEdge d_out).1]))
    · have hki := (List.Nodup.getElem_inj_iff hsnd_nodup).mp
        (show (p.darts.map (·.snd))[k]'(by simpa using hk) = (p.darts.map (·.snd))[i]'(by simpa using hi) by
          simp only [List.getElem_map]; exact hsnd.symm)
      subst hki; exact .inr (rayEdge_inj _ (by rw [← hdt_eq, (dart_edge_eq_rayEdge d_in).2]))
  · rintro (rfl | rfl)
    · rw [hv_eq, ← (dart_edge_eq_rayEdge d_out).1, hd_out_eq]; exact List.mem_map_of_mem (List.getElem_mem hj_lt)
    · rw [← (dart_edge_eq_rayEdge d_in).2]; exact List.mem_map_of_mem (List.getElem_mem hi)

private lemma cycle_local_turning {u : V} (p : FK.squareLattice.Walk u u) (hp : p.IsCycle) :
    ∃ k : ℤ, (k = -1 ∨ k = 1) ∧
      squareWalkCyclicTurn p = k * ∑ v ∈ p.support.tail.toFinset, (2 - ((vertexSectors (fillSet p) v).card : ℤ)) := by
  have hlen3 : 3 ≤ p.darts.length := Walk.length_darts p ▸ hp.three_le_length
  let S := fillSet p
  let dSign (dt : FK.squareLattice.Dart) : ℤ := compassSectorBoundary (vertexSectors S dt.fst) (squareDartCompass dt)
  have hdSign_pm (dt) (hdt : dt ∈ p.darts) : dSign dt = -1 ∨ dSign dt = 1 := by
    have hz : (dSign dt : ZMod 2) = 1 := by
      dsimp [dSign]; rw [sector_boundary_zmod2, ← (dart_edge_eq_rayEdge dt).1, gridWalkInd_eq_ite p hp.edges_nodup]
      exact ite_eq_left (List.mem_map_of_mem hdt)
    rcases sector_boundary_vals (vertexSectors S dt.fst) (squareDartCompass dt) with h0 | h1 | hm1
    · exfalso; change dSign dt = 0 at h0; rw [h0] at hz; exact absurd hz (by decide)
    · exact .inr h1
    · exact .inl hm1
  have hstep_sign (i : ℕ) (hi : i < p.darts.length) :
      let d_in := p.darts[i]; let d_out := (p.darts.rotate 1)[i]'(by simpa using hi)
      dSign d_out = dSign d_in ∧
        primalCompassQuarterTurn (squareDartCompass d_in) (squareDartCompass d_out) =
          dSign d_in * (2 - ((vertexSectors S d_in.snd).card : ℤ)) := by
    intro d_in d_out
    obtain ⟨hv_eq, hab, hrays⟩ := cycle_dart_rays p hp i hi
    let Q := vertexSectors S d_in.snd
    let a := squareDartCompass d_in + 2; let b := squareDartCompass d_out
    have hzero_other (d : Fin 4) (hdb : d ≠ b) (hda : d ≠ a) : compassSectorBoundary Q d = 0 := by
      have hz := sector_boundary_zmod2 p d_in.snd d
      rw [gridWalkInd_eq_ite p hp.edges_nodup, ite_eq_right fun hm => (hrays d).mp hm |>.elim hdb hda] at hz
      rcases sector_boundary_vals Q d with h0 | h1 | hm1
      · exact h0
      · exfalso; change compassSectorBoundary Q d = 1 at h1; rw [h1] at hz; exact absurd hz (by decide)
      · exfalso; change compassSectorBoundary Q d = -1 at hm1; rw [hm1] at hz; exact absurd hz (by decide)
    have ha_val : compassSectorBoundary Q a = -dSign d_in := sector_boundary_opp S d_in
    have hb_val : compassSectorBoundary Q b = dSign d_out := by dsimp [Q, b, dSign]; rw [hv_eq]
    have hsum0 : ∑ d : Fin 4, compassSectorBoundary Q d = 0 := by
      rw [Fin.sum_univ_four]; unfold compassSectorBoundary
      change _ - (if (3 : Fin 4) ∈ Q then 1 else 0) + (_ - (if (0 : Fin 4) ∈ Q then 1 else 0)) +
        (_ - (if (1 : Fin 4) ∈ Q then 1 else 0)) + (_ - (if (2 : Fin 4) ∈ Q then 1 else 0)) = 0; ring
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩),
      Finset.sum_eq_zero fun d hd => by rw [Finset.mem_erase, Finset.mem_erase] at hd; exact hzero_other d hd.1 hd.2.1,
      add_zero, ha_val, hb_val] at hsum0
    have hds_eq : dSign d_out = dSign d_in := by linarith
    refine ⟨hds_eq, ?_⟩
    have hformula := primalCompassQuarterTurn_eq_sector_boundary_formula Q a b (dSign d_in) hab
      (hdSign_pm d_in (List.getElem_mem hi)) fun d => by
        by_cases hdb : d = b
        · subst hdb; rw [ite_eq_left rfl, hb_val, hds_eq]
        · rw [ite_eq_right hdb]; by_cases hda : d = a
          · subst hda; rw [ite_eq_left rfl, ha_val]
          · rw [ite_eq_right hda]; exact hzero_other d hdb hda
    rwa [show a + 2 = squareDartCompass d_in by dsimp [a]; generalize squareDartCompass d_in = x; fin_cases x <;> decide] at hformula
  let k := dSign (p.darts[0]'(by omega))
  have hall_k (i : ℕ) (hi : i < p.darts.length) : dSign p.darts[i] = k := by
    induction i with
    | zero => rfl
    | succ m ih =>
      have hm : m < p.darts.length := by omega
      have h1 := (hstep_sign m hm).1
      rw [show (p.darts.rotate 1)[m]'(by simpa using hm) = p.darts[m + 1] by
        rw [List.getElem_rotate]; simp only [Nat.mod_eq_of_lt hi]] at h1
      exact h1.trans (ih hm)
  refine ⟨k, hdSign_pm _ (List.getElem_mem (by omega)), ?_⟩
  unfold squareWalkCyclicTurn squareWalkCompassDirections; rw [← List.map_rotate]
  have hzip_eq : List.zipWith primalCompassQuarterTurn (p.darts.map squareDartCompass) ((p.darts.rotate 1).map squareDartCompass) =
      (p.darts.map (·.snd)).map (fun v => k * (2 - ((vertexSectors S v).card : ℤ))) :=
    List.ext_getElem (by simp) fun i _ hi2 => by
      have hi : i < p.darts.length := by simpa using hi2
      simp only [List.getElem_zipWith, List.getElem_map]; rw [(hstep_sign i hi).2, hall_k i hi]
  rw [hzip_eq, Walk.map_snd_darts, ← List.sum_toFinset _ hp.support_nodup, Finset.mul_sum]

private def sqVerts (s : V) : Finset V := {(s.1, s.2), (s.1 + 1, s.2), (s.1 + 1, s.2 + 1), (s.1, s.2 + 1)}
private def sqEdges (s : V) : Finset (Sym2 V) :=
  {gridHEdge s.1 s.2, gridHEdge s.1 (s.2 + 1), gridVEdge s.1 s.2, gridVEdge (s.1 + 1) s.2}

private def bdInd (A : Finset V) (e : Sym2 V) : ZMod 2 := ∑ s ∈ A, if e ∈ sqEdges s then 1 else 0

private lemma sum_ite_pair (A : Finset V) {a b : V} (hne : a ≠ b) {P : V → Prop} [DecidablePred P]
    (hiff : ∀ s, P s ↔ s = a ∨ s = b) :
    (∑ s ∈ A, if P s then (1 : ZMod 2) else 0) = (if a ∈ A then 1 else 0) + (if b ∈ A then 1 else 0) := by
  have hsp (s : V) : (if P s then (1 : ZMod 2) else 0) = (if s = a then 1 else 0) + (if s = b then 1 else 0) := by
    simp only [hiff s]; by_cases h1 : s = a <;> by_cases h2 : s = b <;> simp_all
  simp_rw [hsp]; rw [Finset.sum_add_distrib]; simp

private lemma vEdge_mem_sqEdges (x y : ℤ) (s : V) : gridVEdge x y ∈ sqEdges s ↔ s = (x, y) ∨ s = (x - 1, y) := by
  unfold sqEdges; simp only [Finset.mem_insert, Finset.mem_singleton, gridVEdge_ne_hEdge _ _ _ _, false_or]
  exact ⟨fun h => h.imp (fun h => by have := gridVEdge_inj h; ext <;> omega) (fun h => by have := gridVEdge_inj h; ext <;> omega),
    fun h => h.imp (fun h => by subst h; rfl) (fun h => by subst h; exact congrArg₂ gridVEdge (by omega) rfl)⟩

private lemma hEdge_mem_sqEdges (x y : ℤ) (s : V) : gridHEdge x y ∈ sqEdges s ↔ s = (x, y) ∨ s = (x, y - 1) := by
  unfold sqEdges; simp only [Finset.mem_insert, Finset.mem_singleton, (gridVEdge_ne_hEdge _ _ _ _).symm, or_false]
  exact ⟨fun h => h.imp (fun h => by have := gridHEdge_inj h; ext <;> omega) (fun h => by have := gridHEdge_inj h; ext <;> omega),
    fun h => h.imp (fun h => by subst h; rfl) (fun h => by subst h; exact congrArg₂ gridHEdge rfl (by omega))⟩

private lemma bdInd_vEdge (A : Finset V) (x y : ℤ) :
    bdInd A (gridVEdge x y) = (if (x, y) ∈ A then 1 else 0) + (if (x - 1, y) ∈ A then 1 else 0) :=
  sum_ite_pair A (by simp [Prod.ext_iff]; omega) (vEdge_mem_sqEdges x y)

private lemma bdInd_hEdge (A : Finset V) (x y : ℤ) :
    bdInd A (gridHEdge x y) = (if (x, y) ∈ A then 1 else 0) + (if (x, y - 1) ∈ A then 1 else 0) :=
  sum_ite_pair A (by simp [Prod.ext_iff]; omega) (hEdge_mem_sqEdges x y)

private def adjSq (a b : V) : Prop := (|a.1 - b.1| = 1 ∧ a.2 = b.2) ∨ (a.1 = b.1 ∧ |a.2 - b.2| = 1)

private lemma sqEdges_dual_pair {s₀ : V} {e : Sym2 V} (he : e ∈ sqEdges s₀) :
    ∃ b : V, adjSq s₀ b ∧ (∀ C : Finset V, bdInd C e = (if s₀ ∈ C then 1 else 0) + (if b ∈ C then 1 else 0)) ∧
      (∀ t : V, e ∈ sqEdges t ↔ t = s₀ ∨ t = b) := by
  unfold sqEdges at he; simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact ⟨(s₀.1, s₀.2 - 1), .inr ⟨rfl, by norm_num⟩, fun C => bdInd_hEdge C s₀.1 s₀.2, hEdge_mem_sqEdges s₀.1 s₀.2⟩
  · exact ⟨(s₀.1, s₀.2 + 1), .inr ⟨rfl, by rw [show s₀.2 - (s₀.2 + 1) = -1 by ring]; norm_num⟩,
      fun C => by simpa [add_comm] using bdInd_hEdge C s₀.1 (s₀.2 + 1),
      fun t => by simpa [or_comm] using hEdge_mem_sqEdges s₀.1 (s₀.2 + 1) t⟩
  · exact ⟨(s₀.1 - 1, s₀.2), .inl ⟨by norm_num, rfl⟩, fun C => bdInd_vEdge C s₀.1 s₀.2, vEdge_mem_sqEdges s₀.1 s₀.2⟩
  · exact ⟨(s₀.1 + 1, s₀.2), .inl ⟨by rw [show s₀.1 - (s₀.1 + 1) = -1 by ring]; norm_num, rfl⟩,
      fun C => by simpa [add_comm] using bdInd_vEdge C (s₀.1 + 1) s₀.2,
      fun t => by simpa [or_comm] using vEdge_mem_sqEdges (s₀.1 + 1) s₀.2 t⟩

private lemma vDeg_bdInd (A : Finset V) (z : V) : gridVDeg (bdInd A) z = 0 := by
  unfold gridVDeg; rw [Fin.sum_univ_four]; dsimp only [rayEdge]
  rw [bdInd_hEdge, bdInd_vEdge, bdInd_hEdge, bdInd_vEdge]
  generalize (if (z.1, z.2) ∈ A then (1 : ZMod 2) else 0) = s0
  generalize (if (z.1 - 1, z.2) ∈ A then (1 : ZMod 2) else 0) = s1
  generalize (if (z.1 - 1, z.2 - 1) ∈ A then (1 : ZMod 2) else 0) = s2
  generalize (if (z.1, z.2 - 1) ∈ A then (1 : ZMod 2) else 0) = s3
  revert s0 s1 s2 s3; decide

private lemma bdInd_inj {A B : Finset V} (h : bdInd A = bdInd B) : A = B := by
  ext ⟨x, y⟩
  let M : ℤ := ((A ∪ B).sup (fun s => s.1.natAbs) : ℕ) + 1
  have hleft : ∀ s ∈ A ∪ B, -M < s.1 := fun s hs => by
    have := Finset.le_sup (f := fun t : V => t.1.natAbs) hs; dsimp [M]; omega
  have hind (n : ℕ) : (if (-M + n, y) ∈ A then (1 : ZMod 2) else 0) = if (-M + n, y) ∈ B then 1 else 0 := by
    induction n with
    | zero =>
      simp [show (-M, y) ∉ A from fun hm => by have := hleft _ (Finset.mem_union_left B hm); omega,
        show (-M, y) ∉ B from fun hm => by have := hleft _ (Finset.mem_union_right A hm); omega]
    | succ n ih =>
      have hv := congrFun h (gridVEdge (-M + ((n + 1 : ℕ) : ℤ)) y)
      rw [bdInd_vEdge, bdInd_vEdge, show -M + ((n + 1 : ℕ) : ℤ) - 1 = -M + (n : ℤ) by push_cast; ring, ih] at hv
      exact add_right_cancel hv
  by_cases hx : -M ≤ x
  · have := hind (x + M).toNat; rw [show -M + ((x + M).toNat : ℤ) = x by omega] at this
    by_cases hA : (x, y) ∈ A <;> by_cases hB : (x, y) ∈ B <;> simp_all
  · simp [show (x, y) ∉ A from fun hm => by have := hleft _ (Finset.mem_union_left B hm); omega,
      show (x, y) ∉ B from fun hm => by have := hleft _ (Finset.mem_union_right A hm); omega]

private lemma bdInd_fillSet {u : V} (p : FK.squareLattice.Walk u u) : bdInd (fillSet p) = gridWalkInd p := by
  funext e
  have hmem_z (s : V) : (if s ∈ fillSet p then (1 : ZMod 2) else 0) = insideZ p s.1 s.2 := by
    simp only [mem_fillSet]; rcases zmod2_cases (insideZ p s.1 s.2) with h | h <;> simp [h]
  by_cases hv : ∃ x y, e = gridVEdge x y
  · obtain ⟨x, y, rfl⟩ := hv; rw [bdInd_vEdge, hmem_z, hmem_z, insideZ_step_x]
  · by_cases hh : ∃ x y, e = gridHEdge x y
    · obtain ⟨x, y, rfl⟩ := hh; rw [bdInd_hEdge, hmem_z, hmem_z, insideZ_step_y]
    · rw [show bdInd (fillSet p) e = 0 from Finset.sum_eq_zero fun s _ => ite_eq_right fun hm => by
        unfold sqEdges at hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with rfl | rfl | rfl | rfl <;> [exact hh ⟨_, _, rfl⟩; exact hh ⟨_, _, rfl⟩; exact hv ⟨_, _, rfl⟩; exact hv ⟨_, _, rfl⟩],
        gridWalkInd_eq_zero_of_not_mem p fun hm => by
          obtain ⟨dt, _, rfl⟩ := List.mem_map.mp hm
          rcases adj_edge_cases dt.adj with ⟨x, y, he⟩ | ⟨x, y, he⟩ <;> [exact hv ⟨x, y, he⟩; exact hh ⟨x, y, he⟩]]

private lemma eq_empty_or_fillSet {u : V} {p : FK.squareLattice.Walk u u} (hp : p.IsCycle)
    (A : Finset V) (hsupp : ∀ e, bdInd A e ≠ 0 → bdInd (fillSet p) e ≠ 0) :
    A = ∅ ∨ A = fillSet p := by
  have hlen3 : 3 ≤ p.darts.length := Walk.length_darts p ▸ hp.three_le_length
  have hsupp_p (e) (hne : bdInd A e ≠ 0) : e ∈ p.edges := by
    have h1 := hsupp e hne; rw [bdInd_fillSet, gridWalkInd_eq_ite p hp.edges_nodup] at h1
    by_contra hnot; exact h1 (ite_eq_right hnot)
  have hstep (i : ℕ) (hi : i < p.darts.length) :
      bdInd A ((p.darts.rotate 1)[i]'(by simpa using hi)).edge = bdInd A p.darts[i].edge := by
    obtain ⟨hv_eq, hab, hrays⟩ := cycle_dart_rays p hp i hi
    let d_in := p.darts[i]; let d_out := (p.darts.rotate 1)[i]'(by simpa using hi)
    let v := d_in.snd; let a := squareDartCompass d_in + 2; let b := squareDartCompass d_out
    have hsum : ∑ d : Fin 4, bdInd A (rayEdge v d) = 0 := vDeg_bdInd A v
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩),
      Finset.sum_eq_zero fun d hd => by
        rw [Finset.mem_erase, Finset.mem_erase] at hd
        by_contra hne; exact (hrays d).mp (hsupp_p _ hne) |>.elim hd.1 hd.2.1,
      add_zero, (dart_edge_eq_rayEdge d_in).2.symm,
      show rayEdge v b = d_out.edge by dsimp [v, b]; rw [hv_eq]; exact (dart_edge_eq_rayEdge d_out).1.symm] at hsum
    generalize bdInd A d_in.edge = x at hsum ⊢; generalize bdInd A d_out.edge = y at hsum ⊢; revert x y hsum; decide
  have hall (i : ℕ) (hi : i < p.darts.length) : bdInd A p.darts[i].edge = bdInd A (p.darts[0]'(by omega)).edge := by
    induction i with
    | zero => rfl
    | succ m ih =>
      have hm : m < p.darts.length := by omega
      have h1 := hstep m hm
      rw [show (p.darts.rotate 1)[m]'(by simpa using hm) = p.darts[m + 1] by
        rw [List.getElem_rotate]; simp only [Nat.mod_eq_of_lt hi]] at h1
      exact h1.trans (ih hm)
  rcases zmod2_cases (bdInd A (p.darts[0]'(by omega)).edge) with h0 | h1
  · refine .inl (bdInd_inj (funext fun e => ?_))
    rw [show bdInd ∅ e = 0 by simp [bdInd]]
    by_cases he : e ∈ p.edges
    · obtain ⟨dt, hdt, rfl⟩ := List.mem_map.mp he; obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hdt; exact (hall i hi).trans h0
    · by_contra hne; exact he (hsupp_p e hne)
  · refine .inr (bdInd_inj (funext fun e => ?_))
    rw [bdInd_fillSet, gridWalkInd_eq_ite p hp.edges_nodup]
    by_cases he : e ∈ p.edges
    · rw [ite_eq_left he]; obtain ⟨dt, hdt, rfl⟩ := List.mem_map.mp he; obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hdt; exact (hall i hi).trans h1
    · rw [ite_eq_right he]; by_contra hne; exact he (hsupp_p e hne)

private def C_V (S : Finset V) : Finset V := S.biUnion sqVerts
private def E_S (S : Finset V) : Finset (Sym2 V) := S.biUnion sqEdges
private def P_S (S : Finset V) : Finset (Sym2 V) := S.image fun s => gridHEdge s.1 (s.2 + 1)
private def U_G (S : Finset V) : SimpleGraph V := SimpleGraph.fromEdgeSet (E_S S : Set (Sym2 V))
private def R_G (S : Finset V) : SimpleGraph V := SimpleGraph.fromEdgeSet ((E_S S \ P_S S : Finset (Sym2 V)) : Set (Sym2 V))

private lemma sqEdges_subset_squareLattice (s : V) {e : Sym2 V} (he : e ∈ sqEdges s) :
    e ∈ FK.squareLattice.edgeSet ∧ ∀ v ∈ e, v ∈ sqVerts s := by
  unfold sqEdges at he; simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl <;>
    refine ⟨FK.squareLattice.mem_edgeSet.mpr (by rw [FK.squareLattice_adj_iff]; omega), fun v hv => ?_⟩ <;>
    (simp only [gridHEdge, gridVEdge, Sym2.mem_iff] at hv; rcases hv with rfl | rfl <;> simp [sqVerts])

private lemma sq_corners_U_reachable {S : Finset V} {s : V} (hs : s ∈ S) {v : V} (hv : v ∈ sqVerts s) :
    (U_G S).Reachable (s.1, s.2) v := by
  have hadj (e) (he : e ∈ sqEdges s) (a b : V) (hab : e = s(a, b)) (hne : a ≠ b) : (U_G S).Adj a b :=
    (SimpleGraph.fromEdgeSet_adj _).mpr ⟨hab ▸ Finset.mem_biUnion.mpr ⟨s, hs, he⟩, hne⟩
  have h1 := hadj (gridHEdge s.1 s.2) (by simp [sqEdges]) _ _ rfl (by simp [Prod.ext_iff])
  have h2 := hadj (gridVEdge s.1 s.2) (by simp [sqEdges]) _ _ rfl (by simp [Prod.ext_iff])
  have h3 := hadj (gridHEdge s.1 (s.2 + 1)) (by simp [sqEdges]) _ _ rfl (by simp [Prod.ext_iff])
  unfold sqVerts at hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact .refl _
  · exact h1.reachable
  · exact h2.reachable.trans h3.reachable
  · exact h2.reachable

private lemma U_G_connected_on_C {u : V} (p : FK.squareLattice.Walk u u) (hp : p.IsCycle) :
    ∀ v₁ ∈ C_V (fillSet p), ∀ v₂ ∈ C_V (fillSet p), (U_G (fillSet p)).Reachable v₁ v₂ := by
  classical
  set S := fillSet p
  obtain ⟨s₀, hs₀⟩ := fillSet_nonempty p hp
  let S₀ := S.filter fun s => (U_G S).Reachable (s₀.1, s₀.2) (s.1, s.2)
  have hs₀_mem : s₀ ∈ S₀ := Finset.mem_filter.mpr ⟨hs₀, .refl _⟩
  have hEq : S₀ = S := by
    refine (eq_empty_or_fillSet hp S₀ fun e hne => ?_).resolve_left (Finset.Nonempty.ne_empty ⟨s₀, hs₀_mem⟩)
    obtain ⟨s₁, hs₁, he₁⟩ : ∃ s₁ ∈ S₀, e ∈ sqEdges s₁ := by
      by_contra hall; exact hne (Finset.sum_eq_zero fun s hs => ite_eq_right fun hm => hall ⟨s, hs, hm⟩)
    obtain ⟨b, _, hbd, hmem⟩ := sqEdges_dual_pair he₁
    have hbnS : b ∉ S := fun hbS => by
      obtain ⟨w, hw⟩ : ∃ w, w ∈ e := by induction e using Sym2.ind with | _ a _ => exact ⟨a, by simp⟩
      have hb0 : b ∈ S₀ := Finset.mem_filter.mpr ⟨hbS, (Finset.mem_filter.mp hs₁).2.trans
        ((sq_corners_U_reachable (Finset.mem_filter.mp hs₁).1 ((sqEdges_subset_squareLattice s₁ he₁).2 w hw)).trans
          (sq_corners_U_reachable hbS ((sqEdges_subset_squareLattice b ((hmem b).mpr (.inr rfl))).2 w hw)).symm)⟩
      rw [hbd S₀, ite_eq_left hs₁, ite_eq_left hb0, grid_zmod2_two] at hne; exact hne rfl
    rw [hbd S, ite_eq_left (Finset.mem_filter.mp hs₁).1, ite_eq_right hbnS, add_zero]; decide
  intro v₁ hv₁ v₂ hv₂
  obtain ⟨s₁, hs₁, hv₁s⟩ := Finset.mem_biUnion.mp hv₁
  obtain ⟨s₂, hs₂, hv₂s⟩ := Finset.mem_biUnion.mp hv₂
  exact ((Finset.mem_filter.mp (hEq.symm ▸ hs₁)).2.trans (sq_corners_U_reachable hs₁ hv₁s)).symm.trans
    ((Finset.mem_filter.mp (hEq.symm ▸ hs₂)).2.trans (sq_corners_U_reachable hs₂ hv₂s))

private lemma R_G_induce_connected {u : V} (p : FK.squareLattice.Walk u u) (hp : p.IsCycle) :
    ((R_G (fillSet p)).induce (C_V (fillSet p) : Set V)).Connected := by
  set S := fillSet p
  have htop : ∀ n : ℕ, ∀ s ∈ S, (s.2 + walkBound p).toNat = n →
      (R_G S).Reachable (s.1, s.2 + 1) (s.1 + 1, s.2 + 1) := fun n => by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro s hs hn
      have hadjR (e) (he : e ∈ E_S S) (hnp : e ∉ P_S S) (a b : V) (hab : e = s(a, b)) (hne : a ≠ b) : (R_G S).Adj a b :=
        (SimpleGraph.fromEdgeSet_adj _).mpr ⟨hab ▸ Finset.mem_sdiff.mpr ⟨he, hnp⟩, hne⟩
      have hvL := hadjR (gridVEdge s.1 s.2) (Finset.mem_biUnion.mpr ⟨s, hs, by simp [sqEdges]⟩)
        (by simp only [P_S, Finset.mem_image]; rintro ⟨t, _, ht⟩; exact gridVEdge_ne_hEdge _ _ _ _ ht.symm)
        _ _ Sym2.eq_swap (by simp [Prod.ext_iff])
      have hvR := hadjR (gridVEdge (s.1 + 1) s.2) (Finset.mem_biUnion.mpr ⟨s, hs, by simp [sqEdges]⟩)
        (by simp only [P_S, Finset.mem_image]; rintro ⟨t, _, ht⟩; exact gridVEdge_ne_hEdge _ _ _ _ ht.symm)
        _ _ rfl (by simp [Prod.ext_iff])
      by_cases hbelow : (s.1, s.2 - 1) ∈ S
      · have := fillSet_bounds p hbelow
        have hmid := ih (s.2 - 1 + walkBound p).toNat (by omega) (s.1, s.2 - 1) hbelow rfl
        simp only [sub_add_cancel] at hmid
        exact hvL.reachable.trans (hmid.trans hvR.reachable)
      · exact hvL.reachable.trans ((hadjR (gridHEdge s.1 s.2) (Finset.mem_biUnion.mpr ⟨s, hs, by simp [sqEdges]⟩)
          (by simp only [P_S, Finset.mem_image]; rintro ⟨t, ht, heq⟩; have := gridHEdge_inj heq
              exact hbelow (by convert ht using 1; ext <;> omega)) _ _ rfl (by simp [Prod.ext_iff])).reachable.trans hvR.reachable)
  have hreach (a b : V) (hab : (U_G S).Reachable a b) : (R_G S).Reachable a b := by
    obtain ⟨w⟩ := hab
    induction w with
    | nil => exact .refl _
    | @cons b c _ habj _ ih =>
      refine Reachable.trans ?_ ih
      obtain ⟨he, hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp habj
      by_cases hpiv : s(b, c) ∈ P_S S
      · obtain ⟨t, ht, hteq⟩ := Finset.mem_image.mp hpiv
        have htr := htop _ t ht rfl
        rw [gridHEdge, Sym2.eq_iff] at hteq
        rcases hteq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact htr; exact htr.symm
      · exact Adj.reachable ((SimpleGraph.fromEdgeSet_adj _).mpr ⟨Finset.mem_sdiff.mpr ⟨he, hpiv⟩, hne⟩)
  obtain ⟨s₀, hs₀⟩ := fillSet_nonempty p hp
  have : Nonempty (C_V S : Set V) := ⟨⟨(s₀.1, s₀.2), Finset.mem_biUnion.mpr ⟨s₀, hs₀, by simp [sqVerts]⟩⟩⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨w⟩ := hreach x.1 y.1 (U_G_connected_on_C p hp x.1 x.2 y.1 y.2)
  have hmem : ∀ {a b : V} (w' : (R_G S).Walk a b), a ∈ C_V S → ∀ z ∈ w'.support, z ∈ (C_V S : Set V) := by
    intro a b w' ha; induction w' with
    | nil => intro z hz; simp at hz; subst hz; exact ha
    | @cons a c _ hadj _ ih =>
      obtain ⟨s, hs, hes⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp ((SimpleGraph.fromEdgeSet_adj _).mp hadj).1).1
      intro z hz; rcases List.mem_cons.mp hz with rfl | hz
      · exact ha
      · exact ih (Finset.mem_biUnion.mpr ⟨s, hs, (sqEdges_subset_squareLattice s hes).2 c (Sym2.mem_mk_right _ _)⟩) z hz
  exact ⟨w.induce _ (hmem w x.2)⟩

private lemma filling_subset_of_edges_subset {u w : V}
    (p : FK.squareLattice.Walk u u) (hp : p.IsCycle)
    (q : FK.squareLattice.Walk w w) (hq : q.IsCycle)
    (hsub : ∀ e ∈ q.edges, e ∈ E_S (fillSet p)) :
    fillSet q ⊆ fillSet p := by
  classical
  set S := fillSet p; set T := fillSet q
  let M : ℤ := max (walkBound p) (walkBound q) + 1
  let Box : Finset V := Finset.Icc (-M) M ×ˢ Finset.Icc (-M) M
  let adjB (a b : V) : Prop := a ∈ Box \ S ∧ b ∈ Box \ S ∧ adjSq a b
  let isFrame (b : V) : Prop := b.1 = -M ∨ b.1 = M ∨ b.2 = -M ∨ b.2 = M
  let H_hole := (Box \ S).filter fun s => ¬ ∃ b, isFrame b ∧ Relation.ReflTransGen adjB s b
  have hH_empty : H_hole = ∅ := by
    by_contra hne
    obtain ⟨s₀, hs₀⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hdisj : Disjoint H_hole S := Finset.disjoint_left.mpr fun s hsH =>
      (Finset.mem_sdiff.mp (Finset.mem_filter.mp hsH).1).2
    rcases eq_empty_or_fillSet hp H_hole (fun e hne_e => by
      obtain ⟨s₁, hs₁, he₁⟩ : ∃ s₁ ∈ H_hole, e ∈ sqEdges s₁ := by
        by_contra hall; exact hne_e (Finset.sum_eq_zero fun s hs => ite_eq_right fun hm => hall ⟨s, hs, hm⟩)
      obtain ⟨b, hadj, hbd, _⟩ := sqEdges_dual_pair he₁
      have hbnH : b ∉ H_hole := fun hbH => by
        rw [hbd H_hole, ite_eq_left hs₁, ite_eq_left hbH, grid_zmod2_two] at hne_e; exact hne_e rfl
      have hbS : b ∈ S := by
        by_contra hbnS
        obtain ⟨hs₁B, hnR⟩ := Finset.mem_filter.mp hs₁
        have hs₁Box := (Finset.mem_sdiff.mp hs₁B).1
        rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hs₁Box
        have hint : -M < s₁.1 ∧ s₁.1 < M ∧ -M < s₁.2 ∧ s₁.2 < M := by
          by_contra hbnd; exact hnR ⟨s₁, by dsimp [isFrame]; omega, .refl⟩
        have hbBox : b ∈ Box := by
          rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
          rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
            [have := (abs_eq (by norm_num)).mp h1; have := (abs_eq (by norm_num)).mp h2] <;> omega
        have hbBS := Finset.mem_sdiff.mpr ⟨hbBox, hbnS⟩
        obtain ⟨f, hffr, hrf⟩ : ∃ f, isFrame f ∧ Relation.ReflTransGen adjB b f := by
          by_contra hnr; exact hbnH (Finset.mem_filter.mpr ⟨hbBS, hnr⟩)
        exact hnR ⟨f, hffr, .head ⟨hs₁B, hbBS, hadj⟩ hrf⟩
      rw [hbd S, ite_eq_right (Finset.disjoint_left.mp hdisj hs₁), ite_eq_left hbS, zero_add]; decide) with h0 | hEq
    · exact hne h0
    · dsimp only [S] at hdisj; exact Finset.disjoint_left.mp hdisj hs₀ (hEq ▸ hs₀)
  have hadjB_T {a b : V} (hab : adjB a b) : a ∈ T ↔ b ∈ T := by
    obtain ⟨ha, hb, hstep⟩ := hab
    have ⟨e, hbd, hmem⟩ : ∃ e, (∀ C : Finset V, bdInd C e = (if a ∈ C then 1 else 0) + (if b ∈ C then 1 else 0)) ∧
        (∀ t : V, e ∈ sqEdges t ↔ t = a ∨ t = b) := by
      rcases hstep with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · rcases (abs_eq (by norm_num)).mp hx with hx1 | hx1
        · have hb' : b = (a.1 - 1, a.2) := by ext <;> omega
          exact ⟨gridVEdge a.1 a.2, fun C => by simpa [← hb'] using bdInd_vEdge C a.1 a.2,
            fun t => by simpa [← hb'] using vEdge_mem_sqEdges a.1 a.2 t⟩
        · have hb' : b = (a.1 + 1, a.2) := by ext <;> omega
          exact ⟨gridVEdge (a.1 + 1) a.2, fun C => by simpa [← hb', add_comm] using bdInd_vEdge C (a.1 + 1) a.2,
            fun t => by simpa [← hb', or_comm] using vEdge_mem_sqEdges (a.1 + 1) a.2 t⟩
      · rcases (abs_eq (by norm_num)).mp hy with hy1 | hy1
        · have hb' : b = (a.1, a.2 - 1) := by ext <;> omega
          exact ⟨gridHEdge a.1 a.2, fun C => by simpa [← hb'] using bdInd_hEdge C a.1 a.2,
            fun t => by simpa [← hb'] using hEdge_mem_sqEdges a.1 a.2 t⟩
        · have hb' : b = (a.1, a.2 + 1) := by ext <;> omega
          exact ⟨gridHEdge a.1 (a.2 + 1), fun C => by simpa [← hb', add_comm] using bdInd_hEdge C a.1 (a.2 + 1),
            fun t => by simpa [← hb', or_comm] using hEdge_mem_sqEdges a.1 (a.2 + 1) t⟩
    have hq0 : bdInd T e = 0 := by
      rw [bdInd_fillSet, gridWalkInd_eq_ite q hq.edges_nodup]
      refine ite_eq_right fun hm => ?_
      obtain ⟨s, hsS, hes⟩ := Finset.mem_biUnion.mp (hsub _ hm)
      exact (hmem s).mp hes |>.elim (fun h1 => (Finset.mem_sdiff.mp ha).2 (h1 ▸ hsS))
        (fun h2 => (Finset.mem_sdiff.mp hb).2 (h2 ▸ hsS))
    rw [hbd T] at hq0
    by_cases haT : a ∈ T <;> by_cases hbT : b ∈ T <;> simp only [haT, hbT, ite_true, ite_false] at hq0 ⊢ <;>
      exact absurd hq0 (by decide)
  intro t htT; by_contra htnS
  have htBox : t ∈ Box := by
    have := fillSet_bounds q htT; have : walkBound q ≤ M - 1 := by dsimp [M]; omega
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]; omega
  obtain ⟨b, hbfr, hreach⟩ : ∃ b, isFrame b ∧ Relation.ReflTransGen adjB t b := by
    by_contra hnr
    exact Finset.notMem_empty t (hH_empty ▸ Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨htBox, htnS⟩, hnr⟩)
  have hiff : ∀ {x y : V}, Relation.ReflTransGen adjB x y → (x ∈ T ↔ y ∈ T) := by
    intro x y h; induction h with | refl => exact .rfl | tail _ hst ih => exact ih.trans (hadjB_T hst)
  have := fillSet_bounds q ((hiff hreach).mp htT)
  have : walkBound q ≤ M - 1 := by dsimp [M]; omega
  dsimp [isFrame] at hbfr; omega

private lemma R_G_isAcyclic {u : V} (p : FK.squareLattice.Walk u u) (hp : p.IsCycle) :
    (R_G (fillSet p)).IsAcyclic := by
  set S := fillSet p
  have hR_le : R_G S ≤ FK.squareLattice := fun a b hab => by
    obtain ⟨s, _, hes⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp ((SimpleGraph.fromEdgeSet_adj _).mp hab).1).1
    exact FK.squareLattice.mem_edgeSet.mp (sqEdges_subset_squareLattice s hes).1
  intro w q hq
  let q' := q.mapLe hR_le; have hq' : q'.IsCycle := hq.mapLe hR_le
  have hq_edges (e) (he : e ∈ q'.edges) : e ∈ E_S S \ P_S S := by
    have hmem := q.edges_subset_edgeSet (by simpa [q'] using he)
    rw [R_G, SimpleGraph.edgeSet_fromEdgeSet] at hmem; exact hmem.1
  have hTS := filling_subset_of_edges_subset p hp q' hq' fun e he => (Finset.mem_sdiff.mp (hq_edges e he)).1
  obtain ⟨t, htT, htmax⟩ := Finset.exists_max_image (fillSet q') Prod.snd (fillSet_nonempty q' hq')
  have hbd1 : bdInd (fillSet q') (gridHEdge t.1 (t.2 + 1)) = 1 := by
    rw [bdInd_hEdge, ite_eq_right fun hm => by have := htmax _ hm; dsimp at this; omega,
      add_sub_cancel_right, ite_eq_left htT, zero_add]
  rw [bdInd_fillSet, gridWalkInd_eq_ite q' hq'.edges_nodup] at hbd1
  have hpiv_in_q : gridHEdge t.1 (t.2 + 1) ∈ q'.edges := by
    by_contra hnot; rw [ite_eq_right hnot] at hbd1; exact absurd hbd1 (by decide)
  exact (Finset.mem_sdiff.mp (hq_edges _ hpiv_in_q)).2 (Finset.mem_image.mpr ⟨t, hTS htT, rfl⟩)

private lemma sum_card_filter_biUnion {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (F : α → Finset β) :
    ∑ b ∈ S.biUnion F, (S.filter (b ∈ F ·)).card = ∑ s ∈ S, (F s).card := by
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s hs => by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr fun b hb => Finset.mem_biUnion.mpr ⟨s, hs, hb⟩,
      Finset.sum_const, smul_eq_mul, mul_one]

theorem squareWalkCyclicTurn_eq_four_or_neg_four {u : ℤ × ℤ}
    (p : FK.squareLattice.Walk u u) (hp : p.IsCycle) :
    squareWalkCyclicTurn p = 4 ∨ squareWalkCyclicTurn p = -4 := by
  classical
  set S := fillSet p; set C := C_V S; set E := E_S S; set P := P_S S
  let H := (R_G S).induce (C : Set V)
  have htree : H.IsTree := ⟨R_G_induce_connected p hp, (R_G_isAcyclic p hp).induce _⟩
  have htree_card : H.edgeFinset.card + 1 = C.card := by simpa [Fintype.card_coe] using htree.card_edgeFinset
  have hH_edges : H.edgeFinset.card = (E \ P).card :=
    Finset.card_bij (fun e _ => e.map Subtype.val)
      (fun e he => by rw [SimpleGraph.mem_edgeFinset] at he; induction e using Sym2.ind with | _ a b => exact ((SimpleGraph.fromEdgeSet_adj _).mp he).1)
      (fun _ _ _ _ h => Sym2.map.injective Subtype.val_injective h)
      fun e he => by
        obtain ⟨s, hs, hes⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp he).1
        obtain ⟨hesq, hvC⟩ := sqEdges_subset_squareLattice s hes
        induction e using Sym2.ind with | _ a b =>
          exact ⟨s(⟨a, Finset.mem_biUnion.mpr ⟨s, hs, hvC a (by simp)⟩⟩,
            ⟨b, Finset.mem_biUnion.mpr ⟨s, hs, hvC b (by simp)⟩⟩),
            SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.fromEdgeSet_adj _).mpr
              ⟨he, FK.squareLattice.ne_of_adj (FK.squareLattice.mem_edgeSet.mp hesq)⟩), rfl⟩
  have hP_sub : P ⊆ E := fun e he => by
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp he; exact Finset.mem_biUnion.mpr ⟨s, hs, by simp [sqEdges]⟩
  have hP_card : P.card = S.card :=
    Finset.card_image_of_injective S fun _ _ h => Prod.ext (gridHEdge_inj h).1 (by have := (gridHEdge_inj h).2; omega)
  have heuler : C.card + S.card = E.card + 1 := by have := Finset.card_sdiff_add_card_eq_card hP_sub; omega
  have hpE_sub : p.edges.toFinset ⊆ E := fun e he => by
    have hbd : bdInd S e = 1 := by rw [bdInd_fillSet, gridWalkInd_eq_ite p hp.edges_nodup, ite_eq_left (List.mem_toFinset.mp he)]
    by_contra hnE
    have h0 : bdInd S e = 0 := Finset.sum_eq_zero fun s hs => ite_eq_right fun hes => hnE (Finset.mem_biUnion.mpr ⟨s, hs, hes⟩)
    rw [h0] at hbd; exact absurd hbd (by decide)
  have hpE_card : p.edges.toFinset.card = p.length := by rw [List.toFinset_card_of_nodup hp.edges_nodup, Walk.length_edges]
  have sqVerts_card (s : V) : (sqVerts s).card = 4 := by
    unfold sqVerts
    rw [Finset.card_insert_of_notMem (by simp [Prod.ext_iff]), Finset.card_insert_of_notMem (by simp [Prod.ext_iff]),
      Finset.card_insert_of_notMem (by simp [Prod.ext_iff]), Finset.card_singleton]
  have sqEdges_card (s : V) : (sqEdges s).card = 4 := by
    unfold sqEdges
    rw [Finset.card_insert_of_notMem (by simp [(gridVEdge_ne_hEdge _ _ _ _).symm]; intro h; have := gridHEdge_inj h; omega),
      Finset.card_insert_of_notMem (by simp [(gridVEdge_ne_hEdge _ _ _ _).symm]),
      Finset.card_insert_of_notMem (by simp; intro h; have := gridVEdge_inj h; omega), Finset.card_singleton]
  have hedge_inc : 4 * S.card + p.length = 2 * E.card := by
    have h2 : ∑ e ∈ E, (S.filter (e ∈ sqEdges ·)).card = 4 * S.card := by
      dsimp only [E, E_S]; rw [sum_card_filter_biUnion]; simp [sqEdges_card, Nat.mul_comm]
    have hcard_e (e) (he : e ∈ E) : (S.filter (e ∈ sqEdges ·)).card = if e ∈ p.edges.toFinset then 1 else 2 := by
      obtain ⟨s₀, hs₀, hes₀⟩ := Finset.mem_biUnion.mp he
      obtain ⟨b, _, _, hmem⟩ := sqEdges_dual_pair hes₀
      have hpos : 0 < (S.filter (e ∈ sqEdges ·)).card := Finset.card_pos.mpr ⟨s₀, Finset.mem_filter.mpr ⟨hs₀, hes₀⟩⟩
      have hle2 : (S.filter (e ∈ sqEdges ·)).card ≤ 2 :=
        (Finset.card_le_card (t := insert s₀ {b}) fun t ht => by
          rcases (hmem t).mp (Finset.mem_filter.mp ht).2 with rfl | rfl <;> simp).trans (Finset.card_insert_le _ _)
      have hmod : ((S.filter (e ∈ sqEdges ·)).card : ZMod 2) = bdInd S e := by
        unfold bdInd; rw [Finset.card_eq_sum_ones, Finset.sum_filter]; push_cast; rfl
      rw [bdInd_fillSet, gridWalkInd_eq_ite p hp.edges_nodup] at hmod
      have h12 : (S.filter (e ∈ sqEdges ·)).card = 1 ∨ (S.filter (e ∈ sqEdges ·)).card = 2 := by omega
      by_cases hep : e ∈ p.edges <;> simp only [hep, List.mem_toFinset, ite_true, ite_false] at hmod ⊢ <;>
        (rcases h12 with h | h <;> first | exact h | (rw [h] at hmod; exact absurd hmod (by decide)))
    rw [Finset.sum_congr rfl hcard_e] at h2
    have hsplit_E : ∑ e ∈ E, (if e ∈ p.edges.toFinset then 1 else 2) + p.edges.toFinset.card = 2 * E.card := by
      rw [show p.edges.toFinset.card = ∑ e ∈ E, if e ∈ p.edges.toFinset then 1 else 0 by
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hpE_sub, Finset.sum_const, smul_eq_mul, mul_one],
        ← Finset.sum_add_distrib, Finset.sum_congr rfl fun e _ => (by split_ifs <;> rfl : _ + _ = 2),
        Finset.sum_const, smul_eq_mul, mul_comm]
    omega
  have hsector_iff (v s : V) : (∃ d : Fin 4, sectorSq v d = s) ↔ v ∈ sqVerts s := by
    refine ⟨fun ⟨d, hd⟩ => by subst hd; fin_cases d <;> simp [sectorSq, sqVerts], fun hv => ?_⟩
    unfold sqVerts at hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, by simp [sectorSq]⟩
    · exact ⟨2, by simp [sectorSq]⟩
    · exact ⟨3, by simp [sectorSq]⟩
  have hvert_card_eq (v : V) : (vertexSectors S v).card = (S.filter (v ∈ sqVerts ·)).card :=
    Finset.card_bij (fun d _ => sectorSq v d)
      (fun d hd => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hd).2, (hsector_iff v _).mp ⟨d, rfl⟩⟩)
      (fun d₁ _ d₂ _ h => by fin_cases d₁ <;> fin_cases d₂ <;> first | rfl | (exfalso; simp only [sectorSq, Prod.ext_iff] at h; omega))
      fun s hs => by
        obtain ⟨d, rfl⟩ := (hsector_iff v s).mpr (Finset.mem_filter.mp hs).2
        exact ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ d, (Finset.mem_filter.mp hs).1⟩, rfl⟩
  have hvert_inc : ∑ v ∈ C, (vertexSectors S v).card = 4 * S.card := by
    simp_rw [hvert_card_eq]; dsimp only [C, C_V]; rw [sum_card_filter_biUnion]; simp [sqVerts_card, Nat.mul_comm]
  let P_V := p.support.tail.toFinset
  have hPV_sub : P_V ⊆ C := fun v hv => by
    obtain ⟨dt, hdt, rfl⟩ := List.mem_map.mp (Walk.map_snd_darts p ▸ List.mem_toFinset.mp hv)
    obtain ⟨s, hs, hes⟩ := Finset.mem_biUnion.mp (hpE_sub (List.mem_toFinset.mpr (List.mem_map_of_mem hdt)))
    exact Finset.mem_biUnion.mpr ⟨s, hs, (sqEdges_subset_squareLattice s hes).2 dt.snd (by simp [Dart.edge])⟩
  have hPV_card : P_V.card = p.length := by
    rw [List.toFinset_card_of_nodup hp.support_nodup, ← Walk.map_snd_darts, List.length_map, Walk.length_darts]
  have hint_four (v) (hv : v ∈ C \ P_V) : (vertexSectors S v).card = 4 := by
    obtain ⟨hvC, hvnP⟩ := Finset.mem_sdiff.mp hv
    have hvnSupp : v ∉ p.support := fun hsupp => by
      cases p with
      | nil => exact hp.ne_nil rfl
      | cons _ rest =>
        rcases List.mem_cons.mp hsupp with rfl | htail
        · exact hvnP (List.mem_toFinset.mpr (Walk.end_mem_support rest))
        · exact hvnP (List.mem_toFinset.mpr htail)
    have hbd0 (d : Fin 4) : compassSectorBoundary (vertexSectors S v) d = 0 := by
      have hne_p : rayEdge v d ∉ p.edges := fun hm => by
        obtain ⟨dt, hdt, hdt_eq⟩ := List.mem_map.mp hm
        rcases Sym2.mem_iff.mp (hdt_eq ▸ rayEdge_mem_self v d) with rfl | rfl
        · exact hvnSupp (Walk.dart_fst_mem_support_of_mem_darts p hdt)
        · exact hvnP (List.mem_toFinset.mpr (Walk.map_snd_darts p ▸ List.mem_map_of_mem hdt))
      have hz := sector_boundary_zmod2 p v d
      rw [gridWalkInd_eq_ite p hp.edges_nodup, ite_eq_right hne_p] at hz
      rcases sector_boundary_vals (vertexSectors S v) d with h0 | h1 | hm1
      · exact h0
      · exfalso; change compassSectorBoundary _ _ = 1 at h1; rw [h1] at hz; exact absurd hz (by decide)
      · exfalso; change compassSectorBoundary _ _ = -1 at hm1; rw [hm1] at hz; exact absurd hz (by decide)
    rcases compassSectorBoundary_zero_eq_empty_or_univ (vertexSectors S v) hbd0 with hemp | huniv
    · obtain ⟨s, hs, hvs⟩ := Finset.mem_biUnion.mp hvC
      obtain ⟨d, hd⟩ := (hsector_iff v s).mpr hvs
      exact absurd (hemp ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ d, hd.symm ▸ hs⟩) (Finset.notMem_empty d)
    · rw [huniv]; rfl
  have hsum_split : ∑ v ∈ P_V, (vertexSectors S v).card + 4 * (C.card - P_V.card) = 4 * S.card := by
    rw [← hvert_inc, ← Finset.sum_sdiff hPV_sub, Finset.sum_congr rfl hint_four,
      Finset.sum_const, smul_eq_mul, Finset.card_sdiff, Finset.inter_eq_left.mpr hPV_sub, mul_comm, add_comm]
  have hPV_le_C : P_V.card ≤ C.card := Finset.card_le_card hPV_sub
  have hdefect : ∑ v ∈ P_V, (2 - ((vertexSectors S v).card : ℤ)) = 4 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Nat.cast_sum]; omega
  obtain ⟨k, hk, hturn⟩ := cycle_local_turning p hp
  rw [hturn, show p.support.tail.toFinset = P_V from rfl, hdefect]
  rcases hk with rfl | rfl <;> simp

end PottsDiscontinuity.TorusTopology
