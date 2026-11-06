module

public import Chazelle.Core.SpecMerge
public import Mathlib.Data.List.GetD

/-!
# Down phase, math (M-M1): junctions at padded vertices are generic

The merges of the down phase run on chains of the host polygon `R*` of a region
(design `docs/design-downphase-driver.md` §4.2 (e)).  The junction vertices are placed by the
padding rule M2: the shared vertex is a vertex of `Q` whose two host neighbours are vertices of
`Q` (in practice: an inner point of a run item of the host, so the three are consecutive vertices
of `Q`).  With distinct heights this gives `SharedGeneric` (M-M1).

* `host_poly_n`, `host_poly_vtx`: the vertices of `H.poly Q` are the evaluated host points;
* `pts_append_run`: the host points of a run item inside a host;
* **`sharedGeneric_of_vtx`** (M-M1): host points `.vtx a`, `.vtx b`, `.vtx c` with distinct
  indices at the three junction positions give `SharedGeneric J`;
* **`sharedGeneric_run`** (M-M1, run form): a shared vertex strictly inside a run item.
-/

namespace Chazelle.Core

namespace DownMath

@[expose] public section

open Merge (Junction)

/-! ## Host polygons -/

theorem host_poly_n (Q : Polygon) (H : Host) : (H.poly Q).n = (H.pts Q.n).length := by
  simp [Host.poly, Polygon.n]

/-- The vertices of the host polygon are the evaluated host points. -/
theorem host_poly_vtx (Q : Polygon) (H : Host) {i : ℕ} (hi : i < (H.pts Q.n).length) :
    (H.poly Q).vtx i = ((H.pts Q.n).getD i (.vtx 0)).eval Q := by
  unfold Host.poly Polygon.vtx
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    List.getD_eq_getElem _ _ hi]

theorem pts_append (n : ℕ) (H₁ H₂ : Host) : (H₁ ++ H₂).pts n = H₁.pts n ++ H₂.pts n := by
  simp [Host.pts]

theorem pts_cons (n : ℕ) (it : HostItem) (H : Host) :
    Host.pts n (it :: H) = it.pts n ++ H.pts n := by
  simp [Host.pts]

theorem run_pts_length (n a ℓ : ℕ) : ((HostItem.run a ℓ).pts n).length = ℓ + 1 := by
  simp [HostItem.pts]

theorem run_pts_getD (n a ℓ : ℕ) {k : ℕ} (hk : k ≤ ℓ) :
    ((HostItem.run a ℓ).pts n).getD k (.vtx 0) = .vtx ((a + k) % n) := by
  simp only [HostItem.pts]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]

/-- **The points of a run item inside a host.** -/
theorem pts_append_run (n : ℕ) (H₁ H₂ : Host) (a ℓ : ℕ) {k : ℕ} (hk : k ≤ ℓ) :
    ((H₁ ++ HostItem.run a ℓ :: H₂).pts n).getD ((H₁.pts n).length + k) (.vtx 0) =
      .vtx ((a + k) % n) := by
  rw [pts_append, pts_cons, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left, List.getElem?_append_left (by rw [run_pts_length]; omega),
    ← List.getD_eq_getElem?_getD, run_pts_getD n a ℓ hk]

theorem pts_append_run_length (n : ℕ) (H₁ H₂ : Host) (a ℓ : ℕ) :
    (H₁.pts n).length + ℓ + 1 ≤ ((H₁ ++ HostItem.run a ℓ :: H₂).pts n).length := by
  rw [pts_append, pts_cons, List.length_append, List.length_append, run_pts_length]
  omega

/-! ## M-M1 -/

/-- The vertex `k` of a chain of a host polygon is the evaluated host point at index
`(s + k) mod N`. -/
theorem chain_vertex_host {Q : Polygon} {H : Host} {C : Chain} (hP : C.P = H.poly Q) (k : ℕ) :
    C.vertex k = ((H.pts Q.n).getD ((C.s + k) % (H.pts Q.n).length) (.vtx 0)).eval Q := by
  have hn := C.n_pos
  rw [hP, host_poly_n] at hn
  unfold Chain.vertex Chain.edgeIdx
  rw [hP, host_poly_n, host_poly_vtx Q H (Nat.mod_lt _ hn)]

/-- **M-M1.**  If the host points at the three junction positions (the shared vertex of `J` and
its two neighbours) are vertices of `Q` with pairwise distinct indices, distinct heights give
`SharedGeneric J`. -/
theorem sharedGeneric_of_vtx {Q : Polygon} (hdh : DistinctHeights Q) {H : Host} {J : Junction}
    (hP : J.P = H.poly Q) {a b c : ℕ} (ha : a < Q.n) (hb : b < Q.n) (hc : c < Q.n)
    (hab : a ≠ b) (hcb : c ≠ b) (hac : a ≠ c)
    (hu : (H.pts Q.n).getD ((J.s + (J.m₁ - 1)) % (H.pts Q.n).length) (.vtx 0) = .vtx a)
    (hv : (H.pts Q.n).getD ((J.s + J.m₁) % (H.pts Q.n).length) (.vtx 0) = .vtx b)
    (hw : (H.pts Q.n).getD ((J.s + (J.m₁ + 1)) % (H.pts Q.n).length) (.vtx 0) = .vtx c) :
    SharedGeneric J := by
  have hP' : J.whole.P = H.poly Q := hP
  have eU : sharedU J = Q.vtx a := by
    unfold sharedU; rw [chain_vertex_host hP', show J.whole.s = J.s from rfl, hu]; rfl
  have eV : sharedV J = Q.vtx b := by
    unfold sharedV; rw [chain_vertex_host hP', show J.whole.s = J.s from rfl, hv]; rfl
  have eW : sharedW J = Q.vtx c := by
    unfold sharedW; rw [chain_vertex_host hP', show J.whole.s = J.s from rfl, hw]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [eU, eV]; exact hdh a b ha hb hab
  · rw [eW, eV]; exact hdh c b hc hb hcb
  · rw [eU, eW]; exact hdh a c ha hc hac

/-- Small distinct offsets give distinct residues. -/
theorem add_mod_ne {n x i j : ℕ} (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    (x + i) % n ≠ (x + j) % n := by
  intro h
  have h' : i % n = j % n := Nat.ModEq.add_left_cancel' x h
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h'
  exact hij h'

/-- `(x + 1) mod N = j ≥ 1` gives `x mod N = j - 1`. -/
theorem mod_pred {x N j : ℕ} (hN : 0 < N) (h : (x + 1) % N = j) (hj : 1 ≤ j) :
    x % N = j - 1 := by
  rw [Nat.add_mod] at h
  have hlt := Nat.mod_lt x hN
  rcases Nat.lt_or_ge 1 N with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at h
    rcases Nat.lt_or_ge (x % N + 1) N with h2 | h2
    · rw [Nat.mod_eq_of_lt h2] at h; omega
    · rw [show x % N + 1 = N by omega, Nat.mod_self] at h; omega
  · have : N = 1 := by omega
    subst this
    simp at h; omega

/-- `x mod N = j` with `j + 1 < N` gives `(x + 1) mod N = j + 1`. -/
theorem mod_succ {x N j : ℕ} (h : x % N = j) (hj : j + 1 < N) : (x + 1) % N = j + 1 := by
  rw [Nat.add_mod, h, Nat.mod_eq_of_lt (show 1 < N by omega), Nat.mod_eq_of_lt hj]

/-- **M-M1, run form (padding rule M2).**  If the host is `H₁ ++ run a ℓ :: H₂` and the shared
vertex of `J` is the host point `k` of the run with `1 ≤ k < ℓ` (so both host neighbours are
points of the same run, i.e. three consecutive vertices of `Q`), then `SharedGeneric J`. -/
theorem sharedGeneric_run {Q : Polygon} (hn : 3 ≤ Q.n) (hdh : DistinctHeights Q)
    {H₁ H₂ : Host} {a ℓ k : ℕ} {J : Junction} (hP : J.P = (H₁ ++ HostItem.run a ℓ :: H₂).poly Q)
    (hk1 : 1 ≤ k) (hkl : k < ℓ)
    (hj : (J.s + J.m₁) % J.P.n = (H₁.pts Q.n).length + k) : SharedGeneric J := by
  set H := H₁ ++ HostItem.run a ℓ :: H₂
  set N := (H.pts Q.n).length
  have hPn : J.P.n = N := by rw [hP, host_poly_n]
  rw [hPn] at hj
  have hlen : (H₁.pts Q.n).length + ℓ + 1 ≤ N := pts_append_run_length Q.n H₁ H₂ a ℓ
  have hm1 := J.one_le_m₁
  have hu : (J.s + (J.m₁ - 1)) % N = (H₁.pts Q.n).length + (k - 1) := by
    have e : J.s + J.m₁ = (J.s + (J.m₁ - 1)) + 1 := by omega
    rw [e] at hj
    rw [mod_pred (by omega) hj (by omega)]; omega
  have hw : (J.s + (J.m₁ + 1)) % N = (H₁.pts Q.n).length + (k + 1) := by
    rw [← add_assoc, mod_succ hj (by omega)]; omega
  have hv : (J.s + J.m₁) % N = (H₁.pts Q.n).length + k := hj
  have hn0 : 0 < Q.n := by omega
  have e1 : a + (k - 1) + 1 = a + k := by omega
  have e2 : a + (k - 1) + 2 = a + (k + 1) := by omega
  have d1 := add_mod_ne (x := a + (k - 1)) (show 0 < Q.n by omega) (show 1 < Q.n by omega)
    (by omega : (0 : ℕ) ≠ 1)
  have d2 := add_mod_ne (x := a + (k - 1)) (show 2 < Q.n by omega) (show 1 < Q.n by omega)
    (by omega : (2 : ℕ) ≠ 1)
  have d3 := add_mod_ne (x := a + (k - 1)) (show 0 < Q.n by omega) (show 2 < Q.n by omega)
    (by omega : (0 : ℕ) ≠ 2)
  rw [add_zero, e1] at d1
  rw [e1, e2] at d2
  rw [add_zero, e2] at d3
  refine sharedGeneric_of_vtx hdh hP (Nat.mod_lt _ hn0) (Nat.mod_lt _ hn0)
    (Nat.mod_lt _ hn0) d1 d2 d3 ?_ ?_ ?_
  · rw [hu]; exact pts_append_run Q.n H₁ H₂ a ℓ (by omega)
  · rw [hv]; exact pts_append_run Q.n H₁ H₂ a ℓ (by omega)
  · rw [hw]; exact pts_append_run Q.n H₁ H₂ a ℓ (by omega)

end

end DownMath

end Chazelle.Core
