module

public import RequestProject.OrderComplexSurface
public import RequestProject.SurfaceLabel

@[expose] public section

/-!
# The polygon with identified sides is a closed surface: the local conditions

`RequestProject/SurfacePoset.lean` builds the face poset `SCell vc ec hc` of a polygon with `M`
boundary positions whose sides are identified by the labellings `vc` and `ec`.  The nerve of the
block is the comparability graph of this poset, so the simplicial complex of the construction is
its order complex.

This file verifies, for that poset, the local conditions of a two-dimensional closed cell
structure (`FiniteChains.ASC.SurfaceRank`), under the hypotheses which say that the boundary
identification is the identification of the sides of a polygon:

* `FiniteChains.Davis.EdgePairs` — every edge of the surface comes from exactly two positions of
  the boundary of the polygon (the sides are glued in pairs);
* `FiniteChains.Davis.NoLoopSide` — no side of the polygon is a loop, i.e. the two endpoints of
  a side stay distinct after the identification;
* surjectivity of `vc` and `ec` — every vertex and every edge of the surface really occurs.

The result is `FiniteChains.Davis.surfaceRank_SCell`, and with it
`FiniteChains.Davis.edgeInTwoTriangles_SCell`: **every edge of the subdivision lies in exactly
two triangles**.  Connectedness of the vertex links — the condition which distinguishes a closed
surface from a pinched one — is treated in `RequestProject/SurfaceLink.lean`.
-/

namespace FiniteChains
namespace Davis

open Cell ASC

universe u

/-! ### Arithmetic of the boundary cycle -/

section FinAux

variable {M : ℕ} [NeZero M]

variable (p : Fin M)

/-- The predecessor in the cyclic group of boundary positions. -/
def fpred := p - 1

theorem fpred_val : (fpred p).val = if p.val = 0 then M - 1 else p.val - 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne M)
  split
  · next h => rw [show p = 0 from Fin.ext h, fpred, zero_sub, Fin.coe_neg_one]; rfl
  · next h => exact Fin.val_sub_one_of_ne_zero (fun he => h (congrArg Fin.val he))

theorem fpred_add_one : fpred p + 1 = p := sub_add_cancel _ _

theorem fpred_succ : fpred (p + 1) = p := add_sub_cancel_right _ _

theorem fin_succ_ne_self (hM : 2 ≤ M) (p : Fin M) : p + 1 ≠ p := by
  aesop

end FinAux

section Regular

variable {κ ι : Type u} {M : ℕ} [NeZero M] {vc : Fin M → κ} {ec : Fin M → ι}

/-- **The sides of the polygon are glued in pairs**: every edge of the surface comes from
exactly two positions of the boundary. -/
def EdgePairs (ec : Fin M → ι) :=
  ∀ i : Fin M, ∃ j : Fin M, j ≠ i ∧ ec j = ec i ∧ ∀ k : Fin M, ec k = ec i → k = i ∨ k = j

/-- **No side of the polygon becomes a loop**: the two endpoints of a side stay distinct after
the identification. -/
def NoLoopSide (vc : Fin M → κ) := ∀ i : Fin M, vc i ≠ vc (i + 1)

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
    · solve_by_elim
    · exact h
  · intro h
    refine lt_of_le_of_ne (Or.inr h) ?_
    intro he
    have hxy : x = y := he
    simp_all [plt_irrefl]

/-! ### The faces of a cell -/

/-- The vertices of a boundary edge. -/
theorem lt_bed_iff {i : Fin M} {x : Cell κ ι M} :
    (toS vc ec hc x < toS vc ec hc (bed (ec i))) ↔ (x = vtx (vc i) ∨ x = vtx (vc (i + 1))) := by
  rw [lt_iff_plt]
  cases x with
  | vtx v =>
      simp only [Cell.vtx.injEq]
      constructor
      · rintro ⟨j, hj, hv⟩
        rcases hc j i hj with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hv with hv | hv <;> simp_all
      · rintro (rfl | rfl)
        · exact ⟨i, rfl, Or.inl rfl⟩
        · exact ⟨i, rfl, Or.inr rfl⟩
  | _ => simp [plt]

variable {p : Fin M} {x : Cell κ ι M}

/-- The vertices of a collar edge. -/
theorem lt_ced_iff :
    (toS vc ec hc x < toS vc ec hc (ced p)) ↔ (x = cvx p ∨ x = cvx (p + 1)) := by
  rw [lt_iff_plt]
  cases x <;> simp [plt]

/-- The vertices of the edge `dia p`. -/
theorem lt_dia_iff :
    (toS vc ec hc x < toS vc ec hc (dia p)) ↔ (x = vtx (vc p) ∨ x = cvx p) := by
  rw [lt_iff_plt]
  cases x <;> simp [plt, eq_comm]

/-- The vertices of the edge `gdi p`. -/
theorem lt_gdi_iff :
    (toS vc ec hc x < toS vc ec hc (gdi p)) ↔ (x = vtx (vc p) ∨ x = cvx (p + 1)) := by
  rw [lt_iff_plt]
  cases x <;> simp [plt, eq_comm]

/-- The vertices of a radius. -/
theorem lt_rad_iff :
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

variable {p : Fin M}

variable {y : Cell κ ι M}

/-- The faces through a collar edge. -/
theorem ced_lt_iff :
    (toS vc ec hc (ced p) < toS vc ec hc y) ↔ (y = tr2 p ∨ y = inn p) := by
  rw [lt_iff_plt]
  cases y <;> simp [plt, eq_comm]

/-- The faces through the edge `dia p`. -/
theorem dia_lt_iff :
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
theorem gdi_lt_iff :
    (toS vc ec hc (gdi p) < toS vc ec hc y) ↔ (y = tr1 p ∨ y = tr2 p) := by
  rw [lt_iff_plt]
  cases y <;> simp [plt, eq_comm]

/-- The faces through a radius. -/
theorem rad_lt_iff :
    (toS vc ec hc (rad p) < toS vc ec hc y) ↔ (y = inn p ∨ y = inn (fpred p)) := by
  rw [lt_iff_plt]
  cases y with
  | inn s =>
      simp only [plt, Cell.inn.injEq]
      constructor
      · grind [fpred_succ]
      · grind [fpred_add_one]
  | _ => simp [plt]

variable {x : Cell κ ι M}

/-- The proper faces of an outer triangle. -/
theorem lt_tr1_iff :
    (toS vc ec hc x < toS vc ec hc (tr1 p)) ↔
      (x = bed (ec p) ∨ x = dia (p + 1) ∨ x = gdi p ∨
        x = vtx (vc p) ∨ x = vtx (vc (p + 1)) ∨ x = cvx (p + 1)) := by
  rw [lt_iff_plt]
  cases x <;> simp [plt, eq_comm]

/-- The proper faces of an inner triangle of the collar. -/
theorem lt_tr2_iff :
    (toS vc ec hc x < toS vc ec hc (tr2 p)) ↔
      (x = ced p ∨ x = dia p ∨ x = gdi p ∨
        x = vtx (vc p) ∨ x = cvx p ∨ x = cvx (p + 1)) := by
  rw [lt_iff_plt]
  cases x <;> simp [plt, eq_comm]

/-- The proper faces of a triangle of the fan. -/
theorem lt_inn_iff :
    (toS vc ec hc x < toS vc ec hc (inn p)) ↔
      (x = ced p ∨ x = rad p ∨ x = rad (p + 1) ∨
        x = ctr ∨ x = cvx p ∨ x = cvx (p + 1)) := by
  rw [lt_iff_plt]
  cases x <;> simp [plt, eq_comm]

/-! ### The local closed surface conditions -/

/-! ### The incidence counts -/

theorem toS_inj {x y : Cell κ ι M} (h : toS vc ec hc x = toS vc ec hc y) : x = y := h

theorem fpred_ne_self (hM : 2 ≤ M) (p : Fin M) : fpred p ≠ p := by
  grind [fpred_add_one, fin_succ_ne_self]

section

variable (hd : PolygonData vc ec)
include hd

/-- **Every edge of the surface has exactly two endpoints.** -/
theorem two_vertices_SCell :
    ∀ e : SCell vc ec hc, Cell.rk e = 1 → ExactlyTwo (fun v : SCell vc ec hc => v < e) := by
  have hM2 : 2 ≤ M := by have := hd.three_le; omega
  intro e he
  cases e with
  | bed e' =>
      obtain ⟨i, rfl⟩ := hd.ec_surj e'
      refine ⟨vtx _, vtx _, ?_, (lt_bed_iff hc).2 (Or.inl rfl),
        (lt_bed_iff hc).2 (Or.inr rfl), fun z hz => (lt_bed_iff hc).1 hz⟩
      intro h
      exact hd.noLoop i (by injection toS_inj hc h)
  | ced p =>
      refine ⟨cvx p, cvx _, ?_, (lt_ced_iff hc).2 (Or.inl rfl),
        (lt_ced_iff hc).2 (Or.inr rfl), fun z hz => (lt_ced_iff hc).1 hz⟩
      grind [toS_inj, fin_succ_ne_self]
  | dia p =>
      refine ⟨vtx _, cvx p, ?_, (lt_dia_iff hc).2 (Or.inl rfl),
        (lt_dia_iff hc).2 (Or.inr rfl), fun z hz => (lt_dia_iff hc).1 hz⟩ <;> grind
  | gdi p =>
      refine ⟨vtx _, cvx _, ?_, (lt_gdi_iff hc).2 (Or.inl rfl),
        (lt_gdi_iff hc).2 (Or.inr rfl), fun z hz => (lt_gdi_iff hc).1 hz⟩ <;> grind
  | rad p =>
      refine ⟨ctr, cvx p, ?_, (lt_rad_iff hc).2 (Or.inl rfl),
        (lt_rad_iff hc).2 (Or.inr rfl), fun z hz => (lt_rad_iff hc).1 hz⟩ <;> grind
  | _ => simp_all [Cell.rk]

/-- **Every edge of the surface lies in exactly two triangles.** -/
theorem two_faces_SCell :
    ∀ e : SCell vc ec hc, Cell.rk e = 1 → ExactlyTwo (fun f : SCell vc ec hc => e < f) := by
  have hM2 : 2 ≤ M := by have := hd.three_le; omega
  intro e he
  cases e with
  | bed e' =>
      obtain ⟨i, rfl⟩ := hd.ec_surj e'
      obtain ⟨j, hji, hecj, huniq⟩ := hd.pairs i
      refine ⟨tr1 i, tr1 j, ?_, (bed_lt_iff hc).2 ⟨i, rfl, rfl⟩,
        (bed_lt_iff hc).2 ⟨j, hecj, rfl⟩, ?_⟩
      · grind
      · intro z hz
        obtain ⟨p, hp, rfl⟩ := (bed_lt_iff hc).1 hz <;> grind
  | ced p =>
      refine ⟨tr2 p, inn p, ?_, (ced_lt_iff hc).2 (Or.inl rfl),
        (ced_lt_iff hc).2 (Or.inr rfl), fun z hz => (ced_lt_iff hc).1 hz⟩ <;> grind
  | dia p =>
      refine ⟨tr2 p, tr1 _, ?_, (dia_lt_iff hc).2 (Or.inl rfl),
        (dia_lt_iff hc).2 (Or.inr rfl), fun z hz => (dia_lt_iff hc).1 hz⟩ <;> grind
  | gdi p =>
      refine ⟨tr1 p, tr2 p, ?_, (gdi_lt_iff hc).2 (Or.inl rfl),
        (gdi_lt_iff hc).2 (Or.inr rfl), fun z hz => (gdi_lt_iff hc).1 hz⟩ <;> grind
  | rad p =>
      refine ⟨inn p, inn _, ?_, (rad_lt_iff hc).2 (Or.inl rfl),
        (rad_lt_iff hc).2 (Or.inr rfl), fun z hz => (rad_lt_iff hc).1 hz⟩
      grind [toS_inj, fpred_ne_self]
  | _ => simp_all [Cell.rk]

end

section

variable {P : Type*} [PartialOrder P]

/-- Two incidence consequences of a triangular boundary. -/
def TriangleIncidence (r : P → ℕ) (f : P) :=
  (∀ v, r v = 0 → v < f → ExactlyTwo (fun e => v < e ∧ e < f)) ∧
  ∀ v w, r v = 0 → r w = 0 → v < f → w < f → v ≠ w → ∃ e, v < e ∧ w < e ∧ e < f

theorem triangleIncidence_of_sides {r : P → ℕ}
    (rise : StrictMono r) {f : P} (a b c i j k : P)
    (ranks : r a = 0 ∧ r b = 0 ∧ r c = 0 ∧ r i = 1 ∧ r j = 1 ∧ r k = 1)
    (distinct : a ≠ b ∧ b ≠ c ∧ c ≠ a ∧ i ≠ j ∧ j ≠ k ∧ k ≠ i)
    (faces : ∀ z, z < f ↔ z = i ∨ z = j ∨ z = k ∨ z = a ∨ z = b ∨ z = c)
    (endsI : ∀ z, z < i ↔ z = a ∨ z = b) (endsJ : ∀ z, z < j ↔ z = b ∨ z = c)
    (endsK : ∀ z, z < k ↔ z = c ∨ z = a) : TriangleIncidence r f := by
  have vertices (z) (h : r z = 0) (hz : z < f) : z = a ∨ z = b ∨ z = c := by grind
  have edges (v z) (hv : v < z) (hz : z < f) : z = i ∨ z = j ∨ z = k := by
    have := rise hv
    grind
  constructor
  · intro v hv h
    rcases vertices v hv h with rfl | rfl | rfl
    · exact ⟨i, k, by grind⟩
    · exact ⟨i, j, by grind⟩
    · exact ⟨j, k, by grind⟩
  · intro v w hv hw hvf hwf hne
    rcases vertices v hv hvf with rfl | rfl | rfl <;>
      rcases vertices w hw hwf with rfl | rfl | rfl <;>
      first | exact (hne rfl).elim | exact ⟨i, by grind⟩ | exact ⟨j, by grind⟩ | exact ⟨k, by grind⟩

end

section

variable (hd : PolygonData vc ec)
include hd

theorem triangleIncidence_SCell (f : SCell vc ec hc) (hf : Cell.rk f = 2) :
    TriangleIncidence (P := SCell vc ec hc) Cell.rk f := by
  have rise : StrictMono (α := SCell vc ec hc) Cell.rk :=
    fun _ _ h => rk_lt_of_plt ((lt_iff_plt hc).mp h)
  have hM := hd.three_le
  have hn (p : Fin M) := hd.noLoop p
  cases f with
  | tr1 p =>
    apply triangleIncidence_of_sides rise (vtx (vc p)) (vtx (vc (p+1))) (cvx (p+1))
      (bed (ec p)) (dia (p+1)) (gdi p)
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp [SCell, hn]
    · intro z; erw [lt_tr1_iff hc]; tauto
    · apply lt_bed_iff
    · apply lt_dia_iff
    · intro z; exact (lt_gdi_iff hc).trans or_comm
  | tr2 p =>
    apply triangleIncidence_of_sides rise (vtx (vc p)) (cvx p) (cvx (p+1))
      (dia p) (ced p) (gdi p)
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp [SCell]; grind
    · intro z; erw [lt_tr2_iff hc]; tauto
    · apply lt_dia_iff
    · apply lt_ced_iff
    · intro z; exact (lt_gdi_iff hc).trans or_comm
  | inn p =>
    apply triangleIncidence_of_sides rise ctr (cvx p) (cvx (p+1))
      (rad p) (ced p) (rad (p+1))
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp [SCell]; grind
    · intro z; erw [lt_inn_iff hc]; tauto
    · apply lt_rad_iff
    · apply lt_ced_iff
    · intro z; exact (lt_rad_iff hc).trans or_comm
  | _ => simp [Cell.rk] at hf

theorem two_edges_SCell (v f : SCell vc ec hc) (hv : Cell.rk v = 0)
    (hf : Cell.rk f = 2) (hvf : v < f) : ExactlyTwo (fun e : SCell vc ec hc => v < e ∧ e < f) :=
  (triangleIncidence_SCell hc hd f hf).1 v hv hvf

/-- Every cell of the surface is a face of a triangle. -/
theorem exists_face_SCell :
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
  | tr1 p => aesop
  | tr2 p => aesop
  | ctr =>
      exact ⟨inn 0, rfl, le_of_lt ((lt_inn_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩
  | rad p => exact ⟨inn p, rfl, le_of_lt ((lt_inn_iff hc).2 (Or.inr (Or.inl rfl)))⟩
  | inn p => aesop

end

/-- Every triangle of the surface has a vertex. -/
theorem exists_vertex_SCell :
    ∀ f : SCell vc ec hc, Cell.rk f = 2 → ∃ v : SCell vc ec hc, Cell.rk v = 0 ∧ v < f := by
  intro f hf
  cases f with
  | tr1 p =>
      exact ⟨vtx _, rfl, (lt_tr1_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
  | tr2 p =>
      exact ⟨vtx _, rfl, (lt_tr2_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
  | inn p => exact ⟨ctr, rfl, (lt_inn_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
  | _ => simp_all [Cell.rk]

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
