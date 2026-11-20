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
two triangles**.
-/

namespace FiniteChains
namespace Davis

open Cell ASC

universe u

/-! ### Arithmetic of the boundary cycle -/

section FinAux

variable {M : ℕ} [NeZero M]

/-- The predecessor in the cyclic additive group of boundary positions. -/
def fpred (p : Fin M) : Fin M := p - 1

theorem fpred_val (p : Fin M) : (fpred p).val = if p.val = 0 then M - 1 else p.val - 1 := by
  cases M with
  | zero => exact p.elim0
  | succ n => simpa only [fpred, ← Fin.val_eq_zero_iff, Nat.succ_sub_one] using Fin.coe_sub_one p

theorem fpred_add_one (p : Fin M) : fpred p + 1 = p := sub_add_cancel p 1

theorem fpred_succ (p : Fin M) : fpred (p + 1) = p := add_sub_cancel_right p 1

theorem fin_succ_ne_self (hM : 2 ≤ M) (p : Fin M) : p + 1 ≠ p := by
  intro hp
  have h : (1 : Fin M) = 0 := add_left_cancel (hp.trans (add_zero p).symm)
  have := congrArg Fin.val h
  simp [Nat.mod_eq_of_lt (show 1 < M by omega)] at this

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
    rcases hle with h | h <;> tauto
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
      simp only [Cell.vtx.injEq]
      constructor
      · rintro ⟨j, hj, hv⟩
        rcases hc j i hj with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hv with hv | hv <;> simp_all
      · rintro (rfl | rfl)
        · exact ⟨i, rfl, Or.inl rfl⟩
        · exact ⟨i, rfl, Or.inr rfl⟩
  | _ => aesop

/-- The vertices of a collar edge. -/
theorem lt_ced_iff {p : Fin M} {x : Cell κ ι M} :
    (toS vc ec hc x < toS vc ec hc (ced p)) ↔ (x = cvx p ∨ x = cvx (p + 1)) := by
  rw [lt_iff_plt]
  cases x <;> aesop

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
  | _ => aesop

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
  | _ => aesop

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
      simp only [plt, Cell.inn.injEq]
      constructor
      · rintro (h | h)
        · aesop
        · exact Or.inr (by rw [h, fpred_succ])
      · rintro (h | h)
        · exact Or.inl h.symm
        · simp [h, fpred_add_one]
  | _ => aesop

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
  exact fun h => fin_succ_ne_self hM p ((congrArg (· + 1) h).symm.trans (fpred_add_one p))

theorem not_lt_rk_zero {v z : Cell κ ι M} (hv : Cell.rk v = 0) (hz : Cell.rk z = 0)
    (h : toS vc ec hc v < toS vc ec hc z) : False := by
  have := rk_lt_of_plt ((lt_iff_plt hc).1 h)
  omega

private theorem exactlyTwo_of_eq_or {T : Type*} {x y : T} {p : T → Prop}
    (hxy : x ≠ y) (h : ∀ z, p z ↔ z = x ∨ z = y) : ExactlyTwo p :=
  ⟨x, y, hxy, (h x).2 (Or.inl rfl), (h y).2 (Or.inr rfl), fun z => (h z).1⟩

/-- Every edge of the surface has exactly two vertices. -/
theorem two_vertices_SCell (hd : PolygonData vc ec) :
    ∀ e : SCell vc ec hc, Cell.rk e = 1 → ExactlyTwo (fun v : SCell vc ec hc => v < e) := by
  have hM2 : 2 ≤ M := le_trans (by decide) hd.three_le
  intro e he
  cases e with
  | bed l =>
    obtain ⟨i, rfl⟩ := hd.ec_surj l
    exact exactlyTwo_of_eq_or (fun h => hd.noLoop i (by injection toS_inj hc h))
      (fun _ => lt_bed_iff hc)
  | ced p =>
    exact exactlyTwo_of_eq_or (fun h => fin_succ_ne_self hM2 p (by injection (toS_inj hc h).symm)) (fun _ => lt_ced_iff hc)
  | dia p => exact exactlyTwo_of_eq_or (by tauto) (fun _ => lt_dia_iff hc)
  | gdi p => exact exactlyTwo_of_eq_or (by tauto) (fun _ => lt_gdi_iff hc)
  | rad p => exact exactlyTwo_of_eq_or (by tauto) (fun _ => lt_rad_iff hc)
  | _ => simp [Cell.rk] at he

/-- Every edge of the surface lies in exactly two triangles. -/
theorem two_faces_SCell (hd : PolygonData vc ec) :
    ∀ e : SCell vc ec hc, Cell.rk e = 1 → ExactlyTwo (fun f : SCell vc ec hc => e < f) := by
  have hM2 : 2 ≤ M := le_trans (by decide) hd.three_le
  intro e he
  cases e with
  | bed l =>
    obtain ⟨i, rfl⟩ := hd.ec_surj l
    obtain ⟨j, hji, hecj, huniq⟩ := hd.pairs i
    apply exactlyTwo_of_eq_or (x := tr1 i) (y := tr1 j) (by grind)
    intro f
    erw [bed_lt_iff hc (i := i) (y := f)]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (huniq p hp).imp (congrArg tr1) (congrArg tr1)
    · rintro (rfl | rfl)
      · exact ⟨i, rfl, rfl⟩
      · exact ⟨j, hecj, rfl⟩
  | ced p => exact exactlyTwo_of_eq_or (by tauto) (fun _ => ced_lt_iff hc)
  | dia p => exact exactlyTwo_of_eq_or (by tauto) (fun _ => dia_lt_iff hc)
  | gdi p => exact exactlyTwo_of_eq_or (by tauto) (fun _ => gdi_lt_iff hc)
  | rad p =>
    exact exactlyTwo_of_eq_or (fun h => fpred_ne_self hM2 p (by injection (toS_inj hc h).symm)) (fun _ => rad_lt_iff hc)
  | _ => simp [Cell.rk] at he

/-- A triangular face has three named vertices and the three sides joining their pairs. -/
structure TriangleBoundary (f : SCell vc ec hc) where
  a : SCell vc ec hc
  b : SCell vc ec hc
  c : SCell vc ec hc
  ab : SCell vc ec hc
  bc : SCell vc ec hc
  ac : SCell vc ec hc
  ra : Cell.rk a = 0
  rb : Cell.rk b = 0
  rc : Cell.rk c = 0
  hab : a ≠ b
  hbc : b ≠ c
  hac : a ≠ c
  edgeAB : ∀ x : SCell vc ec hc, x < ab ↔ x = a ∨ x = b
  edgeBC : ∀ x : SCell vc ec hc, x < bc ↔ x = b ∨ x = c
  edgeAC : ∀ x : SCell vc ec hc, x < ac ↔ x = a ∨ x = c
  faces : ∀ x : SCell vc ec hc, x < f ↔ x = ab ∨ x = bc ∨ x = ac ∨ x = a ∨ x = b ∨ x = c

variable {hc} in
theorem TriangleBoundary.vertex_cases {v f : SCell vc ec hc} (T : TriangleBoundary hc f)
    (hv : Cell.rk v = 0) (h : v < f) : v = T.a ∨ v = T.b ∨ v = T.c := by
  rcases (T.faces v).1 h with he | he | he | h | h | h
  · exact False.elim (not_lt_rk_zero hc T.ra hv
      (he.symm ▸ (T.edgeAB _).2 (Or.inl rfl)))
  · exact False.elim (not_lt_rk_zero hc T.rb hv
      (he.symm ▸ (T.edgeBC _).2 (Or.inl rfl)))
  · exact False.elim (not_lt_rk_zero hc T.rc hv
      (he.symm ▸ (T.edgeAC _).2 (Or.inr rfl)))
  all_goals tauto

variable {hc} in
theorem TriangleBoundary.incidence {v f : SCell vc ec hc} (T : TriangleBoundary hc f)
    (hv : Cell.rk v = 0) (hvf : v < f) :
    ExactlyTwo (fun e : SCell vc ec hc => v < e ∧ e < f) := by
  have hv' := T.vertex_cases hv hvf
  obtain ⟨a, b, c, ab, bc, ac, ha, hb, hc', hab, hbc, hac, h₁, h₂, h₃, hf⟩ := T
  have hA : a < ab := (h₁ a).2 (Or.inl rfl)
  have hB : b < bc := (h₂ b).2 (Or.inl rfl)
  have hC : c < ac := (h₃ c).2 (Or.inr rfl)
  have hAB : ab ≠ bc := fun h => ((h₂ a).1 (h ▸ hA)).elim hab hac
  have hAC : ab ≠ ac := fun h => ((h₁ c).1 (h ▸ hC)).elim hac.symm hbc.symm
  have hBC : bc ≠ ac := fun h => ((h₃ b).1 (h ▸ hB)).elim hab.symm hbc
  have hn (e : SCell vc ec hc) (h : Cell.rk e = 0) : ¬ v < e := not_lt_rk_zero hc hv h
  have he (e : SCell vc ec hc) : v < e ∧ e < f ↔
      ((v = a ∨ v = b) ∧ e = ab) ∨ ((v = b ∨ v = c) ∧ e = bc) ∨
      ((v = a ∨ v = c) ∧ e = ac) := by
    rw [hf e]
    constructor
    · rintro ⟨h, rfl | rfl | rfl | rfl | rfl | rfl⟩ <;>
        simp_all [hn _ ha, hn _ hb, hn _ hc']
    · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩) <;> simp_all
  rcases hv' with rfl | rfl | rfl
  · exact exactlyTwo_of_eq_or hAC (fun e => by simpa [hab, hac] using he e)
  · exact exactlyTwo_of_eq_or hAB (fun e => by simpa [hab.symm, hbc] using he e)
  · exact exactlyTwo_of_eq_or hBC (fun e => by simpa [hac.symm, hbc.symm] using he e)

/-- Read off the triangular boundary from the incidence table. -/
def triangleBoundary (hd : PolygonData vc ec) (f : SCell vc ec hc) (hf : Cell.rk f = 2) :
    TriangleBoundary hc f := by
  have hs (p : Fin M) : (cvx p : SCell vc ec hc) ≠ cvx (p + 1) :=
    fun h => fin_succ_ne_self (le_trans (by decide) hd.three_le) p
      (by injection (toS_inj hc h).symm)
  cases f with
  | tr1 p =>
    refine ⟨vtx (vc p), vtx (vc (p + 1)), cvx (p + 1), bed (ec p), dia (p + 1), gdi p,
      rfl, rfl, rfl, (fun h => hd.noLoop p (by injection toS_inj hc h)), by tauto, by tauto,
      (fun _ => lt_bed_iff hc), (fun _ => lt_dia_iff hc), (fun _ => lt_gdi_iff hc),
      fun _ => lt_tr1_iff hc⟩
  | tr2 p =>
    refine ⟨vtx (vc p), cvx p, cvx (p + 1), dia p, ced p, gdi p, rfl, rfl, rfl,
      by tauto, hs p, by tauto, (fun _ => lt_dia_iff hc), (fun _ => lt_ced_iff hc),
      (fun _ => lt_gdi_iff hc), ?_⟩
    intro x
    erw [lt_tr2_iff hc (p := p) (x := x)]
    tauto
  | inn p =>
    refine ⟨ctr, cvx p, cvx (p + 1), rad p, ced p, rad (p + 1), rfl, rfl, rfl,
      by tauto, hs p, by tauto, (fun _ => lt_rad_iff hc), (fun _ => lt_ced_iff hc),
      (fun _ => lt_rad_iff hc), ?_⟩
    intro x
    erw [lt_inn_iff hc (p := p) (x := x)]
    tauto
  | _ => simp [Cell.rk] at hf

/-- Every vertex of a triangle lies in exactly two of its edges. -/
theorem two_edges_SCell (hd : PolygonData vc ec) :
    ∀ v f : SCell vc ec hc, Cell.rk v = 0 → Cell.rk f = 2 → v < f →
      ExactlyTwo (fun e : SCell vc ec hc => v < e ∧ e < f) :=
  fun _ f hv hf h => (triangleBoundary hc hd f hf).incidence hv h

/-- Every cell of the surface is a face of a triangle. -/
theorem exists_face_SCell (hd : PolygonData vc ec) :
    ∀ x : SCell vc ec hc, ∃ f : SCell vc ec hc, Cell.rk f = 2 ∧ x ≤ f := by
  intro x
  cases x
  case' vtx v => obtain ⟨i, rfl⟩ := hd.vc_surj v; refine ⟨tr1 i, rfl, ?_⟩
  case' bed e => obtain ⟨i, rfl⟩ := hd.ec_surj e; refine ⟨tr1 i, rfl, ?_⟩
  case' cvx p | ced p | dia p | gdi p => refine ⟨tr2 p, rfl, ?_⟩
  case' ctr => refine ⟨inn 0, rfl, ?_⟩
  case' rad p => refine ⟨inn p, rfl, ?_⟩
  case tr1 p | tr2 p | inn p => exact ⟨_, rfl, le_rfl⟩
  all_goals exact Or.inr (by simp [plt])

/-- Every triangle of the surface has a vertex. -/
theorem exists_vertex_SCell :
    ∀ f : SCell vc ec hc, Cell.rk f = 2 → ∃ v : SCell vc ec hc, Cell.rk v = 0 ∧ v < f := by
  intro f hf
  cases f
  case' tr1 p | tr2 p => refine ⟨vtx (vc p), rfl, ?_⟩
  case' inn p => refine ⟨ctr, rfl, ?_⟩
  all_goals first | exact (lt_iff_plt hc).2 (by simp [plt]) | simp [Cell.rk] at hf

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


section CenterIncidences

variable {κ ι : Type u} {M : ℕ} [NeZero M]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)

theorem ctr_lt_iff {y : Cell κ ι M} :
    (toS vc ec hc ctr < toS vc ec hc y) ↔ (∃ p : Fin M, y = rad p ∨ y = inn p) := by
  rw [lt_iff_plt]
  cases y <;> simp [plt]

theorem ctr_lt_rad (r : Fin M) : toS vc ec hc ctr < toS vc ec hc (rad r) :=
  (lt_rad_iff hc).2 (Or.inl rfl)

theorem ctr_lt_inn (r : Fin M) : toS vc ec hc ctr < toS vc ec hc (inn r) :=
  (lt_inn_iff hc).2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

end CenterIncidences

end Davis
end FiniteChains
