module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepEvTasks
public import Chazelle.Core.SweepIoLHit5
public import Chazelle.Core.SweepIoQPos
public import Chazelle.Core.SweepEvSym
public import Chazelle.Core.RestoreTestMath

/-!
# The sweep (WP-D), stage 3: the genuineness check, mathematics

The hit `w = rayPt a σ τ` of the model of `C₁` from a point `a` of the domain is genuine iff the
reverse ray from `w` (direction `-σ`) leaves the domain beyond `a`, i.e. `τ < hitParam w (-σ)`
(`genuine_iff_rev`); with the hit `h` of the reverse ray this compares the abscissas of `h` and
`a` (`genuine_iff_abs`).  The reverse local hit (the answer stage's (`SweepIo`) `localHit`) yields `h` as the least
of its candidates (`lh_min`).

The arrival position of `w`: its point is `w`, it lies on the chain or on a vertical side of the
box (`arr_facts`), and with a positive height code naming its height it satisfies the conditions
of completeness of the local hit (`lhGeo_pos`, `lhGeo_fix`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt rayPt_fst)
open Chazelle.Chain (sidePt sideLeft)

@[expose] public section

/-! ## The reverse ray -/

theorem rayPt_rev (a : Point) (σ τ u : ℝ) : rayPt (rayPt a σ τ) (-σ) u = rayPt a σ (τ - u) := by
  grind [rayPt]

/-- Points of the chain or of the boundary of its box are off its domain. -/
theorem not_dom_of_onCB {C : Chain} {p : Point} (h : OnCB C p) : p ∉ C.dom := by
  intro hd
  have hb := C.dom_subset_box hd
  rw [Chazelle.Chain.mem_box_iff] at hb
  rcases h with h | h | h
  · exact C.not_mem_set_of_mem_dom hd h
  all_goals simp_all

section
variable {C : Chain} {a : Point} {σ τ : ℝ} (hσ : σ = 1 ∨ σ = -1) (ha : a ∈ C.dom) (hw : rayPt a σ τ ∉ C.dom) (h0 : 0 < τ) (htop : a.2 ≤ C.top.2) (hfree : Merge.FreeAt C (rayPt a σ τ) (-σ))
include hσ ha hw h0 htop hfree
/-- **Genuineness by the reverse ray**: for `a` in the domain and `w = rayPt a σ τ` off it, the
hit is genuine iff the reverse ray from `w` leaves the domain beyond `a`. -/
theorem genuine_iff_rev :
    Genuine C a σ τ ↔ τ < C.hitParam (rayPt a σ τ) (-σ) := by
  have hσ' : -σ = 1 ∨ -σ = -1 := by grind
  obtain ⟨hT, hTD, hin⟩ := Merge.hit_of_freeAt C (p := rayPt a σ τ) (by simp_all) hσ' hfree
  set T := C.hitParam (rayPt a σ τ) (-σ) with hTd
  constructor
  · rintro ⟨-, hin', -⟩
    by_contra hle
    push Not at hle
    rcases hle.lt_or_eq with hlt | heq
    · grind [rayPt_rev]
    · apply hTD
      rw [heq, rayPt_rev, sub_self]
      aesop
  · intro hlt
    refine ⟨h0, fun s hs1 hs2 => ?_, hw⟩
    have := hin (τ - s) (by linarith) (by linarith)
    simp_all [rayPt_rev] 

/-- **Genuineness by abscissas**: the hit `h` of the reverse ray lies beyond `a`. -/
theorem genuine_iff_abs :
    (σ = 1 → (Genuine C a σ τ ↔
      (rayPt (rayPt a σ τ) (-σ) (C.hitParam (rayPt a σ τ) (-σ))).1 < a.1)) ∧
    (σ = -1 → (Genuine C a σ τ ↔
      a.1 < (rayPt (rayPt a σ τ) (-σ) (C.hitParam (rayPt a σ τ) (-σ))).1)) := by
  rw [genuine_iff_rev hσ ha hw h0 htop hfree]
  ram_all <;> ram_grind


end

/-- **The least candidate of the local hit is the hit**: candidates are positive parameters of
points of the chain or of the box boundary, and the hit is a candidate. -/
theorem lh_min {C : Chain} {z : Point} {σ : ℝ} {L : Set ℝ} {τm : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hz : z.2 ≤ C.top.2) (hL : ∀ τ ∈ L, 0 < τ ∧ OnCB C (rayPt z σ τ))
    (hfree : Merge.FreeAt C z σ) (hmem : C.hitParam z σ ∈ L) (hτm : τm ∈ L)
    (hmin : ∀ τ' ∈ L, τm ≤ τ') : τm = C.hitParam z σ := by
  obtain ⟨-, -, hin⟩ := Merge.hit_of_freeAt C hz hσ hfree
  grind [Chazelle.Core.SweepEv.not_dom_of_onCB]

/-! ## The arrival position -/

/-- **The arrival position of a hit** below the top: its point is the hit, it is of the class of
the local hit (a vertical side of the box, or a point of the chain on a walk edge `≥ 6`), and the
hit is off the domain. -/
theorem arr_facts {C : Chain} {Q : Polygon} {N : ℕ} {x : WPos} {w : Point} {σ : ℝ}
    (he : x.edge < (chainModel C).W.n) (hpp : ProperPos (chainModel C) Q N x)
    (harr : Arrival (chainModel C).W w σ x.edge ((chainModel C).param Q x))
    (hy : |w.2| < C.radius) (htop : w.2 ≤ C.top.2) :
    (chainModel C).pos Q x = w ∧ PosClass C Q x ∧
      ((x.edge = 1 ∨ x.edge = 3) ∨ (6 ≤ x.edge ∧ (chainModel C).pos Q x ∈ C.set)) ∧
      w ∉ C.dom := by
  have hpos : (chainModel C).pos Q x = w := by
    rw [pos_eq_sidePt']; exact harr.2.2.2.1
  have hcl : PosClass C Q x := posClass_of he hpp.1 hpp.2.1 (by simp_all)
    (Or.inl (by simp_all))
  have hW : (chainModel C).W = C.sideWalk C.sideBeta := rfl
  have hloc : (x.edge = 1 ∨ x.edge = 3) ∨ (6 ≤ x.edge ∧ (chainModel C).pos Q x ∈ C.set) := by
    rcases hcl with h | ⟨h6, hlt⟩ | ⟨hend, hz⟩
    · omega
    · refine Or.inr ⟨h6, ?_⟩
      rw [pos_eq_sidePt', hW]
      have := C.sideWalk_tour_pt_mem C.sideBeta (i := x.edge - 6)
        (t := (chainModel C).param Q x) (by omega) (fun h => by omega) hpp.1 hpp.2.1
      simp_all
    · refine Or.inr ⟨by omega, ?_⟩
      rw [pos_eq_sidePt', hW, hend, hz]
      exact C.sideWalk_tour_pt_mem C.sideBeta (i := 2 * C.m) (t := 0) le_rfl (fun _ => rfl)
        le_rfl one_pos
  refine ⟨hpos, hcl, hloc, ?_⟩
  rw [← hpos]
  rcases posClass_pt hcl hpp.1 hpp.2.1 (by simp_all) with h | ⟨h, -⟩
  · exact not_dom_of_onCB (Or.inl h)
  · exact not_dom_of_onCB (Or.inr (Or.inl h))

section
variable {M : Model} {Q : Polygon}
/-- A positive normalised height code names the height of the point. -/
theorem hgt_of_pos {x : WPos} {h : ℕ} (hx : x.hgt = h + 1)
    (hpar : M.param Q x ≠ 0) : (Q.vtx h).2 = (M.pos Q x).2 := by
  have hne : (M.wa x.edge).2 ≠ (M.wb x.edge).2 := fun he => hpar (Model.param_horizontal he)
  rw [Model.pos_snd hne]
  core_grind

/-- **The vertex fix**: a vertex position gets a positive height code naming its height; the
parameter (`0`) and the point are kept. -/
theorem vtx_fix {e h' : ℕ} (hht : (Q.vtx h').2 = (M.pos Q ⟨e, 0⟩).2) :
    M.param Q ⟨e, h' + 1⟩ = 0 ∧ M.pos Q ⟨e, h' + 1⟩ = M.pos Q ⟨e, 0⟩ := by
  have hp0 : M.param Q ⟨e, 0⟩ = 0 := rfl
  have hwa : M.pos Q ⟨e, 0⟩ = M.wa e := by
    grind [Model.pos, Geometry.lerp_zero]
  have hpar : M.param Q ⟨e, h' + 1⟩ = 0 :=
    (param_eq_zero_iff M Q ⟨e, h' + 1⟩).2 (Or.inr (Or.inr (by
      simp_all)))
  simp_all [Model.pos] 


end

/-- The two copies `6` and `2m + 6` of the top of a chain have the same point. -/
theorem pos_top_copies (C : Chain) (Q : Polygon) :
    (chainModel C).pos Q ⟨2 * C.m + 6, 0⟩ = (chainModel C).pos Q ⟨6, 0⟩ := by
  rw [pos_eq_sidePt', pos_eq_sidePt']
  have h0 : (chainModel C).param Q ⟨2 * C.m + 6, 0⟩ = 0 := rfl
  have h0' : (chainModel C).param Q ⟨6, 0⟩ = 0 := rfl
  have hW : (chainModel C).W = C.sideWalk C.sideBeta := rfl
  simp only [h0, h0', Chazelle.Chain.sidePt_zero, hW]
  have e1 := C.sideWalk_vtx_tour C.sideBeta (i := 2 * C.m) le_rfl
  have e2 := C.sideWalk_vtx_tour C.sideBeta (i := 0) (by omega)
  rw [show 0 + 6 = 6 by rfl] at e2
  rw [e1, e2, C.sideTour_two_m, C.sideTour_zero]

/-- The height code of a symbolic point (`i` for a vertex, `h` for a point of an edge at the
height of vertex `h`). -/
theorem symHgt {P : Polygon} {c : Config} {o : ℕ} {s : SymPt} (hs : SymPtIn c o s)
    (hl : s.Lt P.n) :
    (if c.nreg o = 0 then c.nreg (o + 1) else c.nreg (o + 2)) < P.n ∧
      ((Qof P).vtx (if c.nreg o = 0 then c.nreg (o + 1) else c.nreg (o + 2))).2 =
        (s.eval (Qof P)).2 := by
  cases s with
  | vtx i =>
    obtain ⟨h0, h1⟩ := hs
    aesop
  | onEdge e h =>
    obtain ⟨h0, -, h2⟩ := hs
    rw [ite_eq_right (by omega), h2]
    exact ⟨hl.2, rfl⟩

/-! ## Region bounds -/

/-- **Arcs and exit chords of the regions** of a normal form of degree `≤ D`. -/
theorem region_bounds {C : Chain} {Q : Polygon} {N : NF} {D : ℕ} (hP : C.P.Simple)
    (hNF : IsNF (chainModel C) Q N) (hdeg : (chainModel C).DegLe (N.F (chainModel C) Q) D) :
    (∀ r, r < N.nRegions → (N.region r).arcs.length ≤ D + 1) ∧
      (∀ r, r < N.nRegions → (N.region r).chords.length ≤ D) := by
  have hNF' := hNF
  obtain ⟨-, -, -, reg, hRC, hCS, hAO, hRO, -⟩ := hNF'
  have hregs : Restore.NFRegs (chainModel C) Q N reg := ⟨hRC, hCS, hAO, hRO⟩
  have hGM : GoodModel (chainModel C) := Or.inl ⟨C, hP, rfl⟩
  refine ⟨fun r hr => ?_, fun r hr => ?_⟩
  · have := Restore.arcs_le_deg hGM hNF hregs hr
    have := hdeg (reg r) (hRC.1 r hr)
    omega
  · have := Restore.chords_le_deg hNF hregs hr
    have := hdeg (reg r) (hRC.1 r hr)
    omega

end

end SweepEv

end Chazelle.Core
