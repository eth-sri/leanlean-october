module

public import Chazelle.Core.SweepPrimDir

/-!
# Sweep RAM primitives (WP-D2), part 14: the cap data of a shared vertex (for WP-F)

For the chain `C` of the descriptor (the whole chain of a junction) and an index `k`
(`1 ≤ k`, `k + 1 ≤ m`) in `50201`, with `u, v, w` the vertices `k - 1, k, k + 1` of `C`:

* `50210`: the bit of `0 < (u.2 - v.2) (w.2 - v.2)` (the shared vertex is a local extremum);
* `50211`: for an extremum, the bit of `|u.2 - v.2| < |w.2 - v.2|` (the nearer arm is `u`);
* `50212`: the height code `h + 1` of the nearer neighbour `near` (the vertex `h` of `Q` has its
  height);
* `50213`: for an extremum with `u.2 ≠ w.2`, the bit of `¬ near.1 < o.1`, where `o` is the
  point of the far arm `[v, far]` at the height of `near` (the cap direction is `+1`).

All tests are sign-kernel tests on the host points of `u, v, w` (heights, and the orientation
`det v far near`, `capx_iff`).  `cvLoad dst`: the host point of chain vertex `50120`.
-/

namespace Chazelle.Core

namespace SweepPrim

open Machine Machine.Stmt Programs SignK WalkKey NFLoc

@[expose] public section

/-! ## Mathematics -/

/-- The orientation of the far arm and a point at a height strictly between. -/
theorem det_lerp (v f p : Point) (hne : f.2 ≠ v.2) :
    det v f p = (f.2 - v.2) * ((Geometry.lerp v f ((p.2 - v.2) / (f.2 - v.2))).1 - p.1) := by
  grind [det, Geometry.lerp_fst]

/-- **The cap direction from an orientation test.** -/
theorem capx_iff (v f p : Point) (hne : f.2 ≠ v.2) :
    p.1 < (Geometry.lerp v f ((p.2 - v.2) / (f.2 - v.2))).1 ↔
      (v.2 < f.2 ∧ 0 < det v f p) ∨ (f.2 < v.2 ∧ ¬ 0 < det v f p ∧ ¬ det v f p = 0) := by
  rw [det_lerp v f p hne]
  set L := (Geometry.lerp v f ((p.2 - v.2) / (f.2 - v.2))).1
  rcases lt_or_gt_of_ne hne with h | h
  · -- `f` below `v`
    
    constructor
    · intro hp; right
      refine ⟨h, ?_, ?_⟩
      all_goals nlinarith
    · rintro (⟨h1, -⟩ | ⟨-, h2, h3⟩)
      · linarith
      · by_contra hc; push Not at hc
        rcases hc.lt_or_eq with hc | hc
        · nlinarith
        simp_all
  · 
    constructor
    · simp_all
    · rintro (⟨-, h2⟩ | ⟨h1, -⟩)
      all_goals nlinarith

/-- The height index of a symbolic point. -/
def shv : SymPt → ℕ
  | .vtx i => i
  | .onEdge _ h => h

theorem eval_snd_shv (Q : Polygon) (s : SymPt) : (s.eval Q).2 = (Q.vtx (shv s)).2 := by
  cases s <;> rfl

/-! ## The host point of a chain vertex -/

/-- The host point of chain vertex `50120` into `dst … dst + 2`. -/
def cvLoad (dst : ℕ) : Stmt :=
  .seq (.instr (.copyN 50091 50120))
    (.seq hostPt (block (copies [(dst, 50046), (dst + 1, 50047), (dst + 2, 50048)])))

/-- The registers written by `cvLoad dst`. -/
def Bcv (dst r : ℕ) : Bool := r == 50091 || Bhost r || decide (dst ≤ r ∧ r < dst + 3)

theorem wr_cvLoad (dst : ℕ) : wr (Bcv dst) (cvLoad dst) = true := by
  aesop (add simp [Bcv, cvLoad, copies, List.map_cons, List.map_nil, block_cons, block_nil, wr, wrOK]) (add safe (by omega))

/-- **The host point of a chain vertex.** -/
theorem cvLoad_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) {k : ℕ} (h120 : c.nreg 50120 = k) (hk : k ≤ C.m) {dst : ℕ}
    (hdst : 50100 ≤ dst) :
    ∃ c' k', Exec P W (cvLoad dst) c c' k' ∧ k' ≤ 27 * H.length + 20 ∧ FrameB (Bcv dst) c c' ∧
      CEnv P W H C c' ∧ ∃ sp : SymPt, SymPtIn c' dst sp ∧ sp.Lt P.n ∧
        sp.eval (Qof P) = C.vertex k := by
  have e₁ := Exec.copyN (P := P) hE.wb 50091 50120
  have hE₁ : CEnv P W H C _ := hE.frame (exec_frameB e₁ (B := fun r => r == 50091) (by decide))
    e₁.wb_right (by decide)
  have hmN : C.m < (H.pts P.n).length := by rw [← hE.n_eq]; exact C.m_lt
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, E₂, sp, hsp, hin⟩ := hostPt_exec (P := P) _ hE₁.host hE₁.hH
    hE₁.wf (by have := hE₁.hW; omega) hE₁.aW hE₁.NW hE₁.r52 hE₁.r87 (k := k)
    (by simp [h120]) hE₁.hs (by omega)
  have hE₂ : CEnv P W H C c₂ := hE₁.of_host E₂ f₂
  obtain ⟨c₃, e₃, h3, h3', _h3r, h3m, _h3rm, _h3o⟩ := copies_exec (P := P)
    [(dst, 50046), (dst + 1, 50047), (dst + 2, 50048)] c₂ e₂.wb_right
    (by intro p hp q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
        grind)
    (by simp)
  have ex : Exec P W (cvLoad dst) c c₃ (1 + (k₂ + 3)) := .seq e₁ (.seq e₂ e₃)
  refine ⟨c₃, _, ex, by omega, exec_frameB ex (wr_cvLoad dst), ?_, sp, ?_, ?_, ?_⟩
  · refine hE₂.keep e₃.wb_right h3m fun r hr => h3' r ?_
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
    omega
  · exact symPtIn_copy hin (h3 (dst, 50046) (by simp)) (h3 (dst + 1, 50047) (by simp))
      (h3 (dst + 2, 50048) (by simp))
  · exact hostWF_pts hE.wf (by have := hE.hG.1.1; omega) _ (List.mem_of_getElem? hsp)
  · rw [chain_vertex_host C hE.hP _ (sp := sp)]
    rw [show (Qof P).n = P.n from shear_n _ _, hE.n_eq]
    exact hsp

end

end SweepPrim

end Chazelle.Core
