module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.RestoreTCall

/-!
# WP-E, the candidate test on the RAM, part 2: comparing keys

The candidate test compares the keys of walk positions (the candidate, the ends of the arcs of
the region, the ends of its exit chords, the arrival position).  `offCmp` with base vertex `0`
compares keys directly (`off n 0 k = k`).  Its input condition excludes the box vertices (height
code `0` on the box edges `0 … 5`); the positions the test handles are at heights of vertices of
`Q`, strictly inside the height band of the box, so they are never box vertices (`posOK_of`).

* `chainModel_ne_interior`, `chainDesc_of`: a descriptor of a chain model is a chain descriptor.
* `PosOK`: the input condition of a position for `offCmp`.
* `keyCmp a b d e`: the bits `key x < key y` (into `50210`) and `key y < key x` (into `50211`)
  for the positions `x = (a, b)`, `y = (d, e)` held in band `bRestore` (`keyCmp_exec`).  The
  chain descriptor address is in `83020`, the constant `0` in `83022`.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim WalkEmbed

/-! ## The descriptor of a chain model -/

/-- A chain model is not an interior model (their counted edges differ). -/
theorem chainModel_ne_interior (C : Chain) (Q : Polygon) : chainModel C ≠ interiorModel Q := by
  intro h
  have := congrArg (fun M : Model => M.counted 0) h
  core_grind

/-- The model descriptor of a chain model holds a chain descriptor after its header. -/
theorem chainDesc_of {m : ℕ → ℕ} {B : ℕ} {Q : Polygon} {M : Model} {C : Chain}
    (h : ModelDescAt m B Q M) (hM : M = chainModel C) :
    m B = 0 ∧ ∃ H C', ChainDescAt m (B + 1) Q H C' ∧ M = chainModel C' := by
  rcases h with ⟨h0, H, C', hC, hM'⟩ | ⟨-, -, hI⟩
  · ram_grind
  · exact absurd (hM.symm.trans hI) (chainModel_ne_interior C Q)

/-! ## Keys as offsets from vertex `0` -/

theorem off_zero {n k : ℝ} (hk : 0 ≤ k) : off n 0 k = k := by
  core_grind

theorem key_nonneg {M : Model} {Q : Polygon} {n : ℕ} {x : WPos} (hx : ProperPos M Q n x) :
    0 ≤ M.key Q x := by
  unfold Model.key; have := hx.1; positivity

/-- **The input condition of a position** for `offCmp`: a proper position of the walk, not a box
vertex. -/
def PosOK (C : Chain) (Q : Polygon) (n : ℕ) (x : WPos) : Prop :=
  x.edge < (chainModel C).W.n ∧ ProperPos (chainModel C) Q n x ∧ (x.hgt = 0 → 6 ≤ x.edge)

/-- A proper position whose point is strictly inside the height band of the box is not a box
vertex. -/
theorem posOK_of {C : Chain} {Q : Polygon} {n : ℕ} {x : WPos} (he : x.edge < (chainModel C).W.n)
    (hx : ProperPos (chainModel C) Q n x) (hy : |((chainModel C).pos Q x).2| < C.radius) :
    PosOK C Q n x := by
  refine ⟨he, hx, fun h0 => ?_⟩
  by_contra h6
  have hp := box_param_pos C (by omega) hx.1 hy
  simp_all [Model.param] <;> omega_nf

/-! ## The comparison call -/

/-- The copies of a key comparison of the positions in `a, b` and `d, e`. -/
def kcL (a b d e : ℕ) : List (ℕ × ℕ) :=
  [(50200, 83020), (50201, a), (50202, b), (50203, d), (50204, e), (50205, 83022)]

/-- **Key comparison** of the positions `(a, b)` and `(d, e)`. -/
def keyCmp (a b d e : ℕ) : Stmt := .seq (block (copies (kcL a b d e))) offCmp

/-- A register of band `bRestore`. -/
def InR (r : ℕ) : Prop := 80000 ≤ r ∧ r < 90000

section
variable {a b d e : ℕ} (ha : InR a) (hb : InR b) (hd : InR d) (he : InR e)
include ha hb hd he
theorem kcL_hd :
    ∀ q ∈ kcL a b d e, ∀ r ∈ kcL a b d e, q.1 ≠ r.2 := by
  unfold InR at *
  simp only [kcL, List.mem_cons, List.not_mem_nil, or_false]
  rintro q (rfl | rfl | rfl | rfl | rfl | rfl) r (rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only <;> omega

/-- **Contract of a key comparison** (at most `11006` steps). -/
theorem keyCmp_exec
    {P : Polygon} {W : ℕ} {c : Config} {H : Host} {C : Chain} (hw : WordsBounded W c)
    (hG : GoodEnv P) (hW : hostWords P.n ≤ W)
    (hwf : ChainWF P (c.nreg ALLOC) c.nmem (c.nreg 83020))
    (hC : ChainDescAt c.nmem (c.nreg 83020) (Qof P) H C) (h0 : c.nreg 83022 = 0)
    (hx : PosOK C (Qof P) P.n ⟨c.nreg a, c.nreg b⟩)
    (hy : PosOK C (Qof P) P.n ⟨c.nreg d, c.nreg e⟩)
    (hWm : 2 * C.m + 7 ≤ W) (hroom : c.nreg ALLOC + 11000 ≤ W) :
    ∃ c' k, Exec P W (keyCmp a b d e) c c' k ∧ k ≤ 11006 ∧
      BitIs c' 50210 ((chainModel C).key (Qof P) ⟨c.nreg a, c.nreg b⟩ <
        (chainModel C).key (Qof P) ⟨c.nreg d, c.nreg e⟩) ∧
      BitIs c' 50211 ((chainModel C).key (Qof P) ⟨c.nreg d, c.nreg e⟩ <
        (chainModel C).key (Qof P) ⟨c.nreg a, c.nreg b⟩) ∧
      Frame primBands c c' k := by
  obtain ⟨c₁, c', k, h1, -, -, ex, hk, hout, hf⟩ := callPrim offCmp_meets (kcL a b d e)
    (kcL_hd ha hb hd he) (by simp [kcL]) (by simp [kcL])
    (src := 83020) (by simp [kcL]) hw hG hW hwf hC (fun c₁ h1 _ _ => by
      have q1 := h1 (50201, a) (by simp [kcL])
      have q2 := h1 (50202, b) (by simp [kcL])
      have q3 := h1 (50203, d) (by simp [kcL])
      have q4 := h1 (50204, e) (by simp [kcL])
      have q5 := h1 (50205, 83022) (by simp [kcL])
      grind [Chazelle.Core.SweepPrim.OffIn, Chazelle.Core.Restore.InR, Chazelle.WordsBounded, Chazelle.Core.GoodEnv, Chazelle.Core.ChainWF, Chazelle.Core.ChainDescAt, Chazelle.Core.Restore.PosOK]) hroom
  have q1 := h1 (50201, a) (by simp [kcL])
  have q2 := h1 (50202, b) (by simp [kcL])
  have q3 := h1 (50203, d) (by simp [kcL])
  have q4 := h1 (50204, e) (by simp [kcL])
  have q5 := h1 (50205, 83022) (by simp [kcL])
  simp only at q1 q2 q3 q4 q5
  obtain ⟨o1, o2⟩ := hout
  rw [q1, q2, q3, q4, q5, h0, Nat.cast_zero, off_zero (key_nonneg hx.2.1),
    off_zero (key_nonneg hy.2.1)] at o1 o2
  exact ⟨c', k, ex, by simp [kcL] at hk; omega, o1, o2, hf⟩


end

end

end Restore

end Chazelle.Core
