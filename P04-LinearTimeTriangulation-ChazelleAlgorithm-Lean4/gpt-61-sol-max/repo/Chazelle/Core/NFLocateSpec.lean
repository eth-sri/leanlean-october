module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.NFLocateChain

/-!
# Double identification: the specification (WP-C, target 2)

`locDir` dispatches on the model kind of the descriptor (`chainDir` or `intDir`); with it,
`locStmt locDir` (`NFLocate`) is proved to meet **`LocateSpec`** from the WP-B fact
`NFLoc.ArcCoverSpec` (`locate_wf`).  The consolidated revision (design doc §10) made
`LocateSpec` equal to the former `LocateSpecWF` (the specification below with the conditions of
the report that follows): proper arc records are part of `IsNF`, the inputs are `NFWithin` and
`ModelDescWF` below the allocator, and the word bound is `hostWords`.

## Why the original `LocateSpec` could not be implemented (report for the lead, now resolved)

1. **Arc positions off the walk proper** (finding C6).  `IsNF` constrains the arc records only
   through the *keys* of their positions.  A start `s = (e', h' + 1)` whose parameter lies outside
   `[0, 1)` (a height code `h'` above the end of its edge) has key `e' + param s`, and deciding
   `key s ≤ key x` for a query `x` on another edge requires comparing a quotient of heights with
   an integer plus another quotient — a degree-two polynomial test in five heights of `Q`, which is
   not one of the kernel's sign tests (`StableAt` does not cover it).  Concretely: an upward edge
   `e'` from height `0` to `2` followed by an upward edge from `2` to `4`, a chord at height `3`
   attached to edge `e' + 1` (key `e' + 1.5`), whose arc start is stored as `(e', h' + 1)` with
   `y_{h'} = 3` (parameter `1.5`, key `e' + 1.5`: valid for `IsNF`); the query `(e' + 1, h'' + 1)`
   with `y_{h''} = 2.5` has key `e' + 1.25`.  Fix: require stored positions to lie on the walk
   proper (`0 ≤ param < 1`) with codes `≤ n`, e.g. as a clause of `IsNF` (chord endpoints already
   satisfy it through `Attached`; `BuildNF` produces arcs from chord endpoints).
2. **Addressability** (finding C7).  `NFAt`/`ModelDescAt` put no bound on the handles and areas:
   with `B = W` (a legal register value) the header word `B + 4` cannot even be addressed without
   exceeding the word bound, so no program reads it.  Fix: state the inputs below the allocator
   (`NFWithin … (c.nreg ALLOC)` for the normal form, and a robust descriptor).
3. **Host descriptors** (finding C8).  The walk vertices of a chain model are points of the host
   `H`; `HostAt` gives no index from point numbers to items, so a lookup scans the items (`O(|H|)`,
   against a cost `κ (⌈log₂ A⌉ + 1)` independent of `|H|`); `HostAt` allows `.pt` items out of
   range (the sign kernel needs `SymPt.Lt n`; e.g. `.pt (.vtx n)` evaluates to the origin, whose
   height is not a kernel quantity), unbounded starts `C.s` (index arithmetic modulo `N`), and
   `N` (the number of host points) above the word bound.  Fix: `HostOk H` (`≤ 64` items, as in
   the down phase), `HostWF` (items in range), `C.s < N`, `2 N ≤ W`.

The revised `LocateSpec` contains exactly these hypotheses; the postcondition and the cost are
unchanged.
-/

namespace Chazelle.Core

namespace NFLoc

open Machine Machine.Stmt Programs SignK WalkKey
open Chazelle.Chain (sideInArc)

@[expose] public section

/-! ## The combined direction procedure -/

/-- Dispatch on the model kind (`0` chain, `1` interior). -/
def locDir : Stmt :=
  .seq (block [.constN 50032 1, .loadN 50033 50000]) (.ifLtN 50033 50032 chainDir intDir)

theorem wr_locDir : wr Bdir locDir = true := by decide

section
variable (P : Polygon) (W : ℕ)
include P W
/-- **Well-formed chain descriptors** for the direction procedure, for a model descriptor at
`D`: if it describes a chain model, at most `64` host items, the host well formed and
addressable, the start below the number `N` of host points, `2 N` within the word bound.  (It
follows from the specification's `ModelDescWF` and `hostWords`: `locChainWF_of`.) -/
def LocChainWF (m : ℕ → ℕ) (D : ℕ) : Prop :=
  m D = 0 → ∀ H C, ChainDescAt m (D + 1) (Qof P) H C →
    H.length ≤ 64 ∧ HostWF P.n H ∧ m (D + 1) + 3 * H.length + 4 ≤ W ∧ C.s < C.P.n ∧
      2 * C.P.n ≤ W

/-- The precondition of the direction procedure. -/
def LocDPre (c : Config) : Prop :=
  GoodEnv P ∧ P.n + 3 ≤ W ∧ c.nreg 50000 + 6 ≤ W ∧ LocChainWF P W c.nmem (c.nreg 50000) ∧
    ∃ M, ModelDescAt c.nmem (c.nreg 50000) (Qof P) M ∧ c.nreg 50002 < M.W.n


end

section
variable {m : ℕ → ℕ}
/-- The layout determines the chain. -/
theorem chain_eq_of_desc {B : ℕ} {Q : Polygon} {H H' : Host} {C C' : Chain}
    (h : ChainDescAt m B Q H C) (h' : ChainDescAt m B Q H' C') : C = C' := by
  have hH : H = H' := hostAt_unique h.1 h'.1
  have hP : C.P = C'.P := by rw [h.2.1, h'.2.1, hH]
  have hs : C.s = C'.s := h.2.2.1.symm.trans h'.2.2.1
  have hm : C.m = C'.m := h.2.2.2.1.symm.trans h'.2.2.2.1
  cases C
  simp_all

/-- **The descriptor determines the model.** -/
theorem modelDesc_unique {D : ℕ} {Q : Polygon} {M M' : Model}
    (h : ModelDescAt m D Q M) (h' : ModelDescAt m D Q M') : M = M' := by
  rcases h with ⟨h0, H, C, hC, rfl⟩ | ⟨h1, -, rfl⟩ <;>
    rcases h' with ⟨h0', H', C', hC', rfl⟩ | ⟨h1', -, rfl⟩
  · rw [chain_eq_of_desc hC hC']
  all_goals simp_all


end

/-- **The direction procedure meets its contract** (at most `5100` steps). -/
theorem locDir_ok : DirOK locDir 5100 LocDPre := by
  intro P W c hw ⟨hG, hW, hDW, hCW, M, hM, he⟩
  obtain ⟨c₁, k₁, e₁, hk₁, q32, q33, r₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.constN 50032 1, .loadN 50033 50000]) c c₁ k₁ ∧ k₁ = 2 ∧ c₁.nreg 50032 = 1 ∧
      c₁.nreg 50033 = c.nmem (c.nreg 50000) ∧
      (∀ r, r ≠ 50032 → r ≠ 50033 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem := by
    exec_block
    · omega
    · ram_simp
  obtain ⟨r₁, m₁⟩ := r₁
  have w₁ := e₁.wb_right
  have d₁ : c₁.nreg 50000 = c.nreg 50000 := r₁ _ (by omega) (by omega)
  have x₁ : c₁.nreg 50002 = c.nreg 50002 := r₁ _ (by omega) (by omega)
  suffices hmain : ∃ c' k, Exec P W locDir c c' k ∧ k ≤ 5100 ∧
      c'.nreg 10502 = dirCode M (c.nreg 50002) by
    obtain ⟨c', k, ex, hk, hd⟩ := hmain
    exact ⟨c', k, ex, hk, exec_frameB ex wr_locDir, fun M' hM' => by
      rw [hd, modelDesc_unique hM hM']⟩
  rcases hM with ⟨h0, H, C, hC, rfl⟩ | ⟨h1, hbit, rfl⟩
  · obtain ⟨hlen, hwf, hHW, hs, hNW⟩ := hCW h0 H C hC
    have he' : c₁.nreg 50002 < 2 * C.m + 7 := by
      rw [x₁]; simpa [chainModel, C.sideWalk_n] using he
    obtain ⟨c₂, k₂, e₂, hk₂, -, d₂⟩ := chainDir_exec (P := P) hG hW c₁ w₁ (H := H) (C := C)
      (by ram_simp) (by omega) (by omega_nf) hwf hs hNW
      he'
    refine ⟨c₂, _, .seq e₁ (.ifLtN_true (by omega) e₂), by omega, ?_⟩
    rw [d₂, x₁]
  · have he' : c₁.nreg 50002 < P.n := by
      rw [x₁]
      have := interiorWalk_n (Qof P)
      simp only [interiorModel] at he
      rw [this] at he
      have hn : (Qof P).n = P.n := shear_n _ _
      omega
    obtain ⟨c₂, k₂, e₂, hk₂, -, d₂⟩ := intDir_exec (P := P) hG hW c₁ w₁ he'
      (by omega) (by ram_simp)
    refine ⟨c₂, _, .seq e₁ (.ifLtN_false (by omega) e₂), by omega, ?_⟩
    rw [d₂, x₁]

/-! ## The specification -/

/-! ## Robust layouts are addressable -/

section
variable {E : ℕ} {m : ℕ → ℕ}
/-- A word that robustly holds a value lies below the bound. -/
theorem robust_addr {a v : ℕ} (h : Robust E m fun m' => m' a = v) :
    a < E := by
  by_contra hge
  have := h (Function.update m a (v + 1)) (fun b hb => by
    ram_simp)
  simp at this

/-- A word reached through a pointer that robustly holds a value: the pointer and the word lie
below the bound. -/
theorem robust_addr2 {b o v : ℕ}
    (h : Robust E m fun m' => m' (m' b + o) = v) : b < E ∧ m b + o < E := by
  have hb : b < E := by
    by_contra hge
    have hX : b ≠ E + b + 1 + o := by omega
    have := h (Function.update (Function.update m b (E + b + 1)) (E + b + 1 + o) (v + 1))
      (fun a ha => by
        ram_simp)
    simp_all
  refine ⟨hb, ?_⟩
  by_contra hge
  have := h (Function.update m (m b + o) (v + 1)) (fun a ha => by
    ram_simp)
  grind


end

/-- **A normal form readable below `E`** has its header, arc area and sequence table below
`E`. -/
theorem nfWithin_bounds {m : ℕ → ℕ} {B E : ℕ} {M : Model} {Q : Polygon} {N : NF}
    (h : NFWithin m B E N) (hNF : IsNF M Q N) (hA : 0 < N.arcs.length) :
    B + 7 ≤ E ∧ m (B + 4) + 5 * N.arcs.length ≤ E ∧ m (B + 6) + N.arcs.length ≤ E := by
  have hsl := seq_length hNF
  have h1 : Robust E m fun m' => m' (m' (B + 4) + 5 * (N.arcs.length - 1) + 4) =
      (N.arc (N.arcs.length - 1)).e.hgt := fun m' hm' =>
    ((h m' hm').2.2.2.2.2.2.1 _ (by omega)).2.2.2.2
  have h2 : Robust E m fun m' => m' (m' (B + 6) + (N.arcs.length - 1)) =
      N.seq.getD (N.arcs.length - 1) 0 := fun m' hm' =>
    (h m' hm').2.2.2.2.2.2.2.2.1 _ (by omega)
  have a1 := robust_addr2 (b := B + 4) (o := 5 * (N.arcs.length - 1) + 4)
    (by omega)
  have a2 := robust_addr2 h2
  omega

/-- A well-formed host of a chain of the geometry polygon has at most `64 n` points. -/
theorem chain_n_le {P : Polygon} {m : ℕ → ℕ} {B : ℕ} {H : Host} {C : Chain}
    (hC : ChainDescAt m B (Qof P) H C) (hlen : H.length ≤ 64) (hwf : HostWF P.n H) :
    C.P.n ≤ 64 * P.n := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  have e : C.P.n = (H.pts P.n).length := by
    rw [hC.2.1]
    show ((H.pts (Qof P).n).map (SymPt.eval (Qof P))).length = _
    simp_all
  rw [e]
  exact (Host.pts_length_le hwf).trans (Nat.mul_le_mul_right _ hlen)

/-- **The specification's descriptor conditions give the direction procedure's.** -/
theorem locChainWF_of {P : Polygon} {W E : ℕ} {m : ℕ → ℕ} {D : ℕ} (h : ModelDescWF P E m D)
    (hE : E ≤ W) (hW : hostWords P.n ≤ W) : D + 6 ≤ W ∧ LocChainWF P W m D := by
  refine ⟨by have := h.1; omega, fun h0 H C hC => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := (h.2 h0).2 H C hC
  have hN := chain_n_le hC h1 h2
  ram_grind

end

end NFLoc

end Chazelle.Core
