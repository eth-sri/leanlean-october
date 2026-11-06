module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.ClusterTables

/-!
# WP-I, part 27: marking the separator on the RAM

`markStmt`: for the corner `u` (register `130600`) of the centroid face, mark in `DF` the
ancestors of `u` in the primal tree whose level lies in the window `[lbot, ltop]` of the piece and
whose position `POS[w]` lies in the segment `[lo, hi)`:

* `t := min (LEV[u], ltop)`; if `t < lbot` nothing is marked;
* the ancestor `w` of `u` at level `t` by binary lifting (`ancLoop`, the table `UPT` of
  `ClusterTables.upStmt` for the parent array `PV`);
* `t + 1 - lbot` steps up from `w`, marking.

`markStmt_exec`: the new flags are `1` exactly at the positions of `lo ≤ POS[x] < hi` among
`up^[LEV[u] - t + i] u`, `i < t + 1 - lbot`; nothing else changes but `DF` and the scratch
registers.

Registers: `130300` `lo`, `130301` `hi`, `130600` `u`; static `130601` (`LEV`), `130602` (`UPT`),
`130603` (`POW`), `130604` (`L`), `130605` (`PV`), `130606` (`POS`), `130607` (`DF`), `130608`
(`μ`), `130609` `lbot`, `130610` `ltop`, `130620` (`UPT + L μ`); scratch `130611 … 130619`.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs

@[expose] public section

/-- One level of the ancestor search: `j := j - 1`, `row := row - μ`, jump if `2^j ≤ diff`. -/
def ancBody : Stmt := .seq (block [.subN 130614 130614 130001, .subN 130615 130615 130608,
    .addN 130618 130603 130614, .loadN 130618 130618])
  (.ifLtN 130613 130618 .skip (block [.addN 130619 130615 130616, .loadN 130616 130619,
    .subN 130613 130613 130618]))

/-- One step of the marking: mark `w` if `lo ≤ POS[w] < hi`, `w := PV[w]`, `cnt := cnt - 1`. -/
def markBody : Stmt := .seq (block [.addN 130618 130606 130616, .loadN 130618 130618])
  (.seq (.ifLtN 130618 130300 .skip (.ifLtN 130618 130301
      (block [.addN 130619 130607 130616, .storeN 130619 130001]) .skip))
    (block [.addN 130618 130605 130616, .loadN 130616 130618, .subN 130617 130617 130001]))

/-- The search for the ancestor at level `t` and the marking. -/
def markMain : Stmt := .seq (block [.subN 130613 130611 130612, .copyN 130616 130600,
    .copyN 130614 130604, .copyN 130615 130620])
  (.seq (.whileLtN 130009 130614 ancBody)
    (.seq (block [.subN 130617 130612 130609, .addN 130617 130617 130001])
      (.whileLtN 130009 130617 markBody)))

/-- **Marking the ancestors of `u` in the window of the piece.** -/
def markStmt : Stmt := .seq (block [.addN 130618 130601 130600, .loadN 130611 130618,
    .copyN 130612 130611])
  (.seq (.ifLtN 130610 130612 (.instr (.copyN 130612 130610)) .skip)
    (.ifLtN 130612 130609 .skip markMain))

/-- The scratch registers of the marking. -/
def MarkRG (r : ℕ) : Prop := 130611 ≤ r ∧ r ≤ 130619

/-- The static registers of the marking. -/
structure MarkCtx (c : Config) (lo hi bLEV bUPT bPOW L bPV bPOS bDF μ lbot ltop : ℕ) : Prop where
  one : c.nreg 130001 = 1
  zero : c.nreg 130009 = 0
  rlo : c.nreg 130300 = lo
  rhi : c.nreg 130301 = hi
  rLEV : c.nreg 130601 = bLEV
  rUPT : c.nreg 130602 = bUPT
  rPOW : c.nreg 130603 = bPOW
  rL : c.nreg 130604 = L
  rPV : c.nreg 130605 = bPV
  rPOS : c.nreg 130606 = bPOS
  rDF : c.nreg 130607 = bDF
  rμ : c.nreg 130608 = μ
  rbot : c.nreg 130609 = lbot
  rtop : c.nreg 130610 = ltop
  rend : c.nreg 130620 = bUPT + L * μ

theorem MarkCtx.of_frame {c c' : Config} {lo hi bLEV bUPT bPOW L bPV bPOS bDF μ lbot ltop : ℕ}
    (h : MarkCtx c lo hi bLEV bUPT bPOW L bPV bPOS bDF μ lbot ltop)
    (hr : ∀ r, ¬ MarkRG r → c'.nreg r = c.nreg r) :
    MarkCtx c' lo hi bLEV bUPT bPOW L bPV bPOS bDF μ lbot ltop := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [hr _ (by unfold MarkRG; omega)]; assumption)

/-- The static memory of the marking. -/
structure MarkMem (m : ℕ → ℕ) (W bLEV bUPT bPOW L bPV bPOS bDF μ : ℕ) (up : ℕ → ℕ) : Prop where
  up_lt : ∀ x, x < μ → up x < μ
  pv : ∀ x, x < μ → m (bPV + x) = up x
  tab : ∀ j, j < L → ∀ x, x < μ → m (bUPT + j * μ + x) = up^[2 ^ j] x
  pow : ∀ j, j < L → m (bPOW + j) = 2 ^ j
  lev_lt : ∀ x, x < μ → m (bLEV + x) < 2 ^ L
  lev_mu : ∀ x, x < μ → m (bLEV + x) < μ
  wLEV : bLEV + μ ≤ W
  wUPT : bUPT + L * μ ≤ W
  wPOW : bPOW + L ≤ W
  wPV : bPV + μ ≤ W
  wPOS : bPOS + μ ≤ W
  wDF : bDF + μ ≤ W
  -- `DF` is disjoint from what is read
  dLEV : bDF + μ ≤ bLEV ∨ bLEV + μ ≤ bDF
  dUPT : bDF + μ ≤ bUPT ∨ bUPT + L * μ ≤ bDF
  dPOW : bDF + μ ≤ bPOW ∨ bPOW + L ≤ bDF
  dPV : bDF + μ ≤ bPV ∨ bPV + μ ≤ bDF
  dPOS : bDF + μ ≤ bPOS ∨ bPOS + μ ≤ bDF

section proofs

variable {P : Polygon} {W : ℕ}

theorem iterate_lt_of {up : ℕ → ℕ} {μ : ℕ} (h : ∀ x, x < μ → up x < μ) (n : ℕ) {x : ℕ}
    (hx : x < μ) : up^[n] x < μ := by
  induction n generalizing x with
  | zero => exact hx
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih (h x hx)

/-- The registers written by the ancestor search. -/
def AncRG (r : ℕ) : Prop :=
  r = 130613 ∨ r = 130614 ∨ r = 130615 ∨ r = 130616 ∨ r = 130618 ∨ r = 130619

/-- **The ancestor search**: from `w = u` with `diff < 2^L`, the loop ends with
`w = up^[diff] u`. -/
theorem ancLoop_exec {c : Config} (hw : WordsBounded W c)
    {lo hi bLEV bUPT bPOW L bPV bPOS bDF μ lbot ltop : ℕ} {up : ℕ → ℕ}
    (hC : MarkCtx c lo hi bLEV bUPT bPOW L bPV bPOS bDF μ lbot ltop)
    (hM : MarkMem c.nmem W bLEV bUPT bPOW L bPV bPOS bDF μ up) {u d0 : ℕ} (hu : u < μ)
    (hd : c.nreg 130613 = d0) (hd0 : d0 < 2 ^ L) (hwu : c.nreg 130616 = u)
    (hj : c.nreg 130614 = L) (hrow : c.nreg 130615 = bUPT + L * μ) :
    ∃ c' k, Exec P W (.whileLtN 130009 130614 ancBody) c c' k ∧ k ≤ 12 * L + 2 ∧
      WordsBounded W c' ∧ c'.nmem = c.nmem ∧ (∀ r, ¬ AncRG r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      c'.nreg 130616 = up^[d0] u := by
  obtain ⟨c', k, e, ⟨hw', hm', hr', hrr', hrm', ho', j, hjL', hj', hrow', hdj, hwj, hwlt⟩, htest, hk⟩ :=
    whileLtN_pot (P := P) (W := W) (a := 130009) (b := 130614) (body := ancBody)
    (fun c2 => WordsBounded W c2 ∧ c2.nmem = c.nmem ∧ (∀ r, ¬ AncRG r → c2.nreg r = c.nreg r) ∧
      c2.rreg = c.rreg ∧ c2.rmem = c.rmem ∧ c2.output = c.output ∧ ∃ j, j ≤ L ∧
      c2.nreg 130614 = j ∧ c2.nreg 130615 = bUPT + j * μ ∧ c2.nreg 130613 < 2 ^ j ∧
      up^[c2.nreg 130613] (c2.nreg 130616) = up^[d0] u ∧ c2.nreg 130616 < μ)
    (fun c2 => 12 * c2.nreg 130614) (fun c2 h => h.1)
    (fun c2 ⟨hw2, hm2, hr2, hrr2, hrm2, ho2, j, hjL, hj2, hrow2, hdj, hwj, hwlt⟩ htest => by
      have hC2 := hC.of_frame (fun r hr => hr2 r (fun h => hr (by unfold AncRG at h; unfold MarkRG; omega)))
      rw [hC2.zero, hj2] at htest
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hrowj : bUPT + (j' + 1) * μ = bUPT + j' * μ + μ := by rw [Nat.succ_mul]; ring
      have hjLμ : j' * μ + μ ≤ L * μ := by
        have := Nat.mul_le_mul_right μ (show j' + 1 ≤ L by omega); rwa [Nat.succ_mul] at this
      have hpow := hM.pow j' (by omega)
      rw [← hm2] at hpow
      set w := c2.nreg 130616
      set df := c2.nreg 130613
      obtain ⟨c3, k3, e3, hk3, hw3, h3j, h3row, h3p, h3r, hrr3, hrm3, ho3, hm3⟩ : ∃ c3 k3,
          Exec P W (block [.subN 130614 130614 130001, .subN 130615 130615 130608,
            .addN 130618 130603 130614, .loadN 130618 130618]) c2 c3 k3 ∧ k3 = 4 ∧
          WordsBounded W c3 ∧ c3.nreg 130614 = j' ∧ c3.nreg 130615 = bUPT + j' * μ ∧
          c3.nreg 130618 = 2 ^ j' ∧
          (∀ r, r ≠ 130614 → r ≠ 130615 → r ≠ 130618 → c3.nreg r = c2.nreg r) ∧
          c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output ∧ c3.nmem = c2.nmem := by
        exec_block
        all_goals try (config_simp; simp only [hC2.rPOW, hC2.one, hj2]; have := hM.wPOW; omega)
        refine ⟨rfl, ‹_›, by config_simp; rw [hj2, hC2.one]; omega, by
          config_simp; rw [hrow2, hC2.rμ, hrowj]; omega, by
          config_simp; rw [hC2.rPOW, hj2, hC2.one, show j' + 1 - 1 = j' by omega]; exact hpow,
          fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
        simp only [Machine.upd_apply, h1, h2, h3, ite_false]
      have h3w : c3.nreg 130616 = w := h3r _ (by omega) (by omega) (by omega)
      have h3d : c3.nreg 130613 = df := h3r _ (by omega) (by omega) (by omega)
      have hframe3 : ∀ r, ¬ AncRG r → c3.nreg r = c.nreg r := fun r hr =>
        (h3r r (by unfold AncRG at hr; omega) (by unfold AncRG at hr; omega)
          (by unfold AncRG at hr; omega)).trans (hr2 r hr)
      by_cases hlt : c3.nreg 130613 < c3.nreg 130618
      · -- no jump
        refine ⟨c3, k3 + (0 + 1), .seq e3 (.ifLtN_true hlt (.skip hw3)), ⟨hw3, hm3.trans hm2,
          hframe3, hrr3.trans hrr2, hrm3.trans hrm2, ho3.trans ho2, j', by omega, h3j, h3row,
          ?_, ?_, ?_⟩, ?_⟩
        · rw [h3d]; rw [h3d, h3p] at hlt; exact hlt
        · rw [h3d, h3w]; exact hwj
        · rw [h3w]; exact hwlt
        · rw [h3j, hj2]; subst hk3; omega
      · -- the jump
        have hwμ := hwlt
        have htab := hM.tab j' (by omega) w hwμ
        rw [← hm2] at htab
        obtain ⟨c4, k4, e4, hk4, hw4, h4w, h4d, h4r, hrr4, hrm4, ho4, hm4⟩ : ∃ c4 k4,
            Exec P W (block [.addN 130619 130615 130616, .loadN 130616 130619,
              .subN 130613 130613 130618]) c3 c4 k4 ∧ k4 = 3 ∧ WordsBounded W c4 ∧
            c4.nreg 130616 = up^[2 ^ j'] w ∧ c4.nreg 130613 = df - 2 ^ j' ∧
            (∀ r, r ≠ 130613 → r ≠ 130616 → r ≠ 130619 → c4.nreg r = c3.nreg r) ∧
            c4.rreg = c3.rreg ∧ c4.rmem = c3.rmem ∧ c4.output = c3.output ∧
            c4.nmem = c3.nmem := by
          exec_block
          · rw [h3row, h3w]; have := hM.wUPT; omega
          · refine ⟨rfl, ‹_›, by config_simp; rw [h3row, h3w, hm3, htab], by
              config_simp; rw [h3d, h3p], fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
            simp only [Machine.upd_apply, h1, h2, h3, ite_false]
        rw [h3d, h3p] at hlt
        refine ⟨c4, k3 + (k4 + 2), .seq e3 (.ifLtN_false (by rw [h3d, h3p]; exact hlt) e4),
          ⟨hw4, hm4.trans (hm3.trans hm2), fun r hr => ?_, hrr4.trans (hrr3.trans hrr2),
          hrm4.trans (hrm3.trans hrm2), ho4.trans (ho3.trans ho2), j', by omega, ?_, ?_, ?_, ?_,
          ?_⟩, ?_⟩
        · rw [h4r r (by unfold AncRG at hr; omega) (by unfold AncRG at hr; omega)
            (by unfold AncRG at hr; omega)]
          exact hframe3 r hr
        · rw [h4r _ (by omega) (by omega) (by omega)]; exact h3j
        · rw [h4r _ (by omega) (by omega) (by omega)]; exact h3row
        · rw [h4d]; rw [pow_succ] at hdj; omega
        · rw [h4d, h4w, ← Function.iterate_add_apply, show df - 2 ^ j' + 2 ^ j' = df by omega]
          exact hwj
        · rw [h4w]; exact iterate_lt_of hM.up_lt _ hwμ
        · rw [h4r _ (by omega) (by omega) (by omega), h3j, hj2]; subst hk3 hk4; omega)
    ⟨hw, rfl, fun _ _ => rfl, rfl, rfl, rfl, L, le_rfl, hj, hrow, by rw [hd]; exact hd0,
      by rw [hd, hwu], by rw [hwu]; exact hu⟩
  have hC' := hC.of_frame (fun r hr => hr' r (fun h => hr (by unfold AncRG at h; unfold MarkRG; omega)))
  rw [hC'.zero, hj'] at htest
  have hj0 : j = 0 := by omega
  subst hj0
  have : c'.nreg 130613 = 0 := by simp at hdj; omega
  refine ⟨c', k, e, ?_, hw', hm', hr', hrr', hrm', ho', ?_⟩
  · rw [hj] at hk; omega
  · rw [this] at hwj; exact hwj

open Classical in
/-- The memory after marking the first `i` vertices `up^[i'] w0`, `i' < i`, found in `[lo, hi)`. -/
noncomputable def markMem (m : ℕ → ℕ) (bPOS bDF lo hi : ℕ) (up : ℕ → ℕ) (w0 i : ℕ) : ℕ → ℕ :=
  fun a => if ∃ x, a = bDF + x ∧ lo ≤ m (bPOS + x) ∧ m (bPOS + x) < hi ∧
    ∃ i', i' < i ∧ x = up^[i'] w0 then 1 else m a

/-- **The marking loop.** -/
theorem markLoop_exec {c : Config} (hw : WordsBounded W c)
    {lo hi bLEV bUPT bPOW L bPV bPOS bDF μ lbot ltop : ℕ} {up : ℕ → ℕ}
    (hC : MarkCtx c lo hi bLEV bUPT bPOW L bPV bPOS bDF μ lbot ltop)
    (hM : MarkMem c.nmem W bLEV bUPT bPOW L bPV bPOS bDF μ up) {w0 cnt : ℕ} (hw0 : w0 < μ)
    (hwr : c.nreg 130616 = w0) (hcnt : c.nreg 130617 = cnt) :
    ∃ c' k, Exec P W (.whileLtN 130009 130617 markBody) c c' k ∧ k ≤ 12 * cnt + 2 ∧
      WordsBounded W c' ∧ c'.nmem = markMem c.nmem bPOS bDF lo hi up w0 cnt ∧
      (∀ r, ¬ MarkRG r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  classical
  obtain ⟨c', k, e, ⟨hw', i, hile, hcnt', hw'', hwlt, hm', hr', hrr', hrm', ho'⟩, htest, hk⟩ :=
    whileLtN_pot (P := P) (W := W) (a := 130009) (b := 130617) (body := markBody)
    (fun c2 => WordsBounded W c2 ∧ ∃ i, i ≤ cnt ∧ c2.nreg 130617 = cnt - i ∧
      c2.nreg 130616 = up^[i] w0 ∧ up^[i] w0 < μ ∧
      c2.nmem = markMem c.nmem bPOS bDF lo hi up w0 i ∧
      (∀ r, ¬ MarkRG r → c2.nreg r = c.nreg r) ∧ c2.rreg = c.rreg ∧ c2.rmem = c.rmem ∧
      c2.output = c.output)
    (fun c2 => 12 * c2.nreg 130617) (fun c2 h => h.1)
    (fun c2 ⟨hw2, i, hile, hc2, hw2', hwlt, hm2, hr2, hrr2, hrm2, ho2⟩ htest => by
      have hC2 := hC.of_frame hr2
      rw [hC2.zero, hc2] at htest
      set w := up^[i] w0
      -- reads of the static arrays are unchanged by the marks
      have hread : ∀ b n, b + n ≤ bDF ∨ bDF + μ ≤ b → ∀ y, y < n →
          c2.nmem (b + y) = c.nmem (b + y) := by
        intro b n hb y hy
        rw [hm2]
        unfold markMem
        rw [ite_eq_right]
        rintro ⟨x, hx, -, -, i', -, rfl⟩
        have := iterate_lt_of hM.up_lt i' hw0
        omega
      have hpos : c2.nmem (bPOS + w) = c.nmem (bPOS + w) := hread _ _ hM.dPOS.symm w hwlt
      have hpv : c2.nmem (bPV + w) = up w := by
        rw [hread _ _ hM.dPV.symm w hwlt, hM.pv w hwlt]
      obtain ⟨c3, k3, e3, hk3, hw3, h3p, h3r, hrr3, hrm3, ho3, hm3⟩ : ∃ c3 k3, Exec P W
          (block [.addN 130618 130606 130616, .loadN 130618 130618]) c2 c3 k3 ∧ k3 = 2 ∧
          WordsBounded W c3 ∧ c3.nreg 130618 = c.nmem (bPOS + w) ∧
          (∀ r, r ≠ 130618 → c3.nreg r = c2.nreg r) ∧ c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧
          c3.output = c2.output ∧ c3.nmem = c2.nmem := by
        exec_block
        · rw [hC2.rPOS, hw2']; have := hM.wPOS; omega
        · refine ⟨rfl, ‹_›, by config_simp; rw [hC2.rPOS, hw2', hpos], fun r hr => ?_, rfl, rfl,
            rfl, rfl⟩
          simp only [Machine.upd_apply, hr, ite_false]
      have hC3 := hC2.of_frame (fun r hr => h3r r (by unfold MarkRG at hr; omega))
      have h3w : c3.nreg 130616 = w := (h3r _ (by omega)).trans hw2'
      have h3c : c3.nreg 130617 = cnt - i := (h3r _ (by omega)).trans hc2
      -- the conditional mark
      set inseg := c.nmem (bPOS + w)
      obtain ⟨c4, k4, e4, hk4, hw4, h4r, hrr4, hrm4, ho4, hm4⟩ : ∃ c4 k4, Exec P W
          (.ifLtN 130618 130300 .skip (.ifLtN 130618 130301
            (block [.addN 130619 130607 130616, .storeN 130619 130001]) .skip)) c3 c4 k4 ∧
          k4 ≤ 5 ∧ WordsBounded W c4 ∧ (∀ r, r ≠ 130619 → c4.nreg r = c3.nreg r) ∧
          c4.rreg = c3.rreg ∧ c4.rmem = c3.rmem ∧ c4.output = c3.output ∧
          c4.nmem = if lo ≤ inseg ∧ inseg < hi then upd c3.nmem (bDF + w) 1 else c3.nmem := by
        by_cases h1 : c3.nreg 130618 < c3.nreg 130300
        · refine ⟨c3, 0 + 1, .ifLtN_true h1 (.skip hw3), by omega, hw3, fun _ _ => rfl, rfl, rfl,
            rfl, ?_⟩
          rw [ite_eq_right]; rw [h3p, hC3.rlo] at h1; omega
        · by_cases h2 : c3.nreg 130618 < c3.nreg 130301
          · obtain ⟨c5, k5, e5, hk5, hw5, h5r, hrr5, hrm5, ho5, hm5⟩ : ∃ c5 k5, Exec P W
                (block [.addN 130619 130607 130616, .storeN 130619 130001]) c3 c5 k5 ∧ k5 = 2 ∧
                WordsBounded W c5 ∧ (∀ r, r ≠ 130619 → c5.nreg r = c3.nreg r) ∧
                c5.rreg = c3.rreg ∧ c5.rmem = c3.rmem ∧ c5.output = c3.output ∧
                c5.nmem = upd c3.nmem (bDF + w) 1 := by
              exec_block
              · rw [hC3.rDF, h3w]; have := hM.wDF; omega
              · refine ⟨rfl, ‹_›, fun r hr => ?_, rfl, rfl, rfl, ?_⟩
                · simp only [Machine.upd_apply, hr, ite_false]
                · config_simp; rw [hC3.rDF, h3w, hC3.one]
            refine ⟨c5, k5 + 1 + 2, .ifLtN_false h1 (.ifLtN_true h2 e5), by omega, hw5, h5r,
              hrr5, hrm5, ho5, ?_⟩
            rw [ite_eq_left]; · exact hm5
            rw [h3p, hC3.rlo] at h1; rw [h3p, hC3.rhi] at h2; omega
          · refine ⟨c3, 0 + 2 + 2, .ifLtN_false h1 (.ifLtN_false h2 (.skip hw3)), by omega, hw3,
              fun _ _ => rfl, rfl, rfl, rfl, ?_⟩
            rw [ite_eq_right]; rw [h3p, hC3.rhi] at h2; omega
      have h4w : c4.nreg 130616 = w := (h4r _ (by omega)).trans h3w
      have h4c : c4.nreg 130617 = cnt - i := (h4r _ (by omega)).trans h3c
      have hC4 := hC3.of_frame (fun r hr => h4r r (by unfold MarkRG at hr; omega))
      have hpv4 : c4.nmem (bPV + w) = up w := by
        rw [hm4]
        split_ifs
        · rw [Machine.upd_other _ _ _ (by have := hM.dPV; omega), hm3, hpv]
        · rw [hm3, hpv]
      obtain ⟨c5, k5, e5, hk5, hw5, h5w, h5c, h5r, hrr5, hrm5, ho5, hm5⟩ : ∃ c5 k5, Exec P W
          (block [.addN 130618 130605 130616, .loadN 130616 130618, .subN 130617 130617 130001])
          c4 c5 k5 ∧ k5 = 3 ∧ WordsBounded W c5 ∧ c5.nreg 130616 = up w ∧
          c5.nreg 130617 = cnt - i - 1 ∧
          (∀ r, r ≠ 130616 → r ≠ 130617 → r ≠ 130618 → c5.nreg r = c4.nreg r) ∧
          c5.rreg = c4.rreg ∧ c5.rmem = c4.rmem ∧ c5.output = c4.output ∧ c5.nmem = c4.nmem := by
        exec_block
        · rw [hC4.rPV, h4w]; have := hM.wPV; omega
        · refine ⟨rfl, ‹_›, by config_simp; rw [hC4.rPV, h4w, hpv4], by
            config_simp; rw [h4c, hC4.one], fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
          simp only [Machine.upd_apply, h1, h2, h3, ite_false]
      refine ⟨c5, k3 + (k4 + k5), .seq e3 (.seq e4 e5), ⟨hw5, i + 1, by omega, by rw [h5c]; omega,
        by rw [h5w, Function.iterate_succ_apply'], by
          rw [Function.iterate_succ_apply']; exact hM.up_lt _ hwlt, ?_, fun r hr => ?_,
        hrr5.trans (hrr4.trans (hrr3.trans hrr2)), hrm5.trans (hrm4.trans (hrm3.trans hrm2)),
        ho5.trans (ho4.trans (ho3.trans ho2))⟩, ?_⟩
      · rw [hm5, hm4, hm3, hm2]
        funext a
        unfold markMem
        by_cases hseg : lo ≤ inseg ∧ inseg < hi
        · rw [ite_eq_left hseg, Machine.upd_apply]
          by_cases ha : a = bDF + w
          · rw [ite_eq_left ha, ite_eq_left ⟨w, ha, hseg.1, hseg.2, i, by omega, rfl⟩]
          · rw [ite_eq_right ha]
            by_cases hex : ∃ x, a = bDF + x ∧ lo ≤ c.nmem (bPOS + x) ∧ c.nmem (bPOS + x) < hi ∧
                ∃ i', i' < i ∧ x = up^[i'] w0
            · rw [ite_eq_left hex, ite_eq_left (by
                obtain ⟨x, h1, h2, h3, i', h4, h5⟩ := hex
                exact ⟨x, h1, h2, h3, i', by omega, h5⟩)]
            · rw [ite_eq_right hex, ite_eq_right]
              rintro ⟨x, h1, h2, h3, i', h4, h5⟩
              rcases Nat.lt_succ_iff_lt_or_eq.mp h4 with h4 | rfl
              · exact hex ⟨x, h1, h2, h3, i', h4, h5⟩
              · exact ha (by rw [h1, h5])
        · rw [ite_eq_right hseg]
          by_cases hex : ∃ x, a = bDF + x ∧ lo ≤ c.nmem (bPOS + x) ∧ c.nmem (bPOS + x) < hi ∧
              ∃ i', i' < i ∧ x = up^[i'] w0
          · rw [ite_eq_left hex, ite_eq_left (by
              obtain ⟨x, h1, h2, h3, i', h4, h5⟩ := hex
              exact ⟨x, h1, h2, h3, i', by omega, h5⟩)]
          · rw [ite_eq_right hex, ite_eq_right]
            rintro ⟨x, h1, h2, h3, i', h4, h5⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp h4 with h4 | rfl
            · exact hex ⟨x, h1, h2, h3, i', h4, h5⟩
            · rw [h5] at h2 h3; exact hseg ⟨h2, h3⟩
      · rw [h5r r (by unfold MarkRG at hr; omega) (by unfold MarkRG at hr; omega)
          (by unfold MarkRG at hr; omega), h4r r (by unfold MarkRG at hr; omega),
          h3r r (by unfold MarkRG at hr; omega)]
        exact hr2 r hr
      · rw [h5c, hc2]; subst hk3 hk5; omega)
    ⟨hw, 0, Nat.zero_le _, by rw [hcnt]; rfl, hwr, hw0, by
      funext a; unfold markMem; rw [ite_eq_right]; rintro ⟨x, -, -, -, i', hi', -⟩; omega,
      fun _ _ => rfl, rfl, rfl, rfl⟩
  have hC' := hC.of_frame hr'
  rw [hC'.zero, hcnt'] at htest
  have hic : i = cnt := by omega
  subst hic
  refine ⟨c', k, e, ?_, hw', hm', hr', hrr', hrm', ho'⟩
  rw [hcnt] at hk; omega

/-- **Marking the ancestors of the corner `u`.** -/
theorem markStmt_exec {c : Config} (hw : WordsBounded W c)
    {lo hi bLEV bUPT bPOW L bPV bPOS bDF μ lbot ltop : ℕ} {up : ℕ → ℕ}
    (hC : MarkCtx c lo hi bLEV bUPT bPOW L bPV bPOS bDF μ lbot ltop)
    (hM : MarkMem c.nmem W bLEV bUPT bPOW L bPV bPOS bDF μ up) {u : ℕ}
    (hu : c.nreg 130600 = u) (huμ : u < μ) :
    ∃ c' k, Exec P W markStmt c c' k ∧ k ≤ 12 * L + 12 * (ltop + 1 - lbot) + 30 ∧
      WordsBounded W c' ∧
      c'.nmem = (if lbot ≤ min (c.nmem (bLEV + u)) ltop then
        markMem c.nmem bPOS bDF lo hi up (up^[c.nmem (bLEV + u) - min (c.nmem (bLEV + u)) ltop] u)
          (min (c.nmem (bLEV + u)) ltop + 1 - lbot) else c.nmem) ∧
      (∀ r, ¬ MarkRG r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  set lu := c.nmem (bLEV + u)
  set t := min lu ltop
  have hlu : lu < 2 ^ L := hM.lev_lt u huμ
  -- `lu` and `t`
  obtain ⟨c1, k1, e1, hk1, hw1, h1l, h1t, h1r, hrr1, hrm1, ho1, hm1⟩ : ∃ c1 k1, Exec P W
      (block [.addN 130618 130601 130600, .loadN 130611 130618, .copyN 130612 130611]) c c1 k1 ∧
      k1 = 3 ∧ WordsBounded W c1 ∧ c1.nreg 130611 = lu ∧ c1.nreg 130612 = lu ∧
      (∀ r, ¬ MarkRG r → c1.nreg r = c.nreg r) ∧ c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧
      c1.output = c.output ∧ c1.nmem = c.nmem := by
    exec_block
    · rw [hC.rLEV, hu]; have := hM.wLEV; omega
    · refine ⟨rfl, ‹_›, by config_simp; rw [hC.rLEV, hu], by config_simp; rw [hC.rLEV, hu],
        fun r hr => ?_, rfl, rfl, rfl, rfl⟩
      simp only [Machine.upd_apply]; unfold MarkRG at hr; split_ifs <;> omega
  have hC1 := hC.of_frame h1r
  obtain ⟨c2, k2, e2, hk2, hw2, h2l, h2t, h2r, hrr2, hrm2, ho2, hm2⟩ : ∃ c2 k2, Exec P W
      (.ifLtN 130610 130612 (.instr (.copyN 130612 130610)) .skip) c1 c2 k2 ∧ k2 ≤ 2 ∧
      WordsBounded W c2 ∧ c2.nreg 130611 = lu ∧ c2.nreg 130612 = t ∧
      (∀ r, ¬ MarkRG r → c2.nreg r = c1.nreg r) ∧ c2.rreg = c1.rreg ∧ c2.rmem = c1.rmem ∧
      c2.output = c1.output ∧ c2.nmem = c1.nmem := by
    by_cases h : c1.nreg 130610 < c1.nreg 130612
    · have ec := Exec.copyN (P := P) hw1 130612 130610
      refine ⟨_, _, .ifLtN_true h ec, le_refl _, ec.wb_right, by simp [h1l], ?_, fun r hr => ?_,
        rfl, rfl, rfl, rfl⟩
      · simp only [Machine.upd_same, hC1.rtop]
        rw [hC1.rtop, h1t] at h; simp only [t]; omega
      · simp only [Machine.upd_apply]; unfold MarkRG at hr; split_ifs <;> omega
    · refine ⟨c1, _, .ifLtN_false h (.skip hw1), by omega, hw1, h1l, ?_, fun _ _ => rfl, rfl,
        rfl, rfl, rfl⟩
      rw [h1t]; rw [hC1.rtop, h1t] at h; simp only [t]; omega
  have hC2 := hC1.of_frame h2r
  have hframe2 : ∀ r, ¬ MarkRG r → c2.nreg r = c.nreg r := fun r hr =>
    (h2r r hr).trans (h1r r hr)
  by_cases hbot : c2.nreg 130612 < c2.nreg 130609
  · -- nothing to mark
    refine ⟨c2, k1 + (k2 + (0 + 1)), .seq e1 (.seq e2 (.ifLtN_true hbot (.skip hw2))),
      by omega, hw2, ?_, hframe2, hrr2.trans hrr1, hrm2.trans hrm1, ho2.trans ho1⟩
    rw [h2t, hC2.rbot] at hbot
    rw [ite_eq_right (by omega), hm2, hm1]
  · have htb : lbot ≤ t := by rw [h2t, hC2.rbot] at hbot; omega
    have hm21 : c2.nmem = c.nmem := hm2.trans hm1
    obtain ⟨c3, k3, e3, hk3, hw3, h3d, h3w, h3j, h3row, h3t, h3r, hrr3, hrm3, ho3, hm3⟩ :
        ∃ c3 k3, Exec P W (block [.subN 130613 130611 130612, .copyN 130616 130600,
          .copyN 130614 130604, .copyN 130615 130620]) c2 c3 k3 ∧ k3 = 4 ∧ WordsBounded W c3 ∧
        c3.nreg 130613 = lu - t ∧ c3.nreg 130616 = u ∧ c3.nreg 130614 = L ∧
        c3.nreg 130615 = bUPT + L * μ ∧ c3.nreg 130612 = t ∧
        (∀ r, ¬ MarkRG r → c3.nreg r = c2.nreg r) ∧
        c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output ∧ c3.nmem = c2.nmem := by
      exec_block
      refine ⟨rfl, ‹_›, by config_simp; rw [h2l, h2t], by config_simp; rw [hframe2 _ (by
        unfold MarkRG; omega), hu], by config_simp; exact hC2.rL, by config_simp; exact hC2.rend,
        by config_simp; exact h2t, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
      simp only [Machine.upd_apply]; unfold MarkRG at hr; split_ifs <;> omega
    have hC3 := hC2.of_frame h3r
    have hM3 : MarkMem c3.nmem W bLEV bUPT bPOW L bPV bPOS bDF μ up := by
      rw [hm3, hm21]; exact hM
    obtain ⟨c4, k4, e4, hk4, hw4, hm4, h4r, hrr4, hrm4, ho4, h4w⟩ := ancLoop_exec (P := P) hw3 hC3
      hM3 huμ h3d (by omega) h3w h3j h3row
    have hA4 : ∀ r, ¬ MarkRG r → ¬ AncRG r := fun r hr h => hr (by
      unfold AncRG at h; unfold MarkRG; omega)
    have hC4 := hC3.of_frame (fun r hr => h4r r (hA4 r hr))
    have h4t : c4.nreg 130612 = t := (h4r _ (by unfold AncRG; omega)).trans h3t
    obtain ⟨c5, k5, e5, hk5, hw5, h5c, h5w, h5r, hrr5, hrm5, ho5, hm5⟩ : ∃ c5 k5, Exec P W
        (block [.subN 130617 130612 130609, .addN 130617 130617 130001]) c4 c5 k5 ∧ k5 = 2 ∧
        WordsBounded W c5 ∧ c5.nreg 130617 = t + 1 - lbot ∧ c5.nreg 130616 = up^[lu - t] u ∧
        (∀ r, ¬ MarkRG r → c5.nreg r = c4.nreg r) ∧ c5.rreg = c4.rreg ∧ c5.rmem = c4.rmem ∧
        c5.output = c4.output ∧ c5.nmem = c4.nmem := by
      exec_block
      · config_simp; rw [h4t, hC4.rbot, hC4.one]; have := hM.wLEV; have := hM.lev_mu u huμ
        simp only [t]; omega
      · refine ⟨rfl, ‹_›, by config_simp; rw [h4t, hC4.rbot, hC4.one]; omega,
          by config_simp; exact h4w, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
        simp only [Machine.upd_apply]; unfold MarkRG at hr; split_ifs <;> omega
    have hC5 := hC4.of_frame h5r
    have hM5 : MarkMem c5.nmem W bLEV bUPT bPOW L bPV bPOS bDF μ up := by
      rw [hm5, hm4]; exact hM3
    obtain ⟨c6, k6, e6, hk6, hw6, hm6, h6r, hrr6, hrm6, ho6⟩ := markLoop_exec (P := P) hw5 hC5 hM5
      (iterate_lt_of hM.up_lt _ huμ) h5w h5c
    refine ⟨c6, _, .seq e1 (.seq e2 (.ifLtN_false hbot (.seq e3 (.seq e4 (.seq e5 e6))))), ?_,
      hw6, ?_,
      fun r hr => ?_, ?_, ?_, ?_⟩
    · have : t + 1 - lbot ≤ ltop + 1 - lbot := by simp only [t]; omega
      subst hk1 hk3 hk5; omega
    · rw [ite_eq_left htb, hm6, hm5, hm4, hm3, hm21]
    · rw [h6r r hr, h5r r hr, h4r r (hA4 r hr), h3r r hr]; exact hframe2 r hr
    · rw [hrr6, hrr5, hrr4, hrr3, hrr2, hrr1]
    · rw [hrm6, hrm5, hrm4, hrm3, hrm2, hrm1]
    · rw [ho6, ho5, ho4, ho3, ho2, ho1]

end proofs

end

end Chazelle.Core.Cluster
