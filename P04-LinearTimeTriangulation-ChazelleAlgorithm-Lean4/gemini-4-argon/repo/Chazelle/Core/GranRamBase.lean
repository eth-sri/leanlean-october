module

public import Chazelle.Core.GranAlgo
public import Chazelle.Programs.Tactics

/-!
# WP-F, RAM part 1: the memory layout of the worklist state

The state `St` of the granularity procedure lives in one area of memory from the base `b0`
(the allocator at entry), with the dimensions `K` (chords), `A` (ring positions), `R` (regions,
the class ids) and `D` (the degree cap, the number of exit slots per class):

| offset | size | content |
|---|---|---|
| `0` | `K` | `live` |
| `oS0`, `oS1` | `K` each | `s0`, `s1` |
| `oNd0`, `oNd1` | `K` each | `nd0`, `nd1` |
| `oDeg`, `oWt` | `R` each | `deg`, `wt` |
| `oExb` | `R` | the absolute base `b0 + oEx + D x` of the exit slots of class `x` |
| `oEx` | `R D` | exit slots: `ex x t` at `oEx + D x + t` |
| `oCnt`, `oNxt`, `oPrv`, `oEg`, `oPz` | `A` each | ring data |
| `oStk` | `K + D K` | the worklist |
| `oTmp` | `D + 1` | scratch (not part of the state) |
| `oList` | `3 K` | the output chord list (not part of the state) |

`Enc m d st`: the memory `m` holds the state `st` in the layout `d` (one field per array); the
write lemmas `Enc.set_live`, … relate stores to updates of the fields.
-/

namespace Chazelle.Core

namespace Gran

@[expose] public section

/-- The dimensions and base of the layout. -/
structure Dm where
  K : ℕ
  A : ℕ
  R : ℕ
  D : ℕ
  b0 : ℕ

namespace Dm

variable (d : Dm)

def oS0 : ℕ := d.K
def oS1 : ℕ := 2 * d.K
def oNd0 : ℕ := 3 * d.K
def oNd1 : ℕ := 4 * d.K
def oDeg : ℕ := 5 * d.K
def oWt : ℕ := 5 * d.K + d.R
def oExb : ℕ := 5 * d.K + 2 * d.R
def oEx : ℕ := 5 * d.K + 3 * d.R
def oCnt : ℕ := d.oEx + d.R * d.D
def oNxt : ℕ := d.oCnt + d.A
def oPrv : ℕ := d.oNxt + d.A
def oEg : ℕ := d.oPrv + d.A
def oPz : ℕ := d.oEg + d.A
def oStk : ℕ := d.oPz + d.A
def cap : ℕ := d.K + d.D * d.K
def oTmp : ℕ := d.oStk + d.cap
def oList : ℕ := d.oTmp + d.D + 1
def oEnd : ℕ := d.oList + 3 * d.K

end Dm

/-- Unfold the layout offsets. -/
macro "dm_simp" : tactic =>
  `(tactic| simp (config := { failIfUnchanged := false }) only [Dm.oS0, Dm.oS1, Dm.oNd0, Dm.oNd1, Dm.oDeg, Dm.oWt, Dm.oExb, Dm.oEx,
    Dm.oCnt, Dm.oNxt, Dm.oPrv, Dm.oEg, Dm.oPz, Dm.oStk, Dm.cap, Dm.oTmp, Dm.oList,
    Dm.oEnd] at *)

/-- **The memory holds the state.** -/
structure Enc (m : ℕ → ℕ) (d : Dm) (st : St) : Prop where
  live : ∀ i, i < d.K → m (d.b0 + i) = st.live i
  s0 : ∀ i, i < d.K → m (d.b0 + d.oS0 + i) = st.s0 i
  s1 : ∀ i, i < d.K → m (d.b0 + d.oS1 + i) = st.s1 i
  nd0 : ∀ i, i < d.K → m (d.b0 + d.oNd0 + i) = st.nd0 i
  nd1 : ∀ i, i < d.K → m (d.b0 + d.oNd1 + i) = st.nd1 i
  deg : ∀ x, x < d.R → m (d.b0 + d.oDeg + x) = st.deg x
  wt : ∀ x, x < d.R → m (d.b0 + d.oWt + x) = st.wt x
  exb : ∀ x, x < d.R → m (d.b0 + d.oExb + x) = d.b0 + d.oEx + d.D * x
  ex : ∀ x t, x < d.R → t < d.D → m (d.b0 + d.oEx + d.D * x + t) = st.ex x t
  cnt : ∀ j, j < d.A → m (d.b0 + d.oCnt + j) = st.cnt j
  nxt : ∀ j, j < d.A → m (d.b0 + d.oNxt + j) = st.nxt j
  prv : ∀ j, j < d.A → m (d.b0 + d.oPrv + j) = st.prv j
  eg : ∀ j, j < d.A → m (d.b0 + d.oEg + j) = st.eg j
  pz : ∀ j, j < d.A → m (d.b0 + d.oPz + j) = st.pz j
  stk : ∀ t, t < d.cap → m (d.b0 + d.oStk + t) = st.stk t

variable {m : ℕ → ℕ} {d : Dm} {st : St}

/-! ## The slot arithmetic -/

theorem slot_lt {D x t R : ℕ} (hx : x < R) (ht : t < D) : D * x + t < R * D := by
  have : D * x + t < D * (x + 1) := by rw [Nat.mul_succ]; omega
  have : D * (x + 1) ≤ D * R := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.mul_comm R D]; omega

theorem slot_div {D x t : ℕ} (ht : t < D) : (D * x + t) / D = x := by
  have hD : 0 < D := by omega
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ hD, Nat.div_eq_of_lt ht, Nat.zero_add]

theorem slot_mod {D x t : ℕ} (ht : t < D) : (D * x + t) % D = t := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]

/-! ## Writing -/

/-- Store into `live`. -/
theorem Enc.set_live (h : Enc m d st) {k : ℕ} (hk : k < d.K) (v : ℕ) :
    Enc (upd m (d.b0 + k) v) d { st with live := Function.update st.live k v } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    by_cases hq : i = k
    · subst hq; simp
    · rw [Machine.upd_other _ _ _ (by omega)]
      dsimp only
      rw [Function.update_of_ne hq]
      exact h.live i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.s0 i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.s1 i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.nd0 i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.nd1 i hi
  · intro x hx
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.deg x hx
  · intro x hx
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.wt x hx
  · intro x hx
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.exb x hx
  · intro x t hx ht
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.ex x t hx ht
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.cnt j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.nxt j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.prv j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.eg j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.pz j hj
  · intro t ht
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.stk t ht

/-- Store into `s0`. -/
theorem Enc.set_s0 (h : Enc m d st) {k : ℕ} (hk : k < d.K) (v : ℕ) :
    Enc (upd m (d.b0 + d.oS0 + k) v) d { st with s0 := Function.update st.s0 k v } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.live i hi
  · intro i hi
    by_cases hq : i = k
    · subst hq; simp
    · rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
      dsimp only
      rw [Function.update_of_ne hq]
      exact h.s0 i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.s1 i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.nd0 i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.nd1 i hi
  · intro x hx
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.deg x hx
  · intro x hx
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.wt x hx
  · intro x hx
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.exb x hx
  · intro x t hx ht
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.ex x t hx ht
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.cnt j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.nxt j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.prv j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.eg j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.pz j hj
  · intro t ht
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.stk t ht

/-- Store into `s1`. -/
theorem Enc.set_s1 (h : Enc m d st) {k : ℕ} (hk : k < d.K) (v : ℕ) :
    Enc (upd m (d.b0 + d.oS1 + k) v) d { st with s1 := Function.update st.s1 k v } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.live i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.s0 i hi
  · intro i hi
    by_cases hq : i = k
    · subst hq; simp
    · rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
      dsimp only
      rw [Function.update_of_ne hq]
      exact h.s1 i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.nd0 i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.nd1 i hi
  · intro x hx
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.deg x hx
  · intro x hx
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.wt x hx
  · intro x hx
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.exb x hx
  · intro x t hx ht
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.ex x t hx ht
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.cnt j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.nxt j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.prv j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.eg j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.pz j hj
  · intro t ht
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.stk t ht

/-- Store into `deg`. -/
theorem Enc.set_deg (h : Enc m d st) {k : ℕ} (hk : k < d.R) (v : ℕ) :
    Enc (upd m (d.b0 + d.oDeg + k) v) d { st with deg := Function.update st.deg k v } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.live i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.s0 i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.s1 i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.nd0 i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.nd1 i hi
  · intro x hx
    by_cases hq : x = k
    · subst hq; simp
    · rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
      dsimp only
      rw [Function.update_of_ne hq]
      exact h.deg x hx
  · intro x hx
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.wt x hx
  · intro x hx
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.exb x hx
  · intro x t hx ht
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.ex x t hx ht
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.cnt j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.nxt j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.prv j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.eg j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.pz j hj
  · intro t ht
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.stk t ht

/-- Store into `wt`. -/
theorem Enc.set_wt (h : Enc m d st) {k : ℕ} (hk : k < d.R) (v : ℕ) :
    Enc (upd m (d.b0 + d.oWt + k) v) d { st with wt := Function.update st.wt k v } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.live i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.s0 i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.s1 i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.nd0 i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.nd1 i hi
  · intro x hx
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.deg x hx
  · intro x hx
    by_cases hq : x = k
    · subst hq; simp
    · rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
      dsimp only
      rw [Function.update_of_ne hq]
      exact h.wt x hx
  · intro x hx
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.exb x hx
  · intro x t hx ht
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.ex x t hx ht
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.cnt j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.nxt j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.prv j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.eg j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.pz j hj
  · intro t ht
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.stk t ht

/-- Store into `cnt`. -/
theorem Enc.set_cnt (h : Enc m d st) {k : ℕ} (hk : k < d.A) (v : ℕ) :
    Enc (upd m (d.b0 + d.oCnt + k) v) d { st with cnt := Function.update st.cnt k v } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.live i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.s0 i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.s1 i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.nd0 i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.nd1 i hi
  · intro x hx
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.deg x hx
  · intro x hx
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.wt x hx
  · intro x hx
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.exb x hx
  · intro x t hx ht
    have := slot_lt (R := d.R) hx ht
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.ex x t hx ht
  · intro j hj
    by_cases hq : j = k
    · subst hq; simp
    · rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
      dsimp only
      rw [Function.update_of_ne hq]
      exact h.cnt j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.nxt j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.prv j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.eg j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.pz j hj
  · intro t ht
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.stk t ht

/-- Store into `nxt`. -/
theorem Enc.set_nxt (h : Enc m d st) {k : ℕ} (hk : k < d.A) (v : ℕ) :
    Enc (upd m (d.b0 + d.oNxt + k) v) d { st with nxt := Function.update st.nxt k v } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.live i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.s0 i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.s1 i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.nd0 i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.nd1 i hi
  · intro x hx
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.deg x hx
  · intro x hx
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.wt x hx
  · intro x hx
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.exb x hx
  · intro x t hx ht
    have := slot_lt (R := d.R) hx ht
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.ex x t hx ht
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.cnt j hj
  · intro j hj
    by_cases hq : j = k
    · subst hq; simp
    · rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
      dsimp only
      rw [Function.update_of_ne hq]
      exact h.nxt j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.prv j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.eg j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.pz j hj
  · intro t ht
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.stk t ht

/-- Store into `prv`. -/
theorem Enc.set_prv (h : Enc m d st) {k : ℕ} (hk : k < d.A) (v : ℕ) :
    Enc (upd m (d.b0 + d.oPrv + k) v) d { st with prv := Function.update st.prv k v } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.live i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.s0 i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.s1 i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.nd0 i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.nd1 i hi
  · intro x hx
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.deg x hx
  · intro x hx
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.wt x hx
  · intro x hx
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.exb x hx
  · intro x t hx ht
    have := slot_lt (R := d.R) hx ht
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.ex x t hx ht
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.cnt j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.nxt j hj
  · intro j hj
    by_cases hq : j = k
    · subst hq; simp
    · rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
      dsimp only
      rw [Function.update_of_ne hq]
      exact h.prv j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.eg j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.pz j hj
  · intro t ht
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.stk t ht

/-- Store into `stk`. -/
theorem Enc.set_stk (h : Enc m d st) {k : ℕ} (hk : k < d.cap) (v : ℕ) :
    Enc (upd m (d.b0 + d.oStk + k) v) d { st with stk := Function.update st.stk k v } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.live i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.s0 i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.s1 i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.nd0 i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.nd1 i hi
  · intro x hx
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.deg x hx
  · intro x hx
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.wt x hx
  · intro x hx
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.exb x hx
  · intro x t hx ht
    have := slot_lt (R := d.R) hx ht
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.ex x t hx ht
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.cnt j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.nxt j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.prv j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.eg j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.pz j hj
  · intro t ht
    by_cases hq : t = k
    · subst hq; simp
    · rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
      dsimp only
      rw [Function.update_of_ne hq]
      exact h.stk t ht

/-- Store into an exit slot. -/
theorem Enc.set_ex (h : Enc m d st) {x₀ t₀ : ℕ} (hx₀ : x₀ < d.R) (ht₀ : t₀ < d.D) (v : ℕ) :
    Enc (upd m (d.b0 + d.oEx + d.D * x₀ + t₀) v) d
      { st with ex := fun x t => if x = x₀ ∧ t = t₀ then v else st.ex x t } := by
  have hs₀ := slot_lt (R := d.R) hx₀ ht₀
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.live i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.s0 i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.s1 i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.nd0 i hi
  · intro i hi
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.nd1 i hi
  · intro x hx
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.deg x hx
  · intro x hx
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.wt x hx
  · intro x hx
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.exb x hx
  · intro x t hx ht
    by_cases hq : x = x₀ ∧ t = t₀
    · obtain ⟨rfl, rfl⟩ := hq; simp
    · rw [Machine.upd_other _ _ _ ?_]
      · dsimp only; rw [ite_eq_right hq]; exact h.ex x t hx ht
      · intro he
        apply hq
        have e1 : d.D * x + t = d.D * x₀ + t₀ := by omega
        have e2 := congrArg (· / d.D) e1
        have e3 := congrArg (· % d.D) e1
        rw [slot_div ht, slot_div ht₀] at e2
        rw [slot_mod ht, slot_mod ht₀] at e3
        exact ⟨e2, e3⟩
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.cnt j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.nxt j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.prv j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.eg j hj
  · intro j hj
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.pz j hj
  · intro t ht
    rw [Machine.upd_other _ _ _ (by dm_simp; omega)]
    exact h.stk t ht

end

end Gran

end Chazelle.Core
