module

public import Chazelle.Golf

public import Chazelle.Core.NFLocateDir

/-!
# Reading a host polygon on the RAM (WP-C, target 2: chain model)

The chain model of a chain `C` of a host polygon `H.poly Q` (`HostAt` layout: the number of
items, then three words per item) needs the symbolic points of `H` at given indices.  Two loops
over the items (at most `64` in the down phase, `HostOk`):

* `cntLoop`: the number `N = (H.pts n).length` of symbolic points (`cnt_exec`);
* `lookLoop`: the symbolic point of index `p < N` (`look_exec`), into `lr 46 … lr 48`
  (`SymPtIn` layout).

Well-formedness needed (`HostWF`): runs `run a ℓ` with `a, ℓ < n` (so that `(a + k) mod n` is
one conditional subtraction), points in range (`SymPt.Lt n`, for the sign kernel).

Registers: `lr 60` the host handle, `lr 61` the number of items, `lr 62` the item index, `lr 63`
the running count, `lr 64` the address of the item, `lr 65 … lr 76` scratch, `lr 67 = 1`,
`lr 68 = 2`, `lr 69 = 3`, `lr 71` the target index.
-/

namespace Chazelle.Core

namespace NFLoc

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-! ## Hosts as lists -/

/-- The number of symbolic points of a host item. -/
def itemCnt : HostItem → ℕ
  | .run _ ℓ => ℓ + 1
  | .pt _ => 1

theorem pts_length_item (n : ℕ) (it : HostItem) : (it.pts n).length = itemCnt it := by
  cases it <;> Θ HostItem.pts, itemCnt

/-- The number of symbolic points of the first `i` items. -/
def preLen (n : ℕ) (H : Host) (i : ℕ) : ℕ := ((H.take i).flatMap (HostItem.pts n)).length

theorem preLen_zero (n : ℕ) (H : Host) : preLen n H 0 = 0 := ⊚ preLen

theorem preLen_succ (n : ℕ) (H : Host) {i : ℕ} (hi : i < H.length) :
    preLen n H (i + 1) = preLen n H i + itemCnt H[i] := by
  unfold preLen
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.flatMap_append,
    List.length_append]
  Θ pts_length_item

theorem preLen_length (n : ℕ) (H : Host) : preLen n H H.length = (H.pts n).length := by
  unfold preLen Host.pts
  Ξ List.take_length

theorem preLen_le_succ (n : ℕ) (H : Host) (i : ℕ) : preLen n H i ≤ preLen n H (i + 1) := by
  by_cases hi : i < H.length
  · rw [preLen_succ n H hi]; omega
  · unfold preLen
    Ξ List.take_of_length_le (⋄), List.take_of_length_le (⋄)

theorem preLen_mono (n : ℕ) (H : Host) {i j : ℕ} (hij : i ≤ j) : preLen n H i ≤ preLen n H j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact ih.trans (preLen_le_succ n H j)

/-- **The point of index `p`** lies in item `i` when `p` is in its range. -/
theorem pts_getElem? (n : ℕ) (H : Host) {i p : ℕ} (hi : i < H.length) (h1 : preLen n H i ≤ p)
    (h2 : p < preLen n H i + itemCnt H[i]) :
    (H.pts n)[p]? = (H[i].pts n)[p - preLen n H i]? := by
  have e : H.pts n = (H.take i).flatMap (HostItem.pts n) ++
      (H[i].pts n ++ (H.drop (i + 1)).flatMap (HostItem.pts n)) := by
    unfold Host.pts
    conv_lhs => rw [← List.take_append_drop i H, List.drop_eq_getElem_cons hi]
    Ξ List.flatMap_append, List.flatMap_cons
  unfold preLen at h1 h2 ⊢
  Ξ e, List.getElem?_append_right h1, List.getElem?_append_left
  Ξ pts_length_item
  omega

/-- The points of a run. -/
theorem run_pts_getElem? (n a ℓ : ℕ) {k : ℕ} (hk : k ≤ ℓ) :
    ((HostItem.run a ℓ).pts n)[k]? = some (SymPt.vtx ((a + k) % n)) := by
  Θ HostItem.pts, List.getElem?_map, List.getElem?_range (by omega : k < ℓ + 1)

/-! ## Decoding the layout -/

/-- The item coded by the words `k, a, b`. -/
def itemOf (k a b : ℕ) : HostItem :=
  if k = 0 then .run a b else if k = 1 then .pt (.vtx a) else .pt (.onEdge a b)

/-- **The layout determines the items.** -/
theorem hostAt_item {m : ℕ → ℕ} {B : ℕ} {H : Host} (h : HostAt m B H) {i : ℕ}
    (hi : i < H.length) :
    H[i] = itemOf (m (B + 1 + 3 * i)) (m (B + 2 + 3 * i)) (m (B + 3 + 3 * i)) ∧
      m (B + 1 + 3 * i) ≤ 2 := by
  have hh := h.2 i hi
  Ξ' getD_of_lt _ hi at hh
  generalize H[i] = it at hh ⊢
  cases it with
  | run a l =>
    obtain ⟨h1, h2, h3⟩ := hh
    Θ itemOf, h1, h2, h3
  | pt x =>
    cases x with
    | vtx j =>
      obtain ⟨h1, h2⟩ := hh
      Θ itemOf, h1, h2
    | onEdge e hh' =>
      obtain ⟨h1, h2, h3⟩ := hh
      Θ itemOf, h1, h2, h3

/-- The layout determines the host. -/
theorem hostAt_unique {m : ℕ → ℕ} {B : ℕ} {H H' : Host} (h : HostAt m B H)
    (h' : HostAt m B H') : H = H' := by
  have hl : H.length = H'.length := h.1.symm.trans h'.1
  apply List.ext_getElem hl
  intro i hi hi'
  Ξ (hostAt_item h hi).1, (hostAt_item h' hi').1

/-- The count of the item coded by `k, a, b`, as the machine computes it. -/
theorem itemCnt_itemOf (k a b : ℕ) : itemCnt (itemOf k a b) = if k < 1 then b + 1 else 1 := by
  unfold itemOf
  split_ifs <;> first | omega | rfl

/-- All symbolic points of a well-formed host are in range. -/
theorem hostWF_pts {n : ℕ} {H : Host} (h : HostWF n H) (hn : 0 < n) :
    ∀ x ∈ H.pts n, x.Lt n := by
  intro x hx
  unfold Host.pts at hx
  obtain ⟨it, hit, hx⟩ := List.mem_flatMap.1 hx
  have := h it hit
  cases it with
  | run a l =>
    ϴ' HostItem.pts, List.mem_map, List.mem_range at hx
    obtain ⟨k, -, rfl⟩ := hx
    exact Nat.mod_lt _ hn
  | pt y =>
    ϴ' HostItem.pts, List.mem_singleton at hx
    subst hx
    exact this

/-! ## Counting the points -/

/-- One item of the count. -/
def cntBody : Stmt :=
  .seq (.instr (.loadN 50065 50064))
    (.seq (.ifLtN 50065 50067 (block [.addN 50070 50064 50068, .loadN 50066 50070,
        .addN 50063 50063 50066, .addN 50063 50063 50067])
      (.instr (.addN 50063 50063 50067)))
      (block [.addN 50062 50062 50067, .addN 50064 50064 50069]))

/-- Constants, `i := 0`, count `:= 0`, address of item `0`. -/
def hostInit : Stmt := block [.constN 50067 1, .constN 50068 2, .constN 50069 3,
  .loadN 50061 50060, .constN 50062 0, .constN 50063 0, .addN 50064 50060 50067]

/-- **The number of symbolic points of the host at `lr 60`**, into `lr 63`. -/
def cntStmt : Stmt := .seq hostInit (.whileLtN 50062 50061 cntBody)

/-- The registers written by the host routines. -/
def Bhost (r : ℕ) : Bool := decide (50046 ≤ r ∧ r < 50049) || decide (50061 ≤ r ∧ r < 50077)

theorem wr_cntStmt : wr Bhost cntStmt = true := ⌖

/-- The facts the host loops keep. -/
structure HostEnv (W Hh len : ℕ) (m : ℕ → ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  h60 : c.nreg 50060 = Hh
  h61 : c.nreg 50061 = len
  h67 : c.nreg 50067 = 1
  h68 : c.nreg 50068 = 2
  h69 : c.nreg 50069 = 3
  mem : c.nmem = m

/-- One step of the count. -/
theorem cntBody_exec {P : Polygon} {W : ℕ} {Hh len : ℕ} {m : ℕ → ℕ} {c : Config}
    (h : HostEnv W Hh len m c) {i : ℕ} (hi : c.nreg 50062 = i) (hil : i < len)
    (ha : c.nreg 50064 = Hh + 1 + 3 * i) (haW : Hh + 3 * len + 4 ≤ W)
    (hacc : c.nreg 50063 + (if m (Hh + 1 + 3 * i) < 1 then m (Hh + 3 + 3 * i) + 1 else 1) ≤ W) :
    ∃ c' k, Exec P W cntBody c c' k ∧ k ≤ 10 ∧ HostEnv W Hh len m c' ∧
      c'.nreg 50062 = i + 1 ∧ c'.nreg 50064 = Hh + 1 + 3 * (i + 1) ∧
      c'.nreg 50063 = c.nreg 50063 +
        (if m (Hh + 1 + 3 * i) < 1 then m (Hh + 3 + 3 * i) + 1 else 1) ∧
      (∀ r, (r < 50061 ∨ 50077 ≤ r) → c'.nreg r = c.nreg r) := by
  have hw := h.wb
  have h60 := h.h60
  have h61 := h.h61
  have h67 := h.h67
  have h68 := h.h68
  have h69 := h.h69
  have hm := h.mem
  have ad : Hh + 1 + 3 * i + 2 = Hh + 3 + 3 * i := ⋄
  unfold cntBody
  refine spec_seq (spec_instr (Exec.loadN hw 50065 50064) fun hw₁ => ?_)
  by_cases hk : m (Hh + 1 + 3 * i) < 1
  · Ξ' ite_eq_left hk at hacc ⊢
    refine spec_seq (spec_ifLtN_true (by config_simp; rw [ha, hm, h67]; exact hk) ?_)
    exec_block
    · config_simp; rw [ha, h68]; omega
    · config_simp; rw [ha, h68, hm, ad]; omega
    · config_simp; rw [ha, h68, hm, ad, h67]; omega
    · config_simp; rw [hi, h67]; omega
    · config_simp; rw [ha, h69]; omega
    refine ⟨⋄, ⟨‹_›, by config_simp; exact h60, by config_simp; exact h61,
      by config_simp; exact h67, by config_simp; exact h68, by config_simp; exact h69,
      by config_simp; exact hm⟩, by config_simp; rw [hi, h67], by config_simp; rw [ha, h69]; ring,
      by config_simp; rw [ha, h68, hm, ad, h67]; ring, fun r hr => ?_⟩
    ϴ upd
    split_ifs <;> first | rfl | omega
  · Ξ' ite_eq_right hk at hacc ⊢
    refine spec_seq (spec_ifLtN_false (by config_simp; rw [ha, hm, h67]; exact hk)
      (spec_instr (Exec.addN hw₁ _ _ _ (by config_simp; rw [h67]; omega)) fun hw₂ => ?_))
    exec_block
    · config_simp; rw [hi, h67]; omega
    · config_simp; rw [ha, h69]; omega
    refine ⟨⋄, ⟨‹_›, by config_simp; exact h60, by config_simp; exact h61,
      by config_simp; exact h67, by config_simp; exact h68, by config_simp; exact h69,
      by config_simp; exact hm⟩, by config_simp; rw [hi, h67], by config_simp; rw [ha, h69]; ring,
      by config_simp; rw [h67], fun r hr => ?_⟩
    ϴ upd
    split_ifs <;> first | rfl | omega

/-- The count the machine adds for item `i` is the number of its points. -/
theorem machineCnt_eq {m : ℕ → ℕ} {Hh : ℕ} {H : Host} (hH : HostAt m Hh H) {i : ℕ}
    (hi : i < H.length) :
    (if m (Hh + 1 + 3 * i) < 1 then m (Hh + 3 + 3 * i) + 1 else 1) = itemCnt H[i] := by
  Ξ (hostAt_item hH hi).1, itemCnt_itemOf

/-- **The count of the symbolic points of a host** (at most `12 |H| + 12` steps). -/
theorem cnt_exec {P : Polygon} {W : ℕ} {Hh n : ℕ} {H : Host} (c : Config) (hw : WordsBounded W c)
    (hH : HostAt c.nmem Hh H) (h60 : c.nreg 50060 = Hh) (haW : Hh + 3 * H.length + 4 ≤ W)
    (hN : (H.pts n).length ≤ W) :
    ∃ c' k, Exec P W cntStmt c c' k ∧ k ≤ 12 * H.length + 12 ∧ FrameB Bhost c c' ∧
      c'.nreg 50063 = (H.pts n).length ∧ HostEnv W Hh H.length c.nmem c' := by
  have hlen := hH.1
  obtain ⟨c₁, k₁, e₁, hk₁, I₁⟩ : ∃ c₁ k₁, Exec P W hostInit c c₁ k₁ ∧ k₁ = 7 ∧
      (HostEnv W Hh H.length c.nmem c₁ ∧ c₁.nreg 50062 = 0 ∧ c₁.nreg 50063 = 0 ∧
        c₁.nreg 50064 = Hh + 1) := by
    unfold hostInit
    exec_block
    · omega
    · omega
    · omega
    · omega
    · omega
    · config_simp; rw [h60]; omega
    · refine ⟨rfl, ⟨‹_›, by config_simp; exact h60, by config_simp; rw [h60, hlen],
        by config_simp, by config_simp, by config_simp, rfl⟩, by config_simp, by config_simp,
        by config_simp; rw [h60]⟩
  obtain ⟨E₁, i0, a0, d0⟩ := I₁
  let I : Config → Prop := fun d => HostEnv W Hh H.length c.nmem d ∧ d.nreg 50062 ≤ H.length ∧
    d.nreg 50063 = preLen n H (d.nreg 50062) ∧ d.nreg 50064 = Hh + 1 + 3 * d.nreg 50062
  have hI₁ : I c₁ := ⟨E₁, by omega, by rw [a0, i0, preLen_zero], by rw [d0, i0]⟩
  obtain ⟨c₂, k₂, e₂, I₂, hx₂, hk₂⟩ := Exec.whileLtN_bounded (P := P) (a := 50062) (b := 50061)
    (body := cntBody) I (fun d => H.length - d.nreg 50062) 10 (fun d hd => hd.1.wb)
    (fun d hd ht => by
      obtain ⟨E, hi, ha, hd'⟩ := hd
      rw [E.h61] at ht
      have hcnt := machineCnt_eq (i := d.nreg 50062) hH ht
      have hpre := preLen_succ n H ht
      have hle := preLen_mono n H (show d.nreg 50062 + 1 ≤ H.length by omega)
      rw [preLen_length] at hle
      obtain ⟨d', k, e, hk, E', i', a', c', -⟩ := cntBody_exec (P := P) E rfl ht hd' haW
        (by rw [ha, hcnt]; omega)
      refine ⟨d', k, e, ⟨E', by omega, ?_, by rw [a', i']⟩, hk, by omega⟩
      rw [c', i', ha, hcnt, hpre]) hI₁
  obtain ⟨E₂, i₂, a₂, -⟩ := I₂
  rw [E₂.h61] at hx₂
  have hlast : c₂.nreg 50062 = H.length := by omega
  have ex : Exec P W cntStmt c c₂ (k₁ + k₂) := .seq e₁ e₂
  refine ⟨c₂, _, ex, ?_, exec_frameB ex wr_cntStmt, by rw [a₂, hlast, preLen_length], E₂⟩
  have : k₂ ≤ 12 * H.length + 2 := by
    have : (10 + 2) * (H.length - c₁.nreg 50062) ≤ 12 * H.length := by
      rw [i0, Nat.sub_zero]
    omega
  omega

/-! ## Looking up a point -/

/-- Membership in a list of registers, as a write set. -/
def Bl (l : List ℕ) (r : ℕ) : Bool := l.contains r

theorem ne_of_Bl {l : List ℕ} {r a : ℕ} (h : Bl l r = false) (ha : a ∈ l) : r ≠ a := by
  rintro rfl
  Ξ' Bl, List.contains_iff_mem.2 ha at h
  exact Bool.noConfusion h

theorem Bl_mono {l l' : List ℕ} {r : ℕ} (h : Bl l' r = false) (hs : l ⊆ l') : Bl l r = false := by
  unfold Bl at *
  by_contra h'
  Ξ' Bool.not_eq_false, List.contains_iff_mem at h'
  Ξ' List.contains_iff_mem.2 (hs h') at h
  exact Bool.noConfusion h

/-- Advance to the next item: count `:= lr 73`, `i := i + 1`, address `+ 3`. -/
def advance : Stmt := block [.copyN 50063 50073, .addN 50062 50062 50067, .addN 50064 50064 50069]

/-- Found in a run `run a ℓ` (`a` in `lr 66`): the vertex `(a + (p - count)) mod n`; exit. -/
def foundRun : Stmt :=
  .seq (block [.subN 50074 50071 50063, .inputSize 50075, .subN 50076 50075 50066])
    (.seq (.ifLtN 50074 50076 (.instr (.addN 50047 50066 50074)) (.instr (.subN 50047 50074 50076)))
      (block [.constN 50046 0, .copyN 50062 50061]))

/-- Found a point item (kind `1` vertex, `2` edge point): copy it; exit. -/
def foundPt : Stmt :=
  block [.subN 50046 50065 50067, .copyN 50047 50066, .copyN 50048 50072, .copyN 50062 50061]

/-- Read item `i` (kind, two arguments), then decide. -/
def lookBody : Stmt :=
  .seq (block [.loadN 50065 50064, .addN 50070 50064 50067, .loadN 50066 50070,
      .addN 50070 50070 50067, .loadN 50072 50070])
    (.ifLtN 50065 50067
      (.seq (block [.addN 50073 50063 50072, .addN 50073 50073 50067])
        (.ifLtN 50071 50073 foundRun advance))
      (.seq (.instr (.addN 50073 50063 50067)) (.ifLtN 50071 50073 foundPt advance)))

/-- **The symbolic point of index `lr 71`** of the host at `lr 60` (after `hostInit`), into
`lr 46 … lr 48`. -/
def lookStmt : Stmt :=
  .seq (block [.constN 50062 0, .constN 50063 0, .addN 50064 50060 50067])
    (.whileLtN 50062 50061 lookBody)

theorem wr_lookStmt : wr Bhost lookStmt = true := ⌖

/-- The invariant of the lookup. -/
def LkI (W n Hh p : ℕ) (H : Host) (m : ℕ → ℕ) (d : Config) : Prop :=
  HostEnv W Hh H.length m d ∧ d.nreg 50071 = p ∧ d.nreg 50062 ≤ H.length ∧
    ((d.nreg 50063 = preLen n H (d.nreg 50062) ∧ preLen n H (d.nreg 50062) ≤ p ∧
        d.nreg 50064 = Hh + 1 + 3 * d.nreg 50062) ∨
      (d.nreg 50062 = H.length ∧ ∃ sp, (H.pts n)[p]? = some sp ∧ SymPtIn d 50046 sp))

/-- `(a + k) mod n` by one conditional subtraction. -/
theorem mod_of_lt_two {a k n : ℕ} (ha : a < n) (hk : k < n) :
    (a + k) % n = if k < n - a then a + k else k - (n - a) := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt (⋄)
  · Ξ Nat.mod_eq_sub_mod (⋄), Nat.mod_eq_of_lt (⋄)
    omega

/-- One step of the lookup. -/
theorem lookBody_exec {P : Polygon} {W Hh p : ℕ} {H : Host} {m : ℕ → ℕ} {d : Config}
    (hH : HostAt m Hh H) (hwf : HostWF P.n H) (hW : P.n ≤ W) (haW : Hh + 3 * H.length + 4 ≤ W)
    (hN : (H.pts P.n).length ≤ W) (hI : LkI W P.n Hh p H m d) (ht : d.nreg 50062 < d.nreg 50061) :
    ∃ d' k, Exec P W lookBody d d' k ∧ LkI W P.n Hh p H m d' ∧ k ≤ 25 ∧
      H.length - d'.nreg 50062 < H.length - d.nreg 50062 := by
  obtain ⟨E, h71, hil, hs⟩ := hI
  have hw := E.wb
  rw [E.h61] at ht
  set i := d.nreg 50062 with hi
  rcases hs with ⟨hacc, hpi, ha⟩ | ⟨hdone, -⟩
  swap
  · omega
  have hitem := hostAt_item hH ht
  have hcnt := machineCnt_eq hH ht
  have hpre := preLen_succ P.n H ht
  have hle := preLen_mono P.n H (show i + 1 ≤ H.length by omega)
  rw [preLen_length] at hle
  have hmem : H[i] ∈ H := List.getElem_mem ht
  set k := m (Hh + 1 + 3 * i) with hk
  set a := m (Hh + 2 + 3 * i) with hak
  set b := m (Hh + 3 + 3 * i) with hbk
  -- the loads
  obtain ⟨d₁, k₁, e₁, hk₁, l65, l66, l72⟩ : ∃ d₁ k₁, Exec P W (block [.loadN 50065 50064,
      .addN 50070 50064 50067, .loadN 50066 50070, .addN 50070 50070 50067,
      .loadN 50072 50070]) d d₁ k₁ ∧ k₁ = 5 ∧ d₁.nreg 50065 = k ∧ d₁.nreg 50066 = a ∧
      d₁.nreg 50072 = b := by
    exec_block
    · config_simp; rw [ha, E.h67]; omega
    · config_simp; rw [ha, E.h67]; omega
    · refine ⟨rfl, by config_simp; rw [ha, E.mem], ?_, ?_⟩
      · config_simp; rw [ha, E.h67, E.mem]; congr 1; omega
      · config_simp; rw [ha, E.h67, E.mem]; congr 1; omega
  have f₁ := exec_frameB e₁ (B := Bl [50065, 50066, 50070, 50072]) (by decide)
  have w₁ := e₁.wb_right
  have g := fun r (hr : Bl [50065, 50066, 50070, 50072] r = false) => f₁.1 r hr
  have g60 : d₁.nreg 50060 = Hh := (g _ (by decide)).trans E.h60
  have g61 : d₁.nreg 50061 = H.length := (g _ (by decide)).trans E.h61
  have g62 : d₁.nreg 50062 = i := g _ (by decide)
  have g63 : d₁.nreg 50063 = preLen P.n H i := (g _ (by decide)).trans hacc
  have g64 : d₁.nreg 50064 = Hh + 1 + 3 * i := (g _ (by decide)).trans ha
  have g67 : d₁.nreg 50067 = 1 := (g _ (by decide)).trans E.h67
  have g68 : d₁.nreg 50068 = 2 := (g _ (by decide)).trans E.h68
  have g69 : d₁.nreg 50069 = 3 := (g _ (by decide)).trans E.h69
  have g71 : d₁.nreg 50071 = p := (g _ (by decide)).trans h71
  have gm : d₁.nmem = m := f₁.2.2.1.trans E.mem
  -- the environment is kept by the rest (they write only `Bhost` registers other than these)
  have env : ∀ d' : Config, WordsBounded W d' → d'.nmem = d₁.nmem →
      (∀ r, Bl [50046, 50047, 50048, 50062, 50063, 50064, 50073, 50074, 50075, 50076] r = false →
        d'.nreg r = d₁.nreg r) → HostEnv W Hh H.length m d' ∧ d'.nreg 50071 = p :=
    fun d' hw' hm' hr' => ⟨⟨hw', (hr' _ (by decide)).trans g60, (hr' _ (by decide)).trans g61,
      (hr' _ (by decide)).trans g67, (hr' _ (by decide)).trans g68,
      (hr' _ (by decide)).trans g69, hm'.trans gm⟩, (hr' _ (by decide)).trans g71⟩
  by_cases hkind : k < 1
  · -- a run
    have hk0 : k = 0 := by omega
    have hrun : H[i] = .run a b := by rw [hitem.1]; simp [itemOf, hk0]
    have hab : a < P.n ∧ b < P.n := by have := hwf _ hmem; rw [hrun] at this; exact this
    rw [ite_eq_left hkind] at hcnt
    obtain ⟨d₂, k₂, e₂, hk₂, l73⟩ : ∃ d₂ k₂, Exec P W (block [.addN 50073 50063 50072,
        .addN 50073 50073 50067]) d₁ d₂ k₂ ∧ k₂ = 2 ∧
        d₂.nreg 50073 = preLen P.n H i + (b + 1) := by
      exec_block
      · rw [g63, l72]; omega
      · config_simp; rw [g63, l72, g67]; omega
      · exact ⟨rfl, by config_simp; rw [g63, l72, g67]; ring⟩
    have f₂ := exec_frameB e₂ (B := Bl [50073]) (by decide)
    have w₂ := e₂.wb_right
    have h2 : ∀ r, r ≠ 50073 → d₂.nreg r = d₁.nreg r := fun r hr =>
      f₂.1 r (by simp [Bl, hr])
    by_cases hf : p < preLen P.n H i + (b + 1)
    · -- found
      have off : p - preLen P.n H i ≤ b := by omega
      obtain ⟨d₃, k₃, e₃, hk₃, o46, o47, o62⟩ : ∃ d₃ k₃, Exec P W foundRun d₂ d₃ k₃ ∧
          k₃ ≤ 8 ∧ d₃.nreg 50046 = 0 ∧ d₃.nreg 50047 = (a + (p - preLen P.n H i)) % P.n ∧
          d₃.nreg 50062 = H.length := by
        unfold foundRun
        refine spec_seq ?_
        exec_block
        · exact hW
        rw [mod_of_lt_two hab.1 (by omega)]
        by_cases hc : p - preLen P.n H i < P.n - a
        · refine spec_seq (spec_ifLtN_true (by
            config_simp; rw [h2 _ (by omega), h2 _ (by omega), h2 _ (by omega), g71, g63, l66]
            exact hc) (spec_instr (Exec.addN ‹_› _ _ _ (by
              config_simp; rw [h2 _ (by omega), h2 _ (by omega), h2 _ (by omega), g71, g63, l66]
              omega)) fun _ => ?_))
          exec_block
          · omega
          refine ⟨by omega, by config_simp, ?_, ?_⟩
          · config_simp
            rw [h2 _ (by omega), h2 _ (by omega), h2 _ (by omega), g71, g63, l66, ite_eq_left hc]
          · config_simp; rw [h2 _ (by omega), g61]
        · refine spec_seq (spec_ifLtN_false (by
            config_simp; rw [h2 _ (by omega), h2 _ (by omega), h2 _ (by omega), g71, g63, l66]
            exact hc) (spec_instr (Exec.subN ‹_› _ _ _) fun _ => ?_))
          exec_block
          · omega
          refine ⟨by omega, by config_simp, ?_, ?_⟩
          · config_simp
            rw [h2 _ (by omega), h2 _ (by omega), h2 _ (by omega), g71, g63, l66, ite_eq_right hc]
          · config_simp; rw [h2 _ (by omega), g61]
      have f₃ := exec_frameB e₃ (B := Bl [50046, 50047, 50062, 50074, 50075, 50076]) (by decide)
      obtain ⟨E₃, p₃⟩ := env d₃ e₃.wb_right (f₃.2.2.1.trans f₂.2.2.1) (fun r hr => by
        rw [f₃.1 r (Bl_mono hr (by intro x hx; simp at hx ⊢; omega)),
          h2 r (ne_of_Bl hr (by simp))])
      have t1 : d₁.nreg 50065 < d₁.nreg 50067 := by rw [l65, g67]; exact hkind
      have t2 : d₂.nreg 50071 < d₂.nreg 50073 := by
        rw [h2 _ (by omega), g71, l73]; exact hf
      refine ⟨d₃, k₁ + ((k₂ + (k₃ + 1)) + 1),
        .seq e₁ (.ifLtN_true t1 (.seq e₂ (.ifLtN_true t2 e₃))),
        ⟨E₃, p₃, by omega, Or.inr ⟨o62, .vtx ((a + (p - preLen P.n H i)) % P.n), ?_,
          ⟨o46, o47⟩⟩⟩, by omega, by omega⟩
      rw [pts_getElem? P.n H ht hpi (by rw [hrun]; simp only [itemCnt]; omega), hrun,
        run_pts_getElem? _ _ _ off]
    · -- not in this item
      obtain ⟨d₃, k₃, e₃, hk₃, o63, o62, o64⟩ : ∃ d₃ k₃, Exec P W advance d₂ d₃ k₃ ∧ k₃ = 3 ∧
          d₃.nreg 50063 = preLen P.n H i + (b + 1) ∧ d₃.nreg 50062 = i + 1 ∧
          d₃.nreg 50064 = Hh + 1 + 3 * (i + 1) := by
        unfold advance
        exec_block
        · config_simp; rw [h2 _ (by omega), h2 _ (by omega), g62, g67]; omega
        · config_simp; rw [h2 _ (by omega), h2 _ (by omega), g64, g69]; omega
        · refine ⟨rfl, by config_simp; rw [l73], ?_, ?_⟩
          · config_simp; rw [h2 _ (by omega), h2 _ (by omega), g62, g67]
          · config_simp; rw [h2 _ (by omega), h2 _ (by omega), g64, g69]; ring
      have f₃ := exec_frameB e₃ (B := Bl [50062, 50063, 50064]) (by decide)
      obtain ⟨E₃, p₃⟩ := env d₃ e₃.wb_right (f₃.2.2.1.trans f₂.2.2.1) (fun r hr => by
        rw [f₃.1 r (Bl_mono hr (by intro x hx; simp at hx ⊢; omega)),
          h2 r (ne_of_Bl hr (by simp))])
      have hpre' : preLen P.n H (i + 1) = preLen P.n H i + (b + 1) := by
        rw [hpre, hrun]; rfl
      have t1 : d₁.nreg 50065 < d₁.nreg 50067 := by rw [l65, g67]; exact hkind
      have t2 : ¬ d₂.nreg 50071 < d₂.nreg 50073 := by
        rw [h2 _ (by omega), g71, l73]; exact hf
      refine ⟨d₃, k₁ + ((k₂ + (k₃ + 2)) + 1),
        .seq e₁ (.ifLtN_true t1 (.seq e₂ (.ifLtN_false t2 e₃))),
        ⟨E₃, p₃, by omega, Or.inl ⟨?_, ?_, ?_⟩⟩, by omega, by omega⟩
      · rw [o63, o62, hpre']
      · rw [o62, hpre']; omega
      · rw [o64, o62]
  · -- a point
    rw [ite_eq_right hkind] at hcnt
    have hk12 : k = 1 ∨ k = 2 := by have := hitem.2; omega
    have e₂ := Exec.addN (P := P) w₁ 50073 50063 50067 (by rw [g63, g67]; omega)
    have w₂ := e₂.wb_right
    by_cases hf : p < preLen P.n H i + 1
    · -- found
      have hp0 : p - preLen P.n H i = 0 := by omega
      obtain ⟨d₃, k₃, e₃, hk₃, o46, o47, o48, o62⟩ : ∃ d₃ k₃, Exec P W foundPt
          { d₁ with nreg := upd d₁.nreg 50073 (d₁.nreg 50063 + d₁.nreg 50067) } d₃ k₃ ∧
          k₃ = 4 ∧ d₃.nreg 50046 = k - 1 ∧ d₃.nreg 50047 = a ∧ d₃.nreg 50048 = b ∧
          d₃.nreg 50062 = H.length := by
        unfold foundPt
        exec_block
        exact ⟨rfl, by config_simp; rw [l65, g67], by config_simp; rw [l66],
          by config_simp; rw [l72], by config_simp; rw [g61]⟩
      have f₃ := exec_frameB e₃ (B := Bl [50046, 50047, 50048, 50062]) (by decide)
      obtain ⟨E₃, p₃⟩ := env d₃ e₃.wb_right f₃.2.2.1 (fun r hr => by
        rw [f₃.1 r (Bl_mono hr (by intro x hx; simp at hx ⊢; omega))]
        simp only [upd]
        rw [ite_eq_right (ne_of_Bl hr (by simp))])
      have hsp : (H.pts P.n)[p]? = some (if k = 1 then SymPt.vtx a else SymPt.onEdge a b) := by
        rw [pts_getElem? P.n H ht hpi (by rw [← hcnt]; omega), hp0, hitem.1]
        rcases hk12 with h1 | h1 <;> simp [itemOf, HostItem.pts, h1]
      have t1 : ¬ d₁.nreg 50065 < d₁.nreg 50067 := by rw [l65, g67]; exact hkind
      have t2 : upd d₁.nreg 50073 (d₁.nreg 50063 + d₁.nreg 50067) 50071 <
          upd d₁.nreg 50073 (d₁.nreg 50063 + d₁.nreg 50067) 50073 := by
        config_simp; rw [g71, g63, g67]; exact hf
      refine ⟨d₃, k₁ + ((1 + (k₃ + 1)) + 2),
        .seq e₁ (.ifLtN_false t1 (.seq e₂ (.ifLtN_true t2 e₃))),
        ⟨E₃, p₃, by omega, Or.inr ⟨o62, _, hsp, ?_⟩⟩, by omega, by omega⟩
      rcases hk12 with h1 | h1
      · rw [ite_eq_left h1]; exact ⟨by rw [o46, h1], o47⟩
      · rw [ite_eq_right (by omega)]; exact ⟨by rw [o46, h1], o47, o48⟩
    · -- not in this item
      obtain ⟨d₃, k₃, e₃, hk₃, o63, o62, o64⟩ : ∃ d₃ k₃, Exec P W advance
          { d₁ with nreg := upd d₁.nreg 50073 (d₁.nreg 50063 + d₁.nreg 50067) } d₃ k₃ ∧
          k₃ = 3 ∧ d₃.nreg 50063 = preLen P.n H i + 1 ∧ d₃.nreg 50062 = i + 1 ∧
          d₃.nreg 50064 = Hh + 1 + 3 * (i + 1) := by
        unfold advance
        exec_block
        · config_simp; rw [g62, g67]; omega
        · config_simp; rw [g64, g69]; omega
        · refine ⟨rfl, by config_simp; rw [g63, g67], ?_, ?_⟩
          · config_simp; rw [g62, g67]
          · config_simp; rw [g64, g69]; ring
      have f₃ := exec_frameB e₃ (B := Bl [50062, 50063, 50064]) (by decide)
      obtain ⟨E₃, p₃⟩ := env d₃ e₃.wb_right f₃.2.2.1 (fun r hr => by
        rw [f₃.1 r (Bl_mono hr (by intro x hx; simp at hx ⊢; omega))]
        simp only [upd]
        rw [ite_eq_right (ne_of_Bl hr (by simp))])
      have hpre' : preLen P.n H (i + 1) = preLen P.n H i + 1 := by rw [hpre, ← hcnt]
      have t1 : ¬ d₁.nreg 50065 < d₁.nreg 50067 := by rw [l65, g67]; exact hkind
      have t2 : ¬ upd d₁.nreg 50073 (d₁.nreg 50063 + d₁.nreg 50067) 50071 <
          upd d₁.nreg 50073 (d₁.nreg 50063 + d₁.nreg 50067) 50073 := by
        config_simp; rw [g71, g63, g67]; exact hf
      refine ⟨d₃, k₁ + ((1 + (k₃ + 2)) + 2),
        .seq e₁ (.ifLtN_false t1 (.seq e₂ (.ifLtN_false t2 e₃))),
        ⟨E₃, p₃, by omega, Or.inl ⟨?_, ?_, ?_⟩⟩, by omega, by omega⟩
      · rw [o63, o62, hpre']
      · rw [o62, hpre']; omega
      · rw [o64, o62]

/-- **The lookup of the symbolic point of index `p`** of the host (at most `27 |H| + 5`
steps). -/
theorem look_exec {P : Polygon} {W Hh p : ℕ} {H : Host} {m : ℕ → ℕ} (c : Config)
    (E : HostEnv W Hh H.length m c) (h71 : c.nreg 50071 = p) (hH : HostAt m Hh H)
    (hwf : HostWF P.n H) (hW : P.n ≤ W) (haW : Hh + 3 * H.length + 4 ≤ W)
    (hN : (H.pts P.n).length ≤ W) (hp : p < (H.pts P.n).length) :
    ∃ c' k, Exec P W lookStmt c c' k ∧ k ≤ 27 * H.length + 5 ∧ FrameB Bhost c c' ∧
      HostEnv W Hh H.length m c' ∧ c'.nreg 50071 = p ∧
      ∃ sp, (H.pts P.n)[p]? = some sp ∧ SymPtIn c' 50046 sp := by
  have hw := E.wb
  obtain ⟨c₁, k₁, e₁, hk₁, I₁⟩ : ∃ c₁ k₁, Exec P W (block [.constN 50062 0, .constN 50063 0,
      .addN 50064 50060 50067]) c c₁ k₁ ∧ k₁ = 3 ∧ LkI W P.n Hh p H m c₁ := by
    exec_block
    · omega
    · omega
    · config_simp; rw [E.h60, E.h67]; omega
    · refine ⟨rfl, ⟨⟨‹_›, by config_simp; exact E.h60, by config_simp; exact E.h61,
        by config_simp; exact E.h67, by config_simp; exact E.h68, by config_simp; exact E.h69,
        E.mem⟩, by config_simp; exact h71, by config_simp; omega, Or.inl ⟨?_, ?_, ?_⟩⟩⟩
      · config_simp; Ξ preLen_zero
      · config_simp; rw [preLen_zero]; omega
      · config_simp; Ξ E.h60, E.h67
  obtain ⟨c₂, k₂, e₂, I₂, hx₂, hk₂⟩ := Exec.whileLtN_bounded (P := P) (a := 50062) (b := 50061)
    (body := lookBody) (LkI W P.n Hh p H m) (fun d => H.length - d.nreg 50062) 25
    (fun d hd => hd.1.wb) (fun d hd ht => by
      obtain ⟨d', k, e, I', hk, hμ⟩ := lookBody_exec hH hwf hW haW hN hd ht
      exact ⟨d', k, e, I', hk, hμ⟩) I₁
  obtain ⟨E₂, p₂, hi₂, hs₂⟩ := I₂
  Ξ' E₂.h61 at hx₂
  have ex : Exec P W lookStmt c c₂ (k₁ + k₂) := .seq e₁ e₂
  refine ⟨c₂, _, ex, ?_, exec_frameB ex wr_lookStmt, E₂, p₂, ?_⟩
  · have : (25 + 2) * (H.length - c₁.nreg 50062) ≤ 27 * H.length :=
      Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    omega
  · rcases hs₂ with ⟨-, hle, -⟩ | ⟨-, hd⟩
    · have : c₂.nreg 50062 = H.length := ⋄
      Ξ' this, preLen_length at hle
      omega
    · exact hd

end

end NFLoc

end Chazelle.Core
