module

public import Chazelle.Core.DownPhaseDrvHArc
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics
public import Chazelle.MiscTactics
set_option maxHeartbeats 1000000

/-!
# Down-phase driver, host RAM (D3a), part 7: the loops

* `arcLoop_exec`: the arc loop writes `walkItems li n N r` into the buffer at `T`;
* `finS_exec`: the host handle `T + 3 K` after the buffer and its count word;
* `cpyLoop_exec`: the items copied to the host layout, reversed when `li = false`;
* `padLoopH_exec`: the allocator raised one by one to the end of the host (exact cost, so that
  the allocation is at most the step count).
-/

namespace Chazelle.Core

namespace DrvH

open Machine Machine.Stmt Programs BuildRam DrvR

@[expose] public section

/-- The registers of the copy loop. -/
def Bcp (q : ℕ) : Bool := decide (215080 ≤ q ∧ q ≤ 215086)

section exec

variable {P : Polygon} {W : ℕ}

/-- **The arc loop** writes `walkItems li n N r` into the buffer. -/
theorem arcLoop_exec (d : Config) (hw : WordsBounded W d) {n : ℕ} {N : NF} {r : ℕ} {li : Bool}
    {T : ℕ} (hE : HEnv W n N r li T d) (h41 : d.nreg 215041 = 0) (hB : Buf n T [] d) :
    ∃ d' k, Exec P W arcLoop d d' k ∧ k ≤ 1512 ∧ Buf n T (walkItems li n N r) d' ∧
      HEnv W n N r li T d' ∧ (∀ a, a < T → d'.nmem a = d.nmem a) ∧ FrameM Bdyn d d' := by
  have hA5 := hE.F.hA
  let Inv : ℕ → Config → Prop := fun t e => WordsBounded W e ∧ e.nreg 215041 = t ∧
    e.nreg 215030 = (N.region r).arcs.length ∧ HEnv W n N r li T e ∧ Buf n T (pre li n N r t) e ∧
    (∀ a, a < T → e.nmem a = d.nmem a) ∧ FrameM Bdyn d e
  obtain ⟨d', k, ex, ⟨w', -, -, E', B', m', f'⟩, hk⟩ := DrvR.forLoop (P := P) (W := W)
    (ir := 215041) (nr := 215030) Inv 300 (N.region r).arcs.length
    (fun t e ⟨hw, h1, h2, _⟩ => ⟨hw, h1, h2⟩)
    (fun t e ht ⟨hwe, e41, e30, Ee, Be, me, fe⟩ => by
      obtain ⟨e', k, ex, hk, v41, B', m', f'⟩ := arcBody_exec (P := P) e hwe Ee e41 ht Be
      exact ⟨e', k, ex, ⟨ex.wb_right, v41, by rw [f'.1 _ (by decide), e30], Ee.keep f' m', B',
        fun a ha => by rw [m' a ha, me a ha], fe.trans f'⟩, hk⟩)
    (j := 0) ⟨hw, h41, hE.aR, hE, hB, fun _ _ => rfl, FrameM.refl _ _⟩ (Nat.zero_le _)
  exact ⟨d', k, ex, by omega, by rw [← pre_full]; exact B', E', m', f'⟩

/-- One item of the copy. -/
theorem cpyBody_exec (e : Config) (hw : WordsBounded W e) {li : Bool} {n S D u w i : ℕ}
    (hK : Kst n li e) (h81 : e.nreg 215081 = S) (h82 : e.nreg 215082 = D)
    (h83 : e.nreg 215083 = u) (h84 : e.nreg 215084 = w) (h80 : e.nreg 215080 = i)
    (hSD : S + 2 < D) (hDW : D + 3 ≤ W) (hSW : S + u ≤ W) (hiW : i + 1 ≤ W) :
    ∃ e' k, Exec P W cpyBody e e' k ∧ k = 14 ∧ e'.nreg 215080 = i + 1 ∧
      e'.nreg 215081 = S + u - w ∧ e'.nreg 215082 = D + 3 ∧
      e'.nmem = wr3 e.nmem D (e.nmem S) (e.nmem (S + 1)) (e.nmem (S + 2)) ∧
      FrameM (fun q => decide (215080 ≤ q ∧ q ≤ 215082) || decide (215085 ≤ q ∧ q ≤ 215086)) e e' := by
  obtain ⟨e', k, ex, hk, h1, h2, h3, hm⟩ : ∃ e' k, Exec P W cpyBody e e' k ∧ k = 14 ∧
      e'.nreg 215080 = i + 1 ∧ e'.nreg 215081 = S + u - w ∧ e'.nreg 215082 = D + 3 ∧
      e'.nmem = wr3 e.nmem D (e.nmem S) (e.nmem (S + 1)) (e.nmem (S + 2)) := by
    unfold cpyBody
    exec_block
    all_goals
      try (config_simp; (try simp only [h81, h82, h83, h84, h80, hK.one, hK.two, hK.three]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> config_simp <;>
      simp only [h81, h82, h83, h84, h80, hK.one, hK.two, hK.three]
    unfold wr3
    rw [Machine.upd_other _ _ _ (show S + 1 ≠ D by omega),
      Machine.upd_other _ _ _ (show S + 2 ≠ D + 1 by omega),
      Machine.upd_other _ _ _ (show S + 2 ≠ D by omega)]
  exact ⟨e', k, ex, hk, h1, h2, h3, hm, exec_frameM ex (by decide)⟩

theorem take_add_one_getD {l : List HostItem} {i : ℕ} (h : i < l.length) (x : HostItem) :
    l.take (i + 1) = l.take i ++ [l.getD i x] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some,
    List.getD_eq_getElem _ _ h]

/-- **The copy of the items** to the host layout (reversed when `li = false`). -/
theorem cpyLoop_exec (d : Config) (hw : WordsBounded W d) {li : Bool} {n T : ℕ}
    {xs : List HostItem} (hK : Kst n li d) (hI : ItemsAt d.nmem T xs)
    (h11 : d.nreg 215011 = xs.length) (h80 : d.nreg 215080 = 0)
    (h82 : d.nreg 215082 = T + 3 * xs.length + 1)
    (h81 : d.nreg 215081 = if li then T else T + 3 * xs.length - 3)
    (h83 : d.nreg 215083 = if li then 3 else 0) (h84 : d.nreg 215084 = if li then 0 else 3)
    (hW : T + 6 * xs.length + 4 ≤ W) :
    ∃ d' k, Exec P W cpyLoop d d' k ∧ k ≤ 16 * xs.length + 2 ∧
      ItemsAt d'.nmem (T + 3 * xs.length + 1) (if li then xs else xs.reverse) ∧
      d'.nreg 215082 = T + 6 * xs.length + 1 ∧
      (∀ a, a < T + 3 * xs.length + 1 → d'.nmem a = d.nmem a) ∧ FrameM Bcp d d' := by
  set K := xs.length with hKdef
  set H := if li then xs else xs.reverse with hH
  have hHl : H.length = K := by rw [hH]; split_ifs <;> simp [hKdef]
  have hHget : ∀ i, i < K → H.getD i (.run 0 0) =
      xs.getD (if li then i else K - 1 - i) (.run 0 0) := fun i hi => by
    rw [hH]; cases li
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact getD_reverse_items hi
    · rfl
  let Inv : ℕ → Config → Prop := fun i e => WordsBounded W e ∧ e.nreg 215080 = i ∧
    e.nreg 215011 = K ∧ e.nreg 215082 = T + 3 * K + 1 + 3 * i ∧
    (i < K → e.nreg 215081 = T + 3 * (if li then i else K - 1 - i)) ∧
    e.nreg 215083 = (if li then 3 else 0) ∧ e.nreg 215084 = (if li then 0 else 3) ∧
    Kst n li e ∧ (∀ a, a < T + 3 * K + 1 → e.nmem a = d.nmem a) ∧
    ItemsAt e.nmem (T + 3 * K + 1) (H.take i) ∧ FrameM Bcp d e
  obtain ⟨d', k, ex, ⟨w', -, -, v82, -, -, -, -, m', I', f'⟩, hk⟩ := DrvR.forLoop (P := P)
    (W := W) (ir := 215080) (nr := 215011) Inv 14 K
    (fun i e ⟨hw, h1, h2, _⟩ => ⟨hw, h1, h2⟩)
    (fun i e hi ⟨hwe, e80, e11, e82, e81, e83, e84, Ke, me, Ie, fe⟩ => by
      set si := if li then i else K - 1 - i with hsi
      have hsiK : si < K := by rw [hsi]; splao
      obtain ⟨e', k, ex, hk, v80, v81, v82, vm, fe'⟩ := cpyBody_exec (P := P) e hwe Ke
        (e81 hi) e82 e83 e84 e80 (by omega) (by omega) (by split_ifs at e83 ⊢ <;> omega)
        (by omega)
      refine ⟨e', k, ex, ⟨ex.wb_right, v80, by rw [fe'.1 _ (by decide), e11], by rwring [v82],
        fun hi' => ?_, by rw [fe'.1 _ (by decide), e83], by rw [fe'.1 _ (by decide), e84],
        Ke.frame fe' (by decide), fun a ha => ?_, ?_, fe.trans (fe'.mono fun q hq => by
          sio only [Bcp, Bool.or_eq_true, decide_eq_true_eq] at hq ⊢)⟩, by omega⟩
      · rw [v81]
        cases li <;> simp only [Bool.false_eq_true, ↓reduceIte] at hsi ⊢ <;> omega
      · rw [vm, wr3_lt (by omega), me a ha]
      · rw [take_add_one_getD (by omega) (.run 0 0), vm]
        have hlen : (H.take i).length = i := by rwo [List.length_take, hHl]
        obtain ⟨a1, a2, a3⟩ := hI si hsiK
        have s0 : e.nmem (T + 3 * si) = encK (H.getD i (.run 0 0)) := by
          rw [me _ (by omega), a1, hHget i hi]
        have s1 : e.nmem (T + 3 * si + 1) = encA (H.getD i (.run 0 0)) := by
          rw [me _ (by omega), a2, hHget i hi]
        have s2 : e.nmem (T + 3 * si + 2) = encB (H.getD i (.run 0 0)) := by
          rw [me _ (by omega), a3, hHget i hi]
        have := Ie.snoc (H.getD i (.run 0 0))
        rw [hlen, ← s0, ← s1, ← s2] at this
        exact this)
    (j := 0) ⟨hw, h80, h11, by omega, fun h0 => by rw [h81]; splao,
      h83, h84, hK, fun _ _ => rfl, by simp only [List.take_zero]; exact ItemsAt.nil _ _,
      FrameM.refl _ _⟩ (Nat.zero_le _)
  refine ⟨d', k, ex, by omega, ?_, by rwring [v82], m', f'⟩
  have htk : H.take K = H := by rw [← hHl, List.take_length]
  rw [htk] at I'
  exact I'

/-- **The end of the host**: the host handle after the buffer, the count word, the copy
arguments. -/
theorem finS_exec (d : Config) (hw : WordsBounded W d) {li : Bool} {n T K : ℕ} (hK : Kst n li d)
    (h40 : d.nreg 215040 = T + 3 * K) (h11 : d.nreg 215011 = K) (h32 : d.nreg 215032 = T)
    (hW : T + 3 * K + 2 ≤ W) :
    ∃ d' k, Exec P W finS d d' k ∧ k ≤ 9 ∧ d'.nreg 215010 = T + 3 * K ∧
      d'.nmem = upd d.nmem (T + 3 * K) K ∧ d'.nreg 215080 = 0 ∧
      d'.nreg 215082 = T + 3 * K + 1 ∧ d'.nreg 215081 = (if li then T else T + 3 * K - 3) ∧
      d'.nreg 215083 = (if li then 3 else 0) ∧ d'.nreg 215084 = (if li then 0 else 3) ∧
      FrameM (fun q => decide (q = 215010) || decide (215080 ≤ q ∧ q ≤ 215084)) d d' := by
  obtain ⟨d', k, ex, hk, v10, vm, v80, v82, v81, v83, v84⟩ : ∃ d' k, Exec P W finS d d' k ∧
      k ≤ 9 ∧ d'.nreg 215010 = T + 3 * K ∧
      d'.nmem = upd d.nmem (T + 3 * K) K ∧ d'.nreg 215080 = 0 ∧
      d'.nreg 215082 = T + 3 * K + 1 ∧ d'.nreg 215081 = (if li then T else T + 3 * K - 3) ∧
      d'.nreg 215083 = (if li then 3 else 0) ∧ d'.nreg 215084 = (if li then 0 else 3) := by
    unfold finS
    refine spec_seq ?_
    exec_block
    all_goals try (config_simp; (try simp only [h40, hK.one]); omega)
    cases li with
    | true =>
      refine spec_ifLtN_true (by config_simp; rwd [hK.zero, hK.li]) ?_
      exec_block
      · omega
      refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;>
        simp only [h40, h11, h32, hK.one, hK.three, ↓reduceIte]
    | false =>
      refine spec_ifLtN_false (by config_simp; rwd [hK.zero, hK.li]) ?_
      exec_block
      · omega
      refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;>
        simp only [h40, h11, hK.one, hK.three, Bool.false_eq_true, ↓reduceIte]
  exact ⟨d', k, ex, hk, v10, vm, v80, v82, v81, v83, v84, exec_frameM ex (by decide)⟩

/-- **The padding loop** runs exactly `3 (r215082 - r9999) + 2` steps. -/
theorem padLoopH_exec : ∀ (m : ℕ) (c : Config), WordsBounded W c → c.nreg 215020 = 1 →
    c.nreg 9999 ≤ c.nreg 215082 → c.nreg 215082 - c.nreg 9999 = m →
    Exec P W padLoopH c { c with nreg := upd c.nreg 9999 (c.nreg 215082) } (3 * m + 2)
  | 0, c, hw, _, hle, hd => by
    have h : c.nreg 9999 = c.nreg 215082 := by omega
    refine ((Exec.whileLtN_false (by omega) hw).cast_end ?_)
    rw [← h, upd_eq_self]
  | m + 1, c, hw, h20, hle, hd => by
    have e := Exec.addN (P := P) hw 9999 9999 215020 (by rw [h20]; have := hw.1 215082; omega)
    have h1 : (upd c.nreg 9999 (c.nreg 9999 + c.nreg 215020)) 215020 = 1 := by
      rw [upd_other _ _ _ (by decide), h20]
    have h2 : (upd c.nreg 9999 (c.nreg 9999 + c.nreg 215020)) 215082 = c.nreg 215082 :=
      upd_other _ _ _ (by decide)
    have h3 : (upd c.nreg 9999 (c.nreg 9999 + c.nreg 215020)) 9999 = c.nreg 9999 + 1 := by
      rw [upd_same, h20]
    have e' := padLoopH_exec m _ e.wb_right h1 (by dsimp only; rwo [h2, h3])
      (by dsimp only; rwo [h2, h3])
    refine ((Exec.whileLtN_true (by omega) (Exec.seq e (.skip e.wb_right)) e').cast
      (by ring)).cast_end ?_
    simp only [h2, upd_upd_same]

end exec

end

end DrvH

end Chazelle.Core
