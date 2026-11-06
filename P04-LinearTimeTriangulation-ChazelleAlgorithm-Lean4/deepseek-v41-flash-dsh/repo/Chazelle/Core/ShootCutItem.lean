module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.ShootCutProg

/-!
# WP-G, part 10: the host item of a host point on the RAM

`itLook` finds the item of the host point `u` (register `150064`): the item index (`150065`), the
offset in the item (`150066`) and the three words of the item (`150067 … 150069`), in at most
`20 |H| + 10` steps (`itLook_exec`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK NFLoc

@[expose] public section

/-- The registers written by `itLook`. -/
def Bit : ℕ → Bool := Bl [150065, 150066, 150067, 150068, 150069, 150073, 150074, 150075,
  150077, 150078, 150079]

theorem wr_itLook : wr Bit itLook = true := ⌖

/-- What the item search keeps. -/
structure ItEnv (W Hh u L : ℕ) (m : ℕ → ℕ) (d : Config) : Prop where
  wb : WordsBounded W d
  mem : d.nmem = m
  h21 : d.nreg 150021 = Hh
  h91 : d.nreg 150091 = 1
  h93 : d.nreg 150093 = 3
  h64 : d.nreg 150064 = u
  h77 : d.nreg 150077 = L

/-- The item found for `u`. -/
def ItFound (n Hh u : ℕ) (H : Host) (m : ℕ → ℕ) (d : Config) (r : ℕ) : Prop :=
  r < H.length ∧ preLen n H r ≤ u ∧ u < preLen n H (r + 1) ∧
    d.nreg 150066 = u - preLen n H r ∧ d.nreg 150067 = m (Hh + 1 + 3 * r) ∧
    d.nreg 150068 = m (Hh + 2 + 3 * r) ∧ d.nreg 150069 = m (Hh + 3 + 3 * r)

/-- The invariant of the item search. -/
def ItI (W n Hh u : ℕ) (H : Host) (m : ℕ → ℕ) (d : Config) : Prop :=
  ItEnv W Hh u H.length m d ∧ d.nreg 150065 ≤ H.length ∧
    ((d.nreg 150073 = preLen n H (d.nreg 150065) ∧ preLen n H (d.nreg 150065) ≤ u ∧
        d.nreg 150074 = Hh + 1 + 3 * d.nreg 150065) ∨
      (d.nreg 150065 = H.length ∧ ItFound n Hh u H m d (d.nreg 150079)))

theorem itBody_exec {P : Polygon} {W Hh u : ℕ} {H : Host} {m : ℕ → ℕ} {d : Config}
    (hH : HostAt m Hh H) (haW : Hh + 3 * H.length + 4 ≤ W) (hN : (H.pts P.n).length ≤ W)
    (_hu : u < (H.pts P.n).length) (hI : ItI W P.n Hh u H m d)
    (ht : d.nreg 150065 < d.nreg 150077) :
    ∃ d' k, Exec P W itBody d d' k ∧ ItI W P.n Hh u H m d' ∧ k ≤ 20 ∧
      H.length - d'.nreg 150065 < H.length - d.nreg 150065 := by
  obtain ⟨E, hil, hs⟩ := hI
  have hw := E.wb
  rw [E.h77] at ht
  set i := d.nreg 150065 with hi
  rcases hs with ⟨hacc, hpi, ha⟩ | ⟨hdone, -⟩
  swap
  · omega
  have hitem := hostAt_item hH ht
  have hcnt := machineCnt_eq hH ht
  have hpre := preLen_succ P.n H ht
  have hle := preLen_mono P.n H (show i + 1 ≤ H.length by omega)
  rw [preLen_length] at hle
  set k := m (Hh + 1 + 3 * i) with hk
  set a := m (Hh + 2 + 3 * i) with hak
  set b := m (Hh + 3 + 3 * i) with hbk
  obtain ⟨d₁, k₁, e₁, hk₁, l67, l68, l69⟩ : ∃ d₁ k₁, Exec P W (block [.loadN 150067 150074,
      .addN 150075 150074 150091, .loadN 150068 150075, .addN 150075 150075 150091,
      .loadN 150069 150075]) d d₁ k₁ ∧ k₁ = 5 ∧ d₁.nreg 150067 = k ∧ d₁.nreg 150068 = a ∧
      d₁.nreg 150069 = b := by
    exec_block
    · config_simp; rw [ha, E.h91]; omega
    · config_simp; rw [ha, E.h91]; omega
    · refine ⟨rfl, by config_simp; rw [ha, E.mem], ?_, ?_⟩
      · config_simp; rw [ha, E.h91, E.mem]; congr 1; omega
      · config_simp; rw [ha, E.h91, E.mem]; congr 1; omega
  have f₁ := exec_frameB e₁ (B := Bl [150067, 150068, 150069, 150075]) (by decide)
  have g := fun r (hr : Bl [150067, 150068, 150069, 150075] r = false) => f₁.1 r hr
  have g21 : d₁.nreg 150021 = Hh := (g _ (by decide)).trans E.h21
  have g64 : d₁.nreg 150064 = u := (g _ (by decide)).trans E.h64
  have g65 : d₁.nreg 150065 = i := g _ (by decide)
  have g73 : d₁.nreg 150073 = preLen P.n H i := (g _ (by decide)).trans hacc
  have g74 : d₁.nreg 150074 = Hh + 1 + 3 * i := (g _ (by decide)).trans ha
  have g77 : d₁.nreg 150077 = H.length := (g _ (by decide)).trans E.h77
  have g91 : d₁.nreg 150091 = 1 := (g _ (by decide)).trans E.h91
  have g93 : d₁.nreg 150093 = 3 := (g _ (by decide)).trans E.h93
  have gm : d₁.nmem = m := f₁.2.2.1.trans E.mem
  have w₁ := e₁.wb_right
  -- the count of the item
  obtain ⟨d₂, k₂, e₂, hk₂, l78⟩ : ∃ d₂ k₂, Exec P W (.ifLtN 150067 150091
      (block [.addN 150078 150073 150069, .addN 150078 150078 150091])
      (.instr (.addN 150078 150073 150091))) d₁ d₂ k₂ ∧ k₂ ≤ 3 ∧
      d₂.nreg 150078 = preLen P.n H (i + 1) := by
    rw [hpre, ← hcnt]
    by_cases hkind : k < 1
    · rw [ite_eq_left hkind]
      refine spec_ifLtN_true (by rw [l67, g91]; exact hkind) ?_
      exec_block
      · rw [g73, l69]; have := hpre; rw [← hcnt, ite_eq_left hkind] at this; omega
      · config_simp; rw [g73, l69, g91]; have := hpre; rw [← hcnt, ite_eq_left hkind] at this
        omega
      · exact ⟨by omega, by config_simp; rw [g73, l69, g91]; ring⟩
    · rw [ite_eq_right hkind]
      refine spec_ifLtN_false (by rw [l67, g91]; exact hkind)
        (spec_instr (Exec.addN e₁.wb_right _ _ _ (by
          rw [g73, g91]; have := hpre; rw [← hcnt, ite_eq_right hkind] at this; omega))
          fun _ => ⟨by omega, by config_simp; rw [g73, g91]⟩)
  have f₂ := exec_frameB e₂ (B := Bl [150078]) (by decide)
  have h2 : ∀ r, r ≠ 150078 → d₂.nreg r = d₁.nreg r := fun r hr => f₂.1 r (by simp [Bl, hr])
  have w₂ := e₂.wb_right
  by_cases hf : u < preLen P.n H (i + 1)
  · -- found
    obtain ⟨d₃, k₃, e₃, hk₃, o66, o79, o65⟩ : ∃ d₃ k₃, Exec P W itFound d₂ d₃ k₃ ∧ k₃ = 3 ∧
        d₃.nreg 150066 = u - preLen P.n H i ∧ d₃.nreg 150079 = i ∧
        d₃.nreg 150065 = H.length := by
      unfold itFound
      exec_block
      refine ⟨rfl, ?_, ?_, ?_⟩
      · config_simp; rw [h2 _ (by omega), h2 _ (by omega), g64, g73]
      · config_simp; rw [h2 _ (by omega), g65]
      · config_simp; rw [h2 _ (by omega), g77]
    have f₃ := exec_frameB e₃ (B := Bl [150065, 150066, 150079]) (by decide)
    have h3 : ∀ r, r ≠ 150065 → r ≠ 150066 → r ≠ 150079 → d₃.nreg r = d₂.nreg r :=
      fun r h1 h2' h3' => f₃.1 r (by simp [Bl, h1, h2', h3'])
    have t1 : d₂.nreg 150064 < d₂.nreg 150078 := by rw [h2 _ (by omega), g64, l78]; exact hf
    refine ⟨d₃, k₁ + (k₂ + (k₃ + 1)), .seq e₁ (.seq e₂ (.ifLtN_true t1 e₃)),
      ⟨⟨e₃.wb_right, f₃.2.2.1.trans (f₂.2.2.1.trans gm), ?_, ?_, ?_, ?_, ?_⟩, by omega,
        Or.inr ⟨o65, ?_⟩⟩, by omega, by omega⟩
    · rw [h3 _ (by omega) (by omega) (by omega), h2 _ (by omega), g21]
    · rw [h3 _ (by omega) (by omega) (by omega), h2 _ (by omega), g91]
    · rw [h3 _ (by omega) (by omega) (by omega), h2 _ (by omega), g93]
    · rw [h3 _ (by omega) (by omega) (by omega), h2 _ (by omega), g64]
    · rw [h3 _ (by omega) (by omega) (by omega), h2 _ (by omega), g77]
    · rw [o79]
      refine ⟨ht, hpi, hf, o66, ?_, ?_, ?_⟩
      · rw [h3 _ (by omega) (by omega) (by omega), h2 _ (by omega), l67]
      · rw [h3 _ (by omega) (by omega) (by omega), h2 _ (by omega), l68]
      · rw [h3 _ (by omega) (by omega) (by omega), h2 _ (by omega), l69]
  · -- the next item
    obtain ⟨d₃, k₃, e₃, hk₃, o73, o65, o74⟩ : ∃ d₃ k₃, Exec P W itNext d₂ d₃ k₃ ∧ k₃ = 3 ∧
        d₃.nreg 150073 = preLen P.n H (i + 1) ∧ d₃.nreg 150065 = i + 1 ∧
        d₃.nreg 150074 = Hh + 1 + 3 * (i + 1) := by
      unfold itNext
      exec_block
      · config_simp; rw [h2 _ (by omega), h2 _ (by omega), g65, g91]; omega
      · config_simp; rw [h2 _ (by omega), h2 _ (by omega), g74, g93]; omega
      · refine ⟨rfl, by config_simp; rw [l78], ?_, ?_⟩
        · config_simp; rw [h2 _ (by omega), h2 _ (by omega), g65, g91]
        · config_simp; rw [h2 _ (by omega), h2 _ (by omega), g74, g93]; ring
    have f₃ := exec_frameB e₃ (B := Bl [150065, 150073, 150074]) (by decide)
    have h3 : ∀ r, r ≠ 150065 → r ≠ 150073 → r ≠ 150074 → d₃.nreg r = d₂.nreg r :=
      fun r h1 h2' h3' => f₃.1 r (by simp [Bl, h1, h2', h3'])
    have t1 : ¬ d₂.nreg 150064 < d₂.nreg 150078 := by rw [h2 _ (by omega), g64, l78]; exact hf
    refine ⟨d₃, k₁ + (k₂ + (k₃ + 2)), .seq e₁ (.seq e₂ (.ifLtN_false t1 e₃)),
      ⟨⟨e₃.wb_right, f₃.2.2.1.trans (f₂.2.2.1.trans gm), ?_, ?_, ?_, ?_, ?_⟩, by omega,
        Or.inl ⟨by rw [o73, o65], by rw [o65]; omega, by rw [o74, o65]⟩⟩, by omega, by omega⟩
    · rw [h3 _ (by omega) (by omega) (by omega), h2 _ (by omega), g21]
    · rw [h3 _ (by omega) (by omega) (by omega), h2 _ (by omega), g91]
    · rw [h3 _ (by omega) (by omega) (by omega), h2 _ (by omega), g93]
    · rw [h3 _ (by omega) (by omega) (by omega), h2 _ (by omega), g64]
    · rw [h3 _ (by omega) (by omega) (by omega), h2 _ (by omega), g77]

/-- **The item of a host point** (at most `22 |H| + 10` steps). -/
theorem itLook_exec {P : Polygon} {W Hh u : ℕ} {H : Host} {m : ℕ → ℕ} (c : Config)
    (hw : WordsBounded W c) (hm : c.nmem = m) (hH : HostAt m Hh H) (h21 : c.nreg 150021 = Hh)
    (h91 : c.nreg 150091 = 1) (h93 : c.nreg 150093 = 3) (h64 : c.nreg 150064 = u)
    (haW : Hh + 3 * H.length + 4 ≤ W) (hN : (H.pts P.n).length ≤ W)
    (hu : u < (H.pts P.n).length) :
    ∃ c' k, Exec P W itLook c c' k ∧ k ≤ 22 * H.length + 10 ∧ FrameB Bit c c' ∧
      ItFound P.n Hh u H m c' (c'.nreg 150065) := by
  have hlen : m Hh = H.length := hH.1
  obtain ⟨c₁, k₁, e₁, hk₁, I₁⟩ : ∃ c₁ k₁, Exec P W itInit c c₁ k₁ ∧ k₁ = 4 ∧
      ItI W P.n Hh u H m c₁ := by
    unfold itInit
    exec_block
    · omega
    · omega
    · config_simp; rw [h21, h91]; omega
    · refine ⟨rfl, ⟨⟨‹_›, by config_simp; exact hm, by config_simp; exact h21,
        by config_simp; exact h91, by config_simp; exact h93, by config_simp; exact h64, ?_⟩,
        by config_simp; omega, Or.inl ⟨?_, ?_, ?_⟩⟩⟩
      · config_simp; rw [h21, hm, hlen]
      · config_simp; rw [preLen_zero]
      · config_simp; rw [preLen_zero]; omega
      · config_simp; rw [h21, h91]
  obtain ⟨c₂, k₂, e₂, I₂, hx₂, hk₂⟩ := Exec.whileLtN_bounded (P := P) (a := 150065)
    (b := 150077) (body := itBody) (ItI W P.n Hh u H m) (fun d => H.length - d.nreg 150065) 20
    (fun d hd => hd.1.wb) (fun d hd ht => by
      obtain ⟨d', k, e, I', hk, hμ⟩ := itBody_exec hH haW hN hu hd ht
      exact ⟨d', k, e, I', hk, hμ⟩) I₁
  obtain ⟨E₂, hil₂, hs₂⟩ := I₂
  rw [E₂.h77] at hx₂
  rcases hs₂ with ⟨hacc, hpi, -⟩ | ⟨-, hfound⟩
  · -- the search cannot run out: `u` is below the number of points
    exfalso
    have d_eq : c₂.nreg 150065 = H.length := by omega
    rw [d_eq, preLen_length] at hpi
    omega
  obtain ⟨c₃, k₃, e₃, o65⟩ : ∃ c₃ k₃, Exec P W (.instr (.copyN 150065 150079)) c₂ c₃ k₃ ∧
      c₃.nreg 150065 = c₂.nreg 150079 ∧ k₃ = 1 ∧ (∀ r, r ≠ 150065 → c₃.nreg r = c₂.nreg r) ∧
      c₃.nmem = c₂.nmem := by
    refine ⟨_, 1, Exec.copyN E₂.wb _ _, by config_simp, rfl, fun r hr => by simp [hr], rfl⟩
  obtain ⟨o65, hk₃, hr₃, hm₃⟩ := o65
  have ex : Exec P W itLook c c₃ (k₁ + (k₂ + k₃)) := .seq e₁ (.seq e₂ e₃)
  refine ⟨c₃, _, ex, ?_, exec_frameB ex wr_itLook, ?_⟩
  · have : H.length - c₁.nreg 150065 ≤ H.length := by omega
    have := Nat.mul_le_mul_left 22 this
    omega
  · rw [o65]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hfound
    exact ⟨h1, h2, h3, by rw [hr₃ _ (by omega)]; exact h4, by rw [hr₃ _ (by omega)]; exact h5,
      by rw [hr₃ _ (by omega)]; exact h6, by rw [hr₃ _ (by omega)]; exact h7⟩

/-! ## A walk vertex -/

/-- The registers written by `locV`. -/
def Bloc : ℕ → Bool := Bl [150060, 150061, 150062, 150063, 150064, 150065, 150066, 150067,
  150068, 150069, 150073, 150074, 150075, 150077, 150078, 150079]

theorem wr_locV : wr Bloc locV = true := ⌖

/-- The tour coordinate by one conditional subtraction. -/
def jOf (S i m2 : ℕ) : ℕ := if S + i < m2 then S + i else S + i - m2

theorem jOf_eq {S i m2 : ℕ} (hS : S ≤ m2) (hi : i < m2) : jOf S i m2 = (S + i) % m2 := by
  unfold jOf
  split_ifs with h
  · exact (Nat.mod_eq_of_lt h).symm
  · Ξ Nat.mod_eq_sub_mod (⋄), Nat.mod_eq_of_lt (⋄)

theorem sideE_jOf {S i m : ℕ} (hS : S ≤ 2 * m) (hi : i ≤ 2 * m) (hm : 1 ≤ m) :
    Chazelle.Chain.sideE m (jOf S i (2 * m)) = Chazelle.Chain.sideE m ((S + i) % (2 * m)) := by
  rcases hi.lt_or_eq with hi | rfl
  · Ξ jOf_eq hS hi
  · unfold jOf
    Ξ ite_eq_right (⋄), Nat.add_mod_right
    rcases hS.lt_or_eq with hS | rfl
    · Ξ Nat.mod_eq_of_lt hS, show S + 2 * m - 2 * m = S by omega
    · Ξ Nat.mod_self, show 2 * m + 2 * m - 2 * m = 2 * m by omega
      unfold Chazelle.Chain.sideE; split_ifs <;> omega

/-- The chain index as the machine computes it. -/
theorem kOf_eq (m J : ℕ) : (if J < m then J else 2 * m - J) = Chazelle.Chain.sideE m J := by
  unfold Chazelle.Chain.sideE; split_ifs <;> omega

/-- The facts `locV` needs about the chain registers. -/
structure ChainRegs (C : Chain) (N Hh : ℕ) (c : Config) : Prop where
  h21 : c.nreg 150021 = Hh
  h22 : c.nreg 150022 = C.s
  h23 : c.nreg 150023 = C.m
  h26 : c.nreg 150026 = N
  h28 : c.nreg 150028 = C.sideS C.sideBeta
  h29 : c.nreg 150029 = 2 * C.m
  h91 : c.nreg 150091 = 1
  h93 : c.nreg 150093 = 3
  h96 : c.nreg 150096 = 6

theorem ChainRegs.of_frame {C : Chain} {N Hh : ℕ} {c c' : Config} (h : ChainRegs C N Hh c)
    (hr : ∀ r, r ∈ [150021, 150022, 150023, 150026, 150028, 150029, 150091, 150093, 150096] →
      c'.nreg r = c.nreg r) : ChainRegs C N Hh c' :=
  ⟨(hr _ (✓)).trans h.h21, (hr _ (✓)).trans h.h22, (hr _ (✓)).trans h.h23,
    (hr _ (✓)).trans h.h26, (hr _ (✓)).trans h.h28, (hr _ (✓)).trans h.h29,
    (hr _ (✓)).trans h.h91, (hr _ (✓)).trans h.h93, (hr _ (✓)).trans h.h96⟩

/-- **A walk vertex of the double boundary**: tour position `i = v - 6`, coordinate `J`, chain
index `k = sideE m J`, climbing bit, host point `u = (C.s + k) mod N` and its item. -/
theorem locV_exec {P : Polygon} {W : ℕ} {C : Chain} {H : Host} {Hh v : ℕ} {m : ℕ → ℕ}
    (c : Config) (hw : WordsBounded W c) (hm : c.nmem = m) (hH : HostAt m Hh H)
    (R : ChainRegs C (H.pts P.n).length Hh c) (h44 : c.nreg 150044 = v) (hv6 : 6 ≤ v)
    (hv : v ≤ 2 * C.m + 6) (hs : C.s < (H.pts P.n).length) (hmN : C.m < (H.pts P.n).length)
    (haW : Hh + 3 * H.length + 4 ≤ W) (hNW : 2 * (H.pts P.n).length ≤ W) :
    ∃ c' k, Exec P W locV c c' k ∧ k ≤ 22 * H.length + 30 ∧ FrameB Bloc c c' ∧
      c'.nreg 150060 = v - 6 ∧ c'.nreg 150061 = jOf (C.sideS C.sideBeta) (v - 6) (2 * C.m) ∧
      c'.nreg 150062 = Chazelle.Chain.sideE C.m ((C.sideS C.sideBeta + (v - 6)) % (2 * C.m)) ∧
      (c'.nreg 150063 = 1 ↔ jOf (C.sideS C.sideBeta) (v - 6) (2 * C.m) < C.m) ∧
      c'.nreg 150063 ≤ 1 ∧
      c'.nreg 150064 = (C.s + Chazelle.Chain.sideE C.m
        ((C.sideS C.sideBeta + (v - 6)) % (2 * C.m))) % (H.pts P.n).length ∧
      ItFound P.n Hh (c'.nreg 150064) H m c' (c'.nreg 150065) := by
  have hS := C.sideS_lt C.sideBeta
  have hm1 := C.one_le
  set S := C.sideS C.sideBeta with hSdef
  set i := v - 6 with hi
  set J := jOf S i (2 * C.m) with hJ
  have hJle : J ≤ 2 * C.m := by rw [hJ]; unfold jOf; split_ifs <;> omega
  have hk := sideE_jOf hS (show i ≤ 2 * C.m by omega) hm1
  rw [← hJ] at hk
  set k := Chazelle.Chain.sideE C.m ((S + i) % (2 * C.m)) with hkdef
  have hkm : k ≤ C.m := by rw [← hk]; exact Chazelle.Chain.sideE_le hJle
  set N := (H.pts P.n).length with hN
  -- straight part
  obtain ⟨c₁, k₁, e₁, hk₁, o60, o75⟩ : ∃ c₁ k₁, Exec P W (block [.subN 150060 150044 150096,
      .subN 150075 150029 150028]) c c₁ k₁ ∧ k₁ = 2 ∧ c₁.nreg 150060 = i ∧
      c₁.nreg 150075 = 2 * C.m - S := by
    exec_block
    refine ⟨rfl, ?_, ?_⟩
    · config_simp; rw [h44, R.h96]
    · config_simp; rw [R.h29, R.h28]
  have f₁ := exec_frameB e₁ (B := Bl [150060, 150075]) (by decide)
  have R₁ : ChainRegs C N Hh c₁ := R.of_frame fun r hr => f₁.1 r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have w₁ := e₁.wb_right
  -- `J`
  obtain ⟨c₂, k₂, e₂, hk₂, o61, r₂⟩ : ∃ c₂ k₂, Exec P W (.ifLtN 150060 150075
      (.instr (.addN 150061 150028 150060)) (.instr (.subN 150061 150060 150075))) c₁ c₂ k₂ ∧
      k₂ ≤ 3 ∧ c₂.nreg 150061 = J ∧ ∀ r, r ≠ 150061 → c₂.nreg r = c₁.nreg r := by
    by_cases h : i < 2 * C.m - S
    · refine spec_ifLtN_true (by rw [o60, o75]; exact h) (spec_instr (Exec.addN w₁ _ _ _
        (by rw [R₁.h28, o60]; omega)) fun _ => ⟨by omega, ?_, fun r hr => by simp [hr]⟩)
      config_simp; rw [R₁.h28, o60, hJ]; unfold jOf; rw [ite_eq_left (by omega)]
    · refine spec_ifLtN_false (by rw [o60, o75]; exact h) (spec_instr (Exec.subN w₁ _ _ _)
        fun _ => ⟨by omega, ?_, fun r hr => by simp [hr]⟩)
      config_simp; rw [o60, o75, hJ]; unfold jOf; rw [ite_eq_right (by omega)]; omega
  have w₂ := e₂.wb_right
  -- `k` and the climbing bit
  obtain ⟨c₃, k₃, e₃, hk₃, o62, o63, o63', r₃⟩ : ∃ c₃ k₃, Exec P W (.ifLtN 150061 150023
      (block [.constN 150063 1, .copyN 150062 150061])
      (block [.constN 150063 0, .subN 150062 150029 150061])) c₂ c₃ k₃ ∧ k₃ ≤ 4 ∧
      c₃.nreg 150062 = k ∧ (c₃.nreg 150063 = 1 ↔ J < C.m) ∧ c₃.nreg 150063 ≤ 1 ∧
      ∀ r, r ≠ 150062 → r ≠ 150063 → c₃.nreg r = c₂.nreg r := by
    have e23 : c₂.nreg 150023 = C.m := by rw [r₂ _ (by omega), R₁.h23]
    have e29 : c₂.nreg 150029 = 2 * C.m := by rw [r₂ _ (by omega), R₁.h29]
    by_cases h : J < C.m
    · refine spec_ifLtN_true (by rw [o61, e23]; exact h) ?_
      exec_block
      · omega
      · refine ⟨by omega, ?_, by simp [h], by simp, fun r h1 h2 => by simp [h1, h2]⟩
        config_simp; rw [o61, ← hk, ← kOf_eq, ite_eq_left h]
    · refine spec_ifLtN_false (by rw [o61, e23]; exact h) ?_
      exec_block
      · omega
      · refine ⟨by omega, ?_, by simp [h], by simp, fun r h1 h2 => by simp [h1, h2]⟩
        config_simp; rw [o61, e29, ← hk, ← kOf_eq, ite_eq_right h]
  have w₃ := e₃.wb_right
  have e22 : c₃.nreg 150022 = C.s := by
    rw [r₃ _ (by omega) (by omega), r₂ _ (by omega), R₁.h22]
  have e26 : c₃.nreg 150026 = N := by
    rw [r₃ _ (by omega) (by omega), r₂ _ (by omega), R₁.h26]
  -- `u`
  obtain ⟨c₄, k₄, e₄, hk₄, o64, r₄⟩ : ∃ c₄ k₄, Exec P W (.seq (.instr (.addN 150075 150022 150062))
      (.ifLtN 150075 150026 (.instr (.copyN 150064 150075))
        (.instr (.subN 150064 150075 150026)))) c₃ c₄ k₄ ∧ k₄ ≤ 4 ∧
      c₄.nreg 150064 = (C.s + k) % N ∧
      ∀ r, r ≠ 150064 → r ≠ 150075 → c₄.nreg r = c₃.nreg r := by
    refine spec_seq (spec_instr (Exec.addN w₃ _ _ _ (by rw [e22, o62]; omega)) fun w' => ?_)
    by_cases h : C.s + k < N
    · refine spec_ifLtN_true (by config_simp; rw [e22, o62, e26]; exact h)
        (spec_instr (Exec.copyN w' _ _) fun _ => ⟨by omega, ?_, fun r h1 h2 => by simp [h1, h2]⟩)
      config_simp; rw [e22, o62, Nat.mod_eq_of_lt h]
    · refine spec_ifLtN_false (by config_simp; rw [e22, o62, e26]; exact h)
        (spec_instr (Exec.subN w' _ _ _) fun _ => ⟨by omega, ?_, fun r h1 h2 => by simp [h1, h2]⟩)
      config_simp; rw [e22, o62, e26, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  have w₄ := e₄.wb_right
  have f₄₃ : ∀ r, Bl [150061, 150062, 150063, 150064, 150075] r = false →
      c₄.nreg r = c₁.nreg r := by
    intro r hr
    have hne : ∀ a ∈ [150061, 150062, 150063, 150064, 150075], r ≠ a := fun a ha => ne_of_Bl hr ha
    rw [r₄ r (hne _ (by simp)) (hne _ (by simp)), r₃ r (hne _ (by simp)) (hne _ (by simp)),
      r₂ r (hne _ (by simp))]
  have R₄ : ChainRegs C N Hh c₄ := R₁.of_frame fun r hr => f₄₃ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have m₄ : c₄.nmem = m := by
    rw [← hm, ← f₁.2.2.1]
    exact (exec_frameB (.seq e₂ (.seq e₃ e₄)) (B := Bl [150061, 150062, 150063, 150064, 150075])
      (by decide)).2.2.1
  obtain ⟨c₅, k₅, e₅, hk₅, f₅, found⟩ := itLook_exec (P := P) c₄ w₄ m₄ hH R₄.h21 R₄.h91 R₄.h93
    o64 haW (by omega) (Nat.mod_lt _ (by omega))
  have ex : Exec P W locV c c₅ (k₁ + (k₂ + (k₃ + (k₄ + k₅)))) := by
    unfold locV
    exact .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))
  refine ⟨c₅, _, ex, by omega, exec_frameB ex wr_locV, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f₅.1 _ (by decide), f₄₃ _ (by decide), o60]
  · rw [f₅.1 _ (by decide), r₄ _ (by omega) (by omega), r₃ _ (by omega) (by omega), o61]
  · rw [f₅.1 _ (by decide), r₄ _ (by omega) (by omega), o62]
  · rw [f₅.1 _ (by decide), r₄ _ (by omega) (by omega), o63]
  · rw [f₅.1 _ (by decide), r₄ _ (by omega) (by omega)]; exact o63'
  · rw [f₅.1 _ (by decide), o64]
  · rw [show c₅.nreg 150064 = (C.s + k) % N by rw [f₅.1 _ (by decide), o64]]
    exact found

end

end ShootCut

end Chazelle.Core
