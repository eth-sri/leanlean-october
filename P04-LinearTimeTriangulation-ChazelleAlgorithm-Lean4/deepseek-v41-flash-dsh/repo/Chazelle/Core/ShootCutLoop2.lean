module

public import Chazelle.Golf

public import Chazelle.Core.ShootCutLoop

/-!
# WP-G, part 23: the main loop on the RAM

`LoopI`: the invariant of the main loop.  The current walk vertex `c` (register `150040`) has the
unwrapped position `U = Uof U₀ n c` (`n = 2m + 7`) with `U₀ ≤ U ≤ F`, the loop flag is `[U < F]`,
the pieces handed to `emit` since `U₀` form a path from `U₀` to `U` (`UPath`) of valid pieces,
and their number plus `G` times the potential is at most `G μ₀` (`G = 2 (log₂ γ + 1)`).

`loopBody_exec`: one iteration keeps the invariant and lowers the potential;
`mainLoop_exec`: the loop ends at `U = F`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK NFLoc

@[expose] public section

theorem Uof_mod {U₀ n c : ℕ} (hn : 0 < n) (hc : c < n) : Uof U₀ n c % n = c := by
  unfold Uof
  have ha := Nat.mod_lt U₀ hn
  Ξ Nat.add_mod, Nat.mod_mod
  by_cases h : c + n - U₀ % n < n
  · rw [Nat.mod_eq_of_lt h, show U₀ % n + (c + n - U₀ % n) = c + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hc]
  · rw [Nat.mod_eq_sub_mod (show n ≤ c + n - U₀ % n by omega),
      Nat.mod_eq_of_lt (show c + n - U₀ % n - n < n by omega),
      Nat.mod_eq_of_lt (show U₀ % n + (c + n - U₀ % n - n) < n by omega)]
    omega

theorem Uof_lt {U₀ n c : ℕ} (hn : 0 < n) : Uof U₀ n c < U₀ + n := by
  unfold Uof; have := Nat.mod_lt (c + n - U₀ % n) hn; omega

/-- The static facts of the main loop: the first and the final unwrapped positions are less
than a lap apart, the final vertex lies on the double boundary below the top, and every stretch
of the double boundary between them is at most `γ` long. -/
structure LStat (C : Chain) (U₀ F γ : ℕ) : Prop where
  hU₀F : U₀ ≤ F
  hUF : F < U₀ + (2 * C.m + 7)
  hF6 : 6 ≤ F % (2 * C.m + 7)
  hF5 : F % (2 * C.m + 7) ≤ 2 * C.m + 5
  hΓ : ∀ v L, U₀ ≤ v → v + L ≤ F → 6 ≤ v % (2 * C.m + 7) → v % (2 * C.m + 7) + L ≤ 2 * C.m + 6 →
    L ≤ γ

/-- **The invariant of the main loop.** -/
def LoopI (P : Polygon) (C : Chain) (H : Host) (Hh MD h γ mode : ℕ) (s e : WPos)
    (m₀ : ℕ → ℕ) (A₀ W : ℕ) (I : List Pc → Config → Prop) (ps₀ : List Pc) (U₀ F μ₀ : ℕ)
    (dI d : Config) : Prop :=
  WordsBounded W d ∧ CoreRegs P C H Hh MD h γ mode s e m₀ d ∧
    (∀ a, a < A₀ → d.nmem a = m₀ a) ∧
    (∀ r, 150000 ≤ r → r < 150044 → r ≠ 150040 → r ≠ 150042 → d.nreg r = dI.nreg r) ∧
    6 ≤ d.nreg 150040 ∧ d.nreg 150040 ≤ 2 * C.m + 6 ∧
    Uof U₀ (2 * C.m + 7) (d.nreg 150040) ≤ F ∧
    d.nreg 150042 = (if Uof U₀ (2 * C.m + 7) (d.nreg 150040) < F then 1 else 0) ∧
    ∃ ps', UPath (2 * C.m + 7) U₀ ps' (Uof U₀ (2 * C.m + 7) (d.nreg 150040)) ∧
      I (ps₀ ++ ps') d ∧ (∀ pc ∈ ps', PcOK P C m₀ h γ pc) ∧
      ps'.length + 2 * (Nat.log 2 γ + 1) *
        mu C (Qof P).n H F (Uof U₀ (2 * C.m + 7) (d.nreg 150040)) ≤
        2 * (Nat.log 2 γ + 1) * μ₀

variable {O : OracleIface} {P : Polygon} {C : Chain} {H : Host} {Hh h γ : ℕ} {m₀ : ℕ → ℕ}
  {A₀ W : ℕ}

/-- The flag after a step to the unwrapped position `U'`. -/
theorem flag_of {n U' F : ℕ} (hn : 0 < n) (hU' : U' ≤ F) (hF : F < U' + n) :
    (if U' % n = F % n then 0 else 1) = (if U' < F then 1 else 0) := by
  by_cases h : U' < F
  · Ξ ite_eq_right (resid_gap hn h hF).1, ite_eq_left h
  · Ξ show U' = F by omega, ite_eq_left rfl, ite_eq_right (lt_irrefl F)

/-- **One iteration of the main loop.** -/
theorem loopBody_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {emit : Stmt}
    {I : List Pc → Config → Prop} {K : ℕ} (hE : EmitOK P W emit A₀ (PcOK P C m₀ h γ) I K)
    {ps₀ : List Pc} {MD mode : ℕ} {s e : WPos} {U₀ F μ₀ : ℕ} (L : LStat C U₀ F γ)
    (dI : Config) (h41 : dI.nreg 150041 = F % (2 * C.m + 7)) (d : Config)
    (hL : LoopI P C H Hh MD h γ mode s e m₀ A₀ W I ps₀ U₀ F μ₀ dI d)
    (ht : d.nreg 150090 < d.nreg 150042) :
    ∃ d' k, Exec P W (.seq (.ifLtN 150040 150032 (cStep emit) (uStep emit)) setFlag) d d' k ∧
      LoopI P C H Hh MD h γ mode s e m₀ A₀ W I ps₀ U₀ F μ₀ dI d' ∧
      k ≤ (2 * K + 90) * (Nat.log 2 γ + 1) + 1700 ∧
      mu C (Qof P).n H F (Uof U₀ (2 * C.m + 7) (d'.nreg 150040)) <
        mu C (Qof P).n H F (Uof U₀ (2 * C.m + 7) (d.nreg 150040)) := by
  obtain ⟨hw, R, hm, hkI, h6, h2m, hUF', h42, ps', hpath, hI, hok, hcnt⟩ := hL
  set n := 2 * C.m + 7 with hn
  have hn0 : 0 < n := by omega
  set c := d.nreg 150040 with hc
  set U := Uof U₀ n c with hUdef
  have hU0 : U₀ ≤ U := by rw [hUdef]; unfold Uof; omega
  have hUlt : U < U₀ + n := Uof_lt hn0
  have hmod : U % n = c := Uof_mod hn0 (by omega)
  have hUF : U < F := by
    rw [R.h90, h42] at ht
    by_contra h'; rw [ite_eq_right h'] at ht; omega
  have hFU := L.hUF
  have hFn : F < U + n := by omega
  obtain ⟨hne, hgap⟩ := resid_gap hn0 hUF hFn
  rw [hmod] at hne hgap
  have hf41 : d.nreg 150041 = F % n := by rw [hkI _ (by omega) (by omega) (by omega) (by omega), h41]
  have hF6 := L.hF6
  have hF5 := L.hF5
  set f := F % n with hfdef
  have hG : 1 ≤ Nat.log 2 γ + 1 := by omega
  have hW1 : 1 ≤ W := by have := S.hW; unfold hostWords at this; omega
  by_cases hc2 : d.nreg 150040 < d.nreg 150032
  · -- a step on the double boundary
    have hc' : c < 2 * C.m + 6 := by rw [R.h32] at hc2; exact hc2
    have hlimF : U + limOf C c f ≤ F := by
      unfold limOf; split_ifs at hgap ⊢ <;> omega
    have hlimγ : limOf C c f ≤ γ := L.hΓ U _ hU0 hlimF (by rw [← hn, hmod]; omega)
      (by rw [← hn, hmod]; unfold limOf; split_ifs <;> omega)
    obtain ⟨d₁, k₁, Lc, ps'', ex₁, hk₁, post⟩ := cStep_exec S (hE.mono fun pc hp => hp.1)
      (ps := ps₀ ++ ps') d hw R hm hc.symm hf41 h6 hc' hF5 hne hlimγ hI
    have hLlim := post.Llim
    have hL1 := post.L1
    have hcL : c + Lc ≤ 2 * C.m + 6 := by
      have : c + limOf C c f ≤ 2 * C.m + 6 := by unfold limOf; split_ifs <;> omega
      omega
    obtain ⟨d₂, k₂, ex₂, hk₂, o42, r₂, m₂⟩ := setFlag_exec (P := P) d₁ post.wb hW1
    have a40 : d₂.nreg 150040 = c + Lc := by rw [r₂ _ (by omega), post.r40]
    have hmod' : (U + Lc) % n = c + Lc := by
      have := mod_shift (n := n) (x := c + Lc) hmod (by omega) (by omega)
      rwa [show U + (c + Lc - c) = U + Lc by omega] at this
    have hU₀ : Uof U₀ n (d₂.nreg 150040) = U + Lc := by
      rw [a40, ← hmod', Uof_eq hn0 (by omega) (by omega)]
    have hU' := hU₀
    have hkeep : ∀ r, 150000 ≤ r → r < 150044 → r ≠ 150040 → r ≠ 150042 →
        d₂.nreg r = d.nreg r := fun r h1 h2 h3 h4 => by
      rw [r₂ r h4, post.keep r h1 h2 h3]
    have hμ : mu C (Qof P).n H F (U + Lc) < mu C (Qof P).n H F U := by
      refine mu_lt (by omega) (by omega) ?_
      rcases post.brk with hb | hb | ⟨-, hb⟩
      · by_cases hfc : f < c
        · rw [show limOf C c f = 2 * C.m + 6 - c by unfold limOf; rw [ite_eq_left hfc]] at hb
          right; right; unfold BrkU BrkRes; left; rw [hmod']; omega
        · rw [show limOf C c f = f - c by unfold limOf; rw [ite_eq_right hfc]] at hb
          rw [ite_eq_left (show c < f by omega)] at hgap
          right; left; omega
      · right; right
        unfold BrkU BrkRes; rw [hmod']
        rcases (show c + Lc = 2 * C.m + 6 ∨ c + Lc < 2 * C.m + 6 by omega) with h' | h'
        · left; exact h'
        · right; refine ⟨by omega, h', ?_⟩
          rw [show c + Lc - 6 = c - 6 + Lc by omega]; exact hb
      · left
        unfold BrkU BrkRes; rw [hmod]
        right; exact ⟨h6, hc', hb⟩
    have hpath' : UPath n U₀ (ps' ++ ps'') (U + Lc) := by
      have := chained_upath (n := n) post.ch (fun pc hp => (post.pv pc hp).2) (by omega) U hmod
      rw [show U + (c + Lc - c) = U + Lc by omega] at this
      exact hpath.append ps'' this
    refine ⟨d₂, k₁ + 1 + k₂, .seq (.ifLtN_true hc2 ex₁) ex₂, ⟨ex₂.wb_right,
      R.of_frame' hkeep (by rw [r₂ _ (by omega)]; exact post.k90)
        (by rw [r₂ _ (by omega)]; exact post.k91) (by rw [r₂ _ (by omega)]; exact post.k92)
        (by rw [r₂ _ (by omega)]; exact post.k93) (by rw [r₂ _ (by omega)]; exact post.k96),
      fun a ha => by rw [m₂]; exact post.mem a ha,
      fun r h1 h2 h3 h4 => (hkeep r h1 h2 h3 h4).trans (hkI r h1 h2 h3 h4),
      by rw [a40]; omega, by rw [a40]; omega, by rw [hU']; omega, ?_,
      ps' ++ ps'', by rw [hU']; exact hpath',
      hE.stable _ _ _ (by rw [← List.append_assoc]; exact post.hI) (exec_frameB ex₂ (by decide)),
      fun pc hp => by
        rcases List.mem_append.1 hp with hp | hp
        · exact hok pc hp
        · exact (post.pv pc hp).1, ?_⟩, by omega, by rw [hU']; exact hμ⟩
    · rw [o42, hU', post.r40, post.keep _ (by omega) (by omega) (by omega), hf41, ← hmod']
      exact flag_of hn0 (by omega) (by omega)
    · rw [hU', List.length_append]
      have hlen := post.len
      have hlog : Nat.log 2 Lc ≤ Nat.log 2 γ := Nat.log_mono_right (by omega)
      have e1 : 2 * (Nat.log 2 γ + 1) * mu C (Qof P).n H F (U + Lc) + 2 * (Nat.log 2 γ + 1) ≤
          2 * (Nat.log 2 γ + 1) * mu C (Qof P).n H F U := by
        have := Nat.mul_le_mul_left (2 * (Nat.log 2 γ + 1)) (show
          mu C (Qof P).n H F (U + Lc) + 1 ≤ mu C (Qof P).n H F U by omega)
        rw [Nat.mul_add, mul_one] at this; exact this
      omega
  · -- through the uncounted block
    have hc' : c = 2 * C.m + 6 := by rw [R.h32] at hc2; omega
    obtain ⟨d₁, k₁, ex₁, hk₁, hI₁, o40, kp, mem₁⟩ := uStep_exec hE (ps := ps₀ ++ ps') (m := C.m)
      d hw R.h32 R.chain.h96 hI (uPc_ok P C m₀ h γ)
    obtain ⟨d₂, k₂, ex₂, hk₂, o42, r₂, m₂⟩ := setFlag_exec (P := P) d₁ ex₁.wb_right hW1
    have hmod' : (U + 7) % n = 6 := by
      rw [add_mod_split hn0 (by omega), hmod, ite_eq_right (by omega)]; omega
    have hF7 : U + 7 ≤ F := by
      rw [ite_eq_right (by omega)] at hgap; omega
    have a40 : d₂.nreg 150040 = 6 := by rw [r₂ _ (by omega), o40]
    have hU₀ : Uof U₀ n (d₂.nreg 150040) = U + 7 := by
      rw [a40, ← hmod', Uof_eq hn0 (by omega) (by omega)]
    have hU' := hU₀
    have hkeep : ∀ r, 150000 ≤ r → r < 150044 → r ≠ 150040 → r ≠ 150042 →
        d₂.nreg r = d.nreg r := fun r h1 h2 h3 h4 => by
      rw [r₂ r h4, kp r (Or.inl ⟨h1, h2⟩) h3]
    have kk : ∀ r, 150089 ≤ r → r < 150100 → d₂.nreg r = d.nreg r := fun r h1 h2 => by
      rw [r₂ r (by omega), kp r (Or.inr ⟨by omega, h2⟩) (by omega)]
    have hμ : mu C (Qof P).n H F (U + 7) < mu C (Qof P).n H F U := by
      refine mu_lt (by omega) hF7 (Or.inl ?_)
      unfold BrkU BrkRes; left; rw [hmod, hc']
    have hKc : 2 * K + 90 ≤ (2 * K + 90) * (Nat.log 2 γ + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    have hpath' : UPath n U₀ (ps' ++ [uPc C.m]) (U + 7) :=
      hpath.append [uPc C.m] ⟨by rw [hmod, hc']; rfl, U + 7, by omega, by rw [hmod']; rfl, rfl⟩
    refine ⟨d₂, k₁ + 2 + k₂, .seq (.ifLtN_false hc2 ex₁) ex₂, ⟨ex₂.wb_right,
      R.of_frame' hkeep (by rw [kk _ (by omega) (by omega)]; exact R.h90)
        (by rw [kk _ (by omega) (by omega)]; exact R.chain.h91)
        (by rw [kk _ (by omega) (by omega)]; exact R.h92)
        (by rw [kk _ (by omega) (by omega)]; exact R.chain.h93)
        (by rw [kk _ (by omega) (by omega)]; exact R.chain.h96),
      fun a ha => by rw [m₂, mem₁ a ha]; exact hm a ha,
      fun r h1 h2 h3 h4 => (hkeep r h1 h2 h3 h4).trans (hkI r h1 h2 h3 h4),
      by rw [a40], by rw [a40]; omega, by rw [hU']; omega, ?_,
      ps' ++ [uPc C.m], by rw [hU']; exact hpath',
      hE.stable _ _ _ (by rw [← List.append_assoc]; exact hI₁) (exec_frameB ex₂ (by decide)),
      fun pc hp => by
        rcases List.mem_append.1 hp with hp | hp
        · exact hok pc hp
        · simp only [List.mem_singleton] at hp; rw [hp]; exact uPc_ok P C m₀ h γ, ?_⟩,
      by omega, by rw [hU']; exact hμ⟩
    · rw [o42, hU', o40, kp _ (Or.inl ⟨by omega, by omega⟩) (by omega), hf41, ← hmod']
      exact flag_of hn0 hF7 (by omega)
    · rw [hU', List.length_append]
      have e1 : 2 * (Nat.log 2 γ + 1) * mu C (Qof P).n H F (U + 7) + 2 * (Nat.log 2 γ + 1) ≤
          2 * (Nat.log 2 γ + 1) * mu C (Qof P).n H F U := by
        have := Nat.mul_le_mul_left (2 * (Nat.log 2 γ + 1)) (show
          mu C (Qof P).n H F (U + 7) + 1 ≤ mu C (Qof P).n H F U by omega)
        rw [Nat.mul_add, mul_one] at this; exact this
      simp only [List.length_singleton]
      omega

/-- **The main loop**, from the first walk vertex (unwrapped `U₀`) to the final one (`F`). -/
theorem mainLoop_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {emit : Stmt}
    {I : List Pc → Config → Prop} {K : ℕ} (hE : EmitOK P W emit A₀ (PcOK P C m₀ h γ) I K)
    {ps₀ : List Pc} {MD mode : ℕ} {s e : WPos} {U₀ F μ₀ : ℕ} (L : LStat C U₀ F γ)
    (dI : Config) (h41 : dI.nreg 150041 = F % (2 * C.m + 7)) (d : Config)
    (hL : LoopI P C H Hh MD h γ mode s e m₀ A₀ W I ps₀ U₀ F μ₀ dI d) :
    ∃ d' k, Exec P W (mainLoop emit) d d' k ∧
      LoopI P C H Hh MD h γ mode s e m₀ A₀ W I ps₀ U₀ F μ₀ dI d' ∧
      Uof U₀ (2 * C.m + 7) (d'.nreg 150040) = F ∧
      k ≤ ((2 * K + 90) * (Nat.log 2 γ + 1) + 1702) *
        mu C (Qof P).n H F (Uof U₀ (2 * C.m + 7) (d.nreg 150040)) + 2 := by
  obtain ⟨d', k, ex, hL', hx, hk⟩ := Exec.whileLtN_bounded (P := P) (a := 150090) (b := 150042)
    (body := .seq (.ifLtN 150040 150032 (cStep emit) (uStep emit)) setFlag)
    (LoopI P C H Hh MD h γ mode s e m₀ A₀ W I ps₀ U₀ F μ₀ dI)
    (fun d => mu C (Qof P).n H F (Uof U₀ (2 * C.m + 7) (d.nreg 150040)))
    ((2 * K + 90) * (Nat.log 2 γ + 1) + 1700) (fun d hd => hd.1)
    (fun d hd ht => loopBody_exec S hE L dI h41 d hd ht) hL
  refine ⟨d', k, ex, hL', ?_, hk⟩
  obtain ⟨-, R', -, -, -, -, hUF, h42, -⟩ := hL'
  Ξ' R'.h90, h42 at hx
  by_contra hne
  Ξ' ite_eq_left (lt_of_le_of_ne hUF hne) at hx
  omega

end

end ShootCut

end Chazelle.Core
