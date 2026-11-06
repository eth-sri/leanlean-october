module

public import Chazelle.Golf

public import Chazelle.Core.ShootCutCutter

/-!
# WP-G, part 35: the arc-cutter's set-up and finish

* `cutInit`: the record pointer `A₀ + 1`, the list base `A₀`, the count `0`, and the limit
  `LIM = A₀ + 1 + 14700 (t + 1)` with `2^t ≥ γ` the first power of two (so `Nmax = 2100 (t + 1)`
  records fit, more than the core hands);
* `cutFin`: the count into the list header, the list address into `150010`, and the allocator
  raised one by one to the end of the list (so that it grows by at most the step count).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK NFLoc

@[expose] public section

/-- The doubling loop of the limit. -/
def cutLimBody : Stmt := block [.addN 140009 140009 140009, .addN 140007 140007 140008]

/-- The constants of the set-up. -/
def cutInitA : Stmt :=
  block [.constN 140003 1, .constN 140006 0, .constN 140008 14700, .constN 140002 0,
    .constN 140009 1]

/-- The pointers of the set-up. -/
def cutInitB : Stmt := block [.copyN 140001 ALLOC, .addN 140000 ALLOC 140003]

/-- The set-up of the arc-cutter. -/
def cutInit : Stmt :=
  .seq cutInitA (.seq cutInitB (.seq (.instr (.addN 140007 140000 140008))
    (.whileLtN 140009 150009 cutLimBody)))

/-- Raise the allocator one by one to the end of the list. -/
def cutBump : Stmt := .whileLtN ALLOC 140000 (.instr (.addN ALLOC ALLOC 140003))

/-- The finish of the arc-cutter. -/
def cutFin : Stmt := .seq (block [.storeN 140001 140002, .copyN 150010 140001]) cutBump

/-- **The arc-cutter.** -/
def cutter : Stmt := .seq cutInit (.seq (core cutEmit) cutFin)

/-- A `while` loop with a potential that pays for its steps, and a quantity that grows by at
most the step count. -/
theorem whileLtN_potential_lb' {P : Polygon} {W : ℕ} {a b : ℕ} {body : Stmt}
    (I : Config → Prop) (Φ ψ : Config → ℕ) (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → c.nreg a < c.nreg b →
      ∃ c' k, Exec P W body c c' k ∧ I c' ∧ Φ c' + k + 2 ≤ Φ c ∧ ψ c' ≤ ψ c + k)
    {c : Config} (hc : I c) :
    ∃ c' k, Exec P W (.whileLtN a b body) c c' k ∧ I c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      k ≤ Φ c + 2 ∧ ψ c' ≤ ψ c + k := by
  induction hn : Φ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    by_cases ht : c.nreg a < c.nreg b
    · obtain ⟨c₁, k₁, hb, hI₁, hΦ, hψ⟩ := hbody c hc ht
      obtain ⟨c', k₂, hl, hI', ht', hk₂, hψ'⟩ := ih (Φ c₁) (⋄) hI₁ rfl
      exact ⟨c', k₁ + 2 + k₂, .whileLtN_true ht hb hl, hI', ht', ⋄, ⋄⟩
    · exact ⟨c, 2, .whileLtN_false ht (hI c hc), hc, ht, ⋄, ⋄⟩

/-- **The set-up of the arc-cutter.** -/
theorem cutInit_exec {P : Polygon} {W : ℕ} (d : Config) (hw : WordsBounded W d) {γ A₀ : ℕ}
    {m₀ : ℕ → ℕ} (hm : ∀ a, a < A₀ → d.nmem a = m₀ a) (h09 : d.nreg 150009 = γ)
    (hA : d.nreg ALLOC = A₀) (hγW : 2 * γ ≤ W)
    (hroom : A₀ + 14700 * Nat.clog 2 γ + 14708 ≤ W) :
    ∃ d' k Nmax, Exec P W cutInit d d' k ∧ k ≤ 5 * Nat.clog 2 γ + 20 ∧
      CutI W A₀ Nmax m₀ [] d' ∧ 2100 * Nat.log 2 γ + 2100 ≤ Nmax ∧
      (∀ x, x / 10000 ≠ 14 → d'.nreg x = d.nreg x) ∧ d'.nmem = d.nmem := by
  have hAl : ALLOC = 9999 := rfl
  have hW1 : A₀ + 14708 ≤ W := by omega
  obtain ⟨da, ka, ea, hka, a03, a06, a08, a02, a09, ra, ma⟩ : ∃ d₁ k₁, Exec P W cutInitA d d₁ k₁ ∧
      k₁ = 5 ∧ d₁.nreg 140003 = 1 ∧ d₁.nreg 140006 = 0 ∧ d₁.nreg 140008 = 14700 ∧
      d₁.nreg 140002 = 0 ∧ d₁.nreg 140009 = 1 ∧
      (∀ x, x / 10000 ≠ 14 → d₁.nreg x = d.nreg x) ∧ d₁.nmem = d.nmem := by
    clear hroom hγW hm hA h09
    unfold cutInitA
    exec_block
    all_goals first | omega | skip
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl⟩
    all_goals first | (config_simp; done) | skip
    simp only [upd]; split_ifs <;> first | rfl | omega
  have hAa : da.nreg 9999 = A₀ := by rw [ra _ (by omega)]; exact hA
  obtain ⟨db, kb, eb, hkb, b01, b00, rb, mb⟩ : ∃ d₁ k₁, Exec P W cutInitB da d₁ k₁ ∧
      k₁ = 2 ∧ d₁.nreg 140001 = A₀ ∧ d₁.nreg 140000 = A₀ + 1 ∧
      (∀ x, x ≠ 140001 → x ≠ 140000 → d₁.nreg x = da.nreg x) ∧ d₁.nmem = da.nmem := by
    have ew := ea.wb_right
    clear hroom hγW hm hA h09 ea ra
    unfold cutInitB
    rw [hAl]
    exec_block
    all_goals first | (config_simp; rw [hAa, a03]; omega) | skip
    refine ⟨rfl, ?_, ?_, fun x h1 h2 => ?_, rfl⟩
    · config_simp; exact hAa
    · config_simp; rw [hAa, a03]
    · simp only [upd]; split_ifs <;> first | rfl | omega
  have b03 : db.nreg 140003 = 1 := by rw [rb _ (by omega) (by omega), a03]
  have b08 : db.nreg 140008 = 14700 := by rw [rb _ (by omega) (by omega), a08]
  have ec := Exec.addN (P := P) eb.wb_right 140007 140000 140008 (by rw [b00, b08]; omega)
  set d₁ := ({ db with nreg := upd db.nreg 140007 (db.nreg 140000 + db.nreg 140008) } : Config)
    with hd₁
  have r₁ : ∀ x, x / 10000 ≠ 14 → d₁.nreg x = d.nreg x := fun x hx => by
    simp only [hd₁, upd]
    rw [ite_eq_right (by omega), rb x (by omega) (by omega), ra x hx]
  have g₁ : ∀ x, x ≠ 140007 → d₁.nreg x = db.nreg x := fun x hx => by
    simp only [hd₁, upd]; rw [ite_eq_right hx]
  have o03 : d₁.nreg 140003 = 1 := by rw [g₁ _ (by omega)]; exact b03
  have o06 : d₁.nreg 140006 = 0 := by rw [g₁ _ (by omega), rb _ (by omega) (by omega)]; exact a06
  have o08 : d₁.nreg 140008 = 14700 := by rw [g₁ _ (by omega)]; exact b08
  have o01 : d₁.nreg 140001 = A₀ := by rw [g₁ _ (by omega)]; exact b01
  have o00 : d₁.nreg 140000 = A₀ + 1 := by rw [g₁ _ (by omega)]; exact b00
  have o02 : d₁.nreg 140002 = 0 := by rw [g₁ _ (by omega), rb _ (by omega) (by omega)]; exact a02
  have o09 : d₁.nreg 140009 = 1 := by rw [g₁ _ (by omega), rb _ (by omega) (by omega)]; exact a09
  have o07 : d₁.nreg 140007 = A₀ + 1 + 14700 := by
    simp only [hd₁, upd, ↓reduceIte]; rw [b00, b08]
  have m₁ : d₁.nmem = d.nmem := by
    show db.nmem = d.nmem; rw [mb, ma]
  -- the doubling loop
  obtain ⟨T, hT⟩ : ∃ T, Nat.clog 2 γ = T := ⟨_, rfl⟩
  rw [hT] at hroom
  let Inv : Config → Prop := fun c => WordsBounded W c ∧ c.nmem = d.nmem ∧
    (∀ x, x / 10000 ≠ 14 → c.nreg x = d.nreg x) ∧ c.nreg 140003 = 1 ∧ c.nreg 140006 = 0 ∧
    c.nreg 140008 = 14700 ∧ c.nreg 140001 = A₀ ∧ c.nreg 140000 = A₀ + 1 ∧ c.nreg 140002 = 0 ∧
    ∃ t, c.nreg 140009 = 2 ^ t ∧ c.nreg 140007 = A₀ + 1 + (14700 * t + 14700) ∧ t ≤ T
  have I₁ : Inv d₁ := ⟨ec.wb_right, m₁, r₁, o03, o06, o08, o01, o00, o02, 0, by rw [o09, pow_zero],
    by rw [o07], Nat.zero_le _⟩
  obtain ⟨d₂, k₂, e₂, I₂, hx₂, hk₂⟩ := Exec.whileLtN_bounded (P := P) (a := 140009) (b := 150009)
    (body := cutLimBody) Inv
    (fun c => T + 1 - (Nat.log 2 (c.nreg 140009))) 2 (fun c hc => hc.1)
    (fun c ⟨hw', hm', hr', h3, h6, h8, h1, h0, h2, t, h9, h7, ht⟩ hlt => by
      have g9 : c.nreg 150009 = γ := by rw [hr' _ (by omega), h09]
      rw [h9, g9] at hlt
      have htc : t < T := by rw [← hT]; exact (Nat.lt_clog_iff_pow_lt (by norm_num)).2 hlt
      have hmul := Nat.mul_le_mul_left 14700 (show t + 1 ≤ T from htc)
      have hW7 : A₀ + 1 + (14700 * t + 14700) + 14700 ≤ W := by
        rw [Nat.mul_succ] at hmul; omega
      unfold cutLimBody
      obtain ⟨c', k, e, hk, o9, o7, r', m'⟩ : ∃ c' k, Exec P W (block [.addN 140009 140009 140009,
          .addN 140007 140007 140008]) c c' k ∧ k = 2 ∧ c'.nreg 140009 = 2 ^ (t + 1) ∧
          c'.nreg 140007 = A₀ + 1 + (14700 * t + 14700) + 14700 ∧
          (∀ x, x ≠ 140009 → x ≠ 140007 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem := by
        have h2W : 2 ^ t + 2 ^ t ≤ W := by omega
        clear hroom hγW hm hmul hlt
        exec_block
        all_goals first | (config_simp; rw [h9]; omega) | (config_simp; rw [h7, h8]; omega) |
          skip
        refine ⟨rfl, ?_, ?_, fun x h1 h2 => ?_, rfl⟩
        · config_simp; rw [h9, pow_succ]; ring
        · config_simp; rw [h7, h8]
        · simp only [upd]; split_ifs <;> first | rfl | omega
      refine ⟨c', k, e, ⟨e.wb_right, by rw [m', hm'], fun x hx => by
        rw [r' x (by omega) (by omega), hr' x hx], by rw [r' _ (by omega) (by omega), h3],
        by rw [r' _ (by omega) (by omega), h6], by rw [r' _ (by omega) (by omega), h8],
        by rw [r' _ (by omega) (by omega), h1], by rw [r' _ (by omega) (by omega), h0],
        by rw [r' _ (by omega) (by omega), h2], t + 1, o9, by rw [o7]; ring, by omega⟩,
        by omega, ?_⟩
      rw [o9, h9, Nat.log_pow (by norm_num), Nat.log_pow (by norm_num)]
      omega) I₁
  obtain ⟨hw₂, hm₂, hr₂, h3, h6, h8, h1, h0, h2, t, h9, h7, ht⟩ := I₂
  have g9 : d₂.nreg 150009 = γ := by rw [hr₂ _ (by omega), h09]
  rw [h9, g9] at hx₂
  have hlog : Nat.log 2 γ ≤ t := by
    rcases Nat.eq_zero_or_pos γ with h0' | hpos
    · rw [h0']; simp
    · have := Nat.log_lt_of_lt_pow (b := 2) (x := t + 1) (y := γ) (by omega)
        (by rw [pow_succ]; omega)
      omega
  have hmul := Nat.mul_le_mul_left 14700 ht
  have hlog' := Nat.mul_le_mul_left 2100 hlog
  refine ⟨d₂, ka + (kb + (1 + k₂)), 2100 * t + 2100, .seq ea (.seq eb (.seq ec e₂)), ?_,
    ⟨by rw [hr₂ _ (by rw [hAl]; omega)]; exact hA, h1, h3, h6, by rw [h7]; ring, by linarith, fun a ha => by rw [hm₂]; exact hm a ha,
    by rw [h0, List.length_nil, Nat.zero_min, Nat.mul_zero, Nat.add_zero],
    by rw [h2, List.length_nil, Nat.zero_min], fun i hi => by simp at hi⟩, by omega, hr₂, hm₂⟩
  have hl1 : Nat.log 2 (d₁.nreg 140009) = 0 := by rw [o09]; exact Nat.log_one_right 2
  rw [hl1] at hk₂
  rw [hT]
  omega

/-- **The finish of the arc-cutter.** -/
theorem cutFin_exec {P : Polygon} {W A₀ Nmax : ℕ} {m₀ : ℕ → ℕ} {ps : List Pc} (d : Config)
    (hw : WordsBounded W d) (hI : CutI W A₀ Nmax m₀ ps d) (hq : ps.length ≤ Nmax) :
    ∃ d' k, Exec P W cutFin d d' k ∧ k ≤ 21 * ps.length + 10 ∧ d'.nreg 150010 = A₀ ∧
      d'.nmem A₀ = ps.length ∧ (∀ a, a ≠ A₀ → d'.nmem a = d.nmem a) ∧
      d'.nreg ALLOC = A₀ + 1 + 7 * ps.length ∧ d'.nreg ALLOC ≤ d.nreg ALLOC + k ∧
      (∀ x, x ≠ ALLOC → x ≠ 150010 → d'.nreg x = d.nreg x) ∧ d'.rreg = d.rreg ∧
      d'.rmem = d.rmem ∧ d'.output = d.output := by
  have hAl : ALLOC = 9999 := rfl
  obtain ⟨hA, hB, h1, -, -, hLW, -, hp, hc, -⟩ := hI
  rw [min_eq_left hq] at hp hc
  obtain ⟨d₁, k₁, e₁, hk₁, o10, om, omo, r₁, rr₁, rm₁, oo₁⟩ : ∃ d₁ k₁, Exec P W
      (block [.storeN 140001 140002, .copyN 150010 140001]) d d₁ k₁ ∧ k₁ = 2 ∧
      d₁.nreg 150010 = A₀ ∧ d₁.nmem A₀ = ps.length ∧ (∀ a, a ≠ A₀ → d₁.nmem a = d.nmem a) ∧
      (∀ x, x ≠ 150010 → d₁.nreg x = d.nreg x) ∧ d₁.rreg = d.rreg ∧ d₁.rmem = d.rmem ∧
      d₁.output = d.output := by
    exec_block
    refine ⟨rfl, by config_simp; exact hB, ?_, fun a ha => ?_, fun x hx => ?_, rfl, rfl, rfl⟩
    · ϴ upd, Config.nmem_mk, hB, ↓reduceIte, hc
    · simp only [upd, Config.nmem_mk, hB]; rw [ite_eq_right ha]
    · simp only [upd, Config.nreg_mk]; rw [ite_eq_right hx]
  set E := A₀ + 1 + 7 * ps.length with hE
  let Inv : Config → Prop := fun c => WordsBounded W c ∧ c.nreg ALLOC ≤ E ∧
    (∀ x, x ≠ ALLOC → c.nreg x = d₁.nreg x) ∧ c.nmem = d₁.nmem ∧ c.rreg = d₁.rreg ∧
    c.rmem = d₁.rmem ∧ c.output = d₁.output
  have a0 : d₁.nreg ALLOC = A₀ := by rw [r₁ _ (by rw [hAl]; omega)]; exact hA
  obtain ⟨d₂, k₂, e₂, ⟨hw₂, hA₂, hr₂, hm₂, hrr₂, hrm₂, ho₂⟩, hx₂, hk₂, hψ⟩ :=
    whileLtN_potential_lb' (P := P) (W := W) (a := ALLOC) (b := 140000)
    (body := .instr (.addN ALLOC ALLOC 140003)) Inv (fun c => 3 * (E - c.nreg ALLOC))
    (fun c => c.nreg ALLOC) (fun c h => h.1)
    (fun c ⟨hw', hA', hr', hm', hrr', hrm', ho'⟩ ht => by
      have e3 : c.nreg 140003 = 1 := by rw [hr' _ (by rw [hAl]; omega), r₁ _ (⋄), h1]
      have e0 : c.nreg 140000 = E := by rw [hr' _ (by rw [hAl]; omega), r₁ _ (⋄), hp]
      rw [e0] at ht
      have ex := Exec.addN (P := P) hw' ALLOC ALLOC 140003 (by rw [e3]; omega)
      refine ⟨_, 1, ex, ⟨ex.wb_right, ?_, fun x hx => ?_, hm', hrr', hrm', ho'⟩, ?_, ?_⟩
      · simp only [Config.nreg_mk, Machine.upd_same]; rw [e3]; omega
      · simp only [Config.nreg_mk]; rw [Machine.upd_other _ _ _ hx]; exact hr' x hx
      · simp only [Config.nreg_mk, Machine.upd_same]; rw [e3]; omega
      · simp only [Config.nreg_mk, Machine.upd_same]; rw [e3])
    ⟨e₁.wb_right, by rw [a0]; omega, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  have e0 : d₂.nreg 140000 = E := by rw [hr₂ _ (by rw [hAl]; omega), r₁ _ (⋄), hp]
  rw [e0] at hx₂
  refine ⟨d₂, k₁ + k₂, by unfold cutFin cutBump; exact .seq e₁ e₂, ?_, ?_, ?_, fun a ha => ?_,
    ⋄, ?_, fun x h1 h2 => ?_, by rw [hrr₂, rr₁], by rw [hrm₂, rm₁], by rw [ho₂, oo₁]⟩
  · rw [a0] at hk₂; omega
  · Ξ hr₂ _ (by rw [hAl]; omega), o10
  · Ξ hm₂, om
  · Ξ hm₂, omo a ha
  · rw [a0] at hψ; omega
  · Ξ hr₂ x h1, r₁ x h2

end

end ShootCut

end Chazelle.Core
