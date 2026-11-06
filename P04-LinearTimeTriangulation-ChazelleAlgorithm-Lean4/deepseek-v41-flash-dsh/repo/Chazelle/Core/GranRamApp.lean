module

public import Chazelle.Golf

public import Chazelle.Core.GranRamBody

/-!
# WP-F, RAM part 5: statements with stores, and the filtering append loop

* `wrS B s`: every instruction of `s` writes a register of `B` or stores into natural memory;
  `exec_frameS`: such a statement changes no other register, no real register or memory outside
  `B` and not the output.
* `appLoop rs rn`: append the entries `≠ c` (`c = r62`) of the list at `rs` of length `rn` to the
  scratch list at `r44` of length `r100` (`appLoop_exec`).
-/

namespace Chazelle.Core

namespace Gran

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-- A register write accepted by `B`, or a natural store. -/
def wrSOK (B : ℕ → Bool) : Instr → Bool
  | .storeN _ _ => true
  | i => wrOK B i

/-- Every instruction of the statement satisfies `wrSOK B`. -/
def wrS (B : ℕ → Bool) : Stmt → Bool
  | .skip => true
  | .instr i => wrSOK B i
  | .seq s t => wrS B s && wrS B t
  | .ifLtN _ _ t e => wrS B t && wrS B e
  | .ifLtR _ _ t e => wrS B t && wrS B e
  | .whileLtN _ _ b => wrS B b
  | .whileLtR _ _ b => wrS B b

/-- Registers outside `B`, real memory and the output agree. -/
def FrameS (B : ℕ → Bool) (c c' : Config) : Prop :=
  (∀ r, B r = false → c'.nreg r = c.nreg r) ∧ (∀ r, B r = false → c'.rreg r = c.rreg r) ∧
    c'.rmem = c.rmem ∧ c'.output = c.output

theorem FrameS.trans {B : ℕ → Bool} {c₁ c₂ c₃ : Config} (h₁ : FrameS B c₁ c₂)
    (h₂ : FrameS B c₂ c₃) : FrameS B c₁ c₃ :=
  ⟨fun r hr => (h₂.1 r hr).trans (h₁.1 r hr), fun r hr => (h₂.2.1 r hr).trans (h₁.2.1 r hr),
    h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.trans h₁.2.2.2⟩

/-- **Frame of a statement with stores.** -/
theorem exec_frameS {P : Polygon} {W : ℕ} {B : ℕ → Bool} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) (hs : wrS B s = true) : FrameS B c c' := by
  induction h with
  | skip _ => exact ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
  | @instr ins c c' _ he _ _ =>
    ϴ' wrS at hs
    cases ins <;> ϴ' wrSOK, wrOK, Bool.false_eq_true at hs <;>
      ϴ' Instr.effect, Option.some.injEq at he <;>
      (try split at he) <;> (try simp only [Option.some.injEq, reduceCtorEq] at he) <;> subst he <;>
      refine ⟨fun j hj => ?_, fun j hj => ?_, rfl, rfl⟩ <;>
      first
      | rfl
      | (simp only [upd]; split_ifs with hh
         · subst hh; simp_all
         · rfl)
  | seq _ _ ih₁ ih₂ =>
    ϴ' wrS, Bool.and_eq_true at hs
    exact (ih₁ hs.1).trans (ih₂ hs.2)
  | ifLtN_true _ _ ih =>
    ϴ' wrS, Bool.and_eq_true at hs; exact ih hs.1
  | ifLtN_false _ _ ih =>
    ϴ' wrS, Bool.and_eq_true at hs; exact ih hs.2
  | ifLtR_true _ _ ih =>
    ϴ' wrS, Bool.and_eq_true at hs; exact ih hs.1
  | ifLtR_false _ _ ih =>
    ϴ' wrS, Bool.and_eq_true at hs; exact ih hs.2
  | whileLtN_false _ _ => exact ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
  | whileLtN_true _ _ _ ih₁ ih₂ => exact (ih₁ hs).trans (ih₂ hs)
  | whileLtR_false _ _ => exact ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
  | whileLtR_true _ _ _ ih₁ ih₂ => exact (ih₁ hs).trans (ih₂ hs)

/-! ## The filtering append loop -/

/-- Append `r102` to the scratch list (`r44` base, `r100` length). -/
def appendV : Stmt := block [.addN 90105 90044 90100, .storeN 90105 90102, .addN 90100 90100 90019]

/-- One step: `v := m[rs + t]`; append `v` if `v ≠ c`; `t := t + 1`. -/
def appBody (rs : ℕ) : Stmt :=
  .seq (block [.addN 90105 rs 90101, .loadN 90102 90105])
    (.seq (.ifLtN 90102 90062 appendV (.ifLtN 90062 90102 appendV .skip))
      (.instr (.addN 90101 90101 90019)))

/-- The loop over `t < r rn`. -/
def appLoop (rs rn : ℕ) : Stmt := .whileLtN 90101 rn (appBody rs)

/-- The registers the loop writes. -/
def Bapp (r : ℕ) : Bool := decide (r = 90100) || decide (r = 90101) || decide (r = 90102) ||
  decide (r = 90105)

/-- The facts the loop keeps. -/
structure AppI (W rs rn S T D' cc ℓ₀ : ℕ) (l P₀ : List ℕ) (m₀ : ℕ → ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  t_le : c.nreg 90101 ≤ l.length
  len : c.nreg 90100 = ℓ₀ + ((l.take (c.nreg 90101)).filter (· != cc)).length
  tmp : ∀ i, i < c.nreg 90100 →
    c.nmem (T + i) = (P₀ ++ (l.take (c.nreg 90101)).filter (· != cc)).getD i 0
  frame : ∀ a, (a < T + ℓ₀ ∨ T + D' ≤ a) → c.nmem a = m₀ a
  rs : c.nreg rs = S
  rn : c.nreg rn = l.length
  r62 : c.nreg 90062 = cc
  r44 : c.nreg 90044 = T
  r19 : c.nreg 90019 = 1

theorem take_succ_filter (l : List ℕ) (t cc : ℕ) (ht : t < l.length) :
    (l.take (t + 1)).filter (· != cc) =
      (l.take t).filter (· != cc) ++ if l.getD t 0 != cc then [l.getD t 0] else [] := by
  Ξ List.take_add_one, List.filter_append, List.getElem?_eq_getElem ht
  simp only [Option.toList_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht,
    Option.getD_some]
  Ξ List.filter_cons
  split_ifs <;> simp

theorem getD_append_left {l₁ l₂ : List ℕ} {i : ℕ} (h : i < l₁.length) :
    (l₁ ++ l₂).getD i 0 = l₁.getD i 0 := by
  Ξ List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h

theorem getD_append_len (l₁ : List ℕ) (v : ℕ) (l₂ : List ℕ) :
    (l₁ ++ v :: l₂).getD l₁.length 0 = v := by
  Ξ List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)
  simp

/-- **The filtering append loop.** -/
theorem appLoop_exec {P : Polygon} {W rs rn S T D' cc ℓ₀ : ℕ} {l P₀ : List ℕ} (c : Config)
    (hrs : rs ≠ 90100 ∧ rs ≠ 90101 ∧ rs ≠ 90102 ∧ rs ≠ 90105 ∧ rs ≠ 90062 ∧ rs ≠ 90044 ∧
      rs ≠ 90019)
    (hrn : rn ≠ 90100 ∧ rn ≠ 90101 ∧ rn ≠ 90102 ∧ rn ≠ 90105 ∧ rn ≠ 90062 ∧ rn ≠ 90044 ∧
      rn ≠ 90019 ∧ rn ≠ rs)
    (hw : WordsBounded W c) (h101 : c.nreg 90101 = 0) (h100 : c.nreg 90100 = ℓ₀)
    (hP : P₀.length = ℓ₀) (hP₀ : ∀ i, i < ℓ₀ → c.nmem (T + i) = P₀.getD i 0)
    (hS : c.nreg rs = S) (hN : c.nreg rn = l.length) (h62 : c.nreg 90062 = cc)
    (h44 : c.nreg 90044 = T) (h19 : c.nreg 90019 = 1)
    (hsrc : ∀ t, t < l.length → c.nmem (S + t) = l.getD t 0)
    (hdisj : ∀ t, t < l.length → S + t < T ∨ T + D' ≤ S + t)
    (hroom : ℓ₀ + l.length ≤ D') (hTW : T + D' ≤ W) (hSW : S + l.length ≤ W) :
    ∃ c' k, Exec P W (appLoop rs rn) c c' k ∧ k ≤ 14 * l.length + 2 ∧
      c'.nreg 90100 = ℓ₀ + (l.filter (· != cc)).length ∧
      (∀ i, i < c'.nreg 90100 → c'.nmem (T + i) = (P₀ ++ l.filter (· != cc)).getD i 0) ∧
      (∀ a, (a < T + ℓ₀ ∨ T + D' ≤ a) → c'.nmem a = c.nmem a) ∧
      FrameS Bapp c c' := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := hrs
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := hrn
  have hWB : ∀ c₁ : Config, AppI W rs rn S T D' cc ℓ₀ l P₀ c.nmem c₁ → WordsBounded W c₁ :=
    fun _ h => h.wb
  have I0 : AppI W rs rn S T D' cc ℓ₀ l P₀ c.nmem c :=
    ⟨hw, by omega, by rw [h101, h100]; simp, fun i hi => by
      rw [h101, h100] at *; simp only [List.take_zero, List.filter_nil, List.append_nil]
      exact hP₀ i hi, fun _ _ => rfl, hS, hN, h62, h44, h19⟩
  obtain ⟨c', k, e, I', hx, hk⟩ := Exec.whileLtN_bounded (P := P) (a := 90101) (b := rn)
    (body := appBody rs) (AppI W rs rn S T D' cc ℓ₀ l P₀ c.nmem)
    (fun d => l.length - d.nreg 90101) 12 hWB
    (fun d hI ht => by
      obtain ⟨hwd, ht_le, hlen, htmp, hfr, hrs', hrn', h62', h44', h19'⟩ := hI
      rw [hrn'] at ht
      set t := d.nreg 90101 with htdef
      have hflen : ((l.take t).filter (· != cc)).length ≤ t := by
        calc _ ≤ (l.take t).length := List.length_filter_le _ _
          _ ≤ t := List.length_take_le _ _
      -- load `v`
      obtain ⟨d₁, k₁, e₁, hk₁, q⟩ : ∃ d₁ k₁, Exec P W (block [.addN 90105 rs 90101,
          .loadN 90102 90105]) d d₁ k₁ ∧ k₁ = 2 ∧ (d₁.nreg 90102 = l.getD t 0 ∧
          (∀ r, r ≠ 90105 → r ≠ 90102 → d₁.nreg r = d.nreg r) ∧ d₁.nmem = d.nmem) := by
        exec_block
        · rw [hrs']; omega
        · refine ⟨rfl, ?_, fun r a1 a2 => by simp [upd, a1, a2], rfl⟩
          config_simp; rw [hrs', hfr _ (by rcases hdisj t ht with h | h <;> omega), hsrc t ht]
      obtain ⟨q102, qr, qm⟩ := q
      have hw₁ := e₁.wb_right
      -- append or skip
      have happ : ∀ d₂ : Config, WordsBounded W d₂ → d₂.nreg 90102 = l.getD t 0 →
          (∀ r, r ≠ 90105 → r ≠ 90102 → d₂.nreg r = d.nreg r) → d₂.nmem = d.nmem →
          ∃ d₃ k₃, Exec P W appendV d₂ d₃ k₃ ∧ k₃ = 3 ∧
            d₃.nreg 90100 = d.nreg 90100 + 1 ∧ d₃.nmem = upd d.nmem (T + d.nreg 90100) (l.getD t 0)
            ∧ (∀ r, r ≠ 90105 → r ≠ 90102 → r ≠ 90100 → d₃.nreg r = d.nreg r) := by
        intro d₂ hw₂ v2 r2' m2
        unfold appendV
        exec_block
        · rw [r2' _ (by decide) (by decide), r2' _ (by decide) (by decide), h44']
          omega
        · config_simp; rw [r2' _ (by decide) (by decide), r2' _ (by decide) (by decide), h19']
          omega
        · refine ⟨rfl, ?_, ?_, fun r a1 a2 a3 => by simp [upd, a1, a3, r2' r a1 a2]⟩
          · config_simp; rw [r2' _ (by decide) (by decide), r2' _ (by decide) (by decide), h19']
          · config_simp
            rw [r2' _ (by decide) (by decide), r2' _ (by decide) (by decide), h44', v2, m2]
      -- the step as a whole
      have hfs := take_succ_filter l t cc ht
      have hv : d₁.nreg 90062 = cc := by rw [qr _ (by decide) (by decide), h62']
      -- the increment and the invariant, from the state after the (possible) append
      have fin : ∀ (d₂ : Config) (k₂ : ℕ), WordsBounded W d₂ → k₂ ≤ 8 →
          Exec P W (.ifLtN 90102 90062 appendV (.ifLtN 90062 90102 appendV .skip)) d₁ d₂ k₂ →
          (∀ r, r ≠ 90105 → r ≠ 90102 → r ≠ 90100 → d₂.nreg r = d.nreg r) →
          d₂.nreg 90100 = ℓ₀ + ((l.take (t + 1)).filter (· != cc)).length →
          (∀ i, i < d₂.nreg 90100 → d₂.nmem (T + i) =
            (P₀ ++ (l.take (t + 1)).filter (· != cc)).getD i 0) →
          (∀ a, (a < T + ℓ₀ ∨ T + D' ≤ a) → d₂.nmem a = c.nmem a) →
          ∃ d₄ k₄, Exec P W (.seq (.ifLtN 90102 90062 appendV
            (.ifLtN 90062 90102 appendV .skip)) (.instr (.addN 90101 90101 90019))) d₁ d₄ k₄ ∧
            k₄ ≤ 10 ∧ AppI W rs rn S T D' cc ℓ₀ l P₀ c.nmem d₄ ∧ d₄.nreg 90101 = t + 1 := by
        intro d₂ k₂ hw₂ hk₂ ex₂ r2' l2 t2 f2
        have e19 : d₂.nreg 90019 = 1 := by rw [r2' 90019 (by decide) (by decide) (by decide), h19']
        have e101 : d₂.nreg 90101 = t := r2' 90101 (by decide) (by decide) (by decide)
        obtain ⟨d₅, ex, v101, vr, vm⟩ : ∃ d₅, Exec P W (.instr (.addN 90101 90101 90019)) d₂ d₅ 1 ∧
            d₅.nreg 90101 = t + 1 ∧ (∀ r, r ≠ 90101 → d₅.nreg r = d₂.nreg r) ∧
            d₅.nmem = d₂.nmem :=
          ⟨_, Exec.addN hw₂ 90101 90101 90019 (by rw [e19, e101]; omega),
            by simp [upd, e19, e101], fun r hr => by simp [upd, hr], rfl⟩
        refine ⟨_, _, .seq ex₂ ex, by omega, ⟨ex.wb_right, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
          v101⟩
        · rw [v101]; omega
        · rw [v101, vr _ (by decide), l2]
        · rw [v101, vr _ (by decide), vm]; exact t2
        · rw [vm]; exact f2
        · rw [vr _ r2, r2' _ r4 r3 r1, hrs']
        · rw [vr _ n2, r2' _ n4 n3 n1, hrn']
        · rw [vr _ (by decide), r2' _ (by decide) (by decide) (by decide), h62']
        · rw [vr _ (by decide), r2' _ (by decide) (by decide) (by decide), h44']
        · rw [vr _ (by decide), e19]
      have key : ∃ d₄ k₄, Exec P W (.seq (.ifLtN 90102 90062 appendV
          (.ifLtN 90062 90102 appendV .skip)) (.instr (.addN 90101 90101 90019))) d₁ d₄ k₄ ∧
          k₄ ≤ 10 ∧ AppI W rs rn S T D' cc ℓ₀ l P₀ c.nmem d₄ ∧ d₄.nreg 90101 = t + 1 := by
        by_cases hne : l.getD t 0 = cc
        · -- skip
          have hn1 : ¬ d₁.nreg 90102 < d₁.nreg 90062 := by rw [q102, hv, hne]; omega
          have hn2 : ¬ d₁.nreg 90062 < d₁.nreg 90102 := by rw [q102, hv, hne]; omega
          have hfs' : (l.take (t + 1)).filter (· != cc) = (l.take t).filter (· != cc) := by
            rw [hfs, hne]; simp
          refine fin d₁ _ hw₁ (by omega) (.ifLtN_false hn1 (.ifLtN_false hn2 (.skip hw₁)))
            (fun r a1 a2 _ => qr r a1 a2) ?_ ?_ ?_
          · rw [qr _ (by decide) (by decide), hlen, hfs']
          · intro i hi; rw [qm, hfs']; rw [qr _ (by decide) (by decide)] at hi; exact htmp i hi
          · intro a ha; rw [qm]; exact hfr a ha
        · -- append
          have hbit : (l.getD t 0 != cc) = true := by simpa using hne
          have hfs' : (l.take (t + 1)).filter (· != cc) =
              (l.take t).filter (· != cc) ++ [l.getD t 0] := by rw [hfs, ite_eq_left hbit]
          obtain ⟨d₂, k₂, e₂, hk₂, l2, m2, r2'⟩ := happ d₁ hw₁ q102 qr qm
          have post : ∀ k₀, k₀ ≤ 5 → Exec P W (.ifLtN 90102 90062 appendV
              (.ifLtN 90062 90102 appendV .skip)) d₁ d₂ (k₂ + k₀) →
              ∃ d₄ k₄, Exec P W (.seq (.ifLtN 90102 90062 appendV
                (.ifLtN 90062 90102 appendV .skip)) (.instr (.addN 90101 90101 90019))) d₁ d₄ k₄ ∧
                k₄ ≤ 10 ∧ AppI W rs rn S T D' cc ℓ₀ l P₀ c.nmem d₄ ∧ d₄.nreg 90101 = t + 1 := by
            intro k₀ hk₀ ex₀
            refine fin d₂ _ ex₀.wb_right (by omega) ex₀ r2' ?_ ?_ ?_
            · rw [l2, hlen, hfs', List.length_append, List.length_singleton]; omega
            · intro i hi
              rw [l2] at hi
              rw [m2]
              by_cases hil : i = d.nreg 90100
              · subst hil
                simp only [upd, ite_true]
                rw [hfs', ← List.append_assoc]
                have : ((P₀ ++ (l.take t).filter (· != cc)).length) = d.nreg 90100 := by
                  rw [List.length_append, hP, hlen]
                rw [← this]; exact (getD_append_len _ _ []).symm
              · simp only [upd, show T + i ≠ T + d.nreg 90100 by omega, ite_false]
                rw [htmp i (by omega), hfs', ← List.append_assoc]
                exact (getD_append_left (l₂ := [l.getD t 0])
                  (by rw [List.length_append, hP, ← hlen]; omega)).symm
            · intro a ha
              rw [m2]
              simp only [upd]
              rw [ite_eq_right (by rw [hlen]; rcases ha with ha | ha <;> omega)]
              exact hfr a ha
          by_cases hlt : l.getD t 0 < cc
          · exact post 1 (by omega) (.ifLtN_true (by rw [q102, hv]; exact hlt) e₂)
          · have hgt : cc < l.getD t 0 := by omega
            exact post 3 (by omega) ((Exec.ifLtN_false (by rw [q102, hv]; omega)
              (.ifLtN_true (by rw [q102, hv]; exact hgt) e₂)).cast (by omega))
      obtain ⟨d₄, k₄, e₄, hk₄, I₄, t₄⟩ := key
      exact ⟨d₄, k₁ + k₄, .seq e₁ e₄, I₄, by omega, by rw [t₄]; omega⟩) I0
  obtain ⟨hw', ht', hlen', htmp', hfr', -, hrn', -, -, -⟩ := I'
  rw [hrn'] at hx
  have hfull : c'.nreg 90101 = l.length := by omega
  rw [hfull, List.take_length] at hlen' htmp'
  refine ⟨c', k, e, ?_, hlen', htmp', hfr', exec_frameS e (by
    simp [wrS, appBody, appendV, block, wrSOK, wrOK, Bapp])⟩
  have : (12 + 2) * (l.length - c.nreg 90101) ≤ 14 * l.length := by rw [h101]; omega
  omega

end

end Gran

end Chazelle.Core
