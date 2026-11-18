module

public import Chazelle.Core.ShootCutCStep

/-!
# WP-G, part 20: one step of the main loop on the RAM

* `runStep_exec`: at a walk vertex whose host point lies in a run: a stretch (climbing or
  descending) or, at a breakpoint, a single edge;
* `cStep_exec`: **a step on the double boundary** from the walk vertex `c ≠ f`: the host item of
  `c` (`locV`), the limit `lim` (the distance to the final vertex `f`, or to the top `2m + 6`),
  then a stretch or a single edge (`StepPost`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK NFLoc
open Chazelle.Chain (sideE)

@[expose] public section

variable {O : OracleIface} {P : Polygon} {C : Chain} {H : Host} {Hh h γ : ℕ} {m₀ : ℕ → ℕ}
  {A₀ W : ℕ}

/-- The limit of a step from `c` towards the final vertex `f`. -/
def limOf (C : Chain) (c f : ℕ) : ℕ := if f < c then 2 * C.m + 6 - c else f - c

/-- `q = (a + t) mod n` by one conditional subtraction. -/
theorem qOf_exec {P : Polygon} {W : ℕ} (e : Config) (hw : WordsBounded W e) {a t n : ℕ}
    (h68 : e.nreg 150068 = a) (h66 : e.nreg 150066 = t) (h27 : e.nreg 150027 = n)
    (hat : a + t < 2 * n) (hW : a + t ≤ W) :
    ∃ e' k, Exec P W (.seq (.instr (.addN 150075 150068 150066))
      (.ifLtN 150075 150027 (.instr (.copyN 150070 150075))
        (.instr (.subN 150070 150075 150027)))) e e' k ∧ k ≤ 4 ∧
      e'.nreg 150070 = (a + t) % n ∧
      (∀ x, x ≠ 150070 → x ≠ 150075 → e'.nreg x = e.nreg x) ∧ e'.nmem = e.nmem := by
  refine spec_seq (spec_instr (Exec.addN hw _ _ _ (by rw [h68, h66]; exact hW)) fun w' => ?_)
  by_cases hlt : a + t < n
  · refine spec_ifLtN_true (by config_simp; rw [h68, h66, h27]; exact hlt)
      (spec_instr (Exec.copyN w' _ _) fun _ => ⟨by omega, ?_, fun x h1 h2 => by simp [h1, h2],
        rfl⟩)
    config_simp; rw [h68, h66, Nat.mod_eq_of_lt hlt]
  · refine spec_ifLtN_false (by config_simp; rw [h68, h66, h27]; exact hlt)
      (spec_instr (Exec.subN w' _ _ _) fun _ => ⟨by omega, ?_, fun x h1 h2 => by simp [h1, h2],
        rfl⟩)
    config_simp; rw [h68, h66, h27, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- **A step at a run point.** -/
theorem runStep_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {emit : Stmt}
    {I : List Pc → Config → Prop} {K : ℕ} (hE : EmitOK P W emit A₀ (VPc P C m₀ h γ) I K)
    {ps : List Pc} (d e : Config) (hw : WordsBounded W e)
    (hm : ∀ a, a < A₀ → e.nmem a = m₀ a) {c lim J r a ℓ t : ℕ} (h40 : e.nreg 150040 = c)
    (h90 : e.nreg 150090 = 0) (h91 : e.nreg 150091 = 1) (h92 : e.nreg 150092 = 2)
    (h93 : e.nreg 150093 = 3) (h96 : e.nreg 150096 = 6)
    (h34 : e.nreg 150034 = m₀ (h + 2)) (h35 : e.nreg 150035 = m₀ (h + 3))
    (h36 : e.nreg 150036 = m₀ (h + 1) + 2) (h23 : e.nreg 150023 = C.m)
    (h27 : e.nreg 150027 = P.n) (h29 : e.nreg 150029 = 2 * C.m) (h61 : e.nreg 150061 = J)
    (h63 : e.nreg 150063 = 1 ↔ J < C.m) (h63' : e.nreg 150063 ≤ 1)
    (h66 : e.nreg 150066 = t) (h68 : e.nreg 150068 = a) (h69 : e.nreg 150069 = ℓ)
    (h72 : e.nreg 150072 = lim)
    (hk : ∀ r, 150000 ≤ r → r < 150044 → r ≠ 150040 → e.nreg r = d.nreg r)
    (hc6 : 6 ≤ c) (hc : c < 2 * C.m + 6) (hlim1 : 1 ≤ lim) (hlim : c + lim ≤ 2 * C.m + 6)
    (hlimγ : lim ≤ γ) (hJ : tJ C (c - 6) = J) (hr : r < H.length) (hrun : H[r] = .run a ℓ)
    (hu : uOf C (c - 6) = NFLoc.preLen (Qof P).n H r + t) (ht : t ≤ ℓ) (ha : a < P.n)
    (hℓ : ℓ < P.n) (hI : I ps e) :
    ∃ d' k L ps', Exec P W (runStep emit) e d' k ∧
      k ≤ (2 * K + 90) * (Nat.log 2 γ + 1) + 60 ∧
      StepPost (VPc P C m₀ h γ) I ps A₀ W m₀ (Brk C (Qof P).n H) c lim d d' ps' L := by
  have hQn := S.hQn
  have hn := S.hn
  have hWn := S.hW
  unfold hostWords at hWn
  obtain ⟨e₂, k₂, ex₂, hk₂, o70, r₂, m₂⟩ := qOf_exec (P := P) e hw h68 h66 h27 (by omega)
    (by omega)
  set q := (a + t) % P.n with hqdef
  have hq : (a + t) % (Qof P).n = q := by rw [hQn]
  have hqn : q < P.n := Nat.mod_lt _ (by omega)
  have w₂ := ex₂.wb_right
  have fr₂ : FrameB Scr e e₂ := exec_frameB ex₂ (by decide)
  have g : ∀ x, x ≠ 150070 → x ≠ 150075 → e₂.nreg x = e.nreg x := r₂
  have hm₂ : ∀ a, a < A₀ → e₂.nmem a = m₀ a := fun a ha => by rw [m₂]; exact hm a ha
  have hk₂' : ∀ r, 150000 ≤ r → r < 150044 → r ≠ 150040 → e₂.nreg r = d.nreg r :=
    fun r h1 h2 h3 => (g r (by omega) (by omega)).trans (hk r h1 h2 h3)
  have hI₂ := hE.stable _ _ _ hI fr₂
  have hC : ∀ {K' : ℕ}, Brk C (Qof P).n H (c - 6) → ∃ d' k, Exec P W (single emit) e₂ d' k ∧
      k ≤ K + 7 ∧ StepPost (VPc P C m₀ h γ) I ps A₀ W m₀ (Brk C (Qof P).n H) c lim d d'
        [sgPc c] 1 := fun hb =>
    single_post S hE d e₂ w₂ hm₂ (by rw [g _ (by omega) (by omega), h40])
      (by rw [g _ (by omega) (by omega), h90]) (by rw [g _ (by omega) (by omega), h91])
      (by rw [g _ (by omega) (by omega), h92]) (by rw [g _ (by omega) (by omega), h93])
      (by rw [g _ (by omega) (by omega), h96]) hk₂' hc hlim1 hb hI₂
  have hcost : K + 7 ≤ (2 * K + 90) * (Nat.log 2 γ + 1) := by
    have : 2 * K + 90 ≤ (2 * K + 90) * (Nat.log 2 γ + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have e63 : e₂.nreg 150063 = e.nreg 150063 := g _ (by omega) (by omega)
  have e91 : e₂.nreg 150091 = 1 := by rw [g _ (by omega) (by omega), h91]
  have e90 : e₂.nreg 150090 = 0 := by rw [g _ (by omega) (by omega), h90]
  have e66 : e₂.nreg 150066 = t := by rw [g _ (by omega) (by omega), h66]
  have e69 : e₂.nreg 150069 = ℓ := by rw [g _ (by omega) (by omega), h69]
  have e27 : e₂.nreg 150027 = P.n := by rw [g _ (by omega) (by omega), h27]
  unfold runStep
  by_cases hb : e₂.nreg 150063 < e₂.nreg 150091
  · -- descending
    have hJm : C.m ≤ J := by
      rw [e63, e91] at hb
      by_contra hc'; have := h63.2 (by omega); omega
    by_cases ht0 : e₂.nreg 150090 < e₂.nreg 150066
    · by_cases hq0 : e₂.nreg 150090 < e₂.nreg 150070
      · obtain ⟨d', k, L, ps', ex, hk', post⟩ := dn_post S hE (ps := ps) d e₂ w₂ hm₂
          (by rw [g _ (by omega) (by omega), h40]) e90 e91
          (by rw [g _ (by omega) (by omega), h34]) (by rw [g _ (by omega) (by omega), h35])
          (by rw [g _ (by omega) (by omega), h36]) (by rw [g _ (by omega) (by omega), h29])
          (by rw [g _ (by omega) (by omega), h61]) e66 o70
          (by rw [g _ (by omega) (by omega), h72]) hk₂' hc6 hlim1 hlim hlimγ hJ hJm hr hrun
          hu ht (by rw [e90, e66] at ht0; exact ht0) hq (by rw [e90, o70] at hq0; exact hq0) hI₂
        exact ⟨d', _, L, ps', .seq ex₂ (.ifLtN_true hb (.ifLtN_true ht0 (.ifLtN_true hq0 ex))),
          by omega, post⟩
      · obtain ⟨d', k, ex, hk', post⟩ := hC (K' := 0) (brk_run C hr hrun hu ht
          (Or.inr (Or.inr (Or.inl (by rw [hq]; rw [e90, o70] at hq0; omega)))))
        exact ⟨d', _, 1, _, .seq ex₂ (.ifLtN_true hb (.ifLtN_true ht0 (.ifLtN_false hq0 ex))),
          by omega, post⟩
    · obtain ⟨d', k, ex, hk', post⟩ := hC (K' := 0) (brk_run C hr hrun hu ht
        (Or.inl (by rw [e90, e66] at ht0; omega)))
      exact ⟨d', _, 1, _, .seq ex₂ (.ifLtN_true hb (.ifLtN_false ht0 ex)), by omega, post⟩
  · -- climbing
    have hJm : J < C.m := by
      rw [e63, e91] at hb
      exact h63.1 (by omega)
    by_cases htl : e₂.nreg 150066 < e₂.nreg 150069
    · rw [e66, e69] at htl
      have e₃ := Exec.addN (P := P) w₂ 150075 150070 150091 (by rw [o70, e91]; omega)
      set e₃c := ({ e₂ with nreg := upd e₂.nreg 150075 (e₂.nreg 150070 + e₂.nreg 150091) } :
        Config) with he₃c
      have g₃ : ∀ x, x ≠ 150075 → e₃c.nreg x = e₂.nreg x := fun x hx => by simp [he₃c, upd, hx]
      have o75 : e₃c.nreg 150075 = q + 1 := by simp [he₃c, upd, o70, e91]
      have w₃ := e₃.wb_right
      have fr₃ : FrameB Scr e₂ e₃c := exec_frameB e₃ (by decide)
      have hI₃ := hE.stable _ _ _ hI₂ fr₃
      have g' : ∀ x, x ≠ 150070 → x ≠ 150075 → e₃c.nreg x = e.nreg x := fun x h1 h2 =>
        (g₃ x h2).trans (g x h1 h2)
      have hm₃ : ∀ a, a < A₀ → e₃c.nmem a = m₀ a := fun a ha => hm₂ a ha
      have hk₃ : ∀ r, 150000 ≤ r → r < 150044 → r ≠ 150040 → e₃c.nreg r = d.nreg r :=
        fun r h1 h2 h3 => (g' r (by omega) (by omega)).trans (hk r h1 h2 h3)
      by_cases hq1 : e₃c.nreg 150075 < e₃c.nreg 150027
      · obtain ⟨d', k, L, ps', ex, hk', post⟩ := up_post S hE (ps := ps) d e₃c w₃ hm₃
          (by rw [g' _ (by omega) (by omega), h40]) (by rw [g' _ (by omega) (by omega), h90])
          (by rw [g' _ (by omega) (by omega), h91])
          (by rw [g' _ (by omega) (by omega), h34]) (by rw [g' _ (by omega) (by omega), h35])
          (by rw [g' _ (by omega) (by omega), h36]) (by rw [g' _ (by omega) (by omega), h23])
          (by rw [g' _ (by omega) (by omega), h61]) (by rw [g' _ (by omega) (by omega), h69])
          (by rw [g' _ (by omega) (by omega), h66]) (by rw [g' _ (by omega) (by omega), h27])
          (by rw [g₃ _ (by omega), o70]) (by rw [g' _ (by omega) (by omega), h72]) hk₃ hc6
          hlim1 hlim hlimγ hJ hJm hr hrun hu htl hq
          (by rw [o75, g' _ (by omega) (by omega), h27] at hq1; exact hq1) hI₃
        exact ⟨d', _, L, ps', .seq ex₂ (.ifLtN_false hb (.ifLtN_true (by rw [e66, e69]; exact htl)
          (.seq e₃ (.ifLtN_true hq1 ex)))), by omega, post⟩
      · have hq1' : q + 1 = P.n := by
          rw [o75, g' _ (by omega) (by omega), h27] at hq1; omega
        obtain ⟨d', k, ex, hk', post⟩ := single_post (K := K) S hE (ps := ps) d e₃c w₃ hm₃
          (by rw [g' _ (by omega) (by omega), h40]) (by rw [g' _ (by omega) (by omega), h90])
          (by rw [g' _ (by omega) (by omega), h91]) (by rw [g' _ (by omega) (by omega), h92])
          (by rw [g' _ (by omega) (by omega), h93]) (by rw [g' _ (by omega) (by omega), h96])
          hk₃ hc hlim1 (brk_run C hr hrun hu ht
            (Or.inr (Or.inr (Or.inr (by rw [hq, hQn]; omega))))) hI₃
        exact ⟨d', _, 1, _, .seq ex₂ (.ifLtN_false hb (.ifLtN_true (by rw [e66, e69]; exact htl)
          (.seq e₃ (.ifLtN_false hq1 ex)))), by omega, post⟩
    · obtain ⟨d', k, ex, hk', post⟩ := hC (K' := 0) (brk_run C hr hrun hu ht
        (Or.inr (Or.inl (by rw [e66, e69] at htl; omega))))
      exact ⟨d', _, 1, _, .seq ex₂ (.ifLtN_false hb (.ifLtN_false htl ex)), by omega, post⟩


theorem bloc_false {r : ℕ} (h : r < 150060 ∨ 150080 ≤ r) : Bloc r = false := by
  unfold Bloc Bl; simp; omega

/-- A host layout depends only on the memory below its end. -/
theorem hostAt_agree' {m m' : ℕ → ℕ} {B E : ℕ} {H : Host} (h : HostAt m B H)
    (hE : B + 3 * H.length + 4 ≤ E) (hm : ∀ a, a < E → m' a = m a) : HostAt m' B H := by
  refine ⟨by rw [hm _ (by omega)]; exact h.1, fun i hi => ?_⟩
  have hh := h.2 i hi
  have e1 := hm (B + 1 + 3 * i) (by omega)
  have e2 := hm (B + 2 + 3 * i) (by omega)
  have e3 := hm (B + 3 + 3 * i) (by omega)
  generalize H.getD i (.run 0 0) = it at hh ⊢
  cases it with
  | run a l => obtain ⟨h1, h2, h3⟩ := hh; exact ⟨e1.trans h1, e2.trans h2, e3.trans h3⟩
  | pt x =>
    cases x with
    | vtx j => obtain ⟨h1, h2⟩ := hh; exact ⟨e1.trans h1, e2.trans h2⟩
    | onEdge e hh' => obtain ⟨h1, h2, h3⟩ := hh; exact ⟨e1.trans h1, e2.trans h2, e3.trans h3⟩

/-- **A step on the double boundary** from the walk vertex `c ≠ f`. -/
theorem cStep_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {emit : Stmt}
    {I : List Pc → Config → Prop} {K : ℕ} (hE : EmitOK P W emit A₀ (VPc P C m₀ h γ) I K)
    {ps : List Pc} {MD mode : ℕ} {s e : WPos} (d : Config) (hw : WordsBounded W d)
    (R : CoreRegs P C H Hh MD h γ mode s e m₀ d) (hm : ∀ a, a < A₀ → d.nmem a = m₀ a)
    {c f : ℕ} (h40 : d.nreg 150040 = c) (h41 : d.nreg 150041 = f) (hc6 : 6 ≤ c)
    (hc : c < 2 * C.m + 6) (hf : f ≤ 2 * C.m + 5) (hcf : c ≠ f) (hlimγ : limOf C c f ≤ γ)
    (hI : I ps d) :
    ∃ d' k L ps', Exec P W (cStep emit) d d' k ∧
      k ≤ (2 * K + 90) * (Nat.log 2 γ + 1) + 1600 ∧
      StepPost (VPc P C m₀ h γ) I ps A₀ W m₀ (Brk C (Qof P).n H) c (limOf C c f) d d' ps' L := by
  have hQn := S.hQn
  have hN := S.hN
  have hNn := S.hNn
  have hWn := S.hW
  unfold hostWords at hWn
  have hmN := C.m_lt
  have hsN := S.hs
  rw [hN] at hmN hsN
  have hHA := S.hHA
  have hAW := S.hAW
  -- `44 := c`
  have e₀ := Exec.copyN (P := P) hw 150044 150040
  set d₀ := ({ d with nreg := upd d.nreg 150044 (d.nreg 150040) } : Config) with hd₀
  have g₀ : ∀ x, x ≠ 150044 → d₀.nreg x = d.nreg x := fun x hx => by simp [hd₀, upd, hx]
  have R₀ : ChainRegs C (H.pts P.n).length Hh d₀ := R.chain.of_frame fun r hr => g₀ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; omega)
  have hH₀ : HostAt d₀.nmem Hh H := hostAt_agree' S.hH hHA fun a ha => hm a (by omega)
  obtain ⟨d₁, k₁, ex₁, hk₁, fr₁, o60, o61, o62, o63, o63', o64, found⟩ :=
    locV_exec (P := P) (W := W) (v := c) d₀ e₀.wb_right rfl hH₀ R₀
      (by simp [hd₀, upd, h40]) hc6 (by omega) hsN hmN (by omega) (by omega)
  have g₁ : ∀ x, (x < 150060 ∨ 150080 ≤ x) → d₁.nreg x = d₀.nreg x := fun x hx =>
    fr₁.1 x (bloc_false hx)
  have m₁ : d₁.nmem = d.nmem := fr₁.2.2.1
  -- the limit
  obtain ⟨d₂, k₂, ex₂, hk₂, o72, g₂, m₂⟩ : ∃ d₂ k₂, Exec P W (.ifLtN 150041 150040
      (.instr (.subN 150072 150032 150040)) (.instr (.subN 150072 150041 150040))) d₁ d₂ k₂ ∧
      k₂ ≤ 3 ∧ d₂.nreg 150072 = limOf C c f ∧ (∀ x, x ≠ 150072 → d₂.nreg x = d₁.nreg x) ∧
      d₂.nmem = d₁.nmem := by
    have a41 : d₁.nreg 150041 = f := by rw [g₁ _ (by omega), g₀ _ (by omega), h41]
    have a40 : d₁.nreg 150040 = c := by rw [g₁ _ (by omega), g₀ _ (by omega), h40]
    have a32 : d₁.nreg 150032 = 2 * C.m + 6 := by rw [g₁ _ (by omega), g₀ _ (by omega), R.h32]
    have w₁ := ex₁.wb_right
    unfold limOf
    by_cases hfc : f < c
    · refine spec_ifLtN_true (by rw [a41, a40]; exact hfc) (spec_instr (Exec.subN w₁ _ _ _)
        fun _ => ⟨by omega, ?_, fun x hx => by simp [hx], rfl⟩)
      config_simp; rw [a32, a40, ite_eq_left hfc]
    · refine spec_ifLtN_false (by rw [a41, a40]; exact hfc) (spec_instr (Exec.subN w₁ _ _ _)
        fun _ => ⟨by omega, ?_, fun x hx => by simp [hx], rfl⟩)
      config_simp; rw [a41, a40, ite_eq_right hfc]
  have w₂ := ex₂.wb_right
  have g : ∀ x, (x < 150060 ∨ 150080 ≤ x) → x ≠ 150072 → x ≠ 150044 → d₂.nreg x = d.nreg x :=
    fun x h1 h2 h3 => by rw [g₂ x h2, g₁ x h1, g₀ x h3]
  have fr : FrameB Scr d d₂ :=
    (exec_frameB e₀ (by decide)).trans ((exec_frameB ex₁ (by decide)).trans
      (exec_frameB ex₂ (by decide)))
  have hI₂ := hE.stable _ _ _ hI fr
  have hm₂ : ∀ a, a < A₀ → d₂.nmem a = m₀ a := fun a ha => by rw [m₂, m₁]; exact hm a ha
  have hk₂' : ∀ r, 150000 ≤ r → r < 150044 → r ≠ 150040 → d₂.nreg r = d.nreg r :=
    fun r h1 h2 _ => g r (by omega) (by omega) (by omega)
  have b40 : d₂.nreg 150040 = c := by rw [g _ (by omega) (by omega) (by omega), h40]
  have b90 : d₂.nreg 150090 = 0 := by rw [g _ (by omega) (by omega) (by omega), R.h90]
  have b91 : d₂.nreg 150091 = 1 := by rw [g _ (by omega) (by omega) (by omega), R.chain.h91]
  have b92 : d₂.nreg 150092 = 2 := by rw [g _ (by omega) (by omega) (by omega), R.h92]
  have b93 : d₂.nreg 150093 = 3 := by rw [g _ (by omega) (by omega) (by omega), R.chain.h93]
  have b96 : d₂.nreg 150096 = 6 := by rw [g _ (by omega) (by omega) (by omega), R.chain.h96]
  -- the item
  have hS2 := C.sideS_lt C.sideBeta
  have hJ : tJ C (c - 6) = jOf (C.sideS C.sideBeta) (c - 6) (2 * C.m) := by
    unfold tJ; rw [jOf_eq hS2 (by omega)]
  have hlim1 : 1 ≤ limOf C c f := by unfold limOf; split_ifs <;> omega
  have hlim : c + limOf C c f ≤ 2 * C.m + 6 := by unfold limOf; split_ifs <;> omega
  obtain ⟨hr, hp1, hp2, h66, h67, h68, h69⟩ := found
  set r := d₁.nreg 150065 with hrdef
  set u := d₁.nreg 150064 with hudef
  have huOf : uOf C (c - 6) = u := by
    unfold uOf tJ; rw [hN, o64]
  have hlo : Hh + 3 + 3 * r < A₀ := by omega
  have e67 : d₂.nreg 150067 = m₀ (Hh + 1 + 3 * r) := by
    rw [g₂ _ (by omega), h67, show d₀.nmem = d.nmem from rfl, hm _ (by omega)]
  have e68 : d₂.nreg 150068 = m₀ (Hh + 2 + 3 * r) := by
    rw [g₂ _ (by omega), h68, show d₀.nmem = d.nmem from rfl, hm _ (by omega)]
  have e69 : d₂.nreg 150069 = m₀ (Hh + 3 + 3 * r) := by
    rw [g₂ _ (by omega), h69, show d₀.nmem = d.nmem from rfl, hm _ (by omega)]
  obtain ⟨hit, -⟩ := NFLoc.hostAt_item S.hH hr
  have hsucc := NFLoc.preLen_succ P.n H hr
  have hcost : K + 7 ≤ (2 * K + 90) * (Nat.log 2 γ + 1) := by
    have : 2 * K + 90 ≤ (2 * K + 90) * (Nat.log 2 γ + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hcore : ∀ (d' : Config) (k k' : ℕ) (L : ℕ) (ps' : List Pc),
      Exec P W (.ifLtN 150067 150091 (runStep emit) (single emit)) d₂ d' k' →
      k' ≤ (2 * K + 90) * (Nat.log 2 γ + 1) + 62 → k = 1 + (k₁ + (k₂ + k')) →
      StepPost (VPc P C m₀ h γ) I ps A₀ W m₀ (Brk C (Qof P).n H) c (limOf C c f) d d' ps' L →
      ∃ d' k L ps', Exec P W (cStep emit) d d' k ∧
        k ≤ (2 * K + 90) * (Nat.log 2 γ + 1) + 1600 ∧
        StepPost (VPc P C m₀ h γ) I ps A₀ W m₀ (Brk C (Qof P).n H) c (limOf C c f) d d' ps'
          L := by
    intro d' k k' L ps' ex hk' hk post
    refine ⟨d', k, L, ps', ?_, ?_, post⟩
    · rw [hk]; exact .seq e₀ (.seq ex₁ (.seq ex₂ ex))
    · have := S.hlen; omega
  by_cases hcode : d₂.nreg 150067 < d₂.nreg 150091
  · -- a run
    have hc0 : m₀ (Hh + 1 + 3 * r) = 0 := by rw [← e67]; rw [b91] at hcode; omega
    set a := m₀ (Hh + 2 + 3 * r)
    set ℓ := m₀ (Hh + 3 + 3 * r)
    have hrun : H[r] = .run a ℓ := by rw [hit, hc0]; rfl
    have hwf := S.hwf _ (List.getElem_mem hr)
    rw [hrun] at hwf hsucc
    simp only [NFLoc.itemCnt] at hsucc
    obtain ⟨ha, hℓ⟩ := hwf
    obtain ⟨d', k', L, ps', ex, hk', post⟩ := runStep_exec S hE (ps := ps) (a := a) (ℓ := ℓ)
      (t := u - NFLoc.preLen P.n H r) (r := r) d d₂ w₂ hm₂ b40 b90 b91 b92 b93 b96
      (by rw [g _ (by omega) (by omega) (by omega), R.h34])
      (by rw [g _ (by omega) (by omega) (by omega), R.h35])
      (by rw [g _ (by omega) (by omega) (by omega), R.h36])
      (by rw [g _ (by omega) (by omega) (by omega), R.chain.h23])
      (by rw [g _ (by omega) (by omega) (by omega), R.h27])
      (by rw [g _ (by omega) (by omega) (by omega), R.chain.h29])
      (by rw [g₂ _ (by omega), o61]) (by rw [g₂ _ (by omega)]; exact o63)
      (by rw [g₂ _ (by omega)]; exact o63') (by rw [g₂ _ (by omega), h66]) e68 e69 o72 hk₂'
      hc6 hc hlim1 hlim hlimγ hJ hr hrun (by rw [huOf, hQn]; omega) (by omega) ha hℓ hI₂
    exact hcore d' _ (k' + 1) L ps' (.ifLtN_true hcode ex) (by omega) rfl post
  · -- a point item: a breakpoint
    have hpt : ∃ x, H[r] = .pt x := by
      rw [hit]; unfold NFLoc.itemOf
      rw [b91, e67] at hcode
      rw [ite_eq_right (by omega)]
      split_ifs <;> exact ⟨_, rfl⟩
    obtain ⟨x, hx⟩ := hpt
    have hb : Brk C (Qof P).n H (c - 6) := brk_pt C hr hx (by rw [huOf, hQn]; exact hp1)
      (by rw [huOf, hQn]; exact hp2)
    obtain ⟨d', k', ex, hk', post⟩ := single_post (K := K) S hE (ps := ps) d d₂ w₂ hm₂ b40 b90
      b91 b92 b93 b96 hk₂' hc hlim1 hb hI₂
    exact hcore d' _ (k' + 2) 1 _ (.ifLtN_false hcode ex) (by omega) rfl post

end

end ShootCut

end Chazelle.Core
