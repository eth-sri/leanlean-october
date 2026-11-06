module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.OraclePrepLoad
public import Mathlib.Data.List.GetD

/-!
# Lemma 3.6 (WP-H), preprocessing part 3: counting loops and fresh arrays

* `forS ri rn r1 body`: `ri := 0; while ri < rn do (body; ri := ri + 1)` with the constant `1`
  in `r1`; `forS_exec`: an invariant indexed by the counter, a body of cost `≤ κ` that keeps the
  counter, the bound and the constant: total cost `≤ n (κ + 3) + 3`.
* `scatS ri rn r1 ra rv body`: a counting loop whose body computes an address (`ra`) and a
  value (`rv`) without writing memory, followed by the store; the memory becomes `scat m g f n`
  (`scatS_exec`).
* `emitS …`: a counting loop whose body decides whether to emit a pair; emitted pairs are
  appended to two arrays (`emitS_exec`).
* `PF B lo c c'`: the frame of a stage (registers outside `B`, memory below `lo`), and its
  conversion into a `Frame` (`PF.frame`).
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

/-- **A counting loop.** -/
def forS (ri rn r1 : ℕ) (body : Stmt) : Stmt :=
  .seq (.instr (.constN ri 0)) (.whileLtN ri rn (.seq body (.instr (.addN ri ri r1))))

/-- **The counting loop.**  `I i c`: the invariant after `i` rounds. -/
theorem forS_exec {P : Polygon} {W ri rn r1 : ℕ} {body : Stmt} (_hir : ri ≠ rn)
    (_hi1 : ri ≠ r1) {n κ : ℕ} (I : ℕ → Config → Prop)
    (hI : ∀ i c, I i c → WordsBounded W c ∧ c.nreg rn = n ∧ c.nreg r1 = 1)
    (hstab : ∀ i c v, I i c → WordsBounded W { c with nreg := upd c.nreg ri v } →
      I i { c with nreg := upd c.nreg ri v })
    (hbody : ∀ i c, i < n → I i c → c.nreg ri = i →
      ∃ c' k, Exec P W body c c' k ∧ k ≤ κ ∧ c'.nreg ri = i ∧ I (i + 1) c')
    {c : Config} (hw : WordsBounded W c) (hn : n ≤ W)
    (h0 : ∀ c', WordsBounded W c' → c'.nreg ri = 0 → (∀ r, r ≠ ri → c'.nreg r = c.nreg r) →
      c'.nmem = c.nmem → c'.rreg = c.rreg → c'.rmem = c.rmem → c'.output = c.output → I 0 c') :
    ∃ c' k, Exec P W (forS ri rn r1 body) c c' k ∧ k ≤ n * (κ + 3) + 3 ∧ I n c' ∧
      c'.nreg ri = n ∧ n ≤ k := by
  -- the start
  have x₀ := Exec.constN (P := P) hw ri 0 (Nat.zero_le _)
  set c₀ : Config := { c with nreg := upd c.nreg ri 0 } with hc₀
  have I₀ : I 0 c₀ := h0 c₀ x₀.wb_right (by rw [hc₀]; simp) (fun r hr => by rw [hc₀]; simp [hr])
    rfl rfl rfl rfl
  -- the loop, with the counter in the invariant
  obtain ⟨c', k, ex, ⟨i, hI', hi, hin⟩, hstop, hk, hψ⟩ := SortR.whileLtN_potential_lb (P := P)
    (W := W) (a := ri) (b := rn) (body := .seq body (.instr (.addN ri ri r1)))
    (fun d => ∃ i, I i d ∧ d.nreg ri = i ∧ i ≤ n) (fun d => (n - d.nreg ri) * (κ + 3))
    (fun d => d.nreg ri)
    (fun d ⟨i, h, _⟩ => (hI i d h).1)
    (fun d ⟨i, hId, hri, hin⟩ ht => by
      obtain ⟨hwd, hrn, hr1⟩ := hI i d hId
      rw [hri, hrn] at ht
      obtain ⟨d₁, k₁, e₁, hk₁, hr₁, hI₁⟩ := hbody i d ht hId hri
      obtain ⟨hw₁, hrn₁, hr1₁⟩ := hI (i + 1) d₁ hI₁
      have e₂ := Exec.addN (P := P) hw₁ ri ri r1 (by omega)
      refine ⟨_, _, .seq e₁ e₂, ⟨i + 1, ?_, ?_, by omega⟩, ?_, ?_⟩
      · exact hstab _ _ _ hI₁ e₂.wb_right
      · ram_simp
      · simp only [upd_same]; rw [hr₁, hr1₁, hri]
        have : (n - (i + 1)) * (κ + 3) + (κ + 3) = (n - i) * (κ + 3) := by
          rw [← Nat.succ_mul]; grind
        omega
      · simp only [upd_same]; omega)
    ⟨0, I₀, by rw [hc₀]; simp, Nat.zero_le _⟩
  obtain ⟨-, hrn, -⟩ := hI i c' hI'
  rw [hi, hrn] at hstop
  have hin' : i = n := by omega
  subst hin'
  have : c₀.nreg ri = 0 := by rw [hc₀]; simp
  rw [this] at hk hψ
  refine ⟨c', _, .seq x₀ ex, ?_, hI', hi, ?_⟩
  all_goals grind

/-! ## Scattering values into memory -/

/-- The memory after the stores `g i ↦ f i` for `i < n`, in order. -/
def scat (m g f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => m
  | i + 1 => upd (scat m g f i) (g i) (f i)

section
variable {m g f : ℕ → ℕ}
theorem scat_other {n a : ℕ} (h : ∀ i, i < n → g i ≠ a) :
    scat m g f n a = m a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [scat]
    rw [upd_other _ _ _ (fun e => h n (by omega) e.symm)]
    grind

theorem scat_at {n i : ℕ} (hi : i < n)
    (hg : ∀ j, j < n → i < j → g j ≠ g i) : scat m g f n (g i) = f i := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [scat]
    core_grind

theorem scat_below {n lo : ℕ} (hg : ∀ i, i < n → lo ≤ g i) {a : ℕ}
    (ha : a < lo) : scat m g f n a = m a :=
  scat_other fun i hi e => by grind


end

/-- **A scatter loop**: `body` computes an address in `ra` and a value in `rv`; they are stored. -/
def scatS (ri rn r1 ra rv : ℕ) (body : Stmt) : Stmt :=
  forS ri rn r1 (.seq body (.instr (.storeN ra rv)))

/-- **The scatter loop.**  The body writes only registers of `B` (not the counter, the bound, the
constant `1`) and no memory, and computes the address `g i ≥ lo` and the value `f i`; `J` is an
invariant insensitive to the registers of `B`, the counter and the memory from `lo` on. -/
theorem scatS_exec {P : Polygon} {W ri rn r1 ra rv : ℕ} {body : Stmt} {B : ℕ → Bool}
    (hBi : B ri = false) (hBn : B rn = false) (hB1 : B r1 = false) (hir : ri ≠ rn) (hi1 : ri ≠ r1)
    (J : Config → Prop) (lo : ℕ)
    (hJ : ∀ c c', J c → (∀ r, B r = false → r ≠ ri → c'.nreg r = c.nreg r) →
      (∀ a, a < lo → c'.nmem a = c.nmem a) → J c')
    {n κ : ℕ} (g f : ℕ → ℕ) (hg : ∀ i, i < n → lo ≤ g i)
    (hbody : ∀ i c, i < n → J c → WordsBounded W c → c.nreg ri = i →
      ∃ c' k, Exec P W body c c' k ∧ k ≤ κ ∧ FrameB B c c' ∧ c'.nreg ra = g i ∧ c'.nreg rv = f i)
    {c : Config} (hw : WordsBounded W c) (hJc : J c) (hn : c.nreg rn = n) (h1 : c.nreg r1 = 1)
    (hnW : n ≤ W) :
    ∃ c' k, Exec P W (scatS ri rn r1 ra rv body) c c' k ∧ k ≤ n * (κ + 4) + 3 ∧
      (∀ r, B r = false → r ≠ ri → c'.nreg r = c.nreg r) ∧
      (∀ r, B r = false → c'.rreg r = c.rreg r) ∧ c'.nmem = scat c.nmem g f n ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧ J c' ∧ c'.nreg ri = n := by
  let I : ℕ → Config → Prop := fun i d => WordsBounded W d ∧
    (∀ r, B r = false → r ≠ ri → d.nreg r = c.nreg r) ∧
    (∀ r, B r = false → d.rreg r = c.rreg r) ∧ d.nmem = scat c.nmem g f i ∧
    d.rmem = c.rmem ∧ d.output = c.output ∧ J d
  obtain ⟨c', k, ex, hk, ⟨_, h2, h3, h4, h5, h6, h7⟩, hi, -⟩ := forS_exec (P := P) (W := W)
    (body := .seq body (.instr (.storeN ra rv))) hir hi1 (n := n) (κ := κ + 1) I
    (fun i d ⟨hw, hr, _⟩ => ⟨hw, by grind,
      by grind⟩)
    (fun i d v ⟨_, hr, hrr, hm, hrm, ho, hJd⟩ hw' => ⟨hw', fun r hB hri => by
        ram_simp, hrr, hm, hrm, ho,
      hJ d _ hJd (fun r _ hri => by ram_simp)
        (fun _ _ => rfl)⟩)
    (fun i d hin ⟨hwd, hr, hrr, hm, hrm, ho, hJd⟩ hri => by
      obtain ⟨d₁, k₁, e₁, hk₁, f₁, ha₁, hv₁⟩ := hbody i d hin hJd hwd hri
      have e₂ := Exec.storeN (P := P) e₁.wb_right ra rv
      refine ⟨_, _, .seq e₁ e₂, by omega, by ram_grind, e₂.wb_right, ?_, ?_, ?_,
        ?_, ?_, ?_⟩
      · ram_grind
      · ram_grind
      · simp only [scat]; ram_grind
      · ram_grind
      · ram_grind
      · refine hJ d _ hJd (fun r hB _ => f₁.1 r hB) (fun a ha => ?_)
        simp only
        rw [ha₁, upd_other _ _ _ (fun e => by grind), f₁.2.2.1])
    hw hnW (fun d hwd h0 hr hm hrr hrm ho => ⟨hwd, fun r _ hri => hr r hri,
      fun r _ => by rw [hrr], by rw [hm]; rfl, hrm, ho,
      hJ c d hJc (fun r _ hri => hr r hri) (fun a _ => by rw [hm])⟩)
  refine ⟨c', k, ex, by nlinarith, h2, h3, h4, h5, h6, h7, hi⟩

/-! ## Emitting pairs into two arrays -/

/-- The pairs emitted by the first `i` rounds. -/
def emitted (φ : ℕ → Option (ℕ × ℕ)) (i : ℕ) : List (ℕ × ℕ) := (List.range i).filterMap φ

section
variable (φ : ℕ → Option (ℕ × ℕ)) (i : ℕ)
theorem emitted_succ :
    emitted φ (i + 1) = emitted φ i ++ (φ i).toList := by
  core_grind [List.range_succ, List.filterMap_append]

theorem emitted_length_le : (emitted φ i).length ≤ i := by
  core_grind


end

theorem mem_emitted {φ : ℕ → Option (ℕ × ℕ)} {i : ℕ} {x : ℕ × ℕ} :
    x ∈ emitted φ i ↔ ∃ j, j < i ∧ φ j = some x := by
  core_grind

/-- Pairs stored in two arrays from the given bases. -/
def PairsAt (m : ℕ → ℕ) (R1 R2 : ℕ) (l : List (ℕ × ℕ)) : Prop :=
  ∀ t, t < l.length → m (R1 + t) = (l.getD t (0, 0)).1 ∧ m (R2 + t) = (l.getD t (0, 0)).2

/-- **An emission loop**: when the flag `rf` is set, the pair `(rv1, rv2)` is stored at the
counter `rc` of the arrays with bases in `rR1`, `rR2`, and the counter advances. -/
def emitS (ri rn r1 rf rv1 rv2 rR1 rR2 rc rt : ℕ) (body : Stmt) : Stmt :=
  forS ri rn r1 (.seq body (.ifLtN rf r1 .skip
    (block [.addN rt rR1 rc, .storeN rt rv1, .addN rt rR2 rc, .storeN rt rv2, .addN rc rc r1])))

/-- **The emission loop.**  The body writes only registers of `B` (not the loop registers) and no
memory, and sets the flag and the pair of `φ i`; `J` is insensitive to the registers of `B`, the
counter, the output counter, the scratch and the memory from `lo` on.  The pairs are appended
after `c₀` entries to the arrays at `R1`, `R2` (with room for `n` more entries in the first). -/
theorem emitS_exec {P : Polygon} {W ri rn r1 rf rv1 rv2 rR1 rR2 rc rt : ℕ} {body : Stmt}
    {B : ℕ → Bool} (hreg : [ri, rn, r1, rc, rR1, rR2, rt].Nodup ∧ rt ≠ rv1 ∧ rt ≠ rv2 ∧
      rf ≠ rt ∧ rf ≠ rc)
    (hBi : B ri = false) (hBn : B rn = false) (hB1 : B r1 = false) (hBc : B rc = false)
    (hBR1 : B rR1 = false) (hBR2 : B rR2 = false)
    {R1 R2 c₀ n κ : ℕ} (J : Config → Prop)
    (hJ : ∀ c c', J c → (∀ r, B r = false → r ≠ ri → r ≠ rc → r ≠ rt → c'.nreg r = c.nreg r) →
      (∀ a, (a < R1 + c₀ ∨ (R1 + c₀ + n ≤ a ∧ a < R2 + c₀) ∨ R2 + c₀ + n ≤ a) →
        c'.nmem a = c.nmem a) → J c')
    (φ : ℕ → Option (ℕ × ℕ))
    (hbody : ∀ i c, i < n → J c → WordsBounded W c → c.nreg ri = i →
      ∃ c' k, Exec P W body c c' k ∧ k ≤ κ ∧ FrameB B c c' ∧ (φ i = none → c'.nreg rf = 0) ∧
        ∀ x, φ i = some x → c'.nreg rf = 1 ∧ c'.nreg rv1 = x.1 ∧ c'.nreg rv2 = x.2)
    {c : Config} (hw : WordsBounded W c) (hJc : J c) (hn : c.nreg rn = n) (h1 : c.nreg r1 = 1)
    (hR1 : c.nreg rR1 = R1) (hR2 : c.nreg rR2 = R2) (hc₀ : c.nreg rc = c₀)
    (hR12 : R1 + c₀ + n ≤ R2) (hRW : R2 + c₀ + n ≤ W) :
    ∃ c' k, Exec P W (emitS ri rn r1 rf rv1 rv2 rR1 rR2 rc rt body) c c' k ∧
      k ≤ n * (κ + 10) + 3 ∧
      (∀ r, B r = false → r ≠ ri → r ≠ rc → r ≠ rt → c'.nreg r = c.nreg r) ∧
      (∀ r, B r = false → c'.rreg r = c.rreg r) ∧
      c'.nreg rc = c₀ + (emitted φ n).length ∧
      PairsAt c'.nmem (R1 + c₀) (R2 + c₀) (emitted φ n) ∧
      (∀ a, (a < R1 + c₀ ∨ (R1 + c₀ + (emitted φ n).length ≤ a ∧ a < R2 + c₀) ∨
        R2 + c₀ + (emitted φ n).length ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧ J c' := by
  obtain ⟨hnd, ht1, ht2, hft, hfc⟩ := hreg
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
    and_true, not_or] at hnd
  obtain ⟨⟨hin, hi1, hic, hiR1, hiR2, hit⟩, ⟨hn1, hnc, hnR1, hnR2, hnt⟩, ⟨h1c, h1R1, h1R2, h1t⟩,
    ⟨hcR1, hcR2, hct⟩, ⟨hR1R2, hR1t⟩, hR2t, -⟩ := hnd
  let I : ℕ → Config → Prop := fun i d => WordsBounded W d ∧
    (∀ r, B r = false → r ≠ ri → r ≠ rc → r ≠ rt → d.nreg r = c.nreg r) ∧
    (∀ r, B r = false → d.rreg r = c.rreg r) ∧ d.nreg rc = c₀ + (emitted φ i).length ∧
    PairsAt d.nmem (R1 + c₀) (R2 + c₀) (emitted φ i) ∧
    (∀ a, (a < R1 + c₀ ∨ (R1 + c₀ + (emitted φ i).length ≤ a ∧ a < R2 + c₀) ∨
      R2 + c₀ + (emitted φ i).length ≤ a) → d.nmem a = c.nmem a) ∧
    d.rmem = c.rmem ∧ d.output = c.output ∧ J d
  obtain ⟨c', k, ex, hk, ⟨_, h2, h3, h4, h5, h6, h7, h8, h9⟩, -, -⟩ := forS_exec (P := P) (W := W)
    (body := .seq body (.ifLtN rf r1 .skip
      (block [.addN rt rR1 rc, .storeN rt rv1, .addN rt rR2 rc, .storeN rt rv2, .addN rc rc r1])))
    hin hi1 (n := n) (κ := κ + 7) I
    (fun i d ⟨hw, hr, _⟩ => ⟨hw, by grind,
      by grind⟩)
    (fun i d v ⟨_, hr, hrr, hc, hp, hm, hrm, ho, hJd⟩ hw' => ⟨hw', fun r hB hri hrc hrt => by
        ram_simp, hrr,
      by simp only; rw [upd_other _ _ _ (Ne.symm hic)]; exact hc, hp, hm, hrm,
      ho, hJ d _ hJd (fun r _ hri _ _ => by ram_simp)
        (fun _ _ => rfl)⟩)
    (fun i d hin' ⟨hwd, hr, hrr, hc, hp, hm, hrm, ho, hJd⟩ hri => by
      obtain ⟨d₁, k₁, e₁, hk₁, f₁, hn₁, hs₁⟩ := hbody i d hin' hJd hwd hri
      have w₁ := e₁.wb_right
      have hlen := emitted_length_le φ i
      have hc₁ : d₁.nreg rc = c₀ + (emitted φ i).length := by rw [f₁.1 _ hBc]; exact hc
      have hR1₁ : d₁.nreg rR1 = R1 := by
        rw [f₁.1 _ hBR1, hr _ hBR1 (Ne.symm hiR1) (Ne.symm hcR1) hR1t]; exact hR1
      have hR2₁ : d₁.nreg rR2 = R2 := by
        rw [f₁.1 _ hBR2, hr _ hBR2 (Ne.symm hiR2) (Ne.symm hcR2) hR2t]; exact hR2
      have h1₁ : d₁.nreg r1 = 1 := by
        rw [f₁.1 _ hB1, hr _ hB1 (Ne.symm hi1) h1c h1t]; exact h1
      have hri₁ : d₁.nreg ri = i := by rw [f₁.1 _ hBi]; exact hri
      cases hφ : φ i with
      | none =>
        have hf0 := hn₁ hφ
        refine ⟨d₁, k₁ + 1, .seq e₁ (.ifLtN_true (by omega)
          (.skip w₁)), by omega, hri₁, w₁, fun r hB a b c => (f₁.1 r hB).trans (hr r hB a b c),
          fun r hB => (f₁.2.1 r hB).trans (hrr r hB), ?_, ?_, ?_, f₁.2.2.2.1.trans hrm,
          f₁.2.2.2.2.trans ho, hJ d d₁ hJd (fun r hB _ _ _ => f₁.1 r hB)
            (fun a _ => by rw [f₁.2.2.1])⟩
        · rw [emitted_succ, hφ]; simp only [Option.toList_none, List.append_nil]; exact hc₁
        · rw [emitted_succ, hφ, f₁.2.2.1]; simpa using hp
        · rw [emitted_succ, hφ, f₁.2.2.1]; simpa using hm
      | some x =>
        obtain ⟨hf1, hv1, hv2⟩ := hs₁ x hφ
        set L := emitted φ i with hL
        have hLn : L.length < n := by omega
        obtain ⟨d₂, k₂, e₂, hk₂, n₂, m₂, rr₂, rm₂, o₂⟩ : ∃ d₂ k₂, Exec P W (block [.addN rt rR1 rc,
            .storeN rt rv1, .addN rt rR2 rc, .storeN rt rv2, .addN rc rc r1]) d₁ d₂ k₂ ∧ k₂ = 5 ∧
            d₂.nreg = upd (upd d₁.nreg rt (R2 + (c₀ + L.length))) rc (c₀ + L.length + 1) ∧
            d₂.nmem = upd (upd d₁.nmem (R1 + (c₀ + L.length)) x.1) (R2 + (c₀ + L.length)) x.2 ∧
            d₂.rreg = d₁.rreg ∧ d₂.rmem = d₁.rmem ∧ d₂.output = d₁.output := by
          have u1 := upd_other d₁.nreg rt (d₁.nreg rR1 + d₁.nreg rc) hR2t
          have u2 := upd_other d₁.nreg rt (d₁.nreg rR1 + d₁.nreg rc) hct
          have u3 := upd_other d₁.nreg rt (d₁.nreg rR1 + d₁.nreg rc) (Ne.symm ht1)
          have u4 := upd_other d₁.nreg rt (d₁.nreg rR2 + d₁.nreg rc) (Ne.symm ht2)
          have u5 := upd_other d₁.nreg rt (d₁.nreg rR2 + d₁.nreg rc) hct
          have u6 := upd_other d₁.nreg rt (d₁.nreg rR2 + d₁.nreg rc) h1t
          exec_block
          · omega
          · grind
          · grind
          · refine ⟨rfl, ?_, ?_, rfl, rfl, rfl⟩
            · ram_simp
            · config_simp
              rw [u3, u1, u2, u4, hR1₁, hR2₁, hc₁, hv1, hv2]
        have hne12 : ∀ t, t < n → R1 + c₀ + t ≠ R2 + (c₀ + L.length) := fun t ht => by omega
        refine ⟨d₂, k₁ + (k₂ + 2), .seq e₁ (.ifLtN_false (by omega)
          e₂), by omega, ?_, e₂.wb_right, ?_, ?_, ?_, ?_, ?_, by rw [rm₂]; exact f₁.2.2.2.1.trans hrm,
          by rw [o₂]; exact f₁.2.2.2.2.trans ho, ?_⟩
        · ram_simp
        · intro r hB a b c'
          rw [n₂, upd_other _ _ _ b, upd_other _ _ _ c']; exact (f₁.1 r hB).trans (hr r hB a b c')
        · intro r hB; rw [rr₂]; exact (f₁.2.1 r hB).trans (hrr r hB)
        · rw [n₂, upd_same, emitted_succ, hφ, ← hL]; simp; omega
        · intro t ht
          rw [emitted_succ, hφ] at ht ⊢
          simp only [Option.toList_some, List.length_append, List.length_cons, List.length_nil]
            at ht
          rw [m₂, f₁.2.2.1]
          rcases Nat.lt_or_ge t L.length with htl | htl
          · rw [List.getD_append _ _ _ _ htl]
            obtain ⟨p1, p2⟩ := hp t htl
            refine ⟨?_, ?_⟩
            · rw [upd_other _ _ _ (hne12 t (by omega)), upd_other _ _ _ (by omega), p1]
            · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), p2]
          · have hteq : t = L.length := by omega
            subst hteq
            rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
            try simp only [List.getD_cons_zero]
            refine ⟨?_, ?_⟩
            · rw [upd_other _ _ _ (by omega), show R1 + c₀ + L.length = R1 + (c₀ + L.length) by
                omega, upd_same]; rfl
            · rw [show R2 + c₀ + L.length = R2 + (c₀ + L.length) by omega, upd_same]; rfl
        · intro a ha
          rw [emitted_succ, hφ] at ha
          simp only [Option.toList_some, List.length_append, List.length_cons,
            List.length_nil] at ha
          rw [m₂, f₁.2.2.1, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
          exact hm a (by omega)
        · refine hJ d d₂ hJd (fun r hB _ hrc hrt => ?_) (fun a ha => ?_)
          · rw [n₂, upd_other _ _ _ hrc, upd_other _ _ _ hrt]; exact f₁.1 r hB
          · rw [m₂, f₁.2.2.1, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)])
    hw (by omega) (fun d hwd h0 hr hm hrr hrm ho => ⟨hwd, fun r _ hri _ _ => hr r hri,
      fun r _ => by rw [hrr], by grind [emitted],
      fun t ht => by grind [emitted], fun a _ => by rw [hm], hrm, ho,
      hJ c d hJc (fun r _ hri _ _ => hr r hri) (fun a _ => by rw [hm])⟩)
  exact ⟨c', k, ex, by nlinarith, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- Pairs at two bases, then more pairs after them. -/
theorem PairsAt.append {m : ℕ → ℕ} {R1 R2 : ℕ} {l l' : List (ℕ × ℕ)} (h : PairsAt m R1 R2 l)
    (h' : PairsAt m (R1 + l.length) (R2 + l.length) l') : PairsAt m R1 R2 (l ++ l') := by
  grind [Chazelle.Core.OracleR.PairsAt]

/-- Pairs survive memory changes away from their cells. -/
theorem PairsAt.congr {m m' : ℕ → ℕ} {R1 R2 : ℕ} {l : List (ℕ × ℕ)} (h : PairsAt m R1 R2 l)
    (hm : ∀ t, t < l.length → m' (R1 + t) = m (R1 + t) ∧ m' (R2 + t) = m (R2 + t)) :
    PairsAt m' R1 R2 l := fun t ht => by
  ram_grind

/-! ## Invariants of the loops: kept registers and old memory -/

section
variable (c₀ : Config) (K : ℕ → Bool) (lo : ℕ)
include c₀ K lo
/-- The registers of `K` keep their values of `c₀` and the memory below `lo` is that of `c₀`. -/
def JK (d : Config) : Prop :=
  (∀ r, K r = true → d.nreg r = c₀.nreg r) ∧ (∀ a, a < lo → d.nmem a = c₀.nmem a)

theorem JK.refl : JK c₀ K lo c₀ :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩


end

/-- `JK` survives writes to registers outside `K` and to memory from `lo` on. -/
theorem JK.stable {c₀ : Config} {K : ℕ → Bool} {lo : ℕ} {B : ℕ → Bool} {rs : List ℕ}
    (hK : ∀ r, K r = true → B r = false ∧ r ∉ rs) {c c' : Config} (h : JK c₀ K lo c)
    (hr : ∀ r, B r = false → r ∉ rs → c'.nreg r = c.nreg r)
    (hm : ∀ a, a < lo → c'.nmem a = c.nmem a) : JK c₀ K lo c' :=
  by core_grind

/-! ## The frame of a stage -/

/-- **The frame of a stage**: registers outside `B` and memory below `lo` unchanged, real memory
below `lo` unchanged, nothing emitted. -/
def PF (B : ℕ → Bool) (lo : ℕ) (c c' : Config) : Prop :=
  (∀ r, B r = false → c'.nreg r = c.nreg r) ∧ (∀ r, B r = false → c'.rreg r = c.rreg r) ∧
    (∀ a, a < lo → c'.nmem a = c.nmem a) ∧ (∀ a, a < lo → c'.rmem a = c.rmem a) ∧
    c'.output = c.output

theorem PF.trans {B : ℕ → Bool} {lo : ℕ} {c₁ c₂ c₃ : Config} (h₁ : PF B lo c₁ c₂)
    (h₂ : PF B lo c₂ c₃) : PF B lo c₁ c₃ :=
  by core_grind

theorem PF.mono {B B' : ℕ → Bool} {lo lo' : ℕ} {c c' : Config} (h : PF B lo c c')
    (hB : ∀ r, B r = true → B' r = true) (hlo : lo' ≤ lo) : PF B' lo' c c' := by
  core_grind

/-- **A frame without the allocator bounds.** -/
def FrameN (S : Finset ℕ) (c c' : Config) : Prop :=
  (∀ r, bandOf r ∉ S → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧ (∀ r, bandOf r ∉ S → c'.rreg r = c.rreg r) ∧
    (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
    (∀ a, a < c.nreg ALLOC → c'.rmem a = c.rmem a) ∧ c'.output = c.output

theorem FrameN.trans {S : Finset ℕ} {c c₁ c₂ : Config} (h₁ : FrameN S c c₁) (h₂ : FrameN S c₁ c₂)
    (hA : c.nreg ALLOC ≤ c₁.nreg ALLOC) : FrameN S c c₂ :=
  by core_grind

theorem FrameN.mono {S S' : Finset ℕ} {c c' : Config} (h : FrameN S c c') (hS : S ⊆ S') :
    FrameN S' c c' :=
  by core_grind

theorem Frame.toN {S : Finset ℕ} {c c' : Config} {k : ℕ} (h : Frame S c c' k) : FrameN S c c' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-- A stage frame is a frame without the allocator bounds. -/
theorem PF.frameN {B : ℕ → Bool} {S : Finset ℕ} {c c' : Config} (h : PF B (c.nreg ALLOC) c c')
    (hB : ∀ r, B r = true → bandOf r ∈ S ∨ r = ALLOC) (hrA : c'.rreg ALLOC = c.rreg ALLOC) :
    FrameN S c c' := by
  grind [Chazelle.Core.OracleR.FrameN, Chazelle.Core.OracleR.PF]

end

end OracleR

end Chazelle.Core
