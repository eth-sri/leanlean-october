module

public import Chazelle.Core.OraclePrepMem
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics

/-!
# Lemma 3.6 (WP-H), preprocessing part 31: the header and the allocator payment

* `stores L`: the registers of `L` stored at consecutive words from the pointer `110005`;
* `hdrS`: the 18-word header of the structure at the allocator (its address in `110003`, the
  bound `E` after it stored as its fourth word);
* `payS`: a counting loop of `ALLOC - A₀` rounds (`A₀` in `120026`), so that the growth of the
  allocator is paid by steps.
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

/-- Store the registers of `L` at consecutive words from the pointer `110005`. -/
def stores : List ℕ → Stmt
  | [] => .skip
  | r :: L => .seq (block [.storeN 110005 r, .addN 110005 110005 120011]) (stores L)

theorem stores_exec {P : Polygon} {W : ℕ} (L : List ℕ) {c : Config} (hw : WordsBounded W c)
    {p : ℕ} (hp : c.nreg 110005 = p) (h1 : c.nreg 120011 = 1) (hL : ∀ r ∈ L, r ≠ 110005)
    (hW : p + L.length ≤ W) :
    ∃ c' k, Exec P W (stores L) c c' k ∧ k = 2 * L.length ∧ c'.nreg 110005 = p + L.length ∧
      (∀ r, r ≠ 110005 → c'.nreg r = c.nreg r) ∧
      (∀ i, i < L.length → c'.nmem (p + i) = c.nreg (L.getD i 0)) ∧
      (∀ a, (a < p ∨ p + L.length ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  induction L generalizing c p with
  | nil =>
    exact ⟨c, 0, .skip hw, rfl, by simpa using hp, fun _ _ => rfl, fun i hi => by simp at hi,
      fun _ _ => rfl, rfl, rfl, rfl⟩
  | cons r L ih =>
    have hr : r ≠ 110005 := hL r (by simp)
    obtain ⟨c₁, k₁, e₁, hk₁, v5, R₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W
        (block [.storeN 110005 r, .addN 110005 110005 120011]) c c₁ k₁ ∧ k₁ = 2 ∧
        c₁.nreg 110005 = p + 1 ∧ (∀ r', r' ≠ 110005 → c₁.nreg r' = c.nreg r') ∧
        c₁.nmem = upd c.nmem p (c.nreg r) ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧
        c₁.output = c.output := by
      exec_block
      · config_simp; rw [hp, h1]; sio at hW
      · refine ⟨rfl, by config_simp; rw [hp, h1], fun r' hr' => ?_, by config_simp; rw [hp],
          rfl, rfl, rfl⟩
        config_simp; rw [upd_other _ _ _ hr']
    obtain ⟨c₂, k₂, e₂, hk₂, v5', R₂, m₂, m₂', rr₂, rm₂, o₂⟩ := ih e₁.wb_right v5
      (by rw [R₁ _ (by decide), h1]) (fun r' hr' => hL r' (by simp [hr']))
      (by sio at hW)
    refine ⟨c₂, _, .seq e₁ e₂, by sio, by rws [v5']; omega,
      fun r' hr' => by rw [R₂ r' hr', R₁ r' hr'], fun i hi => ?_, fun a ha => ?_,
      by rw [rr₂, rr₁], by rw [rm₂, rm₁], by rw [o₂, o₁]⟩
    · rcases i with _ | j
      · rw [Nat.add_zero, m₂' p (Or.inl (by omega)), m₁]; simp [upd]
      · simp [List.length_cons] at hi
        have hj : j < L.length := by omega
        have := m₂ j hj
        rw [show p + 1 + j = p + (j + 1) by omega] at this
        rw [this, List.getD_cons_succ]
        have hmem : L.getD j 0 ∈ L := by
          rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
        exact R₁ _ (hL _ (List.mem_cons_of_mem _ hmem))
    · simp at ha
      rw [m₂' a (by omega), m₁, upd_other _ _ _ (by omega)]

/-- The registers of the header, in order. -/
def hdrRegs : List ℕ :=
  [120013, 120014, 120049, 9999, 120030, 120031, 130004, 130005, 60100, 60102, 60007, 60110,
    120038, 120039, 120040, 120041, 120042, 60034]

/-- **The header** at the allocator (address in `110003`). -/
def hdrS : Stmt :=
  .seq (block [.copyN 110003 9999, .constN 110004 18, .addN 9999 9999 110004, .copyN 110005 110003])
    (stores hdrRegs)

theorem hdrS_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {O : ℕ}
    (hAl : c.nreg 9999 = O) (h1 : c.nreg 120011 = 1) (hW : O + 18 ≤ W) :
    ∃ c' k, Exec P W hdrS c c' k ∧ k = 40 ∧ c'.nreg 110003 = O ∧ c'.nreg 9999 = O + 18 ∧
      (∀ r, r ≠ 110003 → r ≠ 110004 → r ≠ 110005 → r ≠ 9999 → c'.nreg r = c.nreg r) ∧
      (∀ i, i < 18 → i ≠ 3 → c'.nmem (O + i) = c.nreg (hdrRegs.getD i 0)) ∧
      c'.nmem (O + 3) = O + 18 ∧
      (∀ a, (a < O ∨ O + 18 ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, a3, a9, a5, R₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.copyN 110003 9999, .constN 110004 18, .addN 9999 9999 110004,
        .copyN 110005 110003]) c c₁ k₁ ∧ k₁ = 4 ∧ c₁.nreg 110003 = O ∧ c₁.nreg 9999 = O + 18 ∧
      c₁.nreg 110005 = O ∧
      (∀ r, r ≠ 110003 → r ≠ 110004 → r ≠ 110005 → r ≠ 9999 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    · omega
    · config_simp; rwo [hAl]
    · refine ⟨rfl, by config_simp; exact hAl, by config_simp; rw [hAl], by config_simp; exact hAl,
        fun r a b d e => ?_, rfl, rfl, rfl, rfl⟩
      config_simp; simp [upd_apply]; rw [ite_eq_right b, ite_eq_right e, ite_eq_right d, ite_eq_right a]
  obtain ⟨c₂, k₂, e₂, hk₂, v5, R₂, mm, mo, rr₂, rm₂, o₂⟩ := stores_exec (P := P) hdrRegs
    e₁.wb_right a5 (by rw [R₁ _ (by decide) (by decide) (by decide) (by decide), h1])
    (by decide) (by sio [hdrRegs])
  have hl : hdrRegs.length = 18 := rfl
  refine ⟨c₂, _, .seq e₁ e₂, by rw [hk₁, hk₂, hl], by rw [R₂ _ (by decide), a3],
    by rw [R₂ _ (by decide), a9], fun r a b d e => by rw [R₂ r d, R₁ r a b d e],
    fun i hi h3 => ?_, ?_, fun a ha => by rw [mo a (by rwx [hl]), m₁],
    by rw [rr₂, rr₁], by rw [rm₂, rm₁], by rw [o₂, o₁]⟩
  · rw [mm i (by rwx [hl])]
    have hne : hdrRegs.getD i 0 ≠ 110003 ∧ hdrRegs.getD i 0 ≠ 110004 ∧
        hdrRegs.getD i 0 ≠ 110005 ∧ hdrRegs.getD i 0 ≠ 9999 := by
      interval_cases i <;> simp_all [hdrRegs]
    exact R₁ _ hne.1 hne.2.1 hne.2.2.1 hne.2.2.2
  · rw [mm 3 (by rwo [hl])]
    exact a9

/-! ## The payment of the allocator -/

/-- **The payment**: `ALLOC - A₀` rounds of a counting loop (`A₀` in `120026`). -/
def payS : Stmt := .seq (.instr (.subN 110008 9999 120026)) (forS 110009 110008 120011 .skip)

theorem payS_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {A₀ E : ℕ}
    (h26 : c.nreg 120026 = A₀) (hAl : c.nreg 9999 = E) (h1 : c.nreg 120011 = 1) :
    ∃ c' k, Exec P W payS c c' k ∧ k ≤ 3 * (E - A₀) + 4 ∧ E - A₀ ≤ k ∧
      (∀ r, r ≠ 110008 → r ≠ 110009 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have e₁ := Exec.subN (P := P) hw 110008 9999 120026
  set c₁ : Config := { c with nreg := upd c.nreg 110008 (c.nreg 9999 - c.nreg 120026) } with hc₁
  have v8 : c₁.nreg 110008 = E - A₀ := by rw [hc₁]; config_simp; rw [hAl, h26]
  have R₁ : ∀ r, r ≠ 110008 → c₁.nreg r = c.nreg r := fun r hr => by
    rw [hc₁]; config_simp; rw [upd_other _ _ _ hr]
  let I : ℕ → Config → Prop := fun _ d => WordsBounded W d ∧ d.nreg 110008 = E - A₀ ∧
    d.nreg 120011 = 1 ∧ (∀ r, r ≠ 110009 → d.nreg r = c₁.nreg r) ∧ d.nmem = c₁.nmem ∧
    d.rreg = c₁.rreg ∧ d.rmem = c₁.rmem ∧ d.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, ⟨-, -, -, R₂, m₂, rr₂, rm₂, o₂⟩, -, hn⟩ := forS_exec (P := P) (W := W)
    (ri := 110009) (rn := 110008) (r1 := 120011) (body := .skip) (by decide) (by decide)
    (n := E - A₀) (κ := 0) I
    (fun i d h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i d v h hw' => ⟨hw', by simp [upd, h.2.1], by simp [upd, h.2.2.1],
      fun r hr => by simp; rw [upd_other _ _ _ hr]; exact h.2.2.2.1 r hr,
      h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩)
    (fun i d _ h hri => ⟨d, 0, .skip h.1, le_rfl, hri, h⟩)
    e₁.wb_right (by rw [← v8]; exact e₁.wb_right.1 _)
    (fun d hwd h0 hr hm hrr hrm ho => ⟨hwd, by rw [hr _ (by decide), v8],
      by rw [hr _ (by decide), R₁ _ (by decide), h1], fun r hr' => hr r hr', hm, hrr, hrm, ho⟩)
  refine ⟨c₂, _, .seq e₁ e₂, by omega, by omega, fun r a b => by rw [R₂ r b, R₁ r a], m₂,
    rr₂, rm₂, o₂⟩

end

end OracleR

end Chazelle.Core
