module

public import Chazelle.Core.DownPhaseDrvRLib
public import Chazelle.Core.SortList
public import Chazelle.RewriteTactics
set_option maxHeartbeats 1000000

/-!
# Down-phase driver (RAM side): copying a memory block

`cpS` copies `len = r210061` words from `src = r210062` to `dst = r210063` (counter `r210060`,
scratch `r210064`, `r210065`, the constant `r210034 = 1`): `cpS_exec`.  `cpArgs` sets the three
arguments from three registers.
-/

namespace Chazelle.Core

namespace DrvR

open Machine Machine.Stmt Programs SortL BuildRam

@[expose] public section

/-- One word. -/
def cpBody : Stmt :=
  block [.addN 210064 210062 210060, .loadN 210065 210064, .addN 210064 210063 210060,
    .storeN 210064 210065, .addN 210060 210060 210034]

/-- **Copy `len` words from `src` to `dst`.** -/
def cpS : Stmt := .seq (.instr (.constN 210060 0)) (.whileLtN 210060 210061 cpBody)

/-- The registers `cpS` writes. -/
def Bcp (r : ℕ) : Bool := decide (r = 210060) || decide (r = 210064) || decide (r = 210065)

theorem wrM_cpBody : wrM Bcp cpBody = true := by decide

section exec

variable {P : Polygon} {W : ℕ}

theorem cpBody_exec (d : Config) (hw : WordsBounded W d) {i S D : ℕ}
    (h60 : d.nreg 210060 = i) (h62 : d.nreg 210062 = S) (h63 : d.nreg 210063 = D)
    (h34 : d.nreg 210034 = 1) (hW1 : S + i ≤ W) (hW2 : D + i ≤ W) (hW3 : i + 1 ≤ W) :
    ∃ d' k, Exec P W cpBody d d' k ∧ k = 5 ∧ d'.nreg 210060 = i + 1 ∧
      d'.nmem = upd d.nmem (D + i) (d.nmem (S + i)) ∧ FrameM Bcp d d' := by
  obtain ⟨d', k, ex, hk, h1, h2⟩ : ∃ d' k, Exec P W cpBody d d' k ∧ k = 5 ∧
      d'.nreg 210060 = i + 1 ∧ d'.nmem = upd d.nmem (D + i) (d.nmem (S + i)) := by
    unfold cpBody
    exec_block
    all_goals try (config_simp; (try simp [h60, h62, h63, h34]); omega)
    refine ⟨rfl, ?_, ?_⟩ <;> config_simp <;> simp [h60, h62, h63, h34]
  exact ⟨d', k, ex, hk, h1, h2, exec_frameM ex wrM_cpBody⟩

/-- **The copy.** -/
theorem cpS_exec {d : Config} (hw : WordsBounded W d) {S D len : ℕ}
    (h61 : d.nreg 210061 = len) (h62 : d.nreg 210062 = S) (h63 : d.nreg 210063 = D)
    (h34 : d.nreg 210034 = 1) (hsep : S + len ≤ D ∨ D + len ≤ S)
    (hW : S + len ≤ W) (hW' : D + len + 1 ≤ W) :
    ∃ d' k, Exec P W cpS d d' k ∧ k ≤ 7 * len + 3 ∧ WordsBounded W d' ∧
      seg d'.nmem D len = seg d.nmem S len ∧
      (∀ a, (a < D ∨ D + len ≤ a) → d'.nmem a = d.nmem a) ∧ FrameM Bcp d d' := by
  have e₀ := Exec.constN (P := P) hw 210060 0 (Nat.zero_le _)
  set d₀ : Config := { d with nreg := upd d.nreg 210060 0 } with hd₀
  have g₀ : ∀ r, r ≠ 210060 → d₀.nreg r = d.nreg r := fun r hr => by rw [hd₀]; simp [hr]
  have f₀ : FrameM Bcp d d₀ := exec_frameM e₀ (by decide)
  let Inv : ℕ → Config → Prop := fun i e => WordsBounded W e ∧ e.nreg 210060 = i ∧
    e.nreg 210061 = len ∧ e.nreg 210062 = S ∧ e.nreg 210063 = D ∧ e.nreg 210034 = 1 ∧
    FrameM Bcp d e ∧
    ∀ a, e.nmem a = if D ≤ a ∧ a < D + i then d.nmem (S + (a - D)) else d.nmem a
  obtain ⟨d', k, ex, ⟨w', _, _, _, _, _, hf', hm'⟩, hk⟩ := forLoop (P := P) (W := W)
    (ir := 210060) (nr := 210061) Inv 5 len
    (fun i e ⟨hw, h1, h2, _⟩ => ⟨hw, h1, h2⟩)
    (fun i e hi ⟨hw, h1, h2, h3, h4, h5, hf, hm⟩ => by
      obtain ⟨e', k, ex, hk, h1', hm', hf'⟩ := cpBody_exec (P := P) e hw h1 h3 h4 h5
        (by omega) (by omega) (by omega)
      have g  := hf'.1
      refine ⟨e', k, ex, ⟨ex.wb_right, h1', (g _ (by decide)).trans h2, (g _ (by decide)).trans h3,
        (g _ (by decide)).trans h4, (g _ (by decide)).trans h5, hf.trans hf', fun a => ?_⟩,
        by omega⟩
      rw [hm', Machine.upd_apply]
      by_cases ha : a = D + i
      · rw [ite_eq_left ha, hm (S + i), ite_eq_right (by omega), ite_eq_left (by omega),
          show a - D = i by omega]
      · rw [ite_eq_right ha, hm a]; split_ifs <;> first | rfl | omega)
    (j := 0) ⟨e₀.wb_right, by rws [hd₀], by rw [g₀ _ (by decide), h61],
      by rw [g₀ _ (by decide), h62], by rw [g₀ _ (by decide), h63], by rw [g₀ _ (by decide), h34],
      f₀, fun a => by rw [ite_eq_right (by omega)]⟩ (Nat.zero_le _)
  refine ⟨d', 1 + k, .seq e₀ ex, by omega, w', ?_, fun a ha => ?_, hf'⟩
  · unfold seg; apply List.map_congr_left; intro i hi
    rw [List.mem_range] at hi
    rw [hm', ite_eq_left (by omega), show D + i - D = i by omega]
  · rw [hm', ite_eq_right (by omega)]

end exec

end

end DrvR

end Chazelle.Core
