module

public import Chazelle.Core.DownPhaseDrvPTop

/-! Specialize the shared grade-cover proof to the interior oracle environment. -/

namespace Chazelle.Core.IOrc
open Machine

@[expose] public section

variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : Stat}

theorem SEnv.coverEnv {c : Config} (h : SEnv P W O s c) : DrvP.TEnv P W O ⟨s.A₀, s.m₀, s.h⟩ c :=
  ⟨h.good, h.hW, h.r11, h.r12, h.r16, h.r17, h.mem, Nat.le_trans (Nat.le_add_right _ _) h.alloc, h.grade⟩

theorem cmpUpd_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c)
    (hv : c.nreg 170046 < P.n) (hc : c.nreg 170059 < P.n) :
    ∃ c' k, Exec P W cmpUpd c c' k ∧ k ≤ 250 ∧
      c'.nreg 170046 = (if Y P (c.nreg 170046) < Y P (c.nreg 170059) then c.nreg 170059
        else c.nreg 170046) ∧
      (∀ r, r ≠ 170046 → (r < 170060 ∨ 170067 ≤ r) → (r < 10000 ∨ 10500 ≤ r) →
        c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem :=
  DrvP.cmpUpd_exec c hw hS.coverEnv hv hc

theorem topLoop_exec {x y : ℕ} {G : ℕ → Prop} (c : Config) (hw : WordsBounded W c)
    (hS : SEnv P W O s c) (hx : c.nreg 170050 = x) (hy : c.nreg 170051 = y) (hxy : x ≤ y)
    (hyn : y ≤ P.n - 1) (hcap : y - x ≤ 2 ^ (s.m₀ s.h - 1)) (hvG : G (c.nreg 170046))
    (hvn : c.nreg 170046 < P.n) (hvx : Y P x ≤ Y P (c.nreg 170046))
    (hvy : Y P y ≤ Y P (c.nreg 170046)) (hgood : ∀ v, x ≤ v → v ≤ y → G v) :
    ∃ c' k, Exec P W topLoop c c' k ∧ k ≤ 602 * Nat.log 2 (2 * (y - x)) + 6 ∧ SEnv P W O s c' ∧
      G (c'.nreg 170046) ∧ c'.nreg 170046 < P.n ∧
      (∀ v, x ≤ v → v ≤ y → Y P v ≤ Y P (c'.nreg 170046)) ∧
      (∀ r, (r < 170046 ∨ 170070 ≤ r) → (r < 10000 ∨ 10500 ≤ r) → c'.nreg r = c.nreg r) ∧
      Y P (c.nreg 170046) ≤ Y P (c'.nreg 170046) ∧ c'.nmem = c.nmem := by
  obtain ⟨d, k, e, hk, -, hg, hn, hy', hf, hY, hm⟩ :=
    DrvP.topLoop_exec c hw hS.coverEnv hx hy hxy hyn hcap hvG hvn hvx hvy hgood
  exact ⟨d, k, e, hk, hS.keep (fun r hr hr' => hf r (Or.inl (by omega)) (Or.inr (by omega)))
    (fun a _ => congrFun hm a) (by rw [hf ALLOC (Or.inl (by decide)) (Or.inl (by decide))]),
    hg, hn, hy', hf, hY, hm⟩

end
end Chazelle.Core.IOrc
