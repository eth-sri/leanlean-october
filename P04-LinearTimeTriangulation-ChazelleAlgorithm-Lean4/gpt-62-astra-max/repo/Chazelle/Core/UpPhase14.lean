module

public import Chazelle.Core.UpPhase13

/-!
# WP-J up phase, part 14: the chains of a grade

`chainsL = while i < cnt do chainS` and `chainsL_exec`: all `gradeCount n g` chains of grade
`g`, at cost `cnt (stepB g + 2) + 2`, leaving the cells of all chains (`ChainMem … cnt`).
-/

namespace Chazelle.Core.Up

open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41

@[expose] public section

/-- **The chains of the current grade.** -/
def chainsL (sB sL sG sP : Stmt) : Stmt := .whileLtN 170015 170008 (chainS sB sL sG sP)

section proofs

variable {O : OracleIface} {P : Polygon} {W : ℕ}

set_option maxHeartbeats 32000000 in
/-- **All chains of grade `g`.** -/
theorem chainsL_exec {sB sL sG : Stmt} {κB κL : ℕ} {κG : ℕ → ℕ}
    (hB : Meets sB bruteBands
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c bBrute 1 ∧
        rd c bBrute 0 + rd c bBrute 1 + 1 ≤ P.n ∧ 1 ≤ rd c bBrute 2 ∧
        (rd c bBrute 1 = 1 ∨ 2 ≤ rd c bBrute 2))
      (fun P c c' => ∃ C N, C.P = Qof P ∧ C.s = rd c bBrute 0 ∧ C.m = rd c bBrute 1 ∧
        Robust (c'.nreg ALLOC) c'.nmem (fun m => NFAt m (rd c' bBrute 3) N) ∧
        IsCanonicalNF (chainModel C) (Qof P) N (rd c bBrute 2) 4)
      (fun _ c => κB * (rd c bBrute 1 + 1) ^ 3))
    (hL : Meets sL l41Bands
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
        (gradeCtx O).holds P c.nmem (rd c bL41 0) (c.nreg ALLOC) ∧
        rd c bL41 3 ≤ c.nmem (rd c bL41 0) ∧ lemma41Start ≤ rd c bL41 3 ∧
        rd c bL41 1 + rd c bL41 2 + 1 ≤ P.n ∧
        2 ^ (rd c bL41 3 - 1) < rd c bL41 2 ∧ rd c bL41 2 ≤ 2 ^ rd c bL41 3)
      (fun P c c' => ∃ C N, C.P = Qof P ∧ C.s = rd c bL41 1 ∧ C.m = rd c bL41 2 ∧
        Robust (c'.nreg ALLOC) c'.nmem (fun m => NFAt m (rd c' bL41 4) N) ∧
        IsCanonicalNF (chainModel C) (Qof P) N (gradeGran (rd c bL41 3)) 4)
      (fun _ c => κL * (lemma41Nat (rd c bL41 3) + 1)))
    (hGr : Meets sG granBands
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c bGran 2 ∧
        ModelDescWF P (c.nreg ALLOC) c.nmem (rd c bGran 0) ∧
        ∃ M N, ModelDescAt c.nmem (rd c bGran 0) (Qof P) M ∧ GoodModel M ∧
          NFWithin c.nmem (rd c bGran 1) (c.nreg ALLOC) N ∧ IsNF M (Qof P) N ∧
          M.DegLe (N.F M (Qof P)) (rd c bGran 2) ∧
          M.Semigranular (N.F M (Qof P)) (rd c bGran 3))
      (fun P c c' => ∀ M N, ModelDescAt c.nmem (rd c bGran 0) (Qof P) M →
        NFAt c.nmem (rd c bGran 1) N →
        ∃ N', c.nreg ALLOC ≤ rd c' bGran 4 ∧ NFWithin c'.nmem (rd c' bGran 4) (c'.nreg ALLOC) N' ∧
          N'.F M (Qof P) ⊆ N.F M (Qof P) ∧
          IsCanonicalNF M (Qof P) N' (rd c bGran 3) (rd c bGran 2))
      (fun _ c => κG (rd c bGran 2) *
        (c.nmem (rd c bGran 1) * (Nat.clog 2 (c.nmem (rd c bGran 1)) + 1) + 1)))
    (hV : O.Valid) (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) (hn : 2 ≤ P.n) {c : Config}
    (hw : WordsBounded W c) {hp h g R x A : ℕ}
    (hu : URegs c P.n hp h g (gradeCount P.n g) (gradeGran g) (gradeCount P.n (g - 1)) R)
    (hA : c.nreg ALLOC = A) (h15 : c.nreg 170015 = 0) (h16 : c.nreg 170016 = 0)
    (h18 : c.nreg 170018 = x) (h35 : c.nreg 170035 = 0) (h36 : c.nreg 170036 = 1)
    (h2g : 2 ^ g ≤ 2 * P.n)
    (hM : Robust A c.nmem fun m => ChainMem O P m h hp g R x 0 A)
    (hW : A + (gradeCount P.n g + 1) * (stepB κB κL κG O.κ g + 8) ≤ W) :
    ∃ c' k, Exec P W (chainsL sB sL sG O.prep) c c' k ∧
      k ≤ gradeCount P.n g * (stepB κB κL κG O.κ g + 2) + 2 ∧
      WordsBounded W c' ∧ A ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ A + k ∧
      URegs c' P.n hp h g (gradeCount P.n g) (gradeGran g) (gradeCount P.n (g - 1)) R ∧
      Robust (c'.nreg ALLOC) c'.nmem
        (fun m => ChainMem O P m h hp g R (c'.nreg 170018) (gradeCount P.n g) (c'.nreg ALLOC)) ∧
      (∀ a, a < A → c'.nmem a = c.nmem a) ∧ (∀ a, a < A → c'.rmem a = c.rmem a) ∧
      c'.output = c.output ∧
      (∀ r, Kept r → r ≠ 170015 → r ≠ 170016 → r ≠ 170017 → r ≠ 170018 → r ≠ 170035 →
        r ≠ 170036 → c'.nreg r = c.nreg r) ∧
      (∀ r, OutB (bandOf r) → c'.rreg r = c.rreg r) := by
  set cnt := gradeCount P.n g with hcnt
  set K := stepB κB κL κG O.κ g with hK
  let I : Config → Prop := fun c' => ∃ i, i ≤ cnt ∧ WordsBounded W c' ∧
    URegs c' P.n hp h g cnt (gradeGran g) (gradeCount P.n (g - 1)) R ∧
    c'.nreg 170015 = i ∧ c'.nreg 170016 = gradeStart g i ∧ c'.nreg 170035 = 6 * i ∧
    c'.nreg 170036 = 2 * i + 1 ∧ A ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ A + i * (K + 2) ∧
    Robust (c'.nreg ALLOC) c'.nmem
      (fun m => ChainMem O P m h hp g R (c'.nreg 170018) i (c'.nreg ALLOC)) ∧
    (∀ a, a < A → c'.nmem a = c.nmem a) ∧ (∀ a, a < A → c'.rmem a = c.rmem a) ∧
    c'.output = c.output ∧
    (∀ r, Kept r → r ≠ 170015 → r ≠ 170016 → r ≠ 170017 → r ≠ 170018 → r ≠ 170035 →
      r ≠ 170036 → c'.nreg r = c.nreg r) ∧
    (∀ r, OutB (bandOf r) → c'.rreg r = c.rreg r)
  have hI0 : I c := ⟨0, by omega, hw, hu, h15, by rw [h16]; unfold gradeStart; ring,
    by rw [h35], by rw [h36], by omega, by omega, by rw [h18, hA]; exact hM,
    fun _ _ => rfl, fun _ _ => rfl, rfl, fun _ _ _ _ _ _ _ _ => rfl, fun _ _ => rfl⟩
  obtain ⟨c', k, e, ⟨i, hic, hw', hu', i15, i16, i35, i36, a1, a2, hM', mm, mr, mo, fr, frr⟩,
      htest, hk, hψ⟩ :=
    whileLtN_potential_lb' (P := P) (W := W) (a := 170015) (b := 170008)
      (body := chainS sB sL sG O.prep) I (fun c' => (cnt - c'.nreg 170015) * (K + 2))
      (fun c' => c'.nreg ALLOC) (fun c' ⟨_, _, h, _⟩ => h)
      (fun c2 ⟨i, hic, hw2, hu2, i15, i16, i35, i36, a1, a2, hM2, mm, mr, mo, fr, frr⟩ htest => by
        rw [i15, hu2.r08] at htest
        have hKm : i * (K + 2) + (K + 2) ≤ cnt * (K + 2) := by
          rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ htest
        have hW2 : c2.nreg ALLOC + K + 6 ≤ W := by
          have : (cnt + 1) * (K + 8) = cnt * (K + 2) + 6 * cnt + K + 8 := by ring
          omega
        obtain ⟨c3, k3, e3, hk3, hw3, b1, b2, hu3, j15, j16, j35, j36, hM3, m3, r3, o3, f3,
            ff3⟩ :=
          chainS_exec (O := O) (sB := sB) (sL := sL) (sG := sG) hB hL hGr hV hG hWh hn hw2 hu2
            rfl i15 i16 rfl i35 i36 htest h2g hM2 hW2
        refine ⟨c3, k3, e3, ⟨i + 1, by omega, hw3, hu3, j15, j16, j35, j36, by omega, ?_, hM3,
          fun a ha => by rw [m3 a (by omega), mm a ha],
          fun a ha => by rw [r3 a (by omega), mr a ha], by rw [o3, mo],
          fun r hr a1 a2 a3 a4 a5 a6 => by rw [f3 r hr a1 a2 a3 a4 a5 a6, fr r hr a1 a2 a3 a4 a5 a6],
          fun r hr => by rw [ff3 r hr, frr r hr]⟩, ?_, by omega⟩
        · rw [Nat.succ_mul]; omega
        · rw [j15, i15]
          have : (cnt - i) * (K + 2) = (cnt - (i + 1)) * (K + 2) + (K + 2) := by
            rw [← Nat.succ_mul]; congr 1; omega
          omega) hI0
  have hic' : i = cnt := by rw [i15, hu'.r08] at htest; omega
  subst hic'
  refine ⟨c', k, e, by rw [h15] at hk; simpa using hk, hw', a1, by omega, hu', hM', mm, mr, mo,
    fr, frr⟩

end proofs

end

end Chazelle.Core.Up
