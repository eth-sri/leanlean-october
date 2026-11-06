module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseBaseLoop2
public import Chazelle.Core.NFBuildMain

/-!
# Down phase, A1: dropping the augmented chords (`DropAugSpec`)

At the base of the down phase the chord family of the interior map contains `Full`, and
`OutputSpec` needs exactly `Full`.  `dropStmt` removes the chords that are not vertex chords
(`keepX`: no walk edge of the record starts at its height vertex) in linear time, keeping the
event order: the new chord list `keepL` and the renumbered event list `dropE` are a valid input of
`BuildNFSortedSpec` (`ChordTriplesOK`, a `codeLe`-sorted permutation), and the new family is the
old one intersected with `Full` (`family_keepL`).

**`dropAug : DropAugSpec`**, cost `80 (K + 1)`.  Design: `docs/design-downphase-nf.md` §3.
-/

namespace Chazelle.Core

@[expose] public section

open Machine Machine.Stmt Programs SortL
open BuildNF (codeLe)

/-- The `LeftInside` bit of an interior descriptor at `D`. -/
def liBit (m : ℕ → ℕ) (D : ℕ) : Bool := decide (m (D + 1) = 1)

/-- **A1: drop the augmented chords.**  Inputs (band `bDown`): the interior descriptor `D`
(`bDown 0`, word `D + 1` the `LeftInside` bit), the chord list `B` (`bDown 1`) of length `K`
(`bDown 2`), the event list `SE` (`bDown 3`, a `codeLe`-sorted permutation of the codes).
Outputs, fresh above the allocator: the kept chord list (`bDown 4`) of length `K'` (`bDown 5`)
and the renumbered event list (`bDown 6`); the kept family is the old family intersected with
`Full`, and the outputs are a valid sorted input of `BuildNFSortedSpec`.  Cost `κ (K + 1)`. -/
def DropAugSpec : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s {bDown}
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ rd c bDown 0 + 2 ≤ c.nreg ALLOC ∧
      (c.nmem (rd c bDown 0 + 1) = 1 ↔ Mountain.LeftInside (Qof P)) ∧
      ∃ L : List (ℕ × ℕ × ℕ), rd c bDown 2 = L.length ∧
        rd c bDown 1 + 3 * L.length ≤ c.nreg ALLOC ∧ ChordListAt c.nmem (rd c bDown 1) L ∧
        ChordTriplesOK (interiorModel (Qof P)) (Qof P) L ∧
        rd c bDown 3 + 2 * L.length ≤ c.nreg ALLOC ∧
        (seg c.nmem (rd c bDown 3) (2 * L.length)).Perm (List.range (2 * L.length)) ∧
        (seg c.nmem (rd c bDown 3) (2 * L.length)).Pairwise
          (codeLe (interiorModel (Qof P)) (Qof P) L))
    (fun P c c' => ∀ L : List (ℕ × ℕ × ℕ), rd c bDown 2 = L.length →
      ChordListAt c.nmem (rd c bDown 1) L →
        c.nreg ALLOC ≤ rd c' bDown 4 ∧
        rd c' bDown 4 + 3 * (DownBase.keepL (liBit c.nmem (rd c bDown 0)) (Qof P).n L).length ≤
          c'.nreg ALLOC ∧
        ChordListAt c'.nmem (rd c' bDown 4)
          (DownBase.keepL (liBit c.nmem (rd c bDown 0)) (Qof P).n L) ∧
        rd c' bDown 5 = (DownBase.keepL (liBit c.nmem (rd c bDown 0)) (Qof P).n L).length ∧
        c.nreg ALLOC ≤ rd c' bDown 6 ∧
        rd c' bDown 6 +
            2 * (DownBase.keepL (liBit c.nmem (rd c bDown 0)) (Qof P).n L).length ≤
          c'.nreg ALLOC ∧
        seg c'.nmem (rd c' bDown 6)
            (2 * (DownBase.keepL (liBit c.nmem (rd c bDown 0)) (Qof P).n L).length) =
          DownBase.dropE (liBit c.nmem (rd c bDown 0)) (Qof P).n L
            (seg c.nmem (rd c bDown 3) (2 * L.length)) ∧
        {x | ∃ y ∈ DownBase.keepL (liBit c.nmem (rd c bDown 0)) (Qof P).n L,
            x = (recOf y).toSet (interiorModel (Qof P)) (Qof P)} =
          {x | ∃ y ∈ L, x = (recOf y).toSet (interiorModel (Qof P)) (Qof P)} ∩
            (interiorModel (Qof P)).Full ∧
        ChordTriplesOK (interiorModel (Qof P)) (Qof P)
          (DownBase.keepL (liBit c.nmem (rd c bDown 0)) (Qof P).n L) ∧
        (DownBase.dropE (liBit c.nmem (rd c bDown 0)) (Qof P).n L
            (seg c.nmem (rd c bDown 3) (2 * L.length))).Perm
          (List.range (2 * (DownBase.keepL (liBit c.nmem (rd c bDown 0)) (Qof P).n L).length)) ∧
        (DownBase.dropE (liBit c.nmem (rd c bDown 0)) (Qof P).n L
            (seg c.nmem (rd c bDown 3) (2 * L.length))).Pairwise
          (codeLe (interiorModel (Qof P)) (Qof P)
            (DownBase.keepL (liBit c.nmem (rd c bDown 0)) (Qof P).n L)))
    (fun _ c => κ * (rd c bDown 2 + 1))

namespace DownBase

section exec

variable {P : Polygon} {W : ℕ}


/-- The setup block. -/
theorem dSetup_exec (c : Config) (hw : WordsBounded W c) {D B K A₀ : ℕ}
    (h0 : c.nreg 200000 = D) (h1 : c.nreg 200001 = B) (h2 : c.nreg 200002 = K)
    (hA : c.nreg 9999 = A₀) (hDW : D + 1 ≤ W) (hAW : A₀ + 7 * K + 2 ≤ W) (hnW : P.n ≤ W) :
    ∃ c' k, Exec P W dSetup c c' k ∧ k = 22 ∧
      c'.nreg 200100 = 1 ∧ c'.nreg 200101 = 0 ∧ c'.nreg 200105 = 2 ∧
      c'.nreg 200104 = P.n - 1 ∧ c'.nreg 200106 = c.nmem (D + 1) ∧ c'.nreg 200103 = 0 ∧
      c'.nreg 200136 = 2 * K ∧ c'.nreg 200004 = A₀ ∧ c'.nreg 200121 = A₀ + 3 * K ∧
      c'.nreg 200122 = A₀ + 5 * K ∧ c'.nreg 9999 = A₀ + 7 * K ∧
      c'.nreg 200006 = A₀ + 5 * K ∧ c'.nreg 200110 = 0 ∧ c'.nreg 200111 = B ∧
      c'.nreg 200117 = A₀ + 3 * K ∧ c'.nreg 200118 = 0 ∧ c'.nreg 200119 = A₀ ∧
      (∀ r, (r < 200000 ∨ 210000 ≤ r) → r ≠ 9999 → c'.nreg r = c.nreg r) ∧
      (∀ r, (200000 ≤ r ∧ r < 200004) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold dSetup
  exec_block
  all_goals try omega
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h0, h1, h2, hA]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun r hr hra => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h0, h1, h2, hA]
  all_goals omega

/-- The normalised bit. -/
theorem dBit_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) {b : ℕ}
    (h106 : c.nreg 200106 = b) (h105 : c.nreg 200105 = 2) (h101 : c.nreg 200101 = 0)
    (h103 : c.nreg 200103 = 0) :
    ∃ c' k, Exec P W dBit c c' k ∧ k ≤ 4 ∧
      c'.nreg 200103 = (if b = 1 then 1 else 0) ∧
      (∀ r, r ≠ 200103 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  by_cases hb1 : b < 2
  · have t1 : c.nreg 200106 < c.nreg 200105 := by rw [h106, h105]; exact hb1
    by_cases hb0 : 0 < b
    · have t2 : c.nreg 200101 < c.nreg 200106 := by rw [h101, h106]; exact hb0
      have e := Exec.constN (P := P) hw 200103 1 hW
      exact ⟨_, _, .ifLtN_true t1 (.ifLtN_true t2 e), by omega,
        by simp [show b = 1 by omega], fun r hr => by simp [hr], rfl, rfl, rfl, rfl⟩
    · have t2 : ¬ c.nreg 200101 < c.nreg 200106 := by rw [h101, h106]; exact hb0
      exact ⟨c, _, .ifLtN_true t1 (.ifLtN_false t2 (.skip hw)), by omega,
        by rw [h103]; simp [show b ≠ 1 by omega], fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  · have t1 : ¬ c.nreg 200106 < c.nreg 200105 := by rw [h106, h105]; exact hb1
    exact ⟨c, _, .ifLtN_false t1 (.skip hw), by omega,
      by rw [h103]; simp [show b ≠ 1 by omega], fun _ _ => rfl, rfl, rfl, rfl, rfl⟩


/-- Between the passes. -/
theorem dMid_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W dMid c c' k ∧ k = 4 ∧ c'.nreg 200005 = c.nreg 200118 ∧
      c'.nreg 200130 = 0 ∧ c'.nreg 200131 = c.nreg 200003 ∧ c'.nreg 200134 = c.nreg 200122 ∧
      (∀ r, r ≠ 200005 → r ≠ 200130 → r ≠ 200131 → r ≠ 200134 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold dMid
  exec_block
  all_goals try omega
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r a1 a2 a3 a4 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals simp (disch := omega) only [Machine.upd_same, Machine.upd_other]

end exec

end DownBase

end

end Chazelle.Core
