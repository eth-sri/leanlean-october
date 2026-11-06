module

public import Chazelle.Core.DownPhaseDrvPBit
public import Chazelle.RewriteTactics

/-!
# Down-phase pieces (D4), part 5: the model descriptor

`descS` writes the model descriptor of the chain model of the piece at the allocator `A`:
`[0, HB, s, m, T, β]` (`m A = 0`, a chain descriptor at `A + 1`: host handle, start, number of
edges, top index, orientation bit), puts `A` into `218010` and raises the allocator to `A + 6`
(`descS_exec`).
-/


namespace Chazelle.Core

namespace DrvP

open Machine Machine.Stmt Programs

@[expose] public section

/-- **The model descriptor** at the allocator. -/
def descS : Stmt := block [.copyN 218010 ALLOC, .storeN 218010 218020, .addN 218060 218010 218021,
  .storeN 218060 218000, .addN 218060 218060 218021, .storeN 218060 218001,
  .addN 218060 218060 218021, .storeN 218060 218002, .addN 218060 218060 218021,
  .storeN 218060 218013, .addN 218060 218060 218021, .storeN 218060 218014,
  .addN ALLOC 218060 218021]

section exec

variable {P : Polygon} {W : ℕ}

/-- **The descriptor write.** -/
theorem descS_exec (c : Config) (hw : WordsBounded W c) (h20 : c.nreg 218020 = 0)
    (h21 : c.nreg 218021 = 1) (hA : c.nreg ALLOC + 6 ≤ W) :
    ∃ c' k, Exec P W descS c c' k ∧ k = 13 ∧ c'.nreg 218010 = c.nreg ALLOC ∧
      c'.nreg ALLOC = c.nreg ALLOC + 6 ∧
      (∀ r, r ≠ 218010 → r ≠ 218060 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      c'.nmem (c.nreg ALLOC) = 0 ∧ c'.nmem (c.nreg ALLOC + 1) = c.nreg 218000 ∧
      c'.nmem (c.nreg ALLOC + 2) = c.nreg 218001 ∧ c'.nmem (c.nreg ALLOC + 3) = c.nreg 218002 ∧
      c'.nmem (c.nreg ALLOC + 4) = c.nreg 218013 ∧ c'.nmem (c.nreg ALLOC + 5) = c.nreg 218014 := by
  obtain ⟨A, hA'⟩ : ∃ A, c.nreg ALLOC = A := ⟨_, rfl⟩
  rw [hA'] at hA ⊢
  have e : ALLOC = 9999 := rfl
  rw [e] at hA'
  unfold descS
  rw [e]
  exec_block
  all_goals first | (config_simp; rwo [hA', h21]) | skip
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, fun a ha => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [e] at *
  all_goals config_simp
  all_goals simp [hA', h20, h21]
  all_goals (simp [upd]; split_ifs <;> first | rfl | omega)

end exec

end

end DrvP

end Chazelle.Core
