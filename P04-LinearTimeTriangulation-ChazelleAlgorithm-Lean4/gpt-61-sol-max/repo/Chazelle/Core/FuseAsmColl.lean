module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.FuseAsmList

/-!
# WP-F fusion assembly, part 4: collecting the answers of the sweep

`clLoop` scans a result list (four words per result: flag, `h`, `lp`, `rp`) and appends the
triple of every result with flag `1` at the allocator (`collect`).  Registers (band `bFuse`):

| register | content |
|---|---|
| `70111` | number of results |
| `70112` | loop index |
| `70113` | cursor in the result list |
| `70114`, `70119` | scratch |
| `70105`, `70108`, `70117`, `70118` | constants `1`, `0`, `4`, `2` |
-/

namespace Chazelle.Core

namespace FuseAsm

open Machine Machine.Stmt Programs SignK

@[expose] public section

theorem chordListAt_append {m : ℕ → ℕ} {A : ℕ} {L : List (ℕ × ℕ × ℕ)} (h : ChordListAt m A L)
    {x : ℕ × ℕ × ℕ} (h0 : m (A + 3 * L.length) = x.1) (h1 : m (A + 3 * L.length + 1) = x.2.1)
    (h2 : m (A + 3 * L.length + 2) = x.2.2) : ChordListAt m A (L ++ [x]) := by
  intro i hi
  rw [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_or_ge i L.length with hlt | hge
  · ram_grind
  ram_grind


end

end FuseAsm

end Chazelle.Core
