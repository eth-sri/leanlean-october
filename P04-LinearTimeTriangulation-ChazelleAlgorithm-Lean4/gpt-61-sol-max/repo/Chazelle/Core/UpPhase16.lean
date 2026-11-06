module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.UpPhase15

/-!
# WP-J up phase, part 16: the grade record of the next grade

* `recA`: the header `[g + 1, S, T', D]` of the new record `h'` at the allocator;
* `copyL`: the row table `T'[j] = T[j]` for `j < g`; `recB`: `T'[g] = R'` and the registers of
  the next grade (the chain count by the halving table);
* `gamS`: `γ'_{g+1}` from the setup tables (`clogS`, `mulS` of Lemma 4.1).
-/

namespace Chazelle.Core.Up

open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41

@[expose] public section

/-- The header of the new record. -/
def recA : Stmt := block [.copyN 170051 9999, .addN 170052 170007 170020, .storeN 170051 170052,
  .addN 170053 170005 170020, .loadN 170054 170053, .addN 170055 170051 170020,
  .storeN 170055 170054,
  .addN 170053 170005 170022, .loadN 170054 170053, .addN 170055 170051 170022,
  .storeN 170055 170054,
  .addN 170056 170051 170025, .addN 170055 170051 170021, .storeN 170055 170056,
  .addN 170053 170005 170021, .loadN 170057 170053,
  .constN 170050 0, .addN 9999 9999 170025]

/-- One word of the row table. -/
def copyBody : Stmt := block [.addN 170053 170057 170050, .loadN 170054 170053,
  .addN 170055 170056 170050, .storeN 170055 170054, .addN 170050 170050 170020,
  .addN 9999 9999 170020]

/-- The rows of the old grades. -/
def copyL : Stmt := .whileLtN 170050 170007 copyBody

/-- The new row, and the registers of the next grade. -/
def recB1 : Stmt := block [.addN 170055 170056 170007, .storeN 170055 170044,
  .addN 9999 9999 170020,
  .copyN 170005 170051, .copyN 170012 170008, .copyN 170014 170044, .copyN 170019 170010,
  .addN 170010 170010 170010,
  .addN 170053 170003 170009, .loadN 170009 170053,
  .copyN 170007 170052,
  .constN 170015 0, .constN 170016 0, .constN 170035 0, .constN 170036 1]

/-- The new row, and the registers of the next grade (with the chain count). -/
def recB : Stmt := .seq recB1 (block [.addN 170008 170009 170020])

/-- The registers of `gamS`. -/
def gamA : Stmt := block [.constN 160024 1, .constN 160080 2, .addN 160021 170000 170021,
  .copyN 160003 170007,
  .addN 170053 170000 170002, .addN 170053 170053 170025, .addN 170053 170053 170007,
  .loadN 170054 170053, .addN 170053 160021 170054, .loadN 160032 170053]

/-- `γ'_{g}` for the grade `g` in `170007`, in `170011`. -/
def gamS : Stmt := .seq gamA (.seq clogS (.seq mulS (block [.copyN 170011 160032])))

/-- The registers written by `recA` (besides the allocator). -/
def RecRG (r : ℕ) : Prop := 170050 ≤ r ∧ r ≤ 170057

/-- The registers written by `copyL` (besides the allocator). -/
def CopyRG (r : ℕ) : Prop := r = 170050 ∨ r = 170053 ∨ r = 170054 ∨ r = 170055

section proofs

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 64000000 in
theorem recA_exec {c : Config} (hw : WordsBounded W c) {A h g : ℕ}
    (hA : c.nreg ALLOC = A) (h05 : c.nreg 170005 = h) (h07 : c.nreg 170007 = g)
    (h20 : c.nreg 170020 = 1) (h21 : c.nreg 170021 = 2) (h22 : c.nreg 170022 = 3)
    (h25 : c.nreg 170025 = 4) (hh : h + 4 ≤ A) (hWA : A + 4 ≤ W) (hWg : g + 1 ≤ W) :
    ∃ c' k, Exec P W recA c c' k ∧ k = 18 ∧ WordsBounded W c' ∧
      c'.nreg ALLOC = A + 4 ∧ c'.nreg 170051 = A ∧ c'.nreg 170052 = g + 1 ∧
      c'.nreg 170056 = A + 4 ∧ c'.nreg 170057 = c.nmem (h + 2) ∧ c'.nreg 170050 = 0 ∧
      c'.nmem A = g + 1 ∧ c'.nmem (A + 1) = c.nmem (h + 1) ∧ c'.nmem (A + 2) = A + 4 ∧
      c'.nmem (A + 3) = c.nmem (h + 3) ∧
      (∀ a, (a < A ∨ A + 4 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ RecRG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  rw [hAl] at hA ⊢
  unfold recA
  exec_block
  all_goals try (config_simp; omega)
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a h1 => ?_, fun r h1 h2 => ?_,
    rfl, rfl, rfl⟩
  · ram_simp <;> omega_nf
  · ram_simp <;> omega_nf
  · ram_simp <;> omega_nf
  · ram_simp <;> omega_nf
  · grind [Machine.upd_apply]
  · config_simp
  · grind [Machine.upd_apply]
  · grind [Machine.upd_apply]
  · ram_simp <;> omega_nf
  · grind [Machine.upd_apply]
  · config_simp; simp only [hA, h05, h07, h20, h21, h22, h25, Machine.upd_apply]
    grind
  · unfold RecRG at h1
    simp only
    repeat ram_simp 

set_option maxHeartbeats 16000000 in
theorem copyBody_exec {c : Config} (hw : WordsBounded W c) {j T T' Al : ℕ}
    (h50 : c.nreg 170050 = j) (h57 : c.nreg 170057 = T) (h56 : c.nreg 170056 = T')
    (hA : c.nreg ALLOC = Al) (h20 : c.nreg 170020 = 1) (hWT : T + j ≤ W) (hWT' : T' + j ≤ W)
    (hWA : Al + 1 ≤ W) (hWj : j + 1 ≤ W) :
    ∃ c' k, Exec P W copyBody c c' k ∧ k = 6 ∧ WordsBounded W c' ∧
      c'.nreg 170050 = j + 1 ∧ c'.nreg ALLOC = Al + 1 ∧ c'.nmem (T' + j) = c.nmem (T + j) ∧
      (∀ a, a ≠ T' + j → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ CopyRG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  rw [hAl] at hA ⊢
  unfold copyBody
  exec_block
  all_goals simp_all
  simp_all [Machine.upd_apply, CopyRG] 

set_option maxHeartbeats 16000000 in
/-- **The rows of the old grades**: `T'[j] = T[j]` for `j < g`. -/
theorem copyL_exec {c : Config} (hw : WordsBounded W c) {g T T' Al : ℕ}
    (h50 : c.nreg 170050 = 0) (h07 : c.nreg 170007 = g) (h57 : c.nreg 170057 = T)
    (h56 : c.nreg 170056 = T') (hA : c.nreg ALLOC = Al) (h20 : c.nreg 170020 = 1)
    (hTT : T + g ≤ T') (hWA : Al + g + 1 ≤ W) (hWT' : T' + g ≤ W) (hWg : g + 1 ≤ W) :
    ∃ c' k, Exec P W copyL c c' k ∧ k ≤ 8 * g + 2 ∧ WordsBounded W c' ∧
      c'.nreg ALLOC = Al + g ∧ c'.nreg ALLOC ≤ Al + k ∧
      (∀ j, j < g → c'.nmem (T' + j) = c.nmem (T + j)) ∧
      (∀ a, (a < T' ∨ T' + g ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ CopyRG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  let I : Config → Prop := fun c' => ∃ j, j ≤ g ∧ WordsBounded W c' ∧ c'.nreg 170050 = j ∧
    c'.nreg ALLOC = Al + j ∧
    (∀ j', j' < j → c'.nmem (T' + j') = c.nmem (T + j')) ∧
    (∀ a, (a < T' ∨ T' + j ≤ a) → c'.nmem a = c.nmem a) ∧
    (∀ r, ¬ CopyRG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  have hI0 : I c := ⟨0, by omega, hw, h50, by omega, fun _ h => absurd h (by omega),
    fun _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, rfl⟩
  obtain ⟨c', k, e, ⟨j, hj, hw', j50, jA, hcp, hmem, fr, hrr, hrm, ho⟩, htest, hk, hψ⟩ :=
    whileLtN_potential_lb' (P := P) (W := W) (a := 170050) (b := 170007) (body := copyBody) I
      (fun c' => 8 * (g - c'.nreg 170050)) (fun c' => c'.nreg ALLOC) (fun c' ⟨_, _, h, _⟩ => h)
      (fun c2 ⟨j, hj, hw2, j50, jA, hcp, hmem, fr, hrr, hrm, ho⟩ htest => by
        have k07 : c2.nreg 170007 = g := by
          ram_grind
        rw [j50, k07] at htest
        obtain ⟨c3, k3, e3, hk3, hw3, l50, lA, lw, lm, fr3, hrr3, hrm3, ho3⟩ :=
          copyBody_exec (P := P) (T := T) (T' := T') hw2 j50
            (by ram_grind)
            (by ram_grind) jA
            (by ram_grind)
            (by omega) (by omega) (by omega) (by omega)
        refine ⟨c3, k3, e3, ⟨j + 1, by omega, hw3, l50, by omega, fun j' h' => ?_,
          fun a ha => by ram_grind,
          fun r h1 h2 => by ram_grind, by ram_grind, by ram_grind,
          by rw [ho3, ho]⟩, by omega, by omega⟩
        grind) hI0
  have hjg : j = g := by
    grind [CopyRG]
  subst hjg
  exact ⟨c', k, e, by omega, hw', jA, by omega, hcp, hmem, fr,
    hrr, hrm, ho⟩

end proofs

end

end Chazelle.Core.Up
