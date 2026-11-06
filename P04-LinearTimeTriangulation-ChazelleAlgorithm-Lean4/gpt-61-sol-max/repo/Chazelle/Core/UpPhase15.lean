module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.UpPhase14

/-!
# WP-J up phase, part 15: the row of a grade

`rowS`: the row of grade `g` (three words per chain) at the allocator `R'`, rebuilt from the
cells by the back links, last chain first (`rowS_exec`).
-/

namespace Chazelle.Core.Up

open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41

@[expose] public section

/-- One entry of the row (the entry of the chain of cell `x`, just below the pointer `p`). -/
def rowBody : Stmt := block [.subN 170041 170041 170022,
  .loadN 170043 170042, .storeN 170041 170043,
  .addN 170046 170042 170020, .loadN 170043 170046, .addN 170047 170041 170020,
  .storeN 170047 170043,
  .addN 170046 170042 170021, .loadN 170043 170046, .addN 170047 170041 170021,
  .storeN 170047 170043,
  .addN 170046 170042 170022, .loadN 170042 170046,
  .addN 9999 9999 170022, .subN 170040 170040 170020]

/-- **The row of the current grade.** -/
def rowS : Stmt := .seq (block [.copyN 170044 9999, .copyN 170040 170008, .copyN 170042 170018,
    .addN 170045 170008 170008, .addN 170045 170045 170008, .addN 170041 170044 170045])
  (.whileLtN 170029 170040 rowBody)

/-- The registers written by `rowS` (besides the allocator). -/
def RowRG (r : ℕ) : Prop := 170040 ≤ r ∧ r ≤ 170047

/-- The registers written by `rowBody` (besides the allocator). -/
def RowBRG (r : ℕ) : Prop :=
  r = 170040 ∨ r = 170041 ∨ r = 170042 ∨ r = 170043 ∨ r = 170046 ∨ r = 170047

section proofs

variable {O : OracleIface} {P : Polygon} {W : ℕ}

set_option maxHeartbeats 16000000 in
theorem rowBody_exec {c : Config} (hw : WordsBounded W c) {j p x Al : ℕ}
    (h40 : c.nreg 170040 = j) (h41 : c.nreg 170041 = p) (h42 : c.nreg 170042 = x)
    (hA : c.nreg ALLOC = Al) (h20 : c.nreg 170020 = 1) (h21 : c.nreg 170021 = 2)
    (h22 : c.nreg 170022 = 3) (hp3 : 3 ≤ p) (hx : x + 4 ≤ p - 3) (hWp : p ≤ W)
    (hWA : Al + 3 ≤ W) (_hj : 1 ≤ j) :
    ∃ c' k, Exec P W rowBody c c' k ∧ k = 15 ∧ WordsBounded W c' ∧
      c'.nreg 170040 = j - 1 ∧ c'.nreg 170041 = p - 3 ∧ c'.nreg 170042 = c.nmem (x + 3) ∧
      c'.nreg ALLOC = Al + 3 ∧
      c'.nmem (p - 3) = c.nmem x ∧ c'.nmem (p - 3 + 1) = c.nmem (x + 1) ∧
      c'.nmem (p - 3 + 2) = c.nmem (x + 2) ∧
      (∀ a, (a < p - 3 ∨ p ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ RowBRG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  rw [hAl] at hA ⊢
  unfold rowBody
  exec_block
  all_goals try (config_simp; omega)
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a h1 => ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [h40, h20]
  · config_simp; simp only [h41, h22]
  · config_simp; simp only [h42, h22, h41, h20, h21, Machine.upd_apply]
    split_ifs <;> first | omega
  · config_simp; simp only [hA, h22]
  · config_simp; simp only [h42, h22, h41, h20, h21, Machine.upd_apply]
    split_ifs <;> first | omega
  · config_simp; simp only [h42, h22, h41, h20, h21, Machine.upd_apply]
    split_ifs <;> first | omega
  · config_simp; simp only [h42, h22, h41, h20, h21, Machine.upd_apply]
    split_ifs <;> first | omega
  · config_simp; simp only [h42, h22, h41, h20, h21, Machine.upd_apply]
    split_ifs <;> first | omega
  · unfold RowBRG at h1
    simp only
    repeat (rw [Machine.upd_other _ _ _ (by omega)])

set_option maxHeartbeats 32000000 in
/-- **The row of grade `g`**: entry `i` at `R' + 3 i` holds the entry of cell `i`. -/
theorem rowS_exec {c : Config} (hw : WordsBounded W c) {hp g x cnt R' : ℕ}
    (hA : c.nreg ALLOC = R') (h08 : c.nreg 170008 = cnt) (h18 : c.nreg 170018 = x)
    (h20 : c.nreg 170020 = 1) (h21 : c.nreg 170021 = 2) (h22 : c.nreg 170022 = 3)
    (h29 : c.nreg 170029 = 0)
    (hC : Robust R' c.nmem fun m => Cells O P m R' hp g x cnt)
    (hW : R' + 3 * cnt + 3 ≤ W) :
    ∃ c' k, Exec P W rowS c c' k ∧ k ≤ 17 * cnt + 8 ∧ WordsBounded W c' ∧
      c'.nreg ALLOC = R' + 3 * cnt ∧ c'.nreg ALLOC ≤ R' + k ∧ c'.nreg 170044 = R' ∧
      (∀ i, i < cnt → Robust R' c.nmem fun m => UpEntry O P m R' hp g i
        (c'.nmem (R' + 3 * i)) (c'.nmem (R' + 3 * i + 1)) (c'.nmem (R' + 3 * i + 2))) ∧
      (∀ a, (a < R' ∨ R' + 3 * cnt ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ RowRG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  obtain ⟨c1, k1, e1, hk1, hw1, i40, i41, i42, i44, fr1, hm1, hrr1, hrm1, ho1⟩ : ∃ c1 k1,
      Exec P W (block [.copyN 170044 9999, .copyN 170040 170008, .copyN 170042 170018,
        .addN 170045 170008 170008, .addN 170045 170045 170008, .addN 170041 170044 170045])
        c c1 k1 ∧ k1 = 6 ∧ WordsBounded W c1 ∧ c1.nreg 170040 = cnt ∧
      c1.nreg 170041 = R' + 3 * cnt ∧ c1.nreg 170042 = x ∧ c1.nreg 170044 = R' ∧
      (∀ r, ¬ RowRG r → c1.nreg r = c.nreg r) ∧ c1.nmem = c.nmem ∧ c1.rreg = c.rreg ∧
      c1.rmem = c.rmem ∧ c1.output = c.output := by
    rw [hAl] at hA
    exec_block
    all_goals try (config_simp; (try simp only [hA, h08]); omega)
    refine ⟨rfl, ‹_›, by simp_all, by simp_all +arith,
      by simp_all, by simp_all, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    unfold RowRG at hr
    simp only
    repeat ram_simp 
  
  have c1A : c1.nreg ALLOC = R' := by ram_grind
  have c20 : ∀ c' : Config, (∀ r, ¬ RowRG r → r ≠ ALLOC → c'.nreg r = c1.nreg r) →
      c'.nreg 170020 = 1 ∧ c'.nreg 170021 = 2 ∧ c'.nreg 170022 = 3 ∧ c'.nreg 170029 = 0 :=
    fun c' h => by
      ram_grind
  let I : Config → Prop := fun c' => ∃ j, j ≤ cnt ∧ WordsBounded W c' ∧
    c'.nreg 170040 = j ∧ c'.nreg 170041 = R' + 3 * j ∧ c'.nreg ALLOC = R' + 3 * (cnt - j) ∧
    c'.nreg 170044 = R' ∧
    (Robust R' c.nmem fun m => Cells O P m R' hp g (c'.nreg 170042) j) ∧
    (∀ i, j ≤ i → i < cnt → Robust R' c.nmem fun m => UpEntry O P m R' hp g i
        (c'.nmem (R' + 3 * i)) (c'.nmem (R' + 3 * i + 1)) (c'.nmem (R' + 3 * i + 2))) ∧
    (∀ a, (a < R' + 3 * j ∨ R' + 3 * cnt ≤ a) → c'.nmem a = c.nmem a) ∧
    (∀ r, ¬ RowRG r → r ≠ ALLOC → c'.nreg r = c1.nreg r) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  have hI1 : I c1 := ⟨cnt, le_rfl, hw1, i40, i41, by omega, i44,
    by ram_grind, fun i h1 h2 => absurd h2 (by omega), fun a _ => by rw [hm1],
    fun _ _ _ => rfl, hrr1, hrm1, ho1⟩
  obtain ⟨c', k, e, ⟨j, hj, hw', j40, j41, jA, j44, hCj, hE, hmem, fr, hrr, hrm, ho⟩, htest, hk,
      hψ⟩ :=
    whileLtN_potential_lb' (P := P) (W := W) (a := 170029) (b := 170040) (body := rowBody) I
      (fun c' => 17 * c'.nreg 170040) (fun c' => c'.nreg ALLOC) (fun c' ⟨_, _, h, _⟩ => h)
      (fun c2 ⟨j, hj, hw2, j40, j41, jA, j44, hCj, hE, hmem, fr, hrr, hrm, ho⟩ htest => by
        obtain ⟨k20, k21, k22, k29⟩ := c20 c2 fr
        rw [k29, j40] at htest
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        -- the cell of chain `j'`
        have hx4 : c2.nreg 170042 + 4 ≤ R' := (hCj.holds).1
        obtain ⟨c3, k3, e3, hk3, hw3, l40, l41, l42, lA, w0, w1, w2, mw, fr3, hrr3, hrm3, ho3⟩ :=
          rowBody_exec (P := P) hw2 j40 j41 rfl rfl k20 k21 k22 (by omega) (by omega)
            (by omega) (by rw [jA]; omega) (by omega)
        have e3' : R' + 3 * (j' + 1) - 3 = R' + 3 * j' := by omega
        rw [e3'] at l41 w0 w1 w2 mw
        -- the values read are below `R'`
        have r0 : c2.nmem (c2.nreg 170042) = c.nmem (c2.nreg 170042) := hmem _ (Or.inl (by omega))
        have r1 : c2.nmem (c2.nreg 170042 + 1) = c.nmem (c2.nreg 170042 + 1) :=
          hmem _ (Or.inl (by omega))
        have r2 : c2.nmem (c2.nreg 170042 + 2) = c.nmem (c2.nreg 170042 + 2) :=
          hmem _ (Or.inl (by omega))
        have r3 : c2.nmem (c2.nreg 170042 + 3) = c.nmem (c2.nreg 170042 + 3) :=
          hmem _ (Or.inl (by omega))
        refine ⟨c3, k3, e3, ⟨j', by omega, hw3, l40, l41, by rw [lA, jA]; omega,
          by rw [fr3 170044 (by unfold RowBRG; omega) (by rw [hAl]; omega)]; exact j44, ?_, ?_,
          fun a ha => by rw [mw a (by omega), hmem a (by omega)],
          fun r h1 h2 => by
            rw [fr3 r (fun h => h1 (by unfold RowBRG at h; unfold RowRG; omega)) h2, fr r h1 h2],
          by rw [hrr3, hrr], by rw [hrm3, hrm],
          by rw [ho3, ho]⟩, by rw [l40, j40]; omega, by rw [lA, jA]; omega⟩
        · rw [l42, r3]
          intro m hm
          have := (hCj m hm).2.2
          rwa [hm (c2.nreg 170042 + 3) (by omega)] at this
        · intro i h1 h2
          rcases Nat.lt_or_ge i (j' + 1) with h3 | h3
          · have hi : i = j' := by omega
            subst hi
            rw [w0, w1, w2, r0, r1, r2]
            intro m hm
            have := (hCj m hm).2.1
            rwa [hm (c2.nreg 170042) (by omega), hm (c2.nreg 170042 + 1) (by omega),
              hm (c2.nreg 170042 + 2) (by omega)] at this
          · have := hE i h3 h2
            rw [mw (R' + 3 * i) (Or.inr (by omega)), mw (R' + 3 * i + 1) (Or.inr (by omega)),
              mw (R' + 3 * i + 2) (Or.inr (by omega))]
            exact this)
      hI1
  have hj0 : j = 0 := by
    grind
  subst hj0
  refine ⟨c', k1 + k, .seq e1 e, by omega, hw', by omega, by
    ram_grind, j44, fun i h => hE i (by omega) h, fun a ha => hmem a (by omega),
    fun r h1 h2 => by ram_grind, by rw [hrr], by rw [hrm], by rw [ho]⟩

end proofs

end

end Chazelle.Core.Up
