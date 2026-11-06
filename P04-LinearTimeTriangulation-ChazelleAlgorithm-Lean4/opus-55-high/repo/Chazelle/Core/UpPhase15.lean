module

public import Chazelle.MacT
public import Chazelle.Core.Lemma41Exec
public import Chazelle.Core.Lemma41Cover
public import Chazelle.Core.DownPhaseDrvRPlB
public import Chazelle.Core.Lemma41Node
public import Chazelle.Core.NFBuildRegFill

namespace Chazelle.Core.Up
open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41
@[expose] public section
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
      c'.nreg 170040 = j - 1 ∧ c'.nreg 170041 = p - 3 ∧ c'.nreg 170042 = c.nmem ztudm ∧
      c'.nreg ALLOC = Al + 3 ∧
      c'.nmem (p - 3) = c.nmem x ∧ c'.nmem (p - 3 + 1) = c.nmem zthf ∧
      c'.nmem (p - 3 + 2) = c.nmem ztewm ∧
      (∀ a, (a < p - 3 ∨ p ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ RowBRG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuk
  zudh
  unfold rowBody
  exec_block
  all_goals try (config_simp; (try simp only [h40, h41, h42, hA, h20, h21, h22,
    Machine.upd_apply]); (try split_ifs) <;> omega)
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a h1 => ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  · config_simp; omega
  · config_simp; omega
  · config_simp; simp only [h42, h22, h41, h20, h21, Machine.upd_apply]
    grind
  · config_simp; omega
  · config_simp; simp only [h42, h22, h41, h20, h21, Machine.upd_apply]
    simp
  · config_simp; simp only [h42, h22, h41, h20, h21, Machine.upd_apply]
    grind
  · config_simp; simp only [h42, h22, h41, h20, h21, Machine.upd_apply]
    grind
  · config_simp; simp only [h42, h22, h41, h20, h21, Machine.upd_apply]
    grind
  · unfold RowBRG at h1
    zubi
    repeat (rw [Machine.upd_other _ _ _ by_omega])
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
        ztbafv ztbaft ztbafu) ∧
      (∀ a, (a < R' ∨ R' + 3 * cnt ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ RowRG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuk
  obtain ⟨c1, k1, e1, hk1, hw1, i40, i41, i42, i44, fr1, hm1, hrr1, hrm1, ho1⟩ : ∃ c1 k1,
      Exec P W (block [.copyN 170044 9999, .copyN 170040 170008, .copyN 170042 170018,
        .addN 170045 170008 170008, .addN 170045 170045 170008, .addN 170041 170044 170045])
        c c1 k1 ∧ k1 = 6 ∧ WordsBounded W c1 ∧ c1.nreg 170040 = cnt ∧
      c1.nreg 170041 = R' + 3 * cnt ∧ c1.nreg 170042 = x ∧ c1.nreg 170044 = R' ∧
      (∀ r, ¬ RowRG r → c1.nreg r = c.nreg r) ∧ c1.nmem = c.nmem ∧ c1.rreg = c.rreg ∧
      c1.rmem = c.rmem ∧ c1.output = c.output := by
    zuksg
    exec_block
    all_goals try (config_simp; (try simp only [hA, h08]); omega)
    refine ⟨rfl, ‹_›, by_simp_all, by config_simp; omega,
      by simp_all, by_simp_all, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    unfold RowRG at hr
    zubi
    repeat (rw [Machine.upd_other _ _ _ by_omega])
  have g1 : ∀ r, ¬ RowRG r → c1.nreg r = c.nreg r := fr1
  have c1A : c1.nreg ALLOC = R' := by rw [g1 _ ztjrb]; exact hA
  have c20 : ∀ c' : Config, ztgst →
      c'.nreg 170020 = 1 ∧ c'.nreg 170021 = 2 ∧ c'.nreg 170022 = 3 ∧ c'.nreg 170029 = 0 :=
    fun c' h => by
      refine ztfh <;>
        rw [h _ ztjrb by_omega, g1 _ ztjrb] <;>
        assumption
  let I : Config → Prop := fun c' => ∃ j, j ≤ cnt ∧ WordsBounded W c' ∧
    c'.nreg 170040 = j ∧ c'.nreg 170041 = R' + 3 * j ∧ c'.nreg ALLOC = R' + 3 * (cnt - j) ∧
    c'.nreg 170044 = R' ∧
    (Robust R' c.nmem fun m => Cells O P m R' hp g (c'.nreg 170042) j) ∧
    (∀ i, j ≤ i → i < cnt → Robust R' c.nmem fun m => UpEntry O P m R' hp g i
        ztbafv ztbaft ztbafu) ∧
    (∀ a, (a < R' + 3 * j ∨ R' + 3 * cnt ≤ a) → c'.nmem a = c.nmem a) ∧
    ztgst ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  have hI1 : I c1 := ⟨cnt, le_rfl, hw1, i40, i41, by_omega, i44,
    by grind, fun i h1 h2 => absurd h2 by_omega, fun a _ => by zvmxz,
    fun _ _ _ => rfl, hrr1, hrm1, ho1⟩
  obtain ⟨c', k, e, ⟨j, hj, hw', j40, j41, jA, j44, hCj, hE, hmem, fr, hrr, hrm, ho⟩, htest, hk,
      hψ⟩ :=
    whileLtN_potential_lb' (P := P) (W := W) (a := 170029) (b := 170040) (body := rowBody) I
      (fun c' => 17 * c'.nreg 170040) ztcht ztdum
      (fun c2 ⟨j, hj, hw2, j40, j41, jA, j44, hCj, hE, hmem, fr, hrr, hrm, ho⟩ htest => by
        obtain ⟨k20, k21, k22, k29⟩ := c20 c2 fr
        rw [k29, j40] at htest
        zugqe
        -- the cell of chain `j'`
        have hx4 : c2.nreg 170042 + 4 ≤ R' := (hCj.holds).1
        obtain ⟨c3, k3, e3, hk3, hw3, l40, l41, l42, lA, w0, w1, w2, mw, fr3, hrr3, hrm3, ho3⟩ :=
          rowBody_exec (P := P) hw2 j40 j41 rfl rfl k20 k21 k22 by_omega by_omega
            by_omega by_grind by_omega
        have e3' : R' + 3 * ztdhr - 3 = R' + 3 * j' := by_omega
        rw [e3'] at l41 w0 w1 w2 mw
        -- the values read are below `R'`
        have r0 : c2.nmem ztvkk = c.nmem ztvkk := hmem _ ztec
        have r1 : c2.nmem ztrmr = c.nmem ztrmr :=
          hmem _ ztec
        have r2 : c2.nmem ztrms = c.nmem ztrms :=
          hmem _ ztec
        have r3 : c2.nmem ztrmt = c.nmem ztrmt :=
          hmem _ ztec
        refine ⟨c3, k3, e3, ⟨j', by_omega, hw3, l40, l41, by_grind,
          by rw [fr3 170044 (by unfold RowBRG; omega) by_omega]; omega, ?_, ?_,
          fun a ha => by rw [mw a by_omega, hmem a by_omega],
          fun r h1 h2 => by
            rw [fr3 r (fun h => h1 (by unfold RowBRG at h; unfold RowRG; omega)) h2, fr r h1 h2],
          by grind, by_grind,
          by grind⟩, by_grind, by_grind⟩
        · rw [l42, r3]
          zucng
          have := (hCj m hm).2.2
          grind
        · zusx
          rcases Nat.lt_or_ge i ztdhr with h3 | h3
          · have hi : i = j' := by_omega
            zuipx
            rw [w0, w1, w2, r0, r1, r2]
            zucng
            have := (hCj m hm).2.1
            grind
          · have := hE i h3 h2
            rw [mw ztjma ztbh, mw zthcg ztbh,
              mw zthch ztbh]
            omega)
      hI1
  have hj0 : ztebi := by
    grind
  subst hj0
  refine ⟨c', k1 + k, .seq e1 e, by_omega, hw', by_omega, by
    omega, j44, fun i h => hE i by_omega h, fun a ha => hmem a by_omega,
    fun r h1 h2 => by_grind, by zvnhk, by zvnmc, by rw [ho]⟩
end proofs
end
end Chazelle.Core.Up
namespace Chazelle.Core.Up
open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41
@[expose] public section
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
def recB : Stmt := .seq recB1 ztnsa

/-- The registers of `gamS`. -/
def gamA : Stmt := block [.constN 160024 1, .constN 160080 2, .addN 160021 170000 170021,
  .copyN 160003 170007,
  .addN 170053 170000 170002, .addN 170053 170053 170025, .addN 170053 170053 170007,
  .loadN 170054 170053, .addN 170053 160021 170054, .loadN 160032 170053]

/-- `γ'_{g}` for the grade `g` in `170007`, in `170011`. -/
def gamS : Stmt := .seq gamA (.seq clogS (.seq mulS ztoyn))

/-- The registers written by `recA` (besides the allocator). -/
def RecRG (r : ℕ) : Prop := 170050 ≤ r ∧ r ≤ 170057

/-- The registers written by `copyL` (besides the allocator). -/
def CopyRG (r : ℕ) : Prop := r = 170050 ∨ r = 170053 ∨ r = 170054 ∨ r = 170055
section proofs
variable {P : Polygon} {W : ℕ}
variable {c : Config}
set_option maxHeartbeats 64000000 in
theorem recA_exec (hw : WordsBounded W c) {A h g : ℕ}
    (hA : c.nreg ALLOC = A) (h05 : c.nreg 170005 = h) (h07 : c.nreg 170007 = g)
    (h20 : c.nreg 170020 = 1) (h21 : c.nreg 170021 = 2) (h22 : c.nreg 170022 = 3)
    (h25 : c.nreg 170025 = 4) (hh : h + 4 ≤ A) (hWA : A + 4 ≤ W) (hWg : g + 1 ≤ W) :
    ∃ c' k, Exec P W recA c c' k ∧ k = 18 ∧ WordsBounded W c' ∧
      c'.nreg ALLOC = A + 4 ∧ c'.nreg 170051 = A ∧ c'.nreg 170052 = g + 1 ∧
      c'.nreg 170056 = A + 4 ∧ c'.nreg 170057 = c.nmem zteu ∧ c'.nreg 170050 = 0 ∧
      c'.nmem A = g + 1 ∧ c'.nmem ztbo = c.nmem ztgn ∧ c'.nmem ztbcl = A + 4 ∧
      c'.nmem zttf = c.nmem ztbba ∧
      ztzt ∧
      (∀ r, ¬ RecRG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuk
  zudh
  unfold recA
  exec_block
  all_goals try (config_simp; (try simp only [hA, h05, h07, h20, h21, h22, h25]); omega)
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a h1 => ?_, fun r h1 h2 => ?_,
    rfl, rfl, rfl⟩
  · config_simp; omega
  · tauto
  · config_simp; omega
  · config_simp; omega
  · config_simp; simp only [h05, h21, hA, h20, h22, Machine.upd_apply]
    grind
  · config_simp
  · config_simp; simp only [hA, h05, h07, h20, h21, h22, h25, Machine.upd_apply]
    simp
  · config_simp; simp only [hA, h05, h07, h20, h21, h22, h25, Machine.upd_apply]
    grind
  · config_simp; simp only [hA, h05, h07, h20, h21, h22, h25, Machine.upd_apply]
    simp
  · config_simp; simp only [hA, h05, h07, h20, h21, h22, h25, Machine.upd_apply]
    grind
  · config_simp; simp only [hA, h05, h07, h20, h21, h22, h25, Machine.upd_apply]
    grind
  · unfold RecRG at h1
    zubi
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
set_option maxHeartbeats 16000000 in
theorem copyBody_exec (hw : WordsBounded W c) {j T T' Al : ℕ}
    (h50 : c.nreg 170050 = j) (h57 : c.nreg 170057 = T) (h56 : c.nreg 170056 = T')
    (hA : c.nreg ALLOC = Al) (h20 : c.nreg 170020 = 1) (hWT : T + j ≤ W) (hWT' : T' + j ≤ W)
    (hWA : Al + 1 ≤ W) (hWj : j + 1 ≤ W) :
    ∃ c' k, Exec P W copyBody c c' k ∧ k = 6 ∧ WordsBounded W c' ∧
      c'.nreg 170050 = j + 1 ∧ c'.nreg ALLOC = Al + 1 ∧ c'.nmem zttdl = c.nmem ztnps ∧
      (∀ a, a ≠ T' + j → c'.nmem a = c.nmem a) ∧
      ztdbe ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuk
  zudh
  unfold copyBody
  exec_block
  all_goals try (config_simp; (try simp only [hA, h50, h56, h57, h20]); omega)
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, fun a h1 => ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · unfold CopyRG at h1
    simp_all
set_option maxHeartbeats 16000000 in
/-- **The rows of the old grades**: `T'[j] = T[j]` for `j < g`. -/
theorem copyL_exec (hw : WordsBounded W c) {g T T' Al : ℕ}
    (h50 : c.nreg 170050 = 0) (h07 : c.nreg 170007 = g) (h57 : c.nreg 170057 = T)
    (h56 : c.nreg 170056 = T') (hA : c.nreg ALLOC = Al) (h20 : c.nreg 170020 = 1)
    (hTT : T + g ≤ T') (hWA : Al + g + 1 ≤ W) (hWT' : T' + g ≤ W) (hWg : g + 1 ≤ W) :
    ∃ c' k, Exec P W copyL c c' k ∧ k ≤ 8 * g + 2 ∧ WordsBounded W c' ∧
      c'.nreg ALLOC = Al + g ∧ c'.nreg ALLOC ≤ Al + k ∧
      (∀ j, j < g → c'.nmem zttdl = c.nmem ztnps) ∧
      (∀ a, (a < T' ∨ T' + g ≤ a) → c'.nmem a = c.nmem a) ∧
      ztdbe ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuk
  let I : Config → Prop := fun c' => ∃ j, j ≤ g ∧ WordsBounded W c' ∧ c'.nreg 170050 = j ∧
    c'.nreg ALLOC = Al + j ∧
    (∀ j', j' < j → c'.nmem (T' + j') = c.nmem (T + j')) ∧
    (∀ a, (a < T' ∨ T' + j ≤ a) → c'.nmem a = c.nmem a) ∧
    ztdbe ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  have hI0 : I c := ⟨0, by_omega, hw, h50, by_omega, fun _ h => absurd h by_omega,
    fun _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, rfl⟩
  obtain ⟨c', k, e, ⟨j, hj, hw', j50, jA, hcp, hmem, fr, hrr, hrm, ho⟩, htest, hk, hψ⟩ :=
    whileLtN_potential_lb' (P := P) (W := W) (a := 170050) (b := 170007) (body := copyBody) I
      (fun c' => 8 * (g - c'.nreg 170050)) ztcht ztdum
      (fun c2 ⟨j, hj, hw2, j50, jA, hcp, hmem, fr, hrr, hrm, ho⟩ htest => by
        have k07 : c2.nreg 170007 = g := by
          rw [fr _ ztbzm by_omega]; omega
        rw [j50, k07] at htest
        obtain ⟨c3, k3, e3, hk3, hw3, l50, lA, lw, lm, fr3, hrr3, hrm3, ho3⟩ :=
          copyBody_exec (P := P) (T := T) (T' := T') hw2 j50
            ztxbg
            ztxbg jA
            ztxbg
            by_omega by_omega by_omega by_omega
        refine ⟨c3, k3, e3, ⟨j + 1, by_omega, hw3, l50, by_omega, fun j' h' => ?_,
          fun a ha => by_grind,
          fun r h1 h2 => by_simp_all, by_simp_all, by_simp_all,
          by simp_all⟩, by_omega, by_omega⟩
        grind) hI0
  have hjg : j = g := by
    rw [j50, fr _ ztbzm by_omega, h07] at htest; omega
  subst hjg
  exact ⟨c', k, e, by_omega, hw', jA, by_omega, hcp, hmem, fr,
    hrr, hrm, ho⟩
end proofs
end
end Chazelle.Core.Up
namespace Chazelle.Core.Up
open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41
@[expose] public section
def RecBRG (r : ℕ) : Prop :=
  r = 170055 ∨ r = 170053 ∨ r = 170005 ∨ r = 170012 ∨ r = 170014 ∨ r = 170019 ∨ r = 170010 ∨
    r = 170009 ∨ r = 170008 ∨ r = 170007 ∨ r = 170015 ∨ r = 170016 ∨ r = 170035 ∨ r = 170036
section proofs
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 16000000 in
theorem recB_exec {c : Config} (hw : WordsBounded W c) {Al T' g R' h' cnt pg D Q g1 : ℕ}
    (hA : c.nreg ALLOC = Al) (h56 : c.nreg 170056 = T') (h07 : c.nreg 170007 = g)
    (h44 : c.nreg 170044 = R') (h51 : c.nreg 170051 = h') (h08 : c.nreg 170008 = cnt)
    (h10 : c.nreg 170010 = pg) (h03 : c.nreg 170003 = D) (h09 : c.nreg 170009 = Q)
    (h52 : c.nreg 170052 = g1) (h20 : c.nreg 170020 = 1) (hDQ : D + Q < T')
    (hWT : T' + g ≤ W) (hWA : Al + 1 ≤ W) (hWp : pg + pg ≤ W) (hWD : D + Q ≤ W)
    (hWQ : c.nmem ztfnj + 1 ≤ W) :
    ∃ c' k, Exec P W recB c c' k ∧ k = 16 ∧ WordsBounded W c' ∧
      c'.nmem zttdk = R' ∧ c'.nreg ALLOC = Al + 1 ∧ c'.nreg 170005 = h' ∧
      c'.nreg 170012 = cnt ∧ c'.nreg 170014 = R' ∧ c'.nreg 170019 = pg ∧
      c'.nreg 170010 = pg + pg ∧ c'.nreg 170009 = c.nmem ztfnj ∧
      c'.nreg 170008 = c.nmem ztfnj + 1 ∧ c'.nreg 170007 = g1 ∧ c'.nreg 170015 = 0 ∧
      c'.nreg 170016 = 0 ∧ c'.nreg 170035 = 0 ∧ c'.nreg 170036 = 1 ∧
      (∀ a, a ≠ T' + g → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ RecBRG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuk
  obtain ⟨c1, k1, e1, hk1, hw1, w1, A1, i05, i12, i14, i19, i10, i09, i07, i15, i16, i35, i36,
      m1, fr1, hrr1, hrm1, ho1⟩ : ∃ c1 k1, Exec P W recB1 c c1 k1 ∧ k1 = 15 ∧ WordsBounded W c1 ∧
      c1.nmem zttdk = R' ∧ c1.nreg ALLOC = Al + 1 ∧ c1.nreg 170005 = h' ∧
      c1.nreg 170012 = cnt ∧ c1.nreg 170014 = R' ∧ c1.nreg 170019 = pg ∧
      c1.nreg 170010 = pg + pg ∧ c1.nreg 170009 = c.nmem ztfnj ∧ c1.nreg 170007 = g1 ∧
      c1.nreg 170015 = 0 ∧ c1.nreg 170016 = 0 ∧ c1.nreg 170035 = 0 ∧ c1.nreg 170036 = 1 ∧
      (∀ a, a ≠ T' + g → c1.nmem a = c.nmem a) ∧
      (∀ r, ¬ RecBRG r → r ≠ ALLOC → c1.nreg r = c.nreg r) ∧
      c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    zudh
    unfold recB1
    exec_block
    all_goals
      try (config_simp; (try simp only [hA, h56, h07, h44, h51, h08, h10, h03, h09, h52, h20]); omega)
    refine ⟨rfl, ‹_›, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun a h1 => ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
    all_goals try (config_simp <;> (try simp only [hA, h56, h07, h44, h51, h08, h10, h03, h09,
      h52, h20, Machine.upd_apply]) <;> (try split_ifs) <;> first | omega | rfl)
    unfold RecBRG at h1
    zubi
    repeat (rw [Machine.upd_other _ _ _ by_omega])
  have c20 : c1.nreg 170020 = 1 := by
    rw [fr1 _ ztdmj by_omega]; omega
  obtain ⟨c2, k2, e2, hk2, hw2, j08, fr2, hm2, hrr2, hrm2, ho2⟩ : ∃ c2 k2, Exec P W
      ztnsa c1 c2 k2 ∧ k2 = 1 ∧ WordsBounded W c2 ∧
      c2.nreg 170008 = c.nmem ztfnj + 1 ∧ (∀ r, r ≠ 170008 → c2.nreg r = c1.nreg r) ∧
      c2.nmem = c1.nmem ∧ c2.rreg = c1.rreg ∧ c2.rmem = c1.rmem ∧ c2.output = c1.output := by
    exec_block
    all_goals try (config_simp; (try simp only [i09, c20]); omega)
    simp_all
  have g2 : ∀ r, r ≠ 170008 → c2.nreg r = c1.nreg r := fr2
  refine ⟨c2, k1 + k2, .seq e1 e2, by_omega, hw2, by_simp_all,
    by simp_all, by_simp_all,
    by simp_all, by_simp_all,
    by simp_all, by_simp_all,
    by simp_all, j08, by_simp_all,
    by simp_all, by_simp_all,
    by simp_all, by_simp_all,
    fun a ha => by_simp_all, fun r h1 h2 => ?_, by_simp_all, by_simp_all,
    by simp_all⟩
  rw [g2 r (fun e => h1 ztdmj), fr1 r h1 h2]
variable {c : Config}
set_option maxHeartbeats 16000000 in
theorem gamA_exec (hw : WordsBounded W c) {S p g1 cb G2 : ℕ}
    (h00 : c.nreg 170000 = S) (h02 : c.nreg 170002 = p) (h07 : c.nreg 170007 = g1)
    (h21 : c.nreg 170021 = 2) (h25 : c.nreg 170025 = 4)
    (hcb : c.nmem (S + p + 4 + g1) = cb) (hG2 : c.nmem (S + 2 + cb) = G2)
    (hW1 : S + p + 4 + g1 ≤ W) (hW2 : S + 2 + cb ≤ W) (hW8 : 8 ≤ W) :
    ∃ c' k, Exec P W gamA c c' k ∧ k = 10 ∧ WordsBounded W c' ∧
      c'.nreg 160024 = 1 ∧ c'.nreg 160080 = 2 ∧ c'.nreg 160021 = S + 2 ∧
      c'.nreg 160003 = g1 ∧ c'.nreg 160032 = G2 ∧
      (∀ r, r ≠ 160024 → r ≠ 160080 → r ≠ 160021 → r ≠ 160003 → r ≠ 170053 → r ≠ 170054 →
        r ≠ 160032 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold gamA
  exec_block
  all_goals try (config_simp; (try simp only [h00, h02, h07, h21, h25, hcb]); omega)
  simp_all
set_option maxHeartbeats 16000000 in
/-- **`γ'_{g}`** for the grade in `170007`. -/
theorem gamS_exec (hw : WordsBounded W c) {S p g1 : ℕ}
    (h00 : c.nreg 170000 = S) (h02 : c.nreg 170002 = p) (h07 : c.nreg 170007 = g1)
    (h21 : c.nreg 170021 = 2) (h25 : c.nreg 170025 = 4) (hg1 : 1 ≤ g1) (hgp : g1 ≤ p + 1)
    (hS : ∀ i, i ≤ p + 1 → c.nmem ztjmb = 2 ^ i ∧ c.nmem (S + p + 4 + i) = Cost.ceilBeta i)
    (hWS : S + 2 * p + 6 ≤ W) (hWγ : gradeGran g1 + g1 + 2 ≤ W) (hW8 : 8 ≤ W) :
    ∃ c' k, Exec P W gamS c c' k ∧ k ≤ 9 * g1 + 24 ∧ WordsBounded W c' ∧
      c'.nreg 170011 = gradeGran g1 ∧
      (∀ r, zteuy → r ≠ 170053 → r ≠ 170054 → r ≠ 170011 →
        c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hcb := (hS g1 hgp).2
  have hcbl : Cost.ceilBeta g1 ≤ g1 := Cost.ceilBeta_le g1
  have hG2 := (hS (Cost.ceilBeta g1) by_omega).1
  obtain ⟨c1, k1, e1, hk1, hw1, i24, i80, i21, i03, i32, fr1, hm1, hrr1, hrm1, ho1⟩ :=
    gamA_exec (P := P) hw h00 h02 h07 h21 h25 hcb hG2 by_omega by_omega hW8
  have hGg : 2 ^ Cost.ceilBeta g1 ≤ gradeGran g1 := by unfold gradeGran; omega
  obtain ⟨c2, k2, e2, hk2, hw2, j04, fr2, hm2, hrr2, hrm2, ho2⟩ :=
    clogS_exec (P := P) hw1 i21 i03 i24 ztbmx
      hg1 by_omega
  have hcl : Nat.clog 2 g1 ≤ g1 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hgg : gradeGran g1 = 2 ^ Cost.ceilBeta g1 + g1 * (Nat.clog 2 g1 + 2) := by
    zulun
  obtain ⟨c3, k3, e3, hk3, hw3, j32, fr3, hm3, hrr3, hrm3, ho3⟩ :=
    mulS_exec (P := P) (lam := g1) (G2 := 2 ^ Cost.ceilBeta g1) hw2 j04 by_grind
      by_grind
      by_grind
      by_grind by_omega
  obtain ⟨c4, k4, e4, hk4, hw4, j11, fr4, hm4, hrr4, hrm4, ho4⟩ : ∃ c4 k4, Exec P W
      ztoyn c3 c4 k4 ∧ k4 = 1 ∧ WordsBounded W c4 ∧
      c4.nreg 170011 = c3.nreg 160032 ∧ (∀ r, r ≠ 170011 → c4.nreg r = c3.nreg r) ∧
      c4.nmem = c3.nmem ∧ c4.rreg = c3.rreg ∧ c4.rmem = c3.rmem ∧ c4.output = c3.output := by
    exec_block
    refine ⟨rfl, ‹_›, by config_simp, fun r a1 => ?_, rfl, rfl, rfl, rfl⟩
    zubi
    repeat (rw [Machine.upd_other _ _ _ by_omega])
  refine ⟨c4, k1 + ztbqj, .seq e1 ztbal, by_omega, hw4,
    by omega, fun r h1 h2 h3 h4 => ?_, by_grind,
    by grind, by_grind, by_grind⟩
  rw [fr4 r h4, fr3 r by_omega by_omega by_omega by_omega,
    fr2 r by_omega by_omega by_omega,
    fr1 r by_omega by_omega by_omega by_omega h2 h3 by_omega]
end proofs
end
end Chazelle.Core.Up
namespace Chazelle.Core.Up
open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41
@[expose] public section
def gradeB (sB sL sG sP : Stmt) : Stmt :=
  .seq (chainsL sB sL sG sP) (.seq rowS (.seq recA (.seq copyL (.seq recB gamS))))

/-- **The grade invariant** at the head of grade `g`: the registers of the grade and the grade
record `h` with grades `< g` (the row of grade `g - 1` at `R`), the setup record `S` and the
halving table `D`. -/
def GradeInv (O : OracleIface) (P : Polygon) (c : Config) (g h hp R S D : ℕ) : Prop :=
  URegs c P.n hp h g ztduv ztcvr ztwwd R ∧
    c.nreg 170000 = S ∧ c.nreg 170002 = topGrade P.n ∧ c.nreg 170003 = D ∧
    c.nreg 170006 = topGrade P.n + 1 ∧ c.nreg 170009 = ztdfz / 2 ^ g ∧
    c.nreg 170015 = 0 ∧ c.nreg 170016 = 0 ∧ c.nreg 170035 = 0 ∧ c.nreg 170036 = 1 ∧
    Robust ztm c.nmem fun m => UpTab O P m h hp ztm ∧ m h = g ∧
      ztwvx ∧ m ztgn = S ∧ m ztbba = D

/-- The cost bound of grade `g`. -/
noncomputable def gradeC (κB κL : ℕ) (κG : ℕ → ℕ) (κO n g : ℕ) : ℕ :=
  gradeCount n g * (stepB κB κL κG κO g + 19) + 17 * g + 100

/-- The registers kept by a grade (besides the grade registers it updates). -/
def GK (r : ℕ) : Prop :=
  ztgvn ∨ r = 170000 ∨ r = 170001 ∨ r = 170002 ∨
    r = 170003 ∨ r = 170004 ∨ r = 170006 ∨ ztnet ∨ r = 170037 ∨
    ztgxz
section proofs
variable {O : OracleIface} {P : Polygon} {W : ℕ}
theorem two_pow_le_of_le_top {n g : ℕ} (hn : 2 ≤ n) (hg : g ≤ topGrade n) : 2 ^ g ≤ 2 * n := by
  have h1 : ztoqj := Nat.pow_le_pow_right by_norm_num hg
  rcases Nat.lt_or_ge 1 ztkl with h | h
  · have h2 := Nat.pow_pred_clog_lt_self (b := 2) by_norm_num h
    unfold topGrade at h1
    have h3 : ztzom := by
      rcases Nat.eq_zero_or_pos ztzul with h0 | h0
      · have := Nat.le_pow_clog (b := 2) by_norm_num ztkl; grind
      omega
    have e : 2 ^ Nat.clog 2 ztkl = 2 * 2 ^ (Nat.clog 2 ztkl).pred := by
      rw [← pow_succ', show (Nat.clog 2 ztkl).pred + 1 = Nat.clog 2 ztkl by rw [Nat.pred_eq_sub_one]; omega]
    omega
  · have : topGrade n = 0 := by
      unfold topGrade; rw [show n - 1 = 1 by omega]; simp
    grind
variable {r : ℕ}
theorem GK.kept (h : GK r) : Kept r ∧ r ≠ 170015 ∧ r ≠ 170016 ∧ r ≠ 170017 ∧
    r ≠ 170018 ∧ r ≠ 170035 ∧ r ≠ 170036 := by
  zumqy
  rcases h with ⟨h1, h2⟩ | h
  · refine ⟨Or.inl ztwo, ?_⟩
    zukko
    · zufdf
    · omega
  · refine ⟨Or.inr ⟨by unfold bandOf bUp; omega, by_omega⟩, by_omega⟩
theorem GK.ne_alloc (h : GK r) : r ≠ ALLOC := h.kept.1.ne_alloc
theorem GK.range (h : GK r) : r < 10000 ∨ r = 230000 ∨ 250000 ≤ r ∨
    (170000 ≤ r ∧ r ≤ 170004) ∨ r = 170006 ∨ ztnet ∨ r = 170037 ∨
    ztgxz := by
  zumqy
  rcases h with ⟨h1 | h1, -⟩ | h
  · zufdf
  · omega
  · omega
end proofs
end
end Chazelle.Core.Up
namespace Chazelle.Core.Up
open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41
@[expose] public section
def BruteM (sB : Stmt) (κB : ℕ) : Prop := Meets sB bruteBands
  (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c bBrute 1 ∧
    rd c bBrute 0 + rd c bBrute 1 + 1 ≤ P.n ∧ 1 ≤ rd c bBrute 2 ∧
    ztuu)
  (fun P c c' => ∃ C N, C.P = Qof P ∧ C.s = rd c bBrute 0 ∧ C.m = rd c bBrute 1 ∧
    Robust ztdo c'.nmem ztwq ∧
    IsCanonicalNF ztc zta N ztczy 4)
  ztyp

/-- The contract of Lemma 4.1 (`Lemma41Spec O`). -/
def L41M (O : OracleIface) (sL : Stmt) (κL : ℕ) : Prop := Meets sL l41Bands
  (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
    (gradeCtx O).holds P c.nmem ztbdk ztm ∧
    rd c bL41 3 ≤ c.nmem ztbdk ∧ lemma41Start ≤ rd c bL41 3 ∧
    rd c bL41 1 + rd c bL41 2 + 1 ≤ P.n ∧
    2 ^ ztbwz < rd c bL41 2 ∧ rd c bL41 2 ≤ 2 ^ rd c bL41 3)
  (fun P c c' => ∃ C N, C.P = Qof P ∧ C.s = rd c bL41 1 ∧ C.m = rd c bL41 2 ∧
    Robust ztdo c'.nmem ztwr ∧
    IsCanonicalNF ztc zta N ztbqg 4)
  ztxk

/-- The contract of the granularity enforcement (`GranularizeSpec`). -/
def GranM (sG : Stmt) (κG : ℕ → ℕ) : Prop := Meets sG granBands
  (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c bGran 2 ∧
    ModelDescWF P ztm c.nmem ztqa ∧
    ∃ M N, ModelDescAt c.nmem ztqa zta M ∧ GoodModel M ∧
      NFWithin c.nmem ztbdi ztm N ∧ IsNF M zta N ∧
      M.DegLe ztwiv ztqb ∧
      M.Semigranular ztwiv ztbdj)
  (fun P c c' => ∀ M N, ModelDescAt c.nmem ztqa zta M →
    NFAt c.nmem ztbdi N →
    ∃ N', c.nreg ALLOC ≤ rd c' bGran 4 ∧ NFWithin c'.nmem ztcoh ztdo N' ∧
      N'.F M zta ⊆ N.F M zta ∧
      IsCanonicalNF M zta N' ztbdj ztqb)
  (fun _ c => κG ztqb *
    ztin)
section proofs
variable {O : OracleIface} {P : Polygon} {W : ℕ}
set_option maxHeartbeats 64000000 in
/-- **One grade.** -/
theorem gradeB_exec {sB sL sG : Stmt} {κB κL : ℕ} {κG : ℕ → ℕ} (hB : BruteM sB κB)
    (hL : L41M O sL κL) (hGr : GranM sG κG) (hV : O.Valid) (hG : GoodEnv P)
    (hWh : hostWords P.n ≤ W) (hn : 2 ≤ P.n) {c : Config} (hw : WordsBounded W c)
    {g h hp R S D : ℕ} (hI : GradeInv O P c g h hp R S D) (hg : g ≤ topGrade P.n)
    (hW : c.nreg ALLOC + gradeC κB κL κG O.κ P.n g + stepB κB κL κG O.κ g + 8 ≤ W)
    (hWγ : gradeGran ztbs + g + 3 ≤ W) :
    ∃ c' k h' R', Exec P W (gradeB sB sL sG O.prep) c c' k ∧
      k ≤ gradeC κB κL κG O.κ P.n g ∧ WordsBounded W c' ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k ∧
      GradeInv O P c' ztbs h' hp R' S D ∧
      zth ∧
      ztgo ∧ c'.output = c.output ∧
      ztexe ∧
      zttc := by
  zuk
  zuku
  zufgf
  obtain ⟨hu, i00, i02, i03, i06, i09, i15, i16, i35, i36, hM⟩ := hI
  zugou
  zvmze at hM hW
  obtain ⟨hT0, hmh0, hR0, hS0, hD0⟩ := hM.holds
  obtain ⟨-, hSet, hHalf, -, -, ⟨hh4, hSA, hDA⟩, hTA, -, -⟩ := hT0
  rw [hS0] at hSet hSA
  rw [hD0] at hHalf hDA
  rw [hmh0] at hTA
  have h2g := two_pow_le_of_le_top hn hg
  zudbk

  have hcntn : cnt ≤ P.n := by
    rw [hcnt]; unfold gradeCount; have := Nat.div_le_self ztdfz ztgyk; omega
  unfold gradeC at hW
  rw [← hcnt, ← hK] at hW
  clear_value K
  -- the chains
  have hMc : Robust A c.nmem fun m => ChainMem O P m h hp g R (c.nreg 170018) 0 A :=
    robust_of hM le_rfl fun m h' => ⟨h'.1, h'.2.1, h'.2.2.1, trivial⟩
  have hb1 : A + ztbzu * (K + 8) ≤ W := by
    grind
  unfold BruteM at hB
  unfold L41M at hL
  unfold GranM at hGr
  obtain ⟨c1, k1, e1, hk1, hw1, a11, a12, hu1, hM1, m1, r1, o1, f1, ff1⟩ :=
    chainsL_exec (O := O) hB hL hGr hV hG hWh hn hw hu hA i15 i16 rfl i35 i36 h2g hMc by_grind
  have g1 : ∀ r, GK r → c1.nreg r = c.nreg r := fun r hr => by
    obtain ⟨k, a, b, c', d, e, f⟩ := hr.kept; grind
  have u1 : ∀ r, URegR r → c1.nreg r = c.nreg r := fun r hr =>
    f1 r hr.kept ztmq ztmq
      ztmq ztmq
      ztmq ztmq
  obtain ⟨A1, hA1⟩ : ∃ A1, c1.nreg ALLOC = A1 := by_grind
  zvnhf at a11 a12 hM1
  have hk1' : k1 ≤ cnt * ztnu + 2 := by_grind
  have hKc := Nat.mul_le_mul_left cnt (show K + 2 ≤ K + 19 by omega)
  have hc19 : cnt * (K + 19) = cnt * ztnu + 17 * cnt := by_ring
  -- the row
  obtain ⟨c2, k2, e2, hk2, hw2, A2e, a22, j44, hE2, m2, fr2, hrr2, hrm2, ho2⟩ :=
    rowS_exec (O := O) (P := P) (hp := hp) (g := g) hw1 hA1 hu1.r08 rfl hu1.r20 hu1.r21 hu1.r22
      hu1.r29 (robust_of hM1 le_rfl fun m h' => h'.2.2.2) by_omega
  have g2 : ∀ r, GK r → c2.nreg r = c1.nreg r := fun r hr =>
    fr2 r (by have := hr.range; unfold RowRG; omega) hr.ne_alloc
  have u2 : ∀ r, URegR r → c2.nreg r = c1.nreg r := fun r hr =>
    fr2 r (by unfold URegR at hr; unfold RowRG; omega) ztmq
  have hmc2 : ztfai := fun a ha => by
    rw [m2 a by_omega, m1 a ha]
  have U2 := fun r hr => (u2 r hr).trans (u1 r hr)
  -- the header
  obtain ⟨c3, k3, e3, hk3, hw3, A3e, j51, j52, j56, j57, j50, w0, w1, w2, w3, m3, fr3, hrr3,
      hrm3, ho3⟩ :=
    recA_exec (P := P) (h := h) (g := g) hw2 A2e ((U2 170005 ztqk).trans hu.r05)
      ((U2 170007 ztqk).trans hu.r07)
      ((U2 170020 ztqk).trans hu.r20)
      ((U2 170021 ztqk).trans hu.r21)
      ((U2 170022 ztqk).trans hu.r22)
      ((U2 170025 ztqk).trans hu.r25)
      by_omega by_omega by_omega
  have u3 : ∀ r, URegR r → c3.nreg r = c2.nreg r := fun r hr =>
    fr3 r (by unfold URegR at hr; unfold RecRG; omega) ztmq
  have g3 : ∀ r, GK r → c3.nreg r = c2.nreg r := fun r hr =>
    fr3 r (by have := hr.range; unfold RecRG; omega) hr.ne_alloc
  -- the old rows
  have hT : c2.nmem zteu + g ≤ A := by rw [hmc2 _ by_omega]; omega
  obtain ⟨c4, k4, e4, hk4, hw4, A4e, a42, hcp, m4, fr4, hrr4, hrm4, ho4⟩ :=
    copyL_exec (P := P) hw3 j50
      (((u3 170007 ztqk).trans (U2 170007 ztqk)).trans hu.r07)
      j57 j56 A3e
      (((u3 170020 ztqk).trans (U2 170020 ztqk)).trans hu.r20)
      by_omega by_omega by_omega by_omega
  have u4 : ∀ r, URegR r → c4.nreg r = c.nreg r := fun r hr => by
    rw [fr4 r (by unfold URegR at hr; unfold CopyRG; omega) ztmq,
      u3 r hr, u2 r hr, u1 r hr]
  have g4 : ∀ r, GK r → c4.nreg r = c.nreg r := fun r hr => by
    rw [fr4 r (by have := hr.range; unfold CopyRG; omega) hr.ne_alloc,
      g3 r hr, g2 r hr, g1 r hr]
  have hmc4 : ∀ a, a < A → c4.nmem a = c.nmem a := fun a ha => by
    rw [m4 a by_grind, m3 a by_grind, hmc2 a ha]
  -- the new row, the registers of the next grade
  set Q := ztdfz / 2 ^ g with hQ
  clear_value Q
  have hQn : Q ≤ P.n := by zvnao; have := Nat.div_le_self ztdfz ztgyk; omega
  have hQ2 : c4.nmem ztfnj = Q / 2 := by rw [hmc4 _ by_omega]; exact hHalf Q hQn
  have hj44 : c4.nreg 170044 = A1 := by
    rw [fr4 _ ztbzm by_omega,
      fr3 _ (by unfold RecRG; omega) by_omega]; omega
  have hTT : A + 1 ≤ A1 + 3 * cnt + 4 := by_omega
  obtain ⟨c5, k5, e5, hk5, hw5, w5, A5e, j05, j12, j14, j19, j10, j09, j08, j07, j15, j16, j35,
      j36, m5, fr5, hrr5, hrm5, ho5⟩ :=
    recB_exec (P := P) (T' := A1 + 3 * cnt + 4) (g := g) (R' := A1) (h' := A1 + 3 * cnt)
      (cnt := cnt) (pg := 2 ^ g) (D := D) (Q := Q) (g1 := g + 1) hw4 A4e
      ((fr4 170056 ztbzm by_omega).trans j56)
      ((u4 170007 ztqk).trans hu.r07) hj44
      ((fr4 170051 ztbzm by_omega).trans j51)
      ((u4 170008 ztqk).trans hu.r08)
      ((u4 170010 ztqk).trans hu.r10)
      ((u4 170003 ztqk).trans i03)
      ((u4 170009 ztqk).trans i09)
      ((fr4 170052 ztbzm by_omega).trans j52)
      ((u4 170020 ztqk).trans hu.r20) by_omega by_omega by_omega
      by_omega by_omega by_omega
  have w5r : ∀ r, URegR r → ¬ RecBRG r → c5.nreg r = c.nreg r := fun r h1 h2 => by
    rw [fr5 r h2 (by unfold URegR at h1; omega), u4 r h1]
  have g5 : ∀ r, GK r → c5.nreg r = c.nreg r := fun r hr => by
    rw [fr5 r (by have := hr.range; unfold RecBRG; omega) hr.ne_alloc,
      g4 r hr]
  have hSc : ∀ i, i ≤ topGrade P.n + 1 → c5.nmem ztjmb = 2 ^ i ∧
      c5.nmem (S + topGrade P.n + 4 + i) = Cost.ceilBeta i := fun i hi => by
    rw [m5 _ by_omega, m5 _ by_omega, hmc4 _ by_omega, hmc4 _ by_omega]
    exact hSet.2.2.1 i hi
  obtain ⟨c6, k6, e6, hk6, hw6, j11, fr6, hm6, hrr6, hrm6, ho6⟩ :=
    gamS_exec (P := P) (S := S) (p := topGrade P.n) (g1 := g + 1) hw5
      ((w5r 170000 ztqk ztdmj).trans i00)
      ((w5r 170002 ztqk ztdmj).trans i02) j07
      ((w5r 170021 ztqk ztdmj).trans hu.r21)
      ((w5r 170025 ztqk ztdmj).trans hu.r25)
      by_omega by_omega hSc by_omega by_omega by_omega
  have v6 :=
    fun r a b d e => fr6 r (Or.inr a) b d e
  have hA6 :=
    (fr6 ALLOC by_omega by_decide by_decide by_decide).trans A5e
  -- memory
  have mc62 : ∀ a, a < A1 + 3 * cnt → c6.nmem a = c2.nmem a := fun a ha => by
    rw [hm6, m5 a zthef, m4 a (Or.inl zthef),
      m3 a ztbbu]
  have mc61 : ∀ a, a < A1 → c6.nmem a = c1.nmem a := fun a ha => by
    rw [mc62 a zthef, m2 a ztbbu]
  have mc6 : ztknw := fun a ha => by
    rw [mc61 a (by clear * - ha a11; omega), m1 a ha]
  have hQ' : Q / 2 = ztdfz / 2 ^ ztbs := by
    rw [hQ, Nat.div_div_eq_div_mul, ← pow_succ]
  refine ⟨c6, k1 + ztrd, A1 + 3 * cnt, A1,
    .seq e1 ztvb, ?_, hw6,
    by clear * - hA a11 hA6; omega,
    by clear * - hA a12 a22 A2e hk3 A3e A4e a42 hk5 hA6; omega,
    ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, j11, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun a ha => mc6 a by_omega, fun a ha => by
      rw [hrm6, hrm5, hrm4, hrm3, hrm2, r1 a by_omega],
    by rw [ho6, ho5, ho4, ho3, ho2, o1], fun r hr => by
      have := hr.range
      rw [fr6 r by_omega by_omega
        by_omega by_omega, g5 r hr],
    fun r hr => by
      rw [hrr6, hrr5, hrr4, hrr3, hrr2, ff1 r hr]⟩
  · unfold gradeC; rw [← hcnt, ← hK]
    clear * - hk1' hk2 hk3 hk4 hk5 hk6 hc19; omega
  · zumwm; exact hu.r01
  · zumwm; exact hu.r04
  · rw [v6 _ by_decide by_decide by_decide by_decide, j05]
  · rw [v6 _ by_decide by_decide by_decide by_decide, j07]
  · rw [v6 _ by_decide by_decide by_decide by_decide, j08, hQ2, gradeCount_succ, ← hQ]
  · rw [v6 _ by_decide by_decide by_decide by_decide, j10, pow_succ]; ring
  · rw [v6 _ by_decide by_decide by_decide by_decide, j12, Nat.add_sub_cancel]; try rfl
  · rw [v6 _ by_decide by_decide by_decide by_decide, j14]
  · rw [v6 _ by_decide by_decide by_decide by_decide, j19, Nat.add_sub_cancel]
  · zumwm; exact hu.r20
  · zumwm; exact hu.r21
  · zumwm; exact hu.r22
  · zumwm; exact hu.r23
  · zumwm; exact hu.r25
  · zumwm; exact hu.r26
  · zumwm; exact hu.r28
  · zumwm; exact hu.r29
  · zumwm; exact hu.r37
  · zurk
  · zurk
  · zurk
  · zurk
  · rw [v6 _ by_decide by_decide by_decide by_decide, j09, hQ2, hQ']
  · rw [v6 _ by_decide by_decide by_decide by_decide, j15]
  · rw [v6 _ by_decide by_decide by_decide by_decide, j16]
  · rw [v6 _ by_decide by_decide by_decide by_decide, j35]
  · rw [v6 _ by_decide by_decide by_decide by_decide, j36]
  · zumml
    zucng
    clear * - hm hM mc6 hm6 m5 m4 m3 w0 w1 w2 w3 hmc2 hS0 hD0 hcp w5 hE2 mc61 mc62 hcnt a11 hh4
      hSA hDA hTA hg
    have hmc : ∀ a, a < A → m a = c.nmem a := by_grind
    obtain ⟨hTm, hmhm, -, hSm, hDm⟩ := hM m hmc
    obtain ⟨-, hSetm, hHalfm, hHm, hhpm, -, -, hrowm, hEm⟩ := hTm
    rw [hSm] at hSetm; rw [hDm] at hHalfm; rw [hmhm] at hrowm hEm
    have mc63 : ∀ a, a < A1 + 3 * cnt + 4 → c6.nmem a = c3.nmem a := fun a ha => by
      rw [hm6, m5 a by_omega, m4 a ztbbu]
    have e0 : m (A1 + 3 * cnt) = g + 1 :=
      by grind
    have e1 : m (A1 + 3 * cnt + 1) = S :=
      by grind
    have e2 : m (A1 + 3 * cnt + 2) = A1 + 3 * cnt + 4 :=
      by grind
    have e3 : m (A1 + 3 * cnt + 3) = D :=
      by grind
    have hTc : c2.nmem _ = c.nmem zteu := hmc2 _ by_omega
    have et : ∀ j, j < g → m (A1 + 3 * cnt + 4 + j) = m (m _ + j) := fun j hj => by
      rw [hmc zteu by_omega, hmc (c.nmem _ + j) by_omega,
        hm _ by_omega, hm6, m5 _ by_omega, hcp j hj,
        m3 _ by_omega, hTc, hmc2 _ by_omega]
    have eg : m (A1 + 3 * cnt + 4 + g) = A1 := by_grind
    refine ⟨⟨by_omega, by_grind, by zvnak; omega, hHm,
      by omega, by_omega, by_omega,
      fun g' hg' => ?_, fun g' i hg' hi => ?_⟩, e0, fun _ => by
        rw [e2, Nat.add_sub_cancel, eg], e1, e3⟩
    · zukqs
      zucjj
      zuidl
      · grind
      · rw [show g' = g by clear * - hg' h1; omega, eg, ← hcnt]; omega
    · zukqs
      simp only [rowE]
      zucjj
      zuidl
      · rw [et g' h1]; exact (hEm g' i h1 hi).mono by_omega
      · have hgg : g' = g := by_omega
        rw [hgg] at hi ⊢
        have hi' : i < cnt := by_omega
        have b0 : A1 + 3 * i < A1 + 3 * cnt := by_omega
        have b1 : A1 + 3 * i + 1 < A1 + 3 * cnt := by_omega
        have b2 : A1 + 3 * i + 2 < A1 + 3 * cnt := by_omega
        have hmm : ∀ a, a < A1 + 3 * cnt → m a = c2.nmem a := fun a ha =>
          (hm a by_omega).trans by_grind
        rw [eg, hmm _ b0, hmm _ b1, hmm _ b2]
        exact (hE2 i hi' m fun a ha => (hm a by_omega).trans by_grind).mono
          by_omega
end proofs
end
end Chazelle.Core.Up
namespace Chazelle.Core.Up
open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41
@[expose] public section
def gradesL (sB sL sG sP : Stmt) : Stmt := .whileLtN 170007 170006 (gradeB sB sL sG sP)

/-- The budget of grade `g`. -/
noncomputable def gT (κB κL : ℕ) (κG : ℕ → ℕ) (κO n g : ℕ) : ℕ :=
  gradeC κB κL κG κO n g + stepB κB κL κG κO g + 10

/-- **The cost bound of all grades.** -/
noncomputable def upT (κB κL : ℕ) (κG : ℕ → ℕ) (κO n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (topGrade n + 1), gT κB κL κG κO n j
section proofs
variable {O : OracleIface} {P : Polygon} {W : ℕ}
theorem sq_le_two_pow (p : ℕ) : ztdhu ^ 2 ≤ 16 * 2 ^ p := by
  induction p with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ 2 k]
    have h : (k + 1 + 3) ^ 2 ≤ 2 * (k + 3) ^ 2 := by_grind
    linarith

/-- `γ'_{g+1}` is small against the word bound. -/
theorem gradeGran_succ_le {n g : ℕ} (hn : 2 ≤ n) (hg : g ≤ topGrade n) :
    gradeGran ztbs + g + 3 ≤ 128 * n := by
  have h2 := two_pow_le_of_le_top hn hg
  have hp := two_pow_le_of_le_top hn ztzgj
  have hsq := sq_le_two_pow g
  have hgp : ztoqj := Nat.pow_le_pow_right by_norm_num hg
  have hcb : Cost.ceilBeta ztbs ≤ g + 1 := Cost.ceilBeta_le _
  have h3 : 2 ^ Cost.ceilBeta ztbs ≤ 2 ^ ztbs := Nat.pow_le_pow_right by_norm_num hcb
  have hcl : Nat.clog 2 ztbs ≤ g + 1 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have h4 : ztbs * ztxvo ≤ ztnzs ^ 2 := by_nlinarith
  zuhqt
  grind
set_option maxHeartbeats 32000000 in
/-- **All grades.** -/
theorem gradesL_exec {sB sL sG : Stmt} {κB κL : ℕ} {κG : ℕ → ℕ} (hB : BruteM sB κB)
    (hL : L41M O sL κL) (hGr : GranM sG κG) (hV : O.Valid) (hG : GoodEnv P)
    (hWh : hostWords P.n ≤ W) (hn : 2 ≤ P.n) {c : Config} (hw : WordsBounded W c)
    {h hp R S D : ℕ} (hI : GradeInv O P c 0 h hp R S D)
    (hW : c.nreg ALLOC + upT κB κL κG O.κ P.n ≤ W) :
    ∃ c' k h' R', Exec P W (gradesL sB sL sG O.prep) c c' k ∧
      k ≤ upT κB κL κG O.κ P.n + 2 ∧ WordsBounded W c' ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k ∧
      GradeInv O P c' (topGrade P.n + 1) h' hp R' S D ∧
      zth ∧
      ztgo ∧ c'.output = c.output ∧
      ztexe ∧
      zttc := by
  set p := topGrade P.n with hp_def
  set F := gT κB κL κG O.κ P.n with hF
  obtain ⟨A0, hA0⟩ : ztprc := zths
  rw [hA0] at hW ⊢
  zuku
  let I : Config → Prop := fun c' => ∃ g h' R', g ≤ p + 1 ∧ WordsBounded W c' ∧
    GradeInv O P c' g h' hp R' S D ∧ A0 ≤ c'.nreg ALLOC ∧
    c'.nreg ALLOC ≤ A0 + ∑ j ∈ Finset.range g, F j ∧
    ztiub ∧ ztiuc ∧
    c'.output = c.output ∧ ztexe ∧
    zttc
  have hI0 : I c := ⟨0, h, R, by_omega, hw, hI, by_omega, by_omega,
    fun _ _ => rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  have hsplit : ∀ g, g < p + 1 → ∑ j ∈ Finset.Ico g ztr, F j =
      F g + ∑ j ∈ Finset.Ico ztbs ztr, F j := fun g hg =>
    Finset.sum_eq_sum_Ico_succ_bot hg F
  have htot : ∀ g, g ≤ p + 1 → ∑ j ∈ Finset.range g, F j + ∑ j ∈ Finset.Ico g ztr, F j =
      upT κB κL κG O.κ P.n := fun g hg => by
    unfold upT; rw [← hp_def, ← hF, Finset.range_eq_Ico, Finset.sum_Ico_consecutive _ by_omega hg,
      Finset.range_eq_Ico]
  obtain ⟨c', k, e, ⟨g, h', R', hgp, hw', hI', a1, a2, mm, mr, mo, fr, frr⟩, htest, hk, hψ⟩ :=
    whileLtN_potential_lb' (P := P) (W := W) (a := 170007) (b := 170006)
      (body := gradeB sB sL sG O.prep) I
      (fun c' => ∑ j ∈ Finset.Ico (c'.nreg 170007) ztr, F j)
      ztcht (fun c' ⟨_, _, _, _, h, _⟩ => h)
      (fun c2 ⟨g, h2, R2, hgp, hw2, hI2, a1, a2, mm, mr, mo, fr, frr⟩ htest => by
        rw [hI2.1.r07, hI2.2.2.2.2.1] at htest
        have hg : g ≤ p := by_omega
        have hsum := htot g by_omega
        have hs := hsplit g htest
        have hFg : F g = gradeC κB κL κG O.κ P.n g + stepB κB κL κG O.κ g + 10 := rfl
        obtain ⟨c3, k3, h3, R3, e3, hk3, hw3, b1, b2, hI3, m3, r3, o3, f3, ff3⟩ :=
          gradeB_exec (O := O) hB hL hGr hV hG hWh hn hw2 hI2 hg by_omega
            (by have := gradeGran_succ_le hn hg; unfold hostWords at hWh; omega)
        refine ⟨c3, k3, e3, ⟨g + 1, h3, R3, by_omega, hw3, hI3, by_omega, ?_,
          fun a ha => by_grind,
          fun a ha => by_grind, by_grind,
          fun r hr => by_grind, fun r hr => by_grind⟩, ?_,
          by omega⟩
        · grind
        · rw [hI3.1.r07, hI2.1.r07]; omega) hI0
  have hgp' : g = p + 1 := by rw [hI'.1.r07, hI'.2.2.2.2.1] at htest; omega
  subst hgp'
  refine ⟨c', k, h', R', e, ?_, hw', a1, by_omega, hI', mm, mr, mo, fr, frr⟩
  have := htot 0 by_omega
  rw [hI.1.r07] at hk
  omega
end proofs
end
end Chazelle.Core.Up
namespace Chazelle.Core.Up
open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41
@[expose] public section
def initA : Stmt := block [.constN 170020 1, .constN 170021 2, .constN 170022 3,
  .constN 170023 5, .constN 170025 4, .constN 170026 6, .constN 170029 0, .constN 170037 7,
  .copyN 170000 230000, .inputSize 170001, .addN 170053 170000 170020, .loadN 170002 170053,
  .addN 170006 170002 170020, .subN 170028 170001 170020]

/-- The whole host. -/
def initH : Stmt := .seq zthsh
  (.seq proH ztoym)

/-- The record of grade `0` and the registers of grade `0`. -/
def initR : Stmt := block [.copyN 170005 9999, .storeN 170005 170029,
  .addN 170053 170005 170020, .storeN 170053 170000,
  .addN 170053 170005 170021, .addN 170054 170005 170025, .storeN 170053 170054,
  .addN 170053 170005 170022, .storeN 170053 170003, .addN 9999 9999 170025,
  .constN 170007 0, .copyN 170008 170028, .subN 170009 170028 170020, .constN 170010 1,
  .constN 170011 1, .copyN 170012 170028, .constN 170014 0, .constN 170019 1,
  .constN 170015 0, .constN 170016 0, .constN 170035 0, .constN 170036 1]

/-- The registers written by `initR` (besides the allocator). -/
def InitRRG (r : ℕ) : Prop :=
  r = 170005 ∨ r = 170053 ∨ r = 170054 ∨ r = 170007 ∨ r = 170008 ∨ r = 170009 ∨
    r = 170010 ∨ r = 170011 ∨ r = 170012 ∨ r = 170014 ∨ r = 170019 ∨ r = 170015 ∨
    r = 170016 ∨ r = 170035 ∨ r = 170036
section proofs
variable {P : Polygon} {W : ℕ}
variable {c : Config}
set_option maxHeartbeats 16000000 in
theorem initA_exec (hw : WordsBounded W c) {S p : ℕ}
    (h00 : c.nreg 230000 = S) (hS1 : c.nmem ztbgu = p) (hWS : S + 1 ≤ W) (hWp : p + 1 ≤ W)
    (hWn : P.n ≤ W) (hW8 : 8 ≤ W) :
    ∃ c' k, Exec P W initA c c' k ∧ k = 14 ∧ WordsBounded W c' ∧
      c'.nreg 170020 = 1 ∧ c'.nreg 170021 = 2 ∧ c'.nreg 170022 = 3 ∧ c'.nreg 170023 = 5 ∧
      c'.nreg 170025 = 4 ∧ c'.nreg 170026 = 6 ∧ c'.nreg 170029 = 0 ∧ c'.nreg 170037 = 7 ∧
      c'.nreg 170000 = S ∧ c'.nreg 170001 = P.n ∧ c'.nreg 170002 = p ∧
      c'.nreg 170006 = p + 1 ∧ c'.nreg 170028 = P.n - 1 ∧
      (∀ r, bandOf r ≠ bUp → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold initA
  exec_block
  all_goals try (config_simp; (try simp only [h00, hS1]); omega)
  refine ⟨rfl, ‹_›, by config_simp, by config_simp, by config_simp, by config_simp,
    by config_simp, by config_simp, by config_simp, by config_simp, by_simp_all,
    by config_simp, by_simp_all, by_simp_all,
    by config_simp, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  unfold bandOf bUp at hr
  zubi
  repeat (rw [Machine.upd_other _ _ _ by_omega])
set_option maxHeartbeats 16000000 in
theorem initH_exec (hw : WordsBounded W c) {A : ℕ} (hA : c.nreg ALLOC = A)
    (hn : 1 ≤ P.n) (hW : A + 7 ≤ W) (hWn : P.n ≤ W) (hW8 : 8 ≤ W) :
    ∃ c' k, Exec P W initH c c' k ∧ k = 16 ∧ WordsBounded W c' ∧
      c'.nreg ALLOC = A + 7 ∧ c'.nreg 170004 = A ∧ HostAt c'.nmem A ztqg ∧
      ztzt ∧
      (∀ r, bandOf r ≠ bL41 → r ≠ 170004 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuk
  obtain ⟨c1, k1, e1, hk1, hw1, i24, i29, i86, fr1, hm1, hrr1, hrm1, ho1⟩ : ∃ c1 k1, Exec P W
      zthsh c c1 k1 ∧ k1 = 3 ∧
      WordsBounded W c1 ∧ c1.nreg 160024 = 1 ∧ c1.nreg 160029 = 0 ∧ c1.nreg 160086 = 7 ∧
      (∀ r, r ≠ 160024 → r ≠ 160029 → r ≠ 160086 → c1.nreg r = c.nreg r) ∧ c1.nmem = c.nmem ∧
      c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    all_goals try (config_simp; omega)
    simp_all
  have hA1 : ztupb := by
    simp_all
  obtain ⟨c2, k2, e2, hk2, hw2, A2, j27, j15, hH, hm2, fr2, hrr2, hrm2, ho2⟩ :=
    proH_exec (P := P) hw1 hA1 i24 i29 i86 hn hW hWn
  obtain ⟨c3, k3, e3, hk3, hw3, j04, fr3, hm3, hrr3, hrm3, ho3⟩ : ∃ c3 k3, Exec P W
      ztoym c2 c3 k3 ∧ k3 = 1 ∧ WordsBounded W c3 ∧
      c3.nreg 170004 = c2.nreg 160027 ∧ (∀ r, r ≠ 170004 → c3.nreg r = c2.nreg r) ∧
      c3.nmem = c2.nmem ∧ c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output := by
    exec_block
    refine ⟨rfl, ‹_›, by config_simp, fun r a1 => ?_, rfl, rfl, rfl, rfl⟩
    zubi
    repeat (rw [Machine.upd_other _ _ _ by_omega])
  refine ⟨c3, k1 + ztdve, .seq e1 ztbpc, by_omega, hw3,
    by grind, by_omega, by_grind,
    fun a ha => by_grind, fun r h1 h2 h3 => ?_, by_grind,
    by grind, by_grind⟩
  have : r < 160000 ∨ 170000 ≤ r := by unfold bandOf bL41 at h1; omega
  grind
set_option maxHeartbeats 16000000 in
theorem initR_exec (hw : WordsBounded W c) {H S D n1 : ℕ}
    (hA : c.nreg ALLOC = H) (h00 : c.nreg 170000 = S) (h03 : c.nreg 170003 = D)
    (h28 : c.nreg 170028 = n1) (h20 : c.nreg 170020 = 1) (h21 : c.nreg 170021 = 2)
    (h22 : c.nreg 170022 = 3) (h25 : c.nreg 170025 = 4) (h29 : c.nreg 170029 = 0)
    (hW : H + 4 ≤ W) (hW8 : 8 ≤ W) :
    ∃ c' k, Exec P W initR c c' k ∧ k = 22 ∧ WordsBounded W c' ∧
      c'.nreg 170005 = H ∧ c'.nreg ALLOC = H + 4 ∧
      c'.nmem H = 0 ∧ c'.nmem ztemv = S ∧ c'.nmem ztfnq = H + 4 ∧ c'.nmem ztjiy = D ∧
      c'.nreg 170007 = 0 ∧ c'.nreg 170008 = n1 ∧ c'.nreg 170009 = n1 - 1 ∧
      c'.nreg 170010 = 1 ∧ c'.nreg 170011 = 1 ∧ c'.nreg 170012 = n1 ∧ c'.nreg 170014 = 0 ∧
      c'.nreg 170019 = 1 ∧ c'.nreg 170015 = 0 ∧ c'.nreg 170016 = 0 ∧ c'.nreg 170035 = 0 ∧
      c'.nreg 170036 = 1 ∧
      (∀ a, (a < H ∨ H + 4 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ InitRRG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuk
  zudh
  unfold initR
  exec_block
  all_goals
    try (config_simp; (try simp only [hA, h00, h03, h28, h20, h21, h22, h25, h29]); omega)
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun a h1 => ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  all_goals try (config_simp <;> (try simp only [hA, h00, h03, h28, h20, h21, h22, h25, h29,
    Machine.upd_apply]) <;> (try split_ifs) <;> first | omega | rfl)
  unfold InitRRG at h1
  zubi
  repeat (rw [Machine.upd_other _ _ _ by_omega])
end proofs
open Chazelle.Cost
noncomputable def Yg (g : ℕ) : ℝ := (2 : ℝ) ^ g * (2 : ℝ) ^ ztls

/-- **The per-chain constant.** -/
noncomputable def K1 (κB κL : ℕ) (κG : ℕ → ℕ) (κO : ℕ) : ℝ :=
  κB * 129 ^ 3 + κL * (2 * 34200 ^ 3 + 2) +
    κG 4 * ztbrt + κO * ztffe + 2000
section proofs
variable (g : ℕ) (κB κL : ℕ) (κG : ℕ → ℕ)
theorem Yg_pos : 0 < Yg g := by unfold Yg; positivity
theorem one_le_Yg : 1 ≤ Yg g := by
  zulua
  zuogz
  apply Real.one_le_rpow by_norm_num
  grind
theorem Yg_le : Yg g ≤ (2 : ℝ) ^ g := by
  zulua
  have h1 : (2 : ℝ) ^ ztls ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos by_norm_num
    grind
  simp_all

/-- `2^(-g/5) ≤ 2^(-g/76)`, times `2^g`. -/
theorem pow_mul_div5_le : (2 : ℝ) ^ g * (2 : ℝ) ^ ztew ≤ Yg g := by
  zulua
  exact mul_le_mul_of_nonneg_left (two_rpow_neg_div5_le g) by_positivity

/-- `2^g · g 2^(-g/5) ≤ 12 Y g`. -/
theorem pow_mul_lin_le :
    (2 : ℝ) ^ g * ztwmr ≤ 12 * Yg g := by
  zulua
  have := mul_le_mul_of_nonneg_left (slack76_linear g) (show (0 : ℝ) ≤ (2 : ℝ) ^ g by positivity)
  linarith

/-- **Lemma 4.1's bound** is at most a constant times `Y g`. -/
theorem lemma41Nat_le : (lemma41Nat g : ℝ) ≤ (2 * 34200 ^ 3 + 1) * Yg g := by
  unfold lemma41Nat
  set x : ℝ := (g : ℝ) ^ 2 * zttu * (2 : ℝ) ^ ztme with hx
  have hg0 : ztcrf := Nat.cast_nonneg g
  have hcl : (Nat.clog 2 g : ℝ) ≤ g := by exact_mod_cast clog_two_le_self g
  have hcl0 : (0 : ℝ) ≤ Nat.clog 2 g := Nat.cast_nonneg _
  have hp : ztxst := two_rpow_pos _
  zukgw
  have hsq : (g : ℝ) ^ 2 * zttu ≤ 2 * (g : ℝ) ^ 3 := by
    rcases Nat.eq_zero_or_pos g with h | h
    · simp_all
    · have : ztiwz := by exact_mod_cast h
      nlinarith
  have hsplit : (2 : ℝ) ^ ztme = (2 : ℝ) ^ g * (2 : ℝ) ^ ztbkf := by
    zuogz; grind
  have hc := slack76_cubic g
  have hq : ztylc := (two_rpow_pos _).le
  zujyq
  have hxle : x ≤ 2 * 34200 ^ 3 * Yg g := by
    zulua
    calc x ≤ 2 * (g : ℝ) ^ 3 * (2 : ℝ) ^ ztme := by
          zvnly; exact mul_le_mul_of_nonneg_right hsq hp.le
      _ = 2 * (2 : ℝ) ^ g * ((g : ℝ) ^ 3 * (2 : ℝ) ^ ztbkf) := by_grind
      _ ≤ 2 * (2 : ℝ) ^ g * (34200 ^ 3 * (2 : ℝ) ^ ztls) :=
          mul_le_mul_of_nonneg_left hc by_positivity
      _ = 2 * 34200 ^ 3 * ((2 : ℝ) ^ g * (2 : ℝ) ^ ztls) := by_ring
  have hce := Nat.ceil_lt_add_one hx0
  have := one_le_Yg g
  linarith

/-- `1 / (γ'_g + 1) ≤ 2^(-g/5)`. -/
theorem inv_gradeGran_le : 1 / ztlzh ≤ (2 : ℝ) ^ ztew := by
  refine le_trans ?_ (inv_two_pow_ceilBeta_le g)
  have h1 : (2 : ℝ) ^ ceilBeta g ≤ (gradeGran g : ℝ) + 1 := by
    have : 2 ^ ceilBeta g ≤ gradeGran g := by unfold gradeGran; omega
    have : ((2 ^ ceilBeta g : ℕ) : ℝ) ≤ gradeGran g := by exact_mod_cast this
    grind
  exact one_div_le_one_div_of_le by_positivity h1

/-- **The chord bound of a normal form of grade `g`** is `O(2^g 2^(-g/5))`. -/
theorem NB_le : (NB g : ℝ) ≤ 10 * l23c 4 * ztwjl := by
  unfold NB
  zumje
  have hi := inv_gradeGran_le g
  zuegy

  zulnw

  calc (l23c 4 : ℝ) * ztydd * (1 / ztlzh)
      ≤ (l23c 4 : ℝ) * ztydd * (2 : ℝ) ^ ztew :=
        mul_le_mul_of_nonneg_left hi by_positivity
    _ ≤ (l23c 4 : ℝ) * (10 * (2 : ℝ) ^ g) * (2 : ℝ) ^ ztew := by
        zugwx
        apply mul_le_mul_of_nonneg_right _ (two_rpow_pos _).le
        zuldj

    _ = 10 * l23c 4 * ztwjl := by_ring

/-- **The preprocessing term.** -/
theorem NB_term_le :
    ((NB g * ztbs + 1 : ℕ) : ℝ) ≤ ztffe * Yg g := by
  have h := NB_le g
  zubkl

  have hNB0 : (0 : ℝ) ≤ NB g := Nat.cast_nonneg _
  push_cast
  have e1 : (NB g : ℝ) * ztgvx ≤
      10 * l23c 4 * ztwjl * ztgvx :=
    mul_le_mul_of_nonneg_right h by_linarith
  have e2 : 10 * (l23c 4 : ℝ) * ztwjl * ztgvx =
      10 * l23c 4 * ((2 : ℝ) ^ g * ztwmr +
        (2 : ℝ) ^ g * (2 : ℝ) ^ ztew) := by_ring
  have e3 : (2 : ℝ) ^ g * ztwmr +
      (2 : ℝ) ^ g * (2 : ℝ) ^ ztew ≤ 13 * Yg g := by_linarith
  have e4 := mul_le_mul_of_nonneg_left e3 (show (0 : ℝ) ≤ 10 * l23c 4 by positivity)
  nlinarith

/-- **The chord bound of the coarsened child** is `O(2^g 2^(-g/5))`. -/
theorem FB_le : (FB g : ℝ) ≤ 18 * l23c 4 * ztwjl := by
  unfold FB
  zumje
  have hi := inv_gradeGran_le ztfe
  zuegy

  have hg1 : (g : ℝ) ≤ ((g - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast (by omega : g ≤ g - 1 + 1)
  have hsh : (2 : ℝ) ^ zthqb ≤ 2 * (2 : ℝ) ^ ztew := by
    have : (2 : ℝ) ^ zthqb ≤ (2 : ℝ) ^ (1 + -(g : ℝ) / 5) :=
      two_rpow_le_two_rpow by_linarith
    rwa [← two_rpow_mul_two_rpow, Real.rpow_one] at this
  zulnw

  calc (l23c 4 : ℝ) * ztlch * (1 / ((gradeGran ztfe : ℝ) + 1))
      ≤ (l23c 4 : ℝ) * ztlch * ztydm :=
        mul_le_mul_of_nonneg_left (hi.trans hsh) by_positivity
    _ ≤ (l23c 4 : ℝ) * (9 * (2 : ℝ) ^ g) * ztydm := by
        apply mul_le_mul_of_nonneg_right _ by_positivity
        zuldj

    _ = 18 * l23c 4 * ztwjl := by_ring
theorem FB_clog : Nat.clog 2 zthqz ≤ Nat.clog 2 ztmmb + g + 4 := by
  have h1 : FB g ≤ l23c 4 * ztgcj := Nat.div_le_self _ _
  have h2 := Nat.clog_mono_right 2 h1
  have h3 := MergeAsm.clog_mul_le ztmmb ztgcj
  have h4 : Nat.clog 2 ztgcj ≤ g + 4 := by
    zudwq
    grind
  omega

/-- **The coarsening term.** -/
theorem FB_term_le : ((FB g * ztzcj + 1 : ℕ) : ℝ) ≤
    ztbrt * Yg g := by
  have h := FB_le g
  have hc := FB_clog g
  zubkl

  have hF0 : (0 : ℝ) ≤ FB g := Nat.cast_nonneg _
  set a : ℝ := (Nat.clog 2 ztmmb : ℝ) with ha
  have ha0 : 0 ≤ a := Nat.cast_nonneg _
  have hc' : ((Nat.clog 2 zthqz : ℕ) : ℝ) + 1 ≤ a + g + 5 := by
    have : ((Nat.clog 2 zthqz : ℕ) : ℝ) ≤ ((Nat.clog 2 ztmmb + g + 4 : ℕ) : ℝ) := by
      exact_mod_cast hc
    grind
  push_cast
  have e1 : (FB g : ℝ) * ((Nat.clog 2 zthqz : ℝ) + 1) ≤ (FB g : ℝ) * ztgex :=
    mul_le_mul_of_nonneg_left hc' hF0
  have e2 : (FB g : ℝ) * ztgex ≤
      18 * l23c 4 * ztwjl * ztgex :=
    mul_le_mul_of_nonneg_right h by_linarith
  have e3 : 18 * (l23c 4 : ℝ) * ztwjl * ztgex =
      18 * l23c 4 * ((2 : ℝ) ^ g * ztwmr +
        ztnqo * ztwjl) := by_ring
  have e4 : (2 : ℝ) ^ g * ztwmr +
      ztnqo * ztwjl ≤ (a + 17) * Yg g := by
    have := mul_le_mul_of_nonneg_left hA (show (0 : ℝ) ≤ a + 5 by linarith)
    linarith
  have e5 := mul_le_mul_of_nonneg_left e4 (show (0 : ℝ) ≤ 18 * l23c 4 by positivity)
  nlinarith

/-- The cost of one chain, in natural numbers. -/
theorem stepB_le_nat (κO g : ℕ) :
    stepB κB κL κG κO g + 19 ≤ κB * 129 ^ 3 + κL * ztcnv +
      κG 4 * ztbyh + κO * ztxcf + 1993 := by
  unfold stepB nfB
  zus
  · have h1 : 2 ^ g ≤ 2 ^ 6 := Nat.pow_le_pow_right by_norm_num by_omega
    have h2 : ztelc ^ 3 ≤ 129 ^ 3 := Nat.pow_le_pow_left by_omega 3
    have h3 := Nat.mul_le_mul_left κB h2
    omega
  · omega

/-- **The cost of one chain of grade `g` is at most `K₁ · 2^g 2^(-g/76)`.** -/
theorem stepB_le (κO g : ℕ) :
    ((stepB κB κL κG κO g + 19 : ℕ) : ℝ) ≤ K1 κB κL κG κO * Yg g := by
  have h := stepB_le_nat κB κL κG κO g
  have h' : ((stepB κB κL κG κO g + 19 : ℕ) : ℝ) ≤ ((κB * 129 ^ 3 + κL * ztcnv +
      κG 4 * ztbyh + κO * ztxcf + 1993 : ℕ) : ℝ) := by
    exact_mod_cast h
  have hY := one_le_Yg g
  have hL := lemma41Nat_le g
  have hF := FB_term_le g
  have hN := NB_term_le g
  have hB0 : (0 : ℝ) ≤ κB := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ κL := Nat.cast_nonneg _
  have hG0 : (0 : ℝ) ≤ κG 4 := Nat.cast_nonneg _
  have hO0 : (0 : ℝ) ≤ κO := Nat.cast_nonneg _
  obtain ⟨Cc, hCc⟩ : ∃ Cc : ℝ, (34200 : ℝ) ^ 3 = Cc := zths
  rw [hCc] at hL
  have i1 : (κB : ℝ) * 129 ^ 3 ≤ κB * 129 ^ 3 * Yg g :=
    le_mul_of_one_le_right by_positivity hY
  have i2 : (κL : ℝ) * ((lemma41Nat g : ℝ) + 1) ≤ κL * ztjeu * Yg g := by
    have : (lemma41Nat g : ℝ) + 1 ≤ ztjeu * Yg g := by_linarith
    exact (mul_le_mul_of_nonneg_left this hL0).trans_eq by_ring
  have i3 : (κG 4 : ℝ) * ((FB g * ztzcj + 1 : ℕ) : ℝ) ≤
      κG 4 * ztbrt * Yg g := by
    zuogp; exact mul_le_mul_of_nonneg_left hF hG0
  have i4 : (κO : ℝ) * ((NB g * ztbs + 1 : ℕ) : ℝ) ≤ κO * ztffe * Yg g := by
    zuogp; exact mul_le_mul_of_nonneg_left hN hO0
  have i5 : (1993 : ℝ) ≤ 2000 * Yg g := by_linarith
  have hK : K1 κB κL κG κO * Yg g = κB * 129 ^ 3 * Yg g + κL * ztjeu * Yg g +
      κG 4 * ztbrt * Yg g +
      κO * ztffe * Yg g + 2000 * Yg g := by unfold K1; grind
  grind
end proofs
end
end Chazelle.Core.Up
namespace Chazelle.Core.Up
open Chazelle.Cost
@[expose] public section
section proofs
theorem sum_pow_two (m : ℕ) : ∑ g ∈ Finset.range m, 2 ^ g + 1 = 2 ^ m := by
  induction m with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, pow_succ]; omega
variable (κB κL : ℕ) (κG : ℕ → ℕ) (κO : ℕ)
theorem K1_nonneg : 0 ≤ K1 κB κL κG κO := by
  unfold K1; positivity

/-- **The cost of grade `g`.** -/
theorem gT_le (κO n g : ℕ) :
    (gT κB κL κG κO n g : ℝ) ≤
      K1 κB κL κG κO * ztwzd +
        (17 * g + 100) := by
  set S := stepB κB κL κG κO g with hS
  set cnt := gradeCount n g with hcnt
  have h1 : gT κB κL κG κO n g ≤ ztbzu * ztnov + 17 * g + 100 := by
    have e : ztbzu * ztnov = cnt * ztnov + S + 19 := by_ring
    have e2 : stepB κB κL κG κO g = S := hS.symm
    have e3 : gradeCount n g = cnt := hcnt.symm
    unfold gT gradeC; grind
  have h1' : (gT κB κL κG κO n g : ℝ) ≤ ztmyq * ztmyh + 17 * g + 100 := by
    exact_mod_cast h1
  have hSt := stepB_le κB κL κG κO g
  rw [← hS] at hSt; push_cast at hSt
  zujyq
  have hc : (cnt : ℝ) + 1 ≤ (n : ℝ) / (2 : ℝ) ^ g + 2 := by
    rw [hcnt]; unfold gradeCount
    have : ((zteud / 2 ^ g : ℕ) : ℝ) ≤ ((n - 2 : ℕ) : ℝ) / ((2 ^ g : ℕ) : ℝ) := Nat.cast_div_le
    have hn2 : ((n - 2 : ℕ) : ℝ) ≤ n := by_simp
    push_cast at this ⊢
    have : ((n - 2 : ℕ) : ℝ) / (2 : ℝ) ^ g ≤ (n : ℝ) / (2 : ℝ) ^ g :=
      div_le_div_of_nonneg_right hn2 h2g.le
    linarith
  have hK := K1_nonneg κB κL κG κO
  have hY := Yg_le g
  have hY0 := Yg_pos g
  have hS0 : (0 : ℝ) ≤ (S : ℝ) + 19 := by_positivity
  have hc0 : (0 : ℝ) ≤ (cnt : ℝ) + 1 := by_positivity
  have e : ztdej * Yg g =
      (n : ℝ) * (2 : ℝ) ^ ztls + 2 * Yg g := by
    unfold Yg; field_simp
  have i1 : ztmyq * ztmyh ≤ ztdej * ztmbk :=
    mul_le_mul hc hSt hS0 by_positivity
  have i2 : ztdej * ztmbk =
      K1 κB κL κG κO * ztxet := by
    grind
  have i3 : K1 κB κL κG κO * ztxet ≤
      K1 κB κL κG κO * ztwzd :=
    mul_le_mul_of_nonneg_left by_linarith hK
  linarith

/-- **All grades cost `O(n)`.** -/
theorem upT_le_real (κO n : ℕ) (hn : 2 ≤ n) :
    (upT κB κL κG κO n : ℝ) ≤ ztldl * n := by
  zufak
  set K := K1 κB κL κG κO with hK
  have hK0 : 0 ≤ K := K1_nonneg κB κL κG κO
  unfold upT
  rw [← hp]
  push_cast
  have hsum : ∑ g ∈ Finset.range ztr, (gT κB κL κG κO n g : ℝ) ≤
      K * n * ∑ g ∈ Finset.range ztr, (2 : ℝ) ^ ztls +
        K * 2 * ∑ g ∈ Finset.range ztr, (2 : ℝ) ^ g +
        ∑ g ∈ Finset.range ztr, ztdkh := by
    calc ∑ g ∈ Finset.range ztr, (gT κB κL κG κO n g : ℝ)
        ≤ ∑ g ∈ Finset.range ztr, (K * n * (2 : ℝ) ^ ztls +
            K * 2 * (2 : ℝ) ^ g + ztdkh) :=
          Finset.sum_le_sum fun g _ => by
            have := gT_le κB κL κG κO n g
            grind
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum,
            Finset.mul_sum]
  have hA : ∑ g ∈ Finset.range ztr, (2 : ℝ) ^ ztls ≤ 304 := by
    have := sum_two_rpow_neg_le 76 by_norm_num ztr; grind
  have hB : ∑ g ∈ Finset.range ztr, (2 : ℝ) ^ g ≤ 4 * n := by
    have h1 := sum_pow_two ztr
    have h2 := two_pow_le_of_le_top hn ztzgj
    rw [← hp] at h2
    have h3 : ∑ g ∈ Finset.range ztr, 2 ^ g ≤ 4 * n := by_omega
    exact_mod_cast h3
  have hC : ∑ g ∈ Finset.range ztr, ztdkh ≤ 3200 * n := by
    have h1 : ∀ g ∈ Finset.range ztr, ztdkh ≤ 17 * p + 100 := fun g hg => by
      simp_all
    have h2 := Finset.sum_le_sum h1
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
    have h3 : ztr * ztpsy ≤ 100 * ztdhu ^ 2 := by ring_nf; omega
    have h4 := sq_le_two_pow p
    have h5 := two_pow_le_of_le_top hn ztzgj
    rw [← hp] at h5
    have h6 : ztr * ztpsy ≤ 3200 * n := by_omega
    have h7 : ((p + 1 : ℕ) : ℝ) * (17 * (p : ℝ) + 100) ≤ 3200 * n := by exact_mod_cast h6
    grind
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have i1 := mul_le_mul_of_nonneg_left hA (show 0 ≤ K * (n : ℝ) by positivity)
  have i2 : K * 2 * ∑ g ∈ Finset.range ztr, (2 : ℝ) ^ g ≤ 8 * (K * n) := by
    have := mul_le_mul_of_nonneg_left hB (show 0 ≤ K * 2 by positivity)
    grind
  grind

/-- **All grades cost `O(n)`** (natural-number form). -/
theorem upT_le :
    ∃ K : ℕ, ∀ n, 2 ≤ n → upT κB κL κG κO n ≤ K * n := by
  refine ⟨⌈312 * K1 κB κL κG κO + 3200⌉₊, fun n hn => ?_⟩
  have h := upT_le_real κB κL κG κO n hn
  have h2 : ztldl * (n : ℝ) ≤ (⌈312 * K1 κB κL κG κO + 3200⌉₊ : ℝ) * n :=
    mul_le_mul_of_nonneg_right ztvag ztqam
  exact_mod_cast h.trans h2
end proofs
end
end Chazelle.Core.Up
namespace Chazelle.Core.Up
open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41
@[expose] public section
def outS : Stmt := block [.copyN 230001 170005, .addN 170053 170014 170020, .loadN 230002 170053]

/-- **The up phase.** -/
def upS (sB sL sG sP : Stmt) : Stmt :=
  .seq initA (.seq halfS (.seq initH (.seq initR (.seq (gradesL sB sL sG sP) outS))))
section proofs
variable {O : OracleIface}
theorem gradeGran_zero : gradeGran 0 = 1 := by
  unfold gradeGran Cost.ceilBeta; simp
set_option maxHeartbeats 16000000 in
theorem outS_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {h R : ℕ}
    (h05 : c.nreg 170005 = h) (h14 : c.nreg 170014 = R) (h20 : c.nreg 170020 = 1)
    (hWR : R + 1 ≤ W) :
    ∃ c' k, Exec P W outS c c' k ∧ k = 3 ∧ WordsBounded W c' ∧
      c'.nreg 230001 = h ∧ c'.nreg 230002 = c.nmem ztza ∧
      (∀ r, r ≠ 230001 → r ≠ 230002 → r ≠ 170053 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zumtv
  exec_block
  all_goals try (config_simp; (try simp only [h05, h14, h20]); omega)
  simp_all
set_option maxHeartbeats 64000000 in
set_option maxRecDepth 8192 in
/-- **WP-J: the up phase meets its contract.** -/
theorem upPhase_of (hV : O.Valid) (hL41 : Lemma41Spec O) (hBr : BruteSpec) :
    UpPhaseSpec ztsy := by
  obtain ⟨sL, κL, hL⟩ := hL41
  obtain ⟨sB, κB, hB⟩ := hBr
  zugqt
  obtain ⟨K, hK⟩ := upT_le κB κL κG O.κ
  have hB' : BruteM sB κB := by_tauto
  have hL' : L41M O sL κL := by_tauto
  have hGr' : GranM sG κG := by_tauto
  clear hB hL hGr
  refine ⟨upS sB sL sG O.prep, K + 300, fun P W c hw ⟨hG, hWn3, hSet⟩ hbud => ?_⟩
  zuk
  zucgu
  have hn : ztmss := by_omega
  obtain ⟨A0, hA0⟩ : ztprc := by_simp_all
  obtain ⟨S, hS0⟩ : ∃ S, c.nreg (coreReg 0) = S := by_simp_all
  rw [hA0, hS0] at hSet
  have hbud' : A0 + (K * P.n + K + 300 * P.n + 300) ≤ W := by
    grind
  have hWh : ztuum := by unfold hostWords; omega
  obtain ⟨sS0, sS1, sST, sSA⟩ := hSet.holds
  have h230 := hS0
  -- initA
  obtain ⟨c1, k1, e1, hk1, hw1, i20, i21, i22, i23, i25, i26, i29, i37, i00, i01, i02, i06, i28,
      fr1, hm1, hrr1, hrm1, ho1⟩ :=
    initA_exec (P := P) hw h230 sS1 by_omega by_omega by_omega by_omega
  have hA1 : ztupc := by
    rw [fr1 _ by_decide]; omega
  -- halfS
  obtain ⟨c2, k2, e2, hk2, hw2, j03, a21, a22, a23, hHalf, hm2, fr2, hrr2, hrm2, ho2⟩ :=
    halfS_exec (P := P) hw1 hA1 i01 i20 i21 by_omega
  obtain ⟨A2, hA2⟩ : ∃ A2, c2.nreg ALLOC = A2 := by_grind
  rw [hA2] at a21 a22 a23
  -- initH
  obtain ⟨c3, k3, e3, hk3, hw3, A3e, j04, hH3, hm3, fr3, hrr3, hrm3, ho3⟩ :=
    initH_exec (P := P) hw2 hA2 by_omega by_omega by_omega by_omega
  have u3 : ∀ r, 170000 ≤ r → r < 170080 → ¬ HalfRG r → r ≠ 170004 →
      c3.nreg r = c1.nreg r := fun r a b h1 h2 => by
    rw [fr3 r ztozk h2 by_omega,
      fr2 r h1 by_omega]
  -- initR
  obtain ⟨c4, k4, e4, hk4, hw4, r05, A4e, w0, w1, w2, w3, r07, r08, r09, r10, r11, r12, r14, r19,
      r15, r16, r35, r36, mw4, fr4, hrr4, hrm4, ho4⟩ :=
    initR_exec (P := P) (S := S) (D := A0) (n1 := P.n - 1) hw3 A3e
      ztwlc
      (by rw [fr3 _ by_decide by_omega by_omega]; omega)
      ztwlc
      ztwlc
      ztwlc
      ztwlc
      ztwlc
      ztwlc
      by_omega by_omega
  have u4 : ∀ r, 170000 ≤ r → r < 170080 → ¬ HalfRG r → r ≠ 170004 → ¬ InitRRG r →
      c4.nreg r = c1.nreg r := fun r a b h1 h2 h3 => by
    rw [fr4 r h3 by_omega, u3 r a b h1 h2]
  have U : ∀ r, 170000 ≤ r → r < 170080 → ¬ HalfRG r → r ≠ 170004 → ¬ InitRRG r →
      ∀ v, c1.nreg r = v → c4.nreg r = v := fun r a b h1 h2 h3 v hv => (u4 r a b h1 h2 h3).trans hv
  -- the grade invariant at grade `0`
  have hI4 : GradeInv O P c4 0 (A2 + 7) A2 0 S A0 := by
    refine ⟨⟨U _ by_omega by_omega ztlj by_omega
        ztvm _ i01,
      by rw [fr4 _ ztvm by_omega]; omega, r05, r07,
      by rw [r08]; unfold gradeCount; omega, by_omega,
      by rw [r11, gradeGran_zero], by zupax; unfold gradeCount; omega, r14,
      by omega,
      U _ by_omega by_omega ztlj by_omega ztvm _ i20,
      U _ by_omega by_omega ztlj by_omega ztvm _ i21,
      U _ by_omega by_omega ztlj by_omega ztvm _ i22,
      U _ by_omega by_omega ztlj by_omega ztvm _ i23,
      U _ by_omega by_omega ztlj by_omega ztvm _ i25,
      U _ by_omega by_omega ztlj by_omega ztvm _ i26,
      U _ by_omega by_omega ztlj by_omega ztvm _ i28,
      U _ by_omega by_omega ztlj by_omega ztvm _ i29,
      U _ by_omega by_omega ztlj by_omega ztvm _ i37⟩,
      U _ by_omega by_omega ztlj by_omega ztvm _ i00,
      U _ by_omega by_omega ztlj by_omega ztvm _ i02,
      by rw [fr4 _ ztvm by_omega,
        fr3 _ by_decide by_omega by_omega]; omega,
      U _ by_omega by_omega ztlj by_omega ztvm _ i06,
      by omega, r15, r16, r35, r36, ?_⟩
    rw [A4e]
    zucng
    have m4 := fun a ha =>
      (hm a by_omega).trans (mw4 a ztbbu)
    have m3 := fun a ha =>
      (m4 a by_omega).trans (hm3 a ztbbu)
    have m0 : ∀ a, a < A0 → m a = c.nmem a := fun a ha => by
      rw [m3 a by_omega, hm2 a ha, hm1]
    have e0 : ztdbk := (hm _ by_omega).trans w0
    have e1 : m _ = S := (hm _ by_omega).trans w1
    have e2 : m _ = A2 + 7 + 4 := (hm _ by_omega).trans w2
    have e3 : m _ = A0 := (hm _ by_omega).trans w3
    obtain ⟨t0, t1, t2, t3⟩ := hSet m (fun a ha => m0 a ha)
    refine ⟨⟨by_omega, by zvmxy; exact ⟨t0, t1, t2, le_refl _⟩,
      fun x hx => by rw [e3, m3 _ by_omega]; exact hHalf x hx,
      L41.hostAt_agree hH3 rfl by_omega m4, by_omega,
      ⟨by_omega, by_grind, by_grind⟩, by_omega,
      by grind,
      by grind⟩,
      e0, by_grind, e1, e3⟩
  -- all grades
  have hup := hK P.n hn
  obtain ⟨c5, k5, h', R', e5, hk5, hw5, a51, a52, hI5, m5, rm5, o5, f5, ff5⟩ :=
    gradesL_exec (O := O) hB' hL' hGr' hV hG hWh hn hw4 hI4 by_omega
  obtain ⟨hu5, x00, x02, x03, x06, x09, x15, x16, x35, x36, hM5⟩ := hI5
  obtain ⟨hT5, hmh5, hR5, -, -⟩ := hM5.holds
  have hR5' := hR5 by_omega
  rw [show topGrade P.n + 1 - 1 = topGrade P.n by omega] at hR5'
  have hc1 : 0 < gradeCount P.n ztcdz := by rw [gradeCount_top hn]; omega
  have hrow := hT5.2.2.2.2.2.2.2.1 ztcdz by_omega
  rw [hR5'] at hrow
  -- the outputs
  obtain ⟨c6, k6, e6, hk6, hw6, o1, o2, fr6, hm6, hrr6, hrm6, ho6⟩ :=
    outS_exec (P := P) hw5 hu5.r05 hu5.r14 hu5.r20 by_omega
  have hA6 : c6.nreg ALLOC = c5.nreg ALLOC := fr6 _ by_omega by_omega
    by_omega
  -- the frame of the phase
  have hout : ∀ r, bandOf r ∉ phaseBands → r ≠ ALLOC → c6.nreg r = c.nreg r := by
    zucxf
    have hb : OutB ztmcq := by
      zucun

    have hr : r < 10000 ∨ 250000 ≤ r := by unfold OutB bandOf at hb; omega
    rw [fr6 r by_omega by_omega by_omega, f5 r ztzz,
      fr4 r ztvm h2, fr3 r ztozk by_omega h2,
      fr2 r ztlj h2, fr1 r ztiiw]
  have hkeep : c6.nreg ztcpu = c.nreg ztcpu := by
    show c6.nreg 230000 = c.nreg 230000
    rw [fr6 _ by_omega by_omega by_omega,
      f5 _ ztec,
      fr4 _ ztvm by_omega,
      fr3 _ by_decide by_omega by_omega,
      fr2 _ ztlj by_omega, fr1 _ by_decide]
  have mem5 : ∀ a, a < A0 → c5.nmem a = c.nmem a := fun a ha => by
    rw [m5 a by_omega, mw4 a by_grind, hm3 a by_grind,
      hm2 a ha, hm1]
  refine ⟨c6, k1 + ztrd,
    .seq e1 ztvb, ?_, ztfh, ?_⟩
  · grind
  · zug
    simp only [Finset.mem_singleton] at hi
    grind
  · show (gradeCtx O).holds P c6.nmem ztvko _
    rw [hm6, o1, hA6]
    exact holds_of_upTab hn (robust_of hM5 le_rfl fun m h => h.1)
  · show P.n - 1 ≤ 2 ^ (c6.nmem ztvko - 1)
    rw [hm6, o1, hmh5, show topGrade P.n + 1 - 1 = topGrade P.n by omega]
    exact Nat.le_pow_clog by_norm_num _
  · obtain ⟨hN, -⟩ := hT5.2.2.2.2.2.2.2.2 _ 0 by_omega hc1
    simp only [rowE, hR5', Nat.mul_zero, Nat.add_zero] at hN
    let C0 := gChain P _ 0 hn hc1
    obtain ⟨-, -, -, -, -, -, N, hNW, hc⟩ := hN C0 rfl rfl rfl
    refine ⟨C0, N, ⟨rfl, by show gradeStart _ 0 = 0; unfold gradeStart; simp,
      by show gradeLen P.n _ 0 + 1 = P.n; rw [gradeLen_top hn]; omega⟩, ?_, hc⟩
    show Robust _ c6.nmem fun m => NFAt m (c6.nreg 230002) N
    rw [hm6, o2, hA6]; exact hNW
  · refine ⟨hout, fun r h1 => ?_, fun a ha => by rw [hm6, mem5 a by_omega],
      fun a ha => ?_, by_grind, by_omega, by_omega⟩
    · have hb : OutB ztmcq := by
        zucun

      rw [hrr6, ff5 r hb, hrr4, hrr3, hrr2, hrr1]
    · rw [hrm6, rm5 a by_omega, hrm4, hrm3, hrm2, hrm1]

/-- **WP-J** with Lemma 4.1 from `MergeSpec` and `ShootCutSpec O`. -/
theorem upPhase_of' (hM : MergeSpec) (hV : O.Valid) (hSC : ShootCutSpec O) (hBr : BruteSpec) :
    UpPhaseSpec ztsy :=
  upPhase_of hV (lemma41_of O hM hSC) hBr
end proofs
end
end Chazelle.Core.Up
namespace Chazelle.Core
namespace DrvG
open Chazelle.Cost L41
@[expose] public section
def mcost (κM : ℕ) (F G H : ℕ → ℕ) (x y γ M : ℕ) : ℕ :=
  κM * ztcwy * F ztcbh * G ztcbh *
    ztxgb

/-- The constant of `mcost_le`. -/
def mcK (κM κ : ℕ) : ℕ := κM * κ ^ 2 * 14704 * 3 * 19368 * 121 * 8192 * 2236081 + 1
variable (μ : ℕ) (κM κ : ℕ)
theorem ceilBeta_add_65 : ceilBeta μ + 13 ≤ ceilBeta ztfvr := by
  unfold ceilBeta
  rw [beta_eq]
  have e : (1 / 5 : ℝ) * ((μ + 65 : ℕ) : ℝ) = (1 / 5 : ℝ) * μ + (13 : ℕ) := by_grind
  rw [e, Nat.ceil_add_natCast by_positivity]

/-- The granularity of the merges is served at grade `μ + 65`. -/
theorem gamma_le_gradeGran {μ γ₀ γ : ℕ} (hg1 : γ₀ ≤ 4096 * 2 ^ ceilBeta μ) (hγ : γ ≤ γ₀ + 128) :
    γ + fuseLoss ≤ gradeGran ztfvr := by
  have h1 : 2 ^ (ceilBeta μ + 13) ≤ 2 ^ ceilBeta ztfvr :=
    Nat.pow_le_pow_right by_norm_num (ceilBeta_add_65 μ)
  have h2 : 2 ^ ceilBeta ztfvr ≤ gradeGran ztfvr := by unfold gradeGran; omega
  have h3 : 1 ≤ 2 ^ ceilBeta μ := Nat.one_le_two_pow
  rw [pow_add] at h1
  unfold fuseLoss
  omega
theorem M_le_pow {μ M : ℕ} (hM : M ≤ 20 * ztgye) : M ≤ 2 ^ ztfvr := by
  grind

/-- The oracle factors of one merge are at most those of grade `μ + 65`. -/
theorem mcost_le_phiL {μ γ₀ γ M x y : ℕ} (hg1 : γ₀ ≤ 4096 * 2 ^ ceilBeta μ)
    (hγ : γ ≤ γ₀ + 128) :
    mcost κM ztbon ztboo cutGran x y γ M ≤
      ztcwy * phiL ztbdd ztbon ztboo cutGran ztbgc M := by
  have hg := gamma_le_gradeGran hg1 hγ
  have hF := scF_mono κ hg
  have hG := scG_mono κ hg
  have hH := cutGran_mono hg
  unfold mcost phiL
  calc κM * ztcwy * scF κ ztcbh * scG κ ztcbh *
        (cutGran ztcbh + Nat.clog 2 ztdti + 1)
      ≤ κM * ztcwy * scF κ ztbgc * scG κ ztbgc *
        ztyix := by gcongr
    _ = ztcwy * (κM * scF κ ztbgc * scG κ ztbgc *
        ztyix) := by_ring

/-- `E^75 = 2^μ`. -/
theorem E_pow_75 : ((2 : ℝ) ^ ztgwm) ^ 75 = (2 : ℝ) ^ μ := by
  rw [E_pow, ← Real.rpow_natCast]; simp

/-- **The cost of one merge of the region chain is `O(lemma41Nat μ)`.** -/
theorem mcost_le {μ γ₀ γ M x y : ℕ} (h7 : 7 ≤ μ) (hg0 : 2 * gradeGran μ ≤ γ₀)
    (hg1 : γ₀ ≤ 4096 * 2 ^ ceilBeta μ) (hγ : γ ≤ γ₀ + 128) (hM : M ≤ 20 * ztgye)
    (hx : x * ztbfd ≤ 18480 * ztpts) (hy : y * ztbfd ≤ 18480 * ztpts) :
    mcost κM ztbon ztboo cutGran x y γ M ≤ mcK κM κ * lemma41Nat μ := by
  have h1 := mcost_le_phiL κM κ (x := x) (y := y) (M := M) hg1 hγ
  have hφ := phiL_le κM κ (lam := μ + 65) (L := M) by_omega (M_le_pow hM)
  set E := (2 : ℝ) ^ ztgwm with hE
  have hE1 : 1 ≤ E := one_le_E μ
  -- `E' ^ 14 ≤ 2^13 E^14`
  have hE' : ztfar ^ 14 ≤ 8192 * E ^ 14 := by
    rw [E_pow, hE, E_pow]
    have : (2 : ℝ) ^ ((14 : ℕ) * ((μ + 65 : ℕ) : ℝ) / 75) =
        (2 : ℝ) ^ ztmxx * (2 : ℝ) ^ ztiew := by
      zuojc; grind
    zubk
    have h13 : (2 : ℝ) ^ ztmxx ≤ (2 : ℝ) ^ (13 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le by_norm_num by_norm_num
    have h13' : ztixb := by_norm_num
    rw [h13'] at h13
    have : (0 : ℝ) ≤ (2 : ℝ) ^ ztiew := by_positivity
    nlinarith
  -- `(μ + 65)² ≤ 121 μ²`
  have hμ : ztjca ^ 2 ≤ 121 * (μ : ℝ) ^ 2 := by
    have : (7 : ℝ) ≤ μ := by_simp_all
    push_cast; nlinarith
  -- the chords
  have hgg : (2 : ℝ) ^ ceilBeta μ ≤ gradeGran μ := by
    have : 2 ^ ceilBeta μ ≤ gradeGran μ := by unfold gradeGran; omega
    zufc
  have hcb : (2 : ℝ) ^ ztmzx ≤ (2 : ℝ) ^ ceilBeta μ := by
    rw [← Real.rpow_natCast]
    zuldb
    have := le_ceilBeta_real μ; linarith
  have hE15 : E ^ 15 = (2 : ℝ) ^ ztmzx := by
    zuecz
  have hγ₀ : 2 * E ^ 15 ≤ (γ₀ : ℝ) + 1 := by
    have : (2 * gradeGran μ : ℝ) ≤ γ₀ := by exact_mod_cast hg0
    grind
  have hM2 : 2 * (M : ℝ) + 1 ≤ 121 * E ^ 75 := by
    rw [E_pow_75]
    have : (M : ℝ) ≤ 20 * ztgye := by exact_mod_cast hM
    have : (1 : ℝ) ≤ 2 ^ μ := one_le_pow₀ by_norm_num
    linarith
  have hxyR : ((x + y + 1 : ℕ) : ℝ) * ztbjb ≤ 36960 * ztpst + ztbjb := by
    have hx' : (x : ℝ) * ztbjb ≤ 18480 * ztldi := by exact_mod_cast hx
    have hy' : (y : ℝ) * ztbjb ≤ 18480 * ztldi := by exact_mod_cast hy
    grind
  have hxy : ((x + y + 1 : ℕ) : ℝ) ≤ 2236081 * E ^ 60 := by
    have hg0' : (0 : ℝ) < (γ₀ : ℝ) + 1 := by_positivity
    have e75 : E ^ 75 = E ^ 15 * E ^ 60 := by_grind
    have hE60 : 1 ≤ E ^ 60 := one_le_pow₀ hE1
    have hE60p : ztrzt := by_positivity
    have hb : ((x + y + 1 : ℕ) : ℝ) * ztbjb ≤
        ztpua * ztbjb := by
      have a1 : 36960 * ztpst ≤ 2236080 * E ^ 60 * ztbjb := by
        rw [e75]
        have : 2 * E ^ 15 * E ^ 60 ≤ ztbjb * E ^ 60 :=
          mul_le_mul_of_nonneg_right hγ₀ hE60p
        nlinarith
      have a2 : (γ₀ : ℝ) + 1 ≤ E ^ 60 * ztbjb := by_nlinarith
      nlinarith
    exact le_of_mul_le_mul_right hb hg0'
  -- lemma41Nat
  have hN : (μ : ℝ) ^ 2 * E ^ 74 ≤ lemma41Nat μ := by
    unfold lemma41Nat
    have e : E ^ 74 = (2 : ℝ) ^ ztbah := by
      zuecz
    zui
    calc (μ : ℝ) ^ 2 * (2 : ℝ) ^ ztbah
        ≤ (μ : ℝ) ^ 2 * ztflr * (2 : ℝ) ^ ztbah := by
          have : (0 : ℝ) ≤ (μ : ℝ) ^ 2 * (2 : ℝ) ^ ztbah := by_positivity
          have : (0 : ℝ) ≤ (Nat.clog 2 μ : ℝ) := Nat.cast_nonneg _
          nlinarith
      _ ≤ _ := Nat.le_ceil _
  -- assemble
  zuckg
  have hK1p : 0 ≤ K1 := by_positivity
  have hφ' : (phiL ztbdd ztbon ztboo cutGran ztbgc M : ℝ) ≤
      K1 * ztfmq * ztjgf := by
    calc _ ≤ K1 * ztjca ^ 2 * ztfar ^ 14 := hφ
      _ ≤ K1 * ztfmq * ztjgf := by gcongr
  have hmain : (mcost κM ztbon ztboo cutGran x y γ M : ℝ) ≤
      zthay * ztejk := by
    have h1R : (mcost κM ztbon ztboo cutGran x y γ M : ℝ) ≤
        ((x + y + 1 : ℕ) : ℝ) *
          (phiL ztbdd ztbon ztboo cutGran ztbgc M : ℝ) := by
      exact_mod_cast h1
    have hp0 : (0 : ℝ) ≤ (phiL ztbdd ztbon ztboo cutGran ztbgc M : ℝ) :=
      Nat.cast_nonneg _
    calc _ ≤ ((x + y + 1 : ℕ) : ℝ) *
          (phiL ztbdd ztbon ztboo cutGran ztbgc M : ℝ) := h1R
      _ ≤ ztpua * (K1 * ztfmq * ztjgf) :=
          mul_le_mul hxy hφ' hp0 by_positivity
      _ = zthay * ztejk := by_ring
  have hfin : (mcost κM ztbon ztboo cutGran x y γ M : ℝ) ≤
      ((mcK κM κ * lemma41Nat μ : ℕ) : ℝ) := by
    have hKK : K1 * 121 * 8192 * 2236081 ≤ (mcK κM κ : ℝ) := by
      unfold mcK; grind
    have h0 : (0 : ℝ) ≤ (μ : ℝ) ^ 2 * E ^ 74 := by_positivity
    push_cast
    calc _ ≤ zthay * ztejk := hmain
      _ ≤ (mcK κM κ : ℝ) * (lemma41Nat μ : ℝ) := mul_le_mul hKK hN h0 ztdlc
  exact_mod_cast hfin
end
end DrvG
end Chazelle.Core
namespace Chazelle.Core
namespace DrvLC
open Chazelle.Cost L41
@[expose] public section
theorem five_ceilBeta_le (g : ℕ) : 5 * Cost.ceilBeta g ≤ g + 5 := by
  have h := L41.ceilBeta_le_real g
  have : ((5 * Cost.ceilBeta g : ℕ) : ℝ) ≤ ((g + 5 : ℕ) : ℝ) := by_grind
  zufc

/-- **(a)** The levels' size threshold. -/
theorem lv_n0 : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → 2 ^ ztydt + 200 ≤ n := by
  refine ⟨2 ^ 30 + 2, fun n hn => ?_⟩
  zuhrf
  set p := Nat.clog 2 _ with hp
  have hp30 : 30 ≤ p := by
    zubq

    have h1 : ztppe := Nat.le_pow_clog by_norm_num _
    have h2 : 2 ^ p ≤ 2 ^ 29 := Nat.pow_le_pow_right by_norm_num by_omega
    grind
  have hlt : 2 ^ ztoq < n - 1 := by
    have := Nat.pow_pred_clog_lt_self (b := 2) by_norm_num (x := n - 1)
      by_omega
    omega
  have hcb := five_ceilBeta_le p
  have h1 : 2 ^ (Cost.ceilBeta p + 13) ≤ 2 ^ ztftr :=
    Nat.pow_le_pow_right by_norm_num by_omega
  have h2 : 200 ≤ 2 ^ ztftr := by
    grind
  have h3 : 2 ^ ztoq = 2 * 2 ^ ztftr := by
    zufac
  omega

/-! ## Bounds in `E = 2^(μ/75)` -/

/-- `E = 2^(μ/75)`. -/
noncomputable def E (μ : ℕ) : ℝ := (2 : ℝ) ^ ztgwm
variable (μ : ℕ) (κo : ℕ)
theorem E_pos : 0 < E μ := by unfold E; positivity
theorem E_one_le : 1 ≤ E μ := by unfold E; exact L41.one_le_E μ
theorem E_pow_nonneg (μ k : ℕ) : 0 ≤ E μ ^ k := pow_nonneg (E_pos μ).le k
theorem E_pow_ge {μ a b : ℕ} (h : a ≤ b) : E μ ^ a ≤ E μ ^ b := pow_le_pow_right₀ ztpxp h

/-- `lemma41Nat μ ≥ μ² E^74`. -/
theorem lemma41Nat_ge : (μ : ℝ) ^ 2 * E μ ^ 74 ≤ (lemma41Nat μ : ℝ) := by
  have h := Nat.le_ceil ((μ : ℝ) ^ 2 * ztflr * (2 : ℝ) ^ ztbah)
  have hE : E μ ^ 74 = (2 : ℝ) ^ ztbah := by
    unfold E; rw [L41.E_pow]; grind
  have hc : (0 : ℝ) ≤ (Nat.clog 2 μ : ℕ) := Nat.cast_nonneg _
  have hp : (0 : ℝ) ≤ (2 : ℝ) ^ ztbah := by_positivity
  have hm : (0 : ℝ) ≤ (μ : ℝ) ^ 2 := by_positivity
  unfold lemma41Nat
  zugun
  calc (μ : ℝ) ^ 2 * (2 : ℝ) ^ ztbah
      ≤ (μ : ℝ) ^ 2 * ztflr * (2 : ℝ) ^ ztbah := by
        apply mul_le_mul_of_nonneg_right _ hp
        nlinarith
    _ ≤ _ := h

/-- `2^μ = E^75`. -/
theorem two_pow_eq_E : (2 : ℝ) ^ μ = E μ ^ 75 := by
  unfold E; zuodq; simp

/-- `E^15 ≤ 2^⌈βμ⌉`. -/
theorem E15_le : E μ ^ 15 ≤ (2 : ℝ) ^ Cost.ceilBeta μ := by
  unfold E; zuodq
  zuldb
  have := L41.le_ceilBeta_real μ
  grind
theorem regCap_eq : DrvR.regCap = 130 := rfl

/-- The chord bound times its denominator. -/
theorem lvNch_mul :
    DrvR.lvNch μ * ztwtk ≤ 18480 * ztdey := by
  unfold DrvR.lvNch
  rw [regCap_eq]
  exact Nat.div_mul_le_self _ _

/-- `lvNch μ ≤ 223 · 2^μ`. -/
theorem lvNch_le_pow : DrvR.lvNch μ ≤ 223 * 2 ^ μ := by
  zulhh
  have h1 : 3072 ≤ 3 * 2 ^ ztblx + 1 := by
    grind
  have h2 : DrvR.lvNch μ * 3072 ≤ DrvR.lvNch μ * ztwtk :=
    Nat.mul_le_mul_left _ h1
  grind

/-- `lvNch μ ≤ 223 E^60`. -/
theorem lvNch_le_E : (DrvR.lvNch μ : ℝ) ≤ 223 * E μ ^ 60 := by
  zulhh
  have hR : (DrvR.lvNch μ : ℝ) * (3072 * (2 : ℝ) ^ Cost.ceilBeta μ) ≤ 683760 * (2 : ℝ) ^ μ := by
    have h' : ((DrvR.lvNch μ * ztwtk : ℕ) : ℝ) ≤
        ((18480 * ztdey : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ μ := one_le_pow₀ by_norm_num
    have e10 : (2 : ℝ) ^ ztblx = 1024 * (2 : ℝ) ^ Cost.ceilBeta μ := by
      grind
    rw [e10] at h'
    grind
  have h15 := E15_le μ
  have hL : (0 : ℝ) ≤ (DrvR.lvNch μ : ℝ) := Nat.cast_nonneg _
  have hEp := pow_pos (E_pos μ) 15
  rw [two_pow_eq_E μ] at hR
  have h1 : (DrvR.lvNch μ : ℝ) * (3072 * E μ ^ 15) ≤ 683760 * E μ ^ 75 :=
    le_trans (mul_le_mul_of_nonneg_left by_linarith hL) hR
  have e75 : E μ ^ 75 = E μ ^ 15 * E μ ^ 60 := by_grind
  rw [e75] at h1
  have h2 : (DrvR.lvNch μ : ℝ) * 3072 ≤ 683760 * E μ ^ 60 := by
    have : E μ ^ 15 * ((DrvR.lvNch μ : ℝ) * 3072) ≤ E μ ^ 15 * (683760 * E μ ^ 60) := by
      nlinarith
    simp_all
  grind

/-! ## The oracle costs at `γ_r = lvGr μ` -/
theorem lvGr_clog : Nat.clog 2 ztbbn = Cost.ceilBeta μ + 12 := by
  unfold DrvR.lvGr; simp
theorem lvGr_clog_le {μ : ℕ} (h : 15 ≤ μ) : Nat.clog 2 ztbbn + 1 ≤ 2 * μ := by
  zuovo; have := five_ceilBeta_le μ; omega
theorem ceilBeta_real : (Cost.ceilBeta μ : ℝ) ≤ (μ : ℝ) / 5 + 1 := L41.ceilBeta_le_real μ

/-- `γ_r ≤ 8192 E^15`. -/
theorem lvGr_le_E : (DrvR.lvGr μ : ℝ) ≤ 8192 * E μ ^ 15 := by
  have h := L41.two_pow_le_E (n := Cost.ceilBeta μ + 12) (lam := μ) (k := 15) (b := 13)
    (by have := ceilBeta_real μ; grind)
  have h13 : ztixb := by_norm_num
  rw [h13] at h
  unfold DrvR.lvGr E; grind

/-- `H(γ_r) ≤ 19216 E^3`. -/
theorem cutGran_lvGr_le : (cutGran ztbbn : ℝ) ≤ 19216 * E μ ^ 3 := by
  unfold cutGran
  zuovo
  have h1 := gradeGran_le_real ztfni
  have h2 := L41.two_pow_le_E (n := Cost.ceilBeta ztfni) (lam := μ) (k := 3)
    (b := 4) (by
      have a1 := ceilBeta_real ztfni
      have a2 := ceilBeta_real μ
      grind)
  have h16 : (2 : ℝ) ^ (4 : ℝ) = 16 := by_norm_num
  rw [h16] at h2
  unfold E
  linarith

/-- `⌈(H(γ_r) (γ_r + 1)²)^{1/3}⌉ ≤ 11001 E^11`. -/
theorem rpow_lvGr_le :
    (rpowCeil ztxqv ztby : ℝ) ≤
      11001 * E μ ^ 11 := by
  have hE1 := E_one_le μ
  zulhy
  have hG := lvGr_le_E μ
  have hG1 : ((DrvR.lvGr μ : ℕ) : ℝ) + 1 ≤ 8193 * E μ ^ 15 := by
    have : (1 : ℝ) ≤ E μ ^ 15 := one_le_pow₀ hE1
    linarith
  obtain ⟨X, hX⟩ : ∃ X, cutGran (DrvR.lvGr μ) * (DrvR.lvGr μ + 1) ^ 2 = X := by_grind
  obtain ⟨Hc, hHc⟩ : ∃ Hc, (cutGran (DrvR.lvGr μ) : ℝ) = Hc := by_grind
  obtain ⟨G, hGG⟩ : ∃ G, (DrvR.lvGr μ : ℝ) = G := by_grind
  have hXc : (X : ℝ) = Hc * ztsxr ^ 2 := by rw [← hX, ← hHc, ← hGG]; grind
  rw [hHc] at hH
  rw [hGG] at hG1
  zuexv
  have hG0 : (0 : ℝ) ≤ G + 1 := by
    grind
  have hH0 : (0 : ℝ) ≤ Hc := by_grind
  have hXR : (X : ℝ) ≤ ztigr ^ 3 := by
    rw [hXc]
    calc Hc * ztsxr ^ 2
        ≤ (19216 * E μ ^ 3) * (8193 * E μ ^ 15) ^ 2 := by
          apply mul_le_mul hH (pow_le_pow_left₀ hG0 hG1 2) (pow_nonneg hG0 2)
            by_grind
      _ ≤ ztigr ^ 3 := by
          have  := E_pow_nonneg μ 33
          grind
  have hroot : (X : ℝ) ^ ztby ≤ 11000 * E μ ^ 11 := by
    have h0 : (0 : ℝ) ≤ 11000 * E μ ^ 11 := by_positivity
    calc (X : ℝ) ^ ztby ≤ (ztigr ^ 3) ^ ztby :=
          Real.rpow_le_rpow ztdlc hXR by_norm_num
      _ = 11000 * E μ ^ 11 := by
          zucqh
  zujqv

  have : ztlwu := one_le_pow₀ hE1
  linarith

/-- `F(γ_r) ≤ 22003 κo μ E^11`. -/
theorem shCost_lvGr_le {μ : ℕ} (h : 15 ≤ μ) :
    (DrvR.shCost κo ztbbn : ℝ) ≤ 22003 * κo * μ * E μ ^ 11 := by
  unfold DrvR.shCost
  have hc : ztwtb := by
    zulfz
  have hR := rpow_lvGr_le μ
  zuizw
  have hμ : ztpgn := by exact_mod_cast h
  have hE : ztlwu := one_le_pow₀ ztpxp
  have hc0 : (0 : ℝ) ≤ ((Nat.clog 2 ztbbn + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hR0 : (0 : ℝ) ≤ (rpowCeil ztxqv
    ztby : ℝ) := Nat.cast_nonneg _
  push_cast at hc hc0 ⊢
  have h1 : (κo : ℝ) * ((Nat.clog 2 ztbbn : ℝ) + 1) *
      (rpowCeil ztxqv ztby : ℝ) ≤
      κo * ztnfg * (11001 * E μ ^ 11) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left hc hκ) hR hR0 (by
      positivity)
  have h2 : (κo : ℝ) ≤ κo * μ * E μ ^ 11 := by
    have : (1 : ℝ) ≤ μ * E μ ^ 11 := by_nlinarith
    nlinarith
  nlinarith

/-- `G(γ_r) ≤ 2 κo μ`. -/
theorem cuCost_lvGr_le {μ : ℕ} (h : 15 ≤ μ) :
    (DrvR.cuCost κo ztbbn : ℝ) ≤ 2 * κo * μ := by
  unfold DrvR.cuCost
  have hc : ztwtb := by
    zulfz
  zuizw
  push_cast at hc ⊢
  nlinarith

/-- `H(γ_r) + ⌈log₂ γ_r⌉ + 1 ≤ 19516 E^3`. -/
theorem hTerm_le {μ : ℕ} (h : 15 ≤ μ) :
    ((cutGran ztbbn + Nat.clog 2 ztbbn + 1 : ℕ) : ℝ) ≤ 19516 * E μ ^ 3 := by
  have hc : ztwtb := by
    zulfz
  zulhy
  have hμE : (μ : ℝ) ≤ 150 * E μ := by unfold E; exact L41.lam_le_E μ
  have hE3 : E μ ≤ E μ ^ 3 := by
    have := E_one_le μ
    calc E μ = E μ ^ 1 := by_grind
      _ ≤ E μ ^ 3 := pow_le_pow_right₀ this by_norm_num
  grind

/-! ## The level cost -/
theorem clog_lvNch_le : Nat.clog 2 ztdsn ≤ μ + 10 := by
  zudwq
  have h := lvNch_le_pow μ
  grind
set_option maxHeartbeats 1000000 in
/-- **The cost arithmetic of one level (D11).** -/
theorem lvCostSpec : DrvR.LvCostSpec := by
  refine ⟨lv_n0, fun κo => ⟨200000000000 * ztqzo, fun μ hμ => ?_⟩⟩
  have hμR : ztpgn := by_simp_all
  have hL := lemma41Nat_ge μ
  have hE60 : E μ ^ 60 ≤ E μ ^ 74 := E_pow_ge by_norm_num
  have hE0 := E_pow_nonneg μ 60
  have hE74 : 0 ≤ E μ ^ 74 := by_grind
  have hμ2 : (1 : ℝ) ≤ (μ : ℝ) ^ 2 := by_nlinarith
  have hN := lvNch_le_E μ
  have hN1 : ((DrvR.lvNch μ : ℝ) + 1) ≤ 224 * E μ ^ 60 := by
    have : (1 : ℝ) ≤ E μ ^ 60 := one_le_pow₀ ztpxp
    linarith
  have hLn : (0 : ℝ) ≤ (lemma41Nat μ : ℝ) := Nat.cast_nonneg _
  -- the constant
  have hκ : ∀ c : ℕ, c ≤ 200000000000 → c * lemma41Nat μ ≤
      200000000000 * ztqzo * ztud := fun c hc => by
    have h1 : c * lemma41Nat μ ≤ 200000000000 * lemma41Nat μ := Nat.mul_le_mul_right _ hc
    grind
  zusk
  · -- the chords
    have hR : (DrvR.lvNch μ : ℝ) ≤ ((223 * lemma41Nat μ : ℕ) : ℝ) := by
      push_cast
      calc (DrvR.lvNch μ : ℝ) ≤ 223 * E μ ^ 60 := hN
        _ ≤ 223 * ztebp := by_nlinarith
        _ ≤ 223 * (lemma41Nat μ : ℝ) := by_linarith
    have := (Nat.cast_le).1 hR
    grind
  · -- the splice
    have hc := clog_lvNch_le μ
    have hc' : ((Nat.clog 2 ztdsn + 1 : ℕ) : ℝ) ≤ 2 * μ := by
      have : Nat.clog 2 ztdsn + 1 ≤ 2 * μ := by_omega
      zufc
    have hR : ((ztleh * (Nat.clog 2 ztdsn + 1) : ℕ) : ℝ) ≤
        ((448 * lemma41Nat μ : ℕ) : ℝ) := by
      have hc0 : (0 : ℝ) ≤ ((Nat.clog 2 ztdsn + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      rw [Nat.cast_mul]
      calc ((DrvR.lvNch μ + 1 : ℕ) : ℝ) * ((Nat.clog 2 _ + 1 : ℕ) : ℝ)
          ≤ ztigt * ztnfg := by
            apply mul_le_mul by_simp_all hc' hc0 by_linarith
        _ ≤ 448 * ztebp := by
            have a : (μ : ℝ) * E μ ^ 60 ≤ (μ : ℝ) ^ 2 * E μ ^ 74 :=
              mul_le_mul by_nlinarith hE60 hE0 by_positivity
            grind
        _ ≤ ((448 * lemma41Nat μ : ℕ) : ℝ) := by_simp_all
    have := (Nat.cast_le).1 hR
    grind
  · -- the restoration rounds
    have hF := shCost_lvGr_le κo hμ
    have hG := cuCost_lvGr_le κo hμ
    have hH := hTerm_le hμ
    have hκo : ztiww := Nat.cast_nonneg _
    have hμ0 : ztfzp := Nat.cast_nonneg _
    have hE11 := E_pow_nonneg μ 11
    have hE3 := E_pow_nonneg μ 3
    have hF0 : (0 : ℝ) ≤ (DrvR.shCost κo ztbbn : ℝ) := Nat.cast_nonneg _
    have hG0 : (0 : ℝ) ≤ (DrvR.cuCost κo ztbbn : ℝ) := Nat.cast_nonneg _
    have hH0 : (0 : ℝ) ≤ ((cutGran ztbbn + Nat.clog 2 ztbbn + 1 : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    have hP : (((ztleh * DrvR.shCost κo ztbbn * DrvR.cuCost κo ztbbn *
        ztyiw) : ℕ) : ℝ) ≤
        ztigt * ztkpv * ztptz * ztowg := by
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
      have hA : ((DrvR.lvNch μ + 1 : ℕ) : ℝ) ≤ 224 * E μ ^ 60 := by_grind
      have hA0 : (0 : ℝ) ≤ ((DrvR.lvNch μ + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      have p1 : (0 : ℝ) ≤ 224 * E μ ^ 60 := by_linarith
      have p2 : (0 : ℝ) ≤ 22003 * κo * μ * E μ ^ 11 :=
        by grind
      have p3 : (0 : ℝ) ≤ 2 * κo * μ := by_positivity
      apply mul_le_mul _ hH hH0 (mul_nonneg ztttq p3)
      apply mul_le_mul _ hG hG0 ztttq
      exact mul_le_mul hA hF hF0 p1
    have hbig : ztigt * ztkpv * ztptz *
        ztowg = 192375925504 * ((κo : ℝ) ^ 2 * ztebp) := by
      grind
    rw [hbig] at hP
    have hk2 : (0 : ℝ) ≤ (κo : ℝ) ^ 2 := by_positivity
    have hR : ((ztleh * DrvR.shCost κo ztbbn * DrvR.cuCost κo ztbbn *
        ztyiw : ℕ) : ℝ) ≤
        ((200000000000 * (κo ^ 2 * lemma41Nat μ) : ℕ) : ℝ) := by
      refine hP.trans ?_
      push_cast
      have  :=
        mul_le_mul_of_nonneg_left hL hk2
      linarith
    have := (Nat.cast_le).1 hR
    grind
end
end DrvLC
namespace DrvR
open Machine Chazelle Chazelle.Merge L41
@[expose] public section
variable {P : Polygon}
/-- The models of chains on a well-formed, regular, simple host are served by the oracles. -/
theorem okModel_host {H : Host} {C : Chain} (hHok : H.length ≤ 64)
    (hreg : HostRegular (Qof P).n H) (hP : C.P = H.poly zta) (hsimp : (H.poly zta).Simple) :
    OkModel P ztc :=
  ⟨H, C, hHok, hreg, hP, by_simp_all, rfl⟩

/-- A chain descriptor on a well-formed host is well formed. -/
theorem chainWF_host {E : ℕ} {m : ℕ → ℕ} {d HB : ℕ} {H : Host} {C : Chain}
    (hHA : HostAt m HB H) (hHok : H.length ≤ 64) (hwf : HostWF P.n H)
    (hHB : HB + 3 * H.length + 4 ≤ E) (hd : ChainDescAt m d zta H C) (hdh : m d = HB)
    (hdA : d + 5 ≤ E) (hs : C.s < C.P.n) : ChainWF P E m d := by
  refine ⟨hdA, fun H' C' hC' => ?_⟩
  have hH : ztiyi := NFLoc.hostAt_unique hC'.1 by_simp_all
  zulsw
  have hC : ztkzv := L41.chain_eq (hC'.2.1.trans hd.2.1.symm)
    (hC'.2.2.1.symm.trans hd.2.2.1) (hC'.2.2.2.1.symm.trans hd.2.2.2.1)
  simp_all

/-- **The precondition of a merge on a region host** (`L41.mergePre_of` for an arbitrary host). -/
theorem mergePreR {W : ℕ} {c : Config} {X : MemCtx} (hG : GoodEnv P)
    (hWh : hostWords P.n ≤ W) (hX : X.holds P c.nmem ztdab ztm)
    (hcap : rd c bMerge 5 + fuseLoss ≤ X.cap P c.nmem ztdab)
    (h7 : 4 ≤ rd c bMerge 7) (h56 : rd c bMerge 5 + fuseLoss ≤ rd c bMerge 6)
    {HB d1 f1 d2 f2 TD : ℕ} {H : Host} {C1 C2 : Chain} {γ1 γ2 : ℕ} {N1 N2 : NF}
    (hHA : HostAt c.nmem HB H) (hHok : H.length ≤ 64) (hwf : HostWF P.n H)
    (hreg : HostRegular (Qof P).n H) (hsimp : (H.poly zta).Simple)
    (hHB : HB + 3 * H.length + 4 ≤ c.nreg ALLOC)
    (hd1 : ChainDescAt c.nmem d1 zta H C1) (hd1h : c.nmem d1 = HB) (hd1A : d1 + 5 ≤ c.nreg ALLOC)
    (hd2 : ChainDescAt c.nmem d2 zta H C2) (hd2h : c.nmem d2 = HB) (hd2A : d2 + 5 ≤ c.nreg ALLOC)
    (hcons : C2.s = C1.s + C1.m) (hlen : C1.m + C2.m + 1 ≤ C1.P.n)
    (hs1 : C1.s < C1.P.n) (hs2 : C2.s < C2.P.n)
    (hTD : ChainDescAt c.nmem TD zta H (jOf C1 C2 hlen).whole) (hTDh : c.nmem TD = HB)
    (hTDA : TD + 5 ≤ c.nreg ALLOC)
    (r0 : rd c bMerge 0 = d1) (r1 : rd c bMerge 1 = d2) (r2 : rd c bMerge 2 = TD)
    (r3 : rd c bMerge 3 = f1) (r4 : rd c bMerge 4 = f2)
    (hN1 : NFWithin c.nmem f1 ztm N1) (hN2 : NFWithin c.nmem f2 ztm N2)
    (hc1 : IsCanonicalNF ztvlg zta N1 γ1 ztbnk)
    (hc2 : IsCanonicalNF ztvlh zta N2 γ2 ztbnk)
    (hγ1 : γ1 ≤ rd c bMerge 5) (hγ2 : γ2 ≤ rd c bMerge 5)
    (hgen : SharedGeneric ztfsv)
    (hfd : (chainModel (jOf C1 C2 hlen).whole).FullDegLe zta ztbnk) :
    MergePre X OkModel P W c := by
  zuhoc
  have hP1 : C1.P = H.poly zta := hd1.2.1
  have hP2 : C2.P = H.poly zta := hd2.2.1
  zucgq

  have hwP : J.whole.P = H.poly zta := by_tauto
  zuc
  have hsT : J.whole.s < J.whole.P.n := by_tauto
  refine ⟨hG, hWh, hX, hcap, h7, h56,
    ⟨?_, ?_, ?_, fun H' hH' => ?_⟩, H, J, N1, N2, ⟨?_, ?_, ?_⟩,
    by show J.P.Simple; rw [show J.P = H.poly zta from hwP]; omega, hgen,
    by zvnen; exact okModel_host hHok hreg hP1 hsimp,
    by zvnel; exact okModel_host hHok hreg hP2 hsimp, okModel_host hHok hreg hwP hsimp,
    hfd, by_simp_all, by_simp_all, ztrfc,
    ⟨γ2, hγ2, by_simp_all⟩⟩
  · rw [r0]; exact chainWF_host hHA hHok hwf hHB hd1 hd1h hd1A hs1
  · zvnal; exact chainWF_host hHA hHok hwf hHB hd2 hd2h hd2A hs2
  · rw [r2]; exact chainWF_host hHA hHok hwf hHB hTD hTDh hTDA hsT
  · rw [r2, hTDh] at hH'
    rw [NFLoc.hostAt_unique hH' hHA, ← hQn]; omega
  · simp_all
  · simp_all
  simp_all
end
end DrvR
end Chazelle.Core
namespace Chazelle.Core
namespace DrvR
open Machine Machine.Stmt Programs BuildRam SignK
@[expose] public section
def mgLoad : Stmt :=
  block [.addN 219126 219110 219144, .loadN 219120 219126,
    .addN 219126 219110 219145, .loadN 219123 219126,
    .addN 219126 219114 219144, .loadN 219127 219126,
    .addN 219121 219112 219127,
    .addN 219126 219114 219145, .loadN 219125 219126,
    .copyN 50060 219100, .copyN 50061 219107, .constN 50067 1, .constN 50068 2, .constN 50069 3,
    .constN 50052 0, .copyN 50087 219101, .copyN 50091 219120]

/-- The two top points. -/
def mgPts : Stmt :=
  .seq NFLoc.hostPt
    (.seq (block [.copyN 219130 50046, .copyN 219131 50047, .copyN 219132 50048,
        .copyN 50091 219121])
      (.seq NFLoc.hostPt (block [.copyN 219133 50046, .copyN 219134 50047, .copyN 219135 50048])))

/-- The top and the bit of the union (the right part's if its top is strictly higher). -/
def mgSel : Stmt :=
  .ifLtN 219136 219141 (block [.copyN 219138 219120, .copyN 219139 219123])
    (block [.copyN 219138 219121, .copyN 219139 219125])

/-- **The top of the union.** -/
def mgTop : Stmt :=
  .seq mgLoad (.seq mgPts (.seq (SweepPrim.kbit 219130 219133 219130 1 219136) mgSel))

/-- The constants of the merge steps. -/
structure MgConst (c : Config) : Prop where
  r40 : c.nreg 219140 = 0
  r41 : c.nreg 219141 = 1
  r42 : c.nreg 219142 = 2
  r43 : c.nreg 219143 = 3
  r44 : c.nreg 219144 = 4
  r45 : c.nreg 219145 = 5
  r46 : c.nreg 219146 = 6

/-- The registers `mgTop` writes. -/
def Btop (r : ℕ) : Bool :=
  decide (219120 ≤ r ∧ r ≤ 219139) || decide ztcko ||
    decide (50040 ≤ r ∧ r ≤ 50099)
section exec
variable {P : Polygon} {W : ℕ}
theorem frameB_up {B B' : ℕ → Bool} {c c' : Config} (h : FrameB B c c')
    (hB : ∀ r, B' r = false → B r = false) : FrameB B' c c' :=
  ⟨fun r hr => h.1 r by_simp_all, fun r hr => h.2.1 r by_simp_all, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
theorem pts_getD_of_get? {l : List SymPt} {i : ℕ} {sp : SymPt} (h : l[i]? = some sp) :
    l.getD i ztga = sp := by
  simp_all
set_option maxHeartbeats 4000000 in
/-- **The top of the union** of two consecutive sub-chains of the host. -/
theorem mgTop_exec (hG : GoodEnv P) (hWn : hostWords P.n ≤ W) (c : Config)
    (hw : WordsBounded W c) (hK : MgConst c) {H : Host} {HB NP ma : ℕ} {C1 C2 : Chain}
    (h00 : c.nreg 219100 = HB) (h01 : c.nreg 219101 = NP) (h07 : c.nreg 219107 = H.length)
    (h12 : c.nreg 219112 = ma) (hHA : HostAt c.nmem HB H) (hwf : HostWF P.n H)
    (hHok : H.length ≤ 64) (hHB : HB + 3 * H.length + 4 ≤ W) (hNP : NP = (H.pts P.n).length)
    (hd1 : ChainDescAt c.nmem (c.nreg 219110 + 1) (Qof P) H C1)
    (hd2 : ChainDescAt c.nmem (c.nreg 219114 + 1) (Qof P) H C2)
    (hs1 : C1.s = 0) (hm1 : C1.m = ma) (hs2 : C2.s = ma) (hlen : ma + C2.m + 1 ≤ NP)
    (hWa : c.nreg 219110 + 6 ≤ W) (hWb : c.nreg 219114 + 6 ≤ W) :
    ∃ c' k, Exec P W mgTop c c' k ∧ k ≤ 60 * H.length + 330 ∧
      c'.nreg 219138 = (if (C2.top).2 ≤ (C1.top).2 then C1.topIdx else C1.m + C2.topIdx) ∧
      c'.nreg 219139 = (if (C2.top).2 ≤ (C1.top).2 then c.nmem (c.nreg 219110 + 5)
        else c.nmem (c.nreg 219114 + 5)) ∧
      FrameB Btop c c' := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hhw : hostWords P.n = 256 * P.n + 16 := rfl
  have hW3 : P.n + 3 ≤ W := by omega
  have hNW : 2 * NP ≤ W := by
    have h1 := Host.pts_length_le hwf
    have h2 : H.length * P.n ≤ 64 * P.n := Nat.mul_le_mul_right _ hHok
    omega
  have hn3 := hG.1.1
  have hn0 : 0 < P.n := by omega
  have hLt := NFLoc.hostWF_pts hwf hn0
  set D1 := c.nreg 219110 with hD1
  set D2 := c.nreg 219114 with hD2
  have t1 : c.nmem _ = C1.topIdx := hd1.2.2.2.2.1
  have t2 : c.nmem _ = C2.topIdx := hd2.2.2.2.2.1
  have ht1 := hm1 ▸ C1.topIdx_le
  have ht2 := C2.topIdx_le
  -- the loads and the host environment
  obtain ⟨c₁, k₁, e₁, hk₁, v20, v23, v21, v25, E₁, s52, n87, k91, g₁⟩ : ∃ c₁ k₁, Exec P W mgLoad c c₁ k₁ ∧
      k₁ = 17 ∧ c₁.nreg 219120 = C1.topIdx ∧ c₁.nreg 219123 = c.nmem (D1 + 5) ∧
      c₁.nreg 219121 = ma + C2.topIdx ∧ c₁.nreg 219125 = c.nmem (D2 + 5) ∧
      NFLoc.HostEnv W HB H.length c.nmem c₁ ∧ c₁.nreg 50052 = 0 ∧ c₁.nreg 50087 = NP ∧
      c₁.nreg 50091 = C1.topIdx ∧ FrameB Btop c c₁ := by
    have q44 := hK.r44; have q45 := hK.r45
    have hD1W : D1 + 4 ≤ W := by omega
    have t1' : c.nmem (D1 + 4) = C1.topIdx := by omega
    have t2' : c.nmem (D2 + 4) = C2.topIdx := by omega
    obtain ⟨c₁, k₁, e₁, hk₁, v20, v23, v21, v25, v60, v61, v67, v68, v69, s52, n87, k91, m₁⟩ :
        ∃ c₁ k₁, Exec P W mgLoad c c₁ k₁ ∧ k₁ = 17 ∧ c₁.nreg 219120 = C1.topIdx ∧
        c₁.nreg 219123 = c.nmem (D1 + 5) ∧ c₁.nreg 219121 = ma + C2.topIdx ∧
        c₁.nreg 219125 = c.nmem (D2 + 5) ∧ c₁.nreg 50060 = HB ∧ c₁.nreg 50061 = H.length ∧
        c₁.nreg 50067 = 1 ∧ c₁.nreg 50068 = 2 ∧ c₁.nreg 50069 = 3 ∧ c₁.nreg 50052 = 0 ∧
        c₁.nreg 50087 = NP ∧ c₁.nreg 50091 = C1.topIdx ∧ c₁.nmem = c.nmem := by
      unfold mgLoad
      exec_block
      all_goals try (config_simp; (try simp only [← hD1, ← hD2, q44, q45, h12, h00, h07, h01, t1', t2']); omega)
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> config_simp <;>
        (try simp only [← hD1, ← hD2, q44, q45, h12, h00, h07, h01, t1', t2'])
    refine ⟨c₁, k₁, e₁, hk₁, v20, v23, v21, v25, ⟨e₁.wb_right, v60, v61, v67, v68, v69, m₁⟩, s52,
      n87, k91, exec_frameB e₁ (by decide)⟩
  have hNP' := hNP.symm
  -- the first top point
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, E₂, sp₁, hsp₁, in₁⟩ := NFLoc.hostPt_exec (P := P) c₁ E₁ hHA hwf
    (by omega) (by omega) (by omega) s52 (by omega) k91 (by omega) (by omega)
  have g₂ := f₂.1
  obtain ⟨c₃, k₃, e₃, hk₃, a₃, k91', g₃, m₃⟩ : ∃ c₃ k₃, Exec P W
      (block [.copyN 219130 50046, .copyN 219131 50047, .copyN 219132 50048,
        .copyN 50091 219121]) c₂ c₃ k₃ ∧ k₃ = 4 ∧ SymPtIn c₃ 219130 sp₁ ∧
      c₃.nreg 50091 = ma + C2.topIdx ∧
      (∀ r, ¬ (219130 ≤ r ∧ r ≤ 219132) → r ≠ 50091 → c₃.nreg r = c₂.nreg r) ∧
      c₃.nmem = c₂.nmem := by
    have hw₂ := e₂.wb_right
    have q21 : c₂.nreg 219121 = ma + C2.topIdx := by rw [g₂ _ (by decide), v21]
    exec_block
    refine ⟨rfl, NFLoc.symPtIn_copy in₁ (by config_simp) (by config_simp) (by config_simp),
      by config_simp; omega, fun r h1 h2 => ?_, rfl⟩
    simp only [Machine.upd_apply]
    grind
  have E₃ : NFLoc.HostEnv W HB H.length c.nmem c₃ :=
    ⟨e₃.wb_right, by rw [g₃ _ (by omega) (by omega), E₂.h60], by rw [g₃ _ (by omega) (by omega), E₂.h61],
      by rw [g₃ _ (by omega) (by omega), E₂.h67], by rw [g₃ _ (by omega) (by omega), E₂.h68],
      by rw [g₃ _ (by omega) (by omega), E₂.h69], by rw [m₃, E₂.mem]⟩
  have s52' : c₃.nreg 50052 = 0 := by rw [g₃ _ (by omega) (by omega), g₂ _ (by decide), s52]
  have n87' : c₃.nreg 50087 = NP := by rw [g₃ _ (by omega) (by omega), g₂ _ (by decide), n87]
  -- the second top point
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, E₄, sp₂, hsp₂, in₂⟩ := NFLoc.hostPt_exec (P := P) c₃ E₃ hHA hwf
    (by omega) (by omega) (by omega) s52' (by omega) k91' (by omega) (by omega)
  have g₄ := f₄.1
  have a₄ := NFLoc.symPtIn_copy a₃ (g₄ _ (by decide)) (g₄ _ (by decide))
    (g₄ _ (by decide))
  obtain ⟨c₅, k₅, e₅, hk₅, a₅, b₅, g₅, m₅⟩ : ∃ c₅ k₅, Exec P W
      (block [.copyN 219133 50046, .copyN 219134 50047, .copyN 219135 50048]) c₄ c₅ k₅ ∧
      k₅ = 3 ∧ SymPtIn c₅ 219130 sp₁ ∧ SymPtIn c₅ 219133 sp₂ ∧
      (∀ r, ¬ (219133 ≤ r ∧ r ≤ 219135) → c₅.nreg r = c₄.nreg r) ∧ c₅.nmem = c₄.nmem := by
    have hw₄ := e₄.wb_right
    exec_block
    refine ⟨rfl, NFLoc.symPtIn_copy a₄ (by config_simp) (by config_simp) (by config_simp),
      NFLoc.symPtIn_copy in₂ (by config_simp) (by config_simp) (by config_simp), fun r h1 => ?_, rfl⟩
    simp only [Machine.upd_apply]
    split_ifs <;> first | rfl | omega
  -- the comparison
  have l₁ := hLt _ (List.mem_of_getElem? hsp₁)
  have l₂ := hLt _ (List.mem_of_getElem? hsp₂)
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, b6le, b6⟩ := SweepPrim.kbit_exec (P := P) hG hW3 c₅ e₅.wb_right
    (a := 219130) (b := 219133) (d := 219130) (op := 1) (dst := 219136) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) l₁ l₂ l₁ a₅ b₅ a₅
  -- the two tops are the loaded points
  have top1 : C1.top = sp₁.eval (Qof P) := by
    unfold Chain.top
    rw [DownMath.chain_vertex_host hd1.2.1, hs1, hQn, pts_getD_of_get? hsp₁]
  have top2 : C2.top = sp₂.eval (Qof P) := by
    have h2 := pts_getD_of_get? hsp₂
    rw [Nat.zero_add] at h2
    unfold Chain.top
    rw [DownMath.chain_vertex_host hd2.2.1, hs2, hQn, h2]
  have hbit : c₆.nreg 219136 = 1 ↔ ¬ (C2.top).2 ≤ (C1.top).2 := by
    rw [b6, top1, top2]; simp only [SignTest, not_le]
  -- the selection
  have q20 : c₆.nreg 219120 = C1.topIdx := by
    rw [f₆.1 _ (by decide), g₅ _ (by omega), g₄ _ (by decide), g₃ _ (by omega) (by omega),
      g₂ _ (by decide), v20]
  have q21 : c₆.nreg 219121 = ma + C2.topIdx := by
    rw [f₆.1 _ (by decide), g₅ _ (by omega), g₄ _ (by decide), g₃ _ (by omega) (by omega),
      g₂ _ (by decide), v21]
  have q23 : c₆.nreg 219123 = c.nmem (D1 + 5) := by
    rw [f₆.1 _ (by decide), g₅ _ (by omega), g₄ _ (by decide), g₃ _ (by omega) (by omega),
      g₂ _ (by decide), v23]
  have q25 : c₆.nreg 219125 = c.nmem (D2 + 5) := by
    rw [f₆.1 _ (by decide), g₅ _ (by omega), g₄ _ (by decide), g₃ _ (by omega) (by omega),
      g₂ _ (by decide), v25]
  have q41 : c₆.nreg 219141 = 1 := by
    rw [f₆.1 _ (by decide), g₅ _ (by omega), g₄ _ (by decide), g₃ _ (by omega) (by omega),
      g₂ _ (by decide), g₁.1 _ (by decide), hK.r41]
  have hw₆ := e₆.wb_right
  obtain ⟨c₇, k₇, e₇, hk₇, o38, o39, f₇⟩ : ∃ c₇ k₇, Exec P W mgSel c₆ c₇ k₇ ∧ k₇ ≤ 4 ∧
      c₇.nreg 219138 = (if (C2.top).2 ≤ (C1.top).2 then C1.topIdx else C1.m + C2.topIdx) ∧
      c₇.nreg 219139 = (if (C2.top).2 ≤ (C1.top).2 then c.nmem (D1 + 5) else c.nmem (D2 + 5)) ∧
      FrameB Btop c₆ c₇ := by
    by_cases hc : (C2.top).2 ≤ (C1.top).2
    · have h0 : c₆.nreg 219136 < c₆.nreg 219141 := by
        grind
      obtain ⟨c₇, k₇, e₇, hk₇, w38, w39⟩ : ∃ c₇ k₇, Exec P W
          (block [.copyN 219138 219120, .copyN 219139 219123]) c₆ c₇ k₇ ∧ k₇ = 2 ∧
          c₇.nreg 219138 = C1.topIdx ∧ c₇.nreg 219139 = c.nmem (D1 + 5) := by
        exec_block
        refine ⟨rfl, ?_, ?_⟩ <;> config_simp <;> (try simp only [q20, q23])
      have ex7 : Exec P W mgSel c₆ c₇ _ := .ifLtN_true h0 e₇
      refine ⟨c₇, k₇ + 1, ex7, by omega, by grind,
        by grind, exec_frameB ex7 (by decide)⟩
    · have h0 : ¬ c₆.nreg 219136 < c₆.nreg 219141 := by
        grind
      obtain ⟨c₇, k₇, e₇, hk₇, w38, w39⟩ : ∃ c₇ k₇, Exec P W
          (block [.copyN 219138 219121, .copyN 219139 219125]) c₆ c₇ k₇ ∧ k₇ = 2 ∧
          c₇.nreg 219138 = ma + C2.topIdx ∧ c₇.nreg 219139 = c.nmem (D2 + 5) := by
        exec_block
        refine ⟨rfl, ?_, ?_⟩ <;> config_simp <;> (try simp only [q21, q25])
      have ex7 : Exec P W mgSel c₆ c₇ _ := .ifLtN_false h0 e₇
      refine ⟨c₇, k₇ + 2, ex7, by omega, by grind,
        by grind, exec_frameB ex7 (by decide)⟩
  refine ⟨c₇, k₁ + (k₂ + (k₃ + (k₄ + k₅)) + (k₆ + k₇)), ?_, ?_, o38, o39, ?_⟩
  · exact .seq e₁ (.seq (.seq e₂ (.seq e₃ (.seq e₄ e₅))) (.seq e₆ e₇))
  · omega
  · have F3 : FrameB Btop c₂ c₃ := exec_frameB e₃ (by decide)
    have F5 : FrameB Btop c₄ c₅ := exec_frameB e₅ (by decide)
    have hb : ∀ r, Btop r = false → NFLoc.Bhost r = false := fun r hr => by
      simp only [Btop, NFLoc.Bhost, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢; omega
    have hk : ∀ r, Btop r = false → SweepPrim.Bkb 219136 r = false := fun r hr => by
      simp only [Btop, SweepPrim.Bkb, WalkKey.Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not,
        beq_eq_false_iff_ne, ne_eq] at hr ⊢; omega
    exact g₁.trans ((frameB_up f₂ hb).trans (F3.trans ((frameB_up f₄ hb).trans
      (F5.trans ((frameB_up f₆ hk).trans f₇)))))
end exec
end
end DrvR
end Chazelle.Core
namespace Chazelle.Core
namespace DrvR
open Machine Machine.Stmt Programs BuildRam SignK L41 Chazelle Chazelle.Merge
@[expose] public section
def mgDesc : Stmt :=
  block [.copyN 219137 9999, .storeN 9999 219140,
    .addN 219126 219137 219141, .storeN 219126 219100,
    .addN 219126 219126 219141, .storeN 219126 219140,
    .addN 219126 219126 219141, .addN 219127 219112 219116, .storeN 219126 219127,
    .addN 219126 219126 219141, .storeN 219126 219138,
    .addN 219126 219126 219141, .storeN 219126 219139,
    .addN 9999 9999 219146]

/-- The arguments of the merge. -/
def mgArgs : Stmt :=
  block [.addN 100000 219110 219141, .addN 100001 219114 219141, .addN 100002 219137 219141,
    .copyN 100003 219111, .copyN 100004 219115, .copyN 100005 219113, .addN 100006 219113 219141,
    .copyN 100007 219103, .copyN 100009 219104]

/-- The accumulated chain after the merge. -/
def mgOut : Stmt :=
  block [.copyN 219110 219137, .copyN 219111 100008, .addN 219112 219112 219116,
    .addN 219113 219113 219141]

/-- **One merge step.** -/
def mgStep (sM : Stmt) : Stmt := .seq mgTop (.seq mgDesc (.seq mgArgs (.seq sM mgOut)))

/-- The cost of the merge of one step: degree cap `D`, chord counts `x, y` of the parts, their
granularity bound `γ`, the length `M` of the union. -/
def mgCostV (κ F G H : ℕ → ℕ) (D x y γ M : ℕ) : ℕ :=
  κ D * ztcwy * F ztcbh * G ztcbh *
    ztxgb

/-- The bands of a merge step. -/
def mgBands : Finset ℕ := insert bDownDrv ztodk
theorem mgBands_subset : mgBands ⊆ drvBands := by_decide

/-- The registers `mgDesc` writes. -/
def Bdesc (r : ℕ) : Bool := decide (r = 219126 ∨ r = 219127 ∨ r = 219137 ∨ r = 9999)
theorem wrM_mgDesc : wrM Bdesc mgDesc = true := by_decide

/-- The registers `mgArgs` writes. -/
def Bargs (r : ℕ) : Bool := decide (100000 ≤ r ∧ r ≤ 100009)
theorem wr_mgArgs : wr Bargs mgArgs = true := by_decide

/-- The registers `mgOut` writes. -/
def Bout (r : ℕ) : Bool := decide (219110 ≤ r ∧ r ≤ 219113)
theorem wr_mgOut : wr Bout mgOut = true := by_decide
section exec
variable {P : Polygon} {W : ℕ}
theorem mgDesc_exec (c : Config) (hw : WordsBounded W c) {A HB ma mp : ℕ}
    (a40 : c.nreg 219140 = 0) (a41 : c.nreg 219141 = 1) (a46 : c.nreg 219146 = 6)
    (a00 : c.nreg 219100 = HB) (a12 : c.nreg 219112 = ma) (a16 : c.nreg 219116 = mp)
    (aA : c.nreg 9999 = A) (hAW : A + 6 ≤ W) (hmp : ma + mp ≤ W) :
    ∃ c' k, Exec P W mgDesc c c' k ∧ k = 14 ∧ c'.nreg 219137 = A ∧ c'.nreg 9999 = A + 6 ∧
      c'.nmem A = 0 ∧ c'.nmem ztbo = HB ∧ c'.nmem ztbcl = 0 ∧
      c'.nmem zttf = ma + mp ∧ c'.nmem ztckz = c.nreg 219138 ∧
      c'.nmem ztgzp = c.nreg 219139 ∧ zttp ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have aT := hw.1 219138
  have aB := hw.1 219139
  unfold mgDesc
  exec_block
  all_goals try (config_simp; (try simp only [a40, a41, a46, a00, a12, a16, aA]); omega)
  refine ztedv
  · simp_all
  · simp_all
  · config_simp; simp only [aA, a41, a40, Machine.upd_apply]; grind
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · intro a ha; config_simp; simp only [aA, a41, Machine.upd_apply]
    grind
  · config_simp
  · config_simp
  simp
theorem mgArgs_exec (c : Config) (hw : WordsBounded W c) {D1 D2 A f1 f2 γ D g : ℕ}
    (b10 : c.nreg 219110 = D1) (b14 : c.nreg 219114 = D2) (b37 : c.nreg 219137 = A)
    (b11 : c.nreg 219111 = f1) (b15 : c.nreg 219115 = f2) (b13 : c.nreg 219113 = γ)
    (b03 : c.nreg 219103 = D) (b04 : c.nreg 219104 = g) (b41 : c.nreg 219141 = 1)
    (h1 : D1 + 1 ≤ W) (h2 : D2 + 1 ≤ W) (h3 : A + 1 ≤ W) (h4 : γ + 1 ≤ W) :
    ∃ c' k, Exec P W mgArgs c c' k ∧ k = 9 ∧
      c'.nreg 100000 = D1 + 1 ∧ c'.nreg 100001 = D2 + 1 ∧ c'.nreg 100002 = A + 1 ∧
      c'.nreg 100003 = f1 ∧ c'.nreg 100004 = f2 ∧ c'.nreg 100005 = γ ∧
      c'.nreg 100006 = γ + 1 ∧ c'.nreg 100007 = D ∧ c'.nreg 100009 = g ∧ c'.nmem = c.nmem := by
  unfold mgArgs
  exec_block
  all_goals try (config_simp; (try simp only [b10, b14, b37, b11, b15, b13, b03, b04, b41]); omega)
  simp_all
theorem mgOut_exec (c : Config) (hw : WordsBounded W c) {A ma mp γ : ℕ}
    (b37 : c.nreg 219137 = A) (b12 : c.nreg 219112 = ma) (b16 : c.nreg 219116 = mp)
    (b13 : c.nreg 219113 = γ) (b41 : c.nreg 219141 = 1) (h1 : ma + mp ≤ W) (h2 : γ + 1 ≤ W) :
    ∃ c' k, Exec P W mgOut c c' k ∧ k = 4 ∧ c'.nreg 219110 = A ∧
      c'.nreg 219111 = c.nreg 100008 ∧ c'.nreg 219112 = ma + mp ∧ c'.nreg 219113 = γ + 1 := by
  unfold mgOut
  exec_block
  all_goals try (config_simp; (try simp only [b37, b12, b16, b13, b41]); omega)
  simp_all
set_option maxHeartbeats 8000000 in
/-- **One merge step**: the union of the accumulated chain `C₁ = ⟨H.poly Q, 0, m₁⟩` (descriptor
at `r219110 + 1`, normal form at `r219111`, granularity `≤ r219113`) and the next piece `C₂`
(at `r219114 + 1`, `r219115`, `r219116` edges): a model descriptor of the union at the
allocator, its `(γ + 1)`-canonical normal form, written back into `219110 … 219113`. -/
theorem mgStep_exec {sM : Stmt} {κ F G Hf : ℕ → ℕ} {X : MemCtx}
    (hM : MergeMeets sM κ F G Hf X OkModel) (hXc : X.CapLocal)
    (hG : GoodEnv P) (hWn : hostWords P.n ≤ W) (c : Config) (hw : WordsBounded W c)
    (hK : MgConst c) {H : Host} {HB NP D g γ ma mp γ1 γ2 : ℕ} {C1 C2 : Chain} {N1 N2 : NF}
    (h00 : c.nreg 219100 = HB) (h01 : c.nreg 219101 = NP) (h03 : c.nreg 219103 = D)
    (h04 : c.nreg 219104 = g) (h07 : c.nreg 219107 = H.length)
    (h12 : c.nreg 219112 = ma) (h13 : c.nreg 219113 = γ) (h16 : c.nreg 219116 = mp)
    (hHA : Robust ztm c.nmem ztesn)
    (hHok : H.length ≤ 64) (hwf : HostWF P.n H) (hreg : HostRegular (Qof P).n H)
    (hsimp : (H.poly zta).Simple) (hHB : HB + 3 * H.length + 4 ≤ c.nreg ALLOC)
    (hNP : NP = (H.pts P.n).length)
    (hd1 : Robust ztm c.nmem
      (fun m => m ztlku = HB ∧ ChainDescAt m ztlku zta H C1))
    (hd2 : Robust ztm c.nmem
      (fun m => m ztlkv = HB ∧ ChainDescAt m ztlkv zta H C2))
    (hd1A : c.nreg 219110 + 6 ≤ c.nreg ALLOC) (hd2A : c.nreg 219114 + 6 ≤ c.nreg ALLOC)
    (hs1 : C1.s = 0) (hm1 : C1.m = ma) (hs2 : C2.s = ma) (hm2 : C2.m = mp)
    (hlen : C1.m + C2.m + 1 ≤ C1.P.n)
    (hN1 : NFWithin c.nmem (c.nreg 219111) ztm N1)
    (hN2 : NFWithin c.nmem (c.nreg 219115) ztm N2)
    (hc1 : IsCanonicalNF ztvlg zta N1 γ1 D)
    (hc2 : IsCanonicalNF ztvlh zta N2 γ2 D) (hγ1 : γ1 ≤ γ) (hγ2 : γ2 ≤ γ)
    (hgen : SharedGeneric ztfsv)
    (hfd : (chainModel (jOf C1 C2 hlen).whole).FullDegLe zta D) (hD : 4 ≤ D)
    (hX : X.holds P c.nmem g ztm) (hcap : γ + fuseLoss ≤ X.cap P c.nmem g)
    (hγW : γ + 1 ≤ W)
    (hroom : c.nreg ALLOC + 6 +
      mgCostV κ F G Hf D N1.chords.length N2.chords.length γ ztkap ≤ W) :
    ∃ c' k, Exec P W ztvzb c c' k ∧
      k ≤ 60 * H.length + 360 + mgCostV κ F G Hf D N1.chords.length N2.chords.length γ ztkap ∧
      c'.nreg 219110 = c.nreg ALLOC ∧ c.nreg ALLOC + 6 ≤ c'.nreg 219111 ∧
      c'.nreg 219112 = ma + mp ∧ c'.nreg 219113 = γ + 1 ∧ c.nreg ALLOC + 6 ≤ c'.nreg ALLOC ∧
      Robust ztdo c'.nmem (fun m => m ztm = 0 ∧
        m ztccv = HB ∧
        ChainDescAt m ztccv zta H (jOf C1 C2 hlen).whole) ∧
      ModelDescWF P ztdo c'.nmem ztm ∧
      (∃ N, NFWithin c'.nmem (c'.nreg 219111) ztdo N ∧
        IsCanonicalNF (chainModel (jOf C1 C2 hlen).whole) zta N ztgj D) ∧
      (∀ q, bandOf q = bDownDrv → (q < 219110 ∨ (219113 < q ∧ q < 219120) ∨ 219139 < q) →
        c'.nreg q = c.nreg q) ∧
      Frame mgBands c c' k := by
  zuc
  zufut
  zudom
  zuce
  set D1 := c.nreg 219110 with hD1
  set D2 := c.nreg 219114 with hD2

  set f1 := c.nreg 219111 with hf1
  set f2 := c.nreg 219115 with hf2
  have hP1 : C1.P = H.poly _ := hd1.holds.2.2.1
  have hP2 : C2.P = H.poly _ := hd2.holds.2.2.1
  have hC1n : C1.P.n = NP := by rw [hP1, DownMath.host_poly_n, hQn, hNP]
  have hlen' : ma + C2.m + 1 ≤ NP := by_omega
  have hNW : NP ≤ 64 * P.n := by
    have h1 := Host.pts_length_le hwf
    have h2 : ztgak := Nat.mul_le_mul_right _ hHok
    omega

  have hAW : A₀ + 6 ≤ W := by_omega
  -- the top of the union
  obtain ⟨c₁, k₁, e₁, hk₁, t38, t39, g₁⟩ := mgTop_exec hG hWn c hw hK h00 h01 h07 h12 hHA.holds
    hwf hHok by_omega hNP hd1.holds.2 hd2.holds.2 hs1 hm1 hs2 hlen' by_omega by_omega
  zuka
  have u := g₁.1
  have hm₁ := g₁.2.2.1
  -- the descriptor of the union
  have a40 : c₁.nreg 219140 = 0 := by rw [u _ by_decide, hK.r40]
  have a41 : c₁.nreg 219141 = 1 := by rw [u _ by_decide, hK.r41]
  have a46 : c₁.nreg 219146 = 6 := by rw [u _ by_decide, hK.r46]
  have a00 : c₁.nreg 219100 = HB := by rw [u _ by_decide, h00]
  have a12 : c₁.nreg 219112 = ma := by rw [u _ by_decide, h12]
  have a16 : c₁.nreg 219116 = mp := by rw [u _ by_decide, h16]
  have aA : ztlxy := by rw [u _ by_decide]; rfl
  obtain ⟨c₂, k₂, e₂, hk₂, d37, dA, w0, w1, w2, w3, w4, w5, wlt, drr, drm, dout⟩ :=
    mgDesc_exec (P := P) c₁ hw₁ a40 a41 a46 a00 a12 a16 aA hAW by_omega
  zuja
  have g₂ := exec_frameM e₂ wrM_mgDesc
  have v : ∀ r, Btop r = false → Bdesc r = false → c₂.nreg r = c.nreg r := fun r h1 h2 =>
    (g₂.1 r h2).trans by_grind
  have hag : ztfak := fun a ha => by_grind
  -- the union's descriptor, robustly
  have hP21 := hP2.trans hP1.symm
  have hcons : ztsba := by_omega
  have hΦ : ∀ m' : ℕ → ℕ, (∀ a, a < A₀ + 6 → m' a = c₂.nmem a) →
      m' A₀ = 0 ∧ m' ztfnc = HB ∧
      ChainDescAt m' ztfnc zta H (jOf C1 C2 hlen).whole := by
    zubxa
    have ag : ∀ a, a < A₀ → m' a = c.nmem a := by_grind
    obtain ⟨b1h, b1⟩ := hd1 m' ag
    obtain ⟨b2h, b2⟩ := hd2 m' ag
    refine ⟨by_grind, by_grind, ?_⟩
    refine descWhole hlen hP21 hcons b1 b2 ?_ ?_ ?_ ?_ ?_
    · grind
    · grind
    · grind
    · grind
    · rw [show A₀ + 1 + 4 = A₀ + 5 by omega, hm' _ by_omega, w5, t39,
        show D1 + 1 + 4 = D1 + 5 by omega, show D2 + 1 + 4 = D2 + 5 by omega,
        ag _ by_omega, ag _ by_omega]
  have hTD := hΦ c₂.nmem by_omega
  -- the arguments
  have b10 : c₂.nreg 219110 = D1 := v _ by_decide by_decide
  have b14 : c₂.nreg 219114 = D2 := v _ by_decide by_decide
  have b11 : c₂.nreg 219111 = f1 := v _ by_decide by_decide
  have b15 : c₂.nreg 219115 = f2 := v _ by_decide by_decide
  have b13 : c₂.nreg 219113 = γ := by rw [v _ by_decide by_decide, h13]
  have b03 : c₂.nreg 219103 = D := by rw [v _ by_decide by_decide, h03]
  have b04 : c₂.nreg 219104 = g := by rw [v _ by_decide by_decide, h04]
  have b41 : c₂.nreg 219141 = 1 := by rw [v _ by_decide by_decide, hK.r41]
  obtain ⟨c₃, k₃, e₃, hk₃, r0, r1, r2, r3, r4, r5, r6, r7, r9, m₃⟩ :=
    mgArgs_exec (P := P) c₂ hw₂ b10 b14 d37 b11 b15 b13 b03 b04 b41 by_omega by_omega
      by_omega hγW
  zuboe
  have g₃ := exec_frameB e₃ wr_mgArgs
  have A3 : c₃.nreg ALLOC = A₀ + 6 := by rw [g₃.1 _ by_decide]; exact dA
  have ag₃ : ztfal := fun a ha => by_grind
  have hHA₃ := hHA c₃.nmem ag₃
  obtain ⟨b1h, b1⟩ := hd1 c₃.nmem ag₃
  obtain ⟨b2h, b2⟩ := hd2 c₃.nmem ag₃
  have hN1₃ : NFWithin c₃.nmem f1 zterl N1 := by
    zuowd; exact (hN1.transport ag₃).mono by_omega
  have hN2₃ : NFWithin c₃.nmem f2 zterl N2 := by
    zuowd; exact (hN2.transport ag₃).mono by_omega
  have hX₃ : X.holds P c₃.nmem (rd c₃ bMerge 9) zterl := by
    rw [show rd c₃ bMerge 9 = g from r9, A3]
    exact X.mono P _ _ _ _ by_omega (X.local_ P c.nmem c₃.nmem g A₀ by_grind hX)
  have hcap₃ := hXc P c.nmem c₃.nmem g A₀ ag₃ hX
  have hTD₃ := hΦ c₃.nmem by_grind
  have pre :=
    mergePreR hG hWn hX₃ (by rw [show rd c₃ bMerge 9 = g from r9, hcap₃,
      show rd c₃ bMerge 5 = γ from r5]; omega) (by rw [show rd c₃ bMerge 7 = D from r7]; exact hD)
      (by rw [show rd c₃ bMerge 5 = γ from r5, show rd c₃ bMerge 6 = γ + 1 from r6, hfl])
      hHA₃ hHok hwf hreg hsimp by_omega b1 b1h by_omega b2 b2h by_omega hcons hlen
      by_omega by_grind hTD₃.2.2 hTD₃.2.1 by_omega
      r0 r1 r2 r3 r4 hN1₃ hN2₃ ztdgu
      ztdgu
      zthfb
      zthfb hgen
      ztdgu
  have hmc : mergeCost κ F G Hf c₃ =
      mgCostV κ F G Hf D N1.chords.length N2.chords.length γ ztkap := by
    have x1 := hN1₃.nfAt.1
    have x2 := hN2₃.nfAt.1
    have x3 : c₃.nmem (A₀ + 1 + 2) = ma + mp := by
      grind
    unfold mergeCost mgCostV
    rw [show rd c₃ bMerge 7 = D from r7, show rd c₃ bMerge 3 = f1 from r3,
      show rd c₃ bMerge 4 = f2 from r4, show rd c₃ bMerge 5 = γ from r5,
      show rd c₃ bMerge 2 = A₀ + 1 from r2, x1, x2, x3]
  obtain ⟨c₄, k₄, e₄, hk₄, post, fr₄⟩ := hM P W c₃ hw₃ pre
    by_grind
  have hk₄' : k₄ ≤ mgCostV κ F G Hf D N1.chords.length N2.chords.length γ ztkap := by
    grind
  zubwq
  -- the new normal form
  have hJA : JunctionAt c₃.nmem (rd c₃ bMerge 0) (rd c₃ bMerge 1) (rd c₃ bMerge 2) zta H
      ztfsv := by
    zusk
    · rw [show rd c₃ bMerge 0 = D1 + 1 from r0, jOf_left]; exact b1
    · rw [show rd c₃ bMerge 1 = D2 + 1 from r1, jOf_right hlen hP21 hcons]; exact b2
    · rw [show rd c₃ bMerge 2 = A₀ + 1 from r2]; grind
  obtain ⟨N, hN8, hNW8, hNc⟩ := post H ztfsv N1 N2 hJA
    (by rw [show rd c₃ bMerge 3 = f1 from r3]; exact hN1₃.nfAt)
    (by rw [show rd c₃ bMerge 4 = f2 from r4]; exact hN2₃.nfAt)
  rw [show rd c₃ bMerge 6 = γ + 1 from r6, show rd c₃ bMerge 7 = D from r7] at hNc
  -- the band-21 registers survive the merge
  have hmb : ∀ q, bandOf q = bDownDrv → c₄.nreg q = c₃.nreg q := fun q hq => by
    refine fr₄.1 q (by zvnck; decide) ?_
    zvmxo at hq; unfold ALLOC; omega
  have q37 : c₄.nreg 219137 = A₀ := by
    zucem
  have q12 : c₄.nreg 219112 = ma := by
    rw [hmb _ by_decide, g₃.1 _ by_decide, v _ by_decide by_decide, h12]
  have q16 : c₄.nreg 219116 = mp := by
    rw [hmb _ by_decide, g₃.1 _ by_decide, v _ by_decide by_decide, h16]
  have q13 : c₄.nreg 219113 = γ := by
    zucem
  have q41 : c₄.nreg 219141 = 1 := by
    zucem
  obtain ⟨c₅, k₅, e₅, hk₅, o10, o11, o12, o13⟩ :=
    mgOut_exec (P := P) c₄ hw₄ q37 q12 q16 q13 q41 by_omega hγW
  have g₅ := exec_frameB e₅ wr_mgOut
  have A5 : ztcrj := g₅.1 _ by_decide
  have A4 : A₀ + 6 ≤ c₄.nreg ALLOC := by have := fr₄.2.2.2.2.2.1; omega
  have m5 : ∀ a, a < A₀ + 6 → c₅.nmem a = c₂.nmem a := fun a ha => by
    rw [g₅.2.2.1, fr₄.2.2.1 a by_omega, m₃]
  have hΦ5 : Robust ztvnz c₅.nmem (fun m => m A₀ = 0 ∧ m _ = HB ∧
      ChainDescAt m _ _ H (jOf C1 C2 hlen).whole) := fun m' hm' =>
    hΦ m' (fun a ha => (hm' a by_omega).trans (m5 a ha))
  have ag₅ := fun a ha => (m5 a by_omega).trans (hag a ha)
  -- the frame
  have hB21 : ∀ r, bandOf r = bDownDrv → r ≠ ALLOC := fun r hr => by
    zvmxo at hr; unfold ALLOC; omega
  have F1 : Frame mgBands c c₁ k₁ := NFLoc.frame_of_frameB g₁ (fun r hr => by
    simp only [Btop, Bool.or_eq_true, decide_eq_true_eq] at hr
    unfold mgBands
    zubpr
    · zuefv
      exact ztlvh
    · have : ztiyx := by simp only [bandOf, bSign]; omega
      exact ztdxb
    · have : ztlxm := by simp only [bandOf, bLocate]; omega
      exact ztdxb) k₁
  have F2 : Frame mgBands c₁ c₂ k₂ := by
    refine ⟨fun r hr hra => g₂.1 r ?_, by_grind,
      fun a ha => wlt a (lt_of_lt_of_eq ha aA), by_grind, dout,
      by show c₁.nreg 9999 ≤ c₂.nreg 9999; omega,
      by show c₂.nreg 9999 ≤ c₁.nreg 9999 + k₂; omega⟩
    zuoea
    rintro (rfl | rfl | rfl | rfl)
    · zuitp
    · zuitp
    · zuitp
    · exact hra rfl
  have F3 : Frame mgBands c₂ c₃ k₃ := NFLoc.frame_of_frameB g₃ (fun r hr => by
    simp only [Bargs, decide_eq_true_eq] at hr
    have : ztplr := by simp only [bandOf, bMerge]; omega
    exact ztdxb) k₃
  have F4 : Frame mgBands c₃ c₄ k₄ := fr₄.mono (Finset.subset_insert _ _) le_rfl
  have F5 : Frame mgBands c₄ c₅ k₅ := NFLoc.frame_of_frameB g₅ (fun r hr => by
    simp only [Bout, decide_eq_true_eq] at hr
    zuefv
    exact ztlvh) k₅
  have FF := F1.trans (F2.trans (F3.trans (F4.trans F5)))
  simp only [Finset.union_self] at FF
  refine ⟨c₅, k₁ + ztwqm, .seq e₁ ztbq, by_omega,
    o10, ?_, o12, o13, by_omega, hΦ5, ?_, ⟨N, ?_, hNc⟩, ?_, FF⟩
  · rw [o11]; have : A₀ + 6 ≤ rd c₄ bMerge 8 := by_grind
    zufep
  · refine ⟨by_omega, fun _ => ?_⟩
    obtain ⟨y0, y1, y2⟩ := hΦ5.holds
    exact chainWF_host (hHA c₅.nmem ag₅) hHok hwf by_omega y2 y1 by_omega
      (by rw [jOf_whole_s, jOf_whole_P, hs1]; omega)
  · rw [o11, A5, g₅.2.2.1]; exact hNW8
  · intro q hq hr
    have hq' : 210000 ≤ q ∧ q < 220000 := by zvmxo at hq; omega
    rw [g₅.1 q (by simp only [Bout, decide_eq_false_iff_not]; omega), hmb q hq,
      g₃.1 q (by simp only [Bargs, decide_eq_false_iff_not]; omega),
      v q (by simp only [Btop, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
        (by zuoea; omega)]
