module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.OracleZipMath

/-!
# Lemma 3.6 (WP-H), preprocessing part 1: sorting indices by two stored keys

`lexCmp` is a comparator for `SortR.sortStmt`: items `i < K` are compared by the pair of stored
keys `(K1[i], K2[i])` lexicographically (bases in `115000`, `115001`, the bound `K` in `115005`);
items `≥ K` come after, in their natural order.  `lexCmp_ok`: its contract `SortR.CmpOK`.
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

/-- The lexicographic order of the stored key pairs. -/
def lexLe (m : ℕ → ℕ) (B1 B2 K a b : ℕ) : Bool :=
  if a < K then
    (if b < K then decide (m (B1 + a) < m (B1 + b) ∨ (m (B1 + a) = m (B1 + b) ∧
      m (B2 + a) ≤ m (B2 + b))) else true)
  else (if b < K then false else decide (a ≤ b))

section
variable (m : ℕ → ℕ)
theorem lexLe_total (B1 B2 K a b : ℕ) :
    (lexLe m B1 B2 K a b || lexLe m B1 B2 K b a) = true := by
  unfold lexLe
  ram_grind

theorem lexLe_trans (B1 B2 K a b c : ℕ) (h1 : lexLe m B1 B2 K a b = true)
    (h2 : lexLe m B1 B2 K b c = true) : lexLe m B1 B2 K a c = true := by
  unfold lexLe at *
  ram_grind


end

/-- **The comparator.** -/
def lexCmp : Stmt :=
  .ifLtN 30000 115005
    (.ifLtN 30001 115005
      (.seq (block [.addN 115002 115000 30000, .loadN 115003 115002, .addN 115002 115000 30001,
          .loadN 115004 115002])
        (.ifLtN 115003 115004 (.instr (.constN 30002 1))
          (.ifLtN 115004 115003 (.instr (.constN 30002 0))
            (.seq (block [.addN 115002 115001 30000, .loadN 115003 115002,
                .addN 115002 115001 30001, .loadN 115004 115002])
              (.ifLtN 115004 115003 (.instr (.constN 30002 0)) (.instr (.constN 30002 1)))))))
      (.instr (.constN 30002 1)))
    (.ifLtN 30001 115005 (.instr (.constN 30002 0))
      (.ifLtN 30001 30000 (.instr (.constN 30002 0)) (.instr (.constN 30002 1))))

section
variable (m₀ : ℕ → ℕ) (A₀ B1 B2 K : ℕ)
include m₀ A₀ B1 B2 K
/-- The invariant of the comparator: the bases, the bound and the memory below `A₀`. -/
def LexJ (c : Config) : Prop :=
  c.nreg 115000 = B1 ∧ c.nreg 115001 = B2 ∧ c.nreg 115005 = K ∧ ∀ a, a < A₀ → c.nmem a = m₀ a

theorem lexJ_stable : SortR.JStable (LexJ m₀ A₀ B1 B2 K) A₀ := by
  intro c c' ⟨h1, h2, h3, h4⟩ hr _ hm _ _
  grind [Chazelle.Core.OracleR.LexJ, bandOf, bSort, ALLOC]


end

/-- **The contract of the comparator.** -/
theorem lexCmp_ok {P : Polygon} {W : ℕ} {m₀ : ℕ → ℕ} {A₀ B1 B2 K : ℕ}
    (hB1 : B1 + K ≤ A₀) (hB2 : B2 + K ≤ A₀) (hW : 1 ≤ W) (hAW : A₀ ≤ W) :
    SortR.CmpOK P W lexCmp {11} (LexJ m₀ A₀ B1 B2 K) (lexLe m₀ B1 B2 K) 20 := by
  intro c hw ⟨j1, j2, j3, j4⟩
  have hwr : wr (fun r => decide (r = 30002) || decide (115002 ≤ r ∧ r ≤ 115004)) lexCmp = true := by
    decide
  suffices H : ∃ c' k, Exec P W lexCmp c c' k ∧ k ≤ 20 ∧
      c'.nreg 30002 = (if lexLe m₀ B1 B2 K (c.nreg 30000) (c.nreg 30001) then 1 else 0) by
    obtain ⟨c', k, ex, hk, hbit⟩ := H
    have f := exec_frameB ex hwr
    have fr := WalkKey.exec_rframe ex (B := fun _ => false) (by decide)
    refine ⟨c', k, ex, hk, ⟨?_, ?_, ?_, fun a ha => by ram_grind⟩, hbit,
      fun r h0 h1 h2 hb => f.1 r ?_, fun r _ => fr r rfl, f.2.2.1, f.2.2.2.1, f.2.2.2.2⟩
    · rw [f.1 _ (by decide)]; exact j1
    · rw [f.1 _ (by decide)]; exact j2
    · rw [f.1 _ (by decide)]; exact j3
    grind [Bool.or_eq_false_iff, decide_eq_false_iff_not, Finset.mem_singleton, bandOf, ALLOC]
  
  unfold lexCmp lexLe
  
  by_cases ha : c.nreg 30000 < K
  · refine spec_ifLtN_true (by omega) ?_
    by_cases hb : c.nreg 30001 < K
    · refine spec_ifLtN_true (by omega) ?_
      set a := c.nreg 30000
      set b := c.nreg 30001
      
      
      
      
      obtain ⟨c₁, k₁, e₁, hk₁, v3, v4, r₁, m₁⟩ : ∃ c₁ k₁, Exec P W (block [.addN 115002 115000 30000,
          .loadN 115003 115002, .addN 115002 115000 30001, .loadN 115004 115002]) c c₁ k₁ ∧ k₁ = 4 ∧
          c₁.nreg 115003 = m₀ (B1 + a) ∧ c₁.nreg 115004 = m₀ (B1 + b) ∧
          (∀ r, r < 115002 ∨ 115004 < r → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem := by
        exec_block
        · omega
        · config_simp; omega
        · refine ⟨rfl, ?_, ?_, fun r hr => ?_, rfl⟩
          · ram_simp <;> omega_nf
          · ram_simp <;> omega_nf
          · config_simp; upd_solve
      have w₁ := e₁.wb_right
      refine spec_seq ⟨c₁, k₁, e₁, ?_⟩
      by_cases hlt : m₀ (B1 + a) < m₀ (B1 + b)
      · refine spec_ifLtN_true (by omega) (spec_instr (Exec.constN w₁ _ _ hW)
          fun _ => ⟨by omega, ?_⟩)
        simp_all
      refine spec_ifLtN_false (by omega) ?_
      by_cases hgt : m₀ (B1 + b) < m₀ (B1 + a)
      · refine spec_ifLtN_true (by omega) (spec_instr (Exec.constN w₁ 30002 0
          (Nat.zero_le _)) fun _ => ⟨by omega, ?_⟩)
        simp [ha, hb, hlt]; omega
      refine spec_ifLtN_false (by omega) ?_
      have heq : m₀ (B1 + a) = m₀ (B1 + b) := by omega
      obtain ⟨c₂, k₂, e₂, hk₂, u3, u4⟩ : ∃ c₂ k₂, Exec P W (block [.addN 115002 115001 30000,
          .loadN 115003 115002, .addN 115002 115001 30001, .loadN 115004 115002]) c₁ c₂ k₂ ∧
          k₂ = 4 ∧ c₂.nreg 115003 = m₀ (B2 + a) ∧ c₂.nreg 115004 = m₀ (B2 + b) := by
        have g1 : c₁.nreg 115001 = B2 := by simp_all
        have g2 : c₁.nreg 30000 = a := r₁ _ (by omega)
        have g3 : c₁.nreg 30001 = b := r₁ _ (by omega)
        exec_block
        · omega
        · config_simp; omega
        ram_simp 
      have w₂ := e₂.wb_right
      refine spec_seq ⟨c₂, k₂, e₂, ?_⟩
      by_cases h2 : m₀ (B2 + b) < m₀ (B2 + a)
      · refine spec_ifLtN_true (by omega) (spec_instr (Exec.constN w₂ 30002 0
          (Nat.zero_le _)) fun _ => ⟨by omega, ?_⟩)
        simp_all
      · refine spec_ifLtN_false (by omega) (spec_instr (Exec.constN w₂ _ _ hW)
          fun _ => ⟨by omega, ?_⟩)
        simp_all
    · refine spec_ifLtN_false (by omega) (spec_instr (Exec.constN hw _ _ hW) fun _ =>
        ⟨by omega, ?_⟩)
      simp_all
  · refine spec_ifLtN_false (by omega) ?_
    by_cases hb : c.nreg 30001 < K
    · refine spec_ifLtN_true (by omega) (spec_instr (Exec.constN hw _ _ (by omega))
        fun _ => ⟨by omega, ?_⟩)
      simp_all
    · refine spec_ifLtN_false (by omega) ?_
      by_cases hc : c.nreg 30001 < c.nreg 30000
      · refine spec_ifLtN_true hc (spec_instr (Exec.constN hw _ _ (by omega)) fun _ =>
          ⟨by omega, ?_⟩)
        simp [ha, hb]; omega
      · refine spec_ifLtN_false hc (spec_instr (Exec.constN hw _ _ hW) fun _ => ⟨by omega, ?_⟩)
        simp_all

end

end OracleR

end Chazelle.Core
