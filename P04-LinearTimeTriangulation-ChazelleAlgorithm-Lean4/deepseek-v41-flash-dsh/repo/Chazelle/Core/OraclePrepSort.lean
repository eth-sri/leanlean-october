module

public import Chazelle.Golf

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

theorem lexLe_total (m : ℕ → ℕ) (B1 B2 K a b : ℕ) :
    (lexLe m B1 B2 K a b || lexLe m B1 B2 K b a) = true := by
  unfold lexLe
  split_ifs <;> simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.or_true,
    Bool.or_false] <;> omega

theorem lexLe_trans (m : ℕ → ℕ) (B1 B2 K a b c : ℕ) (h1 : lexLe m B1 B2 K a b = true)
    (h2 : lexLe m B1 B2 K b c = true) : lexLe m B1 B2 K a c = true := by
  unfold lexLe at *
  split_ifs at h1 h2 ⊢ <;> simp only [decide_eq_true_eq] at h1 h2 ⊢ <;> omega

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

/-- The invariant of the comparator: the bases, the bound and the memory below `A₀`. -/
def LexJ (m₀ : ℕ → ℕ) (A₀ B1 B2 K : ℕ) (c : Config) : Prop :=
  c.nreg 115000 = B1 ∧ c.nreg 115001 = B2 ∧ c.nreg 115005 = K ∧ ∀ a, a < A₀ → c.nmem a = m₀ a

theorem lexJ_stable (m₀ : ℕ → ℕ) (A₀ B1 B2 K : ℕ) : SortR.JStable (LexJ m₀ A₀ B1 B2 K) A₀ := by
  intro c c' ⟨h1, h2, h3, h4⟩ hr _ hm _ _
  have hb : ∀ r, 115000 ≤ r → r < 116000 → c'.nreg r = c.nreg r := fun r a b =>
    hr r (by unfold bandOf bSort; omega) (by unfold ALLOC; omega)
  exact ⟨by rw [hb _ (⊛) (⊛)]; exact h1,
    by rw [hb _ (⊛) (⊛)]; exact h2,
    by rw [hb _ (⊛) (⊛)]; exact h3, fun a ha => (hm a ha).trans (h4 a ha)⟩

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
    have fr := WalkKey.exec_rframe ex (B := fun _ => false) (⌖)
    refine ⟨c', k, ex, hk, ⟨?_, ?_, ?_, fun a ha => by rw [f.2.2.1]; exact j4 a ha⟩, hbit,
      fun r h0 h1 h2 hb => f.1 r ?_, fun r _ => fr r rfl, f.2.2.1, f.2.2.2.1, f.2.2.2.2⟩
    · rw [f.1 _ (⌖)]; exact j1
    · rw [f.1 _ (⌖)]; exact j2
    · rw [f.1 _ (⌖)]; exact j3
    · ϴ Bool.or_eq_false_iff, decide_eq_false_iff_not
      refine ⟨h2, fun h => ?_⟩
      rcases hb with hb | hb
      · exact hb (by rw [Finset.mem_singleton]; unfold bandOf; omega)
      · unfold ALLOC at hb; omega
  have h1 : c.nreg 115005 = K := j3
  unfold lexCmp lexLe
  have hW' := hW
  by_cases ha : c.nreg 30000 < K
  · refine spec_ifLtN_true (by rw [h1]; exact ha) ?_
    by_cases hb : c.nreg 30001 < K
    · refine spec_ifLtN_true (by rw [h1]; exact hb) ?_
      set a := c.nreg 30000
      set b := c.nreg 30001
      have ma : c.nmem (B1 + a) = m₀ (B1 + a) := j4 _ (⋄)
      have mb : c.nmem (B1 + b) = m₀ (B1 + b) := j4 _ (⋄)
      have ma2 : c.nmem (B2 + a) = m₀ (B2 + a) := j4 _ (⋄)
      have mb2 : c.nmem (B2 + b) = m₀ (B2 + b) := j4 _ (⋄)
      obtain ⟨c₁, k₁, e₁, hk₁, v3, v4, r₁, m₁⟩ : ∃ c₁ k₁, Exec P W (block [.addN 115002 115000 30000,
          .loadN 115003 115002, .addN 115002 115000 30001, .loadN 115004 115002]) c c₁ k₁ ∧ k₁ = 4 ∧
          c₁.nreg 115003 = m₀ (B1 + a) ∧ c₁.nreg 115004 = m₀ (B1 + b) ∧
          (∀ r, r < 115002 ∨ 115004 < r → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem := by
        exec_block
        · rw [j1]; omega
        · config_simp; rw [j1]; omega
        · refine ⟨rfl, ?_, ?_, fun r hr => ?_, rfl⟩
          · config_simp; rw [j1, ← ma]
          · config_simp; rw [j1, ← mb]
          · config_simp; upd_solve
      have w₁ := e₁.wb_right
      refine spec_seq ⟨c₁, k₁, e₁, ?_⟩
      by_cases hlt : m₀ (B1 + a) < m₀ (B1 + b)
      · refine spec_ifLtN_true (by rw [v3, v4]; exact hlt) (spec_instr (Exec.constN w₁ _ _ hW)
          fun _ => ⟨⋄, ?_⟩)
        Θ ha, hb, hlt
      refine spec_ifLtN_false (by rw [v3, v4]; exact hlt) ?_
      by_cases hgt : m₀ (B1 + b) < m₀ (B1 + a)
      · refine spec_ifLtN_true (by rw [v3, v4]; exact hgt) (spec_instr (Exec.constN w₁ 30002 0
          (Nat.zero_le _)) fun _ => ⟨⋄, ?_⟩)
        simp [ha, hb, hlt]; omega
      refine spec_ifLtN_false (by rw [v3, v4]; exact hgt) ?_
      have heq : m₀ (B1 + a) = m₀ (B1 + b) := ⋄
      obtain ⟨c₂, k₂, e₂, hk₂, u3, u4⟩ : ∃ c₂ k₂, Exec P W (block [.addN 115002 115001 30000,
          .loadN 115003 115002, .addN 115002 115001 30001, .loadN 115004 115002]) c₁ c₂ k₂ ∧
          k₂ = 4 ∧ c₂.nreg 115003 = m₀ (B2 + a) ∧ c₂.nreg 115004 = m₀ (B2 + b) := by
        have g1 : c₁.nreg 115001 = B2 := by rw [r₁ _ (⋄)]; exact j2
        have g2 : c₁.nreg 30000 = a := r₁ _ (⋄)
        have g3 : c₁.nreg 30001 = b := r₁ _ (⋄)
        exec_block
        · rw [g1, g2]; omega
        · config_simp; rw [g1, g3]; omega
        · refine ⟨rfl, ?_, ?_⟩
          · config_simp; rw [g1, g2, m₁, ← ma2]
          · config_simp; rw [g1, g3, m₁, ← mb2]
      have w₂ := e₂.wb_right
      refine spec_seq ⟨c₂, k₂, e₂, ?_⟩
      by_cases h2 : m₀ (B2 + b) < m₀ (B2 + a)
      · refine spec_ifLtN_true (by rw [u3, u4]; exact h2) (spec_instr (Exec.constN w₂ 30002 0
          (Nat.zero_le _)) fun _ => ⟨⋄, ?_⟩)
        simp [ha, hb, heq]; omega
      · refine spec_ifLtN_false (by rw [u3, u4]; exact h2) (spec_instr (Exec.constN w₂ _ _ hW)
          fun _ => ⟨⋄, ?_⟩)
        simp [ha, hb, heq]; omega
    · refine spec_ifLtN_false (by rw [h1]; exact hb) (spec_instr (Exec.constN hw _ _ hW) fun _ =>
        ⟨⋄, ?_⟩)
      Θ ha, hb
  · refine spec_ifLtN_false (by rw [h1]; exact ha) ?_
    by_cases hb : c.nreg 30001 < K
    · refine spec_ifLtN_true (by rw [h1]; exact hb) (spec_instr (Exec.constN hw _ _ (⋄))
        fun _ => ⟨⋄, ?_⟩)
      Θ ha, hb
    · refine spec_ifLtN_false (by rw [h1]; exact hb) ?_
      by_cases hc : c.nreg 30001 < c.nreg 30000
      · refine spec_ifLtN_true hc (spec_instr (Exec.constN hw _ _ (⋄)) fun _ =>
          ⟨⋄, ?_⟩)
        simp [ha, hb]; omega
      · refine spec_ifLtN_false hc (spec_instr (Exec.constN hw _ _ hW) fun _ => ⟨⋄, ?_⟩)
        simp [ha, hb]; omega

end

end OracleR

end Chazelle.Core
