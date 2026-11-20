module

public import Chazelle.Core.SweepEvAcc

/-!
# The sweep (WP-D), stage 3: label lists in registers (RAM)

A label list of at most four region indices is held in a count register `bN` and four registers
`bL … bL + 3`: `lblOf c bN bL`.  `addLab bN bL r` appends the value of `r` unless it is already
listed or the list is full.
-/

namespace Chazelle.Core

namespace SweepEv

open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam

@[expose] public section

/-- The label list held at `bN, bL`. -/
def lblOf (c : Config) (bN bL : ℕ) : List ℕ :=
  (List.range (min (c.nreg bN) 4)).map fun i => c.nreg (bL + i)

/-- Append unless listed or full. -/
def addL (l : List ℕ) (v : ℕ) : List ℕ := if v ∈ l ∨ 4 ≤ l.length then l else l ++ [v]

theorem lblOf_length (c : Config) (bN bL : ℕ) : (lblOf c bN bL).length = min (c.nreg bN) 4 := by
  simp [lblOf]

theorem addL_length_le {l : List ℕ} (h : l.length ≤ 4) (v : ℕ) : (addL l v).length ≤ 4 := by
  unfold addL; split_ifs with h1
  · exact h
  · simp only [List.length_append, List.length_singleton]; push Not at h1; omega

theorem mem_addL {l : List ℕ} {v x : ℕ} : x ∈ addL l v → x ∈ l ∨ x = v := by
  unfold addL; split_ifs
  · exact Or.inl
  · intro h; simpa using h

/-- Run `s` if the registers `r`, `x` differ. -/
def neq (r x : ℕ) (s : Stmt) : Stmt := .ifLtN r x s (.ifLtN x r s .skip)

/-- **Append the value of `r`** to the label list `bN, bL`. -/
def addLab (bN bL r : ℕ) : Stmt :=
  .ifLtN bN K1 (block [.copyN bL r, .constN bN 1])
    (neq r bL (.ifLtN bN K2 (block [.copyN (bL + 1) r, .constN bN 2])
      (neq r (bL + 1) (.ifLtN bN K3 (block [.copyN (bL + 2) r, .constN bN 3])
        (neq r (bL + 2) (.ifLtN bN K4 (block [.copyN (bL + 3) r, .constN bN 4])
          (neq r (bL + 3) .skip)))))))

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

theorem neq_irs {r x : ℕ} {s : Stmt} {K : ℕ} {Q : Config → Prop} (hI : IInv W c₀ c)
    (hs : c.nreg r ≠ c.nreg x → IRS P W c₀ s c K Q) (hq : c.nreg r = c.nreg x → Q c) :
    IRS P W c₀ (neq r x s) c (K + 4) Q := by
  unfold neq
  by_cases h1 : c.nreg r < c.nreg x
  · exact (IRS.ifT h1 (hs (by omega))).mono (by omega) (fun _ h => h)
  · by_cases h2 : c.nreg x < c.nreg r
    · exact (IRS.ifF h1 (IRS.ifT h2 (hs (by omega)))).mono (by omega) (fun _ h => h)
    · exact (IRS.ifF h1 (IRS.ifF h2 (IRS.skip (K := 0) hI (hq (by omega))))).mono (by omega)
        (fun _ h => h)

/-- The registers of a label list. -/
def LblR (bN bL q : ℕ) : Prop := q = bN ∨ (bL ≤ q ∧ q < bL + 4)

/-- Two copies: the result of the block `[copyN (bL + i) r, constN bN (i + 1)]`. -/
theorem lab_set_irs {bN bL r i : ℕ} (hI : IInv W c₀ c) (hsN : IScr bN) (hsL : IScr (bL + i))
    (hne : bN ≠ bL + i) (hW : i + 1 ≤ W) :
    IRS P W c₀ (block [.copyN (bL + i) r, .constN bN (i + 1)]) c 2 (fun c' =>
      c'.nreg (bL + i) = c.nreg r ∧ c'.nreg bN = i + 1 ∧
      (∀ q, q ≠ bL + i → q ≠ bN → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  refine (IRS.block [.copyN (bL + i) r, .constN bN (i + 1)] hI ⟨hsL, ⟨hsN, hW⟩, trivial⟩).mono
    le_rfl ?_
  rintro c' rfl
  refine ⟨?_, ?_, fun q h1 h2 => ?_, rfl⟩ <;> simp only [regB, regI]
  · rw [upd_other _ _ _ (Ne.symm hne), upd_same]
  · exact upd_same _ _ _
  · rw [upd_other _ _ _ h2, upd_other _ _ _ h1]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- **Appending a label.** -/
theorem addLab_irs {bN bL r : ℕ} (hI : IInv W c₀ c) (hK : Consts c) (hsN : IScr bN)
    (hsL : ∀ i, i < 4 → IScr (bL + i)) (hNL : ∀ i, i < 4 → bN ≠ bL + i)
    (_hrN : r ≠ bN) (_hrL : ∀ i, i < 4 → r ≠ bL + i)
    (hKN : ∀ k, k = K1 ∨ k = K2 ∨ k = K3 ∨ k = K4 → ¬ LblR bN bL k)
    (hN : c.nreg bN ≤ 4) (hW : 4 ≤ W) :
    IRS P W c₀ (addLab bN bL r) c 30 (fun c' => c'.nreg bN ≤ 4 ∧
      lblOf c' bN bL = addL (lblOf c bN bL) (c.nreg r) ∧
      (∀ q, ¬ LblR bN bL q → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  obtain ⟨-, k1, -, k4, -, k2, k3⟩ := hK
  have kK : ∀ k, k = K1 ∨ k = K2 ∨ k = K3 ∨ k = K4 → ∀ c' : Config,
      (∀ q, ¬ LblR bN bL q → c'.nreg q = c.nreg q) → c'.nreg k = c.nreg k :=
    fun k hk c' h => h k (hKN k hk)
  have lbl : ∀ c' : Config, lblOf c' bN bL =
      (List.range (min (c'.nreg bN) 4)).map fun i => c'.nreg (bL + i) := fun _ => rfl
  have hlen : (lblOf c bN bL).length = c.nreg bN := by rw [lblOf_length]; omega
  -- the frame of a set
  have setFr : ∀ i, i < 4 → ∀ c' : Config, (∀ q, q ≠ bL + i → q ≠ bN → c'.nreg q = c.nreg q) →
      ∀ q, ¬ LblR bN bL q → c'.nreg q = c.nreg q := fun i hi c' h q hq =>
    h q (fun h' => hq (Or.inr ⟨by omega, by omega⟩)) (fun h' => hq (Or.inl h'))
  unfold addLab
  generalize hn : c.nreg bN = n at hN hlen
  interval_cases n
  · -- empty list
    refine (IRS.ifT (by rw [hn, k1]; norm_num) (lab_set_irs (i := 0) hI hsN (hsL 0 (by norm_num))
      (hNL 0 (by norm_num)) (by omega))).mono (by norm_num) ?_
    rintro c' ⟨v1, v2, v3, v4⟩
    refine ⟨by omega, ?_, setFr 0 (by norm_num) c' v3, v4⟩
    rw [lbl c', lbl c, v2, hn]
    simp only [Nat.add_zero] at v1
    simp [addL, v1]
  -- the outcome "unchanged"
  · -- one label
    have hl : lblOf c bN bL = [c.nreg bL] := by rw [lbl c, hn]; simp
    refine IRS.mono (K := 28 + 2) (IRS.ifF (by rw [hn, k1]; norm_num) ?_) le_rfl (fun _ h => h)
    refine IRS.mono (K := 24 + 4) (neq_irs hI (fun hne => ?_) (fun heq => ?_)) le_rfl (fun _ h => h)
    · refine IRS.mono (K := 2 + 2) (IRS.ifT (by rw [hn, k2]; norm_num) (lab_set_irs (i := 1) hI hsN
        (hsL 1 (by norm_num)) (hNL 1 (by norm_num)) (by omega))) (by norm_num) ?_
      rintro c' ⟨v1, v2, v3, v4⟩
      refine ⟨by omega, ?_, setFr 1 (by norm_num) c' v3, v4⟩
      have e0 : c'.nreg bL = c.nreg bL := v3 _ (by omega) (fun h => hNL 0 (by norm_num) (by rw [h]; rfl))
      rw [lbl c', v2, hl]
      simp [addL, List.range_succ, e0, v1, hne]
    · exact ⟨by omega, by rw [hl]; simp [addL, heq], fun _ _ => rfl, rfl⟩
  · -- two labels
    have hl : lblOf c bN bL = [c.nreg bL, c.nreg (bL + 1)] := by rw [lbl c, hn]; simp [List.range_succ]
    refine IRS.mono (K := 28 + 2) (IRS.ifF (by rw [hn, k1]; norm_num) ?_) le_rfl (fun _ h => h)
    refine IRS.mono (K := 24 + 4) (neq_irs hI (fun hne => ?_) (fun heq => ?_)) le_rfl (fun _ h => h)
    · refine IRS.mono (K := 22 + 2) (IRS.ifF (by rw [hn, k2]; norm_num) ?_) le_rfl (fun _ h => h)
      refine IRS.mono (K := 18 + 4) (neq_irs hI (fun hne' => ?_) (fun heq => ?_)) le_rfl (fun _ h => h)
      · refine IRS.mono (K := 2 + 2) (IRS.ifT (by rw [hn, k3]; norm_num) (lab_set_irs (i := 2) hI hsN
          (hsL 2 (by norm_num)) (hNL 2 (by norm_num)) (by omega))) (by norm_num) ?_
        rintro c' ⟨v1, v2, v3, v4⟩
        refine ⟨by omega, ?_, setFr 2 (by norm_num) c' v3, v4⟩
        have e0 : c'.nreg bL = c.nreg bL := v3 _ (by omega) (fun h => hNL 0 (by norm_num) (by rw [h]; rfl))
        have e1 : c'.nreg (bL + 1) = c.nreg (bL + 1) :=
          v3 _ (by omega) (fun h => hNL 1 (by norm_num) h.symm)
        rw [lbl c', v2, hl]
        simp [addL, List.range_succ, e0, e1, v1, hne, hne']
      · exact ⟨by omega, by rw [hl]; simp [addL, heq], fun _ _ => rfl, rfl⟩
    · exact ⟨by omega, by rw [hl]; simp [addL, heq], fun _ _ => rfl, rfl⟩
  · -- three labels
    have hl : lblOf c bN bL = [c.nreg bL, c.nreg (bL + 1), c.nreg (bL + 2)] := by
      rw [lbl c, hn]; simp [List.range_succ]
    refine IRS.mono (K := 28 + 2) (IRS.ifF (by rw [hn, k1]; norm_num) ?_) le_rfl (fun _ h => h)
    refine IRS.mono (K := 24 + 4) (neq_irs hI (fun hne => ?_) (fun heq => ?_)) le_rfl (fun _ h => h)
    · refine IRS.mono (K := 22 + 2) (IRS.ifF (by rw [hn, k2]; norm_num) ?_) le_rfl (fun _ h => h)
      refine IRS.mono (K := 18 + 4) (neq_irs hI (fun hne' => ?_) (fun heq => ?_)) le_rfl (fun _ h => h)
      · refine IRS.mono (K := 16 + 2) (IRS.ifF (by rw [hn, k3]; norm_num) ?_) (by norm_num)
          (fun _ h => h)
        refine IRS.mono (K := 12 + 4) (neq_irs hI (fun hne'' => ?_) (fun heq => ?_)) le_rfl
          (fun _ h => h)
        · refine IRS.mono (K := 2 + 2) (IRS.ifT (by rw [hn, k4]; norm_num) (lab_set_irs (i := 3) hI
            hsN (hsL 3 (by norm_num)) (hNL 3 (by norm_num)) (by omega))) (by norm_num) ?_
          rintro c' ⟨v1, v2, v3, v4⟩
          refine ⟨by omega, ?_, setFr 3 (by norm_num) c' v3, v4⟩
          have e0 : c'.nreg bL = c.nreg bL :=
            v3 _ (by omega) (fun h => hNL 0 (by norm_num) (by rw [h]; rfl))
          have e1 : c'.nreg (bL + 1) = c.nreg (bL + 1) :=
            v3 _ (by omega) (fun h => hNL 1 (by norm_num) h.symm)
          have e2 : c'.nreg (bL + 2) = c.nreg (bL + 2) :=
            v3 _ (by omega) (fun h => hNL 2 (by norm_num) h.symm)
          rw [lbl c', v2, hl]
          simp [addL, List.range_succ, e0, e1, e2, v1, hne, hne', hne'']
        · exact ⟨by omega, by rw [hl]; simp [addL, heq], fun _ _ => rfl, rfl⟩
      · exact ⟨by omega, by rw [hl]; simp [addL, heq], fun _ _ => rfl, rfl⟩
    · exact ⟨by omega, by rw [hl]; simp [addL, heq], fun _ _ => rfl, rfl⟩
  · -- full
    have hl4 : (lblOf c bN bL).length = 4 := hlen
    have hfull : ∀ v, addL (lblOf c bN bL) v = lblOf c bN bL := fun v => by
      unfold addL; rw [ite_eq_left (Or.inr (by omega))]
    have hun : ∀ (K : ℕ), IRS P W c₀ .skip c K (fun c' => c'.nreg bN ≤ 4 ∧
        lblOf c' bN bL = addL (lblOf c bN bL) (c.nreg r) ∧
        (∀ q, ¬ LblR bN bL q → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := fun K =>
      IRS.skip hI ⟨by omega, (hfull _).symm, fun _ _ => rfl, rfl⟩
    have hq : c.nreg bN ≤ 4 ∧ lblOf c bN bL = addL (lblOf c bN bL) (c.nreg r) ∧
        (∀ q, ¬ LblR bN bL q → c.nreg q = c.nreg q) ∧ c.nmem = c.nmem :=
      ⟨by omega, (hfull _).symm, fun _ _ => rfl, rfl⟩
    refine IRS.mono (K := 28 + 2) (IRS.ifF (by rw [hn, k1]; norm_num) ?_) le_rfl (fun _ h => h)
    refine IRS.mono (K := 24 + 4) (neq_irs hI (fun _ => ?_) (fun _ => hq)) le_rfl (fun _ h => h)
    refine IRS.mono (K := 22 + 2) (IRS.ifF (by rw [hn, k2]; norm_num) ?_) le_rfl (fun _ h => h)
    refine IRS.mono (K := 18 + 4) (neq_irs hI (fun _ => ?_) (fun _ => hq)) le_rfl (fun _ h => h)
    refine IRS.mono (K := 16 + 2) (IRS.ifF (by rw [hn, k3]; norm_num) ?_) (by norm_num) (fun _ h => h)
    refine IRS.mono (K := 12 + 4) (neq_irs hI (fun _ => ?_) (fun _ => hq)) le_rfl (fun _ h => h)
    refine IRS.mono (K := 10 + 2) (IRS.ifF (by rw [hn, k4]; norm_num) ?_) (by norm_num) (fun _ h => h)
    exact IRS.mono (K := 0 + 4) (neq_irs hI (fun _ => hun 0) (fun _ => hq)) (by norm_num)
      (fun _ h => h)

end

end SweepEv

end Chazelle.Core
