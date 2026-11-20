/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CountedRecoding

@[expose] public section

namespace VaughtConjecture.Knight

open Value ExtOrd

open Transform

noncomputable section

/-- Greatest target label at a cell of grade at least `k`. -/
def finiteTargetSuppressor
    {D : Type*} [Finite D]
    (grade : D → ℕ) (target : D → ExtOrd) (k : ℕ) : ExtOrd := by
  letI := Fintype.ofFinite D
  exact Finset.univ.sup fun d => if k ≤ grade d then target d else ⊥

theorem finiteTargetSuppressor_antitone
    {D : Type*} [Finite D]
    (grade : D → ℕ) (target : D → ExtOrd) :
    ∀ n m, n < m → finiteTargetSuppressor grade target m ≤
      finiteTargetSuppressor grade target n := by
  classical
  letI := Fintype.ofFinite D
  intro n m hnm
  apply Finset.sup_le
  intro d hd
  by_cases hm : m ≤ grade d
  · have hn : n ≤ grade d := (Nat.le_of_lt hnm).trans hm
    have hterm := Finset.le_sup
      (s := (Finset.univ : Finset D))
      (f := fun e => if n ≤ grade e then target e else ⊥) hd
    aesop
  · simp only [finiteTargetSuppressor, hm, if_false]
    simp

private theorem finset_sup_selfVis
    {A : Type*} (s : Finset A) (f : A → ExtOrd) (k : ℕ)
    (hf : ∀ a ∈ s, f a = extVisibilityReplace (f a) k k) :
    s.sup f = extVisibilityReplace (s.sup f) k k := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih =>
      grind

theorem finiteTargetSuppressor_selfVis
    {D : Type*} [Finite D]
    (grade : D → ℕ) (target : D → ExtOrd)
    (hTarget : IsOrderly grade target) :
    ∀ k, finiteTargetSuppressor grade target k =
      extVisibilityReplace (finiteTargetSuppressor grade target k) k k := by
  classical
  letI := Fintype.ofFinite D
  intro k
  apply finset_sup_selfVis
  intro d _hd
  by_cases hk : k ≤ grade d
  · simp only [hk, if_true]
    have hd : extVisibilityReplace (target d) (grade d) (grade d) = target d :=
      (hTarget d).symm
    exact (selfVis_mono hd hk).symm
  · simp [hk, if_false, extVisibilityReplace]

theorem target_le_finiteTargetSuppressor
    {D : Type*} [Finite D]
    (grade : D → ℕ) (target : D → ExtOrd) (d : D) :
    target d ≤ finiteTargetSuppressor grade target (grade d) := by
  classical
  letI := Fintype.ofFinite D
  have hterm := Finset.le_sup
    (s := (Finset.univ : Finset D))
    (f := fun e => if grade d ≤ grade e then target e else ⊥)
    (Finset.mem_univ d)
  aesop

private theorem isNonSuccessor_limitPart (δ : Ordinal) :
    IsNonSuccessor (limitPart δ) := by
  by_cases h0 : limitPart δ = 0
  · tauto
  · refine Or.inr ?_
    rw [Order.isSuccLimit_iff]
    refine ⟨by simp_all, (Ordinal.isSuccPrelimit_iff_omega0_dvd).2 ?_⟩
    exact ⟨δ / Ordinal.omega0, rfl⟩

private theorem add_omega0_le_of_nonsucc
    {μ ν : Ordinal} (hν : IsNonSuccessor ν) (hμν : μ < ν) :
    μ + Ordinal.omega0 ≤ ν := by
  rcases hν with rfl | hLimit
  · simp at hμν
  · have hFinite : ∀ k : ℕ, μ + (k : Ordinal) < ν := by
      intro k
      induction k with
      | zero => simpa using hμν
      | succ k ih =>
          have hStep : μ + ((k + 1 : ℕ) : Ordinal) =
              Order.succ (μ + (k : Ordinal)) := by
            push_cast
            rw [← add_assoc, ← Order.succ_eq_add_one]
          rw [hStep]
          exact hLimit.succ_lt ih
    rw [Ordinal.add_le_iff_of_isSuccLimit Ordinal.isSuccLimit_omega0]
    intro b hb
    obtain ⟨k, rfl⟩ := Ordinal.lt_omega0.mp hb
    exact (hFinite k).le

/-- Visibility replacement is monotone in its label argument. -/
theorem extVisibilityReplace_mono (k i : ℕ) (hi : i ≤ k) :
    Monotone (fun x : ExtOrd => extVisibilityReplace x k i) := by
  have hOrd : Monotone (fun δ : Ordinal => visibilityReplace δ k i) := by
    intro γ δ hγδ
    by_cases hγ : finitePart γ < k
    · by_cases hδ : finitePart δ < k
      · simp only [visibilityReplace, hγ, hδ, if_true, ordinalReplace]
        exact add_le_add (limitPart_mono hγδ) le_rfl
      · calc
          visibilityReplace γ k i ≤ δ :=
            visReplace_le_of_le_selfVis hγδ (Nat.not_lt.mp hδ) hi
          _ = visibilityReplace δ k i := by grind [visibilityReplace]
    · by_cases hδ : finitePart δ < k
      · simp only [visibilityReplace, hγ, hδ, if_false, if_true, ordinalReplace]
        have hLimitLe : limitPart γ ≤ limitPart δ := limitPart_mono hγδ
        have hLimitNe : limitPart γ ≠ limitPart δ := by
          intro hEq
          have hFiniteLe : finitePart γ ≤ finitePart δ := by
            have hDecomp : limitPart γ + (finitePart γ : Ordinal) ≤
                limitPart γ + (finitePart δ : Ordinal) := by
              calc
                limitPart γ + (finitePart γ : Ordinal) = γ := decomposition γ
                _ ≤ δ := hγδ
                _ = limitPart δ + (finitePart δ : Ordinal) := (decomposition δ).symm
                _ = limitPart γ + (finitePart δ : Ordinal) := by tauto
            simp_all
          omega
        have hLimitLt : limitPart γ < limitPart δ :=
          lt_of_le_of_ne hLimitLe hLimitNe
        have hBlockSep : limitPart γ + Ordinal.omega0 ≤ limitPart δ :=
          add_omega0_le_of_nonsucc (isNonSuccessor_limitPart δ) hLimitLt
        have hGammaLtBlock : γ < limitPart γ + Ordinal.omega0 := by
          calc
            γ = limitPart γ + (finitePart γ : Ordinal) := (decomposition γ).symm
            _ < limitPart γ + Ordinal.omega0 :=
              by simp
        exact hGammaLtBlock.le.trans (hBlockSep.trans le_self_add)
      grind [visibilityReplace]
  intro x y hxy
  match x, y with
  | ⊥, _ => simp
  | some ⊤, ⊥ =>
      assumption
  | some ⊤, some ⊤ => rfl
  | some ⊤, some (some δ) =>
      trivial
  | some (some γ), ⊥ =>
      trivial
  | some (some γ), some ⊤ => tauto
  | some (some γ), some (some δ) =>
      exact WithBot.coe_le_coe.mpr <| WithTop.coe_le_coe.mpr <| hOrd <|
        WithTop.coe_le_coe.mp <| WithBot.coe_le_coe.mp hxy

/-- Greatest prescribed output at an input below `x`. -/
def finiteLowerEnvelope
    (s : Finset ExtOrd) (table : ExtOrd → ExtOrd) (x : ExtOrd) : ExtOrd :=
  s.sup fun y => if y ≤ x then table y else ⊥

theorem finiteLowerEnvelope_mono
    (s : Finset ExtOrd) (table : ExtOrd → ExtOrd) :
    Monotone (finiteLowerEnvelope s table) := by
  intro x y hxy
  apply Finset.sup_le
  intro a ha
  by_cases hax : a ≤ x
  · have hay : a ≤ y := hax.trans hxy
    have hterm := Finset.le_sup
      (s := s) (f := fun z => if z ≤ y then table z else ⊥) ha
    aesop
  · simp only [finiteLowerEnvelope, hax, if_false]
    simp

theorem finiteLowerEnvelope_bot
    (s : Finset ExtOrd) (table : ExtOrd → ExtOrd)
    (hBot : ∀ y ∈ s, y = ⊥ → table y = ⊥) :
    finiteLowerEnvelope s table ⊥ = ⊥ := by
  apply le_antisymm
  · apply Finset.sup_le
    aesop
  simp

theorem finiteLowerEnvelope_source
    (s : Finset ExtOrd) (table : ExtOrd → ExtOrd)
    (hMono : ∀ a ∈ s, ∀ b ∈ s, a ≤ b → table a ≤ table b)
    {x : ExtOrd} (hx : x ∈ s) :
    finiteLowerEnvelope s table x = table x := by
  apply le_antisymm
  · apply Finset.sup_le
    aesop
  · have hterm := Finset.le_sup
      (s := s) (f := fun y => if y ≤ x then table y else ⊥) hx
    aesop

/-- **The bottom-aware orbit law**: at an active table point, either the value is `⊥`, or its
replacement is in the domain with the commuted value. -/
def FiniteShifterWeakOrbit
    (s : Finset ExtOrd) (table : ExtOrd → ExtOrd) (g : ℕ → ExtOrd) : Prop :=
  ∀ x ∈ s, ∀ k i, i ≤ k → table x ≤ g k →
    table x = ⊥ ∨
      (extVisibilityReplace x k i ∈ s ∧
        table (extVisibilityReplace x k i) = extVisibilityReplace (table x) k i)

/-- Every active point visible below a replaced input is controlled from
an old point below the original input.  This is the exact block-gap repair. -/
def FiniteShifterBlockBridge
    (s : Finset ExtOrd) (table : ExtOrd → ExtOrd) (g : ℕ → ExtOrd) : Prop :=
  ∀ x k, finiteLowerEnvelope s table x ≤ g k →
    ∀ i, i ≤ k → ∀ z ∈ s,
      z ≤ extVisibilityReplace x k i →
        table z = ⊥ ∨
          ∃ y ∈ s, y ≤ x ∧
            table z ≤ extVisibilityReplace (table y) k i

theorem finiteLowerEnvelope_visibility_le
    (s : Finset ExtOrd) (table : ExtOrd → ExtOrd) (g : ℕ → ExtOrd)
    (hOrbit : FiniteShifterWeakOrbit s table g)
    (x : ExtOrd) (k i : ℕ) (hi : i ≤ k)
    (hActive : finiteLowerEnvelope s table x ≤ g k) :
    extVisibilityReplace (finiteLowerEnvelope s table x) k i ≤
      finiteLowerEnvelope s table (extVisibilityReplace x k i) := by
  unfold finiteLowerEnvelope
  rw [Finset.apply_sup_eq_sup_comp_of_linearOrder
    (fun z : ExtOrd => extVisibilityReplace z k i)
    (extVisibilityReplace_mono k i hi) rfl]
  apply Finset.sup_le
  intro y hy
  by_cases hyx : y ≤ x
  · have hfy : table y ≤ finiteLowerEnvelope s table x := by
      have hterm := Finset.le_sup
        (s := s) (f := fun z => if z ≤ x then table z else ⊥) hy
      aesop
    simp only [Function.comp_apply, hyx, if_true]
    change extVisibilityReplace (table y) k i ≤
      s.sup (fun z => if z ≤ extVisibilityReplace x k i then table z else ⊥)
    rcases hOrbit y hy k i hi (hfy.trans hActive) with hbot | ⟨hmem, hcomm⟩
    · simp_all
    · have hinput : extVisibilityReplace y k i ≤ extVisibilityReplace x k i :=
        extVisibilityReplace_mono k i hi hyx
      have hterm := Finset.le_sup
        (s := s)
        (f := fun z => if z ≤ extVisibilityReplace x k i then table z else ⊥) hmem
      simp_all
  · simp only [Function.comp_apply, hyx, if_false]
    simp

theorem finiteLowerEnvelope_le_visibility
    (s : Finset ExtOrd) (table : ExtOrd → ExtOrd) (g : ℕ → ExtOrd)
    (hBridge : FiniteShifterBlockBridge s table g)
    (x : ExtOrd) (k i : ℕ) (hi : i ≤ k)
    (hActive : finiteLowerEnvelope s table x ≤ g k) :
    finiteLowerEnvelope s table (extVisibilityReplace x k i) ≤
      extVisibilityReplace (finiteLowerEnvelope s table x) k i := by
  unfold finiteLowerEnvelope
  apply Finset.sup_le
  intro z hz
  by_cases hzNew : z ≤ extVisibilityReplace x k i
  · rcases hBridge x k hActive i hi z hz hzNew with
      hzBot | ⟨y, hy, hyx, hzy⟩
    · simp_all
    · have hterm := Finset.le_sup
        (s := s) (f := fun w => if w ≤ x then table w else ⊥) hy
      have hfy : table y ≤ s.sup (fun w => if w ≤ x then table w else ⊥) := by
        simp_all
      simp only [hzNew, if_true]
      exact hzy.trans (extVisibilityReplace_mono k i hi hfy)
  · simp only [hzNew, if_false]
    simp

/-- **The envelope commutes with replacement at active inputs**, from the weak orbit law and
the bridge. -/
theorem finiteLowerEnvelope_visibility_eq
    (s : Finset ExtOrd) (table : ExtOrd → ExtOrd) (g : ℕ → ExtOrd)
    (hOrbit : FiniteShifterWeakOrbit s table g)
    (hBridge : FiniteShifterBlockBridge s table g)
    (x : ExtOrd) (k i : ℕ) (hi : i ≤ k)
    (hActive : finiteLowerEnvelope s table x ≤ g k) :
    finiteLowerEnvelope s table (extVisibilityReplace x k i) =
      extVisibilityReplace (finiteLowerEnvelope s table x) k i := by grind [finiteLowerEnvelope_le_visibility, finiteLowerEnvelope_visibility_le]

/-- The canonical suppressor vanishes above every grade. -/
theorem finiteTargetSuppressor_eq_bot_of_lt
    {D : Type*} [Finite D] (grade : D → ℕ) (target : D → ExtOrd) {K k : ℕ}
    (hK : ∀ d, grade d ≤ K) (hk : K < k) : finiteTargetSuppressor grade target k = ⊥ := by
  letI := Fintype.ofFinite D
  apply le_bot_iff.mp
  apply Finset.sup_le
  grind

/-- **A finite certificate for a faithful transformation.**  It has no global range-normalization
field: the orbit law is bottom-aware, and the bridge is the only condition on inputs outside the
domain. -/
structure FiniteBlockBridgeCertificate
    {D : Type*} [Finite D]
    (grade : D → ℕ) (source target : D → ExtOrd) where
  tableDomain : Finset ExtOrd
  table : ExtOrd → ExtOrd
  bottom : ∀ y ∈ tableDomain, y = ⊥ → table y = ⊥
  monotone : ∀ a ∈ tableDomain, ∀ b ∈ tableDomain,
    a ≤ b → table a ≤ table b
  orbit : FiniteShifterWeakOrbit tableDomain table
    (finiteTargetSuppressor grade target)
  bridge : FiniteShifterBlockBridge tableDomain table
    (finiteTargetSuppressor grade target)
  source_mem : ∀ d, source d ∈ tableDomain
  realizes : ∀ d, target d = min (table (source d))
    (finiteTargetSuppressor grade target (grade d))

/-- **The cashout**: a certificate for an orderly target is a faithful transformation, witnessed
by the canonical suppressor and the lower envelope of the table. -/
theorem FiniteBlockBridgeCertificate.transformsTo
    {D : Type*} [Finite D]
    {grade : D → ℕ} {source target : D → ExtOrd}
    (C : FiniteBlockBridgeCertificate grade source target)
    (hTarget : IsOrderly grade target) :
    TransformsTo grade source target := by
  refine ⟨finiteTargetSuppressor grade target,
    finiteLowerEnvelope C.tableDomain C.table,
    finiteTargetSuppressor_antitone grade target,
    finiteTargetSuppressor_selfVis grade target hTarget,
    finiteLowerEnvelope_bot C.tableDomain C.table C.bottom,
    finiteLowerEnvelope_mono C.tableDomain C.table, ?_, ?_⟩
  · intro x k hActive i hi
    exact finiteLowerEnvelope_visibility_eq
      C.tableDomain C.table (finiteTargetSuppressor grade target)
      C.orbit C.bridge x k i hi hActive
  · intro d
    rw [finiteLowerEnvelope_source C.tableDomain C.table C.monotone (C.source_mem d)]
    exact C.realizes d

end

end VaughtConjecture.Knight
