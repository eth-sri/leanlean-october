/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CountedRecoding

/-! # The finite block-bridge kernel: faithful locality from a finite shifter table

**What this proves.**  A faithful transformation `TransformsTo grade source target` (Def. 2.3.9,
unguarded clause 5) between finite rows can be certified by **finite data**: a table on a finite
domain of labels, extended to a total shifter by its lower envelope.  This is the repaired finite
lower-envelope machinery of the sibling Knight-VC development (its `PaperFinitePartialShifter
BlockBridge`/`WeakOrbit` files), ported to V-C's `TransformsTo`; the printed lower-envelope proof
of paper Lemma 2.3.10 is refuted there by a block-gap example, and the block bridge below is the
exact repair.

* `finiteTargetSuppressor` — the **canonical suppressor** of a finite target, `g k := ⨆ {target d
  | k ≤ grade d}`; antitone, self-visible for orderly targets, and **lossless**
  (`finiteTargetShifterData_nonempty_of_transformsTo`): any witness can be renormalized to it,
  keeping its shifter.
* `finiteLowerEnvelope` — the total extension of a finite table: monotone, bottom-preserving,
  and exact on a monotone table's domain.
* `FiniteShifterWeakOrbit` — the **bottom-aware orbit law**: at an active table point, either the
  value is `⊥` (contributing nothing to any envelope) or its replacement is in the domain with the
  commuted value.  For the canonical suppressor every obligation above the maximal grade closes
  through the bottom alternative (`FiniteShifterWeakOrbit.of_bounded`), so a producer solves the
  orbit law at the finitely many thresholds `≤ K` only.
* `FiniteShifterBlockBridge` — the **block-gap bridge**: every prescribed source visible below a
  replaced input is bottom-valued or controlled by a source below the original input.  It is
  the missing reverse inequality of the envelope's commutation and stays unrestricted.
* `FiniteBlockBridgeCertificate.transformsTo` — the cashout: table + bottom + monotonicity +
  weak orbit + bridge + realization of the rows gives `TransformsTo`.

No normalization of the ambient witness's range, no global range restriction, and no
transitivity of transformations enter.  Construction-private (not root-exported). -/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight

open Value ExtOrd Transform

/-- Greatest target label at a cell of grade at least `k`. -/
def finiteTargetSuppressor
    {D : Type*} [Finite D]
    (grade : D → ℕ) (target : D → ExtOrd) (k : ℕ) : ExtOrd := by
  letI := Fintype.ofFinite D
  exact Finset.univ.sup fun d => if k ≤ grade d then target d else ⊥

private theorem isNonSuccessor_limitPart (δ : Ordinal) :
    IsNonSuccessor (limitPart δ) := by
  by_cases h0 : limitPart δ = 0
  · exact Or.inl h0
  · exact Or.inr ((Order.isSuccLimit_iff _).2
      ⟨by simpa using h0, (Ordinal.isSuccPrelimit_iff_omega0_dvd).2 ⟨δ / Ordinal.omega0, rfl⟩⟩)

private theorem add_omega0_le_of_nonsucc
    {μ ν : Ordinal} (hν : IsNonSuccessor ν) (hμν : μ < ν) :
    μ + Ordinal.omega0 ≤ ν := by
  rcases hν with rfl | hLimit
  · simp at hμν
  · have hFinite (k : ℕ) : μ + (k : Ordinal) < ν := by
      induction k with
      | zero => simpa using hμν
      | succ k ih =>
          rw [show μ + ((k + 1 : ℕ) : Ordinal) = Order.succ (μ + (k : Ordinal)) by
            push_cast; rw [← add_assoc, ← Order.succ_eq_add_one]]
          exact hLimit.succ_lt ih
    rw [Ordinal.add_le_iff_of_isSuccLimit Ordinal.isSuccLimit_omega0]
    intro b hb
    obtain ⟨k, rfl⟩ := Ordinal.lt_omega0.mp hb
    exact (hFinite k).le

theorem target_le_finiteTargetSuppressor
    {D : Type*} [Finite D]
    (grade : D → ℕ) (target : D → ExtOrd) (d : D) :
    target d ≤ finiteTargetSuppressor grade target (grade d) := by
  classical
  letI := Fintype.ofFinite D
  simpa only [finiteTargetSuppressor, le_refl, if_true] using
    Finset.le_sup (s := (Finset.univ : Finset D))
      (f := fun e => if grade d ≤ grade e then target e else ⊥) (Finset.mem_univ d)

theorem extVisibilityReplace_mono (k i : ℕ) (hi : i ≤ k) :
    Monotone (fun x : ExtOrd => extVisibilityReplace x k i) := by
  have hOrd : Monotone (fun δ : Ordinal => visibilityReplace δ k i) := by
    intro γ δ hγδ
    by_cases hγ : finitePart γ < k
    · by_cases hδ : finitePart δ < k
      · simp only [visibilityReplace, hγ, hδ, if_true, ordinalReplace]
        exact add_le_add (limitPart_mono hγδ) le_rfl
      · exact (visReplace_le_of_le_selfVis hγδ (Nat.not_lt.mp hδ) hi).trans_eq
          (by simp only [visibilityReplace, hδ, if_false])
    · by_cases hδ : finitePart δ < k
      · simp only [visibilityReplace, hγ, hδ, if_false, if_true, ordinalReplace]
        have hLimitLt : limitPart γ < limitPart δ :=
          lt_of_le_of_ne (limitPart_mono hγδ) fun hEq => hγ (lt_of_le_of_lt (by
            have hDecomp : limitPart γ + (finitePart γ : Ordinal) ≤
                limitPart γ + (finitePart δ : Ordinal) := by
              calc
                limitPart γ + (finitePart γ : Ordinal) = γ := decomposition γ
                _ ≤ δ := hγδ
                _ = limitPart δ + (finitePart δ : Ordinal) := (decomposition δ).symm
                _ = limitPart γ + (finitePart δ : Ordinal) := by rw [hEq]
            exact_mod_cast (add_le_add_iff_left (limitPart γ)).mp hDecomp) hδ)
        have hGammaLtBlock : γ < limitPart γ + Ordinal.omega0 := by
          calc
            γ = limitPart γ + (finitePart γ : Ordinal) := (decomposition γ).symm
            _ < limitPart γ + Ordinal.omega0 :=
              (add_lt_add_iff_left (limitPart γ)).2 (Ordinal.natCast_lt_omega0 (finitePart γ))
        exact hGammaLtBlock.le.trans
          ((add_omega0_le_of_nonsucc (isNonSuccessor_limitPart δ) hLimitLt).trans le_self_add)
      · simp only [visibilityReplace, hγ, hδ, if_false]; exact hγδ
  intro x y hxy
  match x, y with
  | ⊥, _ => exact bot_le
  | some ⊤, ⊥ =>
      exact (not_le_of_gt (WithBot.bot_lt_coe (⊤ : WithTop Ordinal)) hxy).elim
  | some ⊤, some ⊤ => exact le_rfl
  | some ⊤, some (some δ) =>
      exact (not_le_of_gt (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top δ)) hxy).elim
  | some (some γ), ⊥ =>
      exact (not_le_of_gt (bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot γ)) hxy).elim
  | some (some γ), some ⊤ => exact le_top
  | some (some γ), some (some δ) =>
      exact WithBot.coe_le_coe.mpr <| WithTop.coe_le_coe.mpr <| hOrd <|
        WithTop.coe_le_coe.mp <| WithBot.coe_le_coe.mp hxy

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
    simpa only [finiteLowerEnvelope, hax, hay, if_true] using
      Finset.le_sup (s := s) (f := fun z => if z ≤ y then table z else ⊥) ha
  · simp only [finiteLowerEnvelope, hax, if_false]; exact bot_le

theorem finiteLowerEnvelope_bot
    (s : Finset ExtOrd) (table : ExtOrd → ExtOrd)
    (hBot : ∀ y ∈ s, y = ⊥ → table y = ⊥) :
    finiteLowerEnvelope s table ⊥ = ⊥ :=
  le_bot_iff.mp <| Finset.sup_le fun y hy => by
    by_cases hyBot : y ≤ (⊥ : ExtOrd)
    · simp only [hyBot, if_true, hBot y hy (le_bot_iff.mp hyBot), le_rfl]
    · simp only [hyBot, if_false, le_rfl]

theorem finiteLowerEnvelope_source
    (s : Finset ExtOrd) (table : ExtOrd → ExtOrd)
    (hMono : ∀ a ∈ s, ∀ b ∈ s, a ≤ b → table a ≤ table b)
    {x : ExtOrd} (hx : x ∈ s) :
    finiteLowerEnvelope s table x = table x := by
  apply le_antisymm
  · refine Finset.sup_le fun y hy => ?_
    by_cases hyx : y ≤ x
    · simpa only [hyx, if_true] using hMono y hy x hx hyx
    · simp only [hyx, if_false]; exact bot_le
  · simpa only [finiteLowerEnvelope, le_refl, if_true] using
      Finset.le_sup (s := s) (f := fun y => if y ≤ x then table y else ⊥) hx

def FiniteShifterWeakOrbit
    (s : Finset ExtOrd) (table : ExtOrd → ExtOrd) (g : ℕ → ExtOrd) : Prop :=
  ∀ x ∈ s, ∀ k i, i ≤ k → table x ≤ g k →
    table x = ⊥ ∨
      (extVisibilityReplace x k i ∈ s ∧
        table (extVisibilityReplace x k i) = extVisibilityReplace (table x) k i)

def FiniteShifterBlockBridge
    (s : Finset ExtOrd) (table : ExtOrd → ExtOrd) (g : ℕ → ExtOrd) : Prop :=
  ∀ x k, finiteLowerEnvelope s table x ≤ g k →
    ∀ i, i ≤ k → ∀ z ∈ s,
      z ≤ extVisibilityReplace x k i →
        table z = ⊥ ∨
          ∃ y ∈ s, y ≤ x ∧
            table z ≤ extVisibilityReplace (table y) k i

theorem finiteLowerEnvelope_visibility_eq
    (s : Finset ExtOrd) (table : ExtOrd → ExtOrd) (g : ℕ → ExtOrd)
    (hOrbit : FiniteShifterWeakOrbit s table g)
    (hBridge : FiniteShifterBlockBridge s table g)
    (x : ExtOrd) (k i : ℕ) (hi : i ≤ k)
    (hActive : finiteLowerEnvelope s table x ≤ g k) :
    finiteLowerEnvelope s table (extVisibilityReplace x k i) =
      extVisibilityReplace (finiteLowerEnvelope s table x) k i := by
  apply le_antisymm
  · unfold finiteLowerEnvelope
    refine Finset.sup_le fun z hz => ?_
    by_cases hzNew : z ≤ extVisibilityReplace x k i
    · rcases hBridge x k hActive i hi z hz hzNew with hzBot | ⟨y, hy, hyx, hzy⟩
      · simp only [hzNew, if_true, hzBot, bot_le]
      · have hfy : table y ≤ s.sup (fun w => if w ≤ x then table w else ⊥) := by
          simpa only [hyx, if_true] using
            Finset.le_sup (s := s) (f := fun w => if w ≤ x then table w else ⊥) hy
        simp only [hzNew, if_true]
        exact hzy.trans (extVisibilityReplace_mono k i hi hfy)
    · simp only [hzNew, if_false, bot_le]
  · unfold finiteLowerEnvelope
    rw [Finset.apply_sup_eq_sup_comp_of_linearOrder
      (fun z : ExtOrd => extVisibilityReplace z k i)
      (extVisibilityReplace_mono k i hi) rfl]
    refine Finset.sup_le fun y hy => ?_
    by_cases hyx : y ≤ x
    · have hfy : table y ≤ finiteLowerEnvelope s table x := by
        simpa only [finiteLowerEnvelope, hyx, if_true] using
          Finset.le_sup (s := s) (f := fun z => if z ≤ x then table z else ⊥) hy
      simp only [Function.comp_apply, hyx, if_true]
      rcases hOrbit y hy k i hi (hfy.trans hActive) with hbot | ⟨hmem, hcomm⟩
      · rw [hbot, extVisibilityReplace_bot]; exact bot_le
      · have hinput : extVisibilityReplace y k i ≤ extVisibilityReplace x k i :=
          extVisibilityReplace_mono k i hi hyx
        rw [← hcomm]
        simpa only [hinput, if_true] using
          Finset.le_sup (s := s)
            (f := fun z => if z ≤ extVisibilityReplace x k i then table z else ⊥) hmem
    · simp only [Function.comp_apply, hyx, if_false]; exact bot_le

theorem finiteTargetSuppressor_eq_bot_of_lt
    {D : Type*} [Finite D] (grade : D → ℕ) (target : D → ExtOrd) {K k : ℕ}
    (hK : ∀ d, grade d ≤ K) (hk : K < k) : finiteTargetSuppressor grade target k = ⊥ := by
  letI := Fintype.ofFinite D
  exact le_bot_iff.mp <| Finset.sup_le fun d _ => by rw [if_neg (by have := hK d; omega)]

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

theorem FiniteBlockBridgeCertificate.transformsTo
    {D : Type*} [Finite D]
    {grade : D → ℕ} {source target : D → ExtOrd}
    (C : FiniteBlockBridgeCertificate grade source target)
    (hTarget : IsOrderly grade target) :
    TransformsTo grade source target := by
  classical
  letI := Fintype.ofFinite D
  refine ⟨finiteTargetSuppressor grade target,
    finiteLowerEnvelope C.tableDomain C.table,
    fun n m hnm => Finset.sup_le fun d hd => by
      by_cases hm : m ≤ grade d
      · have hn : n ≤ grade d := (Nat.le_of_lt hnm).trans hm
        simpa only [finiteTargetSuppressor, hm, hn, if_true] using
          Finset.le_sup (s := (Finset.univ : Finset D))
            (f := fun e => if n ≤ grade e then target e else ⊥) hd
      · simp only [finiteTargetSuppressor, hm, if_false, bot_le],
    fun k => Finset.sup_induction (p := fun x => x = extVisibilityReplace x k k) rfl
      (fun a ha b hb => by
        rcases le_total a b with hab | hba
        · rwa [max_eq_right hab]
        · rwa [max_eq_left hba])
      (fun d _ => by
        by_cases hk : k ≤ grade d
        · simp only [hk, if_true]
          exact (selfVis_mono (hTarget d).symm hk).symm
        · simp only [hk, if_false, extVisibilityReplace]),
    finiteLowerEnvelope_bot C.tableDomain C.table C.bottom,
    finiteLowerEnvelope_mono C.tableDomain C.table,
    fun x k hActive i hi => finiteLowerEnvelope_visibility_eq
      C.tableDomain C.table (finiteTargetSuppressor grade target)
      C.orbit C.bridge x k i hi hActive,
    fun d => by
      rw [finiteLowerEnvelope_source C.tableDomain C.table C.monotone (C.source_mem d)]
      exact C.realizes d⟩
