/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RelativeLiftData

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd SharpWitnessComposition

theorem limitPart_add_nat_of_limit {l : Ordinal.{0}} (hl : limitPart l = l) (n : ℕ) :
    limitPart (l + n) = l := by
  conv_lhs => rw [← hl]
  rw [limitPart_limitPart_add_nat, hl]

theorem finitePart_add_nat_of_limit {l : Ordinal.{0}} (hl : limitPart l = l) (n : ℕ) :
    finitePart (l + n) = n := by
  conv_lhs => rw [← hl]
  rw [finitePart_limitPart_add_nat]

/-- Below a larger limit, a limit plus any natural stays below. -/
theorem add_nat_lt_of_lt_limit {l l' : Ordinal.{0}} (hl : limitPart l = l)
    (hl' : limitPart l' = l') (h : l < l') (n : ℕ) : l + n < l' := by
  have h1 : limitPart l < limitPart l' := by simp_all
  have h2 := limitPart_add_nat_le_of_lt h1 (n + 1)
  rw [hl, hl'] at h2
  refine lt_of_lt_of_le ?_ h2
  simp

/-- **A block code**: target strips for blocks, the listed blocks, and the top code's block. -/
structure BlockCode where
  /-- The listed-offset bound. -/
  N : ℕ
  /-- The grade through which the code commutes; the top code's finite part. -/
  R : ℕ
  R_lt_N : R < N
  /-- The target strip of a block, if any. -/
  Λ : Ordinal.{0} → Option Ordinal.{0}
  /-- The listed blocks. -/
  listed : Ordinal.{0} → Prop
  [dec : DecidablePred listed]
  /-- The top code. -/
  htop : Ordinal.{0}
  R_le_htop : R ≤ finitePart htop
  Λ_limit : ∀ μ l, Λ μ = some l → limitPart l = l
  Λ_le : ∀ μ l, Λ μ = some l → l + N ≤ htop
  low_down : ∀ μ μ', μ ≤ μ' → Λ μ' = none → Λ μ = none
  Λ_mono : ∀ μ μ' l l', μ ≤ μ' → Λ μ = some l → Λ μ' = some l' → l ≤ l'
  Λ_strict : ∀ μ μ' l l', μ < μ' → listed μ' → Λ μ = some l → Λ μ' = some l' → l < l'

namespace BlockCode

variable (B : BlockCode)

attribute [instance] BlockCode.dec

/-- The offset kept on a value: its finite part up to `N` on a listed block, `N` otherwise. -/
noncomputable def off (a : Ordinal.{0}) : ℕ :=
  if B.listed (limitPart a) then min (finitePart a) B.N else B.N

theorem off_le_N (a : Ordinal.{0}) : B.off a ≤ B.N := by
  unfold off; aesop

theorem off_of_listed {a : Ordinal.{0}} (h : B.listed (limitPart a)) :
    B.off a = min (finitePart a) B.N := by
  unfold off; simp_all

theorem off_of_not_listed {a : Ordinal.{0}} (h : ¬ B.listed (limitPart a)) : B.off a = B.N := by
  unfold off; simp_all

/-- The top code. -/
noncomputable def topCode : ExtOrd := ofOrd B.htop

/-- **The code.** -/
noncomputable def code (x : ExtOrd) : ExtOrd :=
  match x with
  | none => ⊥
  | some none => B.topCode
  | some (some a) =>
    match B.Λ (limitPart a) with
    | none => ⊥
    | some l => ofOrd (l + B.off a)

@[simp] theorem code_bot : B.code ⊥ = ⊥ := rfl

@[simp] theorem code_top : B.code ⊤ = B.topCode := rfl

theorem code_ofOrd_of_none {a : Ordinal.{0}} (h : B.Λ (limitPart a) = none) :
    B.code (ofOrd a) = ⊥ := by
  change (match B.Λ (limitPart a) with | none => ⊥ | some l => ofOrd (l + B.off a)) = ⊥
  simp_all

theorem code_ofOrd_of_some {a l : Ordinal.{0}} (h : B.Λ (limitPart a) = some l) :
    B.code (ofOrd a) = ofOrd (l + B.off a) := by
  change (match B.Λ (limitPart a) with | none => ⊥ | some l => ofOrd (l + B.off a)) = _
  simp_all

/-- On a listed block with a target, a value with finite part at most `N` is sent to the
same offset on the target strip. -/
theorem code_listed {a l : Ordinal.{0}} (hl : B.listed (limitPart a))
    (h : B.Λ (limitPart a) = some l) (hfp : finitePart a ≤ B.N) :
    B.code (ofOrd a) = ofOrd (l + finitePart a) := by
  rw [B.code_ofOrd_of_some h, B.off_of_listed hl, min_eq_left hfp]

/-- Every strip value with offset at most `N` lies below the top code. -/
theorem strip_le_topCode {μ l : Ordinal.{0}} (h : B.Λ μ = some l) {n : ℕ} (hn : n ≤ B.N) :
    l + n ≤ B.htop :=
  (add_le_add_right (Nat.cast_le.mpr hn) _).trans (B.Λ_le μ l h)

theorem code_mono : Monotone B.code := by
  intro x y hxy
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · simp
  · simp_all
  rcases ExtOrd.cases y with rfl | rfl | ⟨b, rfl⟩
  · trivial
  · rw [code_top]
    rcases h : B.Λ (limitPart a) with _ | l
    · rw [B.code_ofOrd_of_none h]; simp
    · rw [B.code_ofOrd_of_some h, topCode, ofOrd_le_ofOrd]
      exact B.strip_le_topCode h (B.off_le_N a)
  rw [ofOrd_le_ofOrd] at hxy
  have hlp : limitPart a ≤ limitPart b := limitPart_mono hxy
  rcases ha : B.Λ (limitPart a) with _ | l
  · rw [B.code_ofOrd_of_none ha]; simp
  rcases hb : B.Λ (limitPart b) with _ | l'
  · exact absurd (B.low_down _ _ hlp hb) (by simp_all)
  rw [B.code_ofOrd_of_some ha, B.code_ofOrd_of_some hb, ofOrd_le_ofOrd]
  have hll' : l ≤ l' := B.Λ_mono _ _ l l' hlp ha hb
  rcases hll'.lt_or_eq with hlt | heq
  · exact ((add_nat_lt_of_lt_limit (B.Λ_limit _ l ha) (B.Λ_limit _ l' hb) hlt _).trans_le
      le_self_add).le
  · subst heq
    apply add_le_add_right
    apply Nat.cast_le.mpr
    rcases hlp.lt_or_eq with hlt | heq
    · have hnl : ¬ B.listed (limitPart b) := fun hl =>
        lt_irrefl l (B.Λ_strict _ _ l l hlt hl ha hb)
      rw [B.off_of_not_listed hnl]
      exact B.off_le_N a
    · have hfp : finitePart a ≤ finitePart b := finitePart_le_of_le_of_limitPart_eq hxy heq
      unfold off
      aesop

theorem code_comm (x : ExtOrd) (k i : ℕ) (hk : k ≤ B.R) (hi : i ≤ k) :
    B.code (extVisibilityReplace x k i) = extVisibilityReplace (B.code x) k i := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · rfl
  · rw [extVisibilityReplace_top, code_top, topCode,
      extVisibilityReplace_of_le_finitePart (hk.trans B.R_le_htop)]
  by_cases hfp : k ≤ finitePart a
  · rw [extVisibilityReplace_of_le_finitePart hfp]
    rcases h : B.Λ (limitPart a) with _ | l
    · rw [B.code_ofOrd_of_none h, extVisibilityReplace_bot]
    · rw [B.code_ofOrd_of_some h]
      refine (extVisibilityReplace_of_le_finitePart ?_ _).symm
      rw [finitePart_add_nat_of_limit (B.Λ_limit _ l h)]
      unfold off
      split_ifs
      · exact le_min hfp (hk.trans B.R_lt_N.le)
      · exact hk.trans B.R_lt_N.le
  · have hfp' := not_le.mp hfp
    rw [extVisibilityReplace_of_finitePart_lt hfp']
    rcases h : B.Λ (limitPart a) with _ | l
    · have h' : B.Λ (limitPart (limitPart a + i)) = none := by
        rw [limitPart_limitPart_add_nat]; assumption
      rw [B.code_ofOrd_of_none h, B.code_ofOrd_of_none h', extVisibilityReplace_bot]
    · have h' : B.Λ (limitPart (limitPart a + i)) = some l := by
        rw [limitPart_limitPart_add_nat]; assumption
      rw [B.code_ofOrd_of_some h, B.code_ofOrd_of_some h']
      have hlim := B.Λ_limit _ l h
      by_cases hl : B.listed (limitPart a)
      · have hl' : B.listed (limitPart (limitPart a + i)) := by
          rw [limitPart_limitPart_add_nat]; assumption
        rw [B.off_of_listed hl, B.off_of_listed hl', finitePart_limitPart_add_nat,
          min_eq_left (hfp'.le.trans (hk.trans B.R_lt_N.le)),
          min_eq_left ((hi.trans hk).trans B.R_lt_N.le),
          extVisibilityReplace_of_finitePart_lt
            (by rw [finitePart_add_nat_of_limit hlim]; assumption),
          limitPart_add_nat_of_limit hlim]
      · have hl' : ¬ B.listed (limitPart (limitPart a + i)) := by
          rw [limitPart_limitPart_add_nat]; assumption
        rw [B.off_of_not_listed hl, B.off_of_not_listed hl',
          extVisibilityReplace_of_le_finitePart
            (by rw [finitePart_add_nat_of_limit hlim]; exact hk.trans B.R_lt_N.le)]

/-- **The code is a bounded replacement-commuting map through grade `R`.** -/
theorem boundedMap_code : BoundedMap B.R B.code where
  bot := B.code_bot
  mono := B.code_mono
  comm := B.code_comm

section OfFinset

variable (N R : ℕ) (hR : R < N) (S : Finset Ordinal.{0}) (strip : Ordinal.{0} → Ordinal.{0})
  (htop : Ordinal.{0})

open Classical in
/-- The target of a block: the strip of the largest listed block at or below it. -/
noncomputable def targetOf (μ : Ordinal.{0}) : Option Ordinal.{0} :=
  if h : (S.filter fun μ' => μ' ≤ μ).Nonempty then some (strip ((S.filter fun μ' => μ' ≤ μ).max' h))
  else none

open Classical in
theorem targetOf_eq_none_iff (μ : Ordinal.{0}) :
    targetOf S strip μ = none ↔ ¬ (S.filter fun μ' => μ' ≤ μ).Nonempty := by
  unfold targetOf
  simp

open Classical in
theorem targetOf_eq_some {μ : Ordinal.{0}} (h : (S.filter fun μ' => μ' ≤ μ).Nonempty) :
    targetOf S strip μ = some (strip ((S.filter fun μ' => μ' ≤ μ).max' h)) := by
  unfold targetOf
  simp_all

open Classical in
/-- The largest listed block at or below `μ` is listed, at most `μ`, and above every listed
block at most `μ`. -/
theorem max'_filter_spec {μ : Ordinal.{0}} (h : (S.filter fun μ' => μ' ≤ μ).Nonempty) :
    (S.filter fun μ' => μ' ≤ μ).max' h ∈ S ∧ (S.filter fun μ' => μ' ≤ μ).max' h ≤ μ ∧
      ∀ μ' ∈ S, μ' ≤ μ → μ' ≤ (S.filter fun μ' => μ' ≤ μ).max' h := by
  have hm := Finset.max'_mem _ h
  rw [Finset.mem_filter] at hm
  refine ⟨hm.1, hm.2, fun μ' hμ' hle => ?_⟩
  have hmem : μ' ∈ S.filter fun ν => ν ≤ μ := Finset.mem_filter.mpr ⟨hμ', hle⟩
  exact Finset.le_max' _ _ hmem

open Classical in
/-- **A block code from a finite set of listed blocks** with a strip function strictly
increasing on them, limit-valued, and with `strip μ + N ≤ htop`. -/
noncomputable def ofFinset (hlim : ∀ μ ∈ S, limitPart (strip μ) = strip μ)
    (hle : ∀ μ ∈ S, strip μ + N ≤ htop) (hstrict : ∀ μ ∈ S, ∀ μ' ∈ S, μ < μ' → strip μ < strip μ')
    (hRtop : R ≤ finitePart htop) : BlockCode where
  N := N
  R := R
  R_lt_N := hR
  Λ := targetOf S strip
  listed := fun μ => μ ∈ S
  dec := fun _ => Classical.propDecidable _
  htop := htop
  R_le_htop := hRtop
  Λ_limit := by
    intro μ l hl
    by_cases h : (S.filter fun μ' => μ' ≤ μ).Nonempty
    · rw [targetOf_eq_some S strip h, Option.some.injEq] at hl
      rw [← hl]
      exact hlim _ (max'_filter_spec S h).1
    · rw [(targetOf_eq_none_iff S strip μ).mpr h] at hl
      trivial
  Λ_le := by
    intro μ l hl
    by_cases h : (S.filter fun μ' => μ' ≤ μ).Nonempty
    · rw [targetOf_eq_some S strip h, Option.some.injEq] at hl
      rw [← hl]
      exact hle _ (max'_filter_spec S h).1
    · rw [(targetOf_eq_none_iff S strip μ).mpr h] at hl
      trivial
  low_down := by
    intro μ μ' hμμ' hnone
    rw [targetOf_eq_none_iff] at hnone ⊢
    intro ⟨ν, hν⟩
    rw [Finset.mem_filter] at hν
    exact hnone ⟨ν, by grind⟩
  Λ_mono := by
    intro μ μ' l l' hμμ' hl hl'
    by_cases h : (S.filter fun ν => ν ≤ μ).Nonempty
    swap
    · rw [(targetOf_eq_none_iff S strip μ).mpr h] at hl
      trivial
    by_cases h' : (S.filter fun ν => ν ≤ μ').Nonempty
    swap
    · rw [(targetOf_eq_none_iff S strip μ').mpr h'] at hl'
      trivial
    rw [targetOf_eq_some S strip h, Option.some.injEq] at hl
    rw [targetOf_eq_some S strip h', Option.some.injEq] at hl'
    rw [← hl, ← hl']
    obtain ⟨hm1, hm2, -⟩ := max'_filter_spec S h
    obtain ⟨hm1', -, hm3'⟩ := max'_filter_spec S h'
    grind
  Λ_strict := by
    intro μ μ' l l' hμμ' hμ'S hl hl'
    by_cases h : (S.filter fun ν => ν ≤ μ).Nonempty
    swap
    · rw [(targetOf_eq_none_iff S strip μ).mpr h] at hl
      trivial
    have h' : (S.filter fun ν => ν ≤ μ').Nonempty := ⟨μ', Finset.mem_filter.mpr ⟨hμ'S, le_rfl⟩⟩
    rw [targetOf_eq_some S strip h, Option.some.injEq] at hl
    rw [targetOf_eq_some S strip h', Option.some.injEq] at hl'
    rw [← hl, ← hl']
    obtain ⟨hm1, hm2, -⟩ := max'_filter_spec S h
    obtain ⟨hm1', -, hm3'⟩ := max'_filter_spec S h'
    grind

/-- A listed block's target is its own strip. -/
theorem ofFinset_Λ_listed (hlim : ∀ μ ∈ S, limitPart (strip μ) = strip μ)
    (hle : ∀ μ ∈ S, strip μ + N ≤ htop)
    (hstrict : ∀ μ ∈ S, ∀ μ' ∈ S, μ < μ' → strip μ < strip μ')
    (hRtop : R ≤ finitePart htop) {μ : Ordinal.{0}} (hμ : μ ∈ S) :
    (ofFinset N R hR S strip htop hlim hle hstrict hRtop).Λ μ = some (strip μ) := by
  classical
  have h : (S.filter fun ν => ν ≤ μ).Nonempty := ⟨μ, Finset.mem_filter.mpr ⟨hμ, le_rfl⟩⟩
  change targetOf S strip μ = some (strip μ)
  rw [targetOf_eq_some S strip h]
  congr 2
  exact le_antisymm (max'_filter_spec S h).2.1 ((max'_filter_spec S h).2.2 _ hμ le_rfl)

end OfFinset

end BlockCode

end VaughtConjecture.Knight
