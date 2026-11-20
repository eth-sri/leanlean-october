/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Order.Interval.Finset.Fin
public import VaughtConjecture.Knight.SemScheme

/-! # Step shifters, clipping and finite alphabets of ordinal codes -/

@[expose] public section

namespace VaughtConjecture.Knight

open Value ExtOrd

/-! ### Label arithmetic: ω-blocks and codes -/

namespace Value

/-- Self-visibility at `k` fixes every replacement value, not just `k`:
if `γ = γ ⊔⁺_k k` then `γ = γ ⊔⁺_k i` for every `i`. -/
theorem extVisReplace_eq_self_of_selfVis {v} {k}
    (h : extVisibilityReplace v k k = v) i : extVisibilityReplace v k i = v := by
  rcases (extVisibilityReplace_self_iff v k).mp h with rfl | rfl | ⟨α, rfl, hfp⟩
  · rfl
  · rfl
  · rw [extVisibilityReplace_ofOrd, visibilityReplace, ite_eq_right (not_lt.mpr hfp)]

/-- The limit part of a natural number is zero. -/
theorem limitPart_natCast (n : ℕ) : limitPart (n : Ordinal.{0}) = 0 := by
  unfold limitPart
  rw [Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 n), mul_zero]

/-- `ω * u` is its own limit part. -/
theorem limitPart_omega0_mul u :
    limitPart (Ordinal.omega0 * u) = Ordinal.omega0 * u := by
  unfold limitPart
  rw [Ordinal.mul_div_cancel u Ordinal.omega0_ne_zero]

/-- The limit part of the code `ω * u + m` is `ω * u`. -/
theorem limitPart_code u (m : ℕ) :
    limitPart (Ordinal.omega0 * u + m) = Ordinal.omega0 * u := by
  conv_lhs => rw [← limitPart_omega0_mul u]
  rw [limitPart_limitPart_add_nat, limitPart_omega0_mul]

/-- The finite part of the code `ω * u + m` is `m`. -/
theorem finitePart_code u (m : ℕ) :
    finitePart (Ordinal.omega0 * u + m) = m := by
  conv_lhs => rw [← limitPart_omega0_mul u]
  rw [finitePart_limitPart_add_nat]

/-- An ordinal with finite part `0` is its own limit part. -/
theorem eq_limitPart_of_finitePart_eq_zero {β} (h : finitePart β = 0) :
    limitPart β = β := by
  have := decomposition β
  rwa [h, Nat.cast_zero, add_zero] at this

/-- A block member `x` lies below the next block level: `x < limitPart x + ω`. -/
theorem lt_limitPart_add_omega0 x : x < limitPart x + Ordinal.omega0 := by
  conv_lhs => rw [← decomposition x]
  exact add_lt_add_right (Ordinal.natCast_lt_omega0 _) _

/-- Distinct limit parts are at least a block apart:
if `limitPart x < limitPart y` then `limitPart x + ω ≤ limitPart y`. -/
theorem limitPart_add_omega0_le {x y} (h : limitPart x < limitPart y) :
    limitPart x + Ordinal.omega0 ≤ limitPart y := by
  unfold limitPart at *
  have hdiv : x / Ordinal.omega0 < y / Ordinal.omega0 :=
    (Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono.lt_iff_lt.mp h
  calc Ordinal.omega0 * (x / Ordinal.omega0) + Ordinal.omega0
      = Ordinal.omega0 * Order.succ (x / Ordinal.omega0) := (Ordinal.mul_succ _ _).symm
    _ ≤ Ordinal.omega0 * (y / Ordinal.omega0) :=
        (Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono.monotone
          (Order.succ_le_of_lt hdiv)

/-- Strict block comparison: a member of an earlier block is below every member of a later
block. -/
theorem lt_of_limitPart_lt {x y} (h : limitPart x < limitPart y) : x < y :=
  lt_of_lt_of_le ((lt_limitPart_add_omega0 x).trans_le (limitPart_add_omega0_le h))
    ((limitPart_le y).trans le_rfl)

/-- `min` preserves self-visibility (a `min` of two self-visible labels is one of them). -/
theorem extVisReplace_min_self {x y} {k}
    (hx : extVisibilityReplace x k k = x) (hy : extVisibilityReplace y k k = y) :
    extVisibilityReplace (min x y) k k = min x y := by
  rcases min_cases x y with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm] <;> assumption

end Value

namespace Transform

/-! ### The step suppressor and step shifters -/

/-- The **step suppressor** `g_K` (note §3): `⊤` at thresholds `≤ K`, `⊥` above. -/
def stepSuppressor (K : ℕ) : ℕ → ExtOrd := fun k => if k ≤ K then ⊤ else ⊥

@[simp] theorem stepSuppressor_of_le {K k} (h : k ≤ K) : stepSuppressor K k = ⊤ :=
  ite_eq_left h

@[simp] theorem stepSuppressor_of_gt {K k} (h : K < k) : stepSuppressor K k = ⊥ :=
  ite_eq_right (not_le.mpr h)

theorem stepSuppressor_antitone K :
    ∀ n m : ℕ, n < m → stepSuppressor K m ≤ stepSuppressor K n := by
  intro n m hnm
  unfold stepSuppressor
  split_ifs with hm hn hn
  · exact le_rfl
  · exact absurd ((hnm.le).trans hm) hn
  · exact bot_le
  · exact le_rfl

/-- A **`K`-step shifter** (the legality pattern of the note's §3, shared by the canonical
normalizer and decoder): a label map `σ` that fixes `⊥`, is monotone, preserves
self-visibility at every threshold `≤ K`, is **affine or constant on the sub-`K` part of
every ω-block** (affine onto a block start `β`, or constant at a label self-visible at `K`),
and whose **`⊥`-fiber is closed under whole blocks**.  These five conditions make `(g_K, σ)`
a legal Def. 2.3.9 witness pair (`IsStepShifter.clause5`, `IsStepShifter.transformsTo`). -/
structure IsStepShifter (K : ℕ) (σ : ExtOrd → ExtOrd) : Prop where
  /-- `σ` fixes the bottom label (clause 3). -/
  map_bot : σ ⊥ = ⊥
  /-- `σ` is monotone (clause 4). -/
  mono : Monotone σ
  /-- `σ` preserves self-visibility at every threshold `≤ K`. -/
  selfVis : ∀ x k, k ≤ K → extVisibilityReplace x k k = x →
    extVisibilityReplace (σ x) k k = σ x
  /-- On the sub-`K` part `{limitPart ξ + i : i ≤ K}` of every block, `σ` is affine onto a
  block start (`finitePart β = 0`) or constant at a label self-visible at `K`. -/
  blockwise : ∀ ξ : Ordinal.{0},
    (∃ β, finitePart β = 0 ∧
      ∀ i : ℕ, i ≤ K → σ (ofOrd (limitPart ξ + i)) = ofOrd (β + i)) ∨
    (∃ c, extVisibilityReplace c K K = c ∧
      ∀ i : ℕ, i ≤ K → σ (ofOrd (limitPart ξ + i)) = c)
  /-- The `⊥`-fiber of `σ` on ordinals is a union of whole blocks. -/
  bot_blocks : ∀ ξ ζ : Ordinal.{0}, limitPart ξ = limitPart ζ →
    σ (ofOrd ξ) = ⊥ → σ (ofOrd ζ) = ⊥

/-- **The clause-5 case split, compiled once** (note §3): a `K`-step shifter satisfies
clause 5 of Def. 2.3.9 for the step suppressor `g_K`.  For `k ≤ K` the commutation is
**unguarded**: on self-visible labels both sides are fixed (self-visibility is preserved);
on the sub-`K` part of a block, affine pieces commute with `⊔⁺_k i` and constants are
`⊔⁺_k`-fixed.  For `k > K` the guard `σ α ≤ g_K k = ⊥` pins `σ α = ⊥`, and the
`⊔⁺_k`-orbit of `α` stays in `α`'s block, hence in the `⊥`-fiber (block closure). -/
theorem IsStepShifter.clause5 {K} {σ} (h : IsStepShifter K σ) :
    ∀ α k, σ α ≤ stepSuppressor K k → ∀ i : ℕ, i ≤ k →
      σ (extVisibilityReplace α k i) = extVisibilityReplace (σ α) k i := by
  intro α k hguard i hi
  by_cases hk : k ≤ K
  · -- thresholds `k ≤ K`: unguarded commutation
    rcases ExtOrd.cases α with rfl | rfl | ⟨ξ, rfl⟩
    · rw [extVisibilityReplace_bot, h.map_bot, extVisibilityReplace_bot]
    · rw [extVisibilityReplace_top,
        extVisReplace_eq_self_of_selfVis (h.selfVis ⊤ k hk (extVisibilityReplace_top k k)) i]
    · by_cases hfp : k ≤ finitePart ξ
      · -- self-visible at `k`: both sides fixed
        have hself : extVisibilityReplace (ofOrd ξ) k k = ofOrd ξ :=
          (extVisibilityReplace_self_iff _ k).mpr (Or.inr (Or.inr ⟨ξ, rfl, hfp⟩))
        rw [extVisReplace_eq_self_of_selfVis hself i,
          extVisReplace_eq_self_of_selfVis (h.selfVis _ k hk hself) i]
      · -- inside the sub-`K` part of the block: affine or constant
        rw [not_le] at hfp
        have hrepl : extVisibilityReplace (ofOrd ξ) k i = ofOrd (limitPart ξ + i) := by
          rw [extVisibilityReplace_ofOrd, visibilityReplace, ite_eq_left hfp]; rfl
        have hξ : ofOrd ξ = ofOrd (limitPart ξ + (finitePart ξ : ℕ)) := by
          rw [decomposition]
        rcases h.blockwise ξ with ⟨β, hβ0, haff⟩ | ⟨c, hcvis, hconst⟩
        · have hβ : limitPart β = β := eq_limitPart_of_finitePart_eq_zero hβ0
          rw [hrepl, haff i (hi.trans hk), hξ, haff (finitePart ξ) ((hfp.le).trans hk),
            extVisibilityReplace_ofOrd, visibilityReplace,
            ite_eq_left (by rw [← hβ, finitePart_limitPart_add_nat]; exact hfp),
            ordinalReplace, ← hβ, limitPart_limitPart_add_nat, hβ]
        · rw [hrepl, hconst i (hi.trans hk), hξ, hconst (finitePart ξ) ((hfp.le).trans hk),
            extVisReplace_eq_self_of_selfVis
              (extVisReplace_self_of_le hcvis hk) i]
  · -- thresholds `k > K`: the guard pins `σ α = ⊥`; block closure of the `⊥`-fiber
    rw [stepSuppressor_of_gt (not_le.mp hk)] at hguard
    have hbot : σ α = ⊥ := le_bot_iff.mp hguard
    rw [hbot, extVisibilityReplace_bot]
    rcases ExtOrd.cases α with rfl | rfl | ⟨ξ, rfl⟩
    · rw [extVisibilityReplace_bot, h.map_bot]
    · rw [extVisibilityReplace_top, hbot]
    · rw [extVisibilityReplace_ofOrd]
      unfold visibilityReplace
      split_ifs with hfp
      · exact h.bot_blocks ξ _ (limitPart_limitPart_add_nat ξ i).symm hbot
      · exact hbot

/-- Every `K`-step shifter is a legal transform witness with the step suppressor, on any
family of grades `≤ K`: `p ⇒ σ ∘ p` for **every** labelling `p` (note §3; no hypotheses on
`p`). -/
theorem IsStepShifter.transformsTo {D : Type*} {grade} {K} {σ}
    (h : IsStepShifter K σ) (hK : ∀ d, grade d ≤ K) (p : D → ExtOrd) :
    TransformsTo grade p (fun d => σ (p d)) :=
  ⟨stepSuppressor K, σ, stepSuppressor_antitone K, by
          intro n
          unfold stepSuppressor
          split_ifs <;> rfl, h.map_bot,
    h.mono, h.clause5,
    fun d => by rw [stepSuppressor_of_le (hK d), min_top_right]⟩

/-! ### The Cap Lemma -/

/-- **Cap Lemma** (note §2, Lemma 2.A; the faithful Lemmas 2.3.12/2.4.1 for targets): if
`p ⇒ q` with witness `(g, σ)` and `γ` is self-visible at a bound `K` of every grade of the
family, then `p ⇒ q ∧ γ`, with the direct witness `(g', σ)` where `g' k = min (g k) γ` for
`k ≤ K` and `g' k = ⊥` above.  No transitivity: `g'` is antitone; self-visible at `k` because
`min (g k) γ` is `g k` or `γ`, each self-visible at `k ≤ K` (heredity,
`extVisReplace_self_of_le`); clause 5 for the new guard reduces to the old clause 5 since
`g' k ≤ g k` everywhere.  (The note prints the untruncated witness `min (g, γ)`, whose
self-visibility can fail at thresholds `> K`; the truncation to `⊥` there is the faithful
repair and changes no row value, since every grade is `≤ K`.) -/
theorem TransformsTo.cap {D : Type*} {grade} {p q : D → ExtOrd} {K} {γ}
    (h : TransformsTo grade p q) (hK : ∀ d, grade d ≤ K)
    (hγ : extVisibilityReplace γ K K = γ) :
    TransformsTo grade p (fun d => min (q d) γ) := by
  obtain ⟨g, σ, hg_dec, hg_vis, hσ_bot, hσ_mono, hσ_vis, hσ_eq⟩ := h
  refine ⟨fun k => if k ≤ K then min (g k) γ else ⊥, σ, ?_, ?_, hσ_bot, hσ_mono, ?_, ?_⟩
  · -- antitone
    intro n m hnm
    dsimp only
    split_ifs with hm hn hn
    · exact min_le_min (hg_dec n m hnm) le_rfl
    · exact absurd ((hnm.le).trans hm) hn
    · exact bot_le
    · exact le_rfl
  · -- self-visible
    intro n
    dsimp only
    split_ifs with hn
    · rcases min_cases (g n) γ with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm]
      · exact hg_vis n
      · exact (extVisReplace_self_of_le hγ hn).symm
    · rfl
  · -- clause 5: the truncated guard implies the original guard
    intro α k hle i hi
    dsimp only at hle
    split_ifs at hle with hk
    · exact hσ_vis α k (hle.trans (min_le_left _ _)) i hi
    · exact hσ_vis α k ((le_bot_iff.mp hle).le.trans bot_le) i hi
  · -- the row equation: `min (σ (p d)) (min (g (grade d)) γ) = min (q d) γ`
    intro d
    dsimp only
    rw [ite_eq_left (hK d), ← min_assoc, ← hσ_eq d]

end Transform

open Transform

/-- **Corollary 2.B** (note §2; the faithful Lemma 2.5.8): if `r` respects the restricted
semantics `E⟨B,j⟩` and `γ` is self-visible at `j`, then the capped labelling `r ∧ γ`
respects it too.  Locality is the Cap Lemma applied to `r`'s locality (all grades below the
pair are `≤ j` by `GradedLe`); availability is monotonicity of `min (·, γ)`; orderliness is
preservation of self-visibility under `min` with heredity of `γ`'s self-visibility. -/
theorem RespectsSemanticsBelow.cap {ι : Type*} [DecidableEq ι] {A}
    {D : CellScheme A} {sem} {BJ : Finset ι × ℕ} {r : D.SectionAt BJ}
    (h : sem.Lawful r) {γ}
    (hγ : extVisibilityReplace γ BJ.2 BJ.2 = γ) :
    RespectsSemanticsBelow sem BJ (fun d => min (r d) γ) where
  orderly d :=
    (extVisReplace_min_self (h.orderly d).symm
      (extVisReplace_self_of_le hγ d.2.2)).symm
  locality Sig := by
    have key : TransformsTo (fun d : D.RowDomain Sig.1 => D.grade d.1) (sem.E Sig.1)
        (fun d => min (min (r (CellScheme.below.incl Sig d)) (r Sig)) γ) :=
      (h.locality Sig).cap (fun d => (d.2.trans Sig.2).2) hγ
    have heq : (fun d : D.RowDomain Sig.1 =>
        min (min (r (CellScheme.below.incl Sig d)) (r Sig)) γ) =
        fun d => min (min (r (CellScheme.below.incl Sig d)) γ) (min (r Sig) γ) := by
      funext d
      conv_rhs => rw [min_min_min_comm, min_self]
    rw [heq] at key
    exact key
  availability Sig Xi₀ hscope hgrade := by
    obtain ⟨Xi, hcell, hle⟩ := h.availability Sig Xi₀ hscope hgrade
    exact ⟨Xi, hcell, min_le_min hle le_rfl⟩

/-! ### More label arithmetic for the canonical alphabet -/

namespace Value

/-- The limit part has finite part `0`. -/
theorem finitePart_limitPart x : finitePart (limitPart x) = 0 := by
  have h := finitePart_limitPart_add_nat x 0
  rwa [Nat.cast_zero, add_zero] at h

/-- The limit part is idempotent. -/
theorem limitPart_idem x : limitPart (limitPart x) = limitPart x :=
  eq_limitPart_of_finitePart_eq_zero (finitePart_limitPart x)

/-- A code with a smaller block index is below the larger block level: `ω·u + m < ω·v` for
`u < v`. -/
theorem code_add_lt_mul {u v : Ordinal.{0}} (h : u < v) (m : ℕ) :
    Ordinal.omega0 * u + m < Ordinal.omega0 * v :=
  calc Ordinal.omega0 * u + (m : Ordinal.{0})
      < Ordinal.omega0 * u + Ordinal.omega0 :=
        add_lt_add_right (Ordinal.natCast_lt_omega0 m) _
    _ = Ordinal.omega0 * Order.succ u := (Ordinal.mul_succ _ _).symm
    _ ≤ Ordinal.omega0 * v :=
        (Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono.monotone
          (Order.succ_le_of_lt h)

/-- Within a block, order is finite-part order. -/
theorem finitePart_le_of_le {x y} (hlim : limitPart x = limitPart y)
    (hxy : x ≤ y) : finitePart x ≤ finitePart y := by
  have h1 : limitPart y + (finitePart x : Ordinal) = x := by rw [← hlim]; exact decomposition x
  have h2 : limitPart y + (finitePart y : Ordinal) = y := decomposition y
  have h3 : limitPart y + (finitePart x : Ordinal) ≤ limitPart y + (finitePart y : Ordinal) := by
    rw [h1, h2]; exact hxy
  exact_mod_cast (add_le_add_iff_left (limitPart y)).mp h3

end Value

namespace ExtOrd

/-- The **coded alphabet** at block bound `t` and grade bound `K` (note §§3–4): `⊥` together
with the codes `ω·u + m`, `u ≤ t`, `m ≤ K+1` — a `Finset`. -/
noncomputable def codedAlphabet (t K : ℕ) : Finset ExtOrd :=
  insert ⊥ ((Finset.range (t + 1) ×ˢ Finset.range (K + 2)).image
    fun um => ofOrd (Ordinal.omega0 * um.1 + um.2))

theorem mem_codedAlphabet_iff {t K} {x} :
    x ∈ codedAlphabet t K ↔
      x = ⊥ ∨ ∃ u m, u ≤ t ∧ m ≤ K + 1 ∧ x = ofOrd (Ordinal.omega0 * u + m) := by
  simp only [codedAlphabet, Finset.mem_insert, Finset.mem_image, Finset.mem_product,
    Finset.mem_range]
  constructor
  · rintro (h | ⟨⟨u, m⟩, ⟨hu, hm⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨u, m, by omega, by omega, rfl⟩
  · rintro (h | ⟨u, m, hu, hm, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨⟨u, m⟩, ⟨by omega, by omega⟩, rfl⟩

/-- **The finite inventory at the combinatorial level** (note §4; the counting content of
Lemmas 4.3.4/4.3.9/4.3.11): over a finite family, the labellings with values in the coded
alphabet form a finite set. -/
theorem codedLabellings_finite (D : Type*) [Finite D] t K :
    {F : D → ExtOrd | ∀ d, F d ∈ codedAlphabet t K}.Finite := by
  have h : {F : D → ExtOrd | ∀ d, F d ∈ codedAlphabet t K} =
      Set.pi Set.univ fun _ : D => (codedAlphabet t K : Set ExtOrd) := by
    ext F
    simp [Set.mem_pi]
  rw [h]
  exact Set.Finite.pi fun _ => (codedAlphabet t K).finite_toSet

end ExtOrd
end VaughtConjecture.Knight
