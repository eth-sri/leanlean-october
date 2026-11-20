/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Scott.Formula
public import InfinitaryLogic.Karp.PotentialIso
public import Mathlib.ModelTheory.PartialEquiv
public import Mathlib.SetTheory.Cardinal.Regular
public import Architect

@[expose] public section

universe u v w u' w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]

variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Ordinal BoundedFormulaω Substructure

/-- BFEquiv at the empty tuple level. This is the key semantic predicate for Scott sentences. -/
abbrev BFEquiv0 (M : Type w) (N : Type w') [L.Structure M] [L.Structure N] (α : Ordinal) : Prop :=
  BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)

/-- The ordinal α stabilizes for M if BFEquiv0 at level α characterizes isomorphism
with M among all countable structures of the same type. -/
def StabilizesAt (M : Type w) [L.Structure M] (α : Ordinal) : Prop :=
  ∀ (N : Type w) [L.Structure N] [Countable N], BFEquiv0 (L := L) M N α ↔ Nonempty (M ≃[L] N)

/-- BFEquiv α on n-tuples from M equals BFEquiv (succ α) for all countable N.
This captures when the BFEquiv relation has stopped distinguishing tuples at level α. -/
def StabilizesForTuples (M : Type w) [L.Structure M] (α : Ordinal) (n : ℕ) : Prop :=
  ∀ (N : Type w) [L.Structure N] [Countable N] (a : Fin n → M) (b : Fin n → N),
    BFEquiv (L := L) α n a b ↔ BFEquiv (L := L) (Order.succ α) n a b

/-- All tuple sizes stabilize at α. This is the key condition for the back-and-forth
argument to yield an isomorphism. -/
def StabilizesCompletely (M : Type w) [L.Structure M] (α : Ordinal) : Prop :=
  ∀ n : ℕ, StabilizesForTuples (L := L) M α n

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- An isomorphism induces BF-equivalence at all ordinal levels. -/
theorem equiv_implies_BFEquiv {M N : Type w} [L.Structure M] [L.Structure N]
    (e : M ≃[L] N) (α : Ordinal) (n : ℕ) (a : Fin n → M) :
    BFEquiv (L := L) α n a (e ∘ a) := by
  induction α using Ordinal.limitRecOn generalizing n a with
  | zero =>
    rw [BFEquiv.zero]
    intro idx
    cases idx with
    | eq i j =>
      simp only [AtomicIdx.holds, Function.comp_apply]
      simp
    | rel R f =>
      simp only [AtomicIdx.holds, Function.comp_assoc]
      simp
  | add_one β ih =>
    rw [← Order.succ_eq_add_one, BFEquiv.succ]
    refine ⟨ih n a, ?_, ?_⟩
    · intro m
      use e m
      rw [← Fin.comp_snoc]
      tauto
    · intro n'
      use e.symm n'
      have h1 := ih (n + 1) (Fin.snoc a (e.symm n'))
      rwa [Fin.comp_snoc, e.apply_symm_apply] at h1
  | limit β hβ ih =>
    rw [BFEquiv.limit β hβ]
    tauto

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- Self-stabilization: BFEquiv α on n-tuples from M vs M equals BFEquiv (succ α)
for all n. This is weaker than `StabilizesCompletely` which requires the iff
to hold for all countable N, not just M itself. -/
def SelfStabilizesCompletely (M : Type w) [L.Structure M] (α : Ordinal) : Prop :=
  ∀ (n : ℕ) (a a' : Fin n → M),
    BFEquiv (L := L) α n a a' ↔ BFEquiv (L := L) (Order.succ α) n a a'

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- **Upgrade at a self-stabilization level**: if `M` self-stabilizes completely at `α₀`, then
back-and-forth equivalence at `α₀` of two tuples of `M` persists to every level `β ≥ α₀`.  The
one-structure counterpart of `BFEquiv_upgrade_at_stabilization`; the ordinals and the carrier
live in arbitrary universes, and no countability is assumed. -/
theorem BFEquiv_upgrade_at_selfStabilization {M : Type w} [L.Structure M] {α₀ : Ordinal}
    (hstab : SelfStabilizesCompletely (L := L) M α₀) {n : ℕ} {a a' : Fin n → M}
    (h : BFEquiv (L := L) α₀ n a a') (β : Ordinal) (hβ : α₀ ≤ β) :
    BFEquiv (L := L) β n a a' := by
  induction β using Ordinal.limitRecOn generalizing n a a' with
  | zero => simp_all
  | add_one γ ih =>
    rw [← Order.succ_eq_add_one] at hβ ⊢
    rcases hβ.lt_or_eq with hlt | heq
    · rw [Order.lt_succ_iff] at hlt
      have h_succ := (hstab n a a').mp h
      rw [BFEquiv.succ]
      refine ⟨ih h hlt, fun m ↦ ?_, fun m' ↦ ?_⟩
      · obtain ⟨m', hm'⟩ := BFEquiv.forth h_succ m
        tauto
      · obtain ⟨m, hm⟩ := BFEquiv.back h_succ m'
        tauto
    simp_all
  | limit β hlim ih =>
    rw [BFEquiv.limit β hlim]
    intro γ hγ
    exact (le_or_gt α₀ γ).elim (ih γ hγ h) fun hαγ ↦ BFEquiv.monotone hαγ.le h

private theorem countable_ordinal_bound {I : Type*} [Countable I]
    (f : I → Ordinal.{0}) (hf : ∀ i, f i < Ordinal.omega 1) :
    ∃ α < Ordinal.omega 1, ∀ i, f i < α := by
  let α := ⨆ i, f i
  have hlt : α < Ordinal.omega 1 := Ordinal.iSup_lt_omega_one hf
  refine ⟨Order.succ α, (Cardinal.isSuccLimit_omega 1).succ_lt hlt, fun i => ?_⟩
  exact (le_ciSup ⟨Ordinal.omega 1, by rintro _ ⟨j, rfl⟩; exact (hf j).le⟩ i).trans_lt (Order.lt_succ α)

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- Take a common bound for one failure ordinal of each tuple pair that fails below `ω₁`.
All other tuple pairs remain equivalent at every countable ordinal. -/
@[blueprint "thm:self-stabilization"
  (title := /-- Self-stabilization -/)
  (statement := /-- For any countable $L$-structure $M$, there exists $\alpha < \omegaone$
    such that $M$ self-stabilizes completely at $\alpha$: for every $n$ and tuples
    $a, a' \in M^n$, $\BFEquiv_\alpha(a,a') \iff \BFEquiv_{\alpha+1}(a,a')$. -/)
  (proof := /-- For each triple $(n, a, a')$, the first failure ordinal is $0$ or a
    successor. Take the supremum over countably many triples;
    $\sup + 1 < \omegaone$. -/)
  (uses := ["def:BFEquiv"])]
theorem exists_complete_self_stabilization (M : Type w) [L.Structure M] [Countable M] :
    ∃ α < (Ordinal.omega 1 : Ordinal.{0}), SelfStabilizesCompletely (L := L) M α := by
  have hb (t : Σ n, (Fin n → M) × (Fin n → M)) :
      ∃ β < Ordinal.omega 1, ∀ α, β ≤ α → α < Ordinal.omega 1 →
        (BFEquiv (L := L) α t.1 t.2.1 t.2.2 ↔ BFEquiv (L := L) (Order.succ α) t.1 t.2.1 t.2.2) := by
    by_cases h : ∃ β < Ordinal.omega 1, ¬ BFEquiv (L := L) β t.1 t.2.1 t.2.2
    · obtain ⟨β, hβ, hn⟩ := h
      exact ⟨β, hβ, fun _ hle _ => ⟨fun he => (hn (BFEquiv.monotone hle he)).elim, BFEquiv.of_succ⟩⟩
    · push Not at h
      exact ⟨0, Ordinal.omega_pos 1, fun _ _ hlt =>
        ⟨fun _ => h _ ((Cardinal.isSuccLimit_omega 1).succ_lt hlt), BFEquiv.of_succ⟩⟩
  choose f hf hp using hb
  obtain ⟨α, hα, hbound⟩ := countable_ordinal_bound f hf
  exact ⟨α, hα, fun n a b => hp ⟨n, a, b⟩ α (hbound ⟨n, a, b⟩).le hα⟩

/-- **Counting hypothesis** for per-tuple stabilization.

For a countable structure M in a countable relational language, the set of ordinals
below ω₁ where BFEquiv refinement occurs for a fixed tuple is countable.

This encapsulates the deep counting argument: each refinement step corresponds to a
split in the formula-type partition, and countable structures admit only countably many
such splits.

**Boundary**: This is the sole non-trivial hypothesis in the Scott analysis pipeline.
All other reasoning (descent lemmas, stabilization from countability, Scott rank bounds)
is fully formalized. -/
def CountableRefinementHypothesis (L : Language.{u, v})
    [L.IsRelational] [Countable (Σ l, L.Relations l)] : Prop :=
  ∀ (M : Type w) [L.Structure M] [Countable M] (n : ℕ) (a : Fin n → M),
    Set.Countable {ε : Ordinal.{0} | ε < Ordinal.omega 1 ∧
      ∃ (N : Type w) (_ : L.Structure N) (_ : Countable N) (b : Fin n → N),
        BFEquiv (L := L) ε n a b ∧ ¬BFEquiv (L := L) (Order.succ ε) n a b}

/-- Per-tuple stabilization, conditional on `CountableRefinementHypothesis`. -/
theorem per_tuple_stabilization_below_omega1_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    {M : Type w} [L.Structure M] [Countable M]
    (n : ℕ) (a : Fin n → M) :
    ∃ γ < (Ordinal.omega 1 : Ordinal.{0}),
      ∀ α, γ ≤ α → α < Ordinal.omega 1 → Order.succ α < Ordinal.omega 1 →
        ∀ (N : Type w) [L.Structure N] [Countable N] (b : Fin n → N),
          (BFEquiv (L := L) α n a b ↔ BFEquiv (L := L) (Order.succ α) n a b) := by
  let F := {α : Ordinal.{0} | α < Ordinal.omega 1 ∧
    ∃ (N : Type w) (_ : L.Structure N) (_ : Countable N) (b : Fin n → N),
      BFEquiv (L := L) α n a b ∧ ¬BFEquiv (L := L) (Order.succ α) n a b}
  letI : Countable F := (hcount M n a).to_subtype
  obtain ⟨γ, hγ, hb⟩ := countable_ordinal_bound (fun x : F => x.1) (fun x => x.2.1)
  refine ⟨γ, hγ, fun α hγα hα _ N instN instCN b => ⟨?_, BFEquiv.of_succ⟩⟩
  intro he
  by_contra hn
  exact (hb ⟨α, hα, N, instN, instCN, b, he, hn⟩).not_ge hγα

/-- Complete stabilization, conditional on `CountableRefinementHypothesis`. -/
theorem exists_complete_stabilization_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    (M : Type w) [L.Structure M] [Countable M] :
    ∃ α < (Ordinal.omega 1 : Ordinal.{0}), StabilizesCompletely (L := L) M α := by
  have hTuple : ∀ (t : Σ n, Fin n → M),
      ∃ γ < (Ordinal.omega 1 : Ordinal.{0}),
        ∀ α, γ ≤ α → α < Ordinal.omega 1 → Order.succ α < Ordinal.omega 1 →
          ∀ (N : Type w) [L.Structure N] [Countable N] (b : Fin t.1 → N),
            (BFEquiv (L := L) α t.1 t.2 b ↔ BFEquiv (L := L) (Order.succ α) t.1 t.2 b) :=
    fun ⟨n, a⟩ => per_tuple_stabilization_below_omega1_of hcount n a
  choose f hf hp using hTuple
  obtain ⟨α, hα, hb⟩ := countable_ordinal_bound f hf
  exact ⟨α, hα, fun n N _ _ a b =>
    hp ⟨n, a⟩ α (hb ⟨n, a⟩).le hα ((Cardinal.isSuccLimit_omega 1).succ_lt hα) N b⟩

omit [Countable (Σ l, L.Relations l)] in
/-- At a complete stabilization ordinal, BFEquiv0 implies isomorphism for countable structures.
This is the corrected version of BFEquiv_omega_implies_equiv. -/
theorem BFEquiv_stabilization_implies_equiv {M N : Type w} [L.Structure M] [L.Structure N]
    [Countable M] [Countable N]
    {α : Ordinal} (hstab : StabilizesCompletely (L := L) M α)
    (h : BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)) :
    Nonempty (M ≃[L] N) := (PotentialIso.mk
    { p | BFEquiv (L := L) α p.1 p.2.1 p.2.2 }
    ⟨⟨0, Fin.elim0, Fin.elim0⟩, h⟩
    (fun p hp => (BFEquiv.zero p.2.1 p.2.2).mp (BFEquiv.monotone bot_le hp))
    (fun ⟨k, a, b⟩ hp m => by
      simp only [Set.mem_ofPred_eq] at hp ⊢
      exact BFEquiv.forth ((hstab k N a b).mp hp) m)
    (fun ⟨k, a, b⟩ hp n' => by
      simp only [Set.mem_ofPred_eq] at hp ⊢
      exact BFEquiv.back ((hstab k N a b).mp hp) n')
  ).countable_toEquiv

/-- The stabilization ordinal for a structure M: the least ordinal where the Scott analysis
stabilizes. We fix the ordinal universe to 0 for consistency with our BFEquiv definitions. -/
@[blueprint "def:stabilization-ordinal"
  (title := /-- Stabilization ordinal -/)
  (statement := /-- The stabilization ordinal of a countable structure $M$: the least
    ordinal $\alpha$ such that $\BFEquiv_\alpha$ on $0$-tuples characterizes
    isomorphism among countable structures. -/)]
noncomputable def stabilizationOrdinal (M : Type w) [L.Structure M] [Countable M] :
    Ordinal.{0} :=
  sInf {α : Ordinal.{0} | StabilizesAt (L := L) M α}

/-- The Scott sentence of a countable structure M in a relational countable language.

A sentence is a formula with no free variables, which corresponds to `Formulaω (Fin 0)`
since `Fin 0` is empty. -/
@[blueprint "def:scott-sentence"
  (title := /-- Scott sentence -/)
  (statement := /-- The Scott sentence of $M$: the Scott formula for the empty tuple at
    the stabilization ordinal, $\sigma_{\alpha_0}(\langle\rangle)$. -/)
  (uses := ["def:scottFormula", "def:stabilization-ordinal"])]
noncomputable def scottSentence (M : Type w) [L.Structure M] [Countable M] : L.Formulaω (Fin 0) :=
  scottFormula (L := L) (M := M) (n := 0) Fin.elim0
    (stabilizationOrdinal (L := L) M)

/-- Realize a formula with no free variables as a sentence in a structure. -/
def Formulaω.realize_as_sentence (φ : L.Formulaω (Fin 0)) (N : Type w) [L.Structure N] : Prop :=
  φ.Realize (Fin.elim0 : Fin 0 → N)

omit [L.IsRelational] [Countable ((l : ℕ) × L.Relations l)] in
/-- Bridge between `realize_as_sentence` and `Sentenceω.Realize` via `toSentenceω`. -/
theorem Formulaω.realize_as_sentence_iff_toSentenceω
    (φ : L.Formulaω (Fin 0)) (N : Type w) [L.Structure N] :
    φ.realize_as_sentence N ↔ Sentenceω.Realize φ.toSentenceω N := by
  simpa [Formulaω.realize_as_sentence] using (Formulaω.realize_toSentenceω (M := N) φ).symm

/-- Conditional variant of `exists_stabilization`. -/
theorem exists_stabilization_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    (M : Type w) [L.Structure M] [Countable M] :
    ∃ α < (Ordinal.omega 1 : Ordinal.{0}), StabilizesAt (L := L) M α := by
  obtain ⟨α, hα_lt, hstab⟩ := exists_complete_stabilization_of hcount M
  use α, hα_lt
  intro N _ _
  constructor
  · exact BFEquiv_stabilization_implies_equiv hstab
  · intro ⟨e⟩
    show BFEquiv0 (L := L) M N α
    unfold BFEquiv0
    rw [← comp_fin_elim0 e]
    exact equiv_implies_BFEquiv e α 0 Fin.elim0

/-- Conditional variant of `stabilizationOrdinal_lt_omega1'`. -/
theorem stabilizationOrdinal_lt_omega1_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    (M : Type w) [L.Structure M] [Countable M] :
    stabilizationOrdinal (L := L) M < Ordinal.omega 1 := by
  obtain ⟨α, hα_lt, hα_spec⟩ := exists_stabilization_of hcount M
  exact lt_of_le_of_lt (csInf_le' hα_spec) hα_lt

/-- Conditional variant of `stabilizationOrdinal_stabilizes`. -/
theorem stabilizationOrdinal_stabilizes_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    (M : Type w) [L.Structure M] [Countable M] :
    StabilizesAt (L := L) M (stabilizationOrdinal (L := L) M) := by
  obtain ⟨α, _, hα_spec⟩ := exists_stabilization_of hcount M
  have h_nonempty : {α : Ordinal.{0} | StabilizesAt (L := L) M α}.Nonempty :=
    ⟨α, hα_spec⟩
  exact csInf_mem h_nonempty

/-- **Conditional Scott sentence characterization**: variant of
`scottSentence_characterizes`, conditional on `CountableRefinementHypothesis`.

A countable structure N satisfies the Scott sentence of M iff M ≅ N.
Uses the same `scottSentence M` definition; only the proof is rebuilt
through the conditional pipeline. -/
@[blueprint "thm:scott-characterizes-of"
  (title := /-- Scott characterization (conditional) -/)
  (statement := /-- Assuming the countable refinement hypothesis: the Scott sentence of
    a countable structure $M$ characterizes $M$ up to isomorphism among countable
    structures, i.e., $N \models \sigma_M \iff M \cong N$. -/)
  (proof := /-- By the Scott formula characterization at the stabilization ordinal, plus
    the CRH-conditional stabilization result. -/)
  (proofUses := ["thm:scottFormula-iff", "def:scott-sentence",
    "def:stabilization-ordinal"])]
theorem scottSentence_characterizes_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    (M : Type w) [L.Structure M] [Countable M]
    (N : Type w) [L.Structure N] [Countable N] :
    (scottSentence (L := L) M).realize_as_sentence N ↔ Nonempty (M ≃[L] N) := by
  unfold scottSentence Formulaω.realize_as_sentence
  have h := realize_scottFormula_iff_BFEquiv (L := L) (M := M) (N := N)
    (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)
    (stabilizationOrdinal (L := L) M) (stabilizationOrdinal_lt_omega1_of hcount M)
  rw [h]
  exact stabilizationOrdinal_stabilizes_of hcount M N

end Language

end FirstOrder
