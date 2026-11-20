/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.OrdinalUtil
public import InfinitaryLogic.Scott.Sentence
public import Architect

@[expose] public section

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]

variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Ordinal BoundedFormulaω

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- Chain-constant step: under self-stabilization at α₀, if BFEquiv ε holds at (n+1)-tuples
and BFEquiv (succ(succ ε)) holds at n-tuples, then BFEquiv (succ ε) holds at (n+1)-tuples.

The proof uses back at level succ ε to find an M-witness mw, then self-stabilization to
show the original and new M-witnesses are equivalent at all levels ≥ α₀. -/
private theorem chain_step
    {M : Type w} [L.Structure M]
    {N : Type w} [L.Structure N] [Countable N]
    {α₀ : Ordinal.{0}} (hstab : SelfStabilizesCompletely (L := L) M α₀)
    {n : ℕ} {a : Fin n → M} {b : Fin n → N} {m : M} {m' : N}
    {ε : Ordinal.{0}} (hε : α₀ ≤ ε)
    (hBF_ext : BFEquiv (L := L) ε (n + 1) (Fin.snoc a m) (Fin.snoc b m'))
    (hBF_base : BFEquiv (L := L) (Order.succ (Order.succ ε)) n a b) :
    BFEquiv (L := L) (Order.succ ε) (n + 1) (Fin.snoc a m) (Fin.snoc b m') := by
  obtain ⟨mw, hmw⟩ := BFEquiv.back hBF_base m'
  exact BFEquiv.trans
    (BFEquiv_upgrade_at_selfStabilization hstab
      (BFEquiv.monotone hε (BFEquiv.trans hBF_ext (BFEquiv.symm (BFEquiv.of_succ hmw))))
      (Order.succ ε) (le_of_lt (Order.lt_succ_of_le hε)))
    hmw

private theorem add_nat_succ (α : Ordinal.{0}) (k : ℕ) :
    α + ↑(k + 1) = Order.succ (α + ↑k) := by simp [Order.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_assoc]

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- From a forth/back witness at level α₀, upgrade to BFEquiv (α₀+k) for all k.
Uses `chain_step` inductively: each level α₀+k upgrades to α₀+(k+1) because
self-stabilization forces the witness chain to be constant. -/
private theorem witness_at_all_levels
    {M : Type w} [L.Structure M]
    {N : Type w} [L.Structure N] [Countable N]
    {α₀ : Ordinal.{0}} (hstab : SelfStabilizesCompletely (L := L) M α₀)
    {n : ℕ} {a : Fin n → M} {b : Fin n → N} {m : M} {m' : N}
    (hbase : ∀ k : ℕ, BFEquiv (L := L) (α₀ + ↑k) n a b)
    (h0 : BFEquiv (L := L) α₀ (n + 1) (Fin.snoc a m) (Fin.snoc b m'))
    (k : ℕ) : BFEquiv (L := L) (α₀ + ↑k) (n + 1) (Fin.snoc a m) (Fin.snoc b m') := by
  induction k with
  | zero => simpa using h0
  | succ j ih =>
    rw [add_nat_succ]
    apply chain_step hstab le_self_add ih
    rw [Order.succ_eq_add_one, Order.succ_eq_add_one, add_assoc, add_assoc]
    convert hbase (j + 2) using 1; norm_cast

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
private theorem BFEquiv_of_all_finite_levels
    {M : Type w} [L.Structure M]
    {N : Type w} [L.Structure N] [Countable N]
    {α₀ : Ordinal.{0}} (hstab : SelfStabilizesCompletely (L := L) M α₀)
    {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : ∀ k : ℕ, BFEquiv (L := L) (α₀ + ↑k) n a b)
    (ε : Ordinal.{0}) :
    BFEquiv (L := L) ε n a b := by
  induction ε using Ordinal.limitRecOn generalizing n a b with
  | zero => exact BFEquiv.monotone bot_le (by simpa using h 0)
  | add_one ε ih =>
    have hsucc_α₀ : BFEquiv (L := L) (Order.succ α₀) n a b := by
      have := h 1; simp_all
    rw [← Order.succ_eq_add_one, BFEquiv.succ]; refine ⟨@ih n a b h, fun m => ?_, fun m' => ?_⟩
    · let ⟨m'₀, hm'₀⟩ := BFEquiv.forth hsucc_α₀ m
      exact ⟨m'₀, @ih _ _ _ (witness_at_all_levels hstab h hm'₀)⟩
    · let ⟨m₀, hm₀⟩ := BFEquiv.back hsucc_α₀ m'
      exact ⟨m₀, @ih _ _ _ (witness_at_all_levels hstab h hm₀)⟩
  | limit ε hε ih => rw [BFEquiv.limit ε hε]; solve_by_elim

/-- The countable refinement hypothesis holds for all countable relational languages.

For a countable structure M in a countable relational language, and any n-tuple a from M,
the set of refinement ordinals R(n, a) = {ε < ω₁ | ∃ (N, b), BFEquiv ε ∧ ¬BFEquiv (succ ε)}
is countable.

**Proof**: Self-stabilization (`exists_complete_self_stabilization`) gives α₀ < ω₁ where
internal BFEquiv on M is frozen. For any ε above γ = sup_k(α₀+k) with BFEquiv ε n a b,
the monotonicity of BFEquiv gives BFEquiv (α₀+k) for all k. The "constant chain" argument
(`witness_at_all_levels`) shows that forth/back witnesses at level α₀ work at all higher
levels (via self-stabilization + transitivity), so `BFEquiv_of_all_finite_levels` upgrades
BFEquiv to the successor. Hence no refinement ordinals exist above γ < ω₁. -/
@[blueprint "thm:CRH"
  (title := /-- Countable refinement hypothesis -/)
  (statement := /-- For any countable relational language $L$, countable $L$-structure
    $M$, tuple size $n$, and tuple $a \in M^n$, the set of refinement ordinals
    $\{\varepsilon < \omegaone \mid \exists (N, b)\, \BFEquiv_\varepsilon(a,b)
    \wedge \neg\BFEquiv_{\varepsilon+1}(a,b)\}$ is countable. -/)
  (proof := /-- From self-stabilization: witnesses at $\alpha_0$ persist at all
    $\alpha_0 + k$. The chain $\alpha_0, \alpha_0+1, \ldots$ has limit
    $\gamma < \omegaone$ which is itself a limit ordinal, giving BFEquiv at $\gamma$
    and hence at all ordinals. -/)
  (proofUses := ["thm:self-stabilization"])]
theorem countableRefinementHypothesis : CountableRefinementHypothesis.{u, v, w} L := by
  intro M inst_struct inst_count n a
  obtain ⟨α₀, hα₀_lt, hstab⟩ := exists_complete_self_stabilization (L := L) M
  have hα_k_lt : ∀ k : ℕ, α₀ + ↑k < (Cardinal.aleph 1).ord := by
    intro k; rw [Cardinal.ord_aleph]
    induction k with
    | zero => simpa
    | succ j ih =>
      rw [Nat.cast_succ, ← add_assoc]
      exact Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1) ih
  have hBdd : BddAbove (Set.range fun k : ℕ => α₀ + (↑k : Ordinal.{0})) :=
    ⟨(Cardinal.aleph 1).ord, fun _ ⟨k, hk⟩ => hk ▸ le_of_lt (hα_k_lt k)⟩
  set γ := ⨆ k : ℕ, (α₀ + (↑k : Ordinal.{0}))
  have hγ_lt : γ < Ordinal.omega 1 := by
    exact Ordinal.iSup_lt_omega_one fun k => by rw [← Cardinal.ord_aleph]; exact hα_k_lt k
  apply Set.Countable.mono (s₂ := Set.Iio γ) _ (InfinitaryLogic.setCountable_Iio_of_lt_omega1 γ hγ_lt)
  intro ε ⟨_, N, instN, instCN, b, hBF, hNot⟩
  simp only [Set.mem_Iio]
  by_contra hge; push Not at hge
  exact hNot (BFEquiv_of_all_finite_levels hstab
    (fun k => BFEquiv.monotone (le_trans (le_ciSup hBdd k) hge) hBF)
    (Order.succ ε))

/-- The Scott sentence of M characterizes M up to isomorphism among countable structures. -/
@[blueprint "thm:scott-characterizes"
  (title := /-- Scott characterization -/)
  (statement := /-- The Scott sentence of a countable structure $M$ characterizes $M$
    up to isomorphism among countable structures (unconditional corollary of CRH). -/)
  (proof := /-- Instantiate the conditional characterization theorem with the
    proved Countable Refinement Hypothesis. -/)
  (proofUses := ["thm:CRH", "thm:scott-characterizes-of"])]
theorem scottSentence_characterizes (M : Type w) [L.Structure M] [Countable M]
    (N : Type w) [L.Structure N] [Countable N] :
    (scottSentence (L := L) M).realize_as_sentence N ↔ Nonempty (M ≃[L] N) :=
  scottSentence_characterizes_of countableRefinementHypothesis M N

/-- If N realizes the Scott sentence of M, then M ≃[L] N. -/
theorem scottSentence_realizes_implies_equiv (M : Type w) [L.Structure M] [Countable M]
    (N : Type w) [L.Structure N] [Countable N]
    (h : (scottSentence (L := L) M).realize_as_sentence N) : Nonempty (M ≃[L] N) :=
  (scottSentence_characterizes M N).mp h

/-- M itself satisfies its own Scott sentence. -/
theorem scottSentence_self (M : Type w) [L.Structure M] [Countable M] :
    (scottSentence (L := L) M).realize_as_sentence M :=
  (scottSentence_characterizes M M).mpr ⟨Equiv.refl L M⟩

end Language

end FirstOrder
