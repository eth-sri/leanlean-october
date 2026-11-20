/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RawReferenceContext

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization Value ExtOrd

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}

/-- Acquire representatives first, then choose an arity above all offsets
and install a full-grade cap strictly above every requested endpoint. -/
theorem exists_referenceContext_margin (hM : R.IsModel) (p : S α.1 n) (hp : R.eval t = some p)
    (reqs : List BlockRequest) (hreqs : ∀ r ∈ reqs, IsNonSuccessor r.block ∧ r.block < α.1)
    (Nmin : ℕ) : ∃ C : ReferenceContext R t reqs, Nmin < C.m ∧ ⊥ < C.p₀.label C.capBase ∧
      ∀ r ∈ reqs, ofOrd (r.block + C.m) < C.p₀.label C.capBase := by
  classical
  have hblocks (μ) (hμ : μ ∈ blocksOf reqs) : IsNonSuccessor μ ∧ μ < α.1 := by
    obtain ⟨r, hr, rfl⟩ := mem_blocksOf.mp hμ
    exact hreqs r hr
  obtain ⟨C⟩ := exists_rawReferenceContext hM p hp (blocksOf reqs) hblocks
  let K := C.offsetBound + reqs.toFinset.sup BlockRequest.offset + Nmin
  let N := C.m + K + 1
  obtain ⟨B, hm, ho⟩ := C.pad hM K
  let γ := (blocksOf reqs).sup fun μ => μ + (N : Ordinal.{0})
  have hγ : γ < α.1 := (Finset.sup_lt_iff stage_pos).mpr fun μ hμ =>
    add_nat_lt_stage (hblocks μ hμ).2 N
  obtain ⟨y, hy, q, ⟨cap, hg, hc⟩, hcof, heval⟩ := hM.highGradeDominance B.ctx B.p₀ B.eval_ctx γ hγ
  let T := B.step hcof heval
  have hT : T.m = N := congrArg (· + 1) hm
  let rep (μ : Ordinal.{0}) : Cell q.scheme.scheme × ℕ :=
    if h : μ ∈ blocksOf reqs then (T.repBase ⟨μ, h⟩, T.repOff ⟨μ, h⟩) else (cap, 0)
  have mem (r) (hr : r ∈ reqs) : r.block ∈ blocksOf reqs := mem_blocksOf.mpr ⟨r, hr, rfl⟩
  refine ⟨⟨T.toCtx, cap, hg, (rep · |>.1), (rep · |>.2), ?_, ?_, ?_⟩, ?_,
    (bot_lt_ofOrd _).trans hc, ?_⟩
  · intro r hr
    simpa only [rep, dif_pos (mem r hr)] using! T.rep_label ⟨r.block, mem r hr⟩
  · intro r hr
    have hle := C.rep_off_le ⟨r.block, mem r hr⟩
    change (rep r.block).2 < T.m
    simp only [rep, dif_pos (mem r hr), hT]
    change B.repOff _ < N
    rw [ho]
    omega
  · intro r hr
    have := Finset.le_sup (f := BlockRequest.offset) (List.mem_toFinset.mpr hr)
    change _ < T.m
    rw [hT]
    omega
  · change _ < T.m
    rw [hT]
    omega
  · intro r hr
    change ofOrd (r.block + T.m) < q.label cap
    rw [hT]
    exact (ofOrd_le_ofOrd.mpr (Finset.le_sup (f := fun μ => μ + (N : Ordinal.{0})) (mem r hr))).trans_lt hc

end VaughtConjecture.Knight
