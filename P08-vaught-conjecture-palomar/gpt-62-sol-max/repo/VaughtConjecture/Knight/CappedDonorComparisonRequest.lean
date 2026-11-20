/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorContext
public import VaughtConjecture.Knight.CappedDonorReadback

@[expose] public section

universe w

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan

namespace CappedDonor

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}

/-- Acquire aligned reference data above the given cutoff and threshold floor. -/
theorem exists_ref_above_cut_min (hM : R.IsModel) (p : S α.1 n) (hp : R.eval t = some p)
    (q : S α.1 (n + 1)) (hq : IsCoface p q) (ν : Ordinal.{0}) (hν : ν < α.1) (Nmin : ℕ) :
    ∃ (C : ReferenceContext R t (⟨limitPart ν, finitePart ν⟩ :: donorRequests q))
      (T : WholeDonorAttachment.SharedFace C.p₀.scheme q.scheme p.scheme C.proj)
      (Rf : Ref ↥(blocksOf (⟨limitPart ν, finitePart ν⟩ :: donorRequests q)) n C.m C.m
        q.scheme C.p₀.scheme),
      Rf.p = q.label ∧ Rf.vact = C.p₀.label ∧ Aligned T Rf ∧
      Nmin < C.m ∧ ofOrd ν < Rf.cut Rf.vactL := by
  set reqs : List BlockRequest := ⟨limitPart ν, finitePart ν⟩ :: donorRequests q with hreqs_def
  have hreqs : ∀ r ∈ reqs, Value.IsNonSuccessor r.block ∧ r.block < α.1 := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨isNonSuccessor_limitPart ν, (limitPart_le ν).trans_lt hν⟩
    · exact donorRequests_ok q r hr
  obtain ⟨C, hmax, hcap_pos, hmargin⟩ :=
    exists_referenceContext_margin hM p hp reqs hreqs (max (n + 1) Nmin)
  have hNmin : n + 1 < C.m := (le_max_left _ _).trans_lt hmax
  obtain ⟨T, Rf, h1, h2, hμ, hface⟩ :=
    ref_of_referenceContext hM p hp q hq hreqs (fun r hr => List.mem_cons_of_mem _ hr) C hNmin
      hcap_pos hmargin
  refine ⟨C, T, Rf, h1, h2, hface, (le_max_right _ _).trans_lt hmax, ?_⟩
  have hmem : limitPart ν ∈ blocksOf reqs := mem_blocksOf.mpr ⟨_, List.mem_cons_self, rfl⟩
  have hoff : finitePart ν < C.m := C.offset_lt _ List.mem_cons_self
  rw [Rf.cut_actual]
  refine lt_of_lt_of_le ?_ (Finset.le_sup (f := fun i : ↥(blocksOf reqs) =>
    ofOrd (Rf.μ i + C.m)) (Finset.mem_univ ⟨limitPart ν, hmem⟩))
  rw [hμ]
  change ofOrd ν < ofOrd (limitPart ν + C.m)
  rw [ofOrd_lt_ofOrd]
  calc ν = limitPart ν + finitePart ν := (decomposition ν).symm
    _ < limitPart ν + C.m := (add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr hoff)

end CappedDonor

end VaughtConjecture.Knight
