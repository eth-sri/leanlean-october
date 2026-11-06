import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CappedDonorReceiving
import VaughtConjecture.Knight.CappedDonorFace
import VaughtConjecture.Knight.ReferenceContextMargin
import VaughtConjecture.Knight.ReferenceOrbitRow

/-! # The receiving input from an actual model (notes32 §1, the adapter)

The capped-donor reference data `CappedDonor.Ref` — hence the receiving-input family and both
fibres of `Knight/CappedDonorReceiving.lean` — **obtained from an actual model**: a model `R`,
a realized root tuple `t` of type `p`, and a lawful stage-`α` donor `q`, a coface of `p` (the
request scheme on `A + x` with the actual tuple's type on `A`).

* The **requests** are the block and offset of every proper donor label (`donorRequests`,
  `mem_donorRequests`); their blocks are non-successors below the stage (`donorRequests_ok`).
  The block list `blocks q` may be empty: no representative is then required.
* The **private context** is the reference context with the endpoint margin
  (`exists_referenceContext_margin`, floor `n + 1`), of arity `J = C.m ≥ N`; its cap is the
  full-scope grade-`N` controller `FullController` dominating the reference cap, so the
  acquisition face is the whole context here (`C₀ = univ`).
* The **common face** is literal: the root type is the restriction of the context along the
  projection (the model's consistency clause) and of the donor along the initial segment (the
  coface condition), so `commonFace` / `commonFace_respects` supply the identification and its
  lawfulness transport **at every grade** (`commonFace_grade`, `commonFace_val_congr`), and the
  labels agree on the face (`face_actual`) by `StageType.label_castCell`.  The root arity is
  arbitrary: `KA = n`, with `n = 0` the empty root (the empty face is visible).

`exists_ref` packages all of this: the reference data exists with the donor as `p`, the actual
context labelling as `vact` and the controller as `cap`.  The only model clauses used are those
of the existing reference-context construction (Uniformity, High-Grade Dominance) and
consistency; the margin is supplied by the same High-Grade Dominance step with a larger finite
bound, so no branch is left unsupplied. -/

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization Value ExtOrd  CellScheme.restrictFace

namespace CappedDonor

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}

/-! ## The requests of a donor -/

/-- The block request of a proper label: its block and offset. -/
noncomputable def properRequest : ExtOrd → Option BlockRequest
  | some (some β) => some ⟨limitPart β, finitePart β⟩
  | _ => none

theorem properRequest_ofOrd β :
    properRequest (ofOrd β) = some ⟨limitPart β, finitePart β⟩ := rfl

theorem properRequest_eq_some {x} {r} (h : properRequest x = some r) :
    ∃ β , x = ofOrd β ∧ r = ⟨limitPart β, finitePart β⟩ := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
  · exact nomatch h
  · exact nomatch h
  · grind [properRequest_ofOrd]

/-- The requests of a donor: the block and offset of each proper label. -/
noncomputable def donorRequests (q : S α.1 (n + 1)) :=
  (List.finRange q.scheme.scheme.card).filterMap fun d => properRequest (q.label d)

theorem mem_donorRequests {q : S α.1 (n + 1)} {r} :
    r ∈ donorRequests q ↔ ∃ (d : Cell q.scheme.scheme) (β : Ordinal₀),
      q.label d = ofOrd β ∧ r = ⟨limitPart β, finitePart β⟩ := by
  unfold donorRequests
  
  constructor
  · grind [properRequest_eq_some]
  · grind [properRequest_ofOrd]

/-- The limit part of an ordinal is a non-successor (ported from the reviewer's private lemma in
`FiniteBlockBridge`, with attribution). -/
theorem isNonSuccessor_limitPart δ : IsNonSuccessor (limitPart δ) := by
  by_cases h0 : limitPart δ = 0
  · exact Or.inl h0
  · refine Or.inr ?_
    
    refine ⟨by simpa using h0, Ordinal.isSuccPrelimit_iff_omega0_dvd.2 ?_⟩
    exact ⟨δ / Ordinal.omega0, rfl⟩

/-- The requested blocks are non-successors below the stage. -/
theorem donorRequests_ok (q : S α.1 (n + 1)) :
    ∀ r ∈ donorRequests q, IsNonSuccessor r.block ∧ r.block < α.1 := by
  intro r hr
  obtain ⟨d, β, hβ, rfl⟩ := mem_donorRequests.mp hr
  refine ⟨isNonSuccessor_limitPart β, ?_⟩
  rcases q.label_bound d with h | h
  · rw [hβ, ofOrd_lt_ofOrd] at h
    exact (limitPart_le).trans_lt h
  · simp_all [VaughtConjecture.Knight.ExtOrd.ofOrd]

open Classical in
/-- The blocks of a request list. -/
noncomputable def blocksOf (reqs : List BlockRequest) :=
  reqs.toFinset.image BlockRequest.block

open Classical in
theorem mem_blocksOf {reqs} {μ} :
    μ ∈ blocksOf reqs ↔ ∃ r ∈ reqs, r.block = μ := by
  unfold blocksOf
  simp  

/-- The requested blocks of a donor. -/
noncomputable def blocks (q : S α.1 (n + 1)) := blocksOf (donorRequests q)

theorem mem_blocks {q : S α.1 (n + 1)} {μ : Ordinal₀} :
    μ ∈ blocks q ↔ ∃ r ∈ donorRequests q, r.block = μ := mem_blocksOf

/-! ## The reference data from the model -/

/-- **The receiving input from a reference context**: over a realized root tuple `t` of type `p`
(any arity, the empty root included), a lawful donor `q`, a coface of `p`, and a reference
context with the endpoint margin for a request list containing the donor's requests, there are a
full-scope grade-`N` controller and capped-donor reference data over the blocks of the list whose
donor is `q`, whose actual private labelling is the context's, and whose cap is the controller.
Extra requests are
**comparison-only references**: representatives acquired and their offsets observed before the
threshold is chosen.  This form exports the geometric receipts of the construction: the block map
is the block itself (`μ = Subtype.val`), the faces, representatives and offsets are the context's,
and the face identification is the literal common face `commonFace`. -/
theorem ref_of_referenceContext' (hM : R.IsModel) p
    (hp : R.eval t = some p) q (hq : IsCoface p q) {reqs}
    (hreqs : ∀ r ∈ reqs, Value.IsNonSuccessor r.block ∧ r.block < α.1)
    (hsub : ∀ r ∈ donorRequests q, r ∈ reqs) (C : ReferenceContext R t reqs)
    (hNmin : n + 1 < C.N) (hcap_pos : ⊥ < C.p₀.label C.capBase)
    (hmargin : ∀ r ∈ reqs, ofOrd (r.block + C.N) < C.p₀.label C.capBase) :
    ∃ (F : C.FullController) (Rf : Ref ↥(blocksOf reqs) n C.N C.m q.scheme C.p₀.scheme),
      Rf.p = q.label ∧ Rf.vact = C.p₀.label ∧ Rf.cap = F.cell ∧ Rf.KA = n ∧
      Rf.A' = Finset.univ.image C.proj ∧ Rf.A = Finset.univ.image Fin.castSuccEmb ∧
      Rf.μ = Subtype.val ∧ Rf.C₀ = Finset.univ ∧ Rf.ref = (fun i => C.repBase i.1) ∧
      Rf.off = (fun i => C.repOff i.1) ∧
      ∃ (hvP : Finset.univ.image Fin.castSuccEmb ∈ q.scheme.scheme.plan)
        (hP : q.scheme.restrictFace Fin.castSuccEmb hvP = p.scheme)
        (hvC : Finset.univ.image C.proj ∈ C.p₀.scheme.scheme.plan)
        (hC : C.p₀.scheme.restrictFace C.proj hvC = p.scheme),
        HEq Rf.face (commonFace Fin.castSuccEmb hvP hP C.proj hvC hC n) := by
  
  obtain ⟨F⟩ := C.exists_fullController
  -- the consistency clause: the root type is the restriction of the context along the projection
  have hcons : typeMap C.proj C.p₀ = some p := by
    have h := hM.consistent C.ctx C.p₀ C.proj C.eval_ctx
    rw [C.proj_ctx, hp, knightTower_pull] at h
    exact h.symm
  have hvC : Finset.univ.image C.proj ∈ C.p₀.scheme.scheme.plan :=
    (typeMap_isSome_iff).mp (by rw [hcons]; rfl)
  have hC' : C.p₀.restrictFace C.proj hvC = p := by
    exact?
  -- the coface condition: the root type is the restriction of the donor along the initial face
  have hvP  := hq.extendsDomain.visible
  have hP' : q.restrictFace Fin.castSuccEmb hvP = p := by
    exact?
  have hP : q.scheme.restrictFace Fin.castSuccEmb hvP = p.scheme := congrArg StageType.scheme hP'
  have hC : C.p₀.scheme.restrictFace C.proj hvC = p.scheme := congrArg StageType.scheme hC'
  -- the controller's grade is at most the context arity
  have hNm  := by
    have h := C.p₀.scheme.scheme.grade_le_card_scope F.cell
    rw [show C.p₀.scheme.scheme.grade F.cell = C.N from congrArg Prod.snd F.index,
      show C.p₀.scheme.scheme.scope F.cell = Finset.univ from congrArg Prod.fst F.index,
      Finset.card_univ, Fintype.card_fin] at h
    exact h
  -- each block is the block of a request
  have hblk : ∀ i : ↥(blocksOf reqs), ∃ r ∈ reqs, r.block = i.1 := fun i =>
    mem_blocksOf.mp i.2
  refine ⟨F, {
    arity_lt := hNmin
    N_le := hNm
    μ := Subtype.val
    μ_limit := fun i => by
      obtain ⟨r, hr, hrb⟩ := hblk i
      rw [← hrb]
      exact limitPart_eq_self_of_isNonSuccessor (hreqs r hr).1
    μ_inj := Subtype.val_injective
    ref := fun i => C.repBase i.1
    off := fun i => C.repOff i.1
    off_lt := fun i => by
      obtain ⟨r, hr, hrb⟩ := hblk i
      have h := C.rep_off_lt r hr
      rwa [hrb] at h
    C₀ := Finset.univ
    cap := F.cell
    cap_cell := F.index
    ref_scope := fun _ => Finset.subset_univ _
    vact := C.p₀.label
    vact_respects := C.p₀.respects
    vact_ref := fun i => by
      obtain ⟨r, hr, hrb⟩ := hblk i
      have h := C.rep_label r hr
      rwa [hrb] at h
    cap_pos := hcap_pos.trans_le F.dominates
    margin := fun i => by
      obtain ⟨r, hr, hrb⟩ := hblk i
      have h := hmargin r hr
      rw [hrb] at h
      exact h.trans_le F.dominates
    p := q.label
    p_respects := q.respects
    p_code := fun d hb ht => by
      rcases ExtOrd.cases (q.label d) with h | h | ⟨β, hβ⟩
      · exact absurd h hb
      · exact absurd h ht
      have hr  :=
        hsub _ (mem_donorRequests.mpr ⟨d, β, hβ, rfl⟩)
      refine ⟨⟨limitPart β, mem_blocksOf.mpr ⟨_, hr, rfl⟩⟩, finitePart β, C.offset_lt _ hr, ?_⟩
      rw [hβ]
      exact congrArg ofOrd (decomposition β).symm
    A := Finset.univ.image Fin.castSuccEmb
    A' := Finset.univ.image C.proj
    KA := n
    A_mem := hvP
    KA_le_card := by
      rw [Finset.card_image_of_injective _ Fin.castSuccEmb.injective, Finset.card_univ,
        Fintype.card_fin]
    A'_sub := Finset.subset_univ _
    face := commonFace Fin.castSuccEmb hvP hP C.proj hvC hC n
    face_grade := commonFace_grade Fin.castSuccEmb hvP hP C.proj hvC hC n
    face_actual := fun a => by
      rw [commonFace_val]
      exact (StageType.label_castCell hC'.symm _).trans ((StageType.label_castCell hP' _).trans
        (congrArg q.label (toCell_belowEquiv_symm_val _ _ _ _ a)))
    face_respects := fun k hk r => by
      refine (commonFace_respects Fin.castSuccEmb hvP hP C.proj hvC hC k r).trans ?_
      refine Iff.of_eq (congrArg (RespectsSemanticsBelow q.scheme.rows _) (funext fun a => ?_))
      congr 1
      apply Subtype.ext
      exact commonFace_val_congr Fin.castSuccEmb hvP hP C.proj hvC hC k a _ rfl }, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, hvP, hP, hvC, hC, HEq.rfl⟩


