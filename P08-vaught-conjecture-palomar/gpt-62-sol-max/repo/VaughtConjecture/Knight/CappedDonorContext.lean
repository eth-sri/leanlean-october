/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorReceiving
public import VaughtConjecture.Knight.CappedDonorFace
public import VaughtConjecture.Knight.ReferenceContextMargin
public import VaughtConjecture.Knight.WholeDonorAttachment
public import VaughtConjecture.Knight.CommonFaceAlignment

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan CellScheme.restrictFace
open SemSchemeBoundaryInput

namespace CappedDonor

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}

/-- The block request of a proper label: its block and offset. -/
noncomputable def properRequest : ExtOrd → Option BlockRequest
  | some (some β) => some ⟨limitPart β, finitePart β⟩
  | _ => none

theorem properRequest_ofOrd (β : Ordinal.{0}) :
    properRequest (ofOrd β) = some ⟨limitPart β, finitePart β⟩ := rfl

theorem properRequest_eq_some {x : ExtOrd} {r : BlockRequest} (h : properRequest x = some r) :
    ∃ β : Ordinal.{0}, x = ofOrd β ∧ r = ⟨limitPart β, finitePart β⟩ := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
  · exact nomatch h
  · exact nomatch h
  · rw [properRequest_ofOrd] at h
    aesop

/-- The requests of a donor: the block and offset of each proper label. -/
noncomputable def donorRequests (q : S α.1 (n + 1)) : List BlockRequest :=
  (List.finRange q.scheme.scheme.card).filterMap fun d => properRequest (q.label d)

theorem mem_donorRequests {q : S α.1 (n + 1)} {r : BlockRequest} :
    r ∈ donorRequests q ↔ ∃ (d : Cell q.scheme.scheme) (β : Ordinal.{0}),
      q.label d = ofOrd β ∧ r = ⟨limitPart β, finitePart β⟩ := by
  unfold donorRequests
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨d, -, hd⟩
    obtain ⟨β, hβ, hr⟩ := properRequest_eq_some hd
    tauto
  · rintro ⟨d, β, hβ, rfl⟩
    exact ⟨d, List.mem_finRange d, by aesop⟩

/-- The limit part of an ordinal is a non-successor (ported from the reviewer's private lemma in
`FiniteBlockBridge`, with attribution). -/
theorem isNonSuccessor_limitPart (δ : Ordinal.{0}) : IsNonSuccessor (limitPart δ) := by
  by_cases h0 : limitPart δ = 0
  · exact Or.inl h0
  · refine Or.inr ?_
    rw [Order.isSuccLimit_iff]
    refine ⟨by simpa using h0, (Ordinal.isSuccPrelimit_iff_omega0_dvd).2 ?_⟩
    exact ⟨δ / Ordinal.omega0, rfl⟩

/-- The requested blocks are non-successors below the stage. -/
theorem donorRequests_ok (q : S α.1 (n + 1)) :
    ∀ r ∈ donorRequests q, IsNonSuccessor r.block ∧ r.block < α.1 := by
  intro r hr
  obtain ⟨d, β, hβ, rfl⟩ := mem_donorRequests.mp hr
  refine ⟨isNonSuccessor_limitPart β, ?_⟩
  rcases q.label_bound d with h | h
  · rw [hβ, ofOrd_lt_ofOrd] at h
    exact (limitPart_le β).trans_lt h
  · rw [hβ] at h
    simp_all

/-- The requested blocks of a donor. -/
noncomputable def blocks (q : S α.1 (n + 1)) : Finset Ordinal.{0} := blocksOf (donorRequests q)

theorem mem_blocks {q : S α.1 (n + 1)} {μ : Ordinal.{0}} :
    μ ∈ blocks q ↔ ∃ r ∈ donorRequests q, r.block = μ := mem_blocksOf

/-- The two reference rows are indexed by the very same common cells as the attachment. -/
abbrev Aligned {I : Type*} [Fintype I] {n N : ℕ} {P : SemScheme (n + 1)}
    {C : SemScheme N} {Q : SemScheme n} {e : Fin n ↪ Fin N}
    (T : WholeDonorAttachment.SharedFace C P Q e) (Rf : Ref I n N N P C) : Prop :=
  ∀ i : Cell Q.scheme, ∃ d : P.scheme.below (Rf.A, Rf.KA),
    d.1 = T.boundary.shared.g i ∧ (Rf.face d).1 = T.boundary.shared.f i

/-- Acquire reference data with the literal alignment needed by the receiving probe. -/
theorem ref_of_referenceContext (hM : R.IsModel) (p : S α.1 n)
    (hp : R.eval t = some p) (q : S α.1 (n + 1)) (hq : IsCoface p q) {reqs : List BlockRequest}
    (hreqs : ∀ r ∈ reqs, Value.IsNonSuccessor r.block ∧ r.block < α.1)
    (hsub : ∀ r ∈ donorRequests q, r ∈ reqs) (C : ReferenceContext R t reqs)
    (hNmin : n + 1 < C.m) (hcap_pos : ⊥ < C.p₀.label C.capBase)
    (hmargin : ∀ r ∈ reqs, ofOrd (r.block + C.m) < C.p₀.label C.capBase) :
    ∃ (T : WholeDonorAttachment.SharedFace C.p₀.scheme q.scheme p.scheme C.proj)
      (Rf : Ref ↥(blocksOf reqs) n C.m C.m q.scheme C.p₀.scheme),
      Rf.p = q.label ∧ Rf.vact = C.p₀.label ∧ Rf.μ = Subtype.val ∧ Aligned T Rf := by
  classical
  -- the consistency clause: the root type is the restriction of the context along the projection
  have hcons : typeMap C.proj C.p₀ = some p := by
    have h := hM.consistent C.ctx C.p₀ C.proj C.eval_ctx
    rw [C.proj_ctx, hp, knightTower_pull] at h
    exact h.symm
  have hvC : Finset.univ.image C.proj ∈ C.p₀.scheme.scheme.plan :=
    (typeMap_isSome_iff _ _).mp (by rw [hcons]; rfl)
  have hC' : C.p₀.restrictFace C.proj hvC = p := by
    have h := hcons
    rwa [typeMap_eq_some _ _ hvC, Option.some.injEq] at h
  -- the coface condition: the root type is the restriction of the donor along the initial face
  have hvP : Finset.univ.image Fin.castSuccEmb ∈ q.scheme.scheme.plan := hq.extendsDomain.visible
  have hP' : q.restrictFace Fin.castSuccEmb hvP = p := by
    have h : typeMap Fin.castSuccEmb q = some p := hq
    rwa [typeMap_eq_some _ _ hvP, Option.some.injEq] at h
  have hP : q.scheme.restrictFace Fin.castSuccEmb hvP = p.scheme := congrArg StageType.scheme hP'
  have hC : C.p₀.scheme.restrictFace C.proj hvC = p.scheme := congrArg StageType.scheme hC'
  -- each block is the block of a request
  have hblk : ∀ i : ↥(blocksOf reqs), ∃ r ∈ reqs, r.block = i.1 := fun i =>
    mem_blocksOf.mp i.2
  refine ⟨⟨hvC, hvP, hC, hP⟩, {
    arity_lt := hNmin
    N_le := le_rfl
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
    cap := C.capBase
    cap_cell := C.cap_index
    ref_scope := fun _ => Finset.subset_univ _
    vact := C.p₀.label
    vact_respects := C.p₀.respects
    vact_ref := fun i => by
      obtain ⟨r, hr, hrb⟩ := hblk i
      have h := C.rep_label r hr
      rwa [hrb] at h
    cap_pos := hcap_pos
    margin := fun i => by
      obtain ⟨r, hr, hrb⟩ := hblk i
      have h := hmargin r hr
      rwa [hrb] at h
    p := q.label
    p_respects := q.respects
    p_code := fun d hb ht => by
      rcases ExtOrd.cases (q.label d) with h | h | ⟨β, hβ⟩
      · exact absurd h hb
      · exact absurd h ht
      have hr : (⟨limitPart β, finitePart β⟩ : BlockRequest) ∈ reqs :=
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
      exact commonFace_val_congr Fin.castSuccEmb hvP hP C.proj hvC hC k a _ rfl 
  }, rfl, rfl, rfl, ?_⟩
  intro i
  exact ⟨faceBelow q.scheme p.scheme Fin.castSuccEmb hvP hP i, faceBelow_val _ _ _ _ _ _, by
    rw [commonFace_faceBelow]
    exact faceBelow_val _ _ _ _ _ _⟩

end CappedDonor

end VaughtConjecture.Knight
