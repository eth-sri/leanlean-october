module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.ClusterTrees

/-!
# WP-I, part 24: the star map in arrays

* `star_dual_enc`: arrays of length `3N` with the uniform formulas of the star map (opposite
  darts, the face permutation as rotation, faces as tails; `first f = f`) encode the dual of the
  star map (`EnvEnc`), given arrays of `opp`, `fperm` and `fperm⁻¹` of `M`;
* `starTree_isTreeDart_inl/inl_inr/inr_inr`: the tree darts of `starTree T a` are the tree darts
  of `T` and the two spokes of each `a g`;
* `att_fun`: a representative array `att` (a dart of the face of every dart, constant along
  faces) defines the attachment `a : F → D`.
-/

namespace Chazelle.Core.Cluster

open Chazelle.Separator Chazelle.Separator.CombMap Equiv

@[expose] public section

variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] {M : CombMap (Fin μ) F (Fin N)}

omit [Fintype F] [DecidableEq F] in
/-- **The star arrays encode the dual of the star map.** -/
theorem star_dual_enc {opp fp fpi : ℕ → ℕ} (hopp : ∀ d : Fin N, opp d = M.opp d)
    (hfp : ∀ d : Fin N, fp d = M.fperm d) (hfpi : ∀ d : Fin N, fpi d = (M.fperm⁻¹ d : Fin N))
    {G : Env} (hGN : G.N = 3 * N) (hGnv : G.nv = N)
    (hSO : ∀ d, d < N → G.opp d = opp d ∧ G.opp (N + d) = 2 * N + d ∧ G.opp (2 * N + d) = N + d)
    (hSR : ∀ d, d < N → G.rot d = 2 * N + fp d ∧ G.rot (N + d) = d ∧
      G.rot (2 * N + d) = N + fpi d)
    (hSF : ∀ d, d < N → G.vert d = d ∧ G.vert (N + d) = d ∧ G.vert (2 * N + d) = fpi d)
    (hSFi : ∀ d, d < N → G.first d = d) :
    EnvEnc G (star M).dual (fun g => (g : ℕ)) (enc N) := by
  refine ⟨fun v => by rw [hGnv]; exact v.2, fun v w h => Fin.ext h, fun u hu => ⟨⟨u, ⋄⟩, rfl⟩,
    fun x => by rw [hGN]; exact enc_lt x, fun x y h => enc_inj h, fun e he => ?_,
    fun x => ?_, fun x => ?_, fun x => ?_, fun v => ⟨.inl v, by rw [hSFi v v.2]; rfl, rfl⟩⟩
  · Ξ' hGN at he
    by_cases h1 : e < N
    · exact ⟨.inl ⟨e, h1⟩, rfl⟩
    · by_cases h2 : e < 2 * N
      · exact ⟨.inr (.inl ⟨e - N, ⋄⟩), by simp only [enc]; omega⟩
      · exact ⟨.inr (.inr ⟨e - 2 * N, ⋄⟩), by simp only [enc]; omega⟩
  · rcases x with d | d | d
    · show G.opp d = enc N (starOpp M (.inl d))
      rw [(hSO d d.2).1, hopp]; rfl
    · show G.opp (N + d) = enc N (starOpp M (.inr (.inl d)))
      rw [(hSO d d.2).2.1]; rfl
    · show G.opp (2 * N + d) = enc N (starOpp M (.inr (.inr d)))
      rw [(hSO d d.2).2.2]; rfl
  · rcases x with d | d | d
    · show G.rot d = enc N ((star M).fperm (.inl d))
      rw [(hSR d d.2).1, star_fperm_inl, hfp]; rfl
    · show G.rot (N + d) = enc N ((star M).fperm (.inr (.inl d)))
      rw [(hSR d d.2).2.1, star_fperm_inl_inr]; rfl
    · show G.rot (2 * N + d) = enc N ((star M).fperm (.inr (.inr d)))
      rw [(hSR d d.2).2.2, star_fperm_inr_inr, hfpi]; rfl
  · rcases x with d | d | d
    · show G.vert d = ((starFace M (.inl d) : Fin N) : ℕ)
      rw [(hSF d d.2).1]; rfl
    · show G.vert (N + d) = ((starFace M (.inr (.inl d)) : Fin N) : ℕ)
      rw [(hSF d d.2).2.1]; rfl
    · show G.vert (2 * N + d) = ((starFace M (.inr (.inr d)) : Fin N) : ℕ)
      rw [(hSF d d.2).2.2, hfpi]; rfl

variable {T : SpanTree M} {a : F → Fin N} {ha : ∀ g, M.face (a g) = g}

omit [Fintype F] [DecidableEq F] in
theorem starTree_isTreeDart_inl (d : Fin N) :
    (starTree T a ha).IsTreeDart (.inl d) ↔ T.IsTreeDart d := by
  constructor
  · rintro ⟨y, hy, h⟩
    rcases y with v | g
    · have hv : v ≠ T.root := fun h' => hy (by rw [h']; rfl)
      refine ⟨v, hv, ?_⟩
      rcases h with h | h
      · left; exact Sum.inl_injective h
      · right; exact Sum.inl_injective h
    · rcases h with h | h <;> cases h
  · rintro ⟨v, hv, h⟩
    refine ⟨.inl v, fun h' => hv (Sum.inl_injective h'), ?_⟩
    rcases h with rfl | rfl
    · left; rfl
    · right; rfl

omit [Fintype F] [DecidableEq F] in
theorem starTree_isTreeDart_inl_inr (d : Fin N) :
    (starTree T a ha).IsTreeDart (.inr (.inl d)) ↔ d = a (M.face d) := by
  constructor
  · rintro ⟨y, hy, h⟩
    rcases y with v | g
    · rcases h with h | h <;> cases h
    · rcases h with h | h
      · have : d = a g := by
          have := congrArg (fun x : Fin N ⊕ Fin N ⊕ Fin N => match x with
            | .inr (.inl e) => e | _ => d) h
          simpa [starTree] using this
        rw [this, ha]
      · cases h
  · intro h
    refine ⟨.inr (M.face d), by simp [starTree], Or.inl ?_⟩
    show Sum.inr (Sum.inl d) = Sum.inr (Sum.inl (a (M.face d)))
    rw [← h]

omit [Fintype F] [DecidableEq F] in
theorem starTree_isTreeDart_inr_inr (d : Fin N) :
    (starTree T a ha).IsTreeDart (.inr (.inr d)) ↔ d = a (M.face d) := by
  constructor
  · rintro ⟨y, hy, h⟩
    rcases y with v | g
    · rcases h with h | h <;> cases h
    · rcases h with h | h
      · cases h
      · have : d = a g := by
          have := congrArg (fun x : Fin N ⊕ Fin N ⊕ Fin N => match x with
            | .inr (.inr e) => e | _ => d) h
          simpa [starTree] using this
        rw [this, ha]
  · intro h
    refine ⟨.inr (M.face d), by simp [starTree], Or.inr ?_⟩
    show Sum.inr (Sum.inr d) = starOpp M (Sum.inr (Sum.inl (a (M.face d))))
    rw [← h]; rfl

omit [Fintype F] [DecidableEq F] in
/-- **The attachment from a representative array.** -/
theorem att_fun {att : ℕ → ℕ} (hlt : ∀ d : Fin N, att d < N)
    (hface : ∀ d : Fin N, ∀ h : att d < N, M.face ⟨att d, h⟩ = M.face d)
    (hconst : ∀ d e : Fin N, M.face d = M.face e → att d = att e) :
    ∃ (a : F → Fin N) (_ha : ∀ g, M.face (a g) = g), ∀ d : Fin N, (a (M.face d) : ℕ) = att d := by
  classical
  let rep := fun g => Classical.choose (M.face_surj g)
  have hrep := fun g => Classical.choose_spec (M.face_surj g)
  refine ⟨fun g => ⟨att (rep g), hlt _⟩, fun g => ?_, fun d => ?_⟩
  · Ξ hface (rep g) (hlt _), hrep
  · show att (rep (M.face d)) = att d
    exact hconst _ _ (hrep _)

end

end Chazelle.Core.Cluster
