/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.LowOnlyResidualReceivingCore

/-! # Exact finite-cover receiving in the residual branch

Walk the donor's saturated visible-face chain using exact one-point receiving.
Unlike finite-cut receiving, every intermediate root stays exact, so the donor
needs no repair and the conclusion is literal equality of stage types.
-/

namespace VaughtConjecture.Knight.LowOnlyResidualReceiving
section
universe w
variable {M : Type w} {α : LimitStage} {W : KnightRealization α M}
  (hcons : W.IsExactParentConsistent) (hFC : FiniteCutReceiving W) {K : ℕ}
  (hcoin : KnightRealization.IsCoinitial {x : W.LabelledExt | x.type.topGrade = K}) (hKpos : 0 < K)
  (hres : ∀ {k} (B : Fin k ↪ M), ¬ TopSupportRigidCore.RigidCore W B)

include hcons hFC hcoin hKpos hres

/-- Exact receiving along a specified finite number of one-point face steps. -/
theorem receive_cover_steps_of_tail r :
    ∀ {n m} Q,
      (∀ d, Q.label d = ⊤ → Q.scheme.scheme.grade d ≤ K) →
      ∀ (f : Fin n ↪ Fin m), n + r = m →
      ∀ (t : Fin n ↪ M) (p : S α.1 n), typeMap f Q = some p → W.eval t = some p →
        ∃ u : Fin m ↪ M, f.trans u = t ∧ W.eval u = some Q := by
  induction r with
  | zero =>
    intro n m Q _ f hcard t p hp ht
    subst hcard
    have hbij  := Finite.injective_iff_bijective.mp f.injective
    let e  := Equiv.ofBijective f hbij
    let g  := e.symm.toEmbedding
    
    have hgf : g.trans f = Function.Embedding.refl _ :=
      Function.Embedding.ext fun i => e.apply_symm_apply i
    refine ⟨g.trans t, ?_, ?_⟩
    · aesop
    · rw [hcons t p g ht]
      change typeMap g p = some Q
      rw [typeMap_trans hp, hgf, typeMap_refl]
  | succ r ih =>
    intro n m Q hQK f hcard t p hp ht
    have hvis  :=
      (typeMap_isSome_iff).mp (by rw [hp]; rfl)
    have hcardF : (Finset.univ.image f).card = n := by
      rw [Finset.card_image_of_injective _ f.injective, Finset.card_univ, Fintype.card_fin]
    have hne : Finset.univ.image f ≠ (Finset.univ : FiniteScope m) := by
      intro heq
      rw [heq, Finset.card_univ, Fintype.card_fin] at hcardF
      omega
    obtain ⟨C, hC, hsub, hcardC⟩ :=
      Q.scheme.scheme.isPlan.exists_visible_card_succ_superface hvis hne
    obtain ⟨c, hcC, hcF⟩ := Finset.exists_of_ssubset hsub
    have hcf : c ∉ Set.range f := by
      grind
    have himage : Finset.univ.image (snoc f c hcf) = C := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
        induction i using Fin.lastCases with
        | last => rw [snoc_apply_last]; exact hcC
        | cast j => rw [snoc_apply_castSucc]; exact hsub.subset (Finset.mem_image_of_mem _
            (Finset.mem_univ j))
      · rw [hcardC, hcardF, Finset.card_image_of_injective _ (snoc f c hcf).injective,
          Finset.card_univ, Fintype.card_fin]
    let g  := snoc f c hcf
    have hvg  := himage ▸ hC
    let p'  := Q.restrictFace g hvg
    have hp'  := typeMap_eq_some g Q hvg
    have hcof : IsCoface p p' := by
      change typeMap Fin.castSuccEmb p' = some p
      rw [typeMap_trans hp',
        show Fin.castSuccEmb.trans g = f from castSuccEmb_trans_snoc hcf]
      exact hp
    have hp'K : ∀ d, p'.label d = ⊤ → p'.scheme.scheme.grade d ≤ K := by
      exact?
    obtain ⟨y, hy, hq⟩ := receive_of_tail hcons hFC hcoin hKpos hres t p ht p' hcof hp'K
    obtain ⟨u, hgu, hu⟩ := ih Q hQK g (by omega) (snoc t y hy) p' hp' hq
    refine ⟨u, ?_, hu⟩
    have hf  := (castSuccEmb_trans_snoc hcf).symm
    rw [hf, Function.Embedding.trans_assoc, hgu, castSuccEmb_trans_snoc]

/-- Every finite legal donor with top grades bounded by the characteristic is
received exactly over any literal realized face. -/
theorem receive_cover_of_tail {n m : ℕ} (Q : S α.1 m)
    (hQK : ∀ d, Q.label d = ⊤ → Q.scheme.scheme.grade d ≤ K)
    (f : Fin n ↪ Fin m) (t : Fin n ↪ M) (p : S α.1 n)
    (hp : typeMap f Q = some p) (ht : W.eval t = some p) :
    ∃ u : Fin m ↪ M, f.trans u = t ∧ W.eval u = some Q := by
  have hnm  := by
    have := Fintype.card_le_of_embedding f
    simpa only [Fintype.card_fin] using this
  exact receive_cover_steps_of_tail hcons hFC hcoin hKpos hres (m - n) Q hQK f (by omega) t p hp ht

