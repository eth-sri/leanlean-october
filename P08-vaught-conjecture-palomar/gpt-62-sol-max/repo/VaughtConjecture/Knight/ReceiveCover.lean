/- Copyright (c) 2026 Cameron Freer. Released under Apache 2.0. -/
module

public import VaughtConjecture.Knight.Model
public import VaughtConjecture.Knight.VisibleFaceOneStep

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType AmalgamationPlan

variable {ι : Type*} [DecidableEq ι] {n : ℕ}

theorem image_snoc_univ (f : Fin n ↪ ι) (x : ι) (hx : x ∉ Set.range f) :
    Finset.univ.image (snoc f x hx) = insert x (Finset.univ.image f) := by
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨i, rfl⟩
    induction i using Fin.lastCases <;> simp_all
  · rintro (hy | ⟨i, rfl⟩)
    · exact ⟨Fin.last n, by simp_all⟩
    · exact ⟨i.castSucc, snoc_apply_castSucc f x hx i⟩

theorem exists_visible_snoc {A : Finset ι} {P : Finset (Finset ι)}
    (hP : Plan.IsPlan A P) (f : Fin n ↪ ι) (hf : Finset.univ.image f ∈ P)
    (hne : Finset.univ.image f ≠ A) :
    ∃ (x : ι) (hx : x ∉ Set.range f), Finset.univ.image (snoc f x hx) ∈ P := by
  obtain ⟨C, hC, hsub, hcard⟩ := hP.exists_visible_card_succ_superface hf hne
  obtain ⟨x, hxC, hxf⟩ := Finset.exists_of_ssubset hsub
  have hx : x ∉ Set.range f := by simpa using hxf
  refine ⟨x, hx, ?_⟩
  rw [image_snoc_univ, Finset.eq_of_subset_of_card_le (Finset.insert_subset hxC hsub.subset) ?_]
  all_goals simp_all

variable {M : Type*} {α : LimitStage} {W : KnightRealization α M}

/-- Iterate a one-point receiving operation along a chain of visible faces.
The donor may be repaired at each step, subject to a transitive relation
with the original donor. The invariant can also track the realized root. -/
theorem receiveCover
    (hcons : W.IsExactParentConsistent)
    {Inv : ∀ {n m : ℕ}, (Fin n ↪ M) → S α.1 m → Prop}
    {Rel : ∀ {m : ℕ}, S α.1 m → S α.1 m → Prop}
    (hrefl : ∀ {m} (Q : S α.1 m), Rel Q Q)
    (htrans : ∀ {m} {Q₁ Q₂ Q₃ : S α.1 m}, Rel Q₁ Q₂ → Rel Q₂ Q₃ → Rel Q₁ Q₃)
    (step : ∀ {n m} (Q : S α.1 m) (g : Fin (n + 1) ↪ Fin m)
      (hg : Finset.univ.image g ∈ Q.scheme.scheme.plan)
      (t : Fin n ↪ M) (p : S α.1 n), W.eval t = some p → Inv t Q →
      IsCoface p (Q.restrictFace g hg) →
      ∃ (u : Fin (n + 1) ↪ M) (Q' : S α.1 m) (p' : S α.1 (n + 1)),
        Fin.castSuccEmb.trans u = t ∧ Inv u Q' ∧ Rel Q' Q ∧
          typeMap g Q' = some p' ∧ W.eval u = some p')
    {n m : ℕ} (Q : S α.1 m) (f : Fin n ↪ Fin m) (t : Fin n ↪ M) (p : S α.1 n)
    (hp : typeMap f Q = some p) (ht : W.eval t = some p) (hInv : Inv t Q) :
    ∃ (u : Fin m ↪ M) (Q' : S α.1 m), f.trans u = t ∧ W.eval u = some Q' ∧ Rel Q' Q := by
  have run (r : ℕ) : ∀ {n m} (Q : S α.1 m) (f : Fin n ↪ Fin m) (t : Fin n ↪ M) (p : S α.1 n),
      n + r = m → typeMap f Q = some p → W.eval t = some p → Inv t Q →
      ∃ (u : Fin m ↪ M) (Q' : S α.1 m), f.trans u = t ∧ W.eval u = some Q' ∧ Rel Q' Q := by
    induction r with
    | zero =>
      intro n m Q f t p he hp ht _
      have hm : m = n := by omega
      subst m
      let e := Equiv.ofBijective f (Finite.injective_iff_bijective.mp f.injective)
      let g := e.symm.toEmbedding
      have hfg : f.trans g = Function.Embedding.refl _ :=
        Function.Embedding.ext fun i => e.symm_apply_apply i
      have hgf : g.trans f = Function.Embedding.refl _ :=
        Function.Embedding.ext fun i => e.apply_symm_apply i
      refine ⟨g.trans t, Q, ?_, ?_, hrefl Q⟩
      · rw [← Function.Embedding.trans_assoc, hfg, Function.Embedding.refl_trans]
      · rw [hcons t p g ht]
        change typeMap g p = some Q
        rw [typeMap_trans g f Q p hp, hgf, typeMap_refl]
    | succ r ih =>
      intro n m Q f t p he hp ht hInv
      have hvis := (typeMap_isSome_iff f Q).mp (by rw [hp]; rfl)
      have hne : Finset.univ.image f ≠ Finset.univ := by
        intro heq
        have hcard := congrArg Finset.card heq
        simp only [Finset.card_image_of_injective _ f.injective, Finset.card_univ, Fintype.card_fin] at hcard
        omega
      obtain ⟨x, hx, hvg⟩ := exists_visible_snoc Q.scheme.scheme.isPlan f hvis hne
      let g := snoc f x hx
      have hcof : IsCoface p (Q.restrictFace g hvg) := by
        unfold IsCoface
        rwa [typeMap_trans _ g Q _ (typeMap_eq_some g Q hvg), castSuccEmb_trans_snoc]
      obtain ⟨u, Q', p', hu, huInv, hRel, hp', hEval⟩ := step Q g hvg t p ht hInv hcof
      obtain ⟨v, Q'', hv, hvEval, hvRel⟩ := ih Q' g u p' (by omega) hp' hEval huInv
      refine ⟨v, Q'', ?_, hvEval, htrans hvRel hRel⟩
      rw [← hu, ← hv, ← Function.Embedding.trans_assoc, castSuccEmb_trans_snoc]
  have hnm := Fintype.card_le_of_embedding f
  simp only [Fintype.card_fin] at hnm
  exact run (m - n) Q f t p (by omega) hp ht hInv

end VaughtConjecture.Knight
