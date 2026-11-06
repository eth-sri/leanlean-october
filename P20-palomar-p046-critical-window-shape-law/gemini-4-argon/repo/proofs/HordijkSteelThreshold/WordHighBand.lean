module

public import proofs.HordijkSteelThreshold.WordCoreAvoidance

@[expose] public section

namespace HordijkSteelThreshold

theorem highBand_label_constant {A : Type*} (g : List Bool → A) (M N : ℕ)
    (hMN : M < N)
    (hparent : ∀ s : List Bool, M < s.length → s.length ≤ N →
      g s = g s.tail ∧ g s = g s.dropLast)
    (u v : List Bool) (hu : M ≤ u.length ∧ u.length ≤ N)
    (hv : M ≤ v.length ∧ v.length ≤ N) : g u = g v := by
  have rotate (front : List Bool) : ∀ middle suffix : List Bool,
      front.length = suffix.length → front.length + middle.length = M →
      g (front ++ middle) = g (middle ++ suffix) := by
    induction front with
    | nil => intro _ suffix hs _; cases suffix <;> simp_all
    | cons a front ih =>
      intro middle suffix hs ht
      rcases suffix with _ | ⟨b, suffix⟩; · simp at hs
      have h := hparent ((a :: (front ++ middle)) ++ [b]) (by simp at ht ⊢; omega) (by simp at ht ⊢; omega)
      simp only [List.dropLast_concat] at h
      have h1 : g (a :: (front ++ middle)) = g ((front ++ middle) ++ [b]) :=
        by simpa only [List.cons_append, List.tail_cons] using h.2.symm.trans h.1
      have h2 := ih (middle ++ [b]) suffix (by simpa using hs) (by simp at ht ⊢; omega)
      rw [List.append_assoc] at h1
      simpa only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using h1.trans h2
  let base := List.replicate M false
  have descend (n : ℕ) : ∀ s : List Bool, s.length = n → M ≤ n → n ≤ N → g s = g base := by
    induction n using Nat.strong_induction_on with | h n ih =>
    intro s hs hlo hhi
    by_cases he : n = M
    · simpa using rotate s [] base (by simp [base, hs, he]) (by simpa [he] using hs)
    · exact (hparent s (by omega) (by omega)).2.trans
        (ih _ (by simp; omega) s.dropLast rfl (by simp; omega) (by simp; omega))
  exact (descend _ u rfl hu.1 hu.2).trans (descend _ v rfl hv.1 hv.2).symm

end HordijkSteelThreshold
