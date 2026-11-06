module

public import proofs.HordijkSteelThreshold.WordCoreAvoidance

public section

namespace HordijkSteelThreshold

variable {A : Type*} (g : List Bool → A)

/-- Sliding one letter through a fixed-length word makes its label independent of the word. -/
theorem fixedLength_shift_constant  (M : ℕ)
    (hshift : ∀ (a b : Bool) (t : List Bool), t.length + 1 = M →
      g (a :: t) = g (t ++ [b]))
    (u v : List Bool) (hu : u.length = M) (hv : v.length = M) : g u = g v := by
  have rotate : ∀ front : List Bool, ∀ middle suffix : List Bool,
      front.length = suffix.length → front.length + middle.length = M →
      g (front ++ middle) = g (middle ++ suffix) := by
    intro front
    induction front with
    | nil =>
      grind
    | cons a front ih =>
      intro middle suffix hs ht
      cases suffix with
      | nil => simp_all
      | cons b suffix =>
        have h1 := hshift a b (front ++ middle) $ by
          simp at *
          omega
        grind
  simpa using rotate u [] v (hu.trans hv.symm) $ by omega

/-- If both parent moves above M preserve labels, all words from M through N share a label.
The spare level M+1 is essential. -/
theorem highBand_label_constant  (M N : ℕ)
    (hMN : M < N)
    (hparent : ∀ s : List Bool, M < s.length → s.length ≤ N →
      g s = g s.tail ∧ g s = g s.dropLast)
    (u v : List Bool) (hu : M ≤ u.length ∧ u.length ≤ N)
    (hv : M ≤ v.length ∧ v.length ≤ N) : g u = g v := by
  have hshift : ∀ (a b : Bool) t, t.length + 1 = M →
      g (a :: t) = g (t ++ [b]) := by
    intro a b t ht
    have h := hparent ((a :: t) ++ [b]) (by simp_all) $ by simp_all
    grind
  let base := List.replicate M false
  have descend : ∀ n : ℕ, ∀ s : List Bool, s.length = n → M ≤ n → n ≤ N → g s = g base := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hs hlo hhi
      by_cases he : n = M
      · exact fixedLength_shift_constant g M hshift s base (hs.trans he) $ by grind
      grind
  simp_all

end HordijkSteelThreshold
