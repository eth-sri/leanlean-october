/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPreactivation
public import VaughtConjecture.Knight.GrowthSupportedRepair

@[expose] public section

namespace VaughtConjecture.Knight.Growth

open Transform Value ExtOrd AmalgamationPlan CanonicalPairedInverse

noncomputable section

variable {n J r : ℕ} {P : SemScheme (n + 1)} {C : SemScheme J}
  {F : SemScheme r} {fP : Fin r ↪ Fin (n + 1)}
  {hvP : Finset.univ.image fP ∈ P.scheme.plan} {hP : P.restrictFace fP hvP = F}
  {fC : Fin r ↪ Fin J} {hvC : Finset.univ.image fC ∈ C.scheme.plan}
  {hC : C.restrictFace fC hvC = F}
  {X : RelativeData C.scheme C.rows P.scheme P.rows}
  (R : RootAttachment F fP hvP hP fC hvC hC X)

namespace RootAttachment

include R

theorem private_fibre {j : ℕ} (hj : 1 ≤ j) : (terminalContext X).Fibre j
    (fun d : C.scheme.below (Finset.univ, j) => .inl d.1)
    (RespectsSemanticsBelow C.rows (Finset.univ, j)) := by
  refine (terminalContext X).fibre_of_patch hj (zero_admitted X j) (fun hs => hs.private_lawful) ?_
  intro s p γ hs hp hγ hag
  by_cases hN : j < X.req.N
  · obtain ⟨t, ht, he, hc⟩ := R.private_before hN hs hp hγ hag
    exact ⟨t, ht, he, fun d => (hc d).symm⟩
  · obtain ⟨t, ht, he, hc, -⟩ := private_repair X (not_lt.mp hN) hs hp hγ hag
    exact ⟨t, ht, he, fun d => (hc d).symm⟩

theorem donor_fibre {j : ℕ} (hj : 1 ≤ j) (hN : j < X.req.N) : (terminalContext X).Fibre j
    (fun d : P.scheme.below (Finset.univ, j) => .inr d.1)
    (RespectsSemanticsBelow P.rows (Finset.univ, j)) := by
  refine (terminalContext X).fibre_of_patch hj (zero_admitted X j) (fun hs => hs.donor_lawful) ?_
  intro s p γ hs hp hγ hag
  obtain ⟨t, ht, he, hc⟩ := R.donor_before hN hs hp hγ hag
  exact ⟨t, ht, he, fun d => (hc d).symm⟩

end RootAttachment

/-- Strict donor arity is an independent geometric input, not a consequence
of the weak `RelativeData.grade_le` bound. -/
theorem donor_grade_lt {m N : ℕ} (D : SemScheme m) (hm : m < N) (d : Cell D.scheme) :
    D.scheme.grade d < N :=
  ((D.scheme.grade_le_card_scope d).trans
    (by simpa [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_univ (D.scheme.scope d))).trans_lt hm

end

end VaughtConjecture.Knight.Growth
