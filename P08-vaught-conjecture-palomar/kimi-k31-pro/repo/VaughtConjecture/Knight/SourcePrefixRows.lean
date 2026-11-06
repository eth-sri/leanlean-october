/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SharpWitnessComposition

/-! # Common-grid rows with all lower-controller occurrences retained

The row-layer step of the coupled source-prefix construction. A finite grid
and boundary profiles determine every same-grade cross-reading. Previously
constructed lower sections are used once, as whole sections. Their grid
agreement is the grade-induction hypothesis, not assumed future locality.

This module constructs the new/new faithful incidences and full-index
availability. It does not claim the lower-section induction, geometric
installation, bountifulness, or maximal coatom supply.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.SourcePrefixRows

open Transform Value ExtOrd

variable {X Y Q : Type*}

def Agree (a b : X → ExtOrd) (h : ExtOrd) : Prop :=
  ∀ x, min (a x) h = min (b x) h

theorem Agree.mono {a b : X → ExtOrd} {h c : ExtOrd}
    (hab : Agree a b h) (hc : c ≤ h) : Agree a b c := by
  intro x
  have hh := congrArg (fun z => min z c) (hab x)
  simpa only [min_assoc, min_eq_right hc] using hh

/-- Lift a scalar decoder comparison to all occurrences of two sections.
The comparison is needed only at actual common source values strictly below
their agreement cut. Values at or above the cut are handled by monotonicity.
This consumes, but does not assert existence of, the right-filled decoder
comparison required by the coupled construction. -/
theorem Agree.decode {a b : X → ExtOrd} {s h : ExtOrd} {ν μ : ExtOrd → ExtOrd}
    (hab : Agree a b s) (hν : Monotone ν) (hμ : Monotone μ)
    (hsν : h ≤ ν s) (hsμ : h ≤ μ s)
    (hcompare : ∀ d, a d < s → min (ν (a d)) h = min (μ (a d)) h) :
    Agree (fun d => ν (a d)) (fun d => μ (b d)) h := by
  intro d
  change min (ν (a d)) h = min (μ (b d)) h
  by_cases hd : a d < s
  · have hb : b d < s := by
      by_contra hn
      have he := hab d
      rw [min_eq_left hd.le, min_eq_right (le_of_not_gt hn)] at he
      exact (ne_of_lt hd) he
    have he := hab d
    rw [min_eq_left hd.le, min_eq_left hb.le] at he
    rw [← he]
    exact hcompare d hd
  · have ha : s ≤ a d := le_of_not_gt hd
    have hb : s ≤ b d := by
      have he := hab d
      rw [min_eq_right ha] at he
      exact he.trans_le (min_le_left _ _)
    rw [min_eq_right (hsν.trans (hν ha)), min_eq_right (hsμ.trans (hμ hb))]

open Classical in
noncomputable def cut (G : Finset ExtOrd) (a b : X → ExtOrd) : ExtOrd :=
  (G.filter (Agree a b)).sup id

theorem cut_le {G : Finset ExtOrd} {H : ExtOrd}
    (hG : ∀ h ∈ G, h ≤ H) (a b : X → ExtOrd) : cut G a b ≤ H := by
  classical
  apply Finset.sup_le
  intro h hh
  exact hG h (Finset.mem_filter.mp hh).1

theorem le_cut {G : Finset ExtOrd} {a b : X → ExtOrd} {h : ExtOrd}
    (hh : h ∈ G) (ha : Agree a b h) : h ≤ cut G a b := by
  classical
  exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨hh, ha⟩)

theorem cut_mem {G : Finset ExtOrd} (hbot : ⊥ ∈ G) (a b : X → ExtOrd) :
    cut G a b ∈ G := by
  classical
  have hn : (G.filter (Agree a b)).Nonempty :=
    ⟨⊥, Finset.mem_filter.mpr ⟨hbot, fun _ => by simp⟩⟩
  obtain ⟨h, hh, he⟩ := Finset.sup_mem_of_nonempty (f := id) hn
  change h = cut G a b at he
  exact he ▸ (Finset.mem_filter.mp hh).1

theorem agree_cut {G : Finset ExtOrd} (hbot : ⊥ ∈ G) (a b : X → ExtOrd) :
    Agree a b (cut G a b) := by
  classical
  have hn : (G.filter (Agree a b)).Nonempty :=
    ⟨⊥, Finset.mem_filter.mpr ⟨hbot, fun _ => by simp⟩⟩
  obtain ⟨h, hh, he⟩ := Finset.sup_mem_of_nonempty (f := id) hn
  change h = cut G a b at he
  exact he ▸ (Finset.mem_filter.mp hh).2

theorem cut_symm {G : Finset ExtOrd} (hbot : ⊥ ∈ G) (a b : X → ExtOrd) :
    cut G a b = cut G b a := by
  apply le_antisymm
  · exact le_cut (cut_mem hbot a b) (fun x => (agree_cut hbot a b x).symm)
  · exact le_cut (cut_mem hbot b a) (fun x => (agree_cut hbot b a x).symm)

theorem cut_refl {G : Finset ExtOrd} {H : ExtOrd}
    (hH : H ∈ G) (hG : ∀ h ∈ G, h ≤ H) (a : X → ExtOrd) :
    cut G a a = H :=
  le_antisymm (cut_le hG a a) (le_cut hH (fun _ => rfl))

theorem cut_triangle {G : Finset ExtOrd} (hbot : ⊥ ∈ G) (a b c : X → ExtOrd) :
    min (cut G a b) (cut G b c) ≤ cut G a c := by
  have hm : min (cut G a b) (cut G b c) ∈ G := by
    rcases le_total (cut G a b) (cut G b c) with h | h
    · simpa only [min_eq_left h] using cut_mem hbot a b
    · simpa only [min_eq_right h] using cut_mem hbot b c
  apply le_cut hm
  intro x
  exact ((agree_cut hbot a b).mono (min_le_left _ _) x).trans
    ((agree_cut hbot b c).mono (min_le_right _ _) x)

theorem cross_agreement {G : Finset ExtOrd} (hbot : ⊥ ∈ G) (a b c : X → ExtOrd) :
    min (cut G a c) (cut G a b) = min (cut G b c) (cut G a b) := by grind [cut_symm, cut_triangle]

/-- Proper cells, existing full lower controllers, and the new controllers
remain distinct occurrences. -/
abbrev Occ (X Y Q : Type*) := (X ⊕ Y) ⊕ Q



/-! ## Boundary-orbit support and hidden prefixes

The support predicate records actual boundary occurrences, not merely a set
of numerical blocks. The lower section's support is an induction hypothesis;
the support of every new-controller reading follows from the row formula.
-/

