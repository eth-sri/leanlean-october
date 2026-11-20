/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SharpWitnessComposition

@[expose] public section

namespace VaughtConjecture.Knight.SourcePrefixRows

open Transform Value ExtOrd

variable {X V : Type*} [LinearOrder V]

def Agree (a b : X → V) (h : V) : Prop :=
  ∀ x, min (a x) h = min (b x) h

theorem Agree.mono {a b : X → V} {h c : V}
    (hab : Agree a b h) (hc : c ≤ h) : Agree a b c := by grind +locals

section

variable [OrderBot V]

open Classical in
noncomputable def cut (G : Finset V) (a b : X → V) : V :=
  (G.filter (Agree a b)).sup id

theorem cut_le {G : Finset V} {H : V}
    (hG : ∀ h ∈ G, h ≤ H) (a b : X → V) : cut G a b ≤ H := by
  classical
  apply Finset.sup_le
  simp_all

theorem le_cut {G : Finset V} {a b : X → V} {h : V}
    (hh : h ∈ G) (ha : Agree a b h) : h ≤ cut G a b := by
  classical
  exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨hh, ha⟩)

theorem cut_spec {G : Finset V} (hbot : ⊥ ∈ G) (a b : X → V) :
    cut G a b ∈ G ∧ Agree a b (cut G a b) := by
  classical
  obtain ⟨k, hk, he⟩ := Finset.sup_mem_of_nonempty (f := id)
    (show (G.filter (Agree a b)).Nonempty from ⟨⊥, by simp [Agree, hbot]⟩)
  unfold cut
  rw [← he]
  exact Finset.mem_filter.mp hk

theorem cut_mem {G : Finset V} (hbot : ⊥ ∈ G) (a b : X → V) : cut G a b ∈ G :=
  (cut_spec hbot a b).1

theorem agree_cut {G : Finset V} (hbot : ⊥ ∈ G) (a b : X → V) :
    Agree a b (cut G a b) := (cut_spec hbot a b).2

theorem cut_symm {G : Finset V} (hbot : ⊥ ∈ G) (a b : X → V) :
    cut G a b = cut G b a := by
  apply le_antisymm
  · exact le_cut (cut_mem hbot a b) (fun x => (agree_cut hbot a b x).symm)
  · exact le_cut (cut_mem hbot b a) (fun x => (agree_cut hbot b a x).symm)

theorem cut_refl {G : Finset V} {H : V}
    (hH : H ∈ G) (hG : ∀ h ∈ G, h ≤ H) (a : X → V) :
    cut G a a = H :=
  le_antisymm (cut_le hG a a) (le_cut hH (fun _ => rfl))

theorem cut_triangle {G : Finset V} (hbot : ⊥ ∈ G) (a b c : X → V) :
    min (cut G a b) (cut G b c) ≤ cut G a c := by
  have hm : min (cut G a b) (cut G b c) ∈ G := by
    grind [cut_mem]
  apply le_cut hm
  intro x
  exact ((agree_cut hbot a b).mono (min_le_left _ _) x).trans
    ((agree_cut hbot b c).mono (min_le_right _ _) x)

theorem cross_agreement {G : Finset V} (hbot : ⊥ ∈ G) (a b c : X → V) :
    min (cut G a c) (cut G a b) = min (cut G b c) (cut G a b) := by grind [cut_triangle, cut_symm]

end

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
  · grind +locals
  · have ha : s ≤ a d := le_of_not_gt hd
    have hb : s ≤ b d := by
      have he := hab d
      simp_all
    rw [min_eq_right (hsν.trans (hν ha)), min_eq_right (hsμ.trans (hμ hb))]

end VaughtConjecture.Knight.SourcePrefixRows

namespace VaughtConjecture.Knight.SourcePrefixLayer

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}

abbrev Controller (D : CellScheme A) (k : ℕ) := {c : Cell D // D.cell c = (A, k)}

end VaughtConjecture.Knight.SourcePrefixLayer
