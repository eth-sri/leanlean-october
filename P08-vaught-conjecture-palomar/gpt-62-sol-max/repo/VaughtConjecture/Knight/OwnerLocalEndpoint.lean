/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteFloorCompletion
public import VaughtConjecture.Knight.CappedLocalityRecoding
public import VaughtConjecture.Knight.CountedRecoding
public import VaughtConjecture.Knight.FullScopeBountiful
public import VaughtConjecture.Knight.Domain
public import VaughtConjecture.Knight.OnePointSuccessor
public import Mathlib.Tactic.DeriveFintype

public import VaughtConjecture.Knight.RowCorrectness
public import VaughtConjecture.Knight.RowReadback
public import VaughtConjecture.Knight.WitnessSplice
public import VaughtConjecture.Knight.Type
public import VaughtConjecture.Knight.WitnessAlgebra

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

namespace OwnerLocalEndpoint

/-- Rounding to the `j`-visible endpoint of the strip of `x`. -/
noncomputable abbrev endpoint (j : ℕ) (x : ExtOrd) : ExtOrd := extVisibilityReplace x j j

theorem le_endpoint (j : ℕ) (x : ExtOrd) : x ≤ endpoint j x := le_extVisibilityReplace_self x j

theorem selfVis_endpoint (j : ℕ) (x : ExtOrd) : SelfVis j (endpoint j x) := by
  unfold endpoint
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · rfl
  · exact extVisibilityReplace_top j j
  · rw [extVisibilityReplace_ofOrd, selfVis_ofOrd_iff, finitePart_visibilityReplace]
    split_ifs <;> omega

theorem endpoint_of_selfVis {j : ℕ} {x : ExtOrd} (h : SelfVis j x) : endpoint j x = x := h

theorem endpoint_mono {j : ℕ} {x y : ExtOrd} (h : x ≤ y) : endpoint j x ≤ endpoint j y :=
  evr_mono h le_rfl

variable {ι : Type*}

/-- The owner-local saturation hypotheses: `τ` is bottom-preserving, monotone and bounded by the
positive cap `γ`; the owner `c` exceeds the cap under `p`; the face equation holds on every
argument and the owner's source value is `j`-visible. -/
structure Saturation (j : ℕ) (s p : ι → ExtOrd) (c : ι) (τ : ExtOrd → ExtOrd) (γ : ExtOrd) :
    Prop where
  bot : τ ⊥ = ⊥
  mono : Monotone τ
  bound : ∀ x, τ x ≤ γ
  pos : ⊥ < γ
  cap : γ < p c
  face : ∀ d, τ (s d) = min (p d) γ
  owner_vis : SelfVis j (s c)

/-- The endpoint `h` is the least rounded saturated observation. -/
structure IsEndpoint (j : ℕ) (s : ι → ExtOrd) (τ : ExtOrd → ExtOrd) (γ h : ExtOrd) : Prop where
  least : IsLeast {x | ∃ d, τ (s d) = γ ∧ endpoint j (s d) = x} h

theorem IsEndpoint.le_of_saturated {j : ℕ} {s : ι → ExtOrd} {τ : ExtOrd → ExtOrd} {γ h : ExtOrd}
    (H : IsEndpoint j s τ γ h) {d : ι} (hd : τ (s d) = γ) : h ≤ endpoint j (s d) :=
  H.least.2 ⟨d, hd, rfl⟩

theorem IsEndpoint.exists_witness {j : ℕ} {s : ι → ExtOrd} {τ : ExtOrd → ExtOrd} {γ h : ExtOrd}
    (H : IsEndpoint j s τ γ h) : ∃ d, τ (s d) = γ ∧ endpoint j (s d) = h :=
  H.least.1

section Conclusions

variable {j : ℕ} {s p : ι → ExtOrd} {c : ι} {τ : ExtOrd → ExtOrd} {γ h : ExtOrd}

/-- The owner is saturated. -/
theorem Saturation.owner_saturated (S : Saturation j s p c τ γ) : τ (s c) = γ := by
  rw [S.face c, min_eq_right S.cap.le]

/-- Visibility: the endpoint is `j`-visible. -/
theorem IsEndpoint.selfVis (H : IsEndpoint j s τ γ h) : SelfVis j h := by
  obtain ⟨d, -, hd⟩ := H.exists_witness
  rw [← hd]
  apply selfVis_endpoint

/-- Reaching: the endpoint itself is mapped to the cap. -/
theorem IsEndpoint.reach (H : IsEndpoint j s τ γ h) (S : Saturation j s p c τ γ) : τ h = γ := by
  obtain ⟨d, hd, hdh⟩ := H.exists_witness
  refine le_antisymm (S.bound h) ?_
  calc γ = τ (s d) := hd.symm
    _ ≤ τ h := S.mono (hdh ▸ le_endpoint j (s d))

/-- Positivity: a saturated observation is not bottom, so neither is the endpoint. -/
theorem IsEndpoint.bot_lt (H : IsEndpoint j s τ γ h) (S : Saturation j s p c τ γ) : ⊥ < h := by
  refine bot_lt_iff_ne_bot.mpr fun hb ↦ ?_
  have := H.reach S
  rw [hb, S.bot] at this
  exact S.pos.ne this

/-- The owner bound: the endpoint is at most the owner's (visible) source value. -/
theorem IsEndpoint.le_owner (H : IsEndpoint j s τ γ h) (S : Saturation j s p c τ γ) : h ≤ s c :=
  (H.le_of_saturated S.owner_saturated).trans_eq (endpoint_of_selfVis S.owner_vis)

/-- The single-strip conclusion: a saturated observation below the endpoint rounds to it. -/
theorem IsEndpoint.strip (H : IsEndpoint j s τ γ h) {d : ι} (hlt : s d < h) (hd : τ (s d) = γ) :
    endpoint j (s d) = h :=
  le_antisymm ((endpoint_mono hlt.le).trans_eq (endpoint_of_selfVis H.selfVis))
    (H.le_of_saturated hd)

/-- A saturated observation strictly below the endpoint is `j`-invisible. -/
theorem IsEndpoint.not_selfVis_of_lt (H : IsEndpoint j s τ γ h) {d : ι} (hlt : s d < h)
    (hd : τ (s d) = γ) : ¬ SelfVis j (s d) := fun hv ↦
  hlt.ne (((endpoint_of_selfVis hv).symm.trans (H.strip hlt hd)))

end Conclusions

/-- Over a finite family, the least rounded saturated observation exists. -/
theorem exists_isEndpoint [Finite ι] {j : ℕ} {s p : ι → ExtOrd} {c : ι} {τ : ExtOrd → ExtOrd}
    {γ : ExtOrd} (S : Saturation j s p c τ γ) :
    ∃ h, IsEndpoint j s τ γ h := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨d₀, hd₀, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun d ↦ τ (s d) = γ)
    (fun d ↦ endpoint j (s d)) ⟨c, by simp [S.owner_saturated]⟩
  have H : IsEndpoint j s τ γ (endpoint j (s d₀)) :=
    ⟨⟨by grind, by
      rintro x ⟨d, hd, rfl⟩
      grind⟩⟩
  exact ⟨_, H⟩

/-- The map hypotheses of `Saturation` from a normalized witness with suppressor `gTop j`
(the sufficient condition named in notes40 §2). -/
theorem Saturation.of_witness {j : ℕ} {s p : ι → ExtOrd} {c : ι} {τ : ExtOrd → ExtOrd}
    {γ : ExtOrd} (hτ : Witness (gTop j) τ) (bound : ∀ x, τ x ≤ γ) (pos : ⊥ < γ) (cap : γ < p c)
    (face : ∀ d, τ (s d) = min (p d) γ) (owner_vis : SelfVis j (s c)) :
    Saturation j s p c τ γ :=
  ⟨hτ.bot, hτ.mono, bound, pos, cap, face, owner_vis⟩

end OwnerLocalEndpoint

end VaughtConjecture.Knight
