import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.ProvisionalLocality
import VaughtConjecture.Knight.Reduction

/-! # Proposition 5.3.3: the provisional labelling respects the semantics

`p⁺ = p.someProvisionalValue` (Def. 5.3.1) respects the unchanged semantics of `p`
(`provisionalLift_respects`): orderliness (Lemma 5.3.4 — in the band case, consistency of the
coded row makes its finite part the band index), locality (Lemma 5.3.5 — at a finite-labelled
controller the target is the original one; at a top-labelled controller
`topController_locality_provisional`), availability (Lemma 5.3.6 — the row's availability at a
maximal top witness, transported by the monotone label witness and the band map).  The lift
`p.provisionalLift : S (α + ω) n` is then a genuine stage type reducing literally to `p`
(`reduceType_provisionalLift`).

## The two roles of `M⁺`

The paper's notation `M⁺` conflates a deterministic type-lifting operation with a separate
occurrence-production theorem; the formalization proves the former outright and isolates the
latter.

* **Local transport.**  `p ↦ p⁺` is a canonical, model-free operation on stage types: it
  preserves semantic legality (this module) and reduces literally to `p`.  It is generic label
  arithmetic plus restricted transform composition (`RestrictedComposition`,
  `ProvisionalBandBridge`, `ProvisionalLocality`).
* **Production.**  A model of `S^{α+ω}` must additionally *realize* compatible lifted one-point
  types over every tuple — in particular stable-top / exact-band occurrences supplying the new
  block's uniformity and high-grade demands (Lemma 5.3.10's per-tuple high-grade argument).
  `M⁺` does not manufacture source points: the production half selects suitable already-existing
  source occurrences and installs their canonical lifts.  This is the separate model-level
  premise `OnePointStableTopSupply`, not part of Proposition 5.3.3. -/

namespace VaughtConjecture.Knight

open  Value ExtOrd

namespace StageType

variable {α : Ordinal₀} {n : ℕ}

local notation "S₀" => S α n

/-- Every provisional value lies strictly below the end of the next `ω`-block. -/
theorem someProvisionalValue_lt_add_omega (p : S₀) Xi :
    p.someProvisionalValue Xi < ofOrd (α + Ordinal.omega0) := by
  refine (p.someProvisionalValue_le Xi).trans_lt (ofOrd_lt_ofOrd.mpr ?_)
  exact (add_lt_add_iff_left α).mpr (Ordinal.natCast_lt_omega0 p.topGrade)

/-- The provisional value of an `∞`-cell is at least `α`. -/
theorem le_someProvisionalValue_of_top {p : S₀} {Xi}
    (htop : p.label Xi = ⊤) : ofOrd α ≤ p.someProvisionalValue Xi := by
  by_cases hcap : p.ProvisionalCap Xi
  · simp_all [someProvisionalValue_of_cap]
  · obtain ⟨i, -, -, hval⟩ := someProvisionalValue_of_band htop hcap
    rw [hval]
    exact ofOrd_le_ofOrd.mpr (le_add_of_nonneg_right zero_le)

/-- The label dominates nothing above the provisional value: `p(Ξ) ≤ p⁺(Ξ)` fails only
through `⊤`, so a finite value below `p(Ξ)` is below `p⁺(Ξ)`. -/
theorem le_someProvisionalValue_of_le_label {p : S₀} {Xi}
    {x} (hx : x < ofOrd α) (h : x ≤ p.label Xi) : x ≤ p.someProvisionalValue Xi := by
  by_cases htop : p.label Xi = ⊤
  · grind [le_someProvisionalValue_of_top]
  · rwa [someProvisionalValue_of_ne_top htop]

/-- **Lemma 5.3.4 (orderliness of `p⁺`)**: in the band case, consistency of the coded row makes
its finite part the selected band index. -/
theorem someProvisionalValue_orderly (p : S₀) (hα : Order.IsSuccLimit α) :
    Transform.IsOrderly p.scheme.scheme.grade p.someProvisionalValue := by
  intro Xi
  by_cases htop : p.label Xi = ⊤
  · have hgrade : p.scheme.scheme.grade Xi ≤ p.topGrade := grade_le_topGrade_of_top htop
    by_cases hcap : p.ProvisionalCap Xi
    · rw [someProvisionalValue_of_cap htop hcap, ]
      apply congrArg ofOrd
      symm
      apply (visibilityReplace_self_iff).mpr
      rwa [finitePart_succLimit_add_nat hα]
    · obtain ⟨i, hband, hi, hval⟩ := someProvisionalValue_of_band htop hcap
      obtain ⟨Theta, hXi, hscope, htopGrade, hThetaTop, heq⟩ := hband
      let row := p.scheme.rows.E Theta ⟨Xi, hXi⟩
      have hrowOrder : row = extVisibilityReplace row
          (p.scheme.scheme.grade Xi) (p.scheme.scheme.grade Xi) :=
        p.scheme.rows.orderly Theta ⟨Xi, hXi⟩
      have hrowCoded := p.scheme.rows_coded Theta ⟨Xi, hXi⟩
      rcases hrowCoded with hbot | ⟨a, j, hj, hrow⟩
      · have hne := row_ne_bot_of_label_top p hThetaTop ⟨Xi, hXi⟩ htop
        exact absurd hbot hne
      · have hself : visibilityReplace (Ordinal.omega0 * a + j)
            (p.scheme.scheme.grade Xi) (p.scheme.scheme.grade Xi) =
            Ordinal.omega0 * a + j := by
          have hrow' : row = ofOrd (Ordinal.omega0 * a + j) := hrow
          rw [hrow', extVisibilityReplace_ofOrd, ofOrd_inj] at hrowOrder
          exact hrowOrder.symm
        have hgradeFp  :=
          (visibilityReplace_self_iff).mp hself
        have hfpTop : finitePart (Ordinal.omega0 * a + j) < p.topGrade := by
          by_contra hge
          apply hcap
          refine ⟨Theta, hXi, ⟨Xi, hXi⟩, hscope, htopGrade, hThetaTop, htop, ?_⟩
          rw [hrow, ]
          exact le_of_eq (congrArg ofOrd
            ((visibilityReplace_self_iff).mpr (not_lt.mp hge)))
        have hrowBand  := by
          rw [hrow, extVisibilityReplace_ofOrd, visibilityReplace_of_finitePart_lt hfpTop,
            ofOrd_inj] at heq
          exact heq
        have hfpEq  := by
          calc
            finitePart (Ordinal.omega0 * a + j) =
                finitePart (limitPart (Ordinal.omega0 * a + j) + i) :=
              congrArg finitePart hrowBand
            _ = i := finitePart_limitPart_add_nat _ _
        rw [hval, ]
        apply congrArg ofOrd
        symm
        apply (visibilityReplace_self_iff).mpr
        rwa [finitePart_succLimit_add_nat hα, ← hfpEq]
  · rw [someProvisionalValue_of_ne_top htop]
    exact p.respects.orderly Xi

/-- Below a maximal top witness `Θ` the labels are a monotone function of the row `E(Θ)`
(the locality witness of the labels has `g = ⊤` up to `K^p`). -/
theorem exists_monotone_label_of_row (p : S₀) {Θ}
    (hgr : p.scheme.scheme.grade Θ = p.topGrade) (hΘ : p.label Θ = ⊤) :
    ∃ σ , Monotone σ ∧
      ∀ d ,
        p.label d.1 = σ (p.scheme.rows.E Θ d) := by
  obtain ⟨g, σ, hganti, _, _, hσmono, _, heq⟩ := p.respects.locality Θ
  have heq' : ∀ d ,
      p.label d.1 = min (σ (p.scheme.rows.E Θ d)) (g (p.scheme.scheme.grade d.1)) := by
    grind
  have hgK : ∀ k, k ≤ p.topGrade → g k = ⊤ := by
    intro k hk
    have hΘ' := heq' ⟨Θ, GradedLe.refl _⟩
    change p.label Θ = min (σ (p.scheme.rows.E Θ ⟨Θ, GradedLe.refl _⟩))
      (g (p.scheme.scheme.grade Θ)) at hΘ'
    rw [hΘ, hgr] at hΘ'
    have hgKtop : g p.topGrade = ⊤ := top_le_iff.mp (hΘ'.le.trans (min_le_right _ _))
    rcases hk.lt_or_eq with hlt | rfl
    · grind
    · exact hgKtop
  refine ⟨σ, hσmono, fun d => ?_⟩
  have hk  := by
    have h2 : p.scheme.scheme.grade d.1 ≤ p.scheme.scheme.grade Θ := d.2.2
    rwa [hgr] at h2
  rw [heq' d, hgK _ hk, min_top_right]

/-- **Lemma 5.3.5 (locality of `p⁺`)** at every controller. -/
theorem provisional_locality (p : S₀) (hα : Order.IsSuccLimit α)
    Sig :
    Transform.TransformsTo (fun d =>
        p.scheme.scheme.grade d.1)
      (p.scheme.rows.E Sig)
      (fun d => min (p.someProvisionalValue d.1) (p.someProvisionalValue Sig)) := by
  by_cases htop : p.label Sig = ⊤
  · exact?
  · have hlt : p.label Sig < ofOrd α := (p.label_bound Sig).resolve_right htop
    have hfun : (fun d : p.scheme.scheme.belowCell Sig =>
        min (p.someProvisionalValue d.1) (p.someProvisionalValue Sig)) =
        fun d => min (p.label d.1) (p.label Sig) := by
      funext d
      rw [someProvisionalValue_of_ne_top htop]
      by_cases hd : p.label d.1 = ⊤
      · grind [le_someProvisionalValue_of_top]
      · rw [someProvisionalValue_of_ne_top hd]
    rw [hfun]
    exact p.respects.locality Sig

/-- **Lemma 5.3.6 (availability of `p⁺`)**: at a finite-labelled cell the original
availability; at an `∞`-cell the availability of the row of a maximal top witness `Θ`, read
through the monotone label witness (the found cell is again an `∞`-cell) and the band map. -/
theorem provisional_availability (p : S₀) :
    ∀ Sig Xi₀ : Cell p.scheme.scheme,
      p.scheme.scheme.scope Sig ⊆ p.scheme.scheme.scope Xi₀ →
      p.scheme.scheme.grade Sig = p.scheme.scheme.grade Xi₀ →
      ∃ Xi : Cell p.scheme.scheme, p.scheme.scheme.cell Xi = p.scheme.scheme.cell Xi₀ ∧
        p.someProvisionalValue Sig ≤ p.someProvisionalValue Xi := by
  intro Sig Xi₀ hsub hgrade
  by_cases htop : p.label Sig = ⊤
  · obtain ⟨Θ, hSgΘ, hsc, hgr, hΘ⟩ := exists_top_witness htop
    have hXi₀Θ : GradedLe (p.scheme.scheme.cell Xi₀) (p.scheme.scheme.cell Θ) := by
      refine ⟨?_, ?_⟩
      · simp_all
      · change p.scheme.scheme.grade Xi₀ ≤ p.scheme.scheme.grade Θ
        rw [← hgrade]; exact hSgΘ.2
    obtain ⟨Xi, hcell, hle⟩ :=
      (p.scheme.consistent Θ).availability ⟨Sig, hSgΘ⟩ ⟨Xi₀, hXi₀Θ⟩ hsub hgrade
    obtain ⟨σ, hσmono, hlabel⟩ := exists_monotone_label_of_row p hgr hΘ
    have hXitop  := by
      have h1 := hlabel ⟨Sig, hSgΘ⟩
      have h2 := hlabel Xi
      rw [htop] at h1
      exact top_le_iff.mp (h1.le.trans ((hσmono hle).trans h2.symm.le))
    obtain ⟨lam, hlam, hbridge⟩ := exists_bandBridge p hsc hgr hΘ
    obtain ⟨hlSg, hvalSg⟩ := hbridge ⟨Sig, hSgΘ⟩ htop
    obtain ⟨_, hvalXi⟩ := hbridge Xi hXitop
    refine ⟨Xi.1, hcell, ?_⟩
    rw [← isProvisionalValue_iff.mp hvalSg, ← isProvisionalValue_iff.mp hvalXi]
    exact bandMap_mono_of_le hlam p.topGrade hlSg hle
  · obtain ⟨Xi, hcell, hle⟩ := p.respects.availability Sig Xi₀ hsub hgrade
    refine ⟨Xi, hcell, ?_⟩
    rw [someProvisionalValue_of_ne_top htop]
    exact le_someProvisionalValue_of_le_label ((p.label_bound Sig).resolve_right htop) hle

/-- **Proposition 5.3.3**: the provisional labelling `p⁺` respects the semantics of `p`. -/
theorem provisionalLift_respects (p : S₀) (hα : Order.IsSuccLimit α) :
    RespectsSemantics p.scheme.rows p.someProvisionalValue where
  orderly := someProvisionalValue_orderly p hα
  locality := provisional_locality p hα
  availability := provisional_availability p

/-- The provisional lift `p⁺ ∈ S^{α+ω}` (Prop. 5.3.3): same scheme and rows, labels `p⁺`. -/
noncomputable def provisionalLift (p : S₀) (hα : Order.IsSuccLimit α) :
    S (α + Ordinal.omega0) n where
  scheme := p.scheme
  label := p.someProvisionalValue
  label_bound Xi := Or.inl (p.someProvisionalValue_lt_add_omega Xi)
  respects := provisionalLift_respects p hα

/-- Provisional values reduce literally to the source labels. -/
theorem truncExt_someProvisionalValue (p : S₀) Xi :
    truncExt α (p.someProvisionalValue Xi) = p.label Xi := by
  by_cases htop : p.label Xi = ⊤
  · rw [htop]
    by_cases hcap : p.ProvisionalCap Xi
    · simp_all [someProvisionalValue_of_cap]
    · obtain ⟨i, -, -, hval⟩ := someProvisionalValue_of_band htop hcap
      rw [hval]
      exact truncExt_ofOrd_of_le (le_add_of_nonneg_right zero_le)
  · rw [someProvisionalValue_of_ne_top htop]
    rcases p.label_bound Xi with hlt | htop'
    · exact truncExt_id_of_lt hlt
    · exact absurd htop' htop


