/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ProvisionalLocality
public import VaughtConjecture.Knight.Reduction

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd

namespace StageType

variable {α : Ordinal.{0}} {n : ℕ}

/-- Every provisional value lies strictly below the end of the next `ω`-block. -/
theorem someProvisionalValue_lt_add_omega (p : S α n) (Xi : Cell p.scheme.scheme) :
    p.someProvisionalValue Xi < ofOrd (α + Ordinal.omega0) := by
  refine (p.someProvisionalValue_le Xi).trans_lt (ofOrd_lt_ofOrd.mpr ?_)
  simp

/-- The provisional value of an `∞`-cell is at least `α`. -/
theorem le_someProvisionalValue_of_top {p : S α n} {Xi : Cell p.scheme.scheme}
    (htop : p.label Xi = ⊤) : ofOrd α ≤ p.someProvisionalValue Xi := by
  by_cases hcap : p.ProvisionalCap Xi
  · rw [someProvisionalValue_of_cap htop hcap]
    simp
  · obtain ⟨i, -, -, hval⟩ := someProvisionalValue_of_band htop hcap
    simp_all

/-- The label dominates nothing above the provisional value: `p(Ξ) ≤ p⁺(Ξ)` fails only
through `⊤`, so a finite value below `p(Ξ)` is below `p⁺(Ξ)`. -/
theorem le_someProvisionalValue_of_le_label {p : S α n} {Xi : Cell p.scheme.scheme}
    {x : ExtOrd} (hx : x < ofOrd α) (h : x ≤ p.label Xi) : x ≤ p.someProvisionalValue Xi := by
  by_cases htop : p.label Xi = ⊤
  · exact hx.le.trans (le_someProvisionalValue_of_top htop)
  · rwa [someProvisionalValue_of_ne_top htop]

/-- **Lemma 5.3.4 (orderliness of `p⁺`)**: in the band case, consistency of the coded row makes
its finite part the selected band index. -/
theorem someProvisionalValue_orderly (p : S α n) (hα : Order.IsSuccLimit α) :
    Transform.IsOrderly p.scheme.scheme.grade p.someProvisionalValue := by
  intro Xi
  by_cases htop : p.label Xi = ⊤
  · have hgrade : p.scheme.scheme.grade Xi ≤ p.topGrade := grade_le_topGrade_of_top htop
    by_cases hcap : p.ProvisionalCap Xi
    · rw [someProvisionalValue_of_cap htop hcap, extVisibilityReplace_ofOrd]
      apply congrArg ofOrd
      symm
      apply (visibilityReplace_self_iff _ _).mpr
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
        trivial
      · have hself : visibilityReplace (Ordinal.omega0 * a + j)
            (p.scheme.scheme.grade Xi) (p.scheme.scheme.grade Xi) =
            Ordinal.omega0 * a + j := by
          have hrow' : row = ofOrd (Ordinal.omega0 * a + j) := hrow
          rw [hrow', extVisibilityReplace_ofOrd, ofOrd_inj] at hrowOrder
          tauto
        have hgradeFp : p.scheme.scheme.grade Xi ≤ finitePart (Ordinal.omega0 * a + j) :=
          (visibilityReplace_self_iff _ _).mp hself
        have hfpTop : finitePart (Ordinal.omega0 * a + j) < p.topGrade := by
          by_contra hge
          apply hcap
          refine ⟨Theta, hXi, ⟨Xi, hXi⟩, hscope, htopGrade, hThetaTop, htop, ?_⟩
          rw [hrow, extVisibilityReplace_ofOrd]
          exact le_of_eq (congrArg ofOrd
            ((visibilityReplace_self_iff _ _).mpr (not_lt.mp hge)))
        have hrowBand : Ordinal.omega0 * a + j = limitPart (Ordinal.omega0 * a + j) + i := by
          rw [hrow, extVisibilityReplace_ofOrd, visibilityReplace_of_finitePart_lt hfpTop,
            ofOrd_inj] at heq
          assumption
        have hfpEq : finitePart (Ordinal.omega0 * a + j) = i := by
          calc
            finitePart (Ordinal.omega0 * a + j) =
                finitePart (limitPart (Ordinal.omega0 * a + j) + i) :=
              congrArg finitePart hrowBand
            _ = i := finitePart_limitPart_add_nat _ _
        rw [hval, extVisibilityReplace_ofOrd]
        apply congrArg ofOrd
        symm
        apply (visibilityReplace_self_iff _ _).mpr
        rwa [finitePart_succLimit_add_nat hα, ← hfpEq]
  · rw [someProvisionalValue_of_ne_top htop]
    exact p.respects.orderly Xi

/-- Below a maximal top witness `Θ` the labels are a monotone function of the row `E(Θ)`
(the locality witness of the labels has `g = ⊤` up to `K^p`). -/
theorem exists_monotone_label_of_row (p : S α n) {Θ : Cell p.scheme.scheme}
    (hgr : p.scheme.scheme.grade Θ = p.topGrade) (hΘ : p.label Θ = ⊤) :
    ∃ σ : ExtOrd → ExtOrd, Monotone σ ∧
      ∀ d : p.scheme.scheme.below (p.scheme.scheme.cell Θ),
        p.label d.1 = σ (p.scheme.rows.E Θ d) := by
  obtain ⟨g, σ, hganti, _, _, hσmono, _, heq⟩ := p.respects.locality Θ
  have heq' : ∀ d : p.scheme.scheme.below (p.scheme.scheme.cell Θ),
      p.label d.1 = min (σ (p.scheme.rows.E Θ d)) (g (p.scheme.scheme.grade d.1)) := by
    grind
  have hgK : ∀ k, k ≤ p.topGrade → g k = ⊤ := by
    intro k hk
    have hΘ' := heq' ⟨Θ, GradedLe.refl _⟩
    grind
  refine ⟨σ, hσmono, fun d => ?_⟩
  have hk : p.scheme.scheme.grade d.1 ≤ p.topGrade := by
    have h2 : p.scheme.scheme.grade d.1 ≤ p.scheme.scheme.grade Θ := d.2.2
    omega
  grind

/-- **Lemma 5.3.5 (locality of `p⁺`)** at every controller. -/
theorem provisional_locality (p : S α n) (hα : Order.IsSuccLimit α)
    (Sig : Cell p.scheme.scheme) :
    Transform.TransformsTo (fun d : p.scheme.scheme.below (p.scheme.scheme.cell Sig) =>
        p.scheme.scheme.grade d.1)
      (p.scheme.rows.E Sig)
      (fun d => min (p.someProvisionalValue d.1) (p.someProvisionalValue Sig)) := by
  by_cases htop : p.label Sig = ⊤
  · exact topController_locality_provisional p hα htop
  · have hlt : p.label Sig < ofOrd α := (p.label_bound Sig).resolve_right htop
    have hfun : (fun d : p.scheme.scheme.below (p.scheme.scheme.cell Sig) =>
        min (p.someProvisionalValue d.1) (p.someProvisionalValue Sig)) =
        fun d => min (p.label d.1) (p.label Sig) := by
      funext d
      rw [someProvisionalValue_of_ne_top htop]
      by_cases hd : p.label d.1 = ⊤
      · rw [hd, min_top_left, min_eq_right (hlt.le.trans (le_someProvisionalValue_of_top hd))]
      · rw [someProvisionalValue_of_ne_top hd]
    rw [hfun]
    exact p.respects.locality Sig

/-- **Lemma 5.3.6 (availability of `p⁺`)**: at a finite-labelled cell the original
availability; at an `∞`-cell the availability of the row of a maximal top witness `Θ`, read
through the monotone label witness (the found cell is again an `∞`-cell) and the band map. -/
theorem provisional_availability (p : S α n) :
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
    have hXitop : p.label Xi.1 = ⊤ := by
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
theorem provisionalLift_respects (p : S α n) (hα : Order.IsSuccLimit α) :
    RespectsSemantics p.scheme.rows p.someProvisionalValue where
  orderly := someProvisionalValue_orderly p hα
  locality := provisional_locality p hα
  availability := provisional_availability p

/-- The provisional lift `p⁺ ∈ S^{α+ω}` (Prop. 5.3.3): same scheme and rows, labels `p⁺`. -/
noncomputable def provisionalLift (p : S α n) (hα : Order.IsSuccLimit α) :
    S (α + Ordinal.omega0) n where
  scheme := p.scheme
  label := p.someProvisionalValue
  label_bound Xi := Or.inl (p.someProvisionalValue_lt_add_omega Xi)
  respects := provisionalLift_respects p hα

/-- Provisional values reduce literally to the source labels. -/
theorem truncExt_someProvisionalValue (p : S α n) (Xi : Cell p.scheme.scheme) :
    truncExt α (p.someProvisionalValue Xi) = p.label Xi := by
  by_cases htop : p.label Xi = ⊤
  · rw [htop]
    by_cases hcap : p.ProvisionalCap Xi
    · rw [someProvisionalValue_of_cap htop hcap]
      simp
    · obtain ⟨i, -, -, hval⟩ := someProvisionalValue_of_band htop hcap
      simp_all
  · rw [someProvisionalValue_of_ne_top htop]
    rcases p.label_bound Xi with hlt | htop'
    · exact truncExt_id_of_lt hlt
    trivial

end StageType

end VaughtConjecture.Knight
