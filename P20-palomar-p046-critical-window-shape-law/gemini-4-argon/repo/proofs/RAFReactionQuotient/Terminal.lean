module

public import proofs.RAFReactionQuotient.FiniteApproximation
public import proofs.RAFEmergenceApprox.SourceEvent
public import proofs.RAFEmergenceApprox.ThresholdSweep
public import proofs.HordijkSteelThreshold.SourceTerminalRAF

@[expose] public section

namespace RAFReactionQuotient
open Classical RAF RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source HordijkSteelThreshold
open RAFEmergenceApprox.Generic

theorem quotient_raf_subset_peeling {n L : ℕ} (ω : RepositoryChannel n → Molecule n → Prop)
    {S : Finset (RepositoryChannel n)}
    (hS : IsRevRAF (repositoryCRS n L) (fun x j => ω j x) S) (t : ℕ) :
    S ⊆ peelingActiveAt (RAFEmergenceApprox.Generic.catalystActive ω) (quotientClosure n L) t := by
  induction t with
  | zero =>
    intro r hr
    obtain ⟨x, _, _, hx⟩ := hS.2.2 r hr
    exact (RAFEmergenceApprox.Generic.mem_catalystActive _ _ _).mpr ⟨x, Finset.mem_univ _, hx⟩
  | succ t ih =>
    intro r hr
    obtain ⟨x, k, hx, hcat⟩ := hS.2.2 r hr
    exact (RAFEmergenceApprox.Generic.mem_catalystActive _ _ _).mpr
      ⟨x, quotientClosure_mono n L ih ((mem_quotientClosure S x).mpr ⟨k, hx⟩), hcat⟩

theorem quotient_terminal_hasRAF {n : ℕ} (ω : RepositoryChannel n → Molecule n → Prop)
    (hmass : 6 < (quotientClosure n 2 (peelingActiveAt (RAFEmergenceApprox.Generic.catalystActive ω)
      (quotientClosure n 2) (Fintype.card (RepositoryChannel n)))).card) :
    ∃ S, IsRevRAF (repositoryCRS n 2) (fun x j => ω j x) S := by
  let A := peelingActiveAt (RAFEmergenceApprox.Generic.catalystActive ω) (quotientClosure n 2)
    (Fintype.card (RepositoryChannel n))
  let P : Finset (Reaction n) := Finset.univ.filter fun r => splitToQuotient r ∈ A
  have hpre : quotientClosure n 2 A = temporaryReactionClosure 2 P := by
    rw [show A = quotientOpen (fun j => j ∈ A) by ext; simp [quotientOpen], quotientClosure_pullback]
    congr 1; ext; simp [staticOpenReactions, P]
  have hs : RAFEmergenceApprox.Generic.catalystActive ω (quotientClosure n 2 A) = A :=
    peelingActiveAt_stable_card _ _ (RAFEmergenceApprox.Generic.catalystActive_mono ω)
      (quotientClosure_mono n 2)
  have hraf : IsRevRAF (binaryPolymerCRS n 2) (fun x r => ω (splitToQuotient r) x)
      (usableClosureReactions 2 P) := by
    apply usableClosureReactions_isRAF
    · intro r hr
      have hj : splitToQuotient r ∈ RAFEmergenceApprox.Generic.catalystActive ω (quotientClosure n 2 A) := by
        rw [hs]; exact (Finset.mem_filter.mp hr).2
      obtain ⟨x, hx, hc⟩ := (RAFEmergenceApprox.Generic.mem_catalystActive _ _ _).mp hj
      exact ⟨x, hpre ▸ hx, hc⟩
    · rw [← hpre]
      by_contra! h
      have hsub : quotientClosure n 2 A ⊆ binaryFood n 2 :=
        fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h x hx⟩
      have hc := (Finset.card_le_card hsub).trans (binaryFood_card_le_cutoff n 2)
      have h6 : Fintype.card (Molecule 2) = 6 := by decide
      dsimp [A] at hc; omega
  have he : orCatalysis splitToQuotient (fun x r => ω (splitToQuotient r) x) =
      (fun x j => ω j x) :=
    funext₂ fun x j => propext (quotient_mark_pullback_OR (fun j => ω j x) j)
  exact ⟨_, he ▸ raf_image _ _ splitToQuotient splitToQuotient_lhs splitToQuotient_rhs rfl _ _ hraf⟩

end RAFReactionQuotient
