
import proofs.HordijkSteelThreshold.PeelingHistory
import proofs.RAFCriticalWindowQuantitative.FiniteClosure
import proofs.HordijkSteelThreshold.FixedPoolReactionLaw
import proofs.HordijkSteelThreshold.StaticSeedClosure
import proofs.HordijkSteelThreshold.WordEffectiveClosure
import proofs.HordijkSteelThreshold.StaticParameterMonotonicity



namespace HordijkSteelThreshold
open Classical MeasureTheory RAF.Polymer RAF.Concrete RAFCriticalWindowQuantitative unitInterval

theorem catalyst_raf_ge_static {M R : Type*} [Fintype M] [Fintype R] [DecidableEq M]
    (Q : ReversibleCRS M R) (p q : I) (m : ℕ) (hm : 0 < m)
    (hk : Q.food.card < (m-1)*(Fintype.card M / m))
    (hq : q ≤ fixedPoolParameter p ((m-1)*(Fintype.card M / m))) :
    (Measure.pi fun _ : R => ambientCoordLaw q)
      {ω | NearFull m (fullClosure Q (Finset.univ.filter ω))} ≤
      RAFEmergenceApprox.Generic.law (fun _ : R => p) {ω | ∃ S, IsRevRAF Q (fun x r => ω r x) S} := by
  let k := (m-1)*(Fintype.card M / m)
  have hcard : k ≤ Fintype.card M :=
    (Nat.mul_le_mul_right _ (Nat.sub_le m 1)).trans (Nat.mul_div_le _ _)
  have hc : Monotone (fullClosure Q) := fun S T h => revClosureAt_mono_reactions Q h _
  apply (measure_mono (show _ ⊆ {ω | k ≤ (fullClosure Q (Finset.univ.filter ω)).card} from by
    intro ω hω
    have hd := Nat.mul_le_mul_left (m-1) (Nat.div_mul_le_self (Fintype.card M) m)
    dsimp [NearFull] at hω
    dsimp [k]
    nlinarith)).trans
  apply (product_increasing_mono (fun _ : R => q)
    (fun _ => fixedPoolParameter p (finiteInitialSegment M k).card)
    (fun _ => by simpa [card_finiteInitialSegment M k hcard] using hq)
    _ (by
      intro x y hxy hx
      exact hx.trans (Finset.card_le_card (hc (Finset.monotone_filter_right _ fun r _ => @hxy r))))).trans
  let A := fun ω => peelingActiveAt (RAFEmergenceApprox.Generic.catalystActive ω) (fullClosure Q) (Fintype.card R)
  have hRAF : {ω | k ≤ (fullClosure Q (A ω)).card} ⊆
      {ω | ∃ S, IsRevRAF Q (fun x r => ω r x) S} := by
    intro ω hω
    let B := A ω
    let C := fullClosure Q B
    let U := B.filter fun r => Q.lhs r ⊆ C ∧ Q.rhs r ⊆ C
    have hs : RAFEmergenceApprox.Generic.catalystActive ω C = B :=
      (by
        let C := peelingActiveAt (RAFEmergenceApprox.Generic.catalystActive ω) (fullClosure Q)
        apply bounded_progress (fun k => C (k+1) = C k) fun k => Fintype.card R - (C k).card
        · grind [peelingActiveAt]
        · intro n hn
          have hlt : (C (n+1)).card < (C n).card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
            ⟨peelingActiveAt_antitone (RAFEmergenceApprox.Generic.catalystActive ω) (fullClosure Q) ((RAFEmergenceApprox.Generic.catalystActive_mono ω)) hc (Nat.le_succ n), hn⟩)
          have := Finset.card_le_univ (C n)
          omega
        · intro n
          exact Nat.sub_le _ _)
    have hall (t : ℕ) : revClosureAt Q B t ⊆ C := fun x hx =>
      (closureAt_exists_iff Q B (closure_stable_at_card Q B) x).mp ⟨t, hx⟩
    have hu (t : ℕ) : revClosureAt Q B t ⊆ revClosureAt Q U t := by
      induction t with
      | zero => rfl
      | succ t ih =>
        
        have ht' := hall (t+1)
        simp only [revClosureAt, revClosureStep] at ht' ⊢
        grind (gen := 16) [RevEnabledLhs, RevEnabledRhs]
    have hUC := hu (Fintype.card M)
    have hne : U.Nonempty := by
      by_contra hn
      have hf := revClosureAt_eq_food_of_no_seed Q U
        (by simp_all) (Fintype.card M)
      have hh := Finset.card_le_card hUC
      rw [hf] at hh
      exact (not_lt_of_ge hh) (hk.trans_le hω)
    refine ⟨U, hne, ?_, ?_⟩
    · intro r hr
      exact ⟨Fintype.card M, (Finset.union_subset (Finset.mem_filter.mp hr).2.1
        (Finset.mem_filter.mp hr).2.2).trans hUC⟩
    · intro r hr
      obtain ⟨x, hx, hcat⟩ := (Finset.mem_filter.mp (hs.symm ▸ (Finset.mem_filter.mp hr).1)).2
      exact ⟨x, Fintype.card M, hUC hx, hcat⟩
  refine le_trans ?_ (measure_mono hRAF)
  
  rw [← catalystPool_statistic (fun _ : R => p) (finiteInitialSegment M k) (fun B => k ≤ (fullClosure Q B).card),
    RAFEmergenceApprox.Generic.peeling_statistic_eq_scalar _ (fullClosure Q) hc (Fintype.card R) (fun B => k ≤ (fullClosure Q B).card)]
  apply measure_mono
  intro ω hω
  generalize Fintype.card R = t
  induction t <;>
    exact hω.trans (Finset.card_le_card (hc ((RAFEmergenceApprox.Generic.catalystActive_mono ω)
      (finiteInitialSegment_mono _ (by assumption)))))



/-- Reindex actual food molecules into the finite cutoff universe. This is the
same bounded-word injection used in the repository's reversible trace counts. -/
theorem binaryFood_card_le_cutoff (n L : ℕ) :
    (binaryFood n L).card ≤ Fintype.card (Molecule L) := by
  let f : ↥(binaryFood n L) → Molecule L := fun x =>
    ⟨⟨x.val.1.val, by grind [binaryFood, molLength]⟩, x.val.2⟩
  
  simpa using Fintype.card_le_of_injective f (by
                                               rintro ⟨⟨ai,aw⟩,ha⟩ ⟨⟨bi,bw⟩,hb⟩ h

                                               grind )




end HordijkSteelThreshold
