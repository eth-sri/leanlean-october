module

public import proofs.RAFEmergenceApprox.GenericHistory

@[expose] public section

namespace RAFReactionQuotient
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold

variable {R J : Type*} [Fintype R]

def fieldOR (π : R → J) (ω : R → Prop) (j : J) : Prop :=
  ∃ r, π r = j ∧ ω r

theorem fieldOR_independent (π : R → J) (p : I) :
    iIndepFun (fun j (ω : R → Prop) => fieldOR π ω j) (RAFEmergenceApprox.Generic.colLaw R p) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _
  have hprod (S : Finset J) :
      RAFEmergenceApprox.Generic.colLaw R p {ω | ∀ j ∈ S, fieldOR π ω j ∈ sets j} =
        ∏ j ∈ S, RAFEmergenceApprox.Generic.colLaw R p {ω | fieldOR π ω j ∈ sets j} := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert j S hj ih =>
      let B := Finset.univ.filter (fun r : R => π r = j)
      let D := Finset.univ.filter (fun r : R => π r ∈ S)
      have hd : Disjoint B D := Finset.disjoint_left.mpr fun r hr hs =>
        hj ((Finset.mem_filter.mp hr).2 ▸ (Finset.mem_filter.mp hs).2)
      have ht := (iIndepFun_pi (μ := fun _ : R => ambientCoordLaw p)
        fun _ => measurable_id.aemeasurable).indepFun_finset B D hd fun _ => measurable_pi_apply _
      have hind : IndepFun (fun ω : R → Prop => fieldOR π ω j ∈ sets j)
          (fun ω => ∀ k ∈ S, fieldOR π ω k ∈ sets k) (RAFEmergenceApprox.Generic.colLaw R p) := by
        convert ht.comp (measurable_of_finite fun v : B → Prop => (∃ r, v r) ∈ sets j)
          (measurable_of_finite fun v : D → Prop => ∀ k ∈ S, (∃ r : D, π r.1 = k ∧ v r) ∈ sets k) using 1
        · ext ω; simp [B, fieldOR]
        · ext ω; simp [D, fieldOR]; exact forall₂_congr fun k hk => by congr! 1; aesop
        · rfl
      have hi := hind.measure_inter_preimage_eq_mul {True} {True} (.singleton True) (.singleton True)
      rw [show {ω : R → Prop | ∀ k ∈ insert j S, fieldOR π ω k ∈ sets k} =
        {ω | fieldOR π ω j ∈ sets j} ∩ {ω | ∀ k ∈ S, fieldOR π ω k ∈ sets k} by ext; simp, Finset.prod_insert hj]
      simpa only [Set.preimage, Set.mem_singleton_iff, eq_iff_iff, iff_true, ih] using hi
  convert hprod S using 2
  · ext; simp
  · rfl

theorem fieldOR_closed_probability (π : R → J) (p : I) (j : J) :
    RAFEmergenceApprox.Generic.colLaw R p {ω | ¬ fieldOR π ω j} =
      (toNNReal (σ p) : ENNReal) ^ (Finset.univ.filter (fun r => π r = j)).card := by
  convert RAFEmergenceApprox.Generic.closed_probability p (Finset.univ.filter (fun r => π r = j)) using 2
  ext; simp [fieldOR]

end RAFReactionQuotient
