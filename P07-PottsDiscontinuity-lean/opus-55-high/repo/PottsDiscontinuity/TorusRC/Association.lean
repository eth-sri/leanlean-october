module

public import PottsDiscontinuity.TorusRC.IndexedFK
public import PottsDiscontinuity.TorusRC.RectanglePairs

/-! # FKG association for the critical indexed torus law -/

public section

open Finset
open scoped BigOperators

namespace PottsDiscontinuity.TorusRC

open Torus

variable {N M : ℕ}

def openIndexSet (A : RCConfig N M) : Finset (Fin N × Fin M) :=
  univ.filter fun v => A v = true

section
variable (A B : RCConfig N M)
theorem openIndexSet_inf  :
    openIndexSet (A ⊓ B) = openIndexSet A ∩ openIndexSet B := by
  ext v
  simp [openIndexSet]

theorem openIndexSet_sup  :
    openIndexSet (A ⊔ B) = openIndexSet A ∪ openIndexSet B := by
  ext v
  simp [openIndexSet]

theorem openCount_lattice  :
    openCount (A ⊓ B) + openCount (A ⊔ B) = openCount A + openCount B := by
  change (openIndexSet (A ⊓ B)).card + (openIndexSet (A ⊔ B)).card =
    (openIndexSet A).card + (openIndexSet B).card
  grind [openIndexSet_inf, openIndexSet_sup]

theorem closedCount_lattice  :
    closedCount (A ⊓ B) + closedCount (A ⊔ B) = closedCount A + closedCount B := by
  have hA := openCount_add_closedCount A
  have hB := openCount_add_closedCount B
  have hi := openCount_add_closedCount (A ⊓ B)
  have hu := openCount_add_closedCount (A ⊔ B)
  grind [openCount_lattice]
end

section
variable (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
theorem torusRCWeight_lattice_condition (A B : RCConfig N M) :
    torusRCWeight hN hM q A * torusRCWeight hN hM q B ≤
      torusRCWeight hN hM q (A ⊓ B) * torusRCWeight hN hM q (A ⊔ B) := by
  let p := (rcCriticalParameter q).val
  have hprod (C D : RCConfig N M) :
      torusRCWeight hN hM q C * torusRCWeight hN hM q D =
        (p ^ (openCount C + openCount D) *
          (1 - p) ^ (closedCount C + closedCount D)) *
            q.val ^ (clusterCount hN hM true C + clusterCount hN hM true D) := by
    grind [torusRCWeight]
  rw [hprod A B, hprod (A ⊓ B) (A ⊔ B), ← openCount_lattice A B,
    ← closedCount_lattice A B]
  apply mul_le_mul_of_nonneg_left
  · exact pow_le_pow_right₀ q.property (clusterCount_supermodular hN hM A B)
  · exact mul_nonneg (pow_nonneg (criticalParameter_pos q).le _)
      (pow_nonneg (sub_nonneg.mpr (criticalParameter_lt_one q).le) _)

theorem torusRCMass_lattice_condition (A B : RCConfig N M) :
    torusRCMass hN hM q A * torusRCMass hN hM q B ≤
      torusRCMass hN hM q (A ⊓ B) * torusRCMass hN hM q (A ⊔ B) := by
  simp only [torusRCMass]
  rw [div_mul_div_comm, div_mul_div_comm]
  exact (div_le_div_iff_of_pos_right
    (mul_pos (torusRCPartition_pos hN hM q) (torusRCPartition_pos hN hM q))).2
      (torusRCWeight_lattice_condition hN hM q A B)

/-- Increasing nonnegative functions are positively associated under the torus law. -/
theorem torusRC_positive_association (f g : RCConfig N M → ℝ)
    (hf0 : ∀ A, 0 ≤ f A) (hg0 : ∀ A, 0 ≤ g A)
    (hf : Monotone f) (hg : Monotone g) :
    (∑ A, torusRCMass hN hM q A * f A) *
      (∑ A, torusRCMass hN hM q A * g A) ≤
        ∑ A, torusRCMass hN hM q A * (f A * g A) := by
  have h := _root_.fkg (μ := torusRCMass hN hM q) (f := f) (g := g)
    (fun A => (torusRCMass_pos hN hM q A).le) hf0 hg0 hf hg
    (torusRCMass_lattice_condition hN hM q)
  simpa only [sum_torusRCMass, one_mul] using h

/-- Increasing events are positively associated under the normalized torus law. -/
theorem torusRCProbability_inter_ge_mul (E F : Set (RCConfig N M))
    (hE : ∀ ⦃A B⦄, A ≤ B → A ∈ E → B ∈ E)
    (hF : ∀ ⦃A B⦄, A ≤ B → A ∈ F → B ∈ F) :
    torusRCProbability hN hM q E * torusRCProbability hN hM q F ≤
      torusRCProbability hN hM q (E ∩ F) := by
  classical
  let f : RCConfig N M → ℝ := fun A => if A ∈ E then 1 else 0
  let g : RCConfig N M → ℝ := fun A => if A ∈ F then 1 else 0
  have hf0 : ∀ A, 0 ≤ f A := by
    grind
  have hg0 : ∀ A, 0 ≤ g A := by
    grind
  have hf : Monotone f := by
    intro A B hAB
    by_cases hA : A ∈ E
    · have hB : B ∈ E := by tauto
      aesop
    aesop
  have hg : Monotone g := by
    intro A B hAB
    by_cases hA : A ∈ F
    · have hB : B ∈ F := by tauto
      simp [g, hA, hB]
    · have hgA : g A = 0 := by aesop
      simp_all
  have hleft : (∑ A, torusRCMass hN hM q A * f A) =
      torusRCProbability hN hM q E := by
    rw [torusRCProbability_eq_sum]
    grind [Set.indicator]
  have hmiddle : (∑ A, torusRCMass hN hM q A * g A) =
      torusRCProbability hN hM q F := by
    rw [torusRCProbability_eq_sum]
    grind [Set.indicator]
  have hright : (∑ A, torusRCMass hN hM q A * (f A * g A)) =
      torusRCProbability hN hM q (E ∩ F) := by
    rw [torusRCProbability_eq_sum]
    grind [Set.indicator]
  rw [← hleft, ← hmiddle, ← hright]
  exact (torusRC_positive_association hN hM q f g hf0 hg0 hf hg)
end

/-- A finite intersection of increasing torus events has probability at least
the product of the individual probabilities. -/
theorem torusRCProbability_finset_inter_ge_prod
    {ι : Type*} [DecidableEq ι] (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (s : Finset ι)
    (E : ι → Set (RCConfig N M))
    (hE : ∀ i ⦃A B⦄, A ≤ B → A ∈ E i → B ∈ E i) :
    (∏ i ∈ s, torusRCProbability hN hM q (E i)) ≤
      torusRCProbability hN hM q {A | ∀ i ∈ s, A ∈ E i} := by
  let F (t : Finset ι) := {A | ∀ i ∈ t, A ∈ E i}
  have hFmono (t : Finset ι) : ∀ ⦃A B⦄, A ≤ B → A ∈ F t → B ∈ F t := by
    tauto
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      have hEq : F (insert a s) = F s ∩ E a := by
        ext A
        grind
      have hstep := torusRCProbability_inter_ge_mul hN hM q (F s) (E a)
        (hFmono s) (hE a)
      calc
        (∏ i ∈ insert a s, torusRCProbability hN hM q (E i)) =
            (∏ i ∈ s, torusRCProbability hN hM q (E i)) *
              torusRCProbability hN hM q (E a) := by
                grind
        _ ≤ torusRCProbability hN hM q (F s) *
              torusRCProbability hN hM q (E a) :=
                mul_le_mul_of_nonneg_right ih
                  (torusRCProbability_nonneg hN hM q (E a))
        _ ≤ torusRCProbability hN hM q (F s ∩ E a) := hstep
        _ = torusRCProbability hN hM q (F (insert a s)) := by simp_all

end PottsDiscontinuity.TorusRC
