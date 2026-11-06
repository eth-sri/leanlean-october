module
public import Mathlib

public import PottsDiscontinuity.FK.EndpointLimits

/-! Infinite connection data with all infinite clusters in one marked class.
No assertion about uniqueness of infinite clusters is used or made. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical Filter
noncomputable section

variable {V : Type*}

/-- Collapse marked vertices to the distinguished ghost label; retain the
ordinary component label for every unmarked vertex. -/
def markedClusterLabel (R : Setoid V) (P : V → Prop) : Option V → Option (Quotient R)
  | none => none
  | some x => if P x then none else some (Quotient.mk R x)

/-- The partition obtained by merging all marked clusters with the ghost. -/
def markedClusterSetoid (R : Setoid V) (P : V → Prop)  :=
  Setoid.ker (markedClusterLabel R P)

@[simp] theorem markedClusterSetoid_some_none (R : Setoid V) (P : V → Prop) (x : V) :
    markedClusterSetoid R P (some x) none ↔ P x := by
  change markedClusterLabel R P (some x) = markedClusterLabel R P none ↔ P x
  by_cases hx : P x <;> simp [markedClusterLabel]

theorem markedClusterSetoid_some_some (R : Setoid V) (P : V → Prop)
    (hP : ∀ x y, R x y → (P x ↔ P y)) (x y : V) :
    markedClusterSetoid R P (some x) (some y) ↔ R x y ∨ P x ∧ P y := by
  change markedClusterLabel R P (some x) = markedClusterLabel R P (some y) ↔ _
  by_cases hx : P x <;> by_cases hy : P y
  · simp [markedClusterLabel, hx, hy]
  · grind +locals
  · grind +locals
  · simp [markedClusterLabel, hx, hy, Quotient.eq]

/-- An open component reaches a vertex outside this finite box. -/
def clusterEscapesBox (H : SimpleGraph (ℤ × ℤ)) (n : ℕ) (x : ℤ × ℤ)  :=
  ∃ y, y ∉ box n ∧ H.Reachable x y

/-- The literal infinite-cluster event: infinitely many vertices are reachable. -/
def clusterIsInfinite (H : SimpleGraph (ℤ × ℤ)) (x : ℤ × ℤ)  :=
  Set.Infinite {y | H.Reachable x y}

section

variable (H : SimpleGraph (ℤ × ℤ))
include H

theorem clusterEscapesBox_saturated  (n : ℕ)
    (x y : ℤ × ℤ) (hxy : H.Reachable x y) :
    clusterEscapesBox H n x ↔ clusterEscapesBox H n y := by
  constructor
  · rintro ⟨z, hz, hxz⟩
    exact ⟨z, hz, hxy.symm.trans hxz⟩
  · rintro ⟨z, hz, hyz⟩
    exact ⟨z, hz, hxy.trans hyz⟩

/-- Box escape is equivalent to infinitely many vertices in the component. -/
theorem clusterIsInfinite_iff_escapes  (x : ℤ × ℤ) :
    clusterIsInfinite H x ↔ ∀ n, clusterEscapesBox H n x := by
  constructor
  · intro h n
    by_contra hn
    change ¬ ∃ y, y ∉ box n ∧ H.Reachable x y at hn
    push Not at hn
    apply h
    apply (box n).finite_toSet.subset
    intro y hy
    by_contra hyn
    exact hn y hyn hy
  · intro h hn
    
    obtain ⟨n, hn⟩ := (hn.eventually_all.mpr  fun y _ => FK.eventually_mem_box y ).exists
    obtain ⟨y, hy, hxy⟩ := h n
    exact hy (hn y hxy)

theorem clusterIsInfinite_saturated 
    (x y : ℤ × ℤ) (hxy : H.Reachable x y) :
    clusterIsInfinite H x ↔ clusterIsInfinite H y := by
  simp_rw [clusterIsInfinite_iff_escapes]
  exact forall_congr'  fun n => clusterEscapesBox_saturated H n x y hxy 

end

/-- The connection partition with the exterior of the finite box merged. -/
def exteriorMergedSetoid (H : SimpleGraph (ℤ × ℤ)) (n : ℕ)  :=
  markedClusterSetoid H.reachableSetoid (clusterEscapesBox H n)

/-- Finite clusters retain their actual connection classes, and every infinite
cluster belongs to the ghost class. Distinct infinite clusters are merged. -/
def infiniteMergedSetoid (H : SimpleGraph (ℤ × ℤ))  :=
  markedClusterSetoid H.reachableSetoid (clusterIsInfinite H)

section

variable (H : SimpleGraph (ℤ × ℤ))
include H

@[simp] theorem infiniteMergedSetoid_some_none  (x : ℤ × ℤ) :
    infiniteMergedSetoid H (some x) none ↔ clusterIsInfinite H x :=
  markedClusterSetoid_some_none _ _ _

theorem infiniteMergedSetoid_some_some  (x y : ℤ × ℤ) :
    infiniteMergedSetoid H (some x) (some y) ↔
      H.Reachable x y ∨ clusterIsInfinite H x ∧ clusterIsInfinite H y :=
  by
    solve_by_elim [_root_.PottsDiscontinuity.Potts.markedClusterSetoid_some_some, _root_.PottsDiscontinuity.Potts.clusterIsInfinite_saturated]

theorem exteriorMergedSetoid_some_some  (n : ℕ) (x y : ℤ × ℤ) :
    exteriorMergedSetoid H n (some x) (some y) ↔
      H.Reachable x y ∨ clusterEscapesBox H n x ∧ clusterEscapesBox H n y :=
  by
    solve_by_elim [_root_.PottsDiscontinuity.Potts.markedClusterSetoid_some_some, _root_.PottsDiscontinuity.Potts.clusterEscapesBox_saturated]

/-- Deterministic merged connection data is the decreasing exterior limit.
This statement makes no uniqueness assertion for infinite clusters. -/
theorem exteriorMergedSetoid_limit  (a b : Option (ℤ × ℤ)) :
    (∀ n, exteriorMergedSetoid H n a b) ↔ infiniteMergedSetoid H a b := by
  cases a with
  | none =>
    cases b with
    | none => simp_all
    | some y =>
      have hswap (R : Setoid (Option (ℤ × ℤ))) : R none (some y) ↔ R (some y) none :=
        ⟨R.symm, R.symm⟩
      have hmid : (∀ n, exteriorMergedSetoid H n (some y) none) ↔
          infiniteMergedSetoid H (some y) none := by
        change (∀ n, markedClusterSetoid H.reachableSetoid (clusterEscapesBox H n) (some y) none) ↔
          markedClusterSetoid H.reachableSetoid (clusterIsInfinite H) (some y) none
        simp only [markedClusterSetoid_some_none, clusterIsInfinite_iff_escapes]
      exact (forall_congr'  fun n => hswap (exteriorMergedSetoid H n) ).trans
        (hmid.trans (hswap (infiniteMergedSetoid H)).symm)
  | some x =>
    cases b with
    | none =>
      change (∀ n, markedClusterSetoid H.reachableSetoid (clusterEscapesBox H n) (some x) none) ↔
        markedClusterSetoid H.reachableSetoid (clusterIsInfinite H) (some x) none
      simp only [markedClusterSetoid_some_none, clusterIsInfinite_iff_escapes]
    | some y =>
      simp only [exteriorMergedSetoid_some_some, infiniteMergedSetoid_some_some]
      by_cases hxy : H.Reachable x y
      · simp [hxy]
      · grind [clusterIsInfinite_iff_escapes]

end

end
end PottsDiscontinuity.Potts
