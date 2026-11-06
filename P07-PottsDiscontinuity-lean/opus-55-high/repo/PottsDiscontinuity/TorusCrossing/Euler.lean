module

public import PottsDiscontinuity.FK.ComponentMerge
public import PottsDiscontinuity.FK.Parameters
public import PottsDiscontinuity.Frozen.Defs.RCCriticalParameter
public import PottsDiscontinuity.TorusCrossing.Existence

/-!
# Euler's relation for the mixed board and exact weight duality

Flipping a closed edge `m` of a primal configuration `A` changes the number `kP` of wired
primal clusters by `-1` exactly when the ends of `m` are not connected, and changes the number
`kD` of wired dual clusters of the complementary dual configuration by `+1` exactly when the
dual ends of `m` are not connected after the flip.  By exclusion and existence exactly one of the
two happens, so `kD - kP - |A|` does not depend on `A`.
-/

@[expose] public noncomputable section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open scoped Classical

theorem cfgOf_insert {ends : Cell → Cell × Cell} {P M : Finset Cell} (hD : EndData ends P M)
    (A : Finset Cell) (m : Cell) (hm : m ∈ M) :
    cfgOf hD (insert m A) = insert (endEdgeEquiv hD ⟨m, hm⟩) (cfgOf hD A) := by
  ext e
  obtain ⟨m', rfl⟩ := (endEdgeEquiv hD).surjective e
  rw [mem_cfgOf, Finset.mem_insert, Finset.mem_insert, mem_cfgOf]
  aesop


section CountLemmas

variable {ends : Cell → Cell × Cell} {P M : Finset Cell} (hD : EndData ends P M)
include hD

section
variable (m : Cell) (hm : m ∈ M) (u v : P) (hu : u.1 = (ends m).1) (hv : v.1 = (ends m).2)
include m hm hu hv
theorem endGraph_adj_of_mem  : (endGraph ends P M).Adj u v := by
  refine ⟨fun h => hD.ne m (by simp_all), Or.inl ⟨m, hm, ?_⟩⟩
  simp_all

theorem endEdgeEquiv_eq  :
    endEdgeEquiv hD ⟨m, hm⟩ =
      ⟨s(u, v), (endGraph ends P M).mem_edgeSet.mpr (endGraph_adj_of_mem hD m hm u v hu hv)⟩ := by
  apply Subtype.ext
  aesop
end

section
variable (ξ : FK.BoundaryCondition P) (A : Finset Cell) (m : Cell) (hm : m ∈ M) (u v : P) (hu : u.1 = (ends m).1) (hv : v.1 = (ends m).2)
include hm hu hv
theorem count_cfgOf_insert_of_related (hrel : (FK.componentSetoid (endGraph ends P M) ξ (cfgOf hD A)).r u v) :
    FK.componentCount (endGraph ends P M) ξ (cfgOf hD (insert m A)) =
      FK.componentCount (endGraph ends P M) ξ (cfgOf hD A) := by
  rw [cfgOf_insert hD A m hm, endEdgeEquiv_eq hD m hm u v hu hv]
  exact FK.componentCount_insert_eq_of_related ξ _ (endGraph_adj_of_mem hD m hm u v hu hv) hrel

theorem count_cfgOf_insert_of_not_related (hrel : ¬ (FK.componentSetoid (endGraph ends P M) ξ (cfgOf hD A)).r u v) :
    FK.componentCount (endGraph ends P M) ξ (cfgOf hD (insert m A)) + 1 =
      FK.componentCount (endGraph ends P M) ξ (cfgOf hD A) := by
  rw [cfgOf_insert hD A m hm, endEdgeEquiv_eq hD m hm u v hu hv]
  exact FK.componentCount_insert_of_not_related ξ _ (endGraph_adj_of_mem hD m hm u v hu hv) hrel
end

end CountLemmas

namespace Rect

variable (R : Rect)

section
variable (A : Finset Cell)
/-- Number of wired primal clusters. -/
def kP  : ℕ :=
  FK.componentCount R.pG R.sepBC (cfgOf R.pData A)

/-- Number of wired dual clusters of the complementary configuration. -/
def kD  : ℕ :=
  FK.componentCount R.dG R.dualBC (cfgOf R.dData (R.inner \ A))
end

section
variable (hh : 0 < R.h)
include hh
theorem euler_step (A₀ : Finset Cell) (hA₀ : A₀ ⊆ R.inner) (m : Cell)
    (hm : m ∈ R.inner) (hmA : m ∉ A₀) :
    (R.kD (insert m A₀) : ℤ) - R.kP (insert m A₀) - (insert m A₀).card =
      R.kD A₀ - R.kP A₀ - A₀.card := by
  have hmem := R.pData.mem m hm
  have hmem' := R.dData.mem m hm
  let u : R.pcells := ⟨(primalEnds m).1, hmem.1⟩
  let v : R.pcells := ⟨(primalEnds m).2, hmem.2⟩
  let u' : R.dcells := ⟨(dualEnds m).1, hmem'.1⟩
  let v' : R.dcells := ⟨(dualEnds m).2, hmem'.2⟩
  have hcard := Finset.card_insert_of_notMem hmA
  have hD₁ : insert m (R.inner \ insert m A₀) = R.inner \ A₀ := by
    grind
  have hkD0 : R.kD A₀ = FK.componentCount R.dG R.dualBC
      (cfgOf R.dData (insert m (R.inner \ insert m A₀))) := by
    aesop
  have hkD1 : R.kD (insert m A₀) = FK.componentCount R.dG R.dualBC
      (cfgOf R.dData (R.inner \ insert m A₀)) := rfl
  by_cases hrelP : (FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A₀)).r u v
  · have hD := count_cfgOf_insert_of_not_related R.dData R.dualBC (R.inner \ insert m A₀) m hm
      u' v' rfl rfl (R.exclusion A₀ hA₀ m hm hmA u v rfl rfl u' v' rfl rfl hrelP)
    have e1 : R.kP (insert m A₀) = R.kP A₀ := (count_cfgOf_insert_of_related R.pData R.sepBC A₀ m hm u v rfl rfl hrelP)
    linarith
  · have hD := count_cfgOf_insert_of_related R.dData R.dualBC (R.inner \ insert m A₀) m hm
      u' v' rfl rfl (R.existence hh A₀ hA₀ m hm u v rfl rfl u' v' rfl rfl hrelP)
    have e1 : R.kP (insert m A₀) + 1 = R.kP A₀ := (count_cfgOf_insert_of_not_related R.pData R.sepBC A₀ m hm u v rfl rfl hrelP)
    linarith


/-- **Euler's relation** for the mixed board: `kD - kP - |A|` is independent of `A ⊆ inner`. -/
theorem euler (A : Finset Cell) (hA : A ⊆ R.inner) :
    (R.kD A : ℤ) - R.kP A - A.card = (R.kD ∅ : ℤ) - R.kP ∅ := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert m A₀ hmA ih =>
    have hA₀ : A₀ ⊆ R.inner := by grind
    rw [R.euler_step hh A₀ hA₀ m (by grind) hmA]
    simp_all
end

end Rect

section
variable (q : Set.Ici (1 : ℝ))
/-- The critical Fortuin-Kasteleyn parameters `(p_c(q), q)`. -/
def critParams  : FK.Parameters where
  val := q.val
  property := q.property
  edgeProbability := ⟨(rcCriticalParameter q).val, by
    have hq : 0 < q.val := by grind
    exact div_pos (Real.sqrt_pos.2 hq) (by positivity), by
    change Real.sqrt q.val / (1 + Real.sqrt q.val) < 1
    have hq : 0 < q.val := by grind
    exact (div_lt_one (by positivity)).2 (by linarith)⟩

theorem critParams_edge  :
    FK.edgeParameter (critParams q) = Real.sqrt q.val / (1 + Real.sqrt q.val) := rfl

theorem critParams_val  : (critParams q).val = q.val := rfl
end

end PottsDiscontinuity.TorusCrossing
