import RequestProject.GenusTerminalSpineCockcroft
import RequestProject.CoreSignedCollapseFinsupp
import RequestProject.WedgeCockcroftFinsupp
import RequestProject.TerminalFinsupp
import RequestProject.CockcroftRelatorReindexFinsupp
import RequestProject.GenusStructuralFinsupp
import RequestProject.RelativeNormalizedWords
import RequestProject.Tac


/-! The terminal fixed-core conclusions for arbitrary presentations and block
families.  No generator, relator, core or family is assumed finite.  The actual
genus blocks themselves are finite.  All chains have finite support.
Pending Lean verification. -/

noncomputable section
open scoped Classical

namespace FiniteChains.Davis.Genus

open BlockFamily

variable {A K M S : Type} [DecidableEq A] [DecidableEq K] [DecidableEq S]
  (core : M → FreeGroup A) (q : S → ℕ) [∀ s, NeZero (q s)]
  (u : ∀ s, Fin (q s) × Bool → FreeGroup (A ⊕ K))

/-- Every stable cap is a distinct unit row in the exponent-sum matrix. -/
theorem terminalSpineCore_expMatrix_cap c k :
    expMatrix (terminalSpineCore (K := K) core) c (Sum.inr k) = c (Sum.inr k) := by
  lin_ind c j n =>
      cases j with
      | inl m =>
          have hz : expEntry (terminalSpineCore (K := K) core)
              (Sum.inr k) (Sum.inl m) = 0 := by
            rw [← augPres_foxMatrixPres]
            change augPres (corePres core (fun k => FreeGroup.of (Sum.inr k)))
              (foxMatrixPres _
                (Sum.inr k) (Sum.inl m)) = 0
            rw [CoreSignedCollapse.matrix_core, map_zero]
          simp [expMatrix, Finsupp.linearCombination_single,
            Finsupp.smul_apply, smul_eq_mul, expVec_apply]
          aesop
      | inr l =>
          simp [expMatrix, terminalSpineCore, corePres, expVec_apply, expSum_of,
            Finsupp.single_apply, eq_comm, mul_ite]

/-- Adding arbitrarily many stable generator-cap pairs preserves the genuine
supported exponent-sum injection of the original core. -/
theorem terminalSpineCore_expMatrix_injective
    (hcore : Function.Injective (expMatrix core)) :
    Function.Injective (expMatrix (terminalSpineCore (K := K) core)) := by
  intro c d h
  have hz : expMatrix (terminalSpineCore (K := K) core) (c - d) = 0 := by
    simp_all
  have hcap (k : K) : (c - d) (Sum.inr k) = 0 := by
    rw [← terminalSpineCore_expMatrix_cap core _ k, hz]
    rfl
  exact sub_eq_zero.mp (corePres_expMatrix_kernel_reflect core
    _ hcore _ hz hcap)

theorem terminalSpineWedge_fsIsCockcroft : FSIsCockcroft (terminalSpineWedge q) :=
  fsIsCockcroft_sigmaWedgeRel _
    (fun s => cappedSpinePresentation_isCockcroft _)

theorem terminalSpine_fsIsCockcroft (hcore : Function.Injective (expMatrix core)) :
    FSIsCockcroft (terminalSpinePres core q u) :=
  CoreSignedCollapse.fsIsCockcroft _ _
    _ _ (terminalSpine_collapse_word q u)
    (terminalSpineCore_expMatrix_injective core hcore) (terminalSpineWedge_fsIsCockcroft q)

/-- Actual addRels ordering, with no finiteness assumptions. -/
theorem terminalSpineQ_fsIsCockcroft (hcore : Function.Injective (expMatrix core)) :
    FSIsCockcroft (terminalSpineQ core q u) :=
  RelatorReindex.fsIsCockcroft_of _ _
    terminalCapReindex (terminalSpineQ_reindex core q u)
    (terminalSpine_fsIsCockcroft core q u hcore)

theorem actualTerminalSpineFS_isCockcroft
    ρ
    (hretained : ∀ m, ρ (Sum.inl m) = FreeGroup.map Sum.inl (core m))
    (hcore : Function.Injective (expMatrix core)) :
    FSIsCockcroft (addRels (substPresF ρ (familyFiniteSpineWordBlock q u))
      (terminalSpineCaps (A := A) (K := K) q)) := by
  rw [← terminalSpineQ_eq_actual core q u ρ hretained]
  exact terminalSpineQ_fsIsCockcroft core q u hcore

variable (ρ : M ⊕ S → FreeGroup (A ⊕ K))
  (hrho : ∀ s, ρ (Sum.inr s) = commWord (u s) (finitePairs (q s)))

/-- The actual structural map with the equality instances of the terminal presentation. -/
def terminalStructuralMapFS :
    PresMorFS ρ (substPresF ρ (familyFiniteSpineWordBlock q u)) := by
  let dSrc : DecidableEq (A ⊕ K) := inferInstance
  let dTgt : DecidableEq ((A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s))) := inferInstance
  letI : DecidableEq S := Classical.decEq _
  let dFamilyTgt : DecidableEq ((A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s))) :=
    @instDecidableEqSum _ _ (Classical.decEq _) inferInstance
  exact @PresMorFS.redecide _ _ _ _ (Classical.decEq _) dFamilyTgt _ _
    (finiteSpineFamilyStructuralMap ρ q u hrho) dSrc dTgt

theorem terminalStructuralMapFS_generates : FSGenerates (terminalStructuralMapFS q u ρ hrho) := by
  let dSrc : DecidableEq (A ⊕ K) := inferInstance
  let dTgt : DecidableEq ((A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s))) := inferInstance
  letI : DecidableEq S := Classical.decEq _
  let dFamilyTgt : DecidableEq ((A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s))) :=
    @instDecidableEqSum _ _ (Classical.decEq _) inferInstance
  exact @FSGenerates.redecide _ _ _ _ (Classical.decEq _) dFamilyTgt _ _ _
    (finiteSpineFamilyStructuralMap_generates ρ q u hrho) dSrc dTgt

/-- The actual terminal inclusion, with supported chain modules. -/
def actualTerminalSpineMorFS :=
  addRelsMorFS (substPresF ρ (familyFiniteSpineWordBlock q u))
    (terminalSpineCaps (A := A) (K := K) q)

theorem actualTerminalSpineFS_composite_trivial
    (hcoreTriv : ∀ a,
      (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup ρ) = 1) :
    ∀ g, ((actualTerminalSpineMorFS q u ρ).comp
      (terminalStructuralMapFS q u ρ hrho)).hom g = 1 := by
  apply hom_eq_one_of_gens
  rintro (a | k)
  · grind
  · apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.subset_normalClosure ⟨Sum.inr k, rfl⟩

include hrho in
theorem actualTerminalSpineFS_cells_zero (hP : FSIsCockcroft ρ)
    (hcoreTriv : ∀ a : A,
      (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup ρ) = 1)
    (v : (M ⊕ (Σ s, NamedSpineRel (q s))) →₀
      MonoidAlgebra ℤ (PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u))))
    (hv : FSIsFoxCycle (substPresF ρ (familyFiniteSpineWordBlock q u)) v) :
    (actualTerminalSpineMorFS q u ρ).cells v = 0 := by
  apply fsCells_eq_zero_of_generates_comp (terminalStructuralMapFS q u ρ hrho)
    (actualTerminalSpineMorFS q u ρ)
    (terminalStructuralMapFS_generates q u ρ hrho) ?_ hv
  intro y hy
  exact fsCells_eq_zero_of_isCockcroft_of_hom_trivial
    _
    hP (actualTerminalSpineFS_composite_trivial q u ρ hrho hcoreTriv) y hy

include hrho in
/-- The arbitrary-core terminal step of Lemma 3.10.  The only core H2
assumption is injectivity of expMatrix on actual finitely supported chains.
Both the terminal Cockcroft and zero-pi2 conclusions are proved. -/
theorem actualTerminalSpineFS_conclusions
    (hretained : ∀ m, ρ (Sum.inl m) = FreeGroup.map Sum.inl (core m))
    (hcore : Function.Injective (expMatrix core)) (hP : FSIsCockcroft ρ)
    (hcoreTriv : ∀ a : A,
      (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup ρ) = 1) :
    FSIsCockcroft (addRels (substPresF ρ (familyFiniteSpineWordBlock q u))
        (terminalSpineCaps (A := A) (K := K) q)) ∧
    (∀ v, FSIsFoxCycle (substPresF ρ (familyFiniteSpineWordBlock q u)) v →
      (actualTerminalSpineMorFS q u ρ).cells v = 0) :=
  ⟨actualTerminalSpineFS_isCockcroft core q u ρ hretained hcore,
    (actualTerminalSpineFS_cells_zero q u ρ hrho hP hcoreTriv)⟩
