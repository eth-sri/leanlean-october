import Mathlib.Tactic

import RequestProject.CoreSignedCollapse
import RequestProject.GenusCappedCockcroft
import RequestProject.GenusMarkedSpineFamily
import RequestProject.CockcroftRelatorReindex
import RequestProject.LemmaTerminal

/-! B3 for the actual terminal presentation.  The stable generators are capped,
the original core is retained, and every extra relation is replaced by its actual
named-spine block.  The quotient by the capped core is the wedge of the genuine
capped spines, with the marking cells carrying the opposite orientation.
No collapse map, Hurewicz injection or block Cockcroftness is assumed.
Written proof terms; not compiled in the current proof-first workflow. -/

noncomputable section


namespace FiniteChains.Davis.Genus

open BlockFamily

variable {A K M S : Type} [Fintype A] [Fintype K] [Fintype M] [Fintype S]
  [DecidableEq A] [DecidableEq K] [DecidableEq S]
  (core : M → FreeGroup A) (q : S → ℕ) [∀ s, NeZero (q s)]
  (u : ∀ s, Fin (q s) × Bool → FreeGroup (A ⊕ K))

/-- The original core together with one disk on each stable generator. -/
def terminalSpineCore : M ⊕ K → FreeGroup (A ⊕ K) :=
  corePres core (fun k => FreeGroup.of (Sum.inr k))

variable (s : S)
/-- Each new internal generator belongs to exactly one spine. -/
def terminalSpineGen  (z : SpinePresentationGen (q s)) :
    (A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s)) := Sum.inr ⟨s, z⟩

/-- Actual substituted relators, written out to retain their orientation. -/
def terminalSpineExtra : (Σ s, NamedSpineRel (q s)) →
    FreeGroup ((A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s)))
  | ⟨s, .inl f⟩ => FreeGroup.map (terminalSpineGen (A := A) (K := K) q s)
      (spinePresentation (q s) f)
  | ⟨s, .inr x⟩ => FreeGroup.map Sum.inl (u s x) *
      (FreeGroup.map (terminalSpineGen (A := A) (K := K) q s)
        (spinePresentationMarkedWord (q s) x))⁻¹

/-- Q after capping the stable generators, with caps placed next to the core. -/
def terminalSpinePres  :=
  corePres (terminalSpineCore (K := K) core) (terminalSpineExtra q u)

def terminalNamedWordMap   :=
  (FreeGroup.map (genEmb (Zt := fun s => SpinePresentationGen (q s)) s)).comp
    ((blockSubst (Zt := fun _ : PUnit.{1} => SpinePresentationGen (q s))
      (fun _ => u s) PUnit.unit).comp (FreeGroup.map Sum.swap))

section
omit [Fintype A] [Fintype K] [Fintype S] [DecidableEq A] [DecidableEq K] [DecidableEq S]
theorem terminalNamedWordMap_old (s : S)
    (w : FreeGroup (SpinePresentationGen (q s))) :
    terminalNamedWordMap q u s (FreeGroup.map Sum.inl w) =
      FreeGroup.map (terminalSpineGen (A := A) (K := K) q s) w := by
  have h : (terminalNamedWordMap q u s).comp (FreeGroup.map Sum.inl) =
      FreeGroup.map (terminalSpineGen (A := A) (K := K) q s) := by
    aesop
  exact DFunLike.congr_fun h w

theorem terminalNamedWordMap_mark (s : S) (x : Fin (q s) × Bool) :
    terminalNamedWordMap q u s (FreeGroup.of (Sum.inr x)) =
      FreeGroup.map Sum.inl (u s x) := by
  dsimp [FiniteChains.Davis.Genus.terminalNamedWordMap]
  simp 
  have h : (FreeGroup.map (genEmb (Zt := fun s => SpinePresentationGen (q s)) s)).comp
      (FreeGroup.map (Sum.inl : A ⊕ K → (A ⊕ K) ⊕ SpinePresentationGen (q s))) =
      FreeGroup.map (Sum.inl : A ⊕ K → (A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s))) := by
    apply FreeGroup.ext_hom
    intro a
    simp
  exact DFunLike.congr_fun h (u s x)
end

omit [Fintype A] [Fintype K] [Fintype M] [Fintype S]
  [DecidableEq A] [DecidableEq K] [DecidableEq S] in
/-- The explicit terminal words are exactly the words used in actual B1/B2,
not a different block presentation. -/
theorem terminalSpineExtra_eq_family  (m : NamedSpineRel (q s)) :
    terminalSpineExtra q u ⟨s, m⟩ =
      FreeGroup.map (genEmb (Zt := fun s => SpinePresentationGen (q s)) s)
        (familyFiniteSpineWordBlock q u s m) := by
  change terminalSpineExtra q u ⟨s, m⟩ =
    terminalNamedWordMap q u s (namedSpinePresentation (q s) m)
  cases m with
  | inl f =>
      solve_by_elim [FiniteChains.Davis.Genus.terminalNamedWordMap_old, symm]
  | inr x =>
      change FreeGroup.map Sum.inl (u s x) *
        (FreeGroup.map (terminalSpineGen (A := A) (K := K) q s)
          (spinePresentationMarkedWord (q s) x))⁻¹ =
        terminalNamedWordMap q u s (FreeGroup.of (Sum.inr x) *
          (FreeGroup.map Sum.inl (spinePresentationMarkedWord (q s) x))⁻¹)
      rw [map_mul, map_inv, terminalNamedWordMap_mark, terminalNamedWordMap_old]

/-- The target is the actual wedge of genuine capped-spine presentations. -/
def terminalSpineWedge  :=
  sigmaWedgeRel (fun s => cappedSpinePresentation (q s))

def terminalSpineReverse : (Σ s, NamedSpineRel (q s)) → Bool
  | ⟨_, .inl _⟩ => false
  | ⟨_, .inr _⟩ => true

omit [Fintype A] [Fintype K] [Fintype S] [DecidableEq A] [DecidableEq K] [DecidableEq S] in
theorem terminalSpineGen_drop 
    (w : FreeGroup (SpinePresentationGen (q s))) :
    CoreSignedCollapse.dropCore
      (FreeGroup.map (terminalSpineGen (A := A) (K := K) q s) w) =
      FreeGroup.map (Sigma.mk s) w := by
  have h : (CoreSignedCollapse.dropCore (A := A ⊕ K)).comp
      (FreeGroup.map (terminalSpineGen (A := A) (K := K) q s)) =
      FreeGroup.map (Sigma.mk (β := fun s => SpinePresentationGen (q s)) s) := by
    aesop
  exact DFunLike.congr_fun h w

omit [Fintype A] [Fintype K] [Fintype M] [Fintype S]
  [DecidableEq A] [DecidableEq K] [DecidableEq S] in
theorem terminalSpine_collapse_word (p : Σ s, NamedSpineRel (q s)) :
    CoreSignedCollapse.dropCore (terminalSpineExtra q u p) =
      if terminalSpineReverse q p then (terminalSpineWedge q p)⁻¹
        else terminalSpineWedge q p := by
  obtain ⟨s, f | x⟩ := p
  · solve_by_elim [FiniteChains.Davis.Genus.terminalSpineGen_drop]
  · change CoreSignedCollapse.dropCore
      (FreeGroup.map Sum.inl (u s x) *
        (FreeGroup.map (terminalSpineGen (A := A) (K := K) q s)
          (spinePresentationMarkedWord (q s) x))⁻¹) =
      (FreeGroup.map (Sigma.mk s) (spinePresentationMarkedWord (q s) x))⁻¹
    rw [map_mul, map_inv, CoreSignedCollapse.dropCore_map_inl,
      terminalSpineGen_drop, one_mul]

/-- The presentation just before rule 3: retain the core and replace the
specified products of commutators. -/
def terminalSpineSource  :=
  Sum.elim (fun m => FreeGroup.map Sum.inl (core m))
    (fun s => commWord (u s) (finitePairs (q s)))

/-- The actual simultaneous rule-3 target, before the stable generators are capped. -/
def terminalSpineStructural  :=
  substPresF (terminalSpineSource core q u) (familyFiniteSpineWordBlock q u)

/-- The stable loops capped at the terminal step. -/
def terminalSpineCaps (k : K) :
    FreeGroup ((A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s))) :=
  FreeGroup.of (Sum.inl (Sum.inr k))

/-- The terminal step in the literal `addRels` indexing. -/
def terminalSpineQ  :=
  addRels (terminalSpineStructural core q u) (terminalSpineCaps (A := A) (K := K) q)

/-- Move the stable cap labels next to the core labels, retaining every label. -/
def terminalCapReindex {J : Type} : (M ⊕ J) ⊕ K ≃ (M ⊕ K) ⊕ J where
  toFun
    | .inl (.inl m) => .inl (.inl m)
    | .inl (.inr j) => .inr j
    | .inr k => .inl (.inr k)
  invFun
    | .inl (.inl m) => .inl (.inl m)
    | .inl (.inr k) => .inr k
    | .inr j => .inl (.inr j)
  left_inv := by rintro ((m | j) | k) <;> rfl
  right_inv := by rintro ((m | k) | j) <;> rfl

section
omit [Fintype A] [Fintype K] [Fintype M] [Fintype S]
  [DecidableEq A] [DecidableEq K] [DecidableEq S]
theorem terminalSpineQ_reindex
    (j : (M ⊕ (Σ s, NamedSpineRel (q s))) ⊕ K) :
    terminalSpinePres core q u (terminalCapReindex j) = terminalSpineQ core q u j := by
  rcases j with (m | ⟨s, f⟩) | k
  · rfl
  · exact terminalSpineExtra_eq_family q u s f
  · rfl

/-- The terminal presentation depends only on retained core relators: the
replaced source entries no longer occur in the result of rule 3. -/
theorem terminalSpineQ_eq_actual
    (ρ : M ⊕ S → FreeGroup (A ⊕ K))
    (hcore : ∀ m, ρ (Sum.inl m) = FreeGroup.map Sum.inl (core m)) :
    terminalSpineQ core q u =
      addRels (substPresF ρ (familyFiniteSpineWordBlock q u))
        (terminalSpineCaps (A := A) (K := K) q) := by
  aesop
end

end FiniteChains.Davis.Genus
