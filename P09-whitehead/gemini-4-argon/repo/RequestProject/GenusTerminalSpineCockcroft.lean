module

public import RequestProject.CoreSignedCollapse
public import RequestProject.GenusCappedCockcroft
public import RequestProject.GenusMarkedSpineFamily
public import RequestProject.CockcroftRelatorReindex
public import RequestProject.LemmaTerminal

@[expose] public section

noncomputable section
open scoped Classical

namespace FiniteChains.Davis.Genus

open BlockFamily

variable {A K M S : Type}
  (core : M → FreeGroup A) (q : S → ℕ) [∀ s, NeZero (q s)]
  (u : ∀ s, Fin (q s) × Bool → FreeGroup (A ⊕ K))

def terminalSpineCore : M ⊕ K → FreeGroup (A ⊕ K) :=
  corePres core (fun k => FreeGroup.of (Sum.inr k))

def terminalSpineGen (s : S) (z : SpinePresentationGen (q s)) :
    (A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s)) := Sum.inr ⟨s, z⟩

def terminalSpineExtra : (Σ s, NamedSpineRel (q s)) →
    FreeGroup ((A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s)))
  | ⟨s, .inl f⟩ => FreeGroup.map (terminalSpineGen (A := A) (K := K) q s)
      (spinePresentation (q s) f)
  | ⟨s, .inr x⟩ => FreeGroup.map Sum.inl (u s x) *
      (FreeGroup.map (terminalSpineGen (A := A) (K := K) q s)
        (spinePresentationMarkedWord (q s) x))⁻¹

def terminalSpinePres : (M ⊕ K) ⊕ (Σ s, NamedSpineRel (q s)) →
    FreeGroup ((A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s))) :=
  corePres (terminalSpineCore (K := K) core) (terminalSpineExtra q u)

def terminalNamedWordMap (s : S) : FreeGroup (NamedSpineGen (q s)) →*
    FreeGroup ((A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s))) :=
  (FreeGroup.map (genEmb (Zt := fun s => SpinePresentationGen (q s)) s)).comp
    ((blockSubst (Zt := fun _ : PUnit.{1} => SpinePresentationGen (q s))
      (fun _ => u s) PUnit.unit).comp (FreeGroup.map Sum.swap))

theorem terminalNamedWordMap_old (s : S)
    (w : FreeGroup (SpinePresentationGen (q s))) :
    terminalNamedWordMap q u s (FreeGroup.map Sum.inl w) =
      FreeGroup.map (terminalSpineGen (A := A) (K := K) q s) w := by
  induction w using FreeGroup.induction_on <;> simp_all [terminalNamedWordMap, terminalSpineGen]

theorem terminalNamedWordMap_mark (s : S) (x : Fin (q s) × Bool) :
    terminalNamedWordMap q u s (FreeGroup.of (Sum.inr x)) =
      FreeGroup.map Sum.inl (u s x) := by
  change FreeGroup.map (genEmb (Zt := fun s => SpinePresentationGen (q s)) s)
    (blockSubst (Zt := fun _ : PUnit.{1} => SpinePresentationGen (q s))
      (fun _ => u s) PUnit.unit (FreeGroup.map Sum.swap (FreeGroup.of (Sum.inr x)))) = _
  simp only [FreeGroup.map.of, Sum.swap_inr, blockSubst_of_inl]
  induction u s x using FreeGroup.induction_on <;> simp_all

theorem terminalSpineExtra_eq_family (s : S) (m : NamedSpineRel (q s)) :
    terminalSpineExtra q u ⟨s, m⟩ =
      FreeGroup.map (genEmb (Zt := fun s => SpinePresentationGen (q s)) s)
        (familyFiniteSpineWordBlock q u s m) := by
  change terminalSpineExtra q u ⟨s, m⟩ =
    terminalNamedWordMap q u s (namedSpinePresentation (q s) m)
  cases m with
  | inl f => exact (terminalNamedWordMap_old q u s (spinePresentation (q s) f)).symm
  | inr x =>
      change _ = terminalNamedWordMap q u s (FreeGroup.of (Sum.inr x) *
        (FreeGroup.map Sum.inl (spinePresentationMarkedWord (q s) x))⁻¹)
      rw [map_mul, map_inv, terminalNamedWordMap_mark, terminalNamedWordMap_old]
      rfl

def terminalSpineWedge : (Σ s, NamedSpineRel (q s)) →
    FreeGroup (Σ s, SpinePresentationGen (q s)) :=
  sigmaWedgeRel (fun s => cappedSpinePresentation (q s))

def terminalSpineReverse : (Σ s, NamedSpineRel (q s)) → Bool
  | ⟨_, .inl _⟩ => false
  | ⟨_, .inr _⟩ => true

theorem terminalSpineGen_drop (s : S)
    (w : FreeGroup (SpinePresentationGen (q s))) :
    CoreSignedCollapse.dropCore
      (FreeGroup.map (terminalSpineGen (A := A) (K := K) q s) w) =
      FreeGroup.map (Sigma.mk s) w := by
  induction w using FreeGroup.induction_on <;> simp_all [terminalSpineGen]

theorem terminalSpine_collapse_word (p : Σ s, NamedSpineRel (q s)) :
    CoreSignedCollapse.dropCore (terminalSpineExtra q u p) =
      if terminalSpineReverse q p then (terminalSpineWedge q p)⁻¹
        else terminalSpineWedge q p := by
  obtain ⟨s, f | x⟩ := p
  · exact terminalSpineGen_drop q s (spinePresentation (q s) f)
  · change CoreSignedCollapse.dropCore
      (FreeGroup.map Sum.inl (u s x) *
        (FreeGroup.map (terminalSpineGen (A := A) (K := K) q s)
          (spinePresentationMarkedWord (q s) x))⁻¹) = _
    rw [map_mul, map_inv, CoreSignedCollapse.dropCore_map_inl,
      terminalSpineGen_drop, one_mul]
    rfl

def terminalSpineSource : M ⊕ S → FreeGroup (A ⊕ K) :=
  Sum.elim (fun m => FreeGroup.map Sum.inl (core m))
    (fun s => commWord (u s) (finitePairs (q s)))

def terminalSpineStructural : M ⊕ (Σ s, NamedSpineRel (q s)) →
    FreeGroup ((A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s))) :=
  substPresF (terminalSpineSource core q u) (familyFiniteSpineWordBlock q u)

def terminalSpineCaps (k : K) :
    FreeGroup ((A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s))) :=
  FreeGroup.of (Sum.inl (Sum.inr k))

def terminalSpineQ : (M ⊕ (Σ s, NamedSpineRel (q s))) ⊕ K →
    FreeGroup ((A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s))) :=
  addRels (terminalSpineStructural core q u) (terminalSpineCaps (A := A) (K := K) q)

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

theorem terminalSpineQ_reindex
    (j : (M ⊕ (Σ s, NamedSpineRel (q s))) ⊕ K) :
    terminalSpinePres core q u (terminalCapReindex j) = terminalSpineQ core q u j := by
  rcases j with (m | ⟨s, f⟩) | k
  · rfl
  · exact terminalSpineExtra_eq_family q u s f
  · exact FreeGroup.map.of

theorem terminalSpineQ_eq_actual
    (ρ : M ⊕ S → FreeGroup (A ⊕ K))
    (hcore : ∀ m, ρ (Sum.inl m) = FreeGroup.map Sum.inl (core m)) :
    terminalSpineQ core q u =
      addRels (substPresF ρ (familyFiniteSpineWordBlock q u))
        (terminalSpineCaps (A := A) (K := K) q) := by
  funext j
  rcases j with (m | p) | k
  · exact congrArg (FreeGroup.map Sum.inl) (hcore m).symm
  · rfl
  · rfl
