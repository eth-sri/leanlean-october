module
public import ADR11.Nonbinary.FourTaxa
public import ADR11.Identifiability.Lemma5

/-! On five taxa a quartet with pairs A and B measures the sum of their
split lengths (zero for an absent split). The graph on pairs with an edge
for disjointness contains an odd cycle through every vertex, so these sums
determine the individual lengths. -/
@[expose] public section
namespace ADR11.Skeleton
open Finset SpeciesTree
abbrev Pair := Finset (Fin 5)
abbrev SplitTree := SpeciesTree (Fin 5)
private def pairs : Finset Pair := univ.filter (#· = 2)

private theorem data : ∀ A ∈ pairs, ∀ B ∈ pairs, Disjoint A B →
    let S := A ∪ B; let U := traceOn S A
    S.Nonempty ∧ #S = 4 ∧ 2 ≤ #U ∧ 2 ≤ #Uᶜ ∧ U ≠ univ ∧ Uᶜ ≠ univ ∧ A ≠ Bᶜ ∧ Aᶜ ≠ B ∧
      univ.filter (traceOn S · = U) = {A,Bᶜ} ∧ univ.filter (traceOn S · = Uᶜ) = {Aᶜ,B} := by decide +kernel

private theorem adjacent {σ τ : SplitTree} (hd : σ.unrootedDist id = τ.unrootedDist id) {A B : Pair}
    (ha : A ∈ pairs) (hb : B ∈ pairs) (dis : Disjoint A B) :
    σ.unrootedLength A + σ.unrootedLength B = τ.unrootedLength A + τ.unrootedLength B := by
  obtain ⟨hne,h4,h2,h2',hu,hv,ne,ne',key,key'⟩ := data A ha B hb dis
  have eqn := split_eq ((Challenge.proposition11_theorem9_four (by rw [Fintype.card_coe]; exact h4) _ _).mp (unrootedDist_restrict_eq hd _ hne)) h2 h2'
  simp only [← edge_add_compl,SpeciesTree.restrict,pull_edge _ _ _ h2 hu,pull_edge _ _ _ h2' hv,key,key',sum_pair ne,sum_pair ne'] at eqn ⊢
  linarith

private theorem cycles : ∀ A ∈ pairs, ∃ b ∈ pairs, ∃ c ∈ pairs, ∃ d ∈ pairs, ∃ e ∈ pairs,
    Disjoint A b ∧ Disjoint b c ∧ Disjoint c d ∧ Disjoint d e ∧ Disjoint e A := by decide +kernel

theorem splits {σ τ : SplitTree} (h : σ.unrootedDist id = τ.unrootedDist id) (A : Pair) (ha : #A = 2) :
    σ.unrootedLength A = τ.unrootedLength A := by
  have hm : A ∈ pairs := by simp [pairs,ha]
  obtain ⟨b,hb,c,hc,d,hd,e,he,h₁,h₂,h₃,h₄,h₅⟩ := cycles A hm
  linarith [adjacent h hm hb h₁, adjacent h hb hc h₂, adjacent h hc hd h₃, adjacent h hd he h₄, adjacent h he hm h₅]

end ADR11.Skeleton
