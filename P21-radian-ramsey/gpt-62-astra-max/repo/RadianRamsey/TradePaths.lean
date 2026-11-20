module
public import RadianRamsey.Amplify
public import RadianRamsey.TinyPaths

@[expose] public noncomputable section
namespace RadianRamsey
open OAI.EuclideanRamsey

/-! At each level, concatenate all permutations from the preceding level.
Such symmetrized products only depend on the multiset of letters modulo the
corresponding term of the lower central series. -/
private def symprod {G : Type*} [Monoid G] : ℕ → List G → G
  | 0,l => l.prod
  | n+1,l => (l.permutations.map (symprod n)).prod

private lemma symmetric {G : Type*} [Group G] (n : ℕ) {l r : List G} (h : l.Perm r) :
    QuotientGroup.mk' (Lower G n) (symprod n l) = QuotientGroup.mk' (Lower G n) (symprod n r) := by
  induction n generalizing l r with
  | zero => exact QuotientGroup.eq_iff_div_mem.mpr (Subgroup.mem_top _)
  | succ n ih =>
    let q := QuotientGroup.mk' (Lower G (n+1))
    simp only [symprod,map_list_prod,List.map_map]
    apply (h.permutations.map (q ∘ symprod n)).prod_eq'
    apply List.pairwise_map.mpr
    apply List.pairwise_of_forall_mem_list
    intro a ha b hb
    apply commutatorElement_eq_one_iff_commute.mp
    apply (QuotientGroup.eq_one_iff _).mpr
    have hh := QuotientGroup.eq_iff_div_mem.mp (ih ((List.mem_permutations.mp ha).trans (List.mem_permutations.mp hb).symm))
    simpa [commutatorElement_def,div_eq_mul_inv,mul_assoc] using
      Subgroup.commutator_mem_commutator hh (show symprod n b ∈ (⊤ : Subgroup G) from trivial)

variable {z : Fin 9 → ℂ}
private lemma run (n) (l : List Sim) : Path z (fun i => symprod n (l.map (atom ∘ value (z i)))) ((l.length.factorial:ℝ)^n * energy l) := by
  induction n generalizing l with
  | zero => simpa [symprod,energy,Function.comp_def] using Path.list (a:=z) l Path.copy
  | succ n ih =>
    have eq (k) (hk : k ∈ l.permutations) : (k.length.factorial:ℝ)^n * energy k = (l.length.factorial:ℝ)^n*energy l := by
      have h := List.mem_permutations.mp hk
      simp [h.length_eq,energy,(h.map _).sum_eq]
    simpa [symprod, ← List.map_permutations, List.map_congr_left eq, List.length_permutations, pow_succ', mul_assoc, Function.comp_def] using Path.list l.permutations ih

/-- Arbitrarily different squared lengths at the very same word endpoint. -/
theorem equal_paths (hz : AlgebraicCircle z) : Wide z := by
  intro r hr
  obtain ⟨P,Q,ht,he⟩ := exists_trade hz
  obtain ⟨A,B,h,hlt⟩ := amplify ht he r hr
  let W (A : Rows) i := symprod 8 (A.toList.map (atom ∘ value (z i)))
  have perm (i) : (A.toList.map (value (z i))).Perm (B.toList.map (value (z i))) :=
    Multiset.coe_eq_coe.mp (by simpa [← Multiset.map_coe] using h i)
  have hd (i) : (W A i)⁻¹ * W B i ∈ Lower LetterGroup 8 := QuotientGroup.eq.mp (symmetric 8 (by simpa using (perm i).map atom))
  let m : ℝ := A.card.factorial^8
  obtain ⟨x,y,hy,eq⟩ := deep_changes hz.inj hd 1 (m*(r*energy A-energy B)) (by positivity)
  have e : W A*x.w = W B*y.w := by ext i; simp [eq i (by simp),mul_assoc]
  refine ⟨_,_,_,(run (z:=z) 8 A.toList).mul x.path,e ▸ (run (z:=z) 8 B.toList).mul y.path,?_⟩
  simp [show B.card=A.card by simpa using (perm 0).length_eq.symm]
  linarith [mul_nonneg hr.le x.path.nonneg,x.path.nonneg]

end RadianRamsey
