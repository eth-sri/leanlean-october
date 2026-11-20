module
public import ADR11.MSC.Basic
public import ADR11.Computation.Program

/-! Correctness of polynomial evaluation on the actual clades and forests.
Only the clade schedule is ordered: all sums over mergers are symmetric. -/
@[expose] public section
namespace ADR11.Computation.Sparse
open Finset Real Matrix
variable {n : ℕ}

noncomputable def mon (z : ℕ → ℝ) (k : Key) := (k.map z).prod
noncomputable def eval (z : ℕ → ℝ) : Poly →+ ℝ := Multiset.sumAddMonoidHom.comp
  (Multiset.mapAddMonoidHom fun (q,k) => q * mon z k)

variable (z : ℕ → ℝ)
@[simp] theorem eval_cons (t : ℚ × Key) (P : Poly) : eval z (t ::ₘ P) = t.1 * mon z t.2 + eval z P := by simp [eval]
@[simp] theorem eval_single (q : ℚ) (k : Key) : eval z {(q,k)} = q * mon z k := by simp [eval]
@[simp] theorem eval_shift (q : ℚ) (k : Key) (P : Poly) : eval z (shift q k P) = q * mon z k * eval z P := by
  simp [eval,shift,mon,Multiset.map_map,← Multiset.sum_map_mul_left,mul_assoc,mul_left_comm,mul_comm]
@[simp] theorem eval_weight (P Q : Poly) : eval z (weight P Q) = eval z P * eval z Q := by
  change eval z (P.map (fun (q,k) => shift q k Q)).sum = _
  rw [map_multiset_sum,Multiset.map_map]; simp only [Function.comp_def,eval_shift]
  exact Multiset.sum_map_mul_right

private theorem eval_paths (K F : Family n) (u : Query n) (hu : ∀ G, ¬G ⊆ K → u G = 0) (k : ℕ) (v : Fin (k+1) → Poly) :
    eval z (paths K F k v u) = evolve (eval z ∘ u) k F (fun i => eval z (v i)) := by
  induction k generalizing F with
  | zero => simp [paths,mul_comm]
  | succ k ih => by_cases hf : F ⊆ K
                 · simp [paths,hf,ih,diff,atIndex,sub_eq_add_neg,mul_comm,mul_add,mon,Function.comp_def]
                 · simp only [paths,ite_eq_right hf,map_zero]; symm; apply evolve_off (P := fun G => ¬G ⊆ K) _ _ _ hf
                   · intro H hn G hg; obtain ⟨P,_,rfl⟩ := mem_image.mp hg; exact fun sub => hn ((subset_insert ..).trans sub)
                   · intro G hn; simp [hu G hn]

noncomputable abbrev coords (len : Finset (Fin n) → ℝ) := fun c => exp (-len (decC n c))

@[simp] theorem dec_code (A : Clade n) : decC n (code A) = A := by
  simp only [decC,code,Equiv.apply_symm_apply]; ext; simp [Fin.val_inj]

@[simp] theorem mem_clades (A : Clade n) : A ∈ clades n :=
  List.mem_map.mpr ⟨(List.finRange n).filter (· ∈ A),List.mem_sublists.mpr List.filter_sublist,by ext; simp⟩

private theorem eval_advance (K : Family n) (len : Clade n → ℝ) (A : Clade n) {F : Family n} (hf : IsForest F) (u : Query n) (hu : A = univ → ∀ G, ¬G ⊆ K → u G = 0) :
    eval (coords len) (advance K A F u) = dotProduct (populationKernel len A F) (eval (coords len) ∘ u) := by
  change _ = (populationKernel len A *ᵥ _) F
  rw [population_evolve _ hf,advance,eval_paths _ _ _ _ (by split_ifs with h; exact hu h; simp)]; congr 1
  ext i; by_cases ha : A = univ <;> simp [value,timesAt,ha,infiniteTime,finiteTime,coords,mon,apply_ite,← exp_nat_mul]

private theorem eval_gather (μ : Clade n → Query n → Poly) (p : Finset (Fin n) → Law (Family n))
    (l : List (Clade n)) (hn : l.Nodup) (h : ∀ b ∈ l, ∀ u, eval z (μ b u) = dotProduct (p b) (eval z ∘ u)) (S u) :
    eval z (gather μ l S u) = dotProduct (Law.combine l.toFinset p S) (eval z ∘ u) := by
  induction l generalizing S with
  | nil => simp [gather]
  | cons b l ih =>
    obtain ⟨hb,hn⟩ := List.nodup_cons.mp hn
    rw [gather,h b List.mem_cons_self,List.toFinset_cons,Law.combine_insert _ _ _ _ (by simpa using hb),Law.expect_bind]
    congr 1; funext G; apply ih hn (fun c hc => h c (by simp [hc]))

private theorem eval_tree (σ : SpeciesTree (Fin n)) (K : Family n) (fuel : ℕ) (A : Clade n) (hf : #A < fuel) (u : Query n) (hu : A = univ → ∀ G, ¬G ⊆ K → u G = 0) :
    eval (coords σ.length) (evalTree σ.clusters K fuel A u) = dotProduct (σ.leave id A) (eval (coords σ.length) ∘ u) := by
  induction fuel generalizing A u with
  | zero => omega
  | succ k ih =>
    have eqn : (schedule (σ.kids A)).toFinset = σ.kids A := by ext; simp [schedule]
    have sub (b) (hb : b ∈ schedule (σ.kids A)) := child_lt (eqn ▸ List.mem_toFinset.mpr hb)
    rw [evalTree,eval_gather _ _ (σ.leave id) _ (show (schedule (σ.kids A)).Nodup from List.nodup_dedup _) (fun b hb v => ih b (by have := card_lt_card (sub b hb); omega) v fun e => (((sub b hb).trans_le (subset_univ _)).ne e).elim),eqn,σ.leave_eq,Law.expect_bind _ (populationKernel σ.length A)]
    exact Law.expect_congr fun F hz => eval_advance K σ.length _ ((σ.valid_enter id _).support hz).1 u hu

theorem eval_observed (σ : SpeciesTree (Fin n)) (T : Family n) : eval (coords σ.length) (observed σ.clusters T) = σ.unrootedDist id T := by
  rw [observed,eval_tree σ _ _ _ (by simp)]
  · simp [SpeciesTree.unrootedDist,SpeciesTree.rootedDist,dotProduct,mon,apply_ite,SpeciesTree.leave]
  · rintro _ F hn; split <;> grind [mem_unroot]

end ADR11.Computation.Sparse
