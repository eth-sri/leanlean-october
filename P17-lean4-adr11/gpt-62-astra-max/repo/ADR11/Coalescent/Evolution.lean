module
public import ADR11.Coalescent.Forest

/-! Newton divided differences give a short functional calculus for the
triangular Kingman generator. At a forest with k+1 roots its diagonal
entry is -rate k and each possible merge goes down exactly one level.
A function of the generator is therefore evaluated by taking one divided
difference at each merge. This same recursion applies to matrix powers,
finite times, and the infinite-time projection. -/
@[expose] public section
namespace ADR11
open Finset Matrix Real Filter Topology
variable {L : Type*} [DecidableEq L] [Fintype L]

def level (F : Clusters L) := #(roots F) - 1

private theorem root_count {F : Clusters L} {k} (h : level F = k+1) : #(roots F) = k+2 := by grind [level]

private theorem down {F G : Clusters L} (hf : IsForest F) {k} (hk : level F = k+1) (hm : G ∈ merges F) : level G = k := by
  have := (hf.of_mem_merges hm).2.1; have := root_count hk; unfold level; omega

private theorem increasing : StrictMono rate := strictMono_nat_of_lt_succ fun k => by
  grind [rate]

abbrev Values (k : ℕ) := Fin (k+1) → ℝ
abbrev atIndex {k : ℕ} (i : Fin (k+1)) : Values k →L[ℝ] ℝ := ContinuousLinearMap.proj i
noncomputable def diff (k : ℕ) : Values (k+1) →L[ℝ] Values k :=
  .pi fun i => ((rate (k+1) : ℝ) - rate i)⁻¹ •
    (atIndex (k := k+1) i.castSucc - atIndex (Fin.last (k+1)))

noncomputable def evolve (f : Clusters L → ℝ) : (k : ℕ) → Clusters L → Values k →L[ℝ] ℝ
  | 0,F => f F • ContinuousLinearMap.proj 0
  | k+1,F => f F • ContinuousLinearMap.proj (Fin.last (k+1)) + ∑ G ∈ merges F, (evolve f k G).comp (diff k)

@[simp] theorem evolve_zero (f : Clusters L → ℝ) (F a) : evolve f 0 F a = f F * a 0 := rfl
@[simp] theorem evolve_succ (f : Clusters L → ℝ) (k F a) : evolve f (k+1) F a =
    f F * a (Fin.last _) + ∑ G ∈ merges F, evolve f k G (diff k a) := by simp [evolve]

def power (n k : ℕ) : Values k := fun i => (-(rate i : ℝ))^n

private theorem diff_power (n k : ℕ) : diff k (power (n+1) (k+1)) = power n k - (rate (k+1) : ℝ) • diff k (power n (k+1)) := by
  funext i
  have hn : (rate (k+1) : ℝ) ≠ rate i := by exact_mod_cast (increasing i.isLt).ne'
  simp [diff,atIndex,power,pow_succ]; field_simp; ring

private theorem pow_evolve (f : Clusters L → ℝ) (n : ℕ) {F : Clusters L} (hf : IsForest F) (k : ℕ) (hk : level F = k) :
    ((kingmanGenerator ^ n) *ᵥ f) F = evolve f k F (power n k) := by
  induction n generalizing F k with
  | zero =>
    have hz (k) : diff k (power 0 (k+1)) = 0 := by ext; simp [diff,atIndex,power]
    cases k <;> simp [hz,power]
  | succ n ih =>
    rw [pow_succ',← mulVec_mulVec]; change ∑ G, kingmanGenerator F G * _ = _; rw [hf.sum_kingmanGenerator_mul]
    unfold level at hk
    cases k with
    | zero =>
      have hz := Nat.choose_eq_zero_of_lt (show #(roots F) < 2 by omega)
      simp [merges_eq_empty_of_card_roots_le_one (by omega : #(roots F) ≤ 1),hz,power,rate]
    | succ k =>
      have hc := root_count hk
      rw [ih hf _ hk,Finset.sum_congr rfl fun G hg => ih (hf.of_mem_merges hg).1 _ (down hf hk hg)]
      simp only [evolve_succ,diff_power,map_sub,map_smul,smul_eq_mul,sum_sub_distrib,← mul_sum,hc]
      simp [power,rate,pow_succ]; ring

section MatrixSeries
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open scoped Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false in
theorem hasSum_exp_entry (A : Matrix ι ι ℝ) (i j : ι) :
    HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ * (A ^ n) i j) (NormedSpace.exp A i j) := by
  simpa using Pi.hasSum.mp (Pi.hasSum.mp (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A) i) j

theorem hasSum_exp_vec (A : Matrix ι ι ℝ) (t : ℝ) (v : ι → ℝ) (i : ι) :
    HasSum (fun n : ℕ => t^n / n.factorial * ((A^n) *ᵥ v) i) ((NormedSpace.exp (t • A) *ᵥ v) i) := by
  convert hasSum_sum (s := univ) (fun j _ => (hasSum_exp_entry (t • A) i j).mul_right (v j)) using 1
  · funext n; simp [mulVec,dotProduct,mul_sum,smul_pow,div_eq_mul_inv,mul_comm,mul_assoc,mul_left_comm]
  · rfl
end MatrixSeries

noncomputable def finiteTime (t : ℝ) (k : ℕ) : Values k := fun i => exp (-(rate i : ℝ) * t)
def infiniteTime (k : ℕ) : Values k := fun i => if i.val = 0 then 1 else 0

theorem transition_evolve (f : Clusters L → ℝ) {F : Clusters L} (hf : IsForest F) (t : ℝ) :
    (kingmanTransition t *ᵥ f) F = evolve f (level F) F (finiteTime t _) := by
  have series (k) : HasSum (fun n : ℕ => (t^n / n.factorial : ℝ) • power n k) (finiteTime t k) := by
    apply Pi.hasSum.mpr; intro i
    convert NormedSpace.expSeries_div_hasSum_exp (-(rate i : ℝ) * t) using 1
    · funext n; simp [power]; ring
    · rw [finiteTime,Real.exp_eq_exp_ℝ]
  refine (hasSum_exp_vec _ t f F).unique ?_
  simpa only [pow_evolve f _ hf _ rfl,map_smul,smul_eq_mul] using (evolve f _ F).hasSum (series _)

private theorem limiting (k) : Tendsto (fun t => finiteTime t k) atTop (𝓝 (infiniteTime k)) := by
  apply tendsto_pi_nhds.mpr; intro i
  by_cases h : i.val = 0
  · simp [finiteTime,infiniteTime,h,rate]
  · simp only [finiteTime,infiniteTime,h,ite_false]
    apply tendsto_exp_comp_nhds_zero.mpr
    have hp : 0 < (rate i : ℝ) := by exact_mod_cast Nat.choose_pos (show 2 ≤ i.val+1 by omega)
    exact Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr hp) tendsto_id

private theorem tendsto_vec (f : Clusters L → ℝ) {F : Clusters L} (hf : IsForest F) :
    Tendsto (fun t => (kingmanTransition t *ᵥ f) F) atTop (𝓝 (evolve f (level F) F (infiniteTime _))) := by
  simp_rw [transition_evolve f hf]; exact (evolve f _ F).continuous.continuousAt.tendsto.comp (limiting _)

theorem tendsto_kingmanTransition {F : Clusters L} (hf : IsForest F) (G : Clusters L) :
    Tendsto (fun t => kingmanTransition t F G) atTop (𝓝 (kingmanAbsorption F G)) := by
  have h := tendsto_vec (Pi.single G 1) hf
  simp only [mulVec_single_one,col_apply] at h
  rwa [show kingmanAbsorption F G = _ from h.limUnder_eq]

theorem absorption_evolve (f : Clusters L → ℝ) {F : Clusters L} (hf : IsForest F) :
    (kingmanAbsorption *ᵥ f) F = evolve f (level F) F (infiniteTime _) :=
  tendsto_nhds_unique (tendsto_finsetSum _ fun G _ => (tendsto_kingmanTransition hf G).mul_const (f G)) (tendsto_vec f hf)

theorem kingmanTransition_add (s t : ℝ) : kingmanTransition (L := L) (s+t) = kingmanTransition s * kingmanTransition t := by
  unfold kingmanTransition; rw [add_smul]; exact Matrix.exp_add_of_commute _ _ (((Commute.refl _).smul_left s).smul_right t)

open scoped Matrix.Norms.Operator in
set_option backward.isDefEq.respectTransparency false in
theorem kingmanTransition_nonneg {t : ℝ} (ht : 0 ≤ t) (F G : Clusters L) : 0 ≤ kingmanTransition t F G := by
  let Q := kingmanGenerator (L := L)
  let c := ∑ H : Clusters L, (((#(roots H)).choose 2 : ℕ) : ℝ)
  let P := Q + c • 1
  have hp (H K) : 0 ≤ P H K := by
    have hc : ((#(roots H)).choose 2 : ℝ) ≤ c := single_le_sum (fun H _ => Nat.cast_nonneg ((#(roots H)).choose 2)) (mem_univ H)
    simp only [P,Q,kingmanGenerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
    by_cases e : K = H
    · aesop
    · simp [e,Ne.symm e]; split <;> norm_num
  have scalar (r : ℝ) : NormedSpace.exp (r • (1 : Matrix (Clusters L) (Clusters L) ℝ)) = exp r • 1 := by
    simpa only [Algebra.algebraMap_eq_smul_one,Real.exp_eq_exp_ℝ] using
      (NormedSpace.algebraMap_exp_comm (𝔸 := Matrix (Clusters L) (Clusters L) ℝ) r).symm
  have eqn : t • Q = t • P + (-(t*c)) • 1 := by simp [P,smul_add,smul_smul,add_assoc]
  change 0 ≤ NormedSpace.exp (t • Q) F G
  rw [eqn, Matrix.exp_add_of_commute _ _ ((Commute.one_right _).smul_right _),scalar,mul_smul_comm,mul_one,Matrix.smul_apply]
  apply mul_nonneg (exp_pos _).le
  apply (hasSum_exp_entry _ F G).nonneg; intro n
  rw [smul_pow,Matrix.smul_apply,smul_eq_mul]; exact mul_nonneg (by positivity) (mul_nonneg (pow_nonneg ht n) (Matrix.pow_apply_nonneg hp ..))

variable {X : Type*} [Fintype X] [DecidableEq X]
noncomputable def timesAt (len : Finset X → ℝ) (A : Finset X) (k : ℕ) := if A = univ then infiniteTime k else finiteTime (len A) k

theorem population_evolve (f : Clusters L → ℝ) {F : Clusters L} (hf : IsForest F) (len : Finset X → ℝ) (A : Finset X) :
    (populationKernel len A *ᵥ f) F = evolve f (level F) F (timesAt len A _) := by
  grind [timesAt,populationKernel,transition_evolve,absorption_evolve]

@[simp] theorem times_zero (len : Finset X → ℝ) (A : Finset X) (k : ℕ) : timesAt len A k 0 = 1 := by
  unfold timesAt; split <;> simp [infiniteTime,finiteTime,rate]

private theorem mass {F : Clusters L} (hf : IsForest F) (k : ℕ) (hk : level F = k) (v : Values k) :
    evolve 1 k F v = v 0 := by
  induction k generalizing F with
  | zero => simp
  | succ k ih =>
    have hc := root_count hk
    rw [evolve_succ,sum_congr rfl fun G hg => ih (hf.of_mem_merges hg).1 (down hf hk hg) _]
    simp [diff,atIndex,hf.card_merges,hc,rate]
    have hp : (0 : ℝ) < (k+2).choose 2 := by exact_mod_cast Nat.choose_pos (show 2 ≤ k+2 by omega)
    field_simp; ring

abbrev Above (F G : Clusters L) := IsForest G ∧ F ⊆ G ∧ lineages G = lineages F

/-- A test vanishing on a merge-closed set contributes zero at every level. -/
theorem evolve_off {f : Clusters L → ℝ} {P : Clusters L → Prop} (closed : ∀ F, P F → ∀ G ∈ merges F, P G)
    (zero : ∀ F, P F → f F = 0) (k) {F} (hp : P F) (v) : evolve f k F v = 0 := by
  induction k generalizing F with
  | zero => simp [zero _ hp]
  | succ k ih => simp [zero _ hp,sum_eq_zero fun G hg => ih (closed _ hp G hg) _]

private theorem support {F G : Clusters L} (hf : IsForest F) (k : ℕ) (v : Values k) (h : evolve (Pi.single G 1) k F v ≠ 0) : Above F G := by
  contrapose! h; apply evolve_off (P := Above F) _ _ k ⟨hf,subset_rfl,rfl⟩
  · rintro H ⟨hh,le,e⟩ J hj; obtain ⟨hj,_,sub,eqn⟩ := hh.of_mem_merges hj
    exact ⟨hj,le.trans sub.subset,eqn.trans e⟩
  · intro H ha; exact Pi.single_eq_of_ne (by grind) _

theorem populationKernel_support {len : Finset X → ℝ} {A : Finset X} {F G : Clusters L} (hf : IsForest F) (h : populationKernel len A F G ≠ 0) : Above F G := by
  apply support hf (level F) (timesAt len A _); rw [← population_evolve _ hf,mulVec_single_one]; exact h

theorem populationKernel_nonneg {len : Finset X → ℝ} {A : Finset X} (ht : A ≠ univ → 0 ≤ len A) {F : Clusters L} (hf : IsForest F) (G : Clusters L) : 0 ≤ populationKernel len A F G := by
  unfold populationKernel; split
  · exact ge_of_tendsto (tendsto_kingmanTransition hf G) ((eventually_ge_atTop (0 : ℝ)).mono fun t h => kingmanTransition_nonneg h F G)
  · exact kingmanTransition_nonneg (ht ‹_›) F G

theorem populationKernel_sum (len : Finset X → ℝ) (A : Finset X) {F : Clusters L} (hf : IsForest F) : ∑ G, populationKernel len A F G = 1 := by
  simpa [mulVec,dotProduct,mass hf _ rfl] using population_evolve 1 hf len A

theorem kingmanTransition_mul_kingmanAbsorption {F : Clusters L} (hf : IsForest F) (t : ℝ) (G : Clusters L) :
    ∑ H, kingmanTransition t F H * kingmanAbsorption H G = kingmanAbsorption F G := by
  have h := (tendsto_kingmanTransition hf G).comp (tendsto_atTop_add_const_left atTop t tendsto_id)
  simp only [Function.comp_def,kingmanTransition_add,Matrix.mul_apply,id_eq] at h
  apply tendsto_nhds_unique _ h; apply tendsto_finsetSum; intro H _
  by_cases hz : kingmanTransition t F H = 0; · simp [hz]
  have hh : IsForest H := (support hf _ (finiteTime t _) (by rwa [← transition_evolve _ hf,mulVec_single_one])).1
  exact (tendsto_kingmanTransition hh G).const_mul _

end ADR11
