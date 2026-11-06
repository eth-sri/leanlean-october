module

public import NearlyMinimax.ModelRegularity


@[expose] public section

/-!
The model's ordered coordinate partials are contractions of its genuine
Fréchet derivatives. The finite-order symmetry proof below is adapted from
`RoughRegime/DerivativeSymmetry.lean` in the supplied related formalization.
It uses Schwarz's theorem and adjacent transpositions; no analytic hypothesis
or derivative comparison is assumed.
-/

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators
namespace NearlyMinimax
namespace CoordinatePartialBridge

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Finite continuous differentiability suffices for interchange of the
first two true Fréchet derivative directions. -/
lemma iteratedFDeriv_swap_head {n : ℕ} {f : E → F} {x : E}
    (hf : ContDiffAt ℝ (n+2 : ℕ) f x) (a b : E) (w : Fin n → E) :
    iteratedFDeriv ℝ (n+2) f x (Fin.cons a (Fin.cons b w)) =
      iteratedFDeriv ℝ (n+2) f x (Fin.cons b (Fin.cons a w)) := by
  let g : E → F := fun y => iteratedFDeriv ℝ n f y w
  have hg : ContDiffAt ℝ 2 g x :=
    (ContinuousMultilinearMap.apply ℝ (fun _ => E) F w).contDiff.contDiffAt.comp x
      (hf.iteratedFDeriv_right (by simp [add_comm]))
  have hid (a b : E) : iteratedFDeriv ℝ (n+2) f x (Fin.cons a (Fin.cons b w)) =
      fderiv ℝ (fderiv ℝ g) x a b := by
    rw [(hf.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self (n+1))).iteratedFDeriv_succ_apply_left']
    simp only [Fin.tail_cons,Fin.cons_zero]
    have heq : (fun y => iteratedFDeriv ℝ (n+1) f y (Fin.cons b w)) =ᶠ[𝓝 x]
        fun y => fderiv ℝ g y b := by
      filter_upwards [hf.eventually (by exact Ne.symm (ne_of_beq_false rfl))] with y hy
      have hdy : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) y :=
        hy.differentiableAt_iteratedFDeriv (by exact_mod_cast (show n < n+2 by omega))
      simpa only [Fin.tail_cons,Fin.cons_zero,g] using
        (hdy.iteratedFDeriv_succ_apply_left' (m := Fin.cons b w))
    rw [heq.fderiv_eq]
    have hdg : DifferentiableAt ℝ (fderiv ℝ g) x :=
      (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    rw [fderiv_clm_apply hdg (differentiableAt_const b)]
    simp
  rw [hid a b,hid b a]
  exact (hg.isSymmSndFDerivAt (by simp)) a b



lemma iteratedFDeriv_adjacent_swap (n ) {f : E → F} 
    (hf : ContDiffAt ℝ (n+1 : ℕ) f x) (i : Fin n) (v : Fin (n+1) → E) :
    iteratedFDeriv ℝ (n+1) f x (v ∘ Equiv.swap i.castSucc i.succ) =
      iteratedFDeriv ℝ (n+1) f x v := by
  induction n generalizing x with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · have heq : v ∘ Equiv.swap (0 : Fin (n+2)) 1 =
          Fin.cons (v 1) (Fin.cons (v 0) (Fin.tail (Fin.tail v))) := by
        ext j
        refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
        · simp
        · simp
        · simp only [Function.comp_apply,Equiv.swap_apply_of_ne_of_ne
            (Fin.succ_ne_zero _) (Fin.succ_succ_ne_one _),Fin.cons_succ]
          rfl
      have hdecomp : Fin.cons (v 0) (Fin.cons (v 1) (Fin.tail (Fin.tail v))) = v := by
        rw [show v 1 = Fin.tail v 0 from rfl,Fin.cons_self_tail,Fin.cons_self_tail]
      simpa only [Fin.castSucc_zero,Fin.succ_zero_eq_one,heq,hdecomp] using
        iteratedFDeriv_swap_head hf (v 1) (v 0) (Fin.tail (Fin.tail v))
    · have hzero : (v ∘ Equiv.swap i.succ.castSucc i.succ.succ) 0 = v 0 := by
        simp only [Function.comp_apply,Fin.castSucc_succ,Equiv.swap_apply_of_ne_of_ne
          (Fin.succ_ne_zero _).symm (Fin.succ_ne_zero _).symm]
      have htail : Fin.tail (v ∘ Equiv.swap i.succ.castSucc i.succ.succ) =
          Fin.tail v ∘ Equiv.swap i.castSucc i.succ := by
        funext j
        simp only [Fin.tail,Function.comp_apply,Fin.castSucc_succ]
        rw [← (Fin.succ_injective _).map_swap]
      have hd  :=
        hf.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self (n+1))
      rw [hd.iteratedFDeriv_succ_apply_left',hd.iteratedFDeriv_succ_apply_left',hzero,htail]
      have he : (fun y => iteratedFDeriv ℝ (n+1) f y (Fin.tail v ∘ Equiv.swap i.castSucc i.succ)) =ᶠ[𝓝 x]
          fun y => iteratedFDeriv ℝ (n+1) f y (Fin.tail v) := by
        filter_upwards [hf.eventually (by exact Ne.symm (ne_of_beq_false rfl))] with y hy
        exact ih (hy.of_le (by exact_mod_cast (show n+1 ≤ n+2 by omega))) i (Fin.tail v)
      rw [he.fderiv_eq]



/-- The actual q-th Fréchet derivative of a real C^q function is symmetric.
This uses finite differentiability and genuine adjacent transpositions,
rather than analytic regularity. -/
theorem iteratedFDeriv_comp_perm_finite {q : ℕ} {f : E → F} {x : E}
    (hf : ContDiffAt ℝ q f x) (v : Fin q → E) (σ : Equiv.Perm (Fin q)) :
    iteratedFDeriv ℝ q f x (v ∘ σ) = iteratedFDeriv ℝ q f x v := by
  cases q with
  | zero => congr 1; exact Subsingleton.elim _ _
  | succ n =>
    let S : Submonoid (Equiv.Perm (Fin (n+1))) := {
      carrier := {p | ∀ v : Fin (n+1) → E,
        iteratedFDeriv ℝ (n+1) f x (v ∘ p) = iteratedFDeriv ℝ (n+1) f x v}
      one_mem' := by intro v; rfl
      mul_mem' := by
        intro a b ha hb v
        simpa only [Equiv.Perm.coe_mul,Function.comp_assoc] using (hb (v ∘ a)).trans (ha v) }
    have hgen : Set.range (fun i : Fin n => Equiv.swap i.castSucc i.succ) ⊆ S := by
      rintro p ⟨i,rfl⟩
      exact fun v => iteratedFDeriv_adjacent_swap n hf i v
    have hclosure := Submonoid.closure_le.mpr hgen
    exact hclosure (by rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial) v




end CoordinatePartialBridge

/-- The sorted coordinate word used in the paper's mixed partial definition. -/
def coordinateWord  (γ : Fin d → ℕ) : List (Fin d) :=
  (List.finRange d).flatMap (fun i => List.replicate (γ i) i)

/-- Coordinate directions of a finite word, with the word's actual length. -/
def wordBasis  (w : List (Fin d)) : Fin w.length → Covariate d :=
  fun j => Pi.single (w.get j) 1

/-- Successive coordinate differentiation in the supplied order. -/
def partialWord  (F : Covariate d → ℝ) (w : List (Fin d)) :
    Covariate d → ℝ :=
  w.foldl (fun G i => coordinatePartial i G) F

/-- Left folds add their latest differentiation direction at the head of
the true iterated derivative, hence the reversed word on the right. -/
theorem partialWord_eq_iteratedFDeriv  (U )
    (hU : IsOpen U) (F ) (ℓ : ℕ)
    (hf : ContDiffOn ℝ ℓ F U) (w : List (Fin d)) (hw : w.length ≤ ℓ)
    (x : Covariate d) (hx : x ∈ U) :
    partialWord F w x =
      iteratedFDeriv ℝ w.reverse.length F x (wordBasis w.reverse) := by
  induction w using List.reverseRecOn generalizing x with
  | nil => rfl
  | append_singleton w i ih =>
    have hw' : w.length < ℓ := by simpa using hw
    have he : partialWord F w =ᶠ[𝓝 x]
        fun y => iteratedFDeriv ℝ w.reverse.length F y (wordBasis w.reverse) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact ih (Nat.le_of_lt hw') y hy
    have hd  :=
      (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt_iteratedFDeriv
        (by exact_mod_cast (show w.reverse.length < ℓ by simpa using hw'))
    simp only [partialWord, List.foldl_append, List.foldl_cons, List.foldl_nil,
      coordinatePartial]
    change fderiv ℝ (partialWord F w) x (Pi.single i 1) = _
    rw [he.fderiv_eq]
    have h_wordBasis_cons (i : Fin d) (w : List (Fin d)) : wordBasis (i :: w) = Fin.cons (Pi.single i 1) (wordBasis w) := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [wordBasis, List.get_eq_getElem]
      · simp [wordBasis, List.get_eq_getElem]
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append, h_wordBasis_cons]
    simpa only [List.length_cons, Fin.tail_cons, Fin.cons_zero] using
      (hd.iteratedFDeriv_succ_apply_left' (m := Fin.cons (Pi.single i 1) (wordBasis w.reverse))).symm

theorem coordinateWord_length {d : ℕ} (γ : Fin d → ℕ) :
    (coordinateWord γ).length = ∑ i, γ i := by
  simp only [coordinateWord, List.length_flatMap, List.length_replicate]
  rw [← List.sum_toFinset _ (List.nodup_finRange d)]
  simp

theorem coordinate_counts_sum  (w : List (Fin d)) :
    (∑ i, w.count i) = w.length := by
  simpa using (Multiset.sum_count_eq_card (s := Finset.univ)
    (m := (w : Multiset (Fin d))) (by simp))

theorem iteratedFDeriv_cast_order   (h )
    (F : Covariate d → ℝ) (x : Covariate d) (v : Fin b → Covariate d) :
    iteratedFDeriv ℝ a F x (fun j => v (Fin.cast h j)) =
      iteratedFDeriv ℝ b F x v := by
  cases h
  rfl


/-- Directions corresponding to a mixed partial, in the reverse order
required by its left-fold definition. -/
def multiIndexBasis {d : ℕ} (γ : Fin d → ℕ) : Fin (∑ i, γ i) → Covariate d :=
  fun j => wordBasis (coordinateWord γ).reverse
    (Fin.cast (by rw [List.length_reverse, coordinateWord_length]) j)

theorem multiPartial_eq_iteratedFDeriv  (U )
    (hU : IsOpen U) (F ) (ℓ : ℕ)
    (hf : ContDiffOn ℝ ℓ F U) (γ : Fin d → ℕ) (hγ : (∑ i, γ i) ≤ ℓ)
    (x : Covariate d) (hx : x ∈ U) :
    multiPartial F γ x =
      iteratedFDeriv ℝ (∑ i, γ i) F x (multiIndexBasis γ) := by
  have hpart := partialWord_eq_iteratedFDeriv U hU F ℓ hf (coordinateWord γ)
    (by simpa only [coordinateWord_length] using hγ) x hx
  have hlen : (coordinateWord γ).reverse.length = ∑ i, γ i := by
    rw [List.length_reverse, coordinateWord_length]
  have hder : iteratedFDeriv ℝ (coordinateWord γ).reverse.length F x
      (wordBasis (coordinateWord γ).reverse) =
      iteratedFDeriv ℝ (∑ i, γ i) F x (multiIndexBasis γ) := by
    simpa only [multiIndexBasis, Fin.cast_cast, Fin.cast_eq_self] using
      iteratedFDeriv_cast_order hlen F x (multiIndexBasis γ)
  exact hpart.trans hder

/-- Every ordering of coordinate directions represents the model's mixed
partial with the same multiplicities. -/
theorem iteratedFDeriv_coordinates_eq_multiPartial  (U )
    (hU : IsOpen U) (F : Covariate d → ℝ) (ℓ q : ℕ)
    (hf : ContDiffOn ℝ ℓ F U) (hq : q ≤ ℓ) (σ : Fin q → Fin d)
    (x : Covariate d) (hx : x ∈ U) :
    iteratedFDeriv ℝ q F x (fun j => Pi.single (σ j) 1) =
      multiPartial F (fun i => (List.ofFn σ).count i) x := by
  have h_coordinate_fiber_card {d : ℕ} (σ : Fin q → Fin d) (i : Fin d) : Fintype.card {j : Fin q // σ j = i} = (List.ofFn σ).count i := by
    rw [Fintype.card_subtype, List.ofFn_eq_map]
    change (Finset.univ.filter (fun j => σ j = i)).card = _
    rw [List.count, List.countP_map, List.countP_eq_length_filter]
    have he : ((List.finRange q).filter (fun j => σ j == i)).toFinset =
        Finset.univ.filter (fun j => σ j = i) := by ext; simp
    rw [← he, List.toFinset_card_of_nodup ((List.nodup_finRange q).filter _)]
    rfl
  let γ : Fin d → ℕ := fun i => (List.ofFn σ).count i
  let w := coordinateWord γ
  have hlen : w.reverse.length = q := by
    simp only [List.length_reverse, w, coordinateWord_length, γ]
    rw [coordinate_counts_sum, List.length_ofFn]
  let τ : Fin q → Fin d := fun j => w.reverse.get (Fin.cast hlen.symm j)
  have hlist : List.ofFn τ = w.reverse := by
    dsimp only [τ]
    rw [← List.ofFn_congr hlen w.reverse.get, List.ofFn_get]
  have hcount (i : Fin d) : (List.ofFn σ).count i = (List.ofFn τ).count i := by
    have h_coordinateWord_count (γ : Fin d → ℕ) (i : Fin d) : (coordinateWord γ).count i = γ i := by
      simp only [coordinateWord, List.count_flatMap]
      rw [← List.sum_toFinset _ (List.nodup_finRange d)]
      simp [List.count_replicate]
    rw [hlist, List.count_reverse, show w = coordinateWord γ from rfl, h_coordinateWord_count]
  have h_coordinate_tuple_perm_of_counts : ∃ p : Equiv.Perm (Fin q), τ ∘ p = σ := by
    let e (i : Fin d) : {j : Fin q // σ j = i} ≃ {j : Fin q // τ j = i} :=
      Fintype.equivOfCardEq (by rw [h_coordinate_fiber_card, h_coordinate_fiber_card, hcount i])
    exact ⟨Equiv.ofFiberEquiv e, funext (Equiv.ofFiberEquiv_map e)⟩
  obtain ⟨p, hp⟩ := h_coordinate_tuple_perm_of_counts
  have hsym := CoordinatePartialBridge.iteratedFDeriv_comp_perm_finite
    ((hf.contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast hq))
    (fun j => Pi.single (τ j) ↑1) p
  have hvec : (fun j => (Pi.single (τ j) ↑1 : Covariate d)) ∘ p =
      fun j => (Pi.single (σ j) 1 : Covariate d) := by
    funext j
    simpa only [Function.comp_apply] using
      congrArg (fun i => (Pi.single i 1 : Covariate d)) (congrFun hp j)
  rw [hvec] at hsym
  have hpart := partialWord_eq_iteratedFDeriv U hU F ℓ hf w
    (by simpa only [← hlen, List.length_reverse] using hq) x hx
  have hder : iteratedFDeriv ℝ w.reverse.length F x (wordBasis w.reverse) =
      iteratedFDeriv ℝ q F x (fun j => Pi.single (τ j) 1) := by
    change iteratedFDeriv ℝ w.reverse.length F x
      (fun j => Pi.single (w.reverse.get j) 1) = _
    simpa only [τ, Fin.cast_cast, Fin.cast_eq_self] using
      iteratedFDeriv_cast_order hlen F x (fun j => Pi.single (τ j) 1)
  rw [hder] at hpart
  exact hsym.trans hpart.symm

end NearlyMinimax
