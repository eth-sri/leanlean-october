module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightDifferentialWords.CoordinateJetEstimates

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPContRightJets

open KPContLocalNorm
open scoped Classical Topology ContDiff BigOperators

theorem coordinateList_smooth {n : ℕ} {U : Set (Space n)} (hU : IsOpen U)
    (u : Space n → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (l : List (Fin n)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (coordinateDerivativeList l u) U := by
  induction l with
  | nil => exact hu
  | cons i l ih =>
    exact (ih.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

theorem euclidean_vector_expansion {n : ℕ} (v : Space n) :
    v = ∑ i : Fin n, (v i) • EuclideanSpace.single i 1 := by
  apply PiLp.ext
  intro j
  simp [EuclideanSpace.single, Pi.single_apply, Finset.sum_ite_eq']

private lemma pull_deriv {n m : ℕ} {U : Set (Space m)} {V : Set (Space n)}
    (hU : IsOpen U) (hV : IsOpen V) (π : Space m → Space n)
    (hπ : ContDiffOn ℝ (⊤ : ℕ∞) π U) (himage : π '' U ⊆ V)
    (u : Space n → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u V)
    (l : List (Fin n)) (g : Space m) (hg : g ∈ U) (v : Space m) :
    fderiv ℝ (fun x => coordinateDerivativeList l u (π x)) g v =
      ∑ i : Fin n, ((fderiv ℝ π g v) i : ℂ) * coordinateDerivativeList (i :: l) u (π g) := by
  have hgV := himage ⟨g, hg, rfl⟩
  have hdπ := (hπ.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
  have hdu := ((coordinateList_smooth hV u hu l).differentiableOn (by simp)).differentiableAt (hV.mem_nhds hgV)
  change fderiv ℝ (coordinateDerivativeList l u ∘ π) g v = _
  rw [fderiv_comp g hdu hdπ]
  change fderiv ℝ (coordinateDerivativeList l u) (π g) (fderiv ℝ π g v) = _
  conv_lhs => arg 2; rw [euclidean_vector_expansion (fderiv ℝ π g v)]
  rw [map_sum]
  simp [coordinateDerivativeList]

theorem smooth_word_coefficient_expansion {n m b : ℕ} {U : Set (Space m)} {V : Set (Space n)}
    (hU : IsOpen U) (hV : IsOpen V) (π : Space m → Space n) (frame : Space m → ℂ)
    (fields : Fin b → Space m → Space m)
    (hπ : ContDiffOn ℝ (⊤ : ℕ∞) π U)
    (hframe : ContDiffOn ℝ (⊤ : ℕ∞) frame U)
    (hfields : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fields i) U)
    (himage : π '' U ⊆ V) (w : List (Fin b)) :
    ∃ ts : List ((Space m → ℂ) × List (Fin n)),
      (∀ t ∈ ts, ContDiffOn ℝ (⊤ : ℕ∞) t.1 U ∧ t.2.length ≤ w.length) ∧
      ∀ u : Space n → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) u V →
        ∀ g ∈ U, rightWord fields w (scalarLift π frame u) g =
          (ts.map (fun t => t.1 g * coordinateDerivativeList t.2 u (π g))).sum := by
  induction w with
  | nil =>
    refine ⟨[(frame, [])], ?_, ?_⟩
    · intro t ht; simp only [List.mem_singleton] at ht; subst t; exact ⟨hframe, by simp⟩
    · intro u hu g hg; simp [rightWord, scalarLift, coordinateDerivativeList]
  | cons i w ih =>
    obtain ⟨ts, hts, heq⟩ := ih
    let expand : ((Space m → ℂ) × List (Fin n)) → List ((Space m → ℂ) × List (Fin n)) :=
      fun t => (fun g => fderiv ℝ t.1 g (fields i g), t.2) ::
        (List.finRange n).map (fun j =>
          (fun g => t.1 g * ((fderiv ℝ π g (fields i g)) j : ℂ), j :: t.2))
    refine ⟨ts.flatMap expand, ?_, ?_⟩
    · intro t ht
      obtain ⟨s, hs, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨hsm, hsl⟩ := hts s hs
      simp only [expand, List.mem_cons, List.mem_map] at ht
      rcases ht with rfl | ⟨j, hj, rfl⟩
      · exact ⟨(hsm.fderiv_of_isOpen hU (by simp)).clm_apply (hfields i), by simpa using hsl.trans (Nat.le_succ _)⟩
      · refine ⟨hsm.mul ?_, by simpa using Nat.succ_le_succ hsl⟩
        have hdπ : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ π) U := hπ.fderiv_of_isOpen hU (by simp)
        exact Complex.ofRealCLM.contDiff.comp_contDiffOn
          (((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp_contDiffOn (hdπ.clm_apply (hfields i))))
    · intro u hu g hg
      have hevent : rightWord fields w (scalarLift π frame u) =ᶠ[nhds g]
          (fun x => (ts.map (fun t => t.1 x * coordinateDerivativeList t.2 u (π x))).sum) :=
        Filter.Eventually.mono (hU.mem_nhds hg) fun x hx => heq u hu x hx
      simp only [rightWord]
      rw [hevent.fderiv_eq]
      have term_deriv (s : (Space m → ℂ) × List (Fin n)) (hs : s ∈ ts) :
          fderiv ℝ (fun x => s.1 x * coordinateDerivativeList s.2 u (π x)) g (fields i g) =
          ((expand s).map (fun t => t.1 g * coordinateDerivativeList t.2 u (π g))).sum := by
        have hd1 := ((hts s hs).1.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
        have hdc := ((coordinateList_smooth hV u hu s.2).comp hπ (fun x hx => himage ⟨x,hx,rfl⟩)).differentiableOn (by simp)
        dsimp only [Function.comp_def] at hdc
        rw [fderiv_fun_mul hd1 (hdc.differentiableAt (hU.mem_nhds hg))]
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
        rw [pull_deriv hU hV π hπ himage u hu s.2 g hg (fields i g)]
        simp only [expand, List.map_cons, List.sum_cons, List.map_map, Function.comp_def]
        rw [← List.ofFn_eq_map, List.sum_ofFn]
        simp only [Finset.mul_sum]
        ring_nf
      have sum_deriv : ∀ ss : List ((Space m → ℂ) × List (Fin n)),
          (∀ s ∈ ss, s ∈ ts) →
          fderiv ℝ (fun x => (ss.map (fun t => t.1 x * coordinateDerivativeList t.2 u (π x))).sum) g (fields i g) =
          ((ss.flatMap expand).map (fun t => t.1 g * coordinateDerivativeList t.2 u (π g))).sum := by
        intro ss hss
        induction ss with
        | nil => simp
        | cons s ss ih =>
          have hs := hss s (by simp)
          have hterm (t) (ht : t ∈ ss) := (hts t (hss t (by simp [ht]))).1.mul
            ((coordinateList_smooth hV u hu t.2).comp hπ (fun x hx => himage ⟨x,hx,rfl⟩))
          have list_smooth : ∀ ll : List ((Space m → ℂ) × List (Fin n)),
              (∀ t ∈ ll, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => t.1 x * coordinateDerivativeList t.2 u (π x)) U) →
              ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (ll.map (fun t => t.1 x * coordinateDerivativeList t.2 u (π x))).sum) U := by
            intro ll hall
            induction ll with
            | nil => exact contDiffOn_const
            | cons t ll ih =>
              exact (hall t (by simp)).add (ih (fun z hz => hall z (by simp [hz])))
          have htail := list_smooth ss hterm
          have hhead := (hts s hs).1.mul ((coordinateList_smooth hV u hu s.2).comp hπ (fun x hx => himage ⟨x,hx,rfl⟩))
          dsimp only [Function.comp_def] at hhead
          simp only [List.map_cons, List.sum_cons]
          rw [fderiv_fun_add (hhead.differentiableOn (by simp) |>.differentiableAt (hU.mem_nhds hg))
            (htail.differentiableOn (by simp) |>.differentiableAt (hU.mem_nhds hg))]
          simp only [ContinuousLinearMap.add_apply, List.flatMap_cons, List.map_append, List.sum_append]
          rw [term_deriv s hs, ih (fun t ht => hss t (by simp [ht]))]
      exact sum_deriv ts (fun _ h => h)

theorem coordinateList_perm {d : ℕ} {U : Set (Space d)} (hU : IsOpen U)
    (u : Space d → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    {l r : List (Fin d)} (hp : l.Perm r) :
    Set.EqOn (coordinateDerivativeList l u) (coordinateDerivativeList r u) U := by
  induction hp with
  | nil => intro x hx; rfl
  | cons i h ih =>
    intro x hx
    have he := Filter.eventuallyEq_of_mem (hU.mem_nhds hx) ih
    exact congrArg (fun f : Space d →L[ℝ] ℂ => f (EuclideanSpace.single i 1)) he.fderiv_eq
  | swap i j l =>
    intro x hx
    have ht := ((coordinateList_smooth hU u hu l) x hx).contDiffAt (hU.mem_nhds hx)
    have hd : DifferentiableAt ℝ (fderiv ℝ (coordinateDerivativeList l u)) x :=
      (ht.fderiv_right (m := (1 : ℕ∞)) (by simp)).differentiableAt (by norm_num)
    simpa [coordinateDerivativeList, fderiv_clm_apply hd (differentiableAt_const _)] using
      (ht.isSymmSndFDerivAt (by simp)).eq
        (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)
  | trans h k ih ij => exact ih.trans ij

theorem exists_multiIndex_perm {d k : ℕ} (l : List (Fin d)) (hl : l.length ≤ k) :
    ∃ α : MultiIndex d k, α.directions.Perm l := by
  classical
  have hsum : ∑ i : Fin d, l.count i = l.length := by
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.count_cons, beq_iff_eq]
      simp [Finset.sum_add_distrib, ih (by simpa using Nat.le_of_succ_le hl)]
  let α : MultiIndex d k := ⟨fun i => ⟨l.count i, Nat.lt_succ_of_le (List.count_le_length.trans hl)⟩,
    by simpa using hsum.trans_le hl⟩
  refine ⟨α, List.perm_iff_count.mpr ?_⟩
  intro i
  simp only [MultiIndex.directions, List.count_flatMap, Function.comp_def, List.count_replicate]
  change ((List.finRange d).map (fun j => if (j == i) = true then l.count j else 0)).sum = l.count i
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  simp

end DedekindZetaZeroFree.KPContRightJets
