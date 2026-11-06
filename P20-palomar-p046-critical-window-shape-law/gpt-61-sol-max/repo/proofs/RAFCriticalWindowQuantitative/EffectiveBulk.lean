
import proofs.RAFCriticalWindowQuantitative.SeedDeficit


namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAF.Polymer MeasureTheory unitInterval

variable (b : ℚ) (hb : 0 < b) (hb1 : b ≤ 1) (m : ℕ)




/-- The computed cutoff gives the literal uniform supplied-seed mass guarantee. -/
theorem effective_static_bulk  :
    let a := rationalParameter b hb.le hb1
    let k := seedIndex b hb hb1 m
    ∀ N : ℕ, 0 < N →
      staticReactionMeasure N a {ω |
        MassDeficit m (temporaryReactionClosure (10*k) (staticOpenReactions ω))} ≤ (m : ENNReal)⁻¹ := by
  dsimp
  let a := rationalParameter b hb.le hb1
  let η := (m : ENNReal)⁻¹/(m+1)
  let k := seedIndex b hb hb1 m
  let z := contourBudget a k
  intro N hN
  obtain ⟨hk,hkspec⟩ : seedTest b m k := Nat.find_spec (seedTest_exists b hb hb1 m)
  have hbound : z/(1-z) ≤ 1/((m : ENNReal)*(m+1)) := by
    have h : z * ((m : ENNReal)*(m+1)+1) ≤ 1 := by
      apply (ENNReal.toReal_le_toReal (by dsimp [z, contourBudget]; finiteness) (by simp)).mp
      simp only [ENNReal.toReal_mul, ENNReal.toReal_one, z, contourBudget_real]
      change (molecularContourConstant : ℝ)*(1-(b : ℝ)^2)^k*((m : ℝ)*(m+1)+1) ≤ 1
      exact_mod_cast hkspec
    apply (ENNReal.le_div_iff_mul_le (by simp) (by simp)).mpr
    rw [div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv]
    apply ENNReal.div_le_of_le_mul
    rw [one_mul]
    apply ENNReal.le_sub_of_add_le_right (by dsimp [z, contourBudget]; finiteness)
    simpa [mul_add] using h
  have hηeq : 1 / ((m)*(m+1)) = η := by
    simp [η, div_eq_mul_inv, ENNReal.mul_inv]
  rw [hηeq] at hbound
  calc
    _ ≤ z/(1-z) + m*(z/(1-z)) := by
      have hL : 2*(5*k) ≤ 10*k := by omega
      classical
      let X := ↥(actualBinaryWords N)
      let root : X := ⟨[false], (mem_actualBinaryWords _ _).mpr ⟨by simp, hN⟩⟩
      let μ := staticReactionMeasure N a
      let bad (ω : Reaction N → Prop) : Finset X :=
        Finset.univ.filter fun s => moleculeContourBad hL s.val ω
      let pool (ω : Reaction N → Prop) : Finset X :=
        Finset.univ.filter fun s => indexedEdgeReach (wordEffectiveEdges hL ω) Prod.fst wordEdgeParent
          (boundedFoodRoot (10*k) N) (molecularWordVertex (10*k) N s.val)
      let δ := z/(1-z)
      have hcover (ω) (hr : root ∉ bad ω) (s) (hs : s ∉ bad ω) : s ∈ pool ω := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [← molecularWordVertex_food root.val (by change 1 ≤ (10*k); omega)]
        by_contra hn
        obtain ⟨f, hneq, hcut, hnonempty, hmin⟩ :=
          exists_disabled_separating_bond (wordBasicEdges (10*k) N) _ Prod.fst wordEdgeParent
            _ _ (wordGraph_connected (10*k) N _ _) hn
        rw [molecularWordVertex_label f root.val, molecularWordVertex_label f s.val] at hneq
        have hfailed : contourDetoursFailed hL (wordGraphCut f) (fun (r : Reaction N) (ω : Reaction N → Prop) => ω r) ω := by
                          intro d hd hopen
                          obtain ⟨he, _⟩ := Finset.mem_product.mp hd
                          obtain ⟨hb, hn⟩ := Finset.mem_sdiff.mp (hcut he)
                          apply hn
                          apply Finset.mem_filter.mpr
                          exact ⟨hb, d.2, hopen⟩


        have hb (u : List Bool) (hu : u ∈ actualBinaryWords N)
            (hgood : ¬ moleculeContourBad hL u ω) :=
          Nat.lt_of_not_ge fun (hm : (wordMolecularSide f (boundedWordLabel f u)).card ≤
            (actualBinaryWords N \ wordMolecularSide f (boundedWordLabel f u)).card) => hgood (by
              let z0 := (wordGraphCut f).card
              have hb := Finset.card_pos.mpr hnonempty
              have hcard : z0-1+1 = z0 := Nat.sub_add_cancel hb
              refine ⟨z0-1, wordGraphCut f, ?_, hfailed⟩
              rw [hcard]
              obtain ⟨e, he⟩ := hnonempty
              have hconn (d : _) (hd : d ∈ wordGraphCut f) :
                  wordContourReach (wordGraphCut f) e d := by
                let F := (wordGraphCut f).filter (wordContourReach (wordGraphCut f) e)

                have heF : e ∈ F := Finset.mem_filter.mpr ⟨he, Relation.EqvGen.refl e⟩

                obtain ⟨g, hg⟩ := wordDiamond_closed_subset_cut f F (Finset.filter_subset _ _) (by
                                                                           intro v i j hi hj
                                                                           obtain ⟨hiC, hiR⟩ := Finset.mem_filter.mp hi
                                                                           apply Finset.mem_filter.mpr
                                                                           refine ⟨hj, Relation.EqvGen.trans _ _ _ hiR ?_⟩
                                                                           exact Relation.EqvGen.rel _ _ ⟨hiC, hj, v, i, j, rfl, rfl⟩)
                change ∀ g, (wordGraphCut g).Nonempty → wordGraphCut g ⊆ wordGraphCut f →
                  wordGraphCut g = wordGraphCut f at hmin
                clear * - hmin heF hg hd
                clear_value k
                grind
              have hsub : wordGraphCut f ⊆ _ := Finset.filter_subset _ _
              have helen := boundedFoodWord_nonroot_length e.1 (by simpa [wordBasicEdges] using hsub he)
              have hsN := ((mem_actualBinaryWords u N).mp hu).2
              have hlocal (d : _) (hd : d ∈ wordGraphCut f) :
                  ∃ q : endWordGraph.Walk e.1.val d.1.val, q.length ≤ 4*((wordGraphCut f).card-1) := by
                obtain ⟨p, hp, hl⟩ := wordContour_tour (wordGraphCut f) hsub e he hconn
                have hdp : d ∈ p.support := List.mem_toFinset.mp (hp.symm ▸ hd)
                obtain ⟨q, hq⟩ := wordContour_walk_lift (p.takeUntil d hdp)
                refine ⟨q, ?_⟩
                have ht := p.length_takeUntil_le_length hdp
                omega
              refine Exists.elim ?_ fun p hp =>
                Finset.mem_biUnion.mpr ⟨e, (by
                                                         refine Finset.mem_filter.mpr ⟨?_, endWord_walk_mem_ball p _ hp⟩
                                                         exact Finset.filter_subset _ _ he), by
                                                                                                 apply Finset.mem_filter.mpr
                                                                                                 refine ⟨Finset.mem_powerset.mpr ?_, rfl, he, ?_⟩
                                                                                                 · exact Finset.filter_subset _ _
                                                                                                 · intro d hd
                                                                                                   exact hconn d hd⟩
              let z0 := f (boundedFoodRoot (10*k) N)
              by_cases hshort : e.1.val.length ≤ 8 * (wordGraphCut f).card
              · let M := e.1.val.length + 4 * (wordGraphCut f).card
                have hcut : ∀ d ∈ wordGraphCut f, d.1.val.length ≤ M := by
                  intro d hd
                  obtain ⟨p, hp⟩ := hlocal d hd
                  have hh := endWord_walk_length_bound p

                  omega
                have hLM : (10*k) < M := by omega
                have hsM : u.length ≤ M := by
                  by_cases hMN : M < N
                  · 
                    by_contra h
                    let U := wordMolecularSide f (boundedWordLabel f u)
                    have hconstant (v : List Bool) (hv : v ∈ actualBinaryWords N) (hvM : M ≤ v.length) :
                        boundedWordLabel f u = boundedWordLabel f v :=
                      highBand_label_constant (boundedWordLabel f) M N hMN
                        (wordCut_above_boundary_parents f hLM hcut) u v
                        ⟨by omega, hsN⟩ ⟨hvM, ((mem_actualBinaryWords v N).mp hv).2⟩
                    have hcomp : actualBinaryWords N \ U ⊆ shortBinaryWords (M-1) := by
                      grind [mem_shortBinaryWords, wordMolecularSide]
                    have hc : (actualBinaryWords N \ U).card < 2^M := by
                      have hx := Finset.card_le_card hcomp
                      have hi := shortBinaryWords_card (M-1)
                      grind
                    have htotal := Finset.card_sdiff_add_card_eq_card
                      (show U ⊆ actualBinaryWords N from Finset.filter_subset _ _)
                    rw [actualBinaryWords_card, pow_succ] at htotal
                    have hp := (pow_lt_pow_iff_right₀ (by decide : _ < 2)).mpr hMN
                    change U.card ≤ (actualBinaryWords N \ U).card at hm
                    omega
                  · omega
                obtain ⟨p, hp⟩ := endWord_common_core_walk u e.1.val []
                  ⟨[], u, by simp⟩ ⟨[], e.1.val, by simp⟩

                refine ⟨p, ?_⟩

                omega
              let r := 4 * (wordGraphCut f).card
              let n := e.1.val.length - 2 * r
              let left := e.1.val.take r
              let core := (e.1.val.drop r).take n
              let right := (e.1.val.drop r).drop n
              have hcLen : core.length = e.1.val.length - 2 * r := by simp [core, n]; omega
              have hcoreNe : core ≠ [] := by intro h; simp_all; omega
              have ha : e.1.val = left ++ core ++ right := by simp [left, core, right, List.append_assoc]
              have hl : left.length = r := by simp [left]; omega
              have hr : right.length = r := by simp [right, n]; omega
              have hb := Finset.card_pos.mpr ⟨e, he⟩
              have hcore (d : _) (hd : d ∈ wordGraphCut f) :
                  ∃ l r, d.1.val = l ++ core ++ r := by
                obtain ⟨p, hp⟩ := hlocal d hd
                exact endWord_walk_protects_core p core left right ha (by omega) (by omega)
              have hcut : ∀ d ∈ wordGraphCut f, d.1.val.length ≤ e.1.val.length + r := by
                intro d hd
                obtain ⟨p, hp⟩ := hlocal d hd
                have hh := endWord_walk_length_bound p
                omega
              have hLM : (10*k) < e.1.val.length + r := by omega
              by_cases hc : (boundedWordLabel f u) = z0
              · rw [hc] at hm
                have hp := Finset.card_sdiff_add_card_eq_card
                  (show wordMolecularSide f (z0) ⊆ actualBinaryWords N from Finset.filter_subset _ _)
                rw [molecular_food_complement, Finset.card_image_of_injective _ Subtype.val_injective] at hm
                rw [molecular_food_complement, Finset.card_image_of_injective _ Subtype.val_injective,
                  actualBinaryWords_card] at hp

                have hN := wordFoodSide_minor_cap_bound f hLM hcut core hcoreNe hcore (3*r)
                  (by omega) (by omega)
                have heN := boundedFoodWord_length_le e.1
                obtain ⟨p, hp⟩ := endWord_common_core_walk u e.1.val []
                  ⟨[], u, by simp⟩ ⟨[], e.1.val, by simp⟩
                exact ⟨p, by omega⟩
              · obtain ⟨u, hu, hnonempty⟩ : ∃ v : _, v.val = u ∧ f v ≠ f (boundedFoodRoot _ _) := by clear * - hu hc; clear_value k; grind [boundedWordLabel]
                have hvl := wordCut_nonfood_length_le f hLM hcut core hcoreNe hcore u hnonempty
                obtain ⟨p, hp⟩ := endWord_common_core_walk u.val e.1.val core
                  (by
                     by_contra h
                     exact hnonempty (wordCut_core_avoiding_root f core hcore u h)) ⟨left, right, ha⟩
                exact ⟨p.copy hu rfl, by simpa using (show p.length ≤ 64*(wordGraphCut f).card by omega)⟩)
        have hnotS := hb root.val root.property (by simpa [bad] using hr)
        have hnotT := hb s.val s.property (by simpa [bad] using hs)
        rw [wordMolecularSide_complement_of_ne f _ _ hneq] at hnotS
        rw [wordMolecularSide_complement_of_ne f _ _ hneq.symm] at hnotT
        omega
      have hbad (s : X) : μ {ω | s ∈ bad ω} ≤ δ := by
        simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
        let s := s.val
        change μ {ω | moleculeContourBad hL s ω} ≤ _
        unfold moleculeContourBad
        rw [Set.ofPred_exists]
        calc
          _ ≤ ∑' j : ℕ, μ {ω | ∃ C ∈ wordMoleculeContourEnvelope (10*k) N s (j+1),
            contourDetoursFailed hL C (fun r ω => ω r) ω} := measure_iUnion_le _
          _ ≤ ∑' j : ℕ, z^(j+1) := ENNReal.tsum_le_tsum
            fun j => (by
                       let b := j + 1
                       classical
                       let E := wordMoleculeContourEnvelope (10*k) N s b
                       have hcount : (E.card : ENNReal) ≤ molecularContourConstant^b := by
                         norm_cast
                         let hb : 0 < b := ((by omega))
                         calc
                           _ ≤ 2 * 7 ^ (64 * b) * 81 ^ (b - 1) := by
                             apply (Finset.card_biUnion_le_card_mul _ _ (81^(b-1))
                               (fun e _ => wordAnchoredContours_card (10*k) N e b)).trans
                             exact Nat.mul_le_mul_right _ ((by
                                                             have hc : (wordBallEdgeAnchors (10*k) N s (64 * b)).card ≤
                                                                 (endWordBall (64 * b) s ×ˢ (Finset.univ : Finset Bool)).card := by
                                                               apply Finset.card_le_card_of_injOn fun e : WordBasicEdge (10*k) N => (e.1.val, e.2)
                                                               · intro e he
                                                                 simpa using (Finset.mem_filter.mp he).2
                                                               simp_all
                                                             simp_all
                                                             have hb := endWordBall_card (64 * b) s
                                                             omega))
                           _ ≤ 2 ^ b * 7 ^ (64 * b) * 81 ^ b :=
                             by gcongr <;> grind
                           _ = molecularContourConstant ^ b := by simp only [molecularContourConstant, mul_pow, pow_mul]
                       calc
                         _ ≤ ∑ C ∈ E, μ
                           {ω | contourDetoursFailed hL C (fun r ω => ω r) ω} := by
                           simpa only [← Set.ofPred_exists, exists_prop] using measure_biUnion_finset_le E
                             (fun C => {ω | contourDetoursFailed hL C (fun r ω => ω r) ω}) (μ := μ)
                         _ ≤ ∑ _C ∈ E, ((1-(toNNReal a : ENNReal)^2)^k)^b := by
                           apply Finset.sum_le_sum
                           intro C hC
                           simpa [(show C.card = b from by
                                    obtain ⟨e, _, he⟩ := Finset.mem_biUnion.mp hC
                                    exact (Finset.mem_filter.mp he).2.1)] using staticReaction_contour_failure hL le_rfl C a
                         _ = E.card * ((1-toNNReal a^2)^k)^b := by simp
                         _ ≤ molecularContourConstant^b * ((1-toNNReal a^2)^k)^b := by
                           gcongr
                         _ = z^b := by simp only [z, contourBudget, mul_pow])
          _ = _ := by simp only [ENNReal.tsum_geometric_add_one, δ, div_eq_mul_inv]
      apply le_trans (measure_mono (t := {ω | MassDeficit m (pool ω)}) ?_) ?_
      ·
        intro ω hω
        simp only [X, MassDeficit, Fintype.card_coe, card_molecules_exact, actualBinaryWords_card] at *
        apply lt_of_le_of_lt (Nat.mul_le_mul_left m ?_) hω
        apply Finset.card_le_card_of_injOn fun s : X =>
          sourceWordMolecule s.val (by have := (mem_actualBinaryWords s.val N).mp s.property; grind) ((mem_actualBinaryWords s.val N).mp s.property).2
        · intro s hs
          have hi := wordEffective_reach_generated_iff hL ω (Finset.mem_filter.mp hs).2
          have hg := hi.mp (contractedWordGenerated_root _)
          grind [contractedWordGenerated_iff, sourceWordMolecule_word, molecularWordVertex_val, mem_actualBinaryWords]
        · intro s _ t _ h
          exact Subtype.ext (by simpa using congrArg moleculeWord h)
      · clear_value bad pool
        let : Nonempty X := ⟨root⟩
        have hmass : μ {ω | Fintype.card X ≤ m*(bad ω).card} ≤ m*δ := calc
          _ ≤ (∫⁻ ω, (m : ENNReal)*(bad ω).card ∂μ) / Fintype.card X := by
            simpa [← Nat.cast_mul] using
              meas_ge_le_lintegral_div (μ := μ) (f := fun ω => (m : ENNReal)*(bad ω).card)
                (measurable_of_finite _).aemeasurable (ε := (Fintype.card X : ENNReal))
                (by positivity) (by simp)
          _ ≤ (m : ENNReal)*(Fintype.card X*δ) / Fintype.card X := by
            rw [lintegral_const_mul _ (measurable_of_finite _)]
            gcongr
            have he (ω : Reaction N → Prop) : ((bad ω).card : ENNReal) = ∑ x : X, if x ∈ bad ω then 1 else 0 := by simp
            simp_rw [he]
            rw [lintegral_finsetSum Finset.univ fun _ _ => measurable_of_finite _]
            simpa [Set.indicator] using Finset.sum_le_sum (s := (Finset.univ : Finset X)) fun x _ =>
              (lintegral_indicator_one (μ := μ) (s := {ω | x ∈ bad ω}) (Set.toFinite _).measurableSet).le.trans (hbad x)
          _ = _ := by
            rw [mul_comm (Fintype.card X : ENNReal) δ, ← mul_assoc,
              ENNReal.mul_div_cancel_right (by positivity) (by simp)]
        apply (measure_mono ?_).trans ((measure_union_le _ _).trans (add_le_add (hbad root) hmass))
        intro ω hω
        by_cases hr : root ∈ bad ω
        · exact Or.inl hr
        · right
          change Fintype.card X ≤ m*(bad ω).card
          have hu : bad ω ∪ pool ω = Finset.univ := by ext x; simpa using or_iff_not_imp_left.mpr (hcover ω hr x)
          have hc := Finset.card_union_le (bad ω) (pool ω)
          rw [hu, Finset.card_univ] at hc
          change m*(pool ω).card < (m-1)*Fintype.card X at hω
          have hmul := Nat.mul_le_mul_left m hc
          simp only [mul_add] at hmul
          rw [Nat.sub_mul, one_mul] at hω
          dsimp only [X] at *
          omega
    _ ≤ η+m*η := by gcongr
    _ = _ := by
      rw [← one_add_mul, add_comm 1]
      exact ENNReal.mul_div_cancel (by simp) (by simp)

end RAFCriticalWindowQuantitative
