module

public import PottsDiscontinuity.TorusRC.Association
public import PottsDiscontinuity.TorusRC.ReflectionLaw

/-! # The reflected FKG connection across a double-height rectangle -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}

section

variable (hNp : 0 < N) (hMp : 0 < M)

/-- Reflection maps every sampled open edge to the corresponding sampled
open edge of the reflected configuration, with unchanged horizontal strip. -/
abbrev liftedReflectionStripHom (t : ℤ) (ht : Even t)
    (A : RCConfig N M) (a b : ℤ) :
    liftedStripGraph hNp hMp (reflectRCConfig hMp t A) a b →g
      liftedStripGraph hNp hMp A a b where
  toFun := liftedHorizontalReflect t ht
  map_rel' := by
    intro u v huv
    refine ⟨liftedHorizontalReflect_adj t ht huv.1, ?_, huv.2.2⟩
    rw [liftedHorizontalReflect_index hNp hMp t ht huv.1]
    exact huv.2.1

/-- Connection from (i,0) to (i,2n) within [0,3n] times [0,2n]. -/
def rectangleDoubleConnection (n : ℕ)
    (i : Fin (3 * n + 1)) : Set (RCConfig N M) :=
  {A | ∃ u v : RotatedVertex,
    u.val = ((i.val : ℤ), 0) ∧ v.val = ((i.val : ℤ), 2 * (n : ℤ)) ∧
      ∃ w : (liftedStripGraph hNp hMp A 0 (3 * (n : ℤ))).Walk u v,
        ∀ z ∈ w.support, 0 ≤ z.val.2 ∧ z.val.2 ≤ 2 * (n : ℤ)}

theorem rectanglePair_reflected_inter_subset
    (n : ℕ) (i j : Fin (3 * n + 1)) :
    rectanglePairConnection hNp hMp n i j ∩
      (reflectRCConfig hMp (2 * (n : ℤ)) ⁻¹' rectanglePairConnection hNp hMp n i j) ⊆
      rectangleDoubleConnection hNp hMp n i := by
  rintro A ⟨⟨u,v,hu,hv,w,hw⟩,⟨u',v',hu',hv',w',hw'⟩⟩
  let ht : Even (2 * (n : ℤ)) := ⟨n,by ring⟩
  let F := liftedReflectionStripHom hNp hMp (2 * (n : ℤ)) ht A 0 (3 * (n : ℤ))
  have hmatch : liftedHorizontalReflect (2 * (n : ℤ)) ht v' = v := by
    apply Subtype.ext
    rw [hv]
    change (v'.val.1, 2 * (n : ℤ) - v'.val.2) = _
    rw [hv']
    simp
    ring
  subst v
  refine ⟨u,liftedHorizontalReflect (2 * (n : ℤ)) ht u',hu,?_,
    w.append (w'.map F).reverse,?_⟩
  · change (u'.val.1, 2 * (n : ℤ) - u'.val.2) = _
    rw [hu']
    simp
  · intro z hz
    rw [SimpleGraph.Walk.support_append] at hz
    rcases List.mem_append.mp hz with hz | hz
    · have h := hw z hz
      constructor <;> omega
    · have hz' := List.mem_of_mem_tail hz
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse,
        SimpleGraph.Walk.support_map] at hz'
      obtain ⟨z',hzmem,heq⟩ := List.mem_map.mp hz'
      subst z
      have h := hw' z' hzmem
      change 0 ≤ 2 * (n : ℤ) - z'.val.2 ∧ 2 * (n : ℤ) - z'.val.2 ≤ 2 * (n : ℤ)
      constructor <;> omega

end

theorem rectanglePairConnection_mono (hNp : 0 < N) (hMp : 0 < M)
    (n : ℕ) (i j : Fin (3 * n + 1)) {A B : RCConfig N M} (hAB : A ≤ B)
    (hA : A ∈ rectanglePairConnection hNp hMp n i j) :
    B ∈ rectanglePairConnection hNp hMp n i j := by
  obtain ⟨u,v,hu,hv,w,hw⟩ := hA
  refine ⟨u,v,hu,hv,w.mapLe (liftedStripGraph_mono hNp hMp _ _ hAB),?_⟩
  simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hw

/-- The reflected-pair FKG step in the source, with the exact torus-law
reflection and explicit local paths. -/
theorem rectangleDouble_probability_ge_pair_sq (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (q : Set.Ici (1 : ℝ))
    (n : ℕ) (i j : Fin (3 * n + 1)) :
    torusRCProbability hN hM q (rectanglePairConnection hNp hMp n i j) ^ 2 ≤
      torusRCProbability hN hM q (rectangleDoubleConnection hNp hMp n i) := by
  let E := rectanglePairConnection hNp hMp n i j
  let T : RCConfig N M → RCConfig N M := reflectRCConfig hMp (2 * (n : ℤ))
  have hE : ∀ ⦃A B⦄, A ≤ B → A ∈ E → B ∈ E :=
    fun {_ _} hAB hA => rectanglePairConnection_mono hNp hMp n i j hAB hA
  have hT : ∀ ⦃A B : RCConfig N M⦄, A ≤ B → T A ≤ T B := by
    intro A B hAB e
    exact hAB _
  have h := torusRCProbability_inter_ge_mul hN hM q E (T ⁻¹' E)
    hE (fun {_ _} hAB hA => hE (hT hAB) hA)
  have heq := torusRCProbability_reflect hN hM hNp hMp (2 * (n : ℤ))
    (show Even (2 * (n : ℤ)) from ⟨n,by ring⟩) q E
  rw [← heq] at h
  rw [pow_two]
  exact h.trans (torusRCProbability_mono hN hM q
    (rectanglePair_reflected_inter_subset hNp hMp n i j))

end PottsDiscontinuity.TorusRC
