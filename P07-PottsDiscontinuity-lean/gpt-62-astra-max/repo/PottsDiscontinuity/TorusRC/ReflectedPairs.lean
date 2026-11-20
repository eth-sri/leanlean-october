module

public import PottsDiscontinuity.TorusRC.Association
public import PottsDiscontinuity.TorusRC.ReflectionLaw

/-! # The reflected FKG connection across a double-height rectangle -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}

section
variable (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M) (q : Set.Ici (1 : ℝ)) (n : ℕ)
    (i j : Fin (3 * n + 1))

/-- Reflection maps every sampled open edge to the corresponding sampled
open edge of the reflected configuration, with unchanged horizontal strip. -/
abbrev liftedReflectionStripHom {t : ℤ} (ht : Even t)
    (A : RCConfig N M) (a b : ℤ) :
    liftedStripGraph hNp hMp (reflectRCConfig hMp t A) a b →g
      liftedStripGraph hNp hMp A a b where
  toFun := liftedHorizontalReflect ht
  map_rel' := by
    intro u v huv
    refine ⟨liftedHorizontalReflect_adj t ht huv.1, ?_, huv.2.2⟩
    rw [liftedHorizontalReflect_index hNp hMp t ht huv.1]
    exact huv.2.1

include hNp hMp in
/-- Connection from (i,0) to (i,2n) within [0,3n] times [0,2n]. -/
def rectangleDoubleConnection {n : ℕ}
    (i : Fin (3 * n + 1)) : Set (RCConfig N M) :=
  {A | ∃ u v : RotatedVertex,
    u.val = ((i.val : ℤ), 0) ∧ v.val = ((i.val : ℤ), 2 * (n : ℤ)) ∧
      ∃ w : (liftedStripGraph hNp hMp A 0 (3 * (n : ℤ))).Walk u v,
        ∀ z ∈ w.support, 0 ≤ z.val.2 ∧ z.val.2 ≤ 2 * (n : ℤ)}

theorem rectanglePair_reflected_inter_subset :
    rectanglePairConnection hNp hMp i j ∩
      (reflectRCConfig hMp (2 * (n : ℤ)) ⁻¹' rectanglePairConnection hNp hMp i j) ⊆
      rectangleDoubleConnection hNp hMp i := by
  rintro A ⟨⟨u,v,hu,hv,w,hw⟩,⟨u',v',hu',hv',w',hw'⟩⟩
  let ht : Even (2 * (n : ℤ)) := ⟨n,by ring⟩
  let F := liftedReflectionStripHom hNp hMp ht A 0 (3 * (n : ℤ))
  have hmatch : liftedHorizontalReflect ht v' = v := by
    apply Subtype.ext
    rw [hv]
    change (v'.val.1, 2 * (n : ℤ) - v'.val.2) = _
    grind
  subst v
  refine ⟨u,liftedHorizontalReflect ht u',hu,?_,
    w.append (w'.map F).reverse,?_⟩
  · change (u'.val.1, 2 * (n : ℤ) - u'.val.2) = _
    simp [hu']
  · intro z hz
    rw [SimpleGraph.Walk.support_append] at hz
    rcases List.mem_append.mp hz with hz | hz
    · grind
    · have hz' := List.mem_of_mem_tail hz
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse,
        SimpleGraph.Walk.support_map] at hz'
      obtain ⟨z',hzmem,heq⟩ := List.mem_map.mp hz'
      subst z
      have h := hw' z' hzmem
      change 0 ≤ 2 * (n : ℤ) - z'.val.2 ∧ 2 * (n : ℤ) - z'.val.2 ≤ 2 * (n : ℤ)
      omega

private theorem rectanglePair_walk_mono {V : Type*} {G H : SimpleGraph V}
    (hGH : G ≤ H) {u v : V} (w : G.Walk u v) :
    ∃ w' : H.Walk u v, w'.support = w.support := by
  induction w with
  | nil => exact ⟨.nil,rfl⟩
  | @cons u v w hadj p ih =>
    obtain ⟨p',hp⟩ := ih
    exact ⟨.cons (hGH hadj) p',by grind⟩

theorem rectanglePairConnection_mono {A B : RCConfig N M} (hAB : A ≤ B)
    (hA : A ∈ rectanglePairConnection hNp hMp i j) :
    B ∈ rectanglePairConnection hNp hMp i j := by
  obtain ⟨u,v,hu,hv,w,hw⟩ := hA
  obtain ⟨w',hs⟩ := rectanglePair_walk_mono
    (liftedStripGraph_mono hNp hMp 0 (3 * (n : ℤ)) hAB) w
  exact ⟨u,v,hu,hv,w',by simpa only [hs] using hw⟩

/-- The reflected-pair FKG step in the source, with the exact torus-law
reflection and explicit local paths. -/
theorem rectangleDouble_probability_ge_pair_sq :
    torusRCProbability hN hM q (rectanglePairConnection hNp hMp i j) ^ 2 ≤
      torusRCProbability hN hM q (rectangleDoubleConnection hNp hMp i) := by
  let E := rectanglePairConnection hNp hMp i j
  let T : RCConfig N M → RCConfig N M := reflectRCConfig hMp (2 * (n : ℤ))
  have hE : ∀ ⦃A B⦄, A ≤ B → A ∈ E → B ∈ E :=
    fun {_ _} hAB hA => rectanglePairConnection_mono hNp hMp n i j hAB hA
  have hT : ∀ ⦃A B : RCConfig N M⦄, A ≤ B → T A ≤ T B := by
    intro A B hAB e
    exact hAB _
  have h := torusRCProbability_inter_ge_mul hN hM q (E := E) (F := (T ⁻¹' E))
    hE (fun {_ _} hAB hA => hE (hT hAB) hA)
  have heq := torusRCProbability_reflect hN hM hNp hMp (t := (2 * (n : ℤ)))
    (show Even (2 * (n : ℤ)) from ⟨n,by ring⟩) q E
  rw [← heq] at h
  rw [pow_two]
  exact h.trans (torusRCProbability_mono hN hM q
    (rectanglePair_reflected_inter_subset hNp hMp n i j))

end

/-- The source's uniformly positive double-height point connection, obtained
from h319 by endpoint extraction, reflection symmetry, and FKG. -/
theorem double_connection_of_h319 (q : Set.Ici (1 : ℝ)) (hh319 : h319 q) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N M n : ℕ) (hN : Even N) (hM : Even M)
      (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hn : 0 < n)
      (h3nN : 3 * n ≤ N) (h3nM : 3 * n ≤ M),
      let hNp : 0 < N := by omega
      let hMp : 0 < M := by omega
      ∃ i : Fin (3 * n + 1),
        (c / (9 * (n : ℝ) ^ 2)) ^ 2 ≤ torusRCProbability hN hM q
          (rectangleDoubleConnection hNp hMp i) := by
  obtain ⟨c,hc,hpair⟩ := point_pair_of_h319 q hh319
  refine ⟨c,hc,?_⟩
  intro N M n hN hM hN4 hM4 hn h3nN h3nM
  obtain ⟨ij,hij⟩ := hpair N M n hN hM hN4 hM4 hn h3nN h3nM
  refine ⟨ij.1, ?_⟩
  exact (pow_le_pow_left₀ (by positivity) hij 2).trans
    (rectangleDouble_probability_ge_pair_sq hN hM (by omega) (by omega) q n ij.1 ij.2)

end PottsDiscontinuity.TorusRC
