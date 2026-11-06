module

public import Chazelle.Core.ClusterMap
public import Chazelle.Separator.Maps

/-!
# WP-I, part 22: rotation systems encoding a combinatorial map

`EnvEnc G M' eV eD`: the arrays of the rotation system `G` encode the combinatorial map `M'`
through bijections `eV` (vertices onto `[0, nv)`) and `eD` (darts onto `[0, N)`).  Then

* `EnvEnc.ok`: `G` is well formed;
* `EnvEnc.head`: heads are encoded heads;
* `EnvEnc.step_iff`: a step of `G` between encoded vertices is a dart of `M'` with unblocked
  flags;
* `EnvEnc.reach_iff`: reachability in `G` is the reflexive-transitive closure of the steps of
  `M'` read through the encodings.
-/

namespace Chazelle.Core.Cluster

open Chazelle.Separator

@[expose] public section

variable {V' F' D' : Type*}

/-- The rotation system `G` encodes the map `M'`. -/
structure EnvEnc (G : Env) (M' : CombMap V' F' D') (eV : V' → ℕ) (eD : D' → ℕ) : Prop where
  eV_lt : ∀ v, eV v < G.nv
  eV_inj : Function.Injective eV
  eV_surj : ∀ u, u < G.nv → ∃ v, eV v = u
  eD_lt : ∀ d, eD d < G.N
  eD_inj : Function.Injective eD
  eD_surj : ∀ e, e < G.N → ∃ d, eD d = e
  opp : ∀ d, G.opp (eD d) = eD (M'.opp d)
  rot : ∀ d, G.rot (eD d) = eD (M'.rot d)
  vert : ∀ d, G.vert (eD d) = eV (M'.vert d)
  first : ∀ v, ∃ d, G.first (eV v) = eD d ∧ M'.vert d = v

namespace EnvEnc

variable {G : Env} {M' : CombMap V' F' D'} {eV : V' → ℕ} {eD : D' → ℕ}

theorem iterate_rot (h : EnvEnc G M' eV eD) (n : ℕ) (d : D') :
    G.rot^[n] (eD d) = eD ((M'.rot ^ n) d) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, h.rot, ih, pow_succ, Equiv.Perm.mul_apply]

/-- **The encoded rotation system is well formed.** -/
theorem ok [Finite D'] (h : EnvEnc G M' eV eD) : G.OK := by
  refine ⟨fun e he => ?_, fun e he => ?_, fun e he => ?_, fun e he e' he' hee => ?_,
    fun e he => ?_, fun e he e' he' hee => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · obtain ⟨d, rfl⟩ := h.eD_surj e he; rw [h.opp]; exact h.eD_lt _
  · obtain ⟨d, rfl⟩ := h.eD_surj e he; rw [h.rot]; exact h.eD_lt _
  · obtain ⟨d, rfl⟩ := h.eD_surj e he; rw [h.vert]; exact h.eV_lt _
  · obtain ⟨d, rfl⟩ := h.eD_surj e he
    obtain ⟨d', rfl⟩ := h.eD_surj e' he'
    rw [h.rot, h.rot] at hee
    rw [M'.rot.injective (h.eD_inj hee)]
  · obtain ⟨d, rfl⟩ := h.eD_surj e he; rw [h.rot, h.vert, h.vert, M'.vert_rot]
  · obtain ⟨d, rfl⟩ := h.eD_surj e he
    obtain ⟨d', rfl⟩ := h.eD_surj e' he'
    rw [h.vert, h.vert] at hee
    obtain ⟨n, hn⟩ := (M'.sameCycle_of_vert d d' (h.eV_inj hee)).exists_nat_pow_eq
    exact ⟨n, by rw [h.iterate_rot, hn]⟩
  · obtain ⟨v, rfl⟩ := h.eV_surj u hu
    obtain ⟨d, hd, -⟩ := h.first v
    rw [hd]; exact h.eD_lt _
  · obtain ⟨v, rfl⟩ := h.eV_surj u hu
    obtain ⟨d, hd, hvd⟩ := h.first v
    rw [hd, h.vert, hvd]

theorem head (h : EnvEnc G M' eV eD) (d : D') : G.head (eD d) = eV (M'.head d) := by
  unfold Env.head CombMap.head
  rw [h.opp, h.vert]

/-- **Steps between encoded vertices.** -/
theorem step_iff (h : EnvEnc G M' eV eD) (u w : V') :
    G.Step (eV u) (eV w) ↔ ∃ d, G.db (eD d) ≠ 1 ∧ M'.vert d = u ∧ M'.head d = w ∧
      G.vb (eV u) ≠ 1 ∧ G.vb (eV w) ≠ 1 := by
  constructor
  · rintro ⟨e, he, hdb, hve, hhe, hu, hw⟩
    obtain ⟨d, rfl⟩ := h.eD_surj e he
    rw [h.vert] at hve
    rw [h.head] at hhe
    exact ⟨d, hdb, h.eV_inj hve, h.eV_inj hhe, hu, hw⟩
  · rintro ⟨d, hdb, rfl, rfl, hu, hw⟩
    exact ⟨eD d, h.eD_lt d, hdb, h.vert d, h.head d, hu, hw⟩

/-- The typed step relation read through the encodings. -/
def TStep (G : Env) (M' : CombMap V' F' D') (eV : V' → ℕ) (eD : D' → ℕ) (u w : V') : Prop :=
  ∃ d, G.db (eD d) ≠ 1 ∧ M'.vert d = u ∧ M'.head d = w ∧ G.vb (eV u) ≠ 1 ∧ G.vb (eV w) ≠ 1

/-- **Reachability** in `G` from an encoded vertex is typed reachability. -/
theorem reach_iff (h : EnvEnc G M' eV eD) (u w : V') :
    G.Reach (eV u) (eV w) ↔ Relation.ReflTransGen (TStep G M' eV eD) u w := by
  constructor
  · intro hr
    -- every vertex reached is encoded
    have key : ∀ x, G.Reach (eV u) x → ∃ w', x = eV w' ∧
        Relation.ReflTransGen (TStep G M' eV eD) u w' := by
      intro x hx
      induction hx with
      | refl => exact ⟨u, rfl, Relation.ReflTransGen.refl⟩
      | tail _ hs ih =>
        obtain ⟨w', rfl, hw'⟩ := ih
        obtain ⟨e, he, hdb, hve, hhe, hu, hw⟩ := hs
        obtain ⟨d, rfl⟩ := h.eD_surj e he
        rw [h.head] at hhe
        subst hhe
        rw [h.vert] at hve
        refine ⟨M'.head d, rfl, Relation.ReflTransGen.tail hw' ⟨d, hdb, h.eV_inj hve, rfl,
          by first | exact hu, hw⟩⟩
    obtain ⟨w', hw', hr'⟩ := key _ hr
    rwa [h.eV_inj hw']
  · intro hr
    induction hr with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih => exact Relation.ReflTransGen.tail ih ((h.step_iff _ _).mpr hs)

end EnvEnc

end

end Chazelle.Core.Cluster
