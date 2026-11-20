module

public import AnalyticESC.Conjugation.Characterisation

@[expose] public section

namespace AnalyticESC

open Set Metric Filter Topology

/-- `List.ofFn (w ∘ Fin.rev) = (List.ofFn w)^←`. -/
private theorem composite_ofFn_comp_rev {α : Type*} {m : ℕ} (w : Fin m → α) :
    List.ofFn (w ∘ Fin.rev) = (List.ofFn w).reverse := by
  refine List.ext_getElem (by simp) fun n h1 h2 => ?_
  grind

namespace IFS
variable {N m : ℕ} (Φ : IFS N)

noncomputable abbrev periodProj (hm : 0 < m) (w : Block N m) := Φ.P (periodic hm (w ∘ Fin.rev))

lemma linearizes_period {g} (hg : Regular g) (hm : 0 < m) (w : Block N m) :
    Linearizes g (Φ.R (List.ofFn w)) ↔ EqOn (D g) (Φ.periodProj hm w) I := by
  apply Φ.linearizes_iff_match _ _ hg
  · simpa using hm.ne'
  · let v := periodic hm (w ∘ Fin.rev)
    have e : block m v = (List.ofFn w).reverse := by
      rw [← composite_ofFn_comp_rev]; apply congrArg List.ofFn; funext i
      simp [pref,v,periodic,Nat.mod_eq_of_lt i.isLt]
    have h : shift m v = v := by funext n; simp [shift,v,periodic,Nat.add_mod_right]
    simpa only [e,h,List.reverse_reverse] using Φ.rec_block v m

end IFS
end AnalyticESC
