module
public import RadianRamsey.TradePaths
public import OAI.Combinatorics.EuclideanRamsey.ColoringCompactness
public import OAI.Combinatorics.EuclideanRamsey.Model

@[expose] public noncomputable section
namespace OAI.EuclideanRamsey.Radian
open RadianRamsey

def plane := Complex.orthonormalBasisOneI.repr.symm

private abbrev Block (n : ℕ) := EuclideanSpace ℂ (Fin (n+1))
private abbrev dim (n : ℕ) := Module.finrank ℝ (Block n)
private def encode (n : ℕ) (x : List ℂ) : Space (dim n) :=
  (stdOrthonormalBasis ℝ (Block n)).repr (WithLp.toLp 2 (Fin.cons 0 fun k : Fin n => x[k.val]?.getD 0))

private lemma encode_dist (l : List Sim) (x y : ℂ) :
    dist (encode l.length (word x l).toList) (encode l.length (word y l).toList)^2 = energy l * ‖x-y‖^2 := by
  change _ = (l.map weight).sum * _
  rw [← List.ofFn_getElem_eq_map, List.sum_ofFn,Finset.sum_mul]
  simp [encode, EuclideanSpace.dist_sq_eq, Fin.sum_univ_succ]
  simp [word,value,dist_eq_norm,← mul_sub,mul_pow,Complex.sq_norm]

/-- The length strata of strings are finite dimensional. A bad coloring in
all dimensions would thus give a bad coloring of strings. -/
theorem ramsey_from_strings {a : Fin 9 → Space 2}
    (hcircle : AlgebraicCircle (plane ∘ a)) : Ramsey a := by
  let z := plane ∘ a
  intro r hr
  by_contra! h
  choose c hc using fun n => h (dim n) (Module.finrank_pos (R:=ℝ) (M:=Block n))
  obtain ⟨x,hx,k,hk⟩ := paths_monochromatic z (equal_paths hcircle) (fun s => c s.toList.length (encode _ s.toList))
  let b i := encode x.length (word (z i) x).toList
  have congr : OAI.EuclideanRamsey.Congruent a b := fun i j => (sq_eq_sq₀ dist_nonneg dist_nonneg).mp (by
    simp [b,encode_dist,hx,z,←dist_eq_norm])
  obtain ⟨i,hi'⟩ := hc x.length b congr k
  have H := hk i
  apply hi'
  rwa [show (word (z i) x).toList.length = x.length by simp [word]] at H

end OAI.EuclideanRamsey.Radian
