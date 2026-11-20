module
public import OAI.Combinatorics.EuclideanRamsey.PathWords

@[expose] public noncomputable section
namespace RadianRamsey
open OAI.EuclideanRamsey

/-! On two indices, the cost of a prescribed letter difference can be made
arbitrarily small: subdivide its displacement into `n` equal steps. The squared
cost decreases by a factor of `n`. The edits below use such short paths
to isolate successive commutators on one coordinate. -/

variable {ι : Type*} {a : ι → ℂ}

structure Walk (a : ι → ℂ) where
  w : ι → LetterGroup
  c : ℝ
  path : Path a w c
@[simps] def Walk.diag (g : LetterGroup) : Walk a := ⟨_,_,.diag g⟩
open Walk
@[simps] instance : Mul (Walk a) := ⟨fun u v => ⟨_,_,u.path.mul v.path⟩⟩

private def Axis (a : ι → ℂ) (i j : ι) (g : LetterGroup) :=
  ∀ δ > (0:ℝ), ∃ u : Walk a, u.c < δ ∧ u.w i = g ∧ u.w j = 1

private lemma edge {i j : ι} (h : a i ≠ a j) (x y : ℂ) :
    Axis a i j (atom x*(atom y)⁻¹) := by
  intro δ hδ
  let c := (x-y)/(a i-a j)
  obtain ⟨n,hn⟩ := exists_lt_nsmul hδ (‖c‖^2)
  let N := n+1
  let d := c/N
  let t (k : ℕ) := x-k*(d*(a i-a j))
  let p (k : ℕ) : Sim := (d,t k-d*a i)
  have pj k : value (a j) (p k) = t (k+1) := by simp [value,p,t]; ring
  have hl := Path.list (List.range N) fun k => (Path.copy (a:=a) (p k)).mul (.diag (atom (t (k+1)))⁻¹)
  refine ⟨⟨_,_,hl⟩,?_,?_,?_⟩
  · simp [p,d,←Complex.sq_norm]; field_simp
    simp [N] at *; rw [div_lt_iff₀ (by positivity)]; linarith
  · have e : t N = y := by dsimp [t,d,c,N]; push_cast; field_simp; ring
    simpa [value,p,div_eq_mul_inv,e,t] using List.prod_range_div' N (fun k => atom (t k))
  simp_all

private lemma axis {i j : ι} (h : a i ≠ a j) (g : LetterGroup) : Axis a i j g := by
  induction g using FreeGroup.induction_on with
  | one => exact fun _ h => ⟨diag 1,h,rfl,rfl⟩
  | of x => simpa using edge h x 0
  | inv_of x _ => simpa using edge h 0 x
  | mul x y hx hy =>
    intro δ hδ
    obtain ⟨u,hu,ui,uj⟩ := hx (δ/2) (by positivity)
    obtain ⟨v,hv,vi,vj⟩ := hy (δ/2) (by positivity)
    exact ⟨u*v,by simp; linarith,by simp [*],by simp [*]⟩

/-- Errors removable on `S` after any previous suffix `k`. Quantifying over
that suffix makes them a subgroup: concatenate the next correction after `k*v`. -/
def changes (a : ι → ℂ) (S : Finset ι) : Subgroup (ι → LetterGroup) where
  carrier := {r | ∀ (k : ι → LetterGroup) (δ : ℝ), 0 < δ → ∃ u v : Walk a, u.c+v.c < δ ∧
    ∀ j ∈ S, u.w j = (k j)⁻¹*r j*k j*v.w j}
  one_mem' := fun _ _ h => ⟨diag 1,diag 1,by simp_all,by simp⟩
  inv_mem' := by
    intro r hr k δ hδ
    obtain ⟨u,v,cu,h⟩ := hr k δ hδ
    exact ⟨v,u,add_comm u.c v.c ▸ cu,fun j hj => by simp [h j hj,mul_assoc]⟩
  mul_mem' := by
    intro r s hr hs k δ hδ
    obtain ⟨u,v,cu,h⟩ := hr k (δ/2) (by positivity)
    obtain ⟨x,y,cx,h'⟩ := hs (k*v.w) (δ/2) (by positivity)
    exact ⟨u*x,v*y,by simp; linarith,fun j hj => by simp [h j hj,h' j hj,mul_assoc]⟩

abbrev Lower (G : Type*) [Group G] := (⊤ : Subgroup G).lowerCentralSeries
private lemma deepen [DecidableEq ι] (ha : Function.Injective a) (i : ι) (S : Finset ι) (hi : i ∉ S) :
    Lower LetterGroup S.card ≤ (changes a (insert i S)).comap (MonoidHom.mulSingle _ i) := by
  induction S using Finset.induction_on with
  | empty => exact fun g _ k _ h => ⟨diag ((k i)⁻¹*g*k i),diag 1,by simp_all,by simp⟩
  | @insert j S hj ih =>
    rw [Finset.card_insert_of_notMem hj]
    apply Subgroup.commutator_le.mpr
    intro g hg b _ k δ hδ
    obtain ⟨u,v,cu,h⟩ := ih (by grind) hg k (δ/4) (by positivity)
    let t := (v.w i)⁻¹*(k i)⁻¹*b*k i
    obtain ⟨d,cd,dj,di⟩ := axis (ha.ne (show j≠i by grind)) (t⁻¹*(v.w j)⁻¹) (δ/4) (by positivity)
    let join (x y : Walk a) := x*diag t*d*y
    refine ⟨join u v,join v u,by simp [join]; linarith,fun l hl => ?_⟩
    by_cases h₁ : l=i <;> by_cases h₂ : l=j <;> subst_vars <;>
      simp_all [join,diag,t,Finset.mem_insert,commutatorElement_def,mul_assoc]

theorem deep_changes {a : Fin 9 → ℂ} (ha : Function.Injective a) {r : Fin 9 → LetterGroup}
    (hr : ∀ i, r i ∈ Lower LetterGroup 8) : r ∈ changes a Finset.univ :=
  Subgroup.pi_mem_of_mulSingle_mem r fun i => by
    simpa using deepen ha i (Finset.univ.erase i) (by simp) (by aesop)

end RadianRamsey
