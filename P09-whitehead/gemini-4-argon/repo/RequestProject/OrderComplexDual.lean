module

public import RequestProject.SurfaceRegular
public import RequestProject.MomentAngleConnected

@[expose] public section

namespace FiniteChains.ASC

open Relation

variable {P : Type}

section
variable [PartialOrder P]

theorem SurfaceRank.rk_flag (S : SurfaceRank P) {x y z : P} (hxy : x < y) (hyz : y < z) :
    S.rk x = 0 ∧ S.rk y = 1 ∧ S.rk z = 2 := by
  have := S.rk_lt_of_lt hxy; have := S.rk_lt_of_lt hyz; have := S.rk_le_two z; omega

def FaceAdj (S : SurfaceRank P) (f f' : P) : Prop := ∃ e : P, S.rk e = 1 ∧ e < f ∧ e < f'

def FacesConnected (S : SurfaceRank P) : Prop :=
  ∀ f f' : P, S.rk f = 2 → S.rk f' = 2 → ReflTransGen (FaceAdj S) f f'

def FaceEdges (S : SurfaceRank P) : Prop :=
  ∀ v v' f : P, S.rk v = 0 → S.rk v' = 0 → S.rk f = 2 → v < f → v' < f → v ≠ v' →
    ∃ e : P, v < e ∧ v' < e ∧ e < f

end

variable [DecidableEq P]

theorem card_inter_insert {x y z z' : P} (hxy : x ≠ y) (hz : z ∉ ({x, y} : Finset P))
    (hz' : z' ∉ ({x, y} : Finset P)) (hne : z ≠ z') :
    ((insert z ({x, y} : Finset P)) ∩ (insert z' ({x, y} : Finset P))).card = 2 := by
  rw [show (insert z ({x, y} : Finset P)) ∩ (insert z' ({x, y} : Finset P)) = {x, y} by
    ext w; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at *; grind]
  exact Finset.card_pair hxy

variable [PartialOrder P]

theorem isTri_of_flag {v e f : P} (hve : v < e) (hef : e < f) :
    IsTri (orderComplex P) ({v, e, f} : Finset P) :=
  ⟨by rw [mem_orderComplex]; simpa [Finset.coe_insert] using
      isChain_triple (.inl hve.le) (.inl (hve.trans hef).le) (.inl hef.le),
   by rw [Finset.card_insert_of_notMem (by simp [hve.ne, (hve.trans hef).ne]), Finset.card_pair hef.ne]⟩

namespace SurfaceRank

variable (S : SurfaceRank P)

theorem conn_in_face (hfe : FaceEdges S) {f v e v' e' : P} (hf : S.rk f = 2)
    (hv : S.rk v = 0) (hve : v < e) (hef : e < f)
    (hv' : S.rk v' = 0) (hv'e' : v' < e') (he'f : e' < f) :
    ReflTransGen (TriAdj (orderComplex P)) ({v, e, f} : Finset P) ({v', e', f} : Finset P) := by
  have stepE {u e₁ e₂ : P} (h1 : u < e₁) (h2 : e₁ < f) (h3 : u < e₂) (h4 : e₂ < f) :
      ReflTransGen (TriAdj (orderComplex P)) ({u, e₁, f} : Finset P) ({u, e₂, f} : Finset P) := by
    by_cases h : e₁ = e₂
    · subst h; exact .refl
    · refine .single ⟨isTri_of_flag h1 h2, isTri_of_flag h3 h4, ?_⟩
      rw [Finset.insert_comm u e₁, Finset.insert_comm u e₂]
      exact card_inter_insert (h1.trans h2).ne (by simp [h1.ne', h2.ne]) (by simp [h3.ne', h4.ne]) h
  by_cases hvv' : v = v'
  · subst hvv'; exact stepE hve hef hv'e' he'f
  · obtain ⟨e'', hve'', hv'e'', he''f⟩ :=
      hfe v v' f hv hv' hf (hve.trans hef) (hv'e'.trans he'f) hvv'
    exact ((stepE hve hef hve'' he''f).tail
      ⟨isTri_of_flag hve'' he''f, isTri_of_flag hv'e'' he''f,
        card_inter_insert he''f.ne (by simp [hve''.ne, (hve''.trans he''f).ne])
          (by simp [hv'e''.ne, (hv'e''.trans he''f).ne]) hvv'⟩).trans
      (stepE hv'e'' he''f hv'e' he'f)

theorem dual_connected (hfe : FaceEdges S) (hfc : FacesConnected S) :
    ∀ σ σ' : Finset P, IsTri (orderComplex P) σ → IsTri (orderComplex P) σ' →
      ReflTransGen (TriAdj (orderComplex P)) σ σ' := by
  have hflag {σ : Finset P} (h : IsTri (orderComplex P) σ) :
      ∃ v e f : P, v < e ∧ e < f ∧ σ = ({v, e, f} : Finset P) := by
    obtain ⟨hface, hcard⟩ := h
    have hchain : IsChain (· ≤ ·) (σ : Set P) := mem_orderComplex.1 hface
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 hcard
    have cmp {x y : P} (hx : x ∈ ({a, b, c} : Finset P)) (hy : y ∈ ({a, b, c} : Finset P)) (hxy : x ≠ y) :
        x < y ∨ y < x :=
      (hchain (by exact_mod_cast hx) (by exact_mod_cast hy) hxy).imp
        (lt_of_le_of_ne · hxy) (lt_of_le_of_ne · hxy.symm)
    rcases cmp (by simp) (by simp) hab with h1 | h1 <;>
      rcases cmp (by simp) (by simp) hbc with h2 | h2 <;>
      rcases cmp (by simp) (by simp) hac with h3 | h3
    · exact ⟨a, b, c, h1, h2, rfl⟩
    · exact absurd (h1.trans h2) (asymm h3)
    · exact ⟨a, c, b, h3, h2, by ext; simp; tauto⟩
    · exact ⟨c, a, b, h3, h1, by ext; simp; tauto⟩
    · exact ⟨b, a, c, h1, h3, by ext; simp; tauto⟩
    · exact ⟨b, c, a, h2, h3, by ext; simp; tauto⟩
    · exact absurd (h2.trans h1) (asymm h3)
    · exact ⟨c, b, a, h2, h1, by ext; simp; tauto⟩
  intro σ σ' hσ hσ'
  obtain ⟨v, e, f, hve, hef, rfl⟩ := hflag hσ
  obtain ⟨v', e', f', hv'e', he'f', rfl⟩ := hflag hσ'
  obtain ⟨hv, -, hf⟩ := S.rk_flag hve hef
  obtain ⟨hv', -, hf'⟩ := S.rk_flag hv'e' he'f'
  clear hσ'
  have hconn := hfc f f' hf hf'
  induction hconn generalizing v' e' with
  | refl => exact S.conn_in_face hfe hf hv hve hef hv' hv'e' he'f'
  | @tail c f' _ hcd ih =>
      obtain ⟨d, hd, hdc, hdf'⟩ := id hcd
      have hc : S.rk c = 2 := by have := S.rk_lt_of_lt hdc; have := S.rk_le_two c; omega
      have hfd : S.rk f' = 2 := by have := S.rk_lt_of_lt hdf'; have := S.rk_le_two f'; omega
      obtain ⟨w, -, -, hwd, -, -⟩ := S.two_vertices d hd
      have hw : S.rk w = 0 := by have := S.rk_lt_of_lt hwd; omega
      have s2 : ReflTransGen (TriAdj (orderComplex P)) ({w, d, c} : Finset P) ({w, d, f'} : Finset P) := by
        by_cases hcf' : c = f'
        · subst hcf'; exact .refl
        · refine .single ⟨isTri_of_flag hwd hdc, isTri_of_flag hwd hdf', ?_⟩
          rw [show ({w, d, c} : Finset P) = insert c {w, d} by ext; simp; tauto,
            show ({w, d, f'} : Finset P) = insert f' {w, d} by ext; simp; tauto]
          exact card_inter_insert hwd.ne (by simp [hdc.ne', (hwd.trans hdc).ne'])
            (by simp [hdf'.ne', (hwd.trans hdf').ne']) hcf'
      exact ((ih w d hwd hdc hw hc).trans s2).trans (S.conn_in_face hfe hfd hw hwd hdf' hv' hv'e' he'f')
