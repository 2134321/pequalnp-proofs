import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_759_aux

theorem isAcyclic_of_lt {n : ℕ} (H : SimpleGraph (Fin n))
    (hord : ∀ v u1 u2 : Fin n, H.Adj u1 v → H.Adj u2 v → u1 < v → u2 < v → u1 = u2) :
    H.IsAcyclic := by
  intro v c hc
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image c.support.toFinset (fun w => w)
    ⟨v, List.mem_toFinset.mpr c.start_mem_support⟩
  have hm' : m ∈ c.support := List.mem_toFinset.mp hm
  have hc' : (c.rotate m hm').IsCycle := hc.rotate hm'
  have hle : ∀ w, w ∈ (c.rotate m hm').support → w ≤ m := fun w hw =>
    hmax w (List.mem_toFinset.mpr ((c.mem_support_rotate_iff m hm').mp hw))
  have h1 : H.Adj m (c.rotate m hm').snd := SimpleGraph.Walk.adj_snd hc'.not_nil
  have h2 : H.Adj (c.rotate m hm').penultimate m := SimpleGraph.Walk.adj_penultimate hc'.not_nil
  have hl1 : (c.rotate m hm').snd < m :=
    lt_of_le_of_ne (hle _ (SimpleGraph.Walk.getVert_mem_support _ _)) h1.ne'
  have hl2 : (c.rotate m hm').penultimate < m :=
    lt_of_le_of_ne (hle _ (SimpleGraph.Walk.getVert_mem_support _ _)) h2.ne
  exact hc'.snd_ne_penultimate (hord m _ _ h1.symm h2 hl1 hl2)

def edgePairs : List (Fin 6 × Fin 6) := [(0, 1), (0, 2), (0, 3), (1, 4), (4, 5)]

def rel (i j : Fin 6) : Bool :=
  edgePairs.any (fun p => (p.1 == i && p.2 == j) || (p.1 == j && p.2 == i))

abbrev G : SimpleGraph (Fin 6) := SimpleGraph.fromRel (fun i j => rel i j = true)

theorem acyc : G.IsAcyclic := by
  refine isAcyclic_of_lt G ?_
  decide

theorem has_edge : ∃ i j : Fin 6, G.Adj i j := ⟨0, 1, by decide⟩

theorem cover_lb : ∀ T : Finset (Fin 6), (∀ i j : Fin 6, G.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by
  decide

theorem cover_ub : ∀ i j : Fin 6, G.Adj i j → i ∈ ({0, 4} : Finset (Fin 6)) ∨ j ∈ ({0, 4} : Finset (Fin 6)) := by
  decide

theorem cover_card : ({0, 4} : Finset (Fin 6)).card = 2 := by
  decide

theorem card_edges : G.edgeFinset.card = 5 := by
  decide

theorem adj_cases : ∀ a b : Fin 6, G.Adj a b → (a, b) ∈ edgePairs ∨ (b, a) ∈ edgePairs := by
  decide

theorem fun_eq (x : Fin 6 → Bool) :
    ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) =
      decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  constructor
  · intro h
    simp only [Bool.or_eq_true, Bool.and_eq_true, or_assoc] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨0, 1, by decide, h1, h2⟩
    · exact ⟨0, 2, by decide, h1, h2⟩
    · exact ⟨0, 3, by decide, h1, h2⟩
    · exact ⟨1, 4, by decide, h1, h2⟩
    · exact ⟨4, 5, by decide, h1, h2⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    have hchk : ∀ a b : Fin 6, (a, b) ∈ edgePairs → x a = true → x b = true →
        ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) = true := by
      intro a b hab ha hb
      simp only [edgePairs, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [ha, hb]
    rcases adj_cases i j hij with hm | hm
    · exact hchk i j hm hi hj
    · exact hchk j i hm hj hi

end PEqualNP.Outside.L_meta_759_aux

theorem PEqualNP.Outside.L_meta_759 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) s ↔ 6 ≤ s := by
  intro s
  have hfun : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, PEqualNP.Outside.L_meta_759_aux.G.Adj i j ∧ x i = true ∧ x j = true)) :=
    funext PEqualNP.Outside.L_meta_759_aux.fun_eq
  rw [hfun]
  constructor
  · intro h
    have hb := PEqualNP.MetaComplexity.L104 6 2 s PEqualNP.Outside.L_meta_759_aux.G PEqualNP.Outside.L_meta_759_aux.acyc PEqualNP.Outside.L_meta_759_aux.has_edge PEqualNP.Outside.L_meta_759_aux.cover_lb h
    rw [PEqualNP.Outside.L_meta_759_aux.card_edges] at hb
    omega
  · intro hs
    obtain ⟨C, hC1, hC2, hC3⟩ := PEqualNP.MetaComplexity.L105 6 PEqualNP.Outside.L_meta_759_aux.G {0, 4} PEqualNP.Outside.L_meta_759_aux.has_edge PEqualNP.Outside.L_meta_759_aux.cover_ub
    rw [PEqualNP.Outside.L_meta_759_aux.card_edges, PEqualNP.Outside.L_meta_759_aux.cover_card] at hC2
    exact ⟨C, hC1, by omega, hC3⟩
