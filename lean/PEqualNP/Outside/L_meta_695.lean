import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_695_aux

open PEqualNP.CircuitLowerBounds

def lset (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p : Fin n =>
    (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD w false = true)

def stepR (n : ℕ) (S : Finset (Fin n)) (C : Circuit) (a b : ℕ) : Prop :=
  b < a ∧ (∃ g : Gate, C.gates[a]? = some g ∧ n + b ∈ g.inputs) ∧
    lset n C (n + b) ⊆ S ∧ 2 ≤ (lset n C (n + b)).card

def psi (n : ℕ) (S : Finset (Fin n)) (C : Circuit) (Q : Finset ℕ) (w : ℕ) : Bool :=
  if n ≤ w ∧ (w - n) ∈ Q then
    match C.gates[w - n]? with
    | some g => g.op.eval (g.inputs.map (fun v => if h : v < w then psi n S C Q v else false))
    | none => false
  else decide (¬ lset n C w ⊆ S)
termination_by w
decreasing_by exact h

theorem psi_gate (n : ℕ) (S : Finset (Fin n)) (C : Circuit) (Q : Finset ℕ) (j : ℕ) (hj : j ∈ Q)
    (g : Gate) (hg : C.gates[j]? = some g) :
    psi n S C Q (n + j) =
      g.op.eval (g.inputs.map (fun w => if w < n + j then psi n S C Q w else false)) := by
  have h2 : n + j - n = j := by omega
  have h1 : n ≤ n + j ∧ (n + j - n) ∈ Q := ⟨Nat.le_add_right n j, by rw [h2]; exact hj⟩
  rw [psi, if_pos h1]
  simp only [h2, hg, dite_eq_ite]

theorem psi_out (n : ℕ) (S : Finset (Fin n)) (C : Circuit) (Q : Finset ℕ) (w : ℕ)
    (hw : ∀ j ∈ Q, w ≠ n + j) :
    psi n S C Q w = true ↔ ¬ lset n C w ⊆ S := by
  have h1 : ¬ (n ≤ w ∧ (w - n) ∈ Q) := by
    rintro ⟨hle, hq⟩
    exact hw (w - n) hq (by omega)
  rw [psi, if_neg h1]
  simp

theorem lt_of_get (C : Circuit) (c : ℕ) (g : Gate) (hg : C.gates[c]? = some g) : c < C.size := by
  by_contra hcon
  have hnone : C.gates[c]? = none := List.getElem?_eq_none (Nat.le_of_not_lt hcon)
  rw [hnone] at hg
  exact absurd hg (by simp)

end PEqualNP.Outside.L_meta_695_aux

theorem PEqualNP.Outside.L_meta_695 : ∀ (n r : ℕ) (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → r < C.size → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + r) false = true)) ⊆ S → 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + r) false = true)).card → ∃ (Q : Finset ℕ) (ψ : ℕ → Bool), r ∈ Q ∧ (∀ j ∈ Q, j < C.size ∧ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) ⊆ S ∧ 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)).card) ∧ (∀ j ∈ Q, j ≠ r → ∃ j' ∈ Q, j < j' ∧ ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j']? = some g ∧ n + j ∈ g.inputs) ∧ (∀ j ∈ Q, ∀ j' : ℕ, j' < j → (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g ∧ n + j' ∈ g.inputs) → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)) ⊆ S → 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)).card → j' ∈ Q) ∧ (∀ j ∈ Q, ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g → ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false))) ∧ (∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → (ψ w = true ↔ ¬ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (w) false = true)) ⊆ S)) := by
  intro n r S C _ hr hsub hcard
  classical
  obtain ⟨Q, hQ⟩ : ∃ Q : Finset ℕ, Q = (Finset.range C.size).filter
      (fun j => Relation.ReflTransGen (PEqualNP.Outside.L_meta_695_aux.stepR n S C) r j) := ⟨_, rfl⟩
  refine ⟨Q, PEqualNP.Outside.L_meta_695_aux.psi n S C Q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · subst hQ
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hr, Relation.ReflTransGen.refl⟩
  · subst hQ
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hlt, hreach⟩ := hj
    refine ⟨hlt, ?_⟩
    clear hlt
    induction hreach with
    | refl => exact ⟨hsub, hcard⟩
    | tail _ hstep _ => exact hstep.2.2
  · subst hQ
    intro j hj hne
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    rcases Relation.ReflTransGen.cases_tail hj.2 with h | ⟨c, hc, hstep⟩
    · exact absurd h hne
    · obtain ⟨hlt, ⟨g, hg, hin⟩, _⟩ := hstep
      refine ⟨c, ?_, hlt, g, hg, hin⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨PEqualNP.Outside.L_meta_695_aux.lt_of_get C c g hg, hc⟩
  · subst hQ
    intro j hj j' hlt hread hsub' hcard'
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    exact ⟨lt_trans hlt hj.1, hj.2.tail ⟨hlt, hread, hsub', hcard'⟩⟩
  · intro j hj g hg
    exact PEqualNP.Outside.L_meta_695_aux.psi_gate n S C Q j hj g hg
  · intro w hw
    exact PEqualNP.Outside.L_meta_695_aux.psi_out n S C Q w hw
