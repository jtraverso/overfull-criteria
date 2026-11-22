module

public import OverfullWork.KuhnOsthusSwitchExchanges

@[expose] public section


/-! The sweep that merges the primary factor in Kühn–Osthus Lemma 10.2.
Its representatives are the initial vertices of the paths in (CyA1). -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V : Type*} [Fintype V] {t : ℕ}

/-- Sweep the C₄ switches in path order, using a switch just when the two
adjacent representatives are on different cycles of the primary factor.
Disjoint switch sources keep every later switch available. -/
theorem c4_sweep_merges_primary_with_invariant (F : Fin t → Equiv.Perm V) {i j : Fin t}
    (hij : i ≠ j) (m : ℕ) (root left right : ℕ → V)
    (hSources : ∀ p < m, left p ≠ right p)
    (hDistinct : ∀ p q, p < q → q < m →
      left q ≠ left p ∧ left q ≠ right p ∧ right q ≠ left p ∧ right q ≠ right p)
    (hRoots : ∀ p < m,
      (F i).SameCycle (root p) (left p) ∧ (F i).SameCycle (root (p+1)) (right p))
    (hCover : ∀ z, ∃ p ≤ m, (F i).SameCycle (root p) z)
    (hCross : ∀ p < m, F i (left p) = F j (right p) ∧ F i (right p) = F j (left p))
    (hDis : ∀ a b, a ≠ b → ∀ z, F a z ≠ F b z)
    (P : Equiv.Perm V → Prop) (hInit : P (F j))
    (hSwitch : ∀ p < m, ∀ σ, P σ → P (switchSuccessors σ (left p) (right p))) :
    ∃ G : Fin t → Equiv.Perm V,
      matchingUnion G = matchingUnion F ∧
      (∀ a b, a ≠ b → ∀ z, G a z ≠ G b z) ∧
      HasSpanningCycle (fun x y => G i x = y) ∧
      P (G j) ∧
      factorCycleTotal G % 2 = factorCycleTotal F % 2 ∧
      ∀ a z, (a ≠ i ∧ a ≠ j) ∨ (∀ p < m, z ≠ left p ∧ z ≠ right p) → G a z = F a z := by
  have hStep (n : ℕ) (hn : n ≤ m) :
      ∃ G : Fin t → Equiv.Perm V,
        matchingUnion G = matchingUnion F ∧
        (∀ a b, a ≠ b → ∀ z, G a z ≠ G b z) ∧
        (∀ a b, (F i).SameCycle a b → (G i).SameCycle a b) ∧
        (∀ p ≤ n, (G i).SameCycle (root 0) (root p)) ∧
        P (G j) ∧
        factorCycleTotal G % 2 = factorCycleTotal F % 2 ∧
        ∀ a z, (a ≠ i ∧ a ≠ j) ∨ (∀ p < n, z ≠ left p ∧ z ≠ right p) → G a z = F a z := by
    induction n with
    | zero =>
      refine ⟨F,rfl,hDis,fun _ _ h => h, ?_, hInit, rfl, fun _ _ _ => rfl⟩
      intro p hp
      have he : p = 0 := by omega
      rw [he]
    | succ n ih =>
      obtain ⟨G,hUnion,hDisG,hOld,hPrev,hP,hParity,hKeep⟩ := ih (by omega)
      have hnM : n < m := by omega
      obtain ⟨hL,hR⟩ := hRoots n hnM
      have hLC := hOld _ _ hL
      have hRC := hOld _ _ hR
      by_cases hTogether : (G i).SameCycle (left n) (right n)
      · refine ⟨G,hUnion,hDisG,hOld,?_,hP,hParity,?_⟩
        · intro p hp
          by_cases hpn : p ≤ n
          · exact hPrev p hpn
          · have he : p = n+1 := by omega
            rw [he]
            exact (hPrev n le_rfl).trans (hLC.trans (hTogether.trans hRC.symm))
        · intro a z h
          apply hKeep
          exact h.imp_right (fun hz p hp => hz p (by omega))
      let G' := switchFactors G {i,j} (left n) (right n)
      have hAvailL : ∀ a, G a (left n) = F a (left n) := fun a =>
        hKeep a _ (.inr fun p hp =>
          ⟨(hDistinct p n hp hnM).1, (hDistinct p n hp hnM).2.1⟩)
      have hAvailR : ∀ a, G a (right n) = F a (right n) := fun a =>
        hKeep a _ (.inr fun p hp =>
          ⟨(hDistinct p n hp hnM).2.2.1, (hDistinct p n hp hnM).2.2.2⟩)
      have hCrossL : G i (left n) = G j (right n) := by
        rw [hAvailL,hAvailR]
        exact (hCross n hnM).1
      have hCrossR : G i (right n) = G j (left n) := by
        rw [hAvailR,hAvailL]
        exact (hCross n hnM).2
      obtain ⟨hUnion',hDis'⟩ := c4_exchange_conserves G hCrossL hCrossR hDisG
      have hEq : G' i = switchSuccessors (G i) (left n) (right n) := by
        simp [G',switchFactors]
      have hEqR : G' j = switchSuccessors (G j) (left n) (right n) := by
        simp [G',switchFactors]
      have hP' : P (G' j) := hEqR ▸ hSwitch n hnM (G j) hP
      obtain ⟨hNewTogether,hNewOld,_,_⟩ := switchSuccessors_merge (G i) (left n) (right n) hTogether
      rw [← hEq] at hNewTogether hNewOld
      refine ⟨G',hUnion'.trans hUnion,hDis',fun a b h => hNewOld a b (hOld a b h), ?_,hP',
        (c4_exchange_cycle_parity G hij (hSources n hnM)).trans hParity, ?_⟩
      · intro p hp
        by_cases hpn : p ≤ n
        · exact hNewOld _ _ (hPrev p hpn)
        · have he : p = n+1 := by omega
          rw [he]
          exact (hNewOld _ _ ((hPrev n le_rfl).trans hLC)).trans
            (hNewTogether.trans (hNewOld _ _ hRC.symm))
      · intro a z h
        have hAvoid : a ∉ ({i,j} : Finset (Fin t)) ∨ z ≠ left n ∧ z ≠ right n :=
          h.imp (fun ha => by simp [ha.1,ha.2]) (fun hz => hz n (by omega))
        exact (switchFactors_protects G {i,j} hAvoid).trans
          (hKeep a z (h.imp_right fun hz p hp => hz p (by omega)))
  obtain ⟨G,hUnion,hDisG,hOld,hPrev,hP,hParity,hKeep⟩ := hStep m le_rfl
  refine ⟨G,hUnion,hDisG,spanning_cycle_of_single_orbit (G i) (root 0) ?_,hP,hParity,hKeep⟩
  intro z
  obtain ⟨p,hp,hz⟩ := hCover z
  exact (hPrev p hp).trans (hOld _ _ hz)

/-- The primary sweep with its arc and parity guarantees. -/
theorem c4_sweep_merges_primary (F : Fin t → Equiv.Perm V) {i j : Fin t}
    (hij : i ≠ j) (m : ℕ) (root left right : ℕ → V)
    (hSources : ∀ p < m, left p ≠ right p)
    (hDistinct : ∀ p q, p < q → q < m →
      left q ≠ left p ∧ left q ≠ right p ∧ right q ≠ left p ∧ right q ≠ right p)
    (hRoots : ∀ p < m,
      (F i).SameCycle (root p) (left p) ∧ (F i).SameCycle (root (p+1)) (right p))
    (hCover : ∀ z, ∃ p ≤ m, (F i).SameCycle (root p) z)
    (hCross : ∀ p < m, F i (left p) = F j (right p) ∧ F i (right p) = F j (left p))
    (hDis : ∀ a b, a ≠ b → ∀ z, F a z ≠ F b z) :
    ∃ G : Fin t → Equiv.Perm V,
      matchingUnion G = matchingUnion F ∧
      (∀ a b, a ≠ b → ∀ z, G a z ≠ G b z) ∧
      HasSpanningCycle (fun x y => G i x = y) ∧
      factorCycleTotal G % 2 = factorCycleTotal F % 2 ∧
      ∀ a z, (a ≠ i ∧ a ≠ j) ∨ (∀ p < m, z ≠ left p ∧ z ≠ right p) → G a z = F a z := by
  obtain ⟨G,hUnion,hDisG,hHam,_,hParity,hKeep⟩ :=
    c4_sweep_merges_primary_with_invariant F hij m root left right hSources hDistinct hRoots
      hCover hCross hDis (fun _ => True) trivial (fun _ _ _ _ => trivial)
  exact ⟨G,hUnion,hDisG,hHam,hParity,hKeep⟩

end OverfullWork.DirectedRobustExpansion
