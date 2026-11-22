module

public import OverfullWork.KuhnOsthusTileBudgets
public import OverfullWork.KuhnOsthusWalkQuarters

@[expose] public section


/-! The spanning family of C₄ copies used in Claim 1 of
Kühn–Osthus Lemma 10.3. Split each original part into two
uniform halves and apply the four-part factor. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
universe u

/-- Disjoint oriented C₄ switches that cover the two entire parts.
The first two slots are sources and the last two are destinations. -/
theorem kuhn_osthus_spanning_switch_copies
    (C ε ε' d : ℝ) (hC : 0 < C) (hε : 0 < ε) (hTol : 4*ε ≤ ε')
    (hGap : 2*ε' < d) (hd : d ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] (G : Digraph V) (A B : Finset V) (m r : ℕ),
      0 < m → N ≤ 2*m → A.card = 2*m → B.card = 2*m → Disjoint A B →
      2*(Fintype.card V:ℝ) ≤ C*((2*m:ℕ):ℝ) →
      IsLowerSuperregularPair G ε d A B →
      0 < r → (m:ℝ)*ε' ≤ (r:ℝ) →
      28*((r:ℝ)+1) < (d-2*ε')^14*((d-ε')*(m:ℝ)) →
      ∃ f : Fin m × Fin 4 ↪ V,
        (∀ i, f (i,0) ∈ A ∧ f (i,1) ∈ A ∧ f (i,2) ∈ B ∧ f (i,3) ∈ B) ∧
        (∀ i, G.Adj (f (i,0)) (f (i,2)) ∧ G.Adj (f (i,0)) (f (i,3)) ∧
          G.Adj (f (i,1)) (f (i,2)) ∧ G.Adj (f (i,1)) (f (i,3))) ∧
        (∀ v ∈ A, ∃ i, f (i,0) = v ∨ f (i,1) = v) ∧
        ∀ v ∈ B, ∃ i, f (i,2) = v ∨ f (i,3) = v := by
  obtain ⟨N,hN⟩ := exists_ambient_uniform_refinement.{u,u} C ε hC hε 2 (by decide)
  refine ⟨N,?_⟩
  intro V _ G A B m r hm hLarge hA hB hDis hProfiles hPair hr hCut hBudget
  let profiles := arcProfiles (fun _ : Unit => G)
  have hProfile (S : Finset V) (hS : S.card = 2*m) :
      (Fintype.card (Unit × Bool × V):ℝ) ≤ C*(S.card:ℝ) := by
    rw [hS]
    simpa only [Fintype.card_prod,Fintype.card_unit,Fintype.card_bool,one_mul,Nat.cast_mul,
      Nat.cast_ofNat] using hProfiles
  let U := Classical.choice (hN profiles A m (hA.symm ▸ hLarge) hA (hProfile A hA))
  let W := Classical.choice (hN profiles B m (hB.symm ▸ hLarge) hB (hProfile B hB))
  let X : Fin 4 → Finset V := ![U.cells 0,U.cells 1,W.cells 0,W.cells 1]
  have hSize (a : Fin 4) : (X a).card = m := by
    fin_cases a
    · exact U.size 0
    · exact U.size 1
    · exact W.size 0
    · exact W.size 1
  have hAway (a b : Fin 4) (hne : a ≠ b) : Disjoint (X a) (X b) := by
    fin_cases a <;> fin_cases b <;> first
      | exact (hne rfl).elim
      | exact U.disjoint _ _ (by decide)
      | exact W.disjoint _ _ (by decide)
      | exact hDis.mono (U.subset _) (W.subset _)
      | exact hDis.symm.mono (W.subset _) (U.subset _)
  have hHalf (i j : Fin 2) : IsLowerSuperregularPair G ε' d (U.cells i) (W.cells j) := by
    have hε' : 0 < ε' := by linarith
    have hε'₁ : ε' ≤ 1 := by linarith
    have hp := IsLowerSuperregularPair.on_residual_style_cells G ⊥ bot_le A B
      (U.cells i) (W.cells j) (U.subset i) (W.subset j)
      (card_pos.mp (by rwa [U.size])) ((U.size i).trans (W.size j).symm)
      2 0 d ε ε' 0 (by decide) hε.le hε' hε'₁ (by norm_num) (by linarith)
      (by rw [hA,U.size]) (by rw [hB,W.size])
      ((U.uniform i).inProfile ()) ((W.uniform j).outProfile ())
      (by norm_num; linarith only [hTol]) (by simp) (fun _ _ => by simp [outDegree])
      (fun _ _ => by simp [inDegree,inNeighbours]) hPair
    simpa only [sdiff_bot] using hp
  have hLower (a b : Fin 4) (hab : rectangleTileEdges a b = true) :
      IsLowerSuperregularPair G ε' d (X a) (X b) := by
    fin_cases a <;> fin_cases b <;> first
      | exact hHalf 0 0
      | exact hHalf 0 1
      | exact hHalf 1 0
      | exact hHalf 1 1
      | exact ((by decide : rectangleTileEdges _ _ ≠ true) hab).elim
  have hη : 0 ≤ d-2*ε' := by linarith
  have hη₁ : d-2*ε' ≤ 1 := by linarith
  have hδ : 0 ≤ d-ε' := by linarith
  obtain ⟨hs,hSeed,hAdd,hRepair⟩ := geometric_tile_budgets m r 4 14 (d-2*ε') (d-ε')
    (by decide) (by decide) hη hη₁ hδ hBudget
  have hPairs (a b : Fin 4) (hab : rectangleTileEdges a b = true) :=
    (hLower a b hab).tile_bounds G (X a) (X b) d ε' m r (hSize a) (hSize b) hCut
  obtain ⟨P⟩ := exists_superregular_rectangle_tile_factor X G r (d-2*ε') (d-ε') _
    hr hη hη₁ (by linarith) hs hSeed hAdd hRepair hSize hAway
    (fun a b h => (hPairs a b h).1) (fun a b h => (hPairs a b h).2.1)
    (fun a b h => (hPairs a b h).2.2)
  refine ⟨P.vertices,fun i => ⟨U.subset 0 (P.mem i 0),U.subset 1 (P.mem i 1),
    W.subset 0 (P.mem i 2),W.subset 1 (P.mem i 3)⟩,fun i =>
    ⟨P.edge i 0 2 (by decide),P.edge i 0 3 (by decide),
      P.edge i 1 2 (by decide),P.edge i 1 3 (by decide)⟩,?_,?_⟩
  · intro v hv
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp (U.cover.symm ▸ hv)
    fin_cases i
    · obtain ⟨j,hj⟩ := P.covers_part 0 (hSize 0) v hi
      exact ⟨j,.inl hj⟩
    · obtain ⟨j,hj⟩ := P.covers_part 1 (hSize 1) v hi
      exact ⟨j,.inr hj⟩
  · intro v hv
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp (W.cover.symm ▸ hv)
    fin_cases i
    · obtain ⟨j,hj⟩ := P.covers_part 2 (hSize 2) v hi
      exact ⟨j,.inl hj⟩
    · obtain ⟨j,hj⟩ := P.covers_part 3 (hSize 3) v hi
      exact ⟨j,.inr hj⟩

end OverfullWork.DirectedRobustExpansion
