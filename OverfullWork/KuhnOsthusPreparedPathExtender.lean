module

public import OverfullWork.KuhnOsthusPhysicalSuccessorPairs

@[expose] public section


/-! Assemble the Hamilton extension in Lemma 8.3 from the prepared
chord routes, their restricted reserve, and the untouched styles of
each successor pair. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open DirectedDemandHall (Arc)
open scoped Classical
universe u

/-- Given the physical extender bounds, carry out the whole passage
from the basic path system and its routes to a Hamilton cycle. The
untouched class `B i` supplies the free vertices in both directions. -/
theorem exists_hamilton_extension_of_prepared_chord_routes
    (d ε ν τ γ : ℝ) (hν : 0 < ν) (hWidth : ε+ν ≤ τ) (hε : 0 ≤ ε)
    (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hd : 0 < d) (hCost : ν ≤ d*τ) (hDegrees : γ ≤ d) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {n : ℕ}
      (G : Digraph (Fin (n+1))) (Q H R : Digraph V)
      (cluster : V → Fin (n+1)) (l : Arc Q → List (Fin (n+1)))
      (A B : Fin (n+1) → Finset V) (m e : ℕ) (r : Fin (n+1) → ℕ) (η : ℝ),
      let s := finRotate (n+1)
      let U i := (univ : Finset V).filter (fun x => cluster x = i)
      IsDirectedPathSystem Q →
      (∀ i, ¬ G.Adj i i) →
      (∀ j : Arc Q, DirectedListRoutes.Route (reindexSources G s.symm)
        (cluster j.val.2) (s (cluster j.val.1)) (l j)) →
      0 < m → 50*e ≤ m →
      (∀ i, 50*(A i).card = 24*m) →
      (∀ i, A i ⊆ U i) → (∀ i, B i ⊆ U i) →
      (∀ i, (U i).card = m) →
      (∀ i x, x ∈ A i ∨ x ∈ B i → ¬ IncidentTo Q x) →
      (∀ i, Disjoint (A i) (B i)) →
      (∀ i j, G.Adj i j → ∀ S ⊆ A i, ∀ T ⊆ A j,
        e < S.card → e < T.card → 0 < incidences H S T) →
      (∀ i, 100*(∑ j, chordInteriorLoad s (l j) i) ≤ m) →
      (∀ i, 10*(∑ j : Arc Q, if s.symm (cluster j.val.2) = i then (1:ℕ) else 0) ≤ m) →
      (∀ i, 10*(∑ j : Arc Q, if s (cluster j.val.1) = i then (1:ℕ) else 0) ≤ m) →
      (∀ i, (B i).Nonempty ∧ N ≤ (B i).card) →
      (∀ i, η*m ≤ ε*((B i).card:ℝ)) →
      (∀ i, 0 < r i ∧ ε*m ≤ (r i:ℝ) ∧ (r i:ℝ) ≤ d*((B i).card:ℝ)) →
      (∀ i, ∀ X ⊆ U i, ∀ Y ⊆ U (s i), η*m ≤ (X.card:ℝ) → η*m ≤ (Y.card:ℝ) →
        d*(X.card:ℝ)*(Y.card:ℝ) ≤ (incidences R X Y:ℝ)) →
      (∀ i v, v ∈ U (s i) → d*m ≤ (inNeighbours R (B i) v:ℝ)) →
      (∀ i v, v ∈ U i → d*m ≤ (((B (s i)).filter (R.Adj v)).card:ℝ)) →
      ∃ ρ : Equiv.Perm V, HasSpanningCycle (fun x y => ρ x = y) ∧
        (∀ x y, Q.Adj x y → ρ x = y) ∧ (∀ x, ((Q ⊔ H) ⊔ R).Adj x (ρ x)) := by
  obtain ⟨N,hN⟩ := exists_hamilton_completion_of_physical_successor_pairs.{u}
    d ε ν τ γ hν hWidth hε hτγ hγ hd hCost hDegrees
  refine ⟨N,?_⟩
  intro V _ n G Q H R cluster l A B m e r η s U hQ hG hRoute hm he hA hAU hBU hU hFresh hDis
    hChord hInt hFrom hTo hB hScale hr hRect hIn hOut
  obtain ⟨D,hDQ,hDSub,hPath,hBalance,hUntouched⟩ :=
    exists_balanced_extension_for_routes G Q H cluster s hQ l hG hRoute A m e hm he hA
      (fun i x hx => (mem_filter.mp (hAU i hx)).2)
      (fun i x hx => hFresh i x (Or.inl hx)) hChord hInt (by
        intro i
        convert hFrom i using 2
        apply sum_congr rfl
        intro j _
        by_cases h : s.symm (cluster j.val.2) = i <;> simp [h]) (by
        intro i
        convert hTo i using 2
        apply sum_congr rfl
        intro j _
        by_cases h : s (cluster j.val.1) = i <;> simp [h]) (by
        intro i
        have he (j : Fin (n+1)) :
            (@Finset.filter V (fun x => cluster x = j) (fun _ => Classical.propDecidable _) univ).card =
              (U j).card := by
          congr 1
          ext x
          simp only [U,mem_filter]
        exact (he i).trans ((hU i).trans ((hU (s i)).symm.trans (he (s i)).symm)))
  let S := freeOut D cluster
  let T i := freeIn D cluster (s i)
  have hFree (i : Fin (n+1)) {x : V} (hx : x ∈ B i) :
      x ∈ freeOut D cluster i ∧ x ∈ freeIn D cluster i := by
    have hc := (mem_filter.mp (hBU i hx)).2
    have hApart : x ∉ A (cluster x) := fun ha => disjoint_left.mp (hDis i) (hc ▸ ha) hx
    exact hc ▸ hUntouched x (hFresh i x (Or.inr hx)) hApart
  have hSB (i : Fin (n+1)) : B i ⊆ S i := fun _ hx => (hFree i hx).1
  have hTB (i : Fin (n+1)) : B (s i) ⊆ T i := fun _ hx => (hFree (s i) hx).2
  have hSU (i : Fin (n+1)) : S i ⊆ U i :=
    fun _ hx => mem_filter.mpr ⟨mem_univ _,(mem_freeOut.mp hx).1⟩
  have hTU (i : Fin (n+1)) : T i ⊆ U (s i) :=
    fun _ hx => mem_filter.mpr ⟨mem_univ _,(mem_freeIn.mp hx).1⟩
  have hLow (i : Fin (n+1)) : ((B i).card:ℝ) ≤ (S i).card := by
    exact_mod_cast card_le_card (hSB i)
  have hHigh (i : Fin (n+1)) : ((S i).card:ℝ) ≤ m := by
    exact_mod_cast (card_le_card (hSU i)).trans_eq (hU i)
  have hScale' (i : Fin (n+1)) : η*m ≤ ε*((S i).card:ℝ) :=
    (hScale i).trans (mul_le_mul_of_nonneg_left (hLow i) hε)
  have hN' (i : Fin (n+1)) : N ≤ (S i).card := (hB i).2.trans (card_le_card (hSB i))
  have hO (i : Fin (n+1)) : ∃ x, x ∈ freeIn D cluster i ∧ x ∈ S i := by
    obtain ⟨x,hx⟩ := (hB i).1
    exact ⟨x,(hFree i hx).2,(hFree i hx).1⟩
  have hCut (i : Fin (n+1)) : 0 < r i ∧ ε*((S i).card:ℝ) ≤ (r i:ℝ) ∧
      (r i:ℝ) ≤ d*((S i).card:ℝ) :=
    ⟨(hr i).1,(mul_le_mul_of_nonneg_left (hHigh i) hε).trans (hr i).2.1,
      (hr i).2.2.trans (mul_le_mul_of_nonneg_left (hLow i) hd.le)⟩
  obtain ⟨ρ,hCycle,hKeep,hEdge⟩ := hN D R cluster r hPath hBalance hO hN' hCut
    (fun i X hx Y hy hX hY => hRect i X (hx.trans (hSU i)) Y (hy.trans (hTU i))
      ((hScale' i).trans hX) ((hScale' i).trans hY)) (by
    intro i v hv
    have hMono : inNeighbours R (B i) v ≤ inNeighbours R (S i) v :=
      card_le_card (filter_subset_filter _ (hSB i))
    have hCast : (inNeighbours R (B i) v:ℝ) ≤ (inNeighbours R (S i) v:ℝ) := by
      exact_mod_cast hMono
    exact (mul_le_mul_of_nonneg_left (hHigh i) hd.le).trans
      ((hIn i v (hTU i hv)).trans hCast)) (by
    intro i v hv
    have hMono := card_le_card (filter_subset_filter (R.Adj v) (hTB i))
    have hCast : (((B (s i)).filter (R.Adj v)).card:ℝ) ≤ (((T i).filter (R.Adj v)).card:ℝ) := by
      exact_mod_cast hMono
    exact (mul_le_mul_of_nonneg_left (hHigh i) hd.le).trans
      ((hOut i v (hSU i hv)).trans hCast))
  exact ⟨ρ,hCycle,fun x y h => hKeep x y (hDQ h),
    fun x => (sup_le_sup_right hDSub R) (hEdge x)⟩

end OverfullWork.DirectedRobustExpansion
