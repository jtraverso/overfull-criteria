module

public import OverfullWork.KuhnOsthusCycleAbsorberReserveMiddle
public import OverfullWork.RobustRegularFactor

@[expose] public section


/-! Preserve the pair and endpoint data of Lemma 7.6 after the
successive physical deletions in the proof of Theorem 1.2. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs DirectedArcSelection
open scoped Classical
variable {V I J : Type*} [Fintype V]

/-- The prescribed exceptional endpoints only lose neighbours that
the reserve actually uses at that vertex. -/
theorem endpoint_neighbourhoods_after_reserve_deletion (G C : Digraph V)
    (hC : C ≤ G) (S : Finset V) (z : V) :
    inNeighbours G S z ≤ inNeighbours (G \ C) S z + inDegree C z ∧
      outTo G S z ≤ outTo (G \ C) S z + outDegree C z := by
  have hi := DirectedArcSelection.incidence_partition G C hC S {z}
  have ho := DirectedArcSelection.incidence_partition G C hC {z} S
  simp only [incidences,sum_singleton] at hi
  have ho' : (incidences (G \ C) {z} S:ℝ)+incidences C {z} S = incidences G {z} S := by
    exact_mod_cast ho
  simp only [incidences_eq_sum_outTo,sum_singleton] at ho'
  have hOutSum : outTo (G \ C) S z + outTo C S z = outTo G S z := by exact_mod_cast ho'
  have hin : inNeighbours C S z ≤ inDegree C z :=
    card_le_card (filter_subset_filter _ (subset_univ _))
  have hout : outTo C S z ≤ outDegree C z :=
    card_le_card (filter_subset_filter _ (subset_univ _))
  exact ⟨hi ▸ Nat.add_le_add_left hin _,hOutSum ▸ Nat.add_le_add_left hout _⟩

/-- Both pair families needed by Lemma 7.6 survive a bounded deletion
on the same retained clusters. -/
theorem wound_host_pairs_after_deletion (G H : Digraph V)
    (X : I → Finset V) (R : Digraph I) (s : Equiv.Perm I)
    (m loss : ℕ) (ε η δ d : ℝ) (hH : H ≤ G)
    (hm : 0 < m) (hSize : ∀ i, (X i).card = m)
    (hη : 0 < η) (hη₁ : η ≤ 1) (hδ : 0 ≤ δ) (hd : 0 ≤ d)
    (hTol : 2*(ε+δ) ≤ η) (hLoss : (loss:ℝ) ≤ δ*((m:ℝ)*η))
    (hDegree : ∀ v, inDegree H v ≤ loss ∧ outDegree H v ≤ loss)
    (hReg : ∀ i j, R.Adj i j →
      IsUniform G ε (X i) (X j) ∧ d+(ε+δ) ≤ density G (X i) (X j))
    (hPairs : ∀ i, IsLowerSuperregularPair G ε d (X i) (X (s i))) :
    (∀ i j, R.Adj i j → IsUniform (G \ H) η (X i) (X j) ∧ d ≤ density (G \ H) (X i) (X j)) ∧
    (∀ i, IsLowerSuperregularPair (G \ H) η d (X i) (X (s i))) := by
  have hPos (i : I) : (X i).Nonempty := card_pos.mp ((hSize i).symm ▸ hm)
  have hScale (i : I) : ((X i).card:ℝ)*ε ≤ ((X i).card:ℝ)*η :=
    mul_le_mul_of_nonneg_left (by linarith only [hTol,hδ,hη]) (Nat.cast_nonneg _)
  refine ⟨?_,?_⟩
  · intro i j hij
    obtain ⟨hUniform,hClose⟩ := uniform_on_pair_remainder G H hH (X i) (X j) (X i) (X j)
      Subset.rfl Subset.rfl (hPos i) (hPos j) ε η δ loss hη hη₁ (hScale i) (hScale j)
      hTol (by simpa only [hSize] using hLoss) hδ (fun v _ => (hDegree v).1) (hReg i j hij).1
    exact ⟨hUniform,by linarith only [(abs_lt.mp hClose).1,(hReg i j hij).2]⟩
  · intro i
    exact IsLowerSuperregularPair.after_bounded_arc_deletion hH loss hDegree
      (X i) (X (s i)) (hPos i) (hPos (s i)) m (hSize i) (hSize (s i)) ε η d δ
      hη hη₁ hδ hd hTol hLoss (hPairs i)

/-- Keep the reduced pairs, successor pairs, and endpoint budgets on
one physical host. The second reserve is chosen outside the first.
The endpoint estimate can use the smaller deletion bound specific
to the exceptional vertices. -/
theorem kuhn_osthus_shared_residual_host_after_deletions
    (G P C : Digraph V) (Z : Finset V) (X : I → Finset V) (R : Digraph I)
    (s : Equiv.Perm I) (eligible : J → Finset V)
    (m p c pZ cZ budget : ℕ) (ε η δ d : ℝ)
    (hP : P ≤ G) (hC : C ≤ G \ P)
    (hm : 0 < m) (hSize : ∀ i, (X i).card = m)
    (hη : 0 < η) (hη₁ : η ≤ 1) (hδ : 0 ≤ δ) (hd : 0 ≤ d)
    (hTol : 2*(ε+δ) ≤ η) (hLoss : ((p+c:ℕ):ℝ) ≤ δ*((m:ℝ)*η))
    (hPDeg : ∀ v, inDegree P v ≤ p ∧ outDegree P v ≤ p)
    (hCDeg : ∀ v, inDegree C v ≤ c ∧ outDegree C v ≤ c)
    (hPZ : ∀ z ∈ Z, inDegree P z ≤ pZ ∧ outDegree P z ≤ pZ)
    (hCZ : ∀ z ∈ Z, inDegree C z ≤ cZ ∧ outDegree C z ≤ cZ)
    (hReg : ∀ i j, R.Adj i j →
      IsUniform G ε (X i) (X j) ∧ d+(ε+δ) ≤ density G (X i) (X j))
    (hPairs : ∀ i, IsLowerSuperregularPair G ε d (X i) (X (s i)))
    (hEnds : ∀ j z, z ∈ Z → budget+pZ+cZ < inNeighbours G (eligible j) z ∧
      budget+pZ+cZ < outTo G (eligible j) z) :
    let D := (G \ P) \ C
    (∀ i j, R.Adj i j → IsUniform D η (X i) (X j) ∧ d ≤ density D (X i) (X j)) ∧
    (∀ i, IsLowerSuperregularPair D η d (X i) (X (s i))) ∧
    ∀ j z, z ∈ Z → budget < inNeighbours D (eligible j) z ∧ budget < outTo D (eligible j) z := by
  intro D
  let L := P ⊔ C
  have hL : L ≤ G := sup_le hP (fun _ _ h => (hC h).1)
  have he : D = G \ L := by
    ext x y
    simp only [D,L,Digraph.sdiff_adj,Digraph.sup_adj]
    tauto
  have hDis (v w : V) : ¬ (P.Adj v w ∧ C.Adj v w) :=
    fun h => (hC h.2).2 h.1
  have hDegrees (v : V) : inDegree L v ≤ p+c ∧ outDegree L v ≤ p+c := by
    obtain ⟨ho,hi⟩ := degrees_sup_of_disjoint P C hDis v
    change inDegree (P ⊔ C) v ≤ p+c ∧ outDegree (P ⊔ C) v ≤ p+c
    rw [hi,ho]
    exact ⟨Nat.add_le_add (hPDeg v).1 (hCDeg v).1,Nat.add_le_add (hPDeg v).2 (hCDeg v).2⟩
  have hDegreesZ (v : V) (hv : v ∈ Z) :
      inDegree L v ≤ pZ+cZ ∧ outDegree L v ≤ pZ+cZ := by
    obtain ⟨ho,hi⟩ := degrees_sup_of_disjoint P C hDis v
    change inDegree (P ⊔ C) v ≤ pZ+cZ ∧ outDegree (P ⊔ C) v ≤ pZ+cZ
    rw [hi,ho]
    exact ⟨Nat.add_le_add (hPZ v hv).1 (hCZ v hv).1,
      Nat.add_le_add (hPZ v hv).2 (hCZ v hv).2⟩
  obtain ⟨hUniform,hSuper⟩ := wound_host_pairs_after_deletion G L X R s m (p+c) ε η δ d
    hL hm hSize hη hη₁ hδ hd hTol hLoss hDegrees hReg hPairs
  rw [he]
  refine ⟨hUniform,hSuper,?_⟩
  intro j z hz
  obtain ⟨hi,ho⟩ := endpoint_neighbourhoods_after_reserve_deletion G L hL (eligible j) z
  obtain ⟨hzi,hzo⟩ := hDegreesZ z hz
  obtain ⟨hendi,hendo⟩ := hEnds j z hz
  exact ⟨by omega,by omega⟩

end OverfullWork.DirectedRobustExpansion
