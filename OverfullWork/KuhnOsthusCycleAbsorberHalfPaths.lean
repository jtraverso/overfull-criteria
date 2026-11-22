module

public import OverfullWork.KuhnOsthusIntervalWindingFactor

@[expose] public section


/-! Finish a half of F by inserting the complete exceptional path
system after the primary switch paths and then filling the last
ordinary interval, as in Kühn–Osthus Lemma 10.3. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

omit [Fintype V] in
theorem clusterIntervalVertices_union (A : ℕ → Finset V) {l k r : ℕ} (hk : l ≤ k) (hr : k ≤ r) :
    clusterIntervalVertices A l k ∪ clusterIntervalVertices A k r = clusterIntervalVertices A l r := by
  ext v
  simp only [mem_union,mem_clusterIntervalVertices]
  constructor
  · rintro (⟨i,hi,hi',h⟩ | ⟨i,hi,hi',h⟩)
    · exact ⟨i,hi,hi'.trans hr,h⟩
    · exact ⟨i,hk.trans hi,hi',h⟩
  · rintro ⟨i,hi,hi',h⟩
    by_cases he : i ≤ k
    · exact .inl ⟨i,hi,he,h⟩
    · exact .inr ⟨i,by omega,hi',h⟩

omit [Fintype V] in
theorem clusterIntervalVertices_inter (A : ℕ → Finset V) {l k r : ℕ} (hk : l ≤ k) (hr : k ≤ r)
    (hDis : ∀ i j, l ≤ i → i ≤ r → l ≤ j → j ≤ r → i ≠ j → Disjoint (A i) (A j)) :
    clusterIntervalVertices A l k ∩ clusterIntervalVertices A k r = A k := by
  ext v
  simp only [mem_inter,mem_clusterIntervalVertices]
  constructor
  · rintro ⟨⟨i,hi,hik,hv⟩,⟨j,hkj,hj,hv'⟩⟩
    have he : i = j := by
      by_contra hn
      exact disjoint_left.mp (hDis i j hi (hik.trans hr) (hk.trans hkj) hj hn) hv hv'
    have h : i = k := by omega
    exact h ▸ hv
  · intro hv
    exact ⟨⟨k,hk,le_rfl,hv⟩,⟨k,le_rfl,hr,hv⟩⟩

def IntervalPathCover.castSupport {G : Digraph V} {A B S T : Finset V}
    (X : IntervalPathCover G A S T) (h : A = B) : IntervalPathCover G B S T :=
  h ▸ X

omit [Fintype V] in
theorem IntervalPathCover.castSupport_digraph {G : Digraph V} {A B S T : Finset V}
    (X : IntervalPathCover G A S T) (h : A = B) : (X.castSupport h).digraph = X.digraph := by
  subst B
  rfl

omit [Fintype V] in
/-- Reassemble the half cover from its already chosen ordinary
tail and the prescribed exceptional system, preserving every arc. -/
theorem CycleAbsorberClaimOne.exists_half_path_cover_of_tail {G H : Digraph V}
    {A : ℕ → Finset V} {m n b c : ℕ}
    (C : CycleAbsorberClaimOne G A m n) (hn : n ≤ b) (hc : b ≤ c)
    (E : IntervalPathCover H (clusterIntervalVertices A n b) (A n) (A b))
    (D : OrderedClusterPaths G A (Fin (2*m)) b c)
    (hDis : ∀ i j, i ≤ c → j ≤ c → i ≠ j → Disjoint (A i) (A j)) :
    ∃ F : IntervalPathCover (G ⊔ H) (clusterIntervalVertices A 0 c) (A 0) (A c),
      F.digraph = (C.paths.unionPaths ⊔ E.digraph) ⊔ D.unionPaths := by
  obtain ⟨P,hP,_⟩ := C.paths.exists_interval_path_cover (Nat.zero_le n)
    (fun i j _ hi _ hj h => hDis i j (by omega) (by omega) h)
  obtain ⟨Q,hQ,_⟩ := D.exists_interval_path_cover (by omega : b ≤ c)
    (fun i j _ hi _ hj h => hDis i j hi hj h)
  let P' := P.rehost (le_sup_left : G ≤ G ⊔ H)
  let Q' := Q.rehost (le_sup_left : G ≤ G ⊔ H)
  let E' := E.rehost (le_sup_right : H ≤ G ⊔ H)
  obtain ⟨X,hX,_⟩ := P'.exists_concat E' 
    (clusterIntervalVertices_inter A (Nat.zero_le n) hn
      (fun i j _ hi _ hj h => hDis i j (by omega) (by omega) h))
  let X' := X.castSupport (clusterIntervalVertices_union A (Nat.zero_le n) hn)
  have hX' : X'.digraph = P.digraph ⊔ E.digraph :=
    (X.castSupport_digraph _).trans hX
  obtain ⟨Y,hY,_⟩ := X'.exists_concat Q'
    (clusterIntervalVertices_inter A (Nat.zero_le b) (by omega : b ≤ c)
      (fun i j _ hi _ hj h => hDis i j hi hj h))
  let F := Y.castSupport (clusterIntervalVertices_union A (Nat.zero_le b) (by omega : b ≤ c))
  have hF : F.digraph = X'.digraph ⊔ Q.digraph :=
    (Y.castSupport_digraph _).trans hY
  change X.digraph = P.digraph ⊔ E.digraph at hX
  change Y.digraph = X'.digraph ⊔ Q.digraph at hY
  exact ⟨F,by rw [hF,hX',hP,hQ]⟩
/-- Claim 1 can be extended through the prescribed complete
exceptional system and a final ordinary interval to the opposite
boundary cluster. Both the switch paths and the exceptional system
remain present in the exact union. -/
theorem CycleAbsorberClaimOne.exists_half_path_cover_in {G H : Digraph V} {A : ℕ → Finset V}
    {m n b c : ℕ} (C : CycleAbsorberClaimOne G A m n) (hn : n ≤ b) (hc : b+3 ≤ c)
    (E : IntervalPathCover H (clusterIntervalVertices A n b) (A n) (A b))
    (e : Fin (2*m) ≃ A b) (f : Fin (2*m) ≃ A c)
    (hDis : ∀ i j, i ≤ c → j ≤ c → i ≠ j → Disjoint (A i) (A j))
    (hSize : ∀ i, b ≤ i → i ≤ c → (A i).card = 2*m)
    (ε d : ℝ) (hε : 0 ≤ ε) (hGap : 2*ε < d) (hd : d ≤ 1)
    (hPairs : ∀ i, b ≤ i → i < c → IsLowerSuperregularPair G ε d (A i) (A (i+1)))
    (r : ℕ) (hr : 0 < r) (hCut : ((2*m:ℕ):ℝ)*ε ≤ (r:ℝ))
    (hBudget : 28*((r:ℝ)+1) < (d-2*ε)^14*((d-ε)*((2*m:ℕ):ℝ))) :
    ∃ (D : OrderedClusterPaths G A (Fin (2*m)) b c)
      (F : IntervalPathCover (G ⊔ H) (clusterIntervalVertices A 0 c) (A 0) (A c)),
      F.digraph = (C.paths.unionPaths ⊔ E.digraph) ⊔ D.unionPaths ∧
      (∀ j, D.vertex b j = (e j).val) ∧ ∀ j, D.vertex c j = (f j).val := by
  obtain ⟨D,hStart,hEnd⟩ := exists_ordered_cluster_paths G A b c (2*m) r hc e f ε d hε hGap hd
    hr hCut hBudget hSize (fun i j _ hi _ hj he => hDis i j hi hj he) hPairs
  obtain ⟨F,hF⟩ := C.exists_half_path_cover_of_tail hn (by omega) E D hDis
  exact ⟨D,F,hF,hStart,hEnd⟩

/-- Claim 1 can be extended through the prescribed complete
exceptional system and a final ordinary interval to the opposite
boundary cluster. Both the switch paths and the exceptional system
remain present in the exact union. -/
theorem CycleAbsorberClaimOne.exists_half_path_cover {G : Digraph V} {A : ℕ → Finset V}
    {m n b c : ℕ} (C : CycleAbsorberClaimOne G A m n) (hn : n ≤ b) (hc : b+3 ≤ c)
    (E : IntervalPathCover G (clusterIntervalVertices A n b) (A n) (A b))
    (e : Fin (2*m) ≃ A b) (f : Fin (2*m) ≃ A c)
    (hDis : ∀ i j, i ≤ c → j ≤ c → i ≠ j → Disjoint (A i) (A j))
    (hSize : ∀ i, b ≤ i → i ≤ c → (A i).card = 2*m)
    (ε d : ℝ) (hε : 0 ≤ ε) (hGap : 2*ε < d) (hd : d ≤ 1)
    (hPairs : ∀ i, b ≤ i → i < c → IsLowerSuperregularPair G ε d (A i) (A (i+1)))
    (r : ℕ) (hr : 0 < r) (hCut : ((2*m:ℕ):ℝ)*ε ≤ (r:ℝ))
    (hBudget : 28*((r:ℝ)+1) < (d-2*ε)^14*((d-ε)*((2*m:ℕ):ℝ))) :
    ∃ (D : OrderedClusterPaths G A (Fin (2*m)) b c)
      (F : IntervalPathCover G (clusterIntervalVertices A 0 c) (A 0) (A c)),
      F.digraph = (C.paths.unionPaths ⊔ E.digraph) ⊔ D.unionPaths ∧
      (∀ j, D.vertex b j = (e j).val) ∧ ∀ j, D.vertex c j = (f j).val := by
  obtain ⟨D,F,hF,hStart,hEnd⟩ := C.exists_half_path_cover_in hn hc E e f
    hDis hSize ε d hε hGap hd hPairs r hr hCut hBudget
  let F' := F.rehost (sup_le (le_refl G) (le_refl G))
  exact ⟨D,F',hF,hStart,hEnd⟩

end OverfullWork.DirectedRobustExpansion
