module

public import OverfullWork.KuhnOsthusOrderedPathCover
public import OverfullWork.KuhnOsthusWindingIntervalGeometry

@[expose] public section


/-! The forward sweep and the return form complementary intervals
in a single traversal of the cluster cycle. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V : Type*}

/-- Read the cluster at a natural-number position of a cyclic array. -/
def cyclicCluster {k : ℕ} (X : Fin k → Finset V) (hk : 0 < k) (i : ℕ) : Finset V :=
  X ⟨i % k,Nat.mod_lt _ hk⟩

theorem cyclicCluster_successor {k : ℕ} (X : Fin k → Finset V) (hk : 0 < k) (i : ℕ) :
    cyclicCluster X hk (i+1) = X (finRotate k ⟨i % k,Nat.mod_lt _ hk⟩) := by
  apply congrArg X
  apply Fin.ext
  change (i+1) % k = (finRotate k ⟨i % k,Nat.mod_lt _ hk⟩).val
  rw [finRotate_val_modulo]
  exact (Nat.mod_add_mod i k 1).symm

def rotateClusterArray {k : ℕ} (X : Fin k → Finset V) (hk : 0 < k)
    (offset : ℕ) (i : Fin k) : Finset V :=
  cyclicCluster X hk (offset+i.val)

theorem cyclicCluster_rotateClusterArray {k : ℕ} (X : Fin k → Finset V) (hk : 0 < k)
    (offset i : ℕ) :
    cyclicCluster (rotateClusterArray X hk offset) hk i = cyclicCluster X hk (offset+i) := by
  apply congrArg X
  apply Fin.ext
  exact Nat.add_mod_mod offset i k

theorem cyclicCluster_distinct {k : ℕ} {X : Fin k → Finset V} (hk : 0 < k)
    (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    {i j : ℕ} (h : i % k ≠ j % k) : Disjoint (cyclicCluster X hk i) (cyclicCluster X hk j) :=
  hDis _ _ (fun e => h (congrArg Fin.val e))

variable [Fintype V]

/-- Two complementary intervals on the cyclic cluster array cover
every vertex and share exactly their two endpoints. -/
theorem cyclicCluster_complementary_intervals {k c s : ℕ} (X : Fin k → Finset V)
    (hs : s < c) (hc : c < k)
    (hCover : ∀ x : V, ∃ i, x ∈ X i)
    (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j)) :
    let A := cyclicCluster X (by omega)
    let B := fun i => A (c+i)
    let n := k+s-c
    B 0 = A c ∧ B n = A s ∧
    clusterIntervalVertices A s c ∪ clusterIntervalVertices B 0 n = univ ∧
    clusterIntervalVertices A s c ∩ clusterIntervalVertices B 0 n = B n ∪ B 0 ∧
    (∀ i j, s ≤ i → i ≤ c → s ≤ j → j ≤ c → i ≠ j → Disjoint (A i) (A j)) ∧
    (∀ i j, i ≤ n → j ≤ n → i ≠ j → Disjoint (B i) (B j)) := by
  intro A B n
  have hEnd : c+n = k+s := by dsimp [n]; omega
  have hFirst : B 0 = A c := by simp only [B,Nat.add_zero]
  have hLast : B n = A s := by
    change A (c+n) = A s
    rw [hEnd]
    apply congrArg X
    apply Fin.ext
    exact Nat.add_mod_left k s
  have hApart {i j : ℕ} (h : i % k ≠ j % k) : Disjoint (A i) (A j) :=
    hDis _ _ (fun e => h (congrArg Fin.val e))
  have hMod {i : ℕ} (hi : k ≤ i) (hi' : i ≤ k+s) : i % k = i-k := by
    have he : i = k+(i-k) := by omega
    conv_lhs => rw [he,Nat.add_mod_left,Nat.mod_eq_of_lt (by omega)]
  have hSame {i j : ℕ} (hi : s ≤ i) (hic : i ≤ c) (hj : c ≤ j) (hjk : j ≤ k+s)
      (h : i % k = j % k) : i = c ∧ j = c ∨ i = s ∧ j = k+s := by
    rw [Nat.mod_eq_of_lt (by omega)] at h
    by_cases hlt : j < k
    · rw [Nat.mod_eq_of_lt hlt] at h
      exact .inl ⟨by omega,by omega⟩
    · rw [hMod (by omega) hjk] at h
      exact .inr ⟨by omega,by omega⟩
  refine ⟨hFirst,hLast,?_,?_,?_,?_⟩
  · apply eq_univ_of_forall
    intro v
    obtain ⟨t,ht⟩ := hCover v
    have hAt : ∀ j, j % k = t.val → v ∈ A j := by
      intro j he
      change v ∈ X ⟨j % k,Nat.mod_lt _ (by omega)⟩
      rw [show (⟨j % k,Nat.mod_lt _ (by omega)⟩ : Fin k) = t from Fin.ext he]
      exact ht
    by_cases hlow : t.val < s
    · apply mem_union_right
      exact (mem_clusterIntervalVertices B 0 n v).mpr
        ⟨k+t.val-c,Nat.zero_le _,by omega,by
          change v ∈ A (c+(k+t.val-c))
          rw [show c+(k+t.val-c) = k+t.val by omega]
          exact hAt _ (by rw [Nat.add_mod_left,Nat.mod_eq_of_lt t.isLt])⟩
    · by_cases hle : t.val ≤ c
      · apply mem_union_left
        exact (mem_clusterIntervalVertices A s c v).mpr
          ⟨t.val,by omega,hle,hAt _ (Nat.mod_eq_of_lt t.isLt)⟩
      · apply mem_union_right
        exact (mem_clusterIntervalVertices B 0 n v).mpr
          ⟨t.val-c,Nat.zero_le _,by omega,by
            change v ∈ A (c+(t.val-c))
            rw [show c+(t.val-c) = t.val by omega]
            exact hAt _ (Nat.mod_eq_of_lt t.isLt)⟩
  · ext v
    simp only [mem_inter,mem_union,mem_clusterIntervalVertices]
    constructor
    · rintro ⟨⟨i,hi,hic,hvi⟩,⟨j,_,hj,hvj⟩⟩
      have he : i % k = (c+j) % k := by
        by_contra h
        exact disjoint_left.mp (hApart h) hvi hvj
      rcases hSame hi hic (by omega) (by omega) he with ⟨rfl,_⟩ | ⟨rfl,_⟩
      · exact .inr (hFirst ▸ hvi)
      · exact .inl (hLast ▸ hvi)
    · rintro (hv | hv)
      · exact ⟨⟨s,le_rfl,by omega,hLast ▸ hv⟩,⟨n,Nat.zero_le _,le_rfl,hv⟩⟩
      · exact ⟨⟨c,by omega,le_rfl,hFirst ▸ hv⟩,⟨0,le_rfl,Nat.zero_le _,hv⟩⟩
  · intro i j _ hi _ hj hij
    exact hApart (by rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega : j < k)]; exact hij)
  · intro i j hi hj hij
    apply hApart
    intro he
    by_cases hlt : c+i < k <;> by_cases hlt' : c+j < k
    · rw [Nat.mod_eq_of_lt hlt,Nat.mod_eq_of_lt hlt'] at he
      exact hij (by omega)
    · rw [Nat.mod_eq_of_lt hlt,hMod (by omega) (by omega)] at he
      omega
    · rw [hMod (by omega) (by omega),Nat.mod_eq_of_lt hlt'] at he
      omega
    · rw [hMod (by omega) (by omega),hMod (by omega : k ≤ c+j) (by omega)] at he
      exact hij (by omega)

/-- After rotating the cluster origin, the forward interval starts at
index 3. The return crosses the origin and stops at the same cluster.
The intervals together cover every vertex and share exactly their
two endpoints. -/
theorem cyclicCluster_reserve_intervals {k c : ℕ} (X : Fin k → Finset V)
    (h₃ : 3 < c) (hc : c < k)
    (hCover : ∀ x : V, ∃ i, x ∈ X i)
    (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j)) :
    let A := cyclicCluster X (by omega)
    let B := fun i => A (c+i)
    let n := k+3-c
    B 0 = A c ∧ B n = A 3 ∧
    clusterIntervalVertices A 3 c ∪ clusterIntervalVertices B 0 n = univ ∧
    clusterIntervalVertices A 3 c ∩ clusterIntervalVertices B 0 n = B n ∪ B 0 ∧
    (∀ i j, 3 ≤ i → i ≤ c → 3 ≤ j → j ≤ c → i ≠ j → Disjoint (A i) (A j)) ∧
    (∀ i j, i ≤ n → j ≤ n → i ≠ j → Disjoint (B i) (B j)) :=
  cyclicCluster_complementary_intervals X h₃ hc hCover hDis

end OverfullWork.DirectedRobustExpansion
