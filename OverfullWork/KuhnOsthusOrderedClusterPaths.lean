module

public import OverfullWork.KuhnOsthusPrescribedLongRoutes

@[expose] public section


/-! A bundle of paths through an interval, with a common label for
the consecutive vertices of each path. This lets the interval
construction keep its endpoint orderings when the bundles are joined. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function
open scoped Classical
variable {V J : Type*}

structure OrderedClusterPaths (G : Digraph V) (A : ℕ → Finset V) (J : Type*) (l r : ℕ) where
  vertex : ℕ → J → V
  part : ∀ i, l ≤ i → i ≤ r → ∀ j, vertex i j ∈ A i
  injective : ∀ i, l ≤ i → i ≤ r → Injective (vertex i)
  covers : ∀ i, l ≤ i → i ≤ r → ∀ v ∈ A i, ∃ j, vertex i j = v
  edge : ∀ i, l ≤ i → i < r → ∀ j, G.Adj (vertex i j) (vertex (i+1) j)

def OrderedClusterPaths.pathDigraph {G : Digraph V} {A : ℕ → Finset V} {l r : ℕ}
    (P : OrderedClusterPaths G A J l r) (j : J) : Digraph V :=
  ⟨fun x y => ∃ i, l ≤ i ∧ i < r ∧ x = P.vertex i j ∧ y = P.vertex (i+1) j⟩

theorem OrderedClusterPaths.pathDigraph_le {G : Digraph V} {A : ℕ → Finset V} {l r : ℕ}
    (P : OrderedClusterPaths G A J l r) (j : J) : P.pathDigraph j ≤ G := by
  rintro x y ⟨i,hi,hj,rfl,rfl⟩
  exact P.edge i hi hj j

theorem OrderedClusterPaths.unique_coordinates {G : Digraph V} {A : ℕ → Finset V} {l r : ℕ}
    (P : OrderedClusterPaths G A J l r)
    (hDis : ∀ i k, l ≤ i → i ≤ r → l ≤ k → k ≤ r → i ≠ k → Disjoint (A i) (A k))
    {i k : ℕ} (hi : l ≤ i) (hi' : i ≤ r) (hk : l ≤ k) (hk' : k ≤ r) {j j' : J}
    (h : P.vertex i j = P.vertex k j') : i = k ∧ j = j' := by
  have hik : i = k := by
    by_contra hn
    exact disjoint_left.mp (hDis i k hi hi' hk hk' hn) (P.part i hi hi' j)
      (h.symm ▸ P.part k hk hk' j')
  subst k
  exact ⟨rfl,P.injective i hi hi' h⟩

/-- A prescribed matching between consecutive clusters, indexed
by the common path labels. -/
def OrderedClusterPaths.of_pair (G : Digraph V) (A : ℕ → Finset V) (l : ℕ)
    (e : J ≃ A l) (f : J ≃ A (l+1)) (h : ∀ j, G.Adj (e j) (f j)) :
    OrderedClusterPaths G A J l (l+1) := by
  let vertex (i : ℕ) (j : J) : V := if i = l then (e j).val else (f j).val
  refine ⟨vertex,?_,?_,?_,?_⟩
  · intro i hi hir j
    by_cases h' : i = l
    · subst i
      rw [show vertex l j = (e j).val from if_pos rfl]
      exact (e j).prop
    · have he : i = l+1 := by omega
      subst i
      rw [show vertex (l+1) j = (f j).val from if_neg (by omega)]
      exact (f j).prop
  · intro i _ _
    by_cases h' : i = l
    · exact fun a b he => e.injective (Subtype.ext (by simpa [vertex,h'] using he))
    · exact fun a b he => f.injective (Subtype.ext (by simpa [vertex,h'] using he))
  · intro i hi hir v hv
    by_cases h' : i = l
    · subst i
      obtain ⟨j,hj⟩ := e.surjective ⟨v,hv⟩
      exact ⟨j,by simp [vertex,hj]⟩
    · have he : i = l+1 := by omega
      subst i
      obtain ⟨j,hj⟩ := f.surjective ⟨v,hv⟩
      exact ⟨j,by simp [vertex,hj]⟩
  · intro i hi hir j
    have he : i = l := by omega
    subst i
    simpa [vertex] using h j

@[simp] theorem OrderedClusterPaths.of_pair_left (G : Digraph V) (A : ℕ → Finset V) (l : ℕ)
    (e : J ≃ A l) (f : J ≃ A (l+1)) (h : ∀ j, G.Adj (e j) (f j)) (j : J) :
    (OrderedClusterPaths.of_pair G A l e f h).vertex l j = (e j).val := by
  simp [OrderedClusterPaths.of_pair]

@[simp] theorem OrderedClusterPaths.of_pair_right (G : Digraph V) (A : ℕ → Finset V) (l : ℕ)
    (e : J ≃ A l) (f : J ≃ A (l+1)) (h : ∀ j, G.Adj (e j) (f j)) (j : J) :
    (OrderedClusterPaths.of_pair G A l e f h).vertex (l+1) j = (f j).val := by
  simp [OrderedClusterPaths.of_pair]

/-- Concatenate two bundles when they give the same order to their
common endpoint cluster. -/
def OrderedClusterPaths.concat {G : Digraph V} {A : ℕ → Finset V} {l b r : ℕ}
    (P : OrderedClusterPaths G A J l b) (Q : OrderedClusterPaths G A J b r)
    (h : ∀ j, P.vertex b j = Q.vertex b j) : OrderedClusterPaths G A J l r := by
  let vertex (i : ℕ) (j : J) : V := if i ≤ b then P.vertex i j else Q.vertex i j
  refine ⟨vertex,?_,?_,?_,?_⟩
  · intro i hi hr j
    by_cases hb : i ≤ b
    · simpa [vertex,hb] using P.part i hi hb j
    · simpa [vertex,hb] using Q.part i (by omega : b ≤ i) hr j
  · intro i hi hr
    by_cases hb : i ≤ b
    · simpa [vertex,hb] using P.injective i hi hb
    · simpa [vertex,hb] using Q.injective i (by omega : b ≤ i) hr
  · intro i hi hr v hv
    by_cases hb : i ≤ b
    · simpa [vertex,hb] using P.covers i hi hb v hv
    · simpa [vertex,hb] using Q.covers i (by omega : b ≤ i) hr v hv
  · intro i hi hr j
    rcases lt_trichotomy i b with hb | rfl | hb
    · simpa [vertex,hb.le,(by omega : i+1 ≤ b)] using P.edge i hi hb j
    · simpa [vertex,h j] using Q.edge i le_rfl hr j
    · simpa only [vertex,if_neg (not_le_of_gt hb),if_neg (by omega : ¬ i+1 ≤ b)] using
        Q.edge i hb.le hr j

theorem OrderedClusterPaths.concat_left {G : Digraph V} {A : ℕ → Finset V} {l b r : ℕ}
    (P : OrderedClusterPaths G A J l b) (Q : OrderedClusterPaths G A J b r)
    (h : ∀ j, P.vertex b j = Q.vertex b j) {i : ℕ} (hi : i ≤ b) (j : J) :
    (P.concat Q h).vertex i j = P.vertex i j := by
  simp [OrderedClusterPaths.concat,hi]

theorem OrderedClusterPaths.concat_right {G : Digraph V} {A : ℕ → Finset V} {l b r : ℕ}
    (P : OrderedClusterPaths G A J l b) (Q : OrderedClusterPaths G A J b r)
    (h : ∀ j, P.vertex b j = Q.vertex b j) {i : ℕ} (hi : b ≤ i) (j : J) :
    (P.concat Q h).vertex i j = Q.vertex i j := by
  rcases hi.eq_or_lt with rfl | hi
  · simpa [OrderedClusterPaths.concat] using h j
  · simp [OrderedClusterPaths.concat,not_le_of_gt hi]

private def castClusterOrder {S T : Finset V} (e : J ≃ S) (h : S = T) : J ≃ T :=
  h ▸ e

private theorem castClusterOrder_val {S T : Finset V} (e : J ≃ S) (h : S = T) (j : J) :
    (castClusterOrder e h j).val = (e j).val := by
  subst T
  rfl

variable [Fintype V]

/-- Corollary 4.15 with both endpoint orders specified and with the
cluster indices in their original interval. -/
theorem exists_ordered_cluster_paths (G : Digraph V) (A : ℕ → Finset V) (l r m k : ℕ)
    (hr : l+3 ≤ r) (e : J ≃ A l) (f : J ≃ A r)
    (ε d : ℝ) (hε : 0 ≤ ε) (hGap : 2*ε < d) (hd : d ≤ 1)
    (hk : 0 < k) (hCut : (m:ℝ)*ε ≤ (k:ℝ))
    (hBudget : 28*((k:ℝ)+1) < (d-2*ε)^14*((d-ε)*(m:ℝ)))
    (hSize : ∀ i, l ≤ i → i ≤ r → (A i).card = m)
    (hDis : ∀ i j, l ≤ i → i ≤ r → l ≤ j → j ≤ r → i ≠ j → Disjoint (A i) (A j))
    (hPairs : ∀ i, l ≤ i → i < r → IsLowerSuperregularPair G ε d (A i) (A (i+1))) :
    ∃ P : OrderedClusterPaths G A J l r,
      (∀ j, P.vertex l j = (e j).val) ∧ ∀ j, P.vertex r j = (f j).val := by
  let q := r-l-3
  have hIndex : l+(q+3) = r := by dsimp [q]; omega
  let B (i : ℕ) := A (l+i)
  have hEnd : B (q+3) = A r := congrArg A hIndex
  let E : J ≃ B 0 := e
  let F : J ≃ B (q+3) := castClusterOrder f hEnd.symm
  obtain ⟨Q,hQ0,hQr,hQ⟩ := kuhn_osthus_corollary_4_15 G m k ε d hε hGap hd hk hCut hBudget q B
    (E.symm.trans F) (fun i hi => hSize _ (by omega) (by omega))
    (fun i j hi hj hne => hDis _ _ (by omega) (by omega) (by omega) (by omega) (by omega))
    (fun i hi => hPairs (l+i) (by omega) (by omega))
  let vertex (i : ℕ) (j : J) : V :=
    if hi : i-l < q+4 then (Q ⟨i-l,hi⟩ (E j)).val else (e j).val
  have hV (i : ℕ) (hi : l ≤ i) (hi' : i ≤ r) (j : J) :
      vertex i j = (Q ⟨i-l,by omega⟩ (E j)).val := by
    simp [vertex,show i-l < q+4 by omega]
  refine ⟨⟨vertex,?_,?_,?_,?_⟩,?_,?_⟩
  · intro i hi hi' j
    rw [hV i hi hi' j]
    have h := (Q ⟨i-l,by omega⟩ (E j)).prop
    change _ ∈ A (l+(i-l)) at h
    rwa [Nat.add_sub_of_le hi] at h
  · intro i hi hi' j j' he
    rw [hV i hi hi' j,hV i hi hi' j'] at he
    exact E.injective ((Q ⟨i-l,by omega⟩).injective (Subtype.ext he))
  · intro i hi hi' v hv
    have hv' : v ∈ B (i-l) := by simpa [B,Nat.add_sub_of_le hi] using hv
    obtain ⟨x,hx⟩ := (Q ⟨i-l,by omega⟩).surjective ⟨v,hv'⟩
    obtain ⟨j,rfl⟩ := E.surjective x
    exact ⟨j,(hV i hi hi' j).trans (congrArg Subtype.val hx)⟩
  · intro i hi hi' j
    rw [hV i hi hi'.le j,hV (i+1) (by omega) (by omega) j]
    let z : Fin (q+3) := ⟨i-l,by omega⟩
    have hZ₀ : z.castSucc = (⟨i-l,by omega⟩ : Fin (q+4)) := rfl
    have hZ₁ : z.succ = (⟨i+1-l,by omega⟩ : Fin (q+4)) := Fin.ext (by simp only [z,Fin.val_succ]; omega)
    have h := hQ z (E j)
    rwa [hZ₀,hZ₁] at h
  · intro j
    change vertex l j = (e j).val
    rw [hV l le_rfl (by omega) j]
    have he : (⟨l-l,by omega⟩ : Fin (q+4)) = 0 := Fin.ext (by simp)
    rw [he,hQ0]
    rfl
  · intro j
    change vertex r j = (f j).val
    rw [hV r (by omega) le_rfl j]
    have he : (⟨r-l,by omega⟩ : Fin (q+4)) = Fin.last (q+3) := Fin.ext (by simp; omega)
    rw [he,hQr,Equiv.trans_apply,E.symm_apply_apply]
    exact castClusterOrder_val f hEnd.symm j

end OverfullWork.DirectedRobustExpansion
