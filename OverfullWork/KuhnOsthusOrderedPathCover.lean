module

public import OverfullWork.KuhnOsthusCycleAbsorberOpenReserve
public import OverfullWork.KuhnOsthusIntervalPathTransport

@[expose] public section


/-! Interpret the coordinate paths of Claim 1 and of its open
reserve as the same physical interval path covers used for the
exceptional systems. Their physical arcs are unchanged. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedAbsorbingLadder DirectedSpanningConfiguration
open scoped Classical
variable {V J : Type*}

noncomputable def clusterIntervalVertices (A : ℕ → Finset V) (l r : ℕ) : Finset V :=
  ((range (r+1)).filter (fun i => l ≤ i)).biUnion A

theorem mem_clusterIntervalVertices (A : ℕ → Finset V) (l r : ℕ) (v : V) :
    v ∈ clusterIntervalVertices A l r ↔ ∃ i, l ≤ i ∧ i ≤ r ∧ v ∈ A i := by
  simp only [clusterIntervalVertices,mem_biUnion,mem_filter,mem_range]
  constructor
  · rintro ⟨i,⟨hi,hl⟩,h⟩
    exact ⟨i,hl,by omega,h⟩
  · rintro ⟨i,hl,hi,h⟩
    exact ⟨i,⟨by omega,hl⟩,h⟩

/-- Turn the ordered paths into an interval path cover whose path
digraph is exactly the original union of bundle arcs. -/
theorem OrderedClusterPaths.exists_interval_path_cover {G : Digraph V} {A : ℕ → Finset V}
    {l r : ℕ} (P : OrderedClusterPaths G A J l r) (hlr : l ≤ r)
    (hDis : ∀ i k, l ≤ i → i ≤ r → l ≤ k → k ≤ r → i ≠ k → Disjoint (A i) (A k)) :
    ∃ Q : IntervalPathCover G (clusterIntervalVertices A l r) (A l) (A r),
      Q.digraph = P.unionPaths ∧
      ∀ j, (Q.starts (P.orderAt r hlr le_rfl j)).val = P.vertex l j := by
  let L (j : J) := List.ofFn (fun i : Fin (r-l+1) => P.vertex (l+i.val) j)
  have hLen (j : J) : (L j).length = r-l+1 := List.length_ofFn
  have hGet (j : J) (i : ℕ) (hi : i < (L j).length) : (L j)[i] = P.vertex (l+i) j := by
    simp only [L,List.getElem_ofFn]
  have hMem (j : J) (v : V) : v ∈ L j ↔ ∃ i, l ≤ i ∧ i ≤ r ∧ P.vertex i j = v := by
    constructor
    · intro hv
      obtain ⟨i,hi⟩ := List.mem_ofFn.mp hv
      exact ⟨l+i.val,by omega,by have := i.isLt; omega,hi⟩
    · rintro ⟨i,hi,hir,he⟩
      exact List.mem_ofFn.mpr ⟨⟨i-l,by omega⟩,by simpa [Nat.add_sub_of_le hi] using he⟩
  have hND (j : J) : (L j).Nodup := by
    apply List.nodup_ofFn.mpr
    intro i k h
    obtain ⟨hi,_⟩ := P.unique_coordinates hDis (by omega : l ≤ l+i.val) (by have := i.isLt; omega)
      (by omega : l ≤ l+k.val) (by have := k.isLt; omega) h
    exact Fin.ext (by omega)
  have hChain (j : J) : (L j).IsChain G.Adj := by
    apply List.isChain_iff_getElem.mpr
    intro i hi
    have hLen' := hLen j
    rw [hGet,hGet]
    exact P.edge (l+i) (by omega) (by omega) j
  have hHead (j : J) : (L j).head? = some (P.vertex l j) := by
    rw [List.head?_eq_getElem?,List.getElem?_eq_getElem (by have := hLen j; omega),hGet,Nat.add_zero]
  have hLast (j : J) : (L j).getLast? = some (P.vertex r j) := by
    have hLen' := hLen j
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega), hGet]
    rw [show l+((L j).length-1) = r by omega]
  have hRequests (j : J) : ∃ p : PathRequest G,
      p.source = P.vertex l j ∧ p.target = P.vertex r j ∧ p.vertices = L j := by
    obtain ⟨T,hT⟩ := List.head?_eq_some_iff.mp (hHead j)
    refine ⟨⟨P.vertex l j,P.vertex r j,T,⟨?_,?_⟩,?_⟩,rfl,rfl,?_⟩
    · exact hT ▸ hChain j
    · exact hT ▸ hLast j
    · exact hT ▸ hND j
    · exact hT.symm
  choose path hSource hTarget hWord using hRequests
  let e₀ := P.orderAt l le_rfl hlr
  let e₁ := P.orderAt r hlr le_rfl
  let Q : IntervalPathCover G (clusterIntervalVertices A l r) (A l) (A r) := {
    path := fun v => path (e₁.symm v)
    starts := e₁.symm.trans e₀
    ends := by
      intro v
      refine ⟨hSource _,(hTarget _).trans ?_⟩
      change (e₁ (e₁.symm v)).val = v.val
      rw [e₁.apply_symm_apply]
    disjoint := by
      intro v w hvw x hx hy
      change x ∈ (path (e₁.symm v)).vertices at hx
      change x ∈ (path (e₁.symm w)).vertices at hy
      obtain ⟨i,hi,hir,he⟩ := (hMem _ _).mp (hWord _ ▸ hx)
      obtain ⟨k,hk,hkr,he'⟩ := (hMem _ _).mp (hWord _ ▸ hy)
      have h := (P.unique_coordinates hDis hi hir hk hkr (he.trans he'.symm)).2
      exact hvw (e₁.symm.injective h)
    spans := by
      intro x
      rw [mem_clusterIntervalVertices]
      constructor
      · rintro ⟨i,hi,hir,hx⟩
        obtain ⟨j,hj⟩ := P.covers i hi hir x hx
        refine ⟨e₁ j,?_⟩
        rw [e₁.symm_apply_apply,hWord]
        exact (hMem _ _).mpr ⟨i,hi,hir,hj⟩
      · rintro ⟨v,hv⟩
        change x ∈ (path (e₁.symm v)).vertices at hv
        obtain ⟨i,hi,hir,h⟩ := (hMem _ _).mp (hWord _ ▸ hv)
        exact ⟨i,hi,hir,h ▸ P.part i hi hir (e₁.symm v)⟩ }
  have hArc (j : J) (x y : V) : (wordGraph (L j)).Adj x y ↔ (P.pathDigraph j).Adj x y := by
    have hj := hLen j
    have hSome (a : ℕ) (ha : a < (L j).length) :
        (L j)[a]? = some (P.vertex (l+a) j) := by rw [List.getElem?_eq_getElem ha,hGet]
    constructor
    · intro h
      obtain ⟨i,hi,hAt⟩ := List.infix_iff_getElem?.mp h
      have hSize : i+2 ≤ (L j).length := by
        change 2+i ≤ (L j).length at hi
        omega
      have hx : (L j)[i]? = some x := by simpa using hAt 0 (by simp)
      have hy : (L j)[i+1]? = some y := by simpa [Nat.add_comm] using hAt 1 (by simp)
      refine ⟨l+i,by omega,by omega,?_ ,?_⟩
      · exact Option.some.inj (hx.symm.trans (hSome i (by omega)))
      · exact Option.some.inj (hy.symm.trans (hSome (i+1) (by omega)))
    · rintro ⟨i,hi,hir,rfl,rfl⟩
      apply List.infix_iff_getElem?.mpr
      refine ⟨i-l,by simp; omega,?_⟩
      intro b hb
      have hSize : b < 2 := hb
      have hIndex : b+(i-l) < (L j).length := by omega
      rw [hSome _ hIndex]
      have hEq : b = 0 ∨ b = 1 := by omega
      rcases hEq with rfl | rfl
      · simp [Nat.add_sub_of_le hi]
      · simp [show l+(1+(i-l))=i+1 by omega]
  refine ⟨Q,?_,?_⟩
  · ext x y
    change (⨆ t : A r, wordGraph (path (e₁.symm t)).vertices).Adj x y ↔ _
    rw [Digraph.iSup_adj]
    change (∃ t : A r, (wordGraph (path (e₁.symm t)).vertices).Adj x y) ↔
      (⨆ j, P.pathDigraph j).Adj x y
    rw [Digraph.iSup_adj]
    constructor
    · rintro ⟨t,ht⟩
      rw [hWord] at ht
      exact ⟨e₁.symm t,(hArc _ _ _).mp ht⟩
    · rintro ⟨j,hj⟩
      refine ⟨e₁ j,?_⟩
      rw [e₁.symm_apply_apply,hWord]
      exact (hArc _ _ _).mpr hj
  · intro j
    change (e₀ (e₁.symm (e₁ j))).val = P.vertex l j
    rw [e₁.symm_apply_apply,OrderedClusterPaths.orderAt_val]

end OverfullWork.DirectedRobustExpansion
