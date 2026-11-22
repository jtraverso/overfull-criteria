module

public import OverfullWork.FiniteUniformChunks

@[expose] public section


/-! Build a genuine cluster map from disjoint cells, then split every
cell of a covering family into uniform chunks with bounded remainder. -/
namespace OverfullWork.DirectedClusterQuotient
open Finset
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]
set_option maxHeartbeats 18000000

noncomputable def mapCells (C : I → Finset V) : V → Option I :=
  fun v => if h : ∃ i,v ∈ C i then some h.choose else none

theorem cluster_mapCells (C : I → Finset V)
    (hDis : ∀ i j,i ≠ j → Disjoint (C i) (C j)) (i : I) : cluster (mapCells C) i=C i := by
  ext v
  rw [mem_cluster]
  by_cases hEx : ∃ j,v ∈ C j
  · simp only [mapCells,dif_pos hEx,Option.some.injEq]
    constructor
    · intro hh;rw [←hh];exact hEx.choose_spec
    · intro hv
      by_contra hNe
      exact disjoint_left.mp (hDis hEx.choose i hNe) hEx.choose_spec hv
  · have hn : v ∉ C i := fun hv => hEx ⟨i,hv⟩
    simp [mapCells,hEx,hn]

theorem exists_chunked_partition (A : I → Finset V) (m : ℕ) (hm : 0 < m)
    (hDis : ∀ i j,i ≠ j → Disjoint (A i) (A j))
    (hCover : univ.biUnion A=univ) :
    ∃ g : V → Option (Σ i : I,Fin ((A i).card/m)),
      (∀ j,(cluster g j).card=m) ∧ (∀ j,cluster g j ⊆ A j.1) ∧
      (exceptional g).card ≤ Fintype.card I*(m-1) := by
  choose C hSub hSize hPair hRest using fun i => exists_uniform_chunks (A i) m hm
  let B : (Σ i : I,Fin ((A i).card/m)) → Finset V := fun j => C j.1 j.2
  have hBDis : ∀ i j,i ≠ j → Disjoint (B i) (B j) := by
    rintro ⟨i,a⟩ ⟨j,b⟩ hij
    by_cases hParent : i=j
    · subst j
      exact hPair i a b (by intro he;subst b;exact hij rfl)
    · exact (hDis i j hParent).mono (hSub i a) (hSub j b)
  let g := mapCells B
  have hGSize : ∀ j,(cluster g j).card=m := by
    intro j;rw [cluster_mapCells B hBDis];exact hSize j.1 j.2
  refine ⟨g,hGSize,?_,?_⟩
  · intro j;rw [cluster_mapCells B hBDis];exact hSub j.1 j.2
  · have hOld : ∑ i : I,(A i).card=Fintype.card V := by
      have hh := card_biUnion (s:=univ) (t:=A) (fun i _ j _ hij => hDis i j hij)
      rw [hCover,card_univ] at hh
      exact hh.symm
    have hRemainder : ∀ i : I,(A i).card ≤ m*((A i).card/m)+(m-1) := by
      intro i
      have hh := Nat.mod_add_div (A i).card m
      have ht := Nat.mod_lt (A i).card hm
      omega
    have hSum := sum_le_sum (s:=univ) (fun i _ => hRemainder i)
    rw [hOld,sum_add_distrib,←mul_sum] at hSum
    simp only [sum_const,card_univ,nsmul_eq_mul] at hSum
    simp at hSum
    have hIndices : Fintype.card (Σ i : I,Fin ((A i).card/m))=∑ i : I,(A i).card/m := by
      simp only [Fintype.card_sigma,Fintype.card_fin]
    have hOrder := order_eq g m hGSize
    rw [hIndices] at hOrder
    omega

theorem exists_chunked_subpartition (A : I → Finset V) (m : ℕ) (hm : 0 < m)
    (hDis : ∀ i j,i ≠ j → Disjoint (A i) (A j)) :
    ∃ g : V → Option (Σ i : I,Fin ((A i).card/m)),
      (∀ j,(cluster g j).card=m) ∧ (∀ j,cluster g j ⊆ A j.1) ∧
      (exceptional g).card ≤ (univ\univ.biUnion A).card+Fintype.card I*(m-1) := by
  choose C hSub hSize hPair hRest using fun i => exists_uniform_chunks (A i) m hm
  let B : (Σ i : I,Fin ((A i).card/m)) → Finset V := fun j => C j.1 j.2
  have hBDis : ∀ i j,i ≠ j → Disjoint (B i) (B j) := by
    rintro ⟨i,a⟩ ⟨j,b⟩ hij
    by_cases hParent : i=j
    · subst j
      exact hPair i a b (by intro he;subst b;exact hij rfl)
    · exact (hDis i j hParent).mono (hSub i a) (hSub j b)
  let g := mapCells B
  have hGSize : ∀ j,(cluster g j).card=m := by
    intro j;rw [cluster_mapCells B hBDis];exact hSize j.1 j.2
  refine ⟨g,hGSize,?_,?_⟩
  · intro j;rw [cluster_mapCells B hBDis];exact hSub j.1 j.2
  · have hOld : ∑ i : I,(A i).card=(univ.biUnion A).card :=
      (card_biUnion (s:=univ) (t:=A) (fun i _ j _ hij => hDis i j hij)).symm
    have hRemainder : ∀ i : I,(A i).card ≤ m*((A i).card/m)+(m-1) := by
      intro i
      have hh := Nat.mod_add_div (A i).card m
      have ht := Nat.mod_lt (A i).card hm
      omega
    have hSum := sum_le_sum (s:=univ) (fun i _ => hRemainder i)
    rw [hOld,sum_add_distrib,←mul_sum] at hSum
    simp only [sum_const,card_univ,nsmul_eq_mul] at hSum
    simp at hSum
    have hIndices : Fintype.card (Σ i : I,Fin ((A i).card/m))=∑ i : I,(A i).card/m := by
      simp only [Fintype.card_sigma,Fintype.card_fin]
    have hOrder := order_eq g m hGSize
    rw [hIndices] at hOrder
    have hUniverse := card_sdiff_add_card_inter (univ : Finset V) (univ.biUnion A)
    simp only [univ_inter,card_univ] at hUniverse
    omega

end OverfullWork.DirectedClusterQuotient
