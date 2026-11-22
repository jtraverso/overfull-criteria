module

public import OverfullWork.CMSOperation41PrefixClassTwo
public import OverfullWork.CMSOperation41DegreeLedger

@[expose] public section


/-! A degree record computable before the ordinary pack is chosen.
The virtual graph already accounts for all prescribed and cleanup
edges. The only remaining debit is the ordinary portion of the
prescribed degree in each previous physical layer. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem degree_of_disjoint_trimming_prefix (L : ℕ → SimpleGraph V) (j : ℕ) (v : V)
    (hDis : ∀ i < j,∀ k < j,i ≠ k → Disjoint (L i) (L k)) :
    (usedTrimmingPrefix L j).degree v = ∑ i : Fin j,(L i.val).degree v := by
  have hN : (usedTrimmingPrefix L j).neighborFinset v =
      (univ : Finset (Fin j)).biUnion (fun i => (L i.val).neighborFinset v) := by
    ext x
    rw [mem_neighborFinset]
    change (⨆ i : Fin j,L i.val).Adj v x ↔ _
    simp only [iSup_adj,mem_biUnion,mem_univ,true_and,mem_neighborFinset]
  have hNDis : ∀ (i : Fin j),i ∈ (univ : Finset (Fin j)) →
      ∀ k ∈ (univ : Finset (Fin j)),i ≠ k →
        Disjoint ((L i.val).neighborFinset v) ((L k.val).neighborFinset v) := by
    intro i _ k _ hne
    exact disjoint_neighborFinset_of_disjoint (L i.val) (L k.val) v
      (hDis i.val i.isLt k.val k.isLt (fun h => hne (Fin.ext h)))
  rw [←card_neighborFinset_eq_degree,hN,card_biUnion hNDis]
  simp only [card_neighborFinset_eq_degree]

theorem degree_sup_eq_add_of_disjoint_trimming (P L : SimpleGraph V) (hDis : Disjoint P L)
    (v : V) :
    (P ⊔ L).degree v = P.degree v+L.degree v := by
  have hN : (P ⊔ L).neighborFinset v = P.neighborFinset v ∪ L.neighborFinset v := by
    ext x
    simp only [mem_neighborFinset,sup_adj,mem_union]
  rw [←card_neighborFinset_eq_degree,hN,
    card_union_of_disjoint (disjoint_neighborFinset_of_disjoint P L v hDis)]
  simp only [card_neighborFinset_eq_degree]

noncomputable def auxiliaryPhysicalDegree (S : SimpleGraph V)
    (U : Finset V) (P : ℕ → SimpleGraph V) (credit : ℕ → V → ℕ) (j : ℕ) (v : V) : ℕ :=
  if v ∈ U then S.degree v
  else S.degree v-(∑ i : Fin j,((2-credit i.val v)-(P i.val).degree v))

/-- Step 1 changes only the current virtual graph. All ordinary
debits owed to earlier rounds stay fixed. -/
theorem auxiliary_physical_degree_after_cleanup (S T : SimpleGraph V)
    (U : Finset V) (P : ℕ → SimpleGraph V) (credit : ℕ → V → ℕ) (j : ℕ)
    (hLe : T ≤ S) (v : V) :
    auxiliaryPhysicalDegree T U P credit j v =
      auxiliaryPhysicalDegree S U P credit j v-(sdiff S T).degree v := by
  have hBalance : T.degree v+(sdiff S T).degree v = S.degree v := by
    simpa only [add_comm,←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      MaximumMatching.degree_sdiff_add_of_le S T hLe v
  by_cases hv : v ∈ U
  · simp only [auxiliaryPhysicalDegree,if_pos hv]
    omega
  · simp only [auxiliaryPhysicalDegree,if_neg hv]
    omega

theorem auxiliary_physical_degree_eq (S : SimpleGraph V)
    (U : Finset V) (P L : ℕ → SimpleGraph V) (credit : ℕ → V → ℕ) (j : ℕ)
    (hLe : ∀ i < j,L i ≤ S)
    (hDis : ∀ i < j,∀ k < j,i ≠ k → Disjoint (L i) (L k))
    (hDisParts : ∀ i < j,Disjoint (P i) (L i))
    (hOutside : ∀ i < j,∀ v ∈ U,(L i).degree v = 0)
    (hPrescribed : ∀ i < j,∀ v,v ∉ U → (P i ⊔ L i).degree v = 2-credit i v) :
    ∀ v,auxiliaryPhysicalDegree S U P credit j v =
      (sdiff S (usedTrimmingPrefix L j)).degree v := by
  intro v
  let Used := usedTrimmingPrefix L j
  change auxiliaryPhysicalDegree S U P credit j v = (sdiff S Used).degree v
  have hUsed : Used ≤ S := iSup_le fun i : Fin j => hLe i.val i.isLt
  have hBalance : (sdiff S Used).degree v+Used.degree v = S.degree v := by
    simpa only [←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      MaximumMatching.degree_sdiff_add_of_le S Used hUsed v
  have hDegree : Used.degree v = ∑ i : Fin j,(L i.val).degree v :=
    degree_of_disjoint_trimming_prefix L j v hDis
  by_cases hv : v ∈ U
  · have he : Used.degree v = 0 := by
      rw [hDegree]
      exact sum_eq_zero (fun i _ => hOutside i.val i.isLt v hv)
    rw [auxiliaryPhysicalDegree,if_pos hv]
    omega
  · have hEach (i : Fin j) : (L i.val).degree v = (2-credit i.val v)-(P i.val).degree v := by
      have hS := degree_sup_eq_add_of_disjoint_trimming (P i.val) (L i.val)
        (hDisParts i.val i.isLt) v
      rw [hPrescribed i.val i.isLt v hv] at hS
      omega
    have hSum : Used.degree v = ∑ i : Fin j,((2-credit i.val v)-(P i.val).degree v) := by
      rw [hDegree]
      exact sum_congr rfl (fun i _ => hEach i)
    rw [auxiliaryPhysicalDegree,if_neg hv]
    omega

theorem auxiliary_physical_degree_after_round (S C : SimpleGraph V)
    (U : Finset V) (P : ℕ → SimpleGraph V) (credit : ℕ → V → ℕ) (j : ℕ)
    (hC : C ≤ S) (hP : P j ≤ sdiff S C)
    (hDebit : ∀ v,v ∉ U → (P j).degree v ≤ 2-credit j v) (v : V) :
    let T := sdiff (sdiff S C) (P j)
    let loss := if v ∈ U then (P j).degree v else 2-credit j v
    auxiliaryPhysicalDegree T U P credit (j+1) v =
      auxiliaryPhysicalDegree S U P credit j v-(C.degree v+loss) := by
  intro T loss
  have hBalance : T.degree v+(P j).degree v+C.degree v = S.degree v := by
    simpa only [T,←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      physical_trim_degree_balance S C (P j) hC hP v
  by_cases hv : v ∈ U
  · simp only [auxiliaryPhysicalDegree,if_pos hv,loss]
    omega
  · have hMon := hDebit v hv
    simp only [auxiliaryPhysicalDegree,if_neg hv,loss,Fin.sum_univ_castSucc,
      Fin.val_castSucc,Fin.val_last]
    omega

end OverfullWork.CMSTrimmingRound
