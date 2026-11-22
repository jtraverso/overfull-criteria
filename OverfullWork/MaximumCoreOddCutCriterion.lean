module

public import OverfullWork.TopThreePairReserve

@[expose] public section


/-! Odd-cut criterion for an all-maximum odd core and independent complement. -/
namespace OverfullWork.MaximumCoreOddCutCriterion
open SimpleGraph Finset OddCutDeficit MatchingOddDeficiency PaperSmallCutGeometry
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 32000000

theorem overfull_omits_at_most_one (H : SimpleGraph V) [DecidableRel H.Adj]
    (X : Finset V) (k : ℕ) (hY : Xᶜ.card ≤ k)
    (hHigh : ∀ v ∈ X, H.degree v=H.maxDegree)
    (hDense : Fintype.card V+k+3 ≤ 2*H.maxDegree)
    (hSmall : 4*(k+2) ≤ H.maxDegree)
    (S : Finset V) (hOdd : Odd S.card)
    (hOver : H.maxDegree*(S.card/2) < internalEdges H S) : (X\S).card ≤ 1 := by
  by_contra! hMany
  let A := X\S
  let q := A.card
  have hq : 2 ≤ q := by change 1 < q at hMany;omega
  have hASub : A ⊆ Sᶜ := by intro v hv;exact mem_compl.mpr (mem_sdiff.mp hv).2
  have hBig : H.maxDegree < S.card := by
    have hSimple := NearTightOddSetGeometry.internalEdges_le_card_mul_half H S hOdd
    by_contra! hn
    have hh := Nat.mul_le_mul_right (S.card/2) hn
    omega
  have hSize : q+H.maxDegree+1 ≤ Fintype.card V := by
    have hc := card_le_card hASub
    have ht := card_add_card_compl S
    omega
  have hComp : Sᶜ.card ≤ q+k := (complement_card_le_missing_add X S).trans (by dsimp only [q,A];omega)
  have hSum : (∑ v ∈ A, H.degree v)=q*H.maxDegree := by
    rw [sum_congr rfl (fun v hv => hHigh v (mem_sdiff.mp hv).1)]
    simp [q,A]
  have hCut := selected_degrees_le_cut_add H S A hASub
  have hCost : q*(Sᶜ.card-1) ≤ q*(q+k) := Nat.mul_le_mul_left q (by omega)
  have hLower := quadratic_boundary_lower H.maxDegree 0 k (Fintype.card V) q hq hSize (by omega) (by omega)
  have hGap : (H.maxDegree-0-k-q)+k+q=H.maxDegree := by omega
  have hProduct := congrArg (fun t => q*t) hGap
  have hCutLower : H.maxDegree ≤ cutEdges H S := by
    rw [hSum] at hCut
    change q*H.maxDegree ≤ cutEdges H S+q*(Sᶜ.card-1) at hCut
    nlinarith only [hCut,hCost,hLower,hProduct]
  exact (not_lt_of_ge ((odd_internal_bound_iff_cut_deficit H H.maxDegree H.degree_le_maxDegree S hOdd).mpr (by omega))) hOver

theorem cut_insert_independent_one_leaf (H : SimpleGraph V) [DecidableRel H.Adj]
    (Z : Finset V) (v : V) (hv : v ∉ Z) (hInd : H.IsIndepSet (Z:Set V))
    (hLeaves : ((Plantholt.nbIn H Z v).filter (fun u => H.degree u=1)).card ≤ 1) :
    H.degree v ≤ cutEdges H (insert v Z)+1 := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel H.Adj)
    (fun a b => Classical.propDecidable (H.Adj a b)))
  let A := Plantholt.nbIn H Z v
  have hASub : A ⊆ Z := by intro u hu;exact (mem_filter.mp hu).2
  have hPoint : ∀ u ∈ A, 2 ≤ H.degree u+(if H.degree u=1 then 1 else 0) := by
    intro u hu
    have hAdj : H.Adj v u := (mem_neighborFinset _ _ _).mp (mem_filter.mp hu).1
    have hPos := (H.degree_pos_iff_exists_adj u).mpr ⟨v,hAdj.symm⟩
    split_ifs <;> omega
  have hSum := sum_le_sum hPoint
  rw [sum_add_distrib] at hSum
  have hCount : (∑ u ∈ A, if H.degree u=1 then 1 else 0)=(A.filter (fun u => H.degree u=1)).card := by simp
  rw [hCount] at hSum
  simp only [sum_const,smul_eq_mul] at hSum
  have hSubSum := sum_le_sum_of_subset_of_nonneg hASub (f := fun u => H.degree u) (fun _ _ _ => Nat.zero_le _)
  have hInternal : internalEdges H (insert v Z)=A.card := by
    rw [InducedEdgeExchange.internal_edges_insert H Z v hv,internal_zero_of_independent H Z hInd,zero_add]
  have hCut := internal_cut_identity H (insert v Z)
  rw [hInternal,sum_insert hv] at hCut
  change (A.filter (fun u => H.degree u=1)).card ≤ 1 at hLeaves
  omega

theorem core_superset_nonoverfull (H : SimpleGraph V) [DecidableRel H.Adj]
    (X : Finset V) (hOdd : Odd X.card)
    (hInd : H.IsIndepSet (↑(Xᶜ):Set V)) (b : ℕ)
    (hTotal : H.maxDegree ≤ ∑ y ∈ Xᶜ, H.degree y)
    (hUpper : (∑ y ∈ Xᶜ, H.degree y) ≤ H.maxDegree+b) (hb : b ≤ 2*H.maxDegree)
    (hPairs : ∀ y ∈ Xᶜ, ∀ z ∈ Xᶜ, y ≠ z →
      2*(H.degree y+H.degree z) ≤ (∑ v ∈ Xᶜ, H.degree v)+H.maxDegree)
    (S : Finset V) (hS : Odd S.card) (hXS : X ⊆ S) :
    internalEdges H S ≤ H.maxDegree*(S.card/2) := by
  let W := S\X
  have hWY : W ⊆ Xᶜ := by intro v hv;exact mem_compl.mpr (mem_sdiff.mp hv).2
  have hScY : Sᶜ ⊆ Xᶜ := by intro v hv;exact mem_compl.mpr (fun hh => (mem_compl.mp hv) (hXS hh))
  have hWSub : W ⊆ S := sdiff_subset
  have hWCard : W.card+X.card=S.card := card_sdiff_add_card_eq_card hXS
  have hEven : Even W.card := by
    obtain ⟨a,ha⟩ := hOdd
    obtain ⟨b,hb⟩ := hS
    exact ⟨b-a,by omega⟩
  have hPartition : W ∪ Sᶜ=Xᶜ := by
    ext v
    simp only [W,mem_union,mem_sdiff,mem_compl]
    have hsub : v ∈ X → v ∈ S := fun hv => hXS hv
    tauto
  have hDisjoint : Disjoint W Sᶜ := disjoint_left.mpr (fun v hv hvSc => (mem_compl.mp hvSc) (hWSub hv))
  have hSumSplit : (∑ v ∈ W, H.degree v)+(∑ v ∈ Sᶜ, H.degree v)=∑ v ∈ Xᶜ, H.degree v := by
    rw [←sum_union hDisjoint,hPartition]
  have hScInd : H.IsIndepSet (↑(Sᶜ):Set V) := by
    rw [SimpleGraph.isIndepSet_iff]
    intro v hv w hw hvw hAdj
    exact hInd (hScY hv) (hScY hw) hvw hAdj
  have hCut := cut_eq_complementary_degree_sum H S hScInd
  have hDef : (∑ v ∈ W, (H.maxDegree-H.degree v)) ≤ deficitMass H H.maxDegree S :=
    sum_le_sum_of_subset_of_nonneg hWSub (fun _ _ _ => Nat.zero_le _)
  have hDefSum : (∑ v ∈ W, (H.maxDegree-H.degree v))+(∑ v ∈ W, H.degree v)=W.card*H.maxDegree := by
    rw [←sum_add_distrib]
    simp_rw [Nat.sub_add_cancel (H.degree_le_maxDegree _)]
    simp
  have hReserve : H.maxDegree+2*(∑ v ∈ W, H.degree v) ≤
      W.card*H.maxDegree+(∑ v ∈ Xᶜ, H.degree v) := by
    by_cases hZero : W.card=0
    · have hEmpty := card_eq_zero.mp hZero
      simp only [hEmpty,sum_empty,card_empty,zero_mul,zero_add,mul_zero,add_zero]
      exact hTotal
    by_cases hTwo : W.card=2
    · obtain ⟨y,z,hyz,hW⟩ := card_eq_two.mp hTwo
      have hy : y ∈ W := by rw [hW];simp
      have hz : z ∈ W := by rw [hW];simp
      have hP := hPairs y (hWY hy) z (hWY hz) hyz
      rw [hW,sum_pair hyz,card_pair hyz]
      omega
    · have hFour : 4 ≤ W.card := by obtain ⟨a,ha⟩ := hEven;omega
      have hLe := sum_le_sum_of_subset_of_nonneg hWY (f := fun u => H.degree u) (fun _ _ _ => Nat.zero_le _)
      have hMul := Nat.mul_le_mul_right H.maxDegree hFour
      omega
  apply (odd_internal_bound_iff_cut_deficit H H.maxDegree H.degree_le_maxDegree S hS).mpr
  omega

theorem no_overfull_of_omission_bound (H : SimpleGraph V) [DecidableRel H.Adj]
    (X : Finset V) (hOdd : Odd X.card) (hCore : ∀ v ∈ X, H.degree v=H.maxDegree)
    (hInd : H.IsIndepSet (↑(Xᶜ):Set V)) (b : ℕ)
    (hTotal : H.maxDegree ≤ ∑ y ∈ Xᶜ, H.degree y)
    (hUpper : (∑ y ∈ Xᶜ, H.degree y) ≤ H.maxDegree+b) (hb : b ≤ 2*H.maxDegree)
    (hPairs : ∀ y ∈ Xᶜ, ∀ z ∈ Xᶜ, y ≠ z →
      2*(H.degree y+H.degree z) ≤ (∑ v ∈ Xᶜ, H.degree v)+H.maxDegree)
    (hLeaves : ∀ v ∈ X, ((Plantholt.nbIn H Xᶜ v).filter (fun u => H.degree u=1)).card ≤ 1)
    (hOmissions : ∀ S : Finset V,Odd S.card →
      H.maxDegree*(S.card/2) < internalEdges H S → (X \ S).card ≤ 1) :
    ¬H.HasOverfullSubgraph := by
  rintro ⟨S,hOver⟩
  have hS : Odd S.card := by
    by_contra hh
    exact (not_lt_of_ge (even_internal_bound H H.maxDegree H.degree_le_maxDegree S (Nat.not_odd_iff_even.mp hh))) hOver
  have hOmit := hOmissions S hS hOver
  by_cases hZero : (X\S).card=0
  · have hXS : X ⊆ S := sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp hZero)
    exact (not_lt_of_ge (core_superset_nonoverfull H X hOdd hInd b hTotal hUpper hb hPairs S hS hXS)) hOver
  · obtain ⟨v,hOnly⟩ := card_eq_one.mp (show (X\S).card=1 by omega)
    have hvXS : v ∈ X\S := by rw [hOnly];simp
    have hvX := (mem_sdiff.mp hvXS).1
    let Z := Sᶜ.erase v
    have hZY : Z ⊆ Xᶜ := by
      intro u hu
      apply mem_compl.mpr
      intro huX
      have huOmit : u ∈ X\S := mem_sdiff.mpr ⟨huX,mem_compl.mp (mem_erase.mp hu).2⟩
      rw [hOnly,mem_singleton] at huOmit
      exact (mem_erase.mp hu).1 huOmit
    have hZInd : H.IsIndepSet (Z:Set V) := by
      rw [SimpleGraph.isIndepSet_iff]
      intro a ha b hb hab hAdj
      exact hInd (hZY ha) (hZY hb) hab hAdj
    have hZLeaves : ((Plantholt.nbIn H Z v).filter (fun u => H.degree u=1)).card ≤ 1 := by
      apply (card_le_card ?_).trans (hLeaves v hvX)
      intro u hu
      obtain ⟨huNb,huDegree⟩ := mem_filter.mp hu
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨(mem_filter.mp huNb).1,hZY (mem_filter.mp huNb).2⟩,huDegree⟩
    have hSc : insert v Z=Sᶜ := insert_erase (mem_compl.mpr (mem_sdiff.mp hvXS).2)
    have hCut := cut_insert_independent_one_leaf H Z v (notMem_erase _ _) hZInd hZLeaves
    rw [hSc,hCore v hvX,NearTightOddSetGeometry.cutEdges_compl] at hCut
    have hNear : H.maxDegree ≤ deficitMass H H.maxDegree S+cutEdges H S+1 := by omega
    have hBound := (odd_internal_bound_iff_cut_deficit H H.maxDegree H.degree_le_maxDegree S hS).mpr
      (odd_budget_of_one_below H S hS (by omega))
    exact (not_lt_of_ge hBound) hOver

theorem no_overfull (H : SimpleGraph V) [DecidableRel H.Adj]
    (X : Finset V) (hOdd : Odd X.card) (hCore : ∀ v ∈ X, H.degree v=H.maxDegree)
    (hInd : H.IsIndepSet (↑(Xᶜ):Set V)) (b k : ℕ) (hY : Xᶜ.card ≤ k)
    (hTotal : H.maxDegree ≤ ∑ y ∈ Xᶜ, H.degree y)
    (hUpper : (∑ y ∈ Xᶜ, H.degree y) ≤ H.maxDegree+b) (hb : b ≤ 2*H.maxDegree)
    (hPairs : ∀ y ∈ Xᶜ, ∀ z ∈ Xᶜ, y ≠ z →
      2*(H.degree y+H.degree z) ≤ (∑ v ∈ Xᶜ, H.degree v)+H.maxDegree)
    (hLeaves : ∀ v ∈ X, ((Plantholt.nbIn H Xᶜ v).filter (fun u => H.degree u=1)).card ≤ 1)
    (hDense : Fintype.card V+k+3 ≤ 2*H.maxDegree) (hSmall : 4*(k+2) ≤ H.maxDegree) :
    ¬H.HasOverfullSubgraph := by
  exact no_overfull_of_omission_bound H X hOdd hCore hInd b hTotal hUpper hb hPairs hLeaves
    (overfull_omits_at_most_one H X k hY hCore hDense hSmall)

end OverfullWork.MaximumCoreOddCutCriterion
