module

public import OverfullWork.EqualEvenCellRefinement
public import OverfullWork.RegularPairNeighbourhood

@[expose] public section


/-! # Equal even cells and degree control on one actual partition

The exceptional set, the refined cell map and the final balanced cut
are all constructed. Supplied old-cell size bounds pay an explicit loss
per cell. Bipartite robust expansion is not asserted here.
-/
namespace OverfullWork.RegularityCompatibleCompletionPartition
open SimpleGraph Finset
open scoped Classical

theorem split_filter_card {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (g : V→I) (A : Finset V) (i : I) :
    (A.filter fun v=>g v=i).card+(Aᶜ.filter fun v=>g v=i).card=
      (univ.filter fun v=>g v=i).card := by
  have hh:=sum_add_sum_compl A (fun v=>if g v=i then (1:ℕ) else 0)
  simpa only [←card_filter] using hh

universe u v

/-- A graph-independent threshold, a constructed bounded exceptional
set, equal even refined cells, and a SINGLE cut with exact cell halves,
the prescribed distinguished-pair separation and completed degree bounds. -/
theorem exists_uniform_partition (ε : ℝ) (hε : 0<ε) :
    ∃m₀ : ℕ,∀{V : Type u} [Fintype V] [DecidableEq V]
      {I : Type v} [Fintype I] [DecidableEq I]
      (G : SimpleGraph V) [DecidableRel G.Adj] (M : MultiGraph V) (m D : ℕ),
      m₀≤m → Fintype.card V=2*m → M.IsRegularOfDegree D →
      (∀e,(MultiGraph.ofSimpleGraph G).mult e≤M.mult e) →
      ∀(f : V→I) (E : Finset V) (l c : ℕ),
      (∀i,2*l≤(Eᶜ.filter fun v=>f v=i).card ∧
        (Eᶜ.filter fun v=>f v=i).card≤2*l+c) →
      ∀x y : V,x∈E → y∈E → x≠y →
      ∃E' : Finset V,∃g : V→Option I,∃A : Finset V,
        E⊆E' ∧ E'.card≤E.card+c*Fintype.card I ∧
        (∀z,g z=none ↔ z∈E') ∧
        (∀i,(univ.filter fun z=>g z=some i)⊆Eᶜ.filter (fun z=>f z=i)) ∧
        A.card=m ∧ Aᶜ.card=m ∧ (x∈A ↔ y∉A) ∧
        (∀i,(A.filter fun z=>g z=some i).card=l ∧
          (Aᶜ.filter fun z=>g z=some i).card=l) ∧
        ∀z,|(M.degreeInto A z:ℝ)-(M.degreeInto Aᶜ z:ℝ)|<
          ε*(m:ℝ)+((D-G.degree z:ℕ):ℝ) := by
  obtain ⟨m₀,hm₀⟩:=CellBalancedPartition.exists_uniform_completed_partition.{u,max 0 v} ε hε
  refine ⟨m₀,?_⟩
  intro V _ _ I _ _ G _ M m D hm hcard hreg hsub f E l c hSizes x y hx hy hxy
  obtain ⟨E',g,hEsub,hEbound,hNone,hSizes',hMap,hEven⟩:=
    EqualEvenCellRefinement.exists_refinement f E m l c hcard hSizes
  have hxg:g x=none:=(hNone x).mpr (hEsub hx)
  have hyg:g y=none:=(hNone y).mpr (hEsub hy)
  obtain ⟨A,hA,hAc,hSep,hCells,hDis⟩:=hm₀ G M m D hm hcard hreg hsub g hEven x y hxy
    (hxg.trans hyg.symm)
  refine ⟨E',g,A,hEsub,hEbound,hNone,?_,hA,hAc,hSep,?_,hDis⟩
  · intro i z hz
    have hzg:g z=some i:=(mem_filter.mp hz).2
    apply mem_filter.mpr
    refine ⟨mem_compl.mpr ?_,hMap z i hzg⟩
    intro hzE
    have hn:g z=none:=(hNone z).mpr (hEsub hzE)
    rw [hn] at hzg
    cases hzg
  · intro i
    have hh:=hCells (some i)
    have hs:=split_filter_card g A (some i)
    rw [hSizes' i] at hs
    omega

end OverfullWork.RegularityCompatibleCompletionPartition
