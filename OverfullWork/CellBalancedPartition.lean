module

public import OverfullWork.CellRespectingPairing
public import OverfullWork.RegularCompletionPartition

@[expose] public section


/-! # One partition balances both cells and degree rows

This constructs the common partition used in CMS Lemma 5.4's pairing
step. The cells must already have even order, and the specified pair
must lie in one cell (the exceptional cell in the paper). No regularity,
reduced-graph expansion or bipartite robust expansion is postulated.
-/
namespace OverfullWork.CellBalancedPartition
open Finset
open scoped Classical
variable {V I R : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Fintype R]

theorem exists_matrix_partition (f : V→I) (m : ℕ) (hcard : Fintype.card V=2*m)
    (hEven : ∀i,Even (Fintype.card {v : V // f v=i}))
    (x y : V) (hxy : x≠y) (hSame : f x=f y)
    (w : R→V→ℝ) (hw : ∀r v,0≤w r v ∧ w r v≤1)
    (b : ℝ) (hb : 0≤b) (hsize : 15*(Fintype.card R:ℝ)*(m:ℝ)^3<b^6) :
    ∃A : Finset V,A.card=m ∧ Aᶜ.card=m ∧ (x∈A ↔ y∉A) ∧
      (∀i,(A.filter fun v=>f v=i).card=(Aᶜ.filter fun v=>f v=i).card) ∧
      ∀r,|(∑v∈A,w r v)-(∑v∈Aᶜ,w r v)|<b := by
  obtain ⟨e,hCell,j,hPair⟩:=CellRespectingPairing.exists_pairing_with_pair
    f m hcard hEven x y hxy hSame
  obtain ⟨A,hA,hAc,hSep,hDis⟩:=PairedPartition.exists_balanced_partition e w hw b hb hsize
  refine ⟨A,hA,hAc,?_,fun i=>CellRespectingPairing.cell_halves f e hCell A hSep i,hDis⟩
  rcases hPair with ⟨hx,hy⟩|⟨hy,hx⟩
  · have hh:=hSep j
    rw [hx,hy] at hh
    simpa only [not_not] using hh.not.symm
  · simpa only [hx,hy] using hSep j

end OverfullWork.CellBalancedPartition

namespace OverfullWork.CellBalancedPartition
open SimpleGraph Finset
open scoped Classical
universe u v

/-- A uniform threshold precedes all graph and cell data. The SAME
partition halves every even cell, separates the specified pair, and
controls weighted degrees in the supplied actual regular completion. -/
theorem exists_uniform_completed_partition (ε : ℝ) (hε : 0<ε) :
    ∃m₀ : ℕ,∀{V : Type u} [Fintype V] [DecidableEq V]
      {I : Type v} [Fintype I] [DecidableEq I]
      (G : SimpleGraph V) [DecidableRel G.Adj] (M : MultiGraph V) (m D : ℕ),
      m₀≤m → Fintype.card V=2*m → M.IsRegularOfDegree D →
      (∀e,(MultiGraph.ofSimpleGraph G).mult e≤M.mult e) →
      ∀f : V→I,(∀i,Even (Fintype.card {v : V // f v=i})) →
      ∀x y : V,x≠y → f x=f y →
      ∃A : Finset V,A.card=m ∧ Aᶜ.card=m ∧ (x∈A ↔ y∉A) ∧
        (∀i,(A.filter fun v=>f v=i).card=(Aᶜ.filter fun v=>f v=i).card) ∧
        ∀z,|(M.degreeInto A z:ℝ)-(M.degreeInto Aᶜ z:ℝ)|<
          ε*(m:ℝ)+((D-G.degree z:ℕ):ℝ) := by
  obtain ⟨m₀,hm₀⟩:=MultiGraph.eventually_sixth_size ε hε
  refine ⟨m₀,?_⟩
  intro V _ _ I _ _ G _ M m D hm hcard hreg hsub f hEven x y hxy hSame
  let w:V→V→ℝ:=fun z v=>if G.Adj z v then 1 else 0
  have hw:∀z v,0≤w z v ∧ w z v≤1:=by intro z v;dsimp [w];split_ifs <;>norm_num
  have hsize:15*(Fintype.card V:ℝ)*(m:ℝ)^3<(ε*(m:ℝ))^6:=by
    rw [hcard]
    push_cast
    have hh:=hm₀ m hm
    nlinarith only [hh]
  obtain ⟨A,hA,hAc,hSep,hCells,hDis⟩:=exists_matrix_partition f m hcard hEven
    x y hxy hSame w hw (ε*(m:ℝ)) (by positivity) hsize
  refine ⟨A,hA,hAc,hSep,hCells,?_⟩
  intro z
  have hd:|((MultiGraph.ofSimpleGraph G).degreeInto A z:ℝ)-
      ((MultiGraph.ofSimpleGraph G).degreeInto Aᶜ z:ℝ)|<ε*(m:ℝ):=by
    simpa only [MultiGraph.degreeInto,MultiGraph.ofSimpleGraph,SimpleGraph.mem_edgeSet,
      Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,w] using hDis z
  have hb:=MultiGraph.regular_discrepancy_from_simple M G D hreg hsub A z
  linarith

end OverfullWork.CellBalancedPartition
