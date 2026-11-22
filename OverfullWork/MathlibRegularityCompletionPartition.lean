module

public import OverfullWork.RegularityCompatibleCompletionPartition
public import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma

@[expose] public section


/-! # Invoke Mathlib regularity in the actual completion partition

The uniform equipartition comes from `szemeredi_regularity`; it is not
reproved. Moving the two specified vertices to the exceptional set and
trimming each remaining part loses at most four vertices per old part.
The resulting ONE cut balances the refined parts and completed degrees.
This does not prove reduced-graph or bipartite robust expansion.
-/
namespace OverfullWork.MathlibRegularityCompletionPartition
open SimpleGraph Finset Finpartition
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def cellMap (P : Finpartition (univ : Finset V)) (v : V) : P.parts :=
  ⟨P.part v,P.part_mem.mpr (mem_univ v)⟩

theorem cellMap_mem_iff (P : Finpartition (univ : Finset V)) (v : V) (i : P.parts) :
    cellMap P v=i ↔ v∈i.val := by
  change (⟨P.part v,_⟩:P.parts)=i ↔ v∈i.val
  rw [Subtype.mk_eq_mk]
  exact P.part_eq_iff_mem i.property

theorem outside_cell_eq (P : Finpartition (univ : Finset V)) (E : Finset V) (i : P.parts) :
    (Eᶜ.filter fun v=>cellMap P v=i)=i.val\E := by
  ext v
  simp only [mem_filter,mem_compl,mem_sdiff,cellMap_mem_iff]
  tauto

/-- The nearly equal Mathlib part sizes yield the exact numerical
input of the equal-even-cell constructor, including after deleting E. -/
theorem outside_cell_sizes (P : Finpartition (univ : Finset V)) (hP : P.IsEquipartition)
    (E : Finset V) (i : P.parts) :
    let l:=(Fintype.card V/P.parts.card-E.card)/2
    2*l≤(Eᶜ.filter fun v=>cellMap P v=i).card ∧
      (Eᶜ.filter fun v=>cellMap P v=i).card≤2*l+(E.card+2) := by
  dsimp only
  rw [outside_cell_eq]
  have hlo:=hP.average_le_card_part i.property
  have hhi:=hP.card_part_le_average_add_one i.property
  simp only [card_univ] at hlo hhi
  have hsplit:=card_sdiff_add_card_inter i.val E
  have hinter:(i.val∩E).card≤E.card:=card_le_card inter_subset_right
  omega

end OverfullWork.MathlibRegularityCompletionPartition

namespace OverfullWork.MathlibRegularityCompletionPartition
open SimpleGraph Finset Finpartition
open scoped Classical
universe u

/-- Construct the Mathlib regularity partition, bounded exceptional set,
equal even subcells and the degree-controlled completion cut in one theorem.
Both tolerances and the lower bound on the number of parts precede the graph.
The degree error is linear with an explicit deficit term; this is not the
full CMS Lemma5.4 or its n^(2/3) bound. -/
theorem exists_uniform_partition (η ε : ℝ) (hη : 0<η) (hηsmall : η≤(1:ℝ)/2)
    (hε : 0<ε) (k : ℕ) :
    ∃m₀ : ℕ,∀{V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (M : MultiGraph V) (m D : ℕ),
      m₀≤m → Fintype.card V=2*m → M.IsRegularOfDegree D →
      (∀e,(MultiGraph.ofSimpleGraph G).mult e≤M.mult e) → ∀x y : V,x≠y →
      ∃P : Finpartition (univ : Finset V),P.IsEquipartition ∧ P.IsUniform G η ∧
        k≤P.parts.card ∧ P.parts.card≤SzemerediRegularity.bound η k ∧
        let l:=(Fintype.card V/P.parts.card-2)/2
        2≤l ∧ ∃E' : Finset V,∃g : V→Option P.parts,∃A : Finset V,
          ({x,y}:Finset V)⊆E' ∧ E'.card≤2+4*SzemerediRegularity.bound η k ∧
          (E'.card:ℝ)<η*(m:ℝ) ∧
          (∀z,g z=none ↔ z∈E') ∧
          (∀i,(univ.filter fun z=>g z=some i)⊆i.val) ∧
          A.card=m ∧ Aᶜ.card=m ∧ (x∈A ↔ y∉A) ∧
          (∀i,(A.filter fun z=>g z=some i).card=l ∧
            (Aᶜ.filter fun z=>g z=some i).card=l) ∧
          (∀i j : P.parts,G.IsUniform η i.val j.val →
            G.IsUniform (2*η) (univ.filter fun z=>g z=some i)
              (univ.filter fun z=>g z=some j)) ∧
          ∀z,|(M.degreeInto A z:ℝ)-(M.degreeInto Aᶜ z:ℝ)|<
            ε*(m:ℝ)+((D-G.degree z:ℕ):ℝ) := by
  obtain ⟨m₀,hm₀⟩:=RegularityCompatibleCompletionPartition.exists_uniform_partition.{u,u} ε hε
  let K:=SzemerediRegularity.bound η k
  obtain ⟨q,hq⟩:=exists_nat_gt (((2+4*K:ℕ):ℝ)/η)
  refine ⟨max (max m₀ k) (max q (4*(K+1))),?_⟩
  intro V _ _ G _ M m D hm hcard hreg hsub x y hxy
  have hm':m₀≤m:=by omega
  have hk:k≤Fintype.card V:=by omega
  obtain ⟨P,hP,hLow,hHigh,hUniform⟩:=szemeredi_regularity G hη hk
  let E:Finset V:={x,y}
  have hEcard:E.card=2:=by exact card_pair hxy
  let l:=(Fintype.card V/P.parts.card-2)/2
  have hPpos:0<P.parts.card:=card_pos.mpr ⟨P.part x,P.part_mem.mpr (mem_univ x)⟩
  have hPbound:P.parts.card≤K:=hHigh
  have hOrder:8*P.parts.card≤Fintype.card V:=by omega
  have hAverage:8≤Fintype.card V/P.parts.card:=(Nat.le_div_iff_mul_le hPpos).mpr hOrder
  have hl:2≤l:=by dsimp only [l];omega
  have hSizes:∀i : P.parts,2*l≤(Eᶜ.filter fun z=>cellMap P z=i).card ∧
      (Eᶜ.filter fun z=>cellMap P z=i).card≤2*l+4:=by
    intro i
    have hh:=outside_cell_sizes P hP E i
    simpa only [hEcard] using hh
  obtain ⟨E',g,A,hEsub,hEbound,hNone,hSub,hA,hAc,hSep,hCells,hDis⟩:=
    hm₀ G M m D hm' hcard hreg hsub (cellMap P) E l 4 hSizes x y
      (by simp [E]) (by simp [E]) hxy
  have hSmall:E'.card≤2+4*K:=by
    have hb:E'.card≤2+4*P.parts.card:=by simpa only [hEcard,Fintype.card_coe] using hEbound
    exact hb.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 4 hPbound) 2)
  have hRelative:(E'.card:ℝ)<η*(m:ℝ):=by
    have hq':((2+4*K:ℕ):ℝ)<(q:ℝ)*η:=(div_lt_iff₀ hη).mp hq
    have hqm:(q:ℝ)≤m:=by exact_mod_cast (show q≤m by omega)
    have hqm':η*(q:ℝ)≤η*(m:ℝ):=mul_le_mul_of_nonneg_left hqm hη.le
    have hb:(E'.card:ℝ)≤((2+4*K:ℕ):ℝ):=by exact_mod_cast hSmall
    nlinarith
  have hNewSub:∀i,(univ.filter fun z=>g z=some i)⊆i.val:=by
    intro i z hz
    have hv:=hSub i hz
    rw [outside_cell_eq] at hv
    exact (mem_sdiff.mp hv).1
  have hNewSize:∀i : P.parts,(univ.filter fun z=>g z=some i).card=2*l:=by
    intro i
    have hh:=RegularityCompatibleCompletionPartition.split_filter_card g A (some i)
    rw [(hCells i).1,(hCells i).2] at hh
    omega
  have hHalf:∀i : P.parts,(i.val.card:ℝ)≤2*((univ.filter fun z=>g z=some i).card:ℝ):=by
    intro i
    have hhi:=hP.card_part_le_average_add_one i.property
    simp only [card_univ] at hhi
    have hs:=hNewSize i
    have hn:i.val.card≤2*(univ.filter fun z=>g z=some i).card:=by
      dsimp only [l] at hs hl
      omega
    exact_mod_cast hn
  have hNewUniform:∀i j : P.parts,G.IsUniform η i.val j.val →
      G.IsUniform (2*η) (univ.filter fun z=>g z=some i) (univ.filter fun z=>g z=some j):=by
    intro i j hij
    exact RegularPairNeighbourhood.uniform_on_half_subcells G hηsmall hij
      (hNewSub i) (hNewSub j) (hHalf i) (hHalf j)
  exact ⟨P,hP,hUniform,hLow,hHigh,hl,E',g,A,hEsub,hSmall,hRelative,hNone,hNewSub,
    hA,hAc,hSep,hCells,hNewUniform,hDis⟩

end OverfullWork.MathlibRegularityCompletionPartition
