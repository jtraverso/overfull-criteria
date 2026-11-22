module

public import OverfullWork.OddTwoExceptionCriterion
public import OverfullWork.LowSkeletonPreparation

@[expose] public section


/-! # Constructed choices in the small low-set cases of CMS Step 2

Two deficient vertices can be charged and projected to distinct core
representatives. A singleton low vertex has two actual distinct neighbours;
one can be selected avoiding any prescribed deficient vertex. These are
choices and sparse skeletons, not a spanning-layer realization.
-/
namespace OverfullWork.OddLowSmallCases
open SimpleGraph Finset LowVertexMatchingAbsorption SparseDeficitCore
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-- The pair and its actual representative matching are data. -/
structure ChargedPair (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (U : Finset V) where
  left : V
  right : V
  distinct : left≠right
  left_charge : G.degree left+1≤D
  right_charge : G.degree right+1≤D
  projection : LowSkeletonProjection.Projection G {left,right} U ∅

/-- The two representative vertices are distinct, including when one or
both original endpoints already lie outside U. -/
theorem ChargedPair.representatives_distinct {G : SimpleGraph V} [DecidableRel G.Adj]
    {D : ℕ} {U : Finset V} (P : ChargedPair G D U) :
    (P.projection.representative ⟨P.left,by simp⟩).val≠
      (P.projection.representative ⟨P.right,by simp⟩).val := by
  intro he
  have hh:=P.projection.injective (Subtype.ext he)
  exact P.distinct (congrArg Subtype.val hh)

/-- W=0 means every degree exceeds one third of D. The displayed finite
budget constructs the charged pair and its injection; neither is an input. -/
theorem exists_charged_pair_of_no_low_vertices
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (U : Finset V)
    (hW : ∀w,D<3*G.degree w)
    (hdef : 2≤(univ.filter fun w=>G.degree w<D).card)
    (hbudget : 3*(U.card+2)≤D) : Nonempty (ChargedPair G D U) := by
  obtain ⟨u,hu,v,hv,huv⟩:=one_lt_card.mp (show 1<(univ.filter fun w=>G.degree w<D).card by omega)
  have huD : G.degree u+1≤D := by have hh:=(mem_filter.mp hu).2;omega
  have hvD : G.degree v+1≤D := by have hh:=(mem_filter.mp hv).2;omega
  obtain ⟨P⟩:=LowSkeletonProjection.exists_projection_without_extra_forbidden G {u,v} U (by
    intro w _
    have hh:=hW w
    simp only [card_pair huv]
    omega)
  exact ⟨⟨u,v,huv,huD,hvD,P⟩⟩

/-- The exact empty-low-set test discharges the one-third-degree inequality. -/
theorem exists_charged_pair_of_lowVertices_eq_empty
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    (hW : lowVertices G=∅)
    (hdef : 2≤(univ.filter fun w=>G.degree w<G.maxDegree).card)
    (hbudget : 3*(U.card+2)≤G.maxDegree) :
    Nonempty (ChargedPair G G.maxDegree U) := by
  apply exists_charged_pair_of_no_low_vertices G G.maxDegree U ?_ hdef hbudget
  intro w
  have hw : w∉lowVertices G := by rw [hW];simp
  simp only [lowVertices,mem_filter,mem_univ,true_and] at hw
  omega

/-- A vertex of degree at least two supplies two real distinct neighbours. -/
theorem exists_two_neighbours (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V) (hw : 2≤G.degree w) :
    ∃a b,a≠b ∧ G.Adj w a ∧ G.Adj w b := by
  have hh : 1<(G.neighborFinset w).card := by rw [card_neighborFinset_eq_degree];omega
  obtain ⟨a,ha,b,hb,hab⟩:=one_lt_card.mp hh
  exact ⟨a,b,hab,(mem_neighborFinset _ _ _).mp ha,(mem_neighborFinset _ _ _).mp hb⟩

/-- In the singleton odd case, select one of the two actual matching
edges so that it avoids the deficient vertex x. -/
theorem exists_singleton_edge_avoiding (G : SimpleGraph V) [DecidableRel G.Adj]
    (w x : V) (hw : 2≤G.degree w) :
    ∃a,a≠x ∧ G.Adj w a := by
  obtain ⟨a,b,hab,hwa,hwb⟩:=exists_two_neighbours G w hw
  by_cases ha : a=x
  · exact ⟨b,fun hb=>hab (ha.trans hb.symm),hwb⟩
  · exact ⟨a,ha,hwa⟩

/-- The even singleton choice is the actual two-edge path, with its
precise degrees. It introduces two outside endpoints and is acyclic. -/
theorem exists_singleton_path (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V) (hw : 2≤G.degree w) :
    ∃a b,a≠b ∧ G.Adj w a ∧ G.Adj w b ∧
      (edge w a⊔edge w b)≤G ∧ (edge w a⊔edge w b).IsAcyclic ∧
      ∀z,(edge w a⊔edge w b).degree z=
        (if z=w then 2 else if z=a ∨ z=b then 1 else 0) := by
  obtain ⟨a,b,hab,hwa,hwb⟩:=exists_two_neighbours G w hw
  have hwa' : w≠a:=G.ne_of_adj hwa
  have hwb' : w≠b:=G.ne_of_adj hwb
  have hmatching : OneFactor.IsMatchingGraph (edge w a) := by
    intro u v z huv huz
    simp only [edge_adj] at huv huz
    rcases huv.1 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
      rcases huz.1 with ⟨h1,h2⟩|⟨h1,h2⟩ <;> grind
  have hnot : ¬(edge w a).Adj w b := by simp [edge_adj,hwa',hwb',Ne.symm hab]
  refine ⟨a,b,hab,hwa,hwb,sup_le ((edge_le_iff G).mpr (Or.inr hwa)) ((edge_le_iff G).mpr (Or.inr hwb)),
    PaperLowSkeleton.matching_sup_edge_isAcyclic _ hmatching hwb' hnot,?_⟩
  intro z
  rw [PaperLowSkeleton.matching_sup_edge_degree _ hwb' hnot]
  have he : (edge w a).degree z=if z=w ∨ z=a then 1 else 0 := by
    have hh:=PaperLowSkeleton.matching_sup_edge_degree (⊥:SimpleGraph V)
      hwa' (by simp) z
    have hdeg : (edge w a).degree z=(⊥⊔edge w a).degree z := by
      rw [←card_neighborSet_eq_degree,←card_neighborSet_eq_degree]
      apply Fintype.card_congr
      exact Equiv.subtypeEquivRight (by intro t; simp)
    rw [hdeg]
    simpa only [SimpleGraph.bot_degree,Nat.zero_add] using hh
  rw [he]
  by_cases hzw : z=w <;> by_cases hza : z=a <;> by_cases hzb : z=b <;>
    simp_all

/-- The singleton odd case uses one actual low edge and one charged
vertex x. Choosing the edge avoids x, and the same numerical budget
constructs the required representative matching. -/
theorem exists_singleton_odd_preparation
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) (w x : V)
    (hW : lowVertices G={w}) (hw : 2≤G.degree w) (hxw : x≠w)
    (hx : G.degree x<G.maxDegree) (hbudget : 3*(U.card+2)≤G.maxDegree) :
    ∃a,a≠x ∧ G.Adj w a ∧ G.degree x+1≤G.maxDegree ∧
      Nonempty (LowSkeletonProjection.Projection G {a,x} U ∅) := by
  obtain ⟨a,hax,hwa⟩:=exists_singleton_edge_avoiding G w x hw
  have haw : a≠w := Ne.symm (G.ne_of_adj hwa)
  refine ⟨a,hax,hwa,by omega,?_⟩
  apply LowSkeletonProjection.exists_projection_without_extra_forbidden
  intro z hz
  have hzpair : z=a ∨ z=x := by simpa only [mem_insert,mem_singleton] using (mem_inter.mp hz).1
  have hzw : z≠w := by rcases hzpair with rfl|rfl;exact haw;exact hxw
  have hznot : z∉lowVertices G := by rw [hW];simpa
  have hhigh : G.maxDegree<3*G.degree z := by
    simp only [lowVertices,mem_filter,mem_univ,true_and] at hznot
    omega
  simp only [card_pair hax]
  omega

/-- The even singleton case constructs the two-edge path and projects
its two outside endpoints injectively to the retained core. -/
theorem exists_singleton_even_preparation
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) (w : V)
    (hW : lowVertices G={w}) (hw : 2≤G.degree w)
    (hbudget : 3*(U.card+2)≤G.maxDegree) :
    ∃a b,a≠b ∧ G.Adj w a ∧ G.Adj w b ∧
      (edge w a⊔edge w b)≤G ∧ (edge w a⊔edge w b).IsAcyclic ∧
      (∀z,(edge w a⊔edge w b).degree z=
        (if z=w then 2 else if z=a ∨ z=b then 1 else 0)) ∧
      Nonempty (LowSkeletonProjection.Projection G {a,b} U ∅) := by
  obtain ⟨a,b,hab,hwa,hwb,hle,hacy,hdeg⟩:=exists_singleton_path G w hw
  refine ⟨a,b,hab,hwa,hwb,hle,hacy,hdeg,?_⟩
  apply LowSkeletonProjection.exists_projection_without_extra_forbidden
  intro z hz
  have hzpair : z=a ∨ z=b := by simpa only [mem_insert,mem_singleton] using (mem_inter.mp hz).1
  have hzw : z≠w := by
    rcases hzpair with rfl|rfl
    · exact Ne.symm (G.ne_of_adj hwa)
    · exact Ne.symm (G.ne_of_adj hwb)
  have hznot : z∉lowVertices G := by rw [hW];simpa
  have hhigh : G.maxDegree<3*G.degree z := by
    simp only [lowVertices,mem_filter,mem_univ,true_and] at hznot
    omega
  simp only [card_pair hab]
  omega

/-- Criticality supplies the two-neighbour hypothesis at every vertex. -/
theorem critical_two_le_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) (w : V) : 2≤G.degree w := by
  obtain ⟨a,b,hab⟩:=MaximumCoreTwo.exists_adj_of_not_colorable G hc.2.1
  obtain ⟨z,hwz⟩:=MaximumCoreTwo.exists_adj_of_connected hc.1 hab w
  exact Overfull.two_le_degree hc hwz.symm

universe u
/-- G1 supplies the actual projection budget for every small-case pair.
The exceptional scale and order threshold are fixed before the graph. -/
theorem above_half_small_case_projection_budget (ε : ℝ) (hε : 0<ε) :
    ∃q : ℕ,2≤q ∧ ∃N : ℕ,
      ∀{W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj],
        N≤Fintype.card W → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card W:ℝ)≤(G.maxDegree:ℝ) →
        3*((exceptions G G.maxDegree (Fintype.card W/(8*q))).card+2)≤G.maxDegree := by
  obtain ⟨q,hq,N,hcore⟩:=CriticalDenseCoreTrimming.above_half_critical_sparse_trimming.{u} ε hε
  refine ⟨q,hq,N,?_⟩
  intro W _ _ G _ hn hc hdense
  obtain ⟨hk,hU,_⟩:=hcore G hn hc hdense
  let k:=Fintype.card W/(4096*q^2)
  let U:=exceptions G G.maxDegree (Fintype.card W/(8*q))
  change 0<k at hk
  change U.card≤k at hU
  have hnD : Fintype.card W≤2*G.maxDegree := by
    have he : 0≤ε*(Fintype.card W:ℝ) := by positivity
    exact_mod_cast (show (Fintype.card W:ℝ)≤2*(G.maxDegree:ℝ) by nlinarith only [hdense,he])
  have h32 : 32≤4096*q^2 := by nlinarith [sq_nonneg (q:ℤ)]
  have hkn : 32*k≤Fintype.card W :=
    (Nat.mul_le_mul_right k h32).trans (Nat.mul_div_le (Fintype.card W) (4096*q^2))
  change 3*(U.card+2)≤G.maxDegree
  omega

/-- Both parity choices for a singleton are constructed at every large
above-half critical graph. G1 and criticality discharge all degree and
projection budgets; there is no prescribed matching or layer input. -/
theorem above_half_singleton_choices (ε : ℝ) (hε : 0<ε) :
    ∃q : ℕ,2≤q ∧ ∃N : ℕ,
      ∀{W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj],
        N≤Fintype.card W → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card W:ℝ)≤(G.maxDegree:ℝ) →
        let U:=exceptions G G.maxDegree (Fintype.card W/(8*q))
        ∀w,lowVertices G={w} →
          (∃a b,a≠b ∧ G.Adj w a ∧ G.Adj w b ∧
            (edge w a⊔edge w b)≤G ∧ (edge w a⊔edge w b).IsAcyclic ∧
            (∀z,(edge w a⊔edge w b).degree z=
              (if z=w then 2 else if z=a ∨ z=b then 1 else 0)) ∧
            Nonempty (LowSkeletonProjection.Projection G {a,b} U ∅)) ∧
          (∀x,x≠w → G.degree x<G.maxDegree →
            ∃a,a≠x ∧ G.Adj w a ∧ G.degree x+1≤G.maxDegree ∧
              Nonempty (LowSkeletonProjection.Projection G {a,x} U ∅)) := by
  obtain ⟨q,hq,N,hbudget⟩:=above_half_small_case_projection_budget.{u} ε hε
  refine ⟨q,hq,N,?_⟩
  intro W _ _ G _ hn hc hdense
  dsimp only
  intro w hW
  have hw:=critical_two_le_degree G hc w
  have hb:=hbudget G hn hc hdense
  refine ⟨exists_singleton_even_preparation G _ w hW hw hb,?_⟩
  intro x hxw hx
  exact exists_singleton_odd_preparation G _ w x hW hw hxw hx hb

/-- Above one half, an odd critical graph without an overfull witness has
at least three deficient vertices. This uses the proved two-exception
criterion, rather than postulating a spare charged endpoint. -/
theorem above_half_critical_three_deficient (ε : ℝ) (hε : 0<ε) :
    ∃N : ℕ,∀{W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj],
      N≤Fintype.card W → Overfull.IsDeltaCritical G → ¬G.HasOverfullSubgraph →
      Odd (Fintype.card W) →
      ((1:ℝ)/2+ε)*(Fintype.card W:ℝ)≤(G.maxDegree:ℝ) →
      3≤(univ.filter fun w=>G.degree w<G.maxDegree).card := by
  obtain ⟨N,hN⟩:=PairIdentification.above_half_at_most_two_degree_exceptions.{u} ε hε
  refine ⟨N,?_⟩
  intro W _ _ G _ hn hc hno hodd hdense
  by_contra hh
  have hsmall : (univ.filter fun w=>G.degree w<G.maxDegree).card≤2 := by omega
  exact hc.2.1 ((hN G hn hodd hdense hsmall).mpr hno)

/-- CMS S2.4.1 at the genuine initial critical graph: the deficient pair,
its charged units, and its injective representatives are all constructed.
The exceptional set is supplied uniformly by the proved critical deficit
estimate. No projection or spanning layer is assumed. -/
theorem above_half_empty_low_charged_pair (ε : ℝ) (hε : 0<ε) :
    ∃q : ℕ,2≤q ∧ ∃N : ℕ,
      ∀{W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj],
        N≤Fintype.card W → Overfull.IsDeltaCritical G → ¬G.HasOverfullSubgraph →
        Odd (Fintype.card W) →
        ((1:ℝ)/2+ε)*(Fintype.card W:ℝ)≤(G.maxDegree:ℝ) →
        lowVertices G=∅ →
        Nonempty (ChargedPair G G.maxDegree
          (exceptions G G.maxDegree (Fintype.card W/(8*q)))) := by
  obtain ⟨q,hq,N₀,hcore⟩:=CriticalDenseCoreTrimming.above_half_critical_sparse_trimming.{u} ε hε
  obtain ⟨N₁,hdef⟩:=above_half_critical_three_deficient.{u} ε hε
  refine ⟨q,hq,max N₀ N₁,?_⟩
  intro W _ _ G _ hn hc hno hodd hdense hW
  have hn₀ : N₀≤Fintype.card W := (le_max_left N₀ N₁).trans hn
  have hn₁ : N₁≤Fintype.card W := (le_max_right N₀ N₁).trans hn
  obtain ⟨hk,hU,_⟩:=hcore G hn₀ hc hdense
  let k:=Fintype.card W/(4096*q^2)
  let U:=exceptions G G.maxDegree (Fintype.card W/(8*q))
  change 0<k at hk
  change U.card≤k at hU
  have hnD : Fintype.card W≤2*G.maxDegree := by
    have he : 0≤ε*(Fintype.card W:ℝ) := by positivity
    exact_mod_cast (show (Fintype.card W:ℝ)≤2*(G.maxDegree:ℝ) by nlinarith only [hdense,he])
  have h32 : 32≤4096*q^2 := by nlinarith [sq_nonneg (q:ℤ)]
  have hkn : 32*k≤Fintype.card W :=
    (Nat.mul_le_mul_right k h32).trans (Nat.mul_div_le (Fintype.card W) (4096*q^2))
  have hbudget : 3*(U.card+2)≤G.maxDegree := by omega
  have hdeficient:=hdef G hn₁ hc hno hodd hdense
  exact exists_charged_pair_of_lowVertices_eq_empty G U hW (by omega) hbudget

end OverfullWork.OddLowSmallCases
