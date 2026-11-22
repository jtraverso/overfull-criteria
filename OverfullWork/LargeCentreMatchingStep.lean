module

public import OverfullWork.CriticalIndependentPairMatching
public import OverfullWork.DegreeTwoRealization
public import OverfullWork.MaximumMatchingPeeling

@[expose] public section


/-! # An actual first matching-removal round in the large-centre branch

The two cross edges are constructed by strict Hall. The rest is a real
perfect matching in the even dense core. The excluded anchor is explicitly
nonmaximum; otherwise avoiding it would not lower the maximum degree.
No no-overfull property of the residue or ability to iterate is claimed.
-/
namespace OverfullWork.LargeCentreMatchingStep
open SimpleGraph Finset OddCutDeficit NormalizedAlmostStoppingRun
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000

theorem matching_on_add_edge (G M : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel M.Adj] (W : Finset V) (hM : Plantholt.IsMatchingOn G M W)
    (u v : V) (hu : u∉W) (hv : v∉W) (huv : G.Adj u v) :
    Plantholt.IsMatchingOn G (M⊔edge u v) (insert u (insert v W)) := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun a b=>Classical.propDecidable (G.Adj a b)))
  cases (Subsingleton.elim (inferInstance : DecidableRel M.Adj)
    (fun a b=>Classical.propDecidable (M.Adj a b)))
  have hne:=G.ne_of_adj huv
  have hDis:Disjoint M (edge u v):=by
    apply disjoint_iff_inf_le.mpr
    intro a b ⟨hab,hEdge⟩
    have haW:a∉W:=by
      rcases (edge_adj u v a b).mp hEdge with ⟨h₁,h₂⟩|⟨h₁,h₂⟩ <;> aesop
    have hp:0<M.degree a:=(M.degree_pos_iff_exists_adj a).mpr ⟨b,hab⟩
    have hz:=hM.2.2 a haW
    omega
  have hAdd:∀w,(M⊔edge u v).degree w=M.degree w+(edge u v).degree w:=by
    intro w
    rw [←card_neighborFinset_eq_degree,neighborFinset_sup,
      card_union_of_disjoint (disjoint_neighborFinset_of_disjoint M (edge u v) w hDis),
      card_neighborFinset_eq_degree,card_neighborFinset_eq_degree]
  refine ⟨sup_le hM.1 ?_,?_,?_⟩
  · intro a b hab
    rcases (edge_adj u v a b).mp hab with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact huv
    · exact huv.symm
  · intro w hw
    rw [hAdd,DegreeTwoRealization.degree_edge_exact u v w hne]
    rcases mem_insert.mp hw with hw|hw
    · subst w
      rw [hM.2.2 u hu,if_pos (Or.inl rfl)]
    rcases mem_insert.mp hw with hw|hw
    · subst w
      rw [hM.2.2 v hv,if_pos (Or.inr rfl)]
    · rw [hM.2.1 w hw,if_neg (by
        rintro (he|he)
        · exact hu (he ▸ hw)
        · exact hv (he ▸ hw))]
  · intro w hw
    have hw':w≠u ∧ w≠v ∧ w∉W:=by simpa only [mem_insert,not_or] using hw
    rw [hAdd,hM.2.2 w hw'.2.2,DegreeTwoRealization.degree_edge_exact u v w hne,
      if_neg (by tauto)]

structure Round (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) (x y z : V) where
  matching : SimpleGraph V
  le_original : matching≤G
  degree_le_one : ∀v,matching.degree v≤1
  core_degrees : ∀v∈c.set,matching.degree v=if v=x then 0 else 1
  complementary_degrees : ∀v∈c.setᶜ,matching.degree v=if v=y ∨ v=z then 1 else 0
  residual_maxDegree : (G\matching).maxDegree=G.maxDegree-1
  residual_uncolourable : ¬(G\matching).EdgeColorable (G\matching).maxDegree

/-- The complete matching round is constructed from finite degree
margins and the actual critical cut. No core matching is supplied. -/
theorem exists_round (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) {B K : ℕ} (c : Certificate G B K)
    (x : V) (hx : x∈c.set) (hLarge : G.degree x<(∑y∈c.setᶜ,G.degree y))
    (hxD : G.degree x<G.maxDegree)
    (hMargin : Fintype.card V+2*B+c.setᶜ.card+3≤2*G.maxDegree)
    (y z : V) (hy : y∈c.setᶜ) (hz : z∈c.setᶜ) (hyz : y≠z) :
    Nonempty (Round G c x y z) := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun a b=>Classical.propDecidable (G.Adj a b)))
  obtain ⟨a,b,ha,hb,hax,hbx,hab,hya,hzb⟩:=
    CriticalIndependentPairMatching.exists_pair_edges G hc c hx hLarge y z hy hz hyz
  let W:=((c.set.erase x).erase a).erase b
  have ha':a∈c.set.erase x:=mem_erase.mpr ⟨hax,ha⟩
  have hb':b∈(c.set.erase x).erase a:=mem_erase.mpr ⟨hab.symm,mem_erase.mpr ⟨hbx,hb⟩⟩
  have hCard:W.card+3=c.set.card:=by
    dsimp only [W]
    rw [card_erase_of_mem hb',card_erase_of_mem ha',card_erase_of_mem hx]
    have hThree:3≤c.set.card:=by
      have hp:0<((c.set.erase x).erase a).card:=card_pos.mpr ⟨b,hb'⟩
      rw [card_erase_of_mem ha',card_erase_of_mem hx] at hp
      omega
    omega
  have hEven:Even W.card:=by
    obtain ⟨t,ht⟩:=c.odd
    exact ⟨t-1,by omega⟩
  have hComp:Wᶜ.card=c.setᶜ.card+3:=by
    have h₁:=card_add_card_compl W
    have h₂:=card_add_card_compl c.set
    omega
  have hDense:∀v∈W,W.card≤2*(Plantholt.nbIn G W v).card:=by
    intro v hv
    have hvX:v∈c.set:=(mem_erase.mp (mem_erase.mp (mem_erase.mp hv).2).2).2
    have hvx:v≠x:=(mem_erase.mp (mem_erase.mp (mem_erase.mp hv).2).2).1
    have hLower:=LargeCentreCriticalGeometry.other_degree_lower G c hx hLarge hvX hvx
    have hSub:G.neighborFinset v⊆Plantholt.nbIn G W v∪Wᶜ:=by
      intro w hw
      by_cases hwW:w∈W
      · exact mem_union_left _ (mem_filter.mpr ⟨hw,hwW⟩)
      · exact mem_union_right _ (mem_compl.mpr hwW)
    have hCount:=(card_le_card hSub).trans (card_union_le _ _)
    rw [card_neighborFinset_eq_degree,hComp] at hCount
    have hTotal:=card_add_card_compl W
    omega
  obtain ⟨N,hN⟩:=Plantholt.exists_matchingOn G hEven hDense
  have hyX:y∉c.set:=mem_compl.mp hy
  have hzX:z∉c.set:=mem_compl.mp hz
  have hyW:y∉W:=by simp only [W,mem_erase];tauto
  have haW:a∉W:=by simp only [W,mem_erase];tauto
  have hbW:b∉W:=by simp only [W,mem_erase];tauto
  have hzW:z∉W:=by simp only [W,mem_erase];tauto
  have hzy:z≠y:=hyz.symm
  have hza:z≠a:=fun he=>hzX (he.symm ▸ ha)
  have hby:b≠y:=fun he=>hyX (he ▸ hb)
  have hM₁:=matching_on_add_edge G N W hN y a hyW haW hya
  have hM₂:=matching_on_add_edge G (N⊔edge y a) (insert y (insert a W)) hM₁ z b
    (by simp only [mem_insert];tauto) (by simp only [mem_insert];tauto) hzb
  let F:=(N⊔edge y a)⊔edge z b
  let S:=(c.set.erase x)∪{y,z}
  have hSet:insert z (insert b (insert y (insert a W)))=S:=by
    ext v
    have hyx:y≠x:=fun he=>hyX (he.symm ▸ hx)
    have hzx:z≠x:=fun he=>hzX (he.symm ▸ hx)
    by_cases hva:v=a <;> by_cases hvb:v=b <;>
      simp_all [W,S,or_left_comm,or_comm]
  have hOn:Plantholt.IsMatchingOn G F S:=by simpa only [hSet] using hM₂
  have hDeg:∀v,F.degree v=if v∈S then 1 else 0:=by
    intro v
    split_ifs with hv
    · exact hOn.2.1 v hv
    · exact hOn.2.2 v hv
  have hOne:∀v,F.degree v≤1:=by intro v;rw [hDeg];split_ifs <;>omega
  have hMatch:OneFactor.IsMatchingGraph F:=by
    intro v a' b' hva hvb
    have hCard':(F.neighborFinset v).card≤1:=by simpa only [card_neighborFinset_eq_degree] using hOne v
    exact card_le_one.mp hCard' a' ((mem_neighborFinset _ _ _).mpr hva) b' ((mem_neighborFinset _ _ _).mpr hvb)
  have hCore:∀v∈c.set,F.degree v=if v=x then 0 else 1:=by
    intro v hv
    rw [hDeg]
    have hvy:v≠y:=fun he=>hyX (he ▸ hv)
    have hvz:v≠z:=fun he=>hzX (he ▸ hv)
    simp only [S,mem_union,mem_erase,mem_insert,mem_singleton]
    split_ifs <;>tauto
  have hY:∀v∈c.setᶜ,F.degree v=if v=y ∨ v=z then 1 else 0:=by
    intro v hv
    rw [hDeg]
    have hvX:v∉c.set:=mem_compl.mp hv
    simp only [S,mem_union,mem_erase,mem_insert,mem_singleton]
    simp only [hvX,and_false,false_or]
  have hCover:∀v,G.degree v=G.maxDegree → ∃!w,F.Adj v w:=by
    intro v hv
    have hvX:v∈c.set:=by
      by_contra hn
      have hh:=CriticalIndependentPairMatching.complement_nonmaximum G hc c hx hLarge v (mem_compl.mpr hn)
      omega
    have hvx:v≠x:=by intro he;subst v;omega
    apply degree_eq_one_iff_existsUnique_adj.mp
    rw [hCore v hvX,if_neg hvx]
  have hD:0<G.maxDegree:=by omega
  have hMax:(G\F).maxDegree=G.maxDegree-1:=by
    simpa only [SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
      ←Nat.card_eq_fintype_card] using
      MaximumMatching.maxDegree_sdiff_of_matching_cover G F hD hOn.1 hCover
  have hUncol:¬(G\F).EdgeColorable (G\F).maxDegree:=by
    simpa only [SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
      ←Nat.card_eq_fintype_card] using
      MaximumMatching.critical_residue_not_colourable G F hc hD hOn.1 hMatch hCover
  exact ⟨⟨F,hOn.1,hOne,hCore,hY,
    hMax,hUncol⟩⟩

theorem Round.anchor_degree_eq {G : SimpleGraph V} [DecidableRel G.Adj]
    {B K : ℕ} {c : Certificate G B K} {x y z : V}
    (r : Round G c x y z) (hx : x∈c.set) :
    (G\r.matching).degree x=G.degree x := by
  have hs:(G\r.matching).degree x+r.matching.degree x=G.degree x:=by
    simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      MaximumMatching.degree_sdiff_add_of_le G r.matching r.le_original x
  rw [r.core_degrees x hx,if_pos rfl] at hs
  omega

/-- Exactly two complementary incidences are removed by the actual round. -/
theorem Round.merged_degree_add_two {G : SimpleGraph V} [DecidableRel G.Adj]
    {B K : ℕ} {c : Certificate G B K} {x y z : V}
    (r : Round G c x y z) (hy : y∈c.setᶜ) (hz : z∈c.setᶜ) (hyz : y≠z) :
    (∑v∈c.setᶜ,(G\r.matching).degree v)+2=∑v∈c.setᶜ,G.degree v := by
  have hS:∀v,(G\r.matching).degree v+r.matching.degree v=G.degree v:=by
    intro v
    simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      MaximumMatching.degree_sdiff_add_of_le G r.matching r.le_original v
  have hSum:=sum_congr (s₁:=c.setᶜ) (s₂:=c.setᶜ) rfl (fun v _=>hS v)
  rw [sum_add_distrib] at hSum
  have hSelected:(∑v∈c.setᶜ,r.matching.degree v)=2:=by
    rw [sum_congr rfl (fun v hv=>r.complementary_degrees v hv)]
    have hSplit:∀v:V,(if v=y ∨ v=z then 1 else 0)=
        (if v=y then 1 else 0)+(if v=z then 1 else 0):=by
      intro v
      by_cases hvy:v=y <;> by_cases hvz:v=z <;> simp_all
    simp_rw [hSplit]
    rw [sum_add_distrib]
    simp [hy,hz]
  rw [hSelected] at hSum
  exact hSum

/-- The positive centre excess strictly decreases in a completed round. -/
theorem Round.excess_decreases {G : SimpleGraph V} [DecidableRel G.Adj]
    {B K : ℕ} {c : Certificate G B K} {x y z : V}
    (r : Round G c x y z) (hx : x∈c.set) (hy : y∈c.setᶜ) (hz : z∈c.setᶜ)
    (hyz : y≠z) (hLarge : G.degree x<(∑v∈c.setᶜ,G.degree v)) :
    (∑v∈c.setᶜ,(G\r.matching).degree v)-(G\r.matching).degree x<
      (∑v∈c.setᶜ,G.degree v)-G.degree x := by
  have hSum:=r.merged_degree_add_two hy hz hyz
  have hAnchor:=r.anchor_degree_eq hx
  omega

/-- The odd core loses precisely one unit of deficit when the maximum
falls by one and the excluded nonmaximum anchor keeps its degree. -/
theorem Round.deficit_mass_add_one {G : SimpleGraph V} [DecidableRel G.Adj]
    {B K : ℕ} {c : Certificate G B K} {x y z : V}
    (r : Round G c x y z) (hx : x∈c.set) (hxD : G.degree x<G.maxDegree) :
    deficitMass (G\r.matching) (G\r.matching).maxDegree c.set+1=
      deficitMass G G.maxDegree c.set := by
  rw [r.residual_maxDegree]
  have hPoint:∀v∈c.set,((G.maxDegree-1)-(G\r.matching).degree v)+
      (if v=x then 1 else 0)=G.maxDegree-G.degree v:=by
    intro v hv
    have hS:(G\r.matching).degree v+r.matching.degree v=G.degree v:=by
      simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
        MaximumMatching.degree_sdiff_add_of_le G r.matching r.le_original v
    have hD:=G.degree_le_maxDegree v
    rw [r.core_degrees v hv] at hS
    by_cases hvx:v=x
    · subst v
      rw [if_pos rfl] at hS ⊢
      omega
    · rw [if_neg hvx] at hS ⊢
      omega
  have hSum:=sum_congr rfl hPoint
  rw [sum_add_distrib] at hSum
  have hOne:(∑v∈c.set,if v=x then 1 else 0)=1:=by simp [hx]
  rw [hOne] at hSum
  exact hSum

/-- The original odd stopping core itself stays non-overfull after a
completed round. This assertion is only about c.set, not every odd set
of the residue. Parity pays the two-unit loss of odd-cut slack. -/
theorem Round.core_not_overfull {G : SimpleGraph V} [DecidableRel G.Adj]
    {B K : ℕ} {c : Certificate G B K} {x y z : V}
    (r : Round G c x y z) (hx : x∈c.set) (hy : y∈c.setᶜ) (hz : z∈c.setᶜ)
    (hyz : y≠z) (hxD : G.degree x<G.maxDegree)
    (hLarge : G.degree x<(∑v∈c.setᶜ,G.degree v)) :
    internalEdges (G\r.matching) c.set≤(G\r.matching).maxDegree*(c.set.card/2) := by
  classical
  let R:=G\r.matching
  have hDef:=r.deficit_mass_add_one hx hxD
  have hSum:=r.merged_degree_add_two hy hz hyz
  have hErase:=LargeCentreCriticalGeometry.deficit_erase_add G c.set hx
  have hD:=G.degree_le_maxDegree x
  have hPositive:G.maxDegree<deficitMass G G.maxDegree c.set+(∑v∈c.setᶜ,G.degree v):=by omega
  have hParity:=DegreeOrderedIndependentCut.budget_add_total_degree G c.set
  rw [G.sum_degrees_eq_twice_card_edges] at hParity
  obtain ⟨t,ht⟩:=c.odd
  have hExpand:G.maxDegree*c.set.card+2*(∑v∈c.setᶜ,G.degree v)=
      G.maxDegree+2*(G.maxDegree*t+(∑v∈c.setᶜ,G.degree v)):=by
    rw [ht]
    ring
  rw [hExpand] at hParity
  have hSlack:G.maxDegree+2≤deficitMass G G.maxDegree c.set+(∑v∈c.setᶜ,G.degree v):=by omega
  have hIndependent:G.IsIndepSet (↑(c.setᶜ):Set V):=by simpa only [coe_compl] using c.independent
  have hTwice:(MultiGraph.ofSimpleGraph R).twiceInternal c.setᶜ=0:=by
    unfold MultiGraph.twiceInternal
    apply sum_eq_zero
    intro a ha
    apply sum_eq_zero
    intro b hb
    have hNo:¬R.Adj a b:=by
      intro hab
      exact hIndependent ha hb hab.1.ne hab.1
    simp [MultiGraph.ofSimpleGraph,mem_edgeSet,hNo]
  have hInternal:internalEdges R c.setᶜ=0:=by
    have hh:=(MultiGraph.ofSimpleGraph R).twiceInternal_eq c.setᶜ
    rw [hTwice,←internalEdges_eq_multigraph] at hh
    omega
  have hCut:=internal_cut_identity R c.setᶜ
  rw [hInternal,NearTightOddSetGeometry.cutEdges_compl] at hCut
  apply (odd_internal_bound_iff_cut_deficit R R.maxDegree R.degree_le_maxDegree c.set c.odd).mpr
  have hMax:=r.residual_maxDegree
  change R.maxDegree=G.maxDegree-1 at hMax
  change deficitMass R R.maxDegree c.set+1=deficitMass G G.maxDegree c.set at hDef
  change (∑v∈c.setᶜ,R.degree v)+2=∑v∈c.setᶜ,G.degree v at hSum
  omega

universe u

/-- A freely chosen sparse scale pays the full core matching margin.
The remaining maximum-core case is retained explicitly, as are the
unproved factorization and no-overfull-preservation obligations. -/
theorem above_half_candidate_or_matching_or_maximum_core (ε : ℝ) (hε : 0<ε) :
    ∃Q : ℕ,2≤Q ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N≤Fintype.card V → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        ¬G.HasOverfullSubgraph →
        let k:=Fintype.card V/(4096*Q^2)
        (∃r : CriticalTwoColourReduction.Reduction G,
          (∑v:V,(2-r.layer.degree v))≤2*k+2 ∧
          ¬(G\r.layer).HasOverfullSubgraph) ∨
        ∃c : Certificate G (6*k+6) (k+1),
          Nonempty (NormalizedCanonicalCandidate.Candidate c) ∨
          ((∀v∈c.set,G.degree v=G.maxDegree) ∧
            G.maxDegree<(∑y∈c.setᶜ,G.degree y)) ∨
          (∃x∈c.set,∃y∈c.setᶜ,∃z∈c.setᶜ,y≠z ∧ Nonempty (Round G c x y z)) := by
  obtain ⟨Q,hQ⟩:=exists_nat_gt (max (2:ℝ) (1/ε))
  have hQR:(2:ℝ)≤(Q:ℝ):=(le_max_left _ _).trans hQ.le
  have hQN:2≤Q:=by exact_mod_cast hQR
  have hQε:1≤ε*(Q:ℝ):=by
    have hh:1/ε<(Q:ℝ):=(le_max_right _ _).trans_lt hQ
    have ht:=(div_lt_iff₀ hε).mp hh
    nlinarith only [ht]
  obtain ⟨NF,hFork⟩:=FlexibleAlmostReduction.above_half_normalized_fork_at_budget.{u} ε hε Q hQN
  obtain ⟨NE,hNE⟩:=exists_nat_gt (16/ε)
  refine ⟨Q,hQN,max NF NE,?_⟩
  intro V _ _ G _ hn hc hdense hno
  have hnF:NF≤Fintype.card V:=by omega
  have hnE:NE≤Fintype.card V:=by omega
  dsimp only
  rcases hFork G hnF hc hdense hno with hCert|hReduction
  · obtain ⟨c⟩:=hCert
    right
    refine ⟨c,?_⟩
    let n:=Fintype.card V
    let k:=n/(4096*Q^2)
    have hk:4096*Q^2*k≤n:=Nat.mul_div_le n (4096*Q^2)
    have hkR:(4096:ℝ)*(Q:ℝ)^2*(k:ℝ)≤(n:ℝ):=by exact_mod_cast hk
    have hCoeff:(13:ℝ)≤ε*(4096*(Q:ℝ)^2):=by
      have hh:=mul_le_mul_of_nonneg_left hQε (show 0≤4096*(Q:ℝ) by positivity)
      nlinarith only [hh,hQR]
    have hThirteen:13*(k:ℝ)≤ε*(n:ℝ):=by
      have h₁:=mul_le_mul_of_nonneg_right hCoeff (Nat.cast_nonneg k : (0:ℝ)≤(k:ℝ))
      have h₂:=mul_le_mul_of_nonneg_left hkR hε.le
      nlinarith only [h₁,h₂]
    have hSixteen:(16:ℝ)≤ε*(n:ℝ):=by
      have hh:16/ε<(n:ℝ):=hNE.trans_le (by exact_mod_cast hnE)
      have ht:=(div_lt_iff₀ hε).mp hh
      nlinarith only [ht]
    have hNumeric:n+13*k+16≤2*G.maxDegree:=by
      exact_mod_cast (show (n:ℝ)+13*(k:ℝ)+16≤2*(G.maxDegree:ℝ) by
        nlinarith only [hdense,hThirteen,hSixteen])
    have hMargin:Fintype.card V+2*(6*k+6)+c.setᶜ.card+3≤2*G.maxDegree:=by
      have hSmall:=c.complement_small
      dsimp only [k,n] at hNumeric ⊢
      omega
    have hGap:c.set.card+(6*k+6)+2*c.setᶜ.card≤2*G.maxDegree+2:=by
      have hCards:=card_add_card_compl c.set
      omega
    by_cases hMin:∀x∈c.set,(∑y∈c.setᶜ,G.degree y)≤G.degree x
    · left
      exact NormalizedCanonicalCandidate.exists_candidate G c hno hGap hMin
    · push Not at hMin
      obtain ⟨x,hx,hMinimum,hLarge⟩:=LargeCentreCriticalGeometry.exists_minimum_large_anchor G c hMin
      right
      by_cases hxMax:G.degree x=G.maxDegree
      · left
        refine ⟨?_,?_⟩
        · intro v hv
          have hLo:=hMinimum v hv
          have hHi:=G.degree_le_maxDegree v
          omega
        · simpa only [hxMax] using hLarge
      · right
        have hxD:G.degree x<G.maxDegree:=lt_of_le_of_ne (G.degree_le_maxDegree x) hxMax
        have hTwo:=LargeCentreCriticalGeometry.two_le_complement_card G c hx hLarge
        obtain ⟨y,hy,z,hz,hyz⟩:=one_lt_card.mp (show 1<c.setᶜ.card by omega)
        exact ⟨x,hx,y,hy,z,hz,hyz,exists_round G hc c x hx hLarge hxD hMargin y z hy hz hyz⟩
  · left
    obtain ⟨r,hMissing,hNo⟩:=hReduction
    refine ⟨r,hMissing,?_⟩
    have transport (d₁ d₂ : DecidableRel (G\r.layer).Adj) :
        (¬@SimpleGraph.HasOverfullSubgraph V _ _ (G\r.layer) d₁) →
        ¬@SimpleGraph.HasOverfullSubgraph V _ _ (G\r.layer) d₂:=by
      have hEq:=Subsingleton.elim d₁ d₂
      cases hEq
      exact id
    exact transport _ _ hNo

end OverfullWork.LargeCentreMatchingStep
