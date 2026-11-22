module

public import OverfullWork.PaperTopDegreeMatching

@[expose] public section


/-! # Claim 4.5: odd sets containing the core and two complementary vertices

This is the paper's case (|T intersect X|, |S intersect Y|)=(0,2).
The selected cross edges must use a top-degree pair. The three cases
are precisely zero, one or two selected vertices in the proposed odd set.
No assertion about all subsets of the residue is made by this case alone.
-/
namespace OverfullWork.PaperPairExtensionPreservation
open SimpleGraph Finset OddCutDeficit NormalizedAlmostStoppingRun
open LargeCentreMatchingStep PaperTopDegreeMatching MatchingOddDeficiency
open scoped Classical
attribute [-instance] SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

theorem pair_deficit_le (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) (u v : V) (hu : u∈S) (hv : v∈S) (hne : u≠v) :
    (H.maxDegree-H.degree u)+(H.maxDegree-H.degree v)≤deficitMass H H.maxDegree S := by
  have hSub:({u,v}:Finset V)⊆S:=by
    intro w hw
    rcases mem_insert.mp hw with rfl|hw
    · exact hu
    · exact mem_singleton.mp hw ▸ hv
  have hs:=sum_le_sum_of_subset_of_nonneg hSub (fun _ _ _=>Nat.zero_le _)
    (f:=fun w=>H.maxDegree-H.degree w)
  simpa only [sum_pair hne,deficitMass] using hs

theorem extension_odd {X : Finset V} (hOdd : Odd X.card)
    {u v : V} (hu : u∈Xᶜ) (hv : v∈Xᶜ) (hne : u≠v) :
    Odd (insert u (insert v X)).card := by
  have hCard:=(CriticalAlmostPairNormalization.insert_pair_cardinalities X u v hu hv hne).1
  obtain ⟨t,ht⟩:=hOdd
  exact ⟨t+1,by omega⟩

theorem complement_independent (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) {x y z : V} (r : Round G c x y z)
    (u v : V) : (G\r.matching).IsIndepSet (↑((insert u (insert v c.set))ᶜ):Set V) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro a ha b hb _ hab
  have haX:a∉c.set:=by
    intro ha'
    exact (mem_compl.mp ha) (mem_insert_of_mem (mem_insert_of_mem ha'))
  have hbX:b∉c.set:=by
    intro hb'
    exact (mem_compl.mp hb) (mem_insert_of_mem (mem_insert_of_mem hb'))
  exact c.independent haX hbX hab.1.ne hab.1

/-- The two top original degrees dominate every unselected degree
after the selected vertex loses its one matching edge. -/
theorem unselected_degree_le_selected_add_one (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) {x y z : V}
    (hTop : IsTopPair G c.setᶜ y z) (r : Round G c x y z)
    (w q : V) (hw : w∈c.setᶜ) (hwNot : ¬(w=y ∨ w=z)) (hq : q=y ∨ q=z) :
    (G\r.matching).degree w≤(G\r.matching).degree q+1 := by
  have hDegree:∀a,(G\r.matching).degree a+r.matching.degree a=G.degree a:=by
    intro a
    simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      MaximumMatching.degree_sdiff_add_of_le G r.matching r.le_original a
  have hW:=hDegree w
  rw [r.complementary_degrees w hw,if_neg hwNot] at hW
  rcases hq with he|he
  · subst q
    have hQ:=hDegree y
    rw [r.complementary_degrees y hTop.left_mem,if_pos (Or.inl rfl)] at hQ
    have hRank:=hTop.maximum w hw
    omega
  · subst q
    have hQ:=hDegree z
    rw [r.complementary_degrees z hTop.right_mem,if_pos (Or.inr rfl)] at hQ
    have hRank:=hTop.second w hw (fun he=>hwNot (Or.inl he))
    omega

private theorem selected_pair_nonoverfull (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) {x y z : V}
    (hx : x∈c.set) (hy : y∈c.setᶜ) (hz : z∈c.setᶜ) (hyz : y≠z)
    (r : Round G c x y z) (hNo : ¬G.HasOverfullSubgraph) :
    internalEdges (G\r.matching) (insert y (insert z c.set))≤
      (G\r.matching).maxDegree*((insert y (insert z c.set)).card/2) := by
  let S:=insert y (insert z c.set)
  have hTheta:unmatchedWithin r.matching S={x}:=by
    apply unmatched_eq_singleton_of_supported r.matching S x
      (mem_insert_of_mem (mem_insert_of_mem hx))
    · intro w hw
      have hwX:w∈c.setᶜ:=mem_compl.mpr (fun hh=>hw (mem_insert_of_mem (mem_insert_of_mem hh)))
      have hwNot:¬(w=y ∨ w=z):=by
        rintro (he|he)
        · exact hw (he.symm ▸ mem_insert_self y (insert z c.set))
        · exact hw (he.symm ▸ mem_insert_of_mem (mem_insert_self z c.set))
      rw [r.complementary_degrees w hwX,if_neg hwNot]
    · intro w hw
      by_cases hwX:w∈c.set
      · exact r.core_degrees w hwX
      · have hwSel:w=y ∨ w=z:=by
          rcases mem_insert.mp hw with he|hw
          · exact Or.inl he
          · exact Or.inr ((mem_insert.mp hw).resolve_right hwX)
        have hwx:w≠x:=fun he=>hwX (he.symm ▸ hx)
        rw [r.complementary_degrees w (mem_compl.mpr hwX),if_pos hwSel,if_neg hwx]
  have hD:0<G.maxDegree:=by
    have hPos:0<G.degree y:=(G.degree_pos_iff_exists_adj y).mpr (by
      have hF:r.matching.degree y=1:=by rw [r.complementary_degrees y hy,if_pos (Or.inl rfl)]
      obtain ⟨w,hw⟩:=(r.matching.degree_pos_iff_exists_adj y).mp (by omega)
      exact ⟨w,r.le_original hw⟩)
    exact hPos.trans_le (G.degree_le_maxDegree y)
  have hDrop:(G\r.matching).maxDegree=G.maxDegree-1:=by
    simpa only [SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
      ←Nat.card_eq_fintype_card] using r.residual_maxDegree
  apply internal_nonoverfull_of_one_unmatched G r.matching r.le_original r.degree_le_one hD
    hDrop hNo S (extension_odd c.odd hy hz hyz)
  rw [hTheta,card_singleton]

private theorem none_selected_nonoverfull (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) {x y z : V}
    (hTop : IsTopPair G c.setᶜ y z) (r : Round G c x y z) (hD : 4≤G.maxDegree)
    (u v : V) (hu : u∈c.setᶜ) (hv : v∈c.setᶜ) (huv : u≠v)
    (huNot : ¬(u=y ∨ u=z)) (hvNot : ¬(v=y ∨ v=z)) :
    internalEdges (G\r.matching) (insert u (insert v c.set))≤
      (G\r.matching).maxDegree*((insert u (insert v c.set)).card/2) := by
  let R:=G\r.matching
  let S:=insert u (insert v c.set)
  have hOdd:Odd S.card:=extension_odd c.odd hu hv huv
  have hCut:=cut_eq_complementary_degree_sum R S (complement_independent G c r u v)
  have hyX:y∉c.set:=mem_compl.mp hTop.left_mem
  have hzX:z∉c.set:=mem_compl.mp hTop.right_mem
  have hyOff:y∈Sᶜ:=by
    simp only [S,mem_compl,mem_insert,not_or]
    exact ⟨fun he=>huNot (Or.inl he.symm),fun he=>hvNot (Or.inl he.symm),hyX⟩
  have hzOff:z∈Sᶜ:=by
    simp only [S,mem_compl,mem_insert,not_or]
    exact ⟨fun he=>huNot (Or.inr he.symm),fun he=>hvNot (Or.inr he.symm),hzX⟩
  have hCutLower:R.degree y+R.degree z≤cutEdges R S:=by
    rw [hCut]
    exact CriticalAlmostPairNormalization.pair_degree_sum_le R Sᶜ y z hyOff hzOff hTop.ne
  have hRankU:=unselected_degree_le_selected_add_one G c hTop r u y hu huNot (Or.inl rfl)
  have hRankV:=unselected_degree_le_selected_add_one G c hTop r v z hv hvNot (Or.inr rfl)
  have hDef:=pair_deficit_le R S u v (mem_insert_self _ _) (mem_insert_of_mem (mem_insert_self _ _)) huv
  have hU:=R.degree_le_maxDegree u
  have hV:=R.degree_le_maxDegree v
  have hDrop:R.maxDegree=G.maxDegree-1:=by
    simpa only [R,SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
      ←Nat.card_eq_fintype_card] using r.residual_maxDegree
  apply (odd_internal_bound_iff_cut_deficit R R.maxDegree R.degree_le_maxDegree S hOdd).mpr
  change R.degree u≤R.degree y+1 at hRankU
  change R.degree v≤R.degree z+1 at hRankV
  omega

private theorem one_selected_nonoverfull (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) {x y z : V}
    (hTop : IsTopPair G c.setᶜ y z) (r : Round G c x y z)
    (u v : V) (hu : u∈c.setᶜ) (hv : v∈c.setᶜ) (huv : u≠v)
    (huSel : u=y ∨ u=z) (hvNot : ¬(v=y ∨ v=z)) :
    internalEdges (G\r.matching) (insert u (insert v c.set))≤
      (G\r.matching).maxDegree*((insert u (insert v c.set)).card/2) := by
  let R:=G\r.matching
  let S:=insert u (insert v c.set)
  have hOdd:Odd S.card:=extension_odd c.odd hu hv huv
  obtain ⟨q,hqSel,hqu⟩:∃q:V,(q=y ∨ q=z) ∧ q≠u:=by
    rcases huSel with he|he
    · exact ⟨z,Or.inr rfl,fun h=>hTop.ne (he.symm.trans h.symm)⟩
    · exact ⟨y,Or.inl rfl,fun h=>hTop.ne (h.trans he)⟩
  have hqY:q∈c.setᶜ:=by
    rcases hqSel with he|he
    · simpa only [he] using hTop.left_mem
    · simpa only [he] using hTop.right_mem
  have hqv:q≠v:=by
    intro he
    exact hvNot (he ▸ hqSel)
  have hqOff:q∈Sᶜ:=by
    simp only [S,mem_compl,mem_insert,not_or]
    exact ⟨hqu,hqv,mem_compl.mp hqY⟩
  have hCut:=cut_eq_complementary_degree_sum R S (complement_independent G c r u v)
  have hCutLower:R.degree q≤cutEdges R S:=by
    rw [hCut]
    exact single_le_sum (f:=fun w=>R.degree w) (fun _ _=>Nat.zero_le _) hqOff
  have hRank:=unselected_degree_le_selected_add_one G c hTop r v q hv hvNot hqSel
  have hDef:=pair_deficit_le R S u v (mem_insert_self _ _) (mem_insert_of_mem (mem_insert_self _ _)) huv
  have hU:=R.degree_le_maxDegree u
  have hV:=R.degree_le_maxDegree v
  have hNear:R.maxDegree≤cutEdges R S+deficitMass R R.maxDegree S+1:=by
    change R.degree v≤R.degree q+1 at hRank
    omega
  exact (odd_internal_bound_iff_cut_deficit R R.maxDegree R.degree_le_maxDegree S hOdd).mpr
    (odd_budget_of_one_below R S hOdd hNear)

/-- The complete published (0,2) case of Claim 4.5. The original graph
has no overfull set; the residual assertion for every pair is proved. -/
theorem pair_extension_nonoverfull (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) {x y z : V}
    (hx : x∈c.set) (hTop : IsTopPair G c.setᶜ y z) (r : Round G c x y z)
    (hD : 4≤G.maxDegree) (hNo : ¬G.HasOverfullSubgraph)
    (u v : V) (hu : u∈c.setᶜ) (hv : v∈c.setᶜ) (huv : u≠v) :
    internalEdges (G\r.matching) (insert u (insert v c.set))≤
      (G\r.matching).maxDegree*((insert u (insert v c.set)).card/2) := by
  by_cases huSel:u=y ∨ u=z
  · by_cases hvSel:v=y ∨ v=z
    · rcases huSel with huy|huz <;> rcases hvSel with hvy|hvz
      · exact (huv (huy.trans hvy.symm)).elim
      · subst u;subst v
        exact selected_pair_nonoverfull G c hx hTop.left_mem hTop.right_mem hTop.ne r hNo
      · subst u;subst v
        simpa only [Finset.insert_comm] using
          selected_pair_nonoverfull G c hx hTop.left_mem hTop.right_mem hTop.ne r hNo
      · exact (huv (huz.trans hvz.symm)).elim
    · exact one_selected_nonoverfull G c hTop r u v hu hv huv huSel hvSel
  · by_cases hvSel:v=y ∨ v=z
    · simpa only [Finset.insert_comm] using
        one_selected_nonoverfull G c hTop r v u hv hu huv.symm hvSel huSel
    · exact none_selected_nonoverfull G c hTop r hD u v hu hv huv huSel hvSel

/-- Claim 4.5 excludes any candidate odd set containing at least three
vertices of Y when the whole Y-degree sum is at most twice Delta. -/
theorem nonoverfull_of_three_in_small_total (H : SimpleGraph V) [DecidableRel H.Adj]
    (Y S : Finset V) (hTotal : (∑v∈Y,H.degree v)≤2*H.maxDegree)
    (hOdd : Odd S.card) (hThree : 3≤(S∩Y).card) :
    internalEdges H S≤H.maxDegree*(S.card/2) := by
  let A:=S∩Y
  have hId:=DegreeOrderedIndependentCut.deficit_add_degree_sum H A
  have hDef:deficitMass H H.maxDegree A≤deficitMass H H.maxDegree S:=by
    exact sum_le_sum_of_subset_of_nonneg (inter_subset_left)
      (fun _ _ _=>Nat.zero_le _) (f:=fun v=>H.maxDegree-H.degree v)
  have hSum:(∑v∈A,H.degree v)≤∑v∈Y,H.degree v:=
    sum_le_sum_of_subset_of_nonneg inter_subset_right (fun _ _ _=>Nat.zero_le _)
  have hSize:3*H.maxDegree≤H.maxDegree*A.card:=by
    have hh:=Nat.mul_le_mul_left H.maxDegree hThree
    nlinarith only [hh]
  apply (odd_internal_bound_iff_cut_deficit H H.maxDegree H.degree_le_maxDegree S hOdd).mpr
  omega

theorem three_complement_nonoverfull (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) {x y z : V} (r : Round G c x y z)
    (hy : y∈c.setᶜ) (hz : z∈c.setᶜ) (hyz : y≠z) (hB : B≤G.maxDegree)
    (S : Finset V) (hOdd : Odd S.card) (hThree : 3≤(S∩c.setᶜ).card) :
    internalEdges (G\r.matching) S≤(G\r.matching).maxDegree*(S.card/2) := by
  have hSum:(∑v∈c.setᶜ,(G\r.matching).degree v)+2=∑v∈c.setᶜ,G.degree v:=by
    simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      r.merged_degree_add_two hy hz hyz
  have hBudget:=c.budget
  have hDrop:(G\r.matching).maxDegree=G.maxDegree-1:=by
    simpa only [SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
      ←Nat.card_eq_fintype_card] using r.residual_maxDegree
  have hTotal:(∑v∈c.setᶜ,(G\r.matching).degree v)≤2*(G\r.matching).maxDegree:=by
    rw [hDrop]
    omega
  exact nonoverfull_of_three_in_small_total (G\r.matching) c.setᶜ S hTotal hOdd hThree

/-- Algorithm 2 cannot spoil the proved (0,2) case because its deletion
preserves the maximum degree. No global no-overfull premise on R is used. -/
theorem pair_extension_nonoverfull_after_cleanup (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    {B K : ℕ} (c : Certificate G B K) {x y z : V}
    (hx : x∈c.set) (hTop : IsTopPair G c.setᶜ y z) (r : Round G c x y z)
    (hD : 4≤G.maxDegree) (hNo : ¬G.HasOverfullSubgraph)
    (hLe : H≤G\r.matching) (hMax : H.maxDegree=(G\r.matching).maxDegree)
    (u v : V) (hu : u∈c.setᶜ) (hv : v∈c.setᶜ) (huv : u≠v) :
    internalEdges H (insert u (insert v c.set))≤H.maxDegree*((insert u (insert v c.set)).card/2) := by
  rw [hMax]
  exact (internal_edges_le_of_le (G\r.matching) H hLe _).trans
    (pair_extension_nonoverfull G c hx hTop r hD hNo u v hu hv huv)

/-- All odd supersets of the original core are now covered: zero extra
vertices uses the core bound, two uses the published (0,2) case, and at
least three uses the complementary degree budget. -/
theorem core_supersets_nonoverfull (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) {x y z : V}
    (hx : x∈c.set) (hLarge : G.degree x<(∑w∈c.setᶜ,G.degree w))
    (hxD : G.degree x<G.maxDegree) (hTop : IsTopPair G c.setᶜ y z) (r : Round G c x y z)
    (hD : 4≤G.maxDegree) (hB : B≤G.maxDegree) (hNo : ¬G.HasOverfullSubgraph)
    (S : Finset V) (hOdd : Odd S.card) (hCore : c.set⊆S) :
    internalEdges (G\r.matching) S≤(G\r.matching).maxDegree*(S.card/2) := by
  let A:=S∩c.setᶜ
  have hSplit:S=c.set∪A:=by
    ext v
    simp only [A,mem_union,mem_inter,mem_compl]
    constructor
    · intro hv
      by_cases hvX:v∈c.set
      · exact Or.inl hvX
      · exact Or.inr ⟨hv,hvX⟩
    · rintro (hv|⟨hv,_⟩)
      · exact hCore hv
      · exact hv
  have hDis:Disjoint c.set A:=Finset.disjoint_left.mpr (by
    intro v hv ha
    exact (mem_compl.mp (mem_inter.mp ha).2) hv)
  have hCard:S.card=c.set.card+A.card:=by rw [hSplit,card_union_of_disjoint hDis]
  have hEven:Even A.card:=by
    obtain ⟨k,hk⟩:=c.odd
    obtain ⟨l,hl⟩:=hOdd
    exact ⟨l-k,by omega⟩
  by_cases hZero:A.card=0
  · have hA:A=∅:=card_eq_zero.mp hZero
    have hS:S=c.set:=by simpa only [hA,union_empty] using hSplit
    rw [hS]
    have hBase:=r.core_not_overfull hx hTop.left_mem hTop.right_mem hTop.ne hxD hLarge
    have transport (d₁ d₂ : DecidableRel (G\r.matching).Adj) :
        (@internalEdges V _ _ (G\r.matching) d₁ c.set≤
          @SimpleGraph.maxDegree V (G\r.matching) _ d₁*(c.set.card/2)) →
        (@internalEdges V _ _ (G\r.matching) d₂ c.set≤
          @SimpleGraph.maxDegree V (G\r.matching) _ d₂*(c.set.card/2)):=by
      cases Subsingleton.elim d₁ d₂
      exact id
    exact transport _ _ hBase
  · by_cases hTwo:A.card=2
    · obtain ⟨u,v,huv,hA⟩:=card_eq_two.mp hTwo
      have hu:u∈A:=by rw [hA];simp
      have hv:v∈A:=by rw [hA];simp
      have huY:u∈c.setᶜ:=(mem_inter.mp hu).2
      have hvY:v∈c.setᶜ:=(mem_inter.mp hv).2
      have hS:S=insert u (insert v c.set):=by
        simpa only [hA,union_insert,union_singleton] using hSplit
      rw [hS]
      exact pair_extension_nonoverfull G c hx hTop r hD hNo u v huY hvY huv
    · have hThree:3≤A.card:=by obtain ⟨k,hk⟩:=hEven;omega
      exact three_complement_nonoverfull G c r hTop.left_mem hTop.right_mem hTop.ne hB S hOdd hThree

/-- A constructed top-pair round and its actual Algorithm 2 cleanup.
Every odd core superset, and every set with at least three complementary
vertices, is proved non-overfull in the SAME cleaned graph. -/
theorem exists_top_round_cleaned_with_safe_sets (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) {B K : ℕ} (c : Certificate G B K)
    (x : V) (hx : x∈c.set) (hLarge : G.degree x<(∑w∈c.setᶜ,G.degree w))
    (hxD : G.degree x<G.maxDegree) (hD : 4≤G.maxDegree) (hB : B≤G.maxDegree)
    (hNo : ¬G.HasOverfullSubgraph)
    (hMargin : Fintype.card V+2*B+c.setᶜ.card+3≤2*G.maxDegree) :
    ∃y z,IsTopPair G c.setᶜ y z ∧ ∃r : Round G c x y z,∃H : SimpleGraph V,
      MaximumNeighbourCleanup.DeletionRun c.setᶜ (G\r.matching) H ∧
      H≤G\r.matching ∧ H.maxDegree=G.maxDegree-1 ∧ ¬H.EdgeColorable H.maxDegree ∧
      H.induce (c.set:Set V)=(G\r.matching).induce (c.set:Set V) ∧
      (∀w∈c.setᶜ,H.degree w<H.maxDegree) ∧
      (∀w∈c.setᶜ,∀v,H.Adj w v → PrunedCore.neighboursIn H c.setᶜ v<H.degree w) ∧
      (∀w∈c.setᶜ,∀v,H.Adj w v → H.maxDegree+2≤H.degree w+H.degree v) ∧
      ∀S : Finset V,Odd S.card → (c.set⊆S ∨ 3≤(S∩c.setᶜ).card) →
        internalEdges H S≤H.maxDegree*(S.card/2) := by
  classical
  obtain ⟨y,z,hTop,⟨r⟩⟩:=exists_top_round G hc c x hx hLarge hxD hMargin
  obtain ⟨H,hRun,hLe,hMax,hNC,hCore,hNonmax,hHall,hVal⟩:=
    exists_post_round_cleanup G hc c hx hLarge hD hTop r
  refine ⟨y,z,hTop,r,H,hRun,hLe,hMax,hNC,hCore,hNonmax,hHall,hVal,?_⟩
  intro S hOdd hCase
  have hRMax:(G\r.matching).maxDegree=G.maxDegree-1:=by
    simpa only [SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
      ←Nat.card_eq_fintype_card] using r.residual_maxDegree
  have hSame:H.maxDegree=(G\r.matching).maxDegree:=hMax.trans hRMax.symm
  rw [hSame]
  apply (internal_edges_le_of_le (G\r.matching) H hLe S).trans
  rcases hCase with hCoreIn|hThree
  · exact core_supersets_nonoverfull G c hx hLarge hxD hTop r hD hB hNo S hOdd hCoreIn
  · exact three_complement_nonoverfull G c r hTop.left_mem hTop.right_mem hTop.ne hB S hOdd hThree

/-- If an overfull set still exists after the proved cases, its actual
odd witness omits a core vertex and contains at most two Y vertices.
This is localization of the remaining obligation, not its exclusion. -/
theorem remaining_overfull_configuration (H : SimpleGraph V) [DecidableRel H.Adj]
    (X : Finset V)
    (hSafe : ∀S : Finset V,Odd S.card → (X⊆S ∨ 3≤(S∩Xᶜ).card) →
      internalEdges H S≤H.maxDegree*(S.card/2))
    (hOF : H.HasOverfullSubgraph) :
    ∃S : Finset V,Odd S.card ∧ H.maxDegree*(S.card/2) < internalEdges H S ∧
      ¬X⊆S ∧ (S∩Xᶜ).card≤2 ∧
      cutEdges H S+deficitMass H H.maxDegree S+2≤H.maxDegree := by
  obtain ⟨S,hS⟩:=hOF
  change H.maxDegree*(S.card/2) < internalEdges H S at hS
  have hOdd:Odd S.card:=by
    by_contra hNot
    have heven:=Nat.not_odd_iff_even.mp hNot
    exact (not_lt_of_ge (even_internal_bound H H.maxDegree H.degree_le_maxDegree S heven)) hS
  have hCore:¬X⊆S:=fun hs=>(not_lt_of_ge (hSafe S hOdd (Or.inl hs))) hS
  have hFew:(S∩Xᶜ).card≤2:=by
    by_contra hn
    exact (not_lt_of_ge (hSafe S hOdd (Or.inr (by omega)))) hS
  have hId:=internal_cut_deficit_identity H H.maxDegree H.degree_le_maxDegree S
  obtain ⟨m,hm⟩:=hOdd
  have hHalf:S.card/2=m:=by omega
  have hProduct:H.maxDegree*S.card=2*(H.maxDegree*m)+H.maxDegree:=by rw [hm];ring
  rw [hProduct] at hId
  refine ⟨S,⟨m,hm⟩,hS,hCore,hFew,?_⟩
  rw [hHalf] at hS
  omega

end OverfullWork.PaperPairExtensionPreservation
