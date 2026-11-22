module

public import OverfullWork.MaximumCoreTripleChoice

@[expose] public section


/-! An actual degree-lowering round covering an all-maximum odd core.

The usual two-cross-edge round leaves one core vertex uncovered. Here
three disjoint cross edges and a matching on the remaining even core
cover every maximum vertex. No residual no-overfullness is postulated.
-/
namespace OverfullWork.MaximumCoreThreeCrossRound
open SimpleGraph Finset OddCutDeficit NormalizedAlmostStoppingRun
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 24000000

structure Round (G : SimpleGraph V) [DecidableRel G.Adj] (X U : Finset V) where
  matching : SimpleGraph V
  le_original : matching ≤ G
  degree_le_one : ∀ v, matching.degree v ≤ 1
  core_degrees : ∀ v ∈ X, matching.degree v=1
  complementary_degrees : ∀ v ∈ Xᶜ, matching.degree v=if v ∈ U then 1 else 0
  residual_maxDegree : (G\matching).maxDegree=G.maxDegree-1
  residual_uncolourable : ¬(G\matching).EdgeColorable (G\matching).maxDegree

theorem exists_round_of_core_matchings (G : SimpleGraph V) [DecidableRel G.Adj]
    (hNC : ¬G.EdgeColorable G.maxDegree) (X U : Finset V) (hOdd : Odd X.card)
    (hInd : G.IsIndepSet (↑(Xᶜ):Set V))
    (hHall : ∀ w ∈ Xᶜ, ∀ v, G.Adj w v → PrunedCore.neighboursIn G Xᶜ v < G.degree w)
    (hNonmax : ∀ w ∈ Xᶜ, G.degree w < G.maxDegree)
    (hU : U ⊆ Xᶜ) (hThree : U.card=3) (hPos : ∀ u ∈ U, 0 < G.degree u)
    (hMatching : ∀ a b d,a ∈ X → b ∈ X → d ∈ X → a ≠ b → a ≠ d → b ≠ d →
      let W := ((X.erase a).erase b).erase d
      W.card+3 = X.card → Even W.card → ∃ N,Plantholt.IsMatchingOn G N W) :
    Nonempty (Round G X U) := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun a b => Classical.propDecidable (G.Adj a b)))
  obtain ⟨y,z,t,hyz,hyt,hzt,hUeq⟩ := card_eq_three.mp hThree
  have hyU : y ∈ U := by rw [hUeq];simp
  have hzU : z ∈ U := by rw [hUeq];simp
  have htU : t ∈ U := by rw [hUeq];simp
  have hXpos : X.Nonempty := by
    apply card_pos.mp
    obtain ⟨m,hm⟩ := hOdd
    omega
  obtain ⟨x,hx⟩ := hXpos
  obtain ⟨a,b,d,ha,hb,hd,hab,had,hbd,hya,hzb,htd⟩ :=
    MaximumCoreTripleChoice.exists_triple_edges G Xᶜ hInd hHall x (by simpa using hx)
      y z t (hU hyU) (hU hzU) (hU htU) hyz hyt hzt
      ⟨hPos y hyU,hPos z hzU,hPos t htU⟩
  simp only [compl_compl] at ha hb hd
  let W := ((X.erase a).erase b).erase d
  have hb' : b ∈ X.erase a := mem_erase.mpr ⟨hab.symm,hb⟩
  have hd' : d ∈ (X.erase a).erase b := mem_erase.mpr ⟨hbd.symm,mem_erase.mpr ⟨had.symm,hd⟩⟩
  have hCard : W.card+3=X.card := by
    have hCount : 3 ≤ X.card := by
      have hSub : ({a,b,d}:Finset V) ⊆ X := by simp only [insert_subset_iff,singleton_subset_iff];exact ⟨ha,hb,hd⟩
      have hc := card_le_card hSub
      simpa [hab,had,hbd] using hc
    dsimp only [W]
    rw [card_erase_of_mem hd',card_erase_of_mem hb',card_erase_of_mem ha]
    omega
  have hEven : Even W.card := by
    obtain ⟨m,hm⟩ := hOdd
    exact ⟨m-1,by omega⟩
  obtain ⟨N,hN⟩ := hMatching a b d ha hb hd hab had hbd hCard hEven
  have hyX : y ∉ X := mem_compl.mp (hU hyU)
  have hzX : z ∉ X := mem_compl.mp (hU hzU)
  have htX : t ∉ X := mem_compl.mp (hU htU)
  have hM₁ := LargeCentreMatchingStep.matching_on_add_edge G N W hN y a
    (by simp only [W,mem_erase];tauto) (by simp [W]) hya
  have hM₂ := LargeCentreMatchingStep.matching_on_add_edge G (N⊔edge y a)
    (insert y (insert a W)) hM₁ z b
    (by simp only [mem_insert,W,mem_erase];aesop)
    (by simp only [mem_insert,W,mem_erase];aesop) hzb
  have hM₃ := LargeCentreMatchingStep.matching_on_add_edge G ((N⊔edge y a)⊔edge z b)
    (insert z (insert b (insert y (insert a W)))) hM₂ t d
    (by simp only [mem_insert,W,mem_erase];aesop)
    (by simp only [mem_insert,W,mem_erase];aesop) htd
  let F := ((N⊔edge y a)⊔edge z b)⊔edge t d
  have hSet : insert t (insert d (insert z (insert b (insert y (insert a W)))))=X∪U := by
    ext v
    simp only [W,hUeq,mem_insert,mem_union,mem_erase,mem_singleton]
    by_cases hva : v=a <;> by_cases hvb : v=b <;> by_cases hvd : v=d <;> aesop
  have hOn : Plantholt.IsMatchingOn G F (X∪U) := by simpa only [hSet] using hM₃
  have hDeg : ∀ v, F.degree v=if v ∈ X∪U then 1 else 0 := by
    intro v
    split_ifs with hv
    · exact hOn.2.1 v hv
    · exact hOn.2.2 v hv
  have hOne : ∀ v, F.degree v ≤ 1 := by intro v;rw [hDeg];split_ifs <;> omega
  have hCoreF : ∀ v ∈ X, F.degree v=1 := by intro v hv;rw [hDeg,if_pos (mem_union_left _ hv)]
  have hYF : ∀ v ∈ Xᶜ, F.degree v=if v ∈ U then 1 else 0 := by
    intro v hv
    rw [hDeg]
    simp only [mem_union,mem_compl.mp hv,false_or]
  have hCover : ∀ v, G.degree v=G.maxDegree → ∃! w, F.Adj v w := by
    intro v hv
    have hvX : v ∈ X := by
      by_contra hh
      have hd := hNonmax v (mem_compl.mpr hh)
      omega
    exact degree_eq_one_iff_existsUnique_adj.mp (hCoreF v hvX)
  have hD : 0 < G.maxDegree := by have hh := hPos y hyU;have hd := G.degree_le_maxDegree y;omega
  have hMax : (G\F).maxDegree=G.maxDegree-1 := by
    simpa only [SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      MaximumMatching.maxDegree_sdiff_of_matching_cover G F hD hOn.1 hCover
  have hMatching : OneFactor.IsMatchingGraph F := by
    intro v u w hvu hvw
    have hc : (F.neighborFinset v).card ≤ 1 := by simpa only [card_neighborFinset_eq_degree] using hOne v
    exact card_le_one.mp hc u ((mem_neighborFinset _ _ _).mpr hvu) w ((mem_neighborFinset _ _ _).mpr hvw)
  have hNCF : ¬(G\F).EdgeColorable (G\F).maxDegree := by
    intro hCol
    rw [hMax] at hCol
    exact hNC (MaximumMatching.colourable_of_matching_residue G F hD hOn.1 hMatching hCol)
  exact ⟨⟨F,hOn.1,hOne,hCoreF,hYF,hMax,hNCF⟩⟩

theorem exists_round (G : SimpleGraph V) [DecidableRel G.Adj]
    (hNC : ¬G.EdgeColorable G.maxDegree) (X U : Finset V) (hOdd : Odd X.card)
    (hCore : ∀ v ∈ X, G.degree v=G.maxDegree)
    (hInd : G.IsIndepSet (↑(Xᶜ):Set V))
    (hHall : ∀ w ∈ Xᶜ, ∀ v, G.Adj w v → PrunedCore.neighboursIn G Xᶜ v < G.degree w)
    (hNonmax : ∀ w ∈ Xᶜ, G.degree w < G.maxDegree)
    (hU : U ⊆ Xᶜ) (hThree : U.card=3) (hPos : ∀ u ∈ U, 0 < G.degree u)
    (hMargin : Fintype.card V+Xᶜ.card+3 ≤ 2*G.maxDegree) :
    Nonempty (Round G X U) := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun a b => Classical.propDecidable (G.Adj a b)))
  apply exists_round_of_core_matchings G hNC X U hOdd hInd hHall hNonmax hU hThree hPos
  intro a b d ha hb hd hab had hbd W hCard hEven
  have hComp : Wᶜ.card=Xᶜ.card+3 := by
    have h₁ := card_add_card_compl W
    have h₂ := card_add_card_compl X
    omega
  have hDense : ∀ v ∈ W, W.card ≤ 2*(Plantholt.nbIn G W v).card := by
    intro v hv
    have hvX : v ∈ X := (mem_erase.mp (mem_erase.mp (mem_erase.mp hv).2).2).2
    have hSub : G.neighborFinset v ⊆ Plantholt.nbIn G W v ∪ Wᶜ := by
      intro w hw
      by_cases hwW : w ∈ W
      · exact mem_union_left _ (mem_filter.mpr ⟨hw,hwW⟩)
      · exact mem_union_right _ (mem_compl.mpr hwW)
    have hCount := (card_le_card hSub).trans (card_union_le _ _)
    rw [card_neighborFinset_eq_degree,hCore v hvX,hComp] at hCount
    have hTotal := card_add_card_compl W
    omega
  exact Plantholt.exists_matchingOn G hEven hDense

end OverfullWork.MaximumCoreThreeCrossRound
