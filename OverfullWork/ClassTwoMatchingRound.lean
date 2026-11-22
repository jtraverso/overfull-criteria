module

public import OverfullWork.ClassTwoHallMatching

@[expose] public section


/-! # A matching-removal round with a class-two source

The source need not be critical. Actual Hall inequalities and positive
selected degrees construct the cross edges, a finite high-core margin
constructs the perfect matching, and colouring extension preserves the
class-two obstruction. No residual no-overfullness is assumed or claimed.
-/
namespace OverfullWork.ClassTwoMatchingRound
open SimpleGraph Finset OddCutDeficit PrunedCore LargeCentreMatchingStep
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

structure CoreRound (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (x y z : V) where
  matching : SimpleGraph V
  le_original : matching≤G
  degree_le_one : ∀v,matching.degree v≤1
  core_degrees : ∀v∈X,matching.degree v=if v=x then 0 else 1
  complementary_degrees : ∀v∈Xᶜ,matching.degree v=if v=y ∨ v=z then 1 else 0
  residual_maxDegree : (G\matching).maxDegree=G.maxDegree-1
  residual_uncolourable : ¬(G\matching).EdgeColorable (G\matching).maxDegree

/-- Glue the two selected cross edges to a matching of the remaining core. -/
theorem exists_round_of_core_matchings (G : SimpleGraph V) [DecidableRel G.Adj]
    (hNC : ¬G.EdgeColorable G.maxDegree) (X : Finset V) (hOdd : Odd X.card)
    (hInd : G.IsIndepSet (↑(Xᶜ):Set V))
    (hHall : ∀w∈Xᶜ,∀v,G.Adj w v → neighboursIn G Xᶜ v<G.degree w)
    (hNonmax : ∀w∈Xᶜ,G.degree w<G.maxDegree)
    (x : V) (hx : x∈X) (hxD : G.degree x<G.maxDegree)
    (hMatchCore : ∀ a b, a∈X → b∈X → a≠x → b≠x → a≠b →
      let W := ((X.erase x).erase a).erase b
      W.card+3=X.card → Even W.card → ∃ N,Plantholt.IsMatchingOn G N W)
    (y z : V) (hy : y∈Xᶜ) (hz : z∈Xᶜ) (hyz : y≠z)
    (hyPos : 0<G.degree y) (hzPos : 0<G.degree z) :
    Nonempty (CoreRound G X x y z) := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun a b=>Classical.propDecidable (G.Adj a b)))
  obtain ⟨a,b,ha,hb,hax,hbx,hab,hya,hzb⟩:=
    ClassTwoHallMatching.exists_pair_edges G Xᶜ hInd hHall x y z
      (by simpa only [mem_compl,not_not] using hx) hy hz hyz hyPos hzPos
  have haX:a∈X:=by simpa only [compl_compl] using ha
  have hbX:b∈X:=by simpa only [compl_compl] using hb
  let W:=((X.erase x).erase a).erase b
  have ha':a∈X.erase x:=mem_erase.mpr ⟨hax,haX⟩
  have hb':b∈(X.erase x).erase a:=mem_erase.mpr ⟨hab.symm,mem_erase.mpr ⟨hbx,hbX⟩⟩
  have hCard:W.card+3=X.card:=by
    dsimp only [W]
    rw [card_erase_of_mem hb',card_erase_of_mem ha',card_erase_of_mem hx]
    have hThree:3≤X.card:=by
      have hp:0<((X.erase x).erase a).card:=card_pos.mpr ⟨b,hb'⟩
      rw [card_erase_of_mem ha',card_erase_of_mem hx] at hp
      omega
    omega
  have hEven:Even W.card:=by
    obtain ⟨t,ht⟩:=hOdd
    exact ⟨t-1,by omega⟩
  obtain ⟨N,hN⟩ := hMatchCore a b haX hbX hax hbx hab hCard hEven
  have hyX:y∉X:=mem_compl.mp hy
  have hzX:z∉X:=mem_compl.mp hz
  have hyW:y∉W:=by simp only [W,mem_erase];tauto
  have haW:a∉W:=by simp only [W,mem_erase];tauto
  have hbW:b∉W:=by simp only [W,mem_erase];tauto
  have hzW:z∉W:=by simp only [W,mem_erase];tauto
  have hzy:z≠y:=hyz.symm
  have hza:z≠a:=fun he=>hzX (he.symm ▸ haX)
  have hby:b≠y:=fun he=>hyX (he ▸ hbX)
  have hM₁:=matching_on_add_edge G N W hN y a hyW haW hya
  have hM₂:=matching_on_add_edge G (N⊔edge y a) (insert y (insert a W)) hM₁ z b
    (by simp only [mem_insert];tauto) (by simp only [mem_insert];tauto) hzb
  let F:=(N⊔edge y a)⊔edge z b
  let S:=(X.erase x)∪{y,z}
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
  have hCore:∀v∈X,F.degree v=if v=x then 0 else 1:=by
    intro v hv
    rw [hDeg]
    have hvy:v≠y:=fun he=>hyX (he ▸ hv)
    have hvz:v≠z:=fun he=>hzX (he ▸ hv)
    simp only [S,mem_union,mem_erase,mem_insert,mem_singleton]
    split_ifs <;>tauto
  have hY:∀v∈Xᶜ,F.degree v=if v=y ∨ v=z then 1 else 0:=by
    intro v hv
    rw [hDeg]
    have hvX:v∉X:=mem_compl.mp hv
    simp only [S,mem_union,mem_erase,mem_insert,mem_singleton]
    simp only [hvX,and_false,false_or]
  have hCover:∀v,G.degree v=G.maxDegree → ∃!w,F.Adj v w:=by
    intro v hv
    have hvX:v∈X:=by
      by_contra hn
      have hh:=hNonmax v (mem_compl.mpr hn)
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
    intro hCol
    apply hNC
    apply MaximumMatching.colourable_of_matching_residue G F hD hOn.1 hMatch
    simpa only [hMax] using hCol
  exact ⟨⟨F,hOn.1,hOne,hCore,hY,
    hMax,hUncol⟩⟩

/-- Construct every edge from the restored local invariants. -/
theorem exists_round (G : SimpleGraph V) [DecidableRel G.Adj]
    (hNC : ¬G.EdgeColorable G.maxDegree) (X : Finset V) (hOdd : Odd X.card)
    (hInd : G.IsIndepSet (↑(Xᶜ):Set V))
    (hHall : ∀w∈Xᶜ,∀v,G.Adj w v → neighboursIn G Xᶜ v<G.degree w)
    (hNonmax : ∀w∈Xᶜ,G.degree w<G.maxDegree)
    (x : V) (hx : x∈X) (hxD : G.degree x<G.maxDegree) (b : ℕ)
    (hHigh : ∀v∈X,v≠x → G.maxDegree≤G.degree v+b)
    (hMargin : Fintype.card V+2*b+Xᶜ.card+3≤2*G.maxDegree)
    (y z : V) (hy : y∈Xᶜ) (hz : z∈Xᶜ) (hyz : y≠z)
    (hyPos : 0<G.degree y) (hzPos : 0<G.degree z) :
    Nonempty (CoreRound G X x y z) := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun a b=>Classical.propDecidable (G.Adj a b)))
  apply exists_round_of_core_matchings G hNC X hOdd hInd hHall hNonmax x hx hxD _ y z hy hz hyz hyPos hzPos
  intro a b _ _ _ _ _ W hCard hEven
  have hComp:Wᶜ.card=Xᶜ.card+3:=by
    have h₁:=card_add_card_compl W
    have h₂:=card_add_card_compl X
    omega
  have hDense:∀v∈W,W.card≤2*(Plantholt.nbIn G W v).card:=by
    intro v hv
    have hvX:v∈X:=(mem_erase.mp (mem_erase.mp (mem_erase.mp hv).2).2).2
    have hvx:v≠x:=(mem_erase.mp (mem_erase.mp (mem_erase.mp hv).2).2).1
    have hLower:=hHigh v hvX hvx
    have hSub:G.neighborFinset v⊆Plantholt.nbIn G W v∪Wᶜ:=by
      intro w hw
      by_cases hwW:w∈W
      · exact mem_union_left _ (mem_filter.mpr ⟨hw,hwW⟩)
      · exact mem_union_right _ (mem_compl.mpr hwW)
    have hCount:=(card_le_card hSub).trans (card_union_le _ _)
    rw [card_neighborFinset_eq_degree,hComp] at hCount
    have hTotal:=card_add_card_compl W
    omega
  exact Plantholt.exists_matchingOn G hEven hDense

def CoreRound.ofRound {G : SimpleGraph V} [DecidableRel G.Adj]
    {B K : ℕ} {c : NormalizedAlmostStoppingRun.Certificate G B K} {x y z : V}
    (r : LargeCentreMatchingStep.Round G c x y z) : CoreRound G c.set x y z :=
  ⟨r.matching,r.le_original,r.degree_le_one,r.core_degrees,r.complementary_degrees,
    r.residual_maxDegree,r.residual_uncolourable⟩

end OverfullWork.ClassTwoMatchingRound
