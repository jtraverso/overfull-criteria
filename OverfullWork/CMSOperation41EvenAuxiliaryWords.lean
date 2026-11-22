module

public import OverfullWork.CMSOperation41MatchingArms

@[expose] public section


/-! Every prescribed pair in the even form of Case S2.1 has a
disjoint replacement word in the original graph, with one marked gap. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph PaperLowSkeleton LowSkeletonPreparation
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 1500000 in
theorem exists_even_matching_auxiliary_words {G M : SimpleGraph V} [DecidableRel M.Adj]
    {U W Z : Finset V} (hWU : W ⊆ U) (hM : IsSkeleton G M W) (hMatch : OneFactor.IsMatchingGraph M)
    (P : LowSkeletonProjection.Projection G (outerLeaves M W) U Z) :
    ∃ (f : ℕ) (endpoint : (Fin f × Bool) ↪ ↥(Uᶜ : Finset V)) (low : (Fin f × Bool) ↪ V)
      (word : Fin f → List V),
      0 < f ∧ 2*f = (outerLeaves M W).card ∧
      (∀ i,low i ∈ W) ∧
      (∀ v,v ∈ Set.range endpoint ↔ ∃ a : outerLeaves M W,P.representative a = v) ∧
      (∀ i,(word i).Nodup ∧
        (word i).head? = some (endpoint (i,false)).val ∧
        (word i).getLast? = some (endpoint (i,true)).val ∧
        (word i).IsChain (fun u v => G.Adj u v ∨ (u=low (i,false) ∧ v=low (i,true))) ∧
        List.IsInfix [low (i,false),low (i,true)] (word i)) ∧
      (∀ i v,v ∈ word i → (v ∉ U ↔ v = (endpoint (i,false)).val ∨ v = (endpoint (i,true)).val)) ∧
      (∀ i j,i ≠ j → List.Disjoint (word i) (word j)) ∧
      (∀ a : outerLeaves M W,∃ w ∈ W,M.Adj w a.val ∧
        ∃ i,List.IsInfix [w,a.val] (word i) ∨ List.IsInfix [a.val,w] (word i)) ∧
      (∀ i v,v ∈ word i → v ∈ U → v ∉ W → v ∈ outerLeaves M W) := by
  let A := outerLeaves M W
  obtain ⟨f,hf⟩ := hM.outer_even
  have hCard : Fintype.card (Fin f × Bool) = Fintype.card ↥A := by
    rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Fintype.card_coe]
    change f*2 = (outerLeaves M W).card
    omega
  let coord := Fintype.equivOfCardEq hCard
  obtain ⟨leaf,arm,hLeaf,hArm,hOutside,hDis,_,hShape,hLeafMember⟩ :=
    matching_skeleton_arms hWU hM hMatch P
  let endpoint : (Fin f × Bool) ↪ ↥(Uᶜ : Finset V) :=
    coord.toEmbedding.trans ⟨P.representative,P.injective⟩
  let low := coord.toEmbedding.trans leaf
  let word (i : Fin f) := (arm (coord (i,false))).reverse ++ arm (coord (i,true))
  have hF := hM.outer_two_le
  refine ⟨f,endpoint,low,word,by omega,by omega,fun i => (hLeaf (coord i)).1,?_,?_,?_,?_,?_,?_⟩
  · intro v
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨coord i,rfl⟩
    · rintro ⟨a,rfl⟩
      refine ⟨coord.symm a,?_⟩
      change P.representative (coord (coord.symm a)) = P.representative a
      rw [Equiv.apply_symm_apply]
  · intro i
    let a := coord (i,false)
    let b := coord (i,true)
    have hNe : a ≠ b := by intro h; cases congrArg Prod.snd (coord.injective h)
    have hJ := join_projected_arms G (arm a) (arm b) (leaf a) (leaf b)
      (hArm a).2.2.1 (hArm b).2.2.1 (hArm a).1 (hArm b).1
      (hDis a b hNe) (hArm a).2.1 (hArm b).2.1
    exact ⟨hJ.1,hJ.2.1.trans (hArm a).2.2.2,hJ.2.2.1.trans (hArm b).2.2.2,hJ.2.2.2⟩
  · intro i v hv
    have hMem : v ∈ arm (coord (i,false)) ∨ v ∈ arm (coord (i,true)) := by
      simpa only [word,List.mem_append,List.mem_reverse] using hv
    constructor
    · intro h
      rcases hMem with hMem|hMem
      · exact Or.inl ((hOutside _ _ hMem).mp h)
      · exact Or.inr ((hOutside _ _ hMem).mp h)
    · rintro (rfl|rfl)
      · exact mem_compl.mp (endpoint (i,false)).property
      · exact mem_compl.mp (endpoint (i,true)).property
  · intro i j hij v hv hv'
    have hPair (b c : Bool) : coord (i,b) ≠ coord (j,c) :=
      fun h => hij (congrArg Prod.fst (coord.injective h))
    simp only [word,List.mem_append,List.mem_reverse] at hv hv'
    rcases hv with hi|hi <;> rcases hv' with hj|hj
    · exact hDis _ _ (hPair false false) hi hj
    · exact hDis _ _ (hPair false true) hi hj
    · exact hDis _ _ (hPair true false) hi hj
    · exact hDis _ _ (hPair true true) hi hj
  · intro a
    obtain ⟨⟨i,side⟩,hCoord⟩ := coord.surjective a
    let tail := if a.val ∈ U then [(P.representative a).val] else []
    have hArmEq : arm a = leaf a :: a.val :: tail := hShape a
    refine ⟨leaf a,(hLeaf a).1,(hLeaf a).2,i,?_⟩
    cases side
    · right
      rw [show word i = (arm a).reverse ++ arm (coord (i,true)) by simp only [word,hCoord]]
      exact ⟨tail.reverse,arm (coord (i,true)),by simp [hArmEq,List.reverse_cons,List.append_assoc]⟩
    · left
      rw [show word i = (arm (coord (i,false))).reverse ++ arm a by simp only [word,hCoord]]
      exact ⟨(arm (coord (i,false))).reverse,tail,by simp [hArmEq,List.append_assoc]⟩
  · intro i v hv hu hw
    simp only [word,List.mem_append,List.mem_reverse] at hv
    rcases hv with h | h
    · exact (hLeafMember _ v h hu hw).symm ▸ (coord (i,false)).property
    · exact (hLeafMember _ v h hu hw).symm ▸ (coord (i,true)).property

end OverfullWork.CMSTrimmingRound
