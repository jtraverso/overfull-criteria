module

public import OverfullWork.CMSOperation41FreshOddSkeleton
public import OverfullWork.CMSOperation41MatchingArms
public import OverfullWork.PairedEndpointEnumeration

@[expose] public section


/-! Replacement words for the odd Case S2.1. The two outside leaves
of the two-edge component share a single auxiliary pair. Every other
pair has one gap between its two low leaves. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph PaperLowSkeleton LowSkeletonPreparation
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem paired_endpoints_with_one_special_pair (A : Finset V)
    (hEven : Even A.card) (hFour : 4 ≤ A.card) (x y : A) (hxy : x ≠ y) :
    ∃ (f : ℕ) (e : Fin f × Bool ≃ A) (k : Fin f),
      2 ≤ f ∧ 2*f = A.card ∧ e (k,false) = x ∧ e (k,true) = y := by
  obtain ⟨f,hf,hCard,⟨e⟩⟩ := PairedEndpointEnumeration.exists_pairing A hEven (by omega)
  let k : Fin f := ⟨0,by omega⟩
  let p (j : Bool) : A := e (k,j)
  let q (j : Bool) : A := if j then y else x
  have hp : Function.Injective p := fun _ _ h => congrArg Prod.snd (e.injective h)
  have hq : Function.Injective q := by
    apply Bool.injective_iff.mpr
    simpa [q] using hxy
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair p q hp hq
  exact ⟨f,e.trans σ,k,by omega,by omega,by simpa [p,q] using hσ false,by simpa [p,q] using hσ true⟩

theorem join_projected_arms_at_common_start (G : SimpleGraph V) (A B : List V) (x : V)
    (hHeadA : A.head? = some x) (hHeadB : B.head? = some x) (hTail : B.tail ≠ [])
    (hSimpleA : A.Nodup) (hSimpleB : B.Nodup)
    (hInter : ∀ v,v ∈ A → v ∈ B → v = x)
    (hChainA : A.IsChain G.Adj) (hChainB : B.IsChain G.Adj) :
    let T := A.reverse ++ B.tail
    T.Nodup ∧ T.head? = A.getLast? ∧ T.getLast? = B.getLast? ∧ T.IsChain G.Adj := by
  obtain ⟨B',rfl⟩ := List.head?_eq_some_iff.mp hHeadB
  have hA : A.reverse ≠ [] := by
    intro h
    have he := List.reverse_eq_nil_iff.mp h
    simp [he] at hHeadA
  have hB : B' ≠ [] := hTail
  change (A.reverse ++ B').Nodup ∧ (A.reverse ++ B').head? = A.getLast? ∧
    (A.reverse ++ B').getLast? = (x::B').getLast? ∧ (A.reverse ++ B').IsChain G.Adj
  refine ⟨?_,?_,?_,?_⟩
  · apply List.nodup_append.mpr
    refine ⟨List.nodup_reverse.mpr hSimpleA,(List.nodup_cons.mp hSimpleB).2,?_⟩
    intro u hu v hv he
    subst v
    have h := hInter u (List.mem_reverse.mp hu) (List.mem_cons_of_mem _ hv)
    exact (List.nodup_cons.mp hSimpleB).1 (h ▸ hv)
  · rw [List.head?_append_of_ne_nil _ hA,List.head?_reverse]
  · rw [List.getLast?_append_of_ne_nil _ hB,List.getLast?_cons_of_ne_nil hB]
  · have hReverse : A.reverse.IsChain G.Adj :=
      List.isChain_reverse.mpr (hChainA.imp (fun _ _ h => h.symm))
    apply hReverse.append hChainB.tail
    intro u hu v hv
    rw [List.getLast?_reverse,hHeadA] at hu
    have hux := (Option.mem_some_iff.mp hu).symm
    rw [hux]
    exact hChainB.rel_head? hv

private theorem odd_skeleton_shared_low_endpoints {M : SimpleGraph V}
    {W : Finset V} {w a b : V}
    (hm : OneFactor.IsMatchingGraph M) (hwa : M.Adj w a) (hb : b ∉ W) :
    ∀ z ∈ W,∀ x y,x ≠ y → (M ⊔ edge w b).Adj z x → (M ⊔ edge w b).Adj z y →
      (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  intro z hz x y hxy hx hy
  have hEdge (v : V) (h : (edge w b).Adj z v) : z = w ∧ v = b := by
    rcases (edge_adj w b z v).mp h with ⟨⟨hw,hv⟩|⟨hb',_⟩,_⟩
    · exact ⟨hw,hv⟩
    · exact (hb (hb' ▸ hz)).elim
  rcases hx with hx|hx <;> rcases hy with hy|hy
  · exact (hxy (hm z x y hx hy)).elim
  · obtain ⟨rfl,rfl⟩ := hEdge y hy
    exact Or.inl ⟨hm _ x a hx hwa,rfl⟩
  · obtain ⟨rfl,rfl⟩ := hEdge x hx
    exact Or.inr ⟨rfl,hm _ y a hy hwa⟩
  · exact (hxy ((hEdge x hx).2.trans (hEdge y hy).2.symm)).elim

set_option maxHeartbeats 2400000 in
theorem exists_odd_matching_auxiliary_words {G M : SimpleGraph V} [DecidableRel M.Adj]
    {U W Z : Finset V} (hWU : W ⊆ U) (hMatch : OneFactor.IsMatchingGraph M)
    {w a b : V} (hw : w ∈ W) (hwa : M.Adj w a) (hb : b ∉ W) (hab : a ≠ b)
    (hS : IsSkeleton G (M ⊔ edge w b) W)
    (haA : a ∈ outerLeaves (M ⊔ edge w b) W) (hbA : b ∈ outerLeaves (M ⊔ edge w b) W)
    (hFour : 4 ≤ (outerLeaves (M ⊔ edge w b) W).card)
    (P : LowSkeletonProjection.Projection G (outerLeaves (M ⊔ edge w b) W) U Z) :
    ∃ (f : ℕ) (endpoint : (Fin f × Bool) ↪ ↥(Uᶜ : Finset V))
      (word : Fin f → List V) (gap : Fin f → Option (V × V)) (k : Fin f),
      2 ≤ f ∧ 2*f = (outerLeaves (M ⊔ edge w b) W).card ∧
      (∀ v,v ∈ Set.range endpoint ↔ ∃ a : outerLeaves (M ⊔ edge w b) W,P.representative a = v) ∧
      (∀ i,gap i = none ↔ i = k) ∧
      (∀ i,(word i).Nodup ∧
        (word i).head? = some (endpoint (i,false)).val ∧
        (word i).getLast? = some (endpoint (i,true)).val ∧
        (word i).IsChain (fun u v => G.Adj u v ∨ gap i = some (u,v))) ∧
      (∀ i x y,gap i = some (x,y) → List.IsInfix [x,y] (word i)) ∧
      (∀ i x y,gap i = some (x,y) → x ∈ W ∧ y ∈ W) ∧
      (∀ i v,v ∈ word i → (v ∉ U ↔ v = (endpoint (i,false)).val ∨ v = (endpoint (i,true)).val)) ∧
      (∀ i j,i ≠ j → List.Disjoint (word i) (word j)) ∧
      (∀ i,∃ v ∈ W,v ∈ word i) ∧
      (∀ a : outerLeaves (M ⊔ edge w b) W,∃ x ∈ W,(M ⊔ edge w b).Adj x a.val ∧
        ∃ i,List.IsInfix [x,a.val] (word i) ∨ List.IsInfix [a.val,x] (word i)) ∧
      (∀ i v,v ∈ word i → v ∈ U → v ∉ W → v ∈ outerLeaves (M ⊔ edge w b) W) := by
  let H := M ⊔ edge w b
  let A := outerLeaves H W
  let x : A := ⟨a,haA⟩
  let y : A := ⟨b,hbA⟩
  obtain ⟨f,e,k,hf,hCard,hx,hy⟩ := paired_endpoints_with_one_special_pair A hS.outer_even hFour x y
    (fun h => hab (congrArg Subtype.val h) : x ≠ y)
  obtain ⟨low,arm,hLow,hArm,hOutside,hInter,_,hShape,hLeafMember⟩ := low_skeleton_arms hWU hS P
  let endpoint : (Fin f × Bool) ↪ ↥(Uᶜ : Finset V) :=
    e.toEmbedding.trans ⟨P.representative,P.injective⟩
  let word (i : Fin f) :=
    (arm (e (i,false))).reverse ++ (if i = k then (arm (e (i,true))).tail else arm (e (i,true)))
  let gap (i : Fin f) := if i = k then none else some (low (e (i,false)),low (e (i,true)))
  have hSpecialLow : low (e (k,false)) = w ∧ low (e (k,true)) = w := by
    have hA : H.Adj w a := Or.inl hwa
    have hB : H.Adj w b := Or.inr ((edge_adj w b w b).mpr ⟨Or.inl ⟨rfl,rfl⟩,fun h => hb (h ▸ hw)⟩)
    rw [hx,hy]
    have hAx : H.degree x.val = 1 := (mem_filter.mp x.property).2
    have hBy : H.degree y.val = 1 := (mem_filter.mp y.property).2
    obtain ⟨u,hu,hU⟩ := (degree_eq_one_iff_existsUnique_adj (G := H)).mp hAx
    obtain ⟨v,hv,hV⟩ := (degree_eq_one_iff_existsUnique_adj (G := H)).mp hBy
    exact ⟨(hU _ (hLow x).2.symm).trans (hU _ hA.symm).symm,
      (hV _ (hLow y).2.symm).trans (hV _ hB.symm).symm⟩
  have hDifferentArms (i j : Fin f) (s t : Bool) (hNe : (i,s) ≠ (j,t))
      (hOrd : i ≠ k ∨ j ≠ k) :
      List.Disjoint (arm (e (i,s))) (arm (e (j,t))) := by
    intro v hv hv'
    have hAB : e (i,s) ≠ e (j,t) := fun h => hNe (e.injective h)
    obtain ⟨ha,hb'⟩ := hInter _ _ hAB v hv hv'
    have h₁ : H.Adj v (e (i,s)).val := ha ▸ (hLow _).2
    have h₂ : H.Adj v (e (j,t)).val := hb' ▸ (hLow _).2
    have hvW : v ∈ W := ha ▸ (hLow _).1
    have hAB' : (e (i,s)).val ≠ (e (j,t)).val := fun h => hAB (Subtype.ext h)
    rcases odd_skeleton_shared_low_endpoints hMatch hwa hb v hvW _ _ hAB' h₁ h₂ with h | h
    · have hi := e.injective ((Subtype.ext h.1 : e (i,s) = x).trans hx.symm)
      have hj := e.injective ((Subtype.ext h.2 : e (j,t) = y).trans hy.symm)
      exact hOrd.elim (fun h => h (congrArg Prod.fst hi)) (fun h => h (congrArg Prod.fst hj))
    · have hi := e.injective ((Subtype.ext h.1 : e (i,s) = y).trans hy.symm)
      have hj := e.injective ((Subtype.ext h.2 : e (j,t) = x).trans hx.symm)
      exact hOrd.elim (fun h => h (congrArg Prod.fst hi)) (fun h => h (congrArg Prod.fst hj))
  have hWordMember (i : Fin f) (v : V) (hv : v ∈ word i) :
      v ∈ arm (e (i,false)) ∨ v ∈ arm (e (i,true)) := by
    change v ∈ (arm (e (i,false))).reverse ++ _ at hv
    rcases List.mem_append.mp hv with h | h
    · exact Or.inl (List.mem_reverse.mp h)
    · right
      by_cases hi : i = k
      · rw [if_pos hi] at h
        exact List.mem_of_mem_tail h
      · simpa only [if_neg hi] using h
  refine ⟨f,endpoint,word,gap,k,hf,hCard,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro v
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨e i,rfl⟩
    · rintro ⟨a,rfl⟩
      refine ⟨e.symm a,?_⟩
      change P.representative (e (e.symm a)) = P.representative a
      rw [Equiv.apply_symm_apply]
  · intro i
    by_cases h : i = k <;> simp [gap,h]
  · intro i
    let A₀ := arm (e (i,false))
    let B₀ := arm (e (i,true))
    have hNe : (i,false) ≠ (i,true) := by intro h; cases congrArg Prod.snd h
    by_cases hi : i = k
    · subst i
      have hEA := hArm (e (k,false))
      have hEB := hArm (e (k,true))
      have hHeadA := hEA.2.2.1.trans (congrArg some hSpecialLow.1)
      have hHeadB := hEB.2.2.1.trans (congrArg some hSpecialLow.2)
      have hTail : (arm (e (k,true))).tail ≠ [] := by
        obtain ⟨B',hB'⟩ := List.head?_eq_some_iff.mp hHeadB
        intro h
        rw [hB'] at h
        change B' = [] at h
        rw [hB',h] at hEB
        have he := Option.some.inj hEB.2.2.2
        exact (mem_compl.mp (P.representative (e (k,true))).property) (he ▸ hWU hw)
      have hJoin := join_projected_arms_at_common_start G _ _ w hHeadA hHeadB hTail
        hEA.1 hEB.1
        (fun v hv hv' => (hInter _ _ (fun h => hNe (e.injective h)) v hv hv').1.trans hSpecialLow.1)
        hEA.2.1 hEB.2.1
      simpa only [word,gap,if_pos rfl,if_true,endpoint,Function.Embedding.trans_apply,
        Equiv.toEmbedding_apply,Function.Embedding.coeFn_mk,hEA.2.2.2,hEB.2.2.2,
        reduceCtorEq,or_false] using hJoin
    · have hEA := hArm (e (i,false))
      have hEB := hArm (e (i,true))
      have hJoin := join_projected_arms G A₀ B₀ _ _ hEA.2.2.1 hEB.2.2.1 hEA.1 hEB.1
        (hDifferentArms i i false true hNe (Or.inl hi)) hEA.2.1 hEB.2.1
      refine ⟨?_,?_,?_,?_⟩
      · simpa only [word,if_neg hi] using hJoin.1
      · simpa only [word,if_neg hi,endpoint,Function.Embedding.trans_apply,
          Equiv.toEmbedding_apply,Function.Embedding.coeFn_mk,A₀,B₀] using hJoin.2.1.trans hEA.2.2.2
      · simpa only [word,if_neg hi,endpoint,Function.Embedding.trans_apply,
          Equiv.toEmbedding_apply,Function.Embedding.coeFn_mk,A₀,B₀] using hJoin.2.2.1.trans hEB.2.2.2
      · simp only [word,gap,if_neg hi]
        exact hJoin.2.2.2.1.imp (fun _ _ h => h.imp_right (by rintro ⟨rfl,rfl⟩; rfl))
  · intro i x' y' hg
    have hi : i ≠ k := by intro h; simp [gap,h] at hg
    have hEq : low (e (i,false)) = x' ∧ low (e (i,true)) = y' := by
      simpa only [gap,if_neg hi,Option.some.injEq,Prod.mk.injEq] using hg
    have hNe : (i,false) ≠ (i,true) := by intro h; cases congrArg Prod.snd h
    have hEA := hArm (e (i,false))
    have hEB := hArm (e (i,true))
    have hJoin := join_projected_arms G _ _ _ _ hEA.2.2.1 hEB.2.2.1 hEA.1 hEB.1
      (hDifferentArms i i false true hNe (Or.inl hi)) hEA.2.1 hEB.2.1
    simpa only [word,if_neg hi,hEq.1,hEq.2] using hJoin.2.2.2.2
  · intro i x' y' hg
    have hi : i ≠ k := by intro h; simp [gap,h] at hg
    have hEq : low (e (i,false)) = x' ∧ low (e (i,true)) = y' := by
      simpa only [gap,if_neg hi,Option.some.injEq,Prod.mk.injEq] using hg
    exact ⟨hEq.1 ▸ (hLow _).1,hEq.2 ▸ (hLow _).1⟩
  · intro i v hv
    have hMem := hWordMember i v hv
    constructor
    · intro h
      rcases hMem with hh | hh
      · exact Or.inl ((hOutside _ _ hh).mp h)
      · exact Or.inr ((hOutside _ _ hh).mp h)
    · rintro (rfl|rfl)
      · exact mem_compl.mp (endpoint (i,false)).property
      · exact mem_compl.mp (endpoint (i,true)).property
  · intro i j hij v hv hv'
    have hOther : i ≠ k ∨ j ≠ k := by
      by_cases h : i = k
      · exact Or.inr (fun h' => hij (h.trans h'.symm))
      · exact Or.inl h
    have hMem (l : Fin f) (h : v ∈ word l) : ∃ s,v ∈ arm (e (l,s)) := by
      by_cases hl : l = k
      · simp only [word,if_pos hl,List.mem_append,List.mem_reverse] at h
        exact h.elim (fun h => ⟨false,h⟩) (fun h => ⟨true,List.mem_of_mem_tail h⟩)
      · simp only [word,if_neg hl,List.mem_append,List.mem_reverse] at h
        exact h.elim (fun h => ⟨false,h⟩) (fun h => ⟨true,h⟩)
    obtain ⟨s,hs⟩ := hMem i hv
    obtain ⟨t,ht⟩ := hMem j hv'
    exact hDifferentArms i j s t (fun h => hij (congrArg Prod.fst h)) hOther hs ht
  · intro i
    let a := e (i,false)
    refine ⟨low a,(hLow a).1,?_⟩
    have hHead := (hArm a).2.2.1
    obtain ⟨tail,hTail⟩ := List.head?_eq_some_iff.mp hHead
    apply List.mem_append_left
    rw [List.mem_reverse,hTail]
    exact List.mem_cons_self
  · intro a
    obtain ⟨⟨i,side⟩,hCoord⟩ := e.surjective a
    let tail := if a.val ∈ U then [(P.representative a).val] else []
    have hArmEq : arm a = low a :: a.val :: tail := hShape a
    refine ⟨low a,(hLow a).1,(hLow a).2,i,?_⟩
    cases side
    · right
      have he : word i = (arm a).reverse ++
          (if i = k then (arm (e (i,true))).tail else arm (e (i,true))) := by simp only [word,hCoord]
      rw [he]
      exact ⟨tail.reverse,(if i = k then (arm (e (i,true))).tail else arm (e (i,true))),
        by simp [hArmEq,List.reverse_cons,List.append_assoc]⟩
    · left
      by_cases hi : i = k
      · subst i
        have hLast : ((arm (e (k,false))).reverse).getLast? = some (low a) := by
          rw [List.getLast?_reverse,(hArm (e (k,false))).2.2.1,hSpecialLow.1,←hSpecialLow.2,hCoord]
        obtain ⟨p,hp⟩ := List.getLast?_eq_some_iff.mp hLast
        refine ⟨p,tail,?_⟩
        simp [word,hCoord,hArmEq,hp,List.append_assoc]
      · simp only [word,if_neg hi,hCoord,hArmEq]
        exact ⟨(arm (e (i,false))).reverse,tail,by simp [List.append_assoc]⟩
  · intro i v hv hu hw
    rcases hWordMember i v hv with h | h
    · exact (hLeafMember _ v h hu hw).symm ▸ (e (i,false)).property
    · exact (hLeafMember _ v h hu hw).symm ▸ (e (i,true)).property

end OverfullWork.CMSTrimmingRound
