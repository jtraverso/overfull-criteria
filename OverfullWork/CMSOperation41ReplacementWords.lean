module

public import OverfullWork.CMSOperation41ProjectionHistory
public import OverfullWork.CMSOperation41RealizedPrescription

@[expose] public section


/-! The words of S2.1–S2.4 and the additional two-edge replacements
of S2.5 share the same ordinary core. The latter avoid the earlier
endpoints, isolated ordinary vertices and saturated representatives. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph DirectedSpanningConfiguration DirectedRobustExpansion
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge SimpleGraph.instDecidableMapAdj

variable {V : Type*} [Fintype V] [DecidableEq V]

structure TrimmingReplacementWords (G : SimpleGraph V) (U : Finset V) (I : Type*) where
  endpoint : (I × Bool) ↪ ↥(Uᶜ : Finset V)
  body : I → List V
  gaps : Finset (Sym2 V)
  chain : ∀ i,((endpoint (i,false)).val :: body i ++ [(endpoint (i,true)).val]).IsChain
    (fun a b => G.Adj a b ∨ s(a,b) ∈ gaps)
  gap_witness : ∀ e ∈ gaps,∃ i a b,e = s(a,b) ∧
    List.IsInfix [a,b] ((endpoint (i,false)).val :: body i ++ [(endpoint (i,true)).val])
  simple : ∀ i,(body i).Nodup
  outside : ∀ i v,v ∈ body i → v ∈ U
  disjoint : ∀ i j,i ≠ j → List.Disjoint (body i) (body j)

namespace TrimmingReplacementWords

variable {G : SimpleGraph V} {U : Finset V} {I : Type*}

def word (R : TrimmingReplacementWords G U I) (i : I) : List V :=
  (R.endpoint (i,false)).val :: R.body i ++ [(R.endpoint (i,true)).val]

def prescribedGraph (R : TrimmingReplacementWords G U I) : SimpleGraph V :=
  SimpleGraph.fromRel (fun a b => s(a,b) ∉ R.gaps ∧ ∃ i,List.IsInfix [a,b] (R.word i))

theorem prescribedGraph_adj (R : TrimmingReplacementWords G U I) (a b : V) :
    R.prescribedGraph.Adj a b ↔ s(a,b) ∉ R.gaps ∧
      ∃ i,List.IsInfix [a,b] (R.word i) ∨ List.IsInfix [b,a] (R.word i) := by
  have hAB {x y : V} (hGap : s(x,y) ∉ R.gaps) (i : I) (hWord : List.IsInfix [x,y] (R.word i)) :
      G.Adj x y := by
    have h := ((R.chain i).infix hWord).rel
    exact h.resolve_right hGap
  constructor
  · rintro ⟨_,⟨hGap,i,hi⟩|⟨hGap,i,hi⟩⟩
    · exact ⟨hGap,i,Or.inl hi⟩
    · rw [Sym2.eq_swap] at hGap
      exact ⟨hGap,i,Or.inr hi⟩
  · rintro ⟨hGap,i,hi|hi⟩
    · exact ⟨(hAB hGap i hi).ne,Or.inl ⟨hGap,i,hi⟩⟩
    · have hSwap : s(b,a) ∉ R.gaps := by rwa [Sym2.eq_swap]
      exact ⟨(hAB hSwap i hi).ne.symm,Or.inr ⟨hSwap,i,hi⟩⟩

theorem prescribedGraph_le (R : TrimmingReplacementWords G U I) : R.prescribedGraph ≤ G := by
  intro x y h
  obtain ⟨hn,i,hi|hi⟩ := (R.prescribedGraph_adj x y).mp h
  · exact (((R.chain i).infix hi).rel).resolve_right hn
  · have hSwap : s(y,x) ∉ R.gaps := by rwa [Sym2.eq_swap]
    exact ((((R.chain i).infix hi).rel).resolve_right hSwap).symm

/-- A retained vertex saves one edge for each incident marked pair.
An omitted vertex saves both edges of the round. -/
noncomputable def degreeCredit (R : TrimmingReplacementWords G U I)
    (omitted : Finset ↥(Uᶜ : Finset V)) (v : V) : ℕ :=
  if (∃ x ∉ omitted,x.val = v) ∨ (∃ i,v ∈ R.body i)
  then (trimmingGapGraph R.gaps).degree v else 2

theorem degree_credit_eq_gaps_at_retained_core (R : TrimmingReplacementWords G U I)
    (omitted : Finset ↥(Uᶜ : Finset V)) (v : ↥(Uᶜ : Finset V)) (hv : v ∉ omitted) :
    R.degreeCredit omitted v.val = (trimmingGapGraph R.gaps).degree v.val := by
  rw [degreeCredit,if_pos (Or.inl ⟨v,hv,rfl⟩)]

theorem degree_credit_eq_two_at_omitted_core (R : TrimmingReplacementWords G U I)
    (omitted : Finset ↥(Uᶜ : Finset V)) (v : ↥(Uᶜ : Finset V)) (hv : v ∈ omitted) :
    R.degreeCredit omitted v.val = 2 := by
  rw [degreeCredit,if_neg]
  rintro (⟨u,hu,he⟩|⟨i,hi⟩)
  · exact hu (Subtype.ext he ▸ hv)
  · exact mem_compl.mp v.property (R.outside i _ hi)

theorem degree_add_credit_of_gap_balance (R : TrimmingReplacementWords G U I)
    (omitted : Finset ↥(Uᶜ : Finset V)) (Q : SimpleGraph V) (v : V)
    (hBalance : Q.degree v+(trimmingGapGraph R.gaps).degree v =
      if (∃ x ∉ omitted,x.val = v) ∨ (∃ i,v ∈ R.body i) then 2 else 0) :
    Q.degree v+R.degreeCredit omitted v = 2 := by
  by_cases h : (∃ x ∉ omitted,x.val = v) ∨ (∃ i,v ∈ R.body i)
  · simpa only [degreeCredit,if_pos h] using hBalance
  · simp only [if_neg h] at hBalance
    rw [degreeCredit,if_neg h]
    omega

variable [Fintype I]

set_option maxHeartbeats 2400000 in
/-- Complete the prescribed endpoint pairs with the retired centres of
S2.5. The two new representatives per centre are free appearances. -/
theorem exists_with_retired_spokes (R : TrimmingReplacementWords G U I) [DecidableRel G.Adj]
    (B omitted : Finset V) (hBU : B ⊆ U)
    (hAbsent : ∀ i v,v ∈ R.body i → v ∉ B)
    (hOmit : ∀ i : I × Bool,(R.endpoint i).val ∉ omitted)
    (used : ℕ → Finset V) (j cap k b : ℕ) (hCap : 0 < cap)
    (hUsed : ∀ i < j,(used i).card ≤ b) (hTotal : j*b ≤ k*cap)
    (hDegree : ∀ z ∈ B,U.card+2*Fintype.card I+omitted.card+k+2*B.card ≤ G.degree z) :
    ∃ T : TrimmingReplacementWords G U (I ⊕ ↥B),
      T.gaps = R.gaps ∧ (∀ i c,T.endpoint (Sum.inl i,c) = R.endpoint (i,c)) ∧
      (∀ i,T.body (Sum.inl i) = R.body i) ∧ (∀ z : B,T.body (Sum.inr z) = [z.val]) ∧
      (∀ i : (I ⊕ ↥B) × Bool,(T.endpoint i).val ∉ omitted) ∧
      ∀ z : B,∀ side,projectionLoad (range j) used (T.endpoint (Sum.inr z,side)).val < cap := by
  let ends : Finset V := (univ : Finset (I × Bool)).image fun i => (R.endpoint i).val
  let F := U ∪ ends ∪ omitted
  have hEnds : ends.card = 2*Fintype.card I := by
    have hi : Function.Injective (fun i : I × Bool => (R.endpoint i).val) := fun i j h =>
      R.endpoint.injective (Subtype.ext h)
    rw [card_image_of_injective _ hi,card_univ,Fintype.card_prod,Fintype.card_bool,Nat.mul_comm]
  have hUF : U ⊆ F := subset_union_left.trans subset_union_left
  obtain ⟨e,_,_,_,_,_,_,hAdj,_,hFresh⟩ := exists_spoke_prescription_avoiding_saturated G B U F
    hBU hUF used j cap k b hCap hUsed hTotal (fun z hz => by
      have h1 := card_union_le U ends
      have h2 := card_union_le (U∪ends) omitted
      have h3 := hDegree z hz
      change (U∪ends∪omitted).card+k+2*B.card ≤ G.degree z
      omega)
  have hAvoid (i : ↥B × Bool) : (e i).val ∉ F := fun h =>
    mem_compl.mp (e i).property (mem_union_left _ h)
  let other (i : ↥B × Bool) : ↥(Uᶜ : Finset V) :=
    ⟨(e i).val,mem_compl.mpr (fun h => hAvoid i (hUF h))⟩
  have hOther : Function.Injective other := by
    intro i i' h
    apply e.injective
    apply Subtype.ext
    exact congrArg (fun x : ↥(Uᶜ : Finset V) => x.val) h
  let pick (i : (I ⊕ ↥B) × Bool) : ↥(Uᶜ : Finset V) :=
    i.1.elim (fun a => R.endpoint (a,i.2)) (fun z => other (z,i.2))
  have hPick : Function.Injective pick := by
    rintro ⟨a,c⟩ ⟨b,d⟩ hEq
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        have h := R.endpoint.injective hEq
        exact Prod.ext (congrArg (fun i : I × Bool => Sum.inl i.1) h) (congrArg (fun i : I × Bool => i.2) h)
      | inr z =>
        have he : (R.endpoint (a,c)).val = (e (z,d)).val := congrArg Subtype.val hEq
        have hMem : (R.endpoint (a,c)).val ∈ ends := mem_image.mpr ⟨(a,c),mem_univ _,rfl⟩
        exact (hAvoid (z,d) (mem_union_left _ (mem_union_right _ (he ▸ hMem)))).elim
    | inr z =>
      cases b with
      | inl b =>
        have he : (R.endpoint (b,d)).val = (e (z,c)).val := congrArg Subtype.val hEq.symm
        have hMem : (R.endpoint (b,d)).val ∈ ends := mem_image.mpr ⟨(b,d),mem_univ _,rfl⟩
        exact (hAvoid (z,c) (mem_union_left _ (mem_union_right _ (he ▸ hMem)))).elim
      | inr z' =>
        have h := hOther hEq
        exact Prod.ext (congrArg (fun i : ↥B × Bool => Sum.inr i.1) h) (congrArg (fun i : ↥B × Bool => i.2) h)
  let body : I ⊕ ↥B → List V := Sum.elim R.body (fun z => [z.val])
  let T : TrimmingReplacementWords G U (I ⊕ ↥B) :=
    { endpoint := ⟨pick,hPick⟩
      body := body
      gaps := R.gaps
      chain := by
        intro i
        cases i with
        | inl a => exact R.chain a
        | inr z =>
          have hz := hAdj z
          exact .cons_cons (Or.inl hz.1.symm) (.cons_cons (Or.inl hz.2) (.singleton _))
      gap_witness := by
        intro x hx
        obtain ⟨i,a,b,he,he'⟩ := R.gap_witness x hx
        exact ⟨Sum.inl i,a,b,he,he'⟩
      simple := by
        intro i
        cases i with
        | inl a => exact R.simple a
        | inr z => exact List.nodup_singleton z.val
      outside := by
        intro i v hv
        cases i with
        | inl a => exact R.outside a v hv
        | inr z =>
          have he : v = z.val := List.mem_singleton.mp hv
          exact he.symm ▸ hBU z.property
      disjoint := by
        intro i i' hne v hv hv'
        cases i with
        | inl a =>
          cases i' with
          | inl a' => exact R.disjoint a a' (fun h => hne (congrArg Sum.inl h)) hv hv'
          | inr z => exact hAbsent a v hv ((List.mem_singleton.mp hv').symm ▸ z.property)
        | inr z =>
          cases i' with
          | inl a => exact hAbsent a v hv' ((List.mem_singleton.mp hv).symm ▸ z.property)
          | inr z' =>
            have he := (List.mem_singleton.mp hv).symm.trans (List.mem_singleton.mp hv')
            exact hne (congrArg Sum.inr (Subtype.ext he)) }
  refine ⟨T,rfl,fun _ _ => rfl,fun _ => rfl,fun _ => rfl,?_,?_⟩
  · rintro ⟨i,side⟩
    cases i with
    | inl a => exact hOmit (a,side)
    | inr z => exact fun h => hAvoid (z,side) (mem_union_right _ h)
  · exact fun z side => hFresh (z,side)

set_option maxHeartbeats 2600000 in
theorem realized_is_two_colour_layer_with_gap_balance (R : TrimmingReplacementWords G U I)
    {n : ℕ} (hn : 2 ≤ n+1) (w : Fin (n+1) ↪ ↥(Uᶜ : Finset V))
    (mark : I ↪ Fin (n+1)) (fixed : Finset (Fin (n+1))) (hFixed : fixed = univ.image mark)
    (isolated : Finset ↥(Uᶜ : Finset V)) (hIso : ∀ i,w i ∉ isolated)
    (hEnds : ∀ i,w (mark i) = R.endpoint (i,false) ∧
      w (finRotate (n+1) (mark i)) = R.endpoint (i,true))
    {J : SimpleGraph ↥(Uᶜ : Finset V)} {D : Digraph ↥(Uᶜ : Finset V)} (hOr : IsOrientationOf D J)
    (P : Realization D (cyclicLayout hn w fixed isolated))
    (hHost : ∀ u v,D.Adj u v → G.Adj u.val v.val) :
    let incl : ↥(Uᶜ : Finset V) ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
    let length := (Uᶜ : Finset V).card-isolated.card+∑ i,(R.body i).length
    let Q := R.prescribedGraph ⊔ ((hostEdges J P.used).map incl).deleteEdges (R.gaps : Set (Sym2 V))
    3 ≤ length → (Even length ∨ R.gaps.Nonempty) →
    Q ≤ G ∧ Q.EdgeColorable 2 ∧ (∀ v,Q.degree v ≤ 2) ∧
      (∀ v,v ∉ isolated → (∀ u,s(v.val,u) ∉ R.gaps) → Q.degree v.val = 2) ∧
      (∀ v ∈ isolated,Q.degree v.val = 0) ∧
      ∀ v,Q.degree v+(trimmingGapGraph R.gaps).degree v =
        if (∃ x ∉ isolated,x.val = v) ∨ (∃ i,v ∈ R.body i) then 2 else 0 := by
  intro incl length Q hLength hParity
  let body (i : Fin (n+1)) : List V :=
    if h : ∃ j,mark j = i then R.body h.choose else []
  have hBody (i : I) : body (mark i) = R.body i := by
    have he : ∃ j,mark j = mark i := ⟨i,rfl⟩
    dsimp only [body]
    rw [dif_pos he,mark.injective he.choose_spec]
  have hMarked (i : I) : mark i ∈ fixed := by rw [hFixed]; exact mem_image.mpr ⟨i,mem_univ _,rfl⟩
  have hMem (i : Fin (n+1)) (hi : i ∈ fixed) : ∃ j,i = mark j := by
    rw [hFixed] at hi
    obtain ⟨j,_,rfl⟩ := mem_image.mp hi
    exact ⟨j,rfl⟩
  have hWord (i : I) :
      (incl (w (mark i)) :: body (mark i) ++ [incl (w (finRotate (n+1) (mark i)))]) = R.word i := by
    rw [(hEnds i).1,(hEnds i).2,hBody]
    rfl
  have hAdj (a b : V) : R.prescribedGraph.Adj a b ↔ s(a,b) ∉ R.gaps ∧ ∃ i ∈ fixed,
      List.IsInfix [a,b] (incl (w i) :: body i ++ [incl (w (finRotate (n+1) i))]) ∨
      List.IsInfix [b,a] (incl (w i) :: body i ++ [incl (w (finRotate (n+1) i))]) := by
    rw [R.prescribedGraph_adj]
    constructor
    · rintro ⟨h,i,hi⟩
      exact ⟨h,mark i,hMarked i,by rwa [hWord]⟩
    · rintro ⟨h,i,hi,hWord'⟩
      obtain ⟨j,rfl⟩ := hMem i hi
      exact ⟨h,j,by rwa [hWord] at hWord'⟩
  have hList : ∑ i ∈ fixed,(body i).length = ∑ i,(R.body i).length := by
    rw [hFixed,sum_image mark.injective.injOn]
    simp only [hBody]
  have hSize : 3 ≤ Fintype.card ↥(Uᶜ : Finset V)-isolated.card+(∑ i ∈ fixed,(body i).length) := by
    simpa only [Fintype.card_coe,hList] using hLength
  have hPar : Even (Fintype.card ↥(Uᶜ : Finset V)-isolated.card+(∑ i ∈ fixed,(body i).length)) ∨
      ∃ i ∈ fixed,∃ a b,s(a,b) ∈ R.gaps ∧
        List.IsInfix [a,b] (incl (w i) :: body i ++ [incl (w (finRotate (n+1) i))]) := by
    rcases hParity with h | ⟨e,he⟩
    · exact Or.inl (by simpa only [Fintype.card_coe,hList] using h)
    obtain ⟨i,a,b,rfl,hi⟩ := R.gap_witness e he
    exact Or.inr ⟨mark i,hMarked i,a,b,he,by rwa [hWord]⟩
  have hLayer := realized_prescription_is_two_colour_layer_with_gap_balance G incl hn w fixed isolated
    hOr P hIso hHost body R.gaps R.prescribedGraph hAdj ?_ ?_ ?_ ?_ hSize hPar
  · obtain ⟨hLe,hTwo,hDeg,hOrd,hZero,hBalance⟩ := hLayer
    refine ⟨hLe,hTwo,hDeg,hOrd,hZero,?_⟩
    intro v
    have hGaps : ∀ edge ∈ R.gaps,∃ i ∈ fixed,∃ a b,edge = s(a,b) ∧
        List.IsInfix [a,b] (incl (w i) :: body i ++ [incl (w (finRotate (n+1) i))]) := by
      intro edge he
      obtain ⟨i,a,b,hPair,hInfix⟩ := R.gap_witness edge he
      exact ⟨mark i,hMarked i,a,b,hPair,by rwa [hWord]⟩
    have hOccur : (∃ i ∈ fixed,v ∈ body i) ↔ ∃ i,v ∈ R.body i := by
      constructor
      · rintro ⟨i,hi,hv⟩
        obtain ⟨j,rfl⟩ := hMem i hi
        exact ⟨j,by rwa [hBody] at hv⟩
      · rintro ⟨i,hi⟩
        exact ⟨mark i,hMarked i,by rwa [hBody]⟩
    have hBoth : ((∃ u ∉ isolated,incl u = v) ∨ (∃ i ∈ fixed,v ∈ body i)) ↔
        (∃ u ∉ isolated,u.val = v) ∨ (∃ i,v ∈ R.body i) := or_congr Iff.rfl hOccur
    by_cases h : (∃ u ∉ isolated,u.val = v) ∨ (∃ i,v ∈ R.body i)
    · simpa only [if_pos h,if_pos (hBoth.mpr h)] using hBalance hGaps v
    · simpa only [if_neg h,if_neg (fun hh => h (hBoth.mp hh))] using hBalance hGaps v
  · intro i hi
    obtain ⟨j,rfl⟩ := hMem i hi
    rw [hWord]
    exact R.chain j
  · intro i hi
    obtain ⟨j,rfl⟩ := hMem i hi
    rw [(hEnds j).1,hBody]
    refine List.nodup_cons.mpr ⟨fun h => ?_,R.simple j⟩
    exact mem_compl.mp (R.endpoint (j,false)).property (R.outside j _ h)
  · intro i hi v hv
    obtain ⟨j,rfl⟩ := hMem i hi
    rw [hBody] at hv
    rintro ⟨x,rfl⟩
    exact mem_compl.mp x.property (R.outside j _ hv)
  · intro i hi k hk hne
    obtain ⟨j,rfl⟩ := hMem i hi
    obtain ⟨l,rfl⟩ := hMem k hk
    rw [hBody,hBody]
    exact R.disjoint j l (fun h => hne (congrArg mark h))

theorem realized_is_two_colour_layer (R : TrimmingReplacementWords G U I)
    {n : ℕ} (hn : 2 ≤ n+1) (w : Fin (n+1) ↪ ↥(Uᶜ : Finset V))
    (mark : I ↪ Fin (n+1)) (fixed : Finset (Fin (n+1))) (hFixed : fixed = univ.image mark)
    (isolated : Finset ↥(Uᶜ : Finset V)) (hIso : ∀ i,w i ∉ isolated)
    (hEnds : ∀ i,w (mark i) = R.endpoint (i,false) ∧
      w (finRotate (n+1) (mark i)) = R.endpoint (i,true))
    {J : SimpleGraph ↥(Uᶜ : Finset V)} {D : Digraph ↥(Uᶜ : Finset V)} (hOr : IsOrientationOf D J)
    (P : Realization D (cyclicLayout hn w fixed isolated))
    (hHost : ∀ u v,D.Adj u v → G.Adj u.val v.val) :
    let incl : ↥(Uᶜ : Finset V) ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
    let length := (Uᶜ : Finset V).card-isolated.card+∑ i,(R.body i).length
    let Q := R.prescribedGraph ⊔ ((hostEdges J P.used).map incl).deleteEdges (R.gaps : Set (Sym2 V))
    3 ≤ length → (Even length ∨ R.gaps.Nonempty) →
    Q ≤ G ∧ Q.EdgeColorable 2 ∧ (∀ v,Q.degree v ≤ 2) ∧
      (∀ v,v ∉ isolated → (∀ u,s(v.val,u) ∉ R.gaps) → Q.degree v.val = 2) ∧
      ∀ v ∈ isolated,Q.degree v.val = 0 := by
  intro incl length Q hLength hParity
  obtain ⟨hLe,hTwo,hDeg,hOrd,hZero,_⟩ :=
    R.realized_is_two_colour_layer_with_gap_balance hn w mark fixed hFixed isolated hIso hEnds
      hOr P hHost hLength hParity
  exact ⟨hLe,hTwo,hDeg,hOrd,hZero⟩

end TrimmingReplacementWords
end OverfullWork.CMSTrimmingRound
