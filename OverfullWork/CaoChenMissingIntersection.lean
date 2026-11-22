module

public import OverfullWork.CommonMissingColour
public import OverfullWork.CaoChenDischarging
public import Overfull.Kierstead4
public import Overfull.KempeTools

@[expose] public section


/-! # Protected Kempe improvements for Cao--Chen's bad-palette argument

We count the private parts of a finite family of palettes. The resulting
overlap estimate supplies two vertices sharing an unprotected missing colour.
Together with a root colour absent from all the selected missing palettes,
this constructs an actual Kempe change improving their overlap with the root.
No bad-palette lemma or final R1 charge estimate is assumed.
-/
namespace OverfullWork.CaoChenMissingIntersection
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open scoped Classical
variable {I C : Type*} [DecidableEq I] [Fintype C] [DecidableEq C]
set_option maxHeartbeats 3000000

/-- Pairwise intersections outside X control the total overlap of a family.
The proof allocates each palette its genuinely private part. -/
theorem palette_overlap_bound (T : Finset I) (A : I → Finset C) (X : Finset C)
    (M r : ℕ) (hroot : ∀i∈T,(A i∩X).card≤M)
    (hpair : ∀i∈T,∀j∈T,i≠j → ((A i∩A j)\X).card≤r) :
    X.card+(∑i∈T,(A i).card)≤Fintype.card C+T.card*M+T.card*(T.card-1)*r := by
  let P : I → Finset C := fun i => A i\(X∪(T.erase i).biUnion A)
  have hprivate : Set.PairwiseDisjoint (↑T : Set I) P := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro a hai haj
    have haA := (mem_sdiff.mp haj).1
    have hnot := (mem_sdiff.mp hai).2
    exact hnot (mem_union.mpr (Or.inr (mem_biUnion.mpr
      ⟨j,mem_erase.mpr ⟨hij.symm,hj⟩,haA⟩)))
  have hXdis : Disjoint X (T.biUnion P) := by
    apply Finset.disjoint_left.mpr
    intro a haX haP
    obtain ⟨i,_,hai⟩ := mem_biUnion.mp haP
    exact (mem_sdiff.mp hai).2 (mem_union.mpr (Or.inl haX))
  have hbudget : X.card+(∑i∈T,(P i).card)≤Fintype.card C := by
    have h := card_le_card (subset_univ (X∪T.biUnion P))
    simpa only [card_union_of_disjoint hXdis,card_biUnion hprivate,card_univ] using h
  have hpoint : ∀i∈T,(A i).card≤(P i).card+M+(T.card-1)*r := by
    intro i hi
    let B := (T.erase i).biUnion fun j => (A i∩A j)\X
    have hsub : A i⊆(P i∪(A i∩X))∪B := by
      intro a ha
      by_cases haX : a∈X
      · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr (mem_inter.mpr ⟨ha,haX⟩))))
      · by_cases haP : a∈P i
        · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl haP)))
        · have hOther : a∈(T.erase i).biUnion A := by
            by_contra hn
            exact haP (mem_sdiff.mpr ⟨ha,by simpa only [mem_union,not_or] using And.intro haX hn⟩)
          obtain ⟨j,hj,haj⟩ := mem_biUnion.mp hOther
          exact mem_union.mpr (Or.inr (mem_biUnion.mpr
            ⟨j,hj,mem_sdiff.mpr ⟨mem_inter.mpr ⟨ha,haj⟩,haX⟩⟩))
    have hB : B.card≤(T.card-1)*r := by
      calc
        _ ≤ ∑j∈T.erase i,((A i∩A j)\X).card := card_biUnion_le
        _ ≤ ∑_j∈T.erase i,r := sum_le_sum (fun j hj =>
          hpair i hi j (mem_erase.mp hj).2 (mem_erase.mp hj).1.symm)
        _ = _ := by simp only [sum_const,Nat.nsmul_eq_mul,card_erase_of_mem hi]
    have h := (card_le_card hsub).trans (card_union_le _ _)
    have hp := card_union_le (P i) (A i∩X)
    have hr := hroot i hi
    omega
  have hs := sum_le_sum hpoint
  simp only [sum_add_distrib,sum_const,Nat.nsmul_eq_mul] at hs
  nlinarith only [hbudget,hs]

/-- A large family of large palettes cannot all have small pairwise
intersections away from a large root palette. This is Fact 1 with an
explicit, possibly nonoptimal, weak threshold. -/
theorem exists_large_overlap_outside (T : Finset I) (A : I → Finset C) (X : Finset C)
    (ε : ℝ) (_hε : 0<ε) (hεone : ε<1) (M r : ℕ)
    (hrootlarge : ε*(Fintype.card C:ℝ)<(X.card:ℝ))
    (hlarge : ∀i∈T,ε*(Fintype.card C:ℝ)<((A i).card:ℝ))
    (hroot : ∀i∈T,(A i∩X).card≤M)
    (hsize : 1≤ε*(T.card:ℝ))
    (hthreshold : (M:ℝ)+((T.card-1:ℕ):ℝ)*(r:ℝ)≤ε^2*(Fintype.card C:ℝ)) :
    ∃i∈T,∃j∈T,i≠j ∧ r≤((A i∩A j)\X).card := by
  by_contra hn
  have hp : ∀i∈T,∀j∈T,i≠j → ((A i∩A j)\X).card≤r := by
    intro i hi j hj hij
    have hnot : ¬r≤((A i∩A j)\X).card := fun h => hn ⟨i,hi,j,hj,hij,h⟩
    omega
  have hbN := palette_overlap_bound T A X M r hroot hp
  have hb : (X.card:ℝ)+(∑i∈T,((A i).card:ℝ))≤(Fintype.card C:ℝ)+
      (T.card:ℝ)*(M:ℝ)+(T.card:ℝ)*((T.card-1:ℕ):ℝ)*(r:ℝ) := by
    exact_mod_cast hbN
  have hsum : (T.card:ℝ)*(ε*(Fintype.card C:ℝ))≤∑i∈T,((A i).card:ℝ) := by
    simpa only [sum_const,nsmul_eq_mul] using sum_le_sum (fun i hi => (hlarge i hi).le)
  have hth := mul_le_mul_of_nonneg_left hthreshold (Nat.cast_nonneg T.card : (0:ℝ)≤_)
  have hcover := mul_le_mul_of_nonneg_right hsize
    (show 0≤(1-ε)*(Fintype.card C:ℝ) by positivity)
  nlinarith only [hb,hsum,hrootlarge,hth,hcover]

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every partial proper colouring leaves at least Delta-degree(v)
missing colours; no completeness at v is needed. -/
theorem missing_card_add_degree_ge (c : PEC G (Fin G.maxDegree)) (v : V) :
    G.maxDegree≤(missing c v).card+G.degree v := by
  have h := card_missing_add_colNbrs c v
  have hn : (colNbrs c v).card≤G.degree v :=
    (card_le_card (filter_subset _ _)).trans_eq (card_neighborFinset_eq_degree G v)
  omega

/-- The graph-theoretic form of Fact 1: low vertices with bounded overlap
with the root palette yield a large common palette outside the root. -/
theorem exists_large_common_missing_outside (c : PEC G (Fin G.maxDegree))
    (x : V) (T : Finset V) (ε : ℝ) (hε : 0<ε) (hεone : ε<1) (M r : ℕ)
    (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hlow : ∀v∈T,(G.degree v:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hroot : ∀v∈T,(missing c v∩missing c x).card≤M)
    (hsize : 1≤ε*(T.card:ℝ))
    (hthreshold : (M:ℝ)+((T.card-1:ℕ):ℝ)*(r:ℝ)≤ε^2*(G.maxDegree:ℝ)) :
    ∃u∈T,∃v∈T,u≠v ∧ r≤((missing c u∩missing c v)\missing c x).card := by
  apply exists_large_overlap_outside T (missing c) (missing c x) ε hε hεone M r
  · have h : (G.maxDegree:ℝ)≤((missing c x).card:ℝ)+(G.degree x:ℝ) := by
      exact_mod_cast missing_card_add_degree_ge c x
    simpa only [Fintype.card_fin] using (show ε*(G.maxDegree:ℝ)<((missing c x).card:ℝ) by nlinarith only [h,hx])
  · intro v hv
    have h : (G.maxDegree:ℝ)≤((missing c v).card:ℝ)+(G.degree v:ℝ) := by
      exact_mod_cast missing_card_add_degree_ge c v
    have hl := hlow v hv
    simpa only [Fintype.card_fin] using (show ε*(G.maxDegree:ℝ)<((missing c v).card:ℝ) by nlinarith only [h,hl])
  · exact hroot
  · exact hsize
  · simpa only [Fintype.card_fin] using hthreshold

/-- A root colour avoiding every selected missing palette can be chosen
from a budget on their intersections with the root. -/
theorem exists_root_colour_outside (c : PEC G (Fin G.maxDegree))
    (x : V) (T : Finset V) (F : Finset (Fin G.maxDegree)) (M : ℕ)
    (hroot : ∀v∈T,(missing c v∩missing c x).card≤M)
    (hbudget : F.card+T.card*M<(missing c x).card) :
    ∃δ : Fin G.maxDegree,c.IsFree x δ ∧ δ∉F ∧ ∀v∈T,¬c.IsFree v δ := by
  let X := missing c x
  let B := (X∩F)∪T.biUnion (fun v => missing c v∩X)
  have hB : B.card≤F.card+T.card*M := by
    calc
      _ ≤ (X∩F).card+(T.biUnion fun v => missing c v∩X).card := card_union_le _ _
      _ ≤ F.card+(∑v∈T,(missing c v∩X).card) :=
        Nat.add_le_add (card_le_card inter_subset_right) card_biUnion_le
      _ ≤ F.card+(∑_v∈T,M) := Nat.add_le_add_left (sum_le_sum hroot) _
      _ = _ := by simp only [sum_const,Nat.nsmul_eq_mul]
  obtain ⟨δ,hδX,hδB⟩ := exists_mem_notMem_of_card_lt_card (hB.trans_lt hbudget)
  refine ⟨δ,mem_missing.mp hδX,?_,?_⟩
  · intro hδF
    exact hδB (mem_union.mpr (Or.inl (mem_inter.mpr ⟨hδX,hδF⟩)))
  · intro v hv hδv
    exact hδB (mem_union.mpr (Or.inr (mem_biUnion.mpr
      ⟨v,hv,mem_inter.mpr ⟨mem_missing.mpr hδv,hδX⟩⟩)))

/-- A swap off the root increases the overlap score without losing any
existing root-missing colour at a selected vertex. The second swap colour
is absent from all selected missing palettes and the first is not missing
at the root. This is the genuine monotonicity in Cao--Chen Fact 3. -/
theorem protected_kempe_improves (c : PEC G (Fin G.maxDegree))
    (x : V) (T : Finset V) (F : Finset (Fin G.maxDegree))
    {δ η : Fin G.maxDegree} {v : V}
    (hv : v∈T) (hδ : c.IsFree x δ) (hη : ¬c.IsFree x η)
    (hvη : c.IsFree v η) (hTδ : ∀w∈T,¬c.IsFree w δ)
    (hδF : δ∉F) (hηF : η∉F)
    (hoff : ¬(c.kempeGraph δ η).Reachable v x) :
    (∀w,(c.kempeSwap δ η v).col x w=c.col x w) ∧
    (∀a b γ,γ∈F → c.col a b=some γ →
      (c.kempeSwap δ η v).col a b=some γ) ∧
    (∑w∈T,(missing c w∩missing c x).card)+1≤
      ∑w∈T,(missing (c.kempeSwap δ η v) w∩missing (c.kempeSwap δ η v) x).card := by
  let c' := c.kempeSwap δ η v
  have hfixed : ∀γ,c'.IsFree x γ↔c.IsFree x γ :=
    isFree_kempeSwap_of_not_reachable c δ η hoff
  have hsub : ∀w∈T,missing c w∩missing c x⊆missing c' w∩missing c' x := by
    intro w hw γ hγ
    obtain ⟨hγw,hγx⟩ := mem_inter.mp hγ
    have hγδ : γ≠δ := by
      intro he
      subst γ
      exact hTδ w hw (mem_missing.mp hγw)
    have hγη : γ≠η := by
      intro he
      subst γ
      exact hη (mem_missing.mp hγx)
    exact mem_inter.mpr ⟨mem_missing.mpr
      ((kempeSwap_isFree_of_ne c δ η v w hγδ hγη).mpr (mem_missing.mp hγw)),
      mem_missing.mpr ((hfixed γ).mpr (mem_missing.mp hγx))⟩
  have hδnew : δ∈missing c' v∩missing c' x := by
    refine mem_inter.mpr ⟨mem_missing.mpr ?_,mem_missing.mpr ((hfixed δ).mpr hδ)⟩
    apply (isFree_kempeSwap_of_reachable c δ η (SimpleGraph.Reachable.refl v) δ).mpr
    simpa only [Equiv.swap_apply_left] using hvη
  have hδold : δ∉missing c v∩missing c x := by
    intro h
    exact hTδ v hv (mem_missing.mp (mem_inter.mp h).1)
  have hstrict : (missing c v∩missing c x).card<(missing c' v∩missing c' x).card := by
    apply card_lt_card
    apply ssubset_iff_subset_ne.mpr
    refine ⟨hsub v hv,?_⟩
    intro he
    exact hδold (he.symm ▸ hδnew)
  refine ⟨?_,?_,?_⟩
  · intro w
    exact kempeSwapFun_of_not_reachable c δ η hoff w
  · intro a b γ hγ hc
    exact kempeSwap_col_of_ne c δ η v a b hc (fun he => hδF (he ▸ hγ))
      (fun he => hηF (he ▸ hγ))
  · have hsum := sum_lt_sum (fun w hw => card_le_card (hsub w hw)) ⟨v,hv,hstrict⟩
    exact hsum

/-- In a class-two obstruction, the same root-avoiding swap preserves
the entire missing palette at the other endpoint of the uncoloured edge.
If eta is missing there the endpoint is linked to the root and avoided;
otherwise neither swapped colour is missing there. -/
theorem protected_swap_keeps_other_endpoint (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y v : V} {δ η : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hδ : c.IsFree x δ)
    (hoff : ¬(c.kempeGraph δ η).Reachable v x) (γ : Fin G.maxDegree) :
    (c.kempeSwap δ η v).IsFree y γ↔c.IsFree y γ := by
  have hends := hcm.ab_facts hG
  by_cases hη : c.IsFree y η
  · have hxy := hends.2 δ η hδ hη
    have hyoff : ¬(c.kempeGraph δ η).Reachable v y := by
      intro h
      exact hoff (h.trans hxy.symm)
    exact isFree_kempeSwap_of_not_reachable c δ η hyoff γ
  · exact isFree_kempeSwap_of_neither c δ η v (hends.1 δ hδ) hη γ

/-- Fact 2 together with Fact 3: the hypotheses explicitly construct a
protected Kempe change and certify its strict improvement. There is no
assumed recolouring oracle or assumed extremal contradiction. -/
theorem exists_protected_kempe_improvement
    (c : PEC G (Fin G.maxDegree)) (x : V) (T : Finset V)
    (F : Finset (Fin G.maxDegree)) (ε : ℝ) (hε : 0<ε) (hεone : ε<1) (M : ℕ)
    (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hlow : ∀v∈T,(G.degree v:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hroot : ∀v∈T,(missing c v∩missing c x).card≤M)
    (hsize : 1≤ε*(T.card:ℝ))
    (hthreshold : (M:ℝ)+((T.card-1:ℕ):ℝ)*((F.card+1:ℕ):ℝ)≤ε^2*(G.maxDegree:ℝ))
    (hbudget : F.card+T.card*M<(missing c x).card) :
    ∃v∈T,∃δ η : Fin G.maxDegree,
      δ∉F ∧ η∉F ∧ c.IsFree x δ ∧ ¬c.IsFree x η ∧
      c.IsFree v η ∧ (∀w∈T,¬c.IsFree w δ) ∧
      ¬(c.kempeGraph δ η).Reachable v x ∧
      (∀w,(c.kempeSwap δ η v).col x w=c.col x w) ∧
      (∀a b γ,γ∈F → c.col a b=some γ → (c.kempeSwap δ η v).col a b=some γ) ∧
      (∑w∈T,(missing c w∩missing c x).card)+1≤
        ∑w∈T,(missing (c.kempeSwap δ η v) w∩missing (c.kempeSwap δ η v) x).card := by
  obtain ⟨u,hu,v,hv,huv,hcommon⟩ := exists_large_common_missing_outside c x T ε hε hεone
    M (F.card+1) hx hlow hroot hsize hthreshold
  obtain ⟨η,hηcommon,hηF⟩ := exists_mem_notMem_of_card_lt_card
    (show F.card<((missing c u∩missing c v)\missing c x).card by omega)
  obtain ⟨hηuv,hηx⟩ := mem_sdiff.mp hηcommon
  obtain ⟨hηu,hηv⟩ := mem_inter.mp hηuv
  obtain ⟨δ,hδ,hδF,hTδ⟩ := exists_root_colour_outside c x T F M hroot hbudget
  have hxu : x≠u := by
    intro he
    exact hTδ u hu (he ▸ hδ)
  have hxv : x≠v := by
    intro he
    exact hTδ v hv (he ▸ hδ)
  have hunlinked : ¬(c.kempeGraph δ η).Reachable u x ∨
      ¬(c.kempeGraph δ η).Reachable v x := by
    by_cases h : (c.kempeGraph δ η).Reachable u x
    · right
      intro hh
      exact not_three_linked c hxu hxv huv (Or.inl hδ)
        (Or.inr (mem_missing.mp hηu)) (Or.inr (mem_missing.mp hηv)) h.symm hh.symm
    · exact Or.inl h
  have hηnot : ¬c.IsFree x η := fun h => hηx (mem_missing.mpr h)
  rcases hunlinked with hoff|hoff
  · refine ⟨u,hu,δ,η,hδF,hηF,hδ,hηnot,mem_missing.mp hηu,hTδ,hoff,?_⟩
    exact protected_kempe_improves c x T F hu hδ hηnot (mem_missing.mp hηu) hTδ hδF hηF hoff
  · refine ⟨v,hv,δ,η,hδF,hηF,hδ,hηnot,mem_missing.mp hηv,hTδ,hoff,?_⟩
    exact protected_kempe_improves c x T F hv hδ hηnot (mem_missing.mp hηv) hTδ hδF hηF hoff

end OverfullWork.CaoChenMissingIntersection
