module

public import OverfullWork.CriticalSmallClosedNeighbourhood
public import Overfull.Degree
public import Overfull.Kierstead4

@[expose] public section


/-! # The counting reduction in Cao--Chen Proposition A, Claim 5.2

The sets are constructed from an actual colouring of G−ab. Good second
neighbours are counted after excluding a and the closed neighbourhood of
u. No fork existence or global average-degree estimate is assumed.
-/
namespace OverfullWork.CaoChenForkCounting
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 3000000

def smallVertices (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : Finset V :=
  univ.filter fun x => G.degree x≤d

noncomputable def goodNeighbours (c : PEC G (Fin G.maxDegree)) (a b u : V) : Finset V :=
  (G.neighborFinset u).filter fun z => z≠b ∧ Good c a b u z

noncomputable def goodSecondNeighbours (c : PEC G (Fin G.maxDegree)) (a b u : V) : Finset V :=
  ((goodNeighbours c a b u).biUnion fun z => G.neighborFinset z) \
    insert a (insert u (G.neighborFinset u))

def twoStepVertices (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Finset V :=
  ((G.neighborFinset u) ∪ (G.neighborFinset u).biUnion (fun z => G.neighborFinset z)).erase u

def smallClosedNeighbours (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (v : V) : Finset V :=
  (insert v (G.neighborFinset v)).filter fun x => G.degree x≤d

theorem nonA_card_add_two_le_degree (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {a b : V} (hcm : IsColMinus c a b) :
    (nonA c a b).card+2≤G.degree a := by
  have hcard:=hcm.card_nonA hG
  have ha:=hcm.card_missing_end (Or.inl rfl : a=a ∨ a=b)
  obtain ⟨θ,hθ⟩:=hcm.exists_free_right
  have hb : 1≤(missing c b).card:=card_pos.mpr ⟨θ,mem_missing.mpr hθ⟩
  omega

/-- A genuine good continuation of the spine cannot have small degree.
The two excluded endpoints are handled separately in the counting cover. -/
theorem degree_gt_of_good_continuation (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {a b u : V} {α : Fin G.maxDegree}
    (hcm : IsColMinus c a b) (hbu : c.col b u=some α) (hα : c.IsFree a α)
    (hau : a≠u) (d : ℕ) (hda : G.degree a≤d) (hdelta : 2*d≤G.maxDegree)
    {z : V} (hza : z≠a) (hzb : z≠b) (hgood : Good c a b u z) : d<G.degree z := by
  obtain ⟨γ,huz,hγ⟩:=hgood
  have hK : IsK4 c a b u z α γ:=⟨hcm,hbu,huz,hα,hγ,hau,hza.symm,hzb.symm⟩
  have hcommonA : ((missing c z).filter fun θ => InA c a b θ).card≤1 := by
    rw [card_le_one]
    intro θ₁ h₁ θ₂ h₂
    obtain ⟨hm₁,hA₁⟩:=mem_filter.mp h₁
    obtain ⟨hm₂,hA₂⟩:=mem_filter.mp h₂
    by_contra hne
    exact hK.not_two_common hG hne hA₁ hA₂ (mem_missing.mp hm₁) (mem_missing.mp hm₂)
  have hsplit:=card_filter_add_card_filter_not (s:=missing c z) (fun θ => InA c a b θ)
  have hsub : ((missing c z).filter fun θ => ¬InA c a b θ)⊆nonA c a b := by
    intro θ hθ
    exact mem_nonA.mpr (mem_filter.mp hθ).2
  have hcount:=card_le_card hsub
  have hnonA:=nonA_card_add_two_le_degree hG hcm
  have hmissing:=hcm.card_missing_other hza hzb
  omega

/-- The complete small two-step neighbourhood is covered by good second
neighbours, one closed neighbourhood, and the closed neighbourhoods of
the at most d−2 neighbours whose edge colours lie outside A. -/
theorem small_two_step_card_le_good_second_add (hcrit : IsDeltaCritical G)
    {c : PEC G (Fin G.maxDegree)} {a b u : V} {α : Fin G.maxDegree}
    (hcm : IsColMinus c a b) (hbu : c.col b u=some α) (hα : c.IsFree a α)
    (d : ℕ) (hd : 2≤d) (hda : G.degree a≤d) (hdelta : 2*d≤G.maxDegree) :
    (twoStepVertices G u ∩ smallVertices G d).card≤
      (goodSecondNeighbours c a b u ∩ smallVertices G d).card+(d-1)^2 := by
  have hau : a≠u := by
    intro he
    subst u
    have hba : c.col b a=none := by rw [c.col_symm];exact hcm.uncol
    rw [hba] at hbu
    contradiction
  have hbuAdj := c.col_adj hbu
  let B:=(badNbrs c a b u).biUnion (fun z => smallClosedNeighbours G d z)
  let C:=smallClosedNeighbours G d b
  have hthreshold : 2*d<G.maxDegree+2 := by omega
  have hclosed (z : V) : (smallClosedNeighbours G d z).card≤d-1 :=
    CaoChenSmallNeighbourhood.closed_neighbourhood_small_degree_card_le G hcrit d hd hthreshold z
  have hbad : (badNbrs c a b u).card≤d-2 := by
    have hh:=card_badNbrs_le (c:=c) (a:=a) (b:=b) u
    have hn:=nonA_card_add_two_le_degree hcrit.2.1 hcm
    omega
  have hB : B.card≤(d-2)*(d-1) := by
    calc
      _ ≤ ∑ z∈badNbrs c a b u,(smallClosedNeighbours G d z).card := card_biUnion_le
      _ ≤ ∑ _z∈badNbrs c a b u,(d-1) := sum_le_sum (fun z _ => hclosed z)
      _ = (badNbrs c a b u).card*(d-1) := by simp
      _ ≤ _ := Nat.mul_le_mul_right (d-1) hbad
  have hC : C.card≤d-1 := hclosed b
  have hnear : ∀ t∈smallVertices G d,G.Adj u t → t∈C∪B := by
    intro t ht hut
    have htd := (mem_filter.mp ht).2
    by_cases hta : t=a
    · subst t
      apply mem_union.mpr
      left
      exact mem_filter.mpr ⟨mem_insert_of_mem ((mem_neighborFinset G b a).mpr hcm.adj.symm),htd⟩
    by_cases htb : t=b
    · subst t
      exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨mem_insert_self _ _,htd⟩))
    by_cases hgood : Good c a b u t
    · have hh:=degree_gt_of_good_continuation hcrit.2.1 hcm hbu hα hau d hda hdelta hta htb hgood
      omega
    · have hne : s(u,t)≠s(a,b) := sym2_ne_ab ⟨hau.symm,hbuAdj.ne.symm⟩
      have htbad := not_good_mem_bad hcm hut hne hgood
      apply mem_union.mpr
      right
      exact mem_biUnion.mpr ⟨t,htbad,mem_filter.mpr ⟨mem_insert_self _ _,htd⟩⟩
  have hcover : twoStepVertices G u ∩ smallVertices G d⊆
      (goodSecondNeighbours c a b u ∩ smallVertices G d)∪(C∪B) := by
    intro t ht
    obtain ⟨htstep,htsmall⟩:=mem_inter.mp ht
    obtain ⟨htu,htstep⟩:=mem_erase.mp htstep
    rcases mem_union.mp htstep with htnear|htsecond
    · exact mem_union.mpr (Or.inr (hnear t htsmall ((mem_neighborFinset G u t).mp htnear)))
    obtain ⟨z,hzu,hzt⟩:=mem_biUnion.mp htsecond
    by_cases htnear : G.Adj u t
    · exact mem_union.mpr (Or.inr (hnear t htsmall htnear))
    by_cases hta : t=a
    · subst t
      exact mem_union.mpr (Or.inr (mem_union.mpr (Or.inl (mem_filter.mpr
        ⟨mem_insert_of_mem ((mem_neighborFinset G b a).mpr hcm.adj.symm),(mem_filter.mp htsmall).2⟩))))
    by_cases hzb : z=b
    · subst z
      exact mem_union.mpr (Or.inr (mem_union.mpr (Or.inl (mem_filter.mpr
        ⟨mem_insert_of_mem hzt,(mem_filter.mp htsmall).2⟩))))
    by_cases hgood : Good c a b u z
    · apply mem_union.mpr
      left
      apply mem_inter.mpr
      refine ⟨mem_sdiff.mpr ⟨?_,?_⟩,htsmall⟩
      · exact mem_biUnion.mpr ⟨z,mem_filter.mpr ⟨hzu,hzb,hgood⟩,hzt⟩
      · intro hh
        rcases mem_insert.mp hh with he|hh
        · exact hta he
        · rcases mem_insert.mp hh with he|hh
          · exact htu he
          · exact htnear ((mem_neighborFinset G u t).mp hh)
    · have hne : s(u,z)≠s(a,b) := sym2_ne_ab ⟨hau.symm,hbuAdj.ne.symm⟩
      have hzbad:=not_good_mem_bad hcm ((mem_neighborFinset G u z).mp hzu) hne hgood
      exact mem_union.mpr (Or.inr (mem_union.mpr (Or.inr (mem_biUnion.mpr
        ⟨z,hzbad,mem_filter.mpr ⟨mem_insert_of_mem hzt,(mem_filter.mp htsmall).2⟩⟩))))
  have hcount:=card_le_card hcover
  have hfirst:=card_union_le (goodSecondNeighbours c a b u ∩ smallVertices G d) (C∪B)
  have hsecond:=card_union_le C B
  have hdsub : d-2+1=d-1 := by omega
  have hid : (d-1)+(d-2)*(d-1)=(d-1)^2 := by nlinarith only [congrArg (fun x => x*(d-1)) hdsub]
  omega

/-- Cao--Chen Claim 5.2: many small vertices within distance two leave
many small vertices reached through A-coloured neighbours. This does not
yet assert that the final anchor-to-leaf edges have colours in A. -/
theorem good_second_small_card_lower_bound (hcrit : IsDeltaCritical G)
    {c : PEC G (Fin G.maxDegree)} {a b u : V} {α : Fin G.maxDegree}
    (hcm : IsColMinus c a b) (hbu : c.col b u=some α) (hα : c.IsFree a α)
    (d : ℕ) (hd : 2≤d) (hda : G.degree a≤d)
    (hdelta : (d+1)*(d+3)≤G.maxDegree)
    (hbig : (d-1)^2+(d+1)*(d-1)+(d-2)+1≤
      (twoStepVertices G u ∩ smallVertices G d).card) :
    (d+1)*(d-1)+(d-2)+1≤(goodSecondNeighbours c a b u ∩ smallVertices G d).card := by
  have htwod : 2*d≤G.maxDegree := by nlinarith only [hdelta,hd]
  have hh:=small_two_step_card_le_good_second_add hcrit hcm hbu hα d hd hda htwod
  omega

end OverfullWork.CaoChenForkCounting
