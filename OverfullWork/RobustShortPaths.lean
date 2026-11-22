module

public import OverfullWork.RobustExpansionFinite
public import OverfullWork.SparseDeficitCore
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

@[expose] public section


/-! # Actual short paths in integer robust expanders

Finite undirected form of the bounded-diameter argument in Kuehn--Lo--
Osthus--Staden, The robust component structure of dense regular graphs
and applications, PLMS 110 (2015), 19--56, Section 6.2, Lemma 6.6.
Source: https://web.mat.bham.ac.uk/D.Kuehn/ham3conn_37.pdf, PDF page 20;
retrieved PDF SHA-256:
3a8b952522fde7a0d7d1f30d0e7dadb4a6355e690d407d541264cfa055753dd2.

The paths are constructed by growth of metric balls. No Hamiltonicity
theorem, oracle or spanning-path conclusion is used or asserted.
-/
namespace OverfullWork.RobustShortPaths
open SimpleGraph Finset PrunedCore RobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

noncomputable def ball (x : V) (k : ℕ) : Finset V :=
  univ.filter fun v => ∃p : G.Walk x v,p.length≤k

theorem mem_ball (x v : V) (k : ℕ) :
    v∈ball G x k ↔ ∃p : G.Walk x v,p.length≤k := by simp [ball]

theorem degree_le_ball_one (x : V) : G.degree x≤(ball G x 1).card := by
  have hs : G.neighborFinset x⊆ball G x 1 := by
    intro v hv
    have h:= (mem_neighborFinset G x v).mp hv
    exact (mem_ball G x v 1).mpr ⟨Walk.cons h Walk.nil,by simp⟩
  simpa only [card_neighborFinset_eq_degree] using card_le_card hs

theorem neighbourhood_subset_ball_succ (x : V) (k r : ℕ) (hr : 0<r) :
    neighbourhood G r (ball G x k)⊆ball G x (k+1) := by
  intro v hv
  have hc : 0<neighboursIn G (ball G x k) v :=
    hr.trans_le (mem_filter.mp hv).2
  obtain ⟨z,hz⟩:=card_pos.mp hc
  obtain ⟨hzN,hzB⟩:=mem_filter.mp hz
  obtain ⟨p,hp⟩:=(mem_ball G x z k).mp hzB
  have h:= (mem_neighborFinset G v z).mp hzN
  exact (mem_ball G x v (k+1)).mpr ⟨p.concat h.symm,by simpa using Nat.add_le_add_right hp 1⟩

theorem exists_walk_of_large_ball (x y : V) (t k : ℕ)
    (hdegree : t≤G.degree y) (hlarge : Fintype.card V<(ball G x k).card+t) :
    ∃p : G.Walk x y,p.length≤k+1 := by
  have hcard:=card_union_add_card_inter (ball G x k) (G.neighborFinset y)
  have hbound:=card_le_univ (ball G x k∪G.neighborFinset y)
  rw [card_neighborFinset_eq_degree] at hcard
  have hp : 0<(ball G x k∩G.neighborFinset y).card := by omega
  obtain ⟨z,hz⟩:=card_pos.mp hp
  obtain ⟨hzB,hzN⟩:=mem_inter.mp hz
  obtain ⟨p,hp⟩:=(mem_ball G x z k).mp hzB
  have h:= (mem_neighborFinset G y z).mp hzN
  exact ⟨p.concat h.symm,by simpa using Nat.add_le_add_right hp 1⟩

/-- Ball growth gives an actual bounded walk once k robust increments
would exceed the order. The degree hypotheses only concern its ends. -/
theorem exists_walk_of_robust_growth (r t k : ℕ)
    (hrobust : IsRobustAt G r t) (hr : 0<r)
    (hgrowth : Fintype.card V<t+k*r) (x y : V)
    (hx : t≤G.degree x) (hy : t≤G.degree y) :
    ∃p : G.Walk x y,p.length≤k+2 := by
  by_contra hn
  have hupper : ∀j,j≤k → (ball G x (j+1)).card+t≤Fintype.card V := by
    intro j hj
    by_contra hb
    obtain ⟨p,hp⟩:=exists_walk_of_large_ball G x y t (j+1) hy (Nat.lt_of_not_ge hb)
    exact hn ⟨p,by omega⟩
  have hlower : ∀j,j≤k → t+j*r≤(ball G x (j+1)).card := by
    intro j
    induction j with
    | zero =>
      intro _
      simpa using hx.trans (degree_le_ball_one G x)
    | succ j ih =>
      intro hj
      have hlo:=ih (by omega)
      have hrb:=hrobust (ball G x (j+1)) (by omega) (hupper j (by omega))
      have hsub:=card_le_card (neighbourhood_subset_ball_succ G x (j+1) r hr)
      rw [Nat.succ_mul]
      omega
  have hl:=hlower k le_rfl
  have hu:=card_le_univ (ball G x (k+1))
  omega

/-- Positive robust growth connects any two suitably high-degree ends
by a simple path of length at most floor(n/r)+3. -/
theorem exists_short_path (r t : ℕ) (hrobust : IsRobustAt G r t) (hr : 0<r)
    (x y : V) (hx : t≤G.degree x) (hy : t≤G.degree y) :
    ∃p : G.Walk x y,p.IsPath ∧ p.length≤Fintype.card V/r+3 := by
  have hdiv:=Nat.lt_mul_div_succ (Fintype.card V) hr
  obtain ⟨p,hp⟩:=exists_walk_of_robust_growth G r t (Fintype.card V/r+1) hrobust hr
    (by nlinarith only [hdiv]) x y hx hy
  exact ⟨p.bypass,p.bypass_isPath,(p.length_bypass_le_length.trans hp).trans (by omega)⟩

/-- Induction retains exactly the incidences to a selected vertex set. -/
theorem neighboursIn_induce_image (S : Set V) [DecidablePred (·∈S)] (A : Finset S) (v : S) :
    neighboursIn (G.induce S) A v=neighboursIn G (A.image Subtype.val) v.val := by
  rw [neighboursIn_eq_filter_card,neighboursIn_eq_filter_card,filter_image,
    card_image_of_injective _ Subtype.val_injective]
  rfl

/-- Deleting Z costs at most |Z| robust neighbours. This is a proved
inheritance statement, with both integer thresholds explicit. -/
theorem robust_induce_complement (Z : Finset V) (r r' t : ℕ)
    (hrobust : IsRobustAt G r t) (hbudget : Z.card+r'≤r) :
    IsRobustAt (G.induce ((Z : Set V)ᶜ)) r' t := by
  intro A hlo hhi
  let C : Set V:=(Z : Set V)ᶜ
  let H:=G.induce C
  let B:=A.image Subtype.val
  have hBcard : B.card=A.card := card_image_of_injective _ Subtype.val_injective
  have hCcard : Fintype.card ↥((Z : Set V)ᶜ)≤Fintype.card V :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hRN:=hrobust B (by omega) (by omega)
  have hs : neighbourhood G r B\Z⊆(neighbourhood H r' A).image Subtype.val := by
    intro v hv
    obtain ⟨hvN,hvZ⟩:=mem_sdiff.mp hv
    let w : C:=⟨v,hvZ⟩
    have hc : r≤neighboursIn G B v := (mem_filter.mp hvN).2
    have he:=neighboursIn_induce_image G C A w
    change neighboursIn H A w=neighboursIn G B v at he
    have hw : w∈neighbourhood H r' A := mem_filter.mpr ⟨mem_univ _,by omega⟩
    exact mem_image.mpr ⟨w,hw,rfl⟩
  have hcount:=card_le_card hs
  rw [card_image_of_injective _ Subtype.val_injective] at hcount
  have hdelete:=card_le_card_sdiff_add_card (s:=neighbourhood G r B) (t:=Z)
  change A.card+r'≤(neighbourhood H r' A).card
  omega

/-- A genuine simple path avoids every prescribed forbidden vertex.
Only its two endpoints need the degree reserve t+|Z|. -/
theorem exists_short_path_avoiding (Z : Finset V) (r r' t : ℕ)
    (hrobust : IsRobustAt G r t) (hr' : 0<r') (hbudget : Z.card+r'≤r)
    (x y : V) (hxZ : x∉Z) (hyZ : y∉Z)
    (hx : t+Z.card≤G.degree x) (hy : t+Z.card≤G.degree y) :
    ∃p : G.Walk x y,p.IsPath ∧ p.length≤Fintype.card V/r'+3 ∧
      ∀v∈p.support,v∉Z := by
  let C : Set V:=(Z : Set V)ᶜ
  let H:=G.induce C
  let x' : C:=⟨x,hxZ⟩
  let y' : C:=⟨y,hyZ⟩
  have hR : IsRobustAt H r' t:=robust_induce_complement G Z r r' t hrobust hbudget
  have hx' : t≤H.degree x' := by
    have hd:=SparseDeficitCore.degree_le_induce_compl_add_card G Z x'
    change G.degree x≤H.degree x'+Z.card at hd
    omega
  have hy' : t≤H.degree y' := by
    have hd:=SparseDeficitCore.degree_le_induce_compl_add_card G Z y'
    change G.degree y≤H.degree y'+Z.card at hd
    omega
  obtain ⟨p,hp,hlen⟩:=exists_short_path H r' t hR hr' x' y' hx' hy'
  let f : H →g G:={ toFun:=Subtype.val,map_rel':=fun h => h }
  have hf : Function.Injective f:=Subtype.val_injective
  refine ⟨p.map f,hp.map hf,?_,?_⟩
  · rw [Walk.length_map]
    have hc : Fintype.card C≤Fintype.card V := Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    exact hlen.trans (Nat.add_le_add_right (Nat.div_le_div_right hc) 3)
  · intro v hv
    rw [Walk.support_map,List.mem_map] at hv
    obtain ⟨w,_,rfl⟩:=hv
    exact w.property

end OverfullWork.RobustShortPaths
