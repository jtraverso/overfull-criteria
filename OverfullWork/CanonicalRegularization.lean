module

public import OverfullWork.CanonicalOrderedProfile
public import OverfullWork.CanonicalPairTriangle

@[expose] public section


/-! # Actual canonical completion of an ordered multigraph

CMS Definition 4.1 is constructed from the admissible ordered deficiency
sequence. Both auxiliary edge layers are real: the bipartite half-edge
realization L and the explicit weighted-pair/triangle layer N. Their
additive union with D is regular; no factorization is asserted.
-/
namespace OverfullWork.CanonicalRegularization
open SimpleGraph Finset CanonicalDeficitCut CanonicalOrderedProfile CanonicalPairTriangle
open scoped Classical
set_option maxHeartbeats 10000000

def prefixEmbedding {m k : ℕ} (hk : k≤m) : (Fin k×Bool) ↪ (Fin m×Bool) where
  toFun z:=(⟨z.1.val,z.1.isLt.trans_le hk⟩,z.2)
  inj' := by
    intro a b he
    apply Prod.ext
    · exact Fin.ext (congrArg (fun z : Fin m×Bool=>z.1.val) he)
    · exact congrArg (fun z : Fin m×Bool=>z.2) he

def pairResidue {m k : ℕ} (D : MultiGraph (Fin m×Bool)) (Δ : ℕ) (hk : k≤m) (i : Fin k) : ℕ :=
  Δ-D.degree (prefixEmbedding hk (i,true))

/-- The canonical N phase is the explicit pair graph when the prefix is
full, and the explicit pair-plus-triangle graph otherwise. -/
def IsCanonicalN {m k : ℕ} (D : MultiGraph (Fin m×Bool)) (Δ : ℕ)
    (hkpos : 1≤k) (hk : k≤m) (q : ℕ) (N : MultiGraph (Fin m×Bool)) : Prop :=
  (k=m → N=weightedPairs (prefixEmbedding hk) (pairResidue D Δ hk)) ∧
  (∀hkm : k<m,∃hw : ∀z,(⟨k,hkm⟩,false)≠prefixEmbedding hk z,
    N=pairTriangle (prefixEmbedding hk) (pairResidue D Δ hk) ⟨k-1,by omega⟩
      (⟨k,hkm⟩,false) hw q)

structure Completion {m : ℕ} (D : MultiGraph (Fin m×Bool)) (Δ : ℕ) where
  k : ℕ
  positive : 1≤k
  cut_le : k≤m
  q : ℕ
  L : MultiGraph (Fin m×Bool)
  N : MultiGraph (Fin m×Bool)
  regular : ((D.addCopies L).addCopies N).IsRegularOfDegree Δ
  additions_bounded : ∀v,L.degree v≤Δ-D.degree v
  prefix_degrees : ∀i : Fin m,i.val<k →
    L.degree (i,false)=(Δ-D.degree (i,false))-(Δ-D.degree (i,true)) ∧ L.degree (i,true)=0
  middle_degrees : ∀i : Fin m,i.val=k → L.degree (i,false)+2*q=Δ-D.degree (i,false)
  tail_odd_degrees : ∀i : Fin m,k < i.val → L.degree (i,false)=Δ-D.degree (i,false)
  tail_even_degrees : ∀i : Fin m,k ≤ i.val → L.degree (i,true)=Δ-D.degree (i,true)
  middle_bound : q≤pairResidue D Δ cut_le ⟨k-1,by omega⟩
  paired_q_zero : k=m→q=0
  bipartite : ∃P : Finset (Fin m×Bool),
    (∀i : Fin m,i.val<k → (i,false)∈P ∧ (i,true)∈P) ∧
    (∀i : Fin m,k < i.val → (i,false)∉P ∧ (i,true)∉P) ∧
    (∀i : Fin m,k ≤ i.val → (i,true)∉P) ∧
    (∀u v,0<L.mult s(u,v) → (u∈P ∧ v∉P) ∨ (v∈P ∧ u∉P))
  canonical_N : IsCanonicalN D Δ positive cut_le q N

/-- Construct the full canonical completion, including both edge layers.
The degree order is expressed in consecutive pairs; it is precisely the
nondecreasing degree order used in Definition 4.1. -/
theorem exists_completion {n : ℕ} (D : MultiGraph (Fin (n+1)×Bool)) (Δ : ℕ)
    (hD : ∀v,D.degree v≤Δ)
    (hpair : ∀i : Fin (n+1),D.degree (i,false)≤D.degree (i,true))
    (horder : ∀i j : Fin (n+1),i.val<j.val → D.degree (i,true)≤D.degree (j,false))
    (heven : Even (∑v : Fin (n+1)×Bool,(Δ-D.degree v)))
    (hbalance : 2*(Δ-D.degree (0,false))≤∑v : Fin (n+1)×Bool,(Δ-D.degree v)) :
    Nonempty (Completion D Δ) := by
  let a:=fun i : Fin (n+1)=>Δ-D.degree (i,false)
  let b:=fun i : Fin (n+1)=>Δ-D.degree (i,true)
  obtain ⟨T,hT⟩:=heven
  have htotal : (∑i : Fin (n+1),(a i+b i))=2*T := by
    have hs : (∑v : Fin (n+1)×Bool,(Δ-D.degree v))=∑i : Fin (n+1),(a i+b i) := by
      rw [Fintype.sum_prod_type]
      apply sum_congr rfl
      intro i _
      simp only [Fintype.sum_bool,a,b]
      omega
    omega
  have hab : ∀i,b i≤a i := fun i=>Nat.sub_le_sub_left (hpair i) Δ
  have hfirst : a 0≤T := by
    change 2*a 0≤_ at hbalance
    omega
  obtain ⟨k,q,L,hkpos,hk,hprefix,hmid,htailO,htailE,hqentry,hqzero,hL,hbip⟩:=
    exists_ordered_realization a b T hab hfirst htotal
  have haborder : ∀i j : Fin (n+1),i.val<j.val → a j≤b i := by
    intro i j hij
    exact Nat.sub_le_sub_left (horder i j hij) Δ
  let e:=prefixEmbedding hk
  let r:=pairResidue D Δ hk
  let Dplus:=D.addCopies L
  have hbound : ∀v,Dplus.degree v≤Δ := by
    intro v
    rw [MultiGraph.degree_addCopies]
    have hv:=hD v
    have hl:=hL v
    rcases v with ⟨i,c⟩
    cases c <;> simp only [Bool.true_eq_false,if_false,if_true] at hl <;>
      dsimp [a,b] at hl <;> omega
  have hres : ∀i c,Δ-Dplus.degree (e (i,c))=r i := by
    intro i c
    let j : Fin (n+1):=⟨i.val,i.isLt.trans_le hk⟩
    have hj : j.val<k:=i.isLt
    obtain ⟨ho,he⟩:=hprefix j hj
    have ha:=hD (j,false)
    have hb:=hD (j,true)
    have hd:=hab j
    rw [MultiGraph.degree_addCopies]
    change Δ-(D.degree (j,c)+L.degree (j,c))=b j
    cases c
    · rw [ho]
      dsimp [a,b] at hd ⊢
      omega
    · rw [he]
      rfl
  have hq : q≤r ⟨k-1,by omega⟩ := by
    have he:=middle_le_last_pair a b haborder k hkpos hk
    exact hqentry.trans he
  by_cases hkm:k=n+1
  · let N:=weightedPairs e r
    have hrest : ∀v,(∀z,v≠e z) → Dplus.degree v=Δ := by
      rintro ⟨i,c⟩ hv
      let j : Fin k:=⟨i.val,by omega⟩
      exact False.elim (hv (j,c) (by rfl))
    have hreg:=weightedPairs_regularizes Dplus e r Δ hbound hres hrest
    refine ⟨{
      k:=k,positive:=hkpos,cut_le:=hk,q:=q,L:=L,N:=N,regular:=hreg,
      additions_bounded:=?_,prefix_degrees:=hprefix,middle_degrees:=hmid,
      tail_odd_degrees:=htailO,tail_even_degrees:=htailE,middle_bound:=hq,
      paired_q_zero:=hqzero,bipartite:=hbip,canonical_N:=?_ }⟩
    · intro v
      have hh:=hL v
      rcases v with ⟨i,c⟩
      cases c <;> simpa [a,b] using hh
    · constructor
      · intro _;rfl
      · intro hlt;omega
  · have hlt : k<n+1:=by omega
    let w : Fin (n+1)×Bool:=(⟨k,hlt⟩,false)
    have hw : ∀z,w≠e z := by
      intro z he
      have hi:=congrArg (fun v : Fin (n+1)×Bool=>v.1.val) he
      change k=z.1.val at hi
      have hh:=z.1.isLt
      omega
    let N:=pairTriangle e r ⟨k-1,by omega⟩ w hw q
    have hmiddle : Δ-Dplus.degree w=2*q := by
      have hm:=hmid ⟨k,hlt⟩ rfl
      have hd:=hD w
      change L.degree w+2*q=a ⟨k,hlt⟩ at hm
      rw [MultiGraph.degree_addCopies]
      change Δ-(D.degree w+L.degree w)=2*q
      change L.degree w+2*q=Δ-D.degree w at hm
      omega
    have hrest : ∀v,(∀z,v≠e z) → v≠w → Dplus.degree v=Δ := by
      rintro ⟨i,c⟩ hv hvw
      have hik : k ≤ i.val := by
        by_contra hh
        have hik:i.val<k:=by omega
        exact hv (⟨i.val,hik⟩,c) (by rfl)
      cases c
      · have hi:k < i.val := by
          by_contra hh
          have he:i.val=k:=by omega
          exact hvw (Prod.ext (Fin.ext he) rfl)
        have hl:=htailO i hi
        have hd:=hD (i,false)
        rw [MultiGraph.degree_addCopies]
        change D.degree (i,false)+L.degree (i,false)=Δ
        rw [hl]
        exact Nat.add_sub_of_le hd
      · have hl:=htailE i hik
        have hd:=hD (i,true)
        rw [MultiGraph.degree_addCopies]
        change D.degree (i,true)+L.degree (i,true)=Δ
        rw [hl]
        exact Nat.add_sub_of_le hd
    have hreg:=pairTriangle_regularizes Dplus e r ⟨k-1,by omega⟩ w hw q Δ
      hq hbound hres hmiddle hrest
    refine ⟨{
      k:=k,positive:=hkpos,cut_le:=hk,q:=q,L:=L,N:=N,regular:=hreg,
      additions_bounded:=?_,prefix_degrees:=hprefix,middle_degrees:=hmid,
      tail_odd_degrees:=htailO,tail_even_degrees:=htailE,middle_bound:=hq,
      paired_q_zero:=hqzero,bipartite:=hbip,canonical_N:=?_ }⟩
    · intro v
      have hh:=hL v
      rcases v with ⟨i,c⟩
      cases c <;> simpa [a,b] using hh
    · constructor
      · intro he;omega
      · intro hlt'
        refine ⟨hw,?_⟩
        rfl

end OverfullWork.CanonicalRegularization
