module

public import OverfullWork.CanonicalDeficitCut

@[expose] public section


/-! # The bipartite ordered-deficit phase of canonical completion

The cut and every degree are constructed from the ordered pair sequence.
Only a prefix of complete pairs and at most one even middle deficit remain.
-/
namespace OverfullWork.CanonicalOrderedProfile
open SimpleGraph Finset CanonicalDeficitCut
open scoped Classical
set_option maxHeartbeats 8000000

noncomputable def profile {n : ℕ} (a b : Fin n→ℕ) (k t : ℕ) (v : Fin n×Bool) : ℕ :=
  if v.1.val<k then (if v.2=false then a v.1-b v.1 else 0)
  else if v.1.val=k ∧ v.2=false then t
  else if v.2=false then a v.1 else b v.1

noncomputable def leftPart {n : ℕ} (k : ℕ) (left : Prop) [Decidable left] : Finset (Fin n×Bool) :=
  univ.filter fun v=>v.1.val<k ∨ (v.1.val=k ∧ v.2=false ∧ left)

private theorem prefix_difference {n : ℕ} (a b : Fin n→ℕ) (k : ℕ)
    (hpair : ∀i,b i≤a i) :
    (∑i : Fin n,if i.val<k then a i-b i else 0)+prefixMass b k=prefixMass a k := by
  unfold prefixMass
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro i _
  have hh:=hpair i
  split_ifs <;> omega

private theorem middle_sum {n : ℕ} (t k : ℕ) (hk : k≤n) (hzero : k=n→t=0) :
    (∑i : Fin n,if i.val=k then t else 0)=t := by
  by_cases hkn:k<n
  · exact entry_eq (fun _ : Fin n=>t) ⟨k,hkn⟩
  · have he:k=n:=by omega
    simp [hzero he]

private theorem left_sum {n : ℕ} (a b : Fin n→ℕ) (k t : ℕ) (left : Prop) [Decidable left]
    (hk : k≤n) (hzero : k=n→t=0) :
    (∑v∈leftPart (n:=n) k left,profile a b k t v)=
      (∑i : Fin n,if i.val<k then a i-b i else 0)+(if left then t else 0) := by
  rw [leftPart,sum_filter,Fintype.sum_prod_type]
  have hp : ∀i : Fin n,
      (∑c : Bool,if i.val<k ∨ (i.val=k ∧ c=false ∧ left) then profile a b k t (i,c) else 0)=
      (if i.val<k then a i-b i else 0)+(if left then (if i.val=k then t else 0) else 0) := by
    intro i
    by_cases hi:i.val<k <;> by_cases he:i.val=k <;> by_cases hl:left <;>
      simp [profile,hi,he,hl]
  rw [sum_congr rfl (fun i _=>hp i),sum_add_distrib]
  congr 1
  by_cases hl:left
  · simp only [if_pos hl]
    exact middle_sum t k hk hzero
  · simp [hl]

private theorem total_sum {n : ℕ} (a b : Fin n→ℕ) (k t : ℕ)
    (hpair : ∀i,b i≤a i) (hk : k≤n) (hzero : k=n→t=0) :
    (∑v : Fin n×Bool,profile a b k t v)+2*prefixMass b k+entry a k=
      (∑i,(a i+b i))+t := by
  rw [Fintype.sum_prod_type]
  have hp : ∀i : Fin n,
      (∑c : Bool,profile a b k t (i,c))+
        2*(if i.val<k then b i else 0)+(if i.val=k then a i else 0)=
      a i+b i+(if i.val=k then t else 0) := by
    intro i
    have hh:=hpair i
    by_cases hi:i.val<k
    · have he:i.val≠k:=by omega
      simp only [Fintype.sum_bool,profile,hi,he,if_pos,if_false,false_and,
        Bool.true_eq_false,zero_add]
      omega
    · by_cases he:i.val=k <;>
        simp [profile,hi,he] <;> omega
  have hs:=sum_congr (s₁:=univ) rfl (fun i _=>hp i)
  simp only [sum_add_distrib,←mul_sum] at hs
  change (∑i : Fin n,∑c : Bool,profile a b k t (i,c))+2*prefixMass b k+entry a k=
      (∑i,(a i+b i))+t
  have hm:=middle_sum t k hk hzero
  simpa only [prefixMass,entry,hm,sum_add_distrib] using hs

/-- Actual CMS Lemma 3.1 degree realization on pair-indexed vertices.
The first degree is admissible and the total degree is even; no auxiliary
multigraph, cut, matching or residual shape is supplied as an input. -/
theorem exists_ordered_realization {n : ℕ} (a b : Fin (n+1)→ℕ) (T : ℕ)
    (hpair : ∀i : Fin (n+1),b i≤a i) (hfirst : a 0≤T)
    (htotal : (∑i : Fin (n+1),(a i+b i))=2*T) :
    ∃k q : ℕ,∃L : MultiGraph (Fin (n+1)×Bool),
      1≤k ∧ k≤n+1 ∧
      (∀i : Fin (n+1),i.val<k → L.degree (i,false)=a i-b i ∧ L.degree (i,true)=0) ∧
      (∀i : Fin (n+1),i.val=k → L.degree (i,false)+2*q=a i) ∧
      (∀i : Fin (n+1),k < i.val → L.degree (i,false)=a i) ∧
      (∀i : Fin (n+1),k ≤ i.val → L.degree (i,true)=b i) ∧
      q≤entry a k ∧ (k=n+1→q=0) ∧
      (∀v,L.degree v≤ if v.2=false then a v.1 else b v.1) ∧
      ∃P : Finset (Fin (n+1)×Bool),
        (∀i : Fin (n+1),i.val<k → (i,false)∈P ∧ (i,true)∈P) ∧
        (∀i : Fin (n+1),k < i.val → (i,false)∉P ∧ (i,true)∉P) ∧
        (∀i : Fin (n+1),k ≤ i.val → (i,true)∉P) ∧
        (∀u v,0<L.mult s(u,v) → (u∈P ∧ v∉P) ∨ (v∈P ∧ u∉P)) := by
  obtain ⟨k,hkpos,hk,hpre,hnext⟩:=exists_cut a b T hpair hfirst htotal
  let r:=T-prefixMass a k
  let e:=entry a k
  let left : Prop:=e≤2*r
  let t:=if left then 2*r-e else e-2*r
  let q:=min r (e-r)
  have hrel : prefixMass a k+r=T:=Nat.add_sub_of_le hpre
  have hr : r≤e := by dsimp [r,e];omega
  have hzero : k=n+1→t=0 := by
    intro hkn
    have he:e=0:=entry_eq_zero a k (by omega)
    have hr0:r=0:=by omega
    simp [t,left,he,hr0]
  have hshape : t+2*q=e := by
    dsimp [t,q,left]
    split_ifs <;> omega
  have ht : t≤e:=by omega
  have hbalance : (∑v∈leftPart (n:=n+1) k left,profile a b k t v)=
      ∑v∈(leftPart (n:=n+1) k left)ᶜ,profile a b k t v := by
    have hl:=left_sum a b k t left hk hzero
    have hs:=total_sum a b k t hpair hk hzero
    have hd:=prefix_difference a b k hpair
    have hp:=sum_add_sum_compl (leftPart (n:=n+1) k left) (profile a b k t)
    rw [htotal] at hs
    by_cases hh:left
    · rw [if_pos hh] at hl
      have hte : t=2*r-e := by simp [t,hh]
      dsimp [left] at hh
      change _+2*prefixMass b k+e=_ at hs
      omega
    · rw [if_neg hh] at hl
      have hte : t=e-2*r := by simp [t,hh]
      dsimp [left] at hh
      change _+2*prefixMass b k+e=_ at hs
      omega
  obtain ⟨L,hL,hcross,_⟩:=CanonicalBipartiteRealization.exists_realization
    (profile a b k t) (leftPart (n:=n+1) k left) hbalance
  refine ⟨k,q,L,hkpos,hk,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi
    simp [hL,profile,hi]
  · intro i hi
    have hnot : ¬i.val<k:=by omega
    have hei : e=a i := by change entry a k=a i;rw [←hi,entry_eq]
    simpa [hL,profile,hi] using hshape.trans hei
  · intro i hi
    have hnot : ¬i.val<k:=by omega
    have hne : i.val≠k:=by omega
    simp [hL,profile,hnot,hne]
  · intro i hi
    have hnot : ¬i.val<k:=by omega
    simp [hL,profile,hnot]
  · exact (min_le_left _ _).trans hr
  · intro hkn
    have he:e=0:=entry_eq_zero a k (by omega)
    have hh:=min_le_left r (e-r)
    dsimp [q]
    omega
  · intro v
    rw [hL]
    by_cases hi:v.1.val<k
    · simp only [profile,hi,if_true]
      split_ifs <;> omega
    · by_cases hm:v.1.val=k ∧ v.2=false
      · have hei : e=a v.1 := by change entry a k=a v.1;rw [←hm.1,entry_eq]
        have hh : t≤a v.1 := by simpa only [hei] using ht
        simpa [profile,hm.1,hm.2] using hh
      · simp [profile,hi,hm]
  · refine ⟨leftPart (n:=n+1) k left,?_,?_,?_,hcross⟩
    · intro i hi;simp [leftPart,hi]
    · intro i hi
      have hnot : ¬i.val<k:=by omega
      have hne : i.val≠k:=by omega
      simp [leftPart,hnot,hne]
    · intro i hi
      have hnot : ¬i.val<k:=by omega
      simp [leftPart,hnot]

/-- Global order bounds the middle entry by the residual of the last
complete pair. This is exactly the nonnegativity condition in the
triangle phase of Definition 4.1. -/
theorem middle_le_last_pair {n : ℕ} (a b : Fin (n+1)→ℕ)
    (horder : ∀i j : Fin (n+1),i.val<j.val → a j≤b i)
    (k : ℕ) (hkpos : 1≤k) (hk : k≤n+1) :
    entry a k≤b ⟨k-1,by omega⟩ := by
  by_cases hkn:k<n+1
  · have he : entry a k=a ⟨k,hkn⟩:=entry_eq a ⟨k,hkn⟩
    rw [he]
    exact horder ⟨k-1,by omega⟩ ⟨k,hkn⟩ (by change k-1<k;omega)
  · rw [entry_eq_zero a k (by omega)]
    exact Nat.zero_le _

end OverfullWork.CanonicalOrderedProfile
