module

public import OverfullWork.LooplessRealization

@[expose] public section


/-! # Actual paired and triangle completion of a canonical residual

The final edge additions in CMS Definition 4.1 are constructed as an
explicit sum of weighted pairs. One distinguished pair may give half
the middle deficit to each of two edges incident with the middle vertex.
All degrees are calculated from actual edge multiplicities.
-/
namespace OverfullWork.CanonicalPairTriangle
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 3000000

def scaledCopies (c : ℕ) (M : MultiGraph V) : MultiGraph V where
  mult e:=c*M.mult e
  loopless e he:=by rw [M.loopless e he,Nat.mul_zero]

theorem degree_scaledCopies (c : ℕ) (M : MultiGraph V) (v : V) :
    (scaledCopies c M).degree v=c*M.degree v := by
  change (∑e∈univ.filter (fun e : Sym2 V=>v∈e),c*M.mult e)=
    c*(∑e∈univ.filter (fun e : Sym2 V=>v∈e),M.mult e)
  rw [mul_sum]

def sumCopies {I : Type*} (s : Finset I) (F : I → MultiGraph V) : MultiGraph V where
  mult e:=∑i∈s,(F i).mult e
  loopless e he:=sum_eq_zero (fun i _ => (F i).loopless e he)

theorem degree_sumCopies {I : Type*} (s : Finset I) (F : I → MultiGraph V) (v : V) :
    (sumCopies s F).degree v=∑i∈s,(F i).degree v := by
  change (∑e∈univ.filter (fun e : Sym2 V=>v∈e),∑i∈s,(F i).mult e)=_
  rw [sum_comm]
  rfl

def copiesOn (a b : V) (hab : a≠b) (c : ℕ) : MultiGraph V :=
  scaledCopies c (MultiGraph.unitEdge a b hab)

theorem degree_copiesOn (a b : V) (hab : a≠b) (c : ℕ) (v : V) :
    (copiesOn a b hab c).degree v=if v=a ∨ v=b then c else 0 := by
  rw [copiesOn,degree_scaledCopies,MultiGraph.degree_unitEdge]
  split_ifs <;> simp

def weightedPairs {k : ℕ} (e : (Fin k×Bool) ↪ V) (r : Fin k → ℕ) : MultiGraph V :=
  sumCopies univ (fun i=>copiesOn (e (i,false)) (e (i,true))
    (fun h=>by have hh:=congrArg Prod.snd (e.injective h);cases hh) (r i))

theorem degree_weightedPairs {k : ℕ} (e : (Fin k×Bool) ↪ V) (r : Fin k → ℕ) (v : V) :
    (weightedPairs e r).degree v=∑i,if v=e (i,false) ∨ v=e (i,true) then r i else 0 := by
  rw [weightedPairs,degree_sumCopies]
  apply sum_congr rfl
  intro i _
  exact degree_copiesOn _ _ _ _ _

omit [Fintype V] [DecidableEq V] in
theorem pair_index_iff {k : ℕ} (e : (Fin k×Bool) ↪ V) (i j : Fin k) (b : Bool) :
    (e (i,b)=e (j,false) ∨ e (i,b)=e (j,true)) ↔ i=j := by
  constructor
  · rintro (h|h) <;> exact congrArg Prod.fst (e.injective h)
  · rintro rfl
    cases b <;> simp

theorem degree_weightedPairs_image {k : ℕ} (e : (Fin k×Bool) ↪ V) (r : Fin k → ℕ)
    (i : Fin k) (b : Bool) : (weightedPairs e r).degree (e (i,b))=r i := by
  rw [degree_weightedPairs]
  simp_rw [pair_index_iff]
  simp

theorem degree_weightedPairs_outside {k : ℕ} (e : (Fin k×Bool) ↪ V) (r : Fin k → ℕ)
    (v : V) (hv : ∀z,v≠e z) : (weightedPairs e r).degree v=0 := by
  rw [degree_weightedPairs]
  apply sum_eq_zero
  intro i _
  rw [if_neg (by exact fun h=>h.elim (hv (i,false)) (hv (i,true)))]

/-- The last pair loses q copies, and the middle vertex receives q
copies from each endpoint. The pair weights before this change are r. -/
def pairTriangle {k : ℕ} (e : (Fin k×Bool) ↪ V) (r : Fin k → ℕ)
    (j : Fin k) (w : V) (hw : ∀z,w≠e z) (q : ℕ) : MultiGraph V :=
  (weightedPairs e (fun i=>r i-(if i=j then q else 0))).addCopies
    ((copiesOn w (e (j,false)) (hw _) q).addCopies
      (copiesOn w (e (j,true)) (hw _) q))

theorem degree_pairTriangle_image {k : ℕ} (e : (Fin k×Bool) ↪ V) (r : Fin k → ℕ)
    (j : Fin k) (w : V) (hw : ∀z,w≠e z) (q : ℕ) (hq : q≤r j)
    (i : Fin k) (b : Bool) : (pairTriangle e r j w hw q).degree (e (i,b))=r i := by
  rw [pairTriangle,MultiGraph.degree_addCopies,MultiGraph.degree_addCopies,
    degree_weightedPairs_image,degree_copiesOn,degree_copiesOn]
  have hnotw : e (i,b)≠w := (hw _).symm
  by_cases hij:i=j
  · subst i
    rw [if_pos rfl]
    cases b <;> simp only [hnotw,false_or,e.injective.eq_iff,Prod.mk.injEq,true_and,
      Bool.false_eq_true,Bool.true_eq_false,if_true,if_false] <;> omega
  · rw [if_neg hij]
    have hleft:e (i,b)≠e (j,false):=fun h=>hij (congrArg Prod.fst (e.injective h))
    have hright:e (i,b)≠e (j,true):=fun h=>hij (congrArg Prod.fst (e.injective h))
    simp [hnotw,hleft,hright]

theorem degree_pairTriangle_middle {k : ℕ} (e : (Fin k×Bool) ↪ V) (r : Fin k → ℕ)
    (j : Fin k) (w : V) (hw : ∀z,w≠e z) (q : ℕ) :
    (pairTriangle e r j w hw q).degree w=2*q := by
  rw [pairTriangle,MultiGraph.degree_addCopies,MultiGraph.degree_addCopies,
    degree_weightedPairs_outside e _ w hw,degree_copiesOn,degree_copiesOn]
  simp
  omega

theorem degree_pairTriangle_outside {k : ℕ} (e : (Fin k×Bool) ↪ V) (r : Fin k → ℕ)
    (j : Fin k) (w : V) (hw : ∀z,w≠e z) (q : ℕ)
    (v : V) (hv : ∀z,v≠e z) (hvw : v≠w) :
    (pairTriangle e r j w hw q).degree v=0 := by
  rw [pairTriangle,MultiGraph.degree_addCopies,MultiGraph.degree_addCopies,
    degree_weightedPairs_outside e _ v hv,degree_copiesOn,degree_copiesOn]
  simp [hvw,hv]

/-- Actual regularization for the paired residual branch. -/
theorem weightedPairs_regularizes {k : ℕ} (D : MultiGraph V) (e : (Fin k×Bool) ↪ V)
    (r : Fin k → ℕ) (Δ : ℕ) (hD : ∀v,D.degree v≤Δ)
    (hpair : ∀i b,Δ-D.degree (e (i,b))=r i)
    (hrest : ∀v,(∀z,v≠e z) → D.degree v=Δ) :
    (D.addCopies (weightedPairs e r)).IsRegularOfDegree Δ := by
  intro v
  rw [MultiGraph.degree_addCopies]
  by_cases hv:∃z,e z=v
  · obtain ⟨⟨i,b⟩,rfl⟩:=hv
    rw [degree_weightedPairs_image,←hpair i b]
    exact Nat.add_sub_of_le (hD _)
  · have hout : ∀z,v≠e z := fun z h=>hv ⟨z,h.symm⟩
    rw [degree_weightedPairs_outside e r v hout,hrest v hout,Nat.add_zero]

/-- Actual regularization for the middle-triangle residual branch. -/
theorem pairTriangle_regularizes {k : ℕ} (D : MultiGraph V) (e : (Fin k×Bool) ↪ V)
    (r : Fin k → ℕ) (j : Fin k) (w : V) (hw : ∀z,w≠e z) (q Δ : ℕ)
    (hq : q≤r j) (hD : ∀v,D.degree v≤Δ)
    (hpair : ∀i b,Δ-D.degree (e (i,b))=r i)
    (hmid : Δ-D.degree w=2*q)
    (hrest : ∀v,(∀z,v≠e z) → v≠w → D.degree v=Δ) :
    (D.addCopies (pairTriangle e r j w hw q)).IsRegularOfDegree Δ := by
  intro v
  rw [MultiGraph.degree_addCopies]
  by_cases hv:∃z,e z=v
  · obtain ⟨⟨i,b⟩,rfl⟩:=hv
    rw [degree_pairTriangle_image e r j w hw q hq,←hpair i b]
    exact Nat.add_sub_of_le (hD _)
  · have hout : ∀z,v≠e z := fun z h=>hv ⟨z,h.symm⟩
    by_cases hvw:v=w
    · subst v
      rw [degree_pairTriangle_middle,←hmid]
      exact Nat.add_sub_of_le (hD _)
    · rw [degree_pairTriangle_outside e r j w hw q v hout hvw,hrest v hout hvw,Nat.add_zero]

end OverfullWork.CanonicalPairTriangle
