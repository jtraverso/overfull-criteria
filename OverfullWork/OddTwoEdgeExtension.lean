module

public import OverfullWork.NearTightOddSetGeometry
public import OverfullWork.Critical
public import Mathlib.Data.Finset.Option
public import Mathlib.Algebra.BigOperators.Option

@[expose] public section


/-! # A real even-order extension of a connected odd graph

Adjoin one vertex and join it to two distinct deficient vertices.
Connectedness and odd original order prove preservation of no-overfullness;
the property of the extension is not an input. This supplies the finite
extension step in CMS Subcase 2.1, not its subsequent factorization.
The paper's choice among at least three deficient vertices serves later
canonical conditions and is unnecessary for this preservation theorem.
-/
namespace OverfullWork.OddTwoEdgeExtension
open SimpleGraph Finset OddCutDeficit
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false

def extendedAdj (G : SimpleGraph V) (a b : V) : Option V → Option V → Prop
  | none,none => False
  | none,some v => v=a ∨ v=b
  | some v,none => v=a ∨ v=b
  | some v,some w => G.Adj v w

def extension (G : SimpleGraph V) (a b : V) : SimpleGraph (Option V) where
  Adj:=extendedAdj G a b
  symm:=⟨by intro u v h;cases u <;> cases v <;> simp_all [extendedAdj,G.adj_comm]⟩
  loopless:=⟨by intro u;cases u <;> simp [extendedAdj]⟩

@[simp] theorem adj_new_new (G : SimpleGraph V) (a b : V) :
    ¬(extension G a b).Adj none none := id
@[simp] theorem adj_new_old (G : SimpleGraph V) (a b v : V) :
    (extension G a b).Adj none (some v) ↔ v=a ∨ v=b := Iff.rfl
@[simp] theorem adj_old_new (G : SimpleGraph V) (a b v : V) :
    (extension G a b).Adj (some v) none ↔ v=a ∨ v=b := Iff.rfl
@[simp] theorem adj_old_old (G : SimpleGraph V) (a b v w : V) :
    (extension G a b).Adj (some v) (some w) ↔ G.Adj v w := Iff.rfl

def oldCopy (G : SimpleGraph V) (a b : V) : Copy G (extension G a b) where
  toHom:={toFun:=some,map_rel':=fun h => h}
  injective':=Option.some_injective _

private theorem sum_option_set (S : Finset (Option V)) (f : Option V → ℕ) :
    (∑v∈S,f v)=(if none∈S then f none else 0)+∑v∈S.eraseNone,f (some v) := by
  have hm : (∑v∈S.erase none,f v)=∑v∈S.eraseNone,f (some v) := by
    rw [←map_some_eraseNone,Finset.sum_map]
    rfl
  by_cases hn : none∈S
  · have hs:=sum_erase_add S f hn
    rw [hm] at hs
    rw [if_pos hn]
    omega
  · rw [erase_eq_of_notMem hn] at hm
    simp only [if_neg hn,zero_add]
    exact hm

private theorem degree_eq_sum_adj (K : SimpleGraph V) [DecidableRel K.Adj] (v : V) :
    K.degree v=∑w:V,if K.Adj v w then 1 else 0 := by
  rw [←card_neighborFinset_eq_degree,←card_filter]
  congr 1
  ext w
  simp

private theorem selected_sum (a b : V) (hab : a≠b) (T : Finset V) :
    (∑v∈T,if v=a ∨ v=b then 1 else 0)=
      (if a∈T then 1 else 0)+(if b∈T then 1 else 0) := by
  have hrow : ∀v:V,(if v=a ∨ v=b then 1 else 0)=
      (if v=a then 1 else 0)+(if v=b then 1 else 0) := by
    intro v
    by_cases ha:v=a <;> by_cases hb:v=b <;> simp_all
  simp_rw [hrow]
  rw [sum_add_distrib]
  simp

theorem degree_new (G : SimpleGraph V) (a b : V) (hab : a≠b) :
    (extension G a b).degree none=2 := by
  rw [degree_eq_sum_adj]
  simp only [Fintype.sum_option,adj_new_new,if_false,adj_new_old,zero_add]
  have hs:=selected_sum a b hab (univ : Finset V)
  simpa only [mem_univ,if_true] using hs

theorem degree_old (G : SimpleGraph V) [DecidableRel G.Adj] (a b v : V) :
    (extension G a b).degree (some v)=G.degree v+(if v=a ∨ v=b then 1 else 0) := by
  rw [degree_eq_sum_adj,Fintype.sum_option,degree_eq_sum_adj]
  simp only [adj_old_new,adj_old_old]
  omega

theorem maxDegree_eq (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V)
    (hab : a≠b) (hD : 2≤G.maxDegree)
    (ha : G.degree a<G.maxDegree) (hb : G.degree b<G.maxDegree) :
    (extension G a b).maxDegree=G.maxDegree := by
  apply le_antisymm
  · apply (extension G a b).maxDegree_le_of_forall_degree_le
    intro v
    cases v with
    | none => rw [degree_new G a b hab];exact hD
    | some v =>
      rw [degree_old G a b v]
      by_cases hv : v=a ∨ v=b
      · rw [if_pos hv]
        rcases hv with rfl|rfl <;> omega
      · rw [if_neg hv,Nat.add_zero]
        exact G.degree_le_maxDegree v
  · exact (oldCopy G a b).maxDegree_mono

private theorem twice_internal_sum (K : SimpleGraph V) [DecidableRel K.Adj] (S : Finset V) :
    2*internalEdges K S=∑v∈S,∑w∈S,if K.Adj v w then 1 else 0 := by
  rw [internalEdges_eq_multigraph,←MultiGraph.twiceInternal_eq]
  simp only [MultiGraph.twiceInternal,MultiGraph.ofSimpleGraph,mem_edgeSet]

theorem internal_count (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) (hab : a≠b) (S : Finset (Option V)) :
    2*internalEdges (extension G a b) S=2*internalEdges G S.eraseNone+
      2*(if none∈S then (if a∈S.eraseNone then 1 else 0)+(if b∈S.eraseNone then 1 else 0) else 0) := by
  let T:=S.eraseNone
  let k:=(if a∈T then 1 else 0)+(if b∈T then 1 else 0)
  have hn : (∑v∈S,if (extension G a b).Adj none v then 1 else 0)=k := by
    rw [sum_option_set]
    simp only [adj_new_new,if_false,adj_new_old,ite_self,zero_add]
    exact selected_sum a b hab T
  have hv : ∀v:V,(∑w∈S,if (extension G a b).Adj (some v) w then 1 else 0)=
      (if none∈S then (if v=a ∨ v=b then 1 else 0) else 0)+
        ∑w∈T,if G.Adj v w then 1 else 0 := by
    intro v
    rw [sum_option_set]
    simp only [adj_old_new,adj_old_old]
    rfl
  rw [twice_internal_sum,twice_internal_sum,sum_option_set,hn]
  simp_rw [hv]
  rw [sum_add_distrib]
  have hs:=selected_sum a b hab T
  change (if none∈S then k else 0)+
    ((∑v∈T,if none∈S then (if v=a ∨ v=b then 1 else 0) else 0)+
      ∑v∈T,∑w∈T,if G.Adj v w then 1 else 0)=_
  by_cases h : none∈S
  · simp only [if_pos h]
    change k+((∑v∈T,if v=a ∨ v=b then 1 else 0)+_)=_+2*k
    rw [hs]
    dsimp only [k,T] at *
    omega
  · simp only [if_neg h,sum_const_zero,Nat.zero_add,Nat.mul_zero,Nat.add_zero]
    rfl

theorem cut_positive (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (T : Finset V) (hne : T.Nonempty) (hproper : T≠univ) : 0<cutEdges G T := by
  by_contra hn
  have hz : cutEdges G T=0 := by omega
  have hclosed : ∀u∈T,∀v,G.Adj u v → v∈T := by
    intro u hu v huv
    by_contra hv
    have hp : (u,v)∈crossingEdges G T := by
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hu,mem_compl.mpr hv⟩,huv⟩
    have hc : 0<cutEdges G T:=card_pos.mpr ⟨(u,v),hp⟩
    omega
  obtain ⟨x,hx⟩:=hne
  have hall : ∀y:V,y∈T := by
    intro y
    obtain ⟨p⟩:=hconn.preconnected x y
    have aux : ∀{u v},(p : G.Walk u v) → u∈T → v∈T := by
      intro u v p
      induction p with
      | nil => exact id
      | @cons u v w huv p ih => exact fun hu => ih (hclosed u hu v huv)
    exact aux p hx
  exact hproper (eq_univ_of_forall hall)

theorem selected_deficit_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) (hab : a≠b)
    (ha : G.degree a<G.maxDegree) (hb : G.degree b<G.maxDegree) (T : Finset V) :
    (if a∈T then 1 else 0)+(if b∈T then 1 else 0)≤deficitMass G G.maxDegree T := by
  rw [←selected_sum a b hab]
  apply sum_le_sum
  intro v _
  by_cases hv : v=a ∨ v=b
  · rw [if_pos hv]
    rcases hv with rfl|rfl <;> omega
  · rw [if_neg hv]
    exact Nat.zero_le _

/-- The two-edge extension preserves the actual no-overfull property.
The connectedness assumption is used only for a proper even old set containing
both attachment vertices, where its nonempty cut supplies the final unit. -/
theorem no_overfull (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hodd : Odd (Fintype.card V))
    (a b : V) (hab : a≠b) (hD : 2≤G.maxDegree)
    (ha : G.degree a<G.maxDegree) (hb : G.degree b<G.maxDegree)
    (hno : ¬G.HasOverfullSubgraph) : ¬(extension G a b).HasOverfullSubgraph := by
  have hmax:=maxDegree_eq G a b hab hD ha hb
  have hdeg : ∀v,(extension G a b).degree v≤G.maxDegree := by
    intro v
    simpa only [hmax] using (extension G a b).degree_le_maxDegree v
  rintro ⟨S,hS⟩
  change (extension G a b).maxDegree*(S.card/2)< internalEdges (extension G a b) S at hS
  rw [hmax] at hS
  by_cases hsodd : Odd S.card
  · by_cases hn : none∈S
    · let T:=S.eraseNone
      let k:=(if a∈T then 1 else 0)+(if b∈T then 1 else 0)
      obtain ⟨m,hm⟩:=hsodd
      have hSn : 0<S.card:=card_pos.mpr ⟨none,hn⟩
      have hTc : T.card=2*m := by
        have hc:=card_eraseNone_of_mem hn
        change T.card=S.card-1 at hc
        omega
      have hhalf : S.card/2=m:=by omega
      rw [hhalf] at hS
      have hid:=internal_cut_deficit_identity G G.maxDegree G.degree_le_maxDegree T
      have he : G.maxDegree*T.card=2*(G.maxDegree*m) := by rw [hTc];ring
      rw [he] at hid
      have hkdef:=selected_deficit_le G a b hab ha hb T
      change k≤deficitMass G G.maxDegree T at hkdef
      have hk : k≤2 := by dsimp only [k];split_ifs <;> omega
      have hcount:=internal_count G a b hab S
      rw [if_pos hn] at hcount
      change 2*internalEdges (extension G a b) S=2*internalEdges G T+2*k at hcount
      by_cases hkone : k≤1
      · omega
      · have hktwo : k=2:=by omega
        have haT : a∈T := by
          by_contra h
          dsimp only [k] at hktwo
          rw [if_neg h] at hktwo
          split_ifs at hktwo <;> omega
        have hproper : T≠univ := by
          intro hT
          have hc:=congrArg Finset.card hT
          simp only [card_univ] at hc
          obtain ⟨j,hj⟩:=hodd
          omega
        have hcut:=cut_positive G hconn T ⟨a,haT⟩ hproper
        omega
    · have hcount:=internal_count G a b hab S
      rw [if_neg hn] at hcount
      have hc:=card_eraseNone_of_not_mem hn
      have hbase : internalEdges G S.eraseNone≤G.maxDegree*(S.eraseNone.card/2) := by
        by_contra hh
        exact hno ⟨S.eraseNone,Nat.lt_of_not_ge hh⟩
      rw [hc] at hbase
      omega
  · have heven:=Nat.not_odd_iff_even.mp hsodd
    have hbnd:=even_internal_bound (extension G a b) G.maxDegree hdeg S heven
    omega

theorem even_order (hodd : Odd (Fintype.card V)) : Even (Fintype.card (Option V)) := by
  rw [Fintype.card_option]
  obtain ⟨m,hm⟩:=hodd
  exact ⟨m+1,by omega⟩

/-- Restriction uses the actual embedded old graph, for every palette. -/
theorem colourable_restrict (G : SimpleGraph V) (a b : V) {k : ℕ}
    (hc : (extension G a b).EdgeColorable k) : G.EdgeColorable k :=
  Critical.colourable_of_copy (oldCopy G a b) hc

theorem not_colourable (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) (hab : a≠b) (hD : 2≤G.maxDegree)
    (ha : G.degree a<G.maxDegree) (hb : G.degree b<G.maxDegree)
    (hnc : ¬G.EdgeColorable G.maxDegree) :
    ¬(extension G a b).EdgeColorable (extension G a b).maxDegree := by
  intro hc
  rw [maxDegree_eq G a b hab hD ha hb] at hc
  exact hnc (colourable_restrict G a b hc)

/-- The actual even simple extension of an odd critical no-overfull graph.
Criticality is required only of the source; no criticality of the extension
is asserted. The chosen vertices are genuinely deficient in the source. -/
theorem critical_properties (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) (hodd : Odd (Fintype.card V))
    (a b : V) (hab : a≠b) (hD : 2≤G.maxDegree)
    (ha : G.degree a<G.maxDegree) (hb : G.degree b<G.maxDegree)
    (hno : ¬G.HasOverfullSubgraph) :
    Even (Fintype.card (Option V)) ∧
    (extension G a b).maxDegree=G.maxDegree ∧
    ¬(extension G a b).HasOverfullSubgraph ∧
    ¬(extension G a b).EdgeColorable (extension G a b).maxDegree := by
  exact ⟨even_order hodd,maxDegree_eq G a b hab hD ha hb,
    no_overfull G hc.1 hodd a b hab hD ha hb hno,
    not_colourable G a b hab hD ha hb hc.2.1⟩

end OverfullWork.OddTwoEdgeExtension
