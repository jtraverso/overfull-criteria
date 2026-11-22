module

public import OverfullWork.MaximumCoreProfile
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section


/-! # A large almost-regular induced set from total deficit mass

These finite estimates do not assume an average-degree theorem for critical
graphs. They expose exactly the counting and vertex-deletion costs needed
to use such a theorem if it becomes available.
-/
namespace OverfullWork.SparseDeficitCore
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def totalDeficit (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) : ℕ :=
  ∑v : V,(D-G.degree v)

def exceptions (G : SimpleGraph V) [DecidableRel G.Adj] (D t : ℕ) : Finset V :=
  univ.filter fun v => G.degree v+t<D

omit [DecidableEq V] in
/-- A first-moment tail bound; no criticality or maximum-gap assumption. -/
theorem exception_count_le_mass (G : SimpleGraph V) [DecidableRel G.Adj] (D t : ℕ) :
    (t+1)*(exceptions G D t).card≤totalDeficit G D := by
  let U:=exceptions G D t
  have hp : ∀v∈U,t+1≤D-G.degree v := by
    intro v hv
    have hh:=(mem_filter.mp hv).2
    omega
  calc
    _ = ∑_v∈U,(t+1) := by simp [U,Nat.mul_comm]
    _ ≤ ∑v∈U,(D-G.degree v) := sum_le_sum hp
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ U) (fun _ _ _ => Nat.zero_le _)

omit [DecidableEq V] in
theorem degree_sum_add_deficit (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ) (hD : ∀v,G.degree v≤D) :
    (∑v : V,G.degree v)+totalDeficit G D=D*Fintype.card V := by
  rw [totalDeficit,←sum_add_distrib]
  calc
    _ = ∑_v : V,D := sum_congr rfl (fun v _ => Nat.add_sub_of_le (hD v))
    _ = _ := by simp [Nat.mul_comm]

omit [DecidableEq V] in
/-- A bound on average deficit expressed without divisions or real casts. -/
theorem totalDeficit_le_iff_degree_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (D B : ℕ) (hD : ∀v,G.degree v≤D) :
    totalDeficit G D≤B ↔ D*Fintype.card V≤(∑v : V,G.degree v)+B := by
  have h:=degree_sum_add_deficit G D hD
  omega

omit [DecidableEq V] in
theorem degree_add_threshold_of_not_exception (G : SimpleGraph V)
    [DecidableRel G.Adj] (D t : ℕ) (v : V) (hv : v∉exceptions G D t) :
    D≤G.degree v+t := by
  simpa only [exceptions,mem_filter,mem_univ,true_and,not_lt] using hv

/-- At most one incident edge is lost per deleted vertex. -/
theorem degree_le_induce_compl_add_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (v : {x : V // x∉U}) :
    G.degree v.val≤(G.induce ((U : Set V)ᶜ)).degree v+U.card := by
  have hm:=congrArg Finset.card (G.map_neighborFinset_induce (s:=((U : Set V)ᶜ)) v)
  rw [card_map,card_neighborFinset_eq_degree] at hm
  have he : G.neighborFinset v.val∩((U : Set V)ᶜ).toFinset=G.neighborFinset v.val\U := by
    ext x
    simp
  rw [he] at hm
  have hc:=Finset.card_le_card_sdiff_add_card (s:=G.neighborFinset v.val) (t:=U)
  rw [G.card_neighborFinset_eq_degree,←hm] at hc
  exact hc

theorem degree_induce_compl_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (D t : ℕ) (U : Finset V) (hgood : ∀v∉U,D≤G.degree v+t)
    (v : {x : V // x∉U}) :
    D-t-U.card≤(G.induce ((U : Set V)ᶜ)).degree v := by
  have hd:=degree_le_induce_compl_add_card G U v
  have hg:=hgood v.val (by simpa using v.property)
  omega

theorem minDegree_induce_compl_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (D t : ℕ) (U : Finset V) (hDcard : D≤Fintype.card V)
    (hgood : ∀v∉U,D≤G.degree v+t) :
    D-t-U.card≤(G.induce ((U : Set V)ᶜ)).minDegree := by
  by_cases hne : (Uᶜ : Finset V).Nonempty
  · let : Nonempty ↥((U : Set V)ᶜ) := ⟨⟨hne.choose,by simpa using hne.choose_spec⟩⟩
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    exact degree_induce_compl_lower G D t U hgood
  · have hU : U=univ := by
      have hc : Uᶜ=(∅ : Finset V) := not_nonempty_iff_eq_empty.mp hne
      simpa only [compl_empty,compl_compl] using congrArg (fun T : Finset V => Tᶜ) hc
    simp only [hU,card_univ]
    omega

omit [DecidableEq V] in
/-- Low-degree exceptions are independent whenever every edge obeys weak VAL. -/
theorem exceptions_independent_of_weakVAL (G : SimpleGraph V) [DecidableRel G.Adj]
    (D t : ℕ) (hweak : ∀u v,G.Adj u v → D<G.degree u+G.degree v)
    (hthreshold : 2*(D-t-1)≤D) : G.IsIndepSet (exceptions G D t : Set V) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro u hu v hv _ huv
  have huD : G.degree u+t<D := (mem_filter.mp hu).2
  have hvD : G.degree v+t<D := (mem_filter.mp hv).2
  have huB : G.degree u≤D-t-1 := by omega
  have hvB : G.degree v≤D-t-1 := by omega
  have hh:=hweak u v huv
  omega

theorem critical_exceptions_independent (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (t : ℕ)
    (hthreshold : 2*(G.maxDegree-t-1)≤G.maxDegree) :
    G.IsIndepSet (exceptions G G.maxDegree t : Set V) := by
  apply exceptions_independent_of_weakVAL G G.maxDegree t _ hthreshold
  intro u v huv
  have hh:=Overfull.deg_add hcrit huv
  omega

theorem minDegree_outside_exceptions (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ) :
    G.maxDegree-t-(exceptions G G.maxDegree t).card≤
      (G.induce ((exceptions G G.maxDegree t : Set V)ᶜ)).minDegree := by
  apply minDegree_induce_compl_lower G G.maxDegree t (exceptions G G.maxDegree t)
  · exact G.maxDegree_le_of_forall_degree_le _ (fun v => (G.degree_lt_card_verts v).le)
  · exact degree_add_threshold_of_not_exception G G.maxDegree t

/-- The induced complement has an explicit degree-gap bound. This does not
assert that its colouring extends across the deleted vertices. -/
theorem gap_outside_exceptions (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ) :
    (G.induce ((exceptions G G.maxDegree t : Set V)ᶜ)).maxDegree-
      (G.induce ((exceptions G G.maxDegree t : Set V)ᶜ)).minDegree≤
        t+(exceptions G G.maxDegree t).card := by
  have hlo:=minDegree_outside_exceptions G t
  have hhi:=(Copy.induce G ((exceptions G G.maxDegree t : Set V)ᶜ)).maxDegree_mono
  omega

end OverfullWork.SparseDeficitCore
