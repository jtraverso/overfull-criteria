module

public import OverfullWork.AugmentStep

@[expose] public section


/-! # Accounting identities needed for iterating the local augmentation

These are identities and bounds for arbitrary partial states. They do
not assert that the full completion invariant has been established.
-/

namespace SimpleGraph.MultiGraph

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace EdgeColoring

variable {M N : MultiGraph V} {k : ℕ}

theorem missing_internal_cut_identity (C : M.EdgeColoring k) (S : Finset V) (i : Fin k) :
    (C.missingSet S i).card+2*(C.colourGraph i).edgesWithin S+
      (C.colourGraph i).cutSize S=S.card := by
  have h:=C.missing_card_add_degree_sum S i
  have hd:=(C.colourGraph i).sum_degree_eq_internal_add_cut S
  rw [twiceInternal_eq] at hd
  omega

/-- Internal balance implies paired missing counts even after crossing
edges have been coloured. -/
theorem missing_balance_general (C : M.EdgeColoring k) (S : Finset V)
    (hS : S.card=Sᶜ.card)
    (hbal : ∀ i,(C.colourGraph i).edgesWithin S=(C.colourGraph i).edgesWithin Sᶜ) (i : Fin k) :
    (C.missingSet S i).card=(C.missingSet Sᶜ i).card := by
  have hA:=C.missing_internal_cut_identity S i
  have hB:=C.missing_internal_cut_identity Sᶜ i
  rw [cutSize_compl,←hbal i,←hS] at hB
  omega

/-- Covering one missing vertex on each side lowers each side's missing
count by exactly one for the selected colour. -/
theorem missing_drop_of_degree_update (C : M.EdgeColoring k) (B : N.EdgeColoring k)
    (S : Finset V) (i : Fin k) (u v : V) (hu : u∈S) (hv : v∉S)
    (hd : ∀ z,(B.colourGraph i).degree z=
      (C.colourGraph i).degree z+(if z=u ∨ z=v then 1 else 0)) :
    (C.missingSet S i).card=(B.missingSet S i).card+1 := by
  have hsum : (∑ z∈S,(B.colourGraph i).degree z)=
      (∑ z∈S,(C.colourGraph i).degree z)+1 := by
    simp_rw [hd]
    rw [sum_add_distrib]
    have he : (∑ z∈S,if z=u ∨ z=v then 1 else 0)=1 := by
      calc
        _ = ∑ z∈S,if z=u then 1 else 0 := by
          apply sum_congr rfl
          intro z hz
          have hneq : z≠v:=fun h => hv (h ▸ hz)
          simp only [hneq,or_false]
        _ = 1 := by simp [hu]
    rw [he]
  have hC:=C.missing_card_add_degree_sum S i
  have hB:=B.missing_card_add_degree_sum S i
  omega

theorem total_missing_drop (C : M.EdgeColoring k) (B : N.EdgeColoring k)
    (S : Finset V) (i : Fin k)
    (hi : (C.missingSet S i).card=(B.missingSet S i).card+1)
    (ho : ∀ j,j≠i → C.colourGraph j=B.colourGraph j) :
    (∑ j,(C.missingSet S j).card)=(∑ j,(B.missingSet S j).card)+1 := by
  have he : (∑ j∈univ.erase i,(C.missingSet S j).card)=
      ∑ j∈univ.erase i,(B.missingSet S j).card := by
    apply sum_congr rfl
    intro j hj
    have hg:=ho j (mem_erase.mp hj).1
    have hm : C.missingSet S j=B.missingSet S j := by
      unfold missingSet
      rw [hg]
    rw [hm]
  rw [←sum_erase_add _ _ (mem_univ i),←sum_erase_add _ _ (mem_univ i),he,hi]
  omega

end EdgeColoring

/-- High-degree vertices of a sparse uncoloured remainder are few. -/
theorem high_degree_card_bound (R : MultiGraph V) (a : ℕ) :
    a*(univ.filter (fun v => a≤R.degree v)).card≤2*R.edgeCount := by
  let Z:=univ.filter (fun v => a≤R.degree v)
  have h : (∑ _v∈Z,a)≤∑ v∈Z,R.degree v :=
    sum_le_sum (fun v hv => (mem_filter.mp hv).2)
  have hsub : (∑ v∈Z,R.degree v)≤∑ v : V,R.degree v :=
    sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  rw [R.sum_degrees_eq_twice_edgeCount] at hsub
  simpa [Z,Nat.mul_comm,Nat.nsmul_eq_mul] using h.trans hsub

theorem sparse_bad_vertices (R : MultiGraph V) (m t : ℕ) (ht : 0<t)
    (hsize : R.edgeCount≤2*m*t) :
    25*(univ.filter (fun v => 100*t≤R.degree v)).card≤m := by
  have h:=R.high_degree_card_bound (100*t)
  have hmul : t*(25*(univ.filter (fun v => 100*t≤R.degree v)).card)≤t*m := by
    nlinarith
  exact Nat.le_of_mul_le_mul_left hmul ht

end SimpleGraph.MultiGraph
