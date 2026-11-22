module

public import OverfullWork.CanonicalPrefixCuts

@[expose] public section


/-! # The distinguished triangle is an actual N component

This verifies the support assertions needed to identify, rather than
assume, the remaining independent triple.
-/
namespace OverfullWork.CanonicalTriangleComponent
open SimpleGraph Finset CanonicalPairTriangle CanonicalZeroTriangle CanonicalTriangleSplit CanonicalPrefixCuts
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 8000000

def triangleSet {k : ℕ} (e : (Fin k×Bool) ↪ V) (j : Fin k) (w : V) : Finset V :=
  {e (j,false),e (j,true),w}

omit [Fintype V] in
theorem prefix_mem_triangle_iff {k : ℕ} (e : (Fin k×Bool) ↪ V) (j i : Fin k)
    (w : V) (hw : ∀z,w≠e z) (b : Bool) :
    e (i,b)∈triangleSet e j w ↔ i=j := by
  have hn:e (i,b)≠w:=(hw _).symm
  simp only [triangleSet,mem_insert,mem_singleton,hn,or_false]
  exact pair_index_iff e i j b

omit [Fintype V] in
theorem pairTriangle_boundary_zero {k : ℕ} (e : (Fin k×Bool) ↪ V) (r : Fin k→ℕ)
    (j : Fin k) (w : V) (hw : ∀z,w≠e z) (q : ℕ) (u v : V)
    (hu : u∉triangleSet e j w) (hv : v∈triangleSet e j w) :
    (pairTriangle e r j w hw q).mult s(u,v)=0 := by
  have hPairs:(weightedPairs e (fun i=>r i-(if i=j then q else 0))).mult s(u,v)=0:=by
    by_contra hn
    obtain ⟨i,hi⟩:=weightedPairs_support e _ u v (Nat.pos_of_ne_zero hn)
    rcases Sym2.eq_iff.mp hi with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · have hij: i=j:=(prefix_mem_triangle_iff e j i w hw true).mp hv
      exact hu ((prefix_mem_triangle_iff e j i w hw false).mpr hij)
    · have hij: i=j:=(prefix_mem_triangle_iff e j i w hw false).mp hv
      exact hu ((prefix_mem_triangle_iff e j i w hw true).mpr hij)
  have hUW:u≠w:=by intro hh;exact hu (hh ▸ (by simp [triangleSet]))
  have hUA:u≠e (j,false):=by intro hh;exact hu (hh ▸ (by simp [triangleSet]))
  have hUB:u≠e (j,true):=by intro hh;exact hu (hh ▸ (by simp [triangleSet]))
  have hA:(copiesOn w (e (j,false)) (hw _) q).mult s(u,v)=0:=by
    by_contra hn
    have hh:=copiesOn_support w (e (j,false)) (hw _) q u v (by omega)
    rcases Sym2.eq_iff.mp hh with ⟨he,_⟩|⟨he,_⟩
    · exact hUW he
    · exact hUA he
  have hB:(copiesOn w (e (j,true)) (hw _) q).mult s(u,v)=0:=by
    by_contra hn
    have hh:=copiesOn_support w (e (j,true)) (hw _) q u v (by omega)
    rcases Sym2.eq_iff.mp hh with ⟨he,_⟩|⟨he,_⟩
    · exact hUW he
    · exact hUB he
  change _+(_+_)=0
  rw [hPairs,hA,hB]

theorem pairTriangle_middle_bundle {k : ℕ} (e : (Fin k×Bool) ↪ V) (r : Fin k→ℕ)
    (j : Fin k) (w : V) (hw : ∀z,w≠e z) (q : ℕ) (b : Bool) :
    (pairTriangle e r j w hw q).mult s(w,e (j,b))=q := by
  have hPairs:(weightedPairs e (fun i=>r i-(if i=j then q else 0))).mult s(w,e (j,b))=0:=by
    have hh:=mult_le_degree (weightedPairs e (fun i=>r i-(if i=j then q else 0))) w (e (j,b))
    rw [degree_weightedPairs_outside e _ w hw] at hh
    omega
  have hne:s(w,e (j,false))≠s(w,e (j,true)):=by
    intro hh
    rcases Sym2.eq_iff.mp hh with ⟨_,he⟩|⟨he,_⟩
    · have he':=congrArg Prod.snd (e.injective he);cases he'
    · exact hw (j,true) he
  change (weightedPairs _ _).mult s(w,e (j,b))+
    ((copiesOn _ _ _ q).mult s(w,e (j,b))+(copiesOn _ _ _ q).mult s(w,e (j,b)))=q
  rw [hPairs]
  cases b <;> simp [copiesOn,scaledCopies,MultiGraph.unitEdge,hne,hne.symm]

end OverfullWork.CanonicalTriangleComponent

namespace OverfullWork.CanonicalRegularization
open SimpleGraph Finset CanonicalPairTriangle CanonicalTriangleComponent
open scoped Classical
variable {m Δ : ℕ} {D : MultiGraph (Fin m×Bool)}
set_option maxHeartbeats 8000000

def Completion.triangle (C : Completion D Δ) (hkm : C.k<m) : Finset (Fin m×Bool) :=
  {C.lastFalse,C.lastTrue,C.middleVertex hkm}

theorem Completion.triangle_card (C : Completion D Δ) (hkm : C.k<m) :
    (C.triangle hkm).card=3 := by
  have hAB:C.lastFalse≠C.lastTrue:=by
    intro hh;have he:=congrArg Prod.snd hh;cases he
  have hAW:C.lastFalse≠C.middleVertex hkm:=by
    intro hh
    have he:=congrArg (fun x : Fin m×Bool=>x.1.val) hh
    change C.k-1=C.k at he
    have hk:=C.positive
    omega
  have hBW:C.lastTrue≠C.middleVertex hkm:=by
    intro hh;have he:=congrArg Prod.snd hh;cases he
  simp [Completion.triangle,hAB,hAW,hBW]

theorem Completion.N_triangle_boundary_zero (C : Completion D Δ) (hkm : C.k<m)
    (u v : Fin m×Bool) (hu : u∉C.triangle hkm) (hv : v∈C.triangle hkm) :
    C.N.mult s(u,v)=0 := by
  obtain ⟨hw,hN⟩:=C.canonical_N.2 hkm
  rw [hN]
  exact pairTriangle_boundary_zero _ _ _ _ hw C.q u v hu hv

theorem Completion.N_middle_bundle (C : Completion D Δ) (hkm : C.k<m)
    (t : Fin m×Bool) (ht : t=C.lastFalse ∨ t=C.lastTrue) :
    C.N.mult s(C.middleVertex hkm,t)=C.q := by
  obtain ⟨hw,hN⟩:=C.canonical_N.2 hkm
  rw [hN]
  rcases ht with rfl|rfl
  · exact pairTriangle_middle_bundle _ _ _ _ hw C.q false
  · exact pairTriangle_middle_bundle _ _ _ _ hw C.q true

end OverfullWork.CanonicalRegularization
