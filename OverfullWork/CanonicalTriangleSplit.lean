module

public import OverfullWork.CanonicalZeroTriangle

@[expose] public section


/-! # The positive canonical triangle is a single-bundle perturbation

For the actual L and N, construct a bipartite graph plus q copies of one
edge from the actual middle vertex to the last prefix pair. No arbitrary
triangle is identified with that distinguished triangle by assumption.
-/
namespace OverfullWork.CanonicalTriangleSplit
open SimpleGraph Finset CanonicalPairTriangle
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

omit [Fintype V] in
theorem copiesOn_support (a b : V) (hab : a≠b) (q : ℕ) (u v : V)
    (hEdge : 0<(copiesOn a b hab q).mult s(u,v)) : s(u,v)=s(a,b) := by
  by_contra hn
  have hh:(copiesOn a b hab q).mult s(u,v)=0:=by
    simp only [copiesOn,scaledCopies,MultiGraph.unitEdge,if_neg hn,Nat.mul_zero]
  omega

omit [Fintype V] in
theorem copiesOn_cross (a b : V) (hab : a≠b) (q : ℕ) (P : Finset V)
    (ha : a∈P) (hb : b∉P) :
    ∀u v,0<(copiesOn a b hab q).mult s(u,v) →
      (u∈P ∧ v∉P) ∨ (v∈P ∧ u∉P) := by
  intro u v hEdge
  have hh:=copiesOn_support a b hab q u v hEdge
  rcases Sym2.eq_iff.mp hh with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact Or.inl ⟨ha,hb⟩
  · exact Or.inr ⟨ha,hb⟩

omit [Fintype V] [DecidableEq V] in
theorem addCopies_cross (M N : MultiGraph V) (P : Finset V)
    (hM : ∀u v,0<M.mult s(u,v) → (u∈P ∧ v∉P) ∨ (v∈P ∧ u∉P))
    (hN : ∀u v,0<N.mult s(u,v) → (u∈P ∧ v∉P) ∨ (v∈P ∧ u∉P)) :
    ∀u v,0<(M.addCopies N).mult s(u,v) → (u∈P ∧ v∉P) ∨ (v∈P ∧ u∉P) := by
  intro u v hh
  change 0<M.mult s(u,v)+N.mult s(u,v) at hh
  by_cases hm:0<M.mult s(u,v)
  · exact hM u v hm
  · exact hN u v (by omega)

end OverfullWork.CanonicalTriangleSplit

namespace OverfullWork.CanonicalRegularization
open SimpleGraph Finset CanonicalPairTriangle CanonicalTriangleSplit CanonicalZeroTriangle
open scoped Classical
variable {m Δ : ℕ} {D : MultiGraph (Fin m×Bool)}
set_option maxHeartbeats 8000000

def Completion.middleVertex (C : Completion D Δ) (hkm : C.k<m) : Fin m×Bool :=
  (⟨C.k,hkm⟩,false)

def Completion.lastFalse (C : Completion D Δ) : Fin m×Bool :=
  prefixEmbedding C.cut_le (⟨C.k-1,by have hh:=C.positive;omega⟩,false)

def Completion.lastTrue (C : Completion D Δ) : Fin m×Bool :=
  prefixEmbedding C.cut_le (⟨C.k-1,by have hh:=C.positive;omega⟩,true)

/-- The SAME flipped prefix partition works for L and all paired edges,
independently of the positive triangle parameter. -/
theorem Completion.exists_prefix_flip_partition (C : Completion D Δ) :
    ∃P : Finset (Fin m×Bool),
      (∀u v,0<C.L.mult s(u,v) → (u∈P ∧ v∉P) ∨ (v∈P ∧ u∉P)) ∧
      ∀i : Fin C.k,prefixEmbedding C.cut_le (i,false)∈P ∧
        prefixEmbedding C.cut_le (i,true)∉P := by
  obtain ⟨P,hPrefix,hTail,hEven,hCross⟩:=C.bipartite
  let P':=P.filter fun v=>v.2=false ∨ C.k≤v.1.val
  have hLGood:∀u v,0<C.L.mult s(u,v) → u.2=false ∨ C.k≤u.1.val:=by
    intro u v hEdge
    by_contra hn
    have hTrue:u.2=true:=by cases hh:u.2 <;> simp_all
    have hIndex:u.1.val<C.k:=by omega
    have hh:=C.L_prefix_true_zero u v hIndex hTrue
    omega
  refine ⟨P',?_,?_⟩
  · intro u v hEdge
    have hu:=hLGood u v hEdge
    have hv:=hLGood v u (by simpa only [Sym2.eq_swap] using hEdge)
    have hU:(u∈P' ↔ u∈P):=by simp only [P',mem_filter,and_iff_left hu]
    have hV:(v∈P' ↔ v∈P):=by simp only [P',mem_filter,and_iff_left hv]
    simpa only [hU,hV] using hCross u v hEdge
  · intro i
    have hIn:=(hPrefix ⟨i.val,i.isLt.trans_le C.cut_le⟩ i.isLt).1
    constructor
    · exact mem_filter.mpr ⟨hIn,Or.inl rfl⟩
    · intro hh
      have hBad : ((true : Bool) = false) ∨ (C.k ≤ i.val) := (mem_filter.mp hh).2
      rcases hBad with hh|hh
      · cases hh
      · omega

/-- The non-bipartite contribution is exactly one bundle of q edges.
One of its endpoints is the actual middle vertex. -/
theorem Completion.exists_triangle_bundle_split (C : Completion D Δ) (hkm : C.k<m) :
    ∃P : Finset (Fin m×Bool),∃J : MultiGraph (Fin m×Bool),∃t : Fin m×Bool,
      (t=C.lastFalse ∨ t=C.lastTrue) ∧
      ∃hne : C.middleVertex hkm≠t,
        C.L.addCopies C.N=J.addCopies (copiesOn (C.middleVertex hkm) t hne C.q) ∧
        ∀u v,0<J.mult s(u,v) → (u∈P ∧ v∉P) ∨ (v∈P ∧ u∉P) := by
  obtain ⟨P,hL,hPair⟩:=C.exists_prefix_flip_partition
  obtain ⟨hw,hN⟩:=C.canonical_N.2 hkm
  let j : Fin C.k:=⟨C.k-1,by have hh:=C.positive;omega⟩
  let R:=weightedPairs (prefixEmbedding C.cut_le)
    (fun i=>pairResidue D Δ C.cut_le i-(if i=j then C.q else 0))
  have hR:∀u v,0<R.mult s(u,v) → (u∈P ∧ v∉P) ∨ (v∈P ∧ u∉P):=by
    intro u v hEdge
    obtain ⟨i,hi⟩:=weightedPairs_support _ _ u v hEdge
    rcases Sym2.eq_iff.mp hi with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact Or.inl (hPair i)
    · exact Or.inr (hPair i)
  have hA:C.lastFalse∈P:=(hPair j).1
  have hB:C.lastTrue∉P:=(hPair j).2
  have hwa:C.middleVertex hkm≠C.lastFalse:=hw (j,false)
  have hwb:C.middleVertex hkm≠C.lastTrue:=hw (j,true)
  by_cases hW:C.middleVertex hkm∈P
  · let F:=copiesOn (C.middleVertex hkm) C.lastTrue hwb C.q
    refine ⟨P,(C.L.addCopies R).addCopies F,C.lastFalse,Or.inl rfl,hwa,?_,?_⟩
    · apply MultiGraph.ext_mult
      intro e
      rw [hN]
      change C.L.mult e+(R.mult e+
        ((copiesOn (C.middleVertex hkm) C.lastFalse hwa C.q).mult e+F.mult e))=
        (C.L.mult e+R.mult e+F.mult e)+(copiesOn (C.middleVertex hkm) C.lastFalse hwa C.q).mult e
      omega
    · exact addCopies_cross _ F P (addCopies_cross C.L R P hL hR)
        (copiesOn_cross _ _ hwb C.q P hW hB)
  · let F:=copiesOn (C.middleVertex hkm) C.lastFalse hwa C.q
    refine ⟨P,(C.L.addCopies R).addCopies F,C.lastTrue,Or.inr rfl,hwb,?_,?_⟩
    · apply MultiGraph.ext_mult
      intro e
      rw [hN]
      change C.L.mult e+(R.mult e+
        (F.mult e+(copiesOn (C.middleVertex hkm) C.lastTrue hwb C.q).mult e))=
        (C.L.mult e+R.mult e+F.mult e)+(copiesOn (C.middleVertex hkm) C.lastTrue hwb C.q).mult e
      omega
    · apply addCopies_cross _ F P (addCopies_cross C.L R P hL hR)
      intro u v hEdge
      have hh:=copiesOn_support _ _ hwa C.q u v hEdge
      rcases Sym2.eq_iff.mp hh with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact Or.inr ⟨hA,hW⟩
      · exact Or.inl ⟨hA,hW⟩

end OverfullWork.CanonicalRegularization
