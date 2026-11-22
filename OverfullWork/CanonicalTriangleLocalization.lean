module

public import OverfullWork.CanonicalTriangleComponent

@[expose] public section


/-! # Identify the unsafe independent triple with the canonical triangle

The identification follows from the single-bundle split, N-component
support and actual L degrees. It is not supplied as an input.
-/
namespace OverfullWork.CanonicalRegularization
open SimpleGraph Finset CanonicalPairTriangle CanonicalTripleAddition CanonicalPrefixCuts
open scoped Classical
variable {m Δ : ℕ} {D : MultiGraph (Fin m×Bool)}
set_option maxHeartbeats 10000000

theorem Completion.independent_triple_safe_with_outside_vertex (C : Completion D Δ)
    (hkm : C.k<m) (hdeg : ∀v,D.degree v≤Δ)
    (hOrder : D.degree C.lastTrue≤D.degree (C.middleVertex hkm))
    (t x : Fin m×Bool) (ht : t=C.lastFalse ∨ t=C.lastTrue)
    (hx : x∉C.triangle hkm)
    (hBase : D.twiceInternal {C.middleVertex hkm,t,x}=0) :
    Δ≤((D.addCopies C.L).addCopies C.N).cutSize {C.middleVertex hkm,t,x} := by
  let w:=C.middleVertex hkm
  have hw:w∈C.triangle hkm:=by simp [w,Completion.triangle]
  have htT:t∈C.triangle hkm:=by rcases ht with rfl|rfl <;> simp [Completion.triangle]
  have hwx:w≠x:=by intro hh;exact hx (hh ▸ hw)
  have htx:t≠x:=by intro hh;exact hx (hh ▸ htT)
  have hwt:w≠t:=by
    have hwI:w.1.val=C.k:=rfl
    have htI:t.1.val=C.k-1:=by rcases ht with rfl|rfl <;> rfl
    intro hh
    have he:=congrArg (fun v : Fin m×Bool=>v.1.val) hh
    have hk:=C.positive
    omega
  have hNwx:C.N.mult s(w,x)=0:=by
    rw [Sym2.eq_swap]
    exact C.N_triangle_boundary_zero hkm x w hx hw
  have hNtx:C.N.mult s(t,x)=0:=by
    rw [Sym2.eq_swap]
    exact C.N_triangle_boundary_zero hkm x t hx htT
  have hNwt:C.N.mult s(w,t)=C.q:=C.N_middle_bundle hkm t ht
  have hNI:C.N.twiceInternal {w,t,x}=2*C.q:=by
    rw [CriticalCentreTriples.triple_internal C.N w t x hwt hwx htx,hNwx,hNtx,hNwt]
    omega
  have hLw:=CanonicalTripleAddition.two_bundles_le_degree C.L w t x htx
  have hLt:=CanonicalZeroTriangle.mult_le_degree C.L t x
  have hLI:C.L.twiceInternal {w,t,x}≤2*(C.L.degree w+C.L.degree t):=by
    rw [CriticalCentreTriples.triple_internal C.L w t x hwt hwx htx]
    omega
  have htDegree:C.L.degree t≤D.degree C.lastTrue:=by
    let j : Fin m:=⟨C.k-1,by have hh:=C.positive;have hk:=C.cut_le;omega⟩
    have hj:j.val<C.k:=by dsimp [j];have hh:=C.positive;omega
    obtain ⟨hFalse,hTrue⟩:=C.prefix_degrees j hj
    have hDb:=hdeg C.lastTrue
    rcases ht with rfl|rfl
    · change C.L.degree (j,false)≤D.degree (j,true)
      change C.L.degree (j,false)=(Δ-D.degree (j,false))-(Δ-D.degree (j,true)) at hFalse
      change D.degree (j,true)≤Δ at hDb
      omega
    · change C.L.degree (j,true)≤D.degree (j,true)
      omega
  have hMid:C.L.degree w+2*C.q=Δ-D.degree w:=by
    exact C.middle_degrees ⟨C.k,hkm⟩ rfl
  have hRoom:C.L.degree w+C.L.degree t+C.q≤Δ:=by
    change D.degree C.lastTrue≤D.degree w at hOrder
    have hWdeg:=hdeg w
    omega
  have hCard:({w,t,x}:Finset _).card=3:=by simp [hwt,hwx,htx]
  have hId:=((D.addCopies C.L).addCopies C.N).regular_cut_identity C.regular {w,t,x}
  rw [twiceInternal_addCopies,twiceInternal_addCopies,hBase,hNI,hCard] at hId
  change Δ≤((D.addCopies C.L).addCopies C.N).cutSize {w,t,x}
  omega

theorem Completion.unsafe_independent_triple_eq_triangle (C : Completion D Δ)
    (hkm : C.k<m) (hdeg : ∀v,D.degree v≤Δ)
    (hOrder : D.degree C.lastTrue≤D.degree (C.middleVertex hkm))
    (S : Finset (Fin m×Bool)) (hS : S.card=3) (hBase : D.twiceInternal S=0)
    (hCut : ((D.addCopies C.L).addCopies C.N).cutSize S<Δ) : S=C.triangle hkm := by
  obtain ⟨hw,ht⟩:=C.unsafe_independent_triple_contains_middle hkm S hS hBase hCut
  obtain ⟨t,htS,htPair⟩:∃t,t∈S ∧ (t=C.lastFalse ∨ t=C.lastTrue):=by
    rcases ht with ht|ht
    · exact ⟨_,ht,Or.inl rfl⟩
    · exact ⟨_,ht,Or.inr rfl⟩
  let w:=C.middleVertex hkm
  have hwt:w≠t:=by
    have htI:t.1.val=C.k-1:=by rcases htPair with rfl|rfl <;> rfl
    intro hh
    have he:=congrArg (fun v : Fin m×Bool=>v.1.val) hh
    change C.k=t.1.val at he
    have hk:=C.positive
    omega
  have hSub:({w,t}:Finset _)⊆S:=by simp only [insert_subset_iff,singleton_subset_iff];exact ⟨hw,htS⟩
  have hDiff:(S\{w,t}).card=1:=by rw [card_sdiff_of_subset hSub,hS];simp [hwt]
  obtain ⟨x,hx⟩:=card_eq_one.mp hDiff
  have hxDiff:x∈S\{w,t}:=by rw [hx];simp
  have hxS:x∈S:=(mem_sdiff.mp hxDiff).1
  have hSet:S={w,t,x}:=by
    ext v
    constructor
    · intro hv
      by_cases hvw:v=w
      · simp [hvw]
      · by_cases hvt:v=t
        · simp [hvt]
        · have hh:v∈S\{w,t}:=mem_sdiff.mpr ⟨hv,by simp [hvw,hvt]⟩
          rw [hx,mem_singleton] at hh
          simp [hh]
    · intro hv
      simp only [mem_insert,mem_singleton] at hv
      rcases hv with rfl|rfl|rfl <;> assumption
  by_cases hxT:x∈C.triangle hkm
  · have hSubT:S⊆C.triangle hkm:=by
      rw [hSet]
      simp only [insert_subset_iff,singleton_subset_iff]
      refine ⟨?_,?_,hxT⟩
      · simp [w,Completion.triangle]
      · rcases htPair with rfl|rfl <;> simp [Completion.triangle]
    exact eq_of_subset_of_card_le hSubT (by rw [C.triangle_card hkm,hS])
  · have hSafe:=C.independent_triple_safe_with_outside_vertex hkm hdeg hOrder t x htPair hxT
      (by rwa [←hSet])
    rw [←hSet] at hSafe
    omega

end OverfullWork.CanonicalRegularization
