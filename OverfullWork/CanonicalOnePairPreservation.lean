module

public import OverfullWork.CanonicalTriangleLocalization

@[expose] public section


/-! # Close the distinguished triangle when the canonical prefix is one pair

Every added edge has at least one endpoint in the distinguished triangle.
Its odd complement is therefore unchanged internally. Original
no-overfullness excludes an overfull triangle in the regular completion.
-/
namespace OverfullWork.CanonicalRegularization
open SimpleGraph Finset CanonicalPairTriangle CanonicalTriangleComponent CanonicalTripleAddition
open scoped Classical
variable {m Δ : ℕ} {D : MultiGraph (Fin m×Bool)}
set_option maxHeartbeats 10000000

theorem Completion.N_degree_zero_outside_triangle_of_prefix_one (C : Completion D Δ)
    (hkm : C.k<m) (hk : C.k=1) (u : Fin m×Bool) (hu : u∉C.triangle hkm) :
    C.N.degree u=0 := by
  obtain ⟨hw,hN⟩:=C.canonical_N.2 hkm
  rw [hN]
  apply degree_pairTriangle_outside
  · intro z he
    obtain ⟨i,b⟩:=z
    have hi:i.val=C.k-1:=by have hh:=i.isLt;omega
    have hij:i=⟨C.k-1,by have hh:=C.positive;omega⟩:=Fin.ext hi
    apply hu
    rw [he]
    exact (prefix_mem_triangle_iff (prefixEmbedding C.cut_le) _ i _ hw b).mpr hij
  · intro he
    exact hu (he ▸ (by simp [Completion.triangle,Completion.middleVertex]))

theorem Completion.L_mult_zero_outside_triangle_of_prefix_one (C : Completion D Δ)
    (hkm : C.k<m) (hk : C.k=1) (u v : Fin m×Bool)
    (hu : u∉C.triangle hkm) (hv : v∉C.triangle hkm) : C.L.mult s(u,v)=0 := by
  obtain ⟨P,hPrefix,hTail,hEven,hCross⟩:=C.bipartite
  have hOutside:∀a : Fin m×Bool,a∉C.triangle hkm → a∉P:=by
    rintro ⟨i,b⟩ ha
    have hIndex:i.val≠0:=by
      intro hi
      cases b
      · have he:(i,false)=C.lastFalse:=by
          apply Prod.ext
          · apply Fin.ext;change i.val=C.k-1;omega
          · rfl
        exact ha (he ▸ (by simp [Completion.triangle]))
      · have he:(i,true)=C.lastTrue:=by
          apply Prod.ext
          · apply Fin.ext;change i.val=C.k-1;omega
          · rfl
        exact ha (he ▸ (by simp [Completion.triangle]))
    cases b
    · have hMiddle:i.val≠1:=by
        intro hi
        have he:(i,false)=C.middleVertex hkm:=by
          apply Prod.ext
          · apply Fin.ext;change i.val=C.k;omega
          · rfl
        exact ha (he ▸ (by simp [Completion.triangle]))
      exact (hTail i (by omega)).1
    · exact hEven i (by omega)
  have hU:=hOutside u hu
  have hV:=hOutside v hv
  by_contra hn
  have hh:=hCross u v (by omega)
  tauto

theorem Completion.added_complement_internal_zero_of_prefix_one (C : Completion D Δ)
    (hkm : C.k<m) (hk : C.k=1) :
    (C.L.addCopies C.N).twiceInternal (C.triangle hkm)ᶜ=0 := by
  apply sum_eq_zero
  intro u hu
  apply sum_eq_zero
  intro v hv
  have hU:=mem_compl.mp hu
  have hV:=mem_compl.mp hv
  have hL:=C.L_mult_zero_outside_triangle_of_prefix_one hkm hk u v hU hV
  have hN:=C.N_degree_zero_outside_triangle_of_prefix_one hkm hk u hU
  have hBound:=CanonicalZeroTriangle.mult_le_degree C.N u v
  change C.L.mult s(u,v)+C.N.mult s(u,v)=0
  omega

theorem Completion.triangle_safe_of_prefix_one (C : Completion D Δ)
    (hkm : C.k<m) (hk : C.k=1) (hdeg : ∀v,D.degree v≤Δ)
    (hNo : ¬D.HasOverfullSubset Δ) :
    Δ≤((D.addCopies C.L).addCopies C.N).cutSize (C.triangle hkm) := by
  let T:=C.triangle hkm
  have hT:T.card=3:=C.triangle_card hkm
  have hOdd:Odd T.card:=by rw [hT];exact ⟨1,rfl⟩
  have hEven:Even (Fintype.card (Fin m×Bool)):=by
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
    exact ⟨m,by omega⟩
  have hCompOdd:=MultiGraph.odd_card_compl hEven hOdd
  have hBound:=((D.noOverfull_iff_odd_bounds Δ hdeg).mp hNo) Tᶜ hCompOdd
  have hAdded:=C.added_complement_internal_zero_of_prefix_one hkm hk
  rw [twiceInternal_addCopies] at hAdded
  have hInternal:((D.addCopies C.L).addCopies C.N).twiceInternal Tᶜ=D.twiceInternal Tᶜ:=by
    rw [twiceInternal_addCopies,twiceInternal_addCopies]
    change C.L.twiceInternal Tᶜ+C.N.twiceInternal Tᶜ=0 at hAdded
    omega
  by_contra hn
  have hSmall:((D.addCopies C.L).addCopies C.N).cutSize Tᶜ<Δ:=by
    rw [MultiGraph.cutSize_compl]
    exact Nat.lt_of_not_ge hn
  have hOver:=(((D.addCopies C.L).addCopies C.N).odd_overfull_iff_small_cut C.regular
    Tᶜ hCompOdd).mpr hSmall
  rw [hInternal] at hOver
  omega

end OverfullWork.CanonicalRegularization
