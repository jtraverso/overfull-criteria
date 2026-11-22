module

public import OverfullWork.OsthusStadenShadowBalance

@[expose] public section


/-! Relate shadow expansion to the actual number of in-red and out-red
cells over each primary cluster in Osthus–Staden Claim 5.5. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {U V : Type*} [Fintype U] [Fintype V]

theorem shadow_send_fibres (σ : Equiv.Perm U) (φ : Equiv.Perm V) (project : U → V)
    (incoming outgoing : Finset U) (n : ℕ)
    (hProj : ∀ x, project (σ x) = φ (project x))
    (hDis : Disjoint incoming outgoing)
    (hIn : ∀ u, (incoming.filter (fun x => project x = u)).card = n)
    (hOut : ∀ u, (outgoing.filter (fun x => project x = u)).card = n) :
    ∀ u, fibreWeight (project ∘ shadowSend σ incoming outgoing) univ u = 2*n := by
  intro u
  let R := ↥(incoming ∪ outgoing)
  let A := (univ : Finset R).filter (fun x => project (shadowSend σ incoming outgoing x) = u)
  let emb : R ↪ U := Function.Embedding.subtype (· ∈ incoming ∪ outgoing)
  have hMap : A.map emb = (incoming.filter (fun x => project x = φ u)) ∪
      (outgoing.filter (fun x => project x = u)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨y,hy,hyx⟩ := mem_map.mp hx
      have hp := (mem_filter.mp hy).2
      change (y:U) = x at hyx
      subst x
      by_cases hi : (y:U) ∈ incoming
      · apply mem_union_left
        apply mem_filter.mpr
        refine ⟨hi,?_⟩
        simp only [shadowSend,hi,if_true] at hp
        rw [←hp,←hProj,σ.apply_symm_apply]
      · exact mem_union_right _ (mem_filter.mpr ⟨(mem_union.mp y.property).resolve_left hi,
          by simpa only [shadowSend,hi,if_false] using hp⟩)
    · intro hx
      rcases mem_union.mp hx with hx | hx
      · obtain ⟨hi,hp⟩ := mem_filter.mp hx
        let y : R := ⟨x,mem_union_left _ hi⟩
        refine mem_map.mpr ⟨y,mem_filter.mpr ⟨mem_univ _,?_⟩,rfl⟩
        simp only [shadowSend,show (y:U) ∈ incoming from hi,if_true]
        apply φ.injective
        rw [←hProj,σ.apply_symm_apply]
        exact hp
      · obtain ⟨ho,hp⟩ := mem_filter.mp hx
        let y : R := ⟨x,mem_union_right _ ho⟩
        have hi : (y:U) ∉ incoming := fun h => disjoint_left.mp hDis h ho
        exact mem_map.mpr ⟨y,mem_filter.mpr ⟨mem_univ _,by simpa only [shadowSend,hi,if_false] using hp⟩,rfl⟩
  change A.card = _
  rw [← card_map emb,hMap,card_union_of_disjoint (hDis.mono (filter_subset _ _) (filter_subset _ _)),
    hIn,hOut,two_mul]

theorem shadow_receive_fibres (σ : Equiv.Perm U) (φ : Equiv.Perm V) (project : U → V)
    (incoming outgoing : Finset U) (n : ℕ)
    (hProj : ∀ x, project (σ x) = φ (project x))
    (hSend : ∀ u, fibreWeight (project ∘ shadowSend σ incoming outgoing) univ u = n) :
    ∀ u, fibreWeight (project ∘ shadowReceive σ incoming outgoing) univ u = n := by
  intro u
  have h : ((univ : Finset ↥(incoming ∪ outgoing)).filter
        (fun x => (project ∘ shadowReceive σ incoming outgoing) x = u)) =
      univ.filter (fun x => (project ∘ shadowSend σ incoming outgoing) x = φ.symm u) := by
    ext x
    simp only [mem_filter,mem_univ,true_and,Function.comp_apply,shadowReceive,hProj]
    exact φ.apply_eq_iff_eq_symm_apply
  unfold fibreWeight at *
  rw [h,hSend]

/-- Claim 5.5 from the uniform red-cell counts in (21).
The two shifted endpoints are projected separately to the primary graph. -/
theorem shadow_realRobust_and_degrees (R : Digraph V) (σ : Equiv.Perm U) (φ : Equiv.Perm V)
    (project : U → V) (incoming outgoing : Finset U) (n : ℕ)
    (hProj : ∀ x, project (σ x) = φ (project x)) (hDis : Disjoint incoming outgoing)
    (hIn : ∀ u, (incoming.filter (fun x => project x = u)).card = n)
    (hOut : ∀ u, (outgoing.filter (fun x => project x = u)).card = n)
    (hn : 0 < n) (ν τ : ℝ) (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ 1/4)
    (hOrder : 2 ≤ τ*(Fintype.card V:ℝ)) (hR : IsRealRobust R ν τ) :
    let a := project ∘ shadowSend σ incoming outgoing
    let b := project ∘ shadowReceive σ incoming outgoing
    let shadow := fibrePullback R a b
    IsRealRobust shadow (ν^2/2) (2*τ) ∧
      ∀ x, inDegree shadow x = inDegree R (b x)*(2*n) ∧
        outDegree shadow x = outDegree R (a x)*(2*n) := by
  have hs := shadow_send_fibres σ φ project incoming outgoing n hProj hDis hIn hOut
  have ht := shadow_receive_fibres σ φ project incoming outgoing (2*n) hProj hs
  exact ⟨fibrePullback_realRobust _ _ _ _ hs ht (by omega) ν τ hν hντ hτ hOrder hR,
    fibrePullback_semidegrees _ _ _ _ hs ht⟩

end OverfullWork.DirectedRobustExpansion
