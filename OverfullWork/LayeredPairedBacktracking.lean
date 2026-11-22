module

public import OverfullWork.PairedRoute

@[expose] public section


/-! # Backwards extraction of a simple paired route

At depth n, more than |B|+2n predecessor choices suffice, where B is
closed under the matching permutation. Each recursive choice blocks
both vertices of the next pair. No path or injective embedding is
assumed as an input.
-/
namespace OverfullWork.PairedRoutes
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 16000000

theorem exists_layered_route (τ : Equiv.Perm V) (hτ : ∀ v, τ (τ v)=v)
    (F : SimpleGraph V) [DecidableRel F.Adj] (U : Finset V)
    (hNe : ∀ v ∈ U, τ v ≠ v) (S : ℕ → Finset V) (n : ℕ)
    (hLayers : ∀ j, j ≤ n → S j ⊆ U) (B : Finset V)
    (hClosed : ∀ v ∈ B, τ v ∈ B)
    (hSteps : ∀ j, j < n → ∀ z ∈ S (j+1),
      B.card+2*n < ((S j).filter (fun x => F.Adj (τ x) z)).card)
    (z : V) (hz : z ∈ S n) (hzB : z ∉ B) :
    ∃ p : Route τ F U z n, p.vertices.Nodup ∧
      (∀ v ∈ p.vertices, v ∉ B) ∧ p.first ∈ S 0 := by
  induction n generalizing B z with
  | zero =>
    have hzU := hLayers 0 le_rfl hz
    have hτzB : τ z ∉ B := by
      intro hh
      have ht := hClosed (τ z) hh
      rw [hτ] at ht
      exact hzB ht
    refine ⟨Route.single z hzU,?_,?_,hz⟩
    · simp [Route.vertices,(hNe z hzU).symm]
    · intro v hv
      simp only [Route.vertices,List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with hv|hv
      · exact hv ▸ hzB
      · exact hv ▸ hτzB
  | succ n ih =>
    have hzU := hLayers (n+1) le_rfl hz
    have hτzB : τ z ∉ B := by
      intro hh
      have ht := hClosed (τ z) hh
      rw [hτ] at ht
      exact hzB ht
    let B' := insert z (insert (τ z) B)
    have hCard : B'.card ≤ B.card+2 := by
      have h₁ := card_insert_le z (insert (τ z) B)
      have h₂ := card_insert_le (τ z) B
      change B'.card ≤ _ at h₁
      omega
    have hClosed' : ∀ v ∈ B', τ v ∈ B' := by
      intro v hv
      simp only [B',mem_insert] at hv ⊢
      rcases hv with hv|hv|hv
      · subst v;exact Or.inr (Or.inl rfl)
      · subst v;exact Or.inl (hτ z)
      · exact Or.inr (Or.inr (hClosed v hv))
    let N := (S n).filter (fun x => F.Adj (τ x) z)
    have hLarge : B'.card < N.card := by
      have hh := hSteps n (by omega) z hz
      change B.card+2*(n+1) < N.card at hh
      omega
    have hNonempty : (N\B').Nonempty := by
      have hh := card_le_card_sdiff_add_card (s := N) (t := B')
      apply card_pos.mp
      omega
    obtain ⟨x,hx⟩ := hNonempty
    obtain ⟨hxN,hxB⟩ := mem_sdiff.mp hx
    obtain ⟨hxS,hEdge⟩ := mem_filter.mp hxN
    have hLayers' : ∀ j, j ≤ n → S j ⊆ U := fun j hj => hLayers j (by omega)
    have hSteps' : ∀ j, j < n → ∀ y ∈ S (j+1),
        B'.card+2*n < ((S j).filter (fun x => F.Adj (τ x) y)).card := by
      intro j hj y hy
      have hh := hSteps j (by omega) y hy
      omega
    obtain ⟨p,hp,hAvoid,hFirst⟩ := ih hLayers' B' hClosed' hSteps' x hxS hxB
    let q := Route.snoc p z hzU hEdge
    refine ⟨q,?_,?_,hFirst⟩
    · change (p.vertices ++ [z,τ z]).Nodup
      apply hp.append
      · simp [(hNe z hzU).symm]
      · apply List.disjoint_left.mpr
        intro v hv hvz
        have hh := hAvoid v hv
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hvz
        rcases hvz with hvz|hvz
        · exact hh (mem_insert.mpr (Or.inl hvz))
        · exact hh (mem_insert.mpr (Or.inr (mem_insert.mpr (Or.inl hvz))))
    · intro v hv
      change v ∈ p.vertices ++ [z,τ z] at hv
      rcases List.mem_append.mp hv with hv|hv
      · exact fun hh => hAvoid v hv (mem_insert_of_mem (mem_insert_of_mem hh))
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with hv|hv
        · exact hv ▸ hzB
        · exact hv ▸ hτzB

end OverfullWork.PairedRoutes
