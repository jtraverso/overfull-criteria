module

public import OverfullWork.KuhnOsthusWindingIntervalGeometry

@[expose] public section


/-! The neighbourhood estimate in the proof of Kühn–Osthus
Lemma 7.5(i). Count friendly coarse clusters, keep the full winding
copies in the safe interior, and apply the uniform style refinement. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

/-- The coarse exceptional set absorbs the part of a neighbourhood
outside the coarse clusters. -/
theorem coarse_cluster_profile_lower {V : Type*} [Fintype V]
    (k M : ℕ) (P : Fin k → Finset V) (Z₀ Q : Finset V) (α : ℝ)
    (hα : 0 ≤ α) (hSize : ∀ u, (P u).card = M)
    (hDis : ∀ u v, u ≠ v → Disjoint (P u) (P v))
    (hCover : ∀ v, v ∉ Z₀ → v ∈ univ.biUnion P)
    (hExceptional : (Z₀.card:ℝ) ≤ (α/3)*(Fintype.card V:ℝ))
    (hDegree : α*(Fintype.card V:ℝ) ≤ (Q.card:ℝ)) :
    2*(α/3)*(k:ℝ)*(M:ℝ) ≤ profileCount (univ.biUnion P) Q := by
  classical
  let U := univ.biUnion P
  have hSub : univ \ U ⊆ Z₀ := by
    intro v hv
    by_contra h
    exact (mem_sdiff.mp hv).2 (hCover v h)
  have hLoss : (((univ \ U).card:ℕ):ℝ) ≤ (Z₀.card:ℝ) := by exact_mod_cast card_le_card hSub
  have hCount := exceptional_overlap_loss Q univ U
  rw [univ_inter] at hCount
  have hQ : profileCount (univ : Finset V) Q = (Q.card:ℝ) := by simp [profileCount]
  rw [hQ] at hCount
  have hU : U.card = k*M := by
    unfold U
    rw [card_biUnion (fun u _ v _ h => hDis u v h)]
    simp [hSize]
  have hn : (k:ℝ)*(M:ℝ) ≤ (Fintype.card V:ℝ) := by
    exact_mod_cast (show k*M ≤ Fintype.card V by rw [←hU]; exact card_le_univ _)
  have h := mul_le_mul_of_nonneg_left hn (show 0 ≤ 2*(α/3) by positivity)
  linarith only [h,hCount,hLoss,hExceptional,hDegree]

/-- The profile condition CSys8 and a uniform style refinement yield
a lower bound on the physical neighbours in the safe interior of
a canonical interval before the prefix arcs are deleted. -/
theorem winding_interval_style_profile_lower {V : Type*}
    {p b k : ℕ} (hk : 0 < k) (i : Fin p) (boundary : Fin (b*k))
    (P : Fin k → Finset V) (C A : Fin (p*(b*k)) → Finset V)
    (Q : Finset V) (M K : ℕ) (hM : 0 < M)
    (α θ τ ε : ℝ) (hα : 0 ≤ α) (hθ : 0 ≤ θ) (hτ : τ ≤ α/3) (hε : ε ≤ 1)
    (hP : ∀ u, (P u).card = M)
    (hPDis : ∀ u v, u ≠ v → Disjoint (P u) (P v))
    (hCDis : ∀ x y, x ≠ y → Disjoint (C x) (C y))
    (hA : ∀ x, A x ⊆ C x)
    (hMass : 2*(α/3)*(k:ℝ)*(M:ℝ) ≤ profileCount (univ.biUnion P) Q)
    (hSplit : ∀ x, τ*(M:ℝ) ≤ profileCount (P (windingParent k hk x)) Q →
      θ*profileCount (P (windingParent k hk x)) Q/((p*b:ℕ):ℝ) ≤ profileCount (C x) Q)
    (hThreshold : ∀ x, ε*((C x).card:ℝ) ≤ θ*((α/3)*(M:ℝ))/((p*b:ℕ):ℝ))
    (hRef : ∀ x, UniformProfileCell (fun _ : Unit => Q) (C x) (A x) K ε) :
    let h := θ*((α/3)*(M:ℝ))/((p*b:ℕ):ℝ)
    (α/3*(k:ℝ))*((b-3:ℕ):ℝ)*((1-ε)*(h/(K:ℝ))) ≤
      profileCount ((windingEndpointPositions boundary).biUnion (fun j => A (intervalPosition i j))) Q := by
  classical
  dsimp only
  let F := (univ : Finset (Fin k)).filter (fun u => (α/3)*(M:ℝ) ≤ profileCount (P u) Q)
  let z := θ*((α/3)*(M:ℝ))/((p*b:ℕ):ℝ)
  have hz : 0 ≤ z := by positivity
  have hLarge : α/3*(k:ℝ) ≤ F.card := by
    have h := friendly_cluster_mass P Q (M:ℝ) ((α/3)*(M:ℝ)) (by positivity)
      (fun u => (congrArg (fun n : ℕ => (n:ℝ)) (hP u)).le) hPDis
    simp only [Fintype.card_fin] at h
    change profileCount (univ.biUnion P) Q ≤ (F.card:ℝ)*M+(k:ℝ)*((α/3)*(M:ℝ)) at h
    have hM' : (0:ℝ) < M := by exact_mod_cast hM
    apply (mul_le_mul_iff_of_pos_right hM').mp
    linarith only [h,hMass]
  have hFine (x : Fin (b*k)) (hx : windingParent k hk x ∈ F) :
      ε*((C (intervalPosition i x)).card:ℝ) ≤ profileCount (C (intervalPosition i x)) Q ∧
        z ≤ profileCount (C (intervalPosition i x)) Q := by
    have hx' : (α/3)*(M:ℝ) ≤ profileCount (P (windingParent k hk (intervalPosition i x))) Q := by
      rw [windingParent_intervalPosition]
      exact (mem_filter.mp hx).2
    have hT : τ*(M:ℝ) ≤ profileCount (P (windingParent k hk (intervalPosition i x))) Q :=
      (mul_le_mul_of_nonneg_right hτ (Nat.cast_nonneg M)).trans hx'
    have hB : z ≤ profileCount (C (intervalPosition i x)) Q :=
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hx' hθ) (Nat.cast_nonneg _)).trans
        (hSplit _ hT)
    exact ⟨(hThreshold _).trans hB,hB⟩
  have hLocal := exceptional_interval_profile_lower (windingParent k hk) F
    (windingEndpointPositions boundary) (fun j => C (intervalPosition i j))
    (fun j => A (intervalPosition i j)) Q K (b-3) ε z hε hz
    (fun a _ c _ h => (hCDis _ _ ((intervalPosition i).injective.ne h)).mono (hA _) (hA _))
    (by
      intro u _
      convert winding_interior_copies b k hk boundary u using 2
      ext j
      simp only [mem_filter])
    (fun x _ hx => hFine x hx) (fun x _ => hRef _)
  have hCard : (α/3*(k:ℝ))*((b-3:ℕ):ℝ) ≤ ((F.card*(b-3):ℕ):ℝ) := by
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right hLarge (Nat.cast_nonneg _)
  exact (mul_le_mul_of_nonneg_right hCard (mul_nonneg (sub_nonneg.mpr hε)
    (div_nonneg hz (Nat.cast_nonneg K)))).trans hLocal

end OverfullWork.DirectedRobustExpansion
