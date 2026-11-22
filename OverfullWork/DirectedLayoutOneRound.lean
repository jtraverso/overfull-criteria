module

public import OverfullWork.DirectedDenseMarkerProfiles
public import OverfullWork.DirectedLayoutComplement

@[expose] public section


/-! The full construction of one round from its residual block profiles. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset DirectedRobustExpansion DirectedReserveStitching DirectedLongLayoutPath
  InducedDigraphSampling
open scoped Classical
universe u v

/-- In- and out-neighbour counts into the given part. The centre is
normalized by the size of that part. -/
def ProfilesAround {V : Type*} (D : Digraph V) (B : Finset V) (δ ε : ℝ) : Prop :=
  ∀ x ∈ B, |((B.filter (fun v => D.Adj v x)).card:ℝ)-δ*(B.card:ℝ)| ≤ ε*(B.card:ℝ) ∧
    |((B.filter (fun v => D.Adj x v)).card:ℝ)-δ*(B.card:ℝ)| ≤ ε*(B.card:ℝ)

private theorem marker_real_bounds {V : Type*} (B Y : Finset V) (hY : Y ⊆ B)
    (q p k : ℕ) (hLoss : (B \ Y).card ≤ q) (δ ε η : ℝ) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (hη : 0 ≤ η) (hSlack : ε*(B.card:ℝ)+(q:ℝ)+1 ≤ η*((B.card:ℝ)-q))
    (hApprox : |(p:ℝ)-δ*(B.card:ℝ)| ≤ ε*(B.card:ℝ))
    (hBounds : k ≤ p+1 ∧ p ≤ k+(B \ Y).card) :
    (δ-η)*(Fintype.card (Option Y):ℝ) ≤ (k:ℝ) ∧
      (k:ℝ) ≤ (δ+η)*(Fintype.card (Option Y):ℝ) := by
  have hEq := card_sdiff_add_card_eq_card hY
  have hCard : (Fintype.card (Option Y):ℝ) = (Y.card:ℝ)+1 := by simp
  have hOrder : (B.card:ℝ)-(q:ℝ) ≤ (Fintype.card (Option Y):ℝ) := by
    rw [hCard]
    exact_mod_cast (show (B.card:ℤ)-(q:ℤ) ≤ (Y.card:ℤ)+1 by omega)
  have hScale := hSlack.trans (mul_le_mul_of_nonneg_left hOrder hη)
  have hδUpper : δ*(Fintype.card (Option Y):ℝ) ≤ δ*(B.card:ℝ)+1 := by
    rw [hCard,mul_add,mul_one]
    have h := mul_le_mul_of_nonneg_left (show (Y.card:ℝ) ≤ B.card by
      exact_mod_cast card_le_card hY) hδ
    linarith only [h,hδ₁]
  have hδLower : δ*(B.card:ℝ) ≤ δ*(Fintype.card (Option Y):ℝ)+(q:ℝ) := by
    have hB : (B.card:ℝ) ≤ (Fintype.card (Option Y):ℝ)+(q:ℝ) := by
      rw [hCard]
      exact_mod_cast (show B.card ≤ Y.card+1+q by omega)
    have h := mul_le_mul_of_nonneg_left hB hδ
    have hq := mul_le_mul_of_nonneg_right hδ₁ (Nat.cast_nonneg (α := ℝ) q)
    rw [one_mul] at hq
    nlinarith only [h,hq]
  have hU : (k:ℝ) ≤ (p:ℝ)+1 := by exact_mod_cast hBounds.1
  have hL : (p:ℝ) ≤ (k:ℝ)+(q:ℝ) := by
    exact_mod_cast hBounds.2.trans (Nat.add_le_add_left hLoss k)
  obtain ⟨hPL,hPU⟩ := abs_le.mp hApprox
  constructor <;> nlinarith only [hScale,hδUpper,hδLower,hU,hL,hPL,hPU]

/-- Build one complete configuration using the current dense graph and
reserve. The hypotheses concern the block before routing any of the
short paths. The available dense profile tolerance pays for deleting
their interiors and for introducing the marker. -/
theorem exists_layout_round_uniform_in_density (ν τ α d₀ ρ η : ℝ) (hν : 0 < ν)
    (hντ : ν ≤ τ) (hτα : 256*τ ≤ α) (hα : α ≤ 1)
    (hd₀ : 0 < d₀) (hρ : 0 < ρ) (hη : 0 < η)
    (hGap : 8*η ≤ d₀) (hScale : 52*η ≤ ρ*d₀) :
    ∃ N₀ N₁ : ℕ, ∀ (δ : ℝ), d₀ ≤ δ → δ ≤ 1 → ∀ {V : Type u} [Fintype V] {I : Type v} [Fintype I]
      (D Γ : Digraph V) (L : Layout V I) (long : I) (A Z : Finset V)
      (r s t h : ℕ) (ε : ℝ),
      let B : Finset V := Aᶜ
      let q := L.boundary.card+(univ \ insert long L.fixed).card*h
      let e : A ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
      long ∉ L.fixed → Disjoint L.boundary A → Disjoint L.boundary Z →
      0 < A.card → N₀ ≤ A.card → N₁+q ≤ B.card →
      IsRealRobust (induced Γ A) ν τ →
      (∀ v : A, α*(Fintype.card A:ℝ) ≤ (inDegree (induced Γ A) v:ℝ)) →
      (∀ v : A, α*(Fintype.card A:ℝ) ≤ (outDegree (induced Γ A) v:ℝ)) →
      IsRobustAt (induced Γ B) r t → 0 < s → Fintype.card B/s+5 ≤ h →
      Z.card+q+s ≤ r →
      (∀ v : B, t ≤ inDegree (induced Γ B) v) →
      (∀ v : B, t+Z.card+q+1 ≤ outDegree (induced Γ B) v) →
      ProfilesAround D B δ ε →
      ε*(B.card:ℝ)+(q:ℝ)+1 ≤ η*((B.card:ℝ)-q) →
      ρ*((B.card:ℝ)+1) ≤ (ν/4)^3*(A.card:ℝ) →
      (∀ y ∈ B, 2*ρ*((B.card:ℝ)+1) ≤ ((A.filter (fun w => D.Adj y w)).card:ℝ)) →
      (∀ y ∈ B, 2*ρ*((B.card:ℝ)+1) ≤ ((A.filter (fun w => D.Adj w y)).card:ℝ)) →
      ∃ R : Realization (D ⊔ Γ) L,
        wordGraph (R.word long) ≤ mixed D (induced Γ A) e ∧
        ∀ i ∉ insert long L.fixed, wordGraph (R.word i) ≤ outsideBlock Γ A ∧
          (R.interior i).length ≤ h ∧ ∀ x ∈ R.interior i, x ∉ Z := by
  obtain ⟨N₀,N₁,hExec⟩ := exists_completed_round_uniform_in_density.{u,v} ν τ α d₀ ρ η hν
    hντ hτα hα hd₀ hρ hη hGap hScale
  refine ⟨N₀,N₁,?_⟩
  intro δ hδ₀ hδ₁
  have hδ := hd₀.trans_le hδ₀
  intro V _ I _ D Γ L long A Z r s t h ε
  dsimp only
  intro hLong hA hZ hPos hN₀ hN₁ hR hΓIn hΓOut hR' hs hLen hBudget hIn hOut
    hProfile hSlack hCount hTo hFrom
  let B : Finset V := Aᶜ
  let q := L.boundary.card+(univ \ insert long L.fixed).card*h
  let e : A ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  obtain ⟨S,hKeep,hShort⟩ := exists_shortPortion_outside_block Γ A L long Z hA hZ hR' hs
    hLen (by simpa only [Nat.add_assoc] using hBudget) hIn
    (fun v => by simpa only [Nat.add_assoc] using hOut v)
  let Y := S.denseVertices A
  let d : Y ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let a := L.source long
  let b := L.target long
  have hY : Y ⊆ B := fun v hv =>
    mem_compl.mpr ((mem_filter.mp hv).2.2)
  have hLoss : (B \ Y).card ≤ q := S.dense_trim_bound A h (fun i hi => (hShort i hi).1)
  have hEq := card_sdiff_add_card_eq_card hY
  have hN' : N₁ ≤ Fintype.card (Option Y) := by
    simp only [Fintype.card_option,Fintype.card_coe]
    change N₁+q ≤ B.card at hN₁
    omega
  have ha : a ∈ B := mem_compl.mpr (disjoint_left.mp hA (L.ends long).1)
  have hb : b ∈ B := mem_compl.mpr (disjoint_left.mp hA (L.ends long).2.1)
  have hRep (c : V) (hc : c ∈ B) (x : Option Y) : x.elim c d ∈ B := by
    cases x with
    | none => exact hc
    | some v => exact hY v.prop
  have hSize : (Fintype.card (Option Y):ℝ) ≤ (B.card:ℝ)+1 := by
    simp only [Fintype.card_option,Fintype.card_coe,Nat.cast_add,Nat.cast_one]
    exact_mod_cast Nat.add_le_add_right (card_le_card hY) 1
  have hCount' := (mul_le_mul_of_nonneg_left hSize hρ.le).trans hCount
  have hTwo := mul_le_mul_of_nonneg_left hSize (show 0 ≤ 2*ρ by positivity)
  have hCard (P : V → Prop) : ((univ : Finset A).filter (fun w => P (e w))).card =
      (A.filter P).card := by
    apply card_bij (fun w _ => w.val)
    · intro w hw
      exact mem_filter.mpr ⟨w.prop,(mem_filter.mp hw).2⟩
    · intro w _ z _ hz
      exact Subtype.ext hz
    · intro w hw
      exact ⟨⟨w,(mem_filter.mp hw).1⟩,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hw).2⟩,rfl⟩
  obtain ⟨R,hOld,hGraph,hShortGraph⟩ := hExec δ hδ₀ hδ₁ D Γ (outsideBlock Γ A) L long A S
    hLong hPos hN₀ hN' hKeep hR hΓIn hΓOut
    (fun x => marker_real_bounds B Y hY q _ _ hLoss δ ε η hδ.le hδ₁ hη.le hSlack
      (hProfile _ (hRep b hb x)).1 (dense_marker_inDegree_bounds D e B Y hY a b x))
    (fun x => marker_real_bounds B Y hY q _ _ hLoss δ ε η hδ.le hδ₁ hη.le hSlack
      (hProfile _ (hRep a ha x)).2 (dense_marker_outDegree_bounds D e B Y hY a b x))
    (by simpa only [Fintype.card_coe] using hCount')
    (fun x => by
      change 2*ρ*(Fintype.card (Option Y):ℝ) ≤
        (((univ : Finset A).filter (fun w => D.Adj (x.elim a d) (e w))).card:ℝ)
      rw [hCard]
      exact hTwo.trans (hTo _ (hRep a ha x)))
    (fun x => by
      change 2*ρ*(Fintype.card (Option Y):ℝ) ≤
        (((univ : Finset A).filter (fun w => D.Adj (e w) (x.elim b d))).card:ℝ)
      rw [hCard (fun w => D.Adj w (x.elim b d))]
      exact hTwo.trans (hFrom _ (hRep b hb x)))
  have hHost : outsideBlock Γ A ⊔ mixed D (induced Γ A) e ≤ D ⊔ Γ := by
    intro x y hy
    rcases hy with ⟨hΓ,_,_⟩ | ⟨p,q,hΓ,hp,hq⟩ | ⟨_,hD⟩
    · exact Or.inr hΓ
    · exact Or.inr (hp ▸ hq ▸ hΓ)
    · exact Or.inl hD
  exact ⟨R.rehost hHost,hGraph,fun i hi =>
    ⟨hShortGraph i hi,by simpa only [Realization.rehost,hOld i hi] using hShort i hi⟩⟩

theorem exists_layout_round_threshold (ν τ α δ ρ : ℝ) (hν : 0 < ν)
    (hντ : ν ≤ τ) (hτα : 256*τ ≤ α) (hα : α ≤ 1)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hρ : 0 < ρ) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ N₁ : ℕ, ∀ {V : Type u} [Fintype V] {I : Type v} [Fintype I]
      (D Γ : Digraph V) (L : Layout V I) (long : I) (A Z : Finset V)
      (r s t h : ℕ) (ε : ℝ),
      let B : Finset V := Aᶜ
      let q := L.boundary.card+(univ \ insert long L.fixed).card*h
      let e : A ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
      long ∉ L.fixed → Disjoint L.boundary A → Disjoint L.boundary Z →
      0 < A.card → N₀ ≤ A.card → N₁+q ≤ B.card →
      IsRealRobust (induced Γ A) ν τ →
      (∀ v : A, α*(Fintype.card A:ℝ) ≤ (inDegree (induced Γ A) v:ℝ)) →
      (∀ v : A, α*(Fintype.card A:ℝ) ≤ (outDegree (induced Γ A) v:ℝ)) →
      IsRobustAt (induced Γ B) r t → 0 < s → Fintype.card B/s+5 ≤ h →
      Z.card+q+s ≤ r →
      (∀ v : B, t ≤ inDegree (induced Γ B) v) →
      (∀ v : B, t+Z.card+q+1 ≤ outDegree (induced Γ B) v) →
      ProfilesAround D B δ ε →
      ε*(B.card:ℝ)+(q:ℝ)+1 ≤ η*((B.card:ℝ)-q) →
      ρ*((B.card:ℝ)+1) ≤ (ν/4)^3*(A.card:ℝ) →
      (∀ y ∈ B, 2*ρ*((B.card:ℝ)+1) ≤ ((A.filter (fun w => D.Adj y w)).card:ℝ)) →
      (∀ y ∈ B, 2*ρ*((B.card:ℝ)+1) ≤ ((A.filter (fun w => D.Adj w y)).card:ℝ)) →
      ∃ R : Realization (D ⊔ Γ) L,
        wordGraph (R.word long) ≤ mixed D (induced Γ A) e ∧
        ∀ i ∉ insert long L.fixed, wordGraph (R.word i) ≤ outsideBlock Γ A ∧
          (R.interior i).length ≤ h ∧ ∀ x ∈ R.interior i, x ∉ Z := by
  let η := min (δ/8) (ρ*δ/52)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hGap : 8*η ≤ δ := by
    have h : η ≤ δ/8 := min_le_left _ _
    linarith only [h]
  have hScale : 52*η ≤ ρ*δ := by
    have h : η ≤ ρ*δ/52 := min_le_right _ _
    linarith only [h]
  obtain ⟨N₀,N₁,hN⟩ := exists_layout_round_uniform_in_density.{u,v} ν τ α δ ρ η
    hν hντ hτα hα hδ hρ hη hGap hScale
  exact ⟨η,hη,N₀,N₁,hN δ le_rfl hδ₁⟩

end OverfullWork.DirectedSpanningConfiguration
