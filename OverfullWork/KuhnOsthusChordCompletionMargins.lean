module

public import OverfullWork.KuhnOsthusChordCompletion

@[expose] public section


/-! Explicit margins for Claim 5 of Kühn–Osthus Lemma 9.5.
A bound on the vertices touched in each cluster also supplies a
vertex free in both directions and the lower size of every free side. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
universe u
variable {V : Type u} [Fintype V]

/-- Bound the vertices lost from either side of a cluster by the
full footprint of the prescribed path system. -/
theorem chord_free_slots_of_footprint {I : Type*} (D : Digraph V) (c : V → I)
    (j : I) (m K : ℕ)
    (hSize : (finiteSatisfying (fun v => c v = j)).card = m)
    (hTouch : (finiteSatisfying (fun v => c v = j ∧ IncidentTo D v)).card ≤ K)
    (hRoom : K < m) :
    let A := finiteSatisfying (fun v => c v = j)
    let S := freeOut D c j
    let T := freeIn D c j
    (A \ S).card ≤ K ∧ (A \ T).card ≤ K ∧
      m-K ≤ S.card ∧ m-K ≤ T.card ∧ ∃ v, v ∈ T ∧ v ∈ S := by
  intro A S T
  let P := finiteSatisfying (fun v => c v = j ∧ IncidentTo D v)
  have hS : S ⊆ A := fun v hv => mem_finiteSatisfying.mpr (mem_freeOut.mp hv).1
  have hT : T ⊆ A := fun v hv => mem_finiteSatisfying.mpr (mem_freeIn.mp hv).1
  have hP : P ⊆ A := fun v hv =>
    mem_finiteSatisfying.mpr ((mem_finiteSatisfying (p := fun v => c v = j ∧ IncidentTo D v)).mp hv).1
  have hLossS : (A \ S).card ≤ K := by
    apply le_trans (card_le_card (t := P) ?_) hTouch
    intro v hv
    obtain ⟨hA,hvS⟩ := mem_sdiff.mp hv
    have hC : c v = j := (mem_finiteSatisfying (p := fun v => c v = j)).mp hA
    exact mem_finiteSatisfying.mpr ⟨hC,Or.inl (by
      by_contra! he
      exact hvS (mem_freeOut.mpr ⟨hC,fun ⟨w,hw⟩ => he w hw⟩))⟩
  have hLossT : (A \ T).card ≤ K := by
    apply le_trans (card_le_card (t := P) ?_) hTouch
    intro v hv
    obtain ⟨hA,hvT⟩ := mem_sdiff.mp hv
    have hC : c v = j := (mem_finiteSatisfying (p := fun v => c v = j)).mp hA
    exact mem_finiteSatisfying.mpr ⟨hC,Or.inr (by
      by_contra! he
      exact hvT (mem_freeIn.mpr ⟨hC,fun ⟨w,hw⟩ => he w hw⟩))⟩
  have hCountS := card_sdiff_add_card_eq_card hS
  have hCountT := card_sdiff_add_card_eq_card hT
  have hCountP := card_sdiff_add_card_eq_card hP
  change A.card = m at hSize
  change P.card ≤ K at hTouch
  rw [hSize] at hCountS hCountT hCountP
  obtain ⟨v,hv⟩ := card_pos.mp (show 0 < (A \ P).card by omega)
  obtain ⟨hvA,hvP⟩ := mem_sdiff.mp hv
  have hCv : c v = j := (mem_finiteSatisfying (p := fun v => c v = j)).mp hvA
  have hvI : ¬ IncidentTo D v := fun he => hvP (mem_finiteSatisfying.mpr ⟨hCv,he⟩)
  exact ⟨hLossS,hLossT,by omega,by omega,⟨v,
    mem_freeIn.mpr ⟨hCv,fun h => hvI (Or.inr h)⟩,
    mem_freeOut.mpr ⟨hCv,fun h => hvI (Or.inl h)⟩⟩⟩

/-- Explicit scale choices that suffice for Claim 5 simultaneously
over all rounds. The two budgets bound the footprint in one
cluster and the total number of cycles using the common reserve. -/
theorem exists_chord_completion_of_cluster_budgets (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] {n : ℕ}
      (B L D : Digraph W) (c : W → Fin (n+1)) (q m K : ℕ) (ε : ℝ),
      let s := finRotate (n+1)
      let A (j : Fin (n+1)) := (univ : Finset W).filter (fun v => c v = j)
      L ≤ B → (∀ v, inDegree L v ≤ q ∧ outDegree L v ≤ q) →
      N ≤ m → 0 ≤ ε → ε ≤ ρ/512 →
      (K:ℝ) ≤ (ρ/512)*(m:ℝ) → (q:ℝ) ≤ (ρ/128)^2*(m:ℝ)/16 →
      (∀ j, (A j).card = m) →
      (∀ j, IsSuperregularPair B ε ρ (A j) (A (s j))) →
      IsDirectedPathSystem D →
      (∀ j, (freeOut D c j).card = (freeIn D c (s j)).card) →
      (∀ j, (finiteSatisfying (fun v => c v = j ∧ IncidentTo D v)).card ≤ K) →
      ∃ F : Equiv.Perm W, HasSpanningCycle (fun x y => F x = y) ∧
        (∀ x y, D.Adj x y → F x = y) ∧
        ∀ x, (D ⊔ (B \ L)).Adj x (F x) := by
  let d := ρ/2
  let τ := ρ/64
  let η := ρ/128
  let ν := ρ^2/256
  let δ := η/4
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := by dsimp [η]; linarith
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hρ₂ : ρ^2 ≤ ρ := by nlinarith only [mul_nonneg hρ.le (sub_nonneg.mpr hρ1)]
  have hWidth : η+ν ≤ τ := by dsimp [η,ν,τ]; linarith only [hρ.le,hρ₂]
  have hd : 0 < d := by dsimp [d]; positivity
  have hτ : 16*τ ≤ d := by dsimp [τ,d]; linarith
  have hd1 : d ≤ 1 := by dsimp [d]; linarith
  have hCost : ν ≤ d*τ := by dsimp [ν,d,τ]; nlinarith only [sq_nonneg ρ]
  obtain ⟨N,hN⟩ := exists_chord_path_completion_after_deletion.{u}
    d η ν τ d hν hWidth hη hη1 hτ hd1 hd hCost le_rfl
  refine ⟨max (2*N) ⌈2/η⌉₊,?_⟩
  intro W _ n B L D c q m K ε s A hLB hDeg hm hε hSmall hK hQ hA hPair hPath hBal hTouch
  have hSmall' : ε ≤ η/4 := by dsimp [η]; linarith
  have hK' : (K:ℝ) ≤ (η/4)*(m:ℝ) := by dsimp [η]; linarith
  have hQ' : (q:ℝ) ≤ η^2*(m:ℝ)/16 := hQ
  have hMinM : (2:ℝ)/η ≤ m :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right (2*N) ⌈2/η⌉₊).trans hm)
  have hmη : (2:ℝ) ≤ η*m := by
    have hh := (div_le_iff₀ hη).mp hMinM
    simpa only [mul_comm] using hh
  have hmPos : (0:ℝ) < m := by nlinarith only [hmη,hη.le]
  have hKloss : (K:ℝ) ≤ (m:ℝ)/4 := by
    have hh := mul_le_mul_of_nonneg_right hη1 hmPos.le
    linarith only [hK',hh]
  have hKroom : K < m := by exact_mod_cast (show (K:ℝ) < m by linarith)
  have hCell (j : Fin (n+1)) : finiteSatisfying (fun v => c v = j) = A j := by
    ext v
    simp [A]
  let S (j : Fin (n+1)) := freeOut D c j
  let T (j : Fin (n+1)) := freeIn D c (s j)
  have hFoot (j : Fin (n+1)) :=
    chord_free_slots_of_footprint D c j m K ((congrArg Finset.card (hCell j)).trans (hA j))
      (hTouch j) hKroom
  have hFree (j : Fin (n+1)) : (m:ℝ)-K ≤ ((S j).card:ℝ) := by
    have he : (m:ℝ)-K = ((m-K:ℕ):ℝ) := (Nat.cast_sub hKroom.le).symm
    rw [he]
    exact_mod_cast (hFoot j).2.2.1
  have hFreeT (j : Fin (n+1)) : (m:ℝ)-K ≤ ((T j).card:ℝ) := by
    rw [←hBal j]
    exact hFree j
  have hPay (X : ℕ) (hX : (m:ℝ)-K ≤ X) : ε*(m:ℝ)+K+q ≤ η*X := by
    have h3 : (3:ℝ)*m/4 ≤ X := by linarith
    have hηm := mul_le_mul_of_nonneg_left h3 hη.le
    have hεm := mul_le_mul_of_nonneg_right hSmall' hmPos.le
    have hηsq : η^2 ≤ η := by nlinarith only [mul_nonneg hη.le (sub_nonneg.mpr hη1)]
    have hqm := mul_le_mul_of_nonneg_right hηsq hmPos.le
    nlinarith only [hηm,hεm,hqm,hQ',hK']
  let r (j : Fin (n+1)) := ⌈η*((S j).card:ℝ)⌉₊
  apply hN B L D c q ε ρ δ r hLB hDeg hε (by dsimp [δ]; positivity) hρ1
    (by dsimp [d,η]; linarith) (by dsimp [δ]; linarith only [hSmall'])
  · exact hPair
  · exact hPath
  · exact hBal
  · intro j
    exact (hFoot j).2.2.2.2
  · intro j
    have hmN : (2:ℝ)*N ≤ m := by
      exact_mod_cast (le_max_left (2*N) ⌈2/η⌉₊).trans hm
    exact_mod_cast (show (N:ℝ) ≤ (S j).card by linarith only [hFree j,hKloss,hmN])
  · intro j
    have hHalf : (m:ℝ)/2 ≤ (S j).card := by linarith only [hFree j,hKloss,hmPos]
    have hh := mul_le_mul_of_nonneg_left hHalf (sq_nonneg η)
    change (q:ℝ) ≤ (η/4)*((S j).card:ℝ)*η
    nlinarith only [hh,hQ',mul_nonneg (sq_nonneg η) hmPos.le]
  · intro j
    have hLoss : (((A j \ S j).card):ℝ) ≤ K := by
      exact_mod_cast (show (A j \ S j).card ≤ K from (hCell j) ▸ (hFoot j).1)
    have hA' : (A j).card = m := hA j
    change ε*((A j).card:ℝ)+((A j \ S j).card:ℝ)+q ≤ η*((S j).card:ℝ)
    rw [hA']
    exact (by linarith only [hLoss] : ε*(m:ℝ)+((A j \ S j).card:ℝ)+q ≤ ε*(m:ℝ)+K+q).trans
      (hPay _ (hFree j))
  · intro j
    have hLoss : (((A (s j) \ T j).card):ℝ) ≤ K := by
      exact_mod_cast (show (A (s j) \ T j).card ≤ K from (hCell (s j)) ▸ (hFoot (s j)).2.1)
    have hA' : (A (s j)).card = m := hA (s j)
    change ε*((A (s j)).card:ℝ)+((A (s j) \ T j).card:ℝ)+q ≤ η*((T j).card:ℝ)
    rw [hA']
    exact (by linarith only [hLoss] : ε*(m:ℝ)+((A (s j) \ T j).card:ℝ)+q ≤ ε*(m:ℝ)+K+q).trans
      (hPay _ (hFreeT j))
  · intro j
    have hHalf : (m:ℝ)/2 ≤ (S j).card := by linarith only [hFree j,hKloss,hmPos]
    have hOne : (1:ℝ) ≤ η*((S j).card:ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hHalf hη.le
      linarith only [hh,hmη]
    refine ⟨Nat.ceil_pos.mpr (lt_of_lt_of_le zero_lt_one hOne),Nat.le_ceil _,?_⟩
    have hh := (Nat.ceil_lt_add_one (show 0 ≤ η*((S j).card:ℝ) by positivity)).le
    have hdη : 2*η ≤ d := by dsimp [η,d]; linarith
    have hMul := mul_le_mul_of_nonneg_right hdη (Nat.cast_nonneg (S j).card : (0:ℝ) ≤ _)
    change (⌈η*((S j).card:ℝ)⌉₊:ℝ) ≤ d*((S j).card:ℝ)
    nlinarith only [hh,hOne,hMul]

end OverfullWork.DirectedRobustExpansion
