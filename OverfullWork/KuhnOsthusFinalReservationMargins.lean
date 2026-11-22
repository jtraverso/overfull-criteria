module

public import OverfullWork.KuhnOsthusFinalAssembly

@[expose] public section


/-! Pay for the reserves and exceptional cycles before invoking the
approximate decomposition at the end of Theorem 1.2. -/
namespace OverfullWork.DirectedRobustExpansion

open scoped Classical

/-- Fix the cycle density independently of the later winding counts.
The exceptional density may be decreased further when the winding
and routing parameters have been chosen. -/
theorem exists_kuhn_osthus_final_reservation_densities (ν α d ρ loss : ℝ)
    (hν : 0 < ν) (hα : 0 < α) (hd : 0 < d) (hρ : 0 < ρ) (hLoss : 0 < loss) :
    ∃ d₁ ζMax : ℝ, 0 < d₁ ∧ d₁ ≤ 1 ∧ d₁ < d ∧ 3*d₁ ≤ ρ ∧ 4*d₁ ≤ loss ∧
      0 < ζMax ∧ 32*ζMax ≤ ν ∧ ζMax ≤ (ν/4)^4 ∧
      22*d₁+4*ζMax ≤ ν/2 ∧ 22*d₁+4*ζMax ≤ α := by
  let d₁ := min (min 1 (d/2)) (min (ρ/3) (min (loss/4) (min (ν/88) (α/44))))
  let ζMax := min (ν/32) (min ((ν/4)^4) (α/8))
  have hd₁ : 0 < d₁ := lt_min (lt_min (by norm_num) (by positivity))
    (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by positivity))))
  have hζ : 0 < ζMax := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have h₁ : d₁ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have h₂ : d₁ ≤ d/2 := (min_le_left _ _).trans (min_le_right _ _)
  have h₃ : d₁ ≤ ρ/3 := (min_le_right _ _).trans (min_le_left _ _)
  have h₄ : d₁ ≤ loss/4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h₅ : d₁ ≤ ν/88 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have h₆ : d₁ ≤ α/44 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hζν : ζMax ≤ ν/32 := min_le_left _ _
  have hζν' : ζMax ≤ (ν/4)^4 := (min_le_right _ _).trans (min_le_left _ _)
  have hζα : ζMax ≤ α/8 := (min_le_right _ _).trans (min_le_right _ _)
  exact ⟨d₁,ζMax,hd₁,h₁,by linarith only [hd,h₂],by linarith only [h₃],by linarith only [h₄],
    hζ,by linarith only [hζν],hζν',by linarith only [h₅,hζν,hν],by linarith only [h₆,hζα]⟩

/-- The rate of (11.14), the exceptional density, and the rounded
leftover imply the numeric hypotheses of the exact final assembly. -/
theorem kuhn_osthus_final_reservation_budgets
    (n m z r r₁ b r₀ : ℕ) (ν α d₁ ζ η : ℝ)
    (hd₁ : 0 ≤ d₁) (hη : 0 ≤ η) (hm : m ≤ n) (hr : r ≤ n)
    (hDense : 2*α*(n:ℝ) ≤ (r:ℝ)) (hZ : (z:ℝ) ≤ ζ*(n:ℝ))
    (hR₁ : (r₁:ℝ) ≤ d₁*(m:ℝ)) (hB : b ≤ 22*r₁) (hR₀ : (r₀:ℝ) ≤ η*(r:ℝ))
    (hζν : 32*ζ ≤ ν) (hζν' : ζ ≤ (ν/4)^4)
    (hBudget : 22*d₁+4*ζ ≤ ν/2) (hBudget' : 22*d₁+4*ζ ≤ α) (hLeft : η ≤ α) :
    8*(z:ℝ) ≤ (ν/2)*(n:ℝ)/2 ∧ (z:ℝ) ≤ ((ν/2)/2)^4*(n:ℝ) ∧
      b+4*z+r₀ ≤ r ∧ ((b+4*z:ℕ):ℝ) ≤ (ν/2)*(n:ℝ) ∧
      α*(n:ℝ)+((b+4*z:ℕ):ℝ) ≤ (r:ℝ) := by
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hm' : (m:ℝ) ≤ n := by exact_mod_cast hm
  have hr' : (r:ℝ) ≤ n := by exact_mod_cast hr
  have hB' : (b:ℝ) ≤ 22*(r₁:ℝ) := by exact_mod_cast hB
  have hR₁' := hR₁.trans (mul_le_mul_of_nonneg_left hm' hd₁)
  have hTotal : ((b+4*z:ℕ):ℝ) ≤ (22*d₁+4*ζ)*(n:ℝ) := by
    push_cast
    linarith only [hB',hR₁',hZ]
  have hTotal' := hTotal.trans (mul_le_mul_of_nonneg_right hBudget' hn)
  have hR₀' := (hR₀.trans (mul_le_mul_of_nonneg_left hr' hη)).trans (mul_le_mul_of_nonneg_right hLeft hn)
  refine ⟨?_,?_,?_,hTotal.trans (mul_le_mul_of_nonneg_right hBudget hn),?_⟩
  · linarith only [hZ,mul_le_mul_of_nonneg_right hζν hn]
  · have h : ν/4 = (ν/2)/2 := by ring
    rw [←h]
    exact hZ.trans (mul_le_mul_of_nonneg_right hζν' hn)
  · exact_mod_cast (show ((b+4*z:ℕ):ℝ)+(r₀:ℝ) ≤ (r:ℝ) by linarith only [hDense,hTotal',hR₀'])
  · linarith only [hDense,hTotal']

/-- A packing of at least (1−η)r' cycles in the smaller regular
graph suffices for the exact floor of ηr chosen beforehand.
Restrict the supplied pack to leave that preassigned degree. -/
theorem trim_kuhn_osthus_approximate_pack {V : Type*} (G : Digraph V)
    (r r' t : ℕ) (η : ℝ) (hη : 0 ≤ η) (hr : r' ≤ r)
    (ht : (1-η)*(r':ℝ) ≤ (t:ℝ)) (F : Fin t → Equiv.Perm V)
    (hLe : matchingUnion F ≤ G)
    (hCycle : ∀ i, HasSpanningCycle (fun x y => F i x = y))
    (hDisjoint : ∀ i j, i ≠ j → ∀ x, F i x ≠ F j x) :
    ∃ P : Fin (r'-⌊η*(r:ℝ)⌋₊) → Equiv.Perm V, matchingUnion P ≤ G ∧
      (∀ i, HasSpanningCycle (fun x y => P i x = y)) ∧
      ∀ i j, i ≠ j → ∀ x, P i x ≠ P j x := by
  have hBound : r'-⌊η*(r:ℝ)⌋₊ ≤ t := by
    by_cases h : r' ≤ t
    · exact (Nat.sub_le _ _).trans h
    · have htr : t ≤ r' := (Nat.lt_of_not_ge h).le
      have hR : (r':ℝ) ≤ r := by exact_mod_cast hr
      have h := mul_le_mul_of_nonneg_left hR hη
      have hLeft : r'-t ≤ ⌊η*(r:ℝ)⌋₊ := by
        apply Nat.le_floor
        rw [Nat.cast_sub htr]
        linarith only [ht,h]
      omega
  let e : Fin (r'-⌊η*(r:ℝ)⌋₊) ↪ Fin t := ⟨Fin.castLE hBound,Fin.castLE_injective hBound⟩
  refine ⟨fun i => F (e i),?_,fun i => hCycle (e i),fun _ _ h x => hDisjoint _ _ (e.injective.ne h) x⟩
  rintro x y ⟨i,hi⟩
  exact hLe ⟨e i,hi⟩

universe u

open Finset InducedDigraphSampling

set_option maxHeartbeats 700000 in
/-- The exact assembly accepts the relative cycle count of the
approximate decomposition theorem. The same rounded leftover is
used in the preprocessing extension and in the chosen pack size. -/
theorem kuhn_osthus_final_assembly_of_relative_approximate_pack
    (ν τ α d₁ ζ η : ℝ)
    (hν : 0 < ν) (hν₁ : ν ≤ 1) (hντ : ν ≤ τ) (hτα : 128*τ ≤ α) (hα : α ≤ 1)
    (hd₁ : 0 ≤ d₁) (hη : 0 ≤ η) (hLeft : η ≤ α)
    (hζν : 32*ζ ≤ ν) (hζν' : ζ ≤ (ν/4)^4)
    (hBudget : 22*d₁+4*ζ ≤ ν/2) (hBudget' : 22*d₁+4*ζ ≤ α) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [Nonempty V]
      (G P B : Digraph V) (Z : Finset V) (r b t m : ℕ),
      let n := Fintype.card V
      let r₀ := ⌊η*(r:ℝ)⌋₊
      let r' := r-b-4*Z.card
      N ≤ n → m ≤ n → r ≤ n →
      2*α*(n:ℝ) ≤ (r:ℝ) → (Z.card:ℝ) ≤ ζ*(n:ℝ) → b ≤ 22*⌊d₁*(m:ℝ)⌋₊ →
      (∀ v, ¬ G.Adj v v) → (∀ v, inDegree G v = r ∧ outDegree G v = r) →
      IsRealRobust G ν τ → P ⊔ B ≤ G → Disjoint P B →
      (∀ v, inDegree (P ⊔ B) v = b ∧ outDegree (P ⊔ B) v = b) →
      (∀ D : Digraph V, D ≤ G → IsRealRobust D (ν/2) τ →
        (∀ v, inDegree D v = r' ∧ outDegree D v = r') →
        α*(n:ℝ) ≤ (r':ℝ) →
        ∃ (s : ℕ) (F : Fin s → Equiv.Perm V), (1-η)*(r':ℝ) ≤ (s:ℝ) ∧ matchingUnion F ≤ D ∧
          (∀ i, HasSpanningCycle (fun x y => F i x = y)) ∧ ∀ i j, i ≠ j → ∀ x, F i x ≠ F j x) →
      (∀ D : Digraph V, D ≤ G \ (P ⊔ B) →
        (∀ v, inDegree D v = r₀ ∧ outDegree D v = r₀) →
        (∀ x y, x ∈ Z → y ∈ Z → ¬ D.Adj x y) →
        ∃ (s : ℕ) (F : Fin s → Equiv.Perm V), matchingUnion F ≤ P ⊔ D ∧
          (∀ i, HasSpanningCycle (fun x y => F i x = y)) ∧
          (∀ i j, i ≠ j → ∀ v, F i v ≠ F j v) ∧
          let H := (P ⊔ D) \ matchingUnion F
          (∀ x y, H.Adj x y → x ∉ Z ∧ y ∉ Z) ∧
          ∀ v : ↥Zᶜ, inDegree (induced H Zᶜ) v = t ∧ outDegree (induced H Zᶜ) v = t) →
      (∀ H : Digraph V, H ≤ G \ B → (∀ x y, H.Adj x y → x ∉ Z ∧ y ∉ Z) →
        (∀ v : ↥Zᶜ, inDegree (induced H Zᶜ) v = t ∧ outDegree (induced H Zᶜ) v = t) →
        ∃ (s : ℕ) (F : Fin s → Equiv.Perm V), matchingUnion F = H ⊔ B ∧
          (∀ i, HasSpanningCycle (fun x y => F i x = y)) ∧ ∀ i j, i ≠ j → ∀ x, F i x ≠ F j x) →
      Nonempty (DirectedHamiltonDecomposition G r) := by
  obtain ⟨N,hN⟩ := kuhn_osthus_final_assembly_from_reserves.{u} ν τ α hν hν₁ hντ hτα hα
  refine ⟨N,?_⟩
  intro V _ _ G P B Z r b t m n r₀ r' hNSize hm hr hDense hZ hB hLoop hReg hRob hPB hApart hReserve
    hApprox hProcess hAbsorb
  let r₁ := ⌊d₁*(m:ℝ)⌋₊
  have hR₁ : (r₁:ℝ) ≤ d₁*(m:ℝ) := Nat.floor_le (by positivity)
  have hR₀ : (r₀:ℝ) ≤ η*(r:ℝ) := Nat.floor_le (by positivity)
  obtain ⟨hExc,hSize,hRoom,hLoss,hLeftDense⟩ :=
    kuhn_osthus_final_reservation_budgets n m Z.card r r₁ b r₀ ν α d₁ ζ η hd₁ hη hm hr
      hDense hZ hR₁ hB hR₀ hζν hζν' hBudget hBudget' hLeft
  refine hN G P B Z r b r₀ t hNSize hLoop hReg hRob hPB hApart hReserve
    hExc hSize hRoom hLoss hLeftDense ?_ hProcess hAbsorb
  intro D hD hDRob hDReg hDDense
  obtain ⟨s,F,hRate,hLe,hCycle,hDisjoint⟩ := hApprox D hD hDRob hDReg hDDense
  exact trim_kuhn_osthus_approximate_pack D r r' s η hη
    ((Nat.sub_le (r-b) (4*Z.card)).trans (Nat.sub_le r b)) hRate F hLe hCycle hDisjoint

end OverfullWork.DirectedRobustExpansion
