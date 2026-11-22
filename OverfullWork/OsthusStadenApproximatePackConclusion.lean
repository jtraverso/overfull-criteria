module

public import OverfullWork.OsthusStadenRoundedPackMargins

@[expose] public section


/-! Recover the existence assertion of §5.11 from the refined family,
using the order identity for an adapted partition. -/
namespace OverfullWork.DirectedRobustExpansion

open DirectedClusterQuotient
open scoped Classical
universe u v

/-- One common tolerance pays for the reduced floor, the two unwinding
losses, the physical floor and the exceptional vertices. The lower
bound on the cell size is uniform in the host and its degree. -/
theorem osthus_staden_approximate_conclusion_from_refined_pack
    (α β γ η : ℝ) (s p Kmin : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (hη : 0 < η)
    (hγMain : γ ≤ (η/5)*α/2) (hγLocal : 12*γ ≤ η/5)
    (hβMain : β ≤ (η/5)*α*(Kmin:ℝ)/2)
    (hS : 1 ≤ (η/5)*((2*s:ℕ):ℝ)) (hP : 1 ≤ (η/5)*(p:ℝ)) :
    ∃ mMin : ℕ, ∀ {V : Type u} [Fintype V] {I : Type v} [Fintype I]
      (G : Digraph V) (f : V → Option I) (m r r₀ κ : ℕ) (a : ℝ),
      mMin ≤ m → Kmin ≤ Fintype.card I → α ≤ a →
      a*(Fintype.card V:ℝ) = (r:ℝ) →
      r₀ = ⌊(a-γ)*(Fintype.card I:ℝ)/β⌋₊ →
      κ = ⌊(1-γ)*(1-5*γ)*β*((2*m:ℕ):ℝ)⌋₊ →
      (∀ i, (cluster f i).card = (2*s)*(p*(2*m))) →
      ((exceptional f).card:ℝ) ≤ (η/5)*(Fintype.card V:ℝ) →
      ∀ Pack : Fin (r₀*((2*s-1)*(p-1))*κ) → Equiv.Perm V,
        (∀ i, HasSpanningCycle (fun x y => Pack i x = y)) →
        (∀ i x, G.Adj x (Pack i x)) →
        (∀ i k, i ≠ k → ∀ x, Pack i x ≠ Pack k x) →
        ∃ (t : ℕ) (C : Fin t → Equiv.Perm V), (1-η)*(r:ℝ) ≤ (t:ℝ) ∧
          matchingUnion C ≤ G ∧ (∀ i, HasSpanningCycle (fun x y => C i x = y)) ∧
          ∀ i k, i ≠ k → ∀ x, C i x ≠ C k x := by
  let e := η/5
  have he : 0 < e := by dsimp only [e]; positivity
  change γ ≤ e*α/2 at hγMain
  change 12*γ ≤ e at hγLocal
  change β ≤ e*α*(Kmin:ℝ)/2 at hβMain
  obtain ⟨mMin,hmMin⟩ := exists_nat_ge (1/(e*β))
  refine ⟨mMin,?_⟩
  intro V _ I _ G f m r r₀ κ a hm hK ha hr hr₀ hκ hCell hExc Pack hCycles hArc hDis
  change ((exceptional f).card:ℝ) ≤ e*(Fintype.card V:ℝ) at hExc
  have hKR : (Kmin:ℝ) ≤ (Fintype.card I:ℝ) := by exact_mod_cast hK
  have hmR : (mMin:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hRet := (div_le_iff₀ (mul_pos he hβ)).mp (hmMin.trans hmR)
  have hRound : 1 ≤ (e-6*γ)*(β*((2*m:ℕ):ℝ)) := by
    rw [Nat.cast_mul,Nat.cast_ofNat]
    calc
      _ ≤ (m:ℝ)*(e*β) := hRet
      _ = (e/2)*(β*(2*(m:ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hγLocal]) (by positivity)
  have hOrig : γ*(Fintype.card I:ℝ)+β ≤ e*(a*(Fintype.card I:ℝ)) := by
    have h₁ := mul_le_mul_of_nonneg_right hγMain (Nat.cast_nonneg (α := ℝ) (Fintype.card I))
    have h₂ := mul_le_mul_of_nonneg_left hKR (show 0 ≤ e*α/2 by positivity)
    have h₃ := mul_le_mul_of_nonneg_right ha (show 0 ≤ e*(Fintype.card I:ℝ) by positivity)
    nlinarith only [hβMain,h₁,h₂,h₃]
  have hOrder : (Fintype.card V:ℝ) = ((exceptional f).card:ℝ) +
      (Fintype.card I:ℝ)*((((2*s)*p*(2*m)):ℕ):ℝ) := by
    have h := order_eq f ((2*s)*(p*(2*m))) hCell
    rw [← Nat.mul_assoc, Nat.mul_comm _ (Fintype.card I)] at h
    exact_mod_cast h
  have hVol : (1-e)*(Fintype.card V:ℝ) ≤
      (Fintype.card I:ℝ)*((((2*s)*p*(2*m)):ℕ):ℝ) := by
    linarith only [hOrder,hExc]
  have hs : 0 < s := by by_contra! hs; norm_num [Nat.eq_zero_of_le_zero hs] at hS
  have hp : 0 < p := by by_contra! hp; norm_num [Nat.eq_zero_of_le_zero hp] at hP
  refine ⟨_,Pack,?_,?_,hCycles,hDis⟩
  · exact osthus_staden_cycle_count_of_rounded_degrees r₀ s p κ (Fintype.card I) m (Fintype.card V) r
      a β γ η e e e e e (hα.le.trans ha) hβ hs hp he.le he.le he.le he.le he.le
      hr hr₀ hκ hOrig hS hP hRound hVol (by dsimp only [e]; linarith)
  · rintro x y ⟨i,h⟩
    exact h ▸ hArc i x

end OverfullWork.DirectedRobustExpansion
