module

public import OverfullWork.CMSOperation42TerminalExclusion

@[expose] public section


/-! In the last step of Operation 4.2 the density, deficit budget and
size of the exceptional set imply the numerical guards of the three
regularization cases with a single choice of scales. -/
namespace OverfullWork.CMSMatchingRemoval

open Finset SimpleGraph RobustExpansion
open NormalizedClassTwoStep
open scoped Classical
universe u

set_option maxHeartbeats 2600000 in
theorem cms_no_matching_removal_terminal_of_small_budgets (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ σ : ℝ,0 < σ ∧ ∀ ν : ℝ,0 < ν → ν ≤ σ/4 →
      ∃ ηMax : ℝ,0 < ηMax ∧ ∀ η : ℝ,0 < η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V] {B K : ℕ} (s : State V B K),
          let G := s.graph
          let X := s.cut.set
          let n := Fintype.card V
          let d := G.maxDegree
          N+K+2 ≤ n → α*(n:ℝ) ≤ (d:ℝ) →
          ((B+4:ℕ):ℝ) ≤ η*((n-K-1:ℕ):ℝ) →
          ((K+1:ℕ):ℝ) ≤ 2*η^2*((n-K-1:ℕ):ℝ) →
          IsRealRobust G (8*ν) σ → IsMatchingRemovalStop G X → False := by
  obtain ⟨σ,φ,hσ,hφ,hσφ,hφMax,hUse⟩ :=
    cms_no_matching_removal_terminal_bounded_interval.{u} α hα hα₁
  refine ⟨σ,hσ,?_⟩
  intro ν hν hνσ
  obtain ⟨η₀,hη₀,hUse⟩ := hUse ν hν hνσ
  let ηMax := min η₀ (min 1 (ν/4))
  refine ⟨ηMax,by dsimp only [ηMax]; positivity,?_⟩
  intro η hη hηMax
  have hη1 : η ≤ 1 := (hηMax.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hην : η ≤ ν/4 := (hηMax.trans (min_le_right _ _)).trans (min_le_right _ _)
  obtain ⟨N₀,hUse⟩ := hUse η hη (hηMax.trans (min_le_left _ _))
  let N := max N₀ (max ⌈16/α⌉₊ (max ⌈4/φ⌉₊ ⌈16/ν^2⌉₊))
  refine ⟨N,?_⟩
  intro V _ _ B K s G X n d hn hDens hB₀ hK₀ hRob hStop
  have hLarge (t : ℝ) (ht : ⌈t⌉₊ ≤ N) : t ≤ (n:ℝ) :=
    (Nat.le_ceil t).trans (by exact_mod_cast (show ⌈t⌉₊ ≤ n by omega))
  have hA : 16 ≤ α*(n:ℝ) := by
    have hi := hLarge (16/α) ((le_max_left _ _).trans (le_max_right _ _))
    simpa only [mul_comm α] using (div_le_iff₀ hα).mp hi
  have hPhi : 4 ≤ φ*(n:ℝ) := by
    have hi := hLarge (4/φ) (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _))
    simpa only [mul_comm φ] using (div_le_iff₀ hφ).mp hi
  have hNu : 16 ≤ ν^2*(n:ℝ) := by
    have hi := hLarge (16/ν^2) (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _))
    simpa only [mul_comm (ν^2)] using (div_le_iff₀ (by positivity : 0 < ν^2)).mp hi
  have hnR : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hνn : ν ≤ α/512 := by linarith only [hνσ,hσφ,hφMax]
  have hν1 : ν ≤ 1/512 := by linarith only [hνn,hα₁]
  have hNop : ((n-K-1:ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast (show n-K-1 ≤ n by omega)
  have hSmallB : (B:ℝ) ≤ ν*(n:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hNop hη.le
    have h' := mul_le_mul_of_nonneg_right (show η ≤ ν by linarith only [hην,hν]) hnR
    push_cast at hB₀
    linarith only [h,h',hB₀]
  have hSmallK : ((K+1:ℕ):ℝ) ≤ (ν/2)*(n:ℝ) := by
    have hηsq : η^2 ≤ η := by nlinarith only [mul_nonneg hη.le (sub_nonneg.mpr hη1)]
    have h := mul_le_mul_of_nonneg_left hNop (by positivity : 0 ≤ 2*η^2)
    have h' := mul_le_mul_of_nonneg_right (show 2*η^2 ≤ ν/2 by linarith only [hηsq,hην]) hnR
    linarith only [hK₀,h,h']
  have hνD := mul_le_mul_of_nonneg_right hνn hnR
  have hνN := mul_le_mul_of_nonneg_right hν1 hnR
  have hSmallRoom : B+7 ≤ d := by
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    linarith only [hSmallB,hνD,hA,hDens]
  have hHalfB : 2*B < d+2 := by
    apply (Nat.cast_lt (α := ℝ)).mp
    push_cast
    linarith only [hSmallB,hνD,hA,hDens]
  have hHalfK : 2*K+2 ≤ d := by
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast at hSmallK ⊢
    linarith only [hSmallK,hνD,hA,hDens]
  have hB2K : B+2*K ≤ n := by
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast at hSmallK ⊢
    linarith only [hSmallB,hSmallK,hνN,hnR]
  have hX : X.card+Xᶜ.card = n := card_add_card_compl X
  have hK : Xᶜ.card ≤ K := s.cut.complement_small
  have hRoomX : B+K ≤ X.card := by omega
  have hMax : ((max B (K+1):ℕ):ℝ) ≤ ν*(n:ℝ) := by
    rw [Nat.cast_max]
    exact max_le hSmallB (hSmallK.trans (by linarith only [mul_nonneg hν.le hnR]))
  have hInterval : 4*(K:ℝ) ≤ σ*(n:ℝ) := by
    have h := mul_le_mul_of_nonneg_right hνσ hnR
    push_cast at hSmallK
    linarith only [h,hSmallK]
  have hAtLeast : (3/4)*(n:ℝ) ≤ ((n-K:ℕ):ℝ) := by
    rw [Nat.cast_sub (show K ≤ n by omega)]
    push_cast at hSmallK
    linarith only [hSmallK,hνN,hnR]
  have hGap : φ*(n:ℝ)+2 ≤ 2*φ*((n-K:ℕ):ℝ) := by
    have h := mul_le_mul_of_nonneg_left hAtLeast (show 0 ≤ 2*φ by positivity)
    linarith only [hPhi,h]
  let r := ⌈(ν/2)*((n-K:ℕ):ℝ)⌉₊
  have hr : (ν/4)*(n:ℝ) ≤ (r:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hAtLeast (show 0 ≤ ν/2 by positivity)
    have h' : (ν/2)*((n-K:ℕ):ℝ) ≤ (r:ℝ) := Nat.le_ceil _
    linarith only [h,h',mul_nonneg hν.le hnR]
  have hRate : d ≤ r*r := by
    have h₁ := mul_self_le_mul_self (show 0 ≤ (ν/4)*(n:ℝ) by positivity) hr
    have h₂ := mul_le_mul_of_nonneg_right hNu hnR
    have hd : (d:ℝ) ≤ (n:ℝ) := by
      letI : Nonempty V := Fintype.card_pos_iff.mp (show 0 < n by omega)
      exact_mod_cast (G.maxDegree_lt_card_verts.le)
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    nlinarith only [h₁,h₂,hd]
  have hCut : ⌈(2*φ)*(n:ℝ)⌉₊+B+2*K ≤ d := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ (2*φ)*(n:ℝ) by positivity)
    have hScale := mul_le_mul_of_nonneg_right hφMax hnR
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast at hSmallK ⊢
    linarith only [h,hScale,hSmallB,hSmallK,hνD,hDens,hA]
  exact hUse s (by dsimp only [N] at hn; omega) hDens hSmallRoom hHalfB hHalfK hRoomX
    hB₀ hK₀ hMax hSmallK hInterval hGap hRate hCut hRob hStop

end OverfullWork.CMSMatchingRemoval
