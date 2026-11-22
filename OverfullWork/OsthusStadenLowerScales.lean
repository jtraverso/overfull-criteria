module

public import OverfullWork.OsthusStadenRedBudgetsFromSizes

@[expose] public section


/-! Choose the small scales of §§5.2–5.9 after the number of subdivisions
and the allowed red load have been fixed. -/
namespace OverfullWork.DirectedRobustExpansion

private theorem exists_pos_below_all (xs : List ℝ) (h : ∀ x ∈ xs, 0 < x) :
    ∃ y : ℝ, 0 < y ∧ ∀ x ∈ xs, y ≤ x := by
  induction xs with
  | nil => exact ⟨1, zero_lt_one, by simp⟩
  | cons a l ih =>
      obtain ⟨b, hb, hbl⟩ := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
      refine ⟨min a b, lt_min (h a (by simp)) hb, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hbl x hx)

/-- The adaptation and exceptional-set tolerances can be chosen jointly.
The rate of the original exceptional set may be any nonnegative number
below the returned limit. -/
theorem exists_osthus_staden_lower_scales
    (s p : ℕ) (α β γ d₀ δ finalLoss redRate : ℝ)
    (hs : 4 ≤ s) (hp : 3 ≤ p) (hα : 0 < α) (hβ : 0 < β)
    (hγ : 0 < γ) (hγ₁ : 5*γ < 1) (hd₀ : 0 < d₀)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hFinal : 0 < finalLoss) (hRed : 0 < redRate) :
    ∃ τ ε εBase excLimit ξ loss err : ℝ,
      let b := ((2*s)*(p*2):ℕ)
      let η := δ/2
      let d := (1-5*γ)*β
      0 < τ ∧ τ ≤ 1/16 ∧ 32*τ ≤ γ*d₀ ∧
      0 < ε ∧ ε ≤ 1 ∧ 4*τ ≤ d-ε ∧ max (2*ε) (ε+4*τ) ≤ η ∧
      (((2*s)*p:ℕ):ℝ)*ε ≤ η ∧ η ≤ 1 ∧
      0 < εBase ∧ εBase ≤ τ/4 ∧ 0 < excLimit ∧
      0 < ξ ∧ ξ ≤ 1/8 ∧ 8*ξ ≤ γ*β ∧ 320*(p:ℝ)*ξ ≤ γ*α ∧
      0 < loss ∧ loss ≤ 1/4 ∧ 16*loss*(b:ℝ) ≤ τ^2/16 ∧
      8*loss ≤ γ*d₀ ∧ 288*loss*(b:ℝ) ≤ (γ/8)*α ∧
      4*loss ≤ ξ ∧ 2*(3*loss)*β ≤ ξ*(redRate/16) ∧
      (s:ℝ)*(8*εBase/(b:ℝ)+9*loss) ≤ γ*α/(180*(p:ℝ)) ∧
      (s:ℝ)*(8*εBase) ≤ γ*α/(3*(p:ℝ)) ∧
      0 < err ∧ err ≤ 1 ∧ 8*err ≤ loss ∧ 4*(err+loss) ≤ ε ∧
      4*err ≤ γ*β ∧ 4*err*(b:ℝ) ≤ β ∧
      (((2*s)*p:ℕ):ℝ)*err ≤ γ*β/8 ∧
      ∀ exc : ℝ, 0 ≤ exc → exc ≤ excLimit →
        exc + 2*loss ≤ 1/2 ∧ exc + 2*loss ≤ finalLoss ∧
        exc+8*εBase ≤ (γ/8)*α ∧ 288*exc*β*(p:ℝ) ≤ α*(redRate/4) := by
  let b := ((2*s)*(p*2):ℕ)
  let c := ((2*s)*p:ℕ)
  let η := δ/2
  let d := (1-5*γ)*β
  have hd : 0 < d := mul_pos (by linarith only [hγ₁]) hβ
  have hη : 0 < η := by dsimp only [η]; positivity
  have hsR : 0 < (s:ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hpR : 0 < (p:ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hbR : 0 < (b:ℝ) := by dsimp only [b]; push_cast; positivity
  have hcR : 0 < (c:ℝ) := by dsimp only [c]; push_cast; positivity
  obtain ⟨τ,hτ,hτs⟩ := exists_pos_below_all [1/16,δ/32,d/16,γ*d₀/32] (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> positivity)
  obtain ⟨ε,hε,hεs⟩ := exists_pos_below_all [δ/8,d/4,η/(c:ℝ)] (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> positivity)
  obtain ⟨εBase,hBase,hBases⟩ := exists_pos_below_all
    [τ/4, (b:ℝ)*(γ*α/(180*(p:ℝ))/(16*(s:ℝ))), γ*α/(24*(s:ℝ)*(p:ℝ)), γ*α/128] (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> positivity)
  obtain ⟨excLimit,hExc,hExcs⟩ := exists_pos_below_all
    [γ*α/16, α*redRate/(1152*β*(p:ℝ)), finalLoss/2, 1/4] (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> positivity)
  obtain ⟨ξ,hξ,hξs⟩ := exists_pos_below_all [1/8,γ*β/8,γ*α/(320*(p:ℝ))] (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> positivity)
  obtain ⟨loss,hLoss,hLosses⟩ := exists_pos_below_all
    [1/8, ε/8, τ^2/(256*(b:ℝ)), γ*d₀/8, ξ/4, ξ*redRate/(96*β),
      γ*α/(2304*(b:ℝ)), γ*α/(180*(p:ℝ))/(18*(s:ℝ)), finalLoss/4] (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> positivity)
  obtain ⟨err,hErr,hErrs⟩ := exists_pos_below_all
    [loss/8,γ*β/4,β/(4*(b:ℝ)),(γ*β/8)/(c:ℝ),1] (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> positivity)
  have hBaseLow : εBase/(b:ℝ) ≤ γ*α/(180*(p:ℝ))/(16*(s:ℝ)) := by
    apply (div_le_iff₀ hbR).mpr
    rw [mul_comm]
    exact hBases _ (by simp)
  have hBaseHalf := (le_div_iff₀ (by positivity : 0 < 16*(s:ℝ))).mp hBaseLow
  have hLossHalf := (le_div_iff₀ (by positivity : 0 < 18*(s:ℝ))).mp
    (hLosses (γ*α/(180*(p:ℝ))/(18*(s:ℝ))) (by simp))
  refine ⟨τ,ε,εBase,excLimit,ξ,loss,err,hτ,hτs _ (by simp),?_,hε,?_,?_,?_,?_,?_,
    hBase,hBases _ (by simp),hExc,hξ,hξs _ (by simp),?_,?_,hLoss,?_,?_,?_,?_,?_,?_,?_,?_,
    hErr,hErrs _ (by simp),?_,?_,?_,?_,?_,?_⟩
  · linarith only [hτs (γ*d₀/32) (by simp)]
  · linarith only [hεs (δ/8) (by simp),hδ₁]
  · linarith only [hτs (d/16) (by simp),hεs (d/4) (by simp),hd]
  · apply max_le <;>
      linarith only [hτs (δ/32) (by simp),hεs (δ/8) (by simp),hδ]
  · have h := (le_div_iff₀ hcR).mp (hεs (η/(c:ℝ)) (by simp))
    change (c:ℝ)*ε ≤ η
    simpa only [mul_comm ε (c:ℝ)] using h
  · linarith only [hδ₁]
  · linarith only [hξs (γ*β/8) (by simp)]
  · have h := (le_div_iff₀ (by positivity : 0 < 320*(p:ℝ))).mp
      (hξs (γ*α/(320*(p:ℝ))) (by simp))
    nlinarith only [h]
  · linarith only [hLosses (1/8) (by simp)]
  · have h := (le_div_iff₀ (by positivity : 0 < 256*(b:ℝ))).mp
      (hLosses (τ^2/(256*(b:ℝ))) (by simp))
    nlinarith only [h]
  · linarith only [hLosses (γ*d₀/8) (by simp)]
  · have h := (le_div_iff₀ (by positivity : 0 < 2304*(b:ℝ))).mp
      (hLosses (γ*α/(2304*(b:ℝ))) (by simp))
    nlinarith only [h]
  · linarith only [hLosses (ξ/4) (by simp)]
  · have h := (le_div_iff₀ (by positivity : 0 < 96*β)).mp
      (hLosses (ξ*redRate/(96*β)) (by simp))
    nlinarith only [h]
  · change (s:ℝ)*(8*εBase/(b:ℝ)+9*loss) ≤ _
    rw [show 8*εBase/(b:ℝ) = 8*(εBase/(b:ℝ)) by ring]
    nlinarith only [hBaseHalf,hLossHalf]
  · apply (le_div_iff₀ (by positivity : 0 < 3*(p:ℝ))).mpr
    have h := (le_div_iff₀ (by positivity : 0 < 24*(s:ℝ)*(p:ℝ))).mp
      (hBases (γ*α/(24*(s:ℝ)*(p:ℝ))) (by simp))
    nlinarith only [h]
  · linarith only [hErrs (loss/8) (by simp)]
  · linarith only [hErrs (loss/8) (by simp),hLosses (ε/8) (by simp),hLoss]
  · linarith only [hErrs (γ*β/4) (by simp)]
  · have h := (le_div_iff₀ (by positivity : 0 < 4*(b:ℝ))).mp
      (hErrs (β/(4*(b:ℝ))) (by simp))
    nlinarith only [h]
  · have h := (le_div_iff₀ hcR).mp (hErrs ((γ*β/8)/(c:ℝ)) (by simp))
    change (c:ℝ)*err ≤ _
    simpa only [mul_comm err (c:ℝ)] using h
  · intro exc _ hExcLe
    have hMax₁ := hExcLe.trans (hExcs (1/4) (by simp))
    have hMax₂ := hExcLe.trans (hExcs (finalLoss/2) (by simp))
    have hMax₃ := hExcLe.trans (hExcs (γ*α/16) (by simp))
    have hMax₄ := (le_div_iff₀ (by positivity : 0 < 1152*β*(p:ℝ))).mp
      (hExcLe.trans (hExcs (α*redRate/(1152*β*(p:ℝ))) (by simp)))
    exact ⟨by linarith only [hMax₁,hLosses (1/8) (by simp)],
      by linarith only [hMax₂,hLosses (finalLoss/4) (by simp)],
      by nlinarith only [hMax₃,hBases (γ*α/128) (by simp)],
      by nlinarith only [hMax₄]⟩

end OverfullWork.DirectedRobustExpansion
