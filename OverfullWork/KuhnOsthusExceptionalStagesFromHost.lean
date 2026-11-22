module

public import OverfullWork.KuhnOsthusSetupFromRobustHost
public import OverfullWork.KuhnOsthusStageFromInitialPartition
public import OverfullWork.KuhnOsthusInitialDegreeSchedule
public import OverfullWork.KuhnOsthusFinalReservationMargins
public import OverfullWork.KuhnOsthusPreprocessingDegreeBudgets

@[expose] public section


/-! Prepare the three applications of Lemma 7.6 on the same physical
partition, with the rounded degree schedule of (11.7)–(11.14). -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
universe u

/-- The degree schedule pays the window, expansion and semidegree
conditions of the final degree correction in Lemma 8.6. -/
theorem kuhn_osthus_preprocessing_host_budgets {V : Type*} [Fintype V]
    (Z : Finset V) (p D a r₁ r : ℕ) (ν τ α ζ d₁ : ℝ)
    (hν : 0 < ν) (hτ : 0 ≤ τ) (hTau : 4*τ ≤ α) (hτ₁ : 2*τ ≤ 1)
    (hζ : 0 ≤ ζ) (hζHalf : ζ ≤ 1/2) (hd₁ : 0 ≤ d₁)
    (hSizeZ : (Z.card:ℝ) ≤ ζ*(Fintype.card V:ℝ))
    (hBudgetν : 22*d₁+4*ζ ≤ ν/2) (hBudgetα : 22*d₁+4*ζ ≤ α)
    (hR₁ : (r₁:ℝ) ≤ d₁*(Fintype.card V:ℝ))
    (hD : D ≤ p) (ha : a ≤ p) (hp : p ≤ r₁)
    (hLarge : 2 ≤ α*(Fintype.card V:ℝ)) (hDense : (8*α)*(Fintype.card V:ℝ) ≤ (r:ℝ)) :
    τ*(Fintype.card V:ℝ) ≤ (2*τ)*(Zᶜ.card:ℝ) ∧
      (1-2*τ)*(Zᶜ.card:ℝ) ≤ (1-τ)*(Fintype.card V:ℝ) ∧
      (ν/16)*(Zᶜ.card:ℝ)+(Z.card:ℝ)+((D+a:ℕ):ℝ) ≤ ν*(Fintype.card V:ℝ) ∧
      2*⌈(2*τ)*(Zᶜ.card:ℝ)⌉₊+p+(D+a)+Z.card ≤ r := by
  have hN : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hHalf : 2*Z.card ≤ Fintype.card V := by
    exact_mod_cast (show (2:ℝ)*(Z.card:ℝ) ≤ Fintype.card V by
      linarith only [hSizeZ,mul_le_mul_of_nonneg_right hζHalf hN])
  obtain ⟨hLow,hHigh⟩ := preprocessing_ordinary_width Z τ hτ hτ₁ hHalf
  refine ⟨hLow,hHigh,?_,?_⟩
  all_goals have hOrd : (Zᶜ.card:ℝ) ≤ Fintype.card V := by exact_mod_cast card_le_univ Zᶜ
  · have hPaid : ((D+a:ℕ):ℝ) ≤ 2*(r₁:ℝ) := by exact_mod_cast (show D+a ≤ 2*r₁ by omega)
    have hRate : ν/16+ζ+2*d₁ ≤ ν := by linarith only [hBudgetν,hν,hζ,hd₁]
    linarith only [hPaid,hR₁,hSizeZ,mul_le_mul_of_nonneg_left hOrd (by positivity : 0 ≤ ν/16),
      mul_le_mul_of_nonneg_right hRate hN]
  · let w := ⌈(2*τ)*(Zᶜ.card:ℝ)⌉₊
    have hCeil : (w:ℝ) ≤ (2*τ)*(Zᶜ.card:ℝ)+1 := (Nat.ceil_lt_add_one (by positivity)).le
    have hSpend : ((p+(D+a):ℕ):ℝ) ≤ 3*(r₁:ℝ) := by exact_mod_cast (show p+(D+a) ≤ 3*r₁ by omega)
    have hRate : 4*τ+3*d₁+ζ ≤ 2*α := by linarith only [hTau,hBudgetα,hζ,hd₁]
    have hBound : (2:ℝ)*(w:ℝ)+((p+(D+a):ℕ):ℝ)+(Z.card:ℝ) ≤ (r:ℝ) := by
      have hαN : 0 ≤ α*(Fintype.card V:ℝ) := by linarith only [hLarge]
      linarith only [hCeil,hSpend,hR₁,hSizeZ,hLarge,hDense,hαN,mul_le_mul_of_nonneg_right hRate hN,
        mul_le_mul_of_nonneg_left hOrd (by positivity : 0 ≤ 2*τ)]
    have hBound' : 2*w+(p+(D+a))+Z.card ≤ r := by exact_mod_cast hBound
    simpa only [Nat.add_assoc] using hBound'

set_option maxHeartbeats 3100000 in
/-- Choose the parity rates and cycle density first, then the winding
and the shared small exceptional fraction. Once the cluster count has
an upper bound, fix the preprocessing degrees and one common lower
bound on the actual cell sizes. All three factor constructors are
then available in the successive physical complements. -/
theorem exists_kuhn_osthus_exceptional_stages_from_robust_host
    (ν τ α d θ d₁Max ζMax : ℝ) (l g L : ℕ)
    (hν : 0 < ν) (hν₁ : ν ≤ 1) (hντ : ν ≤ τ)
    (hα : 0 < α) (hα₁ : α ≤ 1) (hTau : 64*τ ≤ α)
    (hd : 0 < d) (hdν : 8*d ≤ ν) (hdα : d ≤ α)
    (hθ : 0 < θ) (hθ₁ : θ < 1) (hd₁Max : 0 < d₁Max) (hζMax : 0 < ζMax)
    (hl : 2 ≤ l) (hg : 2 ≤ g) (hWalk : ⌈25/((ν/8)^2/2)^2⌉₊+4 ≤ L) :
    ∃ d₁ : ℝ, 0 < d₁ ∧ d₁ < d ∧ d₁ ≤ d₁Max ∧
    ∀ (fMin qMin : ℕ) (target : ℝ), 0 < target →
    ∃ (f q b₈ b₁₀ : ℕ) (w₈ : f^2 = l*b₈) (w₉ : f^2 = f*f) (w₁₀ : f^2 = 7*b₁₀),
      fMin ≤ f ∧ qMin ≤ q ∧ g ∣ f ∧ f ∣ q ∧ 0 < q/f ∧ (q/f)*f = q ∧ f ≤ q/f ∧
    ∃ ζ ε ξ σ₈ σ₉ σ₁₀ : ℝ, 0 < ζ ∧ ζ ≤ ζMax ∧ ζ ≤ 1/2 ∧ 0 < ε ∧ 0 < ξ ∧ ξ ≤ target ∧
      0 < σ₈ ∧ 2*σ₈ ≤ d/2 ∧ 0 < σ₉ ∧ 0 < σ₁₀ ∧
      2*ζ ≤ 1/((50*l+1:ℕ):ℝ) ∧ 32*ζ ≤ ν ∧ ζ ≤ (ν/4)^4 ∧
      22*d₁+4*ζ ≤ ν/2 ∧ 22*d₁+4*ζ ≤ α ∧
    ∃ nMax : ℕ, 0 < nMax ∧
    ∀ (d₃Max : ℝ) (ηMax : ℝ → ℝ → ℝ), 0 < d₃Max →
      (∀ x y, 0 < x → 0 < y → 0 < ηMax x y) →
    ∃ d₃ c η : ℝ, 0 < d₃ ∧ 0 < c ∧ 0 < η ∧ c ≤ d₃ ∧ d₃ ≤ d₃Max ∧ η ≤ ηMax d₃ c ∧
    ∀ T : ℕ, ∃ N : ℕ, ∀ {V : Type u} [Fintype V] (G : Digraph V) (r : ℕ),
      N ≤ Fintype.card V → IsRealRobust G ν τ → (8*α)*(Fintype.card V:ℝ) ≤ (r:ℝ) →
      (∀ v, inDegree G v = r ∧ outDegree G v = r) →
      ∃ (k m base m₈ m₉ mWalk : ℕ) (hk : 0 < k) (Z₀ Z : Finset V) (P : Fin k → Finset V)
        (R₀ : Digraph (Fin k)) (A X : Fin (f^2*k) → Finset V)
        (routes : Fin (f^2*k) → List (Fin (f^2*k))) (F : Fin (L+1) → Equiv.Perm (Fin (f^2*k))),
        let n := f^2*k
        let parent := windingParent (n := n) k hk
        let R := fibrePullback R₀ parent parent
        let i₈ : n = l*(b₈*k) := by dsimp only [n]; rw [w₈,Nat.mul_assoc]
        let i₉ : n = f*(f*k) := by dsimp only [n]; rw [w₉,Nat.mul_assoc]
        let i₁₀ : n = 7*(b₁₀*k) := by dsimp only [n]; rw [w₁₀,Nat.mul_assoc]
        let X₈ (i : Fin (l*(b₈*k))) := X (finCongr i₈.symm i)
        let X₉ (i : Fin (f*(f*k))) := X (finCongr i₉.symm i)
        let X₁₀ (i : Fin (7*(b₁₀*k))) := X (finCongr i₁₀.symm i)
        let r₀ := ⌊η*(r:ℝ)⌋₊
        let p := ⌊d₃*(base:ℝ)⌋₊
        let a := 50*l*r₀
        let t := p-a
        let r₁ := ⌊d₁*(base:ℝ)⌋₊
        let r₂ := 96*(L+1)*g^2*n*t
        let D := ⌈c*(base:ℝ)⌉₊
        ∃ (r₃ u : ℕ) (j₈ : 0 < b₈*k) (j₉ : 0 < f*k) (j₁₀ : 0 < b₁₀*k),
          let s := r₁+r₂+t-(q-1)*r₃
          base = 50*m₈ ∧ base = (q/f)*m₉ ∧ f*base = q*m₉ ∧ base = (4*(L+1))*mWalk ∧
          T ≤ m₈ ∧ T ≤ m₉ ∧ T ≤ mWalk ∧ T ≤ base ∧ n ≤ nMax ∧
          2 ≤ (4*τ)*(k:ℝ) ∧ 50*l+1 ≤ n ∧
          14 ∣ n ∧ q ∣ f*n ∧ (∃ p d : ℕ, f*n = p*10 ∧ f*n = d*3*g.choose 2) ∧
          WoundExceptionalPartition G Z₀ Z P A X R₀ hk (f^2) (f^2*m) base α θ ε (ν/8) (4*τ) ∧
          (Z.card:ℝ) ≤ ζ*(Fintype.card V:ℝ) ∧
          (∀ i j, R.Adj i j → IsUniform G ξ (X i) (X j) ∧ d ≤ density G (X i) (X j)) ∧
          (∀ s i, IsLowerSuperregularPair G ξ d (X i) (X (F s i))) ∧
          F 0 = finRotate n ∧ (∀ s i, R.Adj i (F s i)) ∧
          (∀ j, DirectedListRoutes.Route (reindexSources R (finRotate n).symm) j (finRotate n j) (routes j) ∧
            ((routes j).length:ℝ) ≤ 3/((ν/8)^2/2)) ∧
          (∀ x y, ((univ : Finset (Fin (L+1))).filter (fun j => F j x = y)).card =
            elementaryChordMultiplicity (finRotate n) routes x y +
              if finRotate n x = y then L+1 - (∑ z, elementaryChordMultiplicity (finRotate n) routes x z) else 0) ∧
          HasSpanningCycle (fun e f : (Σ _ : Fin (L+1), Fin n) => F e.1 e.2 = f.2) ∧
          0 < r₀ ∧ (r₀:ℝ) ≤ c*(base:ℝ) ∧ a+t = p ∧ p*n^2 ≤ r₁ ∧ r₁ ≤ base ∧ t*n*f^2 ≤ base ∧
          t*(f*n) = q*r₃ ∧ q*r₃ ≤ r₁ ∧ r₂ ≤ r₁ ∧ r₃ ≤ r₁ ∧ (q-1)*r₃+s = r₁+r₂+t ∧ r₂+t+r₃ ≤ s ∧
          p+r₁+r₂+r₃+6*s ≤ 22*r₁ ∧ D+r₀ ≤ p-u ∧ u ≤ p ∧ p ≤ 2*u ∧
          2*(p-u)*(n*base) ≤ u*⌈(ν/16)*((n*base:ℕ):ℝ)⌉₊ ∧
          2*p*(n*base) ≤ ⌈(ν/16)*((n*base:ℕ):ℝ)⌉₊^2 ∧
          Zᶜ.card = n*base ∧ r ≤ 2*n*base ∧
          τ*(Fintype.card V:ℝ) ≤ (2*τ)*(Zᶜ.card:ℝ) ∧
          (1-2*τ)*(Zᶜ.card:ℝ) ≤ (1-τ)*(Fintype.card V:ℝ) ∧
          (ν/16)*(Zᶜ.card:ℝ)+(Z.card:ℝ)+((D+a:ℕ):ℝ) ≤ ν*(Fintype.card V:ℝ) ∧
          2*⌈(2*τ)*(Zᶜ.card:ℝ)⌉₊+p+(D+a)+Z.card ≤ r ∧
          WoundFactorStage G Z X₈ j₈ 50 m₈ r₀ 0 0 σ₈ ∧
          WoundFactorStage G Z X₉ j₉ (q/f) m₉ r₃ (a+t) a σ₉ ∧
          WoundFactorStage G Z X₁₀ j₁₀ 1 base s (a+t+r₁+r₂+r₃) (a+q*r₃) σ₁₀ := by
  let dLoc := d/2
  have hdLoc : 0 < dLoc := by dsimp only [dLoc]; positivity
  have hdLoc₁ : dLoc ≤ 1 := by dsimp only [dLoc]; linarith only [hdν,hν₁]
  have hμτ : ν/8 ≤ 4*τ := by linarith only [hντ,hν]
  have hτ₁ : 4*τ ≤ 1/4 := by linarith only [hTau,hα₁]
  have hατ : 6*(4*τ) ≤ α := by linarith only [hTau,hντ,hν]
  have hμ : 0 < ν/8 := by positivity
  obtain ⟨σ₁₀,ξ₁₀,ρ₁₀,loss₁₀,hσ₁₀,hξ₁₀,hρ₁₀,hLoss₁₀,_,_,_,hStage₁₀⟩ :=
    exists_kuhn_osthus_wound_stage_with_style_bounds.{u} 1 dLoc α θ (ν/8) (4*τ)
      (by decide) hdLoc hdLoc₁ hα hθ hμ hμτ hτ₁ hατ
  obtain ⟨d₁,ζBudget,hd₁,hd₁₁,hd₁Cap,hR₁₀,hD₁₀,hζBudget,hΖν,hΖPow,hΖν',hΖα⟩ :=
    exists_kuhn_osthus_final_reservation_densities ν α (min d d₁Max) ρ₁₀ loss₁₀ hν hα
      (lt_min hd hd₁Max) hρ₁₀ hLoss₁₀
  refine ⟨d₁,hd₁,hd₁Cap.trans_le (min_le_left _ _),hd₁Cap.le.trans (min_le_right _ _),?_⟩
  intro fMin qMin target hTarget
  obtain ⟨f,q,b₈,b₁₀,hfMin,hqMin,hgf,hfq,hqf,hqEq,hRatio,hb₈,hb₁₀,w₈,w₉,w₁₀⟩ :=
    exists_kuhn_osthus_exceptional_windings l g fMin qMin hl (by omega)
  have hf : 0 < f := by omega
  have hq : 0 < q := by omega
  have hf6 : 6 ≤ f := by omega
  refine ⟨f,q,b₈,b₁₀,w₈,w₉,w₁₀,(le_max_right _ _).trans ((le_max_right _ _).trans hfMin),
    (le_max_right _ _).trans hqMin,hgf,hfq,hqf,hqEq,hRatio,?_⟩
  obtain ⟨σ₈,ξ₈,ρ₈,loss₈,hσ₈,hξ₈,hρ₈,hLoss₈,_,hσ₈d,_,hStage₈⟩ :=
    exists_kuhn_osthus_wound_stage_with_style_bounds.{u} 50 dLoc α θ (ν/8) (4*τ)
      (by decide) hdLoc hdLoc₁ hα hθ hμ hμτ hτ₁ hατ
  obtain ⟨σ₉,ξ₉,ρ₉,loss₉,hσ₉,hξ₉,hρ₉,hLoss₉,_,_,_,hStage₉⟩ :=
    exists_kuhn_osthus_wound_stage_with_style_bounds.{u} (q/f) dLoc α θ (ν/8) (4*τ)
      hqf hdLoc hdLoc₁ hα hθ hμ hμτ hτ₁ hατ
  let ζCap := min (min (1/2:ℝ) ζMax) (min ζBudget (1/(2*((50*l+1:ℕ):ℝ))))
  have hζCap : 0 < ζCap := lt_min (lt_min (by norm_num) hζMax) (lt_min hζBudget (by positivity))
  let B := 23*d₁
  obtain ⟨ζ₈,k₈,hζ₈,hζ₈Cap,hReady₈⟩ := hStage₈ (50*l) B ζCap (by positivity) hζCap
  obtain ⟨ζ₉,k₉,hζ₉,hζ₉Cap,hReady₉⟩ := hStage₉ q B ζCap (by positivity) hζCap
  obtain ⟨ζ₁₀,k₁₀,hζ₁₀,hζ₁₀Cap,hReady₁₀⟩ := hStage₁₀ 7 B ζCap (by positivity) hζCap
  let ζ := min ζ₈ (min ζ₉ ζ₁₀)
  have hζ : 0 < ζ := lt_min hζ₈ (lt_min hζ₉ hζ₁₀)
  have hζ' : ζ ≤ ζCap := (min_le_left _ _).trans hζ₈Cap
  have hζHalf : ζ ≤ 1/2 := hζ'.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hζBudget' : ζ ≤ ζBudget := hζ'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hBudgetν : 22*d₁+4*ζ ≤ ν/2 := by linarith only [hΖν',hζBudget']
  have hBudgetα : 22*d₁+4*ζ ≤ α := by linarith only [hΖα,hζBudget']
  have hζSlots : 2*ζ ≤ 1/((50*l+1:ℕ):ℝ) := by
    have hz := hζ'.trans ((min_le_right _ _).trans
      (show min ζBudget (1/(2*((50*l+1:ℕ):ℝ))) ≤ _ from min_le_right _ _))
    rw [mul_comm (2:ℝ),←div_div] at hz
    linarith only [hz]
  let ξCap := min target (min ξ₈ (min ξ₉ ξ₁₀))
  have hξCap : 0 < ξCap := lt_min hTarget (lt_min hξ₈ (lt_min hξ₉ hξ₁₀))
  let kNeed := k₈+k₉+k₁₀+f+96*(L+1)*g^2+210
  obtain ⟨b,hb,hMod⟩ := exists_kuhn_osthus_cluster_count_modulus f g q (50*l+1) hf hg hq (by omega)
  obtain ⟨ε,ξ,hε,hετ,hθε,hξ,hξc,K,hSetup⟩ :=
    exists_kuhn_osthus_setup_from_robust_host.{u} ν τ α d ζ ξCap θ b (f^2) L f q kNeed
      hν hν₁ hντ hα hα₁ hTau hd hdν hdα hζ hζHalf hξCap hθ₁ hb (by positivity) hq hfq hWalk
  let nMax := f^2*(K+1)
  have hnMax : 0 < nMax := by dsimp only [nMax]; positivity
  refine ⟨ζ,ε,ξ,σ₈,σ₉,σ₁₀,hζ,hζ'.trans ((min_le_left _ _).trans (min_le_right _ _)),hζHalf,hε,hξ,
    hξc.trans (min_le_left _ _),hσ₈,hσ₈d,hσ₉,hσ₁₀,hζSlots,by linarith only [hΖν,hζBudget'],
    hζBudget'.trans hΖPow,hBudgetν,hBudgetα,nMax,hnMax,?_⟩
  intro d₃Max ηMax hd₃Max hηMax
  obtain ⟨M₈,hM₈⟩ := hReady₈ nMax hnMax
  obtain ⟨M₉,hM₉⟩ := hReady₉ nMax hnMax
  obtain ⟨M₁₀,hM₁₀⟩ := hReady₁₀ nMax hnMax
  obtain ⟨d₃,c,η,hd₃,hc,hη,hd₃Bound,hηBound,hExtender,_,_,_,M,hSchedule⟩ :=
    exists_kuhn_osthus_initial_degree_schedule_with_dependent_leftover_bound l f q (L+1) g nMax α (ν/16) d₁ ρ₈ ρ₉ ρ₁₀ loss₉ loss₁₀
      d₃Max ηMax (by omega) hf hq hnMax hα (by positivity) (by linarith only [hν₁]) hd₁ hd₁₁ hρ₈ hρ₉
      hLoss₉ hR₁₀ hD₁₀ hd₃Max hηMax
  have hc₃ : c ≤ d₃ := by
    have hμ₁ : ν/16 ≤ 1 := by linarith only [hν₁]
    linarith only [hExtender,hd₃,mul_le_of_le_one_left hd₃.le hμ₁]
  refine ⟨d₃,c,η,hd₃,hc,hη,hc₃,hd₃Bound,hηBound,?_⟩
  intro T
  let T' := T+M₈+M₉+M₁₀+1
  let baseMin := max (max 50 (q/f)*T') (max M (4*(L+1)*T))
  obtain ⟨N,hN⟩ := hSetup baseMin
  refine ⟨max N ⌈2/α⌉₊,?_⟩
  intro V _ G r hLarge hRob hG hRegular
  obtain ⟨k,m,base,hk,Z₀,Z,P,R₀,A,X,routes,F,hkNeed,hK,hOrder,hDiv,hBaseMin,hBaseDiv,hPart,_,_,hSizeZ,
    hReg,hSuper,hFirst,hF,hRoutes,hMult,hWalk'⟩ :=
    hN G ((le_max_left _ _).trans hLarge) hRob (fun v => ⟨(hRegular v).1.symm ▸ hG,(hRegular v).2.symm ▸ hG⟩)
  let n := f^2*k
  have hn : 0 < n := by dsimp only [n]; positivity
  have hnK : k ≤ n := Nat.le_mul_of_pos_left _ (pow_pos hf 2)
  have hnMax' : n ≤ nMax := Nat.mul_le_mul_left _ (hK.trans (by omega))
  obtain ⟨h14,_,_,_,⟨div,hDivQ⟩,hDivRounds⟩ := hMod k (f^2) hDiv
  obtain ⟨m₈,m₉,_,hBase₈,hBase₉,hBaseQ,_,hT₈,hT₉,hTBase⟩ :=
    kuhn_osthus_exceptional_style_cell_sizes f q (L+1) base T' hq hfq (by omega)
      hBaseDiv ((le_max_left _ _).trans hBaseMin)
  obtain ⟨_,_,hWalkDiv,_⟩ := kuhn_osthus_cluster_size_divisibilities f q (L+1) base hq hfq (by omega) hBaseDiv
  obtain ⟨mWalk,hBaseWalk⟩ := hWalkDiv
  have hTWalk : T ≤ mWalk := by
    apply Nat.le_of_mul_le_mul_left _ (by omega : 0 < 4*(L+1))
    rw [←hBaseWalk]
    exact (le_max_right _ _).trans ((le_max_right _ _).trans hBaseMin)
  have hVol : Z.card+n*base = Fintype.card V :=
    (wound_exceptional_density_of_partition X Z base ζ (fun i => (hPart.fine_size i).1)
      hPart.fine_disjoint hPart.fine_ordinary hPart.fine_cover hζHalf hSizeZ).1
  have hOrd : Zᶜ.card = n*base := by have := card_compl_add_card Z; omega
  have hAmbient : base ≤ Fintype.card V :=
    (Nat.le_mul_of_pos_left _ hn).trans (by rw [←hVol]; exact Nat.le_add_left _ _)
  have hAmbient' : Fintype.card V ≤ 2*n*base := by
    have hZHalf : 2*Z.card ≤ Fintype.card V := by
      exact_mod_cast (show (2:ℝ)*(Z.card:ℝ) ≤ (Fintype.card V:ℝ) by
        linarith only [hSizeZ,mul_le_mul_of_nonneg_right hζHalf (Nat.cast_nonneg (Fintype.card V))])
    rw [Nat.mul_assoc]
    omega
  have hBasePos : 0 < base := by dsimp only [T'] at hTBase; omega
  let first : Fin n := ⟨0,hn⟩
  obtain ⟨v,_⟩ := card_pos.mp (by rw [(hPart.fine_size first).1]; exact hBasePos)
  have hr : r ≤ Fintype.card V := (hRegular v).2.symm ▸ DirectedArcSelection.outDegree_le G v
  have hDense : α*(Fintype.card V:ℝ) ≤ (r:ℝ) := by
    linarith only [hG,mul_nonneg hα.le (Nat.cast_nonneg (Fintype.card V))]
  let r₀ := ⌊η*(r:ℝ)⌋₊
  let p := ⌊d₃*(base:ℝ)⌋₊
  let a := 50*l*r₀
  let t := p-a
  let r₁ := ⌊d₁*(base:ℝ)⌋₊
  let r₂ := 96*(L+1)*g^2*n*t
  let D := ⌈c*(base:ℝ)⌉₊
  obtain ⟨hR₀,hSum,hpK,hr₁,hSparse,hRate₈,hLoss₉',hR₀c,r₃,u,hChord,hQr,hR₂,hR₃,hBal,hSpend,hRate₉,hRate₁₀,
    hLoss₁₀',hTot,hExceptional,hDemand,hLow,hHigh,hSmall,hSquare⟩ :=
    hSchedule n base (Fintype.card V) r m₈ m₉ hn hnMax'
      ((by dsimp only [kNeed] at hkNeed; omega : f ≤ k).trans hnK)
      ((by dsimp only [kNeed] at hkNeed; omega : 96*(L+1)*g^2 ≤ k).trans hnK)
      ⟨div,hDivQ⟩ ((le_max_left _ _).trans ((le_max_right _ _).trans hBaseMin))
      hAmbient hAmbient' hr hDense hBase₈ hBaseQ
  have hj₈ : 0 < b₈*k := Nat.mul_pos (by omega) hk
  have hj₉ : 0 < f*k := Nat.mul_pos hf hk
  have hj₁₀ : 0 < b₁₀*k := Nat.mul_pos (by omega) hk
  have hi₈ : n = l*(b₈*k) := by dsimp only [n]; rw [w₈,Nat.mul_assoc]
  have hSlotOrder : 50*l+1 ≤ n := by
    have hkSmall : 51 ≤ k := by dsimp only [kNeed] at hkNeed; omega
    have hkWound : k ≤ b₈*k := Nat.le_mul_of_pos_left _ (by omega)
    calc
      50*l+1 ≤ l*51 := by omega
      _ ≤ l*(b₈*k) := Nat.mul_le_mul_left l (hkSmall.trans hkWound)
      _ = n := hi₈.symm
  have hi₉ : n = f*(f*k) := by dsimp only [n]; rw [w₉,Nat.mul_assoc]
  have hi₁₀ : n = 7*(b₁₀*k) := by dsimp only [n]; rw [w₁₀,Nat.mul_assoc]
  have hTwoD : 2*dLoc = d := by dsimp only [dLoc]; ring
  have hReg' := hReg
  rw [←hTwoD] at hReg'
  have hSup (i : Fin n) : IsLowerSuperregularPair G ξ (2*dLoc) (X i) (X (finRotate n i)) := by
    rw [hTwoD,←hFirst]
    exact hSuper 0 i
  have hr1R : (r₁:ℝ) ≤ d₁*(base:ℝ) := Nat.floor_le (by positivity)
  have hBaseR : (base:ℝ) ≤ Fintype.card V := by exact_mod_cast hAmbient
  have hHostScale : (2:ℝ) ≤ α*(Fintype.card V:ℝ) := by
    have hCeil : ⌈2/α⌉₊ ≤ Fintype.card V := (le_max_right _ _).trans hLarge
    have hCast : (⌈2/α⌉₊:ℝ) ≤ Fintype.card V := by exact_mod_cast hCeil
    exact mul_comm (Fintype.card V:ℝ) α ▸ (div_le_iff₀ hα).mp ((Nat.le_ceil _).trans hCast)
  have hτ : 0 ≤ τ := hν.le.trans hντ
  have hp : p ≤ r₁ := by
    calc
      p = p*1 := by simp
      _ ≤ p*n^2 := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt (pow_pos hn 2))
      _ ≤ r₁ := hpK
  have ha : a ≤ p := (Nat.le_add_right a t).trans (show a+t = p from hSum).le
  have hD : D ≤ p := (Nat.le_add_right D r₀).trans
    ((show D+r₀ ≤ p-u from hDemand).trans (Nat.sub_le p u))
  obtain ⟨hWidthLow,hWidthHigh,hFlowRobust,hFlowDegree⟩ :=
    kuhn_osthus_preprocessing_host_budgets Z p D a r₁ r ν τ α ζ d₁ hν hτ
      (by linarith only [hTau,hτ]) (by linarith only [hTau,hτ,hα₁]) hζ.le hζHalf hd₁.le hSizeZ
      hBudgetν hBudgetα (hr1R.trans (mul_le_mul_of_nonneg_left hBaseR hd₁.le))
      hD ha hp hHostScale hG
  have hCost (v : ℕ) (hv : v ≤ 23*r₁) : (v:ℝ) ≤ B*(base:ℝ) := by
    have hR : (v:ℝ) ≤ 23*(r₁:ℝ) := by exact_mod_cast hv
    dsimp only [B]
    linarith only [hR,hr1R]
  have hZ (z : ℝ) (hz : ζ ≤ z) : (Z.card:ℝ) ≤ z*(Fintype.card V:ℝ) :=
    hSizeZ.trans (mul_le_mul_of_nonneg_right hz (Nat.cast_nonneg _))
  have hExc₈ : a ≤ 23*r₁ := (le_max_left _ _).trans hExceptional
  have hExc₉ : q*r₃+a ≤ 23*r₁ := ((le_max_left _ _).trans (le_max_right _ _)).trans hExceptional
  have hExc₁₀ : 7*(r₁+r₂+t-(q-1)*r₃)+(a+q*r₃) ≤ 23*r₁ :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hExceptional
  refine ⟨k,m,base,m₈,m₉,mWalk,hk,Z₀,Z,P,R₀,A,X,routes,F,r₃,u,hj₈,hj₉,hj₁₀,
    hBase₈,hBase₉,hBaseQ,hBaseWalk,by dsimp only [T'] at hT₈; omega,by dsimp only [T'] at hT₉; omega,
    hTWalk,by dsimp only [T'] at hTBase; omega,hnMax',hOrder,hSlotOrder,h14,⟨div,hDivQ⟩,hDivRounds,hPart,hSizeZ,hReg,hSuper,hFirst,hF,hRoutes,hMult,hWalk',
    hR₀,hR₀c,hSum,hpK,hr₁,hSparse,hChord,hQr,hR₂,hR₃,hBal,hSpend,hTot,hDemand,hLow,hHigh,hSmall,hSquare,
    hOrd,hr.trans hAmbient',hWidthLow,hWidthHigh,hFlowRobust,hFlowDegree,?_,?_,?_⟩
  · apply hM₈ G Z₀ Z P A X R₀ hl hb₈ hk hi₈ w₈ m₈ (f^2*m) r₀ 0 0 ξ ε
    · rwa [←hBase₈]
    · exact hετ
    · exact hθε
    · dsimp only [kNeed] at hkNeed; omega
    · exact hnMax'
    · exact le_rfl
    · dsimp only [T'] at hT₈; omega
    · exact hξc.trans ((min_le_right _ _).trans (min_le_left _ _))
    · exact hZ ζ₈ (min_le_left _ _)
    · rw [←hBase₈,Nat.add_zero]
      exact hCost a hExc₈
    · exact hRate₈
    · simpa only [Nat.cast_zero] using
        mul_nonneg hLoss₈.le (Nat.cast_nonneg (50*m₈))
    · exact hReg'
    · exact hSup
  · apply hM₉ G Z₀ Z P A X R₀ (by omega) hf6 hk hi₉ w₉ m₉ (f^2*m) r₃ (a+t) a ξ ε
    · rwa [←hBase₉]
    · exact hετ
    · exact hθε
    · dsimp only [kNeed] at hkNeed; omega
    · exact hnMax'
    · rw [hqEq]
    · dsimp only [T'] at hT₉; omega
    · exact hξc.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    · exact hZ ζ₉ ((min_le_right _ _).trans (min_le_left _ _))
    · rw [←hBase₉,hqEq]
      exact hCost _ hExc₉
    · exact hRate₉
    · rwa [←hBase₉,hSum]
    · exact hReg'
    · exact hSup
  · apply hM₁₀ G Z₀ Z P A X R₀ (by decide) hb₁₀ hk hi₁₀ w₁₀ base (f^2*m) _ (a+t+r₁+r₂+r₃)
      (a+q*r₃) ξ ε
    · simpa only [one_mul] using hPart
    · exact hετ
    · exact hθε
    · dsimp only [kNeed] at hkNeed; omega
    · exact hnMax'
    · decide
    · dsimp only [T'] at hTBase; omega
    · exact hξc.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    · exact hZ ζ₁₀ ((min_le_right _ _).trans (min_le_right _ _))
    · simpa only [one_mul] using hCost _ hExc₁₀
    · exact hRate₁₀
    · rw [one_mul]
      have hPre : a+t = p := hSum
      rw [hPre]
      exact hLoss₁₀'
    · exact hReg'
    · exact hSup

end OverfullWork.DirectedRobustExpansion
