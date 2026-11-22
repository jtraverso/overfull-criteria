module

public import OverfullWork.CMSOperation42EmptyComplement
public import OverfullWork.CMSOperation42SingleCentreBounds
public import OverfullWork.CMSSecondLowCleanup

@[expose] public section


/-! All three stopping alternatives of Operation 4.2 are incompatible
with the class-two obstruction once the displayed scale inequalities
hold on their actual ambient graph. -/
namespace OverfullWork.CMSMatchingRemoval

open Finset SimpleGraph RobustExpansion CanonicalRegularization
open NormalizedClassTwoStep
open scoped Classical
universe u

set_option maxHeartbeats 2400000 in
theorem cms_no_matching_removal_terminal_bounded_interval (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ σ φ : ℝ,0 < σ ∧ 0 < φ ∧ σ ≤ φ ∧ φ ≤ α/128 ∧ ∀ ν : ℝ,0 < ν → ν ≤ σ/4 →
      ∃ ηMax : ℝ,0 < ηMax ∧ ∀ η : ℝ,0 < η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V] {B K : ℕ} (s : State V B K),
          let G := s.graph
          let X := s.cut.set
          let n := Fintype.card V
          let d := G.maxDegree
          let r₀ := ⌈(ν/2)*((n-K:ℕ):ℝ)⌉₊
          N+K+2 ≤ n → α*(n:ℝ) ≤ (d:ℝ) → B+7 ≤ d →
          2*B < d+2 → 2*K+2 ≤ d → B+K ≤ X.card →
          ((B+4:ℕ):ℝ) ≤ η*((n-K-1:ℕ):ℝ) →
          ((K+1:ℕ):ℝ) ≤ 2*η^2*((n-K-1:ℕ):ℝ) →
          ((max B (K+1):ℕ):ℝ) ≤ ν*(n:ℝ) →
          ((K+1:ℕ):ℝ) ≤ (ν/2)*(n:ℝ) → 4*(K:ℝ) ≤ σ*(n:ℝ) →
          φ*(n:ℝ)+2 ≤ 2*φ*((n-K:ℕ):ℝ) → d ≤ r₀*r₀ →
          ⌈(2*φ)*(n:ℝ)⌉₊+B+2*K ≤ d →
          IsRealRobust G (8*ν) σ → IsMatchingRemovalStop G X → False := by
  obtain ⟨σ₀,hσ₀,hZero⟩ := cms_colourable_of_empty_active_complement_stop.{u} α hα hα₁
  obtain ⟨φ,hφ,hφMax,hOne⟩ := cms_colourable_of_robust_merged_source_bounded_interval.{u} α hα hα₁
  obtain ⟨σ₂,hσ₂,hTwo⟩ := cms_no_second_low_terminal_after_cleanup.{u} α hα hα₁
  let σ := min σ₀ (min φ σ₂)
  have hσ : 0 < σ := by dsimp only [σ]; positivity
  have hσ₀' : σ ≤ σ₀ := min_le_left _ _
  have hφ' : σ ≤ φ := (min_le_right _ _).trans (min_le_left _ _)
  have hσ₂' : σ ≤ σ₂ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨σ,φ,hσ,hφ,hφ',hφMax,?_⟩
  intro ν hν hνσ
  obtain ⟨η₀,hη₀,hZero⟩ := hZero ν hν (by linarith only [hνσ,hσ₀'])
  obtain ⟨η₁,hη₁,hOne⟩ := hOne ν hν (by linarith only [hνσ,hφ',hσ])
  obtain ⟨η₂,hη₂,hTwo⟩ := hTwo ν hν (by linarith only [hνσ,hσ₂',hσ])
  let ηMax := min η₀ (min η₁ η₂)
  refine ⟨ηMax,by dsimp only [ηMax]; positivity,?_⟩
  intro η hη hηMax
  obtain ⟨N₀,hZero⟩ := hZero η hη (hηMax.trans (min_le_left _ _))
  obtain ⟨N₁,hOne⟩ := hOne η hη.le ((hηMax.trans (min_le_right _ _)).trans (min_le_left _ _))
  obtain ⟨N₂,hTwo⟩ := hTwo η hη.le ((hηMax.trans (min_le_right _ _)).trans (min_le_right _ _))
  let N := max N₀ (max N₁ N₂)
  refine ⟨N,?_⟩
  intro V _ _ B K s G X n d r₀ hn hDens hRoom hTwoB hKD hBX hB hK hLoss hνK hτK
    hPhi hRate hCut hRob hStop
  let Y := Xᶜ
  have hY : Y.card ≤ K := s.cut.complement_small
  have hParts : X.card+Y.card = n := card_add_card_compl X
  have hSizeX : N ≤ X.card := by omega
  have hComp : ((n-K-1:ℕ):ℝ) ≤ (X.card:ℝ)-1 := by
    have h : (n-K-1:ℕ)+1 ≤ X.card := by omega
    have h' : ((n-K-1:ℕ):ℝ)+1 ≤ (X.card:ℝ) := by exact_mod_cast h
    linarith only [h']
  have hDX : α*(X.card:ℝ) ≤ (d:ℝ) :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast card_le_univ X) hα.le).trans hDens
  have hBY : ClassTwoMatchingRun.budget G X ≤ d+B := s.cut.budget
  have hRobAt (μ τ : ℝ) (hμ : μ ≤ 8*ν) (hτ : σ ≤ τ) : IsRealRobust G μ τ :=
    real_robust_of_subgraph_degree_loss G G le_rfl 0 (8*ν) μ σ τ hμ hτ
      (by push_cast; exact mul_nonneg (sub_nonneg.mpr hμ) (Nat.cast_nonneg _)) (fun _ => by simp) hRob
  rcases matching_removal_stop_cases s hStop hTwoB with hC | ⟨hPos,hMin⟩ | hSecond
  · have hScale : ((B+4:ℕ):ℝ) ≤ 5*η*((X.card:ℝ)-1) := by
      have hh := mul_le_mul_of_nonneg_left hComp hη.le
      have hNonneg := mul_nonneg hη.le (Nat.cast_nonneg (α := ℝ) (n-K-1))
      linarith only [hB,hh,hNonneg]
    have hνY : (Y.card:ℝ) ≤ ν*(n:ℝ) := by
      have hh : (Y.card:ℝ) ≤ ((K+1:ℕ):ℝ) := by exact_mod_cast hY.trans (Nat.le_succ _)
      linarith only [hh,hνK,mul_nonneg hν.le (Nat.cast_nonneg (α := ℝ) n)]
    have hτY : 4*(Y.card:ℝ) ≤ σ₀*(n:ℝ) := by
      have h₁ : (Y.card:ℝ) ≤ K := by exact_mod_cast hY
      have h₂ := mul_le_mul_of_nonneg_right hσ₀' (Nat.cast_nonneg (α := ℝ) n)
      linarith only [h₁,h₂,hτK]
    exact s.uncolourable (hZero G X B ((le_max_left _ _).trans hSizeX) s.cut.odd hDX hRoom hScale
      hBY hC s.no_overfull (hRobAt (8*ν) σ₀ le_rfl hσ₀') hνY hτY)
  · let m := Fintype.card (IndependentSetIdentification.Vertices Y)
    have hm : m = X.card+1 := by
      dsimp only [m]
      rw [IndependentSetIdentification.card_vertices,show Yᶜ = X from compl_compl X]
    have hYn : 1 ≤ Y.card := by
      have hNonempty : Y.Nonempty := by
        by_contra he
        have hY' := not_nonempty_iff_eq_empty.mp he
        change 0 < ∑ y ∈ Y,G.degree y at hPos
        simp only [hY',sum_empty,lt_self_iff_false] at hPos
      exact card_pos.mpr hNonempty
    have hmN : m ≤ n := by omega
    have hmLo : n-K ≤ m := by omega
    have hM₀ : ((n-K:ℕ):ℝ) ≤ m := by exact_mod_cast hmLo
    have hM₁ : (m:ℝ) ≤ n := by exact_mod_cast hmN
    have hN₁ : N₁ ≤ m := ((le_max_left _ _).trans (le_max_right _ _)).trans (by omega : N ≤ m)
    have hDens₁ := (mul_le_mul_of_nonneg_left hM₁ hα.le).trans hDens
    have hRealB : (B:ℝ) ≤ 5*η*(m:ℝ) := by
      have h₁ : ((n-K-1:ℕ):ℝ) ≤ m := by exact_mod_cast (show n-K-1 ≤ m by omega)
      have h₂ := mul_le_mul_of_nonneg_left h₁ hη.le
      push_cast at hB
      linarith only [h₂,hB,mul_nonneg hη.le (Nat.cast_nonneg (α := ℝ) m)]
    have hRealY : (Y.card:ℝ) ≤ 2*η^2*(m:ℝ) := by
      have h₁ : (Y.card:ℝ) ≤ ((K+1:ℕ):ℝ) := by exact_mod_cast hY.trans (Nat.le_succ _)
      have h₂ : ((n-K-1:ℕ):ℝ) ≤ m := by exact_mod_cast (show n-K-1 ≤ m by omega)
      exact h₁.trans (hK.trans (mul_le_mul_of_nonneg_left h₂ (by positivity)))
    have hLossY : (Y.card:ℝ)+1 ≤ (ν/2)*(n:ℝ) := by
      have h₁ : ((Y.card+1:ℕ):ℝ) ≤ ((K+1:ℕ):ℝ) := by exact_mod_cast Nat.add_le_add_right hY 1
      simpa only [Nat.cast_add,Nat.cast_one] using h₁.trans hνK
    have hGap : φ*(n:ℝ)+2 ≤ (2*φ)*(m:ℝ) :=
      hPhi.trans (mul_le_mul_of_nonneg_left hM₀ (by positivity))
    let r := ⌈(ν/2)*(m:ℝ)⌉₊
    let t := ⌈(2*φ)*(m:ℝ)⌉₊
    have hr : r₀ ≤ r := Nat.ceil_mono (mul_le_mul_of_nonneg_left hM₀ (by positivity))
    have ht : t ≤ ⌈(2*φ)*(n:ℝ)⌉₊ := Nat.ceil_mono (mul_le_mul_of_nonneg_left hM₁ (by positivity))
    have hRate' : d ≤ r*r := hRate.trans (Nat.mul_le_mul hr hr)
    have hDegreeBound := maxDegree_lt_single_centre_order G s.cut hBX
    exact s.uncolourable (hOne G s.cut hN₁ hDegreeBound hDens₁ hMin hPos s.ready
      hRealB hRealY (show 2*Y.card+2 ≤ d by omega) s.no_overfull
      (hRobAt ν φ (by linarith only [hν]) hφ') hLossY hGap hRate'
      (show t+B ≤ d by omega) (show t+2*Y.card ≤ d+1 by omega))
  · obtain ⟨p⟩ := hSecond
    let Z := p.exceptional
    let m := Fintype.card (TwoIndependentIdentifications.Vertices Z)
    have hAct := ClassTwoGlobalNoOverfull.two_active_of_large_centre G s.cut p.anchor p.anchor_mem p.large
    have hActY := hAct.trans (card_le_card (filter_subset _ _))
    have hZCard : Z.card = Y.card+1 := by
      change (insert p.anchor Y).card = _
      exact card_insert_of_notMem (notMem_compl.mpr p.anchor_mem)
    have hZK : Z.card ≤ K+1 := p.card_bound
    have hm : m+Z.card = n+2 := by
      dsimp only [m]
      rw [TwoIndependentIdentifications.card_vertices]
      have h := card_add_card_compl Z
      omega
    have hLeM : m ≤ n := by change 2 ≤ Y.card at hActY; omega
    have hN₂ : N₂ ≤ m := ((le_max_right _ _).trans (le_max_right _ _)).trans (by omega : N ≤ m)
    have hSubN : ((n-K-1:ℕ):ℝ) ≤ m := by exact_mod_cast (show n-K-1 ≤ m by omega)
    have hDens₂ : α*(m:ℝ) ≤ (d:ℝ) :=
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hLeM) hα.le).trans hDens
    have hB₂ : (B:ℝ) ≤ η*(m:ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hSubN hη.le
      push_cast at hB
      linarith only [hB,hh]
    have hK₂ : ((K+1:ℕ):ℝ) ≤ 2*η^2*(m:ℝ) :=
      hK.trans (mul_le_mul_of_nonneg_left hSubN (by positivity))
    exact hTwo p hN₂ hDens₂ hB₂ hK₂ (show B < d by omega) hLoss
      (hRobAt (2*ν) σ₂ (by linarith only [hν]) hσ₂')

theorem cms_no_matching_removal_terminal (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ σ φ : ℝ,0 < σ ∧ 0 < φ ∧ ∀ ν : ℝ,0 < ν → ν ≤ σ/4 →
      ∃ ηMax : ℝ,0 < ηMax ∧ ∀ η : ℝ,0 < η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V] {B K : ℕ} (s : State V B K),
          let G := s.graph
          let X := s.cut.set
          let n := Fintype.card V
          let d := G.maxDegree
          let r₀ := ⌈(ν/2)*((n-K:ℕ):ℝ)⌉₊
          N+K+2 ≤ n → α*(n:ℝ) ≤ (d:ℝ) → B+7 ≤ d →
          2*B < d+2 → 2*K+2 ≤ d → B+K ≤ X.card →
          ((B+4:ℕ):ℝ) ≤ η*((n-K-1:ℕ):ℝ) →
          ((K+1:ℕ):ℝ) ≤ 2*η^2*((n-K-1:ℕ):ℝ) →
          ((max B (K+1):ℕ):ℝ) ≤ ν*(n:ℝ) →
          ((K+1:ℕ):ℝ) ≤ (ν/2)*(n:ℝ) → 4*(K:ℝ) ≤ σ*(n:ℝ) →
          φ*(n:ℝ)+2 ≤ 2*φ*((n-K:ℕ):ℝ) → d ≤ r₀*r₀ →
          ⌈(2*φ)*(n:ℝ)⌉₊+B+2*K ≤ d →
          IsRealRobust G (8*ν) σ → IsMatchingRemovalStop G X → False := by
  obtain ⟨σ,φ,hσ,hφ,_,_,hUse⟩ := cms_no_matching_removal_terminal_bounded_interval.{u} α hα hα₁
  exact ⟨σ,φ,hσ,hφ,hUse⟩

end OverfullWork.CMSMatchingRemoval
