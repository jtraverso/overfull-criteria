module

public import OverfullWork.EvenHamiltonFactorization
public import OverfullWork.OsthusStadenApproximateHamiltonPacking
public import OverfullWork.RealRobustSpanningLinkage

@[expose] public section


/-! The simple regular residue of CMS §5.2, Case 1, with either parity.
The sole auxiliary matching is built by CMS Lemma 3.15. -/
namespace OverfullWork.RobustExpansion
open SimpleGraph Finset PrunedCore
open scoped Classical
universe u

/-- The real robust-neighbour threshold pays for a genuine graph
difference. The size window may be narrowed at the same time. -/
theorem isRealRobust_sdiff_with_loss {V : Type u} [Fintype V] [DecidableEq V]
    (G F : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel F.Adj]
    (ν ν' τ τ' : ℝ) (d : ℕ) (hν : ν' ≤ ν) (hτ : τ ≤ τ')
    (hLoss : (d:ℝ) ≤ (ν-ν')*(Fintype.card V:ℝ))
    (hDeg : ∀ v, F.degree v ≤ d) (hG : IsRealRobust G ν τ) :
    IsRealRobust (G \ F) ν' τ' := by
  intro S hLow hHigh
  have hNN : 0 ≤ (Fintype.card V:ℝ) := Nat.cast_nonneg _
  have hCut := mul_le_mul_of_nonneg_right hτ hNN
  have hGrow := hG S (hCut.trans hLow) (by linarith only [hCut,hHigh])
  have hSub : realNeighbourhood G ν S ⊆ realNeighbourhood (G \ F) ν' S := by
    intro v hv
    have hOcc := (mem_filter.mp hv).2
    have hPay := neighboursIn_le_sdiff_add_degree G F S v
    have hPayR : (neighboursIn G S v:ℝ) ≤
        (neighboursIn (G \ F) S v:ℝ)+(d:ℝ) := by
      exact_mod_cast hPay.trans (Nat.add_le_add_left (hDeg v) _)
    exact mem_filter.mpr ⟨mem_univ _,by linarith only [hOcc,hLoss,hPayR]⟩
  have hCard : ((realNeighbourhood G ν S).card:ℝ) ≤
      ((realNeighbourhood (G \ F) ν' S).card:ℝ) := by
    exact_mod_cast card_le_card hSub
  linarith only [hGrow,hCard,mul_le_mul_of_nonneg_right hν hNN]

end OverfullWork.RobustExpansion

namespace OverfullWork.EvenHamiltonFactorization
open SimpleGraph MultiGraph Finset RobustExpansion
open scoped Classical
universe u

set_option maxHeartbeats 2200000 in
/-- A sufficiently large simple regular robust expander of even order
and linear degree is one-factorizable. In odd degree, remove a perfect
matching supplied by spanning linkage and then apply CMS Theorem 5.5. -/
theorem robust_regular_colourable (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ ν : ℝ, 0 < ν → ∃ N : ℕ,
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
        [DecidableRel G.Adj] (r : ℕ), N ≤ Fintype.card V → Even (Fintype.card V) →
        α*(Fintype.card V:ℝ) ≤ (r:ℝ) → IsRealRobust G ν τ →
        (∀ v, G.degree v = r) → Nonempty ((ofSimpleGraph G).EdgeColoring r) := by
  obtain ⟨τ₀,hτ₀,hDec⟩ := DirectedRobustExpansion.cms_theorem_5_5.{u} (α/2) (by positivity)
  let τ := min τ₀ (α/1024)
  have hτ : 0 < τ := lt_min hτ₀ (by positivity)
  have hτₐ : 256*τ ≤ α/2 := by linarith only [(min_le_right _ _ : τ ≤ α/1024),hα]
  refine ⟨τ,hτ,?_⟩
  intro ν hν
  let μ := min (ν/2) τ
  have hμ : 0 < μ := lt_min (by positivity) hτ
  have hμτ : μ ≤ τ := min_le_right _ _
  have hμν : μ ≤ ν/2 := min_le_left _ _
  have hμν' : μ ≤ ν := by linarith only [hμν,hν]
  obtain ⟨N₁,hN₁⟩ := hDec μ hμ
  obtain ⟨N₂,hN₂⟩ := RobustSpanningLinkage.exists_spanning_linkage_threshold.{u} μ τ (α/2)
    hμ (by linarith only [hμτ,hτₐ,hα₁]) hμτ hτₐ (by linarith only [hα₁])
  obtain ⟨N₃,hN₃⟩ := exists_nat_ge (max (2/ν) (max (2/α) (1/μ^4)))
  refine ⟨max 2 (max N₁ (max N₂ N₃)),?_⟩
  intro V _ _ G _ r hN hEven hDeg hRob hReg
  have h₂ : 2 ≤ Fintype.card V := (le_max_left _ _).trans hN
  have hN' : max N₁ (max N₂ N₃) ≤ Fintype.card V := (le_max_right _ _).trans hN
  have hN₁' : N₁ ≤ Fintype.card V := (le_max_left _ _).trans hN'
  have hN₂' : N₂ ≤ Fintype.card V := (le_max_left _ _).trans ((le_max_right _ _).trans hN')
  have hN₃' : N₃ ≤ Fintype.card V := (le_max_right _ _).trans ((le_max_right _ _).trans hN')
  have hSize := hN₃.trans (show (N₃:ℝ) ≤ (Fintype.card V:ℝ) by exact_mod_cast hN₃')
  have hNN : 0 ≤ (Fintype.card V:ℝ) := Nat.cast_nonneg _
  have hLoss : (1:ℝ) ≤ (ν-μ)*(Fintype.card V:ℝ) := by
    have hPay := (div_le_iff₀ hν).mp ((le_max_left _ _).trans hSize)
    nlinarith only [hPay,mul_le_mul_of_nonneg_right hμν hNN]
  have hAlpha : 2 ≤ α*(Fintype.card V:ℝ) := by
    rw [mul_comm α]
    exact (div_le_iff₀ hα).mp ((le_max_left _ _).trans ((le_max_right _ _).trans hSize))
  have hSingle : 1 ≤ μ^4*(Fintype.card V:ℝ) := by
    rw [mul_comm (μ^4)]
    exact (div_le_iff₀ (pow_pos hμ 4)).mp ((le_max_right _ _).trans ((le_max_right _ _).trans hSize))
  have hμRob : IsRealRobust G μ τ := by
    have h0 : (0:ℝ) ≤ (ν-μ)*(Fintype.card V:ℝ) := by positivity
    simpa only [sdiff_bot] using isRealRobust_sdiff_with_loss G (⊥ : SimpleGraph V)
      ν μ τ τ 0 hμν' le_rfl (by simpa only [Nat.cast_zero] using h0) (by simp) hRob
  have hμRob' : IsRealRobust G μ τ₀ := by
    intro S hLow hHigh
    have h := mul_le_mul_of_nonneg_right (show τ ≤ τ₀ from min_le_left _ _) hNN
    exact hμRob S (h.trans hLow) (by linarith only [h,hHigh])
  rcases Nat.even_or_odd r with hEvenR | hOddR
  · obtain ⟨k,hk⟩ := hEvenR
    have hk' : r = 2*k := by omega
    rw [hk'] at hReg hDeg ⊢
    obtain ⟨P⟩ := hN₁ G k hN₁' (by push_cast at hDeg; nlinarith only [hDeg,mul_nonneg hα.le hNN])
      hμRob' hReg
    exact colourable_of_hamilton_decomposition G P hEven
  · obtain ⟨k,hk⟩ := hOddR
    have hr : r = 2*k+1 := by omega
    have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨x,y,hxy⟩ := exists_pair_ne V
    obtain ⟨P,hP,_hDis,hCover⟩ := hN₂ G hN₂' hμRob
      (fun v => by rw [hReg]; nlinarith only [hDeg,mul_nonneg hα.le hNN])
      (p := 1) (by decide) (by simpa only [Nat.cast_one] using hSingle)
      (fun _ => x) (fun _ => y) (fun _ _ _ => Subsingleton.elim _ _)
      (fun _ _ _ => Subsingleton.elim _ _) (fun _ _ => hxy)
    have hPathSpan : ∀ v, v ∈ (P 0).support := by
      intro v
      obtain ⟨i,hi⟩ := hCover v
      have h : i = 0 := Subsingleton.elim _ _
      simpa only [h] using hi
    obtain ⟨J,hJG,hJ⟩ := one_factor_of_spanning_path (P 0) (hP 0) hPathSpan hxy hEven
    let H := G \ J
    have hH (v : V) : H.degree v = 2*k := by
      have h := MaximumMatching.degree_sdiff_add_of_le G J hJG v
      rw [hJ v,hReg v,hr] at h
      simpa only [H] using (show (G \ J).degree v = 2*k by omega)
    have hHRob : IsRealRobust H μ τ₀ :=
      isRealRobust_sdiff_with_loss G J ν μ τ τ₀ 1 hμν' (min_le_left _ _)
        (by simpa only [Nat.cast_one] using hLoss) (fun v => (hJ v).le) hRob
    have hR : (r:ℝ) = 2*(k:ℝ)+1 := by exact_mod_cast hr
    obtain ⟨P⟩ := hN₁ H k hN₁' (by nlinarith only [hAlpha,hDeg,hR]) hHRob hH
    obtain ⟨C⟩ := colourable_of_hamilton_decomposition H P hEven
    let C₁ : (ofSimpleGraph J).EdgeColoring 1 := {
      col := fun t _ => (ofSimpleGraph J).mult t
      sum_col := by intro t; simp
      proper := fun v _ => by
        change (ofSimpleGraph J).degree v ≤ 1
        rw [degree_ofSimpleGraph,hJ] }
    have hSum : (ofSimpleGraph H).addCopies (ofSimpleGraph J) = ofSimpleGraph G := by
      apply ext_mult
      intro t
      induction t using Sym2.inductionOn with
      | hf a b =>
        change (if H.Adj a b then 1 else 0)+(if J.Adj a b then 1 else 0) =
          if G.Adj a b then 1 else 0
        change (if G.Adj a b ∧ ¬ J.Adj a b then 1 else 0)+_ = _
        by_cases hj : J.Adj a b
        · simp [hj,hJG hj]
        · simp [hj]
    have hC := C.addCopies C₁
    rw [hSum,← hr] at hC
    exact ⟨hC⟩

end OverfullWork.EvenHamiltonFactorization
