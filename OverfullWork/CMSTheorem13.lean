module

public import OverfullWork.CMSOperation41Claim42
public import OverfullWork.CMSOperation41TerminalCleanup

@[expose] public section


/-! The two stopping arguments for Operation 4.1 rule out the
counterexample in Chen–McDonald–Shan's Theorem 1.3. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph RobustExpansion
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge SimpleGraph.instDecidableMapAdj SimpleGraph.fintypeEdgeSetSdiff

universe u

set_option maxHeartbeats 4500000 in
/-- The overfull criterion for robust expanders with weak VAL and
few vertices of large deficit. The size threshold is uniform for all
witnesses `η` up to the selected bound. -/
theorem cms_theorem_1_3 (α : ℝ) (hα : 0 < α) :
    ∃ τ : ℝ, 0 < τ ∧ τ < 1/2 ∧ ∀ ν : ℝ, 0 < ν →
      ∃ ηMax : ℝ, 0 < ηMax ∧ ηMax < 1 ∧ ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
          let n := Fintype.card V
          N ≤ n → α*(n:ℝ) ≤ (G.maxDegree:ℝ) → IsRealRobust G ν τ →
          (∀ u v,G.Adj u v → G.maxDegree+2 ≤ G.degree u+G.degree v) →
          (∃ η : ℝ,0 < η ∧ η ≤ ηMax ∧
            ((initialExceptionalSet G η).card:ℝ) ≤ η^2*(n:ℝ)) →
          (G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph) := by
  by_cases hLarge : 1 < α
  · refine ⟨1/4,by norm_num,by norm_num,fun _ _ => ⟨1/4,by norm_num,by norm_num,1,?_⟩⟩
    intro V _ _ G _ n hN hDegree _ _ _
    letI : Nonempty V := Fintype.card_pos_iff.mp hN
    have hn : 0 < (n:ℝ) := by exact_mod_cast hN
    have hCap : (G.maxDegree:ℝ) ≤ n := by exact_mod_cast G.maxDegree_lt_card_verts.le
    have h := mul_lt_mul_of_pos_right hLarge hn
    exfalso
    linarith only [hDegree,hCap,h]
  have hα₁ : α ≤ 1 := le_of_not_gt hLarge
  obtain ⟨τMax,hτMax,hRun⟩ := cms_operation_4_1_round_limit.{u} α hα hα₁
  obtain ⟨σ,hσ,hDense⟩ := CanonicalRegularization.cms_no_dense_trimming_stop_before_final_cleanup.{u}
    (α/3) (by positivity) (by linarith only [hα₁])
  let τ := min τMax (min (σ/4) (1/4))
  have hτ : 0 < τ := lt_min hτMax (lt_min (by positivity) (by norm_num))
  have hτCap : τ < 1/2 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by norm_num : (1/4:ℝ) < 1/2)
  have hτσ : 4*τ ≤ σ := by
    have h : τ ≤ σ/4 := (min_le_right _ _).trans (min_le_left _ _)
    linarith only [h]
  refine ⟨τ,hτ,hτCap,?_⟩
  intro ν hν
  let νRun := min ν τ
  have hνRun : 0 < νRun := lt_min hν hτ
  obtain ⟨ρ,ηRun,hρ,hηRun,hRun⟩ := hRun τ hτ (min_le_left _ _) νRun hνRun (min_le_right _ _)
  let νDense := min (ρ/16) σ
  have hνDense : 0 < νDense := lt_min (by positivity) hσ
  have hνρ : 4*νDense ≤ ρ/4 := by
    have h : νDense ≤ ρ/16 := min_le_left _ _
    linarith only [h]
  obtain ⟨ηDense,hηDense,hDense⟩ := hDense νDense hνDense (min_le_right _ _)
  let η := min ηRun (min ηDense (min (α/128) (min (νDense/8) (σ/8))))
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηRun' : η ≤ ηRun := min_le_left _ _
  have hηDense' : η ≤ ηDense := (min_le_right _ _).trans (min_le_left _ _)
  have hηMargins : η ≤ min (α/128) (min (νDense/8) (σ/8)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hηα : 128*η ≤ α := by
    have h := hηMargins.trans (min_le_left _ _)
    linarith only [h]
  have hη2 : η ≤ 1/2 := by linarith only [hηα,hα₁]
  have hηSquare : η^2 ≤ η := by nlinarith only [mul_nonneg hη.le (show 0 ≤ 1-η by linarith)]
  have hην : 8*η ≤ νDense := by
    have h := (hηMargins.trans (min_le_right _ _)).trans (min_le_left _ _)
    linarith only [h]
  have hησ : 8*η ≤ σ := by
    have h := (hηMargins.trans (min_le_right _ _)).trans (min_le_right _ _)
    linarith only [h]
  obtain ⟨NRun,hRun⟩ := hRun η hη hηRun'
  obtain ⟨NDense,hDense⟩ := hDense η hη hηDense'
  let N := max NRun (max ⌈6/η^2⌉₊ (2*(NDense+2)))
  refine ⟨η,hη,hη2.trans_lt (by norm_num),N,?_⟩
  intro V _ _ G dG
  cases Subsingleton.elim dG (fun u v => Classical.propDecidable (G.Adj u v))
  intro n hN hDegree hRob hVAL hSome
  refine ⟨Gate8D.no_overfull_of_colourable G,fun hNo => ?_⟩
  by_contra hNC
  let U := initialExceptionalSet G η
  let shift := η*(n:ℝ)
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  obtain ⟨η',hη',hη'η,hFew'⟩ := hSome
  have hU : U ⊆ initialExceptionalSet G η' := by
    intro v hv
    exact mem_filter.mpr ⟨mem_univ _,
      (mul_le_mul_of_nonneg_right hη'η hn).trans_lt (mem_filter.mp hv).2⟩
  have hFew : (U.card:ℝ) ≤ η^2*(n:ℝ) :=
    (by exact_mod_cast card_le_card hU : (U.card:ℝ) ≤ (initialExceptionalSet G η').card).trans
      (hFew'.trans (mul_le_mul_of_nonneg_right (by nlinarith only [hη'.le,hη'η,hη]) hn))
  have hGrob : IsRealRobust G νRun τ :=
    real_robust_of_subgraph_degree_loss G G le_rfl 0 ν νRun τ τ (min_le_left _ _) le_rfl
      (by simpa only [Nat.cast_zero] using mul_nonneg (sub_nonneg.mpr (min_le_left _ _)) hn)
      (fun v => (Nat.le_add_right _ _)) hRob
  obtain ⟨m,_,start,finish,_,K,last,_,_,L,hProps,hJRob,_,hOrd,_,hLinear,hProfile⟩ :=
    hRun G ((le_max_left _ _).trans hN) hDegree hFew hGrob hVAL hNC hNo
  let J := sdiff last.cleaned (usedTrimmingPrefix L m)
  let A := univ.filter (fun v => 0 < J.degree v)
  obtain ⟨W,hWA,hLow,hParity,hFloor⟩ := hProfile
  have hSupport : J.support ⊆ (A : Set V) := by
    intro v hv
    exact mem_filter.mpr ⟨mem_univ _,(J.degree_pos_iff_mem_support v).mpr hv⟩
  have hCardW : W.card ≤ 2 := hParity.elim (fun h => h.trans (by decide)) And.right
  have hSize : 6 ≤ η^2*(n:ℝ) := by
    have hc : (⌈6/η^2⌉₊:ℝ) ≤ n := by exact_mod_cast
      (le_max_left ⌈6/η^2⌉₊ (2*(NDense+2))).trans ((le_max_right _ _).trans hN)
    simpa only [mul_comm (η^2)] using
      (div_le_iff₀ (sq_pos_of_pos hη)).mp ((Nat.le_ceil _).trans hc)
  have hShift : 1 ≤ shift := by
    have h := mul_le_mul_of_nonneg_right hηSquare hn
    dsimp only [shift]
    linarith only [hSize,h]
  have hOrdReserve : ((⌈shift⌉₊+2*U.card:ℕ):ℝ) < (J.maxDegree:ℝ) := by
    have hC := Nat.ceil_lt_add_one (show 0 ≤ shift by positivity)
    have hMass : (U.card:ℝ) ≤ shift := hFew.trans (mul_le_mul_of_nonneg_right hηSquare hn)
    have hαn := mul_le_mul_of_nonneg_right hηα hn
    change α*(n:ℝ)/3 ≤ (J.maxDegree:ℝ) at hLinear
    push_cast
    dsimp only [shift] at hC hMass hShift ⊢
    linarith only [hC,hMass,hShift,hαn,hLinear]
  have hOutside : Aᶜ ⊆ U := by
    intro v hv
    by_contra hvU
    have hZero : J.degree v = 0 := by
      have hNA := mem_compl.mp hv
      by_contra hPos
      exact hNA (mem_filter.mpr ⟨mem_univ _,Nat.pos_of_ne_zero hPos⟩)
    have hOrd' := hOrd v hvU
    rw [hZero,zero_add] at hOrd'
    have hR : (J.maxDegree:ℝ) ≤ ((⌈shift⌉₊+2*U.card:ℕ):ℝ) := by exact_mod_cast hOrd'
    exact (not_lt_of_ge hR) hOrdReserve
  have hOutsideCard := card_le_card hOutside
  have hOutsideR : (Aᶜ.card:ℝ) ≤ η^2*(n:ℝ) := (by exact_mod_cast hOutsideCard :
    (Aᶜ.card:ℝ) ≤ (U.card:ℝ)).trans hFew
  have hSmall : ((Aᶜ.card+W.card:ℕ):ℝ) ≤ 2*(η^2*(n:ℝ)) := by
    have hW : (W.card:ℝ) ≤ 2 := by exact_mod_cast hCardW
    push_cast
    linarith only [hW,hOutsideR,hSize]
  have hSmallν : 8*((Aᶜ.card+W.card:ℕ):ℝ) ≤ (2*νDense)*(n:ℝ) := by
    have h := mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hηSquare
      (show (0:ℝ) ≤ 8 by norm_num)).trans hην) hn
    linarith only [hSmall,h]
  have hSmallτ : 4*((Aᶜ.card+W.card:ℕ):ℝ) ≤ σ*(n:ℝ) := by
    have h := mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hηSquare
      (show (0:ℝ) ≤ 8 by norm_num)).trans hησ) hn
    linarith only [hSmall,h]
  have hHalf : n ≤ 2*A.card := by
    have hSum : (A.card:ℝ)+(Aᶜ.card:ℝ) = n := by exact_mod_cast card_add_card_compl A
    have hOut := hOutsideR.trans (mul_le_mul_of_nonneg_right (hηSquare.trans hη2) hn)
    exact_mod_cast (show (n:ℝ) ≤ 2*(A.card:ℝ) by linarith only [hSum,hOut])
  have hNDense : NDense+W.card ≤ A.card := by
    have h : 2*(NDense+2) ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
    omega
  have hJrob' : IsRealRobust J (4*νDense) σ :=
    real_robust_of_subgraph_degree_loss J J le_rfl 0 (ρ/4) (4*νDense) (4*τ) σ hνρ hτσ
      (by simpa only [Nat.cast_zero] using mul_nonneg (sub_nonneg.mpr hνρ) hn)
      (fun v => Nat.le_add_right _ _) hJRob
  have hDenseFloor (v : V) (hv : v ∈ A) (hW : v ∉ W) :
      (J.maxDegree:ℝ)-6*η*(n:ℝ) ≤ (J.degree v:ℝ) := by
    have h : (J.maxDegree:ℝ) ≤ J.degree v+(⌊6*shift⌋₊:ℝ) := by exact_mod_cast hFloor v hv hW
    have hWidth := Nat.floor_le (show 0 ≤ 6*shift by positivity)
    dsimp only [shift] at hWidth
    linarith only [h,hWidth]
  exact hDense J A W hNDense (by simpa only [div_mul_eq_mul_div] using hLinear)
    hSupport hWA hLow hParity hDenseFloor hProps.2.1 hProps.2.2.2.1 hJrob' hSmallν hSmallτ

end OverfullWork.CMSTrimmingRound
