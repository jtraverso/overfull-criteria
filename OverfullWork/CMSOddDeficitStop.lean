module

public import OverfullWork.CMSOddDenseStoppingGraph
public import OverfullWork.CMSEvenDenseStoppingGraph
public import OverfullWork.CMSCleanupRobustness

@[expose] public section


/-! The empty-complement stop on an odd core. Cleanup at a possible
degree-two minimum either supplies its local degree-sum conditions
or isolates it. In the latter case the actual support is even. -/
namespace OverfullWork.CanonicalRegularization

open Finset SimpleGraph OddCutDeficit RobustExpansion
open CMSMatchingRemoval FixedCoreBudgetTransport
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
universe u

section Induced

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem colourable_of_induced_support_subset (G : SimpleGraph V) (S : Finset V)
    (hSupport : G.support ⊆ (S : Set V)) (k : ℕ)
    (hColour : (G.induce (S : Set V)).EdgeColorable k) : G.EdgeColorable k := by
  let f : G.induce G.support →g G.induce (S : Set V) :=
    { toFun := fun x => ⟨x.val,hSupport x.property⟩
      map_rel' := fun h => h }
  have hf : Function.Injective f := fun _ _ h =>
    Subtype.ext (congrArg (fun a : (S : Set V) => a.val) h)
  exact (Critical.induce_support_colourable_iff G k).mp
    (Critical.colourable_of_copy (f.toCopy hf) hColour)

theorem maxDegree_induce_of_positive_support_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hSupport : G.support ⊆ (S : Set V)) (hPos : 0 < G.maxDegree) :
    (G.induce (S : Set V)).maxDegree = G.maxDegree := by
  have : Nonempty V := by
    by_contra h
    haveI := not_nonempty_iff.mp h
    simp [SimpleGraph.maxDegree] at hPos
  obtain ⟨v,hv⟩ := G.exists_maximal_degree_vertex
  have hMem : v ∈ G.support := (G.degree_pos_iff_mem_support v).mp (by rwa [←hv])
  let x : S := ⟨v,hSupport hMem⟩
  refine (Copy.induce G (S : Set V)).maxDegree_mono.antisymm ?_
  have hDeg := G.degree_induce_of_support_subset hSupport x
  have hLe := (G.induce (S : Set V)).degree_le_maxDegree x
  rw [hv]
  simp only [←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] at hDeg hLe ⊢
  exact hDeg.symm.trans_le hLe

end Induced

set_option maxHeartbeats 1800000 in
theorem cms_colourable_of_odd_deficit_stop (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ τ : ℝ,0 < τ ∧ ∀ ν : ℝ,0 < ν → ν ≤ τ/4 →
      ∃ ηMax : ℝ,0 < ηMax ∧ ∀ η : ℝ,0 < η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj] (B : ℕ),
          let n := Fintype.card V
          let d := G.maxDegree
          N ≤ n → Odd n → α*(n:ℝ) ≤ (d:ℝ) → B+7 ≤ d →
          ((B+4:ℕ):ℝ) ≤ 5*η*((n:ℝ)-1) →
          deficitMass G d univ ≤ d+B → ¬G.HasOverfullSubgraph →
          IsRealRobust G (4*ν) (τ/2) → G.EdgeColorable d := by
  obtain ⟨τ₁,hτ₁,hOdd⟩ := cms_colourable_of_odd_simple_with_degree_profiles.{u} α hα hα₁
  obtain ⟨τ₂,hτ₂,hEven⟩ := cms_colourable_of_even_dense_simple_stop.{u} α hα hα₁
  let τ := min (1/2) (min τ₁ τ₂)
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  have hτ₁' : τ ≤ τ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hτ₂' : τ ≤ τ₂ := (min_le_right _ _).trans (min_le_right _ _)
  have hτHalf : τ ≤ 1/2 := min_le_left _ _
  refine ⟨τ,hτ,?_⟩
  intro ν hν hντ
  obtain ⟨η₁,hη₁,hOdd⟩ := hOdd ν hν (by linarith only [hντ,hτ₁',hτ])
  obtain ⟨η₂,hη₂,hEven⟩ := hEven ν hν (by linarith only [hντ,hτ₂',hτ])
  let ηMax := min η₁ η₂
  refine ⟨ηMax,by dsimp only [ηMax]; positivity,?_⟩
  intro η hη hηMax
  obtain ⟨N₁,hOdd⟩ := hOdd η hη (hηMax.trans (min_le_left _ _))
  obtain ⟨N₂,hEven⟩ := hEven η hη (hηMax.trans (min_le_right _ _))
  obtain ⟨q,hq⟩ := exists_nat_ge (max (4/ν) (8/τ))
  refine ⟨max (max N₁ (N₂+1)) q,?_⟩
  intro V _ _ G _ B n d hSize hOddN hDens hRoom hScale hBudget hNo hRob
  have hSize₁ : N₁ ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hSize)
  have hSize₂ : N₂+1 ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hSize)
  have hQ : (q:ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hSize
  have hνn : 4 ≤ ν*(n:ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ hν).mp ((le_max_left _ _).trans (hq.trans hQ))
  have hτn : 8 ≤ τ*(n:ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ hτ).mp ((le_max_right _ _).trans (hq.trans hQ))
  have hnPos : 0 < n := by obtain ⟨k,hk⟩ := hOddN; omega
  haveI : Nonempty V := Fintype.card_pos_iff.mp hnPos
  have hB (H : SimpleGraph V) [DecidableRel H.Adj] (hD : H.maxDegree = d)
      (hb : deficitMass H d univ ≤ d+(B+4)) :
      (deficitMass H H.maxDegree univ:ℝ) ≤ (H.maxDegree:ℝ)+5*η*(n:ℝ) := by
    rw [hD]
    have hb' : (deficitMass H d univ:ℝ) ≤ (d:ℝ)+((B+4:ℕ):ℝ) := by exact_mod_cast hb
    linarith only [hScale,hb',hη]
  obtain ⟨z,hHigh⟩ := one_low_degree_of_global_deficit_budget G B 4 hBudget (by omega)
  by_cases hz : 2 < G.degree z
  · have hAll (v : V) : 2 < G.degree v := by
      by_cases he : v = z
      · rwa [he]
      · exact (by decide : 2 < 4).trans_le (hHigh v he)
    have hRob₁ := real_robust_of_subgraph_degree_loss G G le_rfl 0 (4*ν) ν (τ/2) τ₁
      (by linarith only [hν]) (by linarith only [hτ₁',hτ])
      (by push_cast; exact mul_nonneg (by linarith only [hν]) (Nat.cast_nonneg _))
      (fun _ => by simp) hRob
    exact hOdd G hSize₁ hOddN hDens (fun v => (hAll v).pos)
      (fun u _ hu _ => (Nat.not_le_of_lt (hAll u) hu).elim)
      (Or.inr (hB G rfl (by omega))) hNo hRob₁
  let S : Finset V := univ.erase z
  have hY : Sᶜ = {z} := by ext v; simp [S]
  have hZ (w : V) (hw : w ∈ ({z} : Finset V)) : G.degree w < G.maxDegree := by
    have he := mem_singleton.mp hw
    subst w
    omega
  by_contra hNCG
  obtain ⟨H,_,hLe,hMax,hNC,hNoH,hCore,hNonmax,hRich⟩ :=
    MaximumNeighbourCleanup.exists_cleanup_no_overfull G hNCG {z} hZ hNo
  have hCore' : H.induce (S : Set V) = G.induce (S : Set V) := by
    have he : (S : Set V) = (↑({z} : Finset V) : Set V)ᶜ := by ext v; simp [S]
    rwa [he]
  have hInd (J : SimpleGraph V) : J.IsIndepSet (↑(Sᶜ) : Set V) := by
    rw [hY,SimpleGraph.isIndepSet_iff]
    intro u hu v hv hne _
    have hu' : u = z := mem_singleton.mp hu
    have hv' : v = z := mem_singleton.mp hv
    exact hne (hu'.trans hv'.symm)
  have hDelta : H.maxDegree = d := hMax
  have hSame := budget_eq_of_fixed_core G H S hCore' hMax (hInd G) (hInd H)
  rw [hY,sum_singleton,sum_singleton,hDelta] at hSame
  change deficitMass H d S+H.degree z = deficitMass G d S+G.degree z at hSame
  have hMassG : deficitMass G d S+(d-G.degree z) = deficitMass G d univ :=
    sum_erase_add univ (fun v => d-G.degree v) (mem_univ z)
  have hMassH : deficitMass H d S+(d-H.degree z) = deficitMass H d univ :=
    sum_erase_add univ (fun v => d-H.degree v) (mem_univ z)
  have hDz : H.degree z ≤ G.degree z := H.degree_le_of_le hLe (v := z)
  have hCz : G.degree z ≤ d := G.degree_le_maxDegree z
  have hMass : deficitMass H d univ ≤ d+(B+4) := by omega
  have hOther (v : V) (hv : v ≠ z) : G.degree v ≤ H.degree v+1 := by
    have h := degree_le_degree_add_complement G H S hCore' v (by simp [S,hv])
    rwa [hY,card_singleton] at h
  have hLoss (v : V) : G.degree v ≤ H.degree v+2 := by
    by_cases he : v = z
    · subst v
      omega
    · exact (hOther v he).trans (by omega)
  have hAll (v : V) (hv : v ≠ z) : 3 ≤ H.degree v := by
    have hs := hHigh v hv
    have ht := hOther v hv
    omega
  have hHRob := real_robust_of_subgraph_degree_loss G H hLe 2 (4*ν) (2*ν) (τ/2) (τ/2)
    (by linarith only [hν]) le_rfl
    (by change (2:ℝ) ≤ (4*ν-2*ν)*(n:ℝ); linarith only [hνn]) hLoss hRob
  have hDen : α*(n:ℝ) ≤ (H.maxDegree:ℝ) := by rwa [hDelta]
  apply hNC
  by_cases hzPos : 0 < H.degree z
  · have hPos (v : V) : 0 < H.degree v := by
      by_cases he : v = z
      · rwa [he]
      · exact (by decide : 0 < 3).trans_le (hAll v he)
    have hWeak (u v : V) (hu : H.degree u ≤ 2) (hAdj : H.Adj u v) :
        H.maxDegree+2 ≤ H.degree u+H.degree v := by
      have heu : u = z := by by_contra hne; have h := hAll u hne; omega
      exact CleanedSourceVAL.weak_VAL H {z} ⟨hNonmax,hRich⟩ u (mem_singleton.mpr heu) v hAdj
    have hHRob₁ := real_robust_of_subgraph_degree_loss H H le_rfl 0 (2*ν) ν (τ/2) τ₁
      (by linarith only [hν]) (by linarith only [hτ₁',hτ])
      (by push_cast; exact mul_nonneg (by linarith only [hν]) (Nat.cast_nonneg _))
      (fun _ => by simp) hHRob
    exact hOdd H hSize₁ hOddN hDen hPos hWeak (Or.inr (hB H hDelta hMass)) hNoH hHRob₁
  · have hz0 : H.degree z = 0 := by omega
    have hCap : H.support ⊆ (S : Set V) := by
      intro v hv
      have hh := (H.degree_pos_iff_mem_support v).mpr hv
      have hne : v ≠ z := by intro he; subst v; omega
      simp [S,hne]
    let J := H.induce (S : Set V)
    let m := Fintype.card S
    have hJMax : J.maxDegree = H.maxDegree :=
      maxDegree_induce_of_positive_support_subset H S hCap (by omega)
    have hDeg (v : S) : J.degree v = H.degree v.val := by
      simpa only [J,←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
        H.degree_induce_of_support_subset hCap v
    have hSz : m+1 = n := by
      dsimp only [m,S]
      rw [Fintype.card_coe,card_erase_of_mem (mem_univ z),card_univ]
      omega
    have hEvenM : Even m := by obtain ⟨k,hk⟩ := hOddN; exact ⟨k,by omega⟩
    have hM : (m:ℝ)+1 = (n:ℝ) := by exact_mod_cast hSz
    have hDensJ : α*(m:ℝ) ≤ (J.maxDegree:ℝ) := by
      rw [hJMax]
      have h := mul_le_mul_of_nonneg_left (by linarith only [hM] : (m:ℝ) ≤ n) hα.le
      exact h.trans hDen
    have hNoJ := Critical.no_overfull_of_copy (Copy.induce H (S : Set V)) hJMax hNoH
    have hS₁ : Sᶜ.card = 1 := by rw [hY,card_singleton]
    have hRobJ := induced_graph_robust_of_small_complement H S (2*ν) (τ/2)
      (by positivity) (by linarith only [hντ,hτHalf]) (by positivity) (by linarith only [hτHalf]) hHRob
      (by rw [hS₁]; push_cast; nlinarith only [hνn])
      (by rw [hS₁]; push_cast; nlinarith only [hτn])
    have hRobJ' : IsRealRobust J ν τ := by
      convert hRobJ using 2 <;> ring
    have hRobJ₂ : IsRealRobust J ν τ₂ := by
      intro A hLo hHi
      have h := mul_le_mul_of_nonneg_right hτ₂'
        (Nat.cast_nonneg (α := ℝ) (Fintype.card (↥(S : Set V))))
      exact hRobJ' A (h.trans hLo) (by linarith only [hHi,h])
    have hHighJ (v : S) : 3 ≤ J.degree v := by
      rw [hDeg]
      apply hAll
      exact (mem_erase.mp v.property).1
    have hSumS : deficitMass H d S ≤ B+4 := by omega
    have hOrd (v : S) : (J.maxDegree:ℝ)-6*η*(m:ℝ) ≤ J.degree v := by
      have hv : d-H.degree v.val ≤ deficitMass H d S :=
        single_le_sum (f := fun v => d-H.degree v) (fun _ _ => Nat.zero_le _) v.property
      have hD := H.degree_le_maxDegree v.val
      have hR : (d:ℝ) ≤ (H.degree v.val:ℝ)+((B+4:ℕ):ℝ) := by
        exact_mod_cast (show d ≤ H.degree v.val+(B+4) by omega)
      have hm' : (n:ℝ)-1 = (m:ℝ) := by linarith only [hM]
      have hs := hScale
      rw [hm'] at hs
      rw [hJMax,hDelta,hDeg]
      linarith only [hR,hs,mul_nonneg hη.le (Nat.cast_nonneg (α := ℝ) m)]
    have hPosM : 0 < m := by
      have hLess := G.maxDegree_lt_card_verts
      omega
    obtain ⟨a⟩ := Fintype.card_pos_iff.mp hPosM
    have hSizeM : N₂ ≤ m := by omega
    have hColour := hEven J hSizeM hEvenM hDensJ
      (fun v => (by decide : 0 < 3).trans_le (hHighJ v))
      (fun u _ h _ => (Nat.not_le_of_lt (hHighJ u) h).elim)
      ⟨a,fun v _ => hOrd v⟩ hNoJ hRobJ₂
    exact colourable_of_induced_support_subset H S hCap H.maxDegree (by rwa [hJMax] at hColour)

end OverfullWork.CanonicalRegularization
