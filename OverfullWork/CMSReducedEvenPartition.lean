module

public import OverfullWork.CMSRobustPurePartition
public import OverfullWork.MathlibRegularityCompletionPartition
public import OverfullWork.NormalizedRobustQuotient

@[expose] public section


/-! Produce the reduced robust graph and the equal even cells used in
the cut construction of CMS Lemma 5.4. -/
namespace OverfullWork.CMSBalancedCut

open Finset SimpleGraph Finpartition DirectedClusterQuotient
open scoped Classical
universe u

set_option maxHeartbeats 2300000 in
/-- The same trimmed cells determine the robust quotient and the
dense regular pairs in the original host. Two specified vertices
are assigned to the exceptional cell, which has even order. -/
theorem exists_reduced_even_partition
    (ν τ ε d β σ : ℝ) (kMin : ℕ)
    (hν : 0 < ν) (hτ : 0 < τ) (hε : 0 < ε) (hεSmall : ε ≤ 1/2)
    (hd : 0 ≤ d) (hβ : 0 < β) (hσ : 0 < σ)
    (hBudget : 4*ε+β/2+4*d ≤ (ν/2)^2) :
    ∃ K N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) (x y : V),
      N ≤ Fintype.card V → Fintype.card V = 2*m → x ≠ y →
      RobustExpansion.IsRealRobust G ν τ →
      ∃ (I : Type u) (inst : Fintype I),
        letI := inst
        ∃ (f : V → Option I) (R : Digraph I) (l : ℕ),
          0 < Fintype.card I ∧ kMin ≤ Fintype.card I ∧ Fintype.card I ≤ K ∧ 2 ≤ l ∧
          f x = none ∧ f y = none ∧
          (∀ i, Even (Fintype.card {v : V // f v = i})) ∧
          (∀ i, (cluster f i).card = 2*l) ∧
          ((exceptional f).card:ℝ) ≤ σ*(Fintype.card V:ℝ) ∧
          DirectedRobustExpansion.IsRealRobust R (ν/4) (2*τ) ∧
          ∀ i j, R.Adj i j → G.IsUniform (2*ε) (cluster f i) (cluster f j) ∧
            d-ε ≤ (G.edgeDensity (cluster f i) (cluster f j):ℝ) := by
  let cutMin := max kMin ⌈8/ν⌉₊
  obtain ⟨K,N₀,hPure⟩ := RobustExpansion.exists_cms_robust_pure_partition.{u}
    ν τ ε d β cutMin hν hε hd hβ hBudget
  let slack := min σ (min (ν/8) (1/4))
  have hSlack : 0 < slack := by dsimp only [slack]; positivity
  let cap := 2+4*K
  obtain ⟨N₁,hN₁⟩ := exists_nat_ge (max ((cap:ℝ)/slack) (2/τ))
  refine ⟨K,max N₀ (max (8*K) N₁),?_⟩
  intro V _ _ G _ m x y hN hCard hxy hRob
  obtain ⟨P,hEqui,_hReg,hLo,hHi,hRobPure⟩ :=
    hPure G ((le_max_left _ _).trans hN) hRob
  let E : Finset V := {x,y}
  let I := P.parts
  let k := P.parts.card
  let H := G.regularityReduced P ε d
  let l := (Fintype.card V/k-2)/2
  have hK : Fintype.card I = k := Fintype.card_coe _
  have hk : 0 < k := card_pos.mpr ⟨P.part x,P.part_mem.mpr (mem_univ x)⟩
  have hE : E.card = 2 := card_pair hxy
  have hSize : 8*k ≤ Fintype.card V :=
    (Nat.mul_le_mul_left 8 hHi).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  have hAvg : 8 ≤ Fintype.card V/k := (Nat.le_div_iff_mul_le hk).mpr hSize
  have hl : 2 ≤ l := by dsimp only [l]; omega
  have hCells (i : I) :
      2*l ≤ (Eᶜ.filter fun z => MathlibRegularityCompletionPartition.cellMap P z = i).card ∧
      (Eᶜ.filter fun z => MathlibRegularityCompletionPartition.cellMap P z = i).card ≤ 2*l+4 := by
    have hh := MathlibRegularityCompletionPartition.outside_cell_sizes P hEqui E i
    simpa only [hE] using hh
  obtain ⟨Z,f,hEsub,hZ,hNone,hCell,hMap,hEven⟩ := EqualEvenCellRefinement.exists_refinement
    (MathlibRegularityCompletionPartition.cellMap P) E m l 4 hCard hCells
  have hF (i : I) : (cluster f i).card = 2*l := by
    rw [show cluster f i = (univ.filter fun v => f v = some i) by ext v; simp [mem_cluster]]
    exact hCell i
  have hExc : exceptional f = Z := by ext z; rw [mem_exceptional,hNone]
  have hZcap : Z.card ≤ cap := by
    dsimp only [cap]
    rw [hE,hK] at hZ
    exact hZ.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 4 hHi) 2)
  have hNreal := hN₁.trans (show (N₁:ℝ) ≤ (Fintype.card V:ℝ) by
    exact_mod_cast (le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hPaid := (div_le_iff₀ hSlack).mp ((le_max_left _ _).trans hNreal)
  have hPaidExc : ((exceptional f).card:ℝ) ≤ slack*(Fintype.card V:ℝ) := by
    rw [hExc,mul_comm]
    exact (show (Z.card:ℝ) ≤ (cap:ℝ) by exact_mod_cast hZcap).trans hPaid
  have hOrder : 2 ≤ τ*(Fintype.card V:ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ hτ).mp ((le_max_right _ _).trans hNreal)
  have hClusters : 4 ≤ (ν/2)*(Fintype.card I:ℝ) := by
    have hh : 8/ν ≤ (Fintype.card I:ℝ) := (Nat.le_ceil _).trans (by
      exact_mod_cast (show ⌈8/ν⌉₊ ≤ Fintype.card I by rw [hK]; exact (le_max_right _ _).trans hLo))
    have hMul := (div_le_iff₀ hν).mp hh
    nlinarith only [hMul]
  have hNn : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hExcSmall : ((exceptional f).card:ℝ) ≤ (Fintype.card V:ℝ)/4 := by
    have hh := mul_le_mul_of_nonneg_right
      (show slack ≤ 1/4 from (min_le_right _ _).trans (min_le_right _ _)) hNn
    linarith only [hPaidExc,hh]
  have hExcLoss : ((exceptional f).card:ℝ)+((0:ℕ):ℝ) ≤ (ν/2)*(Fintype.card V:ℝ)/4 := by
    have hh := mul_le_mul_of_nonneg_right
      (show slack ≤ ν/8 from (min_le_right _ _).trans (min_le_left _ _)) hNn
    push_cast
    linarith only [hPaidExc,hh]
  let D := RobustSpanningLinkage.symmetric H
  let R := quotient D f
  obtain ⟨hSmall,hWindow⟩ := RobustClusterQuotient.paper_scale_budgets f (2*l) 0 hF
    (ν/2) τ (by positivity) hτ hClusters hOrder hExcSmall hExcLoss
  have hR : DirectedRobustExpansion.IsRealRobust R (ν/4) (2*τ) := by
    convert RobustClusterQuotient.real_robust_of_deleted_indegree D D le_rfl
      f (2*l) 0 (by omega) hF (ν/2) τ (by positivity) hτ
      (RobustSpanningLinkage.symmetric_robust H (ν/2) τ hRobPure)
      (fun v => by simp [DirectedRobustExpansion.inDegree,DirectedRobustExpansion.inNeighbours]) hSmall hWindow using 1 <;> ring
  have hSub (i : I) : cluster f i ⊆ i.val := by
    intro z hz
    exact (MathlibRegularityCompletionPartition.cellMap_mem_iff P z i).mp
      (hMap z i ((mem_cluster f i z).mp hz))
  have hHalf (i : I) : (i.val.card:ℝ) ≤ 2*((cluster f i).card:ℝ) := by
    have hs := hEqui.card_part_le_average_add_one i.property
    simp only [card_univ] at hs
    rw [hF]
    change i.val.card ≤ Fintype.card V/k+1 at hs
    exact_mod_cast (show i.val.card ≤ 2*(2*l) by dsimp only [l]; omega)
  refine ⟨I,inferInstance,f,R,l,by rwa [hK],by rw [hK]; exact (le_max_left _ _).trans hLo,
    by rwa [hK],hl,(hNone x).mpr (hEsub (by simp [E])),(hNone y).mpr (hEsub (by simp [E])),
    ?_,hF,hPaidExc.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hNn),hR,?_⟩
  · intro i
    have hi := hEven i
    rw [Fintype.card_subtype] at hi ⊢
    convert hi using 2
  rintro i j ⟨u,v,hu,hv,hAdj⟩
  obtain ⟨_,A,hA,B,hB,hAu,hBv,_,hOld,hDense⟩ := hAdj
  have hi : i.val = A := ((P.part_eq_iff_mem i.property).mpr
    (hSub i ((mem_cluster f i u).mpr hu))).symm.trans ((P.part_eq_iff_mem hA).mpr hAu)
  have hj : j.val = B := ((P.part_eq_iff_mem j.property).mpr
    (hSub j ((mem_cluster f j v).mpr hv))).symm.trans ((P.part_eq_iff_mem hB).mpr hBv)
  rw [←hi,←hj] at hOld hDense
  have hNew := RegularPairNeighbourhood.uniform_on_half_subcells G hεSmall hOld
    (hSub i) (hSub j) (hHalf i) (hHalf j)
  have hSize' (j : I) : (j.val.card:ℝ)*ε ≤ ((cluster f j).card:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right (hHalf j) hε.le
    have hh' := mul_le_mul_of_nonneg_left hεSmall (Nat.cast_nonneg (α := ℝ) (cluster f j).card)
    nlinarith only [hh,hh']
  have hDiff := hOld (hSub i) (hSub j) (hSize' i) (hSize' j)
  exact ⟨hNew,by linarith only [hDense,(abs_lt.mp hDiff).1]⟩

end OverfullWork.CMSBalancedCut
