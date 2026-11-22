module

public import OverfullWork.OsthusStadenPrimaryCopyScales
public import OverfullWork.DirectedPairEnergy
public import OverfullWork.OsthusStadenH1Assembly

@[expose] public section


/-! The common physical copies and thin reserves at the end of §5.2. -/
namespace OverfullWork.DirectedRegularPairs

open Finset DirectedRobustExpansion DirectedClusterQuotient DirectedPairEnergy
open scoped Classical
universe u v

/-- All six parts of each reduced copy use the same retained coordinates.
The exceptional count is measured in the original vertex type. -/
structure OsthusStadenPrimaryReserveData {V : Type u} [Fintype V] {I : Type v} [Fintype I]
    (H : Digraph V) (f : V → Option I) (M : I → I → ℕ) (m₀ b : ℕ)
    (β γ η a exceptionBound : ℝ) where
  size : ℕ
  size_pos : 0 < size
  size_dvd : b ∣ size
  base : I → Fin m₀ ↪ V
  base_cells : ∀ i, (univ : Finset (Fin m₀)).map (base i) = cluster f i
  kept : I → Fin size ↪ Fin m₀
  partition : V → Option I
  retained_cells : ∀ i, (univ : Finset (Fin size)).map ((kept i).trans (base i)) = cluster partition i
  cell_subset : ∀ i, cluster partition i ⊆ cluster f i
  exceptional_eq : (exceptional partition).card =
    (exceptional f).card+(m₀-size)*Fintype.card I
  exceptional_le : ((exceptional partition).card:ℝ) ≤ exceptionBound*(Fintype.card V:ℝ)
  copy : ReducedCopy M → Digraph (Fin m₀)
  copy_le : ∀ e, liftDirectedPair (base e.1.1) (base e.1.2) (copy e) ≤ H
  copy_disjoint : ∀ e e', e ≠ e' →
    Disjoint (liftDirectedPair (base e.1.1) (base e.1.2) (copy e))
      (liftDirectedPair (base e'.1.1) (base e'.1.2) (copy e'))
  thin : Fin 5 → ReducedCopy M → Digraph (Fin size)
  main : ReducedCopy M → Digraph (Fin size)
  thin_regular : ∀ j e, IsCentredRegular (thin j e) η (γ*β)
  main_regular : ∀ e, IsCentredRegular (main e) η ((1-5*γ)*β)
  copy_partition : ∀ e x y, (copy e).Adj (kept e.1.1 x) (kept e.1.2 y) ↔
    (main e).Adj x y ∨ ∃ j,(thin j e).Adj x y
  thin_disjoint : ∀ j l, j ≠ l →
    let src := fun e : ReducedCopy M => (kept e.1.1).trans (base e.1.1)
    let dst := fun e : ReducedCopy M => (kept e.1.2).trans (base e.1.2)
    Disjoint (directedPairUnion src dst (thin j)) (directedPairUnion src dst (thin l))
  main_thin_disjoint : ∀ j,
    let src := fun e : ReducedCopy M => (kept e.1.1).trans (base e.1.1)
    let dst := fun e : ReducedCopy M => (kept e.1.2).trans (base e.1.2)
    Disjoint (directedPairUnion src dst (thin j)) (directedPairUnion src dst main)
  h1 : ∀ j s i x,
    let src := fun e : ReducedCopy M => (kept e.1.1).trans (base e.1.1)
    let dst := fun e : ReducedCopy M => (kept e.1.2).trans (base e.1.2)
    let deg := pairSemidegree s (directedPairUnion src dst (thin j)) ((kept i).trans (base i) x)
    γ*a*(Fintype.card V:ℝ)/3 ≤ (deg:ℝ) ∧ (deg:ℝ) ≤ 2*γ*a*(Fintype.card V:ℝ)

/-- Uniform bound on the residual copies for which a retained vertex has
atypical in- or outdegree, with the two directions counted separately. -/
def OsthusStadenPrimaryReserveData.MainCopyIncidenceBound
    {V I : Type*} [Fintype V] [Fintype I] {H : Digraph V} {f : V → Option I}
    {M : I → I → ℕ} {m₀ b : ℕ} {β γ η a exc : ℝ}
    (B : OsthusStadenPrimaryReserveData H f M m₀ b β γ η a exc) (bound : ℝ) : Prop :=
  ∀ s i x, ((atypicalIncidentCopies (fun e : ReducedCopy M => e.1.1) (fun e => e.1.2)
    B.main η ((1-5*γ)*β) s i x).card:ℝ) ≤ bound

set_option maxHeartbeats 1200000 in
/-- Construct the physical copies, divisible retained cells and their
five disjoint reserves from the regular quotient and its degree bounds. -/
theorem exists_osthus_staden_primary_reserves_for_quotient_with_good_main
    (β γ ε δ₁ δ₂ δ₃ ξ σ : ℝ) (b : ℕ)
    (hβ : 0 < β) (hβ₁ : β ≤ 1) (hγ : 0 < γ) (hSum : 5*γ ≤ 1)
    (hε : 0 ≤ ε) (hClone : ε ≤ δ₁/4)
    (hδ₁ : 0 < δ₁) (hδ₁One : δ₁ ≤ 1)
    (hσ : 0 < σ) (hσSmall : σ ≤ 1/4) (hb : 0 < b)
    (hξ : 0 < ξ) (hξOne : ξ ≤ 1) (hBad : 8*ξ ≤ γ*β)
    (hTrimGood : 4*δ₁ ≤ ξ*σ) (hTrimReg : 4*(δ₁+σ) ≤ δ₂)
    (hReserve : δ₂ ≤ δ₃/4) (hδ₃ : 0 < δ₃) (hδ₃One : δ₃ ≤ 1) (hThin : 2*δ₃ ≤ γ*β) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {I : Type v} [Fintype I]
      (H : Digraph V) (f : V → Option I) (m₀ : ℕ) (a e d : ℝ),
      N ≤ m₀ → 0 < a → 0 ≤ e → e+2*σ ≤ 1/9 → 12*e ≤ a →
      (∀ i, (cluster f i).card = m₀) →
      ((exceptional f).card:ℝ) ≤ e*(Fintype.card V:ℝ) →
      (∀ i j, (quotient H f).Adj i j → IsUniform H ε (cluster f i) (cluster f j) ∧
        β ≤ density H (cluster f i) (cluster f j)) →
      (let M := reducedMultiplicity (quotient H f) (fun i j => density H (cluster f i) (cluster f j)) β
       ∀ (s : Bool) i, let p := if s then ∑ j,M i j else ∑ j,M j i
        (a-4*d)*(Fintype.card I:ℝ) ≤ β*(p:ℝ) ∧ β*(p:ℝ) ≤ (a+2*e)*(Fintype.card I:ℝ)) →
      3*a/4 ≤ (1-ξ)*(a-4*d) →
      let M := reducedMultiplicity (quotient H f) (fun i j => density H (cluster f i) (cluster f j)) β
      ∃ B : OsthusStadenPrimaryReserveData H f M m₀ b β γ δ₃ a (e+2*σ),
        B.MainCopyIncidenceBound (ξ*(a+2*e)*(Fintype.card I:ℝ)/β) := by
  let L := ⌈1/β⌉₊
  have hL : 1 ≤ (L:ℝ)*β := (div_le_iff₀ hβ).mp (Nat.le_ceil _)
  obtain ⟨N₁,hN₁⟩ := exists_quotient_clone_pairs.{u,v} L β ε δ₁ hβ hL hε hClone hδ₁ hδ₁One
  obtain ⟨N₂,hN₂⟩ := exists_primary_copy_trim σ b hσ hσSmall hb
  have hδ₂ : 0 ≤ δ₂ := by linarith only [hTrimReg,hδ₁,hσ]
  obtain ⟨N₃,hN₃⟩ := exists_thin_reserves_with_h1_partition_and_good_main.{u,0,v,v}
    β γ δ₁ δ₂ δ₃ ξ hβ hβ₁ hγ hSum hδ₁ hδ₁One hδ₂ hReserve hδ₃ hδ₃One hThin hξ hξOne
  refine ⟨max N₁ (max N₂ (max 1 (2*N₃))),?_⟩
  intro V _ I _ H f m₀ a e d hm₀ ha he hExcScale hE12 hSize hExc hPairs hCounts hLow
  let K : ℝ := Fintype.card I
  let n : ℝ := Fintype.card V
  let den (i j : I) := density H (cluster f i) (cluster f j)
  let M := reducedMultiplicity (quotient H f) den β
  let source (c : ReducedCopy M) := c.1.1
  let target (c : ReducedCopy M) := c.1.2
  have hK : 0 ≤ K := Nat.cast_nonneg _
  have hn : 0 ≤ n := Nat.cast_nonneg _
  obtain ⟨A,D,hACells,hATag,hD,hDSub,hDDis⟩ := hN₁ H f (quotient H f) m₀ den
    ((le_max_left _ _).trans hm₀) hSize (fun i j hij =>
      ⟨(hPairs i j hij).2,density_le_one H _ _,(hPairs i j hij).1,by simp [den,hε]⟩)
  obtain ⟨t,m,ht,hDiv,hHalf,hTLo,hTHi⟩ := hN₂ m₀
    (((le_max_left _ _).trans (le_max_right _ _)).trans hm₀)
  have hm₀pos : 0 < m₀ := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hm₀
  have hmPos : 0 < m := by omega
  have hmR : (0:ℝ) < m := by exact_mod_cast hmPos
  have hm₀R : (0:ℝ) ≤ m₀ := Nat.cast_nonneg _
  have hHalfR : (m₀:ℝ) ≤ 2*(m:ℝ) := by exact_mod_cast hHalf
  have hSizeEq : (t:ℝ)+(m:ℝ) = (m₀:ℝ) := by exact_mod_cast ht
  have hOrder : n = ((exceptional f).card:ℝ)+(m₀:ℝ)*K := by
    dsimp only [n,K]
    exact_mod_cast order_eq f m₀ hSize
  have hOrdLe : (m₀:ℝ)*K ≤ n := by
    linarith only [hOrder,Nat.cast_nonneg (α := ℝ) (exceptional f).card]
  have hExtra : (t:ℝ)*K ≤ 2*σ*n := by
    have h := mul_le_mul_of_nonneg_right hTHi hK
    rw [mul_assoc] at h
    exact h.trans (mul_le_mul_of_nonneg_left hOrdLe (by positivity))
  have hRetLo : 8*n ≤ 9*((m:ℝ)*K) := by
    have hSplit := congrArg (fun x : ℝ => x*K) hSizeEq
    rw [add_mul] at hSplit
    have hScale := mul_le_mul_of_nonneg_right hExcScale hn
    linarith only [hOrder,hSplit,hScale,hExtra,hExc]
  have hRetHi : (m:ℝ)*K ≤ n := by
    have h := mul_le_mul_of_nonneg_right (show (m:ℝ) ≤ m₀ by
      linarith only [hSizeEq,Nat.cast_nonneg (α := ℝ) t]) hK
    exact h.trans hOrdLe
  let aNorm := a*n/(m:ℝ)
  have hANormEq : aNorm*(m:ℝ) = a*n := div_mul_cancel₀ _ hmR.ne'
  have hANorm : a*K ≤ aNorm := by
    apply (le_div_iff₀ hmR).mpr
    calc
      a*K*(m:ℝ) = a*((m:ℝ)*K) := by ring
      _ ≤ a*n := mul_le_mul_of_nonneg_left hRetHi ha.le
  have hANormUpper : 8*aNorm ≤ 9*a*K := by
    apply (mul_le_mul_iff_of_pos_right hmR).mp
    have hScale := mul_le_mul_of_nonneg_left hRetLo ha.le
    rw [mul_assoc,hANormEq]
    linear_combination hScale
  have hRetGood : 4*δ₁*(m₀:ℝ) ≤ ξ*(t:ℝ) := by
    calc
      _ ≤ (ξ*σ)*(m₀:ℝ) := mul_le_mul_of_nonneg_right hTrimGood hm₀R
      _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hTLo hξ.le
  have hRetReg : 2*δ₁*(m₀:ℝ)+(t:ℝ) ≤ δ₂*(m:ℝ) := by
    calc
      _ ≤ 2*(δ₁+σ)*(m₀:ℝ) := by linarith only [hTHi]
      _ ≤ 2*(δ₁+σ)*(2*(m:ℝ)) := mul_le_mul_of_nonneg_left hHalfR (by positivity)
      _ = (4*(δ₁+σ))*(m:ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hTrimReg hmR.le
  have hFold : 2*δ₁ ≤ δ₂ := by linarith only [hTrimReg,hδ₁,hσ]
  have hRetScale : (m₀:ℝ)*δ₁ ≤ (m:ℝ)*δ₂ := by
    have h := mul_le_mul_of_nonneg_right hHalfR hδ₁.le
    have h' := mul_le_mul_of_nonneg_right hFold hmR.le
    linarith only [h,h']
  have hRetLarge : (m₀:ℝ)*δ₁ ≤ (m:ℝ) := by
    have h := mul_le_mul_of_nonneg_right (show δ₂ ≤ 1 by linarith only [hReserve,hδ₃One]) hmR.le
    linarith only [hRetScale,h]
  have hCounts' (s : Bool) (i : I) :
      (a-4*d)*K ≤ β*((incidentCopySet source target s i).card:ℝ) ∧
        β*((incidentCopySet source target s i).card:ℝ) ≤ (a+2*e)*K := by
    dsimp only [source,target]
    rw [reducedCopy_incident_count]
    exact hCounts s i
  have hLow' : 3*a*K/4 ≤ (1-ξ)*((a-4*d)*K) := by
    calc
      _ = (3*a/4)*K := by ring
      _ ≤ ((1-ξ)*(a-4*d))*K := mul_le_mul_of_nonneg_right hLow hK
      _ = _ := by ring
  have hHigh' : 6*((a+2*e)*K) ≤ 7*a*K := by
    have h := mul_le_mul_of_nonneg_right (show 6*(a+2*e) ≤ 7*a by linarith only [hE12]) hK
    linear_combination h
  have hBad' : 4*ξ*((a+2*e)*K) ≤ γ*β*(a*K) := by
    have h := mul_le_mul_of_nonneg_left (show a+2*e ≤ 2*a by linarith only [ha,hE12]) (show 0 ≤ 4*ξ by positivity)
    have h' := mul_le_mul_of_nonneg_right hBad ha.le
    have hh : 4*ξ*(a+2*e) ≤ γ*β*a := by linarith only [h,h']
    calc
      _ = (4*ξ*(a+2*e))*K := by ring
      _ ≤ (γ*β*a)*K := mul_le_mul_of_nonneg_right hh hK
      _ = _ := by ring
  have hSeparate (i j : I) (x y : Fin m₀) (hxy : A i x = A j y) : i = j :=
    Option.some.inj ((hATag i x).symm.trans ((congrArg f hxy).trans (hATag j y)))
  obtain ⟨keep,F,R,hF,hR,hDis,hRDis,_,hArcEq,hH1,hGoodMain⟩ :=
    hN₃ source target A D t m aNorm a e d (by simpa only [Fintype.card_fin] using ht)
      (by
        have hM : 2*N₃ ≤ m₀ :=
          (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hm₀
        omega)
      (by simpa only [Fintype.card_fin] using hRetGood)
      hFold (by simpa only [Fintype.card_fin] using hRetLarge)
      (by simpa only [Fintype.card_fin] using hRetScale)
      (by simpa only [Fintype.card_fin] using hRetReg)
      hD hSeparate hDDis hCounts' hANorm hANormUpper hLow' hHigh' hBad' hANormEq
  let cells (i : I) := (univ : Finset (Fin m)).map ((keep i).trans (A i))
  have hCellSub (i : I) : cells i ⊆ cluster f i := by
    rw [←hACells i]
    rintro v hv
    obtain ⟨x,_,rfl⟩ := mem_map.mp hv
    exact mem_map.mpr ⟨keep i x,mem_univ _,rfl⟩
  let g := equalize f cells
  have hg (i : I) : cluster g i = cells i := cluster_equalize f cells hCellSub i
  have hgCard (i : I) : (cluster g i).card = m := by
    simp only [hg,cells,card_map,card_univ,Fintype.card_fin]
  have hExcEq : (exceptional g).card = (exceptional f).card+(m₀-m)*Fintype.card I := by
    have hOld := order_eq f m₀ hSize
    have hNew := order_eq g m hgCard
    rw [←ht,add_mul] at hOld
    have hEq : m₀-m = t := by omega
    rw [hEq]
    omega
  have hExcLe : ((exceptional g).card:ℝ) ≤ (e+2*σ)*n := by
    rw [hExcEq,Nat.cast_add,Nat.cast_mul,show m₀-m = t by omega,add_mul]
    exact add_le_add hExc hExtra
  refine ⟨{
    size := m
    size_pos := hmPos
    size_dvd := hDiv
    base := A
    base_cells := hACells
    kept := keep
    partition := g
    retained_cells := fun i => (hg i).symm
    cell_subset := fun i => (hg i).symm ▸ hCellSub i
    exceptional_eq := hExcEq
    exceptional_le := hExcLe
    copy := D
    copy_le := hDSub
    copy_disjoint := hDDis
    thin := F
    main := R
    thin_regular := hF
    main_regular := hR
    copy_partition := hArcEq
    thin_disjoint := hDis
    main_thin_disjoint := hRDis
    h1 := hH1
  },?_⟩
  intro s i x
  refine (hGoodMain s i x).trans ?_
  apply (le_div_iff₀ hβ).mpr
  have h := mul_le_mul_of_nonneg_left (hCounts' s i).2 hξ.le
  calc
    (ξ*((incidentCopySet source target s i).card:ℝ))*β =
        ξ*(β*((incidentCopySet source target s i).card:ℝ)) := by ring
    _ ≤ ξ*(a+2*e)*(Fintype.card I:ℝ) := by simpa only [mul_assoc] using h

/-- Construct the primary reserves with their original interface. -/
theorem exists_osthus_staden_primary_reserves_for_quotient
    (β γ ε δ₁ δ₂ δ₃ ξ σ : ℝ) (b : ℕ)
    (hβ : 0 < β) (hβ₁ : β ≤ 1) (hγ : 0 < γ) (hSum : 5*γ ≤ 1)
    (hε : 0 ≤ ε) (hClone : ε ≤ δ₁/4)
    (hδ₁ : 0 < δ₁) (hδ₁One : δ₁ ≤ 1)
    (hσ : 0 < σ) (hσSmall : σ ≤ 1/4) (hb : 0 < b)
    (hξ : 0 < ξ) (hξOne : ξ ≤ 1) (hBad : 8*ξ ≤ γ*β)
    (hTrimGood : 4*δ₁ ≤ ξ*σ) (hTrimReg : 4*(δ₁+σ) ≤ δ₂)
    (hReserve : δ₂ ≤ δ₃/4) (hδ₃ : 0 < δ₃) (hδ₃One : δ₃ ≤ 1) (hThin : 2*δ₃ ≤ γ*β) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {I : Type v} [Fintype I]
      (H : Digraph V) (f : V → Option I) (m₀ : ℕ) (a e d : ℝ),
      N ≤ m₀ → 0 < a → 0 ≤ e → e+2*σ ≤ 1/9 → 12*e ≤ a →
      (∀ i, (cluster f i).card = m₀) →
      ((exceptional f).card:ℝ) ≤ e*(Fintype.card V:ℝ) →
      (∀ i j, (quotient H f).Adj i j → IsUniform H ε (cluster f i) (cluster f j) ∧
        β ≤ density H (cluster f i) (cluster f j)) →
      (let M := reducedMultiplicity (quotient H f) (fun i j => density H (cluster f i) (cluster f j)) β
       ∀ (s : Bool) i, let p := if s then ∑ j,M i j else ∑ j,M j i
        (a-4*d)*(Fintype.card I:ℝ) ≤ β*(p:ℝ) ∧ β*(p:ℝ) ≤ (a+2*e)*(Fintype.card I:ℝ)) →
      3*a/4 ≤ (1-ξ)*(a-4*d) →
      let M := reducedMultiplicity (quotient H f) (fun i j => density H (cluster f i) (cluster f j)) β
      Nonempty (OsthusStadenPrimaryReserveData H f M m₀ b β γ δ₃ a (e+2*σ)) := by
  obtain ⟨N,hN⟩ := exists_osthus_staden_primary_reserves_for_quotient_with_good_main.{u,v}
    β γ ε δ₁ δ₂ δ₃ ξ σ b hβ hβ₁ hγ hSum hε hClone hδ₁ hδ₁One hσ hσSmall hb
    hξ hξOne hBad hTrimGood hTrimReg hReserve hδ₃ hδ₃One hThin
  refine ⟨N,?_⟩
  intro V I _ _ H f m₀ a e d hN₀ ha he hExcScale hE12 hSize hExc hPairs hCounts hLow
  obtain ⟨B,_⟩ := hN H f m₀ a e d hN₀ ha he hExcScale hE12 hSize hExc hPairs hCounts hLow
  exact ⟨B⟩

end OverfullWork.DirectedRegularPairs
