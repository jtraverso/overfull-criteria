module

public import OverfullWork.CMSOperation41CorePacking
public import OverfullWork.CMSCleanupRobustness

@[expose] public section


/-! Lemma 3.14 with one size threshold and one expansion reserve
over the whole interval of possible host densities. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset SimpleGraph RobustExpansion DirectedReserveUsage
open scoped Classical
universe u v

private theorem finite_density_cover (α ε : ℝ) (hα : α ≤ 1) (hε : 0 < ε)
    (P : ℝ → ℝ → ℝ → ℕ → Prop)
    (hP : ∀ a ∈ Set.Icc α 1,∃ γ ρ : ℝ,0 < γ ∧ 0 < ρ ∧ ∃ N : ℕ,P a γ ρ N) :
    ∃ γ ρ : ℝ,0 < γ ∧ 0 < ρ ∧ ∃ N : ℕ,
      ∀ a ∈ Set.Icc α 1,∃ b ∈ Set.Icc α 1,∃ γ' ρ' : ℝ,∃ N' : ℕ,
        2*γ ≤ γ' ∧ ρ ≤ ρ' ∧ N' ≤ N ∧ |a-b| < min (γ'/2) ε ∧ P b γ' ρ' N' := by
  let I := ↥(Set.Icc α (1:ℝ))
  have hEvery (b : I) : ∃ γ ρ : ℝ,0 < γ ∧ 0 < ρ ∧ ∃ N : ℕ,P b.val γ ρ N :=
    hP b.val b.property
  choose g r hg hr size hs using hEvery
  let U (b : I) := Metric.ball b.val (min (g b/2) ε)
  have hOpen (b : I) : IsOpen (U b) := Metric.isOpen_ball
  have hCover : Set.Icc α 1 ⊆ ⋃ b,U b := by
    intro a ha
    let b : I := ⟨a,ha⟩
    exact Set.mem_iUnion.mpr ⟨b,Metric.mem_ball_self (lt_min (div_pos (hg b) (by norm_num)) hε)⟩
  obtain ⟨S,hS⟩ := (isCompact_Icc : IsCompact (Set.Icc α (1:ℝ))).elim_finite_subcover U hOpen hCover
  have hNonempty : S.Nonempty := by
    obtain ⟨b,hb,_⟩ := Set.mem_iUnion₂.mp (hS (show α ∈ Set.Icc α 1 from ⟨le_rfl,hα⟩))
    exact ⟨b,hb⟩
  obtain ⟨g₀,hgS,hGmin⟩ := S.exists_min_image g hNonempty
  obtain ⟨r₀,hrS,hRmin⟩ := S.exists_min_image r hNonempty
  refine ⟨g g₀/2,r r₀,div_pos (hg g₀) (by norm_num),hr r₀,S.sup size,?_⟩
  intro a ha
  obtain ⟨b,hb,hAb⟩ := Set.mem_iUnion₂.mp (hS ha)
  refine ⟨b.val,b.property,g b,r b,size b,?_,hRmin b hb,le_sup hb,?_,hs b⟩
  · have h := hGmin b hb
    linarith only [h]
  · simpa only [U,Metric.mem_ball,Real.dist_eq] using hAb

def HasPackedCoreLayouts {V : Type u} [Fintype V] {J : Type v} [Fintype J]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : J → ℕ)
    (e : ∀ j,(Fin (f j) × Bool) ↪ V) (I : J → Finset V) (ρ τ : ℝ) : Prop :=
  ∃ (w : ∀ j,Fin (2*f j+2) ↪ V) (F : ∀ j,Finset (Fin (2*f j+2)))
    (mark : ∀ j,Fin (f j) ↪ Fin (2*f j+2)),
    let L : ∀ j,Layout V (Fin (2*f j+2)) := fun j => cyclicLayout (by omega) (w j) (F j) (I j)
    (∀ j,F j = univ.image (mark j)) ∧
    (∀ j i,w j (mark j i) = e j (i,false) ∧ w j (finRotate (2*f j+2) (mark j i)) = e j (i,true)) ∧
    (∀ j i,w j i ∉ I j) ∧
    ∃ P : CMSPacking (fun j => Fin (2*f j+2)) G L,IsRealRobust (G \ hostEdges G P.used) ρ τ

set_option maxHeartbeats 1050000 in
theorem cms_operation_4_1_core_packing_uniform (α gap ν τ : ℝ)
    (hα : 0 < α) (hα₁ : α ≤ 1) (hgap : 0 < gap) (hgapα : 2*gap ≤ α)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτgap : 16384*τ ≤ gap) :
    ∃ γ ρ : ℝ,0 < γ ∧ 0 < ρ ∧ ∃ N : ℕ,
      ∀ {V : Type u} [Fintype V] {J : Type v} [Fintype J]
        (G : SimpleGraph V) [DecidableRel G.Adj] (a : ℝ) (f : J → ℕ)
        (e : ∀ j,(Fin (f j) × Bool) ↪ V) (I : J → Finset V),
        let B : J → Finset V := fun j => univ.image (e j) ∪ I j
        let n := Fintype.card V
        α ≤ a → a ≤ 1 → N ≤ n → IsRealRobust G ν τ →
        (∀ z, |(G.degree z:ℝ)-a*(n:ℝ)| ≤ γ*(n:ℝ)) →
        (Fintype.card J:ℝ) ≤ ((a-2*gap)/2)*(n:ℝ) →
        (∀ j i,e j i ∉ I j) →
        (∀ j,((B j).card+2:ℕ) ≤ γ*(n:ℝ)) →
        (∀ z,(visits B z+2:ℕ) ≤ γ*(n:ℝ)) →
        HasPackedCoreLayouts G f e I ρ τ := by
  let that (a γ ρ : ℝ) (N : ℕ) : Prop :=
    ∀ {V : Type u} [Fintype V] {J : Type v} [Fintype J]
      (G : SimpleGraph V) [DecidableRel G.Adj] (f : J → ℕ)
      (e : ∀ j,(Fin (f j) × Bool) ↪ V) (I : J → Finset V),
      let B : J → Finset V := fun j => univ.image (e j) ∪ I j
      let n := Fintype.card V
      N ≤ n → IsRealRobust G ν τ →
      (∀ z, |(G.degree z:ℝ)-a*(n:ℝ)| ≤ γ*(n:ℝ)) →
      (Fintype.card J:ℝ) ≤ ((a-gap)/2)*(n:ℝ) →
      (∀ j i,e j i ∉ I j) →
      (∀ j,((B j).card+2:ℕ) ≤ γ*(n:ℝ)) →
      (∀ z,(visits B z+2:ℕ) ≤ γ*(n:ℝ)) →
      HasPackedCoreLayouts G f e I ρ τ
  have hEach (a : ℝ) (ha : a ∈ Set.Icc α 1) : ∃ γ ρ : ℝ,0 < γ ∧ 0 < ρ ∧ ∃ N,that a γ ρ N := by
    obtain ⟨γ,ρ,hγ,hρ,N,hN⟩ := cms_operation_4_1_core_packing.{u,v} a gap ν τ
      (hα.trans_le ha.1) ha.2 hgap (by linarith only [ha.1,hgapα,hgap]) hν hντ hτgap
    refine ⟨γ,ρ,hγ,hρ,N,?_⟩
    intro V _ J _ G _ f e I B n hn hR hD hRounds hI hB hLoad
    obtain ⟨w,F,mark,hMark,hEnds,hIso,P,hRes,_⟩ := hN G f e I hn hR hD hRounds hI hB hLoad
    exact ⟨w,F,mark,hMark,hEnds,hIso,P,hRes⟩
  obtain ⟨γ,ρ,hγ,hρ,N,hCover⟩ := finite_density_cover α gap hα₁ hgap that hEach
  refine ⟨γ,ρ,hγ,hρ,N,?_⟩
  intro V _ J _ G _ a f e I B n ha ha₁ hn hR hD hRounds hI hB hLoad
  obtain ⟨b,_,γ',ρ',N',hγ',hρ',hN',hNear,hUse⟩ := hCover a ⟨ha,ha₁⟩
  have hnR : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hγ₁ : γ ≤ γ' := by linarith only [hγ,hγ']
  have hMargin : γ+|a-b| ≤ γ' := by
    have h := hNear.le.trans (min_le_left _ _)
    linarith only [h,hγ']
  have hCloseness (z : V) : |(G.degree z:ℝ)-b*(n:ℝ)| ≤ γ'*(n:ℝ) := calc
    _ ≤ |(G.degree z:ℝ)-a*(n:ℝ)|+|a*(n:ℝ)-b*(n:ℝ)| := abs_sub_le _ _ _
    _ ≤ (γ+|a-b|)*(n:ℝ) := by
      rw [←sub_mul,abs_mul,abs_of_nonneg hnR,add_mul]
      exact add_le_add (hD z) le_rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right hMargin hnR
  have hCap : (Fintype.card J:ℝ) ≤ ((b-gap)/2)*(n:ℝ) := by
    have h := (abs_lt.mp (hNear.trans_le (min_le_right _ _))).2
    exact hRounds.trans (mul_le_mul_of_nonneg_right (by linarith only [h]) hnR)
  have hγn := mul_le_mul_of_nonneg_right hγ₁ hnR
  obtain ⟨w,F,mark,hMark,hEnds,hIso,P,hRest⟩ := hUse G f e I (hN'.trans hn) hR hCloseness
    hCap hI (fun j => (hB j).trans hγn) (fun z => (hLoad z).trans hγn)
  unfold HasPackedCoreLayouts
  refine ⟨w,F,mark,hMark,hEnds,hIso,P,?_⟩
  intro S hLo hHi
  let H := G \ hostEdges G P.used
  have hScale := mul_le_mul_of_nonneg_right hρ' hnR
  have hSub : realNeighbourhood H ρ' S ⊆ realNeighbourhood H ρ S := by
    intro z hz
    exact mem_filter.mpr ⟨mem_univ _,hScale.trans (mem_filter.mp hz).2⟩
  have hMono : ((realNeighbourhood H ρ' S).card:ℝ) ≤ ((realNeighbourhood H ρ S).card:ℝ) :=
    by exact_mod_cast card_le_card hSub
  exact (add_le_add le_rfl hScale).trans ((hRest S hLo hHi).trans hMono)

end OverfullWork.DirectedSpanningConfiguration
