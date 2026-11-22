module

public import OverfullWork.CMSBalancedRobustCut
public import OverfullWork.HeavyNeighbourPartners

@[expose] public section


/-! The partition and light partners from Step 1 of the non-heavy
case of CMS Theorem 4.2, starting from global robust expansion. -/
namespace OverfullWork.CMSBalancedCut

open Finset SimpleGraph PrunedCore BipartiteRobustMargin RegularHeavyCutRepair
open scoped Classical
universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Data used to build the initial equitable internal multicolourings. -/
structure CaseTwoPartition (M : MultiGraph V) (a b : V)
    (d m L r t : ℕ) (η : ℝ) where
  part : Finset V
  partners : Finset V
  card_part : part.card = m
  card_compl : partᶜ.card = m
  centre_mem : a ∈ part
  second_not_mem : b ∉ part
  partnerEquiv : ↥(heavySet M a b L) ≃ ↥partners
  partners_subset : partners ⊆ part
  centre_not_partner : a ∉ partners
  second_not_partner : b ∉ partners
  partners_light : ∀ v ∈ partners, M.mult s(a,v) ≤ L
  heavy_across : ∀ v, v ≠ b → L < M.mult s(a,v) → v ∉ part
  free_weight_le : M.degreeInto (part \ insert a partners) a ≤
    M.degreeInto (partᶜ \ insert b (heavySet M a b L)) a
  centre_internal_le_half : 2*M.degreeInto part a ≤ d
  robust : IsBipartiteRobustAt M.supportGraph part r t
  simple_discrepancy : ∀ v, |(neighboursIn M.supportGraph part v:ℝ)-
    (neighboursIn M.supportGraph partᶜ v:ℝ)| < η*(m:ℝ)

set_option maxHeartbeats 1300000 in
/-- Two bounded cut repairs pay for the heavy neighbours and their
partners. The lower bound for the order is independent of the host. -/
theorem exists_case_two_partition_at_rate (ν τ η : ℝ) (T : ℕ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτcap : τ ≤ 1/16) (hη : 0 < η) (hT : 1 ≤ T) :
    ∃ ρ : ℝ, ρ = ν^4/524288 ∧ 0 < ρ ∧ ρ ≤ ν ∧ ∃ N : ℕ,
      ∀ {W : Type u} [Fintype W] [DecidableEq W]
        (M : MultiGraph W) (a b : W) (d m : ℕ),
        N ≤ Fintype.card W → Fintype.card W = 2*m → a ≠ b →
        M.IsRegularOfDegree d → d ≤ 3*m →
        RobustExpansion.IsRealRobust M.supportGraph ν τ →
        let h := 3*T+1
        let r := ⌈ρ*(m:ℝ)⌉₊-4*h
        let t := ⌈4*τ*(m:ℝ)⌉₊+2*h
        0 < r ∧ 2*t ≤ m ∧ Nonempty (CaseTwoPartition M a b d m (m/T) r t η) := by
  obtain ⟨ρ,hExact,hρ,hρν,N₀,hCuts⟩ := exists_balanced_robust_cut_at_rate.{u}
    ν τ (η/2) hν hντ (by linarith only [hτcap]) (by positivity)
  let h := 3*T+1
  obtain ⟨m₀,hm₀⟩ := exists_nat_ge (max (((4*h+1:ℕ):ℝ)/ρ)
    (max ((8*(h:ℝ))/η) ((8*h+4:ℕ):ℝ)))
  refine ⟨ρ,hExact,hρ,hρν,max N₀ (2*m₀),?_⟩
  intro W _ _ M a b d m hN hOrder hab hReg hD hRob
  let r₀ := ⌈ρ*(m:ℝ)⌉₊
  let t₀ := ⌈4*τ*(m:ℝ)⌉₊
  have hm : m₀ ≤ m := by
    have hh := (le_max_right _ _).trans hN
    rw [hOrder] at hh
    omega
  have hmR : (m₀:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hScale := hm₀.trans hmR
  have hr : 4*h+1 ≤ r₀ := by
    apply (Nat.cast_le (α := ℝ)).mp
    exact ((div_le_iff₀ hρ).mp ((le_max_left _ _).trans hScale)).trans
      (by dsimp only [r₀]; rw [mul_comm]; exact Nat.le_ceil _)
  have hRoom₀ : 8*h+4 ≤ m := by
    exact_mod_cast (le_max_right _ _).trans ((le_max_right _ _).trans hScale)
  have hError : (η/2)*(m:ℝ)+2*(h:ℝ)+2*(h:ℝ) ≤ η*(m:ℝ) := by
    have hh := (div_le_iff₀ hη).mp ((le_max_left _ _).trans ((le_max_right _ _).trans hScale))
    nlinarith only [hh]
  have hτ : 0 < τ := hν.trans_le hντ
  have hWindow : 2*(t₀+2*h) ≤ m := by
    have ht := (Nat.ceil_lt_add_one (show 0 ≤ 4*τ*(m:ℝ) by positivity)).le
    have hMul := mul_le_mul_of_nonneg_right hτcap (Nat.cast_nonneg (α := ℝ) m)
    have hRoomR : ((8*h+4:ℕ):ℝ) ≤ (m:ℝ) := by exact_mod_cast hRoom₀
    push_cast at hRoomR
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    dsimp only [t₀]
    nlinarith only [ht,hMul,hRoomR]
  obtain ⟨A,hA,hAc,ha,hb,hDis,hFwd,hBack⟩ :=
    hCuts M.supportGraph m a b ((le_max_left _ _).trans hN) hOrder hab hRob
  have hCount₀ := heavySet_card_at_scale M a b d m T hReg hD hT
  have hCount : (heavySet M a b (m/T)).card+1 ≤ h := by dsimp only [h]; omega
  obtain ⟨B,hB,hBc,hBa,hBb,hHeavy,_,hRobB,hDisB⟩ :=
    exists_adjusted_cut M d m (m/T) h r₀ t₀ hReg a b A hA hAc ha hb
      hCount (by omega) (by omega) ((η/2)*(m:ℝ)) hDis ⟨hFwd,hBack⟩
  obtain ⟨C,P,hC,hCc,hCa,hCb,hEquiv,hPC,haP,hbP,hLight,hHeavyC,hFree,hHalf,hRobC,hDisC⟩ :=
    HeavyNeighbourPartners.exists_partner_cut M d m (m/T) h (r₀-2*h) (t₀+h) hReg
      a b B hB hBc hBa hBb hHeavy hCount (by omega) (by omega)
      ((η/2)*(m:ℝ)+2*(h:ℝ)) hDisB hRobB
  change 0 < r₀-4*h ∧ 2*(t₀+2*h) ≤ m ∧ _
  refine ⟨by omega,hWindow,⟨{
    part := C
    partners := P
    card_part := hC
    card_compl := hCc
    centre_mem := hCa
    second_not_mem := hCb
    partnerEquiv := Classical.choice hEquiv
    partners_subset := hPC
    centre_not_partner := haP
    second_not_partner := hbP
    partners_light := hLight
    heavy_across := hHeavyC
    free_weight_le := hFree
    centre_internal_le_half := hHalf
    robust := ?_
    simple_discrepancy := fun v => (hDisC v).trans_le hError
  }⟩⟩
  convert hRobC using 1 <;> omega

theorem exists_case_two_partition (ν τ η : ℝ) (T : ℕ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτcap : τ ≤ 1/16) (hη : 0 < η) (hT : 1 ≤ T) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ν ∧ ∃ N : ℕ,
      ∀ {W : Type u} [Fintype W] [DecidableEq W]
        (M : MultiGraph W) (a b : W) (d m : ℕ),
        N ≤ Fintype.card W → Fintype.card W = 2*m → a ≠ b →
        M.IsRegularOfDegree d → d ≤ 3*m →
        RobustExpansion.IsRealRobust M.supportGraph ν τ →
        let h := 3*T+1
        let r := ⌈ρ*(m:ℝ)⌉₊-4*h
        let t := ⌈4*τ*(m:ℝ)⌉₊+2*h
        0 < r ∧ 2*t ≤ m ∧ Nonempty (CaseTwoPartition M a b d m (m/T) r t η) := by
  obtain ⟨r,_,hr,hrν,h⟩ := exists_case_two_partition_at_rate.{u} ν τ η T hν hντ hτcap hη hT
  exact ⟨r,hr,hrν,h⟩

end OverfullWork.CMSBalancedCut
