module

public import OverfullWork.CMSOperation41DegreeHistory
public import OverfullWork.CMSOperation41SingletonExhaustion
public import OverfullWork.CMSOperation41StepSelection

@[expose] public section


/-! After the first critical choice, the exceptional vertices have
small absolute degree, while the shorter limit retains a gap above
them. A vertex can then leave the exceptional set only by becoming
isolated. The ordinary set and its total deficiency have separate
invariants, including during the repair of an exhausted singleton. -/
namespace OverfullWork.CMSTrimmingRound

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In the short phase Step 4 keeps every surviving vertex which
was exceptional at entry. -/
theorem short_phase_exceptional_eq_inter_support
    (U : ℕ → Finset V) (degree : ℕ → V → ℕ) (D m threshold floor : ℕ)
    (hStart : U 0 ⊆ univ.filter (fun v => 0 < degree 0 v))
    (hSmall : ∀ v ∈ U 0,degree 0 v ≤ floor)
    (hMono : ∀ i < m,∀ v,degree (i+1) v ≤ degree i v)
    (hWindow : floor+threshold ≤ D-2*m)
    (hUpdate : ∀ i < m,U (i+1) = nextTrimmingExceptional (U i)
      (univ.filter (fun v => 0 < degree (i+1) v)) (degree (i+1)) (D-2*(i+1)) threshold) :
    ∀ i ≤ m,U i = U 0 ∩ univ.filter (fun v => 0 < degree i v) := by
  have hDegree (i : ℕ) (hi : i ≤ m) (v : V) : degree i v ≤ degree 0 v := by
    induction i with
    | zero => exact le_rfl
    | succ i ih => exact (hMono i (by omega) v).trans (ih (by omega))
  intro i hi
  induction i with
  | zero => exact inter_eq_left.mpr hStart |>.symm
  | succ i ih =>
    have hi' : i < m := by omega
    rw [hUpdate i hi',ih hi'.le]
    ext v
    simp only [nextTrimmingExceptional,mem_filter,mem_inter,mem_univ,true_and]
    constructor
    · exact fun h => ⟨h.1.1.1,h.1.2⟩
    · rintro ⟨hv,hPos⟩
      have hPrev := hMono i hi' v
      have hBound := (hDegree (i+1) hi v).trans (hSmall v hv)
      have hDecay : D-2*m ≤ D-2*(i+1) := by omega
      exact ⟨⟨⟨hv,by omega⟩,hPos⟩,by omega⟩

omit [Fintype V] [DecidableEq V] in
/-- For a fixed ordinary set, a round spends one unit of deficiency
per degree credit and adds precisely the ordinary cleanup losses. -/
theorem ordinary_deficit_balance_after_trimming_round
    (X : Finset V) (before after loss credit : V → ℕ) (d : ℕ) (hD : 2 ≤ d)
    (hBefore : ∀ v ∈ X,before v ≤ d) (hAfter : ∀ v ∈ X,after v ≤ d-2)
    (hCredit : ∀ v ∈ X,credit v ≤ 2)
    (hExact : ∀ v ∈ X,after v+loss v+(2-credit v) = before v) :
    (∑ v ∈ X,(d-2-after v))+(∑ v ∈ X,credit v) =
      (∑ v ∈ X,(d-before v))+(∑ v ∈ X,loss v) := by
  rw [←sum_add_distrib,←sum_add_distrib]
  apply sum_congr rfl
  intro v hv
  have h₁ := hBefore v hv
  have h₂ := hAfter v hv
  have h₃ := hCredit v hv
  have h₄ := hExact v hv
  omega

/-- A neutral round on an odd ordinary side spends the entire remaining
deficiency if the last-edge cleanup left at most two units. -/
theorem TrimmingStepSelection.ordinary_degrees_after_odd_empty_round
    {G : SimpleGraph V} [DecidableRel G.Adj] {initial current active : Finset V}
    {degree : V → ℕ} {d floor j cap : ℕ} {used : ℕ → Finset V}
    (R : TrimmingStepSelection G initial current active degree d floor used j cap)
    (next : V → ℕ) (hD : 2 ≤ d) (hEmpty : active = ∅)
    (hLow : ∀ v ∈ current,degree v < floor+2)
    (hBefore : ∀ v,degree v ≤ d) (hAfter : ∀ v,next v ≤ d-2)
    (hExact : ∀ v,next v+(2-R.round.words.degreeCredit R.round.omitted v) = degree v) :
    let X := (univ.filter (fun v => 0 < degree v)) \ current
    Odd X.card → (∑ v ∈ X,(d-degree v)) ≤ 2 → ∀ v ∈ X,next v = d-2 := by
  intro X hOdd hOld v hv
  have hNone : R.special = none := by
    cases h : R.special with
    | none => rfl
    | some w =>
      obtain ⟨hw,hHigh,_⟩ := R.special_debit w h
      exact (Nat.not_lt_of_ge hHigh (hLow w hw)).elim
  have hSpend := R.empty_odd_ordinary_credit hEmpty hOdd hNone
  change 2 ≤ ∑ u ∈ X,R.round.words.degreeCredit R.round.omitted u at hSpend
  have hBalance := ordinary_deficit_balance_after_trimming_round X degree next (fun _ => 0)
    (R.round.words.degreeCredit R.round.omitted) d hD
    (fun u _ => hBefore u) (fun u _ => hAfter u)
    (fun u _ => R.round.words.degree_credit_le_two R.round.omitted u)
    (fun u _ => by simpa only [add_zero] using hExact u)
  simp only [sum_const_zero,add_zero] at hBalance
  have hOne := single_le_sum (f := fun u => d-2-next u) (fun _ _ => Nat.zero_le _) hv
  have hCap := hAfter v
  omega

omit [Fintype V] in
/-- Removing the last edge at the exceptional singleton costs the
ordinary set at most one unit of total deficiency. -/
theorem ordinary_deficit_after_singleton_exhaustion
    (X : Finset V) (before after : V → ℕ) (d : ℕ) (w x : V) (hw : w ∉ X)
    (hBefore : ∀ v ∈ X,before v ≤ d)
    (hExact : ∀ v ∈ X,after v+(if v=w ∨ v=x then 1 else 0) = before v) :
    (∑ v ∈ X,(d-after v)) ≤ (∑ v ∈ X,(d-before v))+1 := by
  have hEq : (∑ v ∈ X,(d-after v)) =
      (∑ v ∈ X,(d-before v))+(∑ v ∈ X,if v=x then 1 else 0) := by
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro v hv
    have hNe : v ≠ w := fun he => hw (he ▸ hv)
    have hD := hBefore v hv
    have h := hExact v hv
    simp only [hNe,false_or] at h
    split_ifs at * <;> omega
  rw [hEq,Finset.sum_ite_eq']
  split <;> omega

set_option maxHeartbeats 2500000 in
/-- The ordinary side of the critical cut is fixed throughout a
short prefix. Even if cleanup adds deficiency, it cannot isolate an
ordinary vertex while its accumulated cost stays below the target. -/
theorem short_phase_preserves_ordinary_cut_and_deficit
    (U : ℕ → Finset V) (degree loss credit : ℕ → V → ℕ)
    (D m threshold floor b extra : ℕ)
    (hStart : U 0 ⊆ univ.filter (fun v => 0 < degree 0 v))
    (hSmall : ∀ v ∈ U 0,degree 0 v ≤ floor)
    (hWindow : floor+threshold ≤ D-2*m)
    (hRoom : 2*m ≤ D) (hLarge : b+extra < D-2*m)
    (hUpdate : ∀ i < m,U (i+1) = nextTrimmingExceptional (U i)
      (univ.filter (fun v => 0 < degree (i+1) v)) (degree (i+1)) (D-2*(i+1)) threshold)
    (hBound : ∀ i ≤ m,∀ v,degree i v ≤ D-2*i)
    (hCredit : ∀ i < m,∀ v,credit i v ≤ 2)
    (hRound : ∀ i < m,∀ v,degree (i+1) v+loss i v+(2-credit i v) = degree i v) :
    let support (i : ℕ) := univ.filter (fun v => 0 < degree i v)
    let X := support 0 \ U 0
    (∑ v ∈ X,(D-degree 0 v)) ≤ b →
    (∑ i ∈ range m,∑ v ∈ X,loss i v) ≤ extra →
    ∀ i ≤ m,support i \ U i = X ∧
      (∑ v ∈ X,(D-2*i-degree i v)) ≤ b+(∑ j ∈ range i,∑ v ∈ X,loss j v) := by
  intro support X hInitial hBudget
  have hMono (i : ℕ) (hi : i < m) (v : V) : degree (i+1) v ≤ degree i v := by
    have h := hRound i hi v
    omega
  have hKeep := short_phase_exceptional_eq_inter_support U degree D m threshold floor
    hStart hSmall hMono hWindow hUpdate
  have hToStart (i : ℕ) (hi : i ≤ m) : support i ⊆ support 0 := by
    induction i with
    | zero => exact Subset.rfl
    | succ i ih =>
      intro v hv
      have hp := (mem_filter.mp hv).2
      have h := hMono i (by omega) v
      exact ih (by omega) (mem_filter.mpr ⟨mem_univ _,by omega⟩)
  intro i hi
  induction i with
  | zero =>
    exact ⟨rfl,by simpa using hInitial⟩
  | succ i ih =>
    have hi' : i < m := by omega
    obtain ⟨_,hOld⟩ := ih hi'.le
    have hD : D-2*(i+1) = (D-2*i)-2 := by omega
    have hCost := ordinary_deficit_balance_after_trimming_round X (degree i) (degree (i+1))
      (loss i) (credit i) (D-2*i) (by omega)
      (fun v _ => hBound i hi'.le v) (fun v _ => hD ▸ hBound (i+1) hi v)
      (fun v _ => hCredit i hi' v) (fun v _ => hRound i hi' v)
    have hNext : (∑ v ∈ X,(D-2*(i+1)-degree (i+1) v)) ≤
        b+(∑ j ∈ range (i+1),∑ v ∈ X,loss j v) := by
      rw [hD,sum_range_succ]
      omega
    refine ⟨?_,hNext⟩
    rw [hKeep (i+1) hi]
    ext v
    simp only [X,mem_sdiff,mem_inter]
    constructor
    · rintro ⟨hv,hn⟩
      exact ⟨hToStart (i+1) hi hv,fun he => hn ⟨he,hv⟩⟩
    · rintro ⟨hv,hn⟩
      have hvX : v ∈ X := mem_sdiff.mpr ⟨hv,hn⟩
      have hLoss : (∑ j ∈ range (i+1),∑ z ∈ X,loss j z) ≤ extra :=
        (sum_le_sum_of_subset_of_nonneg (range_mono hi) (fun _ _ _ => Nat.zero_le _)).trans hBudget
      have hDef : D-2*(i+1)-degree (i+1) v ≤
          ∑ z ∈ X,(D-2*(i+1)-degree (i+1) z) :=
        single_le_sum (f := fun z => D-2*(i+1)-degree (i+1) z) (fun _ _ => Nat.zero_le _) hvX
      exact ⟨mem_filter.mpr ⟨mem_univ _,by omega⟩,fun he => hn he.1⟩

omit [Fintype V] [DecidableEq V] in
/-- Numerical reserve at the paper's shorter round limit. The upper
exceptional band and the lower reserve of a new active pair both fit. -/
theorem short_limit_exceptional_and_pair_reserves (D loss : ℕ) (shift : ℝ)
    (hShift : 16 ≤ shift) (hD : 6*shift ≤ (D:ℝ)) (hLoss : (loss:ℝ) ≤ shift/2) :
    let floor := ⌊(D:ℝ)/3-shift⌋₊
    let limit := ⌊(D:ℝ)/3-2*shift⌋₊
    let threshold := ⌈shift⌉₊
    floor+1+threshold ≤ D-2*limit ∧ limit+6+loss ≤ floor := by
  intro floor limit threshold
  have hFloor₀ : 0 ≤ (D:ℝ)/3-shift := by linarith only [hShift,hD]
  have hLimit₀ : 0 ≤ (D:ℝ)/3-2*shift := by linarith only [hD]
  have hFloor : (floor:ℝ) ≤ (D:ℝ)/3-shift := Nat.floor_le hFloor₀
  have hFloor' := Nat.lt_floor_add_one ((D:ℝ)/3-shift)
  change (D:ℝ)/3-shift < (floor:ℝ)+1 at hFloor'
  have hLimit : (limit:ℝ) ≤ (D:ℝ)/3-2*shift := Nat.floor_le hLimit₀
  have hThreshold : (threshold:ℝ) ≤ shift+1 := (Nat.ceil_lt_add_one (by linarith only [hShift])).le
  have h₁ : floor+1+threshold+2*limit ≤ D := by
    exact_mod_cast (show (floor:ℝ)+1+threshold+2*limit ≤ D by
      linarith only [hFloor,hLimit,hThreshold,hShift])
  have h₂ : limit+6+loss ≤ floor := by
    exact_mod_cast (show (limit:ℝ)+6+loss ≤ floor by
      linarith only [hFloor',hLimit,hLoss,hShift])
  exact ⟨by omega,h₂⟩

end OverfullWork.CMSTrimmingRound
