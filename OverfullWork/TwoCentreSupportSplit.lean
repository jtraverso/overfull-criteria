module

public import OverfullWork.SecondLowNoOverfullCompletion

@[expose] public section


/-! Split any multigraph simple away from two centres into a simple base
and actual extra copies. The addition away from the first centre costs
at most twice the external degree of the second centre. -/
namespace OverfullWork.TwoCentreSupportSplit
open SimpleGraph Finset
open scoped Classical
variable {W : Type*} [Fintype W] [DecidableEq W]
set_option maxHeartbeats 8000000

noncomputable def base (M : MultiGraph (Sum Bool W)) : MultiGraph (Sum Bool W) :=
  MultiGraph.ofSimpleGraph M.supportGraph

noncomputable def extra (M : MultiGraph (Sum Bool W)) : MultiGraph (Sum Bool W) :=
  M.subtractCopies (base M)

theorem base_le (M : MultiGraph (Sum Bool W)) : ∀ e, (base M).mult e ≤ M.mult e := by
  intro e
  induction e using Sym2.inductionOn with
  | hf u v =>
    simp only [base,MultiGraph.ofSimpleGraph,mem_edgeSet,MultiGraph.supportGraph]
    split_ifs <;> omega

theorem split_eq (M : MultiGraph (Sum Bool W)) : (base M).addCopies (extra M)=M :=
  MultiGraph.add_subtract_of_le M (base M) (base_le M)

theorem base_star (M : MultiGraph (Sum Bool W)) : (base M).IsStarAt (Sum.inl false) := by
  intro u v _ _
  change (if M.supportGraph.Adj u v then 1 else 0) ≤ 1
  split_ifs <;> omega

theorem extra_ordinary_zero (M : MultiGraph (Sum Bool W))
    (hSimple : ∀ u v : W, M.mult s(Sum.inr u,Sum.inr v) ≤ 1) (u v : W) :
    (extra M).mult s(Sum.inr u,Sum.inr v)=0 := by
  have hh := hSimple u v
  simp only [extra,base,MultiGraph.subtractCopies,MultiGraph.ofSimpleGraph,mem_edgeSet,
    MultiGraph.supportGraph]
  split_ifs <;> omega

theorem extra_budget (M : MultiGraph (Sum Bool W)) (D : ℕ) (hReg : M.IsRegularOfDegree D)
    (hSimple : ∀ u v : W, M.mult s(Sum.inr u,Sum.inr v) ≤ 1) :
    (extra M).twiceInternal (univ.erase (Sum.inl false)) ≤
      2*(D-M.mult s(Sum.inl false,Sum.inl true)) := by
  let R := (univ : Finset W).image (Sum.inr : W → Sum Bool W)
  have hNot : Sum.inl true ∉ R := by simp [R]
  have hSet : (univ.erase (Sum.inl false) : Finset (Sum Bool W))=insert (Sum.inl true) R := by
    ext v
    cases v with
    | inl i => cases i <;> simp [R]
    | inr w => simp [R]
  have hInternal : (extra M).twiceInternal (univ.erase (Sum.inl false))=
      2*(∑ w : W, (extra M).mult s(Sum.inl true,Sum.inr w)) := by
    rw [hSet,MultiGraph.twiceInternal]
    simp only [sum_insert hNot,R,sum_image (fun _ _ _ _ h => Sum.inr.inj h),
      extra_ordinary_zero M hSimple,
      (extra M).loopless s(Sum.inl true,Sum.inl true) (by simp),
      sum_const_zero,Nat.add_zero,Nat.zero_add]
    have hSwap : (∑ w : W, (extra M).mult s(Sum.inr w,Sum.inl true))=
        ∑ w : W, (extra M).mult s(Sum.inl true,Sum.inr w) :=
      sum_congr rfl (fun _ _ => congrArg _ Sym2.eq_swap)
    rw [hSwap]
    omega
  have hRow := M.degree_eq_sum_mult (Sum.inl true)
  rw [Fintype.sum_sum_type,Fintype.sum_bool,M.loopless _ (by simp),Nat.zero_add,hReg] at hRow
  have hPair : M.mult s(Sum.inl true,Sum.inl false)=M.mult s(Sum.inl false,Sum.inl true) :=
    congrArg M.mult Sym2.eq_swap
  have hExtra : (∑ w : W, (extra M).mult s(Sum.inl true,Sum.inr w)) ≤
      ∑ w : W, M.mult s(Sum.inl true,Sum.inr w) :=
    sum_le_sum (fun _ _ => Nat.sub_le _ _)
  rw [hInternal]
  rw [hPair] at hRow
  omega

end OverfullWork.TwoCentreSupportSplit
