module

public import OverfullWork.BipartiteRobustCuts

@[expose] public section


/-! # Odd-cut reduction for a base with one exceptional centre

The large-set/small-set split follows CMS Claim 4.3. Here the actual
identified base is simple off one centre, so its deficit budget suffices
to reduce the small odd-cut obstruction to triples through that centre.
No assertion that these last triples are safe is built into the proof.
-/
namespace OverfullWork.StarBudgetOddCuts
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

theorem cut_mono (D M : MultiGraph V) (hsub : ∀e,D.mult e≤M.mult e) (S : Finset V) :
    D.cutSize S≤M.cutSize S := by
  apply sum_le_sum
  intro v hv
  exact sum_le_sum (fun w hw=>hsub _)

omit [Fintype V] in
theorem ordinary_internal_le (D : MultiGraph V) (z : V) (Y : ℕ)
    (hstar : D.IsStarAt z) (hmult : ∀v,D.mult s(z,v)≤Y)
    (S : Finset V) (v : V) (hv : v≠z) :
    (∑w∈S,D.mult s(v,w))≤S.card+Y := by
  have hPoint:∀w,D.mult s(v,w)≤1+(if w=z then Y else 0):=by
    intro w
    by_cases hw:w=z
    · subst w
      have hh:=hmult v
      rw [Sym2.eq_swap] at hh
      simp only [ite_true]
      omega
    · simpa only [if_neg hw,Nat.add_zero] using hstar v w hv hw
  calc
    _ ≤ ∑w∈S,(1+(if w=z then Y else 0)) :=sum_le_sum (fun w _=>hPoint w)
    _ ≤ _ :=by
      by_cases hz:z∈S <;> simp [sum_add_distrib,hz]

theorem three_ordinary_cut_bound (D : MultiGraph V) (Δ B Y : ℕ) (z : V)
    (hdeg : ∀v,D.degree v≤Δ) (hstar : D.IsStarAt z)
    (hmult : ∀v,D.mult s(z,v)≤Y)
    (hBudget : (∑v∈univ.erase z,(Δ-D.degree v))≤Δ+B)
    (S : Finset V) (hThree : 3≤(S.erase z).card) :
    2*Δ≤D.cutSize S+B+3*(S.card+Y) := by
  obtain ⟨U,hU,hCard⟩:=exists_subset_card_eq hThree
  have hUS:U⊆S:=hU.trans (erase_subset _ _)
  have hUz:U⊆univ.erase z:=by
    intro v hv
    exact mem_erase.mpr ⟨(mem_erase.mp (hU hv)).1,mem_univ _⟩
  have hDef:(∑v∈U,(Δ-D.degree v))≤Δ+B:=
    (sum_le_sum_of_subset_of_nonneg hUz (fun _ _ _=>Nat.zero_le _)).trans hBudget
  have hSum:(∑v∈U,D.degree v)+(∑v∈U,(Δ-D.degree v))=3*Δ :=by
    rw [←sum_add_distrib]
    calc
      _ = ∑_v∈U,Δ :=sum_congr rfl (fun v _=>Nat.add_sub_of_le (hdeg v))
      _ = _ :=by simp [hCard,Nat.mul_comm]
  have hInternal:(∑v∈U,∑w∈S,D.mult s(v,w))≤3*(S.card+Y):=by
    calc
      _ ≤ ∑_v∈U,(S.card+Y) :=by
        apply sum_le_sum
        intro v hv
        exact ordinary_internal_le D z Y hstar hmult S v (mem_erase.mp (hU hv)).1
      _ = _ :=by simp [hCard,Nat.mul_comm]
  have hCut:(∑v∈U,∑w∈Sᶜ,D.mult s(v,w))≤D.cutSize S:=
    sum_le_sum_of_subset_of_nonneg hUS (fun _ _ _=>Nat.zero_le _)
  have hSplit:(∑v∈U,D.degree v)=
      (∑v∈U,∑w∈S,D.mult s(v,w))+(∑v∈U,∑w∈Sᶜ,D.mult s(v,w)):=by
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro v hv
    rw [D.degree_eq_sum_mult]
    exact (sum_add_sum_compl S _).symm
  omega

/-- All remaining overfull obstructions, up to complementation, are
three-vertex sets containing the actual exceptional centre. -/
theorem no_overfull_iff_centre_triples (D M : MultiGraph V) (Δ B Y m r t : ℕ)
    (z : V) (A : Finset V)
    (hreg : M.IsRegularOfDegree Δ) (hsub : ∀e,D.mult e≤M.mult e)
    (hdeg : ∀v,D.degree v≤Δ) (hstar : D.IsStarAt z)
    (hmult : ∀v,D.mult s(z,v)≤Y)
    (hBudget : (∑v∈univ.erase z,(Δ-D.degree v))≤Δ+B)
    (hA : A.card=m) (hAc : Aᶜ.card=m)
    (hExpand : BipartiteRobustMargin.IsBipartiteRobustAt M.supportGraph A r t)
    (hThreshold : 2*t≤m) (hLarge : Δ≤r*r)
    (hSmall : B+3*(2*t+Y)≤Δ) :
    (¬M.HasOverfullSubset Δ) ↔
      ∀S : Finset V,S.card=3 → z∈S → Δ≤M.cutSize S := by
  rw [M.noOverfull_iff_odd_cut_bound hreg]
  constructor
  · intro h S hs hz
    exact h S (by rw [hs];exact ⟨1,rfl⟩)
  · intro hTriples S hOdd
    have hCard:Fintype.card V=2*m:=by
      have hh:=card_add_card_compl A
      omega
    have hHalf:∀T : Finset V,Odd T.card → T.card≤m → Δ≤M.cutSize T:=by
      intro T hOddT hT
      by_cases hBig:2*t≤T.card
      · exact hLarge.trans (BipartiteRobustCuts.large_cut_bound M A T m r t
          hA hAc hExpand hT hBig hThreshold)
      · by_cases hThree:3≤(T.erase z).card
        · have hh:=three_ordinary_cut_bound D Δ B Y z hdeg hstar hmult hBudget T hThree
          have hc:=cut_mono D M hsub T
          have hSize:T.card<2*t:=by omega
          have hm:=Nat.mul_le_mul_left 3 (show T.card+Y≤2*t+Y by omega)
          omega
        · have hErase:T.card≤(T.erase z).card+1:=by
            by_cases hz:z∈T
            · exact (card_erase_add_one hz).ge
            · rw [erase_eq_of_notMem hz];omega
          have hPositive:0<T.card:=by obtain ⟨a,ha⟩:=hOddT;omega
          have hOddSmall:T.card=1 ∨ T.card=3:=by obtain ⟨a,ha⟩:=hOddT;omega
          rcases hOddSmall with hOne|hThreeT
          · obtain ⟨v,hv⟩:=card_eq_one.mp hOne
            subst T
            rw [CanonicalAdmissibility.cut_singleton,hreg v]
          · have hz:z∈T:=by
              by_contra hz
              rw [erase_eq_of_notMem hz,hThreeT] at hThree
              omega
            exact hTriples T hThreeT hz
    by_cases hS:S.card≤m
    · exact hHalf S hOdd hS
    · have hEven:Even (Fintype.card V):=by rw [hCard];exact ⟨m,by omega⟩
      have hComp:=MultiGraph.odd_card_compl hEven hOdd
      have hCompSize:Sᶜ.card≤m:=by rw [card_compl,hCard];omega
      rw [←M.cutSize_compl S]
      exact hHalf Sᶜ hComp hCompSize

/-- A sufficient quantitative replacement for the exceptional-triple
case: the centre degree pays the ordinary deficit and bundle losses. -/
theorem centre_triple_cut_bound (D : MultiGraph V) (Δ B Y : ℕ) (z : V)
    (hdeg : ∀v,D.degree v≤Δ) (hstar : D.IsStarAt z)
    (hmult : ∀v,D.mult s(z,v)≤Y)
    (hBudget : (∑v∈univ.erase z,(Δ-D.degree v))+D.degree z≤Δ+B)
    (hCentre : B+4*Y+6≤2*D.degree z)
    (S : Finset V) (hS : S.card=3) (hz : z∈S) :
    Δ≤D.cutSize S := by
  let U:=S.erase z
  have hU:U.card=2:=by dsimp [U];have hh:=card_erase_add_one hz;omega
  have hUz:U⊆univ.erase z:=by
    intro v hv
    exact mem_erase.mpr ⟨(mem_erase.mp hv).1,mem_univ _⟩
  have hDef:(∑v∈U,(Δ-D.degree v))+D.degree z≤Δ+B:=by
    have hh: (∑v∈U,(Δ-D.degree v))≤∑v∈univ.erase z,(Δ-D.degree v):=
      sum_le_sum_of_subset_of_nonneg hUz (fun _ _ _=>Nat.zero_le _)
    omega
  have hSum:(∑v∈U,D.degree v)+(∑v∈U,(Δ-D.degree v))=2*Δ:=by
    rw [←sum_add_distrib]
    calc
      _ = ∑_v∈U,Δ :=sum_congr rfl (fun v _=>Nat.add_sub_of_le (hdeg v))
      _ = _ :=by simp [hU,Nat.mul_comm]
  have hCentreRow:(∑w∈S,D.mult s(z,w))≤2*Y:=by
    have hh:=sum_erase_add S (fun w=>D.mult s(z,w)) hz
    have hLoop:D.mult s(z,z)=0:=D.loopless _ (by simp)
    have hBound:(∑w∈U,D.mult s(z,w))≤2*Y:=by
      calc
        _ ≤ ∑_w∈U,Y :=sum_le_sum (fun w _=>hmult w)
        _ = _ :=by simp [hU,Nat.mul_comm]
    change (∑w∈S.erase z,D.mult s(z,w))≤2*Y at hBound
    omega
  have hOrdinary:(∑v∈U,∑w∈S,D.mult s(v,w))≤2*(3+Y):=by
    calc
      _ ≤ ∑_v∈U,(S.card+Y) :=by
        apply sum_le_sum
        intro v hv
        exact ordinary_internal_le D z Y hstar hmult S v (mem_erase.mp hv).1
      _ = _ :=by simp [hU,hS]
  have hInternal:D.twiceInternal S≤4*Y+6:=by
    have hh:=sum_erase_add S (fun v=>∑w∈S,D.mult s(v,w)) hz
    change (∑v∈S.erase z,∑w∈S,D.mult s(v,w))≤2*(3+Y) at hOrdinary
    unfold MultiGraph.twiceInternal
    omega
  have hSplit:=sum_erase_add S (fun v=>D.degree v) hz
  change (∑v∈S.erase z,(Δ-D.degree v))+D.degree z≤Δ+B at hDef
  change (∑v∈S.erase z,D.degree v)+(∑v∈S.erase z,(Δ-D.degree v))=2*Δ at hSum
  have hId:=D.sum_degree_eq_internal_add_cut S
  omega

end OverfullWork.StarBudgetOddCuts
