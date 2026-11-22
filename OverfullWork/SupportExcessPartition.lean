module

public import OverfullWork.SupportExcessDiscrepancy
public import OverfullWork.SortedCentreL1

@[expose] public section


/-! # Randomize only the simple support and pay excess deterministically

The exceptional centre is either treated by its excess budget or by an
L1-controlled pairing, valid for every signing. No excess-square bound
or restriction S^2 <= m is required.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 4000000

/-- A fixed prescribed pairing with either an ordinary centre budget or
an L1 centre budget yields discrepancy below 2r from simple-support signs. -/
theorem exists_support_excess_partition_for_pairing {m : ℕ} (M : MultiGraph V)
    (e : (Fin m×Bool) ≃ V) (x y : V) (i₀ : Fin m)
    (hex : e (i₀,true)=x) (hey : e (i₀,false)=y) (b S r : ℕ)
    (hbudget : M.HasParallelBudget x b) (hbS : b≤S)
    (hcentre : M.parallelExcess x≤b ∨
      (∑ i : Fin m,|(M.mult s(x,e (i,true)):ℝ)-(M.mult s(x,e (i,false)):ℝ)|)≤2*(S:ℝ))
    (hr : S<r) (hmoment : 3000*(m:ℝ)^4<(r:ℝ)^6) :
    ∃ L : Finset V,L.card=m ∧ Lᶜ.card=m ∧ x∈L ∧ y∉L ∧
      ∀ v,|(M.degreeInto L v:ℝ)-(M.degreeInto Lᶜ v:ℝ)|<2*(r:ℝ) := by
  let a : V → Fin m → ℝ:=fun v i => M.supportRow v (e (i,true))-M.supportRow v (e (i,false))
  have ha : ∀ v i,|a v i|≤1 := by
    intro v i
    have ht:=M.supportRow_bounds v (e (i,true))
    have hf:=M.supportRow_bounds v (e (i,false))
    dsimp [a]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hcard : Fintype.card V=2*m := by
    have hh:=Fintype.card_congr e
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hh
    omega
  have hsize : 15*(Fintype.card V:ℝ)*(m:ℝ)^3<(r:ℝ)^6 := by
    rw [hcard]
    push_cast
    have hmnonneg : (0:ℝ)≤(m:ℝ)^4:=by positivity
    nlinarith only [hmoment,hmnonneg]
  obtain ⟨s,hs⟩:=OverfullWork.SigningMoments.exists_signing_discrepancy m a ha (r:ℝ) (by positivity) hsize
  let L:=OverfullWork.PairedPartition.part e s
  have hsupp : ∀ v,|(∑ u∈L,M.supportRow v u)-(∑ u∈Lᶜ,M.supportRow v u)|<(r:ℝ) := by
    intro v
    dsimp only [L]
    rw [OverfullWork.PairedPartition.difference_eq_signedSum]
    exact hs v
  have hrR : (S:ℝ)<(r:ℝ):=by exact_mod_cast hr
  have hordinary : ∀ v,M.parallelExcess v≤b →
      |(M.degreeInto L v:ℝ)-(M.degreeInto Lᶜ v:ℝ)|<2*(r:ℝ) := by
    intro v hbv
    have herror:=M.degree_discrepancy_le_support_add_excess L v
    have hbound : (M.parallelExcess v:ℝ)≤(S:ℝ):=by exact_mod_cast hbv.trans hbS
    have hsupport:=hsupp v
    nlinarith only [herror,hbound,hsupport,hrR]
  have hdis : ∀ v,|(M.degreeInto L v:ℝ)-(M.degreeInto Lᶜ v:ℝ)|<2*(r:ℝ) := by
    intro v
    by_cases hvx : v=x
    · subst v
      rcases hcentre with hcx|hL1
      · exact hordinary x hcx
      · have hcentral:=OverfullWork.SortedCentreL1.signedSum_abs_le_of_pair_l1 e
          (fun u => (M.mult s(x,u):ℝ)) (2*(S:ℝ)) hL1 s
        have hid : (M.degreeInto L x:ℝ)-(M.degreeInto Lᶜ x:ℝ)=
            OverfullWork.SigningMoments.signedSum
              (fun i => (M.mult s(x,e (i,true)):ℝ)-(M.mult s(x,e (i,false)):ℝ)) s := by
          dsimp only [L]
          simpa only [degreeInto,Nat.cast_sum] using
            OverfullWork.PairedPartition.difference_eq_signedSum e s (fun u => (M.mult s(x,u):ℝ))
        rw [hid]
        exact hcentral.trans_lt (by linarith)
    · exact hordinary v (hbudget v hvx)
  have hxysep : x∈L ↔ y∉L := by
    rw [←hex,←hey]
    exact OverfullWork.PairedPartition.separates_pairs e s i₀
  have hL:=OverfullWork.PairedPartition.card_part e s
  have hSc:=OverfullWork.PairedPartition.card_compl_part e s
  by_cases hx : x∈L
  · exact ⟨L,hL,hSc,hx,hxysep.mp hx,hdis⟩
  · have hy : y∈L := by
      by_contra hny
      exact hx (hxysep.mpr hny)
    refine ⟨Lᶜ,hSc,by simpa using hL,by simpa using hx,by simpa using hy,?_⟩
    intro v
    simpa only [compl_compl,abs_sub_comm] using hdis v

/-- A support/excess partition with one prescribed exceptional centre.
The two branches of CentreControl are handled separately. -/
theorem exists_support_excess_degree_partition_center (M : MultiGraph V)
    (x y : V) (hxy : x≠y) (m b S r : ℕ) (hm : 1≤m)
    (hcard : Fintype.card V=2*m) (hbudget : M.HasParallelBudget x b)
    (hbS : b≤S) (hS : 1≤S) (hcontrol : M.CentreControl x b)
    (hr : S<r) (hmoment : 3000*(m:ℝ)^4<(r:ℝ)^6) :
    ∃ L : Finset V,L.card=m ∧ Lᶜ.card=m ∧ x∈L ∧ y∉L ∧
      ∀ v,|(M.degreeInto L v:ℝ)-(M.degreeInto Lᶜ v:ℝ)|<2*(r:ℝ) := by
  let i₀ : Fin m:=⟨0,by omega⟩
  rcases hcontrol with hcap|hexcess
  · have hw : ∀ v,0≤(M.mult s(x,v):ℝ) ∧ (M.mult s(x,v):ℝ)≤(S:ℝ) := by
      intro v
      exact ⟨Nat.cast_nonneg _,by exact_mod_cast (hcap v).trans hbS⟩
    obtain ⟨e,hex,hey,hL1⟩:=OverfullWork.SortedCentreL1.exists_sorted_pairing_prescribed_l1
      hm hcard x y hxy (fun v => (M.mult s(x,v):ℝ)) (S:ℝ) hw
    exact M.exists_support_excess_partition_for_pairing e x y i₀ hex hey b S r
      hbudget hbS (Or.inr hL1) hr hmoment
  · let p:=pairEmbedding x y hxy
    obtain ⟨e,he⟩:=OverfullWork.PairedPartition.exists_pairing_extending hcard hm p
    have hex : e (i₀,true)=x := by
      have hh:=he (0 : Fin 1) true
      have hp : p (0,true)=x := by
        change (if (true : Bool) then x else y)=x
        simp only [ite_true]
      change e (i₀,true)=p (0,true) at hh
      exact hh.trans hp
    have hey : e (i₀,false)=y := by
      have hh:=he (0 : Fin 1) false
      have hp : p (0,false)=y := by
        change (if (false : Bool) then x else y)=y
        simp only [Bool.false_eq_true,if_false]
      change e (i₀,false)=p (0,false) at hh
      exact hh.trans hp
    exact M.exists_support_excess_partition_for_pairing e x y i₀ hex hey b S r
      hbudget hbS (Or.inl hexcess) hr hmoment

end SimpleGraph.MultiGraph
