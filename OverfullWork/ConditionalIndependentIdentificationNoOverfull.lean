module

public import OverfullWork.IndependentSetIdentification
public import OverfullWork.IndependentIdentificationInternal
public import OverfullWork.MultigraphCuts
public import OverfullWork.OddCutDeficit

@[expose] public section


/-! # A finite no-overfull criterion for independent-set identification

The explicit numerical gap is a hypothesis. It is not inferred from an
unspecified asymptotic scale. The almost-overfull budget controls cuts
of sets away from the centre, while small centre-containing sets are
bounded directly by simplicity away from the centre and its multiplicity.
-/
namespace OverfullWork.ConditionalIndependentIdentification
open SimpleGraph Finset OddCutDeficit
open scoped Classical
variable {W : Type*} [Fintype W] [DecidableEq W]
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

private theorem internal_bound_away (M : MultiGraph (Option W))
    (hstar : M.IsStarAt none) (T : Finset (Option W)) (hnone : none∉T) :
    M.twiceInternal T≤T.card*(T.card-1) := by
  have hrow : ∀v∈T,(∑z∈T,M.mult s(v,z))≤T.card-1 := by
    intro v hv
    have hvnone : v≠none:=fun he=>hnone (he ▸ hv)
    have hs:=sum_erase_add T (fun z=>M.mult s(v,z)) hv
    rw [M.loopless _ (by simp),Nat.add_zero] at hs
    rw [←hs]
    calc
      _ ≤ ∑_z∈T.erase v,1 := by
        apply sum_le_sum
        intro z hz
        have hznone : z≠none:=fun he=>hnone (he ▸ (mem_erase.mp hz).2)
        exact hstar v z hvnone hznone
      _ = _ := by simp [card_erase_of_mem hv]
  calc
    _ ≤ ∑_v∈T,(T.card-1) := sum_le_sum hrow
    _ = _ := by simp

private theorem internal_bound_with_centre (M : MultiGraph (Option W))
    (hstar : M.IsStarAt none) (h : ℕ) (hmu : ∀v,M.mult s(none,v)≤h)
    (S : Finset (Option W)) (hnone : none∈S) :
    M.twiceInternal S≤(S.card-1)*(S.card-1-1)+2*h*(S.card-1) := by
  let A:=S.erase none
  have hA : none∉A:=notMem_erase _ _
  have hdecomp : S=insert none A := (insert_erase hnone).symm
  have hcard : A.card=S.card-1:=card_erase_of_mem hnone
  have hsplit : M.twiceInternal S=M.twiceInternal A+2*(∑v∈A,M.mult s(none,v)) := by
    rw [hdecomp]
    simp only [MultiGraph.twiceInternal,sum_insert hA]
    rw [M.loopless s((none:Option W),none) (by simp)]
    have hs : (∑u∈A,(M.mult s(u,none)+∑v∈A,M.mult s(u,v)))=
        (∑u∈A,M.mult s(none,u))+M.twiceInternal A := by
      rw [sum_add_distrib]
      congr 1
      apply sum_congr rfl
      intro u _
      rw [Sym2.eq_swap]
    rw [hs]
    unfold MultiGraph.twiceInternal
    ring
  have hi:=internal_bound_away M hstar A hA
  have hc : (∑v∈A,M.mult s(none,v))≤h*A.card := by
    calc
      _ ≤ ∑_v∈A,h := sum_le_sum (fun v _=>hmu v)
      _ = _ := by simp [Nat.mul_comm]
  rw [hsplit]
  rw [←hcard]
  nlinarith

private theorem cut_bound_singleton (M : MultiGraph (Option W)) (v : Option W) :
    M.cutSize {v}=M.degree v := by
  have hh:=M.sum_degree_eq_internal_add_cut {v}
  have hi : M.twiceInternal {v}=0 := by
    simp only [MultiGraph.twiceInternal,sum_singleton]
    exact M.loopless s(v,v) (by simp)
  simpa only [sum_singleton,hi,zero_add] using hh.symm

/-- Finite star-multigraph criterion. The only outside obstruction input
is absence of overfull odd sets avoiding the centre; the actual image
wrapper below obtains that property from the original simple graph. -/
theorem no_overfull_of_budget (M : MultiGraph (Option W)) (D B h : ℕ)
    (hdeg : ∀v,M.degree v≤D) (hstar : M.IsStarAt none)
    (hmu : ∀v,M.mult s(none,v)≤h)
    (hmin : ∀w,M.degree none≤M.degree (some w))
    (hodd : Odd (Fintype.card W))
    (hbudget : (∑v∈(univ:Finset (Option W)).erase none,(D-M.degree v))+M.degree none≤D+B)
    (hgap : Fintype.card W+B+2*h≤2*D+2)
    (haway : ∀S : Finset (Option W),Odd S.card → none∉S →
      M.twiceInternal S≤D*(S.card-1)) : ¬M.HasOverfullSubset D := by
  apply (M.noOverfull_iff_odd_bounds D hdeg).mpr
  intro S hSodd
  by_cases hSn:none∈S
  · let T:=Sᶜ
    have hTn : none∉T:=notMem_compl.mpr hSn
    have hsize : S.card+T.card=Fintype.card W+1 := by simp [T,Fintype.card_option]
    have hSp : 1≤S.card:=by obtain ⟨k,hk⟩:=hSodd;omega
    have hTeven : Even (Fintype.card (Option W)) := by
      rw [Fintype.card_option]
      obtain ⟨k,hk⟩:=hodd
      exact ⟨k+1,by omega⟩
    have hTodd : Odd T.card:=MultiGraph.odd_card_compl hTeven hSodd
    have hTp : 1≤T.card:=by obtain ⟨k,hk⟩:=hTodd;omega
    have hcut_implies : M.degree none≤M.cutSize T → M.twiceInternal S≤D*(S.card-1) := by
      intro hcut
      have hs:=M.sum_degree_eq_internal_add_cut S
      have hsum : (∑v∈S,M.degree v)≤D*(S.card-1)+M.degree none := by
        rw [←sum_erase_add S (fun v=>M.degree v) hSn]
        have he : (∑v∈S.erase none,M.degree v)≤D*(S.card-1) := by
          calc
            _ ≤ ∑_v∈S.erase none,D := sum_le_sum (fun v _=>hdeg v)
            _ = _ := by simp [card_erase_of_mem hSn,Nat.mul_comm]
        omega
      have hc : M.cutSize T=M.cutSize S:=M.cutSize_compl S
      omega
    by_cases hT1:T.card=1
    · obtain ⟨v,hv⟩:=card_eq_one.mp hT1
      have hvn : v≠none := by intro he;rw [hv,he] at hTn;simp at hTn
      apply hcut_implies
      rw [hv,cut_bound_singleton]
      cases v with
      | none => exact (hvn rfl).elim
      | some w => exact hmin w
    · have hTtwo : 2≤T.card:=by omega
      by_cases hsmall:T.card+B≤D
      · apply hcut_implies
        have hdef : (∑v∈T,(D-M.degree v))≤
            ∑v∈(univ:Finset (Option W)).erase none,(D-M.degree v) := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro v hv
            exact mem_erase.mpr ⟨fun he=>hTn (he ▸ hv),mem_univ _⟩
          · intro _ _ _;exact Nat.zero_le _
        have hi:=internal_bound_away M hstar T hTn
        have hs : M.twiceInternal T+M.cutSize T+(∑v∈T,(D-M.degree v))=D*T.card := by
          rw [←M.sum_degree_eq_internal_add_cut T,←sum_add_distrib]
          calc
            _ = ∑_v∈T,D := sum_congr rfl (fun v _=>Nat.add_sub_of_le (hdeg v))
            _ = _ := by simp [Nat.mul_comm]
        have hprod : B≤(T.card-1)*(D-T.card) := by
          have h1 : 1≤T.card-1:=by omega
          have h2 : B≤D-T.card:=by omega
          simpa using Nat.mul_le_mul h1 h2
        have halg : T.card*(T.card-1)+D+(T.card-1)*(D-T.card)=D*T.card := by
          calc
            _ = (T.card-1)*(T.card+(D-T.card))+D := by ring
            _ = (T.card-1)*D+D := by rw [Nat.add_sub_of_le (by omega : T.card≤D)]
            _ = D*((T.card-1)+1) := by ring
            _ = _ := by rw [Nat.sub_add_cancel (by omega : 1≤T.card)]
        omega
      · have hcap : (S.card-1)+2*h≤D+1 := by omega
        have hi:=internal_bound_with_centre M hstar h hmu S hSn
        by_cases hS1:S.card=1
        · rw [hS1] at hi ⊢
          simpa using hi
        · have hsub : S.card-1-1+2*h≤D := by omega
          have hm:=Nat.mul_le_mul_left (S.card-1) hsub
          nlinarith
  · exact haway S hSodd hSn

section ActualImage
variable {V : Type*} [Fintype V] [DecidableEq V]
open IndependentSetIdentification

/-- Actual independent-set identification preserves no-overfullness
under the displayed finite gap. The gap is explicit and is not claimed
to follow merely from an unspecified small-exception parameter. -/
theorem actual_image_no_overfull (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (hind : G.IsIndepSet (Y:Set V))
    (hno : ¬G.HasOverfullSubgraph) (hodd : Odd Yᶜ.card) (B : ℕ)
    (hmin : ∀x,x∉Y → (∑y∈Y,G.degree y)≤G.degree x)
    (hbudget : deficitMass G G.maxDegree Yᶜ+(∑y∈Y,G.degree y)≤G.maxDegree+B)
    (hgap : Yᶜ.card+B+2*Y.card≤2*G.maxDegree+2) :
    ¬(graph G Y hind).HasOverfullSubset G.maxDegree := by
  classical
  let M:=graph G Y hind
  have hcard : Fintype.card (Outside Y)=Yᶜ.card := by
    have hh:=card_vertices Y
    rw [Fintype.card_option] at hh
    omega
  have hp : 0<Yᶜ.card := by obtain ⟨k,hk⟩:=hodd;omega
  obtain ⟨x,hx⟩:=card_pos.mp hp
  have hxY : x∉Y:=mem_compl.mp hx
  have hsum : (∑y∈Y,G.degree y)≤G.maxDegree :=
    (hmin x hxY).trans (G.degree_le_maxDegree x)
  have hdeg : ∀v,M.degree v≤G.maxDegree :=
    degree_le G Y hind G.maxDegree G.degree_le_maxDegree hsum
  have hMmin : ∀w,M.degree none≤M.degree (some w) := by
    intro w
    rw [degree_none,degree_some]
    exact hmin w.val w.property
  have hmu : ∀v,M.mult s(none,v)≤Y.card := by
    intro v
    cases v with
    | none => rw [M.loopless s(none,none) (by simp)];exact Nat.zero_le _
    | some v => exact centre_mult_le G Y hind v
  have htotal : (∑v∈(univ:Finset (Vertices Y)).erase none,(G.maxDegree-M.degree v))=
      deficitMass G G.maxDegree Yᶜ := by
    have hs:=sum_erase_add (univ:Finset (Vertices Y))
      (fun v=>G.maxDegree-M.degree v) (mem_univ none)
    rw [Fintype.sum_option] at hs
    have hsome : (∑w : Outside Y,(G.maxDegree-M.degree (some w)))=
        deficitMass G G.maxDegree Yᶜ := by
      simp_rw [M,degree_some]
      exact (sum_subtype Yᶜ (fun v=>mem_compl) (fun v=>G.maxDegree-G.degree v)).symm
    rw [hsome] at hs
    omega
  apply no_overfull_of_budget M G.maxDegree B Y.card hdeg (isStarAt G Y hind) hmu hMmin
  · rw [hcard];exact hodd
  · rw [htotal,degree_none];exact hbudget
  · rw [hcard];exact hgap
  · intro S hS hn
    exact twiceInternal_bound_away_centre G Y hind hno S hS hn

/-- The original maximum degree is attained outside the independent set
under the centre-degree comparison. Identification therefore preserves
its actual maximum degree, as well as the pointwise upper bound. -/
theorem actual_image_has_maximum_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (hind : G.IsIndepSet (Y:Set V)) (hodd : Odd Yᶜ.card)
    (hmin : ∀x,x∉Y → (∑y∈Y,G.degree y)≤G.degree x) :
    (∀v,(graph G Y hind).degree v≤G.maxDegree) ∧
      ∃v,(graph G Y hind).degree v=G.maxDegree := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun x y=>Classical.propDecidable (G.Adj x y)))
  have hp : 0<Yᶜ.card := by obtain ⟨k,hk⟩:=hodd;omega
  obtain ⟨x,hx⟩:=card_pos.mp hp
  have hxY:x∉Y:=mem_compl.mp hx
  have hsum : (∑y∈Y,G.degree y)≤G.maxDegree :=
    (hmin x hxY).trans (G.degree_le_maxDegree x)
  refine ⟨degree_le G Y hind G.maxDegree G.degree_le_maxDegree hsum,?_⟩
  have : Nonempty V:=⟨x⟩
  obtain ⟨z,hz⟩:=G.exists_maximal_degree_vertex
  by_cases hzY:z∈Y
  · have hzsum : G.degree z≤∑y∈Y,G.degree y := by
      have hh:=sum_erase_add Y (fun y=>G.degree y) hzY
      omega
    have hxd : G.degree x=G.maxDegree := by
      have hh:=hmin x hxY
      have hd:=G.degree_le_maxDegree x
      omega
    refine ⟨some ⟨x,hxY⟩,?_⟩
    rw [degree_some,hxd]
  · refine ⟨some ⟨z,hzY⟩,?_⟩
    rw [degree_some,hz]

end ActualImage
end OverfullWork.ConditionalIndependentIdentification
