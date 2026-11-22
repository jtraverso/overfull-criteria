module

public import OverfullWork.MaximumOddCutPacking
public import OverfullWork.SparseDeficitCore

@[expose] public section


/-! # Geometry of near-tight odd sets above density one half

A nontrivial odd set whose internal edge count is within r of the
D-overfull threshold has at least D-r vertices. Its complement is small
when the total degree deficit is small, and its high-degree part has a
separate bound independent of that total deficit. These are necessary
geometric estimates, not a choice of a removable matching or cycle.
-/
namespace OverfullWork.NearTightOddSetGeometry
open SimpleGraph Finset OddCutDeficit PrunedCore RobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Simplicity bounds the number of internal edges at an odd set. -/
theorem internalEdges_le_card_mul_half (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hodd : Odd S.card) :
    internalEdges G S≤S.card*(S.card/2) := by
  have hc : internalEdges G S≤S.card.choose 2 := by
    rw [internalEdges,G.card_filter_edgeFinset_toFinset_subset S]
    have hh:=SimpleGraph.card_edgeFinset_le_card_choose_two
      (G:=G.induce (S : Set V))
    simpa using hh
  obtain ⟨m,hm⟩:=hodd
  have hh : S.card/2=m := by omega
  have he : S.card-1=2*m := by omega
  rw [Nat.choose_two_right,he] at hc
  have hmul : S.card*(2*m)=(S.card*m)*2 := by ring
  rw [hmul,Nat.mul_div_cancel _ (by norm_num)] at hc
  simpa only [hh] using hc

/-- Near-tightness pays for exactly D+2r units of cut plus deficit. -/
theorem cut_deficit_le_of_near_tight (G : SimpleGraph V) [DecidableRel G.Adj]
    (D r : ℕ) (hD : ∀v,G.degree v≤D) (S : Finset V) (hodd : Odd S.card)
    (hnear : D*(S.card/2)≤ internalEdges G S+r) :
    cutEdges G S+deficitMass G D S≤D+2*r := by
  have hi:=internal_cut_deficit_identity G D hD S
  obtain ⟨m,hm⟩:=hodd
  have hh : S.card/2=m := by omega
  rw [hh] at hnear
  rw [hm] at hi
  nlinarith only [hi,hnear]

/-- Singletons are excluded: every other near-tight odd set has size
at least D-r. No minimum-degree assumption is needed. -/
theorem degree_le_card_add_error (G : SimpleGraph V) [DecidableRel G.Adj]
    (D r : ℕ) (S : Finset V) (hodd : Odd S.card) (hthree : 3≤S.card)
    (hnear : D*(S.card/2)≤ internalEdges G S+r) : D≤S.card+r := by
  have hc:=internalEdges_le_card_mul_half G S hodd
  have hm : 1≤S.card/2 := by omega
  by_contra hn
  have hd : S.card+r+1≤D := by omega
  have hh:=Nat.mul_le_mul_right (S.card/2) hd
  have hr:=Nat.mul_le_mul_left r hm
  nlinarith only [hnear,hc,hh,hr,hm]

theorem cutEdges_compl (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    cutEdges G Sᶜ=cutEdges G S := by
  rw [cutEdges_eq_multigraph,cutEdges_eq_multigraph,MultiGraph.cutSize_compl]

/-- Every simple induced block has at most t(t-1) internal degree. -/
theorem twice_internalEdges_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) : 2*internalEdges G T≤T.card*(T.card-1) := by
  have hc : internalEdges G T≤T.card.choose 2 := by
    rw [internalEdges,G.card_filter_edgeFinset_toFinset_subset T]
    have hh:=SimpleGraph.card_edgeFinset_le_card_choose_two
      (G:=G.induce (T : Set V))
    simpa using hh
  have hm:=Nat.mul_le_mul_left 2 hc
  rw [Nat.choose_two_right] at hm
  have heven : 2∣T.card*(T.card-1) := by
    exact even_iff_two_dvd.mp (Nat.even_mul_pred_self T.card)
  rw [Nat.mul_div_cancel' heven] at hm
  exact hm

/-- A near-tight set forces its complement to spend deficit mass.
The left side is the complement's target degree sum. -/
theorem complement_degree_budget (G : SimpleGraph V) [DecidableRel G.Adj]
    (D r : ℕ) (hD : ∀v,G.degree v≤D) (S : Finset V) (hodd : Odd S.card)
    (hnear : D*(S.card/2)≤ internalEdges G S+r) :
    D*Sᶜ.card+deficitMass G D S≤
      Sᶜ.card*(Sᶜ.card-1)+D+2*r+deficitMass G D Sᶜ := by
  have hb:=cut_deficit_le_of_near_tight G D r hD S hodd hnear
  have hi:=internal_cut_deficit_identity G D hD Sᶜ
  rw [cutEdges_compl] at hi
  have hs:=twice_internalEdges_le G Sᶜ
  omega

/-- Above-half degree and small total deficit force the complement of
any nontrivial near-tight odd set to be small. -/
theorem complement_card_mul_gap_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (D r g : ℕ) (hD : ∀v,G.degree v≤D) (S : Finset V)
    (hodd : Odd S.card) (hthree : 3≤S.card)
    (hnear : D*(S.card/2)≤ internalEdges G S+r)
    (hgap : Fintype.card V+g+r≤2*D+1) :
    g*Sᶜ.card≤D+2*r+SparseDeficitCore.totalDeficit G D := by
  have hsize:=degree_le_card_add_error G D r S hodd hthree hnear
  have hcard : S.card+Sᶜ.card=Fintype.card V := by simp
  have hb:=complement_degree_budget G D r hD S hodd hnear
  have hmass : deficitMass G D Sᶜ≤SparseDeficitCore.totalDeficit G D :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
  by_cases ht : Sᶜ.card=0
  · simp only [ht,Nat.mul_zero,Nat.zero_le]
  · have hpred : Sᶜ.card-1+1=Sᶜ.card := by omega
    have hg : g+(Sᶜ.card-1)≤D := by omega
    have hm:=Nat.mul_le_mul_right Sᶜ.card hg
    nlinarith only [hm,hb,hmass]

/-- The high-degree part of the complement has bounded cardinality
independently of the total deficit. All its remaining vertices are among
the explicitly defined low-degree exceptions. -/
theorem high_complement_card_mul_local_gap_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (D r a g : ℕ) (hD : ∀v,G.degree v≤D) (S : Finset V)
    (hodd : Odd S.card)
    (hnear : D*(S.card/2)≤ internalEdges G S+r)
    (hgap : g+Sᶜ.card+a≤D) :
    g*(Sᶜ\SparseDeficitCore.exceptions G D a).card≤D+2*r := by
  let H:=Sᶜ\SparseDeficitCore.exceptions G D a
  have hcard : S.card+Sᶜ.card=Fintype.card V := by simp
  have hrow : ∀v∈H,g≤neighboursIn G S v := by
    intro v hv
    have hnot := (mem_sdiff.mp hv).2
    have hg:=SparseDeficitCore.degree_add_threshold_of_not_exception G D a v hnot
    have hd:=degree_add_card_le_neighboursIn_add_order G S v
    omega
  have hs : g*H.card≤∑v∈H,neighboursIn G S v := by
    calc
      _ = ∑_v∈H,g := by simp [Nat.mul_comm]
      _ ≤ _ := sum_le_sum hrow
  have hcut : cutEdges G S=∑v∈Sᶜ,neighboursIn G S v :=
    MaximumOddCutPacking.cut_eq_sum_neighboursIn G S Sᶜ
      disjoint_compl_right (fun _ _ v _ => by by_cases hv : v∈S <;> simp_all)
  have hsub : H⊆Sᶜ := sdiff_subset
  have hsum : (∑v∈H,neighboursIn G S v)≤cutEdges G S := by
    rw [hcut]
    exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  have hb:=cut_deficit_le_of_near_tight G D r hD S hodd hnear
  exact hs.trans (hsum.trans (by omega))

/-- The global above-half margin implies the local complement margin. -/
theorem high_complement_card_mul_gap_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (D r a g : ℕ) (hD : ∀v,G.degree v≤D) (S : Finset V)
    (hodd : Odd S.card) (hthree : 3≤S.card)
    (hnear : D*(S.card/2)≤ internalEdges G S+r)
    (hgap : Fintype.card V+g+r+a≤2*D) :
    g*(Sᶜ\SparseDeficitCore.exceptions G D a).card≤D+2*r := by
  have hsize:=degree_le_card_add_error G D r S hodd hthree hnear
  have hcard : S.card+Sᶜ.card=Fintype.card V := by simp
  exact high_complement_card_mul_local_gap_le G D r a g hD S hodd hnear (by omega)

/-- A near-tight odd set has only a bounded number of vertices outside
both itself and the low-degree exceptional set. This is an explicit
containment statement, not an assumed absorber. -/
theorem exists_small_high_complement (G : SimpleGraph V) [DecidableRel G.Adj]
    (D r a g : ℕ) (hD : ∀v,G.degree v≤D) (S : Finset V)
    (hodd : Odd S.card) (hthree : 3≤S.card)
    (hnear : D*(S.card/2)≤ internalEdges G S+r)
    (hgap : Fintype.card V+g+r+a≤2*D) :
    ∃H : Finset V,H⊆Sᶜ ∧ g*H.card≤D+2*r ∧
      Sᶜ⊆SparseDeficitCore.exceptions G D a∪H := by
  refine ⟨Sᶜ\SparseDeficitCore.exceptions G D a,sdiff_subset,
    high_complement_card_mul_gap_le G D r a g hD S hodd hthree hnear hgap,?_⟩
  intro v hv
  by_cases he : v∈SparseDeficitCore.exceptions G D a
  · exact mem_union_left _ he
  · exact mem_union_right _ (mem_sdiff.mpr ⟨hv,he⟩)

/-- An actual finite vertex cover bounds the edge count by its degree sum. -/
theorem edge_count_le_cover_degree_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (hcover : ∀u v,G.Adj u v → u∈H ∨ v∈H) :
    G.edgeFinset.card≤∑v∈H,G.degree v := by
  have hsub : G.edgeFinset⊆H.biUnion (fun v => G.incidenceFinset v) := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      have hxy : G.Adj u v := by simpa only [mem_edgeFinset,mem_edgeSet] using he
      rcases hcover u v hxy with hu|hv
      · exact mem_biUnion.mpr ⟨u,hu,G.mem_incidenceFinset.mpr
          (G.mk'_mem_incidenceSet_left_iff.mpr hxy)⟩
      · exact mem_biUnion.mpr ⟨v,hv,G.mem_incidenceFinset.mpr
          (G.mk'_mem_incidenceSet_right_iff.mpr hxy)⟩
  calc
    _ ≤ (H.biUnion (fun v => G.incidenceFinset v)).card := card_le_card hsub
    _ ≤ ∑v∈H,(G.incidenceFinset v).card := card_biUnion_le
    _ = _ := by simp only [card_incidenceFinset_eq_degree]

/-- If the low-degree exceptions are independent, every edge inside T
meets its high-degree remainder; hence the complement has O(|H||T|)
edges rather than just the quadratic simplicity bound. -/
theorem internalEdges_le_high_remainder (G : SimpleGraph V) [DecidableRel G.Adj]
    (D a : ℕ) (T : Finset V)
    (hInd : G.IsIndepSet (SparseDeficitCore.exceptions G D a : Set V)) :
    internalEdges G T≤(T\SparseDeficitCore.exceptions G D a).card*T.card := by
  let K:=G.induce (T : Set V)
  let A : Finset (T : Set V):=univ.filter fun v => v.val∉SparseDeficitCore.exceptions G D a
  have himage : A.image Subtype.val=T\SparseDeficitCore.exceptions G D a := by
    ext v
    simp only [mem_image,mem_sdiff]
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact ⟨w.property,(mem_filter.mp hw).2⟩
    · rintro ⟨hv,hw⟩
      exact ⟨⟨v,hv⟩,mem_filter.mpr ⟨mem_univ _,hw⟩,rfl⟩
  have hcard : A.card=(T\SparseDeficitCore.exceptions G D a).card := by
    rw [←himage,card_image_of_injective _ Subtype.val_injective]
  have hcover : ∀u v,K.Adj u v → u∈A ∨ v∈A := by
    intro u v huv
    by_cases hu : u.val∈SparseDeficitCore.exceptions G D a
    · by_cases hv : v.val∈SparseDeficitCore.exceptions G D a
      · have hi:=hInd
        rw [SimpleGraph.isIndepSet_iff] at hi
        exact False.elim (hi hu hv
          (show u.val≠v.val from (show G.Adj u.val v.val from huv).ne) huv)
      · exact Or.inr (mem_filter.mpr ⟨mem_univ v,hv⟩)
    · exact Or.inl (mem_filter.mpr ⟨mem_univ u,hu⟩)
  have hc:=edge_count_le_cover_degree_sum K A hcover
  have hd : (∑v∈A,K.degree v)≤A.card*T.card := by
    calc
      _ ≤ ∑_v∈A,T.card := sum_le_sum (fun v _ => by
        have hh:=K.degree_lt_card_verts v
        simpa using hh.le)
      _ = _ := by simp [Nat.mul_comm]
  rw [internalEdges,G.card_filter_edgeFinset_toFinset_subset T]
  exact hc.trans (by simpa only [hcard] using hd)

/-- Critical graphs have the independent low-degree remainder needed for
the sparse-complement estimate, by the already proved VAL degree sum. -/
theorem critical_internalEdges_le_high_remainder (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcrit : Overfull.IsDeltaCritical G) (a : ℕ)
    (hthreshold : 2*(G.maxDegree-a-1)≤G.maxDegree) (T : Finset V) :
    internalEdges G T≤(T\SparseDeficitCore.exceptions G G.maxDegree a).card*T.card :=
  internalEdges_le_high_remainder G G.maxDegree a T
    (SparseDeficitCore.critical_exceptions_independent G hcrit a hthreshold)

/-- A critical near-tight odd set has a sparse complement once the
complement fits below the local degree margin. In particular, the edge
bound is linear in the complement size when g is proportional to Delta. -/
theorem critical_complement_internalEdges_mul_gap_le (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcrit : Overfull.IsDeltaCritical G)
    (r a g : ℕ) (S : Finset V) (hodd : Odd S.card)
    (hnear : G.maxDegree*(S.card/2)≤ internalEdges G S+r)
    (hgap : g+Sᶜ.card+a≤G.maxDegree)
    (hthreshold : 2*(G.maxDegree-a-1)≤G.maxDegree) :
    g*internalEdges G Sᶜ≤(G.maxDegree+2*r)*Sᶜ.card := by
  have hh:=high_complement_card_mul_local_gap_le G G.maxDegree r a g
    G.degree_le_maxDegree S hodd hnear hgap
  have he:=critical_internalEdges_le_high_remainder G hcrit a hthreshold Sᶜ
  calc
    _ ≤ g*((Sᶜ\SparseDeficitCore.exceptions G G.maxDegree a).card*Sᶜ.card) :=
      Nat.mul_le_mul_left g he
    _ = (g*(Sᶜ\SparseDeficitCore.exceptions G G.maxDegree a).card)*Sᶜ.card := by ring
    _ ≤ _ := Nat.mul_le_mul_right Sᶜ.card hh

/-- Under the above-half margin two nontrivial near-tight odd sets
cannot be disjoint. This asserts intersection, not laminarity. -/
theorem not_disjoint_of_near_tight (G : SimpleGraph V) [DecidableRel G.Adj]
    (D r : ℕ) (S T : Finset V)
    (hSodd : Odd S.card) (hSthree : 3≤S.card)
    (hSnear : D*(S.card/2)≤ internalEdges G S+r)
    (hTodd : Odd T.card) (hTthree : 3≤T.card)
    (hTnear : D*(T.card/2)≤ internalEdges G T+r)
    (hdense : Fintype.card V+2*r<2*D) : ¬Disjoint S T := by
  intro hdis
  have hS:=degree_le_card_add_error G D r S hSodd hSthree hSnear
  have hT:=degree_le_card_add_error G D r T hTodd hTthree hTnear
  have hc:=card_le_univ (S∪T)
  rw [card_union_of_disjoint hdis] at hc
  omega

end OverfullWork.NearTightOddSetGeometry
