module

public import OverfullWork.SingletonLowSpanningLayer
public import OverfullWork.SmallLowSpanningLayerUniform
public import OverfullWork.SingletonLowSpanningLayerUniform

@[expose] public section


/-! # Actual small-low-set layers with a sparse missing-degree budget

The finite constructions keep the realised core path and its exact
endpoint degrees. They strengthen the existing certificates with a
bound on the actual sum of missing layer degrees. No layer or spanning
path is assumed, and all previous sources remain unchanged.
-/
namespace OverfullWork.SparseSmallLowLayer
open SimpleGraph Finset SparseDeficitCore LowVertexMatchingAbsorption
open LowSkeletonProjection PathGraphRealization SmallLowSpanningLayer
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 8000000

/-- A two-cover away from U, except at two path endpoints, loses at most
two units in the core and at most two per exceptional vertex. -/
theorem missing_le_twice_card_add_two (L : SimpleGraph V) [DecidableRel L.Adj]
    (U : Finset V) (a b : V)
    (hcore : ∀v∉U,(if v=a ∨ v=b then 1 else 2)≤L.degree v) :
    (∑v : V,(2-L.degree v))≤2*U.card+2 := by
  classical
  have hinside : (∑v∈U,(2-L.degree v))≤2*U.card := by
    calc
      _ ≤ ∑_v∈U,2 := sum_le_sum (fun v _=>Nat.sub_le 2 (L.degree v))
      _ = _ := by simp [Nat.mul_comm]
  have hpoint : ∀v∈Uᶜ,2-L.degree v≤(if v=a ∨ v=b then 1 else 0) := by
    intro v hv
    have hh:=hcore v (mem_compl.mp hv)
    split_ifs at hh ⊢ <;> omega
  have houtside : (∑v∈Uᶜ,(2-L.degree v))≤2 := by
    calc
      _ ≤ ∑v∈Uᶜ,if v=a ∨ v=b then 1 else 0 := sum_le_sum hpoint
      _ = (Uᶜ.filter (fun v=>v=a ∨ v=b)).card := by rw [card_filter]
      _ ≤ ({a,b}:Finset V).card := card_le_card (by
        intro v hv
        simpa only [mem_insert,mem_singleton] using (mem_filter.mp hv).2)
      _ ≤ 2 := by
        have hh:=card_insert_le a ({b}:Finset V)
        simpa only [card_singleton] using hh
  have hsplit:=sum_add_sum_compl U (fun v=>2-L.degree v)
  omega

private theorem degree_union (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]
    (hd : Disjoint A B) (v : V) : (A⊔B).degree v=A.degree v+B.degree v := by
  rw [←card_neighborFinset_eq_degree,neighborFinset_sup,
    card_union_of_disjoint (disjoint_neighborFinset_of_disjoint A B v hd),
    card_neighborFinset_eq_degree,card_neighborFinset_eq_degree]

private theorem fixed_endpoint_matching_degree_zero {G : SimpleGraph V} {A U Z : Finset V}
    (P : Projection G A U Z) (v : V) (hvU : v∉U) (hvA : v∈A) : P.matching.degree v=0 := by
  by_contra hn
  obtain ⟨z,hz⟩:=(P.matching.degree_pos_iff_exists_adj v).mp (Nat.pos_of_ne_zero hn)
  rcases P.endpoints v z hz with h|h
  · exact hvU (mem_inter.mp h.1).2
  · exact h.2.2 (mem_union_left _ hvA)


theorem exists_zero_low_layer_sparse_finite (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) (hD : 2≤G.maxDegree)
    (U : Finset V) (hW : lowVertices G=∅)
    (hexception : ∀v∈U,G.degree v+2≤G.maxDegree)
    (P : OddLowSmallCases.ChargedPair G G.maxDegree U)
    (hsize : 5≤Fintype.card ↥((U:Set V)ᶜ))
    (hdense : Fintype.card ↥((U:Set V)ᶜ)+2≤2*(G.induce ((U:Set V)ᶜ)).minDegree) :
    ∃c : Certificate G,(∑v : V,(2-c.layer.degree v))≤2*U.card+2 := by
  classical
  let A : Finset V:={P.left,P.right}
  let N:=P.projection.matching
  let a : A:=⟨P.left,by simp [A]⟩
  let b : A:=⟨P.right,by simp [A]⟩
  let ra:=P.projection.representative a
  let rb:=P.projection.representative b
  have hr : ra≠rb := fun h=>P.distinct (congrArg Subtype.val (P.projection.injective h))
  obtain ⟨K,hKG,hKforest,hKcore,hKzero,hKdegree⟩:=exists_core_path_graph G U ra rb hr hsize hdense
  have hNcross : ∀x y,N.Adj x y → (x∈U ∧ y∉U) ∨ (y∈U ∧ x∉U) := by
    intro x y h
    rcases P.projection.endpoints x y h with h|h
    · exact Or.inl ⟨(mem_inter.mp h.1).2,h.2.1⟩
    · exact Or.inr ⟨(mem_inter.mp h.1).2,h.2.1⟩
  have hdis : Disjoint N K := by
    apply disjoint_iff_inf_le.mpr
    intro x y ⟨hn,hk⟩
    rcases hNcross x y hn with h|h
    · exact (hKcore x y hk).1 h.1
    · exact (hKcore x y hk).2 h.1
  let L:=N⊔K
  have hsum : ∀v,L.degree v=N.degree v+K.degree v := degree_union N K hdis
  have hforest : L.IsAcyclic := by
    have hh:=LowSkeletonLayerGluing.acyclic_of_matching_attachments (⊥:SimpleGraph V) N K ∅ U
      (empty_subset _) (by intro x y z h;cases h) P.projection.isMatching
      (by intro x y h;cases h) hNcross (by simp) hKcore hKforest
    simpa only [bot_sup_eq,L] using hh
  have hdeg : ∀v,L.degree v≤2 := by
    intro v
    rw [hsum]
    have hn:=PaperLowSkeleton.matching_degree_le_one N P.projection.isMatching v
    by_cases hv:v∈U
    · rw [hKzero v hv];omega
    · rw [hKdegree v hv,projection_core_degree P.projection v hv]
      split_ifs with he hrend
      · omega
      · obtain ⟨z,_,hz⟩:=he
        have hzpair : z.val=P.left ∨ z.val=P.right := by simpa only [mem_insert,mem_singleton] using z.property
        exfalso
        apply hrend
        rcases hzpair with h|h
        · have heq:z=a:=Subtype.ext h
          exact Or.inl (hz ▸ congrArg Subtype.val (congrArg P.projection.representative heq))
        · have heq:z=b:=Subtype.ext h
          exact Or.inr (hz ▸ congrArg Subtype.val (congrArg P.projection.representative heq))
      · omega
      · omega
  have hdemand : ∀v,G.degree v+2≤G.maxDegree+L.degree v := by
    intro v
    by_cases hv:v∈U
    · exact (hexception v hv).trans (Nat.le_add_right _ _)
    rw [hsum,hKdegree v hv]
    by_cases hvend : v=ra.val ∨ v=rb.val
    · rw [if_pos hvend]
      by_cases hn : N.degree v=0
      · rw [hn]
        have hvcharge : G.degree v+1≤G.maxDegree := by
          rcases hvend with he|he
          · have hpl : P.left∉U := by
              intro hh
              have hp:=P.projection.selected a hh
              have hpos : 0<N.degree v:=(N.degree_pos_iff_exists_adj v).mpr
                ⟨P.left,he ▸ hp.symm⟩
              omega
            have hrfix:=P.projection.fixed a hpl
            have hvp : v=P.left:=he.trans hrfix
            rw [hvp];exact P.left_charge
          · have hpr : P.right∉U := by
              intro hh
              have hp:=P.projection.selected b hh
              have hpos : 0<N.degree v:=(N.degree_pos_iff_exists_adj v).mpr
                ⟨P.right,he ▸ hp.symm⟩
              omega
            have hrfix:=P.projection.fixed b hpr
            have hvp : v=P.right:=he.trans hrfix
            rw [hvp];exact P.right_charge
        omega
      · have hh:=G.degree_le_maxDegree v;omega
    · rw [if_neg hvend]
      have hh:=G.degree_le_maxDegree v;omega
  have hLG : L≤G:=sup_le P.projection.matching_le hKG
  have hcol : L.EdgeColorable 2:=TwoColourTrimming.two_colourable_of_acyclic_and_degree_le_two L hforest hdeg
  have hdefect : (∑v : V,(2-L.degree v))≤2*U.card+2 := by
    apply missing_le_twice_card_add_two L U ra.val rb.val
    intro v hv
    rw [hsum,hKdegree v hv]
    omega
  let c : Certificate G :=
    { layer:=L
      le_original:=hLG
      acyclic:=hforest
      degree_le_two:=by convert hdeg using 1;congr! 8
      colourable:=hcol
      demands:=by convert hdemand using 1;congr! 8
      low_one_cover:=by
        intro w hw
        rw [hW] at hw
        exact False.elim (notMem_empty _ hw)
      residual_maxDegree:=by
        convert TwoColourTrimming.maxDegree_sdiff_of_degree_demands G L hD hLG hdeg hdemand using 1
        congr! 8
      residual_uncolourable:=by
        convert TwoColourTrimming.critical_residue_of_degree_demands G L hc hD hLG hcol hdeg hdemand using 1
        congr! 8 }
  refine ⟨c,?_⟩
  convert hdefect using 1
  congr! 8

theorem exists_singleton_low_layer_sparse_finite (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Overfull.IsDeltaCritical G) (hD : 2≤G.maxDegree)
    (U : Finset V) (w a x : V) (hW : lowVertices G={w}) (hwU : w∈U)
    (hwa : G.Adj w a) (hax : a≠x) (hxw : x≠w) (hxD : G.degree x+1≤G.maxDegree)
    (hexception : ∀v∈U,G.degree v+2≤G.maxDegree)
    (P : Projection G {a,x} U {w,a})
    (hsize : 5≤Fintype.card ↥((U:Set V)ᶜ))
    (hdense : Fintype.card ↥((U:Set V)ᶜ)+2≤2*(G.induce ((U:Set V)ᶜ)).minDegree) :
    ∃c : Certificate G,(∑v : V,(2-c.layer.degree v))≤2*U.card+2 := by
  classical
  let A : Finset V:={a,x}
  let H:=edge w a
  let N:=P.matching
  let aa : A:=⟨a,by simp [A]⟩
  let xx : A:=⟨x,by simp [A]⟩
  let ra:=P.representative aa
  let rx:=P.representative xx
  have haw : a≠w:=Ne.symm (G.ne_of_adj hwa)
  have hr : ra≠rx:=fun he=>hax (congrArg Subtype.val (P.injective he))
  obtain ⟨K,hKG,hKforest,hKcore,hKzero,hKdegree⟩:=exists_core_path_graph G U ra rx hr hsize hdense
  have hmH : OneFactor.IsMatchingGraph H := by
    intro u v z huv huz
    simp only [H,edge_adj] at huv huz
    rcases huv.1 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
      rcases huz.1 with ⟨h1,h2⟩|⟨h1,h2⟩ <;> grind
  have hHdeg : ∀v,H.degree v=if v=w ∨ v=a then 1 else 0 := by
    intro v
    have hle:=PaperLowSkeleton.matching_degree_le_one H hmH v
    split_ifs with hv
    · have hpos : 0<H.degree v := by
        apply (H.degree_pos_iff_exists_adj v).mpr
        rcases hv with hvw|hva
        · refine ⟨a,?_⟩
          rw [hvw]
          exact (edge_adj w a w a).mpr ⟨Or.inl ⟨rfl,rfl⟩,Ne.symm haw⟩
        · refine ⟨w,?_⟩
          rw [hva]
          exact (edge_adj w a a w).mpr ⟨Or.inr ⟨rfl,rfl⟩,haw⟩
      omega
    · by_contra hh
      obtain ⟨z,hz⟩:=(H.degree_pos_iff_exists_adj v).mp (Nat.pos_of_ne_zero hh)
      exact hv (by rcases (edge_adj w a v z).mp hz |>.1 with h|h;exact Or.inl h.1;exact Or.inr h.1)
  have hNcross : ∀u v,N.Adj u v → (u∈U ∧ v∉U) ∨ (v∈U ∧ u∉U) := by
    intro u v h
    rcases P.endpoints u v h with h|h
    · exact Or.inl ⟨(mem_inter.mp h.1).2,h.2.1⟩
    · exact Or.inr ⟨(mem_inter.mp h.1).2,h.2.1⟩
  have hNw : ∀v,¬N.Adj w v := by
    intro v h
    rcases P.endpoints w v h with h|h
    · have hwA : w=a ∨ w=x := by simpa only [mem_insert,mem_singleton] using (mem_inter.mp h.1).1
      exact hwA.elim (fun he=>haw he.symm) (fun he=>hxw he.symm)
    · exact h.2.1 hwU
  have hHcross : ∀u v,H.Adj u v → (u∈({w}:Finset V) ∧ v∉({w}:Finset V)) ∨ (v∈({w}:Finset V) ∧ u∉({w}:Finset V)) := by
    intro u v h
    rcases (edge_adj w a u v).mp h |>.1 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [haw]
  have hHN : Disjoint H N := by
    apply disjoint_iff_inf_le.mpr
    intro u v ⟨hH,hN⟩
    rcases hHcross u v hH with h|h
    · have hu:u=w:=mem_singleton.mp h.1;subst u;exact hNw v hN
    · have hv:v=w:=mem_singleton.mp h.1;subst v;exact hNw u hN.symm
  let Q:=H⊔N
  have hQsum : ∀v,Q.degree v=H.degree v+N.degree v := degree_union H N hHN
  have hQcross : ∀u v,Q.Adj u v → (u∈U ∧ v∉U) ∨ (v∈U ∧ u∉U) ∨ (u∈U ∧ v∈U) := by
    intro u v h
    rcases h with h|h
    · rcases hHcross u v h with h|h
      · have hu:u=w:=mem_singleton.mp h.1
        by_cases hv:v∈U
        · exact Or.inr (Or.inr ⟨hu ▸ hwU,hv⟩)
        · exact Or.inl ⟨hu ▸ hwU,hv⟩
      · have hv:v=w:=mem_singleton.mp h.1
        by_cases hu:u∈U
        · exact Or.inr (Or.inr ⟨hu,hv ▸ hwU⟩)
        · exact Or.inr (Or.inl ⟨hv ▸ hwU,hu⟩)
    · exact (hNcross u v h).elim Or.inl (Or.inr ∘ Or.inl)
  have hQK : Disjoint Q K := by
    apply disjoint_iff_inf_le.mpr
    intro u v ⟨hq,hk⟩
    obtain ⟨hu,hv⟩:=hKcore u v hk
    rcases hQcross u v hq with h|h|h
    · exact hu h.1
    · exact hv h.1
    · exact hu h.1
  let L:=Q⊔K
  have hsum : ∀v,L.degree v=Q.degree v+K.degree v := degree_union Q K hQK
  have hforest : L.IsAcyclic :=
    LowSkeletonLayerGluing.acyclic_of_matching_attachments H N K {w} U
      (singleton_subset_iff.mpr hwU) hmH P.isMatching hHcross hNcross
      (by intro u hu v;have he:u=w:=mem_singleton.mp hu;subst u;exact hNw v) hKcore hKforest
  have hQcore : ∀v∉U,Q.degree v≤1 := by
    intro v hv
    rw [hQsum,hHdeg]
    have hn:=PaperLowSkeleton.matching_degree_le_one N P.isMatching v
    by_cases hva:v=a
    · subst v
      rw [fixed_endpoint_matching_degree_zero P a hv (by simp),if_pos (Or.inr rfl)]
    · have hvw:v≠w:=fun he=>hv (he ▸ hwU)
      rw [if_neg (by tauto)];omega
  have hQpositive_endpoint : ∀v∉U,0<Q.degree v → v=ra.val ∨ v=rx.val := by
    intro v hv hp
    rw [hQsum,hHdeg] at hp
    by_cases hva:v=a
    · have haout : a∉U := by intro hh;apply hv;rw [hva];exact hh
      have hfix:=P.fixed aa haout
      exact Or.inl (hva.trans hfix.symm)
    · have hvw:v≠w:=fun he=>hv (he ▸ hwU)
      rw [if_neg (by tauto)] at hp
      have hn : 0<N.degree v := by omega
      have hformula:=projection_core_degree P v hv
      rw [hformula] at hn
      split_ifs at hn with he
      · obtain ⟨z,_,hz⟩:=he
        have hzpair:z.val=a ∨ z.val=x := by simpa only [mem_insert,mem_singleton] using z.property
        rcases hzpair with h|h
        · have heq:z=aa:=Subtype.ext h
          exact Or.inl (hz.symm.trans (congrArg Subtype.val (congrArg P.representative heq)))
        · have heq:z=xx:=Subtype.ext h
          exact Or.inr (hz.symm.trans (congrArg Subtype.val (congrArg P.representative heq)))
      · omega
  have hdeg : ∀v,L.degree v≤2 := by
    intro v
    rw [hsum]
    by_cases hv:v∈U
    · rw [hKzero v hv,hQsum]
      have hh:=PaperLowSkeleton.matching_degree_le_one H hmH v
      have hn:=PaperLowSkeleton.matching_degree_le_one N P.isMatching v
      omega
    · rw [hKdegree v hv]
      have hq:=hQcore v hv
      split_ifs with he
      · omega
      · have hn:¬0<Q.degree v:=fun hp=>he (hQpositive_endpoint v hv hp)
        omega
  have hleft : 0<Q.degree ra.val := by
    by_cases ha:a∈U
    · have hh:=P.selected aa ha
      have hpos:0<N.degree ra.val:=(N.degree_pos_iff_exists_adj _).mpr ⟨a,hh.symm⟩
      rw [hQsum];omega
    · have hfix:=P.fixed aa ha
      rw [hQsum,hHdeg,hfix]
      rw [if_pos (Or.inr rfl)]
      omega
  have hdemand : ∀v,G.degree v+2≤G.maxDegree+L.degree v := by
    intro v
    by_cases hv:v∈U
    · exact (hexception v hv).trans (Nat.le_add_right _ _)
    rw [hsum,hKdegree v hv]
    by_cases hvend:v=ra.val ∨ v=rx.val
    · rw [if_pos hvend]
      by_cases hq:0<Q.degree v
      · have hh:=G.degree_le_maxDegree v;omega
      · rcases hvend with he|he
        · have hh:=he ▸ hleft;omega
        · have hxout:x∉U := by
            intro hxU
            have hh:=P.selected xx hxU
            have hn:0<N.degree v:=(N.degree_pos_iff_exists_adj _).mpr ⟨x,he ▸ hh.symm⟩
            have hs:=hQsum v;omega
          have hfix:=P.fixed xx hxout
          have hvx:v=x:=he.trans hfix
          have hh : G.degree v+1≤G.maxDegree := by rw [hvx];exact hxD
          omega
    · rw [if_neg hvend]
      have hh:=G.degree_le_maxDegree v;omega
  have hLG : L≤G:=sup_le (sup_le ((edge_le_iff G).mpr (Or.inr hwa)) P.matching_le) hKG
  have hcol : L.EdgeColorable 2:=TwoColourTrimming.two_colourable_of_acyclic_and_degree_le_two L hforest hdeg
  have hlow : ∀u∈lowVertices G,L.degree u=1 := by
    intro u hu
    have he:u=w:=by simpa only [hW,mem_singleton] using hu
    subst u
    have hn:N.degree w=0 := by
      by_contra hh
      obtain ⟨z,hz⟩:=(N.degree_pos_iff_exists_adj w).mp (Nat.pos_of_ne_zero hh)
      exact hNw z hz
    rw [hsum,hKzero w hwU,hQsum,hHdeg,hn,if_pos (Or.inl rfl)]
  have hdefect : (∑v : V,(2-L.degree v))≤2*U.card+2 := by
    apply missing_le_twice_card_add_two L U ra.val rx.val
    intro v hv
    rw [hsum,hKdegree v hv]
    omega
  let c : Certificate G :=
    { layer:=L
      le_original:=hLG
      acyclic:=hforest
      degree_le_two:=by convert hdeg using 1;congr! 8
      colourable:=hcol
      demands:=by convert hdemand using 1;congr! 8
      low_one_cover:=by convert hlow using 1;congr! 8
      residual_maxDegree:=by
        convert TwoColourTrimming.maxDegree_sdiff_of_degree_demands G L hD hLG hdeg hdemand using 1
        congr! 8
      residual_uncolourable:=by
        convert TwoColourTrimming.critical_residue_of_degree_demands G L hc hD hLG hcol hdeg hdemand using 1
        congr! 8 }
  refine ⟨c,?_⟩
  convert hdefect using 1
  congr! 8

universe u

/-- G1 supplies the exceptional-set bound at any fixed integer scale.
The scale and its order threshold are selected before the graph. -/
theorem exception_count_at_fixed_scale (q : ℕ) (hq : 2≤q) :
    ∃N : ℕ,∀{V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      N≤Fintype.card V → Overfull.IsDeltaCritical G →
      Fintype.card V≤2*G.maxDegree →
      (exceptions G G.maxDegree (Fintype.card V/(8*q))).card≤
        Fintype.card V/(4096*q^2) := by
  let η : ℝ:=1/(262144*(q:ℝ)^3)
  have hη : 0<η := by dsimp [η];positivity
  obtain ⟨D₀,hD⟩:=CaoChenCriticalAverage.deficit_bound.{u} η hη
  refine ⟨max (4096*q^2) (2*D₀),?_⟩
  intro V _ _ G _ hn hc hnD
  have hnscale : 4096*q^2≤Fintype.card V := (le_max_left _ _).trans hn
  have hD₀ : D₀≤G.maxDegree := by
    have hh:=(le_max_right (4096*q^2) (2*D₀)).trans hn
    omega
  have hmass:=hD G hc hD₀
  have hDelta : (G.maxDegree:ℝ)≤(Fintype.card V:ℝ) := by
    exact_mod_cast G.maxDegree_le_of_forall_degree_le
      (Fintype.card V) (fun v=>(G.degree_lt_card_verts v).le)
  have hmass' : (totalDeficit G G.maxDegree:ℝ)≤η*(Fintype.card V:ℝ)^2 := by
    have hh:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hDelta hη.le)
      (Nat.cast_nonneg (Fintype.card V) : (0:ℝ)≤(Fintype.card V:ℝ))
    nlinarith only [hmass,hh]
  have hmassInt:=RobustExpansion.integer_mass_budget_of_quadratic_bound
    (Fintype.card V) q (totalDeficit G G.maxDegree) (by omega) hmass'
  exact RobustExpansion.exception_count_le_of_mass_lt G G.maxDegree
    (Fintype.card V/(8*q)) (Fintype.card V/(4096*q^2)) hmassInt

/-- Empty and singleton low sets both admit an actual layer with a
small total missing-degree budget. q and the order threshold are fixed
before the graph, its low-set case, and all endpoint choices. -/
theorem above_half_small_low_layer_sparse (ε : ℝ) (hε : 0<ε) :
    ∃q : ℕ,2≤q ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N≤Fintype.card V → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        ¬G.HasOverfullSubgraph → (lowVertices G).card≤1 →
        ∃c : Certificate G,
          (∑v : V,(2-c.layer.degree v))≤
            2*(exceptions G G.maxDegree (Fintype.card V/(8*q))).card+2 ∧
          (∑v : V,(2-c.layer.degree v))≤2*(Fintype.card V/(4096*q^2))+2 := by
  obtain ⟨q,hq,N₀,hmargins⟩:=SmallLowSpanningLayerUniform.above_half_small_low_margins.{u} ε hε
  obtain ⟨N₁,hdef⟩:=CriticalDeficientVertices.above_half_critical_two_deficient.{u} ε hε
  obtain ⟨NM,hmassScale⟩:=exception_count_at_fixed_scale.{u} q hq
  refine ⟨q,hq,max (max N₀ N₁) NM,?_⟩
  intro V _ _ G _ hn hc hdense hno hsmall
  classical
  have hnbase : max N₀ N₁≤Fintype.card V := (le_max_left _ _).trans hn
  have hn₀ : N₀≤Fintype.card V := (le_max_left N₀ N₁).trans hnbase
  have hn₁ : N₁≤Fintype.card V := (le_max_right N₀ N₁).trans hnbase
  have hnM : NM≤Fintype.card V := (le_max_right _ _).trans hn
  obtain ⟨hD,hexception,hbudget,hsize,hcore⟩:=hmargins G hn₀ hc hdense
  let a₀:=Fintype.card V/(8*q)
  let U:=exceptions G G.maxDegree a₀
  have hbudgetU : 3*(U.card+4)≤G.maxDegree := by convert hbudget using 1
  have hnD : Fintype.card V≤2*G.maxDegree := by
    have he : 0≤ε*(Fintype.card V:ℝ) := by positivity
    exact_mod_cast (show (Fintype.card V:ℝ)≤2*(G.maxDegree:ℝ) by
      nlinarith only [hdense,he])
  have hUk : U.card≤Fintype.card V/(4096*q^2) := by
    convert hmassScale G hnM hc hnD using 1
  suffices hexc : ∃c : Certificate G,(∑v : V,(2-c.layer.degree v))≤2*U.card+2 by
    obtain ⟨c,hcMissing⟩:=hexc
    refine ⟨c,?_,?_⟩
    · convert hcMissing using 1
    · exact hcMissing.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hUk) 2)
  have haf : 8*q*a₀≤Fintype.card V := Nat.mul_div_le (Fintype.card V) (8*q)
  have h16 : 16*a₀≤Fintype.card V :=
    (Nat.mul_le_mul_right a₀ (by omega : 16≤8*q)).trans haf
  have haD : 8*a₀≤G.maxDegree := by omega
  by_cases hzero : lowVertices G=∅
  · have hdeficient:=hdef G hn₁ hc hdense hno
    obtain ⟨P⟩:=OddLowSmallCases.exists_charged_pair_of_lowVertices_eq_empty
      G U hzero hdeficient (by omega)
    exact exists_zero_low_layer_sparse_finite G hc hD U hzero hexception P hsize hcore
  have hcard : (lowVertices G).card=1 := by
    have hp : 0<(lowVertices G).card:=card_pos.mpr (nonempty_iff_ne_empty.mpr hzero)
    omega
  obtain ⟨w,hW⟩:=card_eq_one.mp hcard
  have hwW : w∈lowVertices G := by rw [hW];simp
  have hwU : w∈U :=
    CriticalLowPartnerProjection.lowVertices_subset_exceptions G a₀ (by omega) haD hwW
  have hdeficient:=hdef G hn₁ hc hdense hno
  obtain ⟨x,hx,y,hy,hxy⟩:=one_lt_card.mp
    (show 1<(univ.filter fun v=>G.degree v<G.maxDegree).card by omega)
  have hspare : ∃x,x≠w ∧ G.degree x+1≤G.maxDegree := by
    by_cases hxw : x=w
    · refine ⟨y,fun he=>hxy (hxw.trans he.symm),?_⟩
      have hh:=(mem_filter.mp hy).2
      omega
    · refine ⟨x,hxw,?_⟩
      have hh:=(mem_filter.mp hx).2
      omega
  obtain ⟨x,hxw,hxD⟩:=hspare
  have hwdeg:=OddLowSmallCases.critical_two_le_degree G hc w
  obtain ⟨a,hax,hwa⟩:=OddLowSmallCases.exists_singleton_edge_avoiding G w x hwdeg
  obtain ⟨P⟩ : Nonempty (LowSkeletonProjection.Projection G {a,x} U {w,a}) := by
    apply LowSkeletonProjection.exists_projection
    intro z hz
    have hzpair : z=a ∨ z=x := by
      simpa only [mem_insert,mem_singleton] using (mem_inter.mp hz).1
    have haw : a≠w := Ne.symm (G.ne_of_adj hwa)
    have hzw : z≠w := by
      rcases hzpair with rfl|rfl
      · exact haw
      · exact hxw
    have hznot : z∉lowVertices G := by rw [hW];simpa using hzw
    have hhigh : G.maxDegree<3*G.degree z := by
      simpa only [lowVertices,mem_filter,mem_univ,true_and,not_le] using hznot
    have hZ : ({w,a}:Finset V).card≤2 := by
      have hh:=card_insert_le w ({a}:Finset V)
      simpa only [card_singleton] using hh
    rw [card_pair hax]
    omega
  exact exists_singleton_low_layer_sparse_finite
    G hc hD U w a x hW hwU hwa hax hxw hxD hexception P hsize hcore


end OverfullWork.SparseSmallLowLayer
