module

public import OverfullWork.CompensatedReduction

@[expose] public section


/-! # Completing the exceptional centre before the ordinary phase

The prefix tracks exactly which initially missing centre colours have
been processed; untouched colours retain the internal seed unchanged.
The construction below leaves an explicit weighted missing-set condition.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace PartialColouring
variable {M : MultiGraph V} {k : ℕ}
set_option maxHeartbeats 4000000

theorem exists_safe_five_of_eligible_start (P : M.PartialColouring k) (S Z : Finset V)
    (i : Fin k) (u v : V) (m d bA : ℕ)
    (hS : S.card=m) (hu : u∈S) (hv : v∈Sᶜ)
    (hmissU : (P.colouring.colourGraph i).degree u=0)
    (hmissV : (P.colouring.colourGraph i).degree v=0)
    (hbadA : (S\(P.colouring.colourGraph i).eligibleVertices
      (P.colouring.colourGraph_degree_le_one i) S Z).card≤bA)
    (hfirst : (((P.colouring.colourGraph i).eligibleVertices
      (P.colouring.colourGraph_degree_le_one i) Sᶜ Z).filter
      fun w => 0<P.available.mult s(u,w)).Nonempty)
    (hNv : d≤(P.available.neighboursInto S v).card)
    (hNold : ∀ z∈Sᶜ,z∉Z → d≤(P.available.neighboursInto S z).card)
    (hroom : m+2*bA<2*d) : Nonempty (P.SafeFive S Z i u v) := by
  classical
  let C:=P.colouring.colourGraph i
  let hc:=P.colouring.colourGraph_degree_le_one i
  let EA:=C.eligibleVertices hc S Z
  let EB:=C.eligibleVertices hc Sᶜ Z
  let τ:=C.matchingPartner hc
  let N : V → V → Prop:=fun a b => 0<P.available.mult s(a,b)
  have hEA : EA⊆S:=C.eligibleVertices_subset hc S Z
  have hEB : EB⊆Sᶜ:=C.eligibleVertices_subset hc Sᶜ Z
  change (S\EA).card≤bA at hbadA
  have hlarge : ∀ z∈EB,EA.card<(EA.filter (N v)).card+(EA.filter (N z)).card := by
    intro z hz
    have hZ : z∉Z:=(mem_filter.mp hz).2.2.2.1
    have hn:=hNold z (hEB hz) hZ
    have h₁:=OverfullWork.ShortAugmentSearch.neighbours_lost S EA hEA (N v)
    have h₂:=OverfullWork.ShortAugmentSearch.neighbours_lost S EA hEA (N z)
    have hE:=card_le_card hEA
    change (S.filter (N z)).card≥d at hn
    change (S.filter (N v)).card≥d at hNv
    omega
  have huE : u∉EA := by
    intro h
    have h1:=(mem_filter.mp h).2.1
    change (P.colouring.colourGraph i).degree u=1 at h1
    omega
  have hvE : v∉EB := by
    intro h
    have h1:=(mem_filter.mp h).2.1
    change (P.colouring.colourGraph i).degree v=1 at h1
    omega
  obtain ⟨p,hp0,hp5,hp1,hp2,hp3,hp4,h01,h23,h54⟩ :=
    OverfullWork.ShortAugmentSearch.exists_five_pattern S Sᶜ EA EB u v τ
      (C.matchingPartner_apply_apply hc) disjoint_compl_right hEA hEB hu hv huE hvE
      (C.eligibleVertices_closed hc S Z) (C.eligibleVertices_closed hc Sᶜ Z)
      (C.eligibleVertices_ne hc S Z) (C.eligibleVertices_ne hc Sᶜ Z) N hfirst hlarge
  have hp2mem : p 2∈EB := by rw [hp2]; exact C.eligibleVertices_closed hc Sᶜ Z (p 1) hp1
  have hp4mem : p 4∈EA := by rw [hp4]; exact C.eligibleVertices_closed hc S Z (p 3) hp3
  have h12 : 1≤C.mult s(p 1,p 2) := by
    rw [hp2]
    exact (C.matchingPartner_adj hc (p 1) (mem_filter.mp hp1).2.1).ge
  have h34 : 1≤C.mult s(p 3,p 4) := by
    rw [hp4]
    exact (C.matchingPartner_adj hc (p 3) (mem_filter.mp hp3).2.1).ge
  refine ⟨{path:=p,first:=hp0,last:=hp5,sided:=?_,safe:=?_,remove_le:=?_,add_le:=?_}⟩
  · exact ⟨hp0 ▸ hu,mem_compl.mp (hEB hp1),mem_compl.mp (hEB hp2mem),hEA hp3,hEA hp4mem,
      hp5 ▸ mem_compl.mp hv⟩
  · intro z hz
    rw [degree_fiveRemoved] at hz
    have he : z=p 1 ∨ z=p 2 ∨ z=p 3 ∨ z=p 4 := by split_ifs at hz <;> simp_all
    rcases he with rfl|rfl|rfl|rfl
    · exact (mem_filter.mp hp1).2.2.2.1
    · exact (mem_filter.mp hp2mem).2.2.2.1
    · exact (mem_filter.mp hp3).2.2.2.1
    · exact (mem_filter.mp hp4mem).2.2.2.1
  · exact fiveRemoved_le_of_edges C p h12 h34
  · exact fiveAdded_le_of_edges P.available p h01 h23 (by
      change 0<P.available.mult s(p 5,p 4) at h54
      have h : 0<P.available.mult s(p 4,p 5) := by simpa only [Sym2.eq_swap] using h54
      omega)

/-- Weighted loss on the ineligible set, rather than its cardinality. -/
theorem eligible_start_of_weighted_bad_room (P : M.PartialColouring k) (S E : Finset V)
    (u : V) (hE : E⊆S)
    (hroom : (∑ w∈S\E,P.available.mult s(u,w))<P.available.degreeInto S u) :
    (E.filter fun w => 0<P.available.mult s(u,w)).Nonempty := by
  by_contra hn
  have hzero : ∑ w∈E,P.available.mult s(u,w)=0 := by
    apply sum_eq_zero
    intro w hw
    by_contra hz
    have hp : 0<P.available.mult s(u,w):=by omega
    exact hn ⟨w,mem_filter.mpr ⟨hw,hp⟩⟩
  have hsplit:=sum_sdiff (f:=fun w => P.available.mult s(u,w)) hE
  rw [hzero,Nat.add_zero] at hsplit
  change (∑ w∈S\E,P.available.mult s(u,w))<(∑ w∈S,P.available.mult s(u,w)) at hroom
  omega

/-- Local crossing degree with no loss from the centre's internal residue. -/
theorem centre_crossing_budget (P : M.PartialColouring k) (S : Finset V) (x : V) (D : ℕ)
    (hx : x∈S) (hreg : M.IsRegularOfDegree D) (hcentre : (P.remainder S).degree x=0) :
    D≤k+P.available.degreeInto Sᶜ x := by
  have hd:=P.available_degree x
  rw [hreg x] at hd
  have hc:=P.colouring.degree_le_palette x
  have hsum:=P.available.degreeInto_add_compl S x
  change (P.available.internalPart S).degree x=0 at hcentre
  rw [degree_internalPart,if_pos hx] at hcentre
  omega

/-- On the opposite side, an untouched internal colour has exactly its
missing vertices ineligible when the only forbidden point is x. -/
theorem ineligible_complement_eq_missing (P : M.PartialColouring k) (S : Finset V)
    (x : V) (i : Fin k) (hx : x∈S) (hcut : (P.colouring.colourGraph i).cutSize S=0) :
    Sᶜ\(P.colouring.colourGraph i).eligibleVertices
      (P.colouring.colourGraph_degree_le_one i) Sᶜ {x}=P.colouring.missingSet Sᶜ i := by
  let Q:=P.colouring.colourGraph i
  let hd:=P.colouring.colourGraph_degree_le_one i
  have hpartner : ∀ v∈Sᶜ,Q.degree v=1 → Q.matchingPartner hd v∈Sᶜ := by
    intro v hv hdeg
    by_contra hn
    have hpS : Q.matchingPartner hd v∈S:=by simpa using hn
    have hz:=Q.cut_mult_eq_zero S hcut (Q.matchingPartner hd v) hpS v hv
    have hpos:=Q.matchingPartner_adj hd v hdeg
    rw [Sym2.eq_swap] at hz
    omega
  ext v
  constructor
  · intro hv
    obtain ⟨hvS,hnot⟩:=mem_sdiff.mp hv
    apply mem_filter.mpr
    refine ⟨hvS,?_⟩
    have hle:=hd v
    change Q.degree v≤1 at hle
    change Q.degree v=0
    by_contra hn
    have hdeg : Q.degree v=1:=by omega
    have hpS:=hpartner v hvS hdeg
    have hvx : v∉({x}:Finset V) := by
      simp only [mem_singleton]
      intro he
      exact (mem_compl.mp hvS) (he ▸ hx)
    have hpx : Q.matchingPartner hd v∉({x}:Finset V) := by
      simp only [mem_singleton]
      intro he
      exact (mem_compl.mp hpS) (he ▸ hx)
    exact hnot (mem_filter.mpr ⟨hvS,hdeg,hpS,hvx,hpx⟩)
  · intro hv
    obtain ⟨hvS,hzero⟩:=mem_filter.mp hv
    apply mem_sdiff.mpr
    refine ⟨hvS,?_⟩
    intro he
    have hdeg:=(mem_filter.mp he).2.1
    omega

structure CentreFirstPrefix (P₀ P : M.PartialColouring k) (S : Finset V)
    (x : V) (T : Finset (Fin k)) : Prop where
  processed : ∀ i∈T,(P.colouring.colourGraph i).degree x=1
  frozen : ∀ i,i∉T → P.colouring.colourGraph i=P₀.colouring.colourGraph i
  seed_missing : ∀ i∈T,(P₀.colouring.colourGraph i).degree x=0
  remainder_degree : ∀ v,(P.remainder S).degree v≤T.card

/-- The prefix begins with zero internal residue and no processed colour. -/
theorem internalSeed_centre_prefix (S : Finset V) (x : V)
    (C : (M.internalPart S).EdgeColoring k) :
    CentreFirstPrefix (internalSeed S C) (internalSeed S C) S x ∅ := by
  refine ⟨by simp,fun _ _ => rfl,by simp,?_⟩
  intro v
  simp only [degree,internalSeed_remainder_zero,sum_const_zero,card_empty]
  omega

theorem centre_prefix_card_le (P₀ P : M.PartialColouring k) (S : Finset V) (x : V)
    (T : Finset (Fin k)) (h : CentreFirstPrefix P₀ P S x T) :
    T.card≤(P₀.colouring.missingPalette x).card := by
  apply card_le_card
  intro i hi
  exact mem_filter.mpr ⟨mem_univ i,h.seed_missing i hi⟩

/-- During the short prefix the high-remainder forbidden set is empty. -/
theorem centre_prefix_forbidden (P₀ P : M.PartialColouring k) (S : Finset V) (x : V)
    (T : Finset (Fin k)) (t c : ℕ) (h : CentreFirstPrefix P₀ P S x T)
    (hdef : (P₀.colouring.missingPalette x).card≤t) (ht : 0<t) (hc : 2≤c) :
    P.scaledForbidden S x t c={x} := by
  have hcard:=centre_prefix_card_le P₀ P S x T h
  have hct:=Nat.mul_le_mul_right t hc
  ext v
  have hr:=h.remainder_degree v
  simp only [scaledForbidden,mem_union,mem_filter,mem_univ,true_and,mem_singleton]
  change (c*t≤(P.remainder S).degree v ∨ v=x) ↔ v=x
  constructor
  · rintro (hh|he)
    · exfalso;omega
    · exact he
  · intro he
    exact Or.inr he

/-- One centre augmentation keeps every other unprocessed seed colour
frozen and increases the residue degree by at most one. -/
theorem centre_prefix_step (P₀ P : M.PartialColouring k) (S Z : Finset V) (x v : V)
    (T : Finset (Fin k)) (i : Fin k) (h : CentreFirstPrefix P₀ P S x T)
    (hi : i∉T) (hseed : (P₀.colouring.colourGraph i).degree x=0)
    (hzero : (P.colouring.colourGraph i).degree x=0)
    (hvzero : (P.colouring.colourGraph i).degree v=0)
    (f : P.SafeFive S Z i x v) :
    CentreFirstPrefix P₀ (P.perturb S Z i x v f hzero hvzero) S x (insert i T) := by
  let Q:=P.perturb S Z i x v f hzero hvzero
  have hselected:=P.perturb_selected_degree S Z i x v f hzero hvzero x
  have hother:=P.perturb_other S Z i x v f hzero hvzero
  refine ⟨?_,?_,?_,?_⟩
  · intro j hj
    rcases mem_insert.mp hj with hji|hj
    · subst j
      change (Q.colouring.colourGraph i).degree x=1
      simpa only [hzero,eq_self_iff_true,true_or,ite_true,Nat.zero_add] using hselected
    · have hji : j≠i:=fun he => hi (he ▸ hj)
      rw [hother j hji]
      exact h.processed j hj
  · intro j hj
    simp only [mem_insert,not_or] at hj
    rw [hother j hj.1]
    exact h.frozen j hj.2
  · intro j hj
    rcases mem_insert.mp hj with rfl|hj
    · exact hseed
    · exact h.seed_missing j hj
  · intro z
    rw [P.perturb_remainder S Z i x v f hzero hvzero,degree_addCopies]
    have hr:=h.remainder_degree z
    have hremoved : (fiveRemoved f.path).degree z≤1 := by
      rw [degree_fiveRemoved]
      split_ifs <;> omega
    rw [card_insert_of_notMem hi]
    omega

/-- Processing exactly the initial missing palette fills every centre slot. -/
theorem centre_prefix_complete (P₀ P : M.PartialColouring k) (S : Finset V) (x : V)
    (h : CentreFirstPrefix P₀ P S x (P₀.colouring.missingPalette x)) :
    ∀ i,(P.colouring.colourGraph i).degree x=1 := by
  intro i
  by_cases hi : i∈P₀.colouring.missingPalette x
  · exact h.processed i hi
  · have hh:=h.frozen i hi
    have hseed : (P₀.colouring.colourGraph i).degree x≠0 := by
      intro hz
      exact hi (mem_filter.mpr ⟨mem_univ i,hz⟩)
    rw [hh]
    have hb:=P₀.colouring.colourGraph_degree_le_one i x
    omega

/-- Untouched colours need only their initial weighted missing-set bound.
The potentially large central multiplicity never multiplies the bad count. -/
theorem centre_prefix_weighted_start (S : Finset V) (x : V)
    (C : (M.internalPart S).EdgeColoring k) (P : M.PartialColouring k)
    (T : Finset (Fin k)) (i : Fin k) (m D t c B : ℕ)
    (h : CentreFirstPrefix (internalSeed S C) P S x T) (hi : i∉T)
    (hdef : (C.missingPalette x).card≤t) (ht : 0<t) (hc : 2≤c)
    (hx : x∈S) (hreg : M.IsRegularOfDegree D) (hcentre : (P.remainder S).degree x=0)
    (hweighted : (∑ z∈C.missingSet Sᶜ i,M.mult s(x,z))≤B) (hroom : k+B<D) :
    (((P.colouring.colourGraph i).eligibleVertices
      (P.colouring.colourGraph_degree_le_one i) Sᶜ (P.scaledForbidden S x t c)).filter
      fun z => 0<P.available.mult s(x,z)).Nonempty := by
  let E:=(P.colouring.colourGraph i).eligibleVertices
    (P.colouring.colourGraph_degree_le_one i) Sᶜ (P.scaledForbidden S x t c)
  have hE : E⊆Sᶜ:=filter_subset _ _
  have hforb:=centre_prefix_forbidden (internalSeed S C) P S x T t c h hdef ht hc
  have hfrozen : P.colouring.colourGraph i=C.colourGraph i:=h.frozen i hi
  have hcut : (P.colouring.colourGraph i).cutSize S=0 := by
    rw [hfrozen]
    exact C.internal_colour_cut_zero S i
  have hbad : Sᶜ\E=C.missingSet Sᶜ i := by
    dsimp only [E]
    rw [hforb,ineligible_complement_eq_missing P S x i hx hcut]
    unfold EdgeColoring.missingSet
    rw [hfrozen]
  have hweight : (∑ z∈Sᶜ\E,P.available.mult s(x,z))≤B := by
    rw [hbad]
    exact (sum_le_sum (fun z _ => (show P.available.mult s(x,z)≤M.mult s(x,z) from Nat.sub_le _ _))).trans hweighted
  have hcross:=P.centre_crossing_budget S x D hx hreg hcentre
  exact P.eligible_start_of_weighted_bad_room Sᶜ E x hE (by omega)

/-- Construct the complete centre-first prefix by processing each initially
missing colour once. The only new analytic hypothesis is the fixed seed's
weighted missing-set bound; the invariant is proved through every step. -/
theorem centre_first_precompletion (S : Finset V) (x : V)
    (C : (M.internalPart S).EdgeColoring k) (m D t c β d B : ℕ)
    (hS : S.card=m) (hSc : Sᶜ.card=m) (hx : x∈S) (ht : 0<t) (hc : 2≤c)
    (hreg : M.IsRegularOfDegree D) (hstar : M.HasParallelBudget x β)
    (hnum : AdditiveFirstBudget β c m D t k d)
    (hinit : (internalSeed S C).ScaledCompletionInvariant S x m t c)
    (hdef : (C.missingPalette x).card≤t)
    (hweighted : ∀ i,(C.colourGraph i).degree x=0 → (∑ z∈C.missingSet Sᶜ i,M.mult s(x,z))≤B)
    (hroom : k+B<D) :
    ∃ P : M.PartialColouring k,P.ScaledCompletionInvariant S x m t c ∧
      CentreFirstPrefix (internalSeed S C) P S x (C.missingPalette x) ∧
      ∀ i,(P.colouring.colourGraph i).degree x=1 := by
  let P₀:=internalSeed S C
  have hprocess : ∀ T : Finset (Fin k),T⊆C.missingPalette x →
      ∃ P : M.PartialColouring k,CentreFirstPrefix P₀ P S x T ∧
        P.ScaledCompletionInvariant S x m t c := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨P₀,internalSeed_centre_prefix S x C,hinit⟩
    | @insert i T hi ih =>
      intro hsub
      have hTsub : T⊆C.missingPalette x:=fun j hj => hsub (mem_insert_of_mem hj)
      obtain ⟨P,hpre,hInv⟩:=ih hTsub
      have hseed : (C.colourGraph i).degree x=0:=
        (mem_filter.mp (hsub (mem_insert_self i T))).2
      have hzero : (P.colouring.colourGraph i).degree x=0 := by
        rw [hpre.frozen i hi]
        exact hseed
      have hmiss : 0<(P.colouring.missingSet S i).card:=
        card_pos.mpr ⟨x,mem_filter.mpr ⟨hx,hzero⟩⟩
      have heq:=P.colouring.missing_balance_general S (hS.trans hSc.symm) hInv.balance i
      have hmissSc : 0<(P.colouring.missingSet Sᶜ i).card:=by omega
      obtain ⟨v,hv⟩:=card_pos.mp hmissSc
      obtain ⟨hvSc,hvzero⟩:=mem_filter.mp hv
      let Z:=P.scaledForbidden S x t c
      have hfirst:=centre_prefix_weighted_start S x C P T i m D t c B hpre hi hdef ht hc
        hx hreg hInv.centre (hweighted i hseed) hroom
      have hforb : Z={x}:=centre_prefix_forbidden P₀ P S x T t c hpre hdef ht hc
      have hbadA : (S\(P.colouring.colourGraph i).eligibleVertices
          (P.colouring.colourGraph_degree_le_one i) S Z).card≤OverfullWork.ScaledMargins.badBound c m t := by
        have hb:=(P.colouring.colourGraph i).ineligible_card_bound
          (P.colouring.colourGraph_degree_le_one i) S Z
        change _≤(P.colouring.missingSet S i).card+(P.colouring.colourGraph i).cutSize S+2*Z.card at hb
        have hZcard : Z.card=1:=by rw [hforb,card_singleton]
        rw [hZcard] at hb
        have hbudget:=hInv.colour_budget i
        unfold OverfullWork.ScaledMargins.badBound
        omega
      have havail : ∀ e,P.available.mult e≤M.mult e:=fun e => Nat.sub_le _ _
      have hOrd : ∀ z∈Sᶜ,d≤(P.available.neighboursInto S z).card := by
        intro z hzSc
        have hznot : z∉S:=mem_compl.mp hzSc
        have hzx : z≠x:=fun he => hznot (he ▸ hx)
        have hbudget:=P.crossing_degree_budget S D (c*t) hreg hInv.remainder_degree z
        rw [if_neg hznot] at hbudget
        have hcount:=P.available.degreeInto_le_neighbours_add_budget S z x β
          (M.parallelBudget_mono P.available x β havail hstar) hzx
        have hh:=hnum.ordinary
        omega
      obtain ⟨f⟩:=P.exists_safe_five_of_eligible_start S Z i x v m d
        (OverfullWork.ScaledMargins.badBound c m t) hS hx hvSc hzero hvzero hbadA hfirst
        (hOrd v hvSc) (fun z hz _ => hOrd z hz) hnum.overlap
      let Q:=P.perturb S Z i x v f hzero hvzero
      have hQ : Q.ScaledCompletionInvariant S x m t c:=
        P.scaled_perturb_preserves S x m t c hInv i x v f hzero hvzero
      have hpreQ : CentreFirstPrefix P₀ Q S x (insert i T):=
        centre_prefix_step P₀ P S Z x v T i hpre hi hseed hzero hvzero f
      exact ⟨Q,hpreQ,hQ⟩
  obtain ⟨P,hpre,hInv⟩:=hprocess (C.missingPalette x) subset_rfl
  exact ⟨P,hInv,hpre,centre_prefix_complete P₀ P S x hpre⟩

end PartialColouring
end SimpleGraph.MultiGraph
