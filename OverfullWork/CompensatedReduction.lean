module

public import OverfullWork.GeneralFreeColourMatching
public import OverfullWork.GeneralFirstPhase

@[expose] public section


/-! # Completion with a uniform excess budget and exact compensation accounting -/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace PartialColouring
variable {M : MultiGraph V} {k : ℕ}

/-- The first expansion margin loses the excess additively when there
is no exceptional high-excess point. -/
structure AdditiveFirstBudget (β c m D t k d : ℕ) : Prop where
  first : OverfullWork.ScaledMargins.badBound c m t+β+k+c*t<D
  ordinary : d+k+c*t+β≤D
  overlap : m+2*OverfullWork.ScaledMargins.badBound c m t<2*d

/-- The expensive factor β in the first-neighbour bound is absent.
The hypothesis bounds excess at every vertex, including the centre. -/
theorem all_budget_invariant_find_five (P : M.PartialColouring k) (S : Finset V) (x : V) (m D t c β d : ℕ)
    (h : P.ScaledCompletionInvariant S x m t c) (ht : 0<t) (hcpos : 0<c) (hnum : AdditiveFirstBudget β c m D t k d)
    (hS : S.card=m) (hbal : S.card=Sᶜ.card) (hx : x∈S)
    (hreg : M.IsRegularOfDegree D) (hstar : ∀ z,M.parallelExcess z≤β)
    (i : Fin k) (u v : V) (hu : u∈S) (hv : v∈Sᶜ)
    (hmissU : (P.colouring.colourGraph i).degree u=0)
    (hmissV : (P.colouring.colourGraph i).degree v=0) :
    Nonempty (P.SafeFive S (P.scaledForbidden S x t c) i u v) := by
  let Z:=P.scaledForbidden S x t c
  let b:=4*t+2*Z.card
  have hz : c*Z.card≤4*m+c:=P.scaled_forbidden_card S x m t c h ht
  have hZ : Z.card≤4*m/c+1 := by
    rw [←Nat.add_div_right (4*m) hcpos]
    apply (Nat.le_div_iff_mul_le hcpos).mpr
    simpa only [Nat.mul_comm] using hz
  have hB : b≤OverfullWork.ScaledMargins.badBound c m t:=by
    dsimp [b,OverfullWork.ScaledMargins.badBound]
    omega
  have hmiss : (P.colouring.missingSet S i).card≤t := by have hh:=h.colour_budget i; omega
  have hcut : (P.colouring.colourGraph i).cutSize S≤3*t := by have hh:=h.colour_budget i; omega
  have hmeq:=P.colouring.missing_balance_general S hbal h.balance i
  have hbA : (S\(P.colouring.colourGraph i).eligibleVertices
      (P.colouring.colourGraph_degree_le_one i) S Z).card≤b := by
    have hb:=(P.colouring.colourGraph i).ineligible_card_bound (P.colouring.colourGraph_degree_le_one i) S Z
    change _≤(P.colouring.missingSet S i).card+(P.colouring.colourGraph i).cutSize S+2*Z.card at hb
    dsimp [b]
    omega
  have hbB : (Sᶜ\(P.colouring.colourGraph i).eligibleVertices
      (P.colouring.colourGraph_degree_le_one i) Sᶜ Z).card≤b := by
    have hb:=(P.colouring.colourGraph i).ineligible_card_bound (P.colouring.colourGraph_degree_le_one i) Sᶜ Z
    rw [cutSize_compl] at hb
    change _≤(P.colouring.missingSet Sᶜ i).card+(P.colouring.colourGraph i).cutSize S+2*Z.card at hb
    dsimp [b]
    omega
  have havail : ∀ e,P.available.mult e≤M.mult e:=fun e => Nat.sub_le _ _
  have hfirst : b<(P.available.neighboursInto Sᶜ u).card := by
    have hbudget:=P.crossing_degree_budget S D (c*t) hreg h.remainder_degree u
    rw [if_pos hu] at hbudget
    have hcount:=P.available.degreeInto_le_neighbours_add_excess Sᶜ u
    have hexcess : P.available.parallelExcess u≤β:=
      (M.parallelExcess_mono P.available havail u).trans (hstar u)
    have hh:=hnum.first
    omega
  have hOrd : ∀ z∈Sᶜ,d≤(P.available.neighboursInto S z).card := by
    intro z hzS
    have hnot : z∉S:=mem_compl.mp hzS
    have hbudget:=P.crossing_degree_budget S D (c*t) hreg h.remainder_degree z
    rw [if_neg hnot] at hbudget
    have hcount:=P.available.degreeInto_le_neighbours_add_excess S z
    have hexcess : P.available.parallelExcess z≤β:=
      (M.parallelExcess_mono P.available havail z).trans (hstar z)
    have hh:=hnum.ordinary
    omega
  have hroom : m+2*b<2*(d) := by have hh:=hnum.overlap;omega
  exact P.exists_safe_five S Z i u v m (d) b b hS hu hv hmissU hmissV hbA hbB
    hfirst (hOrd v hv) (fun z hz _ => hOrd z hz) hroom

/-- With parallel excess bounded at every point, ordinary Hall suffices.
There is no multiplicity hypothesis and no exceptional-centre margin. -/
theorem exists_free_colour_matching_all_budget (P : M.PartialColouring k) (S : Finset V)
    (m D a b : ℕ) (hS : S.card=m) (hSc : Sᶜ.card=m)
    (hreg : M.IsRegularOfDegree D) (hbudgetFull : ∀ v,M.parallelExcess v≤b)
    (hcover : P.CoversInternal S) (hroom : m+2*k+4*a+2*b≤2*D)
    (i : Fin k)
    (hcut : (P.colouring.colourGraph i).cutSize S=0)
    (hbal : (P.colouring.colourGraph i).edgesWithin S=(P.colouring.colourGraph i).edgesWithin Sᶜ)
    (hsmall : (P.colouring.colourGraph i).edgesWithin S≤a) :
    ∃ J : MultiGraph V,(∀ e,J.mult e≤P.available.mult e) ∧
      (∀ z,J.degree z=if (P.colouring.colourGraph i).degree z=0 then 1 else 0) ∧
      ∀ u v,(u∈S ↔ v∈S) → J.mult s(u,v)=0 := by
  classical
  let U:=P.colouring.missingSet S i
  let W:=P.colouring.missingSet Sᶜ i
  let N : V → V → Prop:=fun u v => 0<P.available.mult s(u,v)
  have hU : U⊆S:=filter_subset _ _
  have hW : W⊆Sᶜ:=filter_subset _ _
  have heq : U.card=W.card := by
    have hA:=P.colouring.missing_internal_cut_identity S i
    have hB:=P.colouring.missing_internal_cut_identity Sᶜ i
    rw [cutSize_compl,hcut,←hbal,hSc] at hB
    rw [hcut,hS] at hA
    dsimp [U,W]
    omega
  have hUA : (S\U).card≤2*a := by
    have hid:=P.colouring.missing_internal_cut_identity S i
    rw [hcut,hS] at hid
    have hc:=card_sdiff_add_card_eq_card hU
    dsimp only [U] at hc ⊢
    omega
  have hWB : (Sᶜ\W).card≤2*a := by
    have hc:=card_sdiff_add_card_eq_card hW
    have hc':=card_sdiff_add_card_eq_card hU
    omega
  have havail : ∀ e,P.available.mult e≤M.mult e:=fun e => Nat.sub_le _ _
  have hbudget:=P.crossing_degree_budget S D 0 hreg (fun z => by rw [P.covered_remainder_zero S hcover z])
  have hleft : ∀ z∈U,D-k-2*a-b≤(W.filter (N z)).card := by
    intro z hz
    have hzS:=hU hz
    have hb:=hbudget z
    rw [if_pos hzS] at hb
    have hc:=P.available.degreeInto_le_neighbours_add_excess Sᶜ z
    have hexcess : P.available.parallelExcess z≤b:=
      (M.parallelExcess_mono P.available havail z).trans (hbudgetFull z)
    have hl:=OverfullWork.ShortAugmentSearch.neighbours_lost Sᶜ W hW (N z)
    change (P.available.neighboursInto Sᶜ z).card≤(W.filter (N z)).card+(Sᶜ\W).card at hl
    omega
  have hright : ∀ z∈W,D-k-2*a-b≤(U.filter (fun w => N w z)).card := by
    intro z hz
    have hzS : z∉S:=mem_compl.mp (hW hz)
    have hb:=hbudget z
    rw [if_neg hzS] at hb
    have hc:=P.available.degreeInto_le_neighbours_add_excess S z
    have hexcess : P.available.parallelExcess z≤b:=
      (M.parallelExcess_mono P.available havail z).trans (hbudgetFull z)
    have hl:=OverfullWork.ShortAugmentSearch.neighbours_lost S U hU (N z)
    change (P.available.neighboursInto S z).card≤(U.filter (N z)).card+(S\U).card at hl
    have he : (U.filter (N z)).card=(U.filter (fun w => N w z)).card := by
      congr 1
      ext w
      simp only [mem_filter,N,Sym2.eq_swap]
    rw [he] at hl
    omega
  have hsize : W.card≤2*(D-k-2*a-b) := by
    have hh:=card_le_card hW
    rw [hSc] at hh
    omega
  obtain ⟨f,hf⟩:=OverfullWork.DenseHall.exists_matching_on U W N (D-k-2*a-b)
    heq hsize
    (fun z hz => by
      convert hleft z hz using 1 <;> congr 1 <;> (ext w; simp only [mem_filter]))
    (fun z hz => by
      convert hright z hz using 1 <;> congr 1 <;> (ext w; simp only [mem_filter]))
  have hdis : Disjoint U W:=Finset.disjoint_left.mpr (fun _ hu hw => (mem_compl.mp (hW hw)) (hU hu))
  refine ⟨pairingMatching U W hdis f,pairingMatching_le U W hdis f P.available hf,?_,?_⟩
  · intro z
    rw [pairingMatching_degree]
    have hh : z∈U ∨ z∈W ↔ (P.colouring.colourGraph i).degree z=0 := by
      dsimp only [U,W,EdgeColoring.missingSet]
      simp only [mem_filter,mem_compl]
      tauto
    simp only [hh]
  · intro u v huv
    have hz : (pairingMatching U W hdis f).mult s(u,v)=0 := by
      change (if s(u,v)∈(pairingGraph U W hdis f).edgeSet then 1 else 0)=0
      apply if_neg
      rw [SimpleGraph.mem_edgeSet]
      intro hadj
      rcases hadj with ⟨a,rfl,rfl⟩|⟨a,rfl,rfl⟩
      · exact (mem_compl.mp (hW (f a).2)) (huv.mp (hU a.2))
      · exact (mem_compl.mp (hW (f a).2)) (huv.mpr (hU a.2))
    exact hz

/-- The usual potential is conserved exactly, not decreased: each
filled pair of missing endpoints creates exactly two internal copies. -/
theorem perturb_compensated_energy (P : M.PartialColouring k) (S Z : Finset V)
    (i : Fin k) (u v : V) (f : P.SafeFive S Z i u v)
    (h0 : (P.colouring.colourGraph i).degree u=0)
    (h5 : (P.colouring.colourGraph i).degree v=0) :
    ((P.perturb S Z i u v f h0 h5).remainder S).edgeCount+
        2*(P.perturb S Z i u v f h0 h5).deficit S=
      (P.remainder S).edgeCount+2*P.deficit S := by
  rw [P.perturb_remainder,edgeCount_addCopies,(five_edge_counts f.path).1]
  have hd:=P.perturb_deficit_drop S Z i u v f h0 h5
  omega

/-- Every five-path step only adds to the internal remainder. Therefore
reordering these steps alone cannot produce signed cancellation. -/
theorem perturb_remainder_degree_mono (P : M.PartialColouring k) (S Z : Finset V)
    (i : Fin k) (u v : V) (f : P.SafeFive S Z i u v)
    (h0 : (P.colouring.colourGraph i).degree u=0)
    (h5 : (P.colouring.colourGraph i).degree v=0) (z : V) :
    (P.remainder S).degree z≤((P.perturb S Z i u v f h0 h5).remainder S).degree z := by
  rw [P.perturb_remainder,degree_addCopies]
  omega

/-- Once the exceptional point is covered in every existing colour,
any later five-path augmentation keeps it covered. -/
theorem perturb_preserves_filled_point (P : M.PartialColouring k) (S Z : Finset V)
    (i : Fin k) (u v x : V) (f : P.SafeFive S Z i u v)
    (h0 : (P.colouring.colourGraph i).degree u=0)
    (h5 : (P.colouring.colourGraph i).degree v=0)
    (hfilled : ∀ j,(P.colouring.colourGraph j).degree x=1) :
    ∀ j,((P.perturb S Z i u v f h0 h5).colouring.colourGraph j).degree x=1 := by
  have hxu : x≠u:=by intro he;subst u;have hh:=hfilled i;omega
  have hxv : x≠v:=by intro he;subst v;have hh:=hfilled i;omega
  intro j
  by_cases hj : j=i
  · subst j
    rw [P.perturb_selected_degree]
    simp only [hxu,hxv,or_self,if_false,Nat.add_zero]
    exact hfilled i
  · rw [P.perturb_other S Z i u v f h0 h5 j hj]
    exact hfilled j

/-- One of the existing compensated five-path exchanges. -/
def FiveStep (S : Finset V) (P Q : M.PartialColouring k) : Prop :=
  ∃ (Z : Finset V) (i : Fin k) (u v : V) (f : P.SafeFive S Z i u v)
    (h0 : (P.colouring.colourGraph i).degree u=0)
    (h5 : (P.colouring.colourGraph i).degree v=0),
    Q=P.perturb S Z i u v f h0 h5

/-- The conservation law telescopes along every finite sequence of the
existing perturbations. It is not a hidden new recolouring hypothesis. -/
theorem five_trace_compensated_energy (S : Finset V) {P Q : M.PartialColouring k}
    (h : Relation.ReflTransGen (FiveStep S) P Q) :
    (Q.remainder S).edgeCount+2*Q.deficit S=(P.remainder S).edgeCount+2*P.deficit S := by
  induction h with
  | refl => rfl
  | @tail Q R htrace hstep ih =>
    obtain ⟨Z,i,u,v,f,h0,h5,rfl⟩:=hstep
    exact (Q.perturb_compensated_energy S Z i u v f h0 h5).trans ih

/-- In particular no finite chain of those moves decreases any internal
remainder degree. Load balancing or a genuinely different exchange is needed. -/
theorem five_trace_remainder_degree_mono (S : Finset V) {P Q : M.PartialColouring k}
    (h : Relation.ReflTransGen (FiveStep S) P Q) (z : V) :
    (P.remainder S).degree z≤(Q.remainder S).degree z := by
  induction h with
  | refl => exact le_rfl
  | @tail Q R htrace hstep ih =>
    obtain ⟨Z,i,u,v,f,h0,h5,rfl⟩:=hstep
    exact ih.trans (Q.perturb_remainder_degree_mono S Z i u v f h0 h5 z)

end PartialColouring
end SimpleGraph.MultiGraph
