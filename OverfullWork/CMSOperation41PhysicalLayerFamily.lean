module

public import OverfullWork.CMSOperation41ReplacementWords
public import OverfullWork.CMSOperation41UniformPacking

@[expose] public section


/-! Project all the packed rounds while retaining the same unused
ordinary-core graph. Only the host edges belong to the simultaneously
packed layers. The prescribed edges are supplied by each virtual round. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph DirectedSpanningConfiguration DirectedRobustExpansion RobustExpansion
open DirectedReserveUsage
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge SimpleGraph.instDecidableMapAdj

universe u v
variable {V : Type u} [Fintype V] [DecidableEq V] {K : Type v} [Fintype K]

/-- Reindexing preserves the fixed words and all their gap occurrences. -/
def TrimmingReplacementWords.reindex {G : SimpleGraph V} {U : Finset V} {I J : Type*}
    (R : TrimmingReplacementWords G U I) (e : J ≃ I) : TrimmingReplacementWords G U J where
  endpoint := (Equiv.prodCongr e (Equiv.refl Bool)).toEmbedding.trans R.endpoint
  body := R.body ∘ e
  gaps := R.gaps
  chain := fun i => R.chain (e i)
  gap_witness := by
    intro t ht
    obtain ⟨i,a,b,hEq,hWord⟩ := R.gap_witness t ht
    refine ⟨e.symm i,a,b,hEq,?_⟩
    change List.IsInfix [a,b] (R.word (e (e.symm i)))
    rwa [Equiv.apply_symm_apply]
  simple := fun i => R.simple (e i)
  outside := fun i => R.outside (e i)
  disjoint := fun i j h => R.disjoint (e i) (e j) (fun hEq => h (e.injective hEq))

omit [Fintype V] in
/-- Transfer the accumulated vertex charges to the visit count used by
uniform core packing. The finite index records exactly the completed rounds. -/
theorem core_layout_visits_le_projection_history {C : Type*} [Fintype C] (inc : C ↪ V)
    {m : ℕ} (ready : Fin m → Finset C) (history : ℕ → Finset V)
    (hIncluded : ∀ j x,x ∈ ready j → inc x ∈ history j.val) (x : C) :
    visits ready x ≤ projectionLoad (range m) history (inc x) := by
  apply card_le_card_of_injOn (f := Fin.val)
  · intro j hj
    exact mem_filter.mpr ⟨mem_range.mpr j.isLt,hIncluded j x (mem_filter.mp hj).2⟩
  · exact Fin.val_injective.injOn

/-- The rounded cap in Claim 4.1(7) still leaves room for the
number of representatives used by all earlier rounds. -/
theorem cms_projection_history_has_saturation_budget (n rounds perRound : ℕ) (η : ℝ)
    (hSize : 12 ≤ η*(n:ℝ)) (hRounds : 3*rounds ≤ n)
    (hPerRound : (perRound:ℝ) ≤ 2*η^2*(n:ℝ)) :
    let cap := ⌊η*(n:ℝ)⌋₊
    0 < cap ∧ rounds*perRound ≤ cap*cap := by
  intro cap
  have hFloor : η*(n:ℝ) < (cap:ℝ)+1 := Nat.lt_floor_add_one _
  have hCap : (11/12)*(η*(n:ℝ)) ≤ (cap:ℝ) := by linarith only [hSize,hFloor]
  have hRoundCast : (rounds:ℝ) ≤ (n:ℝ)/3 := by
    have h : 3*(rounds:ℝ) ≤ (n:ℝ) := by exact_mod_cast hRounds
    linarith only [h]
  have hProd := mul_le_mul hRoundCast hPerRound (Nat.cast_nonneg perRound)
    (show 0 ≤ (n:ℝ)/3 by positivity)
  have hSquare := mul_self_le_mul_self (show 0 ≤ (11/12)*(η*(n:ℝ)) by positivity) hCap
  have hNorm : 0 ≤ (η*(n:ℝ))^2 := sq_nonneg _
  constructor
  · exact_mod_cast (show (0:ℝ) < cap by linarith only [hSize,hCap])
  · apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    nlinarith only [hProd,hSquare,hNorm]

set_option maxHeartbeats 3000000 in
theorem physical_layers_of_packed_trimming_words (U : Finset V)
    (host : SimpleGraph ↥(Uᶜ : Finset V)) [DecidableRel host.Adj]
    (afterCleanup : K → SimpleGraph V) (f : K → ℕ)
    (words : ∀ j,TrimmingReplacementWords (afterCleanup j) U (Fin (f j)))
    (omitted : K → Finset ↥(Uᶜ : Finset V)) (ρ τ : ℝ)
    (hHost : ∀ j a b,host.Adj a b → (afterCleanup j).Adj a.val b.val)
    (hPack : HasPackedCoreLayouts host f (fun j => (words j).endpoint) omitted ρ τ)
    (hParity : ∀ j,
      let len := (Uᶜ : Finset V).card-(omitted j).card+∑ i,((words j).body i).length
      3 ≤ len ∧ (Even len ∨ (words j).gaps.Nonempty)) :
    ∃ (reserve : SimpleGraph ↥(Uᶜ : Finset V)) (layer : K → SimpleGraph V),
      reserve ≤ host ∧ IsRealRobust reserve ρ τ ∧
      Pairwise (fun i j => Disjoint (layer i) (layer j)) ∧
      (∀ j a b,(layer j).Adj a b → a ∉ U ∧ b ∉ U) ∧
      (∀ j a b,reserve.Adj a b → ¬(layer j).Adj a.val b.val) ∧
      ∀ j,
        let Q := (words j).prescribedGraph ⊔ layer j
        Q ≤ afterCleanup j ∧ Q.EdgeColorable 2 ∧ (∀ x,Q.degree x ≤ 2) ∧
          (∀ x,x ∉ omitted j → (∀ y,s(x.val,y) ∉ (words j).gaps) → Q.degree x.val = 2) ∧
          (∀ x ∈ omitted j,Q.degree x.val = 0) ∧
          ∀ x,Q.degree x+(words j).degreeCredit (omitted j) x = 2 := by
  obtain ⟨w,F,mark,hMark,hEnds,hIso,P,hRes⟩ := hPack
  let incl : ↥(Uᶜ : Finset V) ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let graph (j : K) := (hostEdges host (P.configuration j).used).map incl
  let layer (j : K) := (graph j).deleteEdges ((words j).gaps : Set (Sym2 V))
  let reserve := host \ hostEdges host P.used
  have hLe (j : K) : layer j ≤ graph j := deleteEdges_le _
  let C := ↥(Uᶜ : Finset V)
  have hTransport (dEq dEq' : DecidableEq C) (dAdj dAdj' : DecidableRel reserve.Adj)
      (h : @IsRealRobust C _ dEq reserve dAdj ρ τ) :
      @IsRealRobust C _ dEq' reserve dAdj' ρ τ := by
    cases Subsingleton.elim dEq dEq'
    cases Subsingleton.elim dAdj dAdj'
    exact h
  have hRes' : IsRealRobust reserve ρ τ := hTransport _ _ _ _ hRes
  refine ⟨reserve,layer,sdiff_le,hRes',?_,?_,?_,?_⟩
  · intro i j hij
    exact Disjoint.mono (hLe i) (hLe j) (mapped_host_edges_disjoint P incl hij)
  · intro j a b h
    obtain ⟨u,v,_,rfl,rfl⟩ := (map_adj incl _ _ _).mp (hLe j h)
    exact ⟨mem_compl.mp u.property,mem_compl.mp v.property⟩
  · intro j a b h hEdge
    obtain ⟨u,v,hv,hu,hv'⟩ := (map_adj incl _ _ _).mp (hLe j hEdge)
    have hUA : u=a := incl.injective hu
    have hVB : v=b := incl.injective hv'
    subst u v
    exact h.2 (packed_core_edges_le_global_usage P j hv)
  · intro j
    obtain ⟨hSize,hEven⟩ := hParity j
    obtain ⟨hQLe,hTwo,hDeg,hOrd,hZero,hBalance⟩ :=
      (words j).realized_is_two_colour_layer_with_gap_balance (by omega) (w j) (mark j) (F j) (hMark j)
        (omitted j) (hIso j) (hEnds j) P.isOrientation (P.configuration j)
        (fun a b h => hHost j a b (P.isOrientation.1 a b h)) hSize hEven
    refine ⟨hQLe,hTwo,hDeg,hOrd,hZero,?_⟩
    intro x
    apply (words j).degree_add_credit_of_gap_balance (omitted j) _ x
    by_cases h : (∃ a ∉ omitted j,a.val = x) ∨ (∃ i,x ∈ (words j).body i)
    · simpa only [if_pos h] using hBalance x
    · simpa only [if_neg h] using hBalance x

end OverfullWork.CMSTrimmingRound
