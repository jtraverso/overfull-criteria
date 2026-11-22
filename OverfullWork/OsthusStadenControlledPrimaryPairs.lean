module

public import OverfullWork.OsthusStadenBalancedPrimaryTrimming

@[expose] public section


/-! Two-sided superregular trimming with simultaneous control across original types. -/
namespace OverfullWork.DirectedRegularPairs

open Finset DirectedRobustExpansion
open scoped Classical

/-- A degree-atypical vertex must be deleted from its primary cell when
trimming the outgoing pair or the incoming pair of a primary factor. -/
noncomputable def atypicalPrimaryVertices {I W : Type*} [Fintype W]
    (σ : Equiv.Perm I) (D : I → Digraph W) (ε d : ℝ) (i : I) : Finset W :=
  univ.filter (fun x => 2*ε*(Fintype.card W:ℝ) <
    |(pairSemidegree true (D i) x:ℝ)-d*(Fintype.card W:ℝ)|) ∪
  univ.filter (fun x => 2*ε*(Fintype.card W:ℝ) <
    |(pairSemidegree false (D (σ.symm i)) x:ℝ)-d*(Fintype.card W:ℝ)|)

set_option maxHeartbeats 1200000 in
/-- Trim all factor pairs to common size and superregularity, while
paying at most `cap` extra types per vertex beyond its atypical incidences. -/
theorem exists_controlled_two_sided_factor_trim
    {T I W : Type*} [Fintype T] [Fintype W]
    (σ : T → Equiv.Perm I) (D : T → I → Digraph W) (count m cap : ℕ) (ε δ d : ℝ)
    (hD : ∀ t i, IsCentredRegular (D t i) ε d)
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hn : 0 < Fintype.card W)
    (hd : 0 ≤ d) (hd₁ : d ≤ 1) (hSize : count+m = Fintype.card W)
    (hBudget : 4*ε*(Fintype.card W:ℝ) ≤ (count:ℝ))
    (hReg : 2*ε ≤ δ) (hLarge : (Fintype.card W:ℝ)*ε ≤ (m:ℝ))
    (hScale : (Fintype.card W:ℝ)*ε ≤ (m:ℝ)*δ)
    (hDegree : 2*ε*(Fintype.card W:ℝ)+(count:ℝ) ≤ δ*(m:ℝ))
    (hCap : 0 < cap) (hRoom : Fintype.card T*count ≤ cap*m) :
    ∃ A : T → I → Fin m ↪ W,
      (∀ t i, let P := pullDirectedPair (A t i) (A t (σ t i)) (D t i)
        IsCentredRegular P δ d ∧
        ∀ b x, |(pairSemidegree b P x:ℝ)-d*(m:ℝ)| ≤ δ*(m:ℝ)) ∧
      ∀ i x, ((univ : Finset T).filter (fun t => x ∉ univ.map (A t i))).card ≤
        ((univ : Finset T).filter (fun t => x ∈ atypicalPrimaryVertices (σ t) (D t) ε d i)).card+cap := by
  let required (i : I) (t : T) := atypicalPrimaryVertices (σ t) (D t) ε d i
  have hRequired (i : I) (t : T) : (required i t).card ≤ count := by
    unfold required atypicalPrimaryVertices
    apply (card_union_le _ _).trans
    let bad (b : Bool) (j : I) := ((univ : Finset W).filter (fun x =>
      2*ε*(Fintype.card W:ℝ) < |(pairSemidegree b (D t j) x:ℝ)-d*(Fintype.card W:ℝ)|)).card
    change bad true i+bad false ((σ t).symm i) ≤ count
    have ho : (bad true i:ℝ) ≤ 2*ε*(Fintype.card W:ℝ) :=
      bad_copy_degree_count (D t i) true ε d (hD t i) hε hε₁ hn
    have hi : (bad false ((σ t).symm i):ℝ) ≤ 2*ε*(Fintype.card W:ℝ) :=
      bad_copy_degree_count (D t ((σ t).symm i)) false ε d (hD t _) hε hε₁ hn
    have hb : (bad true i:ℝ)+(bad false ((σ t).symm i):ℝ) ≤ (count:ℝ) := by
      linarith only [ho,hi,hBudget]
    exact_mod_cast hb
  have hLoss : Fintype.card W-m = count := by omega
  have hLeft : Fintype.card W-count = m := by omega
  choose removed hRemoved _ hCounts using fun i => exists_balanced_required_deletions
    (required i) count cap (by omega) hCap (hRequired i) (by rw [hLeft]; exact hRoom)
  let K (t : T) (i : I) := (removed i t)ᶜ
  have hCard (t : T) (i : I) : Fintype.card (K t i) = m := by
    rw [Fintype.card_coe,card_compl,(hRemoved i t).2,hLeft]
  let A (t : T) (i : I) : Fin m ↪ W :=
    (Fintype.equivFinOfCardEq (hCard t i)).symm.toEmbedding.trans (Function.Embedding.subtype _)
  have hImage (t : T) (i : I) : univ.map (A t i) = K t i := by
    ext x
    constructor
    · intro hx
      obtain ⟨z,_,rfl⟩ := mem_map.mp hx
      exact ((Fintype.equivFinOfCardEq (hCard t i)).symm z).property
    · intro hx
      refine mem_map.mpr ⟨Fintype.equivFinOfCardEq (hCard t i) ⟨x,hx⟩,mem_univ _,?_⟩
      exact congrArg Subtype.val ((Fintype.equivFinOfCardEq (hCard t i)).symm_apply_apply ⟨x,hx⟩)
  have hOld (t : T) (i : I) (b : Bool) (x : Fin m) :
      |(pairSemidegree b (D t i) (if b then A t i x else A t (σ t i) x):ℝ)-d*(Fintype.card W:ℝ)| ≤
        2*ε*(Fintype.card W:ℝ) := by
    let u := if b then i else σ t i
    have hx : A t u x ∈ K t u := ((Fintype.equivFinOfCardEq (hCard t u)).symm x).property
    have hn := fun h => (mem_compl.mp hx) ((hRemoved u t).1 h)
    have hn' : A t u x ∉ required u t := hn
    apply le_of_not_gt
    intro h
    apply hn'
    cases b
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,by
        simpa only [u,Bool.false_eq_true,if_false,Equiv.symm_apply_apply] using h⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,h⟩)
  refine ⟨A,?_,?_⟩
  · intro t i
    refine ⟨centred_regular_pull_of_trim _ _ _ _ _ _ (hD t i) hReg
      (by simpa only [Fintype.card_fin] using hLarge)
      (by simpa only [Fintype.card_fin] using hScale),?_⟩
    intro b x
    have hM : Fintype.card (Fin m) ≤ Fintype.card W := by simp only [Fintype.card_fin]; omega
    have h := typical_semidegree_pull_of_trim (A t i) (A t (σ t i)) (D t i) b x d (2*ε) δ hd hd₁
      hM (hOld t i b x) (by simpa only [Fintype.card_fin,hLoss] using hDegree)
    simpa only [Fintype.card_fin] using h
  · intro i x
    simpa only [hImage,K,mem_compl,not_not] using hCounts i x

/-- The two sides of each original factor use distinct labelled copies
across original types. Charge each mandatory deletion to one of those
incidences, even if the vertex is atypical on both sides. -/
theorem atypical_primary_types_le_incident_copies
    {T I J W : Type*} [Fintype T] [Fintype J] [Fintype W]
    (σ : T → Equiv.Perm I) (source target : J → I) (main : J → Digraph W)
    (pick : T → I → J) (hSrc : ∀ t i, source (pick t i) = i)
    (hDst : ∀ t i, target (pick t i) = σ t i)
    (hInj : Function.Injective (fun q : T × I => pick q.1 q.2)) (ε d : ℝ) (i : I) (x : W) :
    ((univ : Finset T).filter (fun t => x ∈ atypicalPrimaryVertices (σ t) (fun j => main (pick t j)) ε d i)).card ≤
      (atypicalIncidentCopies source target main ε d true i x).card+
      (atypicalIncidentCopies source target main ε d false i x).card := by
  let endpoint (b : Bool) (t : T) := if b then i else (σ t).symm i
  let atypical (b : Bool) (t : T) :=
    2*ε*(Fintype.card W:ℝ) <
      |(pairSemidegree b (main (pick t (endpoint b t))) x:ℝ)-d*(Fintype.card W:ℝ)|
  let types (b : Bool) := (univ : Finset T).filter (atypical b)
  have hEmb (b : Bool) : (types b).card ≤ (atypicalIncidentCopies source target main ε d b i x).card := by
    apply card_le_card_of_injOn (fun t => pick t (endpoint b t))
    · intro t ht
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,?_⟩,(mem_filter.mp ht).2⟩
      cases b
      · simpa only [endpoint,copyEndpoint,Bool.false_eq_true,if_false,hDst,Equiv.apply_symm_apply]
      · simpa only [endpoint,copyEndpoint,if_true,hSrc]
    · intro t _ t' _ h
      have he : (t,endpoint b t) = (t',endpoint b t') := hInj h
      exact congrArg Prod.fst he
  have hEq : ((univ : Finset T).filter
      (fun t => x ∈ atypicalPrimaryVertices (σ t) (fun j => main (pick t j)) ε d i)) =
        types true ∪ types false := by
    ext t
    simp [types,atypical,endpoint,atypicalPrimaryVertices]
  rw [hEq]
  exact (card_union_le _ _).trans (Nat.add_le_add (hEmb true) (hEmb false))

end OverfullWork.DirectedRegularPairs
