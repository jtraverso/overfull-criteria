module

public import OverfullWork.KuhnOsthusBalancedChordExtension
public import OverfullWork.KuhnOsthusExceptionalRoutes
public import OverfullWork.KuhnOsthusExceptionalChordRealization

@[expose] public section


/-! The matching in the identified interval in Lemma 7.6.
Its exceptional shortcuts and correcting chords satisfy Proposition
7.3, stay away from the identified boundary and leave quantified
free sides in every successor pair. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedDemandHall DirectedListRoutes
open scoped Classical
variable {W I E : Type*} [Fintype W] [Fintype I] [Fintype E]

/-- The ordinary vertices with a specified cluster label. -/
noncomputable def intervalCluster (cluster : W → I) (i : I) : Finset W :=
  univ.filter (fun v => cluster v = i)

omit [Fintype I] in
@[simp]
theorem mem_intervalCluster (cluster : W → I) (i : I) (v : W) :
    v ∈ intervalCluster cluster i ↔ cluster v = i := by simp [intervalCluster]

omit [Fintype I] in
private theorem card_cluster_inter_image (cluster : W → I) (f : E → W) (i : I) :
    (intervalCluster cluster i ∩ univ.image f).card ≤
      ((univ : Finset E).filter (fun p => cluster (f p) = i)).card := by
  have he : intervalCluster cluster i ∩ univ.image f =
      ((univ : Finset E).filter (fun p => cluster (f p) = i)).image f := by
    ext x
    simp only [mem_inter,mem_intervalCluster,mem_image,mem_univ,true_and,mem_filter]
    exact ⟨fun ⟨hx,p,he⟩ => ⟨p,he.symm ▸ hx,he⟩,fun ⟨p,hp,he⟩ => ⟨he ▸ hp,p,he⟩⟩
  rw [he]
  exact card_image_le

/-- The exceptional arcs and their physical chords form a balanced
matching supported away from the boundary. The count of simultaneously
free vertices pays for both the old endpoints and the new chord ends. -/
theorem exists_balanced_exceptional_matching_of_routes
    (R : Digraph I) (H : Digraph W) (s : Equiv.Perm I) (cluster : W → I)
    (endpoint : Bool × E → W) (boundary : Finset I)
    (m w e cap interior endLoad : ℕ)
    (hSize : ∀ i, (intervalCluster cluster i).card = m)
    (hInj : Function.Injective endpoint)
    (hInside : ∀ p, cluster (endpoint p) ∉ boundary)
    (hStart : ∀ z, s.symm (cluster (endpoint (true,z))) ∉ boundary)
    (hFinish : ∀ z, s (cluster (endpoint (false,z))) ∉ boundary)
    (hR : ∀ i, ¬R.Adj i i)
    (hCap : ∀ i, ((univ : Finset (Bool × E)).filter (fun p => cluster (endpoint p) = i)).card ≤ cap)
    (hWidth : w+cap ≤ m) (hRoom : 2*(interior+endLoad)+e < w)
    (l : E → List I)
    (hRoute : ∀ j, Route (reindexSources R s.symm) (cluster (endpoint (true,j)))
      (s (cluster (endpoint (false,j)))) (l j))
    (hInt : ∀ i, (∑ j, chordInteriorLoad s (l j) i) ≤ interior)
    (hEnd : ∀ i, (∑ z : E, if s.symm (cluster (endpoint (true,z))) = i then (1:ℕ) else 0) +
      (∑ z : E, if s (cluster (endpoint (false,z))) = i then (1:ℕ) else 0) ≤ endLoad)
    (hBoundary : ∀ j v, v ∈ (l j).dropLast → v ∉ boundary ∧ s.symm v ∉ boundary)
    (hRect : ∀ i j, R.Adj i j → ∀ X ⊆ intervalCluster cluster i, ∀ Y ⊆ intervalCluster cluster j,
      e < X.card → e < Y.card → 0 < incidences H X Y) :
    ∃ D : Digraph W, IsDirectedPathSystem D ∧
      (∀ z, D.Adj (endpoint (false,z)) (endpoint (true,z))) ∧
      (∀ x y, D.Adj x y → cluster x ∉ boundary ∧ cluster y ∉ boundary ∧
        ((∃ z, endpoint (false,z) = x ∧ endpoint (true,z) = y) ∨ H.Adj x y)) ∧
      (∀ i, (freeOut D cluster i).card = (freeIn D cluster (s i)).card) ∧
      ∀ i, m ≤ (freeOut D cluster i ∩ freeIn D cluster i).card + (cap+interior+endLoad) := by
  classical
  let a (z : E) := cluster (endpoint (true,z))
  let b (z : E) := s (cluster (endpoint (false,z)))
  let F : Finset W := univ.image endpoint
  have hF (i : I) : (intervalCluster cluster i ∩ F).card ≤ cap :=
    (card_cluster_inter_image cluster endpoint i).trans (hCap i)
  have hAvail (i : I) : w ≤ (intervalCluster cluster i \ F).card := by
    have h := card_sdiff_add_card_inter (intervalCluster cluster i) F
    have hf := hF i
    have hi := hSize i
    omega
  obtain ⟨f,hf,hApart⟩ := exists_exceptional_chord_edges_for_routes R H s cluster a b l
    (intervalCluster cluster) F w e interior endLoad hR hRoute hInt hEnd
    (fun i x hx => (mem_intervalCluster cluster i x).mp hx) hAvail hRoom hRect
  let P := Σ j, Fin (l j).length
  let src (p : P) := s.symm ((a p.1 :: l p.1)[p.2.val]'(Nat.lt_succ_of_lt p.2.isLt))
  let dst (p : P) := (l p.1)[p.2.val]
  have hTag (p : P) : cluster (f p).1 = src p ∧ cluster (f p).2 = dst p :=
    ⟨(mem_intervalCluster _ _ _).mp (mem_sdiff.mp (hf p).1).1,
      (mem_intervalCluster _ _ _).mp (mem_sdiff.mp (hf p).2.1).1⟩
  have hCount (i : I) : (univ.filter (fun p : P => src p = i)).card +
      (univ.filter (fun p : P => dst p = i)).card ≤ interior+endLoad := by
    rw [chord_position_incidence_count s a l i]
    have h := sum_le_sum (s := univ) (fun j _ =>
      chord_endpoint_load_le R s (a j) (b j) (l j) (hRoute j) i)
    simp only [sum_add_distrib] at h ⊢
    have hi := hInt i
    have he := hEnd i
    change (∑ j, if s.symm (a j) = i then (1:ℕ) else 0) +
      (∑ j, if b j = i then (1:ℕ) else 0) ≤ endLoad at he
    omega
  have hNoBoundary (i : I) (hi : i ∈ boundary) :
      (univ.filter (fun p : P => src p = i)).card +
        (univ.filter (fun p : P => dst p = i)).card = 0 := by
    rw [chord_position_incidence_count s a l i]
    exact sum_eq_zero (fun j _ => chord_has_no_boundary_incidence R s (a j) (b j) (l j)
      boundary (hRoute j) (hStart j) (hFinish j) (hBoundary j) i hi)
  have hFreshBoundary (p : P) : src p ∉ boundary ∧ dst p ∉ boundary := by
    constructor
    · intro h
      have h0 := hNoBoundary (src p) h
      have hp : 0 < (univ.filter (fun q : P => src q = src p)).card :=
        card_pos.mpr ⟨p,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩
      omega
    · intro h
      have h0 := hNoBoundary (dst p) h
      have hp : 0 < (univ.filter (fun q : P => dst q = dst p)).card :=
        card_pos.mpr ⟨p,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩
      omega
  let k (j : E) := (endpoint (false,j),endpoint (true,j))
  let Q : Digraph W := ⟨fun x y => ∃ j, k j = (x,y)⟩
  let C : Digraph W := ⟨fun x y => ∃ p : P, f p = (x,y)⟩
  have hSepQ : ∀ p q : E, p ≠ q →
      (k p).1 ≠ (k q).1 ∧ (k p).1 ≠ (k q).2 ∧ (k p).2 ≠ (k q).1 ∧ (k p).2 ≠ (k q).2 := by
    intro p q hpq
    refine ⟨fun h => hpq (congrArg Prod.snd (hInj h)),
      fun h => Bool.false_ne_true (congrArg Prod.fst (hInj h)),
      fun h => Bool.false_ne_true (congrArg Prod.fst (hInj h)).symm,
      fun h => hpq (congrArg Prod.snd (hInj h))⟩
  have hk : ∀ j, (k j).1 ≠ (k j).2 :=
    fun j h => Bool.false_ne_true (congrArg Prod.fst (hInj h))
  have hQ := path_system_of_separate_arcs k hk hSepQ
  have hArcBij : Function.Bijective (fun j : E => (⟨k j,⟨j,rfl⟩⟩ : Arc Q)) := by
    constructor
    · intro p q h
      exact congrArg Prod.snd (hInj (congrArg (fun v : Arc Q => v.val.1) h))
    · rintro ⟨⟨x,y⟩,j,hj⟩
      exact ⟨j,Subtype.ext hj⟩
  let eqArc : E ≃ Arc Q := Equiv.ofBijective _ hArcBij
  let ll (j : Arc Q) := l (eqArc.symm j)
  let fc (p : Σ j : Arc Q, Fin (ll j).length) := f ⟨eqArc.symm p.1,p.2⟩
  have hEq (j : Arc Q) : k (eqArc.symm j) = j.val :=
    congrArg Subtype.val (eqArc.apply_symm_apply j)
  have hCoords (j : Arc Q) :
      cluster j.val.2 = a (eqArc.symm j) ∧ s (cluster j.val.1) = b (eqArc.symm j) :=
    ⟨congrArg (fun v : W × W => cluster v.2) (hEq j).symm,
      congrArg (fun v : W × W => s (cluster v.1)) (hEq j).symm⟩
  have hChord (p : Σ j : Arc Q, Fin (ll j).length) :
      cluster (fc p).1 = s.symm ((cluster p.1.val.2 :: ll p.1)[p.2.val]'(Nat.lt_succ_of_lt p.2.isLt)) ∧
      cluster (fc p).2 = (ll p.1)[p.2.val] ∧ C.Adj (fc p).1 (fc p).2 ∧ (fc p).1 ≠ (fc p).2 := by
    let q : P := ⟨eqArc.symm p.1,p.2⟩
    refine ⟨?_,(hTag q).2,⟨q,Prod.ext rfl rfl⟩,(hf q).2.2.2⟩
    rw [(hCoords p.1).1]
    exact (hTag q).1
  have hQinF (x : W) (hx : IncidentTo Q x) : x ∈ F := by
    rcases hx with ⟨y,j,hj⟩ | ⟨y,j,hj⟩
    · exact mem_image.mpr ⟨(false,j),mem_univ _,congrArg Prod.fst hj⟩
    · exact mem_image.mpr ⟨(true,j),mem_univ _,congrArg Prod.snd hj⟩
  have hSep (p q : Σ j : Arc Q, Fin (ll j).length) (hpq : p ≠ q) :
      (fc p).1 ≠ (fc q).1 ∧ (fc p).1 ≠ (fc q).2 ∧ (fc p).2 ≠ (fc q).1 ∧ (fc p).2 ≠ (fc q).2 := by
    apply hApart
    exact (Equiv.sigmaCongrLeft (β := fun j : E => Fin (l j).length) eqArc.symm).injective.ne hpq
  obtain ⟨D,hDQ,hSub,hD,hBal⟩ := balanced_chord_extension_of_realized_routes Q C cluster s hQ ll
    (fun j => by rw [(hCoords j).1,(hCoords j).2]; exact (hRoute (eqArc.symm j)).2)
    fc hChord (fun p => ⟨fun h => (mem_sdiff.mp (hf ⟨eqArc.symm p.1,p.2⟩).1).2 (hQinF _ h),
      fun h => (mem_sdiff.mp (hf ⟨eqArc.symm p.1,p.2⟩).2.1).2 (hQinF _ h)⟩)
    hSep (fun i => (hSize i).trans (hSize (s i)).symm)
  refine ⟨D,hD,fun z => hDQ (show Q.Adj _ _ from ⟨z,rfl⟩),?_,hBal,?_⟩
  · intro x y hd
    rcases (Digraph.sup_adj _ _ _ _).mp (hSub hd) with ⟨j,hj⟩ | ⟨p,hp⟩
    · have hx : endpoint (false,j) = x := congrArg Prod.fst hj
      have hy : endpoint (true,j) = y := congrArg Prod.snd hj
      exact ⟨hx ▸ hInside (false,j),hy ▸ hInside (true,j),Or.inl ⟨j,hx,hy⟩⟩
    · have hh := hTag p
      have hb := hFreshBoundary p
      have hArc := (hf p).2.2.1
      rw [hp] at hh hArc
      exact ⟨fun h => hb.1 (hh.1 ▸ h),fun h => hb.2 (hh.2 ▸ h),Or.inr hArc⟩
  · intro i
    let A := intervalCluster cluster i
    let L := univ.image (fun p : P => (f p).1)
    let M := univ.image (fun p : P => (f p).2)
    have hL : (A ∩ L).card ≤ (univ.filter (fun p : P => src p = i)).card := by
      simpa only [A,L,(fun p => (hTag p).1)] using
        card_cluster_inter_image cluster (fun p : P => (f p).1) i
    have hM : (A ∩ M).card ≤ (univ.filter (fun p : P => dst p = i)).card := by
      simpa only [A,M,(fun p => (hTag p).2)] using
        card_cluster_inter_image cluster (fun p : P => (f p).2) i
    let B := (A ∩ F) ∪ (A ∩ L) ∪ (A ∩ M)
    have hBudget : B.card ≤ cap+interior+endLoad := by
      have hBound := (card_union_le ((A ∩ F) ∪ (A ∩ L)) (A ∩ M)).trans
        (Nat.add_le_add_right (card_union_le (A ∩ F) (A ∩ L)) _)
      change B.card ≤ (A ∩ F).card + (A ∩ L).card + (A ∩ M).card at hBound
      have h := hCount i
      have hg : (A ∩ F).card ≤ cap := hF i
      omega
    have hFree : A \ B ⊆ freeOut D cluster i ∩ freeIn D cluster i := by
      intro v hv
      obtain ⟨hvA,hvB⟩ := mem_sdiff.mp hv
      have hClass := (mem_intervalCluster _ _ _).mp hvA
      have hFresh : ¬ IncidentTo D v := by
        rintro (⟨y,hy⟩ | ⟨y,hy⟩)
        · rcases (Digraph.sup_adj _ _ _ _).mp (hSub hy) with h | ⟨p,hp⟩
          · exact hvB (mem_union_left _ (mem_union_left _ (mem_inter.mpr ⟨hvA,hQinF _ (Or.inl ⟨y,h⟩)⟩)))
          · exact hvB (mem_union_left _ (mem_union_right _ (mem_inter.mpr
              ⟨hvA,mem_image.mpr ⟨p,mem_univ _,congrArg Prod.fst hp⟩⟩)))
        · rcases (Digraph.sup_adj _ _ _ _).mp (hSub hy) with h | ⟨p,hp⟩
          · exact hvB (mem_union_left _ (mem_union_left _ (mem_inter.mpr ⟨hvA,hQinF _ (Or.inr ⟨y,h⟩)⟩)))
          · exact hvB (mem_union_right _ (mem_inter.mpr
              ⟨hvA,mem_image.mpr ⟨p,mem_univ _,congrArg Prod.snd hp⟩⟩))
      exact mem_inter.mpr ⟨mem_freeOut.mpr ⟨hClass,fun h => hFresh (Or.inl h)⟩,
        mem_freeIn.mpr ⟨hClass,fun h => hFresh (Or.inr h)⟩⟩
    calc
      m = A.card := (hSize i).symm
      _ ≤ (A \ B).card+B.card := card_le_card_sdiff_add_card
      _ ≤ _ := Nat.add_le_add (card_le_card hFree) hBudget

/-- Schedule all the short routes, realize them on the ordinary
vertices and certify the free-side budget for their union. -/
theorem exists_balanced_exceptional_matching
    (R : Digraph I) (H : Digraph W) (s : Equiv.Perm I) (cluster : W → I)
    (endpoint : Bool × E → W) (boundary : Finset I)
    (m w e endpointCap routeCap routeBudget radius growth cutoff : ℕ)
    (hSize : ∀ i, (intervalCluster cluster i).card = m)
    (hInj : Function.Injective endpoint)
    (hInside : ∀ p, cluster (endpoint p) ∉ boundary)
    (hStart : ∀ z, s.symm (cluster (endpoint (true,z))) ∉ boundary)
    (hFinish : ∀ z, s (cluster (endpoint (false,z))) ∉ boundary)
    (hR : ∀ i, ¬R.Adj i i)
    (hCap : ∀ i, ((univ : Finset (Bool × E)).filter (fun p => cluster (endpoint p) = i)).card ≤ endpointCap)
    (hWidth : w+endpointCap ≤ m) (hRoom : 2*(routeCap+2+2*endpointCap)+e < w)
    (hRobust : IsRobustAt R radius cutoff) (hGrowth : 0 < growth)
    (hAvoid : 2*(routeBudget+boundary.card)+growth ≤ radius)
    (hOut : ∀ i, cutoff+2*(routeBudget+boundary.card) ≤ outDegree R i)
    (hIn : ∀ i, cutoff ≤ inDegree R i)
    (hMass : Fintype.card E*(2*(Fintype.card I/growth+3)) < routeCap*(routeBudget+1))
    (hRect : ∀ i j, R.Adj i j → ∀ X ⊆ intervalCluster cluster i, ∀ Y ⊆ intervalCluster cluster j,
      e < X.card → e < Y.card → 0 < incidences H X Y) :
    ∃ D : Digraph W, IsDirectedPathSystem D ∧
      (∀ z, D.Adj (endpoint (false,z)) (endpoint (true,z))) ∧
      (∀ x y, D.Adj x y → cluster x ∉ boundary ∧ cluster y ∉ boundary ∧
        ((∃ z, endpoint (false,z) = x ∧ endpoint (true,z) = y) ∨ H.Adj x y)) ∧
      (∀ i, (freeOut D cluster i).card = (freeIn D cluster (s i)).card) ∧
      ∀ i, m ≤ (freeOut D cluster i ∩ freeIn D cluster i).card +
        (endpointCap+(routeCap+2)+2*endpointCap) := by
  obtain ⟨l,hRoutes,hInterior⟩ := exists_exceptional_interval_chord_routes R s
    (fun z : E => cluster (endpoint (true,z))) (fun z : E => s (cluster (endpoint (false,z))))
    boundary radius growth cutoff routeCap routeBudget hRobust hGrowth hAvoid
    (fun _ => hOut _) (fun _ => hIn _) hMass
  exact exists_balanced_exceptional_matching_of_routes R H s cluster endpoint boundary
    m w e endpointCap (routeCap+2) (2*endpointCap) hSize hInj hInside hStart hFinish hR hCap
    hWidth hRoom l (fun j => (hRoutes j).1) hInterior
    (exceptional_endpoint_chord_load s cluster endpoint endpointCap hCap)
    (fun j => (hRoutes j).2.2.2) hRect

end OverfullWork.DirectedRobustExpansion
