module

public import OverfullWork.RobustDegreeDemandCuts
public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.Data.Finset.Sum

@[expose] public section


/-! Reduce the directed unit-capacity degree problem to Hall. An arc
has two private vertices in the matching instance. Matching the two
to each other means the arc is unused. -/
namespace OverfullWork.DirectedDemandHall
open Finset DirectedRobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V]

def Arc (D : Digraph V) := {e : V × V // D.Adj e.1 e.2}

noncomputable instance (D : Digraph V) : Fintype (Arc D) := by
  unfold Arc
  infer_instance

abbrev Slots (p : V → ℕ) := Σ v, Fin (p v)

def endpointLinks {E : Type*} (src dst : E → V) (p q : V → ℕ) :
    (Slots p ⊕ E) → (Slots q ⊕ E) → Prop
  | .inl x, .inr a => x.1 = src a
  | .inr a, .inl y => dst a = y.1
  | .inr a, .inr b => a = b
  | .inl _, .inl _ => False

def Links (D : Digraph V) (p q : V → ℕ) : (Slots p ⊕ Arc D) → (Slots q ⊕ Arc D) → Prop :=
  endpointLinks (fun a => a.val.1) (fun a => a.val.2) p q

private theorem slot_card (p : V → ℕ) (S : Finset V) :
    ((univ : Finset (Slots p)).filter (fun x => x.1 ∈ S)).card = ∑ v ∈ S,p v := by
  have he : (univ : Finset (Slots p)).filter (fun x => x.1 ∈ S) =
      S.sigma (fun v => (univ : Finset (Fin (p v)))) := by
    ext ⟨v,j⟩
    simp
  rw [he,Finset.card_sigma]
  simp

private theorem arc_card (D : Digraph V) (S T : Finset V) :
    ((univ : Finset (Arc D)).filter (fun a => a.val.1 ∈ S ∧ a.val.2 ∈ T)).card =
      incidences D S T := by
  let C := (S ×ˢ T).filter (fun a => D.Adj a.1 a.2)
  have he : ((univ : Finset (Arc D)).filter (fun a => a.val.1 ∈ S ∧ a.val.2 ∈ T)).card = C.card := by
    apply card_bij (fun a _ => a.val)
    · intro a ha
      obtain ⟨hs,ht⟩ := (mem_filter.mp ha).2
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hs,ht⟩,a.prop⟩
    · intro a _ b _ he
      exact Subtype.ext he
    · intro a ha
      obtain ⟨hm,hp⟩ := mem_filter.mp ha
      exact ⟨⟨a,hp⟩,mem_filter.mpr ⟨mem_univ _,mem_product.mp hm⟩,rfl⟩
  rw [he]
  simp only [C,incidences,inNeighbours,card_filter,sum_product]
  rw [sum_comm]

private theorem exists_endpoint_slot_matching {E : Type*} [Fintype E] (src dst : E → V)
    (p q : V → ℕ) (hBalance : (∑ v,p v) = ∑ v,q v)
    (hCuts : ∀ S T : Finset V, (∑ v ∈ S,p v) ≤ (∑ v ∈ T,q v) +
      ((univ : Finset E).filter (fun a => src a ∈ S ∧ dst a ∉ T)).card) :
    ∃ F : (Slots p ⊕ E) ≃ (Slots q ⊕ E), ∀ x, endpointLinks src dst p q x (F x) := by
  let N := fun x : Slots p ⊕ E => univ.filter (endpointLinks src dst p q x)
  have hHall (X : Finset (Slots p ⊕ E)) : X.card ≤ (X.biUnion N).card := by
    let S := X.toLeft.image (fun x => x.1)
    let A := X.toRight
    let T := A.image dst
    let B := (univ : Finset (E)).filter (fun a => src a ∈ S ∧ dst a ∉ T)
    let C := (univ : Finset (Slots q)).filter (fun y => y.1 ∈ T)
    have hS : X.toLeft.card ≤ ∑ v ∈ S,p v := by
      rw [← slot_card]
      exact card_le_card (fun x hx => mem_filter.mpr ⟨mem_univ _,mem_image.mpr ⟨x,hx,rfl⟩⟩)
    have hDis : Disjoint A B := by
      apply disjoint_left.mpr
      intro a ha hb
      exact (mem_filter.mp hb).2.2 (mem_image.mpr ⟨a,ha,rfl⟩)
    have hC : C.disjSum (A ∪ B) ⊆ X.biUnion N := by
      intro x hx
      cases x with
      | inl y =>
        have hy := inl_mem_disjSum.mp hx
        obtain ⟨a,ha,he⟩ := mem_image.mp (mem_filter.mp hy).2
        exact mem_biUnion.mpr ⟨Sum.inr a,mem_toRight.mp ha,mem_filter.mpr ⟨mem_univ _,he⟩⟩
      | inr a =>
        rcases mem_union.mp (inr_mem_disjSum.mp hx) with ha | hb
        · exact mem_biUnion.mpr ⟨Sum.inr a,mem_toRight.mp ha,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩
        · obtain ⟨x,hx,he⟩ := mem_image.mp (mem_filter.mp hb).2.1
          exact mem_biUnion.mpr ⟨Sum.inl x,mem_toLeft.mp hx,mem_filter.mpr ⟨mem_univ _,he⟩⟩
    have hN := card_le_card hC
    rw [card_disjSum,card_union_of_disjoint hDis] at hN
    have hCardC : C.card = ∑ v ∈ T,q v := slot_card _ _
    have hX := card_toLeft_add_card_toRight (u := X)
    change X.toLeft.card+A.card = X.card at hX
    have h := hCuts S T
    change (∑ v ∈ S,p v) ≤ (∑ v ∈ T,q v)+B.card at h
    omega
  obtain ⟨f,hf,hfN⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' N).mp hHall
  have he : Fintype.card (Slots p ⊕ E) = Fintype.card (Slots q ⊕ E) := by
    simp only [Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin,hBalance]
  exact ⟨Equiv.ofBijective f ⟨hf,(Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,he⟩ |>.2⟩,
    fun x => (mem_filter.mp (hfN x)).2⟩

/-- The directed capacity inequalities give a perfect matching in the
arc-and-slot formulation. The matching gives an integral flow certificate. -/
theorem exists_arc_slot_matching (D : Digraph V) (p q : V → ℕ)
    (hBalance : (∑ v,p v) = ∑ v,q v)
    (hCuts : ∀ S T : Finset V, (∑ v ∈ S,p v) ≤ (∑ v ∈ T,q v)+incidences D S Tᶜ) :
    ∃ F : (Slots p ⊕ Arc D) ≃ (Slots q ⊕ Arc D), ∀ x, Links D p q x (F x) := by
  apply exists_endpoint_slot_matching _ _ p q hBalance
  intro S T
  simpa only [←mem_compl,arc_card] using hCuts S T

variable {E : Type*} {src dst : E → V} {p q : V → ℕ}
  {F : (Slots p ⊕ E) ≃ (Slots q ⊕ E)}

omit [Fintype V] in
private theorem outgoingSlot (hF : ∀ x, endpointLinks src dst p q x (F x)) (x : Slots p) :
    ∃ a : E, F (.inl x) = .inr a ∧ x.1 = src a ∧ F (.inr a) ≠ .inr a := by
  have h := hF (.inl x)
  cases he : F (.inl x) with
  | inl y => rw [he] at h; exact h.elim
  | inr a =>
    rw [he] at h
    refine ⟨a,rfl,h,?_⟩
    intro ha
    have contra := F.injective (ha.trans he.symm)
    cases contra

omit [Fintype V] in
private theorem selectedOutgoing (hF : ∀ x, endpointLinks src dst p q x (F x)) (a : E)
    (ha : F (.inr a) ≠ .inr a) :
    ∃ x : Slots p, F (.inl x) = .inr a ∧ x.1 = src a := by
  have h := hF (F.symm (.inr a))
  rw [F.apply_symm_apply] at h
  cases he : F.symm (.inr a) with
  | inl x =>
    rw [he] at h
    exact ⟨x,(congrArg F he).symm.trans (F.apply_symm_apply _),h⟩
  | inr b =>
    rw [he] at h
    have hab : b = a := h
    subst b
    exact (ha ((congrArg F he).symm.trans (F.apply_symm_apply _))).elim

omit [Fintype V] in
private theorem selectedIncoming (hF : ∀ x, endpointLinks src dst p q x (F x)) (a : E)
    (ha : F (.inr a) ≠ .inr a) :
    ∃ y : Slots q, F (.inr a) = .inl y ∧ dst a = y.1 := by
  have h := hF (.inr a)
  cases he : F (.inr a) with
  | inl y =>
    rw [he] at h
    exact ⟨y,rfl,h⟩
  | inr b =>
    rw [he] at h
    have hab : a = b := h
    exact (ha (he.trans (congrArg Sum.inr hab.symm))).elim

omit [Fintype V] in
private theorem incomingSlot (hF : ∀ x, endpointLinks src dst p q x (F x)) (y : Slots q) :
    ∃ a : E, F (.inr a) = .inl y ∧ dst a = y.1 ∧ F (.inr a) ≠ .inr a := by
  have h := hF (F.symm (.inl y))
  rw [F.apply_symm_apply] at h
  cases he : F.symm (.inl y) with
  | inl x => rw [he] at h; exact h.elim
  | inr a =>
    have hFa := (congrArg F he).symm.trans (F.apply_symm_apply _)
    rw [he] at h
    refine ⟨a,hFa,h,?_⟩
    intro ha
    have contra := ha.symm.trans hFa
    cases contra

/-- Realize directed degree demands by a subset of labeled arcs. Distinct
labels may have the same endpoints. -/
theorem exists_labeled_arcs_of_capacity_cuts [Fintype E] (src dst : E → V)
    (p q : V → ℕ) (hBalance : (∑ v,p v) = ∑ v,q v)
    (hCuts : ∀ S T : Finset V, (∑ v ∈ S,p v) ≤ (∑ v ∈ T,q v) +
      ((univ : Finset E).filter (fun a => src a ∈ S ∧ dst a ∉ T)).card) :
    ∃ H : Finset E, (∀ v, (H.filter (fun a => src a = v)).card = p v) ∧
      ∀ v, (H.filter (fun a => dst a = v)).card = q v := by
  obtain ⟨F,hF⟩ := exists_endpoint_slot_matching src dst p q hBalance hCuts
  let H := univ.filter (fun a : E => F (.inr a) ≠ .inr a)
  refine ⟨H,?_,?_⟩
  · intro v
    choose a ha hv hs using outgoingSlot hF
    suffices hc : (univ : Finset (Fin (p v))).card = (H.filter (fun a => src a = v)).card by
      simpa only [card_univ,Fintype.card_fin] using hc.symm
    apply card_bij (fun i _ => a ⟨v,i⟩)
    · intro i _
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hs _⟩,(hv ⟨v,i⟩).symm⟩
    · intro i _ j _ he
      have hij := Sum.inl.inj (F.injective ((ha ⟨v,i⟩).trans ((congrArg Sum.inr he).trans (ha ⟨v,j⟩).symm)))
      cases hij
      rfl
    · intro b hb
      obtain ⟨hH,hSrc⟩ := mem_filter.mp hb
      obtain ⟨⟨w,i⟩,hi,hw⟩ := selectedOutgoing hF b (mem_filter.mp hH).2
      have he : w = v := hw.trans hSrc
      subst w
      exact ⟨i,mem_univ _,Sum.inr.inj ((ha ⟨v,i⟩).symm.trans hi)⟩
  · intro v
    choose a ha hv hs using incomingSlot hF
    suffices hc : (univ : Finset (Fin (q v))).card = (H.filter (fun a => dst a = v)).card by
      simpa only [card_univ,Fintype.card_fin] using hc.symm
    apply card_bij (fun i _ => a ⟨v,i⟩)
    · intro i _
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hs _⟩,hv ⟨v,i⟩⟩
    · intro i _ j _ he
      have hij := Sum.inl.inj ((ha ⟨v,i⟩).symm.trans
        ((congrArg (fun b => F (.inr b)) he).trans (ha ⟨v,j⟩)))
      cases hij
      rfl
    · intro b hb
      obtain ⟨hH,hDst⟩ := mem_filter.mp hb
      obtain ⟨⟨w,i⟩,hi,hw⟩ := selectedIncoming hF b (mem_filter.mp hH).2
      have he : w = v := hw.symm.trans hDst
      subst w
      exact ⟨i,mem_univ _,Sum.inr.inj (F.injective ((ha ⟨v,i⟩).trans hi.symm))⟩

/-- The capacity inequalities are sufficient for prescribed outdegrees and
indegrees in a spanning subdigraph. -/
theorem exists_subdigraph_of_capacity_cuts (D : Digraph V) (p q : V → ℕ)
    (hBalance : (∑ v,p v) = ∑ v,q v)
    (hCuts : ∀ S T : Finset V, (∑ v ∈ S,p v) ≤ (∑ v ∈ T,q v)+incidences D S Tᶜ) :
    ∃ H : Digraph V, H ≤ D ∧ (∀ v, outDegree H v = p v) ∧ (∀ v, inDegree H v = q v) := by
  classical
  obtain ⟨F,hF⟩ := exists_arc_slot_matching D p q hBalance hCuts
  let H : Digraph V := ⟨fun v w => ∃ a : Arc D, a.val = (v,w) ∧ F (.inr a) ≠ .inr a⟩
  refine ⟨H,?_,?_,?_⟩
  · intro v w h
    obtain ⟨a,ha,_⟩ := h
    have hadj := a.prop
    rw [ha] at hadj
    exact hadj
  · intro v
    letI : DecidablePred (H.Adj v) := Classical.decPred _
    choose a ha hv hs using outgoingSlot (src := fun a : Arc D => a.val.1) (dst := fun a : Arc D => a.val.2) hF
    suffices hf : (univ : Finset (Fin (p v))).card = (@Finset.filter V (H.Adj v) (Classical.decPred _) univ).card by
      simpa [outDegree] using hf.symm
    apply card_bij (fun i _ => (a ⟨v,i⟩).val.2)
    · intro i _
      exact mem_filter.mpr ⟨mem_univ _,a ⟨v,i⟩,Prod.ext (hv _).symm rfl,hs _⟩
    · intro i _ j _ he
      have hab : a ⟨v,i⟩ = a ⟨v,j⟩ :=
        Subtype.ext (Prod.ext ((hv ⟨v,i⟩).symm.trans (hv ⟨v,j⟩)) he)
      have hij := Sum.inl.inj (F.injective ((ha _).trans ((congrArg Sum.inr hab).trans (ha _).symm)))
      cases hij
      rfl
    · intro w hw
      obtain ⟨b,hb,hsel⟩ := (mem_filter.mp hw).2
      obtain ⟨⟨u,i⟩,hu,hv'⟩ := selectedOutgoing (src := fun a : Arc D => a.val.1) (dst := fun a : Arc D => a.val.2) hF b hsel
      have he : u = v := hv'.trans (congrArg Prod.fst hb)
      subst u
      have hab : a ⟨v,i⟩ = b := Sum.inr.inj ((ha _).symm.trans hu)
      exact ⟨i,mem_univ _,(congrArg (fun e : Arc D => e.val.2) hab).trans (congrArg Prod.snd hb)⟩
  · intro v
    letI : DecidablePred (fun w => H.Adj w v) := Classical.decPred _
    choose a ha hv hs using incomingSlot (src := fun a : Arc D => a.val.1) (dst := fun a : Arc D => a.val.2) hF
    suffices hf : (univ : Finset (Fin (q v))).card = (@Finset.filter V (fun w => H.Adj w v) (Classical.decPred _) univ).card by
      simpa [inDegree,inNeighbours] using hf.symm
    apply card_bij (fun i _ => (a ⟨v,i⟩).val.1)
    · intro i _
      exact mem_filter.mpr ⟨mem_univ _,a ⟨v,i⟩,Prod.ext rfl (hv _),hs _⟩
    · intro i _ j _ he
      have hab : a ⟨v,i⟩ = a ⟨v,j⟩ :=
        Subtype.ext (Prod.ext he ((hv ⟨v,i⟩).trans (hv ⟨v,j⟩).symm))
      have hij := Sum.inl.inj ((ha _).symm.trans ((congrArg (fun e => F (.inr e)) hab).trans (ha _)))
      cases hij
      rfl
    · intro w hw
      obtain ⟨b,hb,hsel⟩ := (mem_filter.mp hw).2
      obtain ⟨⟨u,i⟩,hu,hv'⟩ := selectedIncoming (src := fun a : Arc D => a.val.1) (dst := fun a : Arc D => a.val.2) hF b hsel
      have he : u = v := hv'.symm.trans (congrArg Prod.snd hb)
      subst u
      have hab : a ⟨v,i⟩ = b := Sum.inr.inj (F.injective ((ha _).trans hu.symm))
      exact ⟨i,mem_univ _,(congrArg (fun e : Arc D => e.val.1) hab).trans (congrArg Prod.fst hb)⟩

end OverfullWork.DirectedDemandHall
