module

public import OverfullWork.KuhnOsthusPathPartitionSizes
public import OverfullWork.KuhnOsthusMarkedTours
public import OverfullWork.InducedDigraphSampling

@[expose] public section


/-! The basic path system in Kühn–Osthus Lemma 8.3 and the
contraction used by Observation 7.4. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function
open DirectedDemandHall (Arc)
open scoped Classical
variable {V : Type*} [Fintype V]

/-- On the ordinary vertices, replace each prescribed two-edge path
through an exceptional vertex by a single shortcut. -/
def basicExceptionalPathSystem (Q : Digraph V) (Z : Finset V) : Digraph ↥Zᶜ :=
  ⟨fun x y => Q.Adj x.val y.val ∨ ∃ z ∈ Z, Q.Adj x.val z ∧ Q.Adj z y.val⟩

private theorem basic_edge_has_first {Q : Digraph V} {Z : Finset V} {x y : ↥Zᶜ}
    (h : (basicExceptionalPathSystem Q Z).Adj x y) : ∃ w, Q.Adj x.val w := by
  rcases h with h | ⟨z,_,hz,_⟩
  · exact ⟨y.val,h⟩
  · exact ⟨z,hz⟩

private theorem basic_edge_has_last {Q : Digraph V} {Z : Finset V} {x y : ↥Zᶜ}
    (h : (basicExceptionalPathSystem Q Z).Adj x y) : ∃ w, Q.Adj w y.val := by
  rcases h with h | ⟨z,_,_,hz⟩
  · exact ⟨x.val,h⟩
  · exact ⟨z,hz⟩

/-- Contracting the covered exceptional vertices keeps exactly the
ordinary source and target slots of the original system. -/
theorem basic_exceptional_endpoint_slots (D : Digraph V) (Z : Finset V)
    (hZ : CoversExceptional D Z) (hNo : ∀ x y, D.Adj x y → x ∈ Z → y ∉ Z) (v : ↥Zᶜ) :
    ((∃ w, (basicExceptionalPathSystem D Z).Adj v w) ↔ ∃ w, D.Adj v.val w) ∧
    ((∃ w, (basicExceptionalPathSystem D Z).Adj w v) ↔ ∃ w, D.Adj w v.val) := by
  constructor
  · constructor
    · rintro ⟨w,hw⟩
      exact basic_edge_has_first hw
    · rintro ⟨w,hw⟩
      by_cases hz : w ∈ Z
      · obtain ⟨u,hu⟩ := (hZ w hz).1
        exact ⟨⟨u,mem_compl.mpr (hNo w u hu hz)⟩,Or.inr ⟨w,hz,hw,hu⟩⟩
      · exact ⟨⟨w,mem_compl.mpr hz⟩,Or.inl hw⟩
  · constructor
    · rintro ⟨w,hw⟩
      exact basic_edge_has_last hw
    · rintro ⟨w,hw⟩
      by_cases hz : w ∈ Z
      · obtain ⟨u,hu⟩ := (hZ w hz).2
        have hu' : u ∉ Z := fun h => hNo u w hu h hz
        exact ⟨⟨u,mem_compl.mpr hu'⟩,Or.inr ⟨w,hz,hu,hw⟩⟩
      · exact ⟨⟨w,mem_compl.mpr hz⟩,Or.inl hw⟩

theorem basicExceptionalPathSystem.isDirectedPathSystem
    {Q : Digraph V} {Z : Finset V} (hQ : IsDirectedPathSystem Q) :
    IsDirectedPathSystem (basicExceptionalPathSystem Q Z) := by
  constructor
  · intro x hCycle
    have hTrans {x y : ↥Zᶜ} (h : Relation.TransGen (basicExceptionalPathSystem Q Z).Adj x y) :
        Relation.TransGen Q.Adj x.val y.val := by
      have hStep {a b : ↥Zᶜ} (he : (basicExceptionalPathSystem Q Z).Adj a b) :
          Relation.TransGen Q.Adj a.val b.val := by
        rcases he with he | ⟨z,_,h₁,h₂⟩
        · exact .single he
        · exact .tail (.single h₁) h₂
      induction h with
      | single he => exact hStep he
      | tail _ he ih => exact ih.trans (hStep he)
    exact hQ.acyclic x.val (hTrans hCycle)
  · intro x y w hxy hxw
    apply Subtype.ext
    rcases hxy with hxy | ⟨a,ha,hxa,hay⟩ <;> rcases hxw with hxw | ⟨b,hb,hxb,hbw⟩
    · exact hQ.out_unique hxy hxw
    · exact (mem_compl.mp y.prop ((hQ.out_unique hxy hxb).symm ▸ hb)).elim
    · exact (mem_compl.mp w.prop ((hQ.out_unique hxa hxw) ▸ ha)).elim
    · exact hQ.out_unique hay ((hQ.out_unique hxa hxb).symm ▸ hbw)
  · intro y x w hxy hwy
    apply Subtype.ext
    rcases hxy with hxy | ⟨a,ha,hxa,hay⟩ <;> rcases hwy with hwy | ⟨b,hb,hwb,hby⟩
    · exact hQ.in_unique hxy hwy
    · exact (mem_compl.mp x.prop ((hQ.in_unique hxy hby).symm ▸ hb)).elim
    · exact (mem_compl.mp w.prop ((hQ.in_unique hay hwy) ▸ ha)).elim
    · exact hQ.in_unique hxa ((hQ.in_unique hay hby).symm ▸ hwb)

/-- Contraction keeps all ordinary styles and can only decrease the
number of prescribed arcs. -/
theorem basicExceptionalPathSystem.bounds {Q : Digraph V} {Z : Finset V}
    {J : Type*} {label : V → J} {S : Finset J}
    (hQ : IsDirectedPathSystem Q) (hStyle : SupportedByStyles label Z S Q) :
    SupportedByStyles (fun v : ↥Zᶜ => label v.val) ∅ S (basicExceptionalPathSystem Q Z) ∧
      Fintype.card (Arc (basicExceptionalPathSystem Q Z)) ≤ Fintype.card (Arc Q) := by
  constructor
  · intro x _ hx
    apply hStyle x.val (mem_compl.mp x.prop)
    rcases hx with ⟨y,hy⟩ | ⟨y,hy⟩
    · exact Or.inl (basic_edge_has_first hy)
    · exact Or.inr (basic_edge_has_last hy)
  · let B := basicExceptionalPathSystem Q Z
    have hFirst (e : Arc B) : ∃ w, Q.Adj e.val.1.val w := basic_edge_has_first e.prop
    choose w hw using hFirst
    let f (e : Arc B) : Arc Q := ⟨(e.val.1.val,w e),hw e⟩
    apply Fintype.card_le_of_injective f
    intro e g heq
    have hSrc : e.val.1 = g.val.1 :=
      Subtype.ext (congrArg (fun a : Arc Q => a.val.1) heq)
    have hOther : B.Adj e.val.1 g.val.2 := hSrc.symm ▸ g.prop
    exact Subtype.ext (Prod.ext hSrc ((basicExceptionalPathSystem.isDirectedPathSystem hQ).out_unique
      e.prop hOther))

/-- Expand all components of a 1-factor. The intervals between
consecutive ordinary vertices have length one or two, so expansion
preserves the orbit partition on the ordinary vertices. -/
theorem expand_basic_exceptional_factor_with_segments
    (Q R : Digraph V) (Z : Finset V) (hQ : IsDirectedPathSystem Q)
    (hZ : CoversExceptional Q Z)
    (hNo : ∀ x y, Q.Adj x y → x ∈ Z → y ∉ Z)
    (σ : Equiv.Perm ↥Zᶜ)
    (hKeep : ∀ x y, (basicExceptionalPathSystem Q Z).Adj x y → σ x = y)
    (hEdge : ∀ x, ((basicExceptionalPathSystem Q Z) ⊔
      InducedDigraphSampling.induced R Zᶜ).Adj x (σ x)) :
    ∃ ρ : Equiv.Perm V,
      (∀ x y, Q.Adj x y → ρ x = y) ∧
      (∀ x, (Q ⊔ R).Adj x (ρ x)) ∧
      (∀ a b : ↥Zᶜ, ρ a.val = b.val → σ a = b) ∧
      Nonempty (MarkedCycleSegments ρ (Embedding.subtype (· ∈ Zᶜ)) σ) := by
  let A := ↥Zᶜ
  let F (x y : V) : Prop := ((x ∈ Z ∨ y ∈ Z) ∧ Q.Adj x y) ∨
    ∃ a b : A, a.val = x ∧ b.val = y ∧ σ a = b ∧ ∀ z ∈ Z, ¬ Q.Adj x z
  have hOut (x : V) : ∃ y, F x y := by
    by_cases hx : x ∈ Z
    · obtain ⟨y,hy⟩ := (hZ x hx).1
      exact ⟨y,Or.inl ⟨Or.inl hx,hy⟩⟩
    · by_cases hExc : ∃ z ∈ Z, Q.Adj x z
      · obtain ⟨z,hz,hxz⟩ := hExc
        exact ⟨z,Or.inl ⟨Or.inr hz,hxz⟩⟩
      · let a : A := ⟨x,mem_compl.mpr hx⟩
        exact ⟨(σ a).val,Or.inr ⟨a,σ a,rfl,rfl,rfl,fun z hz he => hExc ⟨z,hz,he⟩⟩⟩
  have hOutUnique {x y w : V} (hy : F x y) (hw : F x w) : y = w := by
    rcases hy with ⟨hzy,hy⟩ | ⟨a,b,ha,hb,he,hno⟩ <;>
      rcases hw with ⟨hzw,hw⟩ | ⟨c,d,hc,hd,hf,hno'⟩
    · exact hQ.out_unique hy hw
    · exact (hzy.elim (fun hx => mem_compl.mp c.prop (hc.symm ▸ hx))
        (fun hyz => hno' y hyz hy)).elim
    · exact (hzw.elim (fun hx => mem_compl.mp a.prop (ha.symm ▸ hx))
        (fun hwz => hno w hwz hw)).elim
    · have hac : a = c := Subtype.ext (ha.trans hc.symm)
      exact hb.symm.trans ((congrArg Subtype.val (he.symm.trans ((congrArg σ hac).trans hf))).trans hd)
  have hMixed {x y w : V} (hy : x ∈ Z ∨ y ∈ Z) (hxy : Q.Adj x y)
      (c d : A) (hc : c.val = w) (hd : d.val = y) (hcd : σ c = d)
      (hno : ∀ z ∈ Z, ¬ Q.Adj w z) : False := by
    have hx : x ∈ Z := hy.resolve_right (fun h => mem_compl.mp d.prop (hd.symm ▸ h))
    obtain ⟨p,hp⟩ := (hZ x hx).2
    have hp' : p ∉ Z := fun hz => hNo p x hp hz hx
    let a : A := ⟨p,mem_compl.mpr hp'⟩
    have hArc : (basicExceptionalPathSystem Q Z).Adj a d :=
      Or.inr ⟨x,hx,hp,hd.symm ▸ hxy⟩
    have hEq : a = c := σ.injective ((hKeep a d hArc).trans hcd.symm)
    have hPW : p = w := (congrArg Subtype.val hEq).trans hc
    exact hno x hx (hPW ▸ hp)
  have hInUnique {x y w : V} (hx : F x y) (hw : F w y) : x = w := by
    rcases hx with ⟨hzx,hx⟩ | ⟨a,b,ha,hb,he,hno⟩ <;>
      rcases hw with ⟨hzw,hw⟩ | ⟨c,d,hc,hd,hf,hno'⟩
    · exact hQ.in_unique hx hw
    · exact (hMixed hzx hx c d hc hd hf hno').elim
    · exact (hMixed hzw hw a b ha hb he hno).elim
    · have hbd : b = d := Subtype.ext (hb.trans hd.symm)
      have hac : a = c := σ.injective (he.trans (hbd.trans hf.symm))
      exact ha.symm.trans ((congrArg Subtype.val hac).trans hc)
  choose f hf using hOut
  have hInject : Function.Injective f := fun x y he => hInUnique (hf x) (he.symm ▸ hf y)
  let ρ : Equiv.Perm V := Equiv.ofBijective f ⟨hInject,Finite.surjective_of_injective hInject⟩
  have hρ (x : V) : F x (ρ x) := hf x
  have hGet {x y : V} (h : F x y) : ρ x = y := hOutUnique (hρ x) h
  have hPreserve (x y : V) (h : Q.Adj x y) : ρ x = y := by
    by_cases hz : x ∈ Z ∨ y ∈ Z
    · exact hGet (Or.inl ⟨hz,h⟩)
    · let a : A := ⟨x,mem_compl.mpr (fun hx => hz (Or.inl hx))⟩
      let b : A := ⟨y,mem_compl.mpr (fun hy => hz (Or.inr hy))⟩
      exact hGet (Or.inr ⟨a,b,rfl,rfl,hKeep a b (Or.inl h),fun z hz' he =>
        hz (Or.inr ((hQ.out_unique h he).symm ▸ hz'))⟩)
  have hSupport (x : V) : (Q ⊔ R).Adj x (ρ x) := by
    rcases hρ x with ⟨_,h⟩ | ⟨a,b,ha,hb,he,hno⟩
    · exact Or.inl h
    · have h := hEdge a
      rw [he] at h
      rcases (Digraph.sup_adj _ _ _ _).mp h with hB | hR
      · rcases hB with hQ' | ⟨z,hz,haz,_⟩
        · have hArc : Q.Adj x b.val := ha ▸ hQ'
          exact Or.inl (hb ▸ hArc)
        · exact (hno z hz (ha ▸ haz)).elim
      · have hArc : R.Adj x b.val := ha ▸ hR
        exact Or.inr (hb ▸ hArc)
  have hProj (a b : A) (he : ρ a.val = b.val) : σ a = b := by
    have h : F a.val b.val := he ▸ hρ a.val
    rcases h with ⟨ha | hb,_⟩ | ⟨p,q,hp,hq,hpq,_⟩
    · exact (mem_compl.mp a.prop ha).elim
    · exact (mem_compl.mp b.prop hb).elim
    · have hpa : p = a := Subtype.ext hp
      have hqb : q = b := Subtype.ext hq
      rwa [hpa,hqb] at hpq
  let span (a : A) := if ∃ z ∈ Z, Q.Adj a.val z then 2 else 1
  have hPos (a : A) : 0 < span a := by unfold span; split <;> decide
  refine ⟨ρ,hPreserve,hSupport,hProj,⟨span,hPos,?_,?_,?_⟩⟩
  · intro a
    change (ρ : V → V)^[span a] a.val = (σ a).val
    by_cases hExc : ∃ z ∈ Z, Q.Adj a.val z
    · obtain ⟨z,hz,haz⟩ := hExc
      obtain ⟨y,hy⟩ := (hZ z hz).1
      let b : A := ⟨y,mem_compl.mpr (hNo z y hy hz)⟩
      have hσ : σ a = b := hKeep a b (Or.inr ⟨z,hz,haz,hy⟩)
      have hLen : span a = 2 := if_pos ⟨z,hz,haz⟩
      rw [hLen,iterate_succ_apply' (ρ : V → V) 1 a.val,iterate_one,hPreserve _ _ haz,
        hPreserve _ _ hy,hσ]
    · have hLen : span a = 1 := if_neg hExc
      rw [hLen,iterate_one]
      exact hGet (Or.inr ⟨a,σ a,rfl,rfl,rfl,fun z hz he => hExc ⟨z,hz,he⟩⟩)
  · intro a d hd hdSpan b
    change (ρ : V → V)^[d] a.val ≠ b.val
    by_cases hExc : ∃ z ∈ Z, Q.Adj a.val z
    · have hLen : span a = 2 := if_pos hExc
      obtain ⟨z,hz,haz⟩ := hExc
      have he : d = 1 := by omega
      rw [he,iterate_one,hPreserve _ _ haz]
      exact fun h => mem_compl.mp b.prop (h ▸ hz)
    · have hLen : span a = 1 := if_neg hExc
      omega
  · intro v
    by_cases hv : v ∈ Z
    · obtain ⟨p,hp⟩ := (hZ v hv).2
      let a : A := ⟨p,mem_compl.mpr (fun hz => hNo p v hp hz hv)⟩
      have hLen : span a = 2 := if_pos ⟨v,hv,hp⟩
      refine ⟨a,1,by omega,?_⟩
      change (ρ : V → V)^[1] p = v
      rw [iterate_one,hPreserve _ _ hp]
    · let a : A := ⟨v,mem_compl.mpr hv⟩
      exact ⟨a,0,hPos a,rfl⟩

/-- Expanding a marked bicycle preserves the two components and
leaves the two ordinary marks in distinct cycles. -/
theorem expand_basic_exceptional_marked_bicycle
    (Q R : Digraph V) (Z : Finset V) (hQ : IsDirectedPathSystem Q)
    (hZ : CoversExceptional Q Z)
    (hNo : ∀ x y, Q.Adj x y → x ∈ Z → y ∉ Z)
    (σ : Equiv.Perm ↥Zᶜ) (a b : ↥Zᶜ) (hB : MarkedBicycle σ a b)
    (hKeep : ∀ x y, (basicExceptionalPathSystem Q Z).Adj x y → σ x = y)
    (hEdge : ∀ x, ((basicExceptionalPathSystem Q Z) ⊔
      InducedDigraphSampling.induced R Zᶜ).Adj x (σ x)) :
    ∃ ρ : Equiv.Perm V, MarkedBicycle ρ a.val b.val ∧
      (∀ x y, Q.Adj x y → ρ x = y) ∧
      (∀ x, (Q ⊔ R).Adj x (ρ x)) ∧
      ∀ x y : ↥Zᶜ, ρ x.val = y.val → σ x = y := by
  obtain ⟨ρ,hPreserve,hSupport,hProj,⟨H⟩⟩ :=
    expand_basic_exceptional_factor_with_segments Q R Z hQ hZ hNo σ hKeep hEdge
  refine ⟨ρ,⟨fun h => hB.1 ((H.sameCycle a b).mp h),?_⟩,hPreserve,hSupport,hProj⟩
  intro v
  obtain ⟨x,hx⟩ := H.cycle_meets_mark v
  exact (hB.2 x).imp (fun h => ((H.sameCycle a x).mpr h).trans hx)
    (fun h => ((H.sameCycle b x).mpr h).trans hx)

/-- Expand a Hamilton cycle and retain the projection of ordinary
arcs that is used to prove disjointness between two expanded factors. -/
theorem expand_basic_exceptional_cycle_with_projection
    (Q R : Digraph V) (Z : Finset V) (hQ : IsDirectedPathSystem Q)
    (hZ : CoversExceptional Q Z)
    (hNo : ∀ x y, Q.Adj x y → x ∈ Z → y ∉ Z)
    (σ : Equiv.Perm ↥Zᶜ) (hCycle : HasSpanningCycle (fun x y => σ x = y))
    (hKeep : ∀ x y, (basicExceptionalPathSystem Q Z).Adj x y → σ x = y)
    (hEdge : ∀ x, ((basicExceptionalPathSystem Q Z) ⊔
      InducedDigraphSampling.induced R Zᶜ).Adj x (σ x)) :
    ∃ ρ : Equiv.Perm V, HasSpanningCycle (fun x y => ρ x = y) ∧
      (∀ x y, Q.Adj x y → ρ x = y) ∧
      (∀ x, (Q ⊔ R).Adj x (ρ x)) ∧
      ∀ a b : ↥Zᶜ, ρ a.val = b.val → σ a = b := by
  obtain ⟨ρ,hPreserve,hSupport,hProj,⟨H⟩⟩ :=
    expand_basic_exceptional_factor_with_segments Q R Z hQ hZ hNo σ hKeep hEdge
  obtain ⟨T,x,_,hAll,hHead,hChain⟩ := hCycle
  have hOrd (w : ↥Zᶜ) : σ.SameCycle x w := by
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp (hAll w)
    have hFirst (n : ℕ) (hn : n < T.length) : σ.SameCycle x T[n] := by
      induction n with
      | zero =>
        have hEq : T[0] = x := Option.some.inj ((List.getElem?_eq_getElem hn).symm.trans
          (List.head?_eq_getElem?.symm.trans hHead))
        rw [hEq]
      | succ n ih =>
        have hChain' : T.IsChain (fun a b => σ a = b) := hChain.prefix (List.prefix_append T [x])
        have hNext := List.isChain_iff_getElem.mp hChain' n hn
        exact (ih (Nat.lt_of_succ_lt hn)).trans
          (hNext ▸ (Equiv.Perm.SameCycle.refl σ T[n]).apply_right)
    exact he ▸ hFirst i hi
  refine ⟨ρ,spanning_cycle_of_single_orbit ρ x.val ?_,hPreserve,hSupport,hProj⟩
  intro v
  obtain ⟨a,ha⟩ := H.cycle_meets_mark v
  exact ((H.sameCycle x a).mpr (hOrd a)).trans ha

/-- Lift a Hamilton cycle on the ordinary vertices through a covered
exceptional path system. -/
theorem expand_basic_exceptional_cycle
    (Q R : Digraph V) (Z : Finset V) (hQ : IsDirectedPathSystem Q)
    (hZ : CoversExceptional Q Z)
    (hNo : ∀ x y, Q.Adj x y → x ∈ Z → y ∉ Z)
    (σ : Equiv.Perm ↥Zᶜ) (hCycle : HasSpanningCycle (fun x y => σ x = y))
    (hKeep : ∀ x y, (basicExceptionalPathSystem Q Z).Adj x y → σ x = y)
    (hEdge : ∀ x, ((basicExceptionalPathSystem Q Z) ⊔
      InducedDigraphSampling.induced R Zᶜ).Adj x (σ x)) :
    ∃ ρ : Equiv.Perm V, HasSpanningCycle (fun x y => ρ x = y) ∧
      (∀ x y, Q.Adj x y → ρ x = y) ∧
      ∀ x, (Q ⊔ R).Adj x (ρ x) := by
  obtain ⟨ρ,hC,hK,hE,_⟩ :=
    expand_basic_exceptional_cycle_with_projection Q R Z hQ hZ hNo σ hCycle hKeep hEdge
  exact ⟨ρ,hC,hK,hE⟩

end OverfullWork.DirectedRobustExpansion
