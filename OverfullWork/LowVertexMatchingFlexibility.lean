module

public import OverfullWork.LowVertexMatchingAbsorption

@[expose] public section


/-! # Strict Hall surplus and avoidance of one prescribed partner

Strict local degree comparison supplies one extra neighbour for every
nonempty left set, and hence an actual injection avoiding any one right
vertex. The critical low-vertex instance is proved from VAL. No acyclic
union of two matchings, linear-forest completion, or Hamilton extension
is asserted by this module.
-/
namespace OverfullWork.LowVertexMatchingFlexibility
open SimpleGraph Finset Overfull
open LowVertexMatchingAbsorption
open scoped Classical
set_option maxHeartbeats 4000000

/-- Strict degree comparison strengthens Hall by one actual right vertex. -/
theorem strict_hall_of_degree_comparison {A B : Type*} [Fintype A] [Fintype B]
    (r : A → B → Prop) [DecidableRel r]
    (hpos : ∀a,0<(univ.filter (r a)).card)
    (hdeg : ∀a b,r a b → (univ.filter (fun a => r a b)).card<(univ.filter (r a)).card)
    (S : Finset A) (hS : S.Nonempty) :
    S.card+1≤(univ.filter (fun b => ∃a∈S,r a b)).card := by
  classical
  let da := fun a => (univ.filter (r a)).card
  let db := fun b => (univ.filter (fun a => r a b)).card
  let T := univ.filter (fun b => ∃a∈S,r a b)
  let w : A → B → ℝ := fun a b => if r a b then 1/(da a:ℝ) else 0
  have hrow : ∀a∈S,(∑b∈T,w a b)=1 := by
    intro a ha
    have hsub : univ.filter (r a)⊆T := by
      intro b hb
      exact mem_filter.mpr ⟨mem_univ _,a,ha,(mem_filter.mp hb).2⟩
    have heq : T.filter (r a)=univ.filter (r a) := by
      ext b
      simp only [mem_filter,mem_univ,true_and]
      exact ⟨fun h => h.2,fun h => ⟨hsub (mem_filter.mpr ⟨mem_univ _,h⟩),h⟩⟩
    have hda : (0:ℝ)<(da a:ℝ) := by exact_mod_cast hpos a
    dsimp [w]
    rw [←sum_filter,heq,sum_const,nsmul_eq_mul]
    change (da a:ℝ)*(1/(da a:ℝ))=1
    exact mul_one_div_cancel (ne_of_gt hda)
  have hcol : ∀b∈T,(∑a∈S,w a b)<1 := by
    intro b hb
    obtain ⟨a,ha,hab⟩ := (mem_filter.mp hb).2
    have hdbNat : 0<db b := card_pos.mpr ⟨a,mem_filter.mpr ⟨mem_univ _,hab⟩⟩
    have hdb : (0:ℝ)<(db b:ℝ) := by exact_mod_cast hdbNat
    have hweight : ∀a∈S,w a b≤(if r a b then 1/(db b:ℝ) else 0) := by
      intro a _
      dsimp [w]
      split_ifs with hab
      · have hh : (db b:ℝ)<(da a:ℝ) := by exact_mod_cast hdeg a b hab
        exact (one_div_lt_one_div_of_lt hdb hh).le
      · exact le_rfl
    have hstrict : w a b<(if r a b then 1/(db b:ℝ) else 0) := by
      dsimp [w]
      simp only [if_pos hab]
      have hh : (db b:ℝ)<(da a:ℝ) := by exact_mod_cast hdeg a b hab
      exact one_div_lt_one_div_of_lt hdb hh
    have hs := sum_lt_sum hweight ⟨a,ha,hstrict⟩
    have heq : (∑a∈S,if r a b then 1/(db b:ℝ) else 0)=
        ((S.filter fun a => r a b).card:ℝ)*(1/(db b:ℝ)) := by
      rw [←sum_filter,sum_const,nsmul_eq_mul]
    rw [heq] at hs
    have hcnt : (S.filter fun a => r a b).card≤db b := card_le_card
      (fun a ha => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp ha).2⟩)
    have hcntR : ((S.filter fun a => r a b).card:ℝ)≤(db b:ℝ) := by exact_mod_cast hcnt
    exact hs.trans_le ((mul_le_mul_of_nonneg_right hcntR (by positivity)).trans_eq
      (mul_one_div_cancel (ne_of_gt hdb)))
  have hT : T.Nonempty := by
    obtain ⟨a,ha⟩ := hS
    obtain ⟨b,hb⟩ := card_pos.mp (hpos a)
    exact ⟨b,mem_filter.mpr ⟨mem_univ _,a,ha,(mem_filter.mp hb).2⟩⟩
  have hsum : (S.card:ℝ)<(T.card:ℝ) := by
    obtain ⟨b,hb⟩ := hT
    calc
      _ = ∑a∈S,(∑b∈T,w a b) := by rw [sum_congr rfl hrow];simp
      _ = ∑b∈T,(∑a∈S,w a b) := sum_comm
      _ < ∑_b∈T,(1:ℝ) := sum_lt_sum (fun b hb => (hcol b hb).le) ⟨b,hb,hcol b hb⟩
      _ = _ := by simp
  have hn : S.card<T.card := by exact_mod_cast hsum
  exact hn

/-- Every strict-Hall relation has a genuine transversal avoiding any
one prescribed right vertex. Only one forbidden vertex is asserted. -/
theorem exists_injection_avoiding_vertex_of_strict_hall
    {A B : Type*} [Fintype A] [Fintype B]
    (r : A → B → Prop) [DecidableRel r]
    (hstrict : ∀S:Finset A,S.Nonempty →
      S.card+1≤(univ.filter (fun b => ∃a∈S,r a b)).card) (b₀ : B) :
    ∃f : A → B,Function.Injective f ∧ (∀a,r a (f a)) ∧ ∀a,f a≠b₀ := by
  classical
  let T := (univ : Finset B).erase b₀
  let r' := fun (a:A) (b:T) => r a b.val
  have hall : ∀S:Finset A,S.card≤(univ.filter fun b:T => ∃a∈S,r' a b).card := by
    intro S
    by_cases hS : S.Nonempty
    · let N := univ.filter (fun b => ∃a∈S,r a b)
      have hs := hstrict S hS
      have hcast := DenseHall.subtype_filter_card T (fun b => ∃a∈S,r a b)
      have heq : T.filter (fun b => ∃a∈S,r a b)=N.erase b₀ := by
        ext b
        simp only [T,N,mem_filter,mem_erase,mem_univ,true_and]
        tauto
      have hcount : (univ.filter fun b:T => ∃a∈S,r' a b).card=(N.erase b₀).card := by
        calc
          _=(T.filter (fun b => ∃a∈S,r a b)).card := by
            convert hcast using 1 <;> congr 1 <;> ext b <;> simp [r']
          _=_ := congrArg Finset.card heq
      rw [hcount]
      by_cases hb : b₀∈N
      · rw [card_erase_of_mem hb]
        change S.card+1≤N.card at hs
        omega
      · rw [erase_eq_of_notMem hb]
        exact (Nat.le_succ _).trans hs
    · have he : S=∅ := not_nonempty_iff_eq_empty.mp hS
      simp [he]
  obtain ⟨f,hf,hfr⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective r').mp hall
  refine ⟨fun a => (f a).val,fun a b he => hf (Subtype.ext he),hfr,?_⟩
  intro a
  exact (mem_erase.mp (f a).property).1

/-- The strict local comparison constructs the avoiding injection; no
Hall condition or selected function is an input. -/
theorem exists_injection_avoiding_vertex_of_strict_degree_comparison
    {A B : Type*} [Fintype A] [Fintype B]
    (r : A → B → Prop) [DecidableRel r]
    (hpos : ∀a,0<(univ.filter (r a)).card)
    (hdeg : ∀a b,r a b → (univ.filter (fun a => r a b)).card<(univ.filter (r a)).card)
    (b₀ : B) :
    ∃f : A → B,Function.Injective f ∧ (∀a,r a (f a)) ∧ ∀a,f a≠b₀ :=
  exists_injection_avoiding_vertex_of_strict_hall r
    (strict_hall_of_degree_comparison r hpos hdeg) b₀

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Criticality proves the strict comparison for the actual low-neighbour
relation across its complementary vertex cut. -/
theorem critical_low_strict_degree_comparison (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcrit : IsDeltaCritical G) :
    (∀a:lowVertices G,
      0<(univ.filter fun b:↥((lowVertices G)ᶜ : Finset V) => G.Adj a.val b.val).card) ∧
    ∀(a:lowVertices G)(b:↥((lowVertices G)ᶜ : Finset V)),G.Adj a.val b.val →
      (univ.filter fun a':lowVertices G => G.Adj a'.val b.val).card<
        (univ.filter fun b':↥((lowVertices G)ᶜ : Finset V) => G.Adj a.val b'.val).card := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun u v => Classical.propDecidable (G.Adj u v)))
  let W := lowVertices G
  obtain ⟨a,b,hab⟩ := MaximumCoreTwo.exists_adj_of_not_colorable G hcrit.2.1
  have hactive : ∀w,0<G.degree w := by
    intro w
    exact (G.degree_pos_iff_exists_adj w).mpr
      (MaximumCoreTwo.exists_adj_of_connected hcrit.1 hab w)
  have hind : ∀u∈W,∀v∈W,¬G.Adj u v := by
    intro u hu v hv huv
    have hsum := Overfull.deg_add hcrit huv
    have huD := (mem_filter.mp hu).2
    have hvD := (mem_filter.mp hv).2
    omega
  have hrow : ∀a:W,(univ.filter fun b:↥(Wᶜ : Finset V) => G.Adj a.val b.val).card=G.degree a.val := by
    intro a
    rw [DenseHall.subtype_filter_card,←card_neighborFinset_eq_degree]
    congr 1
    ext b
    simp only [mem_filter,mem_compl,mem_neighborFinset]
    exact ⟨fun h => h.2,fun h => ⟨fun hb => hind a.val a.property b hb h,h⟩⟩
  have hcol : ∀b:↥(Wᶜ : Finset V),(univ.filter fun a:W => G.Adj a.val b.val).card=
      ((G.neighborFinset b.val).filter fun z => z∈W).card := by
    intro b
    have hcast := DenseHall.subtype_filter_card W (fun a => G.Adj a b.val)
    calc
      _ = (W.filter fun a => G.Adj a b.val).card := by
        convert hcast using 1
      _ = _ := by
        congr 1
        ext a
        simp only [mem_filter,mem_neighborFinset]
        exact ⟨fun h => ⟨h.2.symm,h.1⟩,fun h => ⟨h.2,h.1.symm⟩⟩
  constructor
  · intro a
    rw [hrow]
    exact hactive a.val
  · intro a b hab
    rw [hcol,hrow]
    exact low_vertex_Hall_property G hcrit a.property hab

/-- Every nonempty low-vertex subfamily has at least one more possible
partners outside the low set than its own cardinality. -/
theorem low_neighbour_strict_hall (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : IsDeltaCritical G) (S : Finset (lowVertices G)) (hS : S.Nonempty) :
    S.card+1≤(univ.filter fun b:↥((lowVertices G)ᶜ : Finset V) =>
      ∃a∈S,G.Adj a.val b.val).card := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun u v => Classical.propDecidable (G.Adj u v)))
  obtain ⟨hp,hd⟩ := critical_low_strict_degree_comparison G hcrit
  exact strict_hall_of_degree_comparison
    (fun (a:lowVertices G) (b:↥((lowVertices G)ᶜ : Finset V)) => G.Adj a.val b.val)
    hp hd S hS

/-- A selected core partner can be reserved: the other vertices still
admit an injective actual neighbour assignment saturating all low vertices.
The forbidden vertex is one vertex of the complementary side. -/
theorem exists_low_selection_avoiding_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : IsDeltaCritical G) (b₀ : ↥((lowVertices G)ᶜ : Finset V)) :
    ∃f : lowVertices G → ↥((lowVertices G)ᶜ : Finset V),Function.Injective f ∧
      (∀a,G.Adj a.val (f a).val) ∧ ∀a,f a≠b₀ := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun u v => Classical.propDecidable (G.Adj u v)))
  obtain ⟨hp,hd⟩ := critical_low_strict_degree_comparison G hcrit
  exact exists_injection_avoiding_vertex_of_strict_degree_comparison
    (fun (a:lowVertices G) (b:↥((lowVertices G)ᶜ : Finset V)) => G.Adj a.val b.val)
    hp hd b₀

end OverfullWork.LowVertexMatchingFlexibility
