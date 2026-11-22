module

public import OverfullWork.EvenDeficit

@[expose] public section


/-! # Realizing arbitrary balanced even degree sequences without loops

Repeatedly join two vertices of greatest positive remaining degree.
This construction allows parallel copies; no bounded degree-gap or
asymptotic assumption is used.
-/
namespace OverfullWork.LooplessRealization
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 1000000

def reduce (a : V → ℕ) (u v : V) (w : V) : ℕ :=
  a w-(if w=u ∨ w=v then 1 else 0)

/-- Removing one unit at each of two largest entries preserves balance. -/
theorem exists_reduction (a : V → ℕ) (heven : Even (∑ w,a w))
    (hbal : ∀ w,2*a w≤∑ z,a z) (hpos : 0<∑ w,a w) :
    ∃ u v : V,u≠v ∧ 0<a u ∧ 0<a v ∧
      (∑ w,reduce a u v w)+2=(∑ w,a w) ∧
      ∀ w,2*reduce a u v w≤∑ z,reduce a u v z := by
  classical
  have hx : ∃ w,0<a w := by
    by_contra hn
    have hz : ∀ w,a w=0:=fun w => by have hh : ¬0<a w:=fun h => hn ⟨w,h⟩;omega
    simp [hz] at hpos
  obtain ⟨x,hx⟩:=hx
  obtain ⟨u,_,hmax⟩:=(univ : Finset V).exists_max_image a ⟨x,mem_univ x⟩
  have hu : 0<a u:=(hx.trans_le (hmax x (mem_univ x)))
  let R:=(univ : Finset V).erase u
  have hsumR : (∑ w∈R,a w)+a u=∑ w,a w:=sum_erase_add _ _ (mem_univ u)
  have hRpos : 0<∑ w∈R,a w:=by have hh:=hbal u;omega
  have hRne : R.Nonempty := by
    by_contra hn
    have hz : R=∅:=not_nonempty_iff_eq_empty.mp hn
    simp [hz] at hRpos
  obtain ⟨v,hv,hmaxv⟩:=R.exists_max_image a hRne
  have huv : u≠v:=((mem_erase.mp hv).1).symm
  have hvpos : 0<a v := by
    by_contra hn
    have hz : ∀ w∈R,a w=0:=fun w hw => by have hh:=hmaxv w hw;omega
    have hh : (∑ w∈R,a w)=0:=sum_eq_zero hz
    omega
  have hpoint (w : V) : reduce a u v w+(if w=u ∨ w=v then 1 else 0)=a w := by
    dsimp only [reduce]
    by_cases hw : w=u ∨ w=v
    · rw [if_pos hw]
      rcases hw with rfl|rfl <;> omega
    · rw [if_neg hw]
      omega
  have hsum : (∑ w,reduce a u v w)+2=∑ w,a w := by
    have hh:=sum_congr (s₁:=(univ : Finset V)) rfl (fun w _ => hpoint w)
    rw [sum_add_distrib] at hh
    have hind : (∑ w : V,if w=u ∨ w=v then 1 else 0)=2 := by
      rw [←card_filter]
      have he : univ.filter (fun w : V => w=u ∨ w=v)={u,v}:=by ext w;simp
      rw [he,card_pair huv]
    rwa [hind] at hh
  refine ⟨u,v,huv,hu,hvpos,hsum,?_⟩
  intro w
  have hwbal:=hbal w
  by_cases hw : w=u ∨ w=v
  · change 2*(a w-(if w=u ∨ w=v then 1 else 0))≤_
    rw [if_pos hw]
    rcases hw with rfl|rfl <;> omega
  · have hwu : w≠u:=fun h => hw (Or.inl h)
    have hwv : w≠v:=fun h => hw (Or.inr h)
    have htriple : a u+a v+a w≤∑ z,a z := by
      have hh:=sum_le_sum_of_subset_of_nonneg
        (show ({u,v,w} : Finset V)⊆univ from subset_univ _)
        (f:=a) (fun _ _ _ => Nat.zero_le _)
      simpa [huv,hwu.symm,hwv.symm,add_assoc] using hh
    have hwuMax:=hmax w (mem_univ w)
    have hwvMax:=hmaxv w (mem_erase.mpr ⟨hwu,mem_univ w⟩)
    have hstrict : 2*a w<∑ z,a z:=by omega
    obtain ⟨k,hk⟩:=heven
    change 2*(a w-(if w=u ∨ w=v then 1 else 0))≤_
    rw [if_neg hw]
    omega

/-- Exact loopless multigraph realization, allowing arbitrary parallel
multiplicity and arbitrary prescribed degrees. -/
theorem exists_realization (a : V → ℕ) (heven : Even (∑ v,a v))
    (hbal : ∀ v,2*a v≤∑ w,a w) :
    ∃ J : MultiGraph V,∀ v,J.degree v=a v := by
  classical
  suffices ∀ n : ℕ,∀ a : V → ℕ,(∑ v,a v)=n → Even n →
      (∀ v,2*a v≤n) → ∃ J : MultiGraph V,∀ v,J.degree v=a v from
    this _ a rfl heven hbal
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a hsum heven hbal
    by_cases hn : n=0
    · refine ⟨MultiGraph.ofSimpleGraph ⊥,?_⟩
      intro v
      rw [MultiGraph.degree_ofSimpleGraph]
      have hh:=single_le_sum (f:=a) (s:=univ) (fun _ _ => Nat.zero_le _) (mem_univ v)
      rw [←card_neighborFinset_eq_degree]
      have hz : a v=0:=by omega
      simp [hz]
    · obtain ⟨u,v,huv,hu,hv,hred,hbalance⟩:=exists_reduction a
        (by rwa [hsum]) (by simpa [hsum] using hbal) (by omega)
      have hredlt : (∑ w,reduce a u v w)<n:=by omega
      have hredeven : Even (∑ w,reduce a u v w) := by
        obtain ⟨k,hk⟩:=heven
        exact ⟨k-1,by omega⟩
      obtain ⟨J,hJ⟩:=ih _ hredlt (reduce a u v) rfl hredeven hbalance
      refine ⟨J.addCopies (MultiGraph.unitEdge u v huv),?_⟩
      intro w
      rw [MultiGraph.degree_addCopies,MultiGraph.degree_unitEdge,hJ]
      change a w-(if w=u ∨ w=v then 1 else 0)+(if w=u ∨ w=v then 1 else 0)=a w
      by_cases hw : w=u ∨ w=v
      · rw [if_pos hw]
        rcases hw with rfl|rfl <;> omega
      · rw [if_neg hw]
        omega

theorem degree_balanced (J : MultiGraph V) (v : V) :
    2*J.degree v≤∑ w,J.degree w := by
  have hsum:=sum_erase_add (univ : Finset V) (fun w => J.degree w) (mem_univ v)
  have hdeg : J.degree v≤∑ w∈(univ : Finset V).erase v,J.degree w := by
    have hp:=sum_erase_add (univ : Finset V) (fun w => J.mult s(v,w)) (mem_univ v)
    rw [J.loopless s(v,v) (by simp),Nat.add_zero,←J.degree_eq_sum_mult] at hp
    rw [←hp]
    apply sum_le_sum
    intro w _
    calc
      J.mult s(v,w)=J.mult s(w,v):=by rw [Sym2.eq_swap]
      _ ≤ J.degree w:=J.mult_pair_le_degree w v
  omega

/-- Exact criterion for realizability in the weighted loopless model. -/
theorem realization_iff (a : V → ℕ) :
    (∃ J : MultiGraph V,∀ v,J.degree v=a v) ↔
      Even (∑ v,a v) ∧ ∀ v,2*a v≤∑ w,a w := by
  constructor
  · rintro ⟨J,hJ⟩
    have hs : (∑ v,a v)=2*J.edgeCount := by
      simp_rw [←hJ]
      exact J.sum_degrees_eq_twice_edgeCount
    refine ⟨⟨J.edgeCount,by omega⟩,?_⟩
    intro v
    simpa only [hJ] using degree_balanced J v
  · rintro ⟨heven,hbal⟩
    exact exists_realization a heven hbal

end OverfullWork.LooplessRealization
