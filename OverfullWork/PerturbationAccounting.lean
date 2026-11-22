module

public import OverfullWork.CompletionAccounting

@[expose] public section


/-! # Exact accounting for internal-to-crossing matching perturbations -/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem edgesWithin_addCopies (M N : MultiGraph V) (S : Finset V) :
    (M.addCopies N).edgesWithin S=M.edgesWithin S+N.edgesWithin S := by
  unfold edgesWithin edgeCount
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro e _
  change (if e.toFinset⊆S then M.mult e+N.mult e else 0)=
    (if e.toFinset⊆S then M.mult e else 0)+(if e.toFinset⊆S then N.mult e else 0)
  split_ifs <;> omega

theorem cutSize_addCopies (M N : MultiGraph V) (S : Finset V) :
    (M.addCopies N).cutSize S=M.cutSize S+N.cutSize S := by
  simp only [cutSize,addCopies,sum_add_distrib]

theorem edgesWithin_unitEdge (u v : V) (hne : u≠v) (S : Finset V) :
    (unitEdge u v hne).edgesWithin S=if u∈S ∧ v∈S then 1 else 0 := by
  unfold edgesWithin edgeCount
  change (∑ e : Sym2 V,if e.toFinset⊆S then (if e=s(u,v) then 1 else 0) else 0)=_
  rw [sum_eq_single s(u,v)]
  · simp [Sym2.toFinset_mk_eq,insert_subset_iff,singleton_subset_iff]
  · intro e _ he
    simp [he]
  · simp

theorem sum_degree_unitEdge (u v : V) (hne : u≠v) (S : Finset V) :
    (∑ z∈S,(unitEdge u v hne).degree z)=(if u∈S then 1 else 0)+(if v∈S then 1 else 0) := by
  simp only [degree_unitEdge]
  have he : (∑ z∈S,if z=u ∨ z=v then 1 else 0)=
      (∑ z∈S,if z=u then 1 else 0)+(∑ z∈S,if z=v then 1 else 0) := by
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro z _
    by_cases hu : z=u
    · subst z; simp [hne]
    · simp [hu]
  rw [he]
  simp

theorem cutSize_unitEdge (u v : V) (hne : u≠v) (S : Finset V) :
    (unitEdge u v hne).cutSize S=if (u∈S ↔ v∈S) then 0 else 1 := by
  have h:=(unitEdge u v hne).sum_degree_eq_internal_add_cut S
  rw [twiceInternal_eq,edgesWithin_unitEdge,sum_degree_unitEdge] at h
  by_cases hu : u∈S <;> by_cases hv : v∈S <;> simp_all

/-- No internal copy is silently discarded: each removed internal copy
is added to the exact uncoloured remainder. -/
theorem remainder_internal_exchange (M F R A : MultiGraph V) (S : Finset V)
    (hF : ∀ e,F.mult e≤M.mult e) (hR : ∀ e,R.mult e≤F.mult e)
    (hRi : ∀ u v, ¬(u∈S ↔ v∈S) → R.mult s(u,v)=0)
    (hAc : ∀ u v, (u∈S ↔ v∈S) → A.mult s(u,v)=0) :
    (M.subtractCopies ((F.subtractCopies R).addCopies A)).internalPart S=
      ((M.subtractCopies F).internalPart S).addCopies R := by
  apply ext_mult
  intro e
  induction e using Sym2.inductionOn with
  | hf u v =>
    rw [internalPart_mult]
    change (if (u∈S ↔ v∈S) then M.mult s(u,v)-(F.mult s(u,v)-R.mult s(u,v)+A.mult s(u,v)) else 0)=
      ((M.subtractCopies F).internalPart S).mult s(u,v)+R.mult s(u,v)
    rw [internalPart_mult]
    by_cases h : u∈S ↔ v∈S
    · rw [if_pos h,if_pos h,hAc u v h]
      have hf:=hF s(u,v)
      have hr:=hR s(u,v)
      change M.mult s(u,v)-(F.mult s(u,v)-R.mult s(u,v)+0)=
        M.mult s(u,v)-F.mult s(u,v)+R.mult s(u,v)
      omega
    · rw [if_neg h,if_neg h,hRi u v h]

theorem edgesWithin_exchange (F R A : MultiGraph V) (S : Finset V)
    (hR : ∀ e,R.mult e≤F.mult e)
    (hA : ∀ e,e.toFinset⊆S → A.mult e=0) :
    ((F.subtractCopies R).addCopies A).edgesWithin S+R.edgesWithin S=F.edgesWithin S := by
  unfold edgesWithin edgeCount
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro e _
  change (if e.toFinset⊆S then F.mult e-R.mult e+A.mult e else 0)+
    (if e.toFinset⊆S then R.mult e else 0)=(if e.toFinset⊆S then F.mult e else 0)
  by_cases he : e.toFinset⊆S
  · rw [if_pos he,if_pos he,if_pos he,hA e he]
    have h:=hR e
    omega
  · simp only [if_neg he,Nat.zero_add]

theorem cutSize_exchange (F R A : MultiGraph V) (S : Finset V)
    (hR : ∀ u∈S,∀ v∈Sᶜ,R.mult s(u,v)=0) :
    ((F.subtractCopies R).addCopies A).cutSize S=F.cutSize S+A.cutSize S := by
  unfold cutSize
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro u hu
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro v hv
  change F.mult s(u,v)-R.mult s(u,v)+A.mult s(u,v)=_
  rw [hR u hu v hv,Nat.sub_zero]

/-- The sided geometry of a five-edge augmentation. -/
def FiveSided (S : Finset V) (p : Fin 6 ↪ V) : Prop :=
  p 0∈S ∧ p 1∉S ∧ p 2∉S ∧ p 3∈S ∧ p 4∈S ∧ p 5∉S

theorem five_sided_counts (S : Finset V) (p : Fin 6 ↪ V) (h : FiveSided S p) :
    (fiveRemoved p).edgesWithin S=1 ∧ (fiveRemoved p).edgesWithin Sᶜ=1 ∧
      (fiveRemoved p).cutSize S=0 ∧ (fiveAdded p).edgesWithin S=0 ∧
      (fiveAdded p).edgesWithin Sᶜ=0 ∧ (fiveAdded p).cutSize S=3 := by
  rcases h with ⟨h0,h1,h2,h3,h4,h5⟩
  simp [fiveRemoved,fiveAdded,edgesWithin_addCopies,cutSize_addCopies,
    edgesWithin_unitEdge,cutSize_unitEdge,h0,h1,h2,h3,h4,h5]

theorem mult_eq_zero_of_edgesWithin_zero (M : MultiGraph V) (S : Finset V)
    (h : M.edgesWithin S=0) (e : Sym2 V) (he : e.toFinset⊆S) : M.mult e=0 := by
  have hs : (M.restrict S).mult e≤(M.restrict S).edgeCount :=
    single_le_sum (f:=fun e => (M.restrict S).mult e) (fun _ _ => Nat.zero_le _) (mem_univ e)
  change (if e.toFinset⊆S then M.mult e else 0)≤M.edgesWithin S at hs
  rw [if_pos he,h] at hs
  omega

theorem cut_mult_eq_zero (M : MultiGraph V) (S : Finset V) (h : M.cutSize S=0)
    (u : V) (hu : u∈S) (v : V) (hv : v∈Sᶜ) : M.mult s(u,v)=0 := by
  have hi : M.mult s(u,v)≤∑ w∈Sᶜ,M.mult s(u,w) :=
    single_le_sum (f:=fun w => M.mult s(u,w)) (fun _ _ => Nat.zero_le _) hv
  have ho : (∑ w∈Sᶜ,M.mult s(u,w))≤M.cutSize S :=
    single_le_sum (f:=fun z => ∑ w∈Sᶜ,M.mult s(z,w)) (fun _ _ => Nat.zero_le _) hu
  omega

end SimpleGraph.MultiGraph
