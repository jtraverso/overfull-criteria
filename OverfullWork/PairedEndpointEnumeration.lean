module

public import OverfullWork.PairedPartition
public import Mathlib.Data.Bool.Basic

@[expose] public section


/-! # Actual enumerations of an even endpoint family by disjoint pairs

A cardinality equality constructs the enumeration. When four endpoints
are available, any prescribed distinct endpoints can be placed in
different pairs by extending a two-point correspondence to a permutation.
-/
namespace OverfullWork.PairedEndpointEnumeration
open Finset
open scoped Classical
variable {V : Type*}

/-- Positive even cardinality constructs a complete disjoint pairing. -/
theorem exists_pairing (A : Finset V) (heven : Even A.card) (hpos : 0<A.card) :
    ∃h : ℕ,1≤h ∧ A.card=2*h ∧ Nonempty ((Fin h×Bool)≃A) := by
  obtain ⟨h,hh⟩:=heven
  have hc : A.card=2*h := by omega
  refine ⟨h,by omega,hc,⟨Fintype.equivOfCardEq ?_⟩⟩
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Fintype.card_coe]
  omega

/-- At a fixed even size, two prescribed endpoints can occupy the first
position in two different pairs. The remaining endpoints are filled by a
permutation extension, rather than assumed as a partial pairing. -/
theorem exists_pairing_with_anchors (A : Finset V) (h : ℕ)
    (hcard : A.card=2*h) (htwo : 2≤h) (x y : A) (hxy : x≠y) :
    ∃e : (Fin h×Bool)≃A,
      e (⟨0,by omega⟩,false)=x ∧ e (⟨1,by omega⟩,false)=y := by
  let e₀ : (Fin h×Bool)≃A:=Fintype.equivOfCardEq (by
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Fintype.card_coe]
    omega)
  let p : Bool → A:=fun b => e₀ (if b then ⟨1,by omega⟩ else ⟨0,by omega⟩,false)
  let q : Bool → A:=fun b => if b then y else x
  have hp : Function.Injective p := by
    apply Bool.injective_iff.mpr
    intro he
    have hh:=congrArg (fun z:Fin h×Bool => z.1.val) (e₀.injective he)
    norm_num [p] at hh
  have hq : Function.Injective q := by
    apply Bool.injective_iff.mpr
    simpa only [q,Bool.false_eq_true,if_false,if_true] using hxy
  obtain ⟨σ,hσ⟩:=Equiv.Perm.exists_extending_pair p q hp hq
  refine ⟨e₀.trans σ,?_,?_⟩
  · simpa only [Equiv.trans_apply,p,q,Bool.false_eq_true,if_false] using hσ false
  · simpa only [Equiv.trans_apply,p,q,if_true] using hσ true

/-- Every even family of at least four endpoints admits a pairing which
places the chosen distinct endpoints in different pairs. -/
theorem exists_pairing_separating (A : Finset V) (heven : Even A.card)
    (hfour : 4≤A.card) (x y : A) (hxy : x≠y) :
    ∃h : ℕ,2≤h ∧ ∃e : (Fin h×Bool)≃A,(e.symm x).1≠(e.symm y).1 := by
  obtain ⟨h,hh⟩:=heven
  have hc : A.card=2*h := by omega
  have htwo : 2≤h := by omega
  obtain ⟨e,hx,hy⟩:=exists_pairing_with_anchors A h hc htwo x y hxy
  refine ⟨h,htwo,e,?_⟩
  have hxi : e.symm x=(⟨0,by omega⟩,false) := by rw [←hx,e.symm_apply_apply]
  have hyi : e.symm y=(⟨1,by omega⟩,false) := by rw [←hy,e.symm_apply_apply]
  rw [hxi,hyi]
  exact fun he => by have hh:=congrArg Fin.val he;norm_num at hh

/-- Distinct pair slots yield distinct endpoints. -/
theorem endpoint_ne {A : Finset V} {h : ℕ} (e : (Fin h×Bool)≃A)
    (i j : Fin h) (b d : Bool) (hij : i≠j ∨ b≠d) : e (i,b)≠e (j,d) := by
  intro he
  have hh:=e.injective he
  rcases hij with hi|hb
  · exact hi (congrArg Prod.fst hh)
  · exact hb (congrArg Prod.snd hh)

/-- The two endpoint columns each have no repetitions. -/
theorem endpoint_column_injective {A : Finset V} {h : ℕ} (e : (Fin h×Bool)≃A)
    (b : Bool) : Function.Injective (fun i => e (i,b)) := by
  intro i j he
  exact congrArg Prod.fst (e.injective he)

/-- Every endpoint appears in exactly one of the constructed pairs. -/
theorem covers {A : Finset V} {h : ℕ} (e : (Fin h×Bool)≃A) (v : A) :
    ∃i : Fin h,v=e (i,false) ∨ v=e (i,true) := by
  obtain ⟨⟨i,b⟩,rfl⟩:=e.surjective v
  cases b
  · exact ⟨i,Or.inl rfl⟩
  · exact ⟨i,Or.inr rfl⟩

end OverfullWork.PairedEndpointEnumeration
